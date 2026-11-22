Require Import Utf8.

Require Import Lang.FOmegaEq.Types Lang.FOmegaEq.Kinds Lang.FOmegaEq.Syntax Lang.FOmegaEq.OpSemantics Lang.FOmegaEq.Typing.

Require Import Binding.Intrinsic.
Import Binding.Intrinsic (Ctx, dom, extC, Build_Ctx, mtC).

Require Import Binding.Lib Binding.Env.

Import kindEqDec.

Require Import Coq.Relations.Relation_Operators Coq.Relations.Operators_Properties.

Local Open Scope syn_scope.

Require Import List.
Require Import Eqdep_dec.
Require Import Lia.
Require Import Coq.Program.Equality.

Definition ren_arr {A B : Set} (f : A -> B) : Binding.Set.Arr A B :=
  @Binding.Set.Build_Arr A B f.
Definition vren {A B : Set} (f : A -> B) (v : value A) : value B := vmap (ren_arr f) v.
Definition eren {A B : Set} (f : A -> B) (e : expr A) : expr B := emap (ren_arr f) e.

Lemma rel_lift {V V' : Set} {Δ : Ctx kind} {Γ : V -> typ ⋆ Δ} {Γ' : V' -> typ ⋆ Δ}
      {f : V -> V'} (Hf : forall x, Γ' (f x) = Γ x) (σ : typ ⋆ Δ) :
  forall y : inc V, (Γ' ▹ σ) (@inc_map V V' f y) = (Γ ▹ σ) y.
Proof. intros [|x]; simpl; [reflexivity| exact (Hf x)]. Qed.

Lemma rel_lift2 {V V' : Set} {Δ : Ctx kind} {Γ : V -> typ ⋆ Δ} {Γ' : V' -> typ ⋆ Δ}
      {f : V -> V'} (Hf : forall x, Γ' (f x) = Γ x) (σ τ : typ ⋆ Δ) :
  forall y : inc (inc V),
    ((Γ' ▹ σ) ▹ τ) (@inc_map (inc V) (inc V') (@inc_map V V' f) y) = ((Γ ▹ σ) ▹ τ) y.
Proof.
  intros [|[|x]]; simpl; try reflexivity; exact (Hf x).
Qed.

Definition shiftt (κ : kind) {κ' : kind} {Δ : Ctx kind} (τ : typ κ' Δ) :
  typ κ' (@extC kind κ Δ) :=
  @shift (Ctx kind) (@Arr kind) (typ κ') (@FMap_typ κ') (@extC kind κ)
         (@ShiftableCore_ext kind κ) Δ τ.

Lemma rel_shift {V V' : Set} {Δ : Ctx kind} {Γ : V -> typ ⋆ Δ} {Γ' : V' -> typ ⋆ Δ}
      {f : V -> V'} (Hf : forall x, Γ' (f x) = Γ x) (κ : kind) :
  forall y : V, (Env.compose (shiftt κ) Γ') (f y) = (Env.compose (shiftt κ) Γ) y.
Proof. intro y. unfold shiftt. simpl. apply f_equal, Hf. Qed.

Lemma rel_shift_extend {V V' : Set} {Δ : Ctx kind} {Γ : V -> typ ⋆ Δ} {Γ' : V' -> typ ⋆ Δ}
      {f : V -> V'} (Hf : forall x, Γ' (f x) = Γ x) (κ : kind) (σ : typ ⋆ (@extC kind κ Δ)) :
  forall y : inc V,
    (Env.extend (Env.compose (shiftt κ) Γ') σ) (@inc_map V V' f y) =
    (Env.extend (Env.compose (shiftt κ) Γ) σ) y.
Proof. intros [|x]; simpl; [reflexivity| unfold shiftt; simpl; apply f_equal, Hf]. Qed.

Scheme typing_expr_mut := Induction for typing_expr Sort Prop
with typing_val_mut := Induction for typing_val Sort Prop.

Lemma typing_ren_mut :
  (forall (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
          (e : expr V) (τ : typ ⋆ Δ), Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
   forall (V' : Set) (Γ' : V' -> typ ⋆ Δ) (f : V -> V'),
     (forall x, Γ' (f x) = Γ x) -> Δ ∣ Ψ ∣ Γ' ⊢ₑ eren f e : τ)
  /\
  (forall (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
          (v : value V) (τ : typ ⋆ Δ), Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ ->
   forall (V' : Set) (Γ' : V' -> typ ⋆ Δ) (f : V -> V'),
     (forall x, Γ' (f x) = Γ x) -> Δ ∣ Ψ ∣ Γ' ⊢ᵥ vren f v : τ).
Proof.
  assert (HE : forall (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
          (e : expr V) (τ : typ ⋆ Δ), Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
   forall (V' : Set) (Γ' : V' -> typ ⋆ Δ) (f : V -> V'),
     (forall x, Γ' (f x) = Γ x) -> Δ ∣ Ψ ∣ Γ' ⊢ₑ eren f e : τ).
  { intros V Δ Ψ Γ e τ H.
    induction H using typing_expr_mut with
      (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
                 (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ) =>
             forall (V' : Set) (Γ' : V' -> typ ⋆ Δ) (f : V -> V'),
               (forall x, Γ' (f x) = Γ x) -> Δ ∣ Ψ ∣ Γ' ⊢ᵥ vren f v : τ).
    - (* T_val *) intros V' Γ' f Hf. simpl. eapply T_val. eauto.
    - (* T_bind *) intros V' Γ' f Hf. simpl. eapply T_bind; eauto 12 using rel_lift.
    - (* T_congE *) intros V' Γ' f Hf. simpl. eapply T_congE; eauto.
    - (* T_app *) intros V' Γ' f Hf. simpl. eapply T_app; eauto.
    - (* T_tapp *) intros V' Γ' f Hf. simpl. eapply T_tapp; eauto.
    - (* T_projL *) intros V' Γ' f Hf. simpl. eapply T_projL; eauto.
    - (* T_projR *) intros V' Γ' f Hf. simpl. eapply T_projR; eauto.
    - (* T_abort *) intros V' Γ' f Hf. simpl. eapply T_abort; eauto.
    - (* T_case *) intros V' Γ' f Hf. simpl. eapply T_case; eauto 12 using rel_lift.
    - (* T_unpack *) intros V' Γ' f Hf. simpl. eapply T_unpack; eauto 12 using rel_shift_extend.
    - (* T_unroll *) intros V' Γ' f Hf. simpl. eapply T_unroll; eauto.
    - (* T_cabort *) intros V' Γ' f Hf. simpl. eapply T_cabort; eauto.
    - (* T_capp *) intros V' Γ' f Hf. simpl. eapply T_capp; eauto.
    - (* T_lwith *) intros V' Γ' f Hf. simpl. eapply T_lwith; eauto 12 using rel_lift.
    (* value cases *)
    - (* T_var *) intros V' Γ' f Hf. simpl. apply T_var. apply (eq_trans (Hf x) EQ).
    - (* T_congV *) intros V' Γ' f Hf. simpl. eapply T_congV; eauto.
    - (* T_unit *) intros V' Γ' f Hf. simpl. apply T_unit.
    - (* T_lam *) intros V' Γ' f Hf. simpl. eapply T_lam; eauto 12 using rel_lift.
    - (* T_pair *) intros V' Γ' f Hf. simpl. eapply T_pair; eauto.
    - (* T_injl *) intros V' Γ' f Hf. simpl. eapply T_injl; eauto.
    - (* T_injr *) intros V' Γ' f Hf. simpl. eapply T_injr; eauto.
    - (* T_tlam *) intros V' Γ' f Hf. simpl. eapply T_tlam; eauto 12 using rel_shift.
    - (* T_pack *) intros V' Γ' f Hf. simpl. eapply T_pack; eauto.
    - (* T_roll *) intros V' Γ' f Hf. simpl. eapply T_roll; eauto.
    - (* T_lamC *) intros V' Γ' f Hf. simpl. eapply T_lamC; eauto.
    - (* T_withC *) intros V' Γ' f Hf. simpl. eapply T_withC; eauto.
    - (* T_rec *) intros V' Γ' f Hf. simpl. eapply T_rec.
      change (Δ ∣ Ψ ∣ (Γ' ▹ (τ₁ →ᵗ τ₂) ▹ τ₁) ⊢ₑ
              emap (ren_arr (@inc_map (inc V) (inc V') (@inc_map V V' f))) e : τ₂).
      eauto 12 using rel_lift2. }
  split; [ exact HE | ].
  intros V Δ Ψ Γ v τ H.
  induction H using typing_val_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
           forall (V' : Set) (Γ' : V' -> typ ⋆ Δ) (f : V -> V'),
             (forall x, Γ' (f x) = Γ x) -> Δ ∣ Ψ ∣ Γ' ⊢ₑ eren f e : τ).
  - (* T_val *) intros V' Γ' f Hf. simpl. eapply T_val. eauto.
  - (* T_bind *) intros V' Γ' f Hf. simpl. eapply T_bind; eauto 12 using rel_lift.
  - (* T_congE *) intros V' Γ' f Hf. simpl. eapply T_congE; eauto.
  - (* T_app *) intros V' Γ' f Hf. simpl. eapply T_app; eauto.
  - (* T_tapp *) intros V' Γ' f Hf. simpl. eapply T_tapp; eauto.
  - (* T_projL *) intros V' Γ' f Hf. simpl. eapply T_projL; eauto.
  - (* T_projR *) intros V' Γ' f Hf. simpl. eapply T_projR; eauto.
  - (* T_abort *) intros V' Γ' f Hf. simpl. eapply T_abort; eauto.
  - (* T_case *) intros V' Γ' f Hf. simpl. eapply T_case; eauto 12 using rel_lift.
  - (* T_unpack *) intros V' Γ' f Hf. simpl. eapply T_unpack; eauto 12 using rel_shift_extend.
  - (* T_unroll *) intros V' Γ' f Hf. simpl. eapply T_unroll; eauto.
  - (* T_cabort *) intros V' Γ' f Hf. simpl. eapply T_cabort; eauto.
  - (* T_capp *) intros V' Γ' f Hf. simpl. eapply T_capp; eauto.
  - (* T_lwith *) intros V' Γ' f Hf. simpl. eapply T_lwith; eauto 12 using rel_lift.
  - (* T_var *) intros V' Γ' f Hf. simpl. apply T_var. apply (eq_trans (Hf x) EQ).
  - (* T_congV *) intros V' Γ' f Hf. simpl. eapply T_congV; eauto.
  - (* T_unit *) intros V' Γ' f Hf. simpl. apply T_unit.
  - (* T_lam *) intros V' Γ' f Hf. simpl. eapply T_lam; eauto 12 using rel_lift.
  - (* T_pair *) intros V' Γ' f Hf. simpl. eapply T_pair; eauto.
  - (* T_injl *) intros V' Γ' f Hf. simpl. eapply T_injl; eauto.
  - (* T_injr *) intros V' Γ' f Hf. simpl. eapply T_injr; eauto.
  - (* T_tlam *) intros V' Γ' f Hf. simpl. eapply T_tlam; eauto 12 using rel_shift.
  - (* T_pack *) intros V' Γ' f Hf. simpl. eapply T_pack; eauto.
  - (* T_roll *) intros V' Γ' f Hf. simpl. eapply T_roll; eauto.
  - (* T_lamC *) intros V' Γ' f Hf. simpl. eapply T_lamC; eauto.
  - (* T_withC *) intros V' Γ' f Hf. simpl. eapply T_withC; eauto.
  - (* T_rec *) intros V' Γ' f Hf. simpl. eapply T_rec.
    change (Δ ∣ Ψ ∣ (Γ' ▹ (τ₁ →ᵗ τ₂) ▹ τ₁) ⊢ₑ
            emap (ren_arr (@inc_map (inc V) (inc V') (@inc_map V V' f))) e : τ₂).
    eauto 12 using rel_lift2.
Qed.


(* ---------- Type-level renaming algebra ---------- *)

Lemma t_var_irr (κ : kind) (Δ : Ctx kind) (x : dom Δ) (p q : Δ x = κ) :
  t_var κ x p = t_var κ x q.
Proof. f_equal. apply (UIP_dec kindEqDec.eq_dec). Qed.

Lemma tmap_var_ext (κ : kind) (Δ₁ Δ₂ : Ctx kind) (x : dom Δ₁) (EQ : Δ₁ x = κ)
      (ρ₁ ρ₂ : @Arr kind Δ₁ Δ₂) (H : ρ₁ x = ρ₂ x) :
  t_var κ (ρ₁ x) (eq_trans (arr_hom ρ₁ x) EQ) =
  t_var κ (ρ₂ x) (eq_trans (arr_hom ρ₂ x) EQ).
Proof.
  refine (eq_ind (ρ₁ x) (fun w => forall (r : Δ₂ w = κ),
            t_var κ (ρ₁ x) (eq_trans (arr_hom ρ₁ x) EQ) = t_var κ w r)
          _ (ρ₂ x) H _).
  intro r. apply t_var_irr.
Qed.

Fixpoint tmap_ext (κ : kind) (Δ₁ Δ₂ : Ctx kind) (τ : typ κ Δ₁) {struct τ} :
  forall (ρ₁ ρ₂ : @Arr kind Δ₁ Δ₂), (forall x, ρ₁ x = ρ₂ x) ->
  tmap ρ₁ τ = tmap ρ₂ τ :=
  match τ as τ' in type _ κ' return
        forall (ρ₁ ρ₂ : @Arr kind Δ₁ Δ₂), (forall x, ρ₁ x = ρ₂ x) ->
        tmap ρ₁ τ' = tmap ρ₂ τ' with
  | t_var κ x EQ => fun ρ₁ ρ₂ H => tmap_var_ext κ Δ₁ Δ₂ x EQ ρ₁ ρ₂ (H x)
  | t_lam b => fun ρ₁ ρ₂ H =>
      f_equal t_lam
        (tmap_ext _ (extC _ Δ₁) (extC _ Δ₂) b
           (lift ρ₁) (lift ρ₂)
           (fun x => match x with VZ => eq_refl | VS y => f_equal (@VS (dom _)) (H y) end))
  | t_app σ τ0 => fun ρ₁ ρ₂ H =>
      f_equal2 (fun f a => @t_app Δ₂ _ _ f a)
        (tmap_ext _ Δ₁ Δ₂ σ ρ₁ ρ₂ H) (tmap_ext _ Δ₁ Δ₂ τ0 ρ₁ ρ₂ H)
  | t_ctor c => fun ρ₁ ρ₂ H => eq_refl
  | t_carr ψ τ0 => fun ρ₁ ρ₂ H =>
      f_equal2 (fun z a => @t_carr Δ₂ z a)
        (cmap_ext Δ₁ Δ₂ ψ ρ₁ ρ₂ H) (tmap_ext _ Δ₁ Δ₂ τ0 ρ₁ ρ₂ H)
  | t_cprod ψ τ0 => fun ρ₁ ρ₂ H =>
      f_equal2 (fun z a => @t_cprod Δ₂ z a)
        (cmap_ext Δ₁ Δ₂ ψ ρ₁ ρ₂ H) (tmap_ext _ Δ₁ Δ₂ τ0 ρ₁ ρ₂ H)
  end
with cmap_ext (Δ₁ Δ₂ : Ctx kind) (ψ : constr Δ₁) {struct ψ} :
  forall (ρ₁ ρ₂ : @Arr kind Δ₁ Δ₂), (forall x, ρ₁ x = ρ₂ x) ->
  cmap ρ₁ ψ = cmap ρ₂ ψ :=
  match ψ as ψ' return
        forall (ρ₁ ρ₂ : @Arr kind Δ₁ Δ₂), (forall x, ρ₁ x = ρ₂ x) ->
        cmap ρ₁ ψ' = cmap ρ₂ ψ' with
  | c_eq κ a b => fun ρ₁ ρ₂ H =>
      f_equal2 (fun z w => @c_eq Δ₂ κ z w)
        (tmap_ext κ Δ₁ Δ₂ a ρ₁ ρ₂ H) (tmap_ext κ Δ₁ Δ₂ b ρ₁ ρ₂ H)
  end.

Definition liftA (κ : kind) {Δ₁ Δ₂ : Ctx kind} (ρ : @Arr kind Δ₁ Δ₂) :
  @Arr kind (extC κ Δ₁) (extC κ Δ₂) :=
  @lift (Ctx kind) (@Arr kind) (@extC kind κ) (@ALiftableCore_ext kind κ) Δ₁ Δ₂ ρ.

Definition mkShift (κ : kind) (Δ : Ctx kind) : @Arr kind Δ (extC κ Δ) :=
  @Build_Arr kind Δ (extC κ Δ) (fun x => @VS (dom Δ) x) (fun x => eq_refl).

Fixpoint tmap_tmap (κ : kind) (Δ₁ Δ₂ Δ₃ : Ctx kind) (τ : typ κ Δ₁) {struct τ} :
  forall (f : @Arr kind Δ₂ Δ₃) (g : @Arr kind Δ₁ Δ₂),
  tmap f (tmap g τ) = tmap (arrow_comp f g) τ :=
  match τ as τ' in type _ κ' return
    forall (f : @Arr kind Δ₂ Δ₃) (g : @Arr kind Δ₁ Δ₂),
    tmap f (tmap g τ') = tmap (arrow_comp f g) τ' with
  | @t_var _ κ x EQ => fun f g =>
      t_var_irr κ Δ₃ (f (g x)) _ _
  | @t_lam _ k1 k2 b => fun f g =>
      f_equal t_lam (eq_trans
        (tmap_tmap k2 (extC k1 Δ₁) (extC k1 Δ₂) (extC k1 Δ₃) b
           (liftA k1 f) (liftA k1 g))
        (tmap_ext k2 (extC k1 Δ₁) (extC k1 Δ₃) b
           (arrow_comp (liftA k1 f) (liftA k1 g)) (liftA k1 (arrow_comp f g))
           (fun x => match x with VZ => eq_refl | VS y => eq_refl end)))
  | @t_app _ k1 k2 σ τ0 => fun f g =>
      f_equal2 (fun a b => @t_app Δ₃ k1 k2 a b)
        (tmap_tmap (k1 ⇒ k2) Δ₁ Δ₂ Δ₃ σ f g) (tmap_tmap k1 Δ₁ Δ₂ Δ₃ τ0 f g)
  | @t_ctor _ κ c => fun f g => eq_refl
  | @t_carr _ ψ τ0 => fun f g =>
      f_equal2 (fun a b => @t_carr Δ₃ a b)
        (cmap_tmap Δ₁ Δ₂ Δ₃ ψ f g) (tmap_tmap ⋆ Δ₁ Δ₂ Δ₃ τ0 f g)
  | @t_cprod _ ψ τ0 => fun f g =>
      f_equal2 (fun a b => @t_cprod Δ₃ a b)
        (cmap_tmap Δ₁ Δ₂ Δ₃ ψ f g) (tmap_tmap ⋆ Δ₁ Δ₂ Δ₃ τ0 f g)
  end
with cmap_tmap (Δ₁ Δ₂ Δ₃ : Ctx kind) (ψ : constr Δ₁) {struct ψ} :
  forall (f : @Arr kind Δ₂ Δ₃) (g : @Arr kind Δ₁ Δ₂),
  cmap f (cmap g ψ) = cmap (arrow_comp f g) ψ :=
  match ψ as ψ' return
    forall (f : @Arr kind Δ₂ Δ₃) (g : @Arr kind Δ₁ Δ₂),
    cmap f (cmap g ψ') = cmap (arrow_comp f g) ψ' with
  | @c_eq _ κ a b => fun f g =>
      f_equal2 (fun x y => @c_eq Δ₃ κ x y)
        (tmap_tmap κ Δ₁ Δ₂ Δ₃ a f g) (tmap_tmap κ Δ₁ Δ₂ Δ₃ b f g)
  end.

Lemma shiftt_eq (κ κ' : kind) (Δ : Ctx kind) (τ : typ κ' Δ) :
  shiftt κ τ = tmap (mkShift κ Δ) τ.
Proof. reflexivity. Qed.

Lemma tmap_shift_comm (κ κ' : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂)
      (τ : typ κ' Δ₁) :
  tmap (liftA κ ρ) (shiftt κ τ) = shiftt κ (tmap ρ τ).
Proof.
  rewrite shiftt_eq. rewrite shiftt_eq.
  rewrite tmap_tmap.
  rewrite tmap_tmap.
  apply tmap_ext. intros x. reflexivity.
Qed.

Definition TSub (Δ₁ Δ₂ : Ctx kind) := @Sub kind (fun κ => typ κ) IPC_typ Δ₁ Δ₂.

Definition liftS (k : kind) {Δ₁ Δ₂ : Ctx kind} (ρ : TSub Δ₁ Δ₂) :
  TSub (@extC kind k Δ₁) (@extC kind k Δ₂) :=
  @lift (Ctx kind) TSub (@extC kind k)
        (@SLiftableCore_ext kind (fun κ => typ κ) IPC_typ (fun v => @FMap_typ v) k)
        Δ₁ Δ₂ ρ.

Lemma shift_is_shiftt (k κ' : kind) (Δ : Ctx kind) (u : typ κ' Δ) :
  @shift (Ctx kind) (@Arr kind) (typ κ') (@FMap_typ κ') (@extC kind k)
         (@ShiftableCore_ext kind k) Δ u = shiftt k u.
Proof. reflexivity. Qed.

Lemma compat_liftS (k : kind) (Δ₁ Δ₂ Δ₃ : Ctx kind)
      (ρL : @Arr kind Δ₂ Δ₃) (ρR : TSub Δ₁ Δ₂) (ρR' : TSub Δ₁ Δ₃)
      (H : forall κ (x : dom Δ₁) EQ, tmap ρL (ρR κ x EQ) = ρR' κ x EQ) :
  forall κ (z : dom (extC k Δ₁)) EQ,
    tmap (liftA k ρL) (liftS k ρR κ z EQ) = liftS k ρR' κ z EQ.
Proof.
  intros κ [|y] EQ; simpl.
  - apply t_var_irr.
  - rewrite shift_is_shiftt. rewrite tmap_shift_comm. rewrite H.
    rewrite shift_is_shiftt. reflexivity.
Qed.

Fixpoint tmap_tbind (κ : kind) (Δ₁ Δ₂ Δ₃ : Ctx kind) (τ : typ κ Δ₁) {struct τ} :
  forall (ρL : @Arr kind Δ₂ Δ₃) (ρR : TSub Δ₁ Δ₂) (ρR' : TSub Δ₁ Δ₃),
    (forall κ' (x : dom Δ₁) EQ, tmap ρL (ρR κ' x EQ) = ρR' κ' x EQ) ->
    tmap ρL (tbind ρR τ) = tbind ρR' τ :=
  match τ as τ' in type _ κ' return
    forall (ρL : @Arr kind Δ₂ Δ₃) (ρR : TSub Δ₁ Δ₂) (ρR' : TSub Δ₁ Δ₃),
      (forall κ0 (x : dom Δ₁) EQ, tmap ρL (ρR κ0 x EQ) = ρR' κ0 x EQ) ->
      tmap ρL (tbind ρR τ') = tbind ρR' τ' with
  | @t_var _ κ x EQ => fun ρL ρR ρR' H => H κ x EQ
  | @t_lam _ k1 k2 b => fun ρL ρR ρR' H =>
      f_equal t_lam
        (tmap_tbind k2 (extC k1 Δ₁) (extC k1 Δ₂) (extC k1 Δ₃) b
           (liftA k1 ρL) (liftS k1 ρR) (liftS k1 ρR') (compat_liftS k1 Δ₁ Δ₂ Δ₃ ρL ρR ρR' H))
  | @t_app _ k1 k2 σ τ0 => fun ρL ρR ρR' H =>
      f_equal2 (fun a b => @t_app Δ₃ k1 k2 a b)
        (tmap_tbind (k1 ⇒ k2) Δ₁ Δ₂ Δ₃ σ ρL ρR ρR' H)
        (tmap_tbind k1 Δ₁ Δ₂ Δ₃ τ0 ρL ρR ρR' H)
  | @t_ctor _ κ c => fun ρL ρR ρR' H => eq_refl
  | @t_carr _ ψ τ0 => fun ρL ρR ρR' H =>
      f_equal2 (fun a b => @t_carr Δ₃ a b)
        (cmap_cbind Δ₁ Δ₂ Δ₃ ψ ρL ρR ρR' H) (tmap_tbind ⋆ Δ₁ Δ₂ Δ₃ τ0 ρL ρR ρR' H)
  | @t_cprod _ ψ τ0 => fun ρL ρR ρR' H =>
      f_equal2 (fun a b => @t_cprod Δ₃ a b)
        (cmap_cbind Δ₁ Δ₂ Δ₃ ψ ρL ρR ρR' H) (tmap_tbind ⋆ Δ₁ Δ₂ Δ₃ τ0 ρL ρR ρR' H)
  end
with cmap_cbind (Δ₁ Δ₂ Δ₃ : Ctx kind) (ψ : constr Δ₁) {struct ψ} :
  forall (ρL : @Arr kind Δ₂ Δ₃) (ρR : TSub Δ₁ Δ₂) (ρR' : TSub Δ₁ Δ₃),
    (forall κ' (x : dom Δ₁) EQ, tmap ρL (ρR κ' x EQ) = ρR' κ' x EQ) ->
    cmap ρL (cbind ρR ψ) = cbind ρR' ψ :=
  match ψ as ψ' return
    forall (ρL : @Arr kind Δ₂ Δ₃) (ρR : TSub Δ₁ Δ₂) (ρR' : TSub Δ₁ Δ₃),
      (forall κ0 (x : dom Δ₁) EQ, tmap ρL (ρR κ0 x EQ) = ρR' κ0 x EQ) ->
      cmap ρL (cbind ρR ψ') = cbind ρR' ψ' with
  | @c_eq _ κ a b => fun ρL ρR ρR' H =>
      f_equal2 (fun x y => @c_eq Δ₃ κ x y)
        (tmap_tbind κ Δ₁ Δ₂ Δ₃ a ρL ρR ρR' H)
        (tmap_tbind κ Δ₁ Δ₂ Δ₃ b ρL ρR ρR' H)
  end.

Definition compSub (Δ₁ Δ₂ Δ₃ : Ctx kind) (ρL : @Arr kind Δ₂ Δ₃) (ρR : TSub Δ₁ Δ₂) : TSub Δ₁ Δ₃ :=
  @Build_Sub kind (fun κ => typ κ) IPC_typ Δ₁ Δ₃
    (fun v x EQ => tmap ρL (ρR v x EQ)).

Definition compSub2 (Δ₁ Δ₂ Δ₃ : Ctx kind) (ρL : @Arr kind Δ₁ Δ₂) (ρR : TSub Δ₂ Δ₃) : TSub Δ₁ Δ₃ :=
  @Build_Sub kind (fun κ => typ κ) IPC_typ Δ₁ Δ₃
    (fun v x EQ => tbind ρR (t_var v (ρL x) (eq_trans (arr_hom ρL x) EQ))).

Lemma t_var_congr (κ : kind) (Δ : Ctx kind) (x y : dom Δ) (p : Δ x = κ) (q : Δ y = κ)
      (e : x = y) : t_var κ x p = t_var κ y q.
Proof. destruct e. apply t_var_irr. Qed.

Lemma liftS_ext (k : kind) (Δ₁ Δ₂ : Ctx kind) (ρ₁ ρ₂ : TSub Δ₁ Δ₂)
      (H : forall v x EQ, ρ₁ v x EQ = ρ₂ v x EQ) :
  forall v (z : dom (extC k Δ₁)) EQ,
    liftS k ρ₁ v z EQ = liftS k ρ₂ v z EQ.
Proof.
  intros v [|y] EQ; simpl.
  - reflexivity.
  - apply f_equal, H.
Qed.

Fixpoint tbind_ext (κ : kind) (Δ₁ Δ₂ : Ctx kind) (τ : typ κ Δ₁) {struct τ} :
  forall (ρ₁ ρ₂ : TSub Δ₁ Δ₂),
    (forall v x EQ, ρ₁ v x EQ = ρ₂ v x EQ) -> tbind ρ₁ τ = tbind ρ₂ τ :=
  match τ as τ' in type _ κ' return
    forall (ρ₁ ρ₂ : TSub Δ₁ Δ₂),
      (forall v x EQ, ρ₁ v x EQ = ρ₂ v x EQ) -> tbind ρ₁ τ' = tbind ρ₂ τ' with
  | @t_var _ κ x EQ => fun ρ₁ ρ₂ H => H κ x EQ
  | @t_lam _ k1 k2 b => fun ρ₁ ρ₂ H =>
      f_equal t_lam (tbind_ext k2 (extC k1 Δ₁) (extC k1 Δ₂) b (liftS k1 ρ₁) (liftS k1 ρ₂)
                       (liftS_ext k1 Δ₁ Δ₂ ρ₁ ρ₂ H))
  | @t_app _ k1 k2 σ τ0 => fun ρ₁ ρ₂ H =>
      f_equal2 (fun a b => @t_app Δ₂ k1 k2 a b)
        (tbind_ext (k1 ⇒ k2) Δ₁ Δ₂ σ ρ₁ ρ₂ H) (tbind_ext k1 Δ₁ Δ₂ τ0 ρ₁ ρ₂ H)
  | @t_ctor _ κ c => fun ρ₁ ρ₂ H => eq_refl
  | @t_carr _ ψ τ0 => fun ρ₁ ρ₂ H =>
      f_equal2 (fun a b => @t_carr Δ₂ a b)
        (cbind_ext Δ₁ Δ₂ ψ ρ₁ ρ₂ H) (tbind_ext ⋆ Δ₁ Δ₂ τ0 ρ₁ ρ₂ H)
  | @t_cprod _ ψ τ0 => fun ρ₁ ρ₂ H =>
      f_equal2 (fun a b => @t_cprod Δ₂ a b)
        (cbind_ext Δ₁ Δ₂ ψ ρ₁ ρ₂ H) (tbind_ext ⋆ Δ₁ Δ₂ τ0 ρ₁ ρ₂ H)
  end
with cbind_ext (Δ₁ Δ₂ : Ctx kind) (ψ : constr Δ₁) {struct ψ} :
  forall (ρ₁ ρ₂ : TSub Δ₁ Δ₂),
    (forall v x EQ, ρ₁ v x EQ = ρ₂ v x EQ) -> cbind ρ₁ ψ = cbind ρ₂ ψ :=
  match ψ as ψ' return
    forall (ρ₁ ρ₂ : TSub Δ₁ Δ₂),
      (forall v x EQ, ρ₁ v x EQ = ρ₂ v x EQ) -> cbind ρ₁ ψ' = cbind ρ₂ ψ' with
  | @c_eq _ κ a b => fun ρ₁ ρ₂ H =>
      f_equal2 (fun x y => @c_eq Δ₂ κ x y)
        (tbind_ext κ Δ₁ Δ₂ a ρ₁ ρ₂ H) (tbind_ext κ Δ₁ Δ₂ b ρ₁ ρ₂ H)
  end.


Definition Pirr {Δ₁ Δ₂ : Ctx kind} (ρ : TSub Δ₁ Δ₂) : Prop :=
  forall v (x : dom Δ₁) (e1 e2 : Δ₁ x = v), ρ v x e1 = ρ v x e2.

Lemma liftS_pirr (k : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂) (H : Pirr ρ) :
  Pirr (liftS k ρ).
Proof.
  intros v [|y] e1 e2; simpl.
  - apply t_var_irr.
  - apply f_equal, H.
Qed.

Lemma compSub2_pirr (Δ₁ Δ₂ Δ₃ : Ctx kind) (ρL : @Arr kind Δ₁ Δ₂) (ρR : TSub Δ₂ Δ₃)
      (H : Pirr ρR) : Pirr (compSub2 Δ₁ Δ₂ Δ₃ ρL ρR).
Proof.
  intros v x e1 e2. simpl. apply H.
Qed.

Definition mksubst (κ : kind) {Δ : Ctx kind} (σ : typ κ Δ) : TSub (@extC kind κ Δ) Δ :=
  @mk_subst (Ctx kind) TSub (typ κ) (@extC kind κ)
    (@SubstitutableCore_ext kind (fun k => typ k) IPC_typ κ) Δ σ.

Lemma mk_subst_pirr (κ : kind) (Δ : Ctx kind) (σ : typ κ Δ) :
  Pirr (mksubst κ σ).
Proof.
  intros v [|y] e1 e2; simpl.
  - rewrite (UIP_dec kindEqDec.eq_dec e1 e2). reflexivity.
  - apply t_var_irr.
Qed.

Fixpoint tbind_tmap (κ : kind) (Δ₁ Δ₂ Δ₃ : Ctx kind) (τ : typ κ Δ₁) {struct τ} :
  forall (ρL : @Arr kind Δ₁ Δ₂) (ρR : TSub Δ₂ Δ₃), Pirr ρR ->
    tbind ρR (tmap ρL τ) = tbind (compSub2 Δ₁ Δ₂ Δ₃ ρL ρR) τ :=
  match τ as τ' in type _ κ' return
    forall (ρL : @Arr kind Δ₁ Δ₂) (ρR : TSub Δ₂ Δ₃), Pirr ρR ->
      tbind ρR (tmap ρL τ') = tbind (compSub2 Δ₁ Δ₂ Δ₃ ρL ρR) τ' with
  | @t_var _ κ x EQ => fun ρL ρR H => eq_refl
  | @t_lam _ k1 k2 b => fun ρL ρR H =>
      f_equal t_lam
        (eq_trans
          (tbind_tmap k2 (extC k1 Δ₁) (extC k1 Δ₂) (extC k1 Δ₃) b (liftA k1 ρL) (liftS k1 ρR)
             (liftS_pirr k1 Δ₂ Δ₃ ρR H))
          (tbind_ext k2 (extC k1 Δ₁) (extC k1 Δ₃) b
             (compSub2 (extC k1 Δ₁) (extC k1 Δ₂) (extC k1 Δ₃) (liftA k1 ρL) (liftS k1 ρR))
             (liftS k1 (compSub2 Δ₁ Δ₂ Δ₃ ρL ρR))
             (fun v z EQ => match z as z' return
                 forall (e : (extC k1 Δ₁) z' = v),
                   compSub2 (extC k1 Δ₁) (extC k1 Δ₂) (extC k1 Δ₃) (liftA k1 ρL) (liftS k1 ρR) v z' e
                   = liftS k1 (compSub2 Δ₁ Δ₂ Δ₃ ρL ρR) v z' e with
               | VZ => fun e => t_var_irr v (extC k1 Δ₃) VZ _ _
               | VS y => fun e => f_equal shift (H v (ρL y) _ _)
               end EQ)))
  | @t_app _ k1 k2 σ τ0 => fun ρL ρR H =>
      f_equal2 (fun a b => @t_app Δ₃ k1 k2 a b)
        (tbind_tmap (k1 ⇒ k2) Δ₁ Δ₂ Δ₃ σ ρL ρR H)
        (tbind_tmap k1 Δ₁ Δ₂ Δ₃ τ0 ρL ρR H)
  | @t_ctor _ κ c => fun ρL ρR H => eq_refl
  | @t_carr _ ψ τ0 => fun ρL ρR H =>
      f_equal2 (fun a b => @t_carr Δ₃ a b)
        (cbind_tmap Δ₁ Δ₂ Δ₃ ψ ρL ρR H) (tbind_tmap ⋆ Δ₁ Δ₂ Δ₃ τ0 ρL ρR H)
  | @t_cprod _ ψ τ0 => fun ρL ρR H =>
      f_equal2 (fun a b => @t_cprod Δ₃ a b)
        (cbind_tmap Δ₁ Δ₂ Δ₃ ψ ρL ρR H) (tbind_tmap ⋆ Δ₁ Δ₂ Δ₃ τ0 ρL ρR H)
  end
with cbind_tmap (Δ₁ Δ₂ Δ₃ : Ctx kind) (ψ : constr Δ₁) {struct ψ} :
  forall (ρL : @Arr kind Δ₁ Δ₂) (ρR : TSub Δ₂ Δ₃), Pirr ρR ->
    cbind ρR (cmap ρL ψ) = cbind (compSub2 Δ₁ Δ₂ Δ₃ ρL ρR) ψ :=
  match ψ as ψ' return
    forall (ρL : @Arr kind Δ₁ Δ₂) (ρR : TSub Δ₂ Δ₃), Pirr ρR ->
      cbind ρR (cmap ρL ψ') = cbind (compSub2 Δ₁ Δ₂ Δ₃ ρL ρR) ψ' with
  | @c_eq _ κ a b => fun ρL ρR H =>
      f_equal2 (fun x y => @c_eq Δ₃ κ x y)
        (tbind_tmap κ Δ₁ Δ₂ Δ₃ a ρL ρR H) (tbind_tmap κ Δ₁ Δ₂ Δ₃ b ρL ρR H)
  end.

Lemma compSub_mk_subst (κ : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂)
      (σ : typ κ Δ₁) :
  forall v (x : dom (extC κ Δ₁)) EQ,
    compSub (extC κ Δ₁) Δ₁ Δ₂ ρ (mksubst κ σ) v x EQ
    = compSub2 (extC κ Δ₁) (extC κ Δ₂) Δ₂ (liftA κ ρ) (mksubst κ (tmap ρ σ)) v x EQ.
Proof.
  intros v [|y] EQ; simpl.
  - destruct EQ. reflexivity.
  - apply t_var_irr.
Qed.

Lemma tmap_subst (κ κ' : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂)
      (τ : typ κ' (extC κ Δ₁)) (σ : typ κ Δ₁) :
  tmap ρ (subst τ σ) = subst (tmap (liftA κ ρ) τ) (tmap ρ σ).
Proof.
  change (tmap ρ (tbind (mksubst κ σ) τ)
          = tbind (mksubst κ (tmap ρ σ)) (tmap (liftA κ ρ) τ)).
  etransitivity.
  - apply (tmap_tbind κ' (extC κ Δ₁) Δ₁ Δ₂ τ ρ (mksubst κ σ)
             (compSub (extC κ Δ₁) Δ₁ Δ₂ ρ (mksubst κ σ))).
    intros v x EQ. reflexivity.
  - etransitivity.
    + apply tbind_ext. apply compSub_mk_subst.
    + symmetry.
      apply (tbind_tmap κ' (extC κ Δ₁) (extC κ Δ₂) Δ₂ τ (liftA κ ρ) (mksubst κ (tmap ρ σ))
               (mk_subst_pirr κ Δ₂ (tmap ρ σ))).
Qed.

Lemma tmap_subst_lift (κ κ' : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂)
      (τ : typ κ' (extC κ Δ₁)) (σ : typ κ Δ₁) :
  tmap ρ (subst τ σ) =
  subst (tmap (@lift (Ctx kind) (@Arr kind) (@extC kind κ)
                    (@ALiftableCore_ext kind κ) Δ₁ Δ₂ ρ) τ) (tmap ρ σ).
Proof. apply tmap_subst. Qed.

Lemma cmap_shift_comm (κ : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂) (ψ : constr Δ₁) :
  cmap (liftA κ ρ) (cmap (mkShift κ Δ₁) ψ) = cmap (mkShift κ Δ₂) (cmap ρ ψ).
Proof.
  rewrite cmap_tmap. rewrite cmap_tmap.
  apply cmap_ext. intros x. reflexivity.
Qed.

Lemma tctd_tmap {Δ₁ : Ctx kind} {κ κ' : kind} (σ : typ κ Δ₁) (c : tctor κ') :
  tctd σ c -> forall (Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂), tctd (tmap ρ σ) c.
Proof.
  induction 1; intros Δ₂ ρ; simpl.
  - apply inj_ctor.
  - apply inj_app. apply IHtctd.
Qed.

Definition etaT (κ κ' : kind) {Δ : Ctx kind} (τ : typ (κ ⇒ κ') Δ) : typ (κ ⇒ κ') Δ :=
  t_lam (t_app (shiftt κ τ) (t_var κ (VZ : dom (extC κ Δ)) eq_refl)).

Lemma tmap_eta (κ κ' : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂)
      (τ : typ (κ ⇒ κ') Δ₁) :
  tmap ρ (etaT κ κ' τ) = etaT κ κ' (tmap ρ τ).
Proof.
  change (t_lam (t_app (tmap (liftA κ ρ) (shiftt κ τ))
                        (tmap (liftA κ ρ) (t_var κ (VZ : dom (extC κ Δ₁)) eq_refl)))
          = t_lam (t_app (shiftt κ (tmap ρ τ)) (t_var κ (VZ : dom (extC κ Δ₂)) eq_refl))).
  f_equal.
  rewrite (tmap_shift_comm κ (κ ⇒ κ') Δ₁ Δ₂ ρ τ).
  reflexivity.
Qed.

Definition shiftC (κ : kind) (Δ : Ctx kind) (ψ : constr Δ) : constr (@extC kind κ Δ) :=
  cmap (mkShift κ Δ) ψ.

Lemma map_shift_cmap (κ : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂)
      (Ψ : list (constr Δ₁)) :
  map (cmap (liftA κ ρ)) (map (shiftC κ Δ₁) Ψ) = map (shiftC κ Δ₂) (map (cmap ρ) Ψ).
Proof.
  rewrite List.map_map. rewrite List.map_map.
  apply List.map_ext. intro ψ. apply cmap_shift_comm.
Qed.

Lemma tproves_tmap (Δ₁ : Ctx kind) (Ψ : list (constr Δ₁)) (ψ : constr Δ₁) :
  Ψ ⊩ ψ -> forall (Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂), map (cmap ρ) Ψ ⊩ cmap ρ ψ.
Proof.
  intros H.
  induction H using tproves_i_ind.
  - (* ax *) intros Δ₂ ρ. apply tpi_ax. apply List.in_map. assumption.
  - (* var *) intros Δ₂ ρ. apply tpi_var.
  - (* lam *) intros Δ₂ ρ. eapply tpi_lam. rewrite <- map_shift_cmap. eauto.
  - (* app *) intros Δ₂ ρ. eapply tpi_app; eauto.
  - (* ctor *) intros Δ₂ ρ. apply tpi_ctor.
  - (* carr *) intros Δ₂ ρ. eapply tpi_carr; eauto.
  - (* cprod *) intros Δ₂ ρ. eapply tpi_cprod; eauto.
  - (* symm *) intros Δ₂ ρ. eapply tpi_symm; eauto.
  - (* trans *) intros Δ₂ ρ. eapply tpi_trans; eauto.
  - (* eta *) intros Δ₂ ρ.
    change (map (cmap ρ) Ψ ⊩ c_eq (κₐ ⇒ κᵣ) (tmap ρ τ) (tmap ρ (etaT κₐ κᵣ τ))).
    rewrite (tmap_eta κₐ κᵣ _ Δ₂ ρ τ). apply tpi_eta.
  - (* beta *) intros Δ₂ ρ.
    change (map (cmap ρ) Ψ ⊩ c_eq κᵣ (tmap ρ (t_app (t_lam τ) σ)) (tmap ρ (subst τ σ))).
    rewrite (tmap_subst κₐ κᵣ _ Δ₂ ρ τ σ). apply tpi_beta.
  - (* appInjR *) intros Δ₂ ρ.
    exact (tpi_appInjR (tctd_tmap σ₁ c HI₁ Δ₂ ρ) (tctd_tmap σ₂ c HI₂ Δ₂ ρ)
             (IHtproves_i Δ₂ ρ)).
  - (* appInjL *) intros Δ₂ ρ.
    exact (tpi_appInjL (tctd_tmap σ₁ c HI₁ Δ₂ ρ) (tctd_tmap σ₂ c HI₂ Δ₂ ρ)
             (IHtproves_i Δ₂ ρ)).
  - (* carrInjR *) intros Δ₂ ρ. exact (tpi_carrInjR (IHtproves_i Δ₂ ρ)).
  - (* cprodInjR *) intros Δ₂ ρ. exact (tpi_cprodInjR (IHtproves_i Δ₂ ρ)).
  - (* cprodInjL *) intros Δ₂ ρ.
    exact (tpi_cprodInjL (IHtproves_i1 Δ₂ ρ) (IHtproves_i2 Δ₂ ρ)).
  - (* carrInjL *) intros Δ₂ ρ.
    exact (tpi_carrInjL (IHtproves_i1 Δ₂ ρ) (IHtproves_i2 Δ₂ ρ)).
Qed.

Lemma tdiscr_cmap (Δ₁ : Ctx kind) (ψ : constr Δ₁) : ⊮ ψ ->
  forall (Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂), ⊮ cmap ρ ψ.
Proof.
  induction 1; intros Δ₂ ρ; simpl.
  - eapply td_ctd.
    + exact (tctd_tmap τ₁ c₁ HI₁ Δ₂ ρ).
    + exact (tctd_tmap τ₂ c₂ HI₂ Δ₂ ρ).
    + exact HD.
  - eapply td_carr_ctd. exact (tctd_tmap σ c HI Δ₂ ρ).
  - eapply td_ctd_carr. exact (tctd_tmap σ c HI Δ₂ ρ).
  - eapply td_cprod_ctd. exact (tctd_tmap σ c HI Δ₂ ρ).
  - eapply td_ctd_cprod. exact (tctd_tmap σ c HI Δ₂ ρ).
  - eapply td_carr_cprod.
  - eapply td_cprod_carr.
Qed.

Lemma rel_app_tmap {Δ₁ : Ctx kind} {κ₁ : kind} (σ₁ σ₂ : typ κ₁ Δ₁)
      {κ₂ : kind} (τ₁ τ₂ : typ κ₂ Δ₁) :
  rel_app κ₁ σ₁ σ₂ κ₂ τ₁ τ₂ ->
  forall (Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂),
    rel_app κ₁ (tmap ρ σ₁) (tmap ρ σ₂) κ₂ (tmap ρ τ₁) (tmap ρ τ₂).
Proof.
  induction 1; intros Δ₂ ρ; simpl.
  - apply rel_app_refl.
  - eapply rel_app_app; eauto.
Qed.

Lemma rel_app_tmap_rec {Δ : Ctx kind} {κ : kind} (τ : typ κ (extC κ Δ))
      (σ₁ σ₂ : typ ⋆ Δ) :
  rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂ ->
  forall (Δ₂ : Ctx kind) (ρ : @Arr kind Δ Δ₂),
    rel_app κ (rec_type Δ₂ κ (tmap (liftA κ ρ) τ))
              (subst (tmap (liftA κ ρ) τ) (rec_type Δ₂ κ (tmap (liftA κ ρ) τ)))
              ⋆ (tmap ρ σ₁) (tmap ρ σ₂).
Proof.
  intros H Δ₂ ρ.
  pose proof (rel_app_tmap (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ))
                σ₁ σ₂ H Δ₂ ρ) as HR.
  rewrite (tmap_subst κ κ Δ Δ₂ ρ τ (rec_type Δ κ τ)) in HR.
  exact HR.
Qed.

Lemma ctx_lift_eq {V : Set} {Δ : Ctx kind} {Γ₁ Γ₂ : V -> typ ⋆ Δ}
      (H : forall x, Γ₁ x = Γ₂ x) (σ : typ ⋆ Δ) :
  forall y : inc V, (Γ₁ ▹ σ) y = (Γ₂ ▹ σ) y.
Proof. intros [|x]; simpl; [reflexivity| apply H]. Qed.

Lemma ctx_lift2_eq {V : Set} {Δ : Ctx kind} {Γ₁ Γ₂ : V -> typ ⋆ Δ}
      (H : forall x, Γ₁ x = Γ₂ x) (σ τ : typ ⋆ Δ) :
  forall y : inc (inc V), ((Γ₁ ▹ σ) ▹ τ) y = ((Γ₂ ▹ σ) ▹ τ) y.
Proof. intros [|[|x]]; simpl; try reflexivity; apply H. Qed.

Lemma ctx_shift_eq {V : Set} {Δ : Ctx kind} {Γ₁ Γ₂ : V -> typ ⋆ Δ}
      (H : forall x, Γ₁ x = Γ₂ x) (κ : kind) :
  forall y : V, (Env.compose (shiftt κ) Γ₁) y = (Env.compose (shiftt κ) Γ₂) y.
Proof. intro y. simpl. apply f_equal, H. Qed.

Lemma ctx_shift_extend_eq {V : Set} {Δ : Ctx kind} {Γ₁ Γ₂ : V -> typ ⋆ Δ}
      (H : forall x, Γ₁ x = Γ₂ x) (κ : kind) (σ : typ ⋆ (@extC kind κ Δ)) :
  forall y : inc V,
    (Env.extend (Env.compose (shiftt κ) Γ₁) σ) y =
    (Env.extend (Env.compose (shiftt κ) Γ₂) σ) y.
Proof. intros [|x]; simpl; [reflexivity| apply f_equal, H]. Qed.

Lemma typing_ctx_congr_mut :
  (forall (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ₁ : V -> typ ⋆ Δ)
          (e : expr V) (τ : typ ⋆ Δ), Δ ∣ Ψ ∣ Γ₁ ⊢ₑ e : τ ->
   forall (Γ₂ : V -> typ ⋆ Δ), (forall x, Γ₁ x = Γ₂ x) -> Δ ∣ Ψ ∣ Γ₂ ⊢ₑ e : τ)
  /\
  (forall (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ₁ : V -> typ ⋆ Δ)
          (v : value V) (τ : typ ⋆ Δ), Δ ∣ Ψ ∣ Γ₁ ⊢ᵥ v : τ ->
   forall (Γ₂ : V -> typ ⋆ Δ), (forall x, Γ₁ x = Γ₂ x) -> Δ ∣ Ψ ∣ Γ₂ ⊢ᵥ v : τ).
Proof.
  assert (HE : forall (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ₁ : V -> typ ⋆ Δ)
          (e : expr V) (τ : typ ⋆ Δ), Δ ∣ Ψ ∣ Γ₁ ⊢ₑ e : τ ->
   forall (Γ₂ : V -> typ ⋆ Δ), (forall x, Γ₁ x = Γ₂ x) -> Δ ∣ Ψ ∣ Γ₂ ⊢ₑ e : τ).
  { intros V Δ Ψ Γ₁ e τ H.
    induction H using typing_expr_mut with
      (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
                 (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (Γ₂ : V -> typ ⋆ Δ), (forall x, Γ x = Γ₂ x) -> Δ ∣ Ψ ∣ Γ₂ ⊢ₑ e : τ)
      (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
                 (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ) =>
             forall (Γ₂ : V -> typ ⋆ Δ), (forall x, Γ x = Γ₂ x) -> Δ ∣ Ψ ∣ Γ₂ ⊢ᵥ v : τ).
    - intros Γ₂ H2. apply T_val. eauto.
    - intros Γ₂ H2. eapply T_bind; eauto 12 using ctx_lift_eq.
    - intros Γ₂ H2. eapply T_congE; eauto.
    - intros Γ₂ H2. eapply T_app; eauto.
    - intros Γ₂ H2. eapply T_tapp; eauto.
    - intros Γ₂ H2. eapply T_projL; eauto.
    - intros Γ₂ H2. eapply T_projR; eauto.
    - intros Γ₂ H2. eapply T_abort; eauto.
    - intros Γ₂ H2. eapply T_case; eauto 12 using ctx_lift_eq.
    - intros Γ₂ H2. eapply T_unpack; eauto 12 using ctx_shift_extend_eq.
    - intros Γ₂ H2. eapply T_unroll; eauto.
    - intros Γ₂ H2. eapply T_cabort; eauto.
    - intros Γ₂ H2. eapply T_capp; eauto.
    - intros Γ₂ H2. eapply T_lwith; eauto 12 using ctx_lift_eq.
    - intros Γ₂ H2. apply T_var. apply (eq_trans (eq_sym (H2 x)) EQ).
    - intros Γ₂ H2. eapply T_congV; eauto.
    - intros Γ₂ H2. apply T_unit.
    - intros Γ₂ H2. eapply T_lam; eauto 12 using ctx_lift_eq.
    - intros Γ₂ H2. eapply T_pair; eauto.
    - intros Γ₂ H2. eapply T_injl; eauto.
    - intros Γ₂ H2. eapply T_injr; eauto.
    - intros Γ₂ H2. eapply T_tlam; eauto 12 using ctx_shift_eq.
    - intros Γ₂ H2. eapply T_pack; eauto.
    - intros Γ₂ H2. eapply T_roll; eauto.
    - intros Γ₂ H2. eapply T_lamC; eauto.
    - intros Γ₂ H2. eapply T_withC; eauto.
    - intros Γ₂ H2. eapply T_rec; eauto 12 using ctx_lift2_eq. }
  split; [ exact HE | ].
  intros V Δ Ψ Γ₁ v τ H.
  induction H using typing_val_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
           forall (Γ₂ : V -> typ ⋆ Δ), (forall x, Γ x = Γ₂ x) -> Δ ∣ Ψ ∣ Γ₂ ⊢ₑ e : τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ) =>
           forall (Γ₂ : V -> typ ⋆ Δ), (forall x, Γ x = Γ₂ x) -> Δ ∣ Ψ ∣ Γ₂ ⊢ᵥ v : τ).
  - intros Γ₂ H2. apply T_val. eauto.
  - intros Γ₂ H2. eapply T_bind; eauto 12 using ctx_lift_eq.
  - intros Γ₂ H2. eapply T_congE; eauto.
  - intros Γ₂ H2. eapply T_app; eauto.
  - intros Γ₂ H2. eapply T_tapp; eauto.
  - intros Γ₂ H2. eapply T_projL; eauto.
  - intros Γ₂ H2. eapply T_projR; eauto.
  - intros Γ₂ H2. eapply T_abort; eauto.
  - intros Γ₂ H2. eapply T_case; eauto 12 using ctx_lift_eq.
  - intros Γ₂ H2. eapply T_unpack; eauto 12 using ctx_shift_extend_eq.
  - intros Γ₂ H2. eapply T_unroll; eauto.
  - intros Γ₂ H2. eapply T_cabort; eauto.
  - intros Γ₂ H2. eapply T_capp; eauto.
  - intros Γ₂ H2. eapply T_lwith; eauto 12 using ctx_lift_eq.
  - intros Γ₂ H2. apply T_var. apply (eq_trans (eq_sym (H2 x)) EQ).
  - intros Γ₂ H2. eapply T_congV; eauto.
  - intros Γ₂ H2. apply T_unit.
  - intros Γ₂ H2. eapply T_lam; eauto 12 using ctx_lift_eq.
  - intros Γ₂ H2. eapply T_pair; eauto.
  - intros Γ₂ H2. eapply T_injl; eauto.
  - intros Γ₂ H2. eapply T_injr; eauto.
  - intros Γ₂ H2. eapply T_tlam; eauto 12 using ctx_shift_eq.
  - intros Γ₂ H2. eapply T_pack; eauto.
  - intros Γ₂ H2. eapply T_roll; eauto.
  - intros Γ₂ H2. eapply T_lamC; eauto.
  - intros Γ₂ H2. eapply T_withC; eauto.
  - intros Γ₂ H2. eapply T_rec; eauto 12 using ctx_lift2_eq.
Qed.

Definition typing_expr_congr := proj1 typing_ctx_congr_mut.
Definition typing_val_congr := proj2 typing_ctx_congr_mut.

Ltac sih :=
  multimatch goal with
  | H : forall (Δ₂ : Ctx kind), _ |- _ => exact (H _ _)
  end.

Lemma typing_tren_mut :
  (forall (V : Set) (Δ₁ : Ctx kind) (Ψ : list (constr Δ₁)) (Γ : V -> typ ⋆ Δ₁)
          (e : expr V) (τ : typ ⋆ Δ₁), Δ₁ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
   forall (Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂),
     Δ₂ ∣ map (cmap ρ) Ψ ∣ (fun x => tmap ρ (Γ x)) ⊢ₑ e : tmap ρ τ)
  /\
  (forall (V : Set) (Δ₁ : Ctx kind) (Ψ : list (constr Δ₁)) (Γ : V -> typ ⋆ Δ₁)
          (v : value V) (τ : typ ⋆ Δ₁), Δ₁ ∣ Ψ ∣ Γ ⊢ᵥ v : τ ->
   forall (Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂),
     Δ₂ ∣ map (cmap ρ) Ψ ∣ (fun x => tmap ρ (Γ x)) ⊢ᵥ v : tmap ρ τ).
Proof.
  assert (HE : forall (V : Set) (Δ₁ : Ctx kind) (Ψ : list (constr Δ₁)) (Γ : V -> typ ⋆ Δ₁)
          (e : expr V) (τ : typ ⋆ Δ₁), Δ₁ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
   forall (Δ₂ : Ctx kind) (ρ : @Arr kind Δ₁ Δ₂),
     Δ₂ ∣ map (cmap ρ) Ψ ∣ (fun x => tmap ρ (Γ x)) ⊢ₑ e : tmap ρ τ).
  { intros V Δ₁ Ψ Γ e τ H.
    induction H using typing_expr_mut with
      (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
                 (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (Δ₂ : Ctx kind) (ρ : @Arr kind Δ Δ₂),
               Δ₂ ∣ map (cmap ρ) Ψ ∣ (fun x => tmap ρ (Γ x)) ⊢ₑ e : tmap ρ τ)
      (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
                 (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ) =>
             forall (Δ₂ : Ctx kind) (ρ : @Arr kind Δ Δ₂),
               Δ₂ ∣ map (cmap ρ) Ψ ∣ (fun x => tmap ρ (Γ x)) ⊢ᵥ v : tmap ρ τ).
    - (* T_val *) intros Δ₂ ρ. eapply T_val.
      sih.
    - (* T_bind *) intros Δ₂ ρ. eapply T_bind.
      + sih.
      + eapply typing_expr_congr.
        * sih.
        * intros [|x]; simpl; reflexivity.
    - (* T_congE *) intros Δ₂ ρ. eapply T_congE.
      + apply (tproves_tmap Δ Ψ (@c_eq Δ ⋆ τ τ')). assumption.
      + sih.
    - (* T_app *) intros Δ₂ ρ. eapply T_app.
      + sih.
      + sih.
    - (* T_tapp *) intros Δ₂ ρ. rewrite (tmap_subst κ ⋆ _ Δ₂ ρ τ σ). eapply T_tapp.
      sih.
    - (* T_projL *) intros Δ₂ ρ. eapply T_projL.
      sih.
    - (* T_projR *) intros Δ₂ ρ. eapply T_projR.
      sih.
    - (* T_abort *) intros Δ₂ ρ. eapply T_abort.
      sih.
    - (* T_case *) intros Δ₂ ρ. eapply T_case.
      + eapply typing_expr_congr.
        * sih.
        * intros [|x]; simpl; reflexivity.
      + eapply typing_expr_congr.
        * sih.
        * intros [|x]; simpl; reflexivity.
      + sih.
    - (* T_unpack *) intros Δ₂ ρ. eapply T_unpack.
      + sih.
      + rewrite <- map_shift_cmap.
        eapply typing_expr_congr.
        * rewrite shift_is_shiftt. rewrite <- tmap_shift_comm. sih.
        * intros [|x]; simpl.
          -- reflexivity.
          -- rewrite shift_is_shiftt. rewrite tmap_shift_comm. reflexivity.
    - (* T_unroll *) intros Δ₂ ρ. eapply T_unroll.
      + exact (rel_app_tmap_rec τ σ₁ σ₂ HF Δ₂ ρ).
      + sih.
    - (* T_cabort *) intros Δ₂ ρ. eapply T_cabort.
      + apply tproves_tmap. eassumption.
      + eapply tdiscr_cmap. assumption.
    - (* T_capp *) intros Δ₂ ρ. eapply T_capp.
      + apply tproves_tmap. eassumption.
      + sih.
    - (* T_lwith *) intros Δ₂ ρ. eapply T_lwith.
      + sih.
      + eapply typing_expr_congr.
        * sih.
        * intros [|x]; simpl; reflexivity.
    - (* T_var *) intros Δ₂ ρ. apply T_var. simpl. rewrite EQ. reflexivity.
    - (* T_congV *) intros Δ₂ ρ. eapply T_congV.
      + apply (tproves_tmap Δ Ψ (@c_eq Δ ⋆ τ τ')). assumption.
      + sih.
    - (* T_unit *) intros Δ₂ ρ. apply T_unit.
    - (* T_lam *) intros Δ₂ ρ. eapply T_lam.
      eapply typing_expr_congr.
      * sih.
      * intros [|x]; simpl; reflexivity.
    - (* T_pair *) intros Δ₂ ρ. eapply T_pair.
      + sih.
      + sih.
    - (* T_injl *) intros Δ₂ ρ. eapply T_injl.
      sih.
    - (* T_injr *) intros Δ₂ ρ. eapply T_injr.
      sih.
    - (* T_tlam *) intros Δ₂ ρ. eapply T_tlam.
      rewrite <- map_shift_cmap.
      eapply typing_expr_congr.
      * sih.
      * intro x. simpl. rewrite shift_is_shiftt. rewrite tmap_shift_comm. reflexivity.
    - (* T_pack *) intros Δ₂ ρ.
      refine (@T_pack V Δ₂ (map (cmap ρ) Ψ) (fun x => tmap ρ (Γ x)) κ
                (tmap (@lift (Ctx kind) (@Arr kind) (@extC kind κ)
                             (@ALiftableCore_ext kind κ) Δ Δ₂ ρ) τ)
                (tmap ρ τ') v _).
      rewrite <- (tmap_subst_lift κ ⋆ Δ Δ₂ ρ τ τ'). sih.
    - (* T_roll *) intros Δ₂ ρ. eapply T_roll.
      + exact (rel_app_tmap_rec τ σ₁ σ₂ HF Δ₂ ρ).
      + sih.
    - (* T_lamC *) intros Δ₂ ρ. eapply T_lamC.
      sih.
    - (* T_withC *) intros Δ₂ ρ. eapply T_withC.
      + sih.
      + apply tproves_tmap. eassumption.
    - (* T_rec *) intros Δ₂ ρ. eapply T_rec.
      eapply typing_expr_congr.
      * sih.
      * intros [|[|x]]; simpl; reflexivity.
  }
  split; [ exact HE | ].
  intros V Δ₁ Ψ Γ v τ H.
  induction H using typing_val_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
           forall (Δ₂ : Ctx kind) (ρ : @Arr kind Δ Δ₂),
             Δ₂ ∣ map (cmap ρ) Ψ ∣ (fun x => tmap ρ (Γ x)) ⊢ₑ e : tmap ρ τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ) =>
           forall (Δ₂ : Ctx kind) (ρ : @Arr kind Δ Δ₂),
             Δ₂ ∣ map (cmap ρ) Ψ ∣ (fun x => tmap ρ (Γ x)) ⊢ᵥ v : tmap ρ τ).
  - (* T_val *) intros Δ₂ ρ. eapply T_val.
    sih.
  - (* T_bind *) intros Δ₂ ρ. eapply T_bind.
    + sih.
    + eapply typing_expr_congr.
      * sih.
      * intros [|x]; simpl; reflexivity.
  - (* T_congE *) intros Δ₂ ρ. eapply T_congE.
    + apply (tproves_tmap Δ Ψ (@c_eq Δ ⋆ τ τ')). assumption.
    + sih.
  - (* T_app *) intros Δ₂ ρ. eapply T_app.
    + sih.
    + sih.
  - (* T_tapp *) intros Δ₂ ρ. rewrite (tmap_subst κ ⋆ _ Δ₂ ρ τ σ). eapply T_tapp.
    sih.
  - (* T_projL *) intros Δ₂ ρ. eapply T_projL.
    sih.
  - (* T_projR *) intros Δ₂ ρ. eapply T_projR.
    sih.
  - (* T_abort *) intros Δ₂ ρ. eapply T_abort.
    sih.
  - (* T_case *) intros Δ₂ ρ. eapply T_case.
    + eapply typing_expr_congr.
      * sih.
      * intros [|x]; simpl; reflexivity.
    + eapply typing_expr_congr.
      * sih.
      * intros [|x]; simpl; reflexivity.
    + sih.
  - (* T_unpack *) intros Δ₂ ρ. eapply T_unpack.
    + sih.
    + rewrite <- map_shift_cmap.
      eapply typing_expr_congr.
      * rewrite shift_is_shiftt. rewrite <- tmap_shift_comm. sih.
      * intros [|x]; simpl.
        -- reflexivity.
        -- rewrite shift_is_shiftt. rewrite tmap_shift_comm. reflexivity.
  - (* T_unroll *) intros Δ₂ ρ. eapply T_unroll.
    + exact (rel_app_tmap_rec τ σ₁ σ₂ HF Δ₂ ρ).
    + sih.
  - (* T_cabort *) intros Δ₂ ρ. eapply T_cabort.
    + apply tproves_tmap. eassumption.
    + eapply tdiscr_cmap. assumption.
  - (* T_capp *) intros Δ₂ ρ. eapply T_capp.
    + apply tproves_tmap. eassumption.
    + sih.
  - (* T_lwith *) intros Δ₂ ρ. eapply T_lwith.
    + sih.
    + eapply typing_expr_congr.
      * sih.
      * intros [|x]; simpl; reflexivity.
  - (* T_var *) intros Δ₂ ρ. apply T_var. simpl. rewrite EQ. reflexivity.
  - (* T_congV *) intros Δ₂ ρ. eapply T_congV.
    + apply (tproves_tmap Δ Ψ (@c_eq Δ ⋆ τ τ')). assumption.
    + sih.
  - (* T_unit *) intros Δ₂ ρ. apply T_unit.
  - (* T_lam *) intros Δ₂ ρ. eapply T_lam.
    eapply typing_expr_congr.
    * sih.
    * intros [|x]; simpl; reflexivity.
  - (* T_pair *) intros Δ₂ ρ. eapply T_pair.
    + sih.
    + sih.
  - (* T_injl *) intros Δ₂ ρ. eapply T_injl.
    sih.
  - (* T_injr *) intros Δ₂ ρ. eapply T_injr.
    sih.
  - (* T_tlam *) intros Δ₂ ρ. eapply T_tlam.
    rewrite <- map_shift_cmap.
    eapply typing_expr_congr.
    * sih.
    * intro x. simpl. rewrite shift_is_shiftt. rewrite tmap_shift_comm. reflexivity.
  - (* T_pack *) intros Δ₂ ρ.
    refine (@T_pack V Δ₂ (map (cmap ρ) Ψ) (fun x => tmap ρ (Γ x)) κ
              (tmap (@lift (Ctx kind) (@Arr kind) (@extC kind κ)
                           (@ALiftableCore_ext kind κ) Δ Δ₂ ρ) τ)
              (tmap ρ τ') v _).
    rewrite <- (tmap_subst_lift κ ⋆ Δ Δ₂ ρ τ τ'). sih.
  - (* T_roll *) intros Δ₂ ρ. eapply T_roll.
    + exact (rel_app_tmap_rec τ σ₁ σ₂ HF Δ₂ ρ).
    + sih.
  - (* T_lamC *) intros Δ₂ ρ. eapply T_lamC.
    sih.
  - (* T_withC *) intros Δ₂ ρ. eapply T_withC.
    + sih.
    + apply tproves_tmap. eassumption.
  - (* T_rec *) intros Δ₂ ρ. eapply T_rec.
    eapply typing_expr_congr.
    * sih.
    * intros [|[|x]]; simpl; reflexivity.
Qed.

Definition compSS (Δ₁ Δ₂ Δ₃ : Ctx kind) (ρ₁ : TSub Δ₁ Δ₂) (ρ₂ : TSub Δ₂ Δ₃) : TSub Δ₁ Δ₃ :=
  @Build_Sub kind (fun κ => typ κ) IPC_typ Δ₁ Δ₃
    (fun v x EQ => tbind ρ₂ (ρ₁ v x EQ)).

Lemma tmap_liftA_shiftt (k1 κ : kind) (Δ : Ctx kind) (κ' : kind) (τ : typ κ' Δ) :
  tmap (liftA k1 (mkShift κ Δ)) (shiftt k1 τ) = shiftt k1 (shiftt κ τ).
Proof.
  rewrite tmap_shift_comm.
  rewrite <- shiftt_eq.
  reflexivity.
Qed.

Lemma compat_shift_lift2 (κ k1 : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂) (Hρ : Pirr ρ) :
  forall v (z : dom (extC k1 Δ₁)) EQ,
    compSub2 (extC k1 Δ₁) (extC k1 (extC κ Δ₁)) (extC k1 (extC κ Δ₂))
             (liftA k1 (mkShift κ Δ₁)) (liftS k1 (liftS κ ρ)) v z EQ
    = compSub (extC k1 Δ₁) (extC k1 Δ₂) (extC k1 (extC κ Δ₂))
              (liftA k1 (mkShift κ Δ₂)) (liftS k1 ρ) v z EQ.
Proof.
  intros v [|y] EQ; simpl.
  - apply t_var_irr.
  - assert (Hp : ρ v y (eq_trans eq_refl EQ) = ρ v y EQ) by apply Hρ.
    refine (eq_trans (f_equal (fun u => shiftt k1 (shiftt κ u)) Hp) _).
    change (shiftt k1 (shiftt κ (ρ v y EQ))
            = tmap (liftA k1 (mkShift κ Δ₂)) (shiftt k1 (ρ v y EQ))).
    rewrite tmap_liftA_shiftt. reflexivity.
Qed.

Fixpoint tbind_shift_comm (κ : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂) (Hρ : Pirr ρ)
                         (κ' : kind) (τ : typ κ' Δ₁) {struct τ} :
  tbind (liftS κ ρ) (shiftt κ τ) = shiftt κ (tbind ρ τ) :=
  match τ as τ' in type _ k return
    tbind (liftS κ ρ) (shiftt κ τ') = shiftt κ (tbind ρ τ') with
  | @t_var _ k x EQ =>
      ltac:(simpl;
        assert (Hp : ρ k x (eq_trans (Intrinsic.ShiftableCore_ext_obligation_1 κ Δ₁ x) EQ) = ρ k x EQ)
          by apply Hρ;
        exact (eq_trans (f_equal (fun u => shift u) Hp)
                (@shift_is_shiftt κ k Δ₂ (ρ k x EQ))))
  | @t_lam _ k1 k2 b =>
      f_equal t_lam
        (eq_trans
          (tbind_tmap k2 (extC k1 Δ₁) (extC k1 (extC κ Δ₁)) (extC k1 (extC κ Δ₂))
             b (liftA k1 (mkShift κ Δ₁)) (liftS k1 (liftS κ ρ))
             (liftS_pirr k1 (extC κ Δ₁) (extC κ Δ₂) (liftS κ ρ)
                (liftS_pirr κ Δ₁ Δ₂ ρ Hρ)))
          (eq_trans
            (tbind_ext k2 (extC k1 Δ₁) (extC k1 (extC κ Δ₂)) b
               (compSub2 (extC k1 Δ₁) (extC k1 (extC κ Δ₁)) (extC k1 (extC κ Δ₂))
                  (liftA k1 (mkShift κ Δ₁)) (liftS k1 (liftS κ ρ)))
               (compSub (extC k1 Δ₁) (extC k1 Δ₂) (extC k1 (extC κ Δ₂))
                  (liftA k1 (mkShift κ Δ₂)) (liftS k1 ρ))
               (compat_shift_lift2 κ k1 Δ₁ Δ₂ ρ Hρ))
            (eq_sym (tmap_tbind k2 (extC k1 Δ₁) (extC k1 Δ₂) (extC k1 (extC κ Δ₂))
               b (liftA k1 (mkShift κ Δ₂)) (liftS k1 ρ)
               (compSub (extC k1 Δ₁) (extC k1 Δ₂) (extC k1 (extC κ Δ₂))
                  (liftA k1 (mkShift κ Δ₂)) (liftS k1 ρ))
               (fun v x EQ => eq_refl)))))
  | @t_app _ k1 k2 σ τ0 =>
      f_equal2 (fun a b => @t_app (@extC kind κ Δ₂) k1 k2 a b)
        (tbind_shift_comm κ Δ₁ Δ₂ ρ Hρ (k1 ⇒ k2) σ)
        (tbind_shift_comm κ Δ₁ Δ₂ ρ Hρ k1 τ0)
  | @t_ctor _ k c => eq_refl
  | @t_carr _ ψ τ0 =>
      f_equal2 (fun a b => @t_carr (@extC kind κ Δ₂) a b)
        (cbind_shift_comm κ Δ₁ Δ₂ ρ Hρ ψ)
        (tbind_shift_comm κ Δ₁ Δ₂ ρ Hρ ⋆ τ0)
  | @t_cprod _ ψ τ0 =>
      f_equal2 (fun a b => @t_cprod (@extC kind κ Δ₂) a b)
        (cbind_shift_comm κ Δ₁ Δ₂ ρ Hρ ψ)
        (tbind_shift_comm κ Δ₁ Δ₂ ρ Hρ ⋆ τ0)
  end
with cbind_shift_comm (κ : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂) (Hρ : Pirr ρ)
                      (ψ : constr Δ₁) {struct ψ} :
  cbind (liftS κ ρ) (cmap (mkShift κ Δ₁) ψ) = cmap (mkShift κ Δ₂) (cbind ρ ψ) :=
  match ψ as ψ' return
    cbind (liftS κ ρ) (cmap (mkShift κ Δ₁) ψ') = cmap (mkShift κ Δ₂) (cbind ρ ψ') with
  | @c_eq _ k a b =>
      f_equal2 (fun x y => @c_eq (@extC kind κ Δ₂) k x y)
        (tbind_shift_comm κ Δ₁ Δ₂ ρ Hρ k a)
        (tbind_shift_comm κ Δ₁ Δ₂ ρ Hρ k b)
  end.


Lemma liftS_compSS (k : kind) (Δ₁ Δ₂ Δ₃ : Ctx kind)
      (ρ₁ : TSub Δ₁ Δ₂) (ρ₂ : TSub Δ₂ Δ₃) (H₁ : Pirr ρ₁) (H₂ : Pirr ρ₂) :
  forall v (z : dom (extC k Δ₁)) EQ,
    compSS (extC k Δ₁) (extC k Δ₂) (extC k Δ₃) (liftS k ρ₁) (liftS k ρ₂) v z EQ
    = liftS k (compSS Δ₁ Δ₂ Δ₃ ρ₁ ρ₂) v z EQ.
Proof.
  intros v [|y] EQ; simpl.
  - apply t_var_irr.
  - change (tbind (liftS k ρ₂) (shiftt k (ρ₁ v y EQ))
            = shiftt k (tbind ρ₂ (ρ₁ v y EQ))).
    apply tbind_shift_comm. exact H₂.
Qed.

Fixpoint tbind_tbind (κ : kind) (Δ₁ Δ₂ Δ₃ : Ctx kind) (τ : typ κ Δ₁) {struct τ} :
  forall (ρ₁ : TSub Δ₁ Δ₂) (ρ₂ : TSub Δ₂ Δ₃), Pirr ρ₁ -> Pirr ρ₂ ->
    tbind ρ₂ (tbind ρ₁ τ) = tbind (compSS Δ₁ Δ₂ Δ₃ ρ₁ ρ₂) τ :=
  match τ as τ' in type _ k return
    forall (ρ₁ : TSub Δ₁ Δ₂) (ρ₂ : TSub Δ₂ Δ₃), Pirr ρ₁ -> Pirr ρ₂ ->
      tbind ρ₂ (tbind ρ₁ τ') = tbind (compSS Δ₁ Δ₂ Δ₃ ρ₁ ρ₂) τ' with
  | @t_var _ k x EQ => fun ρ₁ ρ₂ H₁ H₂ => eq_refl
  | @t_lam _ k1 k2 b => fun ρ₁ ρ₂ H₁ H₂ =>
      f_equal t_lam
        (eq_trans
          (tbind_tbind k2 (extC k1 Δ₁) (extC k1 Δ₂) (extC k1 Δ₃) b
             (liftS k1 ρ₁) (liftS k1 ρ₂)
             (liftS_pirr k1 Δ₁ Δ₂ ρ₁ H₁) (liftS_pirr k1 Δ₂ Δ₃ ρ₂ H₂))
          (tbind_ext k2 (extC k1 Δ₁) (extC k1 Δ₃) b
             (compSS (extC k1 Δ₁) (extC k1 Δ₂) (extC k1 Δ₃) (liftS k1 ρ₁) (liftS k1 ρ₂))
             (liftS k1 (compSS Δ₁ Δ₂ Δ₃ ρ₁ ρ₂))
             (liftS_compSS k1 Δ₁ Δ₂ Δ₃ ρ₁ ρ₂ H₁ H₂)))
  | @t_app _ k1 k2 σ τ0 => fun ρ₁ ρ₂ H₁ H₂ =>
      f_equal2 (fun a b => @t_app Δ₃ k1 k2 a b)
        (tbind_tbind (k1 ⇒ k2) Δ₁ Δ₂ Δ₃ σ ρ₁ ρ₂ H₁ H₂)
        (tbind_tbind k1 Δ₁ Δ₂ Δ₃ τ0 ρ₁ ρ₂ H₁ H₂)
  | @t_ctor _ k c => fun ρ₁ ρ₂ H₁ H₂ => eq_refl
  | @t_carr _ ψ τ0 => fun ρ₁ ρ₂ H₁ H₂ =>
      f_equal2 (fun a b => @t_carr Δ₃ a b)
        (cbind_tbind Δ₁ Δ₂ Δ₃ ψ ρ₁ ρ₂ H₁ H₂)
        (tbind_tbind ⋆ Δ₁ Δ₂ Δ₃ τ0 ρ₁ ρ₂ H₁ H₂)
  | @t_cprod _ ψ τ0 => fun ρ₁ ρ₂ H₁ H₂ =>
      f_equal2 (fun a b => @t_cprod Δ₃ a b)
        (cbind_tbind Δ₁ Δ₂ Δ₃ ψ ρ₁ ρ₂ H₁ H₂)
        (tbind_tbind ⋆ Δ₁ Δ₂ Δ₃ τ0 ρ₁ ρ₂ H₁ H₂)
  end
with cbind_tbind (Δ₁ Δ₂ Δ₃ : Ctx kind) (ψ : constr Δ₁) {struct ψ} :
  forall (ρ₁ : TSub Δ₁ Δ₂) (ρ₂ : TSub Δ₂ Δ₃), Pirr ρ₁ -> Pirr ρ₂ ->
    cbind ρ₂ (cbind ρ₁ ψ) = cbind (compSS Δ₁ Δ₂ Δ₃ ρ₁ ρ₂) ψ :=
  match ψ as ψ' return
    forall (ρ₁ : TSub Δ₁ Δ₂) (ρ₂ : TSub Δ₂ Δ₃), Pirr ρ₁ -> Pirr ρ₂ ->
      cbind ρ₂ (cbind ρ₁ ψ') = cbind (compSS Δ₁ Δ₂ Δ₃ ρ₁ ρ₂) ψ' with
  | @c_eq _ k a b => fun ρ₁ ρ₂ H₁ H₂ =>
      f_equal2 (fun x y => @c_eq Δ₃ k x y)
        (tbind_tbind k Δ₁ Δ₂ Δ₃ a ρ₁ ρ₂ H₁ H₂)
        (tbind_tbind k Δ₁ Δ₂ Δ₃ b ρ₁ ρ₂ H₁ H₂)
  end.

Definition idSub (Δ : Ctx kind) : TSub Δ Δ :=
  @Build_Sub kind (fun κ => typ κ) IPC_typ Δ Δ (fun v x EQ => t_var v x EQ).

Lemma liftS_id (k : kind) (Δ : Ctx kind) :
  forall v (z : dom (extC k Δ)) EQ,
    liftS k (idSub Δ) v z EQ = idSub (extC k Δ) v z EQ.
Proof.
  intros v [|y] EQ; simpl.
  - apply t_var_irr.
  - rewrite shift_is_shiftt.
    rewrite shiftt_eq.
    apply t_var_irr.
Qed.

Fixpoint tbind_id (κ : kind) (Δ : Ctx kind) (τ : typ κ Δ) {struct τ} :
  tbind (idSub Δ) τ = τ :=
  match τ as τ' in type _ k return tbind (idSub Δ) τ' = τ' with
  | @t_var _ k x EQ => eq_refl
  | @t_lam _ k1 k2 b =>
      f_equal t_lam
        (eq_trans
          (tbind_ext k2 (extC k1 Δ) (extC k1 Δ) b
             (liftS k1 (idSub Δ)) (idSub (extC k1 Δ)) (liftS_id k1 Δ))
          (tbind_id k2 (extC k1 Δ) b))
  | @t_app _ k1 k2 σ τ0 =>
      f_equal2 (fun a b => @t_app Δ k1 k2 a b)
        (tbind_id (k1 ⇒ k2) Δ σ) (tbind_id k1 Δ τ0)
  | @t_ctor _ k c => eq_refl
  | @t_carr _ ψ τ0 =>
      f_equal2 (fun a b => @t_carr Δ a b)
        (cbind_id Δ ψ) (tbind_id ⋆ Δ τ0)
  | @t_cprod _ ψ τ0 =>
      f_equal2 (fun a b => @t_cprod Δ a b)
        (cbind_id Δ ψ) (tbind_id ⋆ Δ τ0)
  end
with cbind_id (Δ : Ctx kind) (ψ : constr Δ) {struct ψ} :
  cbind (idSub Δ) ψ = ψ :=
  match ψ as ψ' return cbind (idSub Δ) ψ' = ψ' with
  | @c_eq _ k a b =>
      f_equal2 (fun x y => @c_eq Δ k x y) (tbind_id k Δ a) (tbind_id k Δ b)
  end.

Lemma compSub2_mkShift_mksubst (κ : kind) (Δ : Ctx kind) (σ : typ κ Δ) :
  forall v (x : dom Δ) EQ,
    compSub2 Δ (extC κ Δ) Δ (mkShift κ Δ) (mksubst κ σ) v x EQ
    = idSub Δ v x EQ.
Proof. intros v x EQ. simpl. apply t_var_irr. Qed.

Lemma tbind_mksubst_shift (κ κ' : kind) (Δ : Ctx kind) (σ : typ κ Δ) (τ : typ κ' Δ) :
  tbind (mksubst κ σ) (shiftt κ τ) = τ.
Proof.
  change (tbind (mksubst κ σ) (tmap (mkShift κ Δ) τ) = τ).
  rewrite (tbind_tmap κ' Δ (extC κ Δ) Δ τ (mkShift κ Δ) (mksubst κ σ)
             (mk_subst_pirr κ Δ σ)).
  rewrite (tbind_ext κ' Δ Δ τ
             (compSub2 Δ (extC κ Δ) Δ (mkShift κ Δ) (mksubst κ σ))
             (idSub Δ) (compSub2_mkShift_mksubst κ Δ σ)).
  apply tbind_id.
Qed.

Lemma compSS_mk_subst_swap (κ : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂) (Hρ : Pirr ρ)
      (σ : typ κ Δ₁) :
  forall v (x : dom (extC κ Δ₁)) EQ,
    compSS (extC κ Δ₁) Δ₁ Δ₂ (mksubst κ σ) ρ v x EQ
    = compSS (extC κ Δ₁) (extC κ Δ₂) Δ₂ (liftS κ ρ) (mksubst κ (tbind ρ σ)) v x EQ.
Proof.
  intros v [|y] EQ; simpl.
  - destruct EQ; reflexivity.
  - change (ρ v y EQ = tbind (mksubst κ (tbind ρ σ)) (shiftt κ (ρ v y EQ))).
    symmetry. apply tbind_mksubst_shift.
Qed.

Lemma tbind_subst (κ κ' : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂) (Hρ : Pirr ρ)
      (τ : typ κ' (extC κ Δ₁)) (σ : typ κ Δ₁) :
  tbind ρ (subst τ σ) = subst (tbind (liftS κ ρ) τ) (tbind ρ σ).
Proof.
  change (tbind ρ (tbind (mksubst κ σ) τ)
          = tbind (mksubst κ (tbind ρ σ)) (tbind (liftS κ ρ) τ)).
  etransitivity.
  - apply (tbind_tbind κ' (extC κ Δ₁) Δ₁ Δ₂ τ (mksubst κ σ) ρ
             (mk_subst_pirr κ Δ₁ σ) Hρ).
  - etransitivity.
    + apply tbind_ext. apply compSS_mk_subst_swap. exact Hρ.
    + symmetry.
      apply (tbind_tbind κ' (extC κ Δ₁) (extC κ Δ₂) Δ₂ τ
               (liftS κ ρ) (mksubst κ (tbind ρ σ))
               (liftS_pirr κ Δ₁ Δ₂ ρ Hρ) (mk_subst_pirr κ Δ₂ (tbind ρ σ))).
Qed.

Lemma tctd_cbind {Δ₁ : Ctx kind} {κ κ' : kind} (σ : typ κ Δ₁) (c : tctor κ') :
  tctd σ c -> forall (Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂), tctd (tbind ρ σ) c.
Proof.
  induction 1; intros Δ₂ ρ; simpl.
  - apply inj_ctor.
  - apply inj_app. apply IHtctd.
Qed.

Lemma rel_app_tbind (Δ₁ : Ctx kind) (κ₁ : kind) (σ₁ σ₂ : typ κ₁ Δ₁)
      (κ₂ : kind) (τ₁ τ₂ : typ κ₂ Δ₁) :
  rel_app κ₁ σ₁ σ₂ κ₂ τ₁ τ₂ ->
  forall (Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂),
    rel_app κ₁ (tbind ρ σ₁) (tbind ρ σ₂) κ₂ (tbind ρ τ₁) (tbind ρ τ₂).
Proof.
  induction 1; intros Δ₂ ρ; simpl.
  - apply rel_app_refl.
  - eapply rel_app_app; eauto.
Qed.

Lemma rel_app_tbind_rec {Δ : Ctx kind} {κ : kind} (τ : typ κ (extC κ Δ))
      (σ₁ σ₂ : typ ⋆ Δ) :
  rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂ ->
  forall (Δ₂ : Ctx kind) (ρ : TSub Δ Δ₂), Pirr ρ ->
    rel_app κ (rec_type Δ₂ κ (tbind (liftS κ ρ) τ))
              (subst (tbind (liftS κ ρ) τ) (rec_type Δ₂ κ (tbind (liftS κ ρ) τ)))
              ⋆ (tbind ρ σ₁) (tbind ρ σ₂).
Proof.
  intros H Δ₂ ρ Hρ.
  pose proof (rel_app_tbind Δ κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ))
                ⋆ σ₁ σ₂ H Δ₂ ρ) as HR.
  rewrite (tbind_subst κ κ Δ Δ₂ ρ Hρ τ (rec_type Δ κ τ)) in HR.
  exact HR.
Qed.

Fixpoint tproves_refl (κ : kind) (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ κ Δ) {struct τ} :
  Ψ ⊩ τ ≃ τ :=
  match τ as τ' in type _ k return Ψ ⊩ τ' ≃ τ' with
  | @t_var _ k x EQ => tpi_var
  | @t_lam _ k1 k2 b => tpi_lam (tproves_refl k2 (extC k1 Δ) (map shift Ψ) b)
  | @t_app _ k1 k2 σ τ0 => tpi_app (tproves_refl (k1 ⇒ k2) Δ Ψ σ) (tproves_refl k1 Δ Ψ τ0)
  | @t_ctor _ k c => tpi_ctor c
  | @t_carr _ ψ τ0 => tpi_carr (tproves_refl ⋆ Δ Ψ τ0)
  | @t_cprod _ ψ τ0 => tpi_cprod (tproves_refl ⋆ Δ Ψ τ0)
  end.

Lemma tbind_eta (κ κ' : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂) (Hρ : Pirr ρ)
      (τ : typ (κ ⇒ κ') Δ₁) :
  tbind ρ (etaT κ κ' τ) = etaT κ κ' (tbind ρ τ).
Proof.
  change (t_lam (t_app (tbind (liftS κ ρ) (shiftt κ τ))
                        (tbind (liftS κ ρ) (t_var κ (VZ : dom (extC κ Δ₁)) eq_refl)))
          = t_lam (t_app (shiftt κ (tbind ρ τ))
                        (t_var κ (VZ : dom (extC κ Δ₂)) eq_refl))).
  f_equal.
  rewrite (tbind_shift_comm κ Δ₁ Δ₂ ρ Hρ (κ ⇒ κ') τ).
  reflexivity.
Qed.

Lemma map_shift_cbind (κ : kind) (Δ₁ Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂) (Hρ : Pirr ρ)
      (Ψ : list (constr Δ₁)) :
  map (cbind (liftS κ ρ)) (map shift Ψ) = map shift (map (cbind ρ) Ψ).
Proof.
  rewrite List.map_map. rewrite List.map_map.
  apply List.map_ext. intro ψ.
  change (cbind (liftS κ ρ) (cmap (mkShift κ Δ₁) ψ)
          = cmap (mkShift κ Δ₂) (cbind ρ ψ)).
  apply cbind_shift_comm. exact Hρ.
Qed.

Lemma tproves_cbind (Δ₁ : Ctx kind) (Ψ : list (constr Δ₁)) (ψ : constr Δ₁) :
  Ψ ⊩ ψ -> forall (Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂), Pirr ρ -> map (cbind ρ) Ψ ⊩ cbind ρ ψ.
Proof.
  intros H.
  induction H using tproves_i_ind.
  - (* ax *) intros Δ₂ ρ Hρ. apply tpi_ax. apply List.in_map. assumption.
  - (* var *) intros Δ₂ ρ Hρ. simpl. erewrite (Hρ κ x _ _). apply tproves_refl.
  - (* lam *) intros Δ₂ ρ Hρ. eapply tpi_lam.
    rewrite <- (map_shift_cbind κₐ _ Δ₂ ρ Hρ).
    eapply IHtproves_i. exact (liftS_pirr κₐ _ Δ₂ ρ Hρ).
  - (* app *) intros Δ₂ ρ Hρ. eapply tpi_app;
      [ eapply IHtproves_i1; exact Hρ | eapply IHtproves_i2; exact Hρ ].
  - (* ctor *) intros Δ₂ ρ Hρ. apply tpi_ctor.
  - (* carr *) intros Δ₂ ρ Hρ. eapply tpi_carr. eapply IHtproves_i. exact Hρ.
  - (* cprod *) intros Δ₂ ρ Hρ. eapply tpi_cprod. eapply IHtproves_i. exact Hρ.
  - (* symm *) intros Δ₂ ρ Hρ. eapply tpi_symm. eapply IHtproves_i. exact Hρ.
  - (* trans *) intros Δ₂ ρ Hρ. eapply tpi_trans;
      [ eapply IHtproves_i1; exact Hρ | eapply IHtproves_i2; exact Hρ ].
  - (* eta *) intros Δ₂ ρ Hρ.
    change (map (cbind ρ) Ψ ⊩ c_eq (κₐ ⇒ κᵣ) (tbind ρ τ) (tbind ρ (etaT κₐ κᵣ τ))).
    rewrite (tbind_eta κₐ κᵣ _ Δ₂ ρ Hρ τ). apply tpi_eta.
  - (* beta *) intros Δ₂ ρ Hρ.
    change (map (cbind ρ) Ψ ⊩ c_eq κᵣ (tbind ρ (t_app (t_lam τ) σ)) (tbind ρ (subst τ σ))).
    rewrite (tbind_subst κₐ κᵣ _ Δ₂ ρ Hρ τ σ). apply tpi_beta.
  - (* appInjR *) intros Δ₂ ρ Hρ.
    exact (tpi_appInjR (tctd_cbind σ₁ c HI₁ Δ₂ ρ) (tctd_cbind σ₂ c HI₂ Δ₂ ρ)
             (IHtproves_i Δ₂ ρ Hρ)).
  - (* appInjL *) intros Δ₂ ρ Hρ.
    exact (tpi_appInjL (tctd_cbind σ₁ c HI₁ Δ₂ ρ) (tctd_cbind σ₂ c HI₂ Δ₂ ρ)
             (IHtproves_i Δ₂ ρ Hρ)).
  - (* carrInjR *) intros Δ₂ ρ Hρ. exact (tpi_carrInjR (IHtproves_i Δ₂ ρ Hρ)).
  - (* cprodInjR *) intros Δ₂ ρ Hρ. exact (tpi_cprodInjR (IHtproves_i Δ₂ ρ Hρ)).
  - (* cprodInjL *) intros Δ₂ ρ Hρ.
    exact (tpi_cprodInjL (IHtproves_i1 Δ₂ ρ Hρ) (IHtproves_i2 Δ₂ ρ Hρ)).
  - (* carrInjL *) intros Δ₂ ρ Hρ.
    exact (tpi_carrInjL (IHtproves_i1 Δ₂ ρ Hρ) (IHtproves_i2 Δ₂ ρ Hρ)).
Qed.

Lemma tdiscr_cbind (Δ₁ : Ctx kind) (ψ : constr Δ₁) : ⊮ ψ ->
  forall (Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂), ⊮ cbind ρ ψ.
Proof.
  induction 1; intros Δ₂ ρ; simpl.
  - eapply td_ctd.
    + exact (tctd_cbind τ₁ c₁ HI₁ Δ₂ ρ).
    + exact (tctd_cbind τ₂ c₂ HI₂ Δ₂ ρ).
    + exact HD.
  - eapply td_carr_ctd. exact (tctd_cbind σ c HI Δ₂ ρ).
  - eapply td_ctd_carr. exact (tctd_cbind σ c HI Δ₂ ρ).
  - eapply td_cprod_ctd. exact (tctd_cbind σ c HI Δ₂ ρ).
  - eapply td_ctd_cprod. exact (tctd_cbind σ c HI Δ₂ ρ).
  - eapply td_carr_cprod.
  - eapply td_cprod_carr.
Qed.
Ltac solve_pirr := first [ assumption | apply liftS_pirr; solve_pirr ].

Ltac sih2 :=
  multimatch goal with
  | H : forall (Δ₂ : Ctx kind), _ |- _ => refine (H _ _ _); solve_pirr
  end.

Lemma typing_tsubst_mut :
  (forall (V : Set) (Δ₁ : Ctx kind) (Ψ : list (constr Δ₁)) (Γ : V -> typ ⋆ Δ₁)
          (e : expr V) (τ : typ ⋆ Δ₁), Δ₁ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
   forall (Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂), Pirr ρ ->
     Δ₂ ∣ map (cbind ρ) Ψ ∣ (fun x => tbind ρ (Γ x)) ⊢ₑ e : tbind ρ τ)
  /\
  (forall (V : Set) (Δ₁ : Ctx kind) (Ψ : list (constr Δ₁)) (Γ : V -> typ ⋆ Δ₁)
          (v : value V) (τ : typ ⋆ Δ₁), Δ₁ ∣ Ψ ∣ Γ ⊢ᵥ v : τ ->
   forall (Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂), Pirr ρ ->
     Δ₂ ∣ map (cbind ρ) Ψ ∣ (fun x => tbind ρ (Γ x)) ⊢ᵥ v : tbind ρ τ).
Proof.
  assert (HE : forall (V : Set) (Δ₁ : Ctx kind) (Ψ : list (constr Δ₁)) (Γ : V -> typ ⋆ Δ₁)
          (e : expr V) (τ : typ ⋆ Δ₁), Δ₁ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
   forall (Δ₂ : Ctx kind) (ρ : TSub Δ₁ Δ₂), Pirr ρ ->
     Δ₂ ∣ map (cbind ρ) Ψ ∣ (fun x => tbind ρ (Γ x)) ⊢ₑ e : tbind ρ τ).
  { intros V Δ₁ Ψ Γ e τ H.
    induction H using typing_expr_mut with
      (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
                 (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (Δ₂ : Ctx kind) (ρ : TSub Δ Δ₂), Pirr ρ ->
               Δ₂ ∣ map (cbind ρ) Ψ ∣ (fun x => tbind ρ (Γ x)) ⊢ₑ e : tbind ρ τ)
      (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
                 (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ) =>
             forall (Δ₂ : Ctx kind) (ρ : TSub Δ Δ₂), Pirr ρ ->
               Δ₂ ∣ map (cbind ρ) Ψ ∣ (fun x => tbind ρ (Γ x)) ⊢ᵥ v : tbind ρ τ).
    - (* T_val *) intros Δ₂ ρ Hρ. eapply T_val.
      sih2.
    - (* T_bind *) intros Δ₂ ρ Hρ. eapply T_bind.
      + sih2.
      + eapply typing_expr_congr.
        * sih2.
        * intros [|x]; simpl; reflexivity.
    - (* T_congE *) intros Δ₂ ρ Hρ. eapply T_congE.
      + refine (tproves_cbind _ Ψ (@c_eq Δ ⋆ τ τ') _ Δ₂ ρ Hρ); eassumption.
      + sih2.
    - (* T_app *) intros Δ₂ ρ Hρ. eapply T_app.
      + sih2.
      + sih2.
    - (* T_tapp *) intros Δ₂ ρ Hρ. rewrite (tbind_subst κ ⋆ _ Δ₂ ρ Hρ τ σ). eapply T_tapp.
      sih2.
    - (* T_projL *) intros Δ₂ ρ Hρ. eapply T_projL.
      sih2.
    - (* T_projR *) intros Δ₂ ρ Hρ. eapply T_projR.
      sih2.
    - (* T_abort *) intros Δ₂ ρ Hρ. eapply T_abort.
      sih2.
    - (* T_case *) intros Δ₂ ρ Hρ. eapply T_case.
      + eapply typing_expr_congr.
        * sih2.
        * intros [|x]; simpl; reflexivity.
      + eapply typing_expr_congr.
        * sih2.
        * intros [|x]; simpl; reflexivity.
      + sih2.
    - (* T_unpack *) intros Δ₂ ρ Hρ. eapply T_unpack.
      + sih2.
      + rewrite <- (map_shift_cbind κ _ Δ₂ ρ Hρ).
        eapply typing_expr_congr.
        * rewrite shift_is_shiftt. rewrite <- (tbind_shift_comm κ _ Δ₂ ρ Hρ ⋆ τ'). sih2.
        * intros [|x]; simpl.
          -- reflexivity.
          -- rewrite shift_is_shiftt. rewrite (tbind_shift_comm κ _ Δ₂ ρ Hρ ⋆ (Γ x)). reflexivity.
    - (* T_unroll *) intros Δ₂ ρ Hρ. eapply T_unroll.
      + exact (rel_app_tbind_rec τ σ₁ σ₂ HF Δ₂ ρ Hρ).
      + sih2.
    - (* T_cabort *) intros Δ₂ ρ Hρ. eapply T_cabort.
      + refine (tproves_cbind _ Ψ ψ _ Δ₂ ρ Hρ); eassumption.
      + refine (tdiscr_cbind _ ψ _ Δ₂ ρ); eassumption.
    - (* T_capp *) intros Δ₂ ρ Hρ. eapply T_capp.
      + refine (tproves_cbind _ Ψ φ _ Δ₂ ρ Hρ); eassumption.
      + sih2.
    - (* T_lwith *) intros Δ₂ ρ Hρ. eapply T_lwith.
      + sih2.
      + eapply typing_expr_congr.
        * sih2.
        * intros [|x]; simpl; reflexivity.
    - (* T_var *) intros Δ₂ ρ Hρ. apply T_var. simpl. rewrite EQ. reflexivity.
    - (* T_congV *) intros Δ₂ ρ Hρ. eapply T_congV.
      + refine (tproves_cbind _ Ψ (@c_eq Δ ⋆ τ τ') _ Δ₂ ρ Hρ); eassumption.
      + sih2.
    - (* T_unit *) intros Δ₂ ρ Hρ. apply T_unit.
    - (* T_lam *) intros Δ₂ ρ Hρ. eapply T_lam.
      eapply typing_expr_congr.
      * sih2.
      * intros [|x]; simpl; reflexivity.
    - (* T_pair *) intros Δ₂ ρ Hρ. eapply T_pair.
      + sih2.
      + sih2.
    - (* T_injl *) intros Δ₂ ρ Hρ. eapply T_injl.
      sih2.
    - (* T_injr *) intros Δ₂ ρ Hρ. eapply T_injr.
      sih2.
    - (* T_tlam *) intros Δ₂ ρ Hρ. eapply T_tlam.
      rewrite <- (map_shift_cbind κ _ Δ₂ ρ Hρ).
      eapply typing_expr_congr.
      * sih2.
      * intro x. simpl. rewrite shift_is_shiftt.
        rewrite (tbind_shift_comm κ _ Δ₂ ρ Hρ ⋆ (Γ x)). reflexivity.
    - (* T_pack *) intros Δ₂ ρ Hρ.
      refine (@T_pack V Δ₂ (map (cbind ρ) Ψ) (fun x => tbind ρ (Γ x)) κ
                (tbind (liftS κ ρ) τ) (tbind ρ τ') v _).
      rewrite <- (tbind_subst κ ⋆ _ Δ₂ ρ Hρ τ τ'). sih2.
    - (* T_roll *) intros Δ₂ ρ Hρ. eapply T_roll.
      + exact (rel_app_tbind_rec τ σ₁ σ₂ HF Δ₂ ρ Hρ).
      + sih2.
    - (* T_lamC *) intros Δ₂ ρ Hρ. eapply T_lamC.
      sih2.
    - (* T_withC *) intros Δ₂ ρ Hρ. eapply T_withC.
      + sih2.
      + refine (tproves_cbind _ Ψ φ _ Δ₂ ρ Hρ); eassumption.
    - (* T_rec *) intros Δ₂ ρ Hρ. eapply T_rec.
      eapply typing_expr_congr.
      * sih2.
      * intros [|[|x]]; simpl; reflexivity.
  }
  split; [ exact HE | ].
  intros V Δ₁ Ψ Γ v τ H.
  induction H using typing_val_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
           forall (Δ₂ : Ctx kind) (ρ : TSub Δ Δ₂), Pirr ρ ->
             Δ₂ ∣ map (cbind ρ) Ψ ∣ (fun x => tbind ρ (Γ x)) ⊢ₑ e : tbind ρ τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ) =>
           forall (Δ₂ : Ctx kind) (ρ : TSub Δ Δ₂), Pirr ρ ->
             Δ₂ ∣ map (cbind ρ) Ψ ∣ (fun x => tbind ρ (Γ x)) ⊢ᵥ v : tbind ρ τ).
  - (* T_val *) intros Δ₂ ρ Hρ. eapply T_val.
    sih2.
  - (* T_bind *) intros Δ₂ ρ Hρ. eapply T_bind.
    + sih2.
    + eapply typing_expr_congr.
      * sih2.
      * intros [|x]; simpl; reflexivity.
  - (* T_congE *) intros Δ₂ ρ Hρ. eapply T_congE.
    + refine (tproves_cbind _ Ψ (@c_eq Δ ⋆ τ τ') _ Δ₂ ρ Hρ); eassumption.
    + sih2.
  - (* T_app *) intros Δ₂ ρ Hρ. eapply T_app.
    + sih2.
    + sih2.
  - (* T_tapp *) intros Δ₂ ρ Hρ. rewrite (tbind_subst κ ⋆ _ Δ₂ ρ Hρ τ σ). eapply T_tapp.
    sih2.
  - (* T_projL *) intros Δ₂ ρ Hρ. eapply T_projL.
    sih2.
  - (* T_projR *) intros Δ₂ ρ Hρ. eapply T_projR.
    sih2.
  - (* T_abort *) intros Δ₂ ρ Hρ. eapply T_abort.
    sih2.
  - (* T_case *) intros Δ₂ ρ Hρ. eapply T_case.
    + eapply typing_expr_congr.
      * sih2.
      * intros [|x]; simpl; reflexivity.
    + eapply typing_expr_congr.
      * sih2.
      * intros [|x]; simpl; reflexivity.
    + sih2.
  - (* T_unpack *) intros Δ₂ ρ Hρ. eapply T_unpack.
    + sih2.
    + rewrite <- (map_shift_cbind κ _ Δ₂ ρ Hρ).
      eapply typing_expr_congr.
      * rewrite shift_is_shiftt. rewrite <- (tbind_shift_comm κ _ Δ₂ ρ Hρ ⋆ τ'). sih2.
      * intros [|x]; simpl.
        -- reflexivity.
        -- rewrite shift_is_shiftt. rewrite (tbind_shift_comm κ _ Δ₂ ρ Hρ ⋆ (Γ x)). reflexivity.
  - (* T_unroll *) intros Δ₂ ρ Hρ. eapply T_unroll.
    + exact (rel_app_tbind_rec τ σ₁ σ₂ HF Δ₂ ρ Hρ).
    + sih2.
  - (* T_cabort *) intros Δ₂ ρ Hρ. eapply T_cabort.
    + refine (tproves_cbind _ Ψ ψ _ Δ₂ ρ Hρ); eassumption.
    + refine (tdiscr_cbind _ ψ _ Δ₂ ρ); eassumption.
  - (* T_capp *) intros Δ₂ ρ Hρ. eapply T_capp.
    + refine (tproves_cbind _ Ψ φ _ Δ₂ ρ Hρ); eassumption.
    + sih2.
  - (* T_lwith *) intros Δ₂ ρ Hρ. eapply T_lwith.
    + sih2.
    + eapply typing_expr_congr.
      * sih2.
      * intros [|x]; simpl; reflexivity.
  - (* T_var *) intros Δ₂ ρ Hρ. apply T_var. simpl. rewrite EQ. reflexivity.
  - (* T_congV *) intros Δ₂ ρ Hρ. eapply T_congV.
    + refine (tproves_cbind _ Ψ (@c_eq Δ ⋆ τ τ') _ Δ₂ ρ Hρ); eassumption.
    + sih2.
  - (* T_unit *) intros Δ₂ ρ Hρ. apply T_unit.
  - (* T_lam *) intros Δ₂ ρ Hρ. eapply T_lam.
    eapply typing_expr_congr.
    * sih2.
    * intros [|x]; simpl; reflexivity.
  - (* T_pair *) intros Δ₂ ρ Hρ. eapply T_pair.
    + sih2.
    + sih2.
  - (* T_injl *) intros Δ₂ ρ Hρ. eapply T_injl.
    sih2.
  - (* T_injr *) intros Δ₂ ρ Hρ. eapply T_injr.
    sih2.
  - (* T_tlam *) intros Δ₂ ρ Hρ. eapply T_tlam.
    rewrite <- (map_shift_cbind κ _ Δ₂ ρ Hρ).
    eapply typing_expr_congr.
    * sih2.
    * intro x. simpl. rewrite shift_is_shiftt.
      rewrite (tbind_shift_comm κ _ Δ₂ ρ Hρ ⋆ (Γ x)). reflexivity.
  - (* T_pack *) intros Δ₂ ρ Hρ.
    refine (@T_pack V Δ₂ (map (cbind ρ) Ψ) (fun x => tbind ρ (Γ x)) κ
              (tbind (liftS κ ρ) τ) (tbind ρ τ') v _).
    rewrite <- (tbind_subst κ ⋆ _ Δ₂ ρ Hρ τ τ'). sih2.
  - (* T_roll *) intros Δ₂ ρ Hρ. eapply T_roll.
    + exact (rel_app_tbind_rec τ σ₁ σ₂ HF Δ₂ ρ Hρ).
    + sih2.
  - (* T_lamC *) intros Δ₂ ρ Hρ. eapply T_lamC.
    sih2.
  - (* T_withC *) intros Δ₂ ρ Hρ. eapply T_withC.
    + sih2.
    + refine (tproves_cbind _ Ψ φ _ Δ₂ ρ Hρ); eassumption.
  - (* T_rec *) intros Δ₂ ρ Hρ. eapply T_rec.
    eapply typing_expr_congr.
    * sih2.
    * intros [|[|x]]; simpl; reflexivity.
Qed.


Lemma tbind_mksubst_shift_inst (κ κ' : kind) (Δ : Ctx kind) (σ : typ κ Δ) (τ : typ κ' Δ) :
  tbind (mksubst κ σ) (tmap (mk_shift (Inc := @extC kind κ) (A := Δ)) τ) = τ.
Proof. apply tbind_mksubst_shift. Qed.

Lemma cbind_mksubst_shift (κ : kind) (Δ : Ctx kind) (σ : typ κ Δ) (ψ : constr Δ) :
  cbind (mksubst κ σ)
    (@shift (Ctx kind) (@Arr kind) constr (@FMap_constr) (@extC kind κ)
       (@ShiftableCore_ext kind κ) Δ ψ) = ψ.
Proof.
  destruct ψ as [k a b]. simpl.
  apply f_equal2.
  - exact (tbind_mksubst_shift_inst κ k Δ σ a).
  - exact (tbind_mksubst_shift_inst κ k Δ σ b).
Qed.

Lemma tbind_mksubst_shiftS (κ κ' : kind) (Δ : Ctx kind) (σ : typ κ Δ) (τ : typ κ' Δ) :
  tbind (mksubst κ σ)
    (@shift (Ctx kind) (@Arr kind) (typ κ') (@FMap_typ κ') (@extC kind κ)
       (@ShiftableCore_ext kind κ) Δ τ) = τ.
Proof. apply tbind_mksubst_shift. Qed.

Lemma typing_tapp_subst (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ))
      (Γ : V -> typ ⋆ Δ) (κ : kind) (σ : typ κ Δ) (e : expr V) (τ : typ ⋆ (extC κ Δ)) :
  extC κ Δ ∣ map shift Ψ ∣ Env.compose shift Γ ⊢ₑ e : τ ->
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : subst τ σ.
Proof.
  intro H.
  pose proof (proj1 typing_tsubst_mut V (extC κ Δ) (map shift Ψ)
                (Env.compose shift Γ) e τ H Δ (mksubst κ σ) (mk_subst_pirr κ Δ σ)) as H'.
  assert (E : map (cbind (mksubst κ σ)) (map shift Ψ) = Ψ).
  { rewrite <- (List.map_id Ψ) at 2.
    rewrite List.map_map. apply List.map_ext. intro ψ.
    change (cbind (mksubst κ σ)
      (@shift (Ctx kind) (@Arr kind) constr (@FMap_constr) (@extC kind κ)
         (@ShiftableCore_ext kind κ) Δ ψ) = ψ).
    apply cbind_mksubst_shift. }
  rewrite E in H'.
  eapply typing_expr_congr.
  exact H'.
  intro x. simpl. rewrite shift_is_shiftt. apply tbind_mksubst_shift.
Qed.

Lemma typing_unpack_subst (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ))
      (Γ : V -> typ ⋆ Δ) (κ : kind) (τ₀ : typ ⋆ (extC κ Δ)) (τ' : typ ⋆ Δ)
      (τw : typ κ Δ) (e : expr (inc V)) :
  extC κ Δ ∣ map shift Ψ ∣ (Env.compose shift Γ) ▹ τ₀ ⊢ₑ e : shift τ' ->
  Δ ∣ Ψ ∣ Γ ▹ subst τ₀ τw ⊢ₑ e : τ'.
Proof.
  intro H.
  pose proof (proj1 typing_tsubst_mut (inc V) (extC κ Δ) (map shift Ψ)
                ((Env.compose shift Γ) ▹ τ₀) e (shift τ') H
                Δ (mksubst κ τw) (mk_subst_pirr κ Δ τw)) as H'.
  assert (E : map (cbind (mksubst κ τw)) (map shift Ψ) = Ψ).
  { rewrite <- (List.map_id Ψ) at 2.
    rewrite List.map_map. apply List.map_ext. intro ψ.
    change (cbind (mksubst κ τw)
      (@shift (Ctx kind) (@Arr kind) constr (@FMap_constr) (@extC kind κ)
         (@ShiftableCore_ext kind κ) Δ ψ) = ψ).
    apply cbind_mksubst_shift. }
  rewrite E in H'.
  rewrite (tbind_mksubst_shiftS κ ⋆ Δ τw τ') in H'.
  eapply typing_expr_congr.
  exact H'.
  intros [|x]; simpl.
  - reflexivity.
  - rewrite shift_is_shiftt. apply tbind_mksubst_shift.
Qed.


Inductive Ins {A : Type} (x : A) : list A -> list A -> Prop :=
| ins_head Ψ : Ins x Ψ (x :: Ψ)
| ins_tail y Ψ Ψ' : Ins x Ψ Ψ' -> Ins x (y :: Ψ) (y :: Ψ').

Definition shiftC' (κ : kind) (Δ : Ctx kind) (ψ : constr Δ) : constr (extC κ Δ) :=
  @shift (Ctx kind) (@Arr kind) constr (@FMap_constr) (@extC kind κ)
    (@ShiftableCore_ext kind κ) Δ ψ.

Lemma Ins_tail' {A : Type} (x y : A) (Ψ Ψ' : list A) :
  Ins x Ψ Ψ' -> Ins x (y :: Ψ) (y :: Ψ').
Proof. apply ins_tail. Qed.

Lemma Ins_map (κ : kind) (Δ : Ctx kind) (x : constr Δ) (Ψ Ψ' : list (constr Δ)) :
  Ins x Ψ Ψ' ->
  Ins (shiftC' κ Δ x) (map (shiftC' κ Δ) Ψ) (map (shiftC' κ Δ) Ψ').
Proof.
  induction 1; simpl.
  - apply ins_head.
  - apply ins_tail. assumption.
Qed.

Lemma Ins_in {A : Type} (x y : A) (Ψ Ψ' : list A) :
  Ins x Ψ Ψ' -> In y Ψ -> In y Ψ'.
Proof.
  induction 1; simpl; intros Hin.
  - right. assumption.
  - destruct Hin as [<- | Hin]; [ left; reflexivity | right; apply IHIns; assumption ].
Qed.

Lemma tproves_ins (Δ : Ctx kind) (Ψ : list (constr Δ)) (ψ : constr Δ) :
  Ψ ⊩ ψ -> forall (Ψ' : list (constr Δ)) (x : constr Δ), Ins x Ψ Ψ' -> Ψ' ⊩ ψ.
Proof.
  intros H.
  refine (tproves_i_ind (fun Δ Ψ c => forall (Ψ' : list (constr Δ)) (x : constr Δ), Ins x Ψ Ψ' -> Ψ' ⊩ c)
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Δ Ψ ψ H).
  - intros Δ0 Ψ0 ψ0 HIn Ψ' x HI. apply tpi_ax. apply (Ins_in x ψ0 Ψ0 Ψ' HI HIn).
  - intros Δ0 Ψ0 κ x EQ₁ EQ₂ Ψ' x0 HI. apply tpi_var.
  - intros Δ0 Ψ0 κₐ κᵣ τ₁ τ₂ HP IHP Ψ' x HI. eapply tpi_lam.
    change (map (shiftC' κₐ Δ0) Ψ' ⊩ τ₁ ≃ τ₂).
    apply (IHP (map (shiftC' κₐ Δ0) Ψ') (shiftC' κₐ Δ0 x)).
    apply Ins_map. exact HI.
  - intros Δ0 Ψ0 κₐ κᵣ σ₁ σ₂ τ₁ τ₂ HP₁ IHP₁ HP₂ IHP₂ Ψ' x HI.
    eapply tpi_app; [ exact (IHP₁ Ψ' x HI) | exact (IHP₂ Ψ' x HI) ].
  - intros Δ0 Ψ0 κ c Ψ' x HI. apply tpi_ctor.
  - intros Δ0 Ψ0 ψ0 τ₁ τ₂ HP IHP Ψ' x HI. eapply tpi_carr. exact (IHP Ψ' x HI).
  - intros Δ0 Ψ0 ψ0 τ₁ τ₂ HP IHP Ψ' x HI. eapply tpi_cprod. exact (IHP Ψ' x HI).
  - intros Δ0 Ψ0 κ τ₁ τ₂ HP IHP Ψ' x HI. eapply tpi_symm. exact (IHP Ψ' x HI).
  - intros Δ0 Ψ0 κ τ₁ τ₂ τ₃ HP₁ IHP₁ HP₂ IHP₂ Ψ' x HI.
    eapply tpi_trans; [ exact (IHP₁ Ψ' x HI) | exact (IHP₂ Ψ' x HI) ].
  - intros Δ0 Ψ0 κₐ κᵣ τ Ψ' x HI. apply tpi_eta.
  - intros Δ0 Ψ0 κₐ κᵣ σ τ Ψ' x HI. apply tpi_beta.
  - intros Δ0 Ψ0 κₐ κᵣ κ σ₁ σ₂ c τ₁ τ₂ HI₁ HI₂ HP IHP Ψ' x HI.
    eapply tpi_appInjR; [ exact HI₁ | exact HI₂ | exact (IHP Ψ' x HI) ].
  - intros Δ0 Ψ0 κₐ κᵣ κ σ₁ σ₂ c τ₁ τ₂ HI₁ HI₂ HP IHP Ψ' x HI.
    eapply tpi_appInjL; [ exact HI₁ | exact HI₂ | exact (IHP Ψ' x HI) ].
  - intros Δ0 Ψ0 ψ₁ ψ₂ τ₁ τ₂ HP IHP Ψ' x HI. eapply tpi_carrInjR. exact (IHP Ψ' x HI).
  - intros Δ0 Ψ0 ψ₁ ψ₂ τ₁ τ₂ HP IHP Ψ' x HI. eapply tpi_cprodInjR. exact (IHP Ψ' x HI).
  - intros Δ0 Ψ0 ψ₁ ψ₂ τ₁ τ₂ HP IHP h₁ Ih₁ Ψ' x HI.
    eapply tpi_cprodInjL; [ exact (IHP Ψ' x HI) | exact (Ih₁ Ψ' x HI) ].
  - intros Δ0 Ψ0 ψ₁ ψ₂ τ₁ τ₂ HP IHP h₁ Ih₁ Ψ' x HI.
    eapply tpi_carrInjL; [ exact (IHP Ψ' x HI) | exact (Ih₁ Ψ' x HI) ].
Qed.

Ltac sihi c inc :=
  multimatch goal with
  | H : forall (Ψ' : list (constr _)), _ |- _ => refine (H _ c inc)
  end.

Ltac sihi_lwith c HI :=
  multimatch goal with
  | H : forall (Ψ' : list (constr _)), _ |- _ =>
      eapply (H _ c); [ eapply ins_tail; exact HI | ]
  end.

Lemma typing_ins_mut :
  (forall (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
          (e : expr V) (τ : typ ⋆ Δ), Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
   forall (Ψ' : list (constr Δ)) (χ : constr Δ), Ins χ Ψ Ψ' -> Δ ∣ Ψ' ∣ Γ ⊢ₑ e : τ)
  /\
  (forall (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
          (v : value V) (τ : typ ⋆ Δ), Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ ->
   forall (Ψ' : list (constr Δ)) (χ : constr Δ), Ins χ Ψ Ψ' -> Δ ∣ Ψ' ∣ Γ ⊢ᵥ v : τ).
Proof.
  assert (HE : forall (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
          (e : expr V) (τ : typ ⋆ Δ), Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
   forall (Ψ' : list (constr Δ)) (χ : constr Δ), Ins χ Ψ Ψ' -> Δ ∣ Ψ' ∣ Γ ⊢ₑ e : τ).
  { intros V Δ Ψ Γ e τ H.
    induction H using typing_expr_mut with
      (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
                 (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (Ψ' : list (constr Δ)) (χ : constr Δ), Ins χ Ψ Ψ' -> Δ ∣ Ψ' ∣ Γ ⊢ₑ e : τ)
      (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
                 (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ) =>
             forall (Ψ' : list (constr Δ)) (χ : constr Δ), Ins χ Ψ Ψ' -> Δ ∣ Ψ' ∣ Γ ⊢ᵥ v : τ).
    - (* T_val *) intros Ψ' χ Hχ. eapply T_val. sihi χ Hχ.
    - (* T_bind *) intros Ψ' χ Hχ. eapply T_bind.
      + sihi χ Hχ.
      + sihi χ Hχ.
    - (* T_congE *) intros Ψ' χ Hχ. eapply T_congE.
      + refine (tproves_ins Δ Ψ (@c_eq Δ ⋆ τ τ') _ Ψ' χ Hχ); assumption.
      + sihi χ Hχ.
    - (* T_app *) intros Ψ' χ Hχ. eapply T_app.
      + sihi χ Hχ.
      + sihi χ Hχ.
    - (* T_tapp *) intros Ψ' χ Hχ. eapply T_tapp. sihi χ Hχ.
    - (* T_projL *) intros Ψ' χ Hχ. eapply T_projL. sihi χ Hχ.
    - (* T_projR *) intros Ψ' χ Hχ. eapply T_projR. sihi χ Hχ.
    - (* T_abort *) intros Ψ' χ Hχ. eapply T_abort. sihi χ Hχ.
    - (* T_case *) intros Ψ' χ Hχ. eapply T_case.
      + sihi χ Hχ.
      + sihi χ Hχ.
      + sihi χ Hχ.
    - (* T_unpack *) intros Ψ' χ Hχ. eapply T_unpack.
      + sihi χ Hχ.
      + sihi (shiftC' κ Δ χ) (Ins_map κ Δ χ Ψ Ψ' Hχ).
    - (* T_unroll *) intros Ψ' χ Hχ. eapply T_unroll.
      + exact HF.
      + sihi χ Hχ.
    - (* T_cabort *) intros Ψ' χ Hχ. eapply T_cabort.
      + refine (tproves_ins Δ Ψ ψ _ Ψ' χ Hχ); assumption.
      + assumption.
    - (* T_capp *) intros Ψ' χ Hχ. eapply T_capp.
      + refine (tproves_ins Δ Ψ φ _ Ψ' χ Hχ); assumption.
      + sihi χ Hχ.
    - (* T_lwith *) intros Ψ' χ Hχ. eapply T_lwith.
      + sihi χ Hχ.
      + sihi χ (Ins_tail' χ φ Ψ Ψ' Hχ).
    - (* T_var *) intros Ψ' χ Hχ. apply T_var. assumption.
    - (* T_congV *) intros Ψ' χ Hχ. eapply T_congV.
      + refine (tproves_ins Δ Ψ (@c_eq Δ ⋆ τ τ') _ Ψ' χ Hχ); assumption.
      + sihi χ Hχ.
    - (* T_unit *) intros Ψ' χ Hχ. apply T_unit.
    - (* T_lam *) intros Ψ' χ Hχ. eapply T_lam. sihi χ Hχ.
    - (* T_pair *) intros Ψ' χ Hχ. eapply T_pair.
      + sihi χ Hχ.
      + sihi χ Hχ.
    - (* T_injl *) intros Ψ' χ Hχ. eapply T_injl. sihi χ Hχ.
    - (* T_injr *) intros Ψ' χ Hχ. eapply T_injr. sihi χ Hχ.
    - (* T_tlam *) intros Ψ' χ Hχ. eapply T_tlam.
      + sihi (shiftC' κ Δ χ) (Ins_map κ Δ χ Ψ Ψ' Hχ).
    - (* T_pack *) intros Ψ' χ Hχ. eapply T_pack. sihi χ Hχ.
    - (* T_roll *) intros Ψ' χ Hχ. eapply T_roll.
      + exact HF.
      + sihi χ Hχ.
    - (* T_lamC *) intros Ψ' χ Hχ. eapply T_lamC. sihi χ (Ins_tail' χ φ Ψ Ψ' Hχ).
    - (* T_withC *) intros Ψ' χ Hχ. eapply T_withC.
      + sihi χ Hχ.
      + refine (tproves_ins Δ Ψ φ _ Ψ' χ Hχ); assumption.
    - (* T_rec *) intros Ψ' χ Hχ. eapply T_rec. sihi χ Hχ.
  }
  split; [ exact HE | ].
  intros V Δ Ψ Γ v τ H.
  induction H using typing_val_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
           forall (Ψ' : list (constr Δ)) (χ : constr Δ), Ins χ Ψ Ψ' -> Δ ∣ Ψ' ∣ Γ ⊢ₑ e : τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ) =>
           forall (Ψ' : list (constr Δ)) (χ : constr Δ), Ins χ Ψ Ψ' -> Δ ∣ Ψ' ∣ Γ ⊢ᵥ v : τ).
  - (* T_val *) intros Ψ' χ Hχ. eapply T_val. sihi χ Hχ.
  - (* T_bind *) intros Ψ' χ Hχ. eapply T_bind.
    + sihi χ Hχ.
    + sihi χ Hχ.
  - (* T_congE *) intros Ψ' χ Hχ. eapply T_congE.
    + refine (tproves_ins Δ Ψ (@c_eq Δ ⋆ τ τ') _ Ψ' χ Hχ); assumption.
    + sihi χ Hχ.
  - (* T_app *) intros Ψ' χ Hχ. eapply T_app.
    + sihi χ Hχ.
    + sihi χ Hχ.
  - (* T_tapp *) intros Ψ' χ Hχ. eapply T_tapp. sihi χ Hχ.
  - (* T_projL *) intros Ψ' χ Hχ. eapply T_projL. sihi χ Hχ.
  - (* T_projR *) intros Ψ' χ Hχ. eapply T_projR. sihi χ Hχ.
  - (* T_abort *) intros Ψ' χ Hχ. eapply T_abort. sihi χ Hχ.
  - (* T_case *) intros Ψ' χ Hχ. eapply T_case.
    + sihi χ Hχ.
    + sihi χ Hχ.
    + sihi χ Hχ.
  - (* T_unpack *) intros Ψ' χ Hχ. eapply T_unpack.
    + sihi χ Hχ.
    + sihi (shiftC' κ Δ χ) (Ins_map κ Δ χ Ψ Ψ' Hχ).
  - (* T_unroll *) intros Ψ' χ Hχ. eapply T_unroll.
    + exact HF.
    + sihi χ Hχ.
  - (* T_cabort *) intros Ψ' χ Hχ. eapply T_cabort.
    + refine (tproves_ins Δ Ψ ψ _ Ψ' χ Hχ); assumption.
    + assumption.
  - (* T_capp *) intros Ψ' χ Hχ. eapply T_capp.
    + refine (tproves_ins Δ Ψ φ _ Ψ' χ Hχ); assumption.
    + sihi χ Hχ.
  - (* T_lwith *) intros Ψ' χ Hχ. eapply T_lwith.
    + sihi χ Hχ.
    + sihi χ (Ins_tail' χ φ Ψ Ψ' Hχ).
  - (* T_var *) intros Ψ' χ Hχ. apply T_var. assumption.
  - (* T_congV *) intros Ψ' χ Hχ. eapply T_congV.
    + refine (tproves_ins Δ Ψ (@c_eq Δ ⋆ τ τ') _ Ψ' χ Hχ); assumption.
    + sihi χ Hχ.
  - (* T_unit *) intros Ψ' χ Hχ. apply T_unit.
  - (* T_lam *) intros Ψ' χ Hχ. eapply T_lam. sihi χ Hχ.
  - (* T_pair *) intros Ψ' χ Hχ. eapply T_pair.
    + sihi χ Hχ.
    + sihi χ Hχ.
  - (* T_injl *) intros Ψ' χ Hχ. eapply T_injl. sihi χ Hχ.
  - (* T_injr *) intros Ψ' χ Hχ. eapply T_injr. sihi χ Hχ.
  - (* T_tlam *) intros Ψ' χ Hχ. eapply T_tlam.
    + sihi (shiftC' κ Δ χ) (Ins_map κ Δ χ Ψ Ψ' Hχ).
  - (* T_pack *) intros Ψ' χ Hχ. eapply T_pack. sihi χ Hχ.
  - (* T_roll *) intros Ψ' χ Hχ. eapply T_roll.
    + exact HF.
    + sihi χ Hχ.
  - (* T_lamC *) intros Ψ' χ Hχ. eapply T_lamC. sihi χ (Ins_tail' χ φ Ψ Ψ' Hχ).
  - (* T_withC *) intros Ψ' χ Hχ. eapply T_withC.
    + sihi χ Hχ.
    + refine (tproves_ins Δ Ψ φ _ Ψ' χ Hχ); assumption.
  - (* T_rec *) intros Ψ' χ Hχ. eapply T_rec. sihi χ Hχ.
Qed.
Local Open Scope bind_scope.

Definition TSubV {V V' : Set} (Δ : Ctx kind) (Ψ : list (constr Δ))
    (Γ₁ : V -> typ ⋆ Δ) (Γ₂ : V' -> typ ⋆ Δ)
    (ρ : @Binding.Set.Sub value SPC_val V V') : Prop :=
  forall x, Δ ∣ Ψ ∣ Γ₂ ⊢ᵥ Binding.Set.apply_sub ρ x : Γ₁ x.

Lemma TSubV_cons {V V' : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)}
      {Γ₁ : V -> typ ⋆ Δ} {Γ₂ : V' -> typ ⋆ Δ}
      {ρ : @Binding.Set.Sub value SPC_val V V'} (H : TSubV Δ Ψ Γ₁ Γ₂ ρ) (φ : constr Δ) :
  TSubV Δ (φ :: Ψ) Γ₁ Γ₂ ρ.
Proof.
  intro x.
  exact (proj2 typing_ins_mut V' Δ Ψ Γ₂ (Binding.Set.apply_sub ρ x) (Γ₁ x) (H x)
           (φ :: Ψ) φ (@ins_head (constr Δ) φ Ψ)).
Qed.

Lemma TSubV_shift {V V' : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)}
      {Γ₁ : V -> typ ⋆ Δ} {Γ₂ : V' -> typ ⋆ Δ}
      {ρ : @Binding.Set.Sub value SPC_val V V'} (H : TSubV Δ Ψ Γ₁ Γ₂ ρ) (κ : kind) :
  TSubV (extC κ Δ) (map shift Ψ) (Env.compose shift Γ₁) (Env.compose shift Γ₂) ρ.
Proof.
  intro x.
  change (extC κ Δ ∣ map (cmap (mkShift κ Δ)) Ψ
          ∣ (fun y => tmap (mkShift κ Δ) (Γ₂ y))
          ⊢ᵥ Binding.Set.apply_sub ρ x : tmap (mkShift κ Δ) (Γ₁ x)).
  apply (proj2 typing_tren_mut V' Δ Ψ Γ₂ (Binding.Set.apply_sub ρ x) (Γ₁ x) (H x)
           (extC κ Δ) (mkShift κ Δ)).
Qed.

Lemma TSubV_lift {V V' : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)}
      {Γ₁ : V -> typ ⋆ Δ} {Γ₂ : V' -> typ ⋆ Δ}
      {ρ : @Binding.Set.Sub value SPC_val V V'} (H : TSubV Δ Ψ Γ₁ Γ₂ ρ) (σ : typ ⋆ Δ) :
  TSubV Δ Ψ (Γ₁ ▹ σ) (Γ₂ ▹ σ) (ρ ↑).
Proof.
  intros [|x]; simpl.
  - change (Δ ∣ Ψ ∣ Γ₂ ▹ σ ⊢ᵥ v_var VZ : (Γ₁ ▹ σ) VZ).
    apply T_var. reflexivity.
  - change (Δ ∣ Ψ ∣ Γ₂ ▹ σ ⊢ᵥ vren (fun y => VS y) (Binding.Set.apply_sub ρ x) : Γ₁ x).
    apply (proj2 typing_ren_mut V' Δ Ψ Γ₂ (Binding.Set.apply_sub ρ x) (Γ₁ x) (H x)
             (inc V') (Γ₂ ▹ σ) (fun y => VS y)).
    intro y. reflexivity.
Qed.

Lemma typing_val_cast {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)}
      {Γ : V -> typ ⋆ Δ} {τ τ' : typ ⋆ Δ} (v : value V) (EQ : τ = τ') :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ'.
Proof.
  intros H. eapply T_congV. 2: exact H. rewrite EQ. apply tproves_refl.
Qed.

Ltac solve_cond :=
  first [ assumption
        | apply TSubV_lift; solve_cond
        | apply TSubV_shift; solve_cond
        | apply TSubV_cons; solve_cond ].

Ltac sih3 :=
  multimatch goal with
  | H : forall (V' : Set), _ |- _ => refine (H _ _ _ _); solve_cond
  end.

Lemma typing_subst_mut :
  (forall (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ₁ : V -> typ ⋆ Δ)
          (e : expr V) (τ : typ ⋆ Δ), Δ ∣ Ψ ∣ Γ₁ ⊢ₑ e : τ ->
   forall (V' : Set) (Γ₂ : V' -> typ ⋆ Δ) (ρ : @Binding.Set.Sub value SPC_val V V'),
     TSubV Δ Ψ Γ₁ Γ₂ ρ -> Δ ∣ Ψ ∣ Γ₂ ⊢ₑ ebind ρ e : τ)
  /\
  (forall (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ₁ : V -> typ ⋆ Δ)
          (v : value V) (τ : typ ⋆ Δ), Δ ∣ Ψ ∣ Γ₁ ⊢ᵥ v : τ ->
   forall (V' : Set) (Γ₂ : V' -> typ ⋆ Δ) (ρ : @Binding.Set.Sub value SPC_val V V'),
     TSubV Δ Ψ Γ₁ Γ₂ ρ -> Δ ∣ Ψ ∣ Γ₂ ⊢ᵥ vbind ρ v : τ).
Proof.
  assert (HE : forall (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ₁ : V -> typ ⋆ Δ)
          (e : expr V) (τ : typ ⋆ Δ), Δ ∣ Ψ ∣ Γ₁ ⊢ₑ e : τ ->
   forall (V' : Set) (Γ₂ : V' -> typ ⋆ Δ) (ρ : @Binding.Set.Sub value SPC_val V V'),
     TSubV Δ Ψ Γ₁ Γ₂ ρ -> Δ ∣ Ψ ∣ Γ₂ ⊢ₑ ebind ρ e : τ).
  { intros V Δ₁ Ψ Γ e τ H.
    induction H using typing_expr_mut with
      (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
                 (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (V' : Set) (Γ₂ : V' -> typ ⋆ Δ) (ρ : @Binding.Set.Sub value SPC_val V V'),
               TSubV Δ Ψ Γ Γ₂ ρ -> Δ ∣ Ψ ∣ Γ₂ ⊢ₑ ebind ρ e : τ)
      (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
                 (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ) =>
             forall (V' : Set) (Γ₂ : V' -> typ ⋆ Δ) (ρ : @Binding.Set.Sub value SPC_val V V'),
               TSubV Δ Ψ Γ Γ₂ ρ -> Δ ∣ Ψ ∣ Γ₂ ⊢ᵥ vbind ρ v : τ).
    - (* T_val *) intros V' Γ₂ ρ Hρ. simpl. eapply T_val.
      sih3.
    - (* T_bind *) intros V' Γ₂ ρ Hρ. simpl. eapply T_bind.
      + sih3.
      + sih3.
    - (* T_congE *) intros V' Γ₂ ρ Hρ. simpl. eapply T_congE.
      + eassumption.
      + sih3.
    - (* T_app *) intros V' Γ₂ ρ Hρ. simpl. eapply T_app.
      + sih3.
      + sih3.
    - (* T_tapp *) intros V' Γ₂ ρ Hρ. simpl. eapply T_tapp.
      sih3.
    - (* T_projL *) intros V' Γ₂ ρ Hρ. simpl. eapply T_projL.
      sih3.
    - (* T_projR *) intros V' Γ₂ ρ Hρ. simpl. eapply T_projR.
      sih3.
    - (* T_abort *) intros V' Γ₂ ρ Hρ. simpl. eapply T_abort.
      sih3.
    - (* T_case *) intros V' Γ₂ ρ Hρ. simpl. eapply T_case.
      + sih3.
      + sih3.
      + sih3.
    - (* T_unpack *) intros V' Γ₂ ρ Hρ. simpl. eapply T_unpack.
      + sih3.
      + sih3.
    - (* T_unroll *) intros V' Γ₂ ρ Hρ. simpl. eapply T_unroll.
      + exact HF.
      + sih3.
    - (* T_cabort *) intros V' Γ₂ ρ Hρ. simpl. eapply T_cabort.
      + eassumption.
      + eassumption.
    - (* T_capp *) intros V' Γ₂ ρ Hρ. simpl. eapply T_capp.
      + eassumption.
      + sih3.
    - (* T_lwith *) intros V' Γ₂ ρ Hρ. simpl. eapply T_lwith.
      + sih3.
      + sih3.
    - (* T_var *) intros V' Γ₂ ρ Hρ. simpl.
      exact (typing_val_cast (Binding.Set.apply_sub ρ x) EQ (Hρ x)).
    - (* T_congV *) intros V' Γ₂ ρ Hρ. simpl. eapply T_congV.
      + eassumption.
      + sih3.
    - (* T_unit *) intros V' Γ₂ ρ Hρ. simpl. apply T_unit.
    - (* T_lam *) intros V' Γ₂ ρ Hρ. simpl. eapply T_lam.
      sih3.
    - (* T_pair *) intros V' Γ₂ ρ Hρ. simpl. eapply T_pair.
      + sih3.
      + sih3.
    - (* T_injl *) intros V' Γ₂ ρ Hρ. simpl. eapply T_injl.
      sih3.
    - (* T_injr *) intros V' Γ₂ ρ Hρ. simpl. eapply T_injr.
      sih3.
    - (* T_tlam *) intros V' Γ₂ ρ Hρ. simpl. eapply T_tlam.
      sih3.
    - (* T_pack *) intros V' Γ₂ ρ Hρ. simpl. eapply T_pack.
      sih3.
    - (* T_roll *) intros V' Γ₂ ρ Hρ. simpl. eapply T_roll.
      + exact HF.
      + sih3.
    - (* T_lamC *) intros V' Γ₂ ρ Hρ. simpl. eapply T_lamC.
      sih3.
    - (* T_withC *) intros V' Γ₂ ρ Hρ. simpl. eapply T_withC.
      + sih3.
      + eassumption.
    - (* T_rec *) intros V' Γ₂ ρ Hρ. simpl. eapply T_rec.
      sih3.
  }
  split; [ exact HE | ].
  intros V Δ₁ Ψ Γ v τ H.
  induction H using typing_val_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
           forall (V' : Set) (Γ₂ : V' -> typ ⋆ Δ) (ρ : @Binding.Set.Sub value SPC_val V V'),
             TSubV Δ Ψ Γ Γ₂ ρ -> Δ ∣ Ψ ∣ Γ₂ ⊢ₑ ebind ρ e : τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ) =>
           forall (V' : Set) (Γ₂ : V' -> typ ⋆ Δ) (ρ : @Binding.Set.Sub value SPC_val V V'),
             TSubV Δ Ψ Γ Γ₂ ρ -> Δ ∣ Ψ ∣ Γ₂ ⊢ᵥ vbind ρ v : τ).
  - (* T_val *) intros V' Γ₂ ρ Hρ. simpl. eapply T_val.
    sih3.
  - (* T_bind *) intros V' Γ₂ ρ Hρ. simpl. eapply T_bind.
    + sih3.
    + sih3.
  - (* T_congE *) intros V' Γ₂ ρ Hρ. simpl. eapply T_congE.
    + eassumption.
    + sih3.
  - (* T_app *) intros V' Γ₂ ρ Hρ. simpl. eapply T_app.
    + sih3.
    + sih3.
  - (* T_tapp *) intros V' Γ₂ ρ Hρ. simpl. eapply T_tapp.
    sih3.
  - (* T_projL *) intros V' Γ₂ ρ Hρ. simpl. eapply T_projL.
    sih3.
  - (* T_projR *) intros V' Γ₂ ρ Hρ. simpl. eapply T_projR.
    sih3.
  - (* T_abort *) intros V' Γ₂ ρ Hρ. simpl. eapply T_abort.
    sih3.
  - (* T_case *) intros V' Γ₂ ρ Hρ. simpl. eapply T_case.
    + sih3.
    + sih3.
    + sih3.
  - (* T_unpack *) intros V' Γ₂ ρ Hρ. simpl. eapply T_unpack.
    + sih3.
    + sih3.
  - (* T_unroll *) intros V' Γ₂ ρ Hρ. simpl. eapply T_unroll.
    + exact HF.
    + sih3.
  - (* T_cabort *) intros V' Γ₂ ρ Hρ. simpl. eapply T_cabort.
    + eassumption.
    + eassumption.
  - (* T_capp *) intros V' Γ₂ ρ Hρ. simpl. eapply T_capp.
    + eassumption.
    + sih3.
  - (* T_lwith *) intros V' Γ₂ ρ Hρ. simpl. eapply T_lwith.
    + sih3.
    + sih3.
  - (* T_var *) intros V' Γ₂ ρ Hρ. simpl.
    exact (typing_val_cast (Binding.Set.apply_sub ρ x) EQ (Hρ x)).
  - (* T_congV *) intros V' Γ₂ ρ Hρ. simpl. eapply T_congV.
    + eassumption.
    + sih3.
  - (* T_unit *) intros V' Γ₂ ρ Hρ. simpl. apply T_unit.
  - (* T_lam *) intros V' Γ₂ ρ Hρ. simpl. eapply T_lam.
    sih3.
  - (* T_pair *) intros V' Γ₂ ρ Hρ. simpl. eapply T_pair.
    + sih3.
    + sih3.
  - (* T_injl *) intros V' Γ₂ ρ Hρ. simpl. eapply T_injl.
    sih3.
  - (* T_injr *) intros V' Γ₂ ρ Hρ. simpl. eapply T_injr.
    sih3.
  - (* T_tlam *) intros V' Γ₂ ρ Hρ. simpl. eapply T_tlam.
    sih3.
  - (* T_pack *) intros V' Γ₂ ρ Hρ. simpl. eapply T_pack.
    sih3.
  - (* T_roll *) intros V' Γ₂ ρ Hρ. simpl. eapply T_roll.
    + exact HF.
    + sih3.
  - (* T_lamC *) intros V' Γ₂ ρ Hρ. simpl. eapply T_lamC.
    sih3.
  - (* T_withC *) intros V' Γ₂ ρ Hρ. simpl. eapply T_withC.
    + sih3.
    + eassumption.
  - (* T_rec *) intros V' Γ₂ ρ Hρ. simpl. eapply T_rec.
    sih3.
Qed.


Lemma Ins_inv {A : Type} (φ ψ : A) (Ψ Ψ' : list A) :
  Ins φ Ψ Ψ' -> In ψ Ψ' -> In ψ Ψ \/ ψ = φ.
Proof.
  induction 1; simpl; intros Hin.
  - destruct Hin as [-> | Hin]; [ right; reflexivity | left; assumption ].
  - destruct Hin as [-> | Hin]; [ left; left; reflexivity | ].
    destruct (IHIns Hin) as [H' | H']; [ left; right; assumption | right; assumption ].
Qed.

Lemma tproves_cut (Δ : Ctx kind) (Ψ Ψ' : list (constr Δ)) (φ ψ : constr Δ) :
  Ins φ Ψ Ψ' -> Ψ ⊩ φ -> Ψ' ⊩ ψ -> Ψ ⊩ ψ.
Proof.
  intros HI Hφ Hψ.
  refine (tproves_i_ind (fun Δ Ψ' c => forall (Ψ0 : list (constr Δ)) (φ0 : constr Δ),
            Ins φ0 Ψ0 Ψ' -> Ψ0 ⊩ φ0 -> Ψ0 ⊩ c)
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Δ Ψ' ψ Hψ Ψ φ HI Hφ).
  - intros Δ0 Ψ0 ψ0 HIn Ψa φa HI0 Hφ0.
    destruct (Ins_inv φa ψ0 Ψa Ψ0 HI0 HIn) as [Hin | ->].
    + apply tpi_ax. assumption.
    + exact Hφ0.
  - intros Δ0 Ψ0 κ x EQ₁ EQ₂ Ψa φa HI0 Hφ0. apply tpi_var.
  - intros Δ0 Ψ0 κₐ κᵣ τ₁ τ₂ HP IHP Ψa φa HI0 Hφ0. eapply tpi_lam.
    apply (IHP (map shift Ψa) (shiftC' κₐ Δ0 φa)).
    + change (Ins (shiftC' κₐ Δ0 φa) (map (shiftC' κₐ Δ0) Ψa) (map (shiftC' κₐ Δ0) Ψ0)).
      apply Ins_map. exact HI0.
    + change (map (shiftC' κₐ Δ0) Ψa ⊩ shiftC' κₐ Δ0 φa).
      apply (tproves_tmap Δ0 Ψa φa Hφ0 (extC κₐ Δ0) (mkShift κₐ Δ0)).
  - intros Δ0 Ψ0 κₐ κᵣ σ₁ σ₂ τ₁ τ₂ HP₁ IHP₁ HP₂ IHP₂ Ψa φa HI0 Hφ0.
    eapply tpi_app; [ apply (IHP₁ Ψa φa HI0 Hφ0) | apply (IHP₂ Ψa φa HI0 Hφ0) ].
  - intros Δ0 Ψ0 κ c Ψa φa HI0 Hφ0. apply tpi_ctor.
  - intros Δ0 Ψ0 ψ0 τ₁ τ₂ HP IHP Ψa φa HI0 Hφ0. eapply tpi_carr.
    apply (IHP Ψa φa HI0 Hφ0).
  - intros Δ0 Ψ0 ψ0 τ₁ τ₂ HP IHP Ψa φa HI0 Hφ0. eapply tpi_cprod.
    apply (IHP Ψa φa HI0 Hφ0).
  - intros Δ0 Ψ0 κ τ₁ τ₂ HP IHP Ψa φa HI0 Hφ0. eapply tpi_symm.
    apply (IHP Ψa φa HI0 Hφ0).
  - intros Δ0 Ψ0 κ τ₁ τ₂ τ₃ HP₁ IHP₁ HP₂ IHP₂ Ψa φa HI0 Hφ0.
    eapply tpi_trans; [ apply (IHP₁ Ψa φa HI0 Hφ0) | apply (IHP₂ Ψa φa HI0 Hφ0) ].
  - intros Δ0 Ψ0 κₐ κᵣ τ Ψa φa HI0 Hφ0. apply tpi_eta.
  - intros Δ0 Ψ0 κₐ κᵣ σ τ Ψa φa HI0 Hφ0. apply tpi_beta.
  - intros Δ0 Ψ0 κₐ κᵣ κ σ₁ σ₂ c τ₁ τ₂ HI₁ HI₂ HP IHP Ψa φa HI0 Hφ0.
    eapply tpi_appInjR; [ exact HI₁ | exact HI₂ | apply (IHP Ψa φa HI0 Hφ0) ].
  - intros Δ0 Ψ0 κₐ κᵣ κ σ₁ σ₂ c τ₁ τ₂ HI₁ HI₂ HP IHP Ψa φa HI0 Hφ0.
    eapply tpi_appInjL; [ exact HI₁ | exact HI₂ | apply (IHP Ψa φa HI0 Hφ0) ].
  - intros Δ0 Ψ0 ψ₁ ψ₂ τ₁ τ₂ HP IHP Ψa φa HI0 Hφ0. eapply tpi_carrInjR.
    apply (IHP Ψa φa HI0 Hφ0).
  - intros Δ0 Ψ0 ψ₁ ψ₂ τ₁ τ₂ HP IHP Ψa φa HI0 Hφ0. eapply tpi_cprodInjR.
    apply (IHP Ψa φa HI0 Hφ0).
  - intros Δ0 Ψ0 ψ₁ ψ₂ τ₁ τ₂ HP IHP h₁ Ih₁ Ψa φa HI0 Hφ0.
    eapply tpi_cprodInjL; [ apply (IHP Ψa φa HI0 Hφ0) | apply (Ih₁ Ψa φa HI0 Hφ0) ].
  - intros Δ0 Ψ0 ψ₁ ψ₂ τ₁ τ₂ HP IHP h₁ Ih₁ Ψa φa HI0 Hφ0.
    eapply tpi_carrInjL; [ apply (IHP Ψa φa HI0 Hφ0) | apply (Ih₁ Ψa φa HI0 Hφ0) ].
Qed.
Ltac sihc HIc Hφc :=
  multimatch goal with
  | H : forall (Ψa : list (constr _)), _ |- _ => refine (H _ _ HIc Hφc)
  end.

Lemma typing_cut_mut :
  (forall (V : Set) (Δ : Ctx kind) (Ψ' : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
          (e : expr V) (τ : typ ⋆ Δ), Δ ∣ Ψ' ∣ Γ ⊢ₑ e : τ ->
   forall (Ψ : list (constr Δ)) (φ : constr Δ), Ins φ Ψ Ψ' -> Ψ ⊩ φ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ)
  /\
  (forall (V : Set) (Δ : Ctx kind) (Ψ' : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
          (v : value V) (τ : typ ⋆ Δ), Δ ∣ Ψ' ∣ Γ ⊢ᵥ v : τ ->
   forall (Ψ : list (constr Δ)) (φ : constr Δ), Ins φ Ψ Ψ' -> Ψ ⊩ φ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ).
Proof.
  assert (HE : forall (V : Set) (Δ : Ctx kind) (Ψ' : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
          (e : expr V) (τ : typ ⋆ Δ), Δ ∣ Ψ' ∣ Γ ⊢ₑ e : τ ->
   forall (Ψ : list (constr Δ)) (φ : constr Δ), Ins φ Ψ Ψ' -> Ψ ⊩ φ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ).
  { intros V Δ Ψ' Γ e τ H.
    induction H using typing_expr_mut with
      (P := fun (V : Set) (Δ : Ctx kind) (Ψ' : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
                 (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ' ∣ Γ ⊢ₑ e : τ) =>
             forall (Ψ : list (constr Δ)) (φ : constr Δ), Ins φ Ψ Ψ' -> Ψ ⊩ φ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ)
      (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ' : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
                 (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ' ∣ Γ ⊢ᵥ v : τ) =>
             forall (Ψ : list (constr Δ)) (φ : constr Δ), Ins φ Ψ Ψ' -> Ψ ⊩ φ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ).
    - (* T_val *) intros Ψa φa HI Hφ. eapply T_val. sihc HI Hφ.
    - (* T_bind *) intros Ψa φa HI Hφ. eapply T_bind.
      + sihc HI Hφ.
      + sihc HI Hφ.
    - (* T_congE *) intros Ψa φa HI Hφ. eapply T_congE.
      + apply (tproves_cut Δ Ψa Ψ φa (@c_eq Δ ⋆ τ τ') HI Hφ); assumption.
      + sihc HI Hφ.
    - (* T_app *) intros Ψa φa HI Hφ. eapply T_app.
      + sihc HI Hφ.
      + sihc HI Hφ.
    - (* T_tapp *) intros Ψa φa HI Hφ. eapply T_tapp. sihc HI Hφ.
    - (* T_projL *) intros Ψa φa HI Hφ. eapply T_projL. sihc HI Hφ.
    - (* T_projR *) intros Ψa φa HI Hφ. eapply T_projR. sihc HI Hφ.
    - (* T_abort *) intros Ψa φa HI Hφ. eapply T_abort. sihc HI Hφ.
    - (* T_case *) intros Ψa φa HI Hφ. eapply T_case.
      + sihc HI Hφ.
      + sihc HI Hφ.
      + sihc HI Hφ.
    - (* T_unpack *) intros Ψa φa HI Hφ. eapply T_unpack.
      + sihc HI Hφ.
      + sihc (Ins_map κ Δ φa Ψa Ψ HI) (tproves_tmap Δ Ψa φa Hφ (extC κ Δ) (mkShift κ Δ)).
    - (* T_unroll *) intros Ψa φa HI Hφ. eapply T_unroll.
      + exact HF.
      + sihc HI Hφ.
    - (* T_cabort *) intros Ψa φa HI Hφ. eapply T_cabort.
      + apply (tproves_cut Δ Ψa Ψ φa ψ HI Hφ); assumption.
      + assumption.
    - (* T_capp *) intros Ψa φa HI Hφ. eapply T_capp.
      + apply (tproves_cut Δ Ψa Ψ φa φ HI Hφ); assumption.
      + sihc HI Hφ.
    - (* T_lwith *) intros Ψa φa HI Hφ. eapply T_lwith.
      + sihc HI Hφ.
      + sihc (Ins_tail' φa φ Ψa Ψ HI) (tproves_ins Δ Ψa φa Hφ (φ :: Ψa) φ (@ins_head (constr Δ) φ Ψa)).
    - (* T_var *) intros Ψa φa HI Hφ. apply T_var. assumption.
    - (* T_congV *) intros Ψa φa HI Hφ. eapply T_congV.
      + apply (tproves_cut Δ Ψa Ψ φa (@c_eq Δ ⋆ τ τ') HI Hφ); assumption.
      + sihc HI Hφ.
    - (* T_unit *) intros Ψa φa HI Hφ. apply T_unit.
    - (* T_lam *) intros Ψa φa HI Hφ. eapply T_lam. sihc HI Hφ.
    - (* T_pair *) intros Ψa φa HI Hφ. eapply T_pair.
      + sihc HI Hφ.
      + sihc HI Hφ.
    - (* T_injl *) intros Ψa φa HI Hφ. eapply T_injl. sihc HI Hφ.
    - (* T_injr *) intros Ψa φa HI Hφ. eapply T_injr. sihc HI Hφ.
    - (* T_tlam *) intros Ψa φa HI Hφ. eapply T_tlam.
      + sihc (Ins_map κ Δ φa Ψa Ψ HI) (tproves_tmap Δ Ψa φa Hφ (extC κ Δ) (mkShift κ Δ)).
    - (* T_pack *) intros Ψa φa HI Hφ. eapply T_pack. sihc HI Hφ.
    - (* T_roll *) intros Ψa φa HI Hφ. eapply T_roll.
      + exact HF.
      + sihc HI Hφ.
    - (* T_lamC *) intros Ψa φa HI Hφ. eapply T_lamC.
      + sihc (Ins_tail' φa φ Ψa Ψ HI) (tproves_ins Δ Ψa φa Hφ (φ :: Ψa) φ (@ins_head (constr Δ) φ Ψa)).
    - (* T_withC *) intros Ψa φa HI Hφ. eapply T_withC.
      + sihc HI Hφ.
      + apply (tproves_cut Δ Ψa Ψ φa φ HI Hφ); assumption.
    - (* T_rec *) intros Ψa φa HI Hφ. eapply T_rec. sihc HI Hφ.
  }
  split; [ exact HE | ].
  intros V Δ Ψ' Γ v τ H.
  induction H using typing_val_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ' : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ' ∣ Γ ⊢ₑ e : τ) =>
           forall (Ψ : list (constr Δ)) (φ : constr Δ), Ins φ Ψ Ψ' -> Ψ ⊩ φ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ' : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ' ∣ Γ ⊢ᵥ v : τ) =>
           forall (Ψ : list (constr Δ)) (φ : constr Δ), Ins φ Ψ Ψ' -> Ψ ⊩ φ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ).
  - (* T_val *) intros Ψa φa HI Hφ. eapply T_val. sihc HI Hφ.
  - (* T_bind *) intros Ψa φa HI Hφ. eapply T_bind.
    + sihc HI Hφ.
    + sihc HI Hφ.
  - (* T_congE *) intros Ψa φa HI Hφ. eapply T_congE.
    + apply (tproves_cut Δ Ψa Ψ φa (@c_eq Δ ⋆ τ τ') HI Hφ); assumption.
    + sihc HI Hφ.
  - (* T_app *) intros Ψa φa HI Hφ. eapply T_app.
    + sihc HI Hφ.
    + sihc HI Hφ.
  - (* T_tapp *) intros Ψa φa HI Hφ. eapply T_tapp. sihc HI Hφ.
  - (* T_projL *) intros Ψa φa HI Hφ. eapply T_projL. sihc HI Hφ.
  - (* T_projR *) intros Ψa φa HI Hφ. eapply T_projR. sihc HI Hφ.
  - (* T_abort *) intros Ψa φa HI Hφ. eapply T_abort. sihc HI Hφ.
  - (* T_case *) intros Ψa φa HI Hφ. eapply T_case.
    + sihc HI Hφ.
    + sihc HI Hφ.
    + sihc HI Hφ.
  - (* T_unpack *) intros Ψa φa HI Hφ. eapply T_unpack.
    + sihc HI Hφ.
    + sihc (Ins_map κ Δ φa Ψa Ψ HI) (tproves_tmap Δ Ψa φa Hφ (extC κ Δ) (mkShift κ Δ)).
  - (* T_unroll *) intros Ψa φa HI Hφ. eapply T_unroll.
    + exact HF.
    + sihc HI Hφ.
  - (* T_cabort *) intros Ψa φa HI Hφ. eapply T_cabort.
    + apply (tproves_cut Δ Ψa Ψ φa ψ HI Hφ); assumption.
    + assumption.
  - (* T_capp *) intros Ψa φa HI Hφ. eapply T_capp.
    + apply (tproves_cut Δ Ψa Ψ φa φ HI Hφ); assumption.
    + sihc HI Hφ.
  - (* T_lwith *) intros Ψa φa HI Hφ. eapply T_lwith.
    + sihc HI Hφ.
    + sihc (Ins_tail' φa φ Ψa Ψ HI) (tproves_ins Δ Ψa φa Hφ (φ :: Ψa) φ (@ins_head (constr Δ) φ Ψa)).
  - (* T_var *) intros Ψa φa HI Hφ. apply T_var. assumption.
  - (* T_congV *) intros Ψa φa HI Hφ. eapply T_congV.
    + apply (tproves_cut Δ Ψa Ψ φa (@c_eq Δ ⋆ τ τ') HI Hφ); assumption.
    + sihc HI Hφ.
  - (* T_unit *) intros Ψa φa HI Hφ. apply T_unit.
  - (* T_lam *) intros Ψa φa HI Hφ. eapply T_lam. sihc HI Hφ.
  - (* T_pair *) intros Ψa φa HI Hφ. eapply T_pair.
    + sihc HI Hφ.
    + sihc HI Hφ.
  - (* T_injl *) intros Ψa φa HI Hφ. eapply T_injl. sihc HI Hφ.
  - (* T_injr *) intros Ψa φa HI Hφ. eapply T_injr. sihc HI Hφ.
  - (* T_tlam *) intros Ψa φa HI Hφ. eapply T_tlam.
    + sihc (Ins_map κ Δ φa Ψa Ψ HI) (tproves_tmap Δ Ψa φa Hφ (extC κ Δ) (mkShift κ Δ)).
  - (* T_pack *) intros Ψa φa HI Hφ. eapply T_pack. sihc HI Hφ.
  - (* T_roll *) intros Ψa φa HI Hφ. eapply T_roll.
    + exact HF.
    + sihc HI Hφ.
  - (* T_lamC *) intros Ψa φa HI Hφ. eapply T_lamC.
    + sihc (Ins_tail' φa φ Ψa Ψ HI) (tproves_ins Δ Ψa φa Hφ (φ :: Ψa) φ (@ins_head (constr Δ) φ Ψa)).
  - (* T_withC *) intros Ψa φa HI Hφ. eapply T_withC.
    + sihc HI Hφ.
    + apply (tproves_cut Δ Ψa Ψ φa φ HI Hφ); assumption.
  - (* T_rec *) intros Ψa φa HI Hφ. eapply T_rec. sihc HI Hφ.
Qed.


Local Open Scope typ_scope.

Inductive Cval (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ) :
    value V -> typ ⋆ Δ -> Prop :=
| C_var x τ (EQ : Γ x = τ) : Cval V Δ Ψ Γ (v_var x) τ
| C_unit : Cval V Δ Ψ Γ v_unit ⊤
| C_lam e τ₁ τ₂ : Δ ∣ Ψ ∣ Γ ▹ τ₁ ⊢ₑ e : τ₂ -> Cval V Δ Ψ Γ (v_lam e) (τ₁ →ᵗ τ₂)
| C_pair v₁ v₂ τ₁ τ₂ : Cval V Δ Ψ Γ v₁ τ₁ -> Cval V Δ Ψ Γ v₂ τ₂ ->
    Cval V Δ Ψ Γ (v_pair v₁ v₂) (τ₁ × τ₂)
| C_injl v τ₁ τ₂ : Cval V Δ Ψ Γ v τ₁ -> Cval V Δ Ψ Γ (v_inj L v) (τ₁ + τ₂)
| C_injr v τ₁ τ₂ : Cval V Δ Ψ Γ v τ₂ -> Cval V Δ Ψ Γ (v_inj R v) (τ₁ + τ₂)
| C_tlam e κ τ : extC κ Δ ∣ map shift Ψ ∣ Env.compose shift Γ ⊢ₑ e : τ ->
    Cval V Δ Ψ Γ (v_tlam e) (∀ᵗ κ, τ)
| C_pack κ τ τ' v : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : subst τ τ' ->
    Cval V Δ Ψ Γ (v_pack v) (∃ᵗ κ, τ)
| C_roll κ τ σ₁ σ₂ (HF : rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂)
    v : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : σ₂ -> Cval V Δ Ψ Γ (v_roll v) σ₁
| C_lamC e φ τ : Δ ∣ φ :: Ψ ∣ Γ ⊢ₑ e : τ -> Cval V Δ Ψ Γ (v_lamC e) (φ →ᶜ τ)
| C_withC v φ τ : Cval V Δ Ψ Γ v τ -> Ψ ⊩ φ -> Cval V Δ Ψ Γ (⟨ v ⟩ᶜ) (φ ×ᶜ τ)
| C_fix e τ₁ τ₂ : Δ ∣ Ψ ∣ Γ ▹ (τ₁ →ᵗ τ₂) ▹ τ₁ ⊢ₑ e : τ₂ ->
    Cval V Δ Ψ Γ (v_fix e) (τ₁ →ᵗ τ₂)
| C_cong τ τ' v : Ψ ⊩ τ ≃ τ' -> Cval V Δ Ψ Γ v τ -> Cval V Δ Ψ Γ v τ'.

Lemma typing_val_canonical {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)}
      {Γ : V -> typ ⋆ Δ} {v : value V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ -> Cval V Δ Ψ Γ v τ.
Proof.
  intro H.
  induction H using typing_val_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) => True)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ) =>
             Cval V Δ Ψ Γ v τ).
  - exact I. - exact I. - exact I. - exact I. - exact I. - exact I. - exact I.
  - exact I. - exact I. - exact I. - exact I. - exact I. - exact I. - exact I.
  - (* T_var *) eapply C_var. assumption.
  - (* T_congV *) exact (C_cong V Δ Ψ Γ τ τ' v t IHtyping_val).
  - (* T_unit *) eapply C_unit.
  - (* T_lam *) eapply C_lam. assumption.
  - (* T_pair *) eapply C_pair; [ apply IHtyping_val1 | apply IHtyping_val2 ].
  - (* T_injl *) eapply C_injl. apply IHtyping_val.
  - (* T_injr *) eapply C_injr. apply IHtyping_val.
  - (* T_tlam *) eapply C_tlam. assumption.
  - (* T_pack *) eapply C_pack. eassumption.
  - (* T_roll *) eapply C_roll; [ exact HF | assumption ].
  - (* T_lamC *) eapply C_lamC. assumption.
  - (* T_withC *) eapply C_withC; [ apply IHtyping_val | assumption ].
  - (* T_rec *) eapply C_fix. assumption.
Qed.

Lemma Cval_sound {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {τ : typ ⋆ Δ} :
  Cval V Δ Ψ Γ v τ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ.
Proof.
  induction 1; eauto using T_var, T_unit, T_lam, T_pair, T_injl, T_injr,
    T_tlam, T_pack, T_roll, T_lamC, T_withC, T_rec, T_congV.
Qed.


Lemma Ins_map_gen {A B : Type} (f : A -> B) (x : A) (Ψ Ψ' : list A) :
  Ins x Ψ Ψ' -> Ins (f x) (map f Ψ) (map f Ψ').
Proof.
  induction 1; simpl.
  - apply ins_head.
  - apply ins_tail. assumption.
Qed.

Lemma Cval_ins {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {τ : typ ⋆ Δ} :
  Cval V Δ Ψ Γ v τ ->
  forall (Ψ' : list (constr Δ)) (φ : constr Δ), Ins φ Ψ Ψ' -> Cval V Δ Ψ' Γ v τ.
Proof.
  induction 1; intros Ψ' φa HI.
  - apply C_var. assumption.
  - apply C_unit.
  - eapply C_lam. eapply (proj1 typing_ins_mut); [ eassumption | exact HI ].
  - eapply C_pair; [ apply (IHCval1 Ψ' φa HI) | apply (IHCval2 Ψ' φa HI) ].
  - eapply C_injl. apply (IHCval Ψ' φa HI).
  - eapply C_injr. apply (IHCval Ψ' φa HI).
  - eapply C_tlam.
    eapply (proj1 typing_ins_mut); [ eassumption | ].
    apply (Ins_map_gen (fun ψ : constr Δ => shift ψ)). exact HI.
  - eapply C_pack. eapply (proj2 typing_ins_mut); [ eassumption | exact HI ].
  - eapply C_roll; [ exact HF | ].
    eapply (proj2 typing_ins_mut); [ eassumption | exact HI ].
  - eapply C_lamC. eapply (proj1 typing_ins_mut); [ eassumption | ].
    eapply Ins_tail'. exact HI.
  - eapply C_withC; [ apply (IHCval Ψ' φa HI) | ].
    eapply tproves_ins; [ eassumption | exact HI ].
  - eapply C_fix. eapply (proj1 typing_ins_mut); [ eassumption | exact HI ].
  - eapply C_cong; [ | apply (IHCval Ψ' φa HI) ].
    eapply tproves_ins; [ exact H | exact HI ].
Qed.


Lemma tctd_arr_partial (Δ : Ctx kind) (τ : typ ⋆ Δ) :
  tctd ((tc_arr : typ (⋆ ⇒ ⋆ ⇒ ⋆) Δ) τ) tc_arr.
Proof. apply inj_app. apply inj_ctor. Qed.

Lemma tctd_sum_partial (Δ : Ctx kind) (τ : typ ⋆ Δ) :
  tctd ((tc_sum : typ (⋆ ⇒ ⋆ ⇒ ⋆) Δ) τ) tc_sum.
Proof. apply inj_app. apply inj_ctor. Qed.

Lemma tctd_prod_partial (Δ : Ctx kind) (τ : typ ⋆ Δ) :
  tctd ((tc_prod : typ (⋆ ⇒ ⋆ ⇒ ⋆) Δ) τ) tc_prod.
Proof. apply inj_app. apply inj_ctor. Qed.

Lemma tctd_arr_app (Δ : Ctx kind) (τ₁ τ₂ : typ ⋆ Δ) : tctd (τ₁ →ᵗ τ₂) tc_arr.
Proof. unfold t_arr. apply inj_app. apply tctd_arr_partial. Qed.

Lemma tctd_sum_app (Δ : Ctx kind) (τ₁ τ₂ : typ ⋆ Δ) : tctd (τ₁ + τ₂) tc_sum.
Proof. unfold t_sum. apply inj_app. apply tctd_sum_partial. Qed.

Lemma tctd_prod_app (Δ : Ctx kind) (τ₁ τ₂ : typ ⋆ Δ) : tctd (τ₁ × τ₂) tc_prod.
Proof. unfold t_prod. apply inj_app. apply tctd_prod_partial. Qed.

Lemma tproves_arr_inj {Δ : Ctx kind} {Ψ : list (constr Δ)} {τ₁ τ₂ σ₁ σ₂ : typ ⋆ Δ} :
  Ψ ⊩ (τ₁ →ᵗ τ₂) ≃ (σ₁ →ᵗ σ₂) -> Ψ ⊩ τ₁ ≃ σ₁ /\ Ψ ⊩ τ₂ ≃ σ₂.
Proof.
  intro HP. split.
  - exact (tpi_appInjR (inj_ctor tc_arr) (inj_ctor tc_arr)
      (tpi_appInjL (tctd_arr_partial Δ τ₁) (tctd_arr_partial Δ σ₁) HP)).
  - exact (tpi_appInjR (tctd_arr_partial Δ τ₁) (tctd_arr_partial Δ σ₁) HP).
Qed.

Lemma tproves_sum_inj {Δ : Ctx kind} {Ψ : list (constr Δ)} {τ₁ τ₂ σ₁ σ₂ : typ ⋆ Δ} :
  Ψ ⊩ (τ₁ + τ₂) ≃ (σ₁ + σ₂) -> Ψ ⊩ τ₁ ≃ σ₁ /\ Ψ ⊩ τ₂ ≃ σ₂.
Proof.
  intro HP. split.
  - exact (tpi_appInjR (inj_ctor tc_sum) (inj_ctor tc_sum)
      (tpi_appInjL (tctd_sum_partial Δ τ₁) (tctd_sum_partial Δ σ₁) HP)).
  - exact (tpi_appInjR (tctd_sum_partial Δ τ₁) (tctd_sum_partial Δ σ₁) HP).
Qed.

Lemma tproves_prod_inj {Δ : Ctx kind} {Ψ : list (constr Δ)} {τ₁ τ₂ σ₁ σ₂ : typ ⋆ Δ} :
  Ψ ⊩ (τ₁ × τ₂) ≃ (σ₁ × σ₂) -> Ψ ⊩ τ₁ ≃ σ₁ /\ Ψ ⊩ τ₂ ≃ σ₂.
Proof.
  intro HP. split.
  - exact (tpi_appInjR (inj_ctor tc_prod) (inj_ctor tc_prod)
      (tpi_appInjL (tctd_prod_partial Δ τ₁) (tctd_prod_partial Δ σ₁) HP)).
  - exact (tpi_appInjR (tctd_prod_partial Δ τ₁) (tctd_prod_partial Δ σ₁) HP).
Qed.


Lemma typing_val_of_expr_val_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)}
      {Γ : V -> typ ⋆ Δ} {e : expr V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ -> forall (v : value V), e = e_val v -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ.
Proof.
  intro H.
  induction H using typing_expr_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (v0 : value V), e = e_val v0 -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v0 : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ) => True).
  - (* T_val *) intros v0 EV. injection EV as EV. subst. eassumption.
  - (* T_bind *) intros v0 EV. discriminate EV.
  - (* T_congE *) intros v0 EV. eapply T_congV; [ eassumption | exact (IHtyping_expr v0 EV) ].
  - intros v0 EV. discriminate EV.
  - intros v0 EV. discriminate EV.
  - intros v0 EV. discriminate EV.
  - intros v0 EV. discriminate EV.
  - intros v0 EV. discriminate EV.
  - intros v0 EV. discriminate EV.
  - intros v0 EV. discriminate EV.
  - intros v0 EV. discriminate EV.
  - intros v0 EV. discriminate EV.
  - intros v0 EV. discriminate EV.
  - intros v0 EV. discriminate EV.
  - exact I. - exact I. - exact I. - exact I. - exact I. - exact I. - exact I.
  - exact I. - exact I. - exact I. - exact I. - exact I. - exact I.
Qed.

Lemma typing_val_of_expr_val {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)}
      {Γ : V -> typ ⋆ Δ} {v : value V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ (v : expr V) : τ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ.
Proof. intro H. exact (typing_val_of_expr_val_inv H v eq_refl). Qed.


Lemma Cval_unit_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {τ : typ ⋆ Δ} (D : Cval V Δ Ψ Γ v τ) (EV : v = v_unit) :
  Ψ ⊩ ⊤ ≃ τ.
Proof.
  revert EV. induction D; intros EV.
  - discriminate EV.
  - apply tproves_refl.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - eapply tpi_trans; [ apply IHD; assumption | assumption ].
Qed.

Lemma Cval_lam_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {τ : typ ⋆ Δ} (D : Cval V Δ Ψ Γ v τ)
      (e : expr (inc V)) (EV : v = v_lam e) :
  exists τ₁ τ₂, Ψ ⊩ (τ₁ →ᵗ τ₂) ≃ τ /\ Δ ∣ Ψ ∣ Γ ▹ τ₁ ⊢ₑ e : τ₂.
Proof.
  revert EV. induction D; intros EV.
  - discriminate EV.
  - discriminate EV.
  - injection EV as EV. subst. exists τ₁, τ₂. split; [ apply tproves_refl | exact H ].
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - destruct (IHD EV) as (τ₁ & τ₂ & HEQ & HB).
    exists τ₁, τ₂. split; [ eapply tpi_trans; [ exact HEQ | eassumption ] | exact HB ].
Qed.

Lemma Cval_pair_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {τ : typ ⋆ Δ} (D : Cval V Δ Ψ Γ v τ)
      (v1 v2 : value V) (EV : v = v_pair v1 v2) :
  exists τ₁ τ₂, Ψ ⊩ (τ₁ × τ₂) ≃ τ /\
    Cval V Δ Ψ Γ v1 τ₁ /\ Cval V Δ Ψ Γ v2 τ₂.
Proof.
  revert EV. induction D; intros EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - injection EV as EV. subst. exists τ₁, τ₂. split; [ apply tproves_refl | split; assumption ].
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - destruct (IHD EV) as (τ₁ & τ₂ & HEQ & H1 & H2).
    exists τ₁, τ₂. split; [ eapply tpi_trans; [ exact HEQ | eassumption ] | split; assumption ].
Qed.

Lemma Cval_injl_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {τ : typ ⋆ Δ} (D : Cval V Δ Ψ Γ v τ)
      (u : value V) (EV : v = v_inj L u) :
  exists τ₁ τ₂, Ψ ⊩ (τ₁ + τ₂) ≃ τ /\ Cval V Δ Ψ Γ u τ₁.
Proof.
  revert EV. induction D; intros EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - injection EV as EV. subst. exists τ₁, τ₂. split; [ apply tproves_refl | assumption ].
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - destruct (IHD EV) as (τ₁ & τ₂ & HEQ & HB).
    exists τ₁, τ₂. split; [ eapply tpi_trans; [ exact HEQ | eassumption ] | exact HB ].
Qed.

Lemma Cval_injr_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {τ : typ ⋆ Δ} (D : Cval V Δ Ψ Γ v τ)
      (u : value V) (EV : v = v_inj R u) :
  exists τ₁ τ₂, Ψ ⊩ (τ₁ + τ₂) ≃ τ /\ Cval V Δ Ψ Γ u τ₂.
Proof.
  revert EV. induction D; intros EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - injection EV as EV. subst. exists τ₁, τ₂. split; [ apply tproves_refl | assumption ].
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - discriminate EV.
  - destruct (IHD EV) as (τ₁ & τ₂ & HEQ & HB).
    exists τ₁, τ₂. split; [ eapply tpi_trans; [ exact HEQ | eassumption ] | exact HB ].
Qed.

Lemma Cval_fix_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {τ : typ ⋆ Δ} (D : Cval V Δ Ψ Γ v τ)
      (e : expr (inc (inc V))) (EV : v = v_fix e) :
  exists τ₁ τ₂, Ψ ⊩ (τ₁ →ᵗ τ₂) ≃ τ /\
    Δ ∣ Ψ ∣ Γ ▹ (τ₁ →ᵗ τ₂) ▹ τ₁ ⊢ₑ e : τ₂.
Proof.
  revert EV. induction D; intros EV.
  - discriminate EV. - discriminate EV. - discriminate EV. - discriminate EV.
  - discriminate EV. - discriminate EV. - discriminate EV. - discriminate EV.
  - discriminate EV. - discriminate EV. - discriminate EV.
  - injection EV as EV. subst. exists τ₁, τ₂. split; [ apply tproves_refl | exact H ].
  - destruct (IHD EV) as (τ₁ & τ₂ & HEQ & HB).
    exists τ₁, τ₂. split; [ eapply tpi_trans; [ exact HEQ | eassumption ] | exact HB ].
Qed.

Lemma Cval_lamC_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {τ : typ ⋆ Δ} (D : Cval V Δ Ψ Γ v τ)
      (e : expr V) (EV : v = v_lamC e) :
  exists φ τ₀, Ψ ⊩ (φ →ᶜ τ₀) ≃ τ /\ Δ ∣ φ :: Ψ ∣ Γ ⊢ₑ e : τ₀.
Proof.
  revert EV. induction D; intros EV.
  - discriminate EV. - discriminate EV. - discriminate EV. - discriminate EV.
  - discriminate EV. - discriminate EV. - discriminate EV. - discriminate EV.
  - discriminate EV.
  - injection EV as EV. subst. exists φ, τ. split; [ apply tproves_refl | exact H ].
  - discriminate EV. - discriminate EV.
  - destruct (IHD EV) as (φ0 & τ0 & HEQ & HB).
    exists φ0, τ0. split; [ eapply tpi_trans; [ exact HEQ | eassumption ] | exact HB ].
Qed.

Lemma Cval_withC_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {τ : typ ⋆ Δ} (D : Cval V Δ Ψ Γ v τ)
      (u : value V) (EV : v = ⟨ u ⟩ᶜ) :
  exists φ τ₀, Ψ ⊩ (φ ×ᶜ τ₀) ≃ τ /\
    Cval V Δ Ψ Γ u τ₀ /\ Ψ ⊩ φ.
Proof.
  revert EV. induction D; intros EV.
  - discriminate EV. - discriminate EV. - discriminate EV. - discriminate EV.
  - discriminate EV. - discriminate EV. - discriminate EV. - discriminate EV.
  - discriminate EV. - discriminate EV.
  - injection EV as EV. subst. exists φ, τ. split; [ apply tproves_refl | split; assumption ].
  - discriminate EV.
  - destruct (IHD EV) as (φ0 & τ0 & HEQ & HB & HP).
    exists φ0, τ0. split; [ eapply tpi_trans; [ exact HEQ | eassumption ] | split; assumption ].
Qed.

Lemma Cval_tlam_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {τt : typ ⋆ Δ} (D : Cval V Δ Ψ Γ v τt)
      (e : expr V) (EV : v = v_tlam e) :
  exists κ τ₀, Ψ ⊩ (∀ᵗ κ, τ₀) ≃ τt /\
    extC κ Δ ∣ map shift Ψ ∣ Env.compose shift Γ ⊢ₑ e : τ₀.
Proof.
  revert EV. induction D; intros EV.
  - discriminate EV. - discriminate EV. - discriminate EV. - discriminate EV.
  - discriminate EV. - discriminate EV.
  - injection EV as EV. subst. exists κ, τ. split; [ apply tproves_refl | exact H ].
  - discriminate EV. - discriminate EV. - discriminate EV. - discriminate EV.
  - discriminate EV.
  - destruct (IHD EV) as (κ0 & τ0 & HEQ & HB).
    exists κ0, τ0. split; [ eapply tpi_trans; [ exact HEQ | eassumption ] | exact HB ].
Qed.

Lemma Cval_pack_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {τt : typ ⋆ Δ} (D : Cval V Δ Ψ Γ v τt)
      (u : value V) (EV : v = v_pack u) :
  exists κ τ τ', Ψ ⊩ (∃ᵗ κ, τ) ≃ τt /\ Δ ∣ Ψ ∣ Γ ⊢ᵥ u : subst τ τ'.
Proof.
  revert EV. induction D; intros EV.
  - discriminate EV. - discriminate EV. - discriminate EV. - discriminate EV.
  - discriminate EV. - discriminate EV. - discriminate EV.
  - injection EV as EV. subst. exists κ, τ, τ'. split; [ apply tproves_refl | exact H ].
  - discriminate EV. - discriminate EV. - discriminate EV. - discriminate EV.
  - destruct (IHD EV) as (κ0 & τ0 & τ0' & HEQ & HB).
    exists κ0, τ0, τ0'. split; [ eapply tpi_trans; [ exact HEQ | eassumption ] | exact HB ].
Qed.

Lemma Cval_roll_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {τt : typ ⋆ Δ} (D : Cval V Δ Ψ Γ v τt)
      (u : value V) (EV : v = v_roll u) :
  exists κ τ σ₁ σ₂ (HF : rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂),
    Ψ ⊩ σ₁ ≃ τt /\ Δ ∣ Ψ ∣ Γ ⊢ᵥ u : σ₂.
Proof.
  revert EV. induction D; intros EV.
  - discriminate EV. - discriminate EV. - discriminate EV. - discriminate EV.
  - discriminate EV. - discriminate EV. - discriminate EV. - discriminate EV.
  - injection EV as EV. subst. exists κ, τ, σ₁, σ₂, HF. split; [ apply tproves_refl | exact H ].
  - discriminate EV. - discriminate EV. - discriminate EV.
  - destruct (IHD EV) as (κ0 & τ0 & σ10 & σ20 & HF0 & HEQ & HB).
    exists κ0, τ0, σ10, σ20, HF0. split; [ eapply tpi_trans; [ exact HEQ | eassumption ] | exact HB ].
Qed.


Lemma typing_subst_one {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {v : value V} {σ : typ ⋆ Δ} {e : expr (inc V)} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ▹ σ ⊢ₑ e : τ ->
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : σ ->
  Δ ∣ Ψ ∣ Γ ⊢ₑ ebind (mk_subst v) e : τ.
Proof.
  intros He Hv.
  refine (proj1 typing_subst_mut (inc V) Δ Ψ (Γ ▹ σ) e τ He V Γ (mk_subst v) _).
  intros [|x] ; simpl.
  - simpl. exact Hv.
  - apply T_var. reflexivity.
Qed.

Lemma typing_expr_bind_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {e : expr V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
  forall (eA : expr V) (eB : expr (inc V)), e = e_bind eA eB -> exists τ1 τ2, Δ ∣ Ψ ∣ Γ ⊢ₑ eA : τ1 /\ Δ ∣ Ψ ∣ Γ ▹ τ1 ⊢ₑ eB : τ2 /\ Ψ ⊩ τ2 ≃ τ.
Proof.
  intro H.
  induction H using typing_expr_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (eA : expr V) (eB : expr (inc V)), e = e_bind eA eB -> exists τ1 τ2, Δ ∣ Ψ ∣ Γ ⊢ₑ eA : τ1 /\ Δ ∣ Ψ ∣ Γ ▹ τ1 ⊢ₑ eB : τ2 /\ Ψ ⊩ τ2 ≃ τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v0 : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ) => True).
  - (* T_val *) intros eA eB EV. discriminate EV.
  - (* T_bind *) intros eA eB EV. injection EV as E1 E2. subst. exists τ₁, τ₂. split; [ eassumption | split; [ eassumption | apply tproves_refl ] ].
  - (* T_congE *) intros eA eB EV. destruct (IHtyping_expr eA eB EV) as (τ1 & τ2 & H1 & H2 & HEQ). exists τ1, τ2. split; [ exact H1 | split; [ exact H2 | eapply tpi_trans; [ exact HEQ | eassumption ] ] ].
  - (* T_app *) intros eA eB EV. discriminate EV.
  - (* T_tapp *) intros eA eB EV. discriminate EV.
  - (* T_projL *) intros eA eB EV. discriminate EV.
  - (* T_projR *) intros eA eB EV. discriminate EV.
  - (* T_abort *) intros eA eB EV. discriminate EV.
  - (* T_case *) intros eA eB EV. discriminate EV.
  - (* T_unpack *) intros eA eB EV. discriminate EV.
  - (* T_unroll *) intros eA eB EV. discriminate EV.
  - (* T_cabort *) intros eA eB EV. discriminate EV.
  - (* T_capp *) intros eA eB EV. discriminate EV.
  - (* T_lwith *) intros eA eB EV. discriminate EV.
  - (* T_var *) exact I.
  - (* T_congV *) exact I.
  - (* T_unit *) exact I.
  - (* T_lam *) exact I.
  - (* T_pair *) exact I.
  - (* T_injl *) exact I.
  - (* T_injr *) exact I.
  - (* T_tlam *) exact I.
  - (* T_pack *) exact I.
  - (* T_roll *) exact I.
  - (* T_lamC *) exact I.
  - (* T_withC *) exact I.
  - (* T_rec *) exact I.
Qed.

Lemma typing_expr_app_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {e : expr V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
  forall (vA vB : value V), e = e_app vA vB -> exists τ1 τ2, Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : τ1 →ᵗ τ2 /\ Δ ∣ Ψ ∣ Γ ⊢ᵥ vB : τ1 /\ Ψ ⊩ τ2 ≃ τ.
Proof.
  intro H.
  induction H using typing_expr_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (vA vB : value V), e = e_app vA vB -> exists τ1 τ2, Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : τ1 →ᵗ τ2 /\ Δ ∣ Ψ ∣ Γ ⊢ᵥ vB : τ1 /\ Ψ ⊩ τ2 ≃ τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v0 : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ) => True).
  - (* T_val *) intros vA vB EV. discriminate EV.
  - (* T_bind *) intros vA vB EV. discriminate EV.
  - (* T_congE *) intros vA vB EV. destruct (IHtyping_expr vA vB EV) as (τ1 & τ2 & H1 & H2 & HEQ). exists τ1, τ2. split; [ exact H1 | split; [ exact H2 | eapply tpi_trans; [ exact HEQ | eassumption ] ] ].
  - (* T_app *) intros vA vB EV. injection EV as E1 E2. subst. exists τ₁, τ₂. split; [ eassumption | split; [ eassumption | apply tproves_refl ] ].
  - (* T_tapp *) intros vA vB EV. discriminate EV.
  - (* T_projL *) intros vA vB EV. discriminate EV.
  - (* T_projR *) intros vA vB EV. discriminate EV.
  - (* T_abort *) intros vA vB EV. discriminate EV.
  - (* T_case *) intros vA vB EV. discriminate EV.
  - (* T_unpack *) intros vA vB EV. discriminate EV.
  - (* T_unroll *) intros vA vB EV. discriminate EV.
  - (* T_cabort *) intros vA vB EV. discriminate EV.
  - (* T_capp *) intros vA vB EV. discriminate EV.
  - (* T_lwith *) intros vA vB EV. discriminate EV.
  - (* T_var *) exact I.
  - (* T_congV *) exact I.
  - (* T_unit *) exact I.
  - (* T_lam *) exact I.
  - (* T_pair *) exact I.
  - (* T_injl *) exact I.
  - (* T_injr *) exact I.
  - (* T_tlam *) exact I.
  - (* T_pack *) exact I.
  - (* T_roll *) exact I.
  - (* T_lamC *) exact I.
  - (* T_withC *) exact I.
  - (* T_rec *) exact I.
Qed.

Lemma typing_expr_projL_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {e : expr V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
  forall (vA : value V), e = e_proj L vA -> exists τ1 τ2, Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : τ1 × τ2 /\ Ψ ⊩ τ1 ≃ τ.
Proof.
  intro H.
  induction H using typing_expr_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (vA : value V), e = e_proj L vA -> exists τ1 τ2, Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : τ1 × τ2 /\ Ψ ⊩ τ1 ≃ τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v0 : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ) => True).
  - (* T_val *) intros vA EV. discriminate EV.
  - (* T_bind *) intros vA EV. discriminate EV.
  - (* T_congE *) intros vA EV. destruct (IHtyping_expr vA EV) as (τ1 & τ2 & H1 & HEQ). exists τ1, τ2. split; [ exact H1 | eapply tpi_trans; [ exact HEQ | eassumption ] ].
  - (* T_app *) intros vA EV. discriminate EV.
  - (* T_tapp *) intros vA EV. discriminate EV.
  - (* T_projL *) intros vA EV. injection EV as E1. subst. exists τ₁, τ₂. split; [ eassumption | apply tproves_refl ].
  - (* T_projR *) intros vA EV. discriminate EV.
  - (* T_abort *) intros vA EV. discriminate EV.
  - (* T_case *) intros vA EV. discriminate EV.
  - (* T_unpack *) intros vA EV. discriminate EV.
  - (* T_unroll *) intros vA EV. discriminate EV.
  - (* T_cabort *) intros vA EV. discriminate EV.
  - (* T_capp *) intros vA EV. discriminate EV.
  - (* T_lwith *) intros vA EV. discriminate EV.
  - (* T_var *) exact I.
  - (* T_congV *) exact I.
  - (* T_unit *) exact I.
  - (* T_lam *) exact I.
  - (* T_pair *) exact I.
  - (* T_injl *) exact I.
  - (* T_injr *) exact I.
  - (* T_tlam *) exact I.
  - (* T_pack *) exact I.
  - (* T_roll *) exact I.
  - (* T_lamC *) exact I.
  - (* T_withC *) exact I.
  - (* T_rec *) exact I.
Qed.

Lemma typing_expr_projR_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {e : expr V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
  forall (vA : value V), e = e_proj R vA -> exists τ1 τ2, Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : τ1 × τ2 /\ Ψ ⊩ τ2 ≃ τ.
Proof.
  intro H.
  induction H using typing_expr_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (vA : value V), e = e_proj R vA -> exists τ1 τ2, Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : τ1 × τ2 /\ Ψ ⊩ τ2 ≃ τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v0 : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ) => True).
  - (* T_val *) intros vA EV. discriminate EV.
  - (* T_bind *) intros vA EV. discriminate EV.
  - (* T_congE *) intros vA EV. destruct (IHtyping_expr vA EV) as (τ1 & τ2 & H1 & HEQ). exists τ1, τ2. split; [ exact H1 | eapply tpi_trans; [ exact HEQ | eassumption ] ].
  - (* T_app *) intros vA EV. discriminate EV.
  - (* T_tapp *) intros vA EV. discriminate EV.
  - (* T_projL *) intros vA EV. discriminate EV.
  - (* T_projR *) intros vA EV. injection EV as E1. subst. exists τ₁, τ₂. split; [ eassumption | apply tproves_refl ].
  - (* T_abort *) intros vA EV. discriminate EV.
  - (* T_case *) intros vA EV. discriminate EV.
  - (* T_unpack *) intros vA EV. discriminate EV.
  - (* T_unroll *) intros vA EV. discriminate EV.
  - (* T_cabort *) intros vA EV. discriminate EV.
  - (* T_capp *) intros vA EV. discriminate EV.
  - (* T_lwith *) intros vA EV. discriminate EV.
  - (* T_var *) exact I.
  - (* T_congV *) exact I.
  - (* T_unit *) exact I.
  - (* T_lam *) exact I.
  - (* T_pair *) exact I.
  - (* T_injl *) exact I.
  - (* T_injr *) exact I.
  - (* T_tlam *) exact I.
  - (* T_pack *) exact I.
  - (* T_roll *) exact I.
  - (* T_lamC *) exact I.
  - (* T_withC *) exact I.
  - (* T_rec *) exact I.
Qed.

Lemma typing_expr_case_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {e : expr V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
  forall (vA : value V) (eA eB : expr (inc V)), e = e_case vA eA eB -> exists τ1 τ2 τ0, Δ ∣ Ψ ∣ Γ ▹ τ1 ⊢ₑ eA : τ0 /\ Δ ∣ Ψ ∣ Γ ▹ τ2 ⊢ₑ eB : τ0 /\ Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : τ1 + τ2 /\ Ψ ⊩ τ0 ≃ τ.
Proof.
  intro H.
  induction H using typing_expr_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (vA : value V) (eA eB : expr (inc V)), e = e_case vA eA eB -> exists τ1 τ2 τ0, Δ ∣ Ψ ∣ Γ ▹ τ1 ⊢ₑ eA : τ0 /\ Δ ∣ Ψ ∣ Γ ▹ τ2 ⊢ₑ eB : τ0 /\ Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : τ1 + τ2 /\ Ψ ⊩ τ0 ≃ τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v0 : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ) => True).
  - (* T_val *) intros vA eA eB EV. discriminate EV.
  - (* T_bind *) intros vA eA eB EV. discriminate EV.
  - (* T_congE *) intros vA eA eB EV. destruct (IHtyping_expr vA eA eB EV) as (τ1 & τ2 & τ0 & H1 & H2 & H3 & HEQ). exists τ1, τ2, τ0. split; [ exact H1 | split; [ exact H2 | split; [ exact H3 | eapply tpi_trans; [ exact HEQ | eassumption ] ] ] ].
  - (* T_app *) intros vA eA eB EV. discriminate EV.
  - (* T_tapp *) intros vA eA eB EV. discriminate EV.
  - (* T_projL *) intros vA eA eB EV. discriminate EV.
  - (* T_projR *) intros vA eA eB EV. discriminate EV.
  - (* T_abort *) intros vA eA eB EV. discriminate EV.
  - (* T_case *) intros vA eA eB EV. injection EV as E1 E2 E3. subst. exists τ₁, τ₂, τ. split; [ eassumption | split; [ eassumption | split; [ eassumption | apply tproves_refl ] ] ].
  - (* T_unpack *) intros vA eA eB EV. discriminate EV.
  - (* T_unroll *) intros vA eA eB EV. discriminate EV.
  - (* T_cabort *) intros vA eA eB EV. discriminate EV.
  - (* T_capp *) intros vA eA eB EV. discriminate EV.
  - (* T_lwith *) intros vA eA eB EV. discriminate EV.
  - (* T_var *) exact I.
  - (* T_congV *) exact I.
  - (* T_unit *) exact I.
  - (* T_lam *) exact I.
  - (* T_pair *) exact I.
  - (* T_injl *) exact I.
  - (* T_injr *) exact I.
  - (* T_tlam *) exact I.
  - (* T_pack *) exact I.
  - (* T_roll *) exact I.
  - (* T_lamC *) exact I.
  - (* T_withC *) exact I.
  - (* T_rec *) exact I.
Qed.

Lemma typing_expr_capp_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {e : expr V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
  forall (vA : value V), e = e_capp vA -> exists φ τ0, Ψ ⊩ φ /\ Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : φ →ᶜ τ0 /\ Ψ ⊩ τ0 ≃ τ.
Proof.
  intro H.
  induction H using typing_expr_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (vA : value V), e = e_capp vA -> exists φ τ0, Ψ ⊩ φ /\ Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : φ →ᶜ τ0 /\ Ψ ⊩ τ0 ≃ τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v0 : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ) => True).
  - (* T_val *) intros vA EV. discriminate EV.
  - (* T_bind *) intros vA EV. discriminate EV.
  - (* T_congE *) intros vA EV. destruct (IHtyping_expr vA EV) as (φ0 & τ0 & H1 & H2 & HEQ). exists φ0, τ0. split; [ exact H1 | split; [ exact H2 | eapply tpi_trans; [ exact HEQ | eassumption ] ] ].
  - (* T_app *) intros vA EV. discriminate EV.
  - (* T_tapp *) intros vA EV. discriminate EV.
  - (* T_projL *) intros vA EV. discriminate EV.
  - (* T_projR *) intros vA EV. discriminate EV.
  - (* T_abort *) intros vA EV. discriminate EV.
  - (* T_case *) intros vA EV. discriminate EV.
  - (* T_unpack *) intros vA EV. discriminate EV.
  - (* T_unroll *) intros vA EV. discriminate EV.
  - (* T_cabort *) intros vA EV. discriminate EV.
  - (* T_capp *) intros vA EV. injection EV as E1. subst. exists φ, τ. split; [ eassumption | split; [ eassumption | apply tproves_refl ] ].
  - (* T_lwith *) intros vA EV. discriminate EV.
  - (* T_var *) exact I.
  - (* T_congV *) exact I.
  - (* T_unit *) exact I.
  - (* T_lam *) exact I.
  - (* T_pair *) exact I.
  - (* T_injl *) exact I.
  - (* T_injr *) exact I.
  - (* T_tlam *) exact I.
  - (* T_pack *) exact I.
  - (* T_roll *) exact I.
  - (* T_lamC *) exact I.
  - (* T_withC *) exact I.
  - (* T_rec *) exact I.
Qed.

Lemma typing_expr_lwith_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {e : expr V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
  forall (vA : value V) (eA : expr (inc V)), e = e_lwith vA eA -> exists φ σ τ0, Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : φ ×ᶜ σ /\ Δ ∣ φ :: Ψ ∣ Γ ▹ σ ⊢ₑ eA : τ0 /\ Ψ ⊩ τ0 ≃ τ.
Proof.
  intro H.
  induction H using typing_expr_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (vA : value V) (eA : expr (inc V)), e = e_lwith vA eA -> exists φ σ τ0, Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : φ ×ᶜ σ /\ Δ ∣ φ :: Ψ ∣ Γ ▹ σ ⊢ₑ eA : τ0 /\ Ψ ⊩ τ0 ≃ τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v0 : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ) => True).
  - (* T_val *) intros vA eA EV. discriminate EV.
  - (* T_bind *) intros vA eA EV. discriminate EV.
  - (* T_congE *) intros vA eA EV. destruct (IHtyping_expr vA eA EV) as (φ0 & σ0 & τ0 & H1 & H2 & HEQ). exists φ0, σ0, τ0. split; [ exact H1 | split; [ exact H2 | eapply tpi_trans; [ exact HEQ | eassumption ] ] ].
  - (* T_app *) intros vA eA EV. discriminate EV.
  - (* T_tapp *) intros vA eA EV. discriminate EV.
  - (* T_projL *) intros vA eA EV. discriminate EV.
  - (* T_projR *) intros vA eA EV. discriminate EV.
  - (* T_abort *) intros vA eA EV. discriminate EV.
  - (* T_case *) intros vA eA EV. discriminate EV.
  - (* T_unpack *) intros vA eA EV. discriminate EV.
  - (* T_unroll *) intros vA eA EV. discriminate EV.
  - (* T_cabort *) intros vA eA EV. discriminate EV.
  - (* T_capp *) intros vA eA EV. discriminate EV.
  - (* T_lwith *) intros vA eA EV. injection EV as E1 E2. subst. exists φ, σ, τ. split; [ eassumption | split; [ eassumption | apply tproves_refl ] ].
  - (* T_var *) exact I.
  - (* T_congV *) exact I.
  - (* T_unit *) exact I.
  - (* T_lam *) exact I.
  - (* T_pair *) exact I.
  - (* T_injl *) exact I.
  - (* T_injr *) exact I.
  - (* T_tlam *) exact I.
  - (* T_pack *) exact I.
  - (* T_roll *) exact I.
  - (* T_lamC *) exact I.
  - (* T_withC *) exact I.
  - (* T_rec *) exact I.
Qed.



Lemma preservation_LamBetaE (e : expr (inc ∅)) (v : value ∅) :
  forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
    Δ ∣ Ψ ∣ □ ⊢ₑ e_app (v_lam e) v : τ ->
    Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc) e v : τ.
Proof.
  intros Δ Ψ τ H.
  destruct (typing_expr_app_inv H (v_lam e) v eq_refl)
    as (τ1 & τ2 & HV1 & HV2 & HEQ).
  destruct (Cval_lam_inv (typing_val_canonical HV1) e eq_refl)
    as (τ1' & τ2' & HEQarr & HBODY).
  destruct (tproves_arr_inj HEQarr) as (Hτ1 & Hτ2).
  assert (HV2' : Δ ∣ Ψ ∣ □ ⊢ᵥ v : τ1')
    by (eapply T_congV; [ exact (tpi_symm Hτ1) | exact HV2 ]).
  assert (Hsubst : Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc) e v : τ2').
  { change (Δ ∣ Ψ ∣ □ ⊢ₑ ebind (mk_subst v) e : τ2').
    exact (typing_subst_one (V := ∅) (Δ := Δ) (Ψ := Ψ) (Γ := □) (v := v) (σ := τ1') (e := e) (τ := τ2') HBODY HV2'). }
  eapply T_congE.
  - exact (tpi_trans Hτ2 HEQ).
  - exact Hsubst.
Qed.

Lemma preservation_ProjL (v1 v2 : value ∅) :
  forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
    Δ ∣ Ψ ∣ □ ⊢ₑ e_proj L (v_pair v1 v2) : τ -> Δ ∣ Ψ ∣ □ ⊢ₑ v1 : τ.
Proof.
  intros Δ Ψ τ H.
  destruct (typing_expr_projL_inv H (v_pair v1 v2) eq_refl)
    as (τ1 & τ2 & HV & HEQ).
  destruct (Cval_pair_inv (typing_val_canonical HV) v1 v2 eq_refl)
    as (τ1' & τ2' & HEQprod & C1 & C2).
  destruct (tproves_prod_inj HEQprod) as (Hτ1 & Hτ2).
  pose proof (Cval_sound C1) as HV1'.
  apply T_val.
  eapply T_congV; [ exact (tpi_trans Hτ1 HEQ) | exact HV1' ].
Qed.

Lemma preservation_ProjR (v1 v2 : value ∅) :
  forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
    Δ ∣ Ψ ∣ □ ⊢ₑ e_proj R (v_pair v1 v2) : τ -> Δ ∣ Ψ ∣ □ ⊢ₑ v2 : τ.
Proof.
  intros Δ Ψ τ H.
  destruct (typing_expr_projR_inv H (v_pair v1 v2) eq_refl)
    as (τ1 & τ2 & HV & HEQ).
  destruct (Cval_pair_inv (typing_val_canonical HV) v1 v2 eq_refl)
    as (τ1' & τ2' & HEQprod & C1 & C2).
  destruct (tproves_prod_inj HEQprod) as (Hτ1 & Hτ2).
  pose proof (Cval_sound C2) as HV2'.
  apply T_val.
  eapply T_congV; [ exact (tpi_trans Hτ2 HEQ) | exact HV2' ].
Qed.

Lemma preservation_CaseL (v : value ∅) (e1 e2 : expr (inc ∅)) :
  forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
    Δ ∣ Ψ ∣ □ ⊢ₑ e_case (v_inj L v) e1 e2 : τ ->
    Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc) e1 v : τ.
Proof.
  intros Δ Ψ τ H.
  destruct (typing_expr_case_inv H (v_inj L v) e1 e2 eq_refl)
    as (τ1 & τ2 & τ0 & H1 & H2 & HV & HEQ).
  destruct (Cval_injl_inv (typing_val_canonical HV) v eq_refl)
    as (τ1' & τ2' & HEQsum & Cv).
  destruct (tproves_sum_inj HEQsum) as (Hτ1 & Hτ2).
  pose proof (Cval_sound Cv) as Hv'.
  assert (Hv : Δ ∣ Ψ ∣ □ ⊢ᵥ v : τ1)
    by (eapply T_congV; [ exact Hτ1 | exact Hv' ]).
  assert (Hsubst : Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc) e1 v : τ0).
  { change (Δ ∣ Ψ ∣ □ ⊢ₑ ebind (mk_subst v) e1 : τ0).
    exact (typing_subst_one (V := ∅) (Δ := Δ) (Ψ := Ψ) (Γ := □) (v := v) (σ := τ1)
             (e := e1) (τ := τ0) H1 Hv). }
  eapply T_congE; [ exact HEQ | exact Hsubst ].
Qed.

Lemma preservation_CaseR (v : value ∅) (e1 e2 : expr (inc ∅)) :
  forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
    Δ ∣ Ψ ∣ □ ⊢ₑ e_case (v_inj R v) e1 e2 : τ ->
    Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc) e2 v : τ.
Proof.
  intros Δ Ψ τ H.
  destruct (typing_expr_case_inv H (v_inj R v) e1 e2 eq_refl)
    as (τ1 & τ2 & τ0 & H1 & H2 & HV & HEQ).
  destruct (Cval_injr_inv (typing_val_canonical HV) v eq_refl)
    as (τ1' & τ2' & HEQsum & Cv).
  destruct (tproves_sum_inj HEQsum) as (Hτ1 & Hτ2).
  pose proof (Cval_sound Cv) as Hv'.
  assert (Hv : Δ ∣ Ψ ∣ □ ⊢ᵥ v : τ2)
    by (eapply T_congV; [ exact Hτ2 | exact Hv' ]).
  assert (Hsubst : Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc) e2 v : τ0).
  { change (Δ ∣ Ψ ∣ □ ⊢ₑ ebind (mk_subst v) e2 : τ0).
    exact (typing_subst_one (V := ∅) (Δ := Δ) (Ψ := Ψ) (Γ := □) (v := v) (σ := τ2)
             (e := e2) (τ := τ0) H2 Hv). }
  eapply T_congE; [ exact HEQ | exact Hsubst ].
Qed.

Lemma preservation_LamBetaC (e : expr ∅) :
  forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
    Δ ∣ Ψ ∣ □ ⊢ₑ e_capp (v_lamC e) : τ -> Δ ∣ Ψ ∣ □ ⊢ₑ e : τ.
Proof.
  intros Δ Ψ τ H.
  destruct (typing_expr_capp_inv H (v_lamC e) eq_refl)
    as (φ & τ0 & HP & HV & HEQ).
  destruct (Cval_lamC_inv (typing_val_canonical HV) e eq_refl)
    as (φ' & τ' & HEQcarr & HBODY).
  assert (Hτ : Ψ ⊩ τ' ≃ τ0) by (eapply tpi_carrInjR; exact HEQcarr).
  assert (Hφ' : Ψ ⊩ φ') by (eapply tpi_carrInjL; [ exact (tpi_symm HEQcarr) | exact HP ]).
  assert (HB : Δ ∣ Ψ ∣ □ ⊢ₑ e : τ')
    by (exact (proj1 typing_cut_mut ∅ Δ (φ' :: Ψ) □ e τ' HBODY
                 Ψ φ' (@ins_head (constr Δ) φ' Ψ) Hφ')).
  eapply T_congE; [ exact (tpi_trans Hτ HEQ) | exact HB ].
Qed.

Lemma preservation_WithE (v : value ∅) (e : expr (inc ∅)) :
  forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
    Δ ∣ Ψ ∣ □ ⊢ₑ e_lwith (⟨ v ⟩ᶜ) e : τ ->
    Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc) e v : τ.
Proof.
  intros Δ Ψ τ H.
  destruct (typing_expr_lwith_inv H (⟨ v ⟩ᶜ) e eq_refl)
    as (φ & σ & τ0 & HV & HBODY & HEQ).
  destruct (Cval_withC_inv (typing_val_canonical HV) v eq_refl)
    as (φ' & τ' & HEQcprod & Cv & HP').
  assert (Hτ : Ψ ⊩ τ' ≃ σ) by (eapply tpi_cprodInjR; exact HEQcprod).
  assert (Hφ : Ψ ⊩ φ) by (eapply tpi_cprodInjL; [ exact HEQcprod | exact HP' ]).
  pose proof (Cval_sound Cv) as Hv'.
  assert (Hv : Δ ∣ Ψ ∣ □ ⊢ᵥ v : σ)
    by (eapply T_congV; [ exact Hτ | exact Hv' ]).
  assert (Hvφ : Δ ∣ φ :: Ψ ∣ □ ⊢ᵥ v : σ)
    by (exact (proj2 typing_ins_mut ∅ Δ Ψ □ v σ Hv (φ :: Ψ) φ (@ins_head (constr Δ) φ Ψ))).
  assert (Hsubst : Δ ∣ φ :: Ψ ∣ □ ⊢ₑ subst (Inc := inc) e v : τ0).
  { change (Δ ∣ φ :: Ψ ∣ □ ⊢ₑ ebind (mk_subst v) e : τ0).
    exact (typing_subst_one (V := ∅) (Δ := Δ) (Ψ := φ :: Ψ) (Γ := □) (v := v) (σ := σ)
             (e := e) (τ := τ0) HBODY Hvφ). }
  assert (Hcut : Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc) e v : τ0)
    by (exact (proj1 typing_cut_mut ∅ Δ (φ :: Ψ) □ (subst (Inc := inc) e v) τ0 Hsubst
                 Ψ φ (@ins_head (constr Δ) φ Ψ) Hφ)).
  eapply T_congE; [ exact HEQ | exact Hcut ].
Qed.

Lemma preservation_BindE (v : value ∅) (e : expr (inc ∅)) :
  forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
    Δ ∣ Ψ ∣ □ ⊢ₑ (v : expr ∅) >>= e : τ ->
    Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc) e v : τ.
Proof.
  intros Δ Ψ τ H.
  destruct (typing_expr_bind_inv H (v : expr ∅) e eq_refl)
    as (τ1 & τ2 & H1 & H2 & HEQ).
  pose proof (typing_val_of_expr_val_inv H1 v eq_refl) as Hv.
  assert (Hsubst : Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc) e v : τ2).
  { change (Δ ∣ Ψ ∣ □ ⊢ₑ ebind (mk_subst v) e : τ2).
    exact (typing_subst_one (V := ∅) (Δ := Δ) (Ψ := Ψ) (Γ := □) (v := v) (σ := τ1)
             (e := e) (τ := τ2) H2 Hv). }
  eapply T_congE; [ exact HEQ | exact Hsubst ].
Qed.

Lemma preservation_BindE' (e' e'' : expr ∅) (k : expr (inc ∅)) :
  (forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
      Δ ∣ Ψ ∣ □ ⊢ₑ e' : τ -> Δ ∣ Ψ ∣ □ ⊢ₑ e'' : τ) ->
  forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
    Δ ∣ Ψ ∣ □ ⊢ₑ e_bind e' k : τ -> Δ ∣ Ψ ∣ □ ⊢ₑ e_bind e'' k : τ.
Proof.
  intros IH Δ Ψ τ H.
  destruct (typing_expr_bind_inv H e' k eq_refl)
    as (τ1 & τ2 & H1 & H2 & HEQ).
  pose proof (IH Δ Ψ τ1 H1) as H1'.
  eapply T_congE; [ exact HEQ | eapply T_bind; [ exact H1' | exact H2 ] ].
Qed.


Lemma typing_val_shift {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)}
      {Γ : V -> typ ⋆ Δ} {v : value V} {τ : typ ⋆ Δ} (σ : typ ⋆ Δ) :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ ->
  Δ ∣ Ψ ∣ Γ ▹ σ ⊢ᵥ vren (fun x : V => VS x) v : τ.
Proof.
  intro H.
  apply (proj2 typing_ren_mut V Δ Ψ Γ v τ H (inc V) (Γ ▹ σ) (fun x => VS x)).
  intro x. reflexivity.
Qed.

Lemma preservation_LamBetaRec (e : expr (inc (inc ∅))) (v : value ∅) :
  forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
    Δ ∣ Ψ ∣ □ ⊢ₑ e_app (v_fix e) v : τ ->
    Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc)
      (subst (Inc := inc) e (shift v)) (v_fix e) : τ.
Proof.
  intros Δ Ψ τ H.
  destruct (typing_expr_app_inv H (v_fix e) v eq_refl)
    as (τ1 & τ2 & HVfix & HVv & HEQ).
  destruct (Cval_fix_inv (typing_val_canonical HVfix) e eq_refl)
    as (τ1' & τ2' & HEQarr & HBODY).
  destruct (tproves_arr_inj HEQarr) as (Hτ1 & Hτ2).
  assert (Hv' : Δ ∣ Ψ ∣ □ ⊢ᵥ v : τ1')
    by (eapply T_congV; [ exact (tpi_symm Hτ1) | exact HVv ]).
  pose proof (typing_val_shift (V := ∅) (Δ := Δ) (Ψ := Ψ) (Γ := □) (v := v) (τ := τ1')
                (τ1' →ᵗ τ2') Hv') as Hshift.
  pose proof (typing_subst_one (V := inc ∅) (Δ := Δ) (Ψ := Ψ)
                (Γ := □ ▹ (τ1' →ᵗ τ2')) (v := vren (fun x : ∅ => VS x) v)
                (σ := τ1') (e := e) (τ := τ2') HBODY Hshift) as Hinner.
  assert (Hrec : Δ ∣ Ψ ∣ □ ⊢ᵥ v_fix e : τ1' →ᵗ τ2')
    by (eapply T_congV; [ exact (tpi_symm HEQarr) | exact HVfix ]).
  pose proof (typing_subst_one (V := ∅) (Δ := Δ) (Ψ := Ψ) (Γ := □)
                (v := v_fix e) (σ := τ1' →ᵗ τ2')
                (e := subst (Inc := inc) e (vren (fun x : ∅ => VS x) v))
                (τ := τ2') Hinner Hrec) as Houter.
  change (Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc)
            (subst (Inc := inc) e (vren (fun x : ∅ => VS x) v)) (v_fix e) : τ2')
    in Houter.
  eapply T_congE; [ exact (tpi_trans Hτ2 HEQ) | exact Houter ].
Qed.


Lemma subst_liftA_mkshift (κ κᵣ : kind) (Δ : Ctx kind) (τ : typ κᵣ (extC κ Δ)) :
  tbind (mksubst κ (@t_var (extC κ Δ) κ VZ eq_refl))
        (tmap (liftA κ (mkShift κ Δ)) τ) = τ.
Proof.
  rewrite (tbind_tmap κᵣ (extC κ Δ) (extC κ (extC κ Δ)) (extC κ Δ) τ
             (liftA κ (mkShift κ Δ)) (mksubst κ (@t_var (extC κ Δ) κ VZ eq_refl))
             (mk_subst_pirr κ (extC κ Δ) (@t_var (extC κ Δ) κ VZ eq_refl))).
  rewrite (tbind_ext κᵣ (extC κ Δ) (extC κ Δ) τ
             (compSub2 (extC κ Δ) (extC κ (extC κ Δ)) (extC κ Δ)
                (liftA κ (mkShift κ Δ)) (mksubst κ (@t_var (extC κ Δ) κ VZ eq_refl)))
             (idSub (extC κ Δ))
             ltac:(intros v [|y] EQ; destruct EQ; simpl; apply t_var_irr)).
  apply tbind_id.
Qed.

Lemma tproves_lam_inj {Δ : Ctx kind} {Ψ : list (constr Δ)} {κₐ κᵣ : kind}
      {τ σ : typ κᵣ (extC κₐ Δ)} :
  Ψ ⊩ (t_lam τ : typ (κₐ ⇒ κᵣ) Δ) ≃ t_lam σ ->
  map shift Ψ ⊩ τ ≃ σ.
Proof.
  intro HP.
  set (v0 := @t_var (extC κₐ Δ) κₐ VZ eq_refl).
  set (ρL := liftA κₐ (mkShift κₐ Δ)).
  set (τs := tmap ρL τ). set (σs := tmap ρL σ).
  assert (H1 : map (cmap (mkShift κₐ Δ)) Ψ ⊩ c_eq (κₐ ⇒ κᵣ) (t_lam τs) (t_lam σs)).
  { change (map (cmap (mkShift κₐ Δ)) Ψ
            ⊩ cmap (mkShift κₐ Δ) (c_eq (κₐ ⇒ κᵣ) (t_lam τ) (t_lam σ))).
    apply (tproves_tmap Δ Ψ (c_eq (κₐ ⇒ κᵣ) (t_lam τ) (t_lam σ)) HP
             (extC κₐ Δ) (mkShift κₐ Δ)). }
  change (map shift Ψ ⊩ t_lam τs ≃ t_lam σs) in H1.
  assert (Hvar : map shift Ψ ⊩ v0 ≃ v0).
  { apply (tproves_refl κₐ (extC κₐ Δ) (map shift Ψ) v0). }
  pose proof (tpi_app H1 Hvar) as H2.
  pose proof (@tpi_beta (extC κₐ Δ) (map shift Ψ) κₐ κᵣ v0 τs) as HB1.
  pose proof (@tpi_beta (extC κₐ Δ) (map shift Ψ) κₐ κᵣ v0 σs) as HB2.
  assert (Eτ : tbind (mksubst κₐ v0) τs = τ)
    by (change (tbind (mksubst κₐ (@t_var (extC κₐ Δ) κₐ VZ eq_refl))
                 (tmap (liftA κₐ (mkShift κₐ Δ)) τ) = τ);
        apply subst_liftA_mkshift).
  assert (Eσ : tbind (mksubst κₐ v0) σs = σ)
    by (change (tbind (mksubst κₐ (@t_var (extC κₐ Δ) κₐ VZ eq_refl))
                 (tmap (liftA κₐ (mkShift κₐ Δ)) σ) = σ);
        apply subst_liftA_mkshift).
  change (map shift Ψ ⊩ t_app (t_lam τs) v0 ≃ tbind (mksubst κₐ v0) τs) in HB1.
  change (map shift Ψ ⊩ t_app (t_lam σs) v0 ≃ tbind (mksubst κₐ v0) σs) in HB2.
  rewrite Eτ in HB1. rewrite Eσ in HB2.
  eapply tpi_trans.
  - eapply tpi_symm. exact HB1.
  - eapply tpi_trans.
    + exact H2.
    + exact HB2.
Qed.


Lemma tctd_all_partial (κ : kind) (Δ : Ctx kind) (τ : typ (κ ⇒ ⋆) Δ) :
  tctd ((tc_all κ : typ ((κ ⇒ ⋆) ⇒ ⋆) Δ) τ) (tc_all κ).
Proof. apply inj_app. apply inj_ctor. Qed.

Lemma tctd_xist_partial (κ : kind) (Δ : Ctx kind) (τ : typ (κ ⇒ ⋆) Δ) :
  tctd ((tc_xist κ : typ ((κ ⇒ ⋆) ⇒ ⋆) Δ) τ) (tc_xist κ).
Proof. apply inj_app. apply inj_ctor. Qed.

Lemma tctd_rec_partial (κ : kind) (Δ : Ctx kind) (τ : typ (κ ⇒ κ) Δ) :
  tctd ((tc_rec κ : typ ((κ ⇒ κ) ⇒ κ) Δ) τ) (tc_rec κ).
Proof. apply inj_app. apply inj_ctor. Qed.

Lemma tproves_all_inj_same {Δ : Ctx kind} {Ψ : list (constr Δ)} {κ : kind}
      {τ τ' : typ ⋆ (extC κ Δ)} :
  Ψ ⊩ (∀ᵗ κ, τ) ≃ (∀ᵗ κ, τ') -> map shift Ψ ⊩ τ ≃ τ'.
Proof.
  intro HP.
  apply tproves_lam_inj.
  exact (tpi_appInjR (inj_ctor (tc_all κ)) (inj_ctor (tc_all κ)) HP).
Qed.

Lemma tproves_xist_inj_same {Δ : Ctx kind} {Ψ : list (constr Δ)} {κ : kind}
      {τ τ' : typ ⋆ (extC κ Δ)} :
  Ψ ⊩ (∃ᵗ κ, τ) ≃ (∃ᵗ κ, τ') -> map shift Ψ ⊩ τ ≃ τ'.
Proof.
  intro HP.
  apply tproves_lam_inj.
  exact (tpi_appInjR (inj_ctor (tc_xist κ)) (inj_ctor (tc_xist κ)) HP).
Qed.

Lemma tproves_rec_inj_same {Δ : Ctx kind} {Ψ : list (constr Δ)} {κ : kind}
      {τ τ' : typ κ (extC κ Δ)} :
  Ψ ⊩ (rec_type Δ κ τ) ≃ (rec_type Δ κ τ') -> map shift Ψ ⊩ τ ≃ τ'.
Proof.
  intro HP.
  apply tproves_lam_inj.
  unfold rec_type.
  exact (tpi_appInjR (inj_ctor (tc_rec κ)) (inj_ctor (tc_rec κ)) HP).
Qed.


Lemma typing_expr_tapp_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {e : expr V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
  forall (vA : value V), e = e_tapp vA ->
  exists κ τ0 σ, Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : ∀ᵗ κ, τ0 /\ Ψ ⊩ subst τ0 σ ≃ τ.
Proof.
  intro H.
  induction H using typing_expr_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (vA : value V), e = e_tapp vA ->
             exists κ τ0 σ, Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : ∀ᵗ κ, τ0 /\ Ψ ⊩ subst τ0 σ ≃ τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v0 : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ) => True).
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. destruct (IHtyping_expr vA EV) as (κ & τ0 & σ & HV & HEQ).
    exists κ, τ0, σ. split; [ exact HV | eapply tpi_trans; [ exact HEQ | eassumption ] ].
  - intros vA EV. discriminate EV.
  - intros vA EV. injection EV as E1. subst. exists κ, τ, σ. split; [ eassumption | apply tproves_refl ].
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - exact I. - exact I. - exact I. - exact I. - exact I. - exact I. - exact I.
  - exact I. - exact I. - exact I. - exact I. - exact I. - exact I.
Qed.

Lemma typing_expr_unpack_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {e : expr V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
  forall (vA : value V) (eA : expr (inc V)), e = e_unpack vA eA ->
  exists κ τ0 τ',
    Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : ∃ᵗ κ, τ0 /\
    extC κ Δ ∣ map shift Ψ ∣ (Env.compose shift Γ) ▹ τ0 ⊢ₑ eA : shift τ' /\
    Ψ ⊩ τ' ≃ τ.
Proof.
  intro H.
  induction H using typing_expr_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (vA : value V) (eA : expr (inc V)), e = e_unpack vA eA ->
             exists κ τ0 τc,
               Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : ∃ᵗ κ, τ0 /\
               extC κ Δ ∣ map shift Ψ ∣ (Env.compose shift Γ) ▹ τ0 ⊢ₑ eA : shift τc /\
               Ψ ⊩ τc ≃ τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v0 : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ) => True).
  - intros vA eA EV. discriminate EV.
  - intros vA eA EV. discriminate EV.
  - intros vA eA EV. destruct (IHtyping_expr vA eA EV) as (κ & τ0 & τc & HV & HB & HEQ).
    exists κ, τ0, τc. split; [ exact HV | split; [ exact HB | eapply tpi_trans; [ exact HEQ | eassumption ] ] ].
  - intros vA eA EV. discriminate EV.
  - intros vA eA EV. discriminate EV.
  - intros vA eA EV. discriminate EV.
  - intros vA eA EV. discriminate EV.
  - intros vA eA EV. discriminate EV.
  - intros vA eA EV. discriminate EV.
  - intros vA eA EV. injection EV as E1 E2. subst.
    exists κ, τ, τ'. split; [ eassumption | split; [ eassumption | apply tproves_refl ] ].
  - intros vA eA EV. discriminate EV.
  - intros vA eA EV. discriminate EV.
  - intros vA eA EV. discriminate EV.
  - intros vA eA EV. discriminate EV.
  - exact I. - exact I. - exact I. - exact I. - exact I. - exact I. - exact I.
  - exact I. - exact I. - exact I. - exact I. - exact I. - exact I.
Qed.

Lemma typing_expr_unroll_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {e : expr V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ ->
  forall (vA : value V), e = e_unroll vA ->
  exists κ τ0 σ₁ σ₂ (HF : rel_app κ (rec_type Δ κ τ0) (subst τ0 (rec_type Δ κ τ0)) ⋆ σ₁ σ₂),
    Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : σ₁ /\ Ψ ⊩ σ₂ ≃ τ.
Proof.
  intro H.
  induction H using typing_expr_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (vA : value V), e = e_unroll vA ->
             exists κ τ0 σ₁ σ₂
               (HF : rel_app κ (rec_type Δ κ τ0) (subst τ0 (rec_type Δ κ τ0)) ⋆ σ₁ σ₂),
               Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : σ₁ /\ Ψ ⊩ σ₂ ≃ τ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v0 : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ) => True).
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. destruct (IHtyping_expr vA EV) as (κ & τ0 & σ₁ & σ₂ & HF & HV & HEQ).
    exists κ, τ0, σ₁, σ₂, HF. split; [ exact HV | eapply tpi_trans; [ exact HEQ | eassumption ] ].
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. injection EV as E1. subst.
    exists κ, τ, σ₁, σ₂, HF. split; [ eassumption | apply tproves_refl ].
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - intros vA EV. discriminate EV.
  - exact I. - exact I. - exact I. - exact I. - exact I. - exact I. - exact I.
  - exact I. - exact I. - exact I. - exact I. - exact I. - exact I.
Qed.


Lemma preservation_LamBetaT
  (Hbox : forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (κ κ' : kind)
            (τ : typ ⋆ (extC κ Δ)) (τ' : typ ⋆ (extC κ' Δ)),
            Ψ ⊩ (∀ᵗ κ, τ) ≃ (∀ᵗ κ', τ') -> κ = κ')
  (e : expr ∅) :
  forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
    Δ ∣ Ψ ∣ □ ⊢ₑ e_tapp (v_tlam e) : τ -> Δ ∣ Ψ ∣ □ ⊢ₑ e : τ.
Proof.
  intros Δ Ψ τ H.
  destruct (typing_expr_tapp_inv H (v_tlam e) eq_refl)
    as (κ0 & τ0 & σ & HV & HEQ).
  destruct (Cval_tlam_inv (typing_val_canonical HV) e eq_refl)
    as (κb & τb & HEQall & HBODY).
  pose proof (Hbox Δ Ψ κb κ0 τb τ0 HEQall) as EK.
  subst κ0.
  assert (HEQbody : map shift Ψ ⊩ τb ≃ τ0)
    by (exact (tproves_all_inj_same HEQall)).
  assert (HB' : extC κb Δ ∣ map shift Ψ ∣ Env.compose shift □ ⊢ₑ e : τ0)
    by (eapply T_congE; [ exact HEQbody | exact HBODY ]).
  pose proof (typing_tapp_subst ∅ Δ Ψ □ κb σ e τ0 HB') as Hsub.
  eapply T_congE; [ exact HEQ | exact Hsub ].
Qed.

Lemma map_cbind_mksubst (κ : kind) (Δ : Ctx kind) (Ψ : list (constr Δ)) (σ : typ κ Δ) :
  map (cbind (mksubst κ σ)) (map shift Ψ) = Ψ.
Proof.
  rewrite <- (List.map_id Ψ) at 2.
  rewrite List.map_map. apply List.map_ext. intro ψ.
  change (cbind (mksubst κ σ)
    (@shift (Ctx kind) (@Arr kind) constr (@FMap_constr) (@extC kind κ)
       (@ShiftableCore_ext kind κ) Δ ψ) = ψ).
  apply cbind_mksubst_shift.
Qed.

Lemma tproves_subst_body {Δ : Ctx kind} {Ψ : list (constr Δ)} {κ : kind}
      {τ τ' : typ ⋆ (extC κ Δ)} {σ : typ κ Δ} :
  map shift Ψ ⊩ τ ≃ τ' -> Ψ ⊩ subst τ σ ≃ subst τ' σ.
Proof.
  intro HP.
  pose proof (tproves_cbind (extC κ Δ) (map shift Ψ) (c_eq ⋆ τ τ') HP
                Δ (mksubst κ σ) (mk_subst_pirr κ Δ σ)) as H.
  rewrite map_cbind_mksubst in H.
  change (Ψ ⊩ subst τ σ ≃ subst τ' σ) in H.
  exact H.
Qed.

Lemma preservation_UnpackE
  (Hxist : forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (κ κ' : kind)
             (τ : typ ⋆ (extC κ Δ)) (τ' : typ ⋆ (extC κ' Δ)),
             Ψ ⊩ (∃ᵗ κ, τ) ≃ (∃ᵗ κ', τ') -> κ = κ')
  (v : value ∅) (e : expr (inc ∅)) :
  forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
    Δ ∣ Ψ ∣ □ ⊢ₑ e_unpack (v_pack v) e : τ ->
    Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc) e v : τ.
Proof.
  intros Δ Ψ τ H.
  destruct (typing_expr_unpack_inv H (v_pack v) e eq_refl)
    as (κ0 & τ0 & τc & HV & HBODY & HEQ).
  destruct (Cval_pack_inv (typing_val_canonical HV) v eq_refl)
    as (κb & τb & τw & HEQx & Hpay).
  pose proof (Hxist Δ Ψ κb κ0 τb τ0 HEQx) as EK.
  subst κ0.
  assert (HEQbody : map shift Ψ ⊩ τb ≃ τ0)
    by (exact (tproves_xist_inj_same HEQx)).
  assert (Hpay' : Δ ∣ Ψ ∣ □ ⊢ᵥ v : subst τ0 τw)
    by (eapply T_congV; [ exact (tproves_subst_body (κ := κb) (σ := τw) HEQbody) | exact Hpay ]).
  pose proof (typing_unpack_subst ∅ Δ Ψ □ κb τ0 τc τw e HBODY) as HB.
  assert (Hsubst : Δ ∣ Ψ ∣ □ ⊢ₑ subst (Inc := inc) e v : τc).
  { change (Δ ∣ Ψ ∣ □ ⊢ₑ ebind (mk_subst v) e : τc).
    exact (typing_subst_one (V := ∅) (Δ := Δ) (Ψ := Ψ) (Γ := □) (v := v)
             (σ := subst τ0 τw) (e := e) (τ := τc) HB Hpay'). }
  eapply T_congE; [ exact HEQ | exact Hsubst ].
Qed.
Lemma preservation_UnrollE
  (Hroll : forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (κ κ' : kind)
             (τ : typ κ (extC κ Δ)) (τ' : typ κ' (extC κ' Δ))
             (σ₁ σ₂ σ₁' σ₂' : typ ⋆ Δ),
      rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂ ->
      rel_app κ' (rec_type Δ κ' τ') (subst τ' (rec_type Δ κ' τ')) ⋆ σ₁' σ₂' ->
      Ψ ⊩ σ₁ ≃ σ₁' -> Ψ ⊩ σ₂ ≃ σ₂')
  (v : value ∅) :
  forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (τ : typ ⋆ Δ),
    Δ ∣ Ψ ∣ □ ⊢ₑ e_unroll (v_roll v) : τ ->
    Δ ∣ Ψ ∣ □ ⊢ᵥ v : τ.
Proof.
  intros Δ Ψ τ H.
  destruct (typing_expr_unroll_inv H (v_roll v) eq_refl)
    as (κ0 & τ0 & σ₁ & σ₂ & HF0 & HV & HEQ).
  destruct (Cval_roll_inv (typing_val_canonical HV) v eq_refl)
    as (κb & τb & σ₁b & σ₂b & HFb & HEQroll & Hpay).
  assert (H₂ : Ψ ⊩ σ₂ ≃ σ₂b)
    by (exact (Hroll Δ Ψ κ0 κb τ0 τb σ₁ σ₂ σ₁b σ₂b HF0 HFb (tpi_symm HEQroll))).
  assert (Hv : Δ ∣ Ψ ∣ □ ⊢ᵥ v : σ₂)
    by (eapply T_congV; [ exact (tpi_symm H₂) | exact Hpay ]).
  eapply T_congV; [ exact HEQ | exact Hv ].
Qed.

Definition KArr_inj {a b c d : kind} (E : KArr a b = KArr c d) : (a = c) * (b = d) :=
  match E in _ = k' return (match k' with KArr x y => (a = x) * (b = y) | KTyp => True end) with
  | eq_refl => (eq_refl, eq_refl)
  end.


Lemma box_kind_eq_of_discr
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False) :
  forall (Δ : Ctx kind) (κ κ' : kind) (τ : typ ⋆ (extC κ Δ)) (τ' : typ ⋆ (extC κ' Δ)),
    nil ⊩ ((∀ᵗ κ, τ) ≃ (∀ᵗ κ', τ')) -> κ = κ'.
Proof.
  intros Δ κ κ' τ τ' HP.
  destruct (kindEqDec.eq_dec κ κ') as [e|ne]; [ exact e | exfalso ].
  apply (Hdiscr Δ (c_eq ⋆ (∀ᵗ κ, τ) (∀ᵗ κ', τ')) HP).
  unfold t_all.
  eapply (@td_ctd Δ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) ((κ' ⇒ ⋆) ⇒ ⋆)
            ((tc_all κ) (ƛ τ)) ((tc_all κ') (ƛ τ')) (tc_all κ) (tc_all κ')).
  - eapply (@inj_app Δ ⋆ (κ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (t_ctor (tc_all κ)) (ƛ τ) (tc_all κ)).
    apply (@inj_ctor Δ ((κ ⇒ ⋆) ⇒ ⋆) (tc_all κ)).
  - eapply (@inj_app Δ ⋆ (κ' ⇒ ⋆) ((κ' ⇒ ⋆) ⇒ ⋆) (t_ctor (tc_all κ')) (ƛ τ') (tc_all κ')).
    apply (@inj_ctor Δ ((κ' ⇒ ⋆) ⇒ ⋆) (tc_all κ')).
  - unfold cdiscrK.
    destruct (kindEqDec.eq_dec ((κ ⇒ ⋆) ⇒ ⋆) ((κ' ⇒ ⋆) ⇒ ⋆)) as [e|_].
    + exfalso. apply ne.
      destruct (KArr_inj e) as [e1 _].
      destruct (KArr_inj e1) as [ek _].
      exact ek.
    + exact I.
Qed.

Lemma xist_kind_eq_of_discr
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False) :
  forall (Δ : Ctx kind) (κ κ' : kind) (τ : typ ⋆ (extC κ Δ)) (τ' : typ ⋆ (extC κ' Δ)),
    nil ⊩ ((∃ᵗ κ, τ) ≃ (∃ᵗ κ', τ')) -> κ = κ'.
Proof.
  intros Δ κ κ' τ τ' HP.
  destruct (kindEqDec.eq_dec κ κ') as [e|ne]; [ exact e | exfalso ].
  apply (Hdiscr Δ (c_eq ⋆ (∃ᵗ κ, τ) (∃ᵗ κ', τ')) HP).
  unfold t_xist.
  eapply (@td_ctd Δ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) ((κ' ⇒ ⋆) ⇒ ⋆)
            ((tc_xist κ) (ƛ τ)) ((tc_xist κ') (ƛ τ')) (tc_xist κ) (tc_xist κ')).
  - eapply (@inj_app Δ ⋆ (κ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (t_ctor (tc_xist κ)) (ƛ τ) (tc_xist κ)).
    apply (@inj_ctor Δ ((κ ⇒ ⋆) ⇒ ⋆) (tc_xist κ)).
  - eapply (@inj_app Δ ⋆ (κ' ⇒ ⋆) ((κ' ⇒ ⋆) ⇒ ⋆) (t_ctor (tc_xist κ')) (ƛ τ') (tc_xist κ')).
    apply (@inj_ctor Δ ((κ' ⇒ ⋆) ⇒ ⋆) (tc_xist κ')).
  - unfold cdiscrK.
    destruct (kindEqDec.eq_dec ((κ ⇒ ⋆) ⇒ ⋆) ((κ' ⇒ ⋆) ⇒ ⋆)) as [e|_].
    + exfalso. apply ne.
      destruct (KArr_inj e) as [e1 _].
      destruct (KArr_inj e1) as [ek _].
      exact ek.
    + exact I.
Qed.


Lemma preservation_LamBetaT_nil
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  (e : expr ∅) :
  forall (Δ : Ctx kind) (τ : typ ⋆ Δ),
    Δ ∣ nil ∣ □ ⊢ₑ e_tapp (v_tlam e) : τ ->
    Δ ∣ nil ∣ □ ⊢ₑ e : τ.
Proof.
  intros Δ τ H.
  destruct (typing_expr_tapp_inv H (v_tlam e) eq_refl)
    as (κ0 & τ0 & σ & HV & HEQ).
  destruct (Cval_tlam_inv (typing_val_canonical HV) e eq_refl)
    as (κb & τb & HEQall & HBODY).
  pose proof (box_kind_eq_of_discr Hdiscr Δ κb κ0 τb τ0 HEQall) as EK.
  subst κ0.
  assert (HEQbody : map shift nil ⊩ τb ≃ τ0)
    by (exact (tproves_all_inj_same HEQall)).
  assert (HB' : extC κb Δ ∣ map shift nil ∣ Env.compose shift □ ⊢ₑ e : τ0)
    by (eapply T_congE; [ exact HEQbody | exact HBODY ]).
  pose proof (typing_tapp_subst ∅ Δ nil □ κb σ e τ0 HB') as Hsub.
  eapply T_congE; [ exact HEQ | exact Hsub ].
Qed.

Lemma preservation_UnpackE_nil
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  (v : value ∅) (e : expr (inc ∅)) :
  forall (Δ : Ctx kind) (τ : typ ⋆ Δ),
    Δ ∣ nil ∣ □ ⊢ₑ e_unpack (v_pack v) e : τ ->
    Δ ∣ nil ∣ □ ⊢ₑ subst (Inc := inc) e v : τ.
Proof.
  intros Δ τ H.
  destruct (typing_expr_unpack_inv H (v_pack v) e eq_refl)
    as (κ0 & τ0 & τc & HV & HBODY & HEQ).
  destruct (Cval_pack_inv (typing_val_canonical HV) v eq_refl)
    as (κb & τb & τw & HEQx & Hpay).
  pose proof (xist_kind_eq_of_discr Hdiscr Δ κb κ0 τb τ0 HEQx) as EK.
  subst κ0.
  assert (HEQbody : map shift nil ⊩ τb ≃ τ0)
    by (exact (tproves_xist_inj_same HEQx)).
  assert (Hpay' : Δ ∣ nil ∣ □ ⊢ᵥ v : subst τ0 τw)
    by (eapply T_congV; [ exact (tproves_subst_body (κ := κb) (σ := τw) HEQbody) | exact Hpay ]).
  pose proof (typing_unpack_subst ∅ Δ nil □ κb τ0 τc τw e HBODY) as HB.
  assert (Hsubst : Δ ∣ nil ∣ □ ⊢ₑ subst (Inc := inc) e v : τc).
  { change (Δ ∣ nil ∣ □ ⊢ₑ ebind (mk_subst v) e : τc).
    exact (typing_subst_one (V := ∅) (Δ := Δ) (Ψ := nil) (Γ := □) (v := v)
             (σ := subst τ0 τw) (e := e) (τ := τc) HB Hpay'). }
  eapply T_congE; [ exact HEQ | exact Hsubst ].
Qed.


Lemma preservation_UnrollE_nil
  (Hroll : forall (Δ : Ctx kind) (κ κ' : kind)
             (τ : typ κ (extC κ Δ)) (τ' : typ κ' (extC κ' Δ))
             (σ₁ σ₂ σ₁' σ₂' : typ ⋆ Δ),
      rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂ ->
      rel_app κ' (rec_type Δ κ' τ') (subst τ' (rec_type Δ κ' τ')) ⋆ σ₁' σ₂' ->
      nil ⊩ σ₁ ≃ σ₁' -> nil ⊩ σ₂ ≃ σ₂')
  (v : value ∅) :
  forall (Δ : Ctx kind) (τ : typ ⋆ Δ),
    Δ ∣ nil ∣ □ ⊢ₑ e_unroll (v_roll v) : τ ->
    Δ ∣ nil ∣ □ ⊢ᵥ v : τ.
Proof.
  intros Δ τ H.
  destruct (typing_expr_unroll_inv H (v_roll v) eq_refl)
    as (κ0 & τ0 & σ₁ & σ₂ & HF0 & HV & HEQ).
  destruct (Cval_roll_inv (typing_val_canonical HV) v eq_refl)
    as (κb & τb & σ₁b & σ₂b & HFb & HEQroll & Hpay).
  assert (H₂ : nil ⊩ σ₂ ≃ σ₂b)
    by (exact (Hroll Δ κ0 κb τ0 τb σ₁ σ₂ σ₁b σ₂b HF0 HFb (tpi_symm HEQroll))).
  assert (Hv : Δ ∣ nil ∣ □ ⊢ᵥ v : σ₂)
    by (eapply T_congV; [ exact (tpi_symm H₂) | exact Hpay ]).
  eapply T_congV; [ exact HEQ | exact Hv ].
Qed.

Lemma rec_type_tctd (Δ : Ctx kind) (κ : kind) (τ : typ κ (extC κ Δ)) :
  tctd (rec_type Δ κ τ) (tc_rec κ).
Proof.
  unfold rec_type.
  eapply (@inj_app Δ κ (κ ⇒ κ) ((κ ⇒ κ) ⇒ κ)
            (t_ctor (tc_rec κ)) (ƛ τ) (tc_rec κ)).
  apply (@inj_ctor Δ ((κ ⇒ κ) ⇒ κ) (tc_rec κ)).
Qed.

Lemma rel_app_tctd_left {Δ : Ctx kind} {κ : kind} (a b : typ κ Δ) :
  forall {κ₂ : kind} (σ₁ σ₂ : typ κ₂ Δ),
    rel_app κ a b κ₂ σ₁ σ₂ ->
    forall {κc : kind} (c : tctor κc), tctd a c -> tctd σ₁ c.
Proof.
  intros κ₂ σ₁ σ₂ H.
  induction H as [| κa κr f₁ f₂ u Hf IH]; intros κc c HI.
  - exact HI.
  - eapply (@inj_app Δ κr κa κc f₁ u c). apply IH; exact HI.
Qed.

Lemma tproves_subst_body_k {Δ : Ctx kind} {Ψ : list (constr Δ)} {κ κr : kind}
      {τ τ' : typ κr (extC κ Δ)} {σ : typ κ Δ} :
  map shift Ψ ⊩ τ ≃ τ' -> Ψ ⊩ subst τ σ ≃ subst τ' σ.
Proof.
  intro HP.
  pose proof (tproves_cbind (extC κ Δ) (map shift Ψ) (c_eq κr τ τ') HP
                Δ (mksubst κ σ) (mk_subst_pirr κ Δ σ)) as H.
  rewrite map_cbind_mksubst in H.
  change (Ψ ⊩ subst τ σ ≃ subst τ' σ) in H.
  exact H.
Qed.

Lemma roll_kinds_eq_of_discr
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False) :
  forall (Δ : Ctx kind) (κ κ' : kind) (τ : typ κ (extC κ Δ)) (τ' : typ κ' (extC κ' Δ))
         (σ₁ σ₂ σ₁' σ₂' : typ ⋆ Δ),
    rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂ ->
    rel_app κ' (rec_type Δ κ' τ') (subst τ' (rec_type Δ κ' τ')) ⋆ σ₁' σ₂' ->
    nil ⊩ σ₁ ≃ σ₁' -> κ = κ'.
Proof.
  intros Δ κ κ' τ τ' σ₁ σ₂ σ₁' σ₂' HF HF' HEQ.
  destruct (kindEqDec.eq_dec κ κ') as [e|ne]; [ exact e | exfalso ].
  apply (Hdiscr Δ (c_eq ⋆ σ₁ σ₁') HEQ).
  eapply (@td_ctd Δ ⋆ ((κ ⇒ κ) ⇒ κ) ((κ' ⇒ κ') ⇒ κ') σ₁ σ₁' (tc_rec κ) (tc_rec κ')).
  - eapply (@rel_app_tctd_left Δ κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂).
    + exact HF.
    + apply rec_type_tctd.
  - eapply (@rel_app_tctd_left Δ κ' (rec_type Δ κ' τ') (subst τ' (rec_type Δ κ' τ')) ⋆ σ₁' σ₂').
    + exact HF'.
    + apply rec_type_tctd.
  - unfold cdiscrK.
    destruct (kindEqDec.eq_dec ((κ ⇒ κ) ⇒ κ) ((κ' ⇒ κ') ⇒ κ')) as [e|_].
    + exfalso. apply ne. destruct (KArr_inj e) as [_ ek]. exact ek.
    + exact I.
Qed.

Definition Typable (e : expr ∅) : Prop :=
  exists (Δ : Ctx kind) (τ : typ ⋆ Δ), Δ ∣ nil ∣ □ ⊢ₑ e : τ.

Lemma typing_expr_empty_ctx {Δ : Ctx kind} {Ψ : list (constr Δ)} {τ : typ ⋆ Δ}
      (e : expr ∅) (Γ : ∅ -> typ ⋆ Δ) :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ -> Δ ∣ Ψ ∣ □ ⊢ₑ e : τ.
Proof.
  intro H.
  eapply (proj1 typing_ctx_congr_mut _ _ _ Γ e τ H □).
  intro x. destruct x.
Qed.

Lemma typable_LamBetaT (e : expr ∅) :
  Typable (e_tapp (v_tlam e)) -> Typable e.
Proof.
  intros (Δ & τ & H).
  destruct (typing_expr_tapp_inv H (v_tlam e) eq_refl)
    as (κ0 & τ0 & σ & HV & HEQ).
  destruct (Cval_tlam_inv (typing_val_canonical HV) e eq_refl)
    as (κb & τb & HEQall & HBODY).
  exists (extC κb Δ), τb.
  eapply typing_expr_empty_ctx. exact HBODY.
Qed.

Lemma typable_UnrollE (v : value ∅) :
  Typable (e_unroll (v_roll v)) -> Typable v.
Proof.
  intros (Δ & τ & H).
  destruct (typing_expr_unroll_inv H (v_roll v) eq_refl)
    as (κ0 & τ0 & σ₁ & σ₂ & HF & HV & HEQ).
  destruct (Cval_roll_inv (typing_val_canonical HV) v eq_refl)
    as (κb & τb & σ₁b & σ₂b & HFb & HEQroll & Hpay).
  unfold Typable. eexists. eexists. exact (@T_val ∅ Δ nil □ σ₂b v Hpay).
Qed.

Lemma typable_UnpackE
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  (v : value ∅) (e : expr (inc ∅)) :
  Typable (e_unpack (v_pack v) e) -> Typable (subst (Inc := inc) e v).
Proof.
  intros (Δ & τ & H).
  exists Δ, τ.
  exact (preservation_UnpackE_nil Hdiscr v e Δ τ H).
Qed.

Lemma tproves_subst_parm {Δ : Ctx kind} {κ κr : kind}
    (body : typ κr (extC κ Δ)) {a a' : typ κ Δ} :
  nil ⊩ a ≃ a' -> nil ⊩ subst body a ≃ subst body a'.
Proof.
  intro H.
  assert (Happ : nil ⊩ (ƛ body) a ≃ (ƛ body) a').
  { eapply tpi_app.
    - eapply tpi_lam. apply tproves_refl.
    - exact H. }
  pose proof (@tpi_beta Δ nil κ κr a body) as Hb.
  pose proof (@tpi_beta Δ nil κ κr a' body) as Hb'.
  eapply tpi_trans.
  - exact (tpi_symm Hb).
  - eapply tpi_trans; [ exact Happ | exact Hb' ].
Qed.

Fixpoint kind_size (k : kind) : nat :=
  match k with
  | KTyp => 0
  | KArr a b => S (kind_size a + kind_size b)
  end.

Inductive rargs (Δ : Ctx kind) : kind -> kind -> Type :=
| rargs_nil {κ} : rargs Δ κ κ
| rargs_cons {κ κa κr : kind} (pre : rargs Δ κ (κa ⇒ κr)) (u : typ κa Δ) :
    rargs Δ κ κr.

Arguments rargs_nil {Δ κ}.
Arguments rargs_cons {Δ κ κa κr}.

Fixpoint rargs_apply {Δ : Ctx kind} {κ κ₂ : kind} (a : typ κ Δ) (args : rargs Δ κ κ₂)
    {struct args} : typ κ₂ Δ :=
  match args as ar in rargs _ k1 k2 return typ k1 Δ -> typ k2 Δ with
  | rargs_nil => fun a => a
  | rargs_cons pre u => fun a => rargs_apply a pre u
  end a.

Inductive kind_reach : kind -> kind -> Type :=
| kr_refl (k : kind) : kind_reach k k
| kr_step {a r k2 : kind} : kind_reach r k2 -> kind_reach (a ⇒ r) k2.

Lemma kind_reach_cod {κ k2 : kind} (H : kind_reach κ k2) :
  forall κa κr : kind, k2 = κa ⇒ κr -> kind_reach κ κr.
Proof.
  induction H as [k | a r k2 Hpre IH]; intros κa κr E.
  - rewrite E. apply (@kr_step κa κr κr). apply kr_refl.
  - apply (@kr_step a r κr). apply (IH κa κr E).
Qed.

Lemma kind_reach_size {κ κ₂ : kind} (H : kind_reach κ κ₂) :
  kind_size κ₂ <= kind_size κ.
Proof.
  induction H as [k | a r k2 Hpre IH].
  - lia.
  - simpl in *. lia.
Qed.



Lemma kind_reach_cod_det {κ κa κa' κr : kind}
      (H1 : kind_reach κ (κa ⇒ κr)) (H2 : kind_reach κ (κa' ⇒ κr)) :
  κa = κa'.
Proof.
  refine (kind_reach_ind
    (fun κ k2 H => forall (κa κr : kind), k2 = κa ⇒ κr ->
                   forall κa', kind_reach κ (κa' ⇒ κr) -> κa = κa') _ _ κ (κa ⇒ κr) H1 κa κr eq_refl κa' H2).
  - intros k ka kr E ka' H2c.
    rewrite E in H2c.
    dependent destruction H2c.
    + reflexivity.
    + exfalso. match goal with Hx : kind_reach _ (ka' ⇒ kr) |- _ => pose proof (kind_reach_size Hx) as Hs; simpl in Hs; lia end.
  - intros a r k2 Hpre IH ka kr E ka' H2c.
    dependent destruction H2c.
    + exfalso. pose proof (kind_reach_size Hpre) as Hs. simpl in *. lia.
    + match goal with Hx : kind_reach _ (ka' ⇒ kr) |- _ => apply (IH ka kr E ka' Hx) end.
Qed.

Lemma rargs_reach {Δ : Ctx kind} {κ κ₂ : kind} (args : rargs Δ κ κ₂) :
  kind_reach κ κ₂.
Proof.
  induction args as [κ0 | κ κa κr pre IH u].
  - apply kr_refl.
  - apply (kind_reach_cod IH κa κr eq_refl).
Qed.

Lemma rargs_apply_tctd {Δ : Ctx kind} {κ κ₂ : kind} (a : typ κ Δ) (args : rargs Δ κ κ₂)
    {κc : kind} (c : tctor κc) :
  tctd a c -> tctd (rargs_apply a args) c.
Proof.
  intro HI.
  induction args as [κ0 | κ κa κr pre IH u].
  - exact HI.
  - simpl. eapply (@inj_app Δ κr κa κc (rargs_apply a pre) u c). apply IH; exact HI.
Qed.

Lemma rel_app_rargs {Δ : Ctx kind} {κ : kind} (a b : typ κ Δ) :
  forall {κ₂ : kind} {σ₁ σ₂ : typ κ₂ Δ},
    rel_app κ a b κ₂ σ₁ σ₂ ->
    exists args : rargs Δ κ κ₂,
      σ₁ = rargs_apply a args /\ σ₂ = rargs_apply b args.
Proof.
  intros κ₂ σ₁ σ₂ H.
  induction H as [| κa κr f₁ f₂ u Hpre IH].
  - exists rargs_nil. split; reflexivity.
  - destruct IH as (args & E1 & E2). subst f₁ f₂.
    exists (rargs_cons args u). split; reflexivity.
Qed.

Lemma rargs_size_final {Δ : Ctx kind} {κ κ₂ : kind} (args : rargs Δ κ κ₂) :
  κ₂ = κ \/ kind_size κ₂ < kind_size κ.
Proof.
  induction args as [κ0 | κ κa κr pre IH u].
  - left; reflexivity.
  - right. destruct IH as [e|H]; subst; simpl in *; lia.
Qed.

Inductive rargs_rel {Δ : Ctx kind} : forall κ κ₂, rargs Δ κ κ₂ -> rargs Δ κ κ₂ -> Prop :=
| rargs_rel_nil (κ : kind) : @rargs_rel Δ κ κ (@rargs_nil Δ κ) (@rargs_nil Δ κ)
| rargs_rel_cons {κ κa κr : kind}
    {pre1 pre2 : rargs Δ κ (κa ⇒ κr)} {u1 u2 : typ κa Δ} :
    @rargs_rel Δ κ (κa ⇒ κr) pre1 pre2 -> nil ⊩ u1 ≃ u2 ->
    @rargs_rel Δ κ κr (rargs_cons pre1 u1) (rargs_cons pre2 u2).

Arguments rargs_rel_nil {Δ κ}.
Arguments rargs_rel_cons {Δ κ κa κr pre1 pre2 u1 u2}.

Lemma rargs_rel_apply {Δ : Ctx kind} {κ κ₂ : kind} {args1 args2 : rargs Δ κ κ₂} :
  @rargs_rel Δ κ κ₂ args1 args2 ->
  forall (a a' : typ κ Δ), nil ⊩ a ≃ a' ->
    nil ⊩ rargs_apply a args1 ≃ rargs_apply a' args2.
Proof.
  intros Hrel a a' Ha.
  induction Hrel as [κ0 | κ κa κr pre1 pre2 u1 u2 Hrel IH Ht].
  - cbn. exact Ha.
  - cbn. eapply tpi_app.
    + apply (IH a a' Ha).
    + exact Ht.
Qed.





Lemma rargs_nil_inv {Δ : Ctx kind} {κ : kind} (args : rargs Δ κ κ) :
  args = rargs_nil.
Proof.
  dependent destruction args.
  - reflexivity.
  - exfalso. destruct (rargs_size_final args) as [e|H].
    + pose proof (f_equal kind_size e) as Hs. simpl in Hs. lia.
    + simpl in *. lia.
Qed.



Lemma rargs_align_of_eq {Δ : Ctx kind} {κ κ₂ : kind} (a a' : typ κ Δ)
    (args1 : rargs Δ κ κ₂) :
  forall (args2 : rargs Δ κ κ₂) {κc : kind} (c : tctor κc),
    tctd a c -> tctd a' c ->
    nil ⊩ rargs_apply a args1 ≃ rargs_apply a' args2 ->
    nil ⊩ a ≃ a' /\ @rargs_rel Δ κ κ₂ args1 args2.
Proof.
  refine (@rargs_ind Δ
    (fun κ κ₂ args1 => forall (a a' : typ κ Δ) (args2 : rargs Δ κ κ₂)
       (κc : kind) (c : tctor κc),
       tctd a c -> tctd a' c ->
       nil ⊩ rargs_apply a args1 ≃ rargs_apply a' args2 ->
       nil ⊩ a ≃ a' /\ @rargs_rel Δ κ κ₂ args1 args2) _ _ κ κ₂ args1 a a').
  - intros κ0 a0 a'0 args2 κc c Ha Ha' HEQ.
    dependent destruction args2.
    + split; [ exact HEQ | apply rargs_rel_nil ].
    + exfalso.
      match goal with Hx : rargs _ _ (_ ⇒ _) |- _ =>
        destruct (rargs_size_final Hx) as [e|Hs];
        [ pose proof (f_equal kind_size e) as Hsz; simpl in Hsz; lia
        | simpl in *; lia ] end.
  - intros kb κa κr pre IH u1 a0 a'0 args2 κc c Ha Ha' HEQ.
    dependent destruction args2.
    + exfalso.
      match goal with Hx : rargs _ _ (_ ⇒ _) |- _ =>
        destruct (rargs_size_final Hx) as [e|Hs];
        [ pose proof (f_equal kind_size e) as Hsz; simpl in Hsz; lia
        | simpl in *; lia ] end.
    + assert (Edom : κa = κa0)
        by (apply (kind_reach_cod_det (rargs_reach pre) (rargs_reach args2))).
      subst κa0.
      assert (Harg : nil ⊩ u1 ≃ u).
      { eapply tpi_appInjR.
        - apply (rargs_apply_tctd a0 pre c Ha).
        - apply (rargs_apply_tctd a'0 args2 c Ha').
        - cbn. exact HEQ. }
      assert (Hfun : nil ⊩ rargs_apply a0 pre ≃ rargs_apply a'0 args2).
      { eapply tpi_appInjL.
        - apply (rargs_apply_tctd a0 pre c Ha).
        - apply (rargs_apply_tctd a'0 args2 c Ha').
        - cbn. exact HEQ. }
      destruct (IH a0 a'0 args2 κc c Ha Ha' Hfun) as [Hbase Hrel].
      split; [ exact Hbase | apply (rargs_rel_cons Hrel Harg) ].
Qed.

Lemma rec_body_eq_of_base_eq {Δ : Ctx kind} {κ : kind}
    (τ τ' : typ κ (extC κ Δ)) :
  nil ⊩ rec_type Δ κ τ ≃ rec_type Δ κ τ' -> nil ⊩ τ ≃ τ'.
Proof.
  intro HP.
  assert (Hlam : nil ⊩ ((ƛ τ) : typ (κ ⇒ κ) Δ) ≃ ((ƛ τ') : typ (κ ⇒ κ) Δ)).
  { eapply tpi_appInjR.
    - apply (@inj_ctor Δ ((κ ⇒ κ) ⇒ κ) (tc_rec κ)).
    - apply (@inj_ctor Δ ((κ ⇒ κ) ⇒ κ) (tc_rec κ)).
    - change (nil ⊩ (tc_rec κ) (ƛ τ) ≃ (tc_rec κ) (ƛ τ')). exact HP. }
  pose proof (tproves_lam_inj Hlam) as Hb.
  change (nil ⊩ τ ≃ τ') in Hb.
  exact Hb.
Qed.

Lemma roll_eq_of_discr
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False) :
  forall (Δ : Ctx kind) (κ κ' : kind)
         (τ : typ κ (extC κ Δ)) (τ' : typ κ' (extC κ' Δ))
         (σ₁ σ₂ σ₁' σ₂' : typ ⋆ Δ),
    rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂ ->
    rel_app κ' (rec_type Δ κ' τ') (subst τ' (rec_type Δ κ' τ')) ⋆ σ₁' σ₂' ->
    nil ⊩ σ₁ ≃ σ₁' -> nil ⊩ σ₂ ≃ σ₂'.
Proof.
  intros Δ κ κ' τ τ' σ₁ σ₂ σ₁' σ₂' HF HF' H1.
  pose proof (roll_kinds_eq_of_discr Hdiscr Δ κ κ' τ τ' σ₁ σ₂ σ₁' σ₂' HF HF' H1) as EK.
  subst κ'.
  destruct (@rel_app_rargs Δ κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂ HF)
    as (args1 & E11 & E12).
  destruct (@rel_app_rargs Δ κ (rec_type Δ κ τ') (subst τ' (rec_type Δ κ τ')) ⋆ σ₁' σ₂' HF')
    as (args2 & E21 & E22).
  subst σ₁. subst σ₂. subst σ₁'. subst σ₂'.
  destruct (@rargs_align_of_eq Δ κ ⋆ (rec_type Δ κ τ) (rec_type Δ κ τ') args1 args2
              ((κ ⇒ κ) ⇒ κ) (tc_rec κ) (rec_type_tctd Δ κ τ) (rec_type_tctd Δ κ τ') H1)
    as [Hbase Hrel].
  assert (Hτ : nil ⊩ τ ≃ τ') by (eapply rec_body_eq_of_base_eq; exact Hbase).
  assert (Hb1 : nil ⊩ subst τ (rec_type Δ κ τ) ≃ subst τ' (rec_type Δ κ τ))
    by (eapply tproves_subst_body_k; exact Hτ).
  assert (Hb2 : nil ⊩ subst τ' (rec_type Δ κ τ) ≃ subst τ' (rec_type Δ κ τ'))
    by (eapply tproves_subst_parm; exact Hbase).
  assert (Hb : nil ⊩ subst τ (rec_type Δ κ τ) ≃ subst τ' (rec_type Δ κ τ'))
    by (eapply tpi_trans; [ exact Hb1 | exact Hb2 ]).
  exact (@rargs_rel_apply Δ κ ⋆ args1 args2 Hrel
           (subst τ (rec_type Δ κ τ)) (subst τ' (rec_type Δ κ τ')) Hb).
Qed.



Lemma typing_expr_abort_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {e : expr V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ -> forall (vA : value V), e = e_abort vA -> Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : ⊥.
Proof.
  intro H.
  induction H using typing_expr_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             forall (vA : value V), e = e_abort vA -> Δ ∣ Ψ ∣ Γ ⊢ᵥ vA : ⊥)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v0 : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ) => True).
  - (* T_val *) intros vA EV. discriminate EV.
  - (* T_bind *) intros vA EV. discriminate EV.
  - (* T_congE *) intros vA EV. eapply (IHtyping_expr vA EV).
  - (* T_app *) intros vA EV. discriminate EV.
  - (* T_tapp *) intros vA EV. discriminate EV.
  - (* T_projL *) intros vA EV. discriminate EV.
  - (* T_projR *) intros vA EV. discriminate EV.
  - (* T_abort *) intros vA EV. injection EV as EV. subst. assumption.
  - (* T_case *) intros vA EV. discriminate EV.
  - (* T_unpack *) intros vA EV. discriminate EV.
  - (* T_unroll *) intros vA EV. discriminate EV.
  - (* T_cabort *) intros vA EV. discriminate EV.
  - (* T_capp *) intros vA EV. discriminate EV.
  - (* T_lwith *) intros vA EV. discriminate EV.
  - (* T_var *) exact I. - (* T_congV *) exact I. - (* T_unit *) exact I.
  - (* T_lam *) exact I. - (* T_pair *) exact I. - (* T_injl *) exact I.
  - (* T_injr *) exact I. - (* T_tlam *) exact I. - (* T_pack *) exact I.
  - (* T_roll *) exact I. - (* T_lamC *) exact I. - (* T_withC *) exact I.
  - (* T_rec *) exact I.
Qed.

Lemma typing_expr_cabort_inv {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} {Γ : V -> typ ⋆ Δ}
      {e : expr V} {τ : typ ⋆ Δ} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ -> e = e_cabort -> exists ψ, Ψ ⊩ ψ /\ ⊮ ψ.
Proof.
  intro H.
  induction H using typing_expr_mut with
    (P := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (e : expr V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) =>
             e = e_cabort -> exists ψ, Ψ ⊩ ψ /\ ⊮ ψ)
    (P0 := fun (V : Set) (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> typ ⋆ Δ)
               (v0 : value V) (τ : typ ⋆ Δ) (_ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v0 : τ) => True).
  - (* T_val *) intro EV. discriminate EV.
  - (* T_bind *) intro EV. discriminate EV.
  - (* T_congE *) intro EV. eapply IHtyping_expr. exact EV.
  - (* T_app *) intro EV. discriminate EV.
  - (* T_tapp *) intro EV. discriminate EV.
  - (* T_projL *) intro EV. discriminate EV.
  - (* T_projR *) intro EV. discriminate EV.
  - (* T_abort *) intro EV. discriminate EV.
  - (* T_case *) intro EV. discriminate EV.
  - (* T_unpack *) intro EV. discriminate EV.
  - (* T_unroll *) intro EV. discriminate EV.
  - (* T_cabort *) intro EV. exists ψ. split; assumption.
  - (* T_capp *) intro EV. discriminate EV.
  - (* T_lwith *) intro EV. discriminate EV.
  - (* T_var *) exact I. - (* T_congV *) exact I. - (* T_unit *) exact I.
  - (* T_lam *) exact I. - (* T_pair *) exact I. - (* T_injl *) exact I.
  - (* T_injr *) exact I. - (* T_tlam *) exact I. - (* T_pack *) exact I.
  - (* T_roll *) exact I. - (* T_lamC *) exact I. - (* T_withC *) exact I.
  - (* T_rec *) exact I.
Qed.

Definition no_star_arr (k1 k2 : kind) (E : KTyp = KArr k1 k2) : False :=
  match E in _ = k' return (match k' with KTyp => True | KArr _ _ => False end) with
  | eq_refl => I
  end.

Ltac kind_contra E :=
  lazymatch type of E with
  | KTyp = KArr _ _ => exact (no_star_arr _ _ E)
  | KArr _ _ = KTyp => exact (no_star_arr _ _ (eq_sym E))
  | KArr ?a ?b = KArr ?c ?d =>
      let p := fresh "p" in
      pose proof (KArr_inj E) as p;
      let e1 := fresh "e1" in
      let e2 := fresh "e2" in
      destruct p as [e1 e2];
      first [ kind_contra e1 | kind_contra e2 ]
  | _ => idtac
  end.

Ltac solve_cdiscrK :=
  unfold cdiscrK;
  match goal with
  | |- context [kindEqDec.eq_dec ?K ?K] =>
      let e := fresh "e" in let ne := fresh "ne" in let H := fresh "H" in
      destruct (kindEqDec.eq_dec K K) as [e|ne];
      [ assert (H : e = eq_refl) by (apply UIP_dec; exact kindEqDec.eq_dec);
        rewrite H; cbn; constructor
      | exfalso; apply ne; reflexivity ]
  | |- context [kindEqDec.eq_dec ?K1 ?K2] =>
      let e := fresh "e" in let ne := fresh "ne" in
      destruct (kindEqDec.eq_dec K1 K2) as [e|ne];
      [ exfalso; kind_contra e
      | exact I ]
  end.

Lemma cdiscr_unit_arr : cdiscrK tc_unit tc_arr.
Proof. solve_cdiscrK. Qed.
Lemma cdiscr_arr_sum : cdiscrK tc_arr tc_sum.
Proof. solve_cdiscrK. Qed.
Lemma cdiscr_all_xist (k : kind) : cdiscrK (tc_all k) (tc_xist k).
Proof. solve_cdiscrK. Qed.
Lemma cdiscr_arr_all (k : kind) : cdiscrK tc_arr (tc_all k).
Proof. solve_cdiscrK. Qed.

Lemma tctd_all_ty (κ : kind) (Δ : Ctx kind) (τ : typ ⋆ (extC κ Δ)) :
  tctd (∀ᵗ κ, τ) (tc_all κ).
Proof.
  unfold t_all.
  eapply (@inj_app Δ ⋆ (κ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (t_ctor (tc_all κ)) (t_lam τ) (tc_all κ)).
  apply (@inj_ctor Δ ((κ ⇒ ⋆) ⇒ ⋆) (tc_all κ)).
Qed.

Lemma tctd_xist_ty (κ : kind) (Δ : Ctx kind) (τ : typ ⋆ (extC κ Δ)) :
  tctd (∃ᵗ κ, τ) (tc_xist κ).
Proof.
  unfold t_xist.
  eapply (@inj_app Δ ⋆ (κ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (t_ctor (tc_xist κ)) (t_lam τ) (tc_xist κ)).
  apply (@inj_ctor Δ ((κ ⇒ ⋆) ⇒ ⋆) (tc_xist κ)).
Qed.

Lemma tctd_rec_ty (κ : kind) (Δ : Ctx kind) (τ : typ κ (extC κ Δ)) :
  tctd (rec_type Δ κ τ) (tc_rec κ).
Proof.
  unfold rec_type.
  eapply (@inj_app Δ κ (κ ⇒ κ) ((κ ⇒ κ) ⇒ κ) (t_ctor (tc_rec κ)) (t_lam τ) (tc_rec κ)).
  apply (@inj_ctor Δ ((κ ⇒ κ) ⇒ κ) (tc_rec κ)).
Qed.

Ltac hdiscr_concl Hdiscr E :=
  exfalso; eapply Hdiscr; [ exact E | ].



Lemma rel_app_tctd_leftP {Δ : Ctx kind} {κ : kind} (a b : typ κ Δ) :
  forall {κ₂ : kind} (σ₁ σ₂ : typ κ₂ Δ),
    rel_app κ a b κ₂ σ₁ σ₂ ->
    forall {κc : kind} (c : tctor κc), tctd a c -> tctd σ₁ c.
Proof.
  intros κ₂ σ₁ σ₂ H.
  induction H as [| κa κr f₁ f₂ u Hf IH]; intros κc c HI.
  - exact HI.
  - eapply (@inj_app Δ κr κa κc f₁ u c). apply IH; exact HI.
Qed.

Lemma Cval_arrow_shape
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  {Δ : Ctx kind} {v : value ∅} {τ1 τ2 : typ ⋆ Δ}
  (D : Cval ∅ Δ nil □ v (τ1 →ᵗ τ2)) :
  (exists e, v = v_lam e) \/ (exists e, v = v_fix e).
Proof.
  destruct v as [x| |e|v1 v2|ax v|e|v0|v0|e|v0|e].
  - destruct x.
  - (* unit *) exfalso.
    pose proof (Cval_unit_inv D eq_refl) as E.
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ⊤ (τ1 →ᵗ τ2) tc_unit tc_arr).
    + apply inj_ctor.
    + apply tctd_arr_app.
    + solve_cdiscrK.
  - (* lam *) left; eexists; reflexivity.
  - (* pair *) exfalso.
    destruct (Cval_pair_inv D v1 v2 eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (t_prod a b) (τ1 →ᵗ τ2) tc_prod tc_arr).
    + apply tctd_prod_app.
    + apply tctd_arr_app.
    + solve_cdiscrK.
  - (* inj *) destruct ax.
    + (* L *) exfalso.
      destruct (Cval_injl_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (t_sum a b) (τ1 →ᵗ τ2) tc_sum tc_arr).
      * apply tctd_sum_app.
      * apply tctd_arr_app.
      * solve_cdiscrK.
    + (* R *) exfalso.
      destruct (Cval_injr_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (t_sum a b) (τ1 →ᵗ τ2) tc_sum tc_arr).
      * apply tctd_sum_app.
      * apply tctd_arr_app.
      * solve_cdiscrK.
  - (* tlam *) exfalso.
    destruct (Cval_tlam_inv D e eq_refl) as (κ & τ0 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (∀ᵗ κ, τ0) (τ1 →ᵗ τ2) (tc_all κ) tc_arr).
    + apply tctd_all_ty.
    + apply tctd_arr_app.
    + solve_cdiscrK.
  - (* pack *) exfalso.
    destruct (Cval_pack_inv D v0 eq_refl) as (κ & a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (∃ᵗ κ, a) (τ1 →ᵗ τ2) (tc_xist κ) tc_arr).
    + apply tctd_xist_ty.
    + apply tctd_arr_app.
    + solve_cdiscrK.
  - (* roll *) exfalso.
    destruct (Cval_roll_inv D v0 eq_refl) as (κ & a & b & c & HF & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ κ) ⇒ κ) (⋆ ⇒ ⋆ ⇒ ⋆) b (τ1 →ᵗ τ2) (tc_rec κ) tc_arr).
    + eapply (@rel_app_tctd_leftP Δ κ (rec_type Δ κ a) (subst a (rec_type Δ κ a)) ⋆ b c); [ exact HF | apply tctd_rec_ty ].
    + apply tctd_arr_app.
    + solve_cdiscrK.
  - (* lamC *) exfalso.
    destruct (Cval_lamC_inv D e eq_refl) as (φ & τ0 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_carr_ctd Δ φ τ0 (τ1 →ᵗ τ2) (⋆ ⇒ ⋆ ⇒ ⋆) tc_arr).
    apply tctd_arr_app.
  - (* withC *) exfalso.
    destruct (Cval_withC_inv D v0 eq_refl) as (φ & τ0 & E & _ & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_cprod_ctd Δ φ τ0 (τ1 →ᵗ τ2) (⋆ ⇒ ⋆ ⇒ ⋆) tc_arr).
    apply tctd_arr_app.
  - (* fix *) right; eexists; reflexivity.
Qed.

Lemma Cval_unit_shape
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  {Δ : Ctx kind} {v : value ∅}
  (D : Cval ∅ Δ nil □ v ⊤) : v = v_unit.
Proof.
  destruct v as [x| |e|v1 v2|ax v|e|v0|v0|e|v0|e].
  - destruct x.
  - reflexivity.
  - exfalso. destruct (Cval_lam_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ⋆ (a →ᵗ b) ⊤ tc_arr tc_unit).
    + apply tctd_arr_app.
    + apply inj_ctor.
    + solve_cdiscrK.
  - exfalso. destruct (Cval_pair_inv D v1 v2 eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ⋆ (t_prod a b) ⊤ tc_prod tc_unit).
    + apply tctd_prod_app.
    + apply inj_ctor.
    + solve_cdiscrK.
  - destruct ax.
    + exfalso. destruct (Cval_injl_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ⋆ (t_sum a b) ⊤ tc_sum tc_unit).
      * apply tctd_sum_app. * apply inj_ctor. * solve_cdiscrK.
    + exfalso. destruct (Cval_injr_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ⋆ (t_sum a b) ⊤ tc_sum tc_unit).
      * apply tctd_sum_app. * apply inj_ctor. * solve_cdiscrK.
  - exfalso. destruct (Cval_tlam_inv D e eq_refl) as (κ & τ0 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) ⋆ (∀ᵗ κ, τ0) ⊤ (tc_all κ) tc_unit).
    + apply tctd_all_ty. + apply inj_ctor. + solve_cdiscrK.
  - exfalso. destruct (Cval_pack_inv D v0 eq_refl) as (κ & a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) ⋆ (∃ᵗ κ, a) ⊤ (tc_xist κ) tc_unit).
    + apply tctd_xist_ty. + apply inj_ctor. + solve_cdiscrK.
  - exfalso. destruct (Cval_roll_inv D v0 eq_refl) as (κ & a & b & c & HF & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ κ) ⇒ κ) ⋆ b ⊤ (tc_rec κ) tc_unit).
    + eapply (@rel_app_tctd_leftP Δ κ (rec_type Δ κ a) (subst a (rec_type Δ κ a)) ⋆ b c); [ exact HF | apply tctd_rec_ty ].
    + apply inj_ctor. + solve_cdiscrK.
  - exfalso. destruct (Cval_lamC_inv D e eq_refl) as (φ & τ0 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_carr_ctd Δ φ τ0 ⊤ ⋆ tc_unit).
    apply inj_ctor.
  - exfalso. destruct (Cval_withC_inv D v0 eq_refl) as (φ & τ0 & E & _ & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_cprod_ctd Δ φ τ0 ⊤ ⋆ tc_unit).
    apply inj_ctor.
  - exfalso. destruct (Cval_fix_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ⋆ (a →ᵗ b) ⊤ tc_arr tc_unit).
    + apply tctd_arr_app.
    + apply inj_ctor.
    + solve_cdiscrK.
Qed.

Lemma Cval_void_impossible
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  {Δ : Ctx kind} {v : value ∅}
  (D : Cval ∅ Δ nil □ v ⊥) : False.
Proof.
  destruct v as [x| |e|v1 v2|ax v|e|v0|v0|e|v0|e].
  - destruct x.
  - exfalso. pose proof (Cval_unit_inv D eq_refl) as E.
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ⋆ ⋆ ⊤ ⊥ tc_unit tc_void).
    + apply inj_ctor. + apply inj_ctor. + solve_cdiscrK.
  - exfalso. destruct (Cval_lam_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ⋆ (a →ᵗ b) ⊥ tc_arr tc_void).
    + apply tctd_arr_app. + apply inj_ctor. + solve_cdiscrK.
  - exfalso. destruct (Cval_pair_inv D v1 v2 eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ⋆ (t_prod a b) ⊥ tc_prod tc_void).
    + apply tctd_prod_app. + apply inj_ctor. + solve_cdiscrK.
  - destruct ax.
    + exfalso. destruct (Cval_injl_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ⋆ (t_sum a b) ⊥ tc_sum tc_void).
      * apply tctd_sum_app. * apply inj_ctor. * solve_cdiscrK.
    + exfalso. destruct (Cval_injr_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ⋆ (t_sum a b) ⊥ tc_sum tc_void).
      * apply tctd_sum_app. * apply inj_ctor. * solve_cdiscrK.
  - exfalso. destruct (Cval_tlam_inv D e eq_refl) as (κ & τ0 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) ⋆ (∀ᵗ κ, τ0) ⊥ (tc_all κ) tc_void).
    + apply tctd_all_ty. + apply inj_ctor. + solve_cdiscrK.
  - exfalso. destruct (Cval_pack_inv D v0 eq_refl) as (κ & a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) ⋆ (∃ᵗ κ, a) ⊥ (tc_xist κ) tc_void).
    + apply tctd_xist_ty. + apply inj_ctor. + solve_cdiscrK.
  - exfalso. destruct (Cval_roll_inv D v0 eq_refl) as (κ & a & b & c & HF & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ κ) ⇒ κ) ⋆ b ⊥ (tc_rec κ) tc_void).
    + eapply (@rel_app_tctd_leftP Δ κ (rec_type Δ κ a) (subst a (rec_type Δ κ a)) ⋆ b c); [ exact HF | apply tctd_rec_ty ].
    + apply inj_ctor. + solve_cdiscrK.
  - exfalso. destruct (Cval_lamC_inv D e eq_refl) as (φ & τ0 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_carr_ctd Δ φ τ0 ⊥ ⋆ tc_void).
    apply inj_ctor.
  - exfalso. destruct (Cval_withC_inv D v0 eq_refl) as (φ & τ0 & E & _ & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_cprod_ctd Δ φ τ0 ⊥ ⋆ tc_void).
    apply inj_ctor.
  - exfalso. destruct (Cval_fix_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ⋆ (a →ᵗ b) ⊥ tc_arr tc_void).
    + apply tctd_arr_app. + apply inj_ctor. + solve_cdiscrK.
Qed.

Lemma Cval_prod_shape
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  {Δ : Ctx kind} {v : value ∅} {τ1 τ2 : typ ⋆ Δ}
  (D : Cval ∅ Δ nil □ v (t_prod τ1 τ2)) :
  exists v1 v2, v = v_pair v1 v2.
Proof.
  destruct v as [x| |e|v1 v2|ax v|e|v0|v0|e|v0|e].
  - destruct x.
  - exfalso. pose proof (Cval_unit_inv D eq_refl) as E.
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ⊤ (t_prod τ1 τ2) tc_unit tc_prod).
    + apply inj_ctor. + apply tctd_prod_app. + solve_cdiscrK.
  - exfalso. destruct (Cval_lam_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (a →ᵗ b) (t_prod τ1 τ2) tc_arr tc_prod).
    + apply tctd_arr_app. + apply tctd_prod_app. + solve_cdiscrK.
  - exists v1, v2; reflexivity.
  - destruct ax.
    + exfalso. destruct (Cval_injl_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (t_sum a b) (t_prod τ1 τ2) tc_sum tc_prod).
      * apply tctd_sum_app. * apply tctd_prod_app. * solve_cdiscrK.
    + exfalso. destruct (Cval_injr_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (t_sum a b) (t_prod τ1 τ2) tc_sum tc_prod).
      * apply tctd_sum_app. * apply tctd_prod_app. * solve_cdiscrK.
  - exfalso. destruct (Cval_tlam_inv D e eq_refl) as (κ & τ0 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (∀ᵗ κ, τ0) (t_prod τ1 τ2) (tc_all κ) tc_prod).
    + apply tctd_all_ty. + apply tctd_prod_app. + solve_cdiscrK.
  - exfalso. destruct (Cval_pack_inv D v0 eq_refl) as (κ & a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (∃ᵗ κ, a) (t_prod τ1 τ2) (tc_xist κ) tc_prod).
    + apply tctd_xist_ty. + apply tctd_prod_app. + solve_cdiscrK.
  - exfalso. destruct (Cval_roll_inv D v0 eq_refl) as (κ & a & b & c & HF & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ κ) ⇒ κ) (⋆ ⇒ ⋆ ⇒ ⋆) b (t_prod τ1 τ2) (tc_rec κ) tc_prod).
    + eapply (@rel_app_tctd_leftP Δ κ (rec_type Δ κ a) (subst a (rec_type Δ κ a)) ⋆ b c); [ exact HF | apply tctd_rec_ty ].
    + apply tctd_prod_app. + solve_cdiscrK.
  - exfalso. destruct (Cval_lamC_inv D e eq_refl) as (φ & τ0 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_carr_ctd Δ φ τ0 (t_prod τ1 τ2) (⋆ ⇒ ⋆ ⇒ ⋆) tc_prod).
    apply tctd_prod_app.
  - exfalso. destruct (Cval_withC_inv D v0 eq_refl) as (φ & τ0 & E & _ & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_cprod_ctd Δ φ τ0 (t_prod τ1 τ2) (⋆ ⇒ ⋆ ⇒ ⋆) tc_prod).
    apply tctd_prod_app.
  - exfalso. destruct (Cval_fix_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (a →ᵗ b) (t_prod τ1 τ2) tc_arr tc_prod).
    + apply tctd_arr_app. + apply tctd_prod_app. + solve_cdiscrK.
Qed.

Lemma Cval_sum_shape
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  {Δ : Ctx kind} {v : value ∅} {τ1 τ2 : typ ⋆ Δ}
  (D : Cval ∅ Δ nil □ v (t_sum τ1 τ2)) :
  (exists u, v = v_inj L u) \/ (exists u, v = v_inj R u).
Proof.
  destruct v as [x| |e|v1 v2|ax v|e|v0|v0|e|v0|e].
  - destruct x.
  - exfalso. pose proof (Cval_unit_inv D eq_refl) as E.
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ⊤ (t_sum τ1 τ2) tc_unit tc_sum).
    + apply inj_ctor. + apply tctd_sum_app. + solve_cdiscrK.
  - exfalso. destruct (Cval_lam_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (a →ᵗ b) (t_sum τ1 τ2) tc_arr tc_sum).
    + apply tctd_arr_app. + apply tctd_sum_app. + solve_cdiscrK.
  - exfalso. destruct (Cval_pair_inv D v1 v2 eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (t_prod a b) (t_sum τ1 τ2) tc_prod tc_sum).
    + apply tctd_prod_app. + apply tctd_sum_app. + solve_cdiscrK.
  - destruct ax.
    + left; eexists; reflexivity.
    + right; eexists; reflexivity.
  - exfalso. destruct (Cval_tlam_inv D e eq_refl) as (κ & τ0 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (∀ᵗ κ, τ0) (t_sum τ1 τ2) (tc_all κ) tc_sum).
    + apply tctd_all_ty. + apply tctd_sum_app. + solve_cdiscrK.
  - exfalso. destruct (Cval_pack_inv D v0 eq_refl) as (κ & a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (∃ᵗ κ, a) (t_sum τ1 τ2) (tc_xist κ) tc_sum).
    + apply tctd_xist_ty. + apply tctd_sum_app. + solve_cdiscrK.
  - exfalso. destruct (Cval_roll_inv D v0 eq_refl) as (κ & a & b & c & HF & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ ⇒ κ) ⇒ κ) (⋆ ⇒ ⋆ ⇒ ⋆) b (t_sum τ1 τ2) (tc_rec κ) tc_sum).
    + eapply (@rel_app_tctd_leftP Δ κ (rec_type Δ κ a) (subst a (rec_type Δ κ a)) ⋆ b c); [ exact HF | apply tctd_rec_ty ].
    + apply tctd_sum_app. + solve_cdiscrK.
  - exfalso. destruct (Cval_lamC_inv D e eq_refl) as (φ & τ0 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_carr_ctd Δ φ τ0 (t_sum τ1 τ2) (⋆ ⇒ ⋆ ⇒ ⋆) tc_sum).
    apply tctd_sum_app.
  - exfalso. destruct (Cval_withC_inv D v0 eq_refl) as (φ & τ0 & E & _ & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_cprod_ctd Δ φ τ0 (t_sum τ1 τ2) (⋆ ⇒ ⋆ ⇒ ⋆) tc_sum).
    apply tctd_sum_app.
  - exfalso. destruct (Cval_fix_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) (a →ᵗ b) (t_sum τ1 τ2) tc_arr tc_sum).
    + apply tctd_arr_app. + apply tctd_sum_app. + solve_cdiscrK.
Qed.

Lemma cdiscr_all_rec_star : cdiscrK (tc_all ⋆) (tc_rec ⋆).
Proof. solve_cdiscrK. Qed.
Lemma cdiscr_xist_rec_star : cdiscrK (tc_xist ⋆) (tc_rec ⋆).
Proof. solve_cdiscrK. Qed.
Lemma cdiscr_all_xist_gen (κ κ' : kind) : cdiscrK (tc_all κ) (tc_xist κ').
Proof.
  destruct (kindEqDec.eq_dec κ κ') as [E|NE].
  - subst κ'. solve_cdiscrK.
  - unfold cdiscrK. destruct (kindEqDec.eq_dec ((κ ⇒ ⋆) ⇒ ⋆) ((κ' ⇒ ⋆) ⇒ ⋆)) as [e|ne].
    + exfalso. apply NE. destruct (KArr_inj e) as [e1 _]. destruct (KArr_inj e1) as [e2 _]. exact e2.
    + exact I.
Qed.
Lemma cdiscr_xist_all_gen (κ κ' : kind) : cdiscrK (tc_xist κ) (tc_all κ').
Proof.
  destruct (kindEqDec.eq_dec κ κ') as [E|NE].
  - subst κ'. solve_cdiscrK.
  - unfold cdiscrK. destruct (kindEqDec.eq_dec ((κ ⇒ ⋆) ⇒ ⋆) ((κ' ⇒ ⋆) ⇒ ⋆)) as [e|ne].
    + exfalso. apply NE. destruct (KArr_inj e) as [e1 _]. destruct (KArr_inj e1) as [e2 _]. exact e2.
    + exact I.
Qed.
Lemma cdiscr_all_rec_gen (κ κ' : kind) : cdiscrK (tc_all κ) (tc_rec κ').
Proof.
  unfold cdiscrK. destruct (kindEqDec.eq_dec ((κ ⇒ ⋆) ⇒ ⋆) ((κ' ⇒ κ') ⇒ κ')) as [e|ne].
  - destruct (KArr_inj e) as [Edom Ecod]. (* Edom: κ⇒⋆ = κ'⇒κ' , Ecod: ⋆=κ' *)
    symmetry in Ecod. subst κ'.
    destruct (KArr_inj Edom) as [E1 _]. subst κ.
    assert (H : e = eq_refl) by (apply UIP_dec; exact kindEqDec.eq_dec).
    rewrite H. cbn. exact cdiscr_all_rec_star.
  - exact I.
Qed.
Lemma cdiscr_xist_rec_gen (κ κ' : kind) : cdiscrK (tc_xist κ) (tc_rec κ').
Proof.
  unfold cdiscrK. destruct (kindEqDec.eq_dec ((κ ⇒ ⋆) ⇒ ⋆) ((κ' ⇒ κ') ⇒ κ')) as [e|ne].
  - destruct (KArr_inj e) as [Edom Ecod]. symmetry in Ecod. subst κ'.
    destruct (KArr_inj Edom) as [E1 _]. subst κ.
    assert (H : e = eq_refl) by (apply UIP_dec; exact kindEqDec.eq_dec).
    rewrite H. cbn. exact cdiscr_xist_rec_star.
  - exact I.
Qed.
Lemma cdiscr_rec_all_gen (κ κ' : kind) : cdiscrK (tc_rec κ) (tc_all κ').
Proof.
  unfold cdiscrK. destruct (kindEqDec.eq_dec ((κ ⇒ κ) ⇒ κ) ((κ' ⇒ ⋆) ⇒ ⋆)) as [e|ne].
  - destruct (KArr_inj e) as [Edom Ecod]. (* Edom κ⇒κ=κ'⇒⋆, Ecod κ=⋆ *)
    symmetry in Ecod. subst κ.
    destruct (KArr_inj Edom) as [E1 E2]. (* E2: κ=⋆ *)
    symmetry in E2. subst κ'.
    assert (H : e = eq_refl) by (apply UIP_dec; exact kindEqDec.eq_dec).
    rewrite H. cbn. constructor.
  - exact I.
Qed.
Lemma cdiscr_rec_xist_gen (κ κ' : kind) : cdiscrK (tc_rec κ) (tc_xist κ').
Proof.
  unfold cdiscrK. destruct (kindEqDec.eq_dec ((κ ⇒ κ) ⇒ κ) ((κ' ⇒ ⋆) ⇒ ⋆)) as [e|ne].
  - destruct (KArr_inj e) as [Edom Ecod]. symmetry in Ecod. subst κ.
    destruct (KArr_inj Edom) as [E1 E2]. symmetry in E2. subst κ'.
    assert (H : e = eq_refl) by (apply UIP_dec; exact kindEqDec.eq_dec).
    rewrite H. cbn. constructor.
  - exact I.
Qed.


Ltac solve_cdis_any :=
  first [ match goal with
          | |- cdiscrK (tc_all ?k) (tc_xist ?k') => apply cdiscr_all_xist_gen
          | |- cdiscrK (tc_xist ?k) (tc_all ?k') => apply cdiscr_xist_all_gen
          | |- cdiscrK (tc_all ?k) (tc_rec ?k') => apply cdiscr_all_rec_gen
          | |- cdiscrK (tc_xist ?k) (tc_rec ?k') => apply cdiscr_xist_rec_gen
          | |- cdiscrK (tc_rec ?k) (tc_all ?k') => apply cdiscr_rec_all_gen
          | |- cdiscrK (tc_rec ?k) (tc_xist ?k') => apply cdiscr_rec_xist_gen
          end
        | solve_cdiscrK ].
Lemma Cval_all_shape
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  {Δ : Ctx kind} {v : value ∅} {κ : kind} {τ0 : typ ⋆ (extC κ Δ)}
  (D : Cval ∅ Δ nil □ v (∀ᵗ κ, τ0)) :
  exists e, v = v_tlam e.
Proof.
  destruct v as [x| |e|v1 v2|ax v|e|v0|v0|e|v0|e].
  - destruct x.
  - exfalso. pose proof (Cval_unit_inv D eq_refl) as E.
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) ⊤ (∀ᵗ κ, τ0) tc_unit (tc_all κ)).
    + apply inj_ctor. + apply tctd_all_ty. + solve_cdis_any.
  - exfalso. destruct (Cval_lam_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (a →ᵗ b) (∀ᵗ κ, τ0) tc_arr (tc_all κ)).
    + apply tctd_arr_app. + apply tctd_all_ty. + solve_cdis_any.
  - exfalso. destruct (Cval_pair_inv D v1 v2 eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (t_prod a b) (∀ᵗ κ, τ0) tc_prod (tc_all κ)).
    + apply tctd_prod_app. + apply tctd_all_ty. + solve_cdis_any.
  - destruct ax.
    + exfalso. destruct (Cval_injl_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (t_sum a b) (∀ᵗ κ, τ0) tc_sum (tc_all κ)).
      * apply tctd_sum_app. * apply tctd_all_ty. * solve_cdis_any.
    + exfalso. destruct (Cval_injr_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (t_sum a b) (∀ᵗ κ, τ0) tc_sum (tc_all κ)).
      * apply tctd_sum_app. * apply tctd_all_ty. * solve_cdis_any.
  - exists e; reflexivity.
  - exfalso. destruct (Cval_pack_inv D v0 eq_refl) as (κ0 & a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ0 ⇒ ⋆) ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (∃ᵗ κ0, a) (∀ᵗ κ, τ0) (tc_xist κ0) (tc_all κ)).
    + apply tctd_xist_ty. + apply tctd_all_ty. + solve_cdis_any.
  - exfalso. destruct (Cval_roll_inv D v0 eq_refl) as (κ0 & a & b & c & HF & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ0 ⇒ κ0) ⇒ κ0) ((κ ⇒ ⋆) ⇒ ⋆) b (∀ᵗ κ, τ0) (tc_rec κ0) (tc_all κ)).
    + eapply (@rel_app_tctd_leftP Δ κ0 (rec_type Δ κ0 a) (subst a (rec_type Δ κ0 a)) ⋆ b c); [ exact HF | apply tctd_rec_ty ].
    + apply tctd_all_ty. + solve_cdis_any.
  - exfalso. destruct (Cval_lamC_inv D e eq_refl) as (φ & τ1 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_carr_ctd Δ φ τ1 (∀ᵗ κ, τ0) ((κ ⇒ ⋆) ⇒ ⋆) (tc_all κ)).
    apply tctd_all_ty.
  - exfalso. destruct (Cval_withC_inv D v0 eq_refl) as (φ & τ1 & E & _ & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_cprod_ctd Δ φ τ1 (∀ᵗ κ, τ0) ((κ ⇒ ⋆) ⇒ ⋆) (tc_all κ)).
    apply tctd_all_ty.
  - exfalso. destruct (Cval_fix_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (a →ᵗ b) (∀ᵗ κ, τ0) tc_arr (tc_all κ)).
    + apply tctd_arr_app. + apply tctd_all_ty. + solve_cdis_any.
Qed.

Lemma Cval_xist_shape
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  {Δ : Ctx kind} {v : value ∅} {κ : kind} {τ0 : typ ⋆ (extC κ Δ)}
  (D : Cval ∅ Δ nil □ v (∃ᵗ κ, τ0)) :
  exists u, v = v_pack u.
Proof.
  destruct v as [x| |e|v1 v2|ax v|e|v0|v0|e|v0|e].
  - destruct x.
  - exfalso. pose proof (Cval_unit_inv D eq_refl) as E.
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ⋆ ((κ ⇒ ⋆) ⇒ ⋆) ⊤ (∃ᵗ κ, τ0) tc_unit (tc_xist κ)).
    + apply inj_ctor. + apply tctd_xist_ty. + solve_cdis_any.
  - exfalso. destruct (Cval_lam_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (a →ᵗ b) (∃ᵗ κ, τ0) tc_arr (tc_xist κ)).
    + apply tctd_arr_app. + apply tctd_xist_ty. + solve_cdis_any.
  - exfalso. destruct (Cval_pair_inv D v1 v2 eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (t_prod a b) (∃ᵗ κ, τ0) tc_prod (tc_xist κ)).
    + apply tctd_prod_app. + apply tctd_xist_ty. + solve_cdis_any.
  - destruct ax.
    + exfalso. destruct (Cval_injl_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (t_sum a b) (∃ᵗ κ, τ0) tc_sum (tc_xist κ)).
      * apply tctd_sum_app. * apply tctd_xist_ty. * solve_cdis_any.
    + exfalso. destruct (Cval_injr_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (t_sum a b) (∃ᵗ κ, τ0) tc_sum (tc_xist κ)).
      * apply tctd_sum_app. * apply tctd_xist_ty. * solve_cdis_any.
  - exfalso. destruct (Cval_tlam_inv D e eq_refl) as (κ0 & a & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ0 ⇒ ⋆) ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (∀ᵗ κ0, a) (∃ᵗ κ, τ0) (tc_all κ0) (tc_xist κ)).
    + apply tctd_all_ty. + apply tctd_xist_ty. + solve_cdis_any.
  - exists v0; reflexivity.
  - exfalso. destruct (Cval_roll_inv D v0 eq_refl) as (κ0 & a & b & c & HF & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ0 ⇒ κ0) ⇒ κ0) ((κ ⇒ ⋆) ⇒ ⋆) b (∃ᵗ κ, τ0) (tc_rec κ0) (tc_xist κ)).
    + eapply (@rel_app_tctd_leftP Δ κ0 (rec_type Δ κ0 a) (subst a (rec_type Δ κ0 a)) ⋆ b c); [ exact HF | apply tctd_rec_ty ].
    + apply tctd_xist_ty. + solve_cdis_any.
  - exfalso. destruct (Cval_lamC_inv D e eq_refl) as (φ & τ1 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_carr_ctd Δ φ τ1 (∃ᵗ κ, τ0) ((κ ⇒ ⋆) ⇒ ⋆) (tc_xist κ)).
    apply tctd_xist_ty.
  - exfalso. destruct (Cval_withC_inv D v0 eq_refl) as (φ & τ1 & E & _ & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_cprod_ctd Δ φ τ1 (∃ᵗ κ, τ0) ((κ ⇒ ⋆) ⇒ ⋆) (tc_xist κ)).
    apply tctd_xist_ty.
  - exfalso. destruct (Cval_fix_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ ⋆) ⇒ ⋆) (a →ᵗ b) (∃ᵗ κ, τ0) tc_arr (tc_xist κ)).
    + apply tctd_arr_app. + apply tctd_xist_ty. + solve_cdis_any.
Qed.

Lemma Cval_carr_shape
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  {Δ : Ctx kind} {v : value ∅} {φ : constr Δ} {τ0 : typ ⋆ Δ}
  (D : Cval ∅ Δ nil □ v (φ →ᶜ τ0)) :
  exists e, v = v_lamC e.
Proof.
  destruct v as [x| |e|v1 v2|ax v|e|v0|v0|e|v0|e].
  - destruct x.
  - exfalso. pose proof (Cval_unit_inv D eq_refl) as E.
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_carr Δ φ τ0 ⊤ ⋆ tc_unit).
    apply inj_ctor.
  - exfalso. destruct (Cval_lam_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_carr Δ φ τ0 (a →ᵗ b) (⋆ ⇒ ⋆ ⇒ ⋆) tc_arr).
    apply tctd_arr_app.
  - exfalso. destruct (Cval_pair_inv D v1 v2 eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_carr Δ φ τ0 (t_prod a b) (⋆ ⇒ ⋆ ⇒ ⋆) tc_prod).
    apply tctd_prod_app.
  - destruct ax.
    + exfalso. destruct (Cval_injl_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd_carr Δ φ τ0 (t_sum a b) (⋆ ⇒ ⋆ ⇒ ⋆) tc_sum).
      apply tctd_sum_app.
    + exfalso. destruct (Cval_injr_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd_carr Δ φ τ0 (t_sum a b) (⋆ ⇒ ⋆ ⇒ ⋆) tc_sum).
      apply tctd_sum_app.
  - exfalso. destruct (Cval_tlam_inv D e eq_refl) as (κ & a & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_carr Δ φ τ0 (∀ᵗ κ, a) ((κ ⇒ ⋆) ⇒ ⋆) (tc_all κ)).
    apply tctd_all_ty.
  - exfalso. destruct (Cval_pack_inv D v0 eq_refl) as (κ & a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_carr Δ φ τ0 (∃ᵗ κ, a) ((κ ⇒ ⋆) ⇒ ⋆) (tc_xist κ)).
    apply tctd_xist_ty.
  - exfalso. destruct (Cval_roll_inv D v0 eq_refl) as (κ & a & b & c & HF & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_carr Δ φ τ0 b ((κ ⇒ κ) ⇒ κ) (tc_rec κ)).
    eapply (@rel_app_tctd_leftP Δ κ (rec_type Δ κ a) (subst a (rec_type Δ κ a)) ⋆ b c); [ exact HF | apply tctd_rec_ty ].
  - exists e; reflexivity.
  - exfalso. destruct (Cval_withC_inv D v0 eq_refl) as (φ0 & τ1 & E & _ & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_cprod_carr Δ φ φ0 τ0 τ1).
  - exfalso. destruct (Cval_fix_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_carr Δ φ τ0 (a →ᵗ b) (⋆ ⇒ ⋆ ⇒ ⋆) tc_arr).
    apply tctd_arr_app.
Qed.

Lemma Cval_cprod_shape
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  {Δ : Ctx kind} {v : value ∅} {φ : constr Δ} {τ0 : typ ⋆ Δ}
  (D : Cval ∅ Δ nil □ v (φ ×ᶜ τ0)) :
  exists u, v = v_withC u.
Proof.
  destruct v as [x| |e|v1 v2|ax v|e|v0|v0|e|v0|e].
  - destruct x.
  - exfalso. pose proof (Cval_unit_inv D eq_refl) as E.
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_cprod Δ φ τ0 ⊤ ⋆ tc_unit).
    apply inj_ctor.
  - exfalso. destruct (Cval_lam_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_cprod Δ φ τ0 (a →ᵗ b) (⋆ ⇒ ⋆ ⇒ ⋆) tc_arr).
    apply tctd_arr_app.
  - exfalso. destruct (Cval_pair_inv D v1 v2 eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_cprod Δ φ τ0 (t_prod a b) (⋆ ⇒ ⋆ ⇒ ⋆) tc_prod).
    apply tctd_prod_app.
  - destruct ax.
    + exfalso. destruct (Cval_injl_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd_cprod Δ φ τ0 (t_sum a b) (⋆ ⇒ ⋆ ⇒ ⋆) tc_sum).
      apply tctd_sum_app.
    + exfalso. destruct (Cval_injr_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd_cprod Δ φ τ0 (t_sum a b) (⋆ ⇒ ⋆ ⇒ ⋆) tc_sum).
      apply tctd_sum_app.
  - exfalso. destruct (Cval_tlam_inv D e eq_refl) as (κ & a & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_cprod Δ φ τ0 (∀ᵗ κ, a) ((κ ⇒ ⋆) ⇒ ⋆) (tc_all κ)).
    apply tctd_all_ty.
  - exfalso. destruct (Cval_pack_inv D v0 eq_refl) as (κ & a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_cprod Δ φ τ0 (∃ᵗ κ, a) ((κ ⇒ ⋆) ⇒ ⋆) (tc_xist κ)).
    apply tctd_xist_ty.
  - exfalso. destruct (Cval_roll_inv D v0 eq_refl) as (κ & a & b & c & HF & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_cprod Δ φ τ0 b ((κ ⇒ κ) ⇒ κ) (tc_rec κ)).
    eapply (@rel_app_tctd_leftP Δ κ (rec_type Δ κ a) (subst a (rec_type Δ κ a)) ⋆ b c); [ exact HF | apply tctd_rec_ty ].
  - exfalso. destruct (Cval_lamC_inv D e eq_refl) as (φ0 & τ1 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_carr_cprod Δ φ0 φ τ1 τ0).
  - exists v0; reflexivity.
  - exfalso. destruct (Cval_fix_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd_cprod Δ φ τ0 (a →ᵗ b) (⋆ ⇒ ⋆ ⇒ ⋆) tc_arr).
    apply tctd_arr_app.
Qed.

Lemma Cval_rec_shape
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  {Δ : Ctx kind} {v : value ∅} {κ : kind} {σ : typ ⋆ Δ}
  (HI : tctd σ (tc_rec κ))
  (D : Cval ∅ Δ nil □ v σ) :
  exists u, v = v_roll u.
Proof.
  destruct v as [x| |e|v1 v2|ax v|e|v0|v0|e|v0|e].
  - destruct x.
  - exfalso. pose proof (Cval_unit_inv D eq_refl) as E.
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ⋆ ((κ ⇒ κ) ⇒ κ) ⊤ σ tc_unit (tc_rec κ)).
    + apply inj_ctor. + exact HI. + solve_cdis_any.
  - exfalso. destruct (Cval_lam_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ κ) ⇒ κ) (a →ᵗ b) σ tc_arr (tc_rec κ)).
    + apply tctd_arr_app. + exact HI. + solve_cdis_any.
  - exfalso. destruct (Cval_pair_inv D v1 v2 eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ κ) ⇒ κ) (t_prod a b) σ tc_prod (tc_rec κ)).
    + apply tctd_prod_app. + exact HI. + solve_cdis_any.
  - destruct ax.
    + exfalso. destruct (Cval_injl_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ κ) ⇒ κ) (t_sum a b) σ tc_sum (tc_rec κ)).
      * apply tctd_sum_app. * exact HI. * solve_cdis_any.
    + exfalso. destruct (Cval_injr_inv D v eq_refl) as (a & b & E & _).
      hdiscr_concl Hdiscr E.
      eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ κ) ⇒ κ) (t_sum a b) σ tc_sum (tc_rec κ)).
      * apply tctd_sum_app. * exact HI. * solve_cdis_any.
  - exfalso. destruct (Cval_tlam_inv D e eq_refl) as (κ0 & a & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ0 ⇒ ⋆) ⇒ ⋆) ((κ ⇒ κ) ⇒ κ) (∀ᵗ κ0, a) σ (tc_all κ0) (tc_rec κ)).
    + apply tctd_all_ty. + exact HI. + solve_cdis_any.
  - exfalso. destruct (Cval_pack_inv D v0 eq_refl) as (κ0 & a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ ((κ0 ⇒ ⋆) ⇒ ⋆) ((κ ⇒ κ) ⇒ κ) (∃ᵗ κ0, a) σ (tc_xist κ0) (tc_rec κ)).
    + apply tctd_xist_ty. + exact HI. + solve_cdis_any.
  - exists v0; reflexivity.
  - exfalso. destruct (Cval_lamC_inv D e eq_refl) as (φ & τ1 & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_carr_ctd Δ φ τ1 σ ((κ ⇒ κ) ⇒ κ) (tc_rec κ)).
    exact HI.
  - exfalso. destruct (Cval_withC_inv D v0 eq_refl) as (φ & τ1 & E & _ & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_cprod_ctd Δ φ τ1 σ ((κ ⇒ κ) ⇒ κ) (tc_rec κ)).
    exact HI.
  - exfalso. destruct (Cval_fix_inv D e eq_refl) as (a & b & E & _).
    hdiscr_concl Hdiscr E.
    eapply (@td_ctd Δ ⋆ (⋆ ⇒ ⋆ ⇒ ⋆) ((κ ⇒ κ) ⇒ κ) (a →ᵗ b) σ tc_arr (tc_rec κ)).
    + apply tctd_arr_app. + exact HI. + solve_cdis_any.
Qed.

Fixpoint progress_expr
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False)
  (e : expr ∅) {struct e} :
  forall (Δ : Ctx kind) (τ : typ ⋆ Δ),
    Δ ∣ nil ∣ □ ⊢ₑ e : τ ->
    (exists v, e = e_val v) \/ (exists e', head_step e e').
Proof.
  destruct e as [v|e1 e2|v1 v2|v|ax v|v|v e1 e2|v e1|v| |v|v e1].
  - intros Δ τ H. left; eexists; reflexivity.
  - intros Δ τ H.
    destruct (typing_expr_bind_inv H e1 e2 eq_refl) as (τ1 & τ2 & H1 & H2 & HEQ).
    destruct (progress_expr Hdiscr e1 Δ τ1 H1) as [ [v EV] | [e1' HS] ].
    + subst e1. right. eexists. eapply BindE.
    + right. eexists. eapply BindE'. exact HS.
  - intros Δ τ H.
    destruct (typing_expr_app_inv H v1 v2 eq_refl) as (τ1 & τ2 & HV1 & HV2 & HEQ).
    destruct (Cval_arrow_shape Hdiscr (typing_val_canonical HV1)) as [ [e0 E] | [e0 E] ].
    + subst v1. right. eexists. apply LamBetaE.
    + subst v1. right. eexists. apply LamBetaRec.
  - intros Δ τ H.
    destruct (typing_expr_tapp_inv H v eq_refl) as (κ & τ0 & σ & HV & HEQ).
    destruct (Cval_all_shape Hdiscr (typing_val_canonical HV)) as [e0 E].
    subst v. right. eexists. apply LamBetaT.
  - destruct ax.
    + intros Δ τ H.
      destruct (typing_expr_projL_inv H v eq_refl) as (τ1 & τ2 & HV & HEQ).
      destruct (Cval_prod_shape Hdiscr (typing_val_canonical HV)) as (v1 & v2 & E).
      subst v. right. eexists. apply ProjLE.
    + intros Δ τ H.
      destruct (typing_expr_projR_inv H v eq_refl) as (τ1 & τ2 & HV & HEQ).
      destruct (Cval_prod_shape Hdiscr (typing_val_canonical HV)) as (v1 & v2 & E).
      subst v. right. eexists. apply ProjRE.
  - intros Δ τ H.
    pose proof (typing_expr_abort_inv H v eq_refl) as HV.
    exfalso. eapply Cval_void_impossible; [ exact Hdiscr | apply typing_val_canonical; exact HV ].
  - intros Δ τ H.
    destruct (typing_expr_case_inv H v e1 e2 eq_refl) as (τ1 & τ2 & τ0 & H1 & H2 & HV & HEQ).
    destruct (Cval_sum_shape Hdiscr (typing_val_canonical HV)) as [ [u E] | [u E] ].
    + subst v. right. eexists. eapply CaseLE.
    + subst v. right. eexists. eapply CaseRE.
  - intros Δ τ H.
    destruct (typing_expr_unpack_inv H v e1 eq_refl) as (κ & τ0 & τc & HV & HB & HEQ).
    destruct (Cval_xist_shape Hdiscr (typing_val_canonical HV)) as [u E].
    subst v. right. eexists. eapply UnpackE.
  - intros Δ τ H.
    destruct (typing_expr_unroll_inv H v eq_refl) as (κ & τ0 & σ1 & σ2 & HF & HV & HEQ).
    assert (HI : tctd σ1 (tc_rec κ)).
    { eapply (@rel_app_tctd_leftP Δ κ (rec_type Δ κ τ0) (subst τ0 (rec_type Δ κ τ0)) ⋆ σ1 σ2); [ exact HF | apply tctd_rec_ty ]. }
    destruct (Cval_rec_shape Hdiscr HI (typing_val_canonical HV)) as [u E].
    subst v. right. eexists. apply UnrollE.
  - intros Δ τ H.
    destruct (typing_expr_cabort_inv H eq_refl) as (ψ & Hp & Hd).
    exfalso. exact (Hdiscr Δ ψ Hp Hd).
  - intros Δ τ H.
    destruct (typing_expr_capp_inv H v eq_refl) as (φ & τ0 & Hφ & HV & HEQ).
    destruct (Cval_carr_shape Hdiscr (typing_val_canonical HV)) as [e0 E].
    subst v. right. eexists. apply LamBetaC.
  - intros Δ τ H.
    destruct (typing_expr_lwith_inv H v e1 eq_refl) as (φ & σ & τ0 & HV & HB & HEQ).
    destruct (Cval_cprod_shape Hdiscr (typing_val_canonical HV)) as [u E].
    subst v. right. eexists. eapply WithE.
Defined.

Definition HrollProp : Prop :=
  forall (Δ : Ctx kind) (κ κ' : kind)
         (τ : typ κ (extC κ Δ)) (τ' : typ κ' (extC κ' Δ))
         (σ₁ σ₂ σ₁' σ₂' : typ ⋆ Δ),
    rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂ ->
    rel_app κ' (rec_type Δ κ' τ') (subst τ' (rec_type Δ κ' τ')) ⋆ σ₁' σ₂' ->
    nil ⊩ σ₁ ≃ σ₁' -> nil ⊩ σ₂ ≃ σ₂'.

Lemma Hroll_of_discr
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False) :
  HrollProp.
Proof.
  red. intros Δ κ κ' τ τ' σ1 σ2 σ1' σ2' HF HF' HEQ.
  eapply roll_eq_of_discr; [ exact Hdiscr | exact HF | exact HF' | exact HEQ ].
Qed.

Lemma preservation_head_step
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False) :
  forall (e e' : expr ∅), head_step e e' ->
  forall (Δ : Ctx kind) (τ : typ ⋆ Δ),
    Δ ∣ nil ∣ □ ⊢ₑ e : τ -> Δ ∣ nil ∣ □ ⊢ₑ e' : τ.
Proof.
  intros e e' HS.
  induction HS; intros Δ τ Hty.
  - eapply preservation_LamBetaRec; exact Hty.
  - eapply preservation_LamBetaE; exact Hty.
  - eapply preservation_LamBetaT_nil; [ exact Hdiscr | exact Hty ].
  - eapply preservation_LamBetaC; exact Hty.
  - eapply preservation_ProjL; exact Hty.
  - eapply preservation_ProjR; exact Hty.
  - eapply preservation_CaseL; exact Hty.
  - eapply preservation_CaseR; exact Hty.
  - eapply preservation_UnpackE_nil; [ exact Hdiscr | exact Hty ].
  - apply T_val. eapply preservation_UnrollE_nil; [ apply Hroll_of_discr; exact Hdiscr | exact Hty ].
  - eapply preservation_WithE; exact Hty.
  - eapply preservation_BindE; exact Hty.
  - destruct (typing_expr_bind_inv Hty e' e eq_refl) as (τ1 & τ2 & H1 & H2 & HEQ).
    eapply T_congE; [ exact HEQ | ].
    eapply T_bind.
    + apply IHHS. exact H1.
    + exact H2.
Qed.

Lemma safe_of_progress_preservation
  (Hdiscr : forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False) :
  forall (e : expr ∅) (τ : typ ⋆ mtC),
    mtC ∣ nil ∣ □ ⊢ₑ e : τ -> safe e.
Proof.
  intros e τ Hty e' Hstep.
  revert τ Hty.
  induction Hstep as [x | x y z HR Hrest IH]; intros τ Hty.
  - destruct (progress_expr Hdiscr x mtC τ Hty) as [ [v EV] | [e'' HS] ].
    + left; exists v; exact EV.
    + right; exists e''; exact HS.
  - apply (IH τ).
    eapply preservation_head_step; [ exact Hdiscr | exact HR | exact Hty ].
Qed.



(* ----------  Basic impossible-head facts for tctd/tdiscr  ---------- *)

Lemma tctd_lam_false {Δ : Ctx kind} {κ' κ κc : kind} (b : typ κ' (extC κ Δ))
      (c : tctor κc) : tctd (@t_lam Δ κ κ' b) c -> False.
Proof. intro H. dependent destruction H. Qed.

Lemma tctd_redex_false {Δ : Ctx kind} {κa κr κc : kind}
      (b : typ κr (extC κa Δ)) (a : typ κa Δ) (c : tctor κc) :
  tctd ((t_lam b) a) c -> False.
Proof. intro H. dependent destruction H. dependent destruction H. Qed.

Lemma tctd_carr_false {Δ : Ctx kind} {κc : kind} (ψ : constr Δ) (τ : typ ⋆ Δ)
      (c : tctor κc) : tctd (@t_carr Δ ψ τ) c -> False.
Proof. intro H. dependent destruction H. Qed.

Lemma tctd_cprod_false {Δ : Ctx kind} {κc : kind} (ψ : constr Δ) (τ : typ ⋆ Δ)
      (c : tctor κc) : tctd (@t_cprod Δ ψ τ) c -> False.
Proof. intro H. dependent destruction H. Qed.

Lemma tctd_var_false {Δ : Ctx kind} {κ κc : kind} (x : dom Δ) (EQ : Δ x = κ)
      (c : tctor κc) : tctd (@t_var Δ κ x EQ) c -> False.
Proof. intro H. dependent destruction H. Qed.

Lemma tctd_app_inv {Δ : Ctx kind} {κa κr κc : kind}
      (σ : typ (κa ⇒ κr) Δ) (τ : typ κa Δ) (c : tctor κc) :
  tctd (σ τ) c -> tctd σ c.
Proof. intro H. dependent destruction H. assumption. Qed.

(* cdiscrK is irreflexive. *)
Lemma cdiscrK_self {κ : kind} (c : tctor κ) : cdiscrK c c -> False.
Proof.
  unfold cdiscrK.
  destruct (kindEqDec.eq_dec κ κ) as [e|n].
  - rewrite (UIP_dec kindEqDec.eq_dec e eq_refl). simpl.
    destruct c; cbn; intros H; inversion H.
  - exfalso. apply n. reflexivity.
Qed.

(* A type with a tctd head cannot be discriminable from itself. *)
Lemma tdiscr_ctor_self {Δ : Ctx kind} {κ : kind} (c : tctor κ) :
  ⊮ ((t_ctor c) ≃ (t_ctor c) : constr Δ) -> False.
Proof.
  intro H. dependent destruction H.
  dependent destruction HI₁. dependent destruction HI₂.
  exact (cdiscrK_self c HD).
Qed.

(* Redexes and lambdas never occur as a tdiscr side. *)
Lemma tdiscr_lam_left {Δ : Ctx kind} {κa κr : kind}
      (b : typ κr (extC κa Δ)) (σ : typ (κa ⇒ κr) Δ) :
  ⊮ ((t_lam b : typ (κa ⇒ κr) Δ) ≃ σ) -> False.
Proof.
  intro H. dependent destruction H.
  all: eauto using tctd_lam_false.
Qed.

Lemma cdiscr_symm {κ : kind} (c1 c2 : tctor κ) : cdiscr c1 c2 -> cdiscr c2 c1.
Proof. intros H; destruct H; econstructor. Qed.

Lemma cdiscrK_symm {κ1 κ2 : kind} (c1 : tctor κ1) (c2 : tctor κ2) :
  cdiscrK c1 c2 -> cdiscrK c2 c1.
Proof.
  intro H. unfold cdiscrK in *.
  destruct (kindEqDec.eq_dec κ1 κ2) as [e|n].
  - destruct e.
    destruct (kindEqDec.eq_dec κ1 κ1) as [e2|n2].
    + rewrite (UIP_dec kindEqDec.eq_dec e2 eq_refl).
      simpl in H. simpl. apply cdiscr_symm. exact H.
    + exfalso; apply n2; reflexivity.
  - destruct (kindEqDec.eq_dec κ2 κ1) as [e|n2].
    + exfalso; apply n; symmetry; exact e.
    + exact I.
Qed.

Lemma tdiscr_symm {Δ : Ctx kind} {κ : kind} (τ1 τ2 : typ κ Δ) :
  ⊮ (τ1 ≃ τ2) -> ⊮ (τ2 ≃ τ1).
Proof.
  intro H. dependent destruction H.
  - eapply td_ctd; eauto using cdiscrK_symm.
  - eapply td_ctd_carr; eauto.
  - eapply td_carr_ctd; eauto.
  - eapply td_ctd_cprod; eauto.
  - eapply td_cprod_ctd; eauto.
  - eapply td_cprod_carr; eauto.
  - eapply td_carr_cprod; eauto.
Qed.

Lemma tdiscr_lam_right {Δ : Ctx kind} {κa κr : kind}
      (b : typ κr (extC κa Δ)) (σ : typ (κa ⇒ κr) Δ) :
  ⊮ (σ ≃ (t_lam b : typ (κa ⇒ κr) Δ)) -> False.
Proof. intro H. apply (tdiscr_lam_left b σ). apply tdiscr_symm; assumption. Qed.

Lemma tdiscr_redex_left {Δ : Ctx kind} {κa κr : kind}
      (b : typ κr (extC κa Δ)) (a : typ κa Δ) (σ : typ κr Δ) :
  ⊮ (((t_lam b) a : typ κr Δ) ≃ σ) -> False.
Proof.
  intro H. dependent destruction H.
  all: eauto using tctd_redex_false.
Qed.

(* tdiscr of two applications forces tdiscr of their function parts. *)
Lemma tdiscr_app_func {Δ : Ctx kind} {κa κr : kind}
      (σ1 σ2 : typ (κa ⇒ κr) Δ) (τ1 τ2 : typ κa Δ) :
  ⊮ ((σ1 τ1) ≃ (σ2 τ2)) -> ⊮ (σ1 ≃ σ2).
Proof.
  intro H. dependent destruction H.
  eapply td_ctd.
  - exact (tctd_app_inv σ1 τ1 c₁ HI₁).
  - exact (tctd_app_inv σ2 τ2 c₂ HI₂).
  - exact HD.
Qed.

(* carr/cprod rigidity when both sides have the same head shape. *)
Lemma tdiscr_carr_carr_false {Δ : Ctx kind} (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ) :
  ⊮ ((t_carr ψ1 τ1) ≃ (t_carr ψ2 τ2)) -> False.
Proof.
  intro H. dependent destruction H.
  all: eauto using tctd_carr_false.
Qed.

Lemma tdiscr_cprod_cprod_false {Δ : Ctx kind} (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ) :
  ⊮ ((t_cprod ψ1 τ1) ≃ (t_cprod ψ2 τ2)) -> False.
Proof.
  intro H. dependent destruction H.
  all: eauto using tctd_cprod_false.
Qed.

Lemma tdiscr_var_var_false {Δ : Ctx kind} {κ : kind} (x y : dom Δ)
      (EQ1 EQ2 : Δ x = κ) (EQ3 EQ4 : Δ y = κ) :
  ⊮ ((@t_var Δ κ x EQ1) ≃ (@t_var Δ κ y EQ3)) -> False.
Proof.
  intro H. dependent destruction H.
  all: eauto using tctd_var_false.
Qed.

(* ---------- Reduction of Hdiscr to the remaining semantic/injectivity facts ---------- *)

Lemma Hdiscr_of_hard
  (Htrans : forall (Δ : Ctx kind) (κ : kind) (τ1 τ2 τ3 : typ κ Δ),
      nil ⊩ τ1 ≃ τ2 -> nil ⊩ τ2 ≃ τ3 -> ⊮ (τ1 ≃ τ3) -> False)
  (HappR : forall (Δ : Ctx kind) (κa κr κc : kind)
      (σ1 σ2 : typ (κa ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ κa Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False)
  (HappL : forall (Δ : Ctx kind) (κa κr κc : kind)
      (σ1 σ2 : typ (κa ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ κa Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (σ1 ≃ σ2) -> False)
  (HcarrR : forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
      nil ⊩ (t_carr ψ1 τ1) ≃ (t_carr ψ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False)
  (HcprodR : forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
      nil ⊩ (t_cprod ψ1 τ1) ≃ (t_cprod ψ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False)
  (HcarrL : forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
      nil ⊩ (t_carr ψ1 τ1) ≃ (t_carr ψ2 τ2) -> nil ⊩ ψ1 -> ⊮ ψ2 -> False)
  (HcprodL : forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
      nil ⊩ (t_cprod ψ1 τ1) ≃ (t_cprod ψ2 τ2) -> nil ⊩ ψ1 -> ⊮ ψ2 -> False) :
  forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False.
Proof.
  assert (Haux : forall (Δ : Ctx kind) (Ψ : list (constr Δ)) (ψ : constr Δ),
             Ψ ⊩ ψ -> Ψ = nil -> ⊮ ψ -> False).
  { intros Δh Ψh ψh H0.
    refine (tproves_i_ind
      (fun (Δ : Ctx kind) (Ψ : list (constr Δ)) (ψ : constr Δ) =>
         Ψ = nil -> ⊮ ψ -> False)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Δh Ψh ψh H0).
  - (* ax *) intros Δ0 Ψ0 ψ0 HIn E0. subst Ψ0. inversion HIn.
  - (* var *) intros Δ0 Ψ0 κ x EQ1 EQ2 E0 HD. subst Ψ0.
    exact (tdiscr_var_var_false x x EQ1 EQ1 EQ2 EQ2 HD).
  - (* lam *) intros Δ0 Ψ0 κa κr τ1 τ2 Hprem IH E0 HD. subst Ψ0.
    exact (tdiscr_lam_left τ1 (t_lam τ2) HD).
  - (* app *) intros Δ0 Ψ0 κa κr σ1 σ2 τ1 τ2 Hf IHf Ha IHa E0 HD. subst Ψ0.
    exact (IHf eq_refl (tdiscr_app_func σ1 σ2 τ1 τ2 HD)).
  - (* ctor *) intros Δ0 Ψ0 κ c E0 HD. subst Ψ0.
    exact (tdiscr_ctor_self c HD).
  - (* carr *) intros Δ0 Ψ0 ψ0 τ1 τ2 Hprem IH E0 HD. subst Ψ0.
    exact (tdiscr_carr_carr_false ψ0 ψ0 τ1 τ2 HD).
  - (* cprod *) intros Δ0 Ψ0 ψ0 τ1 τ2 Hprem IH E0 HD. subst Ψ0.
    exact (tdiscr_cprod_cprod_false ψ0 ψ0 τ1 τ2 HD).
  - (* symm *) intros Δ0 Ψ0 κ τ1 τ2 Hprem IH E0 HD. subst Ψ0.
    exact (IH eq_refl (tdiscr_symm τ2 τ1 HD)).
  - (* trans *) intros Δ0 Ψ0 κ τ1 τ2 τ3 H1 IH1 H2 IH2 E0 HD. subst Ψ0.
    exact (Htrans Δ0 κ τ1 τ2 τ3 H1 H2 HD).
  - (* eta *) intros Δ0 Ψ0 κa κr τ E0 HD. subst Ψ0.
    eapply tdiscr_lam_right; exact HD.
  - (* beta *) intros Δ0 Ψ0 κa κr σ τ E0 HD. subst Ψ0.
    exact (tdiscr_redex_left τ σ (subst τ σ) HD).
  - (* appInjR *) intros Δ0 Ψ0 κa κr κ σ1 σ2 c τ1 τ2 HI1 HI2 Hprem IH E0 HD. subst Ψ0.
    exact (HappR Δ0 κa κr κ σ1 σ2 c τ1 τ2 HI1 HI2 Hprem HD).
  - (* appInjL *) intros Δ0 Ψ0 κa κr κ σ1 σ2 c τ1 τ2 HI1 HI2 Hprem IH E0 HD. subst Ψ0.
    exact (HappL Δ0 κa κr κ σ1 σ2 c τ1 τ2 HI1 HI2 Hprem HD).
  - (* carrInjR *) intros Δ0 Ψ0 ψ1 ψ2 τ1 τ2 Hprem IH E0 HD. subst Ψ0.
    exact (HcarrR Δ0 ψ1 ψ2 τ1 τ2 Hprem HD).
  - (* cprodInjR *) intros Δ0 Ψ0 ψ1 ψ2 τ1 τ2 Hprem IH E0 HD. subst Ψ0.
    exact (HcprodR Δ0 ψ1 ψ2 τ1 τ2 Hprem HD).
  - (* cprodInjL *) intros Δ0 Ψ0 ψ1 ψ2 τ1 τ2 Hprem IH H1 IH1 E0 HD. subst Ψ0.
    exact (HcprodL Δ0 ψ1 ψ2 τ1 τ2 Hprem H1 HD).
  - (* carrInjL *) intros Δ0 Ψ0 ψ1 ψ2 τ1 τ2 Hprem IH H1 IH1 E0 HD. subst Ψ0.
    exact (HcarrL Δ0 ψ1 ψ2 τ1 τ2 Hprem H1 HD).
  }
  intros Δ ψ H. exact (Haux Δ nil ψ H eq_refl).
Qed.

(* tctd uniqueness, needed below. *)
Lemma tctd_unique {Δ : Ctx kind} :
  forall (κ1 : kind) (τ : typ κ1 Δ) (κ2 : kind) (c2 : tctor κ2),
    tctd τ c2 ->
    forall (κ3 : kind) (c3 : tctor κ3), tctd τ c3 ->
      exists (E : κ2 = κ3), eq_rect κ2 (fun k => tctor k) c2 κ3 E = c3.
Proof.
  refine (tctd_ind Δ
    (fun κ1 τ κ2 c2 => forall κ3 c3, tctd τ c3 ->
       exists E : κ2 = κ3, eq_rect κ2 (fun k => tctor k) c2 κ3 E = c3)
    _ _).
  - intros κ c κ3 c3 H2. dependent destruction H2.
    + exists eq_refl. reflexivity.
  - intros κ κa κ' σ τ0 c HI IH κ3 c3 H2.
    dependent destruction H2.
    apply (IH _ _ H2).
Qed.


(* Same-head tctd derivations cannot be discriminable. *)
Lemma tctd_same_head_not_discr {Δ : Ctx kind} {κ κc : kind}
      (τ1 τ2 : typ κ Δ) (c : tctor κc) :
  tctd τ1 c -> tctd τ2 c -> ⊮ (τ1 ≃ τ2) -> False.
Proof.
  intros H1 H2 HD.
  dependent destruction HD.
  all: try (exfalso; eauto using tctd_carr_false, tctd_cprod_false).
  destruct (tctd_unique κ τ1 κ₁ c₁ HI₁ κc c H1) as [E1 Hc1].
  destruct E1. simpl in Hc1.
  destruct (tctd_unique κ τ2 κ₂ c₂ HI₂ κ₁ c H2) as [E2 Hc2].
  destruct E2. simpl in Hc2.
  rewrite Hc1 in HD. rewrite Hc2 in HD.
  exact (cdiscrK_self c HD).
Qed.


Lemma HappL_proved : forall (Δ : Ctx kind) (κa κr κc : kind)
      (σ1 σ2 : typ (κa ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ κa Δ),
  tctd σ1 c -> tctd σ2 c ->
  nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (σ1 ≃ σ2) -> False.
Proof.
  intros. exact (tctd_same_head_not_discr σ1 σ2 c H H0 H2).
Qed.

Corollary Hdiscr_of_six
  (Htrans : forall (Δ : Ctx kind) (κ : kind) (τ1 τ2 τ3 : typ κ Δ),
      nil ⊩ τ1 ≃ τ2 -> nil ⊩ τ2 ≃ τ3 -> ⊮ (τ1 ≃ τ3) -> False)
  (HappR : forall (Δ : Ctx kind) (κa κr κc : kind)
      (σ1 σ2 : typ (κa ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ κa Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False)
  (HcarrR : forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
      nil ⊩ (t_carr ψ1 τ1) ≃ (t_carr ψ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False)
  (HcprodR : forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
      nil ⊩ (t_cprod ψ1 τ1) ≃ (t_cprod ψ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False)
  (HcarrL : forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
      nil ⊩ (t_carr ψ1 τ1) ≃ (t_carr ψ2 τ2) -> nil ⊩ ψ1 -> ⊮ ψ2 -> False)
  (HcprodL : forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
      nil ⊩ (t_cprod ψ1 τ1) ≃ (t_cprod ψ2 τ2) -> nil ⊩ ψ1 -> ⊮ ψ2 -> False) :
  forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False.
Proof.
  intros. eapply Hdiscr_of_hard; eauto using HappL_proved.
Qed.

(* The transitivity hard case at base kind follows from the appInjR hard case. *)
Lemma Htrans_star_of_HappR
  (HappR : forall (Δ : Ctx kind) (κa κr κc : kind)
      (σ1 σ2 : typ (κa ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ κa Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False) :
  forall (Δ : Ctx kind) (τ1 τ2 τ3 : typ ⋆ Δ),
    nil ⊩ τ1 ≃ τ2 -> nil ⊩ τ2 ≃ τ3 -> ⊮ (τ1 ≃ τ3) -> False.
Proof.
  intros Δ τ1 τ2 τ3 H12 H23 HD.
  assert (H13 : nil ⊩ τ1 ≃ τ3) by (eapply tpi_trans; eauto).
  set (σ := @t_ctor Δ (⋆ ⇒ ⋆ ⇒ ⋆) tc_arr).
  assert (Happ : nil ⊩ (σ τ1) ≃ (σ τ3)).
  { eapply tpi_app. apply tpi_ctor. exact H13. }
  eapply (HappR Δ ⋆ (⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) σ σ tc_arr τ1 τ3).
  - apply inj_ctor.
  - apply inj_ctor.
  - exact Happ.
  - exact HD.
Qed.

(* carr/cprod injectivity on the tau component follows from appInjR at base kind. *)
Lemma HcarrR_of_HappR
  (HappR : forall (Δ : Ctx kind) (κa κr κc : kind)
      (σ1 σ2 : typ (κa ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ κa Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False) :
  forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
    nil ⊩ (t_carr ψ1 τ1) ≃ (t_carr ψ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False.
Proof.
  intros Δ ψ1 ψ2 τ1 τ2 H HD.
  assert (Hτ : nil ⊩ τ1 ≃ τ2) by (eapply tpi_carrInjR; exact H).
  set (σ := @t_ctor Δ (⋆ ⇒ ⋆ ⇒ ⋆) tc_arr).
  assert (Happ : nil ⊩ (σ τ1) ≃ (σ τ2)).
  { eapply tpi_app. apply tpi_ctor. exact Hτ. }
  eapply (HappR Δ ⋆ (⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) σ σ tc_arr τ1 τ2).
  - apply inj_ctor.
  - apply inj_ctor.
  - exact Happ.
  - exact HD.
Qed.

Lemma HcprodR_of_HappR
  (HappR : forall (Δ : Ctx kind) (κa κr κc : kind)
      (σ1 σ2 : typ (κa ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ κa Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False) :
  forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
    nil ⊩ (t_cprod ψ1 τ1) ≃ (t_cprod ψ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False.
Proof.
  intros Δ ψ1 ψ2 τ1 τ2 H HD.
  assert (Hτ : nil ⊩ τ1 ≃ τ2) by (eapply tpi_cprodInjR; exact H).
  set (σ := @t_ctor Δ (⋆ ⇒ ⋆ ⇒ ⋆) tc_prod).
  assert (Happ : nil ⊩ (σ τ1) ≃ (σ τ2)).
  { eapply tpi_app. apply tpi_ctor. exact Hτ. }
  eapply (HappR Δ ⋆ (⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) σ σ tc_prod τ1 τ2).
  - apply inj_ctor.
  - apply inj_ctor.
  - exact Happ.
  - exact HD.
Qed.

(* tdiscr is preserved by applying both sides to the same argument. *)
Lemma tdiscr_app_same_arg {Δ : Ctx kind} {κa κr : kind}
      (σ1 σ2 : typ (κa ⇒ κr) Δ) (x : typ κa Δ) :
  ⊮ (σ1 ≃ σ2) -> ⊮ ((σ1 x) ≃ (σ2 x)).
Proof.
  intro H. dependent destruction H.
  refine (@td_ctd Δ κr κ₁ κ₂ (σ1 x) (σ2 x) c₁ c₂ _ _ HD).
  - apply inj_app. exact HI₁.
  - apply inj_app. exact HI₂.
Qed.


(* Reduce consistency at every kind to consistency at base kind. *)
Lemma Hdiscr_any_of_star
  (Hstar : forall (Δ : Ctx kind) (A B : typ ⋆ Δ),
      nil ⊩ A ≃ B -> ⊮ (A ≃ B) -> False) :
  forall (κ : kind) (Δ : Ctx kind) (A B : typ κ Δ),
    nil ⊩ A ≃ B -> ⊮ (A ≃ B) -> False.
Proof.
  induction κ as [| κa IHa κr IHr]; intros Δ A B H HD.
  - exact (Hstar Δ A B H HD).
  - set (Δ' := extC κa Δ).
    set (A' := tmap (mkShift κa Δ) A).
    set (B' := tmap (mkShift κa Δ) B).
    assert (H' : nil ⊩ (A' ≃ B')).
    { change (nil ⊩ cmap (mkShift κa Δ) (c_eq (κa ⇒ κr) A B)).
      apply (tproves_tmap Δ nil (c_eq (κa ⇒ κr) A B) H (extC κa Δ) (mkShift κa Δ)). }
    assert (HD' : ⊮ (A' ≃ B')).
    { change (⊮ cmap (mkShift κa Δ) (c_eq (κa ⇒ κr) A B)).
      apply (tdiscr_cmap Δ (c_eq (κa ⇒ κr) A B) HD (extC κa Δ) (mkShift κa Δ)). }
    set (x := @t_var (extC κa Δ) κa VZ eq_refl).
    assert (Hx : nil ⊩ (x ≃ x)) by (apply (tproves_refl κa (extC κa Δ) nil x)).
    assert (Happ : nil ⊩ ((A' x) ≃ (B' x))).
    { eapply tpi_app; [ exact H' | exact Hx ]. }
    assert (HDapp : ⊮ ((A' x) ≃ (B' x)))
      by (apply (tdiscr_app_same_arg A' B' x HD')).
    exact (IHr (extC κa Δ) (A' x) (B' x) Happ HDapp).
Qed.

(* Base-kind consistency from the appInjR hard case at base argument kind. *)
Lemma Hdiscr_star_of_HappR_star
  (HappR : forall (Δ : Ctx kind) (κr κc : kind)
      (σ1 σ2 : typ (⋆ ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ ⋆ Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False) :
  forall (Δ : Ctx kind) (A B : typ ⋆ Δ),
    nil ⊩ A ≃ B -> ⊮ (A ≃ B) -> False.
Proof.
  intros Δ A B H HD.
  set (σ := @t_ctor Δ (⋆ ⇒ ⋆ ⇒ ⋆) tc_arr).
  assert (Happ : nil ⊩ (σ A) ≃ (σ B)).
  { eapply tpi_app. apply tpi_ctor. exact H. }
  eapply (HappR Δ (⋆ ⇒ ⋆) (⋆ ⇒ ⋆ ⇒ ⋆) σ σ tc_arr A B).
  - apply inj_ctor.
  - apply inj_ctor.
  - exact Happ.
  - exact HD.
Qed.

(* Full consistency reduces to the single base-argument appInjR fact. *)
Lemma Hdiscr_of_HappR_star
  (HappR : forall (Δ : Ctx kind) (κr κc : kind)
      (σ1 σ2 : typ (⋆ ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ ⋆ Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False) :
  forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False.
Proof.
  intros Δ [κ A B] H HD.
  exact (Hdiscr_any_of_star (Hdiscr_star_of_HappR_star HappR) κ Δ A B H HD).
Qed.

(* All six previously-isolated hard cases follow from the single base HappR fact. *)
Lemma HappR_of_HappR_star
  (HappR : forall (Δ : Ctx kind) (κr κc : kind)
      (σ1 σ2 : typ (⋆ ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ ⋆ Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False) :
  forall (Δ : Ctx kind) (κa κr κc : kind)
      (σ1 σ2 : typ (κa ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ κa Δ),
    tctd σ1 c -> tctd σ2 c ->
    nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False.
Proof.
  intros Δ κa κr κc σ1 σ2 c τ1 τ2 HI1 HI2 H HD.
  exact (Hdiscr_of_HappR_star HappR Δ (c_eq κa τ1 τ2)
           (tpi_appInjR HI1 HI2 H) HD).
Qed.

Lemma Htrans_of_HappR_star
  (HappR : forall (Δ : Ctx kind) (κr κc : kind)
      (σ1 σ2 : typ (⋆ ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ ⋆ Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False) :
  forall (Δ : Ctx kind) (κ : kind) (τ1 τ2 τ3 : typ κ Δ),
    nil ⊩ τ1 ≃ τ2 -> nil ⊩ τ2 ≃ τ3 -> ⊮ (τ1 ≃ τ3) -> False.
Proof.
  intros Δ κ τ1 τ2 τ3 H12 H23 HD.
  exact (Hdiscr_of_HappR_star HappR Δ (c_eq κ τ1 τ3)
           (tpi_trans H12 H23) HD).
Qed.

Lemma HcarrL_of_HappR_star
  (HappR : forall (Δ : Ctx kind) (κr κc : kind)
      (σ1 σ2 : typ (⋆ ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ ⋆ Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False) :
  forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
    nil ⊩ (t_carr ψ1 τ1) ≃ (t_carr ψ2 τ2) -> nil ⊩ ψ1 -> ⊮ ψ2 -> False.
Proof.
  intros Δ ψ1 ψ2 τ1 τ2 H H1 HD.
  exact (Hdiscr_of_HappR_star HappR Δ ψ2 (tpi_carrInjL H H1) HD).
Qed.

Lemma HcprodL_of_HappR_star
  (HappR : forall (Δ : Ctx kind) (κr κc : kind)
      (σ1 σ2 : typ (⋆ ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ ⋆ Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False) :
  forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
    nil ⊩ (t_cprod ψ1 τ1) ≃ (t_cprod ψ2 τ2) -> nil ⊩ ψ1 -> ⊮ ψ2 -> False.
Proof.
  intros Δ ψ1 ψ2 τ1 τ2 H H1 HD.
  exact (Hdiscr_of_HappR_star HappR Δ ψ2 (tpi_cprodInjL H H1) HD).
Qed.

Lemma HappL_of_HappR_star
  (HappR : forall (Δ : Ctx kind) (κr κc : kind)
      (σ1 σ2 : typ (⋆ ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ ⋆ Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False) :
  forall (Δ : Ctx kind) (κa κr κc : kind)
      (σ1 σ2 : typ (κa ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ κa Δ),
    tctd σ1 c -> tctd σ2 c ->
    nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (σ1 ≃ σ2) -> False.
Proof.
  intros Δ κa κr κc σ1 σ2 c τ1 τ2 HI1 HI2 H HD.
  exact (Hdiscr_of_HappR_star HappR Δ (c_eq (κa ⇒ κr) σ1 σ2)
           (tpi_appInjL HI1 HI2 H) HD).
Qed.

Lemma HcarrR_of_HappR_star
  (HappR : forall (Δ : Ctx kind) (κr κc : kind)
      (σ1 σ2 : typ (⋆ ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ ⋆ Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False) :
  forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
    nil ⊩ (t_carr ψ1 τ1) ≃ (t_carr ψ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False.
Proof.
  intros Δ ψ1 ψ2 τ1 τ2 H HD.
  exact (Hdiscr_of_HappR_star HappR Δ (c_eq ⋆ τ1 τ2)
           (tpi_carrInjR H) HD).
Qed.

Lemma HcprodR_of_HappR_star
  (HappR : forall (Δ : Ctx kind) (κr κc : kind)
      (σ1 σ2 : typ (⋆ ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ ⋆ Δ),
      tctd σ1 c -> tctd σ2 c ->
      nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False) :
  forall (Δ : Ctx kind) (ψ1 ψ2 : constr Δ) (τ1 τ2 : typ ⋆ Δ),
    nil ⊩ (t_cprod ψ1 τ1) ≃ (t_cprod ψ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False.
Proof.
  intros Δ ψ1 ψ2 τ1 τ2 H HD.
  exact (Hdiscr_of_HappR_star HappR Δ (c_eq ⋆ τ1 τ2)
           (tpi_cprodInjR H) HD).
Qed.

(* Conversely, HappR at base argument kind is exactly base-kind consistency. *)
Lemma HappR_star_of_Hstar
  (Hstar : forall (Δ : Ctx kind) (A B : typ ⋆ Δ),
      nil ⊩ A ≃ B -> ⊮ (A ≃ B) -> False) :
  forall (Δ : Ctx kind) (κr κc : kind)
      (σ1 σ2 : typ (⋆ ⇒ κr) Δ) (c : tctor κc) (τ1 τ2 : typ ⋆ Δ),
    tctd σ1 c -> tctd σ2 c ->
    nil ⊩ (σ1 τ1) ≃ (σ2 τ2) -> ⊮ (τ1 ≃ τ2) -> False.
Proof.
  intros Δ κr κc σ1 σ2 c τ1 τ2 HI1 HI2 H HD.
  exact (Hstar Δ τ1 τ2 (tpi_appInjR HI1 HI2 H) HD).
Qed.


Lemma Hdiscr_of_Hstar
  (Hstar : forall (Δ : Ctx kind) (A B : typ ⋆ Δ), nil ⊩ (A ≃ B) -> ⊮ (A ≃ B) -> False) :
  forall (Δ : Ctx kind) (ψ : constr Δ), nil ⊩ ψ -> ⊮ ψ -> False.
Proof.
  intros Δ [κ A B] H HD.
  exact (Hdiscr_of_HappR_star (HappR_star_of_Hstar Hstar) Δ (c_eq κ A B) H HD).
Qed.


Lemma soundness_of_Hstar
  (Hstar : forall (Δ : Ctx kind) (A B : typ ⋆ Δ),
      nil ⊩ (A ≃ B) -> ⊮ (A ≃ B) -> False) :
  forall (e : expr ∅) (τ : typ ⋆ mtC),
    mtC ∣ nil ∣ □ ⊢ₑ e : τ -> safe e.
Proof.
  intros e τ HT.
  exact (safe_of_progress_preservation (Hdiscr_of_Hstar Hstar) e τ HT).
Qed.

Theorem soundness e τ (HT : mtC ∣ nil ∣ □ ⊢ₑ e : τ) :
  safe e.



