Require Import Utf8.

Require Import Lang.Syntax.

Record op_sig (Eff : Set) : Set :=
  { op_input  : typ0 Eff
  ; op_output : typ0 Eff
  }.

Arguments op_input  {Eff}.

Arguments op_output {Eff}.

Definition eff_sig (Eff : Set) : Set := Eff → list (op_sig Eff).

Reserved Notation "'Ef[' FS '⊢' op '∷' Θ ']'".

Inductive op_typing {Eff : Set} (Θ : op_sig Eff) :
    list (op_sig Eff) → Op → Prop :=
| OT_O : ∀ FS, Ef[ Θ :: FS ⊢ 0 ∷ Θ ]
| OT_S : ∀ FS Θ' op,
    Ef[ FS ⊢ op ∷ Θ ] →
    Ef[ Θ' :: FS ⊢ S op ∷ Θ ]
where "Ef[ FS ⊢ op ∷ Θ ]" := (@op_typing _ Θ FS op).

Definition shift_env {Eff V EV : Set} (Γ : V → typ Eff EV) :
    V → typ Eff (inc EV) := λ x, tshift (Γ x).

Notation "Γ '↑+'" := (shift_env Γ) (at level 45, left associativity).

Section Typing.

Context {Eff : Set} {EffDec : DecEffectEq Eff}.

Context (Σ : eff_sig Eff).

Reserved Notation "'SF[' ε₁ '≾' ε₂ ']'".

Inductive subeff {EV : Set} : effect Eff EV → effect Eff EV → Prop :=
| SF_Refl  : ∀ (ε : effect Eff EV), SF[ ε ≾ ε ]
| SF_Trans : ∀ (ε₁ ε₂ ε₃ : effect Eff EV),
    SF[ ε₁ ≾ ε₂ ] → SF[ ε₂ ≾ ε₃ ] → SF[ ε₁ ≾ ε₃ ]
| SF_Swap  : ∀ l₁ l₂ (ε : effect Eff EV),
    SF[ ef_cons l₁ (ef_cons l₂ ε) ≾ ef_cons l₂ (ef_cons l₁ ε) ]
| SF_Nil   : ∀ (ε : effect Eff EV), SF[ ef_nil ≾ ε ]
| SF_Cons  : ∀ l (ε₁ ε₂ : effect Eff EV),
   SF[ ε₁ ≾ ε₂ ] →
   SF[ ef_cons l ε₁ ≾ ef_cons l ε₂ ]
where "SF[ ε₁ ≾ ε₂ ]" := (@subeff _ ε₁ ε₂).

Reserved Notation "'ST[' σ '≾' τ ']'".

Inductive subtyp {EV : Set} : typ Eff EV → typ Eff EV → Prop :=
| ST_Refl  : ∀ (τ : typ Eff EV), ST[ τ ≾ τ ]
| ST_Trans : ∀ (τ₁ τ₂ τ₃ : typ Eff EV),
    ST[ τ₁ ≾ τ₂ ] → ST[ τ₂ ≾ τ₃ ] → ST[ τ₁ ≾ τ₃ ]
| ST_Arrow : ∀ σ₁ σ₂ ε₁ ε₂ (τ₁ τ₂ : typ Eff EV),
    ST[ σ₂ ≾ σ₁ ] →
    SF[ ε₁ ≾ ε₂ ] →
    ST[ τ₁ ≾ τ₂ ] →
    ST[ t_arrow σ₁ ε₁ τ₁ ≾ t_arrow σ₂ ε₂ τ₂ ]
| ST_ForallE : ∀ (τ₁ τ₂ : typ Eff (inc EV)),
    ST[ τ₁ ≾ τ₂ ] →
    ST[ t_forallE τ₁ ≾ t_forallE τ₂ ]
where "ST[ σ ≾ τ ]" := (@subtyp _ σ τ).

Reserved Notation "'T[' Γ '⊢' e '∷' τ '//' ε ']'".

Reserved Notation "'H[' Γ ';' FS '⊢' h '∷' τ '//' ε ']'".

Inductive typing {V EV : Set} (Γ : V → typ Eff EV) :
    expr Eff V → typ Eff EV → effect Eff EV → Prop :=
| T_var  : ∀ x,
    T[ Γ ⊢ v_var x ∷ Γ x // ef_nil ]
| T_unit :
    T[ Γ ⊢ v_unit ∷ t_unit // ef_nil ]
| T_lam  : ∀ e σ ε τ,
    T[ Γ ,+ σ ⊢ e ∷ τ // ε ] →
    T[ Γ ⊢ v_lam e ∷ t_arrow σ ε τ // ef_nil ]
| T_elam : ∀ e τ,
    T[ Γ ↑+ ⊢ e ∷ τ // ef_nil ] →
    T[ Γ ⊢ v_elam e ∷ t_forallE τ // ef_nil ]
| T_op   : ∀ l op Θ,
    Ef[ Σ l ⊢ op ∷ Θ ] →
    T[ Γ ⊢ v_op l op ∷
      t_arrow (topen (op_input Θ))
              (ef_cons l ef_nil)
              (topen (op_output Θ))
      // ef_nil ]
| T_app  : ∀ e₁ e₂ σ τ ε,
    T[ Γ ⊢ e₁ ∷ t_arrow σ ε τ // ε ] →
    T[ Γ ⊢ e₂ ∷ σ // ε ] →
    T[ Γ ⊢ e_app e₁ e₂ ∷ τ // ε ]
| T_eapp : ∀ e τ ε ε',
    T[ Γ ⊢ e ∷ t_forallE τ // ε ] →
    T[ Γ ⊢ e_eapp e ∷ tsubst τ ε' // ε ]
| T_lift : ∀ l e τ ε,
    T[ Γ ⊢ e ∷ τ // ε ] →
    T[ Γ ⊢ e_lift l e ∷ τ // ef_cons l ε ]
| T_handle : ∀ l e h r σ τ ε,
    T[ Γ ⊢ e ∷ σ // ef_cons l ε ] →
    H[ Γ ; Σ l ⊢ h ∷ τ // ε ] →
    T[ Γ ,+ σ ⊢ r ∷ τ // ε ] →
    T[ Γ ⊢ e_handle l e h r ∷ τ // ε ]
| T_sub : ∀ e τ₁ τ₂ ε₁ ε₂,
    T[ Γ ⊢ e ∷ τ₁ // ε₁ ] →
    ST[ τ₁ ≾ τ₂ ] →
    SF[ ε₁ ≾ ε₂ ] →
    T[ Γ ⊢ e ∷ τ₂ // ε₂ ]
with htyping {V EV : Set} (Γ : V → typ Eff EV) : list (op_sig Eff) →
    list (expr Eff (inc (inc V))) → typ Eff EV → effect Eff EV → Prop :=
| H_nil  : ∀ τ ε, H[ Γ ; nil ⊢ nil ∷ τ // ε ]
| H_cons : ∀ Θ FS e h τ ε,
    T[ Γ ,+ topen (op_input Θ) ,+ t_arrow (topen (op_output Θ)) ε τ
     ⊢ e ∷ τ // ε ] →
    H[ Γ ; FS ⊢ h ∷ τ // ε ] →
    H[ Γ ; Θ :: FS ⊢ e :: h ∷ τ // ε ]
where "T[ Γ ⊢ e ∷ τ // ε ]"     := (@typing _ _ Γ e τ ε)
and   "H[ Γ ; FS ⊢ h ∷ τ // ε ]" := (@htyping _ _ Γ FS h τ ε).

End Typing.

Notation "SF[ ε₁ ≾ ε₂ ]" := (@subeff _ _ ε₁ ε₂).

Notation "ST[ σ ≾ τ ]"   := (@subtyp _ _ σ τ).

Notation "'T[' Σ ; Γ '⊢' e '∷' τ '//' ε ']'" := (@typing _ Σ _ _ Γ e τ ε).

Notation "'H[' Σ ; Γ ; FS '⊢' h '∷' τ '//' ε ']'" :=
  (@htyping _ Σ _ _ Γ FS h τ ε).
