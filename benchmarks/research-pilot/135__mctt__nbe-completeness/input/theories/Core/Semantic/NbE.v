From Mctt.Core Require Import Base.

From Mctt.Core.Semantic Require Export Domain Evaluation Readback.

From Mctt.Core.Syntactic Require Export System.

Import Domain_Notations.

Generalizable All Variables.

Inductive initial_env : ctx -> env -> Prop :=
| initial_env_nil : initial_env nil empty_env
| initial_env_cons :
  `( initial_env Γ ρ ->
     {{ ⟦ A ⟧ ρ ↘ a }} ->
     initial_env (A :: Γ) d{{{ ρ ↦ ⇑! a (length Γ) }}}).

Inductive nbe : ctx -> exp -> typ -> nf -> Prop :=
| nbe_run :
  `( initial_env Γ ρ ->
     {{ ⟦ A ⟧ ρ ↘ a }} ->
     {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ Rnf ⇓ a m in (length Γ) ↘ w }} ->
     nbe Γ M A w ).

Inductive nbe_ty : ctx -> typ -> nf -> Prop :=
| nbe_ty_run :
  `( initial_env Γ ρ ->
     {{ ⟦ M ⟧ ρ ↘ m }} ->
     {{ Rtyp m in (length Γ) ↘ W }} ->
     nbe_ty Γ M W ).
