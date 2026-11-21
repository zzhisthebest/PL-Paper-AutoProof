Set Implicit Arguments.

Require Import Coq.Program.Equality List.

Require Import Sequences.

Require Import Definitions Binding.

Reserved Notation "γ '⟦' t '⤳' u '⟧'" (at level 40).

Inductive lookup_step : sta -> def_rhs -> def_rhs -> Prop :=




| lookup_var : forall γ x v,
    binds x v γ ->
    γ ⟦ pvar x ⤳ defv v ⟧




| lookup_sel_p : forall γ p q a,
    γ ⟦ p ⤳ defp q ⟧ ->
    γ ⟦ p•a ⤳ defp (q•a) ⟧




| lookup_sel_v : forall γ p a t T ds,
    γ ⟦ p ⤳ defv (val_new T ds) ⟧ ->
    defs_has ds { a := t } ->
    γ ⟦ p•a ⤳ open_defrhs_p p t ⟧

where "γ '⟦' p '⤳' t '⟧'" := (lookup_step γ (defp p) t).

Notation "γ '⟦' t '⤳*' u '⟧'" := (star (lookup_step γ) t u) (at level 40).
