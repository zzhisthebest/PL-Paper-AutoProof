Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Require Import Effects.

Definition eff_ctx_corr_one (ℰ : eff_ctx) effs :=
  (forall x effs', binds x effs' ℰ ->
                   forall eff, (eff \in (from_list effs')) ->
                               (eff \in (from_list effs))).

Inductive eff_ctx_corr : list eff_ctx -> list effects -> Prop :=

| eff_ctx_corr_nil : eff_ctx_corr nil nil

| eff_ctx_corr_cons : forall ℰ ℰs effs effss,
    eff_ctx_corr ℰs effss ->
    eff_ctx_corr_one ℰ effs ->
    eff_ctx_corr (ℰ :: ℰs) (effs :: effss).
