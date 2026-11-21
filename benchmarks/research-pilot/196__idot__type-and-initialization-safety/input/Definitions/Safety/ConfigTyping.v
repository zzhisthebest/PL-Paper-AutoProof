Set Implicit Arguments.

Require Import LibExtra List.

Require Import AbstractSyntax Typing GeneralTyping RecordTypes InertTypes DefRecordInertTyping HeapCorrespondence.

Require Import Effects.

Require Import HeapDefsPointsTo WellPointed.

Require Import FreeItems.

Require Import Initialization InitTyping CommittedSubHeap.

Require Import FreeSubHeapSingle.

Require Import EffectCorrespondence FreeSubHeapStack StackTyping InertInitContexts.

Inductive ty_config :
  ctx -> init_ctx -> list eff_ctx -> list effects -> config -> typ -> Prop :=

| ty_config_c : forall Gamma Delta Sigma ℰ ℰs Fs t T i U effs' effs effss,
    inert Gamma ->
    inert_inits Delta ->
    heap_correspond Gamma Sigma ->
    free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs) ->
    ty_stack Gamma Delta (ℰ :: ℰs) Fs T i (effs :: effss)%list U ->
    Gamma ⊢ t ∶ T ->
    ⊢e t ∶ effs' ->
    Gamma ⸴ Delta ⸴ (dom ℰ) ⊢i t ∶ i ->
    eff_ctx_corr (ℰ :: ℰs) ((effs' ++ effs) :: effss)%list ->
    ty_config Gamma Delta (ℰ :: ℰs) ((effs' ++ effs) :: effss)%list (t; Fs; Sigma) U.
