Set Implicit Arguments.

Require Import LibExtra.

Require Import AbstractSyntax PreTyping Typing GeneralTyping.

Require Import Effects Initialization InitTyping.

Inductive ty_stack :
  ctx -> init_ctx -> list eff_ctx -> stack ->
  typ -> init_typ -> list effects -> typ -> Prop :=

  | ty_stack_nil : forall Gamma Delta T U ℰ i,
      Gamma ⊢ T <: U ->
              ty_stack Gamma Delta (ℰ :: nil)
                       nil T i
                       (nil :: nil)%list U

  | ty_stack_let : forall L Gamma Delta ℰ ℰs Fs t S i i' T effs effss effs' U,
      ty_stack Gamma Delta (ℰ :: ℰs)
               Fs T i'
               (effs :: effss) U ->
      (forall x, x \notin L -> Gamma & x ~ S ⊢ open x t ∶ T) ->
      (forall x,
          x \notin L ->
          Gamma & x ~ S ⸴ Delta & x ~ i ⸴ dom ℰ \u \{ x} ⊢i open x t ∶ i') ->
      (forall x, x \notin L -> ⊢e open x t ∶ effs') ->
      ty_stack Gamma Delta (ℰ :: ℰs)
               (frame_let t :: Fs)%list S i
               ((effs' ++ effs) :: effss)%list U

  | ty_stack_ret_free : forall Gamma Delta ℰ ℰs Fs x S i effs effss T U,
      ty_stack Gamma Delta (ℰ :: ℰs)
               Fs T free
               (effs :: effss) U ->
      Gamma ⊢ trm_var (avar_f x) ∶ T ->
      Gamma ⸴ Delta ⸴ (dom ℰ) ⊢i trm_var (avar_f x) ∶ free ->
      ty_stack Gamma Delta (ℰ :: ℰs)
               (frame_ret x :: Fs)%list S i
               (effs :: effss)%list U

  | ty_stack_ret_committed : forall Gamma Delta ℰ ℰs Fs x S i effss T U,
      ty_stack Gamma Delta ℰs
               Fs T committed
               effss U ->
      Gamma ⊢ trm_var (avar_f x) ∶ T ->

      Gamma ⸴ Delta ⸴ (dom ℰ) ⊢i trm_var (avar_f x) ∶ free ->
      ty_stack Gamma Delta (ℰ :: ℰs)
               (frame_ret x :: Fs)%list S i
               (nil :: effss)%list U.
