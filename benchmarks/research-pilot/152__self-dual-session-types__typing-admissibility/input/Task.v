Require Import Language Sessions.

Theorem ForkB_typed Γ σ e :
  typed Γ e (FunT Lin (toL (dual σ)) UnitT) ->
  typed Γ (ForkB e) (toL σ).

Theorem SendB_typed Γ Γ1 Γ2 e1 e2 n ts σs i :
  env_split Γ Γ1 Γ2 ->
  typed Γ1 e1 (toL (SendTB n ts σs)) ->
  typed Γ2 e2 (ts i) ->
  typed Γ (SendB e1 i e2) (toL (σs i)).

Theorem RecvB_typed Γ e n ts σs :
  typed Γ e (toL (RecvTB n ts σs)) ->
  typed Γ (RecvB e) (SumT n (λ i, PairT (toL (σs i)) (ts i))).

Theorem CloseB_typed Γ e :
  typed Γ e (toL EndTB) ->
  typed Γ (CloseB e) UnitT.
