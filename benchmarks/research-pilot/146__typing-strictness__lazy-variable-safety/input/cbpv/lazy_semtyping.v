Require Export strictness.cbpv.typing strictness.cbpv.semantics.

Require Import Coq.Program.Equality.

Require Import Coq.Logic.Eqdep_dec.

Require Import Coq.Arith.Peano_dec.

From Coq Require Import FunctionalExtensionality.

Require Import Psatz.

Fixpoint LR {n k} (τ : Ty n k) (C : Clos k) mLower (γCtx : attrs n) :=
    (match τ in Ty _ k return Clos k -> Prop with
    | VUnit => fun C => C = Unit
    | VThunk γ B => fun C =>
      exists mOuter mInner γScoped γInner ρ M (HInner : mOuter <= mInner) (Hn : mOuter <= n) (HLower : mLower <= mOuter),
        down_env_until γ mOuter Hn = γScoped /\
        down_env_until γInner mOuter HInner = γScoped /\
        C = Thunk mOuter mInner γScoped ρ M /\
        (forall (Hnlower : mLower <= n),
          (down_env_until γCtx mLower Hnlower) γS<= (down_env_until γ mLower Hnlower) ->
        exists T, EvalComp γInner ρ M T /\ LR B (mOuter T↓ T) mLower γCtx)
    | VProd A1 A2 => fun C => exists W1 W2,
      C = Pair W1 W2 /\ LR A1 W1 mLower γCtx /\ LR A2 W2 mLower γCtx
    | VSum A1 A2 => fun C => exists W',
      (C = Inl W' /\ LR A1 W' mLower γCtx) \/ (C = Inr W' /\ LR A2 W' mLower γCtx)
    | CF A => fun C => exists W, C = Return W /\ LR A W mLower γCtx
    | CAbs q A B => fun C =>
      exists mOuter mInner γScoped γInner ρ M (Hn : mOuter <= n) (HInner : mOuter <= mInner) (HLower : mLower <= mOuter),
      down_env_until γInner mOuter HInner = γScoped /\
      C = Closure mOuter mInner γScoped ρ M /\
      (forall W, LR A W mLower γCtx ->
        exists T, EvalComp (q .: γInner) ((mOuter W↓ W) .: ρ) M T /\ LR B (mOuter T↓ T) mLower γCtx)
    end) C
.

Definition ρ_ok {n} (γ : attrs n) (ρ : env n) (Γ : context n) mLower γCtx :=
  forall (i : fin n), γ i <> Lazy -> LR (Γ i) (ρ i) mLower γCtx.

Definition SemVWt {n} (γ : attrs n) (Γ : context n) V (A : ValTy n) :=
  forall ρ γCtx mLower (Hnlower : mLower <= n), ρ_ok γCtx ρ Γ mLower γCtx ->
    γCtx = pad_with Strict (down_env_until γCtx mLower Hnlower) n Hnlower ->
    (down_env_until γCtx mLower Hnlower) γS<= (down_env_until γ mLower Hnlower) ->
    exists W, EvalVal γ ρ V W /\ LR A W mLower γCtx.

Definition SemCWt {n} (γ : attrs n) (Γ : context n) M (B : CompTy n) :=
  forall ρ γCtx mLower (Hnlower : mLower <= n), ρ_ok γCtx ρ Γ mLower γCtx ->
    γCtx = pad_with Strict (down_env_until γCtx mLower Hnlower) n Hnlower ->
    (down_env_until γCtx mLower Hnlower) γS<= (down_env_until γ mLower Hnlower) ->
    exists T, EvalComp γ ρ M T /\ LR B T mLower γCtx.

Section SemTyping.

Context {n : nat} (γ : attrs n) (Γ : context n).

End SemTyping.
