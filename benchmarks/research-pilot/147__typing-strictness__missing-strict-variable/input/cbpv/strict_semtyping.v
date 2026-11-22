Require Export strictness.cbpv.typing strictness.cbpv.semantics.

Require Import Coq.Program.Equality.

Require Import Coq.Logic.Eqdep_dec.

Require Import Coq.Arith.Peano_dec.

From Coq Require Import FunctionalExtensionality.

Require Import Psatz.

Definition non_func {n} (B : CompTy n) :=
  forall q A B', B <> CAbs q A B'.

Definition LRM {n} (B : Ty n CompFlag)
  (LR_maybe : Ty n CompFlag -> Clos CompFlag -> forall m,fin m -> Prop)
  (LR_no : Ty n CompFlag -> Clos CompFlag -> forall m,fin m -> Prop)
 mInner (γ : attrs mInner) mOuter mLower x (Hnlower : mLower <= mInner) ρ M :=
  ((down_env_until γ mLower Hnlower) x = Strict ->
    (non_func B -> EvalCompFail ρ M) /\
    (~ non_func B -> EvalCompFail ρ M \/ exists T, EvalComp γ ρ M T /\
      LR_no B (mOuter T↓ T) mLower x)) /\
  ((down_env_until γ mLower Hnlower) x <> Strict ->
    EvalCompFail ρ M \/ exists T, EvalComp γ ρ M T /\ LR_maybe B (mOuter T↓ T) mLower x).

Fixpoint LR_maybe {n k} (τ : Ty n k) (C : Clos k) mLower (x : fin mLower) :=
    (match τ in Ty _ k return Clos k -> Prop with
    | VUnit => fun C => C = Unit
    | VThunk γ B => fun C =>
      exists mOuter mInner γScoped γInner ρ M (HInner : mOuter <= mInner)
        (Hn : mOuter <= n) (HLower : mLower <= mOuter) (Hnlower : mLower <= mInner),
        down_env_until γ mOuter Hn = γScoped /\
        down_env_until γInner mOuter HInner = γScoped /\
        C = Thunk mOuter mInner γScoped ρ M /\
        LRM B LR_maybe LR_no mInner γInner mOuter mLower x Hnlower ρ M
    | VProd A1 A2 => fun C => exists W1 W2,
      C = Pair W1 W2 /\ LR_maybe A1 W1 mLower x /\ LR_maybe A2 W2 mLower x
    | VSum A1 A2 => fun C => exists W',
      (C = Inl W' /\ LR_maybe A1 W' mLower x) \/ (C = Inr W' /\ LR_maybe A2 W' mLower x)
    | CF A => fun C => exists W, C = Return W /\ LR_maybe A W mLower x
    | CAbs q A B => fun C =>
      exists mOuter mInner γScoped γInner ρ M (Hn : mOuter <= n)
        (HInner : mOuter <= mInner) (HLower : mLower <= mOuter) (Hnlower : mLower <= mInner),
      down_env_until γInner mOuter HInner = γScoped /\
      C = Closure mOuter mInner γScoped ρ M /\
      (forall W, LR_maybe A W mLower x ->
        EvalCompFail ((mOuter W↓ W) .: ρ) M \/
        exists T, EvalComp (q .: γInner) ((mOuter W↓ W) .: ρ) M T /\ LR_maybe B (mOuter T↓ T) mLower x)
    end) C

with LR_no {n k} (τ : Ty n k) (C : Clos k) mLower (x : fin mLower) :=
    (match τ in Ty _ k return Clos k -> Prop with
    | CAbs q A B => fun C =>
      exists mOuter mInner γScoped γInner ρ M (Hn : mOuter <= n) (HInner : mOuter <= mInner)
        (HLower : mLower <= mOuter) (Hnlower : mLower <= mInner),
      down_env_until γInner mOuter HInner = γScoped /\
      C = Closure mOuter mInner γScoped ρ M /\
      (forall W, LR_maybe A W mLower x ->
        (non_func B -> EvalCompFail ((mOuter W↓ W) .: ρ) M) /\
        (~ non_func B -> EvalCompFail ((mOuter W↓ W) .: ρ) M \/
            exists T, EvalComp (q .: γInner) ((mOuter W↓ W) .: ρ) M T /\ LR_no B (mOuter T↓ T) mLower x))
    | _ => fun C => False
    end) C.

Definition ρ_not_ok {n} γ (ρ : env n) (Γ : context n) mLower (x : fin mLower) (Hnlower : mLower <= n) :=
    (down_env_until γ mLower Hnlower) x = Strict /\
    (down_env_until ρ mLower Hnlower) x = Absent /\
    (forall (j : fin n), j <> up_fin_until n Hnlower x -> LR_maybe (Γ j) (ρ j) mLower x).

Definition ρ_maybe_ok {n} γ (ρ : env n) (Γ : context n) mLower (x : fin mLower) (Hnlower : mLower <= n) :=
    (down_env_until γ mLower Hnlower) x <> Strict /\
    (down_env_until ρ mLower Hnlower) x = Absent /\
    (forall (j : fin n), j <> up_fin_until n Hnlower x -> LR_maybe (Γ j) (ρ j) mLower x).

Definition SemVWt {n} (γ : attrs n) (Γ : context n) V (A : ValTy n) :=
    forall ρ mLower x (Hnlower : mLower <= n),
        (ρ_not_ok γ ρ Γ mLower x Hnlower -> EvalValFail ρ V) /\
        (ρ_maybe_ok γ ρ Γ mLower x Hnlower ->
          EvalValFail ρ V \/ exists W, EvalVal γ ρ V W /\ LR_maybe A W mLower x).

Definition SemCWt {n} (γ : attrs n) (Γ : context n) M (B : CompTy n) :=
    forall ρ mLower x (Hnlower : mLower <= n),
        (ρ_not_ok γ ρ Γ mLower x Hnlower ->
            (non_func B -> EvalCompFail ρ M) /\
            (~ non_func B -> EvalCompFail ρ M \/ exists T, EvalComp γ ρ M T /\ LR_no B T mLower x)) /\
        (ρ_maybe_ok γ ρ Γ mLower x Hnlower ->
            EvalCompFail ρ M \/ exists T, EvalComp γ ρ M T /\ LR_maybe B T mLower x).

Section SemTyping.

Context {n : nat} (γ : attrs n) (Γ : context n).

End SemTyping.
