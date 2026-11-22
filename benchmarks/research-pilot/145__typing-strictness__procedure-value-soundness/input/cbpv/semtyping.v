Require Export strictness.cbpv.typing strictness.cbpv.semantics.

Require Import Coq.Logic.Eqdep_dec.

From Coq Require Import FunctionalExtensionality.

Require Import Psatz.

Require Import Coq.Program.Equality.

Fixpoint LR {n k} (τ : Ty n k) (C : Clos k) :=
    (match τ in Ty _ k return Clos k -> Prop with
    | VUnit => fun C => C = Unit
    | VThunk γ B => fun C =>
      exists mOuter mInner γScoped γInner ρ M (HInner : mOuter <= mInner) (Hn : mOuter <= n),
        down_env_until γ mOuter Hn = γScoped /\
        down_env_until γInner mOuter HInner = γScoped /\
        C = Thunk mOuter mInner γScoped ρ M /\ exists T, EvalComp γInner ρ M T /\ LR B (mOuter T↓ T)
    | VProd A1 A2 => fun C => exists W1 W2,
      C = Pair W1 W2 /\ LR A1 W1 /\ LR A2 W2
    | VSum A1 A2 => fun C => exists W',
      (C = Inl W' /\ LR A1 W') \/ (C = Inr W' /\ LR A2 W')
    | CF A => fun C => exists W, C = Return W /\ LR A W
    | CAbs q A B => fun C =>
      exists mOuter mInner γScoped γInner ρ M (Hn : mOuter <= n) (HInner : mOuter <= mInner),
      down_env_until γInner mOuter HInner = γScoped /\
      C = Closure mOuter mInner γScoped ρ M /\
      (forall W, LR A W -> exists T, EvalComp (q .: γInner) ((mOuter W↓ W) .: ρ) M T /\ LR B (mOuter T↓ T))
    end) C.

Definition ρ_ok {n} (ρ : env n) (Γ : context n) :=
  forall (i : fin n), LR (Γ i) (ρ i).

Notation "Γ |= ρ" := (ρ_ok ρ Γ) (at level 80).

Definition SemVWt {n} (γ : attrs n) (Γ : context n) V (A : ValTy n) :=
  forall ρ, Γ |= ρ -> exists W, EvalVal γ ρ V W /\ LR A W.

Definition SemCWt {n} (γ : attrs n) (Γ : context n) M (B : CompTy n) :=
  forall ρ, Γ |= ρ -> exists T, EvalComp γ ρ M T /\ LR B T.

Section SemTyping.

Context {n : nat} (γ : attrs n) (Γ : context n).

End SemTyping.
