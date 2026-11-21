Require Import Utf8.

Require Import Lang.FOmegaEq.Types Lang.FOmegaEq.Kinds Lang.FOmegaEq.Syntax Lang.FOmegaEq.OpSemantics Lang.FOmegaEq.Typing.

Import Binding.Intrinsic (Ctx, dom, extC, Build_Ctx, mtC).

Require Import Binding.Lib Binding.Env.

Import kindEqDec.

Require Import Coq.Relations.Relation_Operators Coq.Relations.Operators_Properties.

Local Open Scope syn_scope.

Require Import List.

Theorem soundness e τ (HT : mtC ∣ nil ∣ □ ⊢ₑ e : τ) :
  safe e.
