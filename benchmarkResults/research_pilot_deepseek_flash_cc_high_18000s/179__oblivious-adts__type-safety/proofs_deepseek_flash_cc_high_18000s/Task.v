From oadt Require Import lang_oadt.base.

From oadt Require Import lang_oadt.syntax.

From oadt Require Import lang_oadt.semantics.

From oadt Require Import lang_oadt.typing.

Import syntax.notations.

Import semantics.notations.

Import typing.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

Definition stuck (Σ : gctx) (e : expr) : Prop :=
  nf (@step Σ) e /\ ¬val e.

Theorem soundness e Σ τ e' :
  Σ; e ▷ τ ->
  Σ ⊨ e -->* e' ->
  ¬(stuck Σ e').
