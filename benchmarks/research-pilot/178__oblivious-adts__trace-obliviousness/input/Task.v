From oadt Require Import lang_oadt.base.

From oadt Require Import lang_oadt.syntax.

From oadt Require Import lang_oadt.semantics.

From oadt Require Import lang_oadt.typing.

Import syntax.notations.

Import semantics.notations.

Import typing.notations.

Implicit Types (b : bool) (x X y Y : atom) (L : aset).

Definition trace_indistinguishable Σ e1 e2 : Prop :=
  forall n e1',
    Σ ⊨ e1 -->{n} e1' ->
    (exists e2', Σ ⊨ e2 -->{n} e2') /\
    (forall e2', Σ ⊨ e2 -->{n} e2' -> e1' ≈ e2').

Theorem obliviousness Σ e1 e2 τ1 τ2 :
  Σ; e1 ▷ τ1 ->
  Σ; e2 ▷ τ2 ->
  e1 ≈ e2 ->
  trace_indistinguishable Σ e1 e2.
