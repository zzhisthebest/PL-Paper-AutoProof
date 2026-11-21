Require Import Utf8.

Require Import Lang.Syntax Lang.Typing.

Require Import Lang.Reduction.

Section TypeSoundness.

Context {Eff : Set} {EffDec : DecEffectEq Eff}.

Context {Σ : eff_sig Eff}.

Theorem type_soundness (e e' : expr0 Eff) :
  T[ Σ; of_empty ⊢ e ∷ (t_unit : typ0 Eff) // ef_nil ] →
  red_rtc e e' →
  irred e' →
  e' = v_unit.

End TypeSoundness.
