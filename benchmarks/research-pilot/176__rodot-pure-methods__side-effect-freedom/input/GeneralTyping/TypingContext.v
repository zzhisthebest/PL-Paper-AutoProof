Set Implicit Arguments.

Require Import TypingMode.

Require Import LibExtra AbstractSyntax.

Notation vis_hide typing_mode G := (
  match (mode_visibility' typing_mode) with
  | mode_visibility_all => G
  | mode_visibility_hide_method => (ctx_hide G)
  end
  ) (only parsing).

Definition ctx_obj_met typing_mode (G: ctx)(Go: objctx)(xz: var)(TZ: typ)(xc: var)(TC: typ) :=
  match Go with
  | objctx_empty => ctx_met (vis_hide typing_mode G) xz TZ xc TC
  | objctx_lit x T => ctx_met_refined (vis_hide typing_mode (G § x / v_self ~ open x T)) xz TZ xc TC (typ_and (open x T) (open xc T))
  | objctx_heap y T => ctx_met_refined_heap (vis_hide typing_mode G) xz TZ xc TC y T

  end.
