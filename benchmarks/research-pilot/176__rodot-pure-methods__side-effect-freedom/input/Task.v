Set Implicit Arguments.

Require Import LibExtra AbstractSyntax TypingMode GeneralTyping.

Require Import OperationalSemantics ConfigTyping MethodCall.

Theorem SefG_I :
  forall (typing_mode : Mode) (w1 : var) (m : met_label) (w2 : var)
         (TZv : typ) (c1 : config) (G : ctx) (c4 : config) (k : nat),
  mode_has_sef typing_mode ->
  mode_has_mutability typing_mode ->
  config_trm c1 = trm_call (avar_f w1) m (avar_f w2) ->
  (G ⁏ (config_env c1) ⊢ w1 ∶ typ_rcd (dec_met m typ_nocap TZv typ_top) /\
   G ⁏ (config_env c1) ⊢ w2 ∶ TZv /\
   G ⁏ (config_env c1) ⊢ typ_nocap <: TZv) ->
  (exists T1, ty_config G c1 T1) ->
  c1 ⊣k↦* c4 ->
  (exists j c3, frame_end_in c1 j c3 /\ j < k) \/
  subheap_unchanged (config_heap c1) (config_heap c4).
