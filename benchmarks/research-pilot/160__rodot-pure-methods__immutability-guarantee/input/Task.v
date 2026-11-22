Set Implicit Arguments.

Require Import LibExtra AbstractSyntax GeneralTyping ConfigTyping.
Require Import OperationalSemantics MutableReachability.

Section WithRodotMode.
Context (typing_mode: Mode).
Context (Hmm: mode_has_mutability typing_mode).

Theorem immutability_guarantee t1 s1 S1 e1 Lv1 F T n t2 s2 S2 e2 Lv2 y ds:
    binds y (item_obj ds) S1 ->
    ty_config F (t1 ; s1 ; S1 ; e1; Lv1) T ->
    (t1 ; s1 ; S1 ; e1; Lv1) ⊣ n ↦* (t2 ; s2 ; S2 ; e2; Lv2) -> (
      binds y (item_obj ds) S2 \/
      F ⊢ (t1 ; s1 ; S1 ; e1; Lv1) mreach y
    ).

End WithRodotMode.
