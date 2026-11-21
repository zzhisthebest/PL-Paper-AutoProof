Require full.CBN.translation full.CBV.translation.

Module CBN.

Import full.CBN.translation.

Theorem cbn_translation_correct :
    forall n (γ : gradeVec n) (Γ : contextL n) e T,
    Wt γ Γ e T ->
    CWt γ (translateContext Γ)
        (translateTerm e) (translateType T) ϵ.

End CBN.

Module CBV.

Import full.CBV.translation.

Theorem cbv_translation_correct :
    forall n (γ : gradeVec n) (Γ : contextL n) e T,
    Wt γ Γ e T ->
    CWt γ (translateContext Γ)
        (translateTerm e) (CF Qone (translateType T)) ϵ.

End CBV.
