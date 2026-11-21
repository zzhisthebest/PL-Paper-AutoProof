Require Export uni.def_ott.

Require Export uni.def_extra.

Require Export uni.decl.def_extra.

Require Export uni.prop_ln.

Notation "x ∉ L" := (x `notin` L)
  (at level 70, no associativity).

Notation "` X" := (typ_var_f X)
  (at level 0, X at level 0, no associativity) : type_scope.

Notation "↑ n" := (typ_var_b n)
  (at level 0, n at level 0, no associativity) : type_scope.

Notation "{ B ᵗ/ₜ X } A" :=
  (subst_typ_in_typ B X A)
    ( at level 49, B at level 50, X at level 0, right associativity) : type_scope.

Notation "{ e' ᵉ/ₑ x } e" :=
  (subst_exp_in_exp e' x e)
    ( at level 49, e' at level 50, x at level 0, right associativity) : type_scope.

Notation "{ A ᵉ/ₜ X } e" :=
  (subst_typ_in_exp A X e)
    ( at level 49, A at level 50, X at level 0, right associativity) : type_scope.

Notation "{ A ᶜˢ/ₜ X } cs" :=
  (subst_typ_in_conts A X cs)
    ( at level 49, A at level 50, X at level 0, right associativity) : type_scope.

Notation "{ A ᶜᵈ/ₜ X } cd" :=
  (subst_typ_in_contd A X cd)
    ( at level 49, A at level 50, X at level 0, right associativity) : type_scope.

Notation "{ e ᶜˢ/ₑ x } cs" :=
  (subst_exp_in_conts e x cs)
    ( at level 49, e at level 50, x at level 0, right associativity) : type_scope.

Notation "{ e ᶜᵈ/ₑ x } cd" :=
  (subst_exp_in_contd e x cd)
    ( at level 49, e at level 50, x at level 0
    , right associativity) : type_scope.

Notation "{ A ʷ/ₜ X } w" :=
  (subst_typ_in_work A X w)
    ( at level 49, A at level 50, X at level 0
    , right associativity) : type_scope.

Notation "{ e ʷ/ₑ x } w" :=
  (subst_exp_in_work e x w)
    ( at level 49, e at level 50, x at level 0
    , right associativity) : type_scope.

Notation "{ A ᵃʷ/ₜ X } Γ" :=
  (subst_typ_in_aworklist A X Γ)
    ( at level 49, A at level 50, X at level 0
    , right associativity) : type_scope.

Notation "T ᵗ^ₜ X" := (open_typ_wrt_typ T (typ_var_f X))
  (at level 48, left associativity) : type_scope.

Notation "T1 ᵗ^^ₜ T2" := (open_typ_wrt_typ T1 T2)
  (at level 48, left associativity) : type_scope.

Notation "e1 ᵉ^^ₑ e2" := (open_exp_wrt_exp e1 e2)
  (at level 48, left associativity) : type_scope.

Notation "e ᵉ^^ₜ A" := (open_exp_wrt_typ e A)
  (at level 48, left associativity) : type_scope.

Notation "⊢ᵈ Ψ" :=
  (d_wf_env Ψ)
    (at level 65, no associativity) : type_scope.

Notation "⊢ᵈₜ Ψ" :=
  (d_wf_tenv Ψ)
    (at level 65, no associativity) : type_scope.

Notation "Ψ ᵗ⊢ᵈ A" :=
  (d_wf_typ Ψ A)
    (at level 65, no associativity) : type_scope.

Notation "Ψ ᵗ⊢ᵈₘ T" :=
  (d_mono_typ Ψ T)
    (at level 65, no associativity) : type_scope.

Notation "Ψ ᵉ⊢ᵈ e" :=
  (d_wf_exp Ψ e)
    (at level 65, no associativity) : type_scope.

Notation "X ~ □ ∈ᵈ Ψ" := (binds X (dbind_tvar_empty) Ψ)
  (at level 50, no associativity) : type_scope.

Notation "X ~ ■ ∈ᵈ Ψ" := (binds X (dbind_stvar_empty) Ψ)
  (at level 50, no associativity) : type_scope.

Notation "x ~ A ∈ᵈ Ψ" := (binds x (dbind_typ A) Ψ)
  (at level 50, A at next level, no associativity) : type_scope.

Notation "Ψ ⊢ A <: B" :=
  (d_sub Ψ A B)
    (at level 65, A at next level, no associativity) : type_scope.

Notation "Ψ ⊢ e ⇐ A" :=
  (d_chk_inf Ψ e typingmode__chk A)
    (at level 65, e at next level, no associativity) : type_scope.

Notation "Ψ ⊢ e ⇒ A" :=
  (d_chk_inf Ψ e typingmode__inf A)
    (at level 65, e at next level, no associativity) : type_scope.

Notation "Ψ ⊢ A ○ B ⇒⇒ C" :=
  (d_inftapp Ψ A B C)
    (at level 65, A at next level, B at next level, no associativity) : type_scope.

Notation "Ψ ⊢ A ▹ B → C" :=
  (d_infabs Ψ A B C)
    (at level 65, A at next level, B at next level, no associativity) : type_scope.

Notation "Σ ᵗ⊢ᵃ A" :=
  (a_wf_typ Σ A)
    (at level 65, no associativity) : type_scope.

Notation "Σ ᵗ⊢ᵃₘ A" :=
  (a_mono_typ Σ A)
    (at level 65, no associativity) : type_scope.

Notation "⊢ᵃ Σ" :=
  (a_wf_env Σ)
    (at level 65, no associativity) : type_scope.

Notation "Σ ᵉ⊢ᵃ e" :=
  (a_wf_exp Σ e)
    (at level 65, no associativity) : type_scope.

Notation "Σ ᶜˢ⊢ᵃ cs" :=
  (a_wf_conts Σ cs)
    (at level 65, no associativity) : type_scope.

Notation "Σ ᶜᵈ⊢ᵃ cd" :=
  (a_wf_contd Σ cd)
    (at level 65, no associativity) : type_scope.

Notation "Σ ʷ⊢ᵃ cd" :=
  (a_wf_work Σ cd)
    (at level 65, no associativity) : type_scope.

Notation "X ~ □ ∈ᵃ Σ" := (binds X (abind_tvar_empty) Σ)
  (at level 50, no associativity) : type_scope.

Notation "X ~ ■ ∈ᵃ Σ" := (binds X (abind_stvar_empty) Σ)
  (at level 50, no associativity) : type_scope.

Notation "X ~ ⬒ ∈ᵃ Σ" := (binds X (abind_etvar_empty) Σ)
  (at level 50, no associativity) : type_scope.

Notation "x ~ A ∈ᵃ Σ" := (binds x (abind_var_typ A) Σ)
  (at level 50, A at next level, no associativity) : type_scope.

Declare Scope dbind_scope.

Delimit Scope dbind_scope with dbind.

Bind Scope dbind_scope with dbind.

Notation "□" := dbind_tvar_empty : dbind_scope.

Notation "■" := dbind_stvar_empty : dbind_scope.

Declare Scope abind_scope.

Delimit Scope abind_scope with abind.

Bind Scope abind_scope with abind.

Notation "□" := abind_tvar_empty : abind_scope.

Notation "■" := abind_stvar_empty : abind_scope.

Notation "⬒" := abind_etvar_empty : abind_scope.
