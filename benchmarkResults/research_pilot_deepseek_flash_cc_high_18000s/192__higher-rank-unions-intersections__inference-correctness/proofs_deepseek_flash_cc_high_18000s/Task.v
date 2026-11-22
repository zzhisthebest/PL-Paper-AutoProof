Require Import Coq.Program.Equality.

Require Import Program.Tactics.

Require Import Metalib.Metatheory.

Require Import List.

Require Import uni.notations.

Require Import uni.algo_worklist.def_extra.

Open Scope aworklist_scope.

Open Scope dworklist_scope.

Theorem a_wl_red_chk_soundness: forall e A,
  nil ᵉ⊢ᵃ e ->
  nil ᵗ⊢ᵃ A ->
  (work_check e A ⫤ᵃ aworklist_empty) ⟶ᵃʷ⁎⋅ ->
  nil ⊢ e ⇐ A.

Theorem a_wl_red_inf_soundness: forall e,
  nil ᵉ⊢ᵃ e ->
  (work_infer e (conts_sub typ_top) ⫤ᵃ aworklist_empty) ⟶ᵃʷ⁎⋅ ->
  exists A, nil ⊢ e ⇒ A.

Theorem a_wl_red_chk_completeness : forall e A,
  nil ᵉ⊢ᵈ e ->
  nil ᵗ⊢ᵈ A ->
  nil ⊢ e ⇐ A ->
  (work_check e A ⫤ᵃ aworklist_empty) ⟶ᵃʷ⁎⋅.

Theorem a_wl_red_inf_completeness : forall e A,
  nil ᵉ⊢ᵈ e ->
  nil ⊢ e ⇒ A ->
  (work_infer e (conts_sub typ_top) ⫤ᵃ aworklist_empty) ⟶ᵃʷ⁎⋅.
