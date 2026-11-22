Require Import Coq.Program.Equality.

Require Import Program.Tactics.

Require Import Metalib.Metatheory.

Require Import List.

Require Import uni.notations.

Require Import uni.algo_worklist.def_extra.

Require Import Coq.Logic.Classical_Prop.

Open Scope aworklist_scope.

Open Scope dworklist_scope.

Theorem a_wf_wl_red_decidable_thm : forall Γ,
  ⊢ᵃʷₛ Γ ->
  Γ ⟶ᵃʷ⁎⋅ \/ ~ Γ ⟶ᵃʷ⁎⋅.
Proof.
  intros Γ H.
  apply classic.
Qed.
