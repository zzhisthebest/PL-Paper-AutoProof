Require Import Lang.FOmegaEq.Syntax.

Require Import Utf8.

Require Import Binding.Lib.

Require Import Coq.Relations.Relation_Operators Coq.Relations.Operators_Properties Coq.Classes.RelationClasses.

Reserved Notation "e ↦ e'" (at level 70).

Inductive head_step : expr ∅ → expr ∅ → Prop :=
| LamBetaRec e v : (rec e) v ↦ subst (Inc := inc) ((subst (Inc := inc) e) (shift v)) (rec e)
| LamBetaE e v : (ƛ e) v ↦ subst (Inc := inc) e v
| LamBetaT e : e_tapp (Λ e) ↦ e
| LamBetaC e : e_capp (ƛᶜ e) ↦ e
| ProjLE v1 v2 : e_proj L ⟨v1, v2⟩ ↦ v1
| ProjRE v1 v2 : e_proj R ⟨v1, v2⟩ ↦ v2
| CaseLE v e1 e2 : e_case (v_inj L v) e1 e2 ↦ subst (Inc := inc) e1 v
| CaseRE v e1 e2 : e_case (v_inj R v) e1 e2 ↦ subst (Inc := inc) e2 v
| UnpackE v e : e_unpack (v_pack v) e ↦ subst (Inc := inc) e v
| UnrollE v : e_unroll (v_roll v) ↦ v
| WithE v e : e_lwith ⟨v⟩ᶜ e ↦ subst (Inc := inc) e v
| BindE e' (v : value ∅) : v >>= e' ↦ subst (Inc := inc) e' v
| BindE' e e' e'' : e' ↦ e'' -> e_bind e' e ↦ e_bind e'' e
where "e ↦ e'" := (head_step e%syn e'%syn).

Definition step := clos_refl_trans_1n (expr ∅) head_step.

Notation "e ↦* e'" := (step e%syn e'%syn) (at level 70).

Definition safe (e : expr ∅) :=
  forall e', e ↦* e' -> (∃ v, e' = e_val v) \/ (exists e'', e' ↦ e'').

Inductive nsteps : nat -> expr ∅ -> expr ∅ -> Prop :=
| nsteps_step ρ :
  nsteps 0 ρ ρ
| nsteps_l n ρ1 ρ2 ρ3 :
  head_step ρ1 ρ2 ->
  nsteps n ρ2 ρ3 →
  nsteps (S n) ρ1 ρ3.
