Require Import Poulet4.P4cub.Syntax.CubNotations.

From Stdlib Require Import ZArith.

From Poulet4.P4cub.Semantics.Dynamic.BigStep Require Import Value.Syntax ExprUtil.

Reserved Notation "⟨ ϵ , e ⟩ ⇓ v"
         (at level 80, no associativity).

Local Open Scope val_scope.

Local Open Scope exp_scope.

Inductive exp_big_step (ϵ : list Val.t)
  : Exp.t -> Val.t -> Prop :=
| ebs_bool (b : bool) :
  ⟨ ϵ, Exp.Bool b ⟩ ⇓ Val.Bool b
| ebs_bit w n :
  ⟨ ϵ, w `W n ⟩ ⇓ w VW n
| ebs_int w z :
  ⟨ ϵ, w `S z ⟩ ⇓ w VS z
| ebs_varbit m w n :
  ⟨ ϵ, Exp.VarBit m w n ⟩ ⇓ Val.VarBit m w n
| ebs_var τ og x v :
  nth_error ϵ x = Some v ->
  ⟨ ϵ, Exp.Var τ og x ⟩ ⇓ v
| ebs_slice e hi lo v v' :
  slice_val hi lo v = Some v' ->
  ⟨ ϵ, e ⟩ ⇓ v ->
  ⟨ ϵ, Exp.Slice hi lo e ⟩ ⇓ v'
| ebs_cast τ e v v' :
  eval_cast τ v = Some v' ->
  ⟨ ϵ, e ⟩ ⇓ v ->
  ⟨ ϵ, Exp.Cast τ e ⟩ ⇓ v'
| ebs_error err :
  ⟨ ϵ, Exp.Error err ⟩ ⇓ Val.Error err
| ebs_uop τ op e v v' :
  eval_una op v = Some v' ->
  ⟨ ϵ, e ⟩ ⇓ v ->
  ⟨ ϵ, Exp.Uop τ op e ⟩ ⇓ v'
| ebs_bop τ op e₁ e₂ v v₁ v₂ :
  eval_bin op v₁ v₂ = Some v ->
  ⟨ ϵ, e₁ ⟩ ⇓ v₁ ->
  ⟨ ϵ, e₂ ⟩ ⇓ v₂ ->
  ⟨ ϵ, Exp.Bop τ op e₁ e₂ ⟩ ⇓ v
| ebs_member τ x e ls vs v :
  nth_error vs x = Some v ->
  ⟨ ϵ, e ⟩ ⇓ Val.Lists ls vs ->
  ⟨ ϵ, Exp.Member τ x e ⟩ ⇓ v
| ebs_index τ e₁ e₂ ls vs w n v :
  nth_error vs (Z.to_nat n) = Some v ->
  ⟨ ϵ, e₁ ⟩ ⇓ Val.Lists ls vs ->
  ⟨ ϵ, e₂ ⟩ ⇓ w VW n ->
  ⟨ ϵ, Exp.Index τ e₁ e₂ ⟩ ⇓ v
| ebs_lists ls es vs :
  Forall2 (exp_big_step ϵ) es vs ->
  ⟨ ϵ, Exp.Lists ls es ⟩ ⇓ Val.Lists ls vs
where "⟨ ϵ , e ⟩ ⇓ v"
  := (exp_big_step ϵ e v) : type_scope.
