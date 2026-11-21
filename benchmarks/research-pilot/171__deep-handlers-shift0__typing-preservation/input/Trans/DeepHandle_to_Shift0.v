Require Import Utf8.

Require Import Binding.Lib.

Require Lang.DeepHandle.

Require Lang.Shift0.

Module S := Lang.DeepHandle.

Module T := Lang.Shift0.

Import T.

Fixpoint tr_expr {V : Set} (e : S.expr V) : T.expr V :=
  match e with
  | S.e_value v     => tr_value v
  | S.e_app   e₁ e₂ => tr_expr e₁ @ tr_expr e₂
  | S.e_do    v     =>

    e_sft0 ([λ] #VZ @ shift (Inc:=inc) (shift (Inc:=inc) (tr_value v : T.expr V)) @ ([λ] #(VS (VS VZ)) @ #VZ @ #(VS VZ)))
  | S.e_handle e h =>

    ⟨ ([λ] [λ] #(VS VZ)) @ tr_expr e ⟩ @ ([λ] [λ] tr_expr h)
  | S.e_handle_ret e h r =>

    ⟨tr_expr e ∣ [λ] shift (Inc:=inc) (tr_expr r)⟩ @ ([λ] [λ] tr_expr h)
  | S.e_lift e => (tr_expr e)⇑
  end%exp
with tr_value {V : Set} (v : S.value V) : T.value V :=
  match v with
  | S.v_var x => #x
  | S.v_lam e => [λ] tr_expr e
  end%exp.

Fixpoint tr_ectx {V : Set} (X : S.ectx V) : T.ectx V :=
  match X with
  | S.x_hole     => x_hole
  | S.x_app1 X e => x_app1 (tr_ectx X) (tr_expr e)
  | S.x_app2 v X => x_app2 (tr_value v) (tr_ectx X)
  | S.x_handle X h =>

    x_app1 (x_rst (x_app2 ([λ] [λ] #(VS VZ)) (tr_ectx X))) ([λ] [λ] tr_expr h)
  | S.x_handle_ret X h r =>

    x_app1 (x_rst_ret (tr_ectx X) ([λ] shift (Inc:=inc) (tr_expr r))) ([λ] [λ] (tr_expr h))
  | S.x_lift X => x_lift (tr_ectx X)
  end%exp.
