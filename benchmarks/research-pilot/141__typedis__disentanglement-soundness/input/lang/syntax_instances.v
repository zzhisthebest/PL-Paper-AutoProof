From stdpp Require Import base countable strings list binders gmap.

From dislog Require Import syntax.

Global Instance bool_op_eq_dec : EqDecision bool_op := ltac:(solve_decision).
Global Instance int_op_eq_dec : EqDecision int_op := ltac:(solve_decision).
Global Instance int_cmp_eq_dec : EqDecision int_cmp := ltac:(solve_decision).
Global Instance PrimEq_dec : EqDecision prim := ltac:(solve_decision).

Fixpoint eq_val (x y : val) {struct x} : {x = y} + {x ≠ y} :=
  ltac:(decide equality; [apply bool_eq_dec | apply Z.eq_dec | apply loc_eq_dec])
with eq_expr (x y : expr) {struct x} : {x = y} + {x ≠ y} :=
  ltac:(decide equality;
    [ apply String.string_dec
    | unshelve eapply (list_eq_dec l l0); intros ? ?; unfold Decision; apply eq_expr
    | apply PrimEq_dec | apply binder_dec_eq | apply binder_dec_eq | apply binder_dec_eq ])
with eq_func (x y : function) {struct x} : {x = y} + {x ≠ y} :=
  ltac:(decide equality; [apply (list_eq_dec l l0) | apply binder_dec_eq]).

Global Instance val_eq_dec : EqDecision val := eq_val.
Global Instance function_eq_dec : EqDecision function := eq_func.
Global Instance expr_eq_dec : EqDecision expr := eq_expr.
