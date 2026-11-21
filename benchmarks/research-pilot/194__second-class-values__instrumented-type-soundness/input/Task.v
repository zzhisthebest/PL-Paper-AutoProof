Require Export Arith.EqNat.

From Stdlib Require Export PeanoNat.

Require Export stlc1.

Inductive wf_env : venv -> tenv -> Prop :=
| wfe_nil : forall n, wf_env (@Def vl nil nil n) (@Def ty nil nil n)
| wfe_cons : forall v t vs ts n,
    val_type (expand_env vs v n) v t ->
    wf_env vs ts ->
    get_inv_idx vs = get_inv_idx ts ->
    wf_env (expand_env vs v n) (expand_env ts t n)

with val_type : venv -> vl -> ty -> Prop :=
| v_bool: forall venv b,
    val_type venv (vbool b) TBool
| v_abs: forall env venv tenv y T1 T2 m retcl,
    wf_env venv tenv ->
    has_type (expand_env (expand_env tenv (TFun T1 m T2 retcl) Second) T1 m) y retcl T2 ->
    val_type env (vabs venv m y retcl) (TFun T1 m T2 retcl).

Inductive stp: venv -> ty -> venv -> ty -> Prop :=
| stp_refl: forall G1 G2 T,
   stp G1 T G2 T.

Inductive res_type: venv -> option vl -> ty -> Prop :=
| not_stuck: forall venv v T,
      val_type venv v T ->
      res_type venv (Some v) T.

Theorem full_safety : forall k e n tenv venv res T,
  teval k venv e n = Some res -> has_type tenv e n T -> wf_env venv tenv ->
  res_type venv res T.
