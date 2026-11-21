Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Import subtyping.AmberLocal.

Require Import subtyping.AmberSoundness.

Require Import subtyping.AmberCompleteness.

Require Export rules_inf.

Require Export LibTactics.

Require Import Lia.

Fixpoint trans_ty (A : typ) : Rules.typ :=
  match A with
  | t_top => typ_top
  | t_int => typ_nat
  | t_arrow A1 A2 =>
      typ_arrow (trans_ty A1) (trans_ty A2)
  | t_var_f X => typ_fvar X
  | t_var_b n => typ_bvar n
  | t_mu A => typ_mu (trans_ty A)
  end.

Fixpoint back_ty (A : Rules.typ) : typ :=
  match A with
  | typ_top => t_top
  | typ_nat => t_int
  | typ_arrow A1 A2 =>
      t_arrow (back_ty A1) (back_ty A2)
  | typ_fvar X => t_var_f X
  | typ_bvar n => t_var_b n
  | typ_mu A => t_mu (back_ty A)
  end.

Fixpoint env_to_tctx (D: env) : tctx :=
  match D with
  | nil => nil
  | (X, bind_sub) :: D' => (X, tt) :: env_to_tctx D'
  | (X, bind_typ _) :: D' =>  (X, tt) :: env_to_tctx D'
  end.

Fixpoint tctx_to_env (D: tctx) : env :=
  match D with
  | nil => nil
  | (X, tt) :: D' => (X, bind_sub) :: tctx_to_env D'
  end.
