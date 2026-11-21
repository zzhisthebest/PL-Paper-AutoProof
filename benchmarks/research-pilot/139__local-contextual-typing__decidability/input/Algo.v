Require Import Syntax.

Inductive sub : Env -> Typ -> Polar -> Typ -> Env -> Prop :=
| s_int : forall Δ p,
    SRegular Δ ->
    sub Δ Int p Int Δ
| s_var_ty : forall Δ p x,
    SRegular Δ ->
    lookupTy Δ x ->
    sub Δ (TVar x) p (TVar x) Δ
| s_ex_l : forall Δ Ψ x A,
    substEnv A x Δ Ψ ->
    sub Δ (TVar x) Pos A Ψ
| s_ex_r : forall Δ Ψ x A,
    substEnv A x Δ Ψ ->
    sub Δ A Neg (TVar x) Ψ
| s_exty_l : forall Δ x A,
    SRegular Δ ->
    lookupExTy Δ x A ->
    sub Δ (TVar x) Pos A Δ
| s_exty_r : forall Δ x A,
    SRegular Δ ->
    lookupExTy Δ x A ->
    sub Δ A Neg (TVar x) Δ
| s_arr : forall Δ Ω Ψ p A B C D,
    sub Ω C (neg p) A Ψ ->
    sub Δ B p D Ω ->
    sub Δ (Arr A B) p (Arr C D) Ψ
| s_all : forall Δ Ψ p A B,
    sub (TyCons Δ) A p B (TyCons Ψ) ->
    sub Δ (All A) p (All B) Ψ.

Inductive grd_typ : Env -> Typ -> Typ -> Prop :=
| grd_int : forall Δ, grd_typ Δ Int Int
| grd_var_exty : forall Δ x A,
    lookupExTy Δ x A ->
    grd_typ Δ (TVar x) A
| grd_var_ty : forall Δ x,
    lookupTy Δ x ->
    grd_typ Δ (TVar x) (TVar x)
| grd_arr : forall Δ A B A' B',
    grd_typ Δ A A' ->
    grd_typ Δ B B' ->
    grd_typ Δ (Arr A B) (Arr A' B')
| grd_all : forall Δ A A',
    grd_typ (TyCons Δ) A A' ->
    grd_typ Δ (All A) (All A').

Fixpoint rm_sep (Γ : Env) : Env :=
  match Γ with
  | EnvEmpty      => EnvEmpty
  | TmCons Γ' A   => TmCons (rm_sep Γ') A
  | ExCons Γ'     => ExCons (rm_sep Γ')
  | TyCons Γ'     => TyCons (rm_sep Γ')
  | ExTyCons Γ' A => ExTyCons (rm_sep Γ') A
  | SepCons Γ'    => rm_sep Γ'
  end.

Inductive ty : Env -> Context -> Trm -> Typ -> Prop :=
| ty_lit : forall Γ n,
    TRegular Γ ->
    ty Γ CtxEmpty (Lit n) Int
| ty_var : forall Γ x A,
    TRegular Γ ->
    lookupTm Γ x A ->
    ty Γ CtxEmpty (Var x) A
| ty_ann : forall Γ e A B,
    ty Γ (CtxTyp A) e B ->
    ty Γ CtxEmpty (Ann e A) A
| ty_app : forall Γ Σ e1 e2 A B,
    ty Γ (CtxTrm e2 Σ) e1 (Arr A B) ->
    ty Γ Σ (App e1 e2) B
| ty_lam1 : forall Γ A B C e,
    ty (TmCons Γ A) (CtxTyp B) e C ->
    ty Γ (CtxTyp (Arr A B)) (Lam e) (Arr A C)
| ty_lam2 : forall Γ Σ A B e e2,
    ty Γ CtxEmpty e2 A ->
    ty (TmCons Γ A) (tm_shift_ctx Σ 0) e B ->
    ty Γ (CtxTrm e2 Σ) (Lam e) (Arr A B)
| ty_sub : forall Γ Σ g A B,
    ty Γ CtxEmpty g A ->
    NonEmpty Σ ->
    GenericConsumer g ->
    sub_ctx (SepCons Γ) A Σ (SepCons Γ) B ->
    ty Γ Σ g B
| ty_tabs : forall Γ e A,
    ty (TyCons Γ) CtxEmpty e A ->
    ty Γ CtxEmpty (TLam e) (All A)
| ty_tapp : forall Γ Σ e A B B',
    ty Γ (CtxTApp A Σ) e (All B) ->
    B' = subst B 0 A ->
    ty Γ Σ (TApp e A) B'
| ty_tabs_ty : forall Γ e A B,
    ty (TyCons Γ) (CtxTyp A) e B ->
    ty Γ (CtxTyp (All A)) (TLam e) (All A)






with
sub_ctx : Env -> Typ -> Context -> Env -> Typ -> Prop :=
| s_empty : forall Δ A A',
    SRegular Δ ->
    close Δ A ->
    grd_typ Δ A A' ->
    sub_ctx Δ A CtxEmpty Δ A'
| s_typ : forall Δ A B Ψ,
    sub Δ A Pos B Ψ ->
    sub_ctx Δ A (CtxTyp B) Ψ B
| s_trm_c : forall Δ A B Σ Ψ e A' A'' D,
    close Ψ A ->
    grd_typ Ψ A A' ->
    ty (rm_sep Ψ) (CtxTyp A') e A'' ->
    sub_ctx Δ B Σ Ψ D ->
    sub_ctx Δ (Arr A B) (CtxTrm e Σ) Ψ (Arr A' D)
| s_trm_o : forall Δ A B e Σ Ψ C D Ω,
    open Ω A ->
    ty (rm_sep Ω) CtxEmpty e C ->
    sub Ω C Neg A Ψ ->
    sub_ctx Δ B Σ Ω D ->
    sub_ctx Δ (Arr A B) (CtxTrm e Σ) Ψ (Arr C D)
| s_alll : forall Δ A e Σ Ψ B C D,
    sub_ctx (ExCons Δ) A (CtxTrm (ty_shift_tm e 0) (ty_shift_ctx Σ 0)) (ExTyCons Ψ B) (Arr (ty_shift C 0) (ty_shift D 0)) ->
    sub_ctx Δ (All A) (CtxTrm e Σ) Ψ (Arr C D)
| s_alll_no : forall Δ A e Σ Ψ C D,
    sub_ctx (ExCons Δ) A (CtxTrm (ty_shift_tm e 0) (ty_shift_ctx Σ 0)) (ExCons Ψ) (Arr (ty_shift C 0) (ty_shift D 0)) ->
    sub_ctx Δ (All A) (CtxTrm e Σ) Ψ (Arr C D)
| s_tapp : forall Δ A B Σ Ψ C,
    sub_ctx (ExTyCons Δ B) A (ty_shift_ctx Σ 0) (ExTyCons Ψ B) C ->
    sub_ctx Δ (All A) (CtxTApp B Σ) Ψ (All C)
| s_svar_trm : forall Δ x e Σ A B C,
    lookupExTy Δ x A ->
    sub_ctx Δ A (CtxTrm e Σ) Δ (Arr B C) ->
    sub_ctx Δ (TVar x) (CtxTrm e Σ) Δ (Arr B C)
| s_svar_tapp : forall Δ x Σ A B C,
    lookupExTy Δ x A ->
    sub_ctx Δ A (CtxTApp B Σ) Δ (All C) ->
    sub_ctx Δ (TVar x) (CtxTApp B Σ) Δ (All C)
| s_evar_infers : forall Δ x e Σ Ψ A,
    infs Δ (CtxTrm e Σ) A ->
    substEnv A x Δ Ψ ->
    sub_ctx Δ (TVar x) (CtxTrm e Σ) Ψ A
with
infs : Env -> Context -> Typ -> Prop :=
| infs_z : forall Γ A,
    TRegular Γ ->
    RegularTyp Γ A ->
    infs Γ (CtxTyp A) A
| infs_s : forall Γ e Σ A B,
    ty Γ CtxEmpty e A ->
    infs Γ Σ B ->
    infs Γ (CtxTrm e Σ) (Arr A B).
