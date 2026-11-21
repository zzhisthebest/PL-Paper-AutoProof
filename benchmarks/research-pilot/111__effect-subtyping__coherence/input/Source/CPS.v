From Stdlib Require Import Utf8.
Require Import Common.Metatheory Common.Types.
Require Import Source.Typing.
Require Import Target.Syntax.
Require Source.Syntax.

Reserved Notation "S⟦ D ⟧".
Reserved Notation "C⟦ D ⟧".

Fixpoint trans_sub {T U : typ_eff} (D : T ≺: U) : crc :=
  match D with
  | S_Refl _                    => crc_id
  | S_Trans _ _ _ D₁ D₂         => crc_comp S⟦ D₁ ⟧ S⟦ D₂ ⟧
  | S_Arrow _ _ _ _ D₁ D₂       => crc_arrow S⟦ D₁ ⟧ S⟦ D₂ ⟧
  | S_Lift _ _ _ D              => crc_lift S⟦ D ⟧
  | S_Cons _ _ _ _ _ _ D₁ D₂ D₃ => crc_cons S⟦ D₁ ⟧ S⟦ D₂ ⟧ S⟦ D₃ ⟧
  end
where "S⟦ D ⟧" := (@trans_sub _ _ D).

Definition cps_app {V : Set} (e₁ e₂ : exp V) :=
  exp_abs (
    exp_app (weaken e₁) (exp_abs (
    exp_app (weaken (weaken e₂)) (exp_abs (
      exp_app (exp_app (exp_var (VS VZ)) (exp_var VZ))
        (exp_var (VS (VS VZ)))))))).
(* cps_pure_dollar e₁ e₂
   can be defined as (exp_app e₂ e₁), but expression e₁ should be evaluated
   first *)
Definition cps_pure_dollar {V : Set} (e₁ e₂ : exp V) :=
  exp_app (exp_abs (exp_app (weaken e₂) (exp_var VZ))) e₁.
Definition cps_dollar {V : Set} (e₁ e₂ : exp V) :=
  exp_abs (
    exp_app (weaken e₁) (exp_abs (
    exp_app (exp_app (weaken (weaken e₂)) (exp_var VZ)) (exp_var (VS VZ))))).
Definition cps_succ {V : Set} (e : exp V) :=
  exp_abs (exp_app (weaken e) (exp_abs (
    exp_app (exp_var (VS VZ)) (exp_succ (exp_var VZ))))).
Definition cps_case {V : Set} (e e₁ : exp V) (e₂ : exp (inc V)) :=
  exp_abs (exp_app (weaken e) (exp_abs (
    exp_case (exp_var VZ)
      (exp_app (weaken (weaken e₁)) (exp_var (VS VZ)))
      (exp_app (weaken1 (weaken1 e₂)) (exp_var (VS (VS VZ))))
  ))).

Fixpoint cps {V : Set}
    {Γ : env V} {e : Source.Syntax.exp V} {T : typ_eff}
    (D : Γ ⊢ e ∷ T) : exp V :=
  match D with
  | T_Var   x                     => exp_var x
  | T_Const m                     => exp_const m
  | T_Abs D                 => exp_abs C⟦ D ⟧
  | T_PApp D₁ D₂          => exp_app C⟦ D₁ ⟧ C⟦ D₂ ⟧
  | T_App D₁ D₂   => cps_app C⟦ D₁ ⟧ C⟦ D₂ ⟧
  | T_Sft D               => exp_abs C⟦ D ⟧
  | T_Rst D                 => exp_app C⟦ D ⟧ (exp_abs (exp_var VZ))
  | T_PDol D₁ D₂        => cps_pure_dollar C⟦ D₁ ⟧ C⟦ D₂ ⟧
  | T_Dol D₁ D₂   => cps_dollar C⟦ D₁ ⟧ C⟦ D₂ ⟧
  | T_Fix D                 => exp_fix C⟦ D ⟧
  | T_PSucc D                   => exp_succ C⟦ D ⟧
  | T_Succ D                => cps_succ C⟦ D ⟧
  | T_PCase D₁ D₂ D₃      => exp_case C⟦ D₁ ⟧ C⟦ D₂ ⟧ C⟦ D₃ ⟧
  | T_Case D₁ D₂ D₃ => cps_case C⟦ D₁ ⟧ C⟦ D₂ ⟧ C⟦ D₃ ⟧
  | T_Sub D₁ D₂             => exp_capp S⟦ D₂ ⟧ C⟦ D₁ ⟧
  end
where "C⟦ D ⟧" := (@cps _ _ _ _ D).
