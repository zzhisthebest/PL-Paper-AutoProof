Set Implicit Arguments.

Require Import Psatz Logic List Classes.Morphisms.

Import List Notations.

Parameter E : Type.

Parameter ϵ : E.

Parameter tick : E.

Parameter add : E -> E -> E.

Notation "ϕ1 'E+' ϕ2" := (add ϕ1 ϕ2) (at level 60).

Parameter eff_idL : forall {ϕ}, ϵ E+ ϕ = ϕ.

Parameter eff_idR : forall {ϕ}, ϕ E+ ϵ = ϕ.

Parameter eff_assoc : forall {ϕ1 ϕ2 ϕ3}, (ϕ1 E+ ϕ2) E+ ϕ3 = ϕ1 E+ (ϕ2 E+ ϕ3).

Inductive subeff : E -> E -> Prop :=
  | subeff_refl ϕ : subeff ϕ ϕ
  | subeff_trans ϕ1 ϕ2 ϕ3 :
    subeff ϕ1 ϕ2 -> subeff ϕ2 ϕ3 -> subeff ϕ1 ϕ3
  | subeff_add_right_compatible ϕ1 ϕ2 ϕ :
    subeff ϕ1 ϕ2 -> subeff (ϕ1 E+ ϕ) (ϕ2 E+ ϕ)
  | subeff_add_left_compatible ϕ1 ϕ2 ϕ :
    subeff ϕ1 ϕ2 -> subeff (ϕ E+ ϕ1) (ϕ E+ ϕ2).

Notation "ϕ1 'E<=' ϕ2" := (subeff ϕ1 ϕ2) (at level 70).
