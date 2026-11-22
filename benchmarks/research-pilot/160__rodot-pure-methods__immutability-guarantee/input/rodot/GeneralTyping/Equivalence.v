Set Implicit Arguments.

Require Import LibExtra SyntaxClasses.

Require Import AbstractSyntax.

Class TypingEquiv (A : Set) := typing_equiv : renv -> A -> A -> Prop.

Notation "e ⊢ a '≈' b" := (typing_equiv e a b) (at level 40, a at level 59).

Inductive tyq_var: TypingEquiv var :=
| tyq_var_refl(e: renv)(v: var):
  typing_equiv e v v
| tyq_var_binds(e: renv)(v1 v2: var):
  renv_binds v1 v2 e ->
  typing_equiv e v1 v2
| tyq_var_sym(e: renv)(v1 v2: var):
  typing_equiv e v1 v2 ->
  typing_equiv e v2 v1
| tyq_var_trans(e: renv)(v1 v2 v3: var):
  typing_equiv e v1 v2 ->
  typing_equiv e v2 v3 ->
  typing_equiv e v1 v3
.

Existing Instance tyq_var.

Inductive tyq_typ: TypingEquiv typ :=
| tyq_typ_nulary(e: renv) T:
  typ_nulary T ->
    typing_equiv e T T
| tyq_typ_andor T (e: renv) t11 t12 t21 t22:
  typ_andor T ->
    typing_equiv e t11 t21 ->
    typing_equiv e t12 t22 ->
    typing_equiv e (T t11 t12) (T t21 t22)
| tyq_typ_fun (e: renv) t11 t12 t21 t22:
    typing_equiv e t11 t21 ->
    (forall x, typing_equiv e (open x t12) (open x t22)) ->
    typing_equiv e (typ_fun t11 t12) (typ_fun t21 t22)
| tyq_typ_fld (e: renv) a t11 t12 t21 t22:
    typing_equiv e t11 t21 ->
    typing_equiv e t12 t22 ->
    typing_equiv e (typ_rcd (dec_fld a t11 t12)) (typ_rcd (dec_fld a t21 t22))
| tyq_typ_typ (e: renv) B t11 t12 t21 t22:
    (forall x, typing_equiv e (open x t11) (open x t21)) ->
    (forall x, typing_equiv e (open x t12) (open x t22)) ->
    typing_equiv e (typ_rcd (dec_typ B t11 t12)) (typ_rcd (dec_typ B t21 t22))
| tyq_typ_sel_normal(e: renv)(v1 v2: var) (v3: avar)(l: typ_normal_label):
    typing_equiv e v1 v2 ->
    typing_equiv e (typ_sel (avar_f v1) (typ_label_normal l) v3) (typ_sel (avar_f v2) (typ_label_normal l) v3)
| tyq_typ_sel(e: renv)(v1 v2: avar)(l: typ_label):
    typing_equiv e (typ_sel v1 l v2) (typ_sel v1 l v2)
| tyq_typ_bnd(e: renv)(t1 t2: typ):
    (forall x, typing_equiv e (open x t1) (open x t2)) ->
    typing_equiv e (typ_bnd t1) (typ_bnd t2)
| tyq_typ_met m (e: renv) t11 t12 t13 t21 t22 t23:
    (forall x, typing_equiv e (open x t11) (open x t21)) ->
    typing_equiv e t12 t22 ->
    (forall x y, typing_equiv e (open_met x y t13) (open_met x y t23)) ->
    typing_equiv e (typ_rcd (dec_met m t11 t12 t13)) (typ_rcd (dec_met m t21 t22 t23))
.

Existing Instance tyq_typ.

Inductive tyq_var_alt: renv -> var -> var -> Prop :=
| tyq_var_alt_eq e v:
    tyq_var_alt e v v
| tyq_var_alt_wy e w y:
    binds w y e ->
    tyq_var_alt e w y
| tyq_var_alt_yw e w y:
    binds w y e ->
    tyq_var_alt e y w
| tyq_var_alt_ww e w1 w2 y:
    binds w1 y e ->
    binds w2 y e ->
    tyq_var_alt e w1 w2.
