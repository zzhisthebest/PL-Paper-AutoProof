From TLC Require Import LibList LibFset LibLN.

Require Import DeclDef.

Require Import HM.

Inductive h2d_desugar : htrm -> dtrm -> Prop :=
  | h2d_desugar_var : forall x,
      h2d_desugar (htrm_fvar x) (dtrm_fvar x)
  | h2d_desugar_nat : forall i,
      h2d_desugar (htrm_nat i) (dtrm_nat i)
  | h2d_desugar_abs : forall L e1 s1,
      (forall x, x \notin L ->
            h2d_desugar (e1 hopen_ee_var x) (s1 dopen_ee_var x)) ->
      h2d_desugar (htrm_abs e1) (dtrm_abs s1)
  | h2d_desugar_app : forall s1 s2 e1 e2,
      h2d_desugar e2 s2 ->
      h2d_desugar e1 s1 ->
      h2d_desugar (htrm_app e2 e1) (dtrm_app s2 s1)
  | h2d_desugar_let : forall L e1 e2 s1 s2,
      h2d_desugar e1 s1 ->
      (forall x, x \notin L ->
            h2d_desugar (e2 hopen_ee_var x) (s2 dopen_ee_var x)) ->
      h2d_desugar (htrm_let e1 e2) (dtrm_app (dtrm_abs s2) s1).

Theorem hm_preserve: forall E e t s,
    htyping E e t ->
    h2d_desugar e s ->
    exists T, dtyping E nil s T /\ dsub plain T t.
