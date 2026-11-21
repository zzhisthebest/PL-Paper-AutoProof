Require Import Metalib.Metatheory.

Require Import target_inf.

Definition relation := exp -> exp -> Prop.

Section Star.

Variable R : relation.

Inductive star: relation :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Definition irred a : Prop := forall b, ~(R a b).

End Star.

Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).

Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).

Notation "e ^ x"        := (open_exp_wrt_exp e (trm_var_f x)).

Notation "c |= T1 ~> T2" := (cotyp c T1 T2) (at level 69).

Notation "E |= t ~: T" := (typing E t T) (at level 69).

Notation "R 'star'" := (star R) (at level 69).

Notation "t ->* t'" := (step star t t') (at level 68).

Notation "'|' A '|'" := (ptyp2styp A) (at level 60).

Notation "'∥' Γ '∥'" := (map ptyp2styp Γ) (at level 60).

Notation "A ≺: B ⇝ co " := (sub A B co) (at level 45).

Notation "Γ ⊢ E ⇒ A ⇝ t" := (has_type Γ E Inf A t) (at level 45).

Notation "Γ ⊢ E ⇐ A ⇝ t" := (has_type Γ E Chk A t) (at level 45).

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * exp).
