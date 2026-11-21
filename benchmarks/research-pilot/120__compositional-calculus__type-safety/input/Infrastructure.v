Require Import Coq.micromega.Lia.

Require Export rules_inf.

Notation "A & B"         := (t_and A B) (at level 66).

Notation "[ z ~~> u ] t" := (typsubst_typ u z t) (at level 0).

Notation "t ^-^ u"       := (open_typ_wrt_typ t u) (at level 67).

Notation "t -^ x"        := (open_typ_wrt_typ t (t_tvar_f x))(at level 67).

Notation "[[ A ]]"       := (typefv_typ A) (A at level 99).

Fixpoint typefv_typ_range (E : list (atom*typ))
  : atoms :=
  match E with
    | nil => empty
    | (_, A) :: E' => [[A]] \u (typefv_typ_range E')
  end.

Definition relation (X:Type) := X -> X -> Prop.

Section Star.

Variable A : Type.

Variable R : relation A.

Inductive star: relation A:=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Definition irred a : Prop := forall b, ~(R a b).

End Star.

Notation "Γ ⊢ E ⇒ A" := (Typing Γ E Inf A) (at level 45).

Notation "Γ ⊢ E ⇐ A" := (Typing Γ E Chk A) (at level 45).

Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).

Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).

Notation "e ^ x"        := (open_exp_wrt_exp e (e_var_f x)).

Notation "v ~-> A v'" := (casting v A v') (at level 68).

Notation "R 'star'" := (star exp R) (at level 69).

Notation "t ->* t'" := (step star t t') (at level 68).

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * exp).
