Require Export axioms.

Set Implicit Arguments.

Unset Strict Implicit.

Definition ap {X Y} (f : X -> Y) {x y : X} (p : x = y) : f x = f y :=
  match p with eq_refl => eq_refl end.

Definition apc {X Y} {f g : X -> Y} {x y : X} (p : f = g) (q : x = y) : f x = g y :=
  match q with eq_refl => match p with eq_refl => eq_refl end end.

Fixpoint fin (n : nat) : Type :=
  match n with
  | 0 => False
  | S m => option (fin m)
  end.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

Class Subst1 (X : nat -> Type) (Y : nat -> Type) :=
  subst1 : forall {m n}, (fin m -> X n) -> Y m -> Y n.

Class Ren1 (X : nat -> Type) :=
  ren1 : forall {m n}, (fin m -> fin n) -> X m -> X n.

Class Subst2 (X1 X2 : nat -> Type) (Y : nat -> nat -> Type) :=
  subst2 : forall {m1 m2 n1 n2}, (fin m1 -> X1 n1) -> (fin m2 -> X2 n2) -> Y m1 m2 -> Y n1 n2.

Class Ren2 (X : nat -> Type) :=
  ren2 : forall {m n}, (fin m -> fin n) -> X m -> X n.

Notation "s [ sigma ]" := (@subst1 _ _ _ _ _ sigma s) (at level 7, left associativity, format "s '/' [ sigma ]") : subst_scope.

Notation "s [ sigma ; tau ]" := (subst1  sigma tau s) (at level 7, left associativity, format "s '/' [ sigma ; '/'  tau ]") : subst_scope.

Notation "s ⟨ sigma ⟩" := (@ren1 _ _ _ _ sigma s) (at level 7, left associativity, format "s '/' ⟨ sigma ⟩") : subst_scope.

Notation "[ sigma ]" := (@subst1 _ _ _ _ _ sigma) (at level 1, left associativity) : fscope.

Notation "⟨ xi ⟩" := (@ren1 _ _ _ _ xi) (at level 1, left associativity, format "⟨ xi ⟩") : fscope.

Arguments funcomp {X Y Z} (g)%fscope (f)%fscope.

Notation "f >> g" := (funcomp g f)   (at level 50).

Open Scope subst_scope.

Definition scons {X : Type} {n : nat} (x : X) (f : fin n -> X) (m : fin (S n)) : X :=
  match m with
  | None => x
  | Some i => f i
  end.

Notation "x .: f" := (@scons _ _ x f) (at level 55) : subst_scope.

Definition ren (m n : nat) : Type := fin m -> fin n.

Definition bound {n : nat} : fin (S n) := None.

Definition null {T} (i : fin 0) : T := match i with end.

Definition shift {n : nat} : ren n (S n) :=
  Some.

Definition up_ren m n (xi : ren m n) : ren (S m) (S n) :=
  bound .: xi >> shift.

Definition var_zero {n : nat} : fin (S n) := None.

Definition idren {k: nat} : ren k k :=
  fun x => x.

Definition comp := @funcomp.

Definition id {X} (x : X) := x.

Class Var (X : nat -> Type) :=
  ids : forall {m}, fin m -> X m.

Module CommaNotation.

Notation "s , sigma" := (scons s sigma) (at level 60, format "s ,  sigma", right associativity) : subst_scope.

End CommaNotation.

Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.

Notation "↑" := (shift) : subst_scope.
