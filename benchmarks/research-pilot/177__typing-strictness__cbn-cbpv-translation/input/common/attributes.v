Require Export strictness.common.fin_util.

From Stdlib Require Import Arith.

From Stdlib Require Export PeanoNat.

Inductive attr : Type :=
    | Lazy
    | Strict
    | Unknown.

Definition attr_le (c1 c2 : attr) :=
    match c1, c2 with
    | Unknown, _ => True
    | Lazy, Lazy => True
    | Strict, Strict => True
    | _, _ => False
    end.

Notation "c1 C<= c2" := (attr_le c1 c2) (at level 60).

Definition attr_stricter (c1 c2 : attr) :=
    match c1, c2 with
    | Strict, _ => True
    | Unknown, _ => True
    | _, Lazy => True
    | _, _ => False
    end.

Notation "c1 'S<=' c2" := (attr_stricter c1 c2) (at level 60).

Definition attr_add (c1 c2 : attr) : attr :=
    match c1, c2 with
    | Lazy, c2 => c2
    | c1, Lazy => c1
    | _, Strict => Strict
    | Strict, _ => Strict
    | _, _ => Unknown
    end.

Notation "c C+ d" := (attr_add c d) (at level 60).

Definition attrs n : Type := fin n -> attr.

Definition ren_env {A n n'} (γ : fin n -> A) (ξ : fin n' -> fin n) : fin n' -> A :=
    fun fn => γ (ξ fn).

Definition lazyvector {n} : attrs n := fun _ => Lazy.

Definition strictvector {n} : attrs n := fun _ => Strict.

Definition attr_vector_add {n} (γ1 γ2 : attrs n) : attrs n :=
    fun fn => γ1 fn C+ γ2 fn.

Notation "c γ+ d" := (attr_vector_add c d) (at level 60).

Definition attr_vector_le {n} (γ1 γ2 : attrs n) : Prop := forall fn,
    γ1 fn C<= γ2 fn.

Notation "γ1 γ<= γ2" := (attr_vector_le γ1 γ2) (at level 50).

Definition attr_vector_stricter {n} (γ1 γ2 : attrs n) : Prop := forall fn,
    γ1 fn S<= γ2 fn.

Notation "γ1 γS<= γ2" := (attr_vector_stricter γ1 γ2) (at level 50).

Definition down_attrs {n} (γ : attrs (S n)) : attrs n := ren_env γ shift.

Notation "'γ↓' γ" := (down_attrs γ) (at level 85).

Definition env_set {n} {A : Type} (ϕ : fin n -> A) (i : fin n) (a : A) :=
    fun fn => if fin_eqb i fn then a else ϕ fn.

Notation "ϕ <- a @ i " := (env_set ϕ i a) (at level 70).

Definition down_env_until' {A m} k (γ : fin (k + m) -> A) : fin m -> A :=
    ren_env γ (shift_p k).

Definition up_fin_until {n} m (H : n <= m) : ren n m :=
  fun i => eq_rect _ fin (shift_p (m - n) i) _ (Nat.sub_add n m H).

Definition down_env_until {A n} (γ : fin n -> A) m (H : m <= n) : fin m -> A :=
  fun i => γ (up_fin_until n H i).
