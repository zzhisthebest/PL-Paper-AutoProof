From Stdlib Require Import Utf8.
Require Import Common.Metatheory.

Inductive typ : Set :=
| typ_nat   : typ
| typ_arrow : typ → typ_eff → typ
with typ_eff : Set :=
| typ_pure : typ → typ_eff
| typ_cons : typ → typ_eff → typ_eff → typ_eff
.


Notation "'ℕ'" := typ_nat.
Notation "A ↦ B" := (typ_arrow A B) (at level 38, right associativity).
Notation "( A )ε" := (typ_pure A).
Notation "A ![ B ] C" := (typ_cons A B C) (at level 38, right associativity).

Definition env (V : Set) : Set := V → typ.

Definition empty_env : env empty := of_empty.
Notation "'ø'" := empty_env.

Definition extend {V : Set} (Γ : env V) (τ : typ) : env (inc V) :=
  fun x =>
  match x with
  | VZ   => τ
  | VS y => Γ y
  end.

Notation "G / T" := (@extend _ G T) (at level 40, left associativity).
