From Stdlib Require Import List CRelationClasses.
Import ListNotations.

Set Implicit Arguments.

Notation "l · a" := (l ++ a :: nil) (at level 56, left associativity) : list_scope.
Infix "<=>" := iffT (at level 95, no associativity).

Fixpoint InT {A : Type} (a : A) (l : list A) : Type :=
  match l with
  | nil => False
  | b :: m => sum (b = a) (InT a m)
  end.

Definition Atom : Type := nat.

Inductive form := var (_ : Atom) | omega | inter (_ _ : form) | arrow (_ _ : form).

Notation Ω := omega.
Infix "∩" := inter (at level 35).
Infix "→" := arrow (right associativity, at level 39).

Reserved Notation "a ≤ b" (at level 70).

Inductive bcd_sub {lax : list (Atom -> form * form)} : crelation form :=
| bcd_identity a : a ≤ a
| bcd_trans a b c : a ≤ b -> b ≤ c -> a ≤ c
| bcd_omega_right a : a ≤ Ω
| bcd_inter_left1 a b : a ∩ b ≤ a
| bcd_inter_left2 a b : a ∩ b ≤ b
| bcd_inter_right a : a ≤ a ∩ a
| bcd_inter a b c d : a ≤ c -> b ≤ d -> a ∩ b ≤ c ∩ d
| bcd_arrow a b c d : c ≤ a -> b ≤ d -> a → b ≤ c → d
| bcd_arrow_inter a b c : (a → b) ∩ (a → c) ≤ a → b ∩ c
| bcd_arrow_omega : Ω ≤ Ω → Ω
| bcd_axiom ax x : InT ax lax -> fst (ax x) ≤ snd (ax x)
where "a ≤ b" := (bcd_sub a b).

Reserved Notation "a ❘ l ⊦ b" (at level 65, l at next level, b at next level).
Reserved Notation "a ❘ ⊦ b" (at level 65, b at next level).

Inductive sub : list form -> crelation form :=
| identity a : a ❘ ⊦ a
| omega_right a l : a ❘ l ⊦ Ω
| inter_left1 b a c l : a ❘ l ⊦ c -> a ∩ b ❘ l ⊦ c
| inter_left2 b a c l : a ❘ l ⊦ c -> b ∩ a ❘ l ⊦ c
| inter_right a b c l : c ❘ l ⊦ a -> c ❘ l ⊦ b -> c ❘ l ⊦ a ∩ b
| arrow_left a b c d l : c ❘ ⊦ a -> b ❘ l ⊦ d -> a → b ❘ c :: l ⊦ d
| arrow_right a b c l : c ❘ l · a ⊦ b -> c ❘ l ⊦ a → b
where "a ❘ l ⊦ b" := (sub l a b)
  and "a ❘ ⊦ b" := (sub nil a b).

Notation "a ⩽ b " := (@bcd_sub [] a b) (at level 70).

Theorem is_bcd_equiv a b : a ⩽ b <=> a ❘ ⊦ b.
