Inductive Fin: nat -> Type :=
| fzero {n}: Fin (S n)
| fsucc {n}: Fin n -> Fin (S n).

Inductive Term (L: Type) (n: nat) : Type :=
| 𝓤: L -> Term L n
| Π: Term L n -> Term L (S n) -> Term L n
| var: Fin n -> Term L n
| lam: Term L n -> Term L (S n) -> Term L n
| app: Term L n -> Term L n -> Term L n.
Arguments 𝓤 [_] [_] _.
Arguments Π [_] [_] _ _.
Arguments var [_] [_] _.
Arguments lam [_] [_] _ _.
Arguments app [_] [_] _ _.
Notation "[ T ] t" := (lam T t) (at level 30).
Infix "$" := app (at level 40, left associativity).

Definition fin_match {A: Type} {n} (z: A)
  (s: Fin n -> A) (x: Fin (S n)) : A :=
match x with
| fzero => fun _ => z
| @fsucc n' x => fun eq: n' = n =>
    s (eq_rect _ Fin x _ eq)
end eq_refl.

Definition weak {m n} (f: Fin m -> Fin n):
  Fin (S m) -> Fin (S n) :=
fin_match fzero (fun x => fsucc (f x)).

Fixpoint rename {L m n} (f: Fin m -> Fin n)
  (t: Term L m): Term L n :=
match t with
| 𝓤 ℓ => 𝓤 ℓ
| Π T U => Π (rename f T) (rename (weak f) U)
| var x => var (f x)
| [ T ] t => [ rename f T ] rename (weak f) t
| g $ t => rename f g $ rename f t
end.

Definition shift {L n} (t: Term L n) : Term L (S n) :=
  rename (fun x => fsucc x) t.

Definition transpose {L m n} (f: Fin m -> Term L n):
  Fin (S m) -> Term L (S n) :=
fin_match (var fzero) (fun x => shift (f x)).

Fixpoint replace {L m n} (f: Fin m -> Term L n)
  (t: Term L m) : Term L n :=
match t with
| 𝓤 ℓ => 𝓤 ℓ
| Π T U => Π (replace f T) (replace (transpose f) U)
| var x => f x
| [ T ] t => [ replace f T ] replace (transpose f) t
| g $ t => replace f g $ replace f t
end.

Definition subst {L n}
  (f: Term L (S n)) (t: Term L n): Term L n :=
replace (fin_match t (fun x => var x)) f.
Infix "◁" := subst (at level 45, left associativity).
