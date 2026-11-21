From Mctt.Core.Syntactic Require Export Syntax.

Reserved Notation "'env'".

Inductive domain : Set :=
| d_univ : nat -> domain
| d_nat : domain
| d_zero : domain
| d_succ : domain -> domain
| d_pi : domain -> env -> exp -> domain
| d_fn : env -> exp -> domain
| d_sigma : domain -> env -> exp -> domain
| d_pair : domain -> domain -> domain
| d_eq : domain -> domain -> domain -> domain
| d_refl : domain -> domain
| d_neut : domain -> domain_ne -> domain
with domain_ne : Set :=




| d_var : forall (x : nat), domain_ne
| d_app : domain_ne -> domain_nf -> domain_ne
| d_fst : domain_ne -> domain_ne
| d_snd : domain_ne -> domain_ne
| d_natrec : env -> typ -> domain -> exp -> domain_ne -> domain_ne
| d_eqrec : env -> domain -> typ -> exp -> domain -> domain -> domain_ne -> domain_ne
with domain_nf : Set :=
| d_dom : domain -> domain -> domain_nf
where "'env'" := (nat -> domain).

Definition empty_env : env := fun x => d_zero.

Arguments empty_env _ /.

Definition extend_env (ρ : env) (d : domain) : env :=
  fun n =>
    match n with
    | 0 => d
    | S n' => ρ n'
    end.

Arguments extend_env _ _ _ /.

Definition drop_env (ρ : env) : env := fun n => ρ (S n).

Arguments drop_env _ _ /.

#[global] Declare Custom Entry domain.

#[global] Bind Scope mctt_scope with domain.

Module Domain_Notations.

Export Syntax_Notations.

Notation "'d{{{' x '}}}'" := x (at level 0, x custom domain at level 99, format "'d{{{'  x  '}}}'") : mctt_scope.

Notation "( x )" := x (in custom domain at level 0, x custom domain at level 60) : mctt_scope.

Notation "'^' x" := x (in custom domain at level 0, x constr at level 0) : mctt_scope.

Notation "x" := x (in custom domain at level 0, x ident) : mctt_scope.

Notation "'𝕌' @ n" := (d_univ n) (in custom domain at level 0, n constr at level 0) : mctt_scope.

Notation "'ℕ'" := d_nat (in custom domain) : mctt_scope.

Notation "'zero'" := d_zero (in custom domain at level 0) : mctt_scope.

Notation "'succ' m" := (d_succ m) (in custom domain at level 30, m custom domain at level 30) : mctt_scope.

Notation "'rec' m 'under' ρ 'return' P | 'zero' -> mz | 'succ' -> MS 'end'" := (d_natrec ρ P mz MS m) (in custom domain at level 0, P custom exp at level 60, mz custom domain at level 60, MS custom exp at level 60, ρ custom domain at level 60, m custom domain at level 60) : mctt_scope.

Notation "'Π' a ρ B" := (d_pi a ρ B) (in custom domain at level 0, a custom domain at level 30, ρ custom domain at level 0, B custom exp at level 30) : mctt_scope.

Notation "'λ' ρ M" := (d_fn ρ M) (in custom domain at level 0, ρ custom domain at level 30, M custom exp at level 30) : mctt_scope.

Notation "f x .. y" := (d_app .. (d_app f x) .. y) (in custom domain at level 40, f custom domain, x custom domain at next level, y custom domain at next level) : mctt_scope.

Notation "'Σ' a ρ B" := (d_sigma a ρ B) (in custom domain at level 0, a custom domain at level 30, ρ custom domain at level 0, B custom exp at level 30) : mctt_scope.

Notation "⟨ a ; b ⟩ " := (d_pair a b) (in custom domain at level 0, a custom domain at level 30, b custom domain at level 30) : mctt_scope.

Notation "'fst' e" := (d_fst e) (in custom domain at level 0, e custom domain at level 30) : mctt_scope.

Notation "'snd' e" := (d_snd e) (in custom domain at level 0, e custom domain at level 30) : mctt_scope.

Notation "'Eq' a m n" := (d_eq a m n) (in custom domain at level 1, a custom domain at level 30, m custom domain at level 35, n custom domain at level 40) : mctt_scope.

Notation "'refl' m" := (d_refl m) (in custom domain at level 1, m custom domain at level 40) : mctt_scope.

Notation "'eqrec' n 'under' ρ 'as' 'Eq' a m1 m2 'return' B | 'refl' -> BR 'end'" := (d_eqrec ρ a B BR m1 m2 n) (in custom domain at level 0, a custom domain at level 30, B custom exp at level 60, BR custom exp at level 60, m1 custom domain at level 35, m2 custom domain at level 40, n custom domain at level 60) : mctt_scope.

Notation "'!' n" := (d_var n) (in custom domain at level 0, n constr at level 0) : mctt_scope.

Notation "'⇑' a m" := (d_neut a m) (in custom domain at level 0, a custom domain at level 30, m custom domain at level 30) : mctt_scope.

Notation "'⇓' a m" := (d_dom a m) (in custom domain at level 0, a custom domain at level 30, m custom domain at level 30) : mctt_scope.

Notation "'⇑!' a n" := (d_neut a (d_var n)) (in custom domain at level 0, a custom domain at level 30, n constr at level 0) : mctt_scope.

Notation "ρ ↦ m" := (extend_env ρ m) (in custom domain at level 20, left associativity) : mctt_scope.

Notation "ρ '↯'" := (drop_env ρ) (in custom domain at level 10, ρ custom domain) : mctt_scope.

End Domain_Notations.

Import Domain_Notations.
