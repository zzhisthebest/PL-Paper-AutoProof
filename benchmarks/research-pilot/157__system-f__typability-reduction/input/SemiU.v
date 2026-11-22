(* Author: Andrej Dudenhefner. From SemiUnification/SemiU.v. *)

Inductive term : Set :=
  | atom : nat -> term
  | arr : term -> term -> term.

Definition valuation : Set := nat -> term.

(* substitute atoms n of a term t by (f n) *)
Fixpoint substitute (f: valuation) (t: term) : term :=
  match t with
  | atom n => f n
  | arr s t => arr (substitute f s) (substitute f t)
  end.

(* The two inequalities share the same left-hand side s. *)
Definition LU2SemiU : term * term * term -> Prop :=
  fun '(s, t0, t1) => exists (φ ψ0 ψ1: valuation),
    substitute ψ0 (substitute φ s) = substitute φ t0 /\ substitute ψ1 (substitute φ s) = substitute φ t1.
