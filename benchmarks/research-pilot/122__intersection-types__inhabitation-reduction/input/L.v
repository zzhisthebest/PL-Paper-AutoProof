(* Term syntax excerpted from theories/L/L.v. *)
Inductive term : Type :=
| var (n : nat) : term
| app (s : term) (t : term)
| lam (s : term).
