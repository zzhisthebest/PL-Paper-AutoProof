(* 
  Author(s):
    Dominique Larchey-Wendling (1)
    Andrej Dudenhefner (2)
    Johannes Hostert (2)
  Affiliation(s):
    (1) LORIA -- CNRS
    (2) Saarland University, Saarbrücken, Germany
*)

(** * Satisfiability of elementary, square, and uniform Diophantine constraints H10C_SAT, H10SQC_SAT, and H10UC_SAT *)

(* 
  Problems(s):
    Diophantine Constraint Solvability (H10C_SAT)
    Square Diophantine Constraint Solvability (H10SQC_SAT)
    Uniform Diophantine Constraint Solvability (H10UC_SAT)
    Uniform Diophantine Pair Constraint Solvability (H10UPC_SAT)
*)

From Stdlib Require Import List.

(* Diophantine constraints (h10c) are of three shapes:
      x = 1 | x + y = z | x * y = z  with x, y, z in nat 
*)

Inductive h10c : Set :=
  | h10c_one : nat -> h10c
  | h10c_plus : nat -> nat -> nat -> h10c
  | h10c_mult : nat -> nat -> nat -> h10c.
  
Definition h10c_sem c φ :=
  match c with
    | h10c_one x      => φ x = 1
    | h10c_plus x y z => φ x + φ y = φ z
    | h10c_mult x y z => φ x * φ y = φ z
  end.

(*
  Diophantine Constraint Solvability:
    given a list of Diophantine constraints, is there a valuation that satisfies each constraint?
*)
Definition H10C_SAT (cs: list h10c) := exists (φ: nat -> nat), forall c, In c cs -> h10c_sem c φ.
