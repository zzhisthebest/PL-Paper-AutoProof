Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Coq.Relations.Relation_Operators.

Require Export LibTactics.

Require Export progress.

Fixpoint erase (t:exp) :=
  match t with
  | e_var_f x => e_var_f x
  | e_var_b x => e_var_b x
  | e_abs t1 t2 => e_abs t1 (erase t2)
  | e_app t1 t2 => e_app (erase t1) (erase t2)
  | e_lit l => e_lit l
  | e_cast c e => erase e
  end.

Notation "e1 '==>*' e2" := (clos_refl_trans exp Reduction e1 e2) (at level 40).

Notation "e1 '==>+' e2" := (clos_trans exp Reduction e1 e2) (at level 40).
