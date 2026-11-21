Require Import Metalib.Metatheory.

Require Import syntax_ott rules_inf Infrastructure rules_inf2.

Require Import Coq.Strings.String.

Fixpoint erase_anno (e:exp) : dexp :=
  match e with
  | (e_var_b nat) => de_var_b nat
  | (e_var_f x) => de_var_f x
  | e_top => de_top
  | (e_lit i5) => de_lit i5
  | (e_abs A e B) => de_abs (erase_anno e)
  | (e_fixpoint e A) => de_fixpoint (erase_anno e)
  | (e_app e1 e2) => de_app (erase_anno e1) (erase_anno e2)
  | (e_merge e1 e2) => de_merge (erase_anno e1) (erase_anno e2)
  | (e_anno e A) => erase_anno e
  end.

Notation "| e |" := (erase_anno e) (at level 30, e at level 39).

From Stdlib Require Import Lia.

Theorem reduction_soundness : forall e e',
    step e e' -> (erase_anno e) ->>* (erase_anno e').
