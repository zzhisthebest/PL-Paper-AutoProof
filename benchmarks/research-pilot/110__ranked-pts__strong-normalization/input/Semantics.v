From Stdlib Require Import Relations.
From PTSrk Require Export Syntax.

Inductive RTC {A} (R: relation A): relation A :=
| rtc_refl x: RTC R x x
| rtc_step {x y z}: R x y -> RTC R y z -> RTC R x z.

Inductive Sym {A} (R: relation A): relation A :=
| forward {x y}: R x y -> Sym R x y
| backwards {x y}: R y x -> Sym R x y.

Definition EquivClosure {A} (R: relation A):
  relation A := RTC (Sym R).

Reserved Notation "t →ᵝ t'"
  (at level 50, no associativity).
Inductive step L n: relation (Term L n) :=
| step_pi_left {T T' U}:
       T →ᵝ T' ->
(* --------------- *)
   Π T U →ᵝ Π T' U
| step_pi_right {T U U'}:
       U →ᵝ U' ->
(* --------------- *)
   Π T U →ᵝ Π T U'
| step_lam_left {T T' t}:
       T →ᵝ T' ->
(* --------------- *)
   [T] t →ᵝ [T'] t
| step_lam_right {T t t'}:
       t →ᵝ t' ->
(* --------------- *)
   [T] t →ᵝ [T] t'
| step_app_left {f f' t}:
       f →ᵝ f' ->
(* --------------- *)
   f $ t →ᵝ f' $ t
| step_app_right {f t t'}:
       t →ᵝ t' ->
(* --------------- *)
   f $ t →ᵝ f $ t'
| step_beta T f t:
(* ------------------ *)
   [T] f $ t →ᵝ f ◁ t
where "t →ᵝ t'" := (step _ _ t t').

Definition def_equiv L n: relation (Term L n) :=
  EquivClosure (step L n).
Infix "=ᵝ" := (def_equiv _ _)
  (at level 50, no associativity).

Inductive Acc {A} (R: relation A) (x: A): Prop :=
| acc: (forall y, R x y -> Acc R y) -> Acc R x.

Definition sn {L n}: Term L n -> Prop := Acc (step L n).
