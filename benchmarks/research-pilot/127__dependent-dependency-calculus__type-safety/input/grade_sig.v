Require Import Metalib.Metatheory.

Require Import Coq.Structures.Orders.

Require Import Stdlib.Init.Sumbool.

Require Import Coq.Program.Equality.

Require Import ssreflect.

Module Type GradeSig.

Parameter grade : Set.

Parameter q_Top : grade.

Parameter q_Bot : grade.

Parameter q_C   : grade.

Parameter q_R   : grade.

Parameter q_eqb  : grade -> grade -> bool.

Parameter q_leb  : grade -> grade -> bool.

Parameter q_join : grade -> grade -> grade.

Parameter q_meet : grade -> grade -> grade.

Parameter q_eq   : grade -> grade.

Definition t := grade.

Definition eq := @Logic.eq grade.

Definition eqb  := q_eqb.

Parameter q_eq_dec : forall (A : grade) (B : grade), { A = B } + { not (A = B) }.

Parameter eqb_eq : forall (n m : grade), q_eqb n m = true <-> n = m.

Definition eq_equiv : Equivalence (@Logic.eq grade) := eq_equivalence.

Definition eq_dec := q_eq_dec.

Include BackportEq.

Definition leb  := q_leb.

Definition le n m := is_true (q_leb n m).

Definition q_lt n m := is_true (q_leb n m) /\ n <> m.

Definition size_grade : grade -> nat := fun _ => 1%nat.

Declare Scope grade_scope.

Bind Scope grade_scope with grade.

Local Open Scope grade_scope.

Infix "=?" := q_eqb (at level 70) : grade_scope.

Infix "<=?" := q_leb (at level 70) : grade_scope.

Notation "q1 <= q2" := (is_true (q_leb q1 q2)) (at level 70)  : grade_scope.

Notation "q1 < q2" := (q_lt q1 q2) (at level 70)  : grade_scope.

Notation "x * y"  := (q_join x y) : grade_scope.

Notation "x + y " := (q_meet x y)  : grade_scope.

Parameter join_assoc : forall a b c, a * (b * c) = (a * b) * c.

Parameter join_comm  : forall a b, a * b = b * a.

Parameter meet_assoc : forall a b c, a + (b + c) = (a + b) + c.

Parameter meet_comm : forall a b, a + b = b + a.

Parameter absorb_meet : forall a b, a * (a + b) = a.

Parameter absorb_join : forall a b, a + (a * b) = a.

Parameter join_idem : forall a, a * a = a.

Parameter meet_idem : forall psi, psi + psi = psi.

Parameter join_Top_r : forall a, a * q_Top = q_Top.

Parameter meet_Bot_r : forall a, a + q_Bot = q_Bot.

Parameter order_q_C_dec : forall q, { q <= q_C } + { q_C < q }.

Parameter leb_leq  : forall (n m : grade), (n <=? m) = true <-> n <= m.

Parameter join_leq : forall a b,  a <= b -> (a * b) = b.

Parameter leq_join : forall a b, (a * b) = b -> a <= b.

Parameter meet_leq : forall a b,  a <= b -> (a + b) = a.

Parameter leq_meet : forall a b, (a + b) = a -> a <= b.

End GradeSig.

Declare Module Grade : GradeSig.

Export Grade.

Section GradeFacts.

Local Open Scope grade_scope.

End GradeFacts.
