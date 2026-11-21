Set Implicit Arguments.

Require Import Coq.Lists.List.

Declare Scope ltac_scope.

Inductive Boxer : Type :=
| boxer : forall (A:Type), A -> Boxer.

Inductive ltac_No_arg : Set :=
| ltac_no_arg : ltac_No_arg.

Inductive ltac_Wild : Set :=
| ltac_wild : ltac_Wild.

Notation "'__'" := ltac_wild : ltac_scope.

Inductive ltac_Wilds : Set :=
| ltac_wilds : ltac_Wilds.

Notation "'___'" := ltac_wilds : ltac_scope.

Open Scope ltac_scope.

Inductive ltac_Mark : Type :=
| ltac_mark : ltac_Mark.

Notation "'>>'" :=
(@nil Boxer)
(at level 0)
: ltac_scope.

Notation "'>>' v1" :=
((boxer v1)::nil)
(at level 0, v1 at level 0)
: ltac_scope.

Notation "'>>' v1 v2" :=
((boxer v1)::(boxer v2)::nil)
(at level 0, v1 at level 0, v2 at level 0)
: ltac_scope.

Notation "'>>' v1 v2 v3" :=
((boxer v1)::(boxer v2)::(boxer v3)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0)
: ltac_scope.

Notation "'>>' v1 v2 v3 v4" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
 v4 at level 0)
: ltac_scope.

Notation "'>>' v1 v2 v3 v4 v5" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
 v4 at level 0, v5 at level 0)
: ltac_scope.

Notation "'>>' v1 v2 v3 v4 v5 v6" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
 ::(boxer v6)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
 v4 at level 0, v5 at level 0, v6 at level 0)
: ltac_scope.

Notation "'>>' v1 v2 v3 v4 v5 v6 v7" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
 ::(boxer v6)::(boxer v7)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
 v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0)
: ltac_scope.

Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
 ::(boxer v6)::(boxer v7)::(boxer v8)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
 v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
 v8 at level 0)
: ltac_scope.

Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
 ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
 v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
 v8 at level 0, v9 at level 0)
: ltac_scope.

Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
 ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
 v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
 v8 at level 0, v9 at level 0, v10 at level 0)
: ltac_scope.

Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
 ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
 ::(boxer v11)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
 v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
 v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0)
: ltac_scope.

Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
 ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
 ::(boxer v11)::(boxer v12)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
 v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
 v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
 v12 at level 0)
: ltac_scope.

Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13" :=
((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
 ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
 ::(boxer v11)::(boxer v12)::(boxer v13)::nil)
(at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
 v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
 v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
 v12 at level 0, v13 at level 0)
: ltac_scope.

Inductive Ltac_database_token : Prop := ltac_database_token.

Definition ltac_database (D:Boxer) (T:Boxer) (A:Boxer) := Ltac_database_token.

Notation "'Register' D T" := (ltac_database (boxer D) (boxer T) _)
(at level 69, D at level 0, T at level 0).

Definition rm (A:Type) (X:A) := X.

Require Coq.Numbers.BinNums Coq.ZArith.BinInt.

Definition ltac_int_to_nat (x:BinInt.Z) : nat :=
match x with
| BinInt.Z0 => 0%nat
| BinInt.Zpos p => BinPos.nat_of_P p
| BinInt.Zneg p => 0%nat
end.

Definition ltac_tag_subst (A:Type) (x:A) := x.

Definition ltac_to_generalize (A:Type) (x:A) := x.

Definition eq' := @eq.

Notation "x '='' y" := (@eq' _ x y)
(at level 70, y at next level).

Section equatesLemma.

Variables (A0 A1 : Type).

Variables (A2 : forall (x1 : A1), Type).

Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).

Variables (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).

Variables (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type).

Variables (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

End equatesLemma.

Notation "'nosimpl' t" := (match tt with tt => t end)
(at level 10).

Require Import Coq.Logic.ProofIrrelevance.

Section FuncEq.

Variables (A1 A2 A3 A4 A5 A6 A7 B : Type).

End FuncEq.

Require Import Coq.Program.Equality.

Require Import Coq.Arith.Compare_dec.

Require Import Coq.micromega.Lia.

Definition COIND (P:Prop) := P.

Definition ltac_something (P:Type) (e:P) := e.

Notation "'Something'" :=
(@ltac_something _ _).

Module LibTacticsCompatibility.

End LibTacticsCompatibility.

Open Scope nat_scope.
