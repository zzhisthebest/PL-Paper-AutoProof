From AccInSProp Require Import core unscoped.

From AccInSProp Require Import BasicAST.

From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Module Core.

Inductive term : Type :=
  | var : nat -> term
  | Sort : level -> term
  | assm : aref -> term
  | Pi : level -> level -> term -> term -> term
  | lam : level -> level -> term -> term -> term -> term
  | app : level -> level -> term -> term -> term -> term -> term
  | Nat : term
  | zero : term
  | succ : term -> term
  | rec : level -> term -> term -> term -> term -> term
  | acc : level -> term -> term -> term -> term
  | accin : level -> term -> term -> term -> term -> term
  | accinv : level -> term -> term -> term -> term -> term -> term -> term
  | accel :
      level -> level -> term -> term -> term -> term -> term -> term -> term
  | accelcomp :
      level -> level -> term -> term -> term -> term -> term -> term -> term
  | obseq : level -> term -> term -> term -> term
  | obsrefl : level -> term -> term -> term
  | J : level -> term -> term -> term -> term -> term -> term -> term
  | cast : level -> term -> term -> term -> term -> term
  | injpi1 : level -> level -> term -> term -> term -> term -> term -> term
  | injpi2 :
      level -> level -> term -> term -> term -> term -> term -> term -> term.

Definition upRen_term_term (xi : nat -> nat) : nat -> nat := (up_ren xi).

Fixpoint ren_term (xi_term : nat -> nat) (s : term) {struct s} : term :=
  match s with
  | var s0 => var (xi_term s0)
  | Sort s0 => Sort s0
  | assm s0 => assm s0
  | Pi s0 s1 s2 s3 =>
      Pi s0 s1 (ren_term xi_term s2) (ren_term (upRen_term_term xi_term) s3)
  | lam s0 s1 s2 s3 s4 =>
      lam s0 s1 (ren_term xi_term s2) (ren_term (upRen_term_term xi_term) s3)
        (ren_term (upRen_term_term xi_term) s4)
  | app s0 s1 s2 s3 s4 s5 =>
      app s0 s1 (ren_term xi_term s2) (ren_term (upRen_term_term xi_term) s3)
        (ren_term xi_term s4) (ren_term xi_term s5)
  | Nat => Nat
  | zero => zero
  | succ s0 => succ (ren_term xi_term s0)
  | rec s0 s1 s2 s3 s4 =>
      rec s0 (ren_term (upRen_term_term xi_term) s1) (ren_term xi_term s2)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s3)
        (ren_term xi_term s4)
  | acc s0 s1 s2 s3 =>
      acc s0 (ren_term xi_term s1)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s2)
        (ren_term xi_term s3)
  | accin s0 s1 s2 s3 s4 =>
      accin s0 (ren_term xi_term s1)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s2)
        (ren_term xi_term s3) (ren_term xi_term s4)
  | accinv s0 s1 s2 s3 s4 s5 s6 =>
      accinv s0 (ren_term xi_term s1)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s2)
        (ren_term xi_term s3) (ren_term xi_term s4) (ren_term xi_term s5)
        (ren_term xi_term s6)
  | accel s0 s1 s2 s3 s4 s5 s6 s7 =>
      accel s0 s1 (ren_term xi_term s2)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s3)
        (ren_term (upRen_term_term xi_term) s4)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s5)
        (ren_term xi_term s6) (ren_term xi_term s7)
  | accelcomp s0 s1 s2 s3 s4 s5 s6 s7 =>
      accelcomp s0 s1 (ren_term xi_term s2)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s3)
        (ren_term (upRen_term_term xi_term) s4)
        (ren_term (upRen_term_term (upRen_term_term xi_term)) s5)
        (ren_term xi_term s6) (ren_term xi_term s7)
  | obseq s0 s1 s2 s3 =>
      obseq s0 (ren_term xi_term s1) (ren_term xi_term s2)
        (ren_term xi_term s3)
  | obsrefl s0 s1 s2 =>
      obsrefl s0 (ren_term xi_term s1) (ren_term xi_term s2)
  | J s0 s1 s2 s3 s4 s5 s6 =>
      J s0 (ren_term xi_term s1) (ren_term xi_term s2)
        (ren_term (upRen_term_term xi_term) s3) (ren_term xi_term s4)
        (ren_term xi_term s5) (ren_term xi_term s6)
  | cast s0 s1 s2 s3 s4 =>
      cast s0 (ren_term xi_term s1) (ren_term xi_term s2)
        (ren_term xi_term s3) (ren_term xi_term s4)
  | injpi1 s0 s1 s2 s3 s4 s5 s6 =>
      injpi1 s0 s1 (ren_term xi_term s2) (ren_term xi_term s3)
        (ren_term (upRen_term_term xi_term) s4)
        (ren_term (upRen_term_term xi_term) s5) (ren_term xi_term s6)
  | injpi2 s0 s1 s2 s3 s4 s5 s6 s7 =>
      injpi2 s0 s1 (ren_term xi_term s2) (ren_term xi_term s3)
        (ren_term (upRen_term_term xi_term) s4)
        (ren_term (upRen_term_term xi_term) s5) (ren_term xi_term s6)
        (ren_term xi_term s7)
  end.

Definition up_term_term (sigma : nat -> term) : nat -> term := (scons (var var_zero) (funcomp (ren_term shift) sigma)).

Fixpoint subst_term (sigma_term : nat -> term) (s : term) {struct s} :
term :=
  match s with
  | var s0 => sigma_term s0
  | Sort s0 => Sort s0
  | assm s0 => assm s0
  | Pi s0 s1 s2 s3 =>
      Pi s0 s1 (subst_term sigma_term s2)
        (subst_term (up_term_term sigma_term) s3)
  | lam s0 s1 s2 s3 s4 =>
      lam s0 s1 (subst_term sigma_term s2)
        (subst_term (up_term_term sigma_term) s3)
        (subst_term (up_term_term sigma_term) s4)
  | app s0 s1 s2 s3 s4 s5 =>
      app s0 s1 (subst_term sigma_term s2)
        (subst_term (up_term_term sigma_term) s3) (subst_term sigma_term s4)
        (subst_term sigma_term s5)
  | Nat => Nat
  | zero => zero
  | succ s0 => succ (subst_term sigma_term s0)
  | rec s0 s1 s2 s3 s4 =>
      rec s0 (subst_term (up_term_term sigma_term) s1)
        (subst_term sigma_term s2)
        (subst_term (up_term_term (up_term_term sigma_term)) s3)
        (subst_term sigma_term s4)
  | acc s0 s1 s2 s3 =>
      acc s0 (subst_term sigma_term s1)
        (subst_term (up_term_term (up_term_term sigma_term)) s2)
        (subst_term sigma_term s3)
  | accin s0 s1 s2 s3 s4 =>
      accin s0 (subst_term sigma_term s1)
        (subst_term (up_term_term (up_term_term sigma_term)) s2)
        (subst_term sigma_term s3) (subst_term sigma_term s4)
  | accinv s0 s1 s2 s3 s4 s5 s6 =>
      accinv s0 (subst_term sigma_term s1)
        (subst_term (up_term_term (up_term_term sigma_term)) s2)
        (subst_term sigma_term s3) (subst_term sigma_term s4)
        (subst_term sigma_term s5) (subst_term sigma_term s6)
  | accel s0 s1 s2 s3 s4 s5 s6 s7 =>
      accel s0 s1 (subst_term sigma_term s2)
        (subst_term (up_term_term (up_term_term sigma_term)) s3)
        (subst_term (up_term_term sigma_term) s4)
        (subst_term (up_term_term (up_term_term sigma_term)) s5)
        (subst_term sigma_term s6) (subst_term sigma_term s7)
  | accelcomp s0 s1 s2 s3 s4 s5 s6 s7 =>
      accelcomp s0 s1 (subst_term sigma_term s2)
        (subst_term (up_term_term (up_term_term sigma_term)) s3)
        (subst_term (up_term_term sigma_term) s4)
        (subst_term (up_term_term (up_term_term sigma_term)) s5)
        (subst_term sigma_term s6) (subst_term sigma_term s7)
  | obseq s0 s1 s2 s3 =>
      obseq s0 (subst_term sigma_term s1) (subst_term sigma_term s2)
        (subst_term sigma_term s3)
  | obsrefl s0 s1 s2 =>
      obsrefl s0 (subst_term sigma_term s1) (subst_term sigma_term s2)
  | J s0 s1 s2 s3 s4 s5 s6 =>
      J s0 (subst_term sigma_term s1) (subst_term sigma_term s2)
        (subst_term (up_term_term sigma_term) s3) (subst_term sigma_term s4)
        (subst_term sigma_term s5) (subst_term sigma_term s6)
  | cast s0 s1 s2 s3 s4 =>
      cast s0 (subst_term sigma_term s1) (subst_term sigma_term s2)
        (subst_term sigma_term s3) (subst_term sigma_term s4)
  | injpi1 s0 s1 s2 s3 s4 s5 s6 =>
      injpi1 s0 s1 (subst_term sigma_term s2) (subst_term sigma_term s3)
        (subst_term (up_term_term sigma_term) s4)
        (subst_term (up_term_term sigma_term) s5) (subst_term sigma_term s6)
  | injpi2 s0 s1 s2 s3 s4 s5 s6 s7 =>
      injpi2 s0 s1 (subst_term sigma_term s2) (subst_term sigma_term s3)
        (subst_term (up_term_term sigma_term) s4)
        (subst_term (up_term_term sigma_term) s5) (subst_term sigma_term s6)
        (subst_term sigma_term s7)
  end.

Class Up_term X Y :=
    up_term : X -> Y.

#[global] Instance Subst_term : (Subst1 _ _ _) := @subst_term.

#[global] Instance Up_term_term : (Up_term _ _) := @up_term_term.

#[global] Instance Ren_term : (Ren1 _ _ _) := @ren_term.

#[global]
Instance VarInstance_term : (Var _ _) := @var.

Notation "s [ sigma_term ]" := (subst_term sigma_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__term" := up_term (only printing)  : subst_scope.

Notation "↑__term" := up_term_term (only printing)  : subst_scope.

Notation "s ⟨ xi_term ⟩" := (ren_term xi_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var ( at level 1, only printing)  : subst_scope.

Notation "x '__term'" := (@ids _ _ VarInstance_term x)
( at level 5, format "x __term", only printing)  : subst_scope.

Notation "x '__term'" := (var x) ( at level 5, format "x __term")  :
subst_scope.

End Core.

Module Extra.

Import Core.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.
