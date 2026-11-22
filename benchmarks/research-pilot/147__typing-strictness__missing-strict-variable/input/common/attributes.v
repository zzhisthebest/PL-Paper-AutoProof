Require Export strictness.common.fin_util.

From Coq Require Import FunctionalExtensionality.

Require Import Coq.Logic.Eqdep_dec.

Require Import Arith.

From Coq Require Export PeanoNat.

Require Import Psatz.

Inductive attr : Type :=
    | Lazy
    | Strict
    | Unknown.

Definition attr_le (c1 c2 : attr) :=
    match c1, c2 with
    | Unknown, _ => True
    | Lazy, Lazy => True
    | Strict, Strict => True
    | _, _ => False
    end.

Notation "c1 C<= c2" := (attr_le c1 c2) (at level 60).

Definition attr_stricter (c1 c2 : attr) :=
    match c1, c2 with
    | Strict, _ => True
    | Unknown, _ => True
    | _, Lazy => True
    | _, _ => False
    end.

Notation "c1 'S<=' c2" := (attr_stricter c1 c2) (at level 60).

Definition attr_add (c1 c2 : attr) : attr :=
    match c1, c2 with
    | Lazy, c2 => c2
    | c1, Lazy => c1
    | _, Strict => Strict
    | Strict, _ => Strict
    | _, _ => Unknown
    end.

Notation "c C+ d" := (attr_add c d) (at level 60).

Definition attrs n : Type := fin n -> attr.

Definition ren_env {A n n'} (γ : fin n -> A) (ξ : fin n' -> fin n) : fin n' -> A :=
    fun fn => γ (ξ fn).

Definition lazyvector {n} : attrs n := fun _ => Lazy.

Definition strictvector {n} : attrs n := fun _ => Strict.

Definition attr_vector_add {n} (γ1 γ2 : attrs n) : attrs n :=
    fun fn => γ1 fn C+ γ2 fn.

Notation "c γ+ d" := (attr_vector_add c d) (at level 60).

Definition attr_vector_le {n} (γ1 γ2 : attrs n) : Prop := forall fn,
    γ1 fn C<= γ2 fn.

Notation "γ1 γ<= γ2" := (attr_vector_le γ1 γ2) (at level 50).

Definition attr_vector_stricter {n} (γ1 γ2 : attrs n) : Prop := forall fn,
    γ1 fn S<= γ2 fn.

Notation "γ1 γS<= γ2" := (attr_vector_stricter γ1 γ2) (at level 50).

Definition down_attrs {n} (γ : attrs (S n)) : attrs n := ren_env γ shift.

Notation "'γ↓' γ" := (down_attrs γ) (at level 85).

Definition env_set {n} {A : Type} (ϕ : fin n -> A) (i : fin n) (a : A) :=
    fun fn => if fin_eqb i fn then a else ϕ fn.

Notation "ϕ <- a @ i " := (env_set ϕ i a) (at level 70).

Definition le_minus_plus n m : n <= m -> m = m - n + n := ltac:(lia).
Definition le_succ_succ_diag_r m : m <= S (S m) := ltac:(lia).

Definition up_fin_until : forall {n : nat} (m : nat), n <= m -> ren n m :=
fun (n m : nat) (H : n <= m) =>
(fun fn : fin n =>
 let fn0 := shift_p (m - n) fn in
 let H0 : m = m - n + n := le_minus_plus n m H in
 let fn1 := eq_rec_r (fun n0 : nat => fin n0) fn0 H0 in fn1)
:
ren n m.
Arguments up_fin_until {n} m H _.

Definition down_env_until' {A m} k (γ : fin (k + m) -> A) : fin m -> A :=
    ren_env γ (shift_p k).

Definition down_env_until : forall {A : Type} {n : nat},
       (fin n -> A) -> forall m : nat, m <= n -> fin m -> A :=
fun (A : Type) (n : nat) (γ : fin n -> A) (m : nat) (H : m <= n) =>
let H0 : n - m + m = n :=
  let H0 : n = n - m + m := le_minus_plus m n H in eq_sym H0 in
let γ0 := eq_rect_r (fun n0 : nat => fin n0 -> A) γ H0 in
down_env_until' (n - m) γ0.
Arguments down_env_until {A} {n} 
  γ m H _.

Definition pad_with' : forall {n : nat}, attr -> attrs n -> forall k : nat, attrs (k + n) :=
fun (n : nat) (q : attr) (γ : attrs n) (k : nat) =>
nat_rect (fun k0 : nat => attrs (k0 + n)) (γ : attrs (0 + n))
  (fun (k0 : nat) (IHk : attrs (k0 + n)) =>
   let H : S (k0 + n) = S k0 + n := eq_refl in
   eq_rect (S (k0 + n)) (fun n0 : nat => attrs n0)
     ((fun i : fin (S (k0 + n)) =>
       match i with
       | Some f => (fun f0 : fin (k0 + n) => IHk f0) f
       | None => q
       end)
      :
      attrs (S (k0 + n)))
     (S k0 + n) H)
  k.
Arguments pad_with' {n} q γ k _.

Definition pad_with : forall {n : nat}, attr -> attrs n -> forall m : nat, n <= m -> attrs m :=
fun (n : nat) (q : attr) (γ : attrs n) (m : nat) (H : n <= m) =>
let γPad := pad_with' q γ (m - n) in
let HeqγPad : γPad = pad_with' q γ (m - n) := eq_refl in
let H0 : m = m - n + n := le_minus_plus n m H in
let γPad0 := eq_rect_r (fun n0 : nat => attrs n0) γPad H0 in γPad0.
Arguments pad_with {n} q γ m H _.

Definition fin_to_nat : forall {n : nat}, fin (S n) -> nat :=
fix fin_to_nat (n : nat) (f : fin (S n)) {struct n} : nat :=
  match f with
  | Some f0 =>
      (fun f1 : fin n =>
       match n as n0 return (fin n0 -> nat) with
       | 0 => fun f2 : fin 0 => False_rec nat f2
       | S n0 =>
           (fun (n1 : nat) (f2 : fin (S n1)) => S (fin_to_nat n1 f2)) n0
       end f1) f0
  | None => 0
  end.
Arguments fin_to_nat {n} f.
