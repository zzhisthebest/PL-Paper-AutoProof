Require Export Arith.EqNat.

Require Export PeanoNat.

Require Import Coq.Program.Equality.

Require Import Coq.Bool.Bool.

Require Import Coq.Arith.Arith.

Require Import Coq.Lists.List.

Require Import Psatz.

Require Import Coq.Arith.Compare_dec.

Import ListNotations.

Require Import FunctionalExtensionality.

Require Import Coq.Logic.PropExtensionality.

Require Import vars.

Require Import nats.

Require Import boolean.

Definition qual : Type := (bool  * nats  * nats  * nats ).

Definition Qual : Type := (Prop * Nats * Nats * Nats).

Definition qfresh {A B C D} (q : A * B * C * D): A := fst (fst (fst q)).

Definition qfvs   {A B C D} (q : A * B * C * D): B := snd (fst (fst q)).

Definition qbvs   {A B C D} (q : A * B * C * D): C := snd (fst q).

Definition qlocs  {A B C D} (q : A * B * C * D): D := snd q.

Definition qmemb (v : var + loc) (d : qual) : bool  :=
  match v with
  | inl (varF v) => qfvs d v
  | inl (varB v) => qbvs d v
  | inr l        => qlocs d l
  end.

Definition qmem (v : var + loc) (d : qual) : Prop :=
  match v with
  | inl (varF v) => N_lift (qfvs d) v
  | inl (varB v) => N_lift (qbvs d) v
  | inr l        => N_lift (qlocs d) l
  end.

Definition qdom {A} (Σ : list A): qual := (true, n_empty, n_empty, (n_dom Σ)).

Definition qdom' {A} (Σ : list (option A)): qual := (true, n_empty, n_empty, (n_dom' Σ)).

Definition subq (d1 d2 : qual) : Prop :=
  Is_true (implb (qfresh d1) (qfresh d2)) /\ (n_sub (qfvs d1) (qfvs d2)) /\ (n_sub (qbvs d1) (qbvs d2)) /\ (n_sub (qlocs d1) (qlocs d2)).

Definition qor (d1 d2 : qual) : qual := (orb  (qfresh d1) (qfresh d2), n_or  (qfvs d1) (qfvs d2), n_or  (qbvs d1) (qbvs d2), n_or  (qlocs d1) (qlocs d2)).

Definition qand (d1 d2 : qual) : qual := (andb (qfresh d1) (qfresh d2), n_and (qfvs d1) (qfvs d2), n_and (qbvs d1) (qbvs d2), n_and (qlocs d1) (qlocs d2)).

Definition qdiff (d1 d2 : qual) : qual := (andb (qfresh d1) (negb (qfresh d2)), n_diff (qfvs d1) (qfvs d2), n_diff (qbvs d1) (qbvs d2), n_diff (qlocs d1) (qlocs d2)).

Definition qqplus (q1 q2 : qual) : qual := if (qfresh q1) then (qor q1 q2) else q1.

Arguments qqplus _ / _.

Definition Subq (d1 d2 : Qual) : Prop :=
  ((qfresh d1) -> (qfresh d2)) /\ (N_sub (qfvs d1) (qfvs d2)) /\ (N_sub (qbvs d1) (qbvs d2)) /\ (N_sub (qlocs d1) (qlocs d2)).

Definition Qor (d1 d2 : Qual) : Qual := ((qfresh d1) \/ (qfresh d2), N_or  (qfvs d1) (qfvs d2), N_or  (qbvs d1) (qbvs d2), N_or  (qlocs d1) (qlocs d2)).

Definition Qand (d1 d2 : Qual) : Qual := ((qfresh d1) /\ (qfresh d2), N_and (qfvs d1) (qfvs d2), N_and (qbvs d1) (qbvs d2), N_and (qlocs d1) (qlocs d2)).

Definition Qqplus (d1 d2 : Qual) : Qual := (qfresh d1, (fun x => (qfresh d1 -> N_or (qfvs d1) (qfvs d2) x)   /\ (~ (qfresh d1) -> qfvs d1 x)),
                                                       (fun x => (qfresh d1 -> N_or (qbvs d1) (qbvs d2) x)   /\ (~ (qfresh d1) -> qbvs d1 x)),
                                                       (fun x => (qfresh d1 -> N_or (qlocs d1) (qlocs d2) x) /\ (~ (qfresh d1) -> qlocs d1 x))).

Definition Qdiff (d1 d2 : Qual) : Qual := (qfresh d1 /\ ((qfresh d2) -> False), N_diff (qfvs d1) (qfvs d2), N_diff (qbvs d1) (qbvs d2), N_diff (qlocs d1) (qlocs d2)).

Definition Qdom {A} (Σ : list A): Qual := (True, N_empty, N_empty, (N_dom Σ)).

Definition q_empty: qual := (false, n_empty, n_empty, n_empty).

Definition Q_empty: Qual := (False, N_empty, N_empty, N_empty).

Definition Q_lift (q: qual): Qual := (Is_true (qfresh q), N_lift (qfvs q), N_lift (qbvs q), N_lift (qlocs q)).

Definition open_qual (k : nat) (d' : qual) (d : qual) : qual :=
  if (qbvs d k) then
  qor (qfresh d, qfvs d, n_diff (qbvs d) (n_one k), qlocs d) d'
  else d
.

Definition open_Qual (k : nat) (d' : Qual) (d : Qual) : Qual :=
  (
  (qbvs d k -> qfresh d \/ qfresh d') /\ (~(qbvs d k) -> qfresh d),
  fun x => (qbvs d k -> (N_or (qfvs d) (qfvs d') x)) /\ (~(qbvs d k) -> qfvs d x),
  fun x => (qbvs d k -> (N_or (N_diff (qbvs d) (N_one k)) (qbvs d') x)) /\ (~(qbvs d k) -> qbvs d x),
  fun x => (qbvs d k -> (N_or (qlocs d) (qlocs d') x)) /\ (~(qbvs d k) -> qlocs d x)
  )
.

Definition splice_qual (n : nat) (d : qual) : qual :=
  (qfresh d,(n_splice n (qfvs d)),qbvs d,qlocs d)
.

Definition splice_Qual (n : nat) (d : Qual) : Qual :=
  (qfresh d,(N_splice n (qfvs d)),qbvs d,qlocs d)
.

Definition unsplice_qual (n : nat) (d : qual) : qual :=
  (qfresh d,(n_unsplice n (qfvs d)),qbvs d,qlocs d)
.

Definition unsplice_Qual (n : nat) (d : Qual) : Qual :=
  (qfresh d,(N_unsplice n (qfvs d)),qbvs d,qlocs d)
.

Definition subst_qual (q : qual) (v : nat) (q' : qual) : qual :=
  if qfvs q v
  then qor (qfresh q, n_unsplice 0 (n_diff (qfvs q) (n_one v)), qbvs q, qlocs q) q'
  else (qfresh q, n_unsplice 0 (qfvs q), qbvs q, qlocs q)
.

Definition subst_Qual (q : Qual) (v : nat) (q' : Qual) : Qual :=
  (
  (qfvs q v -> qfresh q \/ qfresh q') /\ (~(qfvs q v) -> qfresh q),
  fun x => (qfvs q v -> (N_or (N_unsplice 0 (N_diff (qfvs q) (N_one v))) (qfvs q') x)) /\ (~(qfvs q v) -> N_unsplice 0 (qfvs q) x),
  fun x => (qfvs q v -> (N_or (qbvs q) (qbvs q') x)) /\ (~(qfvs q v) -> qbvs q x),
  fun x => (qfvs q v -> (N_or (qlocs q) (qlocs q') x)) /\ (~(qfvs q v) -> qlocs q x)
  )
.

Definition closed_qual b f l (q : qual) :=
  closed_nats f (qfvs q) /\ closed_nats b (qbvs q) /\ closed_nats l (qlocs q).

Definition closed_Qual b f l (q : Qual) :=
  closed_Nats f (qfvs q) /\ closed_Nats b (qbvs q) /\ closed_Nats l (qlocs q).

Module QualNotations.

Declare Scope qualifiers.

Notation "∅"        := (q_empty) (at level 9) : qualifiers.

Notation "{♦}"      := (true, n_empty, n_empty, n_empty) (at level 9) : qualifiers.

Notation "∅{ f }"   := (f, n_empty, n_empty, n_empty)  (at level 9) : qualifiers.

Notation "l ∈ₗ d"   := (qmem (inr l) d) (at level 75) : qualifiers.

Notation "v ∈ᵥ d"   := (qmem (inl v) d) (at level 75) : qualifiers.

Notation "l ∈?ₗ d"  := (qmemb (inr l) d) (at level 75) : qualifiers.

Notation "v ∈?ᵥ d"  := (qmemb (inl v) d) (at level 75) : qualifiers.

Notation "♦∈ d"     := (Is_true (qfresh d)) (at level 75) : qualifiers.

Notation "♦∉ d"     := (~Is_true (qfresh d)) (at level 75) : qualifiers.

Notation "♦∈? d"    := (qfresh d) (at level 75) : qualifiers.

Notation "$! x "    := (false, (n_one x), n_empty, n_empty) (at level 0, right associativity) : qualifiers.

Notation "#! x "    := (false, n_empty, (n_one x), n_empty) (at level 0, right associativity) : qualifiers.

Notation "&! l "    := (false, n_empty, n_empty, (n_one l)) (at level 0, right associativity) : qualifiers.

Notation "$♦ x"     := (true, (n_one x), n_empty, n_empty) (at level 0, right associativity) : qualifiers.

Notation "#♦ x "    := (true, n_empty, (n_one x), n_empty) (at level 0, right associativity) : qualifiers.

Notation "&♦ l "    := (true, n_empty, n_empty, (n_one l)) (at level 0, right associativity) : qualifiers.

Notation "${ f } x" := (f, (n_one x), n_empty, n_empty) (at level 0, right associativity) : qualifiers.

Notation "#{ f } x" := (f, n_empty, (n_one x), n_empty) (at level 0, right associativity) : qualifiers.

Notation "&{ f } l" := (f, n_empty, n_empty, (n_one l)) (at level 0, right associativity) : qualifiers.

Notation "d ↑" := (Q_lift d) (at level 9) : qualifiers.

Notation "d1 ⊑ d2"  := (subq d1 d2) (at level 75) : qualifiers.

Notation "d1 ⊑↑ d2"  := (Subq (Q_lift d1) (Q_lift d2)) (at level 75) : qualifiers.

Notation "d1 ⊔ d2"  := (qor d1 d2) (at level 70, right associativity) : qualifiers.

Notation "d1 ⊓ d2"  := (qand d1 d2) (at level 65, right associativity) : qualifiers.

Notation "q1 ⋓ q2"  := (qqplus q1 q2) (at level 70, right associativity) : qualifiers.

Notation "q1 ⋒ q2"  := (qor (qand q1 q2) (true, n_empty, n_empty, n_empty)) (at level 70, right associativity) : qualifiers.

End QualNotations.

Export QualNotations.

Local Open Scope qualifiers.
