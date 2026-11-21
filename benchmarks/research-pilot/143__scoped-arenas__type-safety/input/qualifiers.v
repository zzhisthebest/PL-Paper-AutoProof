Require Export Arith.EqNat.

Require Export PeanoNat.

Require Import Coq.Program.Equality.

Require Import Coq.Bool.Bool.

Require Import Coq.Arith.Arith.

Require Import Coq.Lists.List.

Require Import Psatz.

Require Import Coq.Arith.Compare_dec.

Require Import FunctionalExtensionality.

Require Import Coq.Logic.PropExtensionality.

Import ListNotations.

Require Import vars.

Require Export nats.

Require Export boolean.

Require Export qualifiers_base.

Require Export qualifiers_slow.

Export QualNotations.

Local Open Scope qualifiers.

Definition qfr : qual -> nats := (fun q _ => qfresh q).

Definition Qfr : Qual -> Nats := (fun q _ => qfresh q).

Definition Q_lift_qn' (f : qual -> nats) (F : Qual -> Nats) :=
  forall (q : qual), N_lift (f q) = F (Q_lift q).

Definition Qn_or_dist' (qenv_Qn : Qual -> Nats) := forall q1 q2, qenv_Qn (Qor q1 q2) = N_or (qenv_Qn q1) (qenv_Qn q2).

Definition qn_or_dist' (qn : qual -> nats) := forall q1 q2, qn (qor q1 q2) = n_or (qn q1) (qn q2).

Definition Qn_and_dist' (qenv_Qn : Qual -> Nats) := forall q1 q2, qenv_Qn (Qand q1 q2) = N_and (qenv_Qn q1) (qenv_Qn q2).

Definition qn_and_dist' (qn : qual -> nats) := forall q1 q2, qn (qand q1 q2) = n_and (qn q1) (qn q2).

Definition Qn_sub' (Qn : Qual -> Nats) := forall q1 q2 : Qual, Subq q1 q2 -> N_sub (Qn q1) (Qn q2).

Definition qn_sub' (qn : qual -> nats) := forall q1 q2 : qual, q1 ⊑ q2 -> n_sub (qn q1) (qn q2).

Definition Qn_splice_dist' (qenv_Qn : Qual -> Nats) := forall n q, qenv_Qn (splice_Qual n q) = N_splice n (qenv_Qn q).

Definition Qn_splice_inv' (qenv_Qn : Qual -> Nats) := forall n q, qenv_Qn (splice_Qual n q) = (qenv_Qn q).

Definition qn_splice_dist' (qenv_qn : qual -> nats) := forall n q, qenv_qn (splice_qual n q) = n_splice n (qenv_qn q).

Definition qn_splice_inv' (qenv_qn : qual -> nats) := forall n q, qenv_qn (splice_qual n q) = (qenv_qn q).

Class qnmap (qn : qual -> nats) (Qn : Qual -> Nats) : Type := {
  qn_sub : qn_sub' qn;
  Qn_sub : Qn_sub' Qn;
  qn_or_dist : qn_or_dist' qn;
  Qn_or_dist : Qn_or_dist' Qn;
  qn_and_dist : qn_and_dist' qn;
  Qn_and_dist : Qn_and_dist' Qn;
  Q_lift_qn : Q_lift_qn' qn Qn;
}.
