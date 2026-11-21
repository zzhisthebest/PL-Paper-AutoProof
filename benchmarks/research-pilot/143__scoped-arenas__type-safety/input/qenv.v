Require Export Arith.EqNat.

Require Export PeanoNat.

Require Import Coq.Arith.Arith.

Require Import Coq.Bool.Bool.

Require Import Coq.Program.Equality.

Require Import Coq.Lists.List.

Require Import Psatz.

Require Import ZArith.

Require Import Coq.Arith.Compare_dec.

Import ListNotations.

Require Import vars.

Require Import env.

Require Import nats.

Require Import qualifiers.

Require Import boolean.

Require Import lang.

Import QualNotations.

Local Open Scope qualifiers.

Definition env := fun (p : Type) => list p.

Definition tenv := env (binding * bool * ty * qual).

Definition senvs := env (ty * qual).

Definition senv := env (senvs).

Definition getquals (p : ty * qual) : qual :=
  match p with
  | (_ , q) => q
  end.

Notation "p .q" := (map getquals p) (at level 75).

Fixpoint qunify (lq : list qual) : (qual) :=
  match lq with
  | [] => ∅
  | q :: tl => qor q (qunify tl)
  end.

Definition squish (Σ : senv) : senvs := map (fun x => (TUnit, qunify (x.q))) Σ.

Class qenv {p : Type} : Type := {

  qenv_q : p -> qual;

  qenv_qn : qual -> nats;
  qenv_Qn : Qual -> Nats;
}.

#[export] Instance tenv_qenv : @qenv (binding * bool * ty * qual) := {
  qenv_q := snd; qenv_qn := qfvs; qenv_Qn := qfvs;
}.

#[export] Instance senv_qenv : @qenv (ty * qual) := {
  qenv_q := snd; qenv_qn := qlocs; qenv_Qn := qlocs;
}.

Definition wf_senvs (L : nat) (c : senvs) : Prop :=
  forall x T q, indexr x c = Some (T, q) -> ♦∉ q /\ closed_ty 0 0 L T /\ closed_Qual 0 0 L q↑
.

Definition wf_senvc (L : nat) (c : senvs) : Prop := ‖ c ‖ > 0 /\ wf_senvs L c.

Definition wf_senv (Σ : senv) : Prop := forall l c,
  indexr l Σ = Some c -> wf_senvc (‖Σ‖) c
.

Inductive wf_tenv : tenv -> senv -> Prop :=
  | wf_tenv_nil : forall Σ, wf_senv Σ -> wf_tenv [] Σ
  | wf_tenv_cons : forall Γ Σ bd fr T q,
      wf_tenv Γ Σ ->
      closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
      closed_Qual 0 (‖Γ‖) (‖Σ‖) q↑ ->
      wf_tenv ((bd, fr, T, q) :: Γ) Σ
.

Inductive wf_qenv {p : Type} `{qenv p} : (env p) -> Prop :=
  | wf_qenv_nil : wf_qenv []
  | wf_qenv_cons : forall E a,
      wf_qenv E ->
      closed_Nats (‖E‖) (qenv_Qn (qenv_q a) ↑) ->
      wf_qenv (a :: E).

Definition closed_qenv {p : Type} `{qenv p} (b f l : nat) (E : env p) : Prop :=
  forall x a, indexr x E = Some a -> closed_Qual b f l (qenv_q a) ↑.

Definition closed_qenv_qn {p : Type} `{qenv p} (n : nat) (E : env p) : Prop :=
  forall x a, indexr x E = Some a -> closed_Nats n (qenv_Qn (qenv_q a) ↑).
