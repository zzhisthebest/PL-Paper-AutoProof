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

Require Import qenv.

Import QualNotations.

Local Open Scope qualifiers.

Import OpeningNotations.

Local Open Scope opening.

Class splicible_env {p : Type} `{@qenv p}: Type := {

  env_splice : nat -> p -> p;
  env_unsplice : nat -> p -> p;
  env_elmt_fvs : p -> nat -> bool;

}.

Definition splice_tenv_elmt := (fun n (X : (binding * bool * ty * qual)) =>
  match X with
  | (bd, b, T, q) => (bd, b, splice_ty n T, splice_qual n q)
  end).

Definition splice_senv_elmt := (fun n (X : (ty * qual)) =>
  match X with
  | (T, q) => (splice_ty n T, splice_qual n q)
  end).

Definition unsplice_tenv_elmt := (fun n (X : (binding * bool * ty * qual)) =>
  match X with
  | (bd, b, T, q) => (bd, b, unsplice_ty n T, unsplice_qual n q)
  end).

Definition unsplice_senv_elmt := (fun n (X : (ty * qual)) =>
  match X with
  | (T, q) => (unsplice_ty n T, unsplice_qual n q)
  end).

#[export] Instance tenv_splicible : @splicible_env (binding * bool * ty * qual) tenv_qenv := {
  env_splice := splice_tenv_elmt;
  env_unsplice := unsplice_tenv_elmt;
  env_elmt_fvs := fun a n => tfvs (snd (fst a)) n || qfvs (snd a) n;

}.

#[export] Instance senv_splicible : @splicible_env (ty * qual) senv_qenv := {
  env_splice := splice_senv_elmt;
  env_unsplice := unsplice_senv_elmt;
  env_elmt_fvs := fun a n => tfvs (fst a) n || qfvs (snd a) n;

}.

Definition splice_env {p : Type} `{splicible_env p} (n : nat) (E : env p) : env p := map (env_splice n) E.

Definition splice_tenv (n : nat) (Γ : tenv) : tenv := splice_env n Γ.

Definition splice_senvs (n : nat) (Σ : senvs) : senvs := splice_env n Σ.

Definition splice_senv (n : nat) (Σ : senv) : senv := map (splice_senvs n) Σ.

Module SplicingNotations.

Declare Scope splicing.

Notation "t ↑ᵗ n" := (splice n t) (at level 10) : splicing.

Notation "T ↑ᵀ n" := (splice_ty n T) (at level 10) : splicing.

Notation "q ↑ᵈ n" := (splice_qual n q) (at level 10) : splicing.

Notation "g ↑ᴳ n" := (splice_env n g) (at level 10) : splicing.

Notation "g s↑ᴳ n" := (splice_senv n g) (at level 10) : splicing.

End SplicingNotations.

Import SplicingNotations.

Local Open Scope splicing.

Fixpoint subst_tm (t : tm) (v : nat) (u : tm) : tm :=
  match t with
  | ttabs t       => ttabs (subst_tm t v u)
  | ttapp t       => ttapp (subst_tm t v u)
  | tunit         => tunit
  | # x           => # x
  | $ x           => if Nat.eqb x v then u else $(pred x)
  | tabs t        => tabs (subst_tm t v u)
  | tapp t1 t2    => tapp (subst_tm t1 v u) (subst_tm t2 v u)
  | & (l, o)      => & (l, o)
  | tref t        => tref (subst_tm t v u)
  | trefat t1 t2  => trefat (subst_tm t1 v u) (subst_tm t2 v u)
  | ! t           => ! (subst_tm t v u)
  | tassign t1 t2 => tassign (subst_tm t1 v u) (subst_tm t2 v u)
  | twithr t1 t2  => twithr (subst_tm t1 v u) (subst_tm t2 v u)
  | twithc l t    => twithc l (subst_tm t v u)
  end.

Fixpoint subst_ty (T : ty) (v : nat) (U: ty) (q : qual) : ty :=
  match T with
  | TTop             => TTop
  | TVar (varF i)    => if Nat.eqb i v then U else (TVar (varF (pred i)))
  | TVar (varB i)    => TVar (varB i)
  | TAll q1 q2 T1 T2 => TAll (subst_qual q1 v q) (subst_qual q2 v q) (subst_ty T1 v U q) (subst_ty T2 v U q)
  | TUnit            => TUnit
  | TFun q1 q2 T1 T2 => TFun (subst_qual q1 v q) (subst_qual q2 v q) (subst_ty T1 v U q) (subst_ty T2 v U q)
  | TRef q1 T        => TRef (subst_qual q1 v q) (subst_ty T v U q)
  end.

Class substitutable_env {p : Type} `{@qenv p}: Type := {

  env_subst : nat -> ty -> qual -> p -> p;
}.

Definition subst_tenv_elmt := (fun n T' q' (X : (binding * bool * ty * qual)) =>
  match X with
  | (bd, b, T, q) => (bd, b, subst_ty T n T' q', subst_qual q n q')
  end).

Definition subst_senv_elmt := (fun n T' q' (X : (ty * qual)) =>
  match X with
  | (T, q) => (subst_ty T n T' q', subst_qual q n q')
  end).

#[export] Instance tenv_substitutable : @substitutable_env (binding * bool * ty * qual) tenv_qenv := {
  env_subst := subst_tenv_elmt;
}.

#[export] Instance senv_substitutable : @substitutable_env (ty * qual) senv_qenv := {
  env_subst := subst_senv_elmt;
}.

Definition subst_env {p : Type} `{substitutable_env p} (n : nat) (T' : ty) (q' : qual)  (E : env p): env p := map (env_subst n T' q') E.

Definition subst_tenv (Γ : tenv) (v : nat) (U: ty)(q1 : qual) : tenv := subst_env v U q1 Γ.

Definition subst_senv (Σ : senv) (v : nat) (U: ty)(q1 : qual) : senv := map (subst_env v U q1) Σ.

Module SubstitutionNotations.

Declare Scope substitutions.

Notation "{ v1 |-> t1 ; t2 }ᵗ t"  := (subst_tm (subst_tm t v1 t1) v1 t2) (at level 10) : substitutions.

Notation "{ v1 |-> t1 }ᵗ t"       := (subst_tm t v1 t1) (at level 10) : substitutions.

Notation "{ v1 |-> q1 ; q2 }ᵈ q"  := (subst_qual (subst_qual q v1 q1) v1 q2) (at level 10) : substitutions.

Notation "{ v1 |-> q1 }ᵈ q"       := (subst_qual q v1 q1) (at level 10) : substitutions.

Notation "{ v1 |-> U1 ~ q1 ; U2 ~ q2  }ᵀ T" := (subst_ty (subst_ty T v1 U1 q1) v1 U2 q2) (at level 10) : substitutions.

Notation "{ v1 |-> U1 ~ q1 }ᵀ T" := (subst_ty T v1 U1 q1) (at level 10) : substitutions.

Notation "{ v1 |-> T1 ~ q1 }ᴳ G" := (subst_env v1 T1 q1 G) (at level 10) : substitutions.

Notation "{ v1 |-> T1 ~ q1 ; T2 ~ q2 }ᴳ G" := (subst_env v1 T2 q2 (subst_env v1 T1 q1 G)) (at level 10) : substitutions.

End SubstitutionNotations.

Import SubstitutionNotations.

Local Open Scope substitutions.

Fixpoint q_trans_one {p : Type} `{qenv p} (E : env p) (q : qual) :=
  match E with
  | a :: E' => if (qenv_qn q (length E'))
      then qor (q_trans_one E' q) (qenv_q a)
      else (q_trans_one E' q)
  | [] => q
  end.

Definition N_trans_one {p : Type} `{qenv p} (E : env p) (q : Qual) (f : Qual -> Nats) (x : nat) : Prop :=
  f q x \/
    exists x',
      qenv_Qn q x' /\
        exists a, indexr x' E = Some a /\ f (Q_lift (qenv_q a)) x.

Fixpoint q_trans'' {p : Type} `{qenv p} (E : env p) (q : qual) (fuel : nat) {struct fuel} :=
  match fuel with
  | 0 => q
  | S fuel' => q_trans'' E (q_trans_one E q) fuel'
  end.

Definition N_trans'' {p : Type} `{qenv p} (E : env p) (q : Qual) (f : Qual -> Nats) (fuel : nat) (x : nat) : Prop :=
  f q x \/
  exists fuel', fuel = S fuel' /\
  exists x', qenv_Qn q x' /\
  exists a, indexr x' E = Some a /\ f (Q_lift (q_trans'' E (qenv_q a) fuel')) x.

Definition q_trans_tenv (Γ : tenv) (q : qual) := q_trans'' Γ q (‖Γ‖).

Definition qenv_saturated_q'' {p : Type} `{qenv p} (E : env p) (q : qual) :=
  q_trans_one E q = q.

Fixpoint cardinality (q : qual) {p : Type} `{qenv p} (E : env p) : nat :=
  match E with
  | [] => 0
  | a :: E' => if qenv_qn q (‖ E' ‖) then S (cardinality q E') else cardinality q E'
  end.

Definition Q_trans'' {p : Type} `{qenv p} (E : env p) (q : Qual) (fuel : nat) : Qual :=
  (N_trans'' E q Qfr fuel 0, N_trans'' E q qfvs fuel, N_trans'' E q qbvs fuel, N_trans'' E q qlocs fuel).

Definition Q_trans_one {p : Type} `{qenv p} (E : env p) (q : Qual) : Qual :=
  (N_trans_one E q Qfr 0, N_trans_one E q qfvs, N_trans_one E q qbvs, N_trans_one E q qlocs).

Definition extends_2D (Σ' Σ : senv) := forall l c, indexr l Σ = Some c -> exists c', indexr l Σ' = Some c' /\ c' ⊇ c.

Notation "x ⊇₂ y" := (extends_2D x y) (at level 75).
