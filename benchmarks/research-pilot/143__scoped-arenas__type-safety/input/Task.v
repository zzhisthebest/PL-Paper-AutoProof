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

Require Import ops.

Require Import killsep.

Require Import rules.

Require Import vtp_subst.

Import QualNotations.

Local Open Scope qualifiers.

Import OpeningNotations.

Local Open Scope opening.

Import SplicingNotations.

Local Open Scope splicing.

Import SubstitutionNotations.

Local Open Scope substitutions.

Inductive disjointq (Σ Σ' : senv) : qual -> qual -> Prop :=
| disj_bot : forall q,
    disjointq Σ Σ' q ∅
| disj_loc : forall T q q',
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    ♦∉ q ->
    Σ' = [(T,q)] :: Σ ->
    disjointq Σ Σ' q' (&!‖Σ‖)
.

Arguments disj_loc { Σ Σ' }.

Notation " S → T ∋ q ⊕ q'" := (disjointq S T q q') (at level 10).

Definition CtxOK (Γ : tenv) (φ : qual) (Σ : senv) (ϰ : qual) (σ : store) : Prop :=
  qdom' σ ⊑↑ qdom Σ /\ ‖ σ ‖ = ‖ Σ ‖ /\
     φ ⊑↑ (qdom Σ) /\
  closed_Qual 0 0 (‖Σ‖) ϰ↑ /\
  kill_sep ϰ φ /\
  forall l o cty T q,
  (l ∈ₗ ϰ -> indexr l σ = Some None) /\ (~(l∈ₗ ϰ) ->
    l ∈ₗ φ ->
    indexr l Σ = Some cty ->
    (exists ctm, (indexr l σ = Some (Some ctm) /\ (‖ cty ‖) = (‖ ctm ‖)) /\
    (indexr o cty = Some (T,q) ->  (exists v, indexr o ctm = Some v /\
      value v /\ (q ⊑↑ φ -> vtp Σ ϰ φ v T q))))

  )
.

Fixpoint wf_step (t:tm) : Prop :=
  match t with
  | ttabs t1 => local_locs t1 = ∅
  | ttapp t1 => wf_step t1
  | tabs t1 => local_locs t1 = ∅
  | tapp t1 t2 => wf_step t1 /\ wf_step t2 /\ ((value t1) \/ local_locs t2 = ∅)
  | tref t1 => wf_step t1
  | trefat t1 t2 => wf_step t1 /\ wf_step t2 /\ (local_locs t1 = ∅ \/ (value t2))
  | tderef t1 => wf_step t1
  | tassign t1 t2 => wf_step t1 /\ wf_step t2 /\ ((value t1) \/ local_locs t2 = ∅)
  | twithr t1 t2 => wf_step t1 /\ wf_step t2 /\ (local_locs t2 = ∅)
  | twithc l t1 => wf_step t1
  | _ => True
  end.

Definition wf_store (σ : store) : Prop :=
    forall l o v, sindexr' l o σ = Some (v) -> wf_step v /\ value v.

Inductive envUpdate (Σ : senv) (φ : qual) (ϰ : qual) (LC : qual): senv -> qual -> qual -> Prop :=
| env_phi : forall Σ',

    Σ' ⊇₂ Σ ->
    ‖Σ'‖ = ‖Σ‖ ->
    envUpdate Σ φ ϰ LC Σ' φ ϰ
| env_fresh : forall T q,
    kill_sep ϰ q ->
    envUpdate Σ φ ϰ LC ([(T,q)] :: Σ) (φ ⊔ &!(‖Σ‖)) ϰ
| env_kill : forall l,
    l < (‖Σ‖) ->
    l ∈ₗ LC ->
    envUpdate Σ φ ϰ LC Σ (q_remove Σ l φ) (ϰ ⊔ &!l)
.

Inductive preserve (Γ : tenv) (Σ : senv) (ϰ : qual) (φ : qual) (LC : qual) (t' : tm) (T : ty) (d : qual) (σ' : store) : Prop :=
| Preserve : forall Σ' d' φ' ϰ',
    Σ' ⊇₂ Σ ->

    envUpdate Σ φ ϰ LC Σ' φ' ϰ' ->
    d' ⊑↑ φ' ->
    wf_senv Σ' ->
    CtxOK Γ φ' Σ' ϰ' σ' ->
    Σ → Σ' ∋ d ⊕ d'  ->
    has_type Γ φ' Σ' t' T (d ⋓ d') ->

    wf_store σ' ->
    wf_step t' ->
    preserve Γ Σ ϰ φ LC t' T d σ'.

Arguments Preserve {Γ Σ ϰ φ LC t' T d σ'}.

Theorem type_safety: forall {Σ ϰ t T d φ},
  has_type [] φ Σ t T d -> wf_senv Σ -> wf_step t -> (
    value t \/
    (forall {σ} , CtxOK [] φ Σ ϰ σ -> wf_store σ ->
      (exists t' σ',
        step t σ t' σ' /\ preserve [] Σ ϰ φ (local_locs t) t' T d σ'
      )
    )
  ).
