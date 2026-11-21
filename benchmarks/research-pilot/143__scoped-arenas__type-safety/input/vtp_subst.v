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

Import QualNotations.

Local Open Scope qualifiers.

Import OpeningNotations.

Local Open Scope opening.

Import SplicingNotations.

Local Open Scope splicing.

Import SubstitutionNotations.

Local Open Scope substitutions.

Inductive vtp: senv -> qual -> qual -> tm -> ty -> qual -> Prop :=
| vtp_tabs: forall Σ ϰ φ t T1 T2 T3 T4 d1 d2 d3 d4 df1 df2,
  closed_tm 2 0 (‖Σ‖) t ->
  closed_ty 0 0 (‖Σ‖) (TAll d3 d4 T3 T4) ->
  closed_ty 0 0 (‖Σ‖) (TAll d1 d2 T1 T2) ->
  has_type [(bind_ty, false, T1, d1); (bind_tm, true, (TAll d1 d2 T1 T2), df1)] (df1 ⊔ $!0 ⊔ $!1) Σ
           (t <~²ᵗ ([] : tenv)) (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv)) ->
  stp [] Σ T3 d3 T1 d1 ->
  qstp [] Σ df1 df2 ->
  stp [(bind_ty, false, T3, d3); (bind_tm, true, (TAll d1 d2 T1 T2), {♦})] Σ
      (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv))
      (T4 <~²ᵀ ([] : tenv)) (d4 <~²ᵈ ([] : tenv)) ->
  d1 ⊑↑ df1 ⊔ {♦} ->
  ♦∉ df1 ->
  kill_sep ϰ df2 ->
  kill_sep (local_locs t) df2 ->
  vtp Σ ϰ φ (ttabs t) (TAll d3 d4 T3 T4) df2

| vtp_base: forall Σ ϰ φ d,
  closed_Qual 0 0 (‖Σ‖) d↑ ->
  kill_sep ϰ d ->
  vtp Σ ϰ φ tunit TUnit d

| vtp_loc:  forall Σ ϰ φ l o T U q1 q2 d,
  closed_Qual 0 0 (‖Σ‖) d↑ ->
  closed_ty 0 0 (‖Σ‖) T ->
  closed_Qual 0 0 (‖Σ‖) q1↑ ->
  closed_Qual 0 0 (‖Σ‖) q2↑ ->
  l ∈ₗ φ ->
  sindexr l o Σ = Some (T,q1) ->
  stp [] Σ T ∅ U ∅ ->
  stp [] Σ U ∅ T ∅ ->
  qstp [] Σ (&!l) d ->
  ♦∉ q1 ->
  qstp [] Σ q1 q2 ->
  qstp [] Σ q2 q1 ->
  kill_sep ϰ d ->
  vtp Σ ϰ φ &(l, o) (TRef q2 U) d

| vtp_abs: forall Σ ϰ φ T1 d1 T2 d2 T3 d3 T4 d4 df1 df2 t,
  closed_tm 2 0 (‖Σ‖) t ->
  closed_Qual 0 0 (‖Σ‖) df2↑ ->
  closed_ty 0 0 (‖Σ‖) (TFun d3 d4 T3 T4) ->
  closed_ty 0 0 (‖Σ‖) (TFun d1 d2 T1 T2) ->
  has_type [(bind_tm, false,T1,d1) ; (bind_tm, true, (TFun d1 d2 T1 T2), df1)]
            (df1 ⊔ $!0 ⊔ $!1) Σ (t <~²ᵗ ([] : tenv)) (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv)) ->
  stp [] Σ T3 d3 T1 d1 ->
  qstp [] Σ df1 df2 ->
  stp [(bind_tm, false,T3, d3) ; (bind_tm, true, (TFun d1 d2 T1 T2), {♦})] Σ
      (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv))
      (T4 <~²ᵀ ([] : tenv)) (d4 <~²ᵈ ([] : tenv)) ->
  d1 ⊑↑ df1 ⊔ {♦} ->
  ♦∉ df1 ->
  kill_sep ϰ df2 ->
  kill_sep (local_locs t) df2 ->
  vtp Σ ϰ φ (tabs t) (TFun d3 d4 T3 T4) df2

| vtp_top: forall Σ ϰ φ t T d,
   vtp Σ ϰ φ t T d ->
  vtp Σ ϰ φ t TTop d
.
