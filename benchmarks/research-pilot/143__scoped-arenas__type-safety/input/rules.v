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

Import QualNotations.

Local Open Scope qualifiers.

Import OpeningNotations.

Local Open Scope opening.

Import SplicingNotations.

Local Open Scope splicing.

Import SubstitutionNotations.

Local Open Scope substitutions.

Inductive qstp : tenv -> senv -> qual -> qual -> Prop :=
| qs_sq : forall Γ Σ d1 d2,
    d1 ⊑↑ d2 ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) d2↑ ->
    qstp Γ Σ d1 d2

| qs_self : forall Γ Σ f df T1 d1 T2 d2,
    indexr f Γ = Some ((bind_tm, true, (TFun d1 d2 T1 T2), df)) ->
    closed_Qual 0 f (‖Σ‖) df↑ ->
    ♦∉ df ->
    qstp Γ Σ (df ⊔ $!f) $!f

| qs_self_all : forall Γ Σ f df T1 d1 T2 d2,
    indexr f Γ = Some ((bind_tm, true, (TAll d1 d2 T1 T2), df)) ->
    closed_Qual 0 f (‖Σ‖) df↑ ->
    ♦∉ df ->
    qstp Γ Σ (df ⊔ $!f) $!f

| qs_qvar : forall Γ Σ b U x q1,
    indexr x Γ = Some((bind_tm, b, U, q1)) ->
    closed_ty 0 x (‖Σ‖) U ->
    closed_Qual 0 x (‖Σ‖) q1↑ ->
    ♦∉ q1 ->
    qstp Γ Σ $!x q1

| qs_qvar_ty : forall Γ Σ b U x q1,
    indexr x Γ = Some((bind_ty, b, U, q1)) ->
    closed_ty 0 x (‖Σ‖) U ->
    closed_Qual 0 x (‖Σ‖) q1↑ ->
    ♦∉ q1 ->
    qstp Γ Σ $!x q1

| qs_cong : forall Γ Σ q d1 d2,
    qstp Γ Σ d1 d2 ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) q↑ ->
    qstp Γ Σ (q ⊔ d1) (q ⊔ d2)

| qs_trans : forall Γ Σ d1 d2 d3,
    qstp Γ Σ d1 d2 -> qstp Γ Σ d2 d3 -> qstp Γ Σ d1 d3
.

Inductive stp : tenv -> senv -> ty -> qual -> ty -> qual -> Prop :=
| s_top : forall Γ Σ T d1 d2,
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) T ->
    qstp Γ Σ d1 d2 ->
    stp Γ Σ T d1 TTop d2

| s_tvar_refl: forall Γ Σ x d1 d2 v,
    indexr x Γ = Some v ->
    qstp Γ Σ d1 d2 ->
    stp Γ Σ (TVar (varF x)) d1 (TVar (varF x)) d2

| s_tvar_trans: forall Γ Σ T1 T2 d0 d1 d2 x,
    indexr x Γ = Some((bind_ty, false, T1, d0)) ->
    closed_ty  0 0 (‖ Σ ‖) T1 ->
    stp Γ Σ T1 d1 T2 d2 ->
    stp Γ Σ (TVar (varF x)) d1 T2 d2

| s_all: forall Γ Σ T1 T2 T3 T4 d1 d2 d3 d4 d5 d6,
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) (TAll d1 d2 T1 T2) ->
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) (TAll d3 d4 T3 T4) ->
    qstp Γ Σ d5 d6 ->
    stp Γ Σ T3 d3 T1 d1  ->
    stp ((bind_ty, false, T3, d3) :: (bind_tm, true, TAll d1 d2 T1 T2, {♦}) :: Γ) Σ (open_ty' Γ T2) (openq' Γ d2) (open_ty' Γ T4) (openq' Γ d4) ->
    stp Γ Σ (TAll d1 d2 T1 T2) d5 (TAll d3 d4 T3 T4) d6

| s_base : forall Γ Σ d1 d2,
    qstp Γ Σ d1 d2 ->
    stp Γ Σ TUnit d1 TUnit d2

| s_ref : forall Γ Σ T1 T2 q1 q2 d1 d2,
    qstp Γ Σ d1 d2 ->
    stp Γ Σ T1 ∅ T2 ∅ ->
    stp Γ Σ T2 ∅ T1 ∅ ->
    qstp Γ Σ q1 q2 ->
    qstp Γ Σ q2 q1 ->
    stp Γ Σ (TRef q1 T1) d1 (TRef q2 T2) d2

| s_fun : forall Γ Σ T1 d1 T2 d2 T3 d3 T4 d4 d5 d6,
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) (TFun d1 d2 T1 T2) ->
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) (TFun d3 d4 T3 T4) ->
    qstp Γ Σ d5 d6 ->
    stp Γ Σ T3 d3 T1 d1 ->
    stp ((bind_tm, false, T3,d3) :: (bind_tm, true, TFun d1 d2 T1 T2, {♦}) :: Γ) Σ (open_ty' Γ T2) (openq' Γ d2) (open_ty' Γ T4) (openq' Γ d4) ->
    stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6

| s_trans : forall Γ Σ T1 T2 T3 d1 d2 d3,
    stp Γ Σ T1 d1 T2 d2 -> stp Γ Σ T2 d2 T3 d3 -> stp Γ Σ T1 d1 T3 d3
.

Definition not_free (v : id) (T : ty): Prop := [[ v ~> TUnit ~ ∅ ]]ᵀ T = T.

Fixpoint local_locs (t: tm) : qual :=
  match t with
  | ttabs t  => local_locs t
  | ttapp t  => local_locs t
  | tabs  t  => local_locs t
  | tapp t1 t2  => (local_locs t1) ⊔ (local_locs t2)
  | tref  t  => local_locs t
  | trefat t1 t2 => (local_locs t1) ⊔ (local_locs t2)
  | tderef t  => local_locs t
  | tassign t1 t2  => (local_locs t1) ⊔ (local_locs t2)
  | twithr t1 t2  => (local_locs t1) ⊔ (local_locs t2)
  | twithc l t => &!l ⊔ (local_locs t)
  | _ => ∅
  end.

Inductive has_type : tenv -> qual -> senv -> tm -> ty -> qual -> Prop :=
| t_tabs: forall Γ φ Σ t T1 T2 df d1 d2,
    closed_tm 2 (‖Γ‖) (‖Σ‖) t ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) (TAll d1 d2 T1 T2) ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    d1 ⊑↑ df ⊔ {♦} ->
    df ⊑↑ φ ->
    ♦∉ df ->
    kill_sep (local_locs t) df ->
    has_type ((bind_ty, false, T1, d1)  :: (bind_tm, true, (TAll d1 d2 T1 T2), df) :: Γ)
             (df ⊔ ($!‖Γ‖) ⊔ $!(S (‖Γ‖))) Σ (t <~²ᵗ Γ) (T2 <~²ᵀ Γ) (d2 <~²ᵈ Γ) ->
    has_type Γ φ Σ (ttabs t) (TAll d1 d2 T1 T2) df

| t_tapp: forall Γ φ Σ t T1 T2 d1 d2 df,
    has_type Γ φ Σ t (TAll d1 d2 T1 T2) df ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T1 ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) d1↑ ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    ♦∉ d1 ->
    d1 ⊑↑ φ ->
    not_free 0 T2 ->
    kill_sep (local_locs t) d1 ->
    kill_sep (local_locs t) (d2) ->
    has_type Γ φ Σ (ttapp t) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_tapp_fresh : forall Γ φ Σ t d1 d2 df T1 T2,
    has_type Γ φ Σ t (TAll (q_trans_tenv Γ df ⋒ q_trans_tenv Γ d1) d2 T1 T2) df ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T1 ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) d1↑ ->
    d1 ⊑↑ (φ ⊔ {♦}) ->
    (♦∈ d1 -> not_free 1 T2) ->
    not_free 0 T2 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    (q_trans_tenv Γ d1) ⋒ (q_trans_tenv Γ df) ⊑↑ (φ ⊔ {♦}) ->
    kill_sep (local_locs t) d1 ->
    kill_sep (local_locs t) (d2) ->
    kill_sep (local_locs t) ((q_trans_tenv Γ d1) ⋒ (q_trans_tenv Γ df)) ->
    has_type Γ φ Σ (ttapp t) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_base : forall Γ Σ φ,
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    has_type Γ φ Σ tunit TUnit ∅

| t_var : forall Γ φ Σ x b T d,
    indexr x Γ = Some ((bind_tm, b,T,d)) ->
    $!x ⊑↑ φ ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    closed_ty   0 x (‖Σ‖) T ->
    closed_Qual 0 x (‖Σ‖) d↑ ->
    has_type Γ φ Σ $x T $!x

| t_abs: forall Γ φ Σ T1 d1 T2 d2 df t,
    closed_tm   2 (‖Γ‖) (‖Σ‖) t ->
    closed_ty   0 (‖Γ‖) (‖Σ‖) (TFun d1 d2 T1 T2) ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    d1 ⊑↑ df ⊔ {♦} ->
    df ⊑↑ φ ->
    ♦∉ df ->
    kill_sep (local_locs t) df ->
    has_type ((bind_tm, false, T1, d1) :: (bind_tm, true, (TFun d1 d2 T1 T2), df) :: Γ)
             (df ⊔ ($!‖Γ‖) ⊔ $!(S (‖Γ‖))) Σ (t <~²ᵗ Γ) (T2 <~²ᵀ Γ) (d2 <~²ᵈ Γ) ->
    has_type Γ φ Σ (tabs t) (TFun d1 d2 T1 T2) df

| t_app : forall Γ φ φd Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun d1 d2 T1 T2) df ->
    has_type Γ φd Σ t2 T1 d1 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    ♦∉ d1 ->
    not_free 0 T2 ->
    (qdiff φ (local_locs t1)) = φd ->
    kill_sep (local_locs t2) (df) ->
    kill_sep (local_locs t1 ⊔ local_locs t2) (d2) ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_app_fresh : forall Γ φ φd Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun (q_trans_tenv Γ df ⋒ q_trans_tenv Γ d1) d2 T1 T2) df ->
    has_type Γ φd Σ t2 T1 d1 ->
    (♦∈ d1 -> not_free 1 T2) ->
    not_free 0 T2 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    (q_trans_tenv Γ d1) ⋒ (q_trans_tenv Γ df) ⊑↑ (φ ⊔ {♦}) ->
    (qdiff φ (local_locs t1)) = φd ->
    kill_sep (local_locs t2) (df) ->
    kill_sep (local_locs t1 ⊔ local_locs t2) (d2) ->
    kill_sep (local_locs t1) ((q_trans_tenv Γ d1) ⋒ (q_trans_tenv Γ df)) ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_loc : forall Γ φ Σ l o T q,
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    sindexr l o Σ = Some (T,q) ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    &!l ⊑↑ φ ->
    ♦∉ q ->

    has_type Γ φ Σ &(l,o) (TRef q T) (&!l)

| t_ref: forall Γ φ Σ T t d1,
    has_type Γ φ Σ t T d1 ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tref t) (TRef d1 T) ({♦})

| t_refat : forall Γ φ φd Σ t1 t2 T d T1 d1 d2,
    has_type Γ φd Σ t1 T d ->
    ♦∉ d ->
    has_type Γ φ Σ (t2) (TRef d1 T1) (d2) ->
    (qdiff φ (local_locs t2)) = φd ->
    kill_sep (local_locs t1) (d2) ->
    has_type Γ φ Σ (trefat t1 t2) (TRef (d) T) (d2)

| t_deref: forall Γ φ Σ T d d1 t,
    has_type Γ φ Σ t (TRef d1 T) d ->
    ♦∉ d1 ->
    d1 ⊑↑ φ ->





    kill_sep (local_locs t) d1 ->
    has_type Γ φ Σ !t T d1

| t_assign: forall Γ φ φd Σ T t1 d d1 t2,
    has_type Γ φ Σ t1 (TRef d1 T) d ->
    has_type Γ φd Σ t2 T d1 ->
    ♦∉ d1 ->
    (qdiff φ (local_locs t1)) = φd ->
    kill_sep (local_locs t2) (d) ->
    has_type Γ φ Σ (tassign t1 t2) TUnit ∅

| t_sub: forall Γ φ Σ e T1 d1 T2 d2,
    has_type Γ φ Σ e T1 d1 ->
    stp Γ Σ T1 d1 T2 d2 ->
    d2 ⊑↑ (φ ⊔ {♦}) ->
    kill_sep (local_locs e) d2 ->
    has_type Γ φ Σ e T2 d2

| t_withr : forall Γ φ φd Σ t1 t2 T1 d1 T2 d2,
    has_type Γ φ Σ t1 T1 d1 ->
    ♦∉ d1 ->



    closed_ty 0 (‖Γ‖) (‖Σ‖) T2 ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) d2↑ ->
    closed_tm 2 (‖Γ‖) (‖Σ‖) t2 ->
    has_type ((bind_tm, false, TRef d1 T1, {♦}) :: (bind_tm, true, TUnit, {♦}) :: Γ)
      (φd ⊔ $!(S (‖Γ‖))) Σ (t2 <~²ᵗ Γ) (T2) (d2) ->
    φd ⊑↑ φ ->
    kill_sep (local_locs t1) φd ->
    has_type Γ φ Σ (twithr t1 t2) T2 d2


| t_withc : forall Γ φ Σ l t T d,
    l < ‖Σ‖ ->
    has_type Γ (φ) Σ t T d ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) d↑ ->
    kill_sep &!l d ->
    has_type Γ φ Σ (twithc l t) T d
.

Inductive value : tm -> Prop :=
| value_ttabs: forall t, value (ttabs t)
| value_abs : forall t, value (tabs t)
| value_cst : value tunit
| value_loc : forall l o, value &(l, o)
.

Definition store := list (option (list (tm))).

Inductive step : tm -> store -> tm -> store -> Prop :=

| step_ttapp: forall t σ,
  step (ttapp (ttabs t)) σ (t <~ᵗ (ttabs t); tunit) σ
| step_beta : forall t v σ,
    value v ->
    step (tapp (tabs t) v) σ (t <~ᵗ (tabs t); v) σ
| step_ref : forall v σ,
    value v ->
    step (tref v) σ (&‖σ‖) ((Some [v]) :: σ)
| step_refat: forall v l o s σ,
    value v ->
    indexr l σ = Some (Some s) ->

    step (trefat v &(l, o)) σ &(l, ‖s‖) (cinsert σ l (v))
| step_deref : forall σ l o s v,
    indexr l σ = Some (Some s) ->
    indexr o s = Some (v) ->
    step (! &(l, o)) σ v σ
| step_assign : forall σ l o v s,
    l < ‖σ‖ ->
    indexr l σ = Some (Some s) ->
    o < ‖s‖ ->
    value v ->
    step (tassign &(l, o) v) σ tunit (supdate σ l o v)
| step_twithr : forall σ v t,
    value v ->
    step (twithr v t) σ (twithc (‖σ‖) (t <~ᵗ tunit; (&‖σ‖))) ((Some [v]) :: σ)
| step_twithc : forall σ v l,
    value v ->
    step (twithc l v) σ v (update σ l None)

| step_c_tapp: forall t t' σ σ',
  step t σ t' σ' ->
  step (ttapp t)  σ (ttapp t') σ'
| step_c_ref : forall t t' σ σ',
    step t σ t' σ' ->
    step (tref t) σ (tref t') σ'
| step_c_refat_l : forall t1 t1' t2 σ σ',
    value t2 ->
    step t1 σ t1' σ' ->
    step (trefat t1 t2) σ (trefat t1' t2) σ'
| step_c_refat_r : forall t1 t2 t2' σ σ',
    step t2 σ t2' σ' ->
    step (trefat t1 t2) σ (trefat t1 t2') σ'
| step_c_deref : forall t t' σ σ',
    step t σ t' σ' ->
    step !t σ !t' σ'
| step_c_app_l : forall t1 t1' t2 σ σ',
    step t1 σ t1' σ' ->
    step (tapp t1 t2) σ (tapp t1' t2) σ'
| step_c_app_r : forall v t2 t2' σ σ',
    value v ->
    step t2 σ t2' σ' ->
    step (tapp v t2) σ (tapp v t2') σ'
| step_c_assign_l : forall t1 t1' t2 σ σ',
    step t1 σ t1' σ' ->
    step (tassign t1 t2) σ (tassign t1' t2) σ'
| step_c_assign_r : forall v t2 t2' σ σ',
    value v ->
    step t2 σ t2' σ' ->
    step (tassign v t2) σ (tassign v t2') σ'
| step_c_twithr_l : forall t1 t2 t1' σ σ',
  step t1 σ t1' σ' ->
  step (twithr t1 t2) σ (twithr t1' t2) σ'
| step_c_twithc : forall l t t' σ σ',
  step t σ t' σ' ->
  step (twithc l t) σ (twithc l t') σ'
.

Definition relation (X : Type)(Y: Type) := X -> Y -> X ->  Y -> Prop.

Definition deterministic {X : Type}{Y: Type} (R : relation X Y) :=
  forall (x x1 x2 : X) (y y1 y2: Y), R x y x1 y1 -> R x y x2 y2 -> x1 = x2 /\ y1 = y2.

Local Open Scope splicing.

Local Open Scope substitutions.

Inductive Substq : tenv -> senv -> qual -> qual -> Prop :=
| SExact : forall Γ Σ df,    ♦∉ df -> Substq Γ Σ df df
| SGrow  : forall Γ Σ df dx,
    ♦∉ dx ->
    closed_Qual 0 (‖ Γ ‖) (‖ Σ ‖) df ↑ ->
    Substq Γ Σ (q_trans_tenv Γ df ⋒ q_trans_tenv Γ dx) dx
.

Definition tph := tunit.

Definition root' (c : option (list tm)) : (option tm) :=
  match c with
  | None => None
  | Some (s) => match indexr 0 s with
                | None => Some tph
                | Some x => Some x
                end
  end.

Definition squish' (σ : store) : list (option tm) := map (root') σ.

Definition indexr' {X : Type} (n : nat) (l : option (list X)) : option X :=
  match l with
    | None => None
    | Some c => indexr n c
  end.

Fixpoint sindexr' {X : Type} (l : loc) (o : offset) (σ : list (option (list X))) : option X :=
  match σ with
    | [] => None
    | a :: σ' =>
      if (Nat.eqb l (length σ')) then indexr' o a else sindexr' l o σ'
  end.
