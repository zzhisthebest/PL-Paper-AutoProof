Require Export Arith.EqNat.

From Stdlib Require Export PeanoNat.

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

Definition not_free (v : id) (T : ty): Prop := [[ v ~> TUnit ~ ∅ ]]ᵀ T = T.

Inductive stp : tenv -> senv -> ty -> qual -> ty -> qual -> Prop :=
| s_bot : forall Γ Σ T d1 d2,
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) T ->
    qstp Γ Σ d1 d2 ->
    stp Γ Σ TBot d1 T d2

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
    stp ((bind_ty, false, T3, d3) :: (bind_tm, true, TAll d1 d2 T1 T2, {♦}) :: Γ) Σ  (open_ty' Γ T2) (openq' Γ d2) (open_ty' Γ T4) (openq' Γ d4) ->
    stp Γ Σ (TAll d1 d2 T1 T2) d5 (TAll d3 d4 T3 T4) d6

| s_base : forall Γ Σ d1 d2,
    qstp Γ Σ d1 d2 ->
    stp Γ Σ TUnit d1 TUnit d2

| s_ref : forall Γ Σ T1 T2 q1 q2 d1 d2,
    qstp Γ Σ d1 d2 ->
    stp Γ Σ T1 ∅ T2 ∅ ->
    stp Γ Σ T2 ∅ T1 ∅ ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) q1 ↑ ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) q2 ↑ ->
    qstp Γ Σ q1 q2 ->
    qstp Γ Σ q2 q1 ->
    stp Γ Σ (TRef q1 T1) d1 (TRef q2 T2) d2

| s_sref : forall Γ Σ T1 T2 U1 U2 q1 q2 p1 p2 d1 d2,
    qstp Γ Σ d1 d2 ->
    stp Γ Σ U1 ∅ T1 ∅ ->
    stp Γ Σ T2 ∅ U2 ∅ ->
    closed_Qual 1 (‖Γ‖) (‖Σ‖) q1 ↑ ->
    closed_Qual 1 (‖Γ‖) (‖Σ‖) p2 ↑ ->
    qstp Γ Σ ([[0 ~> ∅ ]]ᵈ p1) ([[0 ~> ∅ ]]ᵈ q1) ->
    n_sub (qbvs p1) (qbvs q1) ->
    qstp Γ Σ ([[0 ~> ∅ ]]ᵈ q2) ([[0 ~> ∅ ]]ᵈ p2) ->
    n_sub (qbvs q2) (qbvs p2) ->
    stp Γ Σ (TSRef q1 T1 q2 T2) d1 (TSRef p1 U1 p2 U2) d2

| s_fun : forall Γ Σ T1 d1 T2 d2 T3 d3 T4 d4 d5 d6,
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) (TFun d1 d2 T1 T2) ->
    closed_ty 0 (‖ Γ ‖) (‖ Σ ‖) (TFun d3 d4 T3 T4) ->
    qstp Γ Σ d5 d6 ->
    stp Γ Σ T3 d3 T1 d1 ->
    stp ((bind_tm, false, T3,d3) :: (bind_tm, true, TFun d1 d2 T1 T2, {♦}) :: Γ) Σ (open_ty' Γ T2) (openq' Γ d2) (open_ty' Γ T4) (openq' Γ d4) ->
    (not_free 1 T2 <-> not_free 1 T4) ->
    stp Γ Σ (TFun d1 d2 T1 T2) d5 (TFun d3 d4 T3 T4) d6

| s_trans : forall Γ Σ T1 T2 T3 d1 d2 d3,
    stp Γ Σ T1 d1 T2 d2 -> stp Γ Σ T2 d2 T3 d3 -> stp Γ Σ T1 d1 T3 d3

| s_int : forall Γ Σ d1 d2,
    qstp Γ Σ d1 d2 ->
    stp Γ Σ TInt d1 TInt d2

| s_bool : forall Γ Σ d1 d2,
    qstp Γ Σ d1 d2 ->
    stp Γ Σ TBool d1 TBool d2
.

Inductive saturated_var (Γ : tenv) (Σ : senv) (x : id) (q : qual) : Prop :=
| sat_var : forall b U q',
    indexr x Γ = Some ((bind_tm, b, U, q')) ->
    q' ⊑↑ q ->
    closed_Qual 0 x (‖Σ‖) q' ↑ ->
    saturated_var Γ Σ x q
| sat_tvar : forall b U q',
    indexr x Γ = Some ((bind_ty, b, U, q')) ->
    q' ⊑↑ q ->
    closed_Qual 0 x (‖Σ‖) q' ↑ ->
    saturated_var Γ Σ x q.

Arguments sat_var {Γ Σ x q}.

Arguments sat_tvar {Γ Σ x q}.

Inductive saturated_loc (Σ : senv) (l : id) (q : qual) : Prop :=
| sat_loc : forall U q',
    indexr l Σ = Some (U, q') ->
    q' ⊑↑ q ->
    closed_Qual 0 0 l q' ↑ ->
    saturated_loc Σ l q.

Arguments sat_loc {Σ l q}.

Definition q_trans_tenv (Γ : tenv) (q : qual) := q_trans'' Γ q (‖Γ‖).

Definition q_trans_senv (Σ : senv) (q : qual) := q_trans'' Σ q (‖Σ‖).

Definition q_trans (Γ : tenv) (Σ : senv) (q : qual) := (q_trans_senv Σ (q_trans_tenv Γ q)).

Definition Q_trans_one {p : Type} `{qenv p} (E : env p) (q : Qual) : Qual :=
  (N_trans_one E q Qfr 0, N_trans_one E q qfvs, N_trans_one E q qbvs, N_trans_one E q qlocs).

Definition Q_trans'' {p : Type} `{qenv p} (E : env p) (q : Qual) (fuel : nat) : Qual :=
  (N_trans'' E q Qfr fuel 0, N_trans'' E q qfvs fuel, N_trans'' E q qbvs fuel, N_trans'' E q qlocs fuel).

Definition Q_trans (Γ : tenv) (Σ : senv) (q : Qual) := (Q_trans'' Σ (Q_trans'' Γ q (‖Γ‖)) (‖Σ‖)).

Definition qenv_saturated_q {p : Type} `{qenv p} (E : env p) (q : qual) :=
  forall x a,
  qenv_Qn q↑ x ->
  indexr x E = Some a ->
  (qenv_q a) ⊑↑ q.

Definition qenv_saturated_q'' {p : Type} `{qenv p} (E : env p) (q : qual) :=
  q_trans_one E q = q.

Definition tenv_saturated (Γ : tenv) (q: qual) := qenv_saturated_q Γ q.

Definition senv_saturated (Σ : senv) (q: qual) := qenv_saturated_q Σ q.

Definition saturated (Γ : tenv) (Σ : senv) (q: qual) := tenv_saturated Γ q /\ senv_saturated Σ q.

Fixpoint cardinality (q : qual) {p : Type} `{qenv p} (E : env p) : nat :=
  match E with
  | [] => 0
  | a :: E' => if qenv_qn q (‖ E' ‖) then S (cardinality q E') else cardinality q E'
  end.

Inductive value : tm -> Prop :=
| value_ttabs: forall t, value (ttabs t)
| value_abs : forall t, value (tabs t)
| value_cst : value tunit
| value_loc : forall l, value &l
| value_nat : forall c, value (tnat c)
| value_bool : forall c, value (tbool c)
.

Inductive vl : senv -> tm -> ty -> qual -> Prop :=
| vl_loc:  forall Σ l T q,
  vl Σ &l (TRef q T) &!l
| vl_sloc:  forall Σ l T1 q1 T2 q2,
  vl Σ &l (TSRef q1 T1 q2 T2) &!l
| vl_top: forall Σ l d,
  vl Σ &l TTop d
| vl_store: forall Σ l T1 q1 T2 q2 T q q',
  closed_Qual 1 0 l q ↑ ->
  indexr l Σ = Some (true,T,q) ->



  q' ⊑↑ q ->
  vl Σ &l (TSRef q1 T1 q2 T2) (&!l ⊔ [[0 ~> ∅ ]]ᵈ q')
.

Inductive has_type : tenv -> qual -> senv -> tm -> ty -> qual -> Prop :=
| t_tabs: forall Γ φ Σ t T1 T2 df d1 d2,
    closed_tm 2 (‖Γ‖) (‖Σ‖) t ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) (TAll d1 d2 T1 T2) ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    d1 ⊑↑ df ⊔ {♦} ->
    df ⊑↑ φ ->
    ♦∉ df ->
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
    has_type ((bind_tm, false, T1, d1) :: (bind_tm, true, (TFun d1 d2 T1 T2), df) :: Γ)
             (df ⊔ ($!‖Γ‖) ⊔ $!(S (‖Γ‖))) Σ (t <~²ᵗ Γ) (T2 <~²ᵀ Γ) (d2 <~²ᵈ Γ) ->
    has_type Γ φ Σ (tabs t) (TFun d1 d2 T1 T2) df

| t_app_empty : forall Γ φ Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun d1 d2 T1 T2) df ->
    has_type Γ φ Σ t2 T1 d1 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    d1 = ∅ ->
    ♦∉ d1 ->
    not_free 0 T2 ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_app_var : forall Γ φ Σ f t1 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun $!f d2 T1 T2) df ->
    has_type Γ φ Σ $ f T1 $! f ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->

    not_free 0 T2 ->
    has_type Γ φ Σ (tapp t1 $f) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ $!f) (d2 <~ᵈ df ; $!f)

| t_app_val : forall Γ φ Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun d1 d2 T1 T2) df ->
    value t2 ->
    (forall l, t2 = &l -> vl Σ t2 T1 d1) ->
    has_type Γ φ Σ t2 T1 d1 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    ♦∉ d1 ->
    not_free 0 T2 ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)


| t_app : forall Γ φ Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun d1 d2 T1 T2) df ->
    has_type Γ φ Σ t2 T1 d1 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    ♦∉ d1 ->
    not_free 0 T2 ->
    not_free 1 T2 ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_app_fresh : forall Γ φ Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun (q_trans_tenv Γ df ⋒ q_trans_tenv Γ d1) d2 T1 T2) df ->
    has_type Γ φ Σ t2 T1 d1 ->
    (♦∈ d1 -> not_free 1 T2) ->
    not_free 0 T2 ->
    not_free 1 T2 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    (q_trans_tenv Γ d1) ⋒ (q_trans_tenv Γ df) ⊑↑ (φ ⊔ {♦}) ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_loc : forall Γ φ Σ l T q,
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    indexr l Σ = Some (false,T,q) ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    &!l ⊑↑ φ ->
    ♦∉ q ->
    has_type Γ φ Σ &l (TRef q T) &!l

| t_sloc : forall Γ φ Σ l T q,
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    indexr l Σ = Some (true,T,q) ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 1 0 (‖Σ‖) q↑ ->
    &!l ⊑↑ φ ->
    ♦∉ q ->
    has_type Γ φ Σ &l (TSRef q T q T) &!l

| t_ref: forall Γ φ Σ T t d1,
    has_type Γ φ Σ t T d1 ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tref t) (TRef d1 T) ({♦})

| t_sref: forall Γ φ Σ T t d1,
    has_type Γ φ Σ t T ([[0 ~> ∅ ]]ᵈ d1) ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tsref t) (TSRef d1 T d1 T) ({♦})

| t_esc: forall Γ φ Σ T1 T2 t d1 d2 d d1' d2' d',
    qstp Γ Σ ([[0 ~> ∅ ]]ᵈ d1') ([[0 ~> ∅ ]]ᵈ d1) ->
    n_sub (qbvs d1') (qbvs d1) ->
    qstp Γ Σ ([[0 ~> ∅ ]]ᵈ d2 ⊔ d) ([[0 ~> ∅ ]]ᵈ d2' ⊔ d') ->
    qstp Γ Σ d d' ->
    d' ⊑↑ φ ⊔ {♦} ->
    has_type Γ φ Σ t (TSRef d1 T1 d2 T2) d ->
    has_type Γ φ Σ t (TSRef d1' T1 (d2' ⊔ #!0) T2) d'

| t_deref: forall Γ φ Σ T d d1 t,
    has_type Γ φ Σ t (TRef d1 T) d ->
    ♦∉ d1 ->
    d1 ⊑↑ φ ->
    has_type Γ φ Σ !t T d1

| t_sderef: forall Γ φ Σ T1 T2 d d1 d2 t,
		has_type Γ φ Σ t (TSRef d1 T1 d2 T2) d ->
		♦∉ d2 ->
		([[0 ~> d]]ᵈ d2) ⊑↑ φ ⊔ {♦} ->
		has_type Γ φ Σ !t T2 ([[0 ~> d]]ᵈ d2)

| t_assign: forall Γ φ Σ T t1 d d1 t2,
    has_type Γ φ Σ t1 (TRef d1 T) d ->
    has_type Γ φ Σ t2 T d1 ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tassign t1 t2) TUnit ∅


| t_sassign: forall Γ φ Σ T1 T2 t1 d d1 d2 t2,
    has_type Γ φ Σ t1 (TSRef d1 T1 d2 T2) d ->
    has_type Γ φ Σ t2 T1 ([[0 ~> ∅]]ᵈ d1) ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tassign t1 t2) TUnit ∅

| t_sassign_v: forall Γ φ Σ T1 T2 f d d1 d2 t2,
    has_type Γ φ Σ (tvar (varF f)) (TSRef d1 T1 d2 T2) d ->
    has_type Γ φ Σ t2 T1 ([[0 ~> $!f ]]ᵈ d1) ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tassign (tvar (varF f)) t2) TUnit ∅

| t_sassign_l: forall Γ φ Σ T1 T2 l d d1 d2 t2,
    has_type Γ φ Σ (tloc l) (TSRef d1 T1 d2 T2) d ->
    has_type Γ φ Σ t2 T1 ([[0 ~> &!l ]]ᵈ d1) ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tassign (tloc l) t2) TUnit ∅

| t_sassign_ql: forall Γ φ Σ T q q' T1 T2 l d d1 d2 t2,
    has_type Γ φ Σ (tloc l) (TSRef d1 T1 d2 T2) d ->
    indexr l Σ = Some (true,T,q) ->
    q' ⊑↑ q ->
    has_type Γ φ Σ t2 T1 ([[0 ~> &!l ⊔ [[0 ~> ∅ ]]ᵈ q' ]]ᵈ d1) ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tassign (tloc l) t2) TUnit ∅

| t_sub: forall Γ φ  Σ e T1 d1 T2 d2,
    has_type Γ φ Σ e T1 d1 ->
    stp Γ Σ T1 d1 T2 d2 ->
    d2 ⊑↑ (φ ⊔ {♦}) ->
    has_type Γ φ Σ e T2 d2

| t_nat : forall Γ φ Σ c,
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    has_type Γ φ Σ (tnat c) TInt ∅




| t_succ : forall Γ φ Σ t q,
    has_type Γ φ Σ t TInt q ->
    has_type Γ φ Σ (tsucc t) TInt ∅

| t_mul : forall Γ φ Σ t1 t2 q1 q2,
    has_type Γ φ Σ t1 TInt q1 ->
    has_type Γ φ Σ t2 TInt q2 ->
    has_type Γ φ Σ (tmul t1 t2) TInt ∅

| t_pred : forall Γ φ Σ t q,
    has_type Γ φ Σ t TInt q ->
    has_type Γ φ Σ (tpred t) TInt ∅

| t_iszero : forall Γ φ Σ t q,
    has_type Γ φ Σ t TInt q ->
    has_type Γ φ Σ (tiszero t) TBool ∅

| t_bool : forall Γ φ Σ c,
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    has_type Γ φ Σ (tbool c) TBool ∅

| t_if : forall Γ φ Σ t1 t2 t3 T q1 q2 q3,
    has_type Γ φ Σ t1 TBool q1 ->
    has_type Γ φ Σ t2 T q2 ->
    has_type Γ φ Σ t3 T q3 ->
    has_type Γ φ Σ (tif t1 t2 t3) T (q2 ⊔ q3)
.

Definition store := list (option tm).

Inductive step : tm -> store -> tm -> store -> Prop :=

| step_ttapp: forall t σ,
  step (ttapp (ttabs t)) σ (t <~ᵗ (ttabs t); tunit) σ
| step_beta : forall t v σ,
    value v ->
    step (tapp (tabs t) v) σ (t <~ᵗ (tabs t); v) σ
| step_ref : forall v σ,
    value v ->
    step (tref v) σ (&‖σ‖) ((Some v) :: σ)
| step_sref : forall v σ,
    value v ->
    step (tsref v) σ (&‖σ‖) ((Some v) :: σ)
| step_deref : forall σ l v,
    indexr l σ = Some (Some v) ->
    step (! &l) σ v σ
| step_assign : forall σ l v,
    l < ‖σ‖ ->
    value v ->
    step (tassign &l v) σ tunit (update σ l (Some v))
| step_succ : forall σ n,
    step (tsucc (tnat n)) σ (tnat (S n)) σ
| step_mul : forall σ n1 n2,
    step (tmul (tnat n1) (tnat n2)) σ (tnat (n1 * n2)) σ
| step_pred : forall σ n,

    step (tpred (tnat n)) σ (tnat (pred n)) σ
| step_iszero : forall σ n,
    step (tiszero (tnat n)) σ (if n =? 0 then (tbool true) else (tbool false)) σ
| step_if_true : forall σ t1 t2,
    step (tif (tbool true) t1 t2) σ t1 σ
| step_if_false : forall σ t1 t2,
    step (tif (tbool false) t1 t2) σ t2 σ

| step_c_tapp: forall t t' σ σ',
  step t σ t' σ' ->
  step (ttapp t)  σ (ttapp t') σ'
| step_c_sref : forall t t' σ σ',
    step t σ t' σ' ->
    step (tsref t) σ (tsref t') σ'
| step_c_ref : forall t t' σ σ',
    step t σ t' σ' ->
    step (tref t) σ (tref t') σ'
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
| step_c_succ : forall t t' σ σ',
    step t σ t' σ' ->
    step (tsucc t) σ (tsucc t') σ'
| step_c_mul_l : forall t1 t1' t2 σ σ',
    step t1 σ t1' σ' ->
    step (tmul t1 t2) σ (tmul t1' t2) σ'
| step_c_mul_r : forall v1 t2 t2' σ σ',
    value v1 ->
    step t2 σ t2' σ' ->
    step (tmul v1 t2) σ (tmul v1 t2') σ'
| step_c_pred : forall t t' σ σ',
    step t σ t' σ' ->
    step (tpred t) σ (tpred t') σ'
| step_c_iszero : forall t t' σ σ',
    step t σ t' σ' ->
    step (tiszero t) σ (tiszero t') σ'
| step_c_if : forall t t' t1 t2 σ σ',
    step t σ t' σ' ->
    step (tif t t1 t2) σ (tif t' t1 t2) σ'
.

Definition CtxOK (Γ : tenv) (φ : qual) (Σ : senv) (σ : store) : Prop :=
  qdom' σ ⊑↑ qdom Σ /\ ‖ σ ‖ = ‖ Σ ‖ /\
  φ ⊑↑ (qdom' σ) /\
  forall b l v T q,
  l ∈ₗ φ ->
  indexr l Σ = Some (b,T,q) ->
  indexr l σ = Some (Some v) ->
  value v /\
  (b = false -> has_type Γ (φ ⊔ q) Σ v T q) /\
  (b = true -> has_type Γ (φ ⊔ ([[0 ~> &!l ]]ᵈ q)) Σ v T ([[0 ~> &!l ]]ᵈ q)).

Inductive disjointq (Σ Σ' : senv) : qual -> qual -> Prop :=
| disj_bot : forall q,
    disjointq Σ Σ' q ∅
| disj_loc : forall b T q q',

    closed_ty 0 0 (‖Σ‖) T ->
    (b = true -> closed_Qual 1 0 (‖Σ‖) q↑) ->
    (b = false -> closed_Qual 0 0 (‖Σ‖) q↑) ->
    ♦∉ q ->
    Σ' = (b,T,q) :: Σ ->
    disjointq Σ Σ' q' (&!‖Σ‖)
.

Arguments disj_loc { Σ Σ' }.

Notation " S → T ∋ q ⊕ q'" := (disjointq S T q q') (at level 10).

Inductive preserve (Γ : tenv) (Σ : senv) (φ : qual) (t' : tm) (T : ty) (d : qual) (σ σ' : store) : Prop :=
| Preserve : forall Σ' d' φ',
    Σ' ⊇ Σ ->
    φ ⊑↑ φ' ->
    d' ⊑↑ φ' ->
    wf_senv Σ' ->
    CtxOK Γ φ' Σ' σ' ->
    Σ → Σ' ∋ d ⊕ d'  ->
    qdom' σ ⊑↑ qdom' σ' ->
    has_type Γ φ' Σ' t' T (d ⋓ d') ->
    preserve Γ Σ φ t' T d σ σ'.

Arguments Preserve {Γ Σ φ t' T d σ σ'}.

Theorem type_safety: forall {Σ t T d φ},
  has_type [] φ Σ t T d -> wf_senv Σ -> (
    value t \/
    (forall {σ} , CtxOK [] φ Σ σ ->
      (exists t' σ',
        step t σ t' σ' /\ preserve [] Σ φ t' T d σ σ'
      )
    )
  ).
