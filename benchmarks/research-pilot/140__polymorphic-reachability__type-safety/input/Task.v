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

Import QualNotations.

Local Open Scope qualifiers.

Inductive ty : Type :=
| TTop  : ty
| TVar  : var -> ty
| TAll  : qual -> qual -> ty ->  ty -> ty
| TUnit : ty
| TFun  : qual -> qual -> ty -> ty -> ty
| TRef  : qual -> ty -> ty
.

Inductive tm : Type :=
| ttabs   :   tm -> tm
| ttapp   : tm ->   tm
| tunit   : tm
| tvar    : var -> tm
| tabs    : tm  -> tm
| tapp    : tm  -> tm -> tm
| tloc    : loc -> tm
| tref    : tm  -> tm
| tderef  : tm  -> tm
| tassign : tm  -> tm -> tm
.

Notation "& l"   := (tloc l) (at level 0, right associativity).

Notation "! t"   := (tderef t) (at level 0, right associativity).

Coercion tvar : var >-> tm.

Coercion TVar : var >-> ty.

Inductive binding :=
| bind_tm : binding
| bind_ty : binding
.

Definition extends {A} (l1 l2 : list A): Prop := exists l', l1 = l' ++ l2.

Notation "x ⊇ y" := (extends x y) (at level 75).

Notation "‖ x ‖" := (length x) (at level 10).

Fixpoint open_rec_tm (k : nat) (u : tm) (t : tm) {struct t} : tm :=
  match t with
  | ttabs   t => ttabs   (open_rec_tm (S (S k)) u t)
  | ttapp t   => ttapp (open_rec_tm k u t)
  | tunit            => tunit
  | tvar   (varF x) => tvar (varF x)
  | tvar   (varB x) => if Nat.eqb k x then u else tvar (varB x)
  | tabs    t       => tabs    (open_rec_tm (S (S k)) u t)
  | tapp    t1 t2   => tapp    (open_rec_tm k u t1) (open_rec_tm k u t2)
  | tloc    l       => tloc l
  | tref    t       => tref    (open_rec_tm k u t)
  | tderef  t       => tderef  (open_rec_tm k u t)
  | tassign t1 t2   => tassign (open_rec_tm k u t1) (open_rec_tm k u t2)
  end
.

Definition open_tm (u u' t : tm) := open_rec_tm 1 u' (open_rec_tm 0 u t).

Definition open_tm' {A : Type} (env : list A) t := open_rec_tm 1 $(S (‖ env ‖)) (open_rec_tm 0 ($‖env‖) t).

Definition openq (u u' q : qual) : qual := open_qual 1 u' (open_qual 0 u q).

Definition openq' {A} (env : list A) q  := openq ($!‖env‖) $!(S (‖env‖)) q.

Fixpoint open_rec_ty (k : nat)(U:  ty) (d' : qual) (T : ty) : ty :=
  match T with
  | TTop              => TTop
  | TVar (varF x)     => TVar (varF x)
  | TVar (varB x)     => if Nat.eqb k x then U else (TVar (varB x))
  | TAll d1 d2 T1 T2  => TAll (open_qual k d' d1) (open_qual (S (S k)) d' d2) (open_rec_ty k U d' T1) (open_rec_ty (S (S k)) U d' T2)
  | TUnit             => TUnit
  | TFun d1 d2 T1 T2  => TFun (open_qual k d' d1) (open_qual (S (S k)) d' d2) (open_rec_ty k U d' T1) (open_rec_ty (S (S k)) U d' T2)
  | TRef d T          => TRef (open_qual k d' d) (open_rec_ty k U d' T)
  end.

Definition open_ty (U : ty)(du : qual)(V : ty)(dv : qual) (T : ty) : ty := (open_rec_ty 1 V dv  (open_rec_ty 0 U du T)).

Definition open_ty' {A : Type} (env : list A) (T : ty) :=
  open_ty  (TVar $(‖env‖)) ($!‖env‖) (TVar $(S (‖env‖))) ($!( S (‖env‖))) T.

Module OpeningNotations.

Declare Scope opening.

Notation "[[ k ~> u ]]ᵗ t"       := (open_rec_tm k u t) (at level 10) : opening.

Notation "[[ k ~> U ~ d ]]ᵀ T"   := (open_rec_ty k U d T) (at level 10) : opening.

Notation "[[ k ~> q' ]]ᵈ q"      := (open_qual k q' q) (at level 10) : opening.

Notation "t <~ᵗ q ; q'"          := (open_tm q q' t) (at level 10, q at next level) : opening.

Notation "T <~ᵀ U ~ du ; V ~ dv" := (open_ty U du V dv  T) (at level 10, U, du at next level) : opening.

Notation "q <~ᵈ q' ; q''"        := (openq q' q'' q) (at level 10, q' at next level) : opening.

Notation "t <~²ᵗ g"              := (open_tm' g t) (at level 10) : opening.

Notation "T <~²ᵀ g"              := (open_ty' g T) (at level 10) : opening.

Notation "q <~²ᵈ g"              := (openq' g q) (at level 10) : opening.

End OpeningNotations.

Import OpeningNotations.

Local Open Scope opening.

Fixpoint ty_size (T : ty) : nat :=
  match T with
  | TTop            => 0
  | TVar _          => 0
  | TAll _ _ T1 T2  => S (ty_size T1 + ty_size T2)
  | TUnit           => 0
  | TFun  _ _ T1 T2 => S (ty_size T1 + ty_size T2)
  | TRef  _ T       => S (ty_size T)
  end.

Fixpoint splice (n : nat) (t : tm) {struct t} : tm :=
  match t with
  | ttabs   t  => ttabs (splice n t)
  | ttapp t    => ttapp (splice n t)
  | tunit          => tunit
  | tvar (varF i)  =>
    if le_lt_dec n i then tvar (varF (S i))
    else tvar (varF i)
  | tvar (varB i)  => tvar    (varB i)
  | tabs    t      => tabs    (splice n t)
  | tapp    t1 t2  => tapp    (splice n t1) (splice n t2)
  | tloc    l      => tloc     l
  | tref    t      => tref    (splice n t)
  | tderef  t      => tderef  (splice n t)
  | tassign t1 t2  => tassign (splice n t1) (splice n t2)
  end.

Fixpoint splice_ty (n : nat) (T : ty) {struct T} : ty :=
  match T with
  | TTop             => TTop
  | TVar (varF i)    => if le_lt_dec n i then TVar (varF (S i)) else TVar (varF i)
  | TVar (varB i)    => TVar (varB i)
  | TAll d1 d2 T1 T2 => TAll (splice_qual n d1) (splice_qual n d2) (splice_ty n T1) (splice_ty n T2)
  | TUnit            => TUnit
  | TFun d1 d2 T1 T2 => TFun (splice_qual n d1) (splice_qual n d2) (splice_ty n T1) (splice_ty n T2)
  | TRef d1 T        => TRef (splice_qual n d1) (splice_ty n T)
  end.

Fixpoint unsplice_ty (n : nat) (T : ty) {struct T} : ty :=
  match T with
  | TTop             => TTop
  | TVar (varF i)    => if lt_dec n i then TVar (varF (Init.Nat.pred i)) else TVar (varF i)
  | TVar (varB i)    => TVar (varB i)
  | TAll d1 d2 T1 T2 => TAll (unsplice_qual n d1) (unsplice_qual n d2) (unsplice_ty n T1) (unsplice_ty n T2)
  | TUnit            => TUnit
  | TFun d1 d2 T1 T2 => TFun (unsplice_qual n d1) (unsplice_qual n d2) (unsplice_ty n T1) (unsplice_ty n T2)
  | TRef d1 T        => TRef (unsplice_qual n d1) (unsplice_ty n T)
  end.

Inductive closed_tm: nat  -> nat  -> nat  -> tm -> Prop :=
| cl_ttabs: forall b f l t,
  closed_tm (S (S b)) f l t ->
  closed_tm b f l (ttabs t)
| cl_ttapp: forall b f l t,
  closed_tm b f l t ->
  closed_tm b f l (ttapp t)
| cl_tsct : forall b f l,
    closed_tm b f l tunit
| cl_tvarb: forall b f l x,
    x < b ->
    closed_tm b f l #x
| cl_tvarf: forall b f l x,
    x < f ->
    closed_tm b f l $x
| cl_tabs:  forall b f l tm,
    closed_tm (S (S b)) f l tm ->
    closed_tm b f l (tabs tm)
| cl_tapp:  forall b f l tm1 tm2,
    closed_tm b f l tm1 ->
    closed_tm b f l tm2 ->
    closed_tm b f l (tapp tm1 tm2)
| cl_tloc: forall b f l l',
    l' < l ->
    closed_tm b f l &l'
| cl_tref:  forall b f l tm,
    closed_tm b f l tm ->
    closed_tm b f l (tref tm)
| cl_tderef:  forall b f l tm,
    closed_tm b f l tm ->
    closed_tm b f l (tderef tm)
| cl_tassign:  forall b f l tm1 tm2,
    closed_tm b f l tm1 ->
    closed_tm b f l tm2 ->
    closed_tm b f l (tassign tm1 tm2)
.

Inductive closed_ty : nat  -> nat  -> nat  -> ty -> Prop :=
| cl_TTop : forall b f l,
  closed_ty b  f l TTop
| cl_ttvarf: forall b f l x,
  x < f ->
  closed_ty b f l (TVar (varF x))
| cl_ttvarb: forall b f l x,
  x < b ->
  closed_ty b f l (TVar (varB x))
|  cl_TAll:  forall b f l d1 d2 T1 T2 ,
  closed_Qual b f l d1 ↑ ->
  closed_Qual  (S (S b)) f l d2 ↑ ->
  closed_ty b f l T1 ->
  closed_ty (S (S b)) f l T2 ->
  closed_ty b f l (TAll d1 d2 T1 T2)
| cl_TUnit : forall b f l,
    closed_ty b f l TUnit
| cl_TRef : forall b f l T q,
    closed_ty b f l T ->
    closed_Qual b f l q ↑ ->
    closed_ty b f l (TRef q T)
| cl_TFun : forall b f l d1 d2 T1 T2,
    closed_Qual b f l d1 ↑ ->
    closed_Qual (S (S b)) f l d2 ↑ ->
    closed_ty b f l T1 ->
    closed_ty (S (S b)) f l T2 ->
    closed_ty b f l (TFun d1 d2 T1 T2)
.

Fixpoint tfvs (T : ty) (n : nat) {struct T} : bool :=
  match T with
  | TVar (varF i)    => i =? n
  | TAll d1 d2 T1 T2 => qfvs d1 n || qfvs d2 n || tfvs T1 n || tfvs T2 n
  | TFun d1 d2 T1 T2 => qfvs d1 n || qfvs d2 n || tfvs T1 n || tfvs T2 n
  | TRef d1 T        => qfvs d1 n || tfvs T n
  | _                => false
  end.

Fixpoint Tfvs (T : ty) (n : nat) {struct T} : Prop :=
  match T with
  | TVar (varF i)    => i = n
  | TAll d1 d2 T1 T2 => qfvs d1↑ n \/ qfvs d2↑ n \/ Tfvs T1 n \/ Tfvs T2 n
  | TFun d1 d2 T1 T2 => qfvs d1↑ n \/ qfvs d2↑ n \/ Tfvs T1 n \/ Tfvs T2 n
  | TRef d1 T        => qfvs d1↑ n \/ Tfvs T n
  | _                => False
  end.

Definition env := fun (p : Type) => list p.

Definition tenv := env (binding * bool * ty * qual).

Definition senv := env (ty * qual).

Class qenv {p : Type} : Type := {

  qenv_q : p -> qual;

  qenv_qn : qual -> nats;
  qenv_Qn : Qual -> Nats;
}.

#[export] Instance tenv_qenv : @qenv (binding * bool * ty * qual) :=
  {| qenv_q := snd; qenv_qn := qfvs; qenv_Qn := qfvs |}.

#[export] Instance senv_qenv : @qenv (ty * qual) :=
  {| qenv_q := snd; qenv_qn := qlocs; qenv_Qn := qlocs |}.

Inductive wf_senv : senv -> Prop :=
| wf_senv_nil : wf_senv []
| wf_senv_cons : forall Σ T q,
    wf_senv Σ ->
    ♦∉ q ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    wf_senv ((T, q) :: Σ)
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

Definition not_free (v : id) (T : ty): Prop := [[ v ~> TUnit ~ ∅ ]]ᵀ T = T.

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

Inductive has_type : tenv -> qual -> senv -> tm -> ty -> qual -> Prop :=
| t_tabs: forall Γ φ Σ t T1 T2 df d1 d2,
    closed_tm 2 (‖Γ‖) (‖Σ‖) t ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) (TAll d1 d2 T1 T2) ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    d1 ⊑↑ df ⊔ {♦}  ->
    df ⊑↑ φ ->
    ♦∉ df ->
    senv_saturated Σ df ->
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
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
    senv_saturated Σ d1 ->
    not_free 0 T2 ->
    has_type Γ φ Σ (ttapp t) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_tapp_fresh : forall Γ φ Σ t d1 d2 df T1 T2,
    has_type Γ φ Σ t (TAll (q_trans Γ Σ df ⋒ q_trans Γ Σ d1) d2 T1 T2) df ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T1 ->
    closed_Qual 0 (‖Γ‖) (‖Σ‖) d1↑ ->
    d1 ⊑↑ (φ ⊔ {♦}) ->
    (♦∈ d1 -> not_free 1 T2) ->
    senv_saturated Σ d1 ->
    not_free 0 T2 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    (q_trans Γ Σ d1) ⋒ (q_trans Γ Σ df) ⊑↑ (φ ⊔ {♦}) ->
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
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
    d1 ⊑↑ df ⊔ {♦}  ->
    df ⊑↑ φ ->
    ♦∉ df ->
    senv_saturated Σ df ->
    has_type ((bind_tm, false, T1, d1) :: (bind_tm, true, (TFun d1 d2 T1 T2), df) :: Γ)
             (df ⊔ ($!‖Γ‖) ⊔ $!(S (‖Γ‖))) Σ (t <~²ᵗ Γ) (T2 <~²ᵀ Γ) (d2 <~²ᵈ Γ) ->
    has_type Γ φ Σ (tabs t) (TFun d1 d2 T1 T2) df

| t_app : forall Γ φ Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun d1 d2 T1 T2) df ->
    has_type Γ φ Σ t2 T1 d1 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    ♦∉ d1 ->
    not_free 0 T2 ->
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_app_fresh : forall Γ φ Σ t1 d1 t2 d2 df T1 T2,
    has_type Γ φ Σ t1 (TFun (q_trans Γ Σ df ⋒ q_trans Γ Σ d1) d2 T1 T2) df ->
    has_type Γ φ Σ t2 T1 d1 ->
    (♦∈ d1 -> not_free 1 T2) ->
    not_free 0 T2 ->
    (d2 <~ᵈ ∅ ; ∅) ⊑↑ (φ ⊔ {♦}) ->
    (q_trans Γ Σ d1) ⋒ (q_trans Γ Σ df) ⊑↑ (φ ⊔ {♦}) ->
    senv_saturated Σ (d2 <~ᵈ ∅ ; ∅) ->
    has_type Γ φ Σ (tapp t1 t2) (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)

| t_loc : forall Γ φ Σ l T q,
    closed_Qual 0 (‖Γ‖) (‖Σ‖) φ↑ ->
    indexr l Σ = Some (T,q) ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    &!l ⊑↑ φ ->
    senv_saturated Σ q ->
    q ⊑↑ φ ->
    ♦∉ q ->
    has_type Γ φ Σ &l (TRef q T) (q ⊔ &!l)

| t_ref: forall Γ φ Σ T t d1,
    has_type Γ φ Σ t T d1 ->
    closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tref t) (TRef d1 T) ({♦} ⊔ d1)

| t_deref: forall Γ φ Σ T d d1 t,
    has_type Γ φ Σ t (TRef d1 T) d ->
    ♦∉ d1 ->
    d1 ⊑↑ φ ->
    senv_saturated Σ d1 ->
    has_type Γ φ Σ !t T d1

| t_assign: forall Γ φ Σ T t1 d d1 t2,
    has_type Γ φ Σ t1 (TRef d1 T) d ->
    has_type Γ φ Σ t2 T d1 ->
    ♦∉ d1 ->
    has_type Γ φ Σ (tassign t1 t2) TUnit ∅

| t_sub: forall Γ φ  Σ e T1 d1 T2 d2,
    has_type Γ φ Σ e T1 d1 ->
    stp Γ Σ T1 d1 T2 d2 ->
    d2 ⊑↑ (φ ⊔ {♦}) ->
    senv_saturated Σ d2 ->
    has_type Γ φ Σ e T2 d2
.

Inductive value : tm -> Prop :=
| value_ttabs: forall t, value (ttabs t)
| value_abs : forall t, value (tabs t)
| value_cst : value tunit
| value_loc : forall l, value &l
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
| step_deref : forall σ l v,
    indexr l σ = Some (Some v) ->
    step (! &l) σ v σ
| step_assign : forall σ l v,
    l < ‖σ‖ ->
    value v ->
    step (tassign &l v) σ tunit (update σ l (Some v))

| step_c_tapp: forall t t' σ σ',
  step t σ t' σ' ->
  step (ttapp t)  σ (ttapp t') σ'
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
.

Definition CtxOK (Γ : tenv) (φ : qual) (Σ : senv) (σ : store) : Prop :=
  qdom' σ ⊑↑ qdom Σ /\ ‖ σ ‖ = ‖ Σ ‖ /\
  φ ⊑↑ (qdom' σ) /\ forall l v T q,
  l ∈ₗ φ ->
  indexr l Σ = Some (T,q) ->
  indexr l σ = Some (Some v) ->
  value v /\ has_type Γ φ Σ v T q.

Inductive disjointq (Σ Σ' : senv) : qual -> qual -> Prop :=
| disj_bot : forall q,
    disjointq Σ Σ' q ∅
| disj_loc : forall T q q',
    q ⊑↑ q' ->
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    senv_saturated Σ q ->
    ♦∉ q ->
    Σ' = (T,q) :: Σ ->
    disjointq Σ Σ' q' (q ⊔ &!‖Σ‖)
.

Arguments disj_loc { Σ Σ' }.

Notation " S → T ∋ q ⊕ q'" := (disjointq S T q q') (at level 10).

Inductive preserve (Γ : tenv) (Σ : senv) (φ : qual) (t' : tm) (T : ty) (d : qual) (σ' : store) : Prop :=
| Preserve : forall Σ' d' φ',
    Σ' ⊇ Σ ->
    φ ⊑↑ φ' ->
    d' ⊑↑ φ' ->
    wf_senv Σ' ->
    CtxOK Γ φ' Σ' σ' ->
    Σ → Σ' ∋ d ⊕ d'  ->
    has_type Γ φ' Σ' t' T (d ⋓ d') ->
    preserve Γ Σ φ t' T d σ'.

Arguments Preserve {Γ Σ φ t' T d σ'}.

Theorem type_safety: forall {Σ t T d φ},
  has_type [] φ Σ t T d -> wf_senv Σ -> (
    value t \/
    (forall {σ} , CtxOK [] φ Σ σ ->
      (exists t' σ',
        step t σ t' σ' /\ preserve [] Σ φ t' T d σ'
      )
    )
  ).
