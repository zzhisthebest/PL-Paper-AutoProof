Require Import Nbe.Syntax.Def Nbe.Utils.Notations.

Set Implicit Arguments.

Require Import Nbe.Domain.Def.

Require Import Nbe.Domain.Eval.

Inductive RbNf: nat -> DNf -> Tm -> Prop :=
| reifyNf_abs: forall m DA db F DB W w f,
  RbNf m (DdownN DA) W ->
  App F (Dup DA $ Dvar m) DB ->
  App f (Dup DA $ Dvar m) db ->
  RbNf (S m) (Ddown DB db) w ->
  RbNf m     (DdownX (Dfun DA F) f) (TmAbs W w)

| reifyNf_d1: forall m e,
  RbNf m (DdownX Dunit e) Tm1

| reifyNf_ne: forall m e n,
  RbNe m e n ->
  RbNf m (DdownN $ DupN e) n

| reifyNf_0: forall m,
  RbNf m (Ddown Dnat D0) Tm0

| reifyNf_S: forall m t d,
  RbNf m (Ddown Dnat d) t ->
  RbNf m (Ddown Dnat (DS d)) (TmS t)

| reifyNf_nat: forall m,
  RbNf m (DdownN Dnat) TmNat

| reifyNf_unit: forall m,
  RbNf m (DdownN Dunit) TmUnit

| reifyNf_fun: forall m DA DF DB A F,
  RbNf m (DdownN   DA) A ->
  App DF (Dup DA $ Dvar m) DB ->
  RbNf (S m) (DdownN   DB) F ->
  RbNf m     (DdownN $ Dfun DA DF) (TmFun A F)

| reifyNf_empty: forall m,
  RbNf m (DdownN Dempty) TmEmpty

| reifyNf_univ: forall m,
  RbNf m (DdownN Duniv) TmUniv




with RbNe: nat -> DNe -> Tm -> Prop :=

| reifyNe_var: forall m j,
  RbNe m (Dvar j) (tmVar (m - S j))

| reifyNe_app: forall m e d ne nd,
  RbNe m e ne ->
  RbNf m d nd ->
  RbNe m (Dapp e d) (TmApp ne nd)

| reifyNe_absurd: forall m DA u A n,
  RbNe m u n ->
  RbNf m DA A ->
  RbNe m (DneAbsurd DA u) (TmApp (TmAbsurd A) n)
.

Scheme RbNf_mind := Induction for RbNf Sort Prop
with   RbNe_mind := Induction for RbNe Sort Prop
.

Combined Scheme Rbs_ind from RbNf_mind, RbNe_mind.

Inductive Nf: Tm -> Prop :=
| Nf_ne: forall n, Ne n -> Nf n
| Nf_d1: Nf Tm1
| Nf_univ: Nf TmUniv
| Nf_unit: Nf TmUnit
| Nf_nat: Nf TmNat
| Nf_0: Nf Tm0
| Nf_s: forall t, Nf t -> Nf (TmS t)
| Nf_empty: Nf TmEmpty
| Nf_abs: forall W w, Nf W -> Nf w -> Nf (TmAbs W w)
| Nf_fun: forall A B, Nf A -> Nf B -> Nf (TmFun A B)
with Ne: Tm -> Prop :=
| Ne_var: forall i, Ne (tmVar i)
| Ne_app: forall tf tx, Ne tf -> Nf tx -> Ne (TmApp tf tx)
| Ne_absurd: forall n A, Ne n -> Nf A -> Ne (TmApp (TmAbsurd A) n)
.
