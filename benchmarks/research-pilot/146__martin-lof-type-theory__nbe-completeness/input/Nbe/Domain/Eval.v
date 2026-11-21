Require Import Nbe.Syntax.Def Nbe.Utils.Notations.

Set Implicit Arguments.

Require Import Nbe.Domain.Def.

Inductive EvalTm: Tm -> DEnv -> D -> Prop :=

| evalVar : forall d env,
  EvalTm (TmVar) (Dext env d) d

| evalAbs : forall a t env,
  EvalTm (TmAbs a t) env (Dclo t env)

| eval0 : forall env,
  EvalTm Tm0 env D0

| evalS : forall env t d,
  EvalTm t env d ->
  EvalTm (TmS t) env (DS d)

| evalApp : forall tf df tx dx dr env,
  EvalTm tf env df ->
  EvalTm tx env dx ->
  App df dx dr ->
  EvalTm (TmApp tf tx) env dr

| evalSb: forall s env envs t d,
  EvalSb s env envs ->
  EvalTm t envs d ->
  EvalTm (TmSb t s) env d

| eval1 : forall env,
  EvalTm Tm1 env D1

| evalUnit : forall env,
  EvalTm TmUnit env Dunit

| evalNat: forall denv,
  EvalTm TmNat denv Dnat

| evalFun: forall A B denv DA,
  EvalTm A denv DA ->
  EvalTm (TmFun A B) denv (Dfun DA $ Dclo B denv)

| evalEmpty: forall denv,
  EvalTm TmEmpty denv Dempty

| evalAbsurd: forall A DA denv,
  EvalTm A denv DA ->
  EvalTm (TmAbsurd A) denv (Dabsurd DA)

| evalUniv: forall denv,
  EvalTm TmUniv denv Duniv




with EvalSb: Sb -> DEnv -> DEnv -> Prop :=

| evalId : forall env,
  EvalSb Sid env env

| evalUp : forall d env,
  EvalSb Sup (Dext env d) env






| evalSeq : forall env0 env1 env2 s1 s2,
  EvalSb s2 env0 env1 ->
  EvalSb s1 env1 env2 ->
  EvalSb (Sseq s1 s2) env0 env2

| evalExt : forall env0 envs s t d,
  EvalSb s env0 envs ->
  EvalTm t env0 d ->
  EvalSb (Sext s t) env0 (Dext envs d)




with App: D -> D -> D -> Prop :=

| appClo  : forall tm denv dx dr,
  EvalTm tm (Dext denv dx) dr ->
  App (Dclo tm denv) dx dr

| appFun : forall DA DF DB e a,
  App DF a DB ->
  App (DupX (Dfun DA DF) e) a (Dup DB (Dapp e (Ddown DA a)))

| appNeAbsurd: forall DA u,
  App (Dabsurd DA) (DupN u) (Dup DA $ DneAbsurd (DdownN DA) u)
.

Scheme EvalTm_mind := Induction for EvalTm Sort Prop
with   EvalSb_mind := Induction for EvalSb Sort Prop
with   App_mind    := Induction for App    Sort Prop
.

Combined Scheme Evals_ind from EvalTm_mind,  EvalSb_mind, App_mind.

Inductive EvalCxt : Cxt -> DEnv -> Prop :=
 | EvalCxt_empty:
   EvalCxt nil Did

 | EvalCxt_ext: forall Gamma A denv DA,
   EvalCxt Gamma denv ->
   EvalTm  A denv DA ->
   EvalCxt (Gamma,,A) (Dext denv $ Dup DA $ Dvar $ length Gamma)
.
