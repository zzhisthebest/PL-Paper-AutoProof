From Coq.ssr Require Import ssreflect.

From stdpp Require Import strings binders gmap gmultiset.

From dislog.utils Require Import graph.

From dislog.lang Require Export head_semantics.

Inductive task_tree (A:Type) : Type :=
| Leaf : A -> task_tree A
| Node : A -> task_tree A -> task_tree A -> task_tree A.

Arguments Leaf {A}%_type_scope.

Arguments Node {A}%_type_scope.

Fixpoint leaves `{Countable A} (T:task_tree A) : gset A :=
  match T with
  | Leaf t => {[t]}
  | Node t T1 T2 => {[t]} ∪ leaves T1 ∪ leaves T2 end.

Fixpoint frontier `{Countable A} (T:task_tree A) : gset A :=
  match T with
  | Leaf x => {[x]}
  | Node _ T1 T2 => frontier T1 ∪ frontier T2 end.

Definition is_leaf `{Countable A} (T:task_tree A) := match T with | Leaf _ => true | _ => false end.

Inductive sched_step `{Countable A} :
  store -> gmap loc A -> graph A -> task_tree A -> expr ->
  store -> gmap loc A -> graph A -> task_tree A -> expr -> Prop :=
| SchedHead : forall σ α G t e σ' α' e',
    head_step G t σ α e σ' α' e' ->
    sched_step σ α G (Leaf t) e σ' α' G (Leaf t) e'
| SchedFork : forall σ α G G' t0 t1 t2 (v1 v2:val),
    t1 ∉ vertices G ->
    t2 ∉ vertices G ->
    t1 ≠ t2 ->
    G' = graph_fork G t0 t1 t2 ->
    sched_step
      σ α G (Leaf t0) (Par v1 v2)
      σ α G' (Node t0 (Leaf t1) (Leaf t2)) (RunPar (Call v1 [Val VUnit]) (Call v2 [Val VUnit]))
| SchedJoin : forall σ α G G' t1 t2 t3 (v1 v2:val) σ' α' (l:loc),
    G' = graph_join G t1 t2 t3 ->
    l ∉ dom σ ->
    l ∉ dom α ->
    σ' = <[l:=SProd v1 v2]> σ ->
    α' = <[l:=t3]> α ->
    sched_step
      σ  α  G (Node t3 (Leaf t1) (Leaf t2)) (RunPar v1 v2)
      σ' α' G' (Leaf t3) l.

Inductive step `{Countable A} :
  store -> gmap loc A -> graph A -> task_tree A -> expr ->
  store -> gmap loc A -> graph A -> task_tree A -> expr -> Prop :=
| StepHead : forall σ α G T2 e2 σ' α' G' T2' e2',
    sched_step σ α G T2 e2 σ' α' G' T2' e2' ->
    step σ α G T2 e2 σ' α' G' T2' e2'
| StepBind : forall σ α G T e σ' α' G' T' e' K,
    step σ α G T e σ' α' G' T' e' ->
    step σ α G T (fill_item K e) σ' α' G' T' (fill_item K e')
| StepParL : forall σ α G G' e1 e2 T1 T2 σ' α' T1' e1' t,
    step σ α G T1 e1 σ' α' G' T1' e1' ->
    step σ α G (Node t T1 T2) (RunPar e1 e2) σ' α' G' (Node t T1' T2) (RunPar e1' e2)
| StepParR : forall σ α G G' e1 e2 T1 T2 σ' α' T2' e2' t,
    step σ α G T2 e2 σ' α' G' T2' e2' ->
    step σ α G (Node t T1 T2) (RunPar e1 e2) σ' α' G' (Node t T1 T2') (RunPar e1 e2')
.

Inductive pstep `{Countable A} : graph.path ->
  store -> gmap loc A -> graph A -> task_tree A -> expr ->
  store -> gmap loc A -> graph A -> task_tree A -> expr -> Prop :=
| PStepHead : forall σ α G T2 e2 σ' α' G' T2' e2',
    sched_step σ α G T2 e2 σ' α' G' T2' e2' ->
    pstep [] σ α G T2 e2 σ' α' G' T2' e2'
| PStepBind : forall p σ α G T e σ' α' G' T' e' K,
    pstep p σ α G T e σ' α' G' T' e' ->
    pstep p σ α G T (fill_item K e) σ' α' G' T' (fill_item K e')
| PStepParL : forall p σ α G G' e1 e2 T1 T2 σ' α' T1' e1' t,
    pstep p σ α G T1 e1 σ' α' G' T1' e1' ->
    pstep (Left::p) σ α G (Node t T1 T2) (RunPar e1 e2) σ' α' G' (Node t T1' T2) (RunPar e1' e2)
| PStepParR : forall p σ α G G' e1 e2 T1 T2 σ' α' T2' e2' t,
    pstep p σ α G T2 e2 σ' α' G' T2' e2' ->
    pstep (Right::p) σ α G (Node t T1 T2) (RunPar e1 e2) σ' α' G' (Node t T1 T2') (RunPar e1 e2')
.
