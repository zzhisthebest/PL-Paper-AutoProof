From Coq.ssr Require Import ssreflect.

From stdpp Require Import base gmap fin_sets.

From dislog.utils Require Import graph.

From dislog.lang Require Import syntax semantics_cycle.

Section go.

Context `{Countable A}.

Definition abef (G:graph.graph A) (α:gmap loc A) t l :=
  match α !! l with
  | Some v' => reachable G v' t
  | None => False end.

Fixpoint vabef G α t v :=
  match v with
  | VLoc l => abef G α t l
  | VFold v => vabef G α t v
  | _ => True end.

Definition all_abef G α (t:A) (L:gset loc) :=
  set_Forall (abef G α t) L.

Inductive disentangled : graph.graph A -> gmap loc A -> semantics_cycle.task_tree A -> expr -> Prop :=
| DELeaf : forall G α (t:A) (e:expr),
  all_abef G α t (locs e) ->
  disentangled G α (Leaf t) e
| DEBind : forall G α t T1 T2 (K:ctx) (e:expr),
  disentangled G α (Node t T1 T2) e ->
  (set_Forall (fun t => all_abef G α t (locs K)) (frontier T1 ∪ frontier T2)) ->
  disentangled G α (Node t T1 T2) (fill_item K e)
| DEPar : forall G α T1 T2 (e1 e2:expr) t,
  disentangled G α T1 e1 ->
  disentangled G α T2 e2 ->
  disentangled G α (Node t T1 T2) (RunPar e1 e2).

End go.
