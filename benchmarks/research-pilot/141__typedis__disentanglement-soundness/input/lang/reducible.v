From stdpp Require Import base sets fin_sets.

From dislog.lang Require Import syntax semantics_cycle semantics.

Inductive OOB : store -> expr -> Prop :=
| OOBAlloc : forall σ (i:Z) (v:val),
  ¬ (0 < i)%Z ->
  OOB σ (Alloc i v)
| OOBLoad : forall σ (l:loc) bs (i:Z),
  σ !! l = Some (SBlock bs) ->
  ¬ (0 <= i < (Z.of_nat (length bs)))%Z ->
  OOB σ (Load l i)
| OOBCAS : forall σ (l:loc) bs (i:Z) (v1 v2:val),
  σ !! l = Some (SBlock bs) ->
  ¬ (0 <= i < (Z.of_nat (length bs)))%Z ->
  OOB σ (CAS l i v1 v2)
| OOBStore : forall σ (l:loc) bs (i:Z) (v:val),
  σ !! l = Some (SBlock bs) ->
  ¬ (0 <= i < (Z.of_nat (length bs)))%Z ->
  OOB σ (Store l i v).

Inductive reducible : bool -> store -> amap -> graph -> task_tree -> expr -> Prop :=
| RedSched : forall b σ α G T e σ' α' G' T' e',
  sched_step σ α G T e σ' α' G' T' e' ->
  reducible b σ α G T e
| RedOOB : forall σ α G t e,
  OOB σ e ->
  reducible true σ α G (Leaf t) e
| RedCtx : forall b σ α G T e K,
    reducible b σ α G T e ->
    reducible b σ α G T (fill_item K e)
| RedPar : forall b σ α G T1 T2 e1 e2 t,
    (¬ (is_val e1) ∨ ¬ (is_val e2)) ->
    (¬ is_val e1 -> reducible b σ α G T1 e1) ->
    (¬ is_val e2 -> reducible b σ α G T2 e2) ->
    reducible b σ α G (Node t T1 T2) (RunPar e1 e2).
