From Coq.ssr Require Import ssreflect.

From stdpp Require Import strings binders gmap gmultiset.

From dislog.lang Require Export semantics_cycle disentangled.

Definition head_step := @head_step timestamp eqdec_timestamp countable_timestamp.

Definition sched_step := @sched_step timestamp eqdec_timestamp countable_timestamp.

Definition step := @step timestamp eqdec_timestamp countable_timestamp.

Notation amap := (gmap loc timestamp).

Notation graph := (graph timestamp).

Notation task_tree := (task_tree timestamp).
