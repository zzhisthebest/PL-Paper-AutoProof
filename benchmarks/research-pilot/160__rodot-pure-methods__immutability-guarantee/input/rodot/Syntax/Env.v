Set Implicit Arguments.

Require Import LibExtra SyntaxClasses.

Require Import Vars Types Context Envs.

Notation renv := (env var) (only parsing).

Notation renv_empty := (empty) (only parsing).

Notation renv_bind e v1 v2 := (e & v1 ~ v2) (only parsing).

Definition renv_notin (v: var) (e: renv) := v \notin (dom e \u fv_env e).

Definition renv_idempotent (e: renv) := forall x, x \in dom e -> x \notin fv_env e.

Notation renv_binds v1 v2 e := (binds v1 v2 e) (only parsing).
