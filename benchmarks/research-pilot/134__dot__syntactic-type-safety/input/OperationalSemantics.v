Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import TLC.LibLN.

Require Import Definitions Binding.

Reserved Notation "t1 '|->' t2" (at level 40, t2 at level 39).

Inductive red : sta * trm -> sta * trm -> Prop :=



| red_sel : forall x m s t T ds,
    binds x (val_new T ds) s ->
    defs_has (open_defs x ds) (def_trm m t) ->
    (s, trm_sel (avar_f x) m) |-> (s, t)




| red_app : forall f a s T t,
    binds f (val_lambda T t) s ->
    (s, trm_app (avar_f f) (avar_f a)) |-> (s, open_trm a t)


| red_let_val : forall v t s x,
    x # s ->
    (s, trm_let (trm_val v) t) |-> (s & x ~ v, open_trm x t)


| red_let_var : forall t s x,
    (s, trm_let (trm_var (avar_f x)) t) |-> (s, open_trm x t)




| red_let_tgt : forall t0 t s t0' s',
    (s, t0) |-> (s', t0') ->
    (s, trm_let t0 t) |-> (s', trm_let t0' t)

where "t1 '|->' t2" := (red t1 t2).

Inductive norm_form: trm -> Prop :=
| nf_var: forall x, norm_form (trm_var x)
| nf_val: forall v, norm_form (trm_val v).
