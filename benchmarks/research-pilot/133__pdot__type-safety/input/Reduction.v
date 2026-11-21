Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import Definitions Lookup Sequences.

Reserved Notation "t1 '⟼' t2" (at level 40, t2 at level 39).

Inductive red : sta * trm -> sta * trm -> Prop :=




| red_app: forall γ p q T t,
    γ ⟦ defp q ⤳* defv (λ(T) t) ⟧ ->
    (γ, trm_app q p) ⟼ (γ, open_trm_p p t)


| red_let_val : forall v t γ x,
    x # γ ->
    (γ, trm_let (trm_val v) t) ⟼ (γ & x ~ v, open_trm x t)


| red_let_path : forall t γ p,
    (γ, trm_let (trm_path p) t) ⟼ (γ, open_trm_p p t)




| red_let_tgt : forall t0 t γ t0' γ',
    (γ, t0) ⟼ (γ', t0') ->
    (γ, trm_let t0 t) ⟼ (γ', trm_let t0' t)

where "t1 '⟼' t2" := (red t1 t2).

Notation "t1 '⟼*' t2" := (star red t1 t2) (at level 40).

Inductive norm_form: trm -> Prop :=
| nf_path: forall p, norm_form (trm_path p)
| nf_val: forall v, norm_form (trm_val v).
