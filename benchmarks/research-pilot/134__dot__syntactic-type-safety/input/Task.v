Set Implicit Arguments.

Require Import Coq.Program.Equality String.

Require Import Binding Definitions OperationalSemantics RecordAndInertTypes.

Inductive sta_trm_typ : sta * trm -> typ -> Prop :=
| sta_trm_typ_c : forall G s t T,
    inert G ->
    well_typed G s ->
    G ⊢ t : T ->
    sta_trm_typ (s, t) T.

Notation "'⊢' t ':' T" := (sta_trm_typ t T) (at level 40, t at level 59).

Theorem preservation : forall s s' t t' T,
    ⊢ (s, t) : T ->
    (s, t) |-> (s', t') ->
    ⊢ (s', t') : T.

Theorem progress: forall s t T,
    ⊢ (s, t) : T ->
    norm_form t \/ exists s' t', (s, t) |-> (s', t').
