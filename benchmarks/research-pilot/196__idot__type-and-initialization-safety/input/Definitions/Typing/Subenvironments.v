Set Implicit Arguments.

Require Import LibExtra.

Require Import AbstractSyntax Typing GeneralTyping.

Reserved Notation "G1 ⪯ G2" (at level 35).

Inductive subenv: ctx -> ctx -> Prop :=
| subenv_empty : empty ⪯ empty
| subenv_grow: forall G G' x T T',
    G ⪯ G' ->
    ok (G & x ~ T) ->
    G ⊢ T <: T' ->
    G & x ~ T ⪯ G' & x ~ T'
where "G1 ⪯ G2" := (subenv G1 G2).
