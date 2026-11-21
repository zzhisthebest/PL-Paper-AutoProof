Set Implicit Arguments.

Require Import Coq.Program.Equality List String.

Require Import Sequences.

Require Import Binding Definitions Lookup Reduction PreciseTyping RecordAndInertTypes TightTyping.

Close Scope string_scope.

Section Safety.

Reserved Notation "x '==>' T '=' bs '=>' U" (at level 40, T at level 20).

Inductive lookup_fields_typ : var -> typ -> list trm_label -> typ -> Prop :=
| lft_empty : forall x T,
    x ==> T =nil=> T
| lft_cons : forall T bs U x a S,
    x ==> T =bs=> μ U ->
    record_has (open_typ_p (p_sel (avar_f x) bs) U) {a ⦂ S} ->
    x ==> T =a::bs=> S

where "x '==>' T '=' bs '=>' U" := (lookup_fields_typ x T bs U).

Definition diverges := infseq red.

Theorem safety t T :
  empty ⊢ t : T ->
  diverges (empty, t) \/
  (exists γ u G, (empty, t) ⟼* (γ, u) /\
            norm_form u /\
            G ⊢ u : T /\
            γ ⫶ G /\
            wf G /\
            inert G).

End Safety.
