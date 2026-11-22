From stdpp Require Export prelude.

From Autosubst Require Export Autosubst.

Class IdsLemmas (term : Type) {Ids_term : Ids term} := {
  ids_inj x y : ids x = ids y → x = y
}.

Section Autosubst_Lemmas.

Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}
          {IdsLeamms_term : IdsLemmas term}.

End Autosubst_Lemmas.

Reserved Notation "⟦ τ ⟧" (at level 0, τ at level 70).

Reserved Notation "⟦ τ ⟧ₑ" (at level 0, τ at level 70).

Reserved Notation "⟦ Γ ⟧*" (at level 0, Γ at level 70).
