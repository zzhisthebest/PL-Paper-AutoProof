Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Class CommitTyping (A : Set) :=
  commit_typing : ctx -> init_ctx -> A -> Prop.

Notation "Gamma ⸴ Delta '⊢c' t " :=
  (commit_typing Gamma Delta t) (at level 40, Delta at level 39, t at level 59).

Class InitTyping (A : Set) :=
  init_typing : ctx -> init_ctx -> vars -> A -> init_typ -> Prop.

Notation "Gamma ⸴ Delta ⸴ vs '⊢i' t '∶' i" :=
  (init_typing Gamma Delta vs t i)
    (at level 40, Delta at level 39, vs at level 39, t at level 59).

Class InitTypings (A : Set) :=
  init_typings : ctx -> init_ctx -> vars -> A -> inits -> Prop.

Notation "Gamma  ⸴ Delta ⸴ vs '⊢i' t '::' Ts" :=
  (init_typings Gamma Delta vs t Ts)
    (at level 40, Delta at level 39, vs at level 39, t at level 59).
