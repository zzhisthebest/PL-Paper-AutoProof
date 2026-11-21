Require Import Infrastructure.

Inductive BotDisjoint : stctx -> sty -> Prop :=
| bl_bot : forall Δ A,
    TopLike A ->
    BotDisjoint Δ A
| bl_and : forall Δ A B,
    BotDisjoint Δ A ->
    BotDisjoint Δ B ->
    BotDisjoint Δ (sty_and A B)
| bl_tvar : forall Δ A X,
    binds X A Δ ->
    sub Δ A sty_bot->
    BotDisjoint Δ (sty_var_f X).
