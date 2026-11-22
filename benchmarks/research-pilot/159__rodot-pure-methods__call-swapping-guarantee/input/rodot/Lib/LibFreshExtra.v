Set Implicit Arguments.

From TLC Require Import LibVar LibLN LibTactics.

Require Import LibListExtra LibListReorder LibVarExtra LibSetExtra.

Inductive freshy: vars -> vars -> list var -> list var -> Prop :=
| freshy_nil L Lx:
  freshy L Lx nil nil
| freshy_fresh L Lx xs ys x y:
  x \notin (L \u Lx) ->
  x \notin (from_list xs) ->
  freshy L Lx xs ys ->
  freshy L Lx (x::xs) (y::ys)
| freshy_same L Lx xs ys x:
  freshy L Lx xs ys ->
  x \in Lx ->
  freshy L Lx (x::xs) (x::ys).
