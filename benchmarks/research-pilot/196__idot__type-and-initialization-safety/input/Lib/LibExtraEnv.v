Set Implicit Arguments.

From TLC Require Import LibEnv LibTactics.

Require Import LibExtraFset LibExtraVar LibExtraList.

Notation "xs ~** vs" := (singles (List.rev xs) (List.rev vs))
  (at level 27, left associativity) : env_scope.
