Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Require Import Effects Initialization.

Inductive init_sub : init_typ -> init_typ -> Prop :=
| init_sub_refl : forall i, init_sub i i
| init_sub_comm_unspec : init_sub committed unspecified
| init_sub_free_unspec : init_sub free unspecified.

Inductive init_var : init_ctx -> vars -> var -> init_typ -> Prop :=

| init_var_commit : forall Delta vs x,
    binds x committed Delta ->
    init_var Delta vs x committed

| init_var_free : forall Delta vs x,
    x \in vs ->
    binds x free Delta ->
    init_var Delta vs x free

| init_var_unspec : forall Delta vs x,
    x \in vs ->
    binds x unspecified Delta ->
    init_var Delta vs x unspecified

| init_var_sub : forall Delta vs x i i',
    init_var Delta vs x i' ->
    init_sub i' i ->
    init_var Delta vs x i.
