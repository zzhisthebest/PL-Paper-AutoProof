Set Implicit Arguments.

Require Import LibExtra.

Require Import AbstractSyntax Deref HeapUpdate.

Reserved Notation "t1 ↦ t2" (at level 40, t2 at level 39).

Inductive red : config -> config -> Prop :=

| red_read : forall yObj wObj m Sigma e Lv yVal wVal ds fs,
    fresh_in_config (wVal :: nil) (trm_read (avar_f wObj) m; fs ; Sigma; e; Lv) ->
    binds wObj yObj e ->
    binds yObj (item_obj ds) Sigma ->
    defs_has ds (def_fld m (avar_f yVal)) ->
    (trm_read (avar_f wObj) m; fs ; Sigma; e; Lv)
      ↦ (trm_var (avar_f wVal); fs; Sigma; e & wVal ~ yVal; fv_config (trm_read (avar_f wObj) m; fs ; Sigma; e; Lv))

| red_write : forall yObj wObj m Sigma e Lv yArg wArg Sigma' fs,
    heap_update Sigma yObj m yArg Sigma' ->
    binds wObj yObj e ->
    binds wArg yArg e ->
    (trm_write (avar_f wObj) m (avar_f wArg); fs; Sigma; e; Lv)
      ↦ (trm_var (avar_f wArg); fs ; Sigma'; e; fv_config (trm_write (avar_f wObj) m (avar_f wArg); fs; Sigma; e; Lv))

| red_call : forall yObj wObj m Sigma e Lv wArg t ds fs,
    binds yObj (item_obj ds) Sigma ->
    defs_has ds (def_met m t) ->
    binds wObj yObj e ->
    (trm_call (avar_f wObj) m (avar_f wArg); fs ; Sigma; e; Lv)
      ↦ ((open wArg (open_rec 1 wObj t)); fs ; Sigma; e; fv_config (trm_call (avar_f wObj) m (avar_f wArg); fs ; Sigma; e; Lv))

| red_apply : forall yFun wFun wArg Sigma e Lv t fs,
    binds yFun (item_fun t) Sigma ->
    binds wFun yFun e ->
    (trm_apply (avar_f wFun) (avar_f wArg); fs; Sigma; e; Lv)
      ↦ (open wArg t; fs; Sigma; e; fv_config (trm_apply (avar_f wFun) (avar_f wArg); fs; Sigma; e; Lv))

| red_let_fun : forall T t1 t2 Sigma e Lv y w fs,
    fresh_in_config (y :: w :: nil) (trm_lit (lit_fun T t1) t2 ; fs; Sigma; e; Lv) ->
    y <> w ->
    (trm_lit (lit_fun T t1) t2 ; fs; Sigma; e; Lv)
      ↦ (open w t2 ; fs; Sigma & y ~ (item_fun t1); e & w ~ y ; fv_config (trm_lit (lit_fun T t1) t2 ; fs; Sigma; e; Lv))

| red_let_obj : forall T ds t Sigma e Lv y w fs,
    fresh_in_config (y :: w :: nil) (trm_lit (lit_obj T ds) t ; fs; Sigma; e; Lv) ->
    w <> y ->
    (trm_lit (lit_obj T ds) t ; fs; Sigma; e; Lv)
      ↦ (open w t ; fs; Sigma & y ~ (item_obj (deref_defs (e & w ~ y) (open w ds))); e & w ~ y ; fv_config (trm_lit (lit_obj T ds) t ; fs; Sigma; e; Lv))

| red_let_var : forall t Sigma e Lv x fs,
    (trm_var (avar_f x); (stack_cons (frame_let t) fs); Sigma; e; Lv)
      ↦ (open x t; fs; Sigma; e ; fv_config (trm_var (avar_f x); (stack_cons (frame_let t) fs); Sigma; e; Lv))

| red_let_push : forall s t fs Sigma e Lv,
    (trm_let s t; fs; Sigma; e; Lv)
      ↦ (s; (stack_cons (frame_let t) fs); Sigma; e ; fv_config (trm_let s t; fs; Sigma; e; Lv))

where "t1 ↦ t2" := (red t1 t2).

Inductive answer: config -> Prop :=
| nf_loc: forall x Sigma e Lv, answer (trm_var (avar_f x); stack_nil; Sigma; e; Lv).

Reserved Notation "C1 ⊣ n ↦* C2"
         (at level 40, n at level 41, C2 at level 39).

Inductive red_closure :  config -> nat -> config -> Prop :=

| red_refl : forall (C : config),
    C ⊣ 0 ↦* C

| red_trans : forall (C1 C2 C3 : config) (n : nat),
    C1 ⊣ n ↦* C2 ->
    C2      ↦  C3 ->
    C1 ⊣ S n ↦* C3

where "C1 ⊣ n ↦* C2" := (red_closure C1 n C2).

Definition config_terminates_in C n :=
 (exists (Ca : config), answer Ca /\ (C ⊣n↦* Ca)).

Definition config_terminates C :=
 (exists (n : nat), config_terminates_in C n).
