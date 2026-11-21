Set Implicit Arguments.

Require Import LibExtra.

Require Import AbstractSyntax HeapUpdate.

Reserved Notation "t1 ↦ t2" (at level 40, t2 at level 39).

Inductive red : config -> config -> Prop :=

| red_sel : forall x a Sigma y T hds fs,
    binds x (item_obj T hds) Sigma ->
    labels_has hds (heap_def_trm a (Some y)) ->
    (trm_sel (avar_f x) a; fs ; Sigma)
      ↦ (trm_var (avar_f y); fs ; Sigma)

| red_asn : forall x a Sigma y Sigma' fs,
    heap_update Sigma x a y Sigma' ->
    (trm_asn (avar_f x) a (avar_f y); fs; Sigma)
      ↦ (trm_var (avar_f y); fs; Sigma')

| red_app : forall f a Sigma T t fs,
    binds f (item_lit (lit_fun T t)) Sigma ->
    (trm_app (avar_f f) (avar_f a); fs; Sigma)
      ↦ (open a t; fs; Sigma)

| red_let_lit : forall T l t Sigma x fs,
    x # Sigma ->
    (trm_lit T l t ; fs; Sigma)
      ↦ (open x t ; fs; Sigma & x ~ (item_lit l))

| red_new : forall Ts is' T ds t Sigma x c ys avs fs,
    x # Sigma ->
    x \notin fv (open_rec_vars 1 ys ds) ->
    binds c (item_lit (lit_con Ts is' T ds t)) Sigma ->
    length ys = length_s Ts ->
    vars_of_avars ys avs ->
    (trm_new (avar_f c) avs; fs; Sigma)
      ↦ ((open_vars (cons x ys) t)
           ; (frame_ret x :: fs)%list
           ; Sigma & x ~ (item_obj
                        (open_rec_vars 1 ys T)
                        (open_vars (cons x ys) (heap_defs_of_defs ds))))

| red_return : forall Sigma x y fs,
    (trm_var (avar_f y); (frame_ret x :: fs)%list; Sigma)
      ↦ (trm_var (avar_f x); fs; Sigma)

| red_let_var : forall t Sigma x fs,
    (trm_var (avar_f x); (frame_let t :: fs)%list; Sigma)
      ↦ (open x t; fs; Sigma)

| red_let_sta : forall T s t fs Sigma,
    (trm_let T s t; fs; Sigma)
      ↦ (s; (frame_let t :: fs)%list; Sigma)

where "t1 ↦ t2" := (red t1 t2).

Inductive answer: config -> Prop :=
| nf_loc: forall x Sigma, answer (trm_var (avar_f x); nil; Sigma).
