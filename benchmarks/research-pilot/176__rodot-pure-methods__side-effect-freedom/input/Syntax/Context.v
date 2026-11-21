Set Implicit Arguments.

Require Import LibExtra SyntaxClasses.

Require Import Vars TransformCollect Types.

Require Import Coq.Sets.Ensembles.

Require Import Coq.Sets.Constructive_sets.

Inductive ctx: Set :=

| ctx_empty

| ctx_push: ctx -> var -> varkind -> typ -> ctx

| ctx_stop: ctx -> ctx

| ctx_hide: ctx -> ctx
.

Notation "G '§' v / vk ~ T" := (ctx_push G v vk T)
  (at level 30, vk at level 20, v at level 20, T at level 20).

Notation "v / vk ~ T" := (ctx_push ctx_empty v vk T)
  (at level 30, vk at level 20, T at level 20).

Notation "G '§ʸ' v ~ T" := (ctx_push G v v_loc T)
  (at level 30, v at level 20, T at level 20).

Notation "G '§ʷ' v ~ T" := (ctx_push G v v_ref T)
  (at level 30, v at level 20, T at level 20).

Notation "G '§ʳ' v ~ T" := (ctx_push G v v_recv T)
  (at level 30, v at level 20, T at level 20).

Notation "G '§ᶻ' v ~ T" := (ctx_push G v v_par T)
  (at level 30, v at level 20, T at level 20).

Notation "G '§ˢ' v ~ T" := (ctx_push G v v_self T)
  (at level 30, v at level 20, T at level 20).

Notation "G '§ˣ' v ~ T" := (ctx_push G v v_let T)
  (at level 30, v at level 20, T at level 20).

Fixpoint ctx_concat(G1 G2: ctx): ctx :=
match G2 with
| ctx_empty => G1
| ctx_push c v vk t => ctx_push (ctx_concat G1 c) v vk t
| ctx_stop c => ctx_stop (ctx_concat G1 c)
| ctx_hide c => ctx_hide (ctx_concat G1 c)
end.

Notation "E §& F" := (ctx_concat E F)
  (at level 28, left associativity) : env_scope.

Fixpoint ctx_map(fn: typ -> typ)(G: ctx): ctx :=
match G with
| ctx_empty => ctx_empty
| ctx_push G1 v vk t => ctx_push (ctx_map fn G1) v vk (fn t)
| ctx_stop G1 => ctx_stop (ctx_map fn G1)
| ctx_hide G1 => ctx_hide (ctx_map fn G1)
end.

Fixpoint ctx_collect_values(A: Set)(fn: typ -> fset A)(G: ctx): fset A :=
match G with
| ctx_empty => \{}
| ctx_push G1 v vk t => (fn t) \u (ctx_collect_values fn G1)
| ctx_stop G1 => (ctx_collect_values fn G1)
| ctx_hide G1 => (ctx_collect_values fn G1)
end.

Notation ctx_fv := (ctx_collect_values fv).

Instance CtxFreeVar : FreeVar ctx := ctx_fv.

Fixpoint ctx_keys(G: ctx): list var :=
match G with
| ctx_empty => nil
| ctx_push G v vk t =>  v :: (ctx_keys G)
| ctx_stop G => ctx_keys G
| ctx_hide G => ctx_keys G
end.

Fixpoint ctx_dom(G: ctx): fset var :=
match G with
| ctx_empty => \{}
| ctx_push G v vk t =>  \{ v } \u (ctx_dom G)
| ctx_stop G => ctx_dom G
| ctx_hide G => ctx_dom G
end.

Notation "x '§#' E" := (x \notin (ctx_dom E)) (at level 67) : env_scope.

Inductive ctx_ok: ctx -> Prop :=
| ctx_ok_empty:
  ctx_ok ctx_empty
| ctx_ok_push(G: ctx)(v: var)(vk: varkind)(t: typ):
  ctx_ok G ->
  v §# G ->
  ctx_ok (ctx_push G v vk t)
| ctx_ok_stop(G: ctx):
  ctx_ok G -> ctx_ok (ctx_stop G)
| ctx_ok_hide(G: ctx):
  ctx_ok G -> ctx_ok (ctx_hide G)
.

Inductive ctx_weakens: ctx -> Prop :=
| ctx_weakens_empty: ctx_weakens ctx_empty
| ctx_weakens_push G v vk t:
  ctx_weakens G ->
  ctx_weakens (ctx_push G v vk t)
.

Inductive ctx_weakens_hide: ctx -> Prop :=
| ctx_weakens_hide_empty: ctx_weakens_hide ctx_empty
| ctx_weakens_hide_push G v vk t:
    ctx_weakens_hide G ->
    ctx_weakens_hide (ctx_push G v vk t)
| ctx_weakens_hide_hide G:
    ctx_weakens_hide G ->
    ctx_weakens_hide (ctx_hide G)
.

Inductive ctx_binds: var -> typ -> ctx -> Prop :=
| ctx_binds_e(v: var)(vk: varkind)(t: typ)(G: ctx):
    ctx_binds v t (ctx_push G v vk t)
| ctx_binds_n(v v2: var)(vk: varkind)(t t2: typ)(G: ctx):
    v <> v2 ->
    ctx_binds v t G ->
    ctx_binds v t (ctx_push G v2 vk t2)
| ctx_binds_hide(v: var)(t: typ)(G: ctx):
    ctx_binds v t G ->
    ctx_binds v t (ctx_hide G)
.

Inductive ctx_binds_k_after: var -> varkind -> typ -> ctx -> ctx -> Prop :=
| ctx_binds_k_e(v: var)(vk: varkind)(t: typ)(G: ctx):
    ctx_binds_k_after v vk t (ctx_push G v vk t) G
| ctx_binds_k_n(v v2: var)(vk1 vk2: varkind)(t t2: typ)(G1 G2: ctx):
    v <> v2 ->
    ctx_binds_k_after v vk1 t G1 G2 ->
    ctx_binds_k_after v vk1 t (ctx_push G1 v2 vk2 t2) G2
.

Fixpoint ctx_kdom(vk: varkind)(c: ctx): fset var :=
match c with
| ctx_empty => \{}
| ctx_push c v vk2 t => If (vk = vk2) then (\{ v } \u (ctx_kdom vk c)) else (ctx_kdom vk c)
| ctx_stop c => ctx_kdom vk c
| ctx_hide c => ctx_kdom vk c
end.

Definition ctx_k G v vk:=
  exists t G2, ctx_binds_k_after v vk t G G2.

Notation subst_ctx x y := (ctx_map (subst_var x y)).

Notation "G '/[§' x '->' y ']'" :=
  (subst_ctx x y G) (x at level 69, at level 7, left associativity) : syntax_scope.

Notation subst_ctx_vars xs ys := (ctx_map (subst_vars xs ys)).

Notation "G '/[§' xs '-->' ys ']'" :=
  (subst_ctx_vars xs ys G) (xs at level 69, at level 7, left associativity) : syntax_scope.

Notation subst_ctx_pvars xs ys := (ctx_map (subst_pvars xs ys)).

Notation "G '//[§' xs '-->' ys ']'" :=
  (subst_ctx_pvars xs ys G) (xs at level 69, at level 7, left associativity) : syntax_scope.

Fixpoint ctx_seal_rec n x G :=
  match G with
  | ctx_empty => ctx_empty
  | ctx_stop G => ctx_stop (ctx_seal_rec n x G)
  | ctx_hide G => ctx_hide (ctx_seal_rec n x G)
  | ctx_push G y vk t => ctx_push (ctx_seal_rec n x G) y vk (seal_rec n x t)
  end.

Instance CtxSealable: Sealable ctx := ctx_seal_rec.

Inductive ctx_vis: ctx -> var -> Prop :=
| ctx_vis_e(v: var)(vk: varkind)(t: typ)(G: ctx):
    ctx_vis (ctx_push G v vk t) v
| ctx_vis_n(v v2: var)(vk: varkind)(t: typ)(G: ctx):
    v <> v2 ->
    ctx_vis G v ->
    ctx_vis (ctx_push G v2 vk t) v
.
