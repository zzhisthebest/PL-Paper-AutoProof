Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Language Infra SubDis Determinism.

Definition i : Set := nat.

Definition sctx : Set := list ( i * typ ).

Inductive sexp :=
  | se_i : nat -> sexp
  | se_lit : nat -> sexp
  | se_unit : sexp
  | se_abs : nat -> sexp -> sexp
  | se_app : sexp -> sexp -> sexp
  | se_merge : sexp -> sexp -> sexp.

Inductive lityp : typ -> Prop :=
  | li_int : lityp int
  | li_top : lityp top
  | li_arr : forall (A B:typ),
      lityp A ->
      lityp B ->
      lityp (arr A B)
  | li_and : forall (A B:typ),
      lityp A ->
      lityp B ->
      lityp (and A B).

Definition sbinds (x : i) (A : typ) (E : list (i * typ)) : Prop := In (x, A) E.

Fixpoint sdom (E : list (i * typ)) {struct E} : list i :=
  match E with
    | nil => nil
    | (x, A) :: E' => cons x (sdom E')
  end.

Inductive suniq : list (i * typ) -> Prop :=
  | suniq_nil :
      suniq nil
  | suniq_push : forall x A E,
      suniq E ->
      ~ In x (sdom E) ->
      suniq (cons (x, A) E).

Fixpoint ctx_sw (E : list (i * typ)) {struct E} : typ :=
  match E with
    | nil => top
    | (x, A) :: E' => and (ctx_sw E') (rcd x A)
  end.

Inductive contains: nat -> typ -> Prop:=
  | ct_rcd : forall x A,
      contains x (rcd x A)
  | ct_andl : forall x A B,
      contains x A ->
      contains x (and A B)
  | ct_andr : forall x A B,
      contains x B ->
      contains x (and A B).

Definition fresh x A := ~ (contains x A).

Inductive styping : sctx -> sexp -> typ -> exp -> Prop :=
  | styping_lit : forall (G:sctx) (i5:i),
      suniq  G  ->
      styping G (se_lit i5) int (lit i5)
  | styping_top : forall (G:sctx),
      suniq  G  ->
      styping G se_unit top unit
  | styping_var : forall (G:sctx) (x:i) (A:typ),
      suniq G  ->
      sbinds  x A G  ->
      lityp A ->
      styping G (se_i x) A (proj  ( (ann ctx (rcd x A)) )  x)
  | styping_abs : forall (G:sctx) (x:i) (A:typ) (ee:sexp) (B:typ) (e:exp),
      styping  (cons ( x , A )  G )  ee B e ->
      lityp A ->
      lityp B ->
      styping G (se_abs x ee) (arr A B) (ann (lam wh e) (arr (rcd x A) B))
  | styping_app : forall (G:sctx) (ee1 ee2:sexp) (B:typ) (e1 e2:exp) (A:typ),
      styping G ee1 (arr A B) e1 ->
      styping G ee2 A e2 ->
      lityp A ->
      lityp B ->
      styping G (se_app ee1 ee2) B (app e1 e2)
  | styping_merge : forall (G:sctx) (ee1 ee2:sexp) (B:typ) (e1 e2:exp) (A:typ) (m:nat),
    styping G ee1 A e1 ->
    styping G ee2 B e2 ->
    lityp A ->
    lityp B ->
    disjoint A B ->
    fresh m A ->
    styping G (se_merge ee1 ee2) (and A B) (box (rec m ctx) (merge (box (proj ctx m) e1) (box (proj (ann ctx (rcd m (ctx_sw G))) m) e2)))
  | styping_sub : forall (G:sctx) (ee1 ee2:sexp) (B:typ) (e1 e2:exp) (A:typ) (m:nat),
    styping G ee1 A e1 ->
    lityp A ->
    lityp B ->
    sub A B ->
    styping G ee1 B (ann e1 B).

Section ListProperties.

Variables X : Set.

Variables x y : X.

Variables l l1 l2 l3 : list X.

End ListProperties.

Theorem encoding_complete: forall sctx A ee e,
  styping sctx ee A e ->
  has_type (ctx_sw sctx) e inf A.
