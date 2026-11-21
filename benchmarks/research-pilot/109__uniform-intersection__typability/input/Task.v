From Stdlib Require Import List Permutation.
Import ListNotations.

(* simple types *)
Inductive sty : Type :=
  | satom (x : nat)   (* type variable *)
  | sarr (s t : sty). (* function type *)

(* type-annotated lambda-terms *)
Inductive tm : Type :=
  | var (n : nat)           (* term variable *)
  | app (M N : tm)          (* application *)
  | lam (t : sty) (M : tm). (* type-annotated abstraction *)

(* simply typed lambda-calculus *)
(* stlc Gamma M s means that in the type environment Gamma the term M is assigned the type s *)
Inductive stlc (Gamma : list sty) : tm -> sty -> Prop :=
  | stlc_var x t : nth_error Gamma x = Some t -> stlc Gamma (var x) t
  | stlc_app M N s t : stlc Gamma M (sarr s t) -> stlc Gamma N s -> stlc Gamma (app M N) t
  | stlc_lam M s t : stlc (cons s Gamma) M t -> stlc Gamma (lam (sarr s t) M) (sarr s t).

Inductive nity : Type :=
  | niatom (x : nat) : nity
  | niarr (u : list nity) (A : nity) : nity.

(* type environment *)
Notation environment := (list (list nity)).

(* ssim s A means non-idempotent type A collapses to simple type s *)
Inductive ssim : sty -> nity -> Prop :=
  | ssim_atom x : ssim (satom x) (niatom x)
  | ssim_arr s t A u B : Forall (ssim s) (cons A u) -> ssim t B -> ssim (sarr s t) (niarr (cons A u) B).


(* environment permutation *)
Notation sty_permutation Gammas Deltas :=
  (forall x, @Permutation nity
    (concat (map (fun Gamma => nth x Gamma nil) Gammas))
    (concat (map (fun Delta => nth x Delta nil) Deltas))).

(* non-idempotently typed lambda-calculus *)
(* nitlc Gamma M A means that in the type environment Gamma the term M is assigned the type A *)
Inductive nitlc (Gamma : environment) : tm -> nity -> Prop :=
  | nitlc_var t x A :
      ssim t A ->
      In A (nth x Gamma nil) ->
      nitlc Gamma (var x) A
  | nitlc_app Gamma' Deltas M N u A :
      sty_permutation [Gamma] (Gamma' :: Deltas) ->
      nitlc Gamma' M (niarr u A) ->
      Forall2 (fun B Delta => nitlc Delta N B) u Deltas ->
      nitlc Gamma (app M N) A
  | nitlc_lam t M u A :
      ssim t (niarr u A) ->
      nitlc (cons u Gamma) M A ->
      nitlc Gamma (lam t M) (niarr u A).

Theorem nitlc_type_inference M Gamma0 t : stlc Gamma0 M t ->
  exists Gamma A,
    nitlc Gamma M A /\
    Forall2 (fun s u => u <> [] /\ Forall (ssim s) u) Gamma0 Gamma /\
    ssim t A.
