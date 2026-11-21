Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Require Import Stdlib.Init.Sumbool.

Require Import LibExtra.

Generalizable Variables A B.

Declare Scope syntax_scope.

Delimit Scope syntax_scope with S.

Open Scope syntax_scope.

Class Openable (A : Set) := open_rec : nat -> var -> A -> A.

Class FreeVar (A : Set) := fv : A -> vars.

Class SubstVar (A : Set) := subst_var : var -> var -> A -> A.

Bind Scope syntax_scope with Openable FreeVar SubstVar.

Arguments open_rec _ _ _ _ !_ /.

Arguments fv _ _ !_ /.

Arguments subst_var _ _ _ _ !_ /.

Class AbstractSyntax (A : Set) `(Openable A) `(FreeVar A) `(SubstVar A).

Notation "z '/[' x '->' y ']'" :=
  (subst_var x y z) (x at level 69, at level 7, left associativity) : syntax_scope.

Notation subst_vars := (vars_zip_map subst_var) (only parsing).

Notation "z '/[' xs '-->' ys ']'" :=
  (subst_vars xs ys z) (xs at level 69, at level 7, left associativity) : syntax_scope.

Definition subst_pvars `{AS: SubstVar A} `{AF: FreeVar A}
  (xs ys: list var) (a: A): A :=
    let (zs, _) := (var_freshes (from_list xs \u from_list ys \u fv a) (length ys))
    in a /[xs --> zs] /[zs --> ys].

Notation "z '//[' xs '-->' ys ']'" :=
  (subst_pvars xs ys z) (xs at level 69, at level 7, left associativity) : syntax_scope.

Notation open := (open_rec 0) (only parsing).

Definition open_depth_rec `{AS : Openable A} n x a d :=
  open_rec (n + d) x a.

Notation open_depth := (open_depth_rec 0).

Arguments open_depth_rec _ _ _ _ !_ _ /.

Definition closed `{AS: Openable A} a :=
  forall n x, open_rec n x a = a.

Fixpoint open_rec_vars `{AS : Openable A} (k: nat) (ys: list var) (X: A): A :=
  match ys with
  | nil => X
  | cons y ys => open_rec_vars (S k) ys (open_rec k y X)
  end.

Notation open_vars := (open_rec_vars 0) (only parsing).

Arguments open_rec_vars _ _ _ !_ _ /.

Notation "z '/[#' n '->' y ']'" :=
  (open_rec n y z) (n at level 69, at level 7, left associativity) : syntax_scope.

Notation "z '/[->' y ']'" :=
  (open y z) (at level 7, left associativity) : syntax_scope.

Notation "z '/[#' n '-->' ys ']'" :=
  (open_rec_vars n ys z) (n at level 69, at level 7, left associativity) : syntax_scope.

Notation "z '/[-->' ys ']'" :=
  (open_vars ys z) (at level 7, left associativity) : syntax_scope.

Class Sealable (A: Set) := seal_rec: nat -> var -> A -> A.

Bind Scope syntax_scope with Sealable.

Arguments seal_rec _ _ _ _ !_ /.

Notation seal := (seal_rec 0).

Definition sealed `{AS: Sealable A} a :=
  forall x, seal x a = a.

Definition seal_depth_rec `{AS: Sealable A} n x a d := seal_rec (n+d) x a.

Arguments seal_depth_rec _ _ _ _ !_ _ /.

Notation "z '/[->>' y ']'" :=
  (seal y z) (at level 7) : syntax_scope.

Notation "z '/[#' n '->>' y ']'" :=
  (seal_rec n y z) (n at level 69, at level 7) : syntax_scope.

Class DecideFv `(AS: AbstractSyntax A) := dec_fv : var -> A -> bool.

Arguments dec_fv _ _ _ _ _ _ _ !_ /.

Definition dec_notin_fv `{DFv: DecideFv A} x a := negb (dec_fv x a).

Arguments dec_notin_fv _ _ _ _ _ _ _ !_ /.

Class ReflectFv `(DFv: DecideFv A) :=
  reflect_fv : forall x a,
    (x \in fv a) <-> (dec_fv x a) = true.

Class Closing `(AS: AbstractSyntax A) :=
  close_rec : nat -> var -> A -> A.

Bind Scope syntax_scope with Closing.

Notation close := (close_rec 0).

Arguments close_rec : simpl never.

Definition close_depth_rec `{Cl : Closing A} n x a d :=
  close_rec (n + d) x a.

Notation close_depth := (close_depth_rec 0).

Arguments close_depth_rec _ _ _ _ _ _ _ _ !_ /.

Fixpoint close_rec_vars `{AS: AbstractSyntax A}{AC : Closing AS} (k: nat) (ys: list var) (X: A): A :=
  match ys with
  | nil => X
  | cons y ys => close_rec_vars (S k) ys (close_rec k y X)
  end.

Notation close_vars := (close_rec_vars 0) (only parsing).

Arguments close_rec_vars _ _ _ !_ _ /.

Notation "z '/[#' n '<-' x ']'" :=
  (close_rec n x z) (n at level 69, at level 7, left associativity) : syntax_scope.

Notation "z '/[#' n '<--' xs ']'" :=
  (close_rec_vars n xs z) (n at level 69, at level 7, left associativity) : syntax_scope.

Notation "z '/[<-' x ']'" :=
  (close x z) (x at level 69, at level 7, left associativity) : syntax_scope.

Notation "z '/[<--' xs ']'" :=
  (close_vars xs z) (xs at level 69, at level 7, left associativity) : syntax_scope.

Notation fv_env := (fv_in_values fv).

Notation subst_env x y := (map (subst_var x y)).

Notation subst_env_vars xs ys := (map (subst_vars xs ys)).
