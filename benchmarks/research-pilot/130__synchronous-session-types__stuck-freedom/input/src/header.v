From mathcomp Require Import ssreflect.seq all_ssreflect.

Require Import List String Coq.Arith.PeanoNat Relations ZArith Datatypes Setoid Morphisms Coq.Logic.Decidable Coq.Program.Basics Coq.Init.Datatypes.

Import ListNotations.

Open Scope list_scope.

From Paco Require Import paco.

Import ListNotations.

Notation fin := nat.

Notation part := string (only parsing).

Notation label := nat (only parsing).

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.

Inductive multiS {X : Type} (R : relation X) : relation X :=
  | multi_sing : forall (x y : X), R x y -> multiS R x y
  | multi_sstep : forall (x y z : X), R x y -> multiS R y z -> multiS R x z.

Inductive Forall2R {X Y} (P : X -> Y -> Prop) : list X -> list Y -> Prop :=
  | Forall2R_nil : forall ys, Forall2R P nil ys
  | Forall2R_cons : forall x xs y ys, P x y -> Forall2R P xs ys -> Forall2R P (x :: xs) (y :: ys).

Inductive Forall3 {A B C} : (A -> B -> C -> Prop) -> list A -> list B -> list C -> Prop :=
  | Forall3_nil : forall P, Forall3 P nil nil nil
  | Forall3_cons : forall P a b c xa xb xc, P a b c -> Forall3 P xa xb xc -> Forall3 P (a :: xa) (b :: xb) (c :: xc).

Inductive Forall3S {A} : (A -> A -> A -> Prop) -> list A -> list A -> list A -> Prop :=
  | Forall3s_nil0 : forall P xs, Forall3S P nil xs xs
  | Forall3s_nil1 : forall P xs, Forall3S P xs nil xs
  | Forall3s_cons : forall P a xa b xb c xc, P a b c -> Forall3S P xa xb xc -> Forall3S P (a :: xa) (b :: xb) (c :: xc).

Fixpoint SList {A} (lis : list (option A)) : Prop :=
  match lis with
    | Datatypes.Some x :: [] => True
    | _ :: xs                => SList xs
    | []                     => False
  end.

Fixpoint extendLis {A} (n : fin) (ST : option A) : list (option A) :=
  match n with
    | S m  => None :: extendLis m ST
    | 0    => [ST]
  end.

Fixpoint onth {A : Type} (n : fin) (lis : list (option A)) : option A :=
  match n with
    | S m =>
      match lis with
        | x::xs => onth m xs
        | []    => None
      end
    | 0   =>
      match lis with
        | x::xs => x
        | []    => None
      end
  end.

Fixpoint noneLis {A} (n : fin) : list (option A) :=
  match n with
    | 0 => nil
    | S m => None :: noneLis m
  end.

Fixpoint overwrite_lis {A} (n : fin) (x : (option A)) (xs : list (option A)) : list (option A) :=
  match xs with
    | y::xs => match n with
        | 0 => x :: xs
        | S k => y :: overwrite_lis k x xs
      end
    | nil   => match n with
        | 0 => [x]
        | S k => None :: overwrite_lis k x nil
      end
  end.

Definition Forall2_mono {X Y} {R T : X -> Y -> Prop} (HRT : forall x y, R x y -> T x y) :
      forall l m, Forall2 R l m -> Forall2 T l m :=
  fix loop l m h {struct h} :=
    match h with
    | Forall2_nil => Forall2_nil T
    | Forall2_cons _ _ _ _ h1 h2 => Forall2_cons _ _ (HRT _ _ h1) (loop _ _ h2)
    end.

Definition Forall2R_mono {X Y} {R T : X -> Y -> Prop} (HRT : forall x y, R x y -> T x y) :
      forall l m, Forall2R R l m -> Forall2R T l m :=
  fix loop l m h {struct h} :=
    match h with
    | Forall2R_nil xs => Forall2R_nil T xs
    | Forall2R_cons _ _ _ _ h1 h2 => Forall2R_cons _ _ _ _ _ (HRT _ _ h1) (loop _ _ h2)
    end.
