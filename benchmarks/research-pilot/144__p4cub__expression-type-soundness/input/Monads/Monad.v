Require Import Coq.Lists.List.

Require Import Coq.Program.Basics.

Class Monad (M : Type -> Type) : Type :=
  { mret : forall {A}, A -> M A;
    mbind : forall {A B}, M A -> (A -> M B) -> M B
  }.

Declare Scope monad_scope.

Delimit Scope monad_scope with monad.

Notation "c >>= f" := (@mbind _ _ _ _ c f) (at level 50, left associativity) : monad_scope.

Notation "f =<< c" := (@mbind _ _ _ _ c f) (at level 51, right associativity) : monad_scope.

Notation "x <- c1 ;; c2" := (@mbind _ _ _ _ c1 (fun x => c2))
  ( at level 100, c1 at next level,
    format "x  '<-'  c1 ';;' '//' c2",
    right associativity
  ) : monad_scope.

Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
  (at level 61, right associativity) : monad_scope.

Notation "'let*' x ':=' c1 'in' c2" := (@mbind _ _ _ _ c1 (fun x => c2))
  ( at level 61, x pattern,
    format "'let*'  x  ':='  c1  'in' '//' c2", c1 at next level,
    right associativity
  ) : monad_scope.

Notation "'let*' ' x ':=' c1 'in' c2" := (@mbind _ _ _ _ c1 (fun x => c2))
  ( at level 61, x pattern,
    format "'let*'  ' x  ':='  c1  'in' '//' c2", c1 at next level,
    right associativity
  ) : monad_scope.

Open Scope monad.

Fixpoint sequence {A} {m: Type -> Type} {M : Monad m} (acts: list (m A)) : m (list A) :=
  match acts with
  | nil => mret nil
  | x :: xs =>
    let* t    := x in
    let* rest := @sequence A m M xs in
    mret (t :: rest)
  end.

Fixpoint asequence {K A} {m: Type -> Type} {M : Monad m} (acts: list (K * m A)) : m (list (K * A)) :=
  match acts with
  | nil => mret nil
  | (k, x) :: xs =>
    let* t    := x in
    let* rest := @asequence K A m M xs in
      mret ((k, t) :: rest)
  end.

Definition fold_left_monad
  {A B : Type} {m : Type -> Type} {M : Monad m}
  (f : A -> B -> m A) (l : list B) (a : A) : m A :=
  List.fold_left
    (fun ma b => let* a := ma in f a b)
    l (mret a).

Definition fold_right_monad
  {A B : Type} {m : Type -> Type} {M : Monad m}
  (f : B -> A -> m A) (a : A) : list B -> m A :=
  List.fold_right
    (fun b ma => ma >>= f b) (mret a).

Definition map_monad {A B : Type} {m : Type -> Type} {M : Monad m} (f : A -> m B) : list A -> m (list B) :=
  compose sequence (List.map f).

Definition lift_monad {A B} {m: Type -> Type} {M : Monad m} (f: A -> B) (ma : m A) : m B :=
  ma >>= fun a => mret (f a).

Notation "c '>>|' f" := (lift_monad f c) (at level 50, left associativity) : monad_scope.

Notation "x '<<|' c1 ;; c2" := (lift_monad (fun x => c2) c1)
  ( at level 100, c1 at next level,
    format "x  '<<|'  c1 ';;' '//' c2",
    right associativity
  ) : monad_scope.

Notation "'let^' x ':=' c1 'in' c2" := (@lift_monad _ _ _ _ (fun x => c2) c1)
  ( at level 61, x pattern,
    format "'let^'  x  ':='  c1  'in' '//' c2", c1 at next level,
    right associativity
  ) : monad_scope.

Notation "'let^' ' x ':=' c1 'in' c2" := (@lift_monad _ _ _ _ (fun x => c2) c1)
  ( at level 61, x pattern,
    format "'let^'  ' x  ':='  c1  'in' '//' c2", c1 at next level,
    right associativity
  ) : monad_scope.

Definition opt_sequence
  {A} {m : Type -> Type} `{M : Monad m}
  (o : option (list (m A))) : m (option (list A)) :=
  match o with
  | Some l => sequence l >>| Some
  | None   => mret None
  end.
