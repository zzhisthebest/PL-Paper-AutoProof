Require Export Arith.EqNat.

Require Export PeanoNat.

Require Import Coq.Arith.Arith.

Require Import Coq.Program.Equality.

Require Import Coq.Lists.List.

Require Import Psatz.

Require Import Coq.Arith.Compare_dec.

Import ListNotations.

Require Import vars.

Fixpoint update {A} (σ : list A) (l : nat) (v : A) : list A :=
  match σ with
  | [] => σ
  | a :: σ' =>
      if (Nat.eqb l (length σ')) then (v :: σ') else (a :: (update σ' l v ))
  end.

Fixpoint insert {A} (σ : list A) (l : nat) (v : A) : list A :=
  match σ with
  | [] => σ
  | a :: σ' =>
      if (Nat.eqb l (length σ')) then (a :: v :: σ') else (a :: (insert σ' l v ))
  end.

Fixpoint indexr {X : Type} (n : nat) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (Nat.eqb n (length l')) then Some a else indexr n l'
  end.

Fixpoint delete_nth (n : nat) {A} (l : list A) : list A :=
  match l with
  | nil       => nil
  | cons x xs => if (Nat.eqb n (length xs)) then xs else x :: (delete_nth n xs)
  end.

Definition slength {A} (l : option (list A)) : nat :=
  match l with
  | None => 0
  | Some l' => length l'
  end.

Definition update' {A} (s : option (list A)) (o : nat) (v : A) : option (list A) :=
  match s with
  | None => None
  | Some c => Some (update c o v)
  end.

Fixpoint supdate {A} (σ : list (option (list (A)))) (l : loc) (o : offset) (v : A) : list (option (list (A))) :=
  match σ with
  | [] => σ
  | a :: σ' =>
      if (Nat.eqb l (length σ')) then ( (update' a o v) :: σ') else (a :: (supdate σ' l o v ))
  end.

Definition insert' {A} (s : option (list A)) (v : A) : option (list A) :=
  match s with
  | None => None
  | Some c => Some (v :: c)
  end.

Fixpoint cinsert {A} (σ : list (option (list (A)))) (l : loc) (v : A) : list (option (list (A))) :=
  match σ with
  | [] => σ
  | a :: σ' =>
      if (Nat.eqb l (length σ')) then
        insert' a v :: σ'
      else (a :: (cinsert σ' l v ))
  end.

Fixpoint sindexr {X : Type} (l : loc) (o : offset) (σ : list (list X)) : option X :=
  match σ with
    | [] => None
    | a :: σ' =>
      if (Nat.eqb l (length σ')) then indexr o a else sindexr l o σ'
  end.

Fixpoint sinsert {A} (s : list ((list (A)))) (l : loc) (x : A) : list (list (A)) :=
  match s with
  | [] => s
  | c :: s' =>
      if (Nat.eqb l (length s')) then
        ((x :: c) :: s')
      else (c :: (sinsert s' l x ))
  end.
