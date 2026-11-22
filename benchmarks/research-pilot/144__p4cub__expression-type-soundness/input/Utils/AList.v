Require Import Coq.Classes.EquivDec.

Require Import Coq.Lists.List.

Require Import Coq.Sorting.Permutation.

Require Import Stdlib.Init.Sumbool.

Require Coq.ssr.ssrbool.

Require Coq.Strings.String.

Require Import Coq.Classes.Morphisms Poulet4.Utils.Utils.

Import ListNotations.

Definition AList
    (K V: Type)
    (R: Relation_Definitions.relation K)
    `{Equivalence K R} :=
  list (K * V)
.

Definition sublist {A} (l1 l2: list A): Prop := exists l3, Permutation (l1 ++ l3) l2.

Section AList.

Context {K V: Type}.

Context {R: Relation_Definitions.relation K}.

Context `{H: Equivalence K R}.

Context {KEqDec: EqDec K R}.

Definition get (l: AList K V R) (k: K) : option V :=
    let filter := fun '(k', _) =>
      if KEqDec k k' then true else false in
    match List.find filter l with
    | None => None
    | Some (k, v) => Some v
    end
  .

Fixpoint set (l: AList K V R) (k: K) (v: V) : option (AList K V R) :=
    match l with
    | (k', v') :: l' =>
      if KEqDec k k'
      then Some ((k, v) :: l')
      else match set l' k v with
           | Some l'' => Some ((k', v') :: l'')
           | None => None
           end
    | nil =>
      None
    end.

Fixpoint set_some (l: AList K V R) (k: K) (v: V) : (AList K V R) :=
    match l with
    | (k', v') :: l' =>
      if KEqDec k k'
      then ((k, v) :: l')
      else ((k', v') :: (set_some l' k v))
    | nil =>[(k, v)]
    end.

Fixpoint key_unique (l : AList K V R) : bool :=
    match l with
    | [] => true
    | (k, _) :: tl =>
      match get tl k with
      | Some _ => false
      | None => key_unique tl
      end
    end.

Fixpoint filter (l : AList K V R) (f : K -> bool) : (AList K V R) :=
    match l with
    | [] => []
    | (k, v) :: tl =>
      if f k then (k, v) :: (filter tl f)
      else filter tl f
    end.

Definition all_values {A B} (hold_one_value : A -> B -> Prop) :
    AList K A R -> AList K B R -> Prop :=
    Forall2 (fun a b => fst a = fst b /\ hold_one_value (snd a) (snd b)).

Definition keys (c : AList K V R) : list K :=
    List.map fst c.

Definition map_values {W} (f : V -> W) (c : AList K V R) : AList K W R :=
    List.map (fun '(k, v) => (k, f v)) c.

End AList.

Definition StringAList V := AList String.string V eq.
