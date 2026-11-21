Require Import List.

Require Import Relation_Definitions.

Require Import Coq.Arith.Arith.

Import Relation_Operators.

Import ListNotations.

Definition uncurry {A B C : Type} (X : A -> B -> C) : (A * B) -> C := fun p => (X (fst p) (snd p)).

Definition curry {A B C : Type} (X : (A * B) -> C) : A -> B -> C := fun a b => X (a, b).

Definition ForallCrossPairs {L R : Type} (P : L -> R -> Prop) (ls : list L) (rs : list R) : Prop
:= Forall (fun l => Forall (P l) rs) ls.

Fixpoint map_in_incl {A B : Type} (l : list A) (f : forall a : A, In a l -> B) (l' : list A) : incl l' l -> list B
:= match l' with
   | nil => fun _ => nil
   | cons a l' => fun l'l => cons (f a (l'l a (or_introl (eq_refl a)))) (map_in_incl l f l' (fun a' a'inl' => l'l a' (or_intror a'inl')))
   end.

Definition map_in {A B : Type} (l : list A) (f : forall a : A, In a l -> B) : list B
:= map_in_incl l f l (incl_refl l).
