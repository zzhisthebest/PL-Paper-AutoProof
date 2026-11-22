Require Export Poulet4.Monads.Option Coq.Classes.EquivDec.

Require Import Basics.

Definition pipeline {A B : Type} (x : A) (f : A -> B) : B := f x.

Infix "▷" := pipeline (at level 45, left associativity).

Infix "∘" := compose (at level 40, left associativity).

Infix "$" := apply (at level 41, right associativity).

Section MapProd.

Context {A B C : Type}.

Variable f : A -> B.

Definition map_fst '((a,c) : A * C) : B * C := (f a, c).

Definition map_snd '((c,a) : C * A) : C * B := (c, f a).

End MapProd.

Fixpoint n_compose {A : Type} (n : nat) (f : A -> A) (x : A) : A :=
  match n with
  | O => x
  | S n => n_compose n f (f x)
  end.

Section Curry3.

Context {A B C D : Type}.

Definition curry3
             (f : A * B * C -> D) : A -> B -> C -> D :=
    fun a b c => f (a,b,c).

Definition uncurry3
             (f : A -> B -> C -> D) : A * B * C -> D :=
    fun '(a,b,c) => f a b c.

End Curry3.

Section Curry4.

Context {A B C D E : Type}.

Definition curry4  (f : A * B * C * D -> E) : A -> B -> C -> D -> E :=
    fun a b c d => f (a,b,c,d).

Definition uncurry4 (f : A -> B -> C -> D -> E) : A * B * C * D -> E :=
    fun '(a,b,c,d) => f a b c d.

End Curry4.

Section Triple.

Context {A B C : Type}.

Definition triple_1 '((a,_,_) : A * B * C) : A := a.

Definition triple_2 '((_,b,_) : A * B * C) : B := b.

Definition triple_3 '((_,_,c) : A * B * C) : C := c.

End Triple.

Section Fourple.

Context {A B C D : Type}.

Definition fourple_1 '((a,_,_,_) : A * B * C * D) : A := a.

Definition fourple_2 '((_,b,_,_) : A * B * C * D) : B := b.

Definition fourple_3 '((_,_,c,_) : A * B * C * D) : C := c.

Definition fourple_4 '((_,_,_,d) : A * B * C * D) : D := d.

End Fourple.

Definition
  map_sum
  {A B C D : Type} (f : A -> B) (g : C -> D) (e : A + C) : B + D :=
  match e with
  | inl a => inl (f a)
  | inr b => inr (g b)
  end.

Section OExists.

Context {A : Set}.

Variable P : A -> Prop.

Variant OExists : option A -> Prop :=
    OExist_some a :
      P a -> OExists (Some a).

End OExists.

Section OptionEffect.
Polymorphic Universes a b c.

Polymorphic Context {A : Type@{a}} {B : Type@{b}} {C : Type@{a}}.

Polymorphic Variable default : C.

Polymorphic Variable f : A -> B * C.

Polymorphic Variable R : A -> B -> C -> Prop.

Polymorphic Definition omap_effect (o : option A) : option B * C :=
    match o with
    | Some a => let '(b, c) := f a in (Some b, c)
    | None   => (None, default)
    end.

Polymorphic Variant orelate_effect : option A -> option B -> C -> Prop :=
    | orelate_effect_some a b c :
      R a b c ->
      orelate_effect (Some a) (Some b) c
    | orelate_effect_none :
      orelate_effect None None default.

End OptionEffect.

Section Forall_Sum.
Polymorphic Universes a b.

Polymorphic Context {A : Type@{a}} {B : Type@{b}}.

Polymorphic Variables (P : A -> Prop) (Q : B -> Prop).

Polymorphic Variant SumForall : A + B -> Prop :=
    | Forall_inl a : P a -> SumForall (inl a)
    | Forall_inr b : Q b -> SumForall (inr b).

End Forall_Sum.

Reserved Infix "`^" (at level 10, left associativity).

Fixpoint mapply {A : Set} (f : A -> A) (m : nat) (a : A) : A :=
  match m with
  | O => a
  | S m => f $ f `^ m a
  end
where "f `^ m" := (mapply f m).

Section mapply.

Context {A : Set}.

Variable f : A -> A.

End mapply.
