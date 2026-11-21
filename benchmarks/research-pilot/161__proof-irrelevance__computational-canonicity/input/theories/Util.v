From Stdlib Require Import Utf8 List Bool Setoid Morphisms Relation_Definitions Setoid Morphisms Relation_Definitions Relation_Operators.

Import ListNotations.

Notation "'∑' x .. y , p" := (sigT (λ x, .. (sigT (λ y, p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Inductive All {A} (P : A → Type) : list A → Type :=
| All_nil : All P []
| All_cons a l : P a → All P l → All P (a :: l).

Fixpoint rForall [A] (P : A → Prop) l :=
  match l with
  | [] => True
  | x :: l => P x ∧ rForall P l
  end.

Inductive OnOne2 {A} (R : A → A → Prop) : list A → list A → Prop :=
| OnOne2_hd a a' l : R a a' → OnOne2 R (a :: l) (a' :: l)
| OnOne2_tl a l l' : OnOne2 R l l' → OnOne2 R (a :: l) (a :: l').

Definition onSome [A] (P : A → Prop) (o : option A) : Prop :=
  match o with
  | Some a => P a
  | None => True
  end.

Definition onSomeb [A] (P : A → bool) (o : option A) : bool :=
  match o with
  | Some a => P a
  | None => true
  end.

Inductive OnSome [A] (P : A → Prop) : option A → Prop :=
| OnSome_None : OnSome P None
| OnSome_Some a : P a → OnSome P (Some a).

Definition onSomeT [A] (P : A → Type) (o : option A) : Type :=
  match o with
  | Some a => P a
  | None => unit
  end.

Inductive option_rel [A B] (R : A → B → Prop) : option A → option B → Prop :=
| option_none : option_rel R None None
| option_some x y : R x y → option_rel R (Some x) (Some y).

Inductive some_rel [A B] (R : A → B → Prop) : option A → option B → Prop :=
| some_rel_some a b : R a b → some_rel R (Some a) (Some b).

Notation "`=1`" := (pointwise_relation _ Logic.eq) (at level 80).
