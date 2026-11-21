Require Import Utf8.

Require Import Binding.Core.

Require Import Binding.Inc.

Require Import Binding.Properties.

Require Import Morphisms.

Record Ctx {V : Type} :=
  {dom : Set;
   arr :> dom -> V
  }.

Arguments Ctx V : clear implicits.

Definition mtC {V : Type} : Ctx V :=
  {| dom := Empty_set;
     arr x := match x with end
  |}.

Definition extC {V : Type} (v : V) (Γ : Ctx V) : Ctx V :=
  {| dom := inc (dom Γ);
     arr x := match x with
              | VZ => v
              | VS x => Γ x
              end
  |}.

Notation "'ε'" := mtC.

Notation "Γ ▹ v" := (extC v Γ) (at level 40, left associativity).

Class IntPureCore {V : Type} (F : V → Ctx V → Type) : Type :=
  int_pure : ∀ (Γ : Ctx V) v (x : dom Γ) (EQ : Γ x = v) , F v Γ.

Arguments int_pure {V F _ Γ}.

Record Arr {V : Type} {Γ Δ : Ctx V} : Type :=
  { apply_arr : dom Γ → dom Δ;
    arr_hom   : ∀ x : dom Γ, Δ (apply_arr x) = Γ x
  }.

Arguments Arr {V} Γ Δ.

Notation " A '[→]' B " := (Arr A B) (at level 100, no associativity) : type_scope.

Coercion apply_arr : Arr >-> Funclass.

Record Sub {V} {F : V → Ctx V → Type} {FP : IntPureCore F} (Γ Δ : Ctx V) : Type :=
  { apply_sub : ∀ v (x : dom Γ) (EQ : Γ x = v), F v Δ
  }.

Notation " A '[⇒]' B " := (Sub A B) (at level 100, no associativity) : type_scope.

Arguments apply_sub {V F FP Γ Δ}.

Coercion apply_sub : Sub >-> Funclass.

Instance ArrEqC {V} : EqIndCore (Arr (V := V)) :=
  λ A B f g, ∀ x, f x = g x.

Instance SubEqC {V F} {FP : IntPureCore (V := V) F} : EqIndCore Sub :=
  λ A B f g, ∀ v x EQ, f v x EQ = g v x EQ.

Global Instance ArrowCore_Set {V} : ArrowCore (Arr (V := V)) :=
  { arrow_id   := λ _,         {| apply_arr := λ x, x; arr_hom := λ x, eq_refl |}
  ; arrow_comp := λ _ _ _ f g, {| apply_arr := λ x, f (g x);
                                arr_hom := λ x, eq_trans (arr_hom f (g x)) (arr_hom g x) |}
  }.

Class IntPure {V} (F : V → Ctx V → Type) {FP : IntPureCore (V := V) F}
    {MapF : ∀ v, FunctorCore (F v)}
    {BndF : ∀ v, BindCore (Sub := Sub) (F v)} : Prop :=
  { fmap_int_pure : ∀ (Γ Δ : Ctx V) (f : Arr Γ Δ) v (x : dom Γ) (EQ : Γ x = v),
        fmap f (int_pure v x EQ) = int_pure v (f x) (eq_trans (arr_hom f x) EQ)
  ; bind_set_pure : ∀ (Γ Δ : Ctx V) (f : Sub Γ Δ) v (x : dom Γ) (EQ : Γ x = v),
      bind f (int_pure (IntPureCore := FP) v x EQ) = f v x EQ
  }.

Section IntInstances.

Context {V} {F : V → Ctx V → Type} {FP : IntPureCore F}.

Context {MapF : ∀ v, FunctorCore (Arr := Arr) (F v)}.

Context {BndF : ∀ v, BindCore (Sub := Sub) (F v)}.

Context {SPF : IntPure F}.

Global Instance SubstArrCore_Set : ArrowCore (Sub (V := V)) :=
    { arrow_id A := {| apply_sub := int_pure |};
      arrow_comp A B C f g := {| apply_sub := λ v x EQ, bind f (g v x EQ) |} }.

Global Instance SubstCore_Set : SubstCore Arr Sub :=
    λ Γ Δ f, {| apply_sub := λ v x EQ, int_pure v (f x) (eq_trans (arr_hom f x) EQ) |}.

Definition extFun v (Γ Δ : Ctx V) (f : Arr Γ Δ) : Arr (Γ ▹ v) (Δ ▹ v) :=
    @Build_Arr V (Γ ▹ v) (Δ ▹ v) (inc_map f)
      ltac:(intros [| x]; simpl; [reflexivity | exact (arr_hom f x)]).

Global Instance ALiftableCore_ext {v : V} : LiftableCore Arr (extC v) :=
    { lift := extFun v }.

Global Program Instance ShiftableCore_ext {v : V} : ShiftableCore Arr (extC v) :=
    λ A, {| apply_arr := VS : dom A → dom (A ▹ v) |}.

Global Instance SLiftableCore_ext {v : V} : LiftableCore Sub (extC v) :=
    { lift Γ Δ ρ :=
        {| apply_sub := λ u (x : dom (Γ ▹ v)),
                        match x with
                        | VZ   => λ EQ, int_pure u (VZ : dom (Δ ▹ v)) EQ
                        | VS y => λ EQ, shift (ρ u y EQ)
                        end
        |}
    }.

Global Instance SubstitutableCore_ext {v : V} : SubstitutableCore Sub (F v) (extC v) :=
    λ A u,
    {| apply_sub := λ w (x : dom (A ▹ v)),
                    match x with
                    | VZ => λ EQ, match EQ with eq_refl => u end
                    | VS y => int_pure w y
                    end
    |}.

End IntInstances.

Arguments int_pure {V F _ Γ v} /.
