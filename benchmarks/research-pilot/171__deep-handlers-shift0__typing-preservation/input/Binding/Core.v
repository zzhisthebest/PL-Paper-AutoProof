Require Import Utf8.

Require Import RelationClasses.

Require Vector.

Section Core.

Context {Obj : Type}.

Section Arrows.

Class ArrowCore (Arr : Obj → Obj → Type) : Type :=
  { arrow_id   : ∀ A, Arr A A
  ; arrow_comp : ∀ A B C, Arr B C → Arr A B → Arr A C
  ; arrow_eq   : ∀ A B, Arr A B → Arr A B → Prop
  }.

Global Arguments arrow_id   {Arr _ A}.

Global Arguments arrow_comp {Arr _ A B C}.

Global Arguments arrow_eq   {Arr _ A B}.

Class Arrow (Arr : Obj → Obj → Type) {AC : ArrowCore Arr} : Prop :=
  { arrow_eq_refl : ∀ A B (f : Arr A B), arrow_eq f f
  ; arrow_eq_symm : ∀ A B (f g : Arr A B),
      arrow_eq f g → arrow_eq g f
  ; arrow_eq_trans : ∀ A B (f g h : Arr A B),
      arrow_eq f g → arrow_eq g h → arrow_eq f h
  ; arrow_comp_id_l : ∀ A B (f : Arr A B),
      arrow_eq (arrow_comp arrow_id f) f
  ; arrow_comp_id_r : ∀ A B (f : Arr A B),
      arrow_eq (arrow_comp f arrow_id) f
  ; arrow_comp_assoc : ∀ A B C D (f : Arr C D) (g : Arr B C) (h : Arr A B),
      arrow_eq (arrow_comp (arrow_comp f g) h) (arrow_comp f (arrow_comp g h))
  ; arrow_comp_proper : ∀ A B C (f₁ f₂ : Arr B C) (g₁ g₂ : Arr A B)
                          (EQf : arrow_eq f₁ f₂) (EQg : arrow_eq g₁ g₂),
      arrow_eq (arrow_comp f₁ g₁) (arrow_comp f₂ g₂)
  }.

Context {Arr : Obj → Obj → Type} {AC : ArrowCore Arr}.

Class IsMapCore {F : Obj → Type} (map : ∀ A B, Arr A B → F A → F B).

Definition fmap {F : Obj → Type} {map : ∀ A B, Arr A B → F A → F B}
  {MapG : IsMapCore map} {A B : Obj}
  (f : Arr A B) : F A → F B := map _ _ f.

Class FMap {F : Obj → Type} (map : ∀ A B, Arr A B → F A → F B)
    {MapF : IsMapCore map} : Prop :=
  { map_id       : ∀ A (f : Arr A A) (t : F A),
      arrow_eq f arrow_id → fmap f t = t
  ; map_map_comp : ∀ A B C (f : Arr B C) (g : Arr A B) h (t : F A),
      arrow_eq (arrow_comp f g) h → fmap f (fmap g t) = fmap h t
  }.

Global Arguments map_id       {F map MapF _ A}.

Global Arguments map_map_comp {F map MapF _ A B C}.

End Arrows.

Section Substitutions.

Section PreSubst.

Class PreSubstCore (Sub : Obj → Obj → Type) : Type :=
  { subst_pure : ∀ A, Sub A A
  ; subst_eq   : ∀ A B, Sub A B → Sub A B → Prop
  }.

Global Arguments subst_pure {Sub _ A}.

Global Arguments subst_eq   {Sub _ A B}.

Class PreSubst (Sub : Obj → Obj → Type) {PSC : PreSubstCore Sub} : Prop :=
  { subst_eq_refl     : ∀ A B (f : Sub A B), subst_eq f f
  ; subst_eq_symm     : ∀ A B (f g : Sub A B),
      subst_eq f g → subst_eq g f
  ; subst_eq_trans    : ∀ A B (f g h : Sub A B),
      subst_eq f g → subst_eq g h → subst_eq f h
  }.

Context {Sub : Obj → Obj → Type} {PSC : PreSubstCore Sub}.

End PreSubst.

Class SubstCore
    (Arr : Obj → Obj → Type) {AC : ArrowCore Arr}
    (Sub : Obj → Obj → Type) {PSC : PreSubstCore Sub} : Type :=
  { arrow_subst_comp : ∀ A B C, Arr B C → Sub A B → Sub A C
  ; subst_comp       : ∀ A B C, Sub B C → Sub A B → Sub A C
  }.

Global Arguments arrow_subst_comp {Arr AC Sub PSC _ A B C}.

Global Arguments subst_comp       {Arr AC Sub PSC _ A B C}.

Definition of_arrow
    {Arr : Obj → Obj → Type} {AC  : ArrowCore Arr}
    {Sub : Obj → Obj → Type} {PSC : PreSubstCore Sub}
    {SC  : SubstCore Arr Sub}
    {A B : Obj} (f : Arr A B) : Sub A B :=
  arrow_subst_comp f subst_pure.

Class Subst
    (Arr : Obj → Obj → Type) {AC  : ArrowCore Arr}
    (Sub : Obj → Obj → Type) {PSC : PreSubstCore Sub}
    {SC : SubstCore Arr Sub} : Prop :=
  { arrow_subst_comp_id : ∀ A B (f : Sub A B),
      subst_eq (arrow_subst_comp arrow_id f) f
  ; arrow_subst_assoc   : ∀ A B C D (f : Arr C D) (g : Sub B C) (h : Sub A B),
      subst_eq (subst_comp (arrow_subst_comp f g) h) (arrow_subst_comp f (subst_comp g h))
  ; arrow_subst_proper  : ∀ A B C (f₁ f₂ : Arr B C) (g₁ g₂ : Sub A B)
                            (EQf : arrow_eq f₁ f₂) (EQg : subst_eq g₁ g₂),
      subst_eq (arrow_subst_comp f₁ g₁) (arrow_subst_comp f₂ g₂)
  ; arrow_comp_subst    : ∀ A B C D (f : Arr C D) (g : Arr B C) (h : Sub A B),
      subst_eq (arrow_subst_comp (arrow_comp f g) h) (arrow_subst_comp f (arrow_subst_comp g h))
  ; subst_comp_pure_l   : ∀ A B (f : Sub A B),
      subst_eq (subst_comp subst_pure f) f
  ; subst_comp_pure_r   : ∀ A B (f : Sub A B),
      subst_eq (subst_comp f subst_pure) f
  ; subst_comp_assoc    : ∀ A B C D (f : Sub C D) (g : Sub B C) (h : Sub A B),
      subst_eq (subst_comp (subst_comp f g) h) (subst_comp f (subst_comp g h))
  ; subst_comp_proper   : ∀ A B C (f₁ f₂ : Sub B C) (g₁ g₂ : Sub A B)
                            (EQf : subst_eq f₁ f₂) (EQg : subst_eq g₁ g₂),
      subst_eq (subst_comp f₁ g₁) (subst_comp f₂ g₂)
  }.

Context {Arr : Obj → Obj → Type} {AC  : ArrowCore Arr}.

Context {Sub : Obj → Obj → Type} {PSC : PreSubstCore Sub}.

Context {SC  : SubstCore Arr Sub}.

Class IsBindCore {F : Obj → Type} (bnd : ∀ A B, Sub A B → F A → F B).

Definition bind {F : Obj → Type} {bnd : ∀ A B, Sub A B → F A → F B}
  {BindF : IsBindCore bnd} {A B : Obj}
  (f : Sub A B) : F A → F B := bnd _ _ f.

Class BindMap {F : Obj → Type}
    (map : ∀ A B, Arr A B → F A → F B) {MapF : IsMapCore map}
    (bnd : ∀ A B, Sub A B → F A → F B) {BindF : IsBindCore bnd} : Prop :=
  { bind_map_comp : ∀ A B B' C
      (f  : Sub B C)  (g : Arr A B)
      (g' : Arr B' C) (f' : Sub A B') t,
      subst_eq (subst_comp f (of_arrow g)) (arrow_subst_comp g' f') →
      bind f (fmap g t) = fmap g' (bind f' t)
  }.

Class Bind {F : Obj → Type} (bnd : ∀ A B, Sub A B → F A → F B)
    {BindF : IsBindCore bnd} : Prop :=
  { bind_pure  : ∀ A (f : Sub A A) (t : F A),
      subst_eq f subst_pure → bind f t = t
  ; bind_bind_comp : ∀ A B C (f : Sub B C) (g : Sub A B) h (t : F A),
      subst_eq (subst_comp f g) h → bind f (bind g t) = bind h t
  }.

End Substitutions.

Section Lifting.

Class ALiftableCore (Arr : Obj → Obj → Type) (G : Obj → Obj) :=
  liftA : ∀ A B, Arr A B → Arr (G A) (G B).

Class SLiftableCore (Sub : Obj → Obj → Type) (G : Obj → Obj) :=
  liftS : ∀ A B, Sub A B → Sub (G A) (G B).

Global Arguments liftA {Arr G _ A B}.

Global Arguments liftS {Sub G _ A B}.

Fixpoint liftAn {Arr G} {ALC : ALiftableCore Arr G} {A B : Obj}
         n (f : Arr A B) : Arr (Nat.iter n G A) (Nat.iter n G B) :=
  match n with
  | O => f
  | S n => liftA (liftAn n f)
  end.

Fixpoint liftSn {Sub G} {ALC : SLiftableCore Sub G} {A B : Obj}
         n (f : Sub A B) : Sub (Nat.iter n G A) (Nat.iter n G B) :=
  match n with
  | O => f
  | S n => liftS (liftSn n f)
  end.

Context (Arr : Obj → Obj → Type) {AC  : ArrowCore Arr}.

Context (Sub : Obj → Obj → Type) {PSC : PreSubstCore Sub}.

Context {SC : SubstCore Arr Sub}.

Class ALiftable (G : Obj → Obj) {ALC : ALiftableCore Arr G} : Prop :=
  { liftA_id    : ∀ A (f : Arr A A),
      arrow_eq f arrow_id → arrow_eq (liftA f) arrow_id
  ; liftA_comp  : ∀ A B C (f : Arr B C) (g : Arr A B) h,
      arrow_eq (arrow_comp f g) h →
      arrow_eq (arrow_comp (liftA f) (liftA g)) (liftA h)
  ; liftA_proper : ∀ A B (f₁ f₂ : Arr A B) (EQf : arrow_eq f₁ f₂),
      arrow_eq (liftA f₁) (liftA f₂)
  }.

Class ASLiftable (G : Obj → Obj)
    {ALC : ALiftableCore Arr G} {SLC : SLiftableCore Sub G} : Prop :=
  liftS_liftA_comp : ∀ A B B' C
      (f  : Sub B C)  (g : Arr A B)
      (g' : Arr B' C) (f' : Sub A B'),
      subst_eq (subst_comp f (of_arrow g)) (arrow_subst_comp g' f') →
      subst_eq
        (subst_comp (liftS f) (of_arrow (liftA g)))
        (arrow_subst_comp (liftA g') (liftS f')).

Class SLiftable (G : Obj → Obj) {SLC : SLiftableCore Sub G} : Prop :=
  { liftS_pure  : ∀ A (f : Sub A A),
      subst_eq f subst_pure → subst_eq (liftS f) subst_pure
  ; liftS_comp  : ∀ A B C (f : Sub B C) (g : Sub A B) h,
      subst_eq (subst_comp f g) h →
      subst_eq (subst_comp (liftS f) (liftS g)) (liftS h)
  ; liftS_proper : ∀ A B (f₁ f₂ : Sub A B) (EQf : subst_eq f₁ f₂),
      subst_eq (liftS f₁) (liftS f₂)
  }.

End Lifting.

Global Arguments liftA_id   {Arr AC G ALC _ A}.

Global Arguments liftA_comp {Arr AC G ALC _ A B C}.

Global Arguments liftS_liftA_comp {Arr AC Sub PSC SC G ALC SLC _ A B B' C}.

Global Arguments liftS_pure {Arr AC Sub PSC SC G SLC _ A}.

Global Arguments liftS_comp {Arr AC Sub PSC SC G SLC _ A B C}.

Section Shifting.

Class ShiftableCore (Arr : Obj → Obj → Type) (Inc : Obj → Obj) : Type :=
  mk_shift : ∀ A : Obj, Arr A (Inc A).

Global Arguments mk_shift {Arr Inc _ A}.

Definition shift
  {Arr : Obj → Obj → Type}
  {F   : Obj → Type} {map} {MapF : IsMapCore (F:=F) map}
  {Inc : Obj → Obj} {Sh : ShiftableCore Arr Inc}
  {A : Obj}
  (a : F A) : F (Inc A) := fmap mk_shift a.

Context (Arr : Obj → Obj → Type) {AC : ArrowCore Arr}.

Context (Sub : Obj → Obj → Type) {PSC : PreSubstCore Sub}.

Context {SC  : SubstCore Arr Sub}.

Context (Inc : Obj → Obj) {Sh : ShiftableCore Arr Inc}.

Class LiftAShift {ALC : ALiftableCore Arr Inc} : Prop :=
  liftA_mk_shift_comm : ∀ (A B : Obj) (f : Arr A B),
    arrow_eq (arrow_comp (liftA f) mk_shift) (arrow_comp mk_shift f).

Class LiftSShift {SLC : SLiftableCore Sub Inc} : Prop :=
  liftS_mk_shift_comm : ∀ (A B : Obj) (f : Sub A B),
    subst_eq
      (subst_comp (liftS f) (of_arrow mk_shift))
      (arrow_subst_comp mk_shift f).

End Shifting.

Global Arguments liftA_mk_shift_comm {Arr AC Inc Sh ALC _ A B}.

Global Arguments liftS_mk_shift_comm {Arr AC Sub PSC SC Inc Sh SLC _ A B}.

Section Substituting.

Class SubstitutableCore
    (Sub : Obj → Obj → Type) (F : Obj → Type) (Inc : Obj → Obj) : Type :=
  mk_subst : ∀ A : Obj, F A → Sub (Inc A) A.

Global Arguments mk_subst {Sub F Inc _ A} x.

Definition subst
  {Sub : Obj → Obj → Type}
  {G   : Obj → Type} {bnd} {BindG : IsBindCore (F:=G) bnd}
  {F   : Obj → Type} {Inc : Obj → Obj} {Sb : SubstitutableCore Sub F Inc}
  {A : Obj}
  (a : G (Inc A)) (v : F A) : G A := bind (mk_subst v) a.

Context (Arr : Obj → Obj → Type) {AC : ArrowCore Arr}.

Context (Sub : Obj → Obj → Type) {PSC : PreSubstCore Sub}.

Context {SC  : SubstCore Arr Sub}.

Context (F : Obj → Type) (Inc : Obj → Obj) {Sb : SubstitutableCore Sub F Inc}.

Class SubstShift {Sh : ShiftableCore Arr Inc} : Prop :=
  subst_shift_pure : ∀ (A : Obj) (v : F A),
    subst_eq (subst_comp (mk_subst v) (of_arrow mk_shift)) subst_pure.

Class SubstFMap
  {map : ∀ A B : Obj, Arr A B → F A → F B} {MapF : IsMapCore map}
  {ALC : ALiftableCore Arr Inc} : Prop :=
  map_mk_subst_comm : ∀ (A B : Obj) (f : Arr A B) (v : F A),
    subst_eq
      (arrow_subst_comp f (mk_subst v))
      (subst_comp (mk_subst (fmap f v)) (of_arrow (liftA f))).

Class SubstBind
  {bnd : ∀ A B : Obj, Sub A B → F A → F B} {BndF : IsBindCore bnd}
  {SLC : SLiftableCore Sub Inc} : Prop :=
  bind_mk_subst_comm : ∀ (A B : Obj) (f : Sub A B) (v : F A),
    subst_eq
      (subst_comp f (mk_subst v))
      (subst_comp (mk_subst (bind f v)) (liftS f)).

End Substituting.

Global Arguments subst_shift_pure {Arr AC Sub PSC SC F Inc Sb Sh _ A}.

Global Arguments
  map_mk_subst_comm {Arr AC Sub PSC SC F Inc Sb map MapF ALC _ A B}.

Global Arguments
  bind_mk_subst_comm {Arr AC Sub PSC SC F Inc Sb bnd BndF SLC _ A B}.

End Core.
