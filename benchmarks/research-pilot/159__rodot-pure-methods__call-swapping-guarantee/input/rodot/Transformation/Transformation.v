Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.

Require Import Context Equivalence Indep GeneralTyping.

Require Import Weakening.

Unset Auto Template Polymorphism.
Inductive TypedElement (AC AT A: Type): Type := typed_elem (G: AC) (T: AT) (a: A).
Set Auto Template Polymorphism.

Notation "'〈' G '⊢' a '∶' T '〉'" :=
  (typed_elem G T a) (at level 41, G at level 32).

Definition Transform (AC AT A: Type) := (TypedElement AC AT A) -> (TypedElement AC AT A) -> Prop.

Definition transform (AC AT A: Type) (Tr: Transform AC AT A) a b := Tr a b.

Notation " TEa '∼' trf '∼>' TEb " :=
  (transform trf TEa TEb) (at level 42).

Definition TrfCond TC T A := TypedElement TC T A -> Prop.

Definition trf_concat TC T A (trf1 trf2: Transform TC T A): Transform TC T A :=
    fun TEa TEb =>
      exists TEc,
      TEa ∼trf1∼> TEc /\
      TEc ∼trf2∼> TEb.

Definition trf_union TC T A (trf1 trf2: Transform TC T A): Transform TC T A :=
    fun TEa TEb =>
      TEa ∼trf1∼> TEb \/
      TEa ∼trf2∼> TEb.

Definition trf_inverse TC T A (trf: Transform TC T A): Transform TC T A :=
    fun TEa TEb =>
      TEb ∼trf∼> TEa.

Class ReflexiveTransform TC T A (trf: Transform TC T A) :=
  trf_reflexive TEa: TEa ∼trf∼> TEa.

Class SymmetricTransform TC T A (trf: Transform TC T A) :=
  trf_symmetric TEa TEb:
    TEa ∼trf∼> TEb ->
    TEb ∼trf∼> TEa.

Class TransitiveTransform C T A (trf: Transform C T A) :=
  trf_transitive TEa TEb TEc:
    TEa ∼trf∼> TEb ->
    TEb ∼trf∼> TEc ->
    TEa ∼trf∼> TEc.

Class ReflexiveIfTransform TC T A (Cond: TrfCond TC T A) (trf: Transform TC T A) :=
  trf_reflexive_if TEa: Cond TEa -> TEa ∼trf∼> TEa.

Class IdempotentTransformOp TC T A (trfop: Transform TC T A -> Transform TC T A) :=
  trf_op_idempotent trf: (trfop trf) = (trfop (trfop trf)).

Class TransformRequires TC T A (Cond: TrfCond TC T A) (trf: Transform TC T A) :=
  trf_requires TEa TEb:
    TEa ∼trf∼> TEb ->
    Cond TEa.

Class TransformPreserves TC T A (Cond: TrfCond TC T A) (trf: Transform TC T A) :=
  trf_preserves TEa TEb:
    TEa ∼trf∼> TEb ->
    Cond TEa ->
    Cond TEb.

Class TransformEnsures TC T A (Cond: _ -> _ -> Prop) (trf: Transform TC T A) :=
  trf_ensures TEa TEb:
    TEa ∼trf∼> TEb ->
    Cond TEa TEb.

Class TransformClosedOver TC T A (Cond: _ -> _ -> Prop) (trf: Transform TC T A) :=
  trf_closer_over TEa TEb TEc:
    TEa ∼trf∼> TEb ->
    Cond TEa TEc ->
    TEc ∼trf∼> TEb.

Class TransformShares TC T A (Cond: _ -> _ -> Prop) (trf: Transform TC T A) :=
  trf_shares TEa TEb TEc:
    TEa ∼trf∼> TEb ->
    TEa ∼trf∼> TEc ->
    Cond TEb TEc.

Notation TransformFunctional TC T A := (@TransformShares TC T A eq).

Class TransformCommute TC T A (trf1 trf2: Transform TC T A) :=
  trf_commute:
    trf_concat trf1 trf2 = trf_concat trf2 trf1.

Class TransformCompat TC T A (trf1 trf2: Transform TC T A) :=
  trf_compat TEa1 TEb1 TEa2 TEb2:
    TEa1 ∼trf1∼> TEb1 ->
    TEa1 ∼trf2∼> TEa2 ->
    TEb1 ∼trf2∼> TEb2 ->
    TEa2 ∼trf1∼> TEb2.

Class TransformCondCompat TC T A (Cond: _ -> _ -> Prop) (trf1 trf2: Transform TC T A) :=
  trf_cond_compat TEa1 TEb1 TEa2 TEb2:
    TEa1 ∼trf1∼> TEb1 ->
    TEa1 ∼trf2∼> TEa2 ->
    TEb1 ∼trf2∼> TEb2 ->
    Cond TEa2 TEb2 ->
    TEa2 ∼trf1∼> TEb2.

Inductive trf_iterate TC T A (Cond: _ -> Prop) (trf: Transform TC T A): Transform TC T A :=
| trf_iterate_0 TEa:
  Cond TEa ->
  TEa ∼(trf_iterate Cond trf)∼> TEa
| trf_iterate_S TEa TEb TEc:
  TEa ∼(trf_iterate Cond trf)∼> TEb ->
  TEb ∼trf∼> TEc ->
  TEa ∼(trf_iterate Cond trf)∼> TEc.

Definition trf_id_cond TC T A (Cond: _ -> Prop): Transform TC T A :=
  fun TEa TEb =>
    TEa = TEb /\ Cond TEa.

Definition TransformCondTypeIdentical TC T A (TEa TEb: TypedElement TC T A) :=
  match TEa,TEb with
    〈Ga ⊢ a ∶ Ta〉,〈Gb ⊢ b ∶ Tb〉 => Ga = Gb /\ Ta = Tb
  end.

Notation " TEa '∼' Cond '∼∼' trf '∼>' TEb " :=
  ((Cond TEa TEb) -> (transform trf TEa TEb)) (at level 42, no associativity).

Definition LiftCond := forall TC T A : Type, TypedElement TC T A -> TypedElement TC T A -> Prop.

Definition trf_liftcond_id: LiftCond := fun TC T A => (@eq (TypedElement TC T A)).

Definition trf_liftcond_true: LiftCond := fun TC T A TEa TEb => True.

Definition trf_liftcond_inverse (Cond: LiftCond): LiftCond := fun TC T A TEa TEb => Cond TC T A TEb TEa.

Class TransformLiftCondSymmetric (Cond: LiftCond):=
  trf_liftcond_symmetric TC T A TEa TEb:
    Cond TC T A TEa TEb ->
    Cond TC T A TEb TEa.

Definition ImplyTransformInd (TC T A: Type) (trf1 trf2: Transform TC T A) :=
  forall TEa TEb,
  trf1 TEa TEb ->
  trf2 TEa TEb.

Definition InverseTransformInd (TC1 TC2 T1 T2 A1 A2: Type) (trf: Transform TC1 T1 A1) (trfop: Transform TC1 T1 A1 -> Transform TC2 T2 A2) :=
  ImplyTransformInd (trfop trf) (trf_inverse (trfop (trf_inverse trf))).

Definition InverseTransformIndCond (TC1 TC2 T1 T2 A1 A2: Type) (Cond: LiftCond) (trf: Transform TC1 T1 A1) (trfop: LiftCond -> Transform TC1 T1 A1 -> Transform TC2 T2 A2) :=
  ImplyTransformInd (trfop Cond trf) (trf_inverse (trfop (trf_liftcond_inverse Cond) (trf_inverse trf))).

Definition CondTransformInd (TC T A: Type) (Cond: _ -> Prop) (trf1: Transform TC T A) :=
  forall TEa TEb,
  trf1 TEa TEb ->
  Cond TEa.

Definition ClosedTransformInd (TC T A: Type) (Cond: _ -> _ -> Prop)  (trf: Transform TC T A) :=
  forall TEa TEb,
  trf TEa TEb ->
  forall TEc,
  Cond TEa TEc ->
  trf TEc TEb.

Definition CondCompatTransformInd (TC T A: Type) (Cond: _ -> _ -> Prop)  (trf trf2: Transform TC T A) :=
  forall TEa TEb,
  trf TEa TEb ->
  forall TEc TEd,
  trf2 TEa TEc ->
  trf2 TEb TEd ->
  Cond TEc TEd ->
  trf TEc TEd.
