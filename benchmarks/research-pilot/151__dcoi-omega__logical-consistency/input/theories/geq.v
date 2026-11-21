Require Import imports.

Module Type geq_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice).

Definition econtext := list T.

Open Scope lattice_scope.

Definition elookup i Ξ (ℓ : T) := nth_error Ξ i = Some ℓ.

Inductive IOk (Ξ : econtext) (ℓ : T) : tm -> Prop :=
  | IO_Var i ℓ0 :
    elookup i Ξ ℓ0 ->
    ℓ0 ⊆ ℓ ->

    IOk Ξ ℓ (var_tm i)
  | IO_Univ i :

    IOk Ξ ℓ (tUniv i)
  | IO_Pi ℓ0 A B :
    IOk Ξ ℓ A ->
    IOk (ℓ0 :: Ξ) ℓ B ->

    IOk Ξ ℓ (tPi ℓ0 A B)
  | IO_Abs ℓ0 a :
    IOk (ℓ0 :: Ξ) ℓ a ->

    IOk Ξ ℓ (tAbs ℓ0 a)
  | IO_App a ℓ0 b :
    IOk Ξ ℓ a ->
    IOk Ξ ℓ0 b ->

    IOk Ξ ℓ (tApp a ℓ0 b)
  | IO_Void :
    IOk Ξ ℓ tVoid
  | IO_Absurd ℓ0 a:
    IOk Ξ ℓ0 a ->
    IOk Ξ ℓ (tAbsurd a)
  | IO_Refl :
    IOk Ξ ℓ tRefl
  | IO_Eq ℓ0 a b :
    ℓ0 ⊆ ℓ ->
    IOk Ξ ℓ0 a ->
    IOk Ξ ℓ0 b ->

    IOk Ξ ℓ (tEq ℓ0 a b)
  | IO_J ℓp t p :
    ℓp ⊆ ℓ ->
    IOk Ξ ℓ t ->
    IOk Ξ ℓp p ->

    IOk Ξ ℓ (tJ ℓp t p)

  | IO_Sig ℓ0 A B :
    IOk Ξ ℓ A ->
    IOk (ℓ0 :: Ξ) ℓ B ->

    IOk Ξ ℓ (tSig ℓ0 A B)

  | IO_Pack ℓ0 a b :
    IOk Ξ ℓ0 a ->
    IOk Ξ ℓ b ->

    IOk Ξ ℓ (tPack ℓ0 a b)

  | IO_Let ℓ0 ℓ1 a b :
    ℓ1 ⊆ ℓ ->
    IOk Ξ ℓ1 a ->
    IOk (ℓ1::ℓ0::Ξ) ℓ b ->

    IOk Ξ ℓ (tLet ℓ0 ℓ1 a b)

  | IO_Zero :
    IOk Ξ ℓ tZero

  | IO_Suc a :
    IOk Ξ ℓ a ->

    IOk Ξ ℓ (tSuc a)

  | IO_Ind ℓ0 a b c :
    ℓ0 ⊆ ℓ ->
    IOk Ξ ℓ0 a ->
    IOk (ℓ0 :: ℓ0 :: Ξ) ℓ0 b ->
    IOk Ξ ℓ0 c ->

    IOk Ξ ℓ (tInd ℓ0 a b c)

  | IO_Nat :

    IOk Ξ ℓ tNat

  | IO_Unit :

    IOk Ξ ℓ tUnit

  | IO_TT :

    IOk Ξ ℓ tTT

  | IO_Seq ℓ0 a b :
    ℓ0 ⊆ ℓ ->
    IOk Ξ ℓ0 a ->
    IOk Ξ ℓ b ->

    IOk Ξ ℓ (tSeq ℓ0 a b).

Inductive IEq (Ξ : econtext) (ℓ : T) : tm -> tm -> Prop :=
  | I_Var i ℓ0 :
    elookup i Ξ ℓ0 ->
    ℓ0 ⊆ ℓ ->

    IEq Ξ ℓ (var_tm i) (var_tm i)
  | I_Univ i :

    IEq Ξ ℓ (tUniv i) (tUniv i)
  | I_Pi ℓ0 A0 A1 B0 B1 :
    IEq Ξ ℓ A0 A1 ->
    IEq (ℓ0 :: Ξ) ℓ B0 B1 ->

    IEq Ξ ℓ (tPi ℓ0 A0 B0) (tPi ℓ0 A1 B1)
  | I_Abs ℓ0 a0 a1 :
    IEq (ℓ0 :: Ξ) ℓ a0 a1 ->

    IEq Ξ ℓ (tAbs ℓ0 a0) (tAbs ℓ0 a1)
  | I_App a0 a1 ℓ0 b0 b1 :
    IEq Ξ ℓ a0 a1 ->
    GIEq Ξ ℓ ℓ0 b0 b1 ->

    IEq Ξ ℓ (tApp a0 ℓ0 b0) (tApp a1 ℓ0 b1)
  | I_Void :
    IEq Ξ ℓ tVoid tVoid
  | I_Absurd a b :
    IEq Ξ ℓ (tAbsurd a) (tAbsurd b)
  | I_Refl :
    IEq Ξ ℓ tRefl tRefl
  | I_Eq ℓ0 a0 a1 b0 b1 :
    ℓ0 ⊆ ℓ ->
    IEq Ξ ℓ a0 a1 ->
    IEq Ξ ℓ b0 b1 ->

    IEq Ξ ℓ (tEq ℓ0 a0 b0) (tEq ℓ0 a1 b1)
  | I_J ℓp t0 t1 p0 p1 :
    ℓp ⊆ ℓ ->
    IEq Ξ ℓ t0 t1 ->
    IEq Ξ ℓ p0 p1 ->

    IEq Ξ ℓ (tJ ℓp t0 p0) (tJ ℓp t1 p1)
  | I_Sig ℓ0 A0 B0 A1 B1 :
    IEq Ξ ℓ A0 A1 ->
    IEq (ℓ0 :: Ξ) ℓ B0 B1 ->

    IEq Ξ ℓ (tSig ℓ0 A0 B0) (tSig ℓ0 A1 B1)

  | I_Pack ℓ0 a0 b0 a1 b1 :
    GIEq Ξ ℓ ℓ0 a0 a1 ->
    IEq Ξ ℓ b0 b1 ->

    IEq Ξ ℓ (tPack ℓ0 a0 b0) (tPack ℓ0 a1 b1)

  | I_Let ℓ0 ℓ1 a0 b0 a1 b1 :
    ℓ1 ⊆ ℓ ->
    IEq Ξ ℓ a0 a1 ->
    IEq (ℓ1::ℓ0::Ξ) ℓ b0 b1 ->

    IEq Ξ ℓ (tLet ℓ0 ℓ1 a0 b0) (tLet ℓ0 ℓ1 a1 b1)

  | I_Zero :
    IEq Ξ ℓ tZero tZero

  | I_Suc a0 a1 :
    IEq Ξ ℓ a0 a1 ->

    IEq Ξ ℓ (tSuc a0) (tSuc a1)

  | I_Ind ℓ0 a0 b0 c0 a1 b1 c1 :
    ℓ0 ⊆ ℓ ->
    IEq Ξ ℓ a0 a1 ->
    IEq (ℓ0 :: ℓ0 :: Ξ) ℓ b0 b1 ->
    IEq Ξ ℓ c0 c1 ->

    IEq Ξ ℓ (tInd ℓ0 a0 b0 c0) (tInd ℓ0 a1 b1 c1)

  | I_Nat :

    IEq Ξ ℓ tNat tNat

  | I_Unit :

    IEq Ξ ℓ tUnit tUnit

  | I_TT :

    IEq Ξ ℓ tTT tTT

  | I_Seq ℓ0 a0 a1 b0 b1 :
    ℓ0 ⊆ ℓ ->
    IEq Ξ ℓ a0 a1 ->
    IEq Ξ ℓ b0 b1 ->

    IEq Ξ ℓ (tSeq ℓ0 a0 b0) (tSeq ℓ0 a1 b1)

  with GIEq (Ξ : econtext) (ℓ : T) : T -> tm -> tm -> Prop :=
  | GI_Dist ℓ0 A B :
    ℓ0 ⊆ ℓ ->
    IEq Ξ ℓ A B ->

    GIEq Ξ ℓ ℓ0 A B
  | GI_InDist ℓ0 A B :
    ~ (ℓ0 ⊆ ℓ) ->

    GIEq Ξ ℓ ℓ0 A B.

Scheme IEq_ind' := Induction for IEq Sort Prop
      with GIEq_ind' := Induction for GIEq Sort Prop.

Combined Scheme IEq_mutual from IEq_ind', GIEq_ind'.

Definition iok_ren_ok ρ Ξ Δ := forall i ℓ, elookup i Ξ ℓ -> exists ℓ0, elookup (ρ i) Δ ℓ0 /\ ℓ0 ⊆ ℓ.

Definition iok_subst_ok ρ Ξ Δ := forall i ℓ, elookup i Ξ ℓ -> IOk Δ ℓ (ρ i).

End geq_sig.
