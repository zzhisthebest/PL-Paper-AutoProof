Require Import imports par geq conv syntax.

Module Type typing_sig
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq).

Definition context := list (T * tm).

Inductive lookup : nat -> context -> T -> tm -> Prop :=
  | here ℓ A Γ : lookup 0 ((ℓ, A) :: Γ) ℓ (A ⟨shift⟩)
  | there n A Γ ℓ B :
      lookup n Γ ℓ A -> lookup (S n) (B :: Γ) ℓ (A ⟨shift⟩).

Definition lookup_good_renaming ξ Γ Δ :=
  forall i ℓ A, lookup i Γ ℓ A -> exists ℓ0, lookup (ξ i) Δ ℓ0 A⟨ξ⟩ /\ ℓ0 ⊆ ℓ.

Reserved Notation "Γ ⊢ a ; ℓ ∈ A" (at level 70).

Reserved Notation "⊢ Γ" (at level 70).

Definition c2e : context -> econtext := map (fun '(ℓ, _) => ℓ).

Inductive Wt : context -> T -> tm -> tm -> Prop :=
| T_Var Γ ℓ0 ℓ i A :
  ⊢ Γ ->
  lookup i Γ ℓ0 A ->
  ℓ0 ⊆ ℓ ->

  Γ ⊢ (var_tm i) ; ℓ ∈ A

| T_Pi Γ i j ℓ ℓ0 A B :
  Γ ⊢ A ; ℓ ∈ (tUniv i) ->
  ((ℓ0, A) :: Γ) ⊢ B ; ℓ ∈ (tUniv j) ->

  Γ ⊢ (tPi ℓ0 A B) ; ℓ ∈ (tUniv (max i j))

| T_Abs Γ ℓ ℓ0 ℓ1 A a B i :
  Γ ⊢ (tPi ℓ0 A B) ; ℓ1 ∈ (tUniv i) ->
  ((ℓ0, A) :: Γ) ⊢ a ; ℓ ∈ B ->

  Γ ⊢ (tAbs ℓ0 a) ; ℓ ∈ (tPi ℓ0 A B)

| T_App Γ ℓ ℓ0 a A B b :
  Γ ⊢ a ; ℓ ∈ (tPi ℓ0 A B) ->
  Γ ⊢ b ; ℓ0 ∈ A ->

  Γ ⊢ (tApp a ℓ0 b) ; ℓ ∈ (B [ b.. ])

| T_Conv Γ ℓ ℓ0 a A B i :
  Γ ⊢ a ; ℓ ∈ A ->
  Γ ⊢ B ; ℓ0 ∈ (tUniv i) ->
  conv (c2e Γ) A B ->

  Γ ⊢ a ; ℓ ∈ B

| T_Zero Γ ℓ :
  ⊢ Γ ->

  Γ ⊢ tZero ; ℓ ∈ tNat

| T_Suc Γ ℓ a :
  Γ ⊢ a ; ℓ ∈ tNat ->

  Γ ⊢ tSuc a ; ℓ ∈ tNat

| T_Ind Γ ℓ ℓ0 a b c A ℓA i :
  ℓ0 ⊆ ℓ ->
  (ℓ0, tNat) :: Γ ⊢ A ; ℓA ∈ tUniv i ->
  Γ ⊢ a ; ℓ0 ∈ A [tZero..] ->
  (ℓ0, A) :: (ℓ0, tNat) :: Γ ⊢ b ; ℓ0 ∈ A[tSuc (var_tm 0) .: S >> var_tm]⟨S⟩ ->
  Γ ⊢ c ; ℓ0 ∈ tNat ->

  Γ ⊢ tInd ℓ0 a b c ; ℓ ∈ (A [c..])

| T_Nat Γ ℓ i :
  ⊢ Γ ->

  Γ ⊢ tNat ; ℓ ∈ tUniv i

| T_Univ Γ ℓ i :
  ⊢ Γ ->

  Γ ⊢ (tUniv i) ; ℓ ∈ (tUniv (S i))

| T_Void Γ ℓ i :
  ⊢ Γ ->

  Γ ⊢ tVoid ; ℓ ∈ tUniv i

| T_Absurd Γ ℓ ℓ0 ℓ1 i a A :
  Γ ⊢ a ; ℓ0 ∈ tVoid  ->
  Γ ⊢ A ; ℓ1 ∈ tUniv i ->

  Γ ⊢ tAbsurd a ; ℓ ∈ A

| T_Refl Γ ℓ a ℓ0 A:
  Γ ⊢ a ; ℓ0 ∈ A ->

  Γ ⊢ tRefl ; ℓ ∈ (tEq ℓ0 a a)

| T_Eq Γ ℓ ℓ0 a b A i:
  ℓ0 ⊆ ℓ ->
  Γ ⊢ a ; ℓ0 ∈ A ->
  Γ ⊢ b ; ℓ0 ∈ A ->

  Γ ⊢ (tEq ℓ0 a b) ; ℓ ∈ (tUniv i)

| T_J Γ t a b p A i j C ℓ ℓp ℓT ℓ0 ℓ1:
  ℓ1 ⊆ ℓ0 ->
  ℓp ⊆ ℓ ->
  Γ ⊢ a ; ℓ1 ∈ A ->
  Γ ⊢ b ; ℓ1 ∈ A ->
  Γ ⊢ A ; ℓT ∈ (tUniv j) ->

  Γ ⊢ p ; ℓp ∈ (tEq ℓ0 a b) ->


  ((ℓp, tEq ℓ0 (ren_tm shift a) (var_tm 0)) :: (ℓ1, A) :: Γ) ⊢ C ; ℓ0 ∈ (tUniv i) ->
  Γ ⊢ t ; ℓ ∈ (C [tRefl .: a ..]) ->
  Γ ⊢ (tJ ℓp t p) ; ℓ ∈ (C [p .: b..])

| T_Sig Γ i j ℓ ℓ0 A B :
  Γ ⊢ A ; ℓ ∈ (tUniv i) ->
  ((ℓ0, A) :: Γ) ⊢ B ; ℓ ∈ (tUniv j) ->

  Γ ⊢ (tSig ℓ0 A B) ; ℓ ∈ (tUniv (max i j))

| T_Pack Γ ℓ ℓ0 a A b B ℓT i :
  Γ ⊢ a ; ℓ0 ∈ A ->
  Γ ⊢ b ; ℓ ∈ B[a..] ->
  Γ ⊢ tSig ℓ0 A B ; ℓT ∈ tUniv i ->

  Γ ⊢ tPack ℓ0 a b ; ℓ ∈ tSig ℓ0 A B

| T_Let Γ ℓ ℓp ℓ0 a b ℓT A B C i j k :
  ℓp ⊆ ℓ ->
  Γ ⊢ A ; ℓT ∈ tUniv j ->
  (ℓ0, A) :: Γ ⊢ B ; ℓT ∈ tUniv k ->
  Γ ⊢ a ; ℓp ∈ tSig ℓ0 A B ->
  (ℓp, B) :: (ℓ0, A) :: Γ ⊢ b ; ℓ ∈ C[(tPack ℓ0 (var_tm 1) (var_tm 0)) .: (shift >> shift >> var_tm)] ->
  (ℓp, tSig ℓ0 A B) :: Γ ⊢ C ; ℓT ∈ tUniv i ->

  Γ ⊢ tLet ℓ0 ℓp a b ; ℓ ∈ C[a ..]

| T_TT Γ ℓ :
  ⊢ Γ ->

  Γ ⊢ tTT ; ℓ ∈ tUnit

| T_Unit Γ ℓ i :
  ⊢ Γ ->

  Γ ⊢ tUnit ; ℓ ∈ tUniv i

| T_Seq Γ ℓ ℓ0 ℓC a b C i :
  ℓ0 ⊆ ℓ ->
  Γ ⊢ a ; ℓ0 ∈ tUnit ->
  Γ ⊢ b ; ℓ ∈ C[tTT..] ->
  (ℓ0, tUnit) :: Γ ⊢ C ; ℓC ∈ tUniv i ->

  Γ ⊢ tSeq ℓ0 a b ; ℓ ∈ C[a..]

with Wff : context -> Prop :=
| Wff_nil :

  ⊢ nil
| Wff_cons Γ ℓ0 ℓ A i :
  ⊢ Γ ->
  Γ ⊢ A ; ℓ ∈ tUniv i ->

  ⊢ (ℓ0, A) :: Γ
where
  "Γ ⊢ a ; ℓ ∈ A" := (Wt Γ ℓ a A) and "⊢ Γ" := (Wff Γ).

Scheme wt_ind := Induction for Wt Sort Prop
    with wff_ind := Induction for Wff Sort Prop.

Combined Scheme wt_mutual from wt_ind, wff_ind.

End typing_sig.
