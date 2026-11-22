Require Import Coq.PArith.BinPos Coq.ZArith.BinInt Coq.NArith.BinNat Poulet4.P4cub.Syntax.AST Poulet4.Utils.P4Arith Poulet4.P4cub.Syntax.CubNotations Poulet4.P4cub.Semantics.Static.Util.

Reserved Notation "'`⟨' Δ , Γ ⟩ ⊢ e ∈ τ" (at level 80, no associativity).

Local Open Scope typ_scope.

Local Open Scope exp_scope.

Inductive type_exp (Δ : nat) (Γ : list Typ.t)
  : Exp.t -> Typ.t -> Prop :=
| type_bool (b : bool) :
  `⟨ Δ, Γ ⟩ ⊢ Exp.Bool b ∈ Typ.Bool
| type_bit w n :
  BitArith.bound w n ->
  `⟨ Δ, Γ ⟩ ⊢ w `W n ∈ Typ.Bit w
| type_int w n :
  IntArith.bound w n ->
  `⟨ Δ, Γ ⟩ ⊢ w `S n ∈ Typ.Int w
| type_varbit m w n :
  (w <= m)%N ->
  BitArith.bound w n ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.VarBit m w n ∈ Typ.VarBit m
| type_var τ og x :
  nth_error Γ x = Some τ ->
  typ_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Var τ og x ∈ τ
| type_slice hi lo e w τ :
  (Npos lo <= Npos hi < w)%N ->
  numeric_width w τ ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Slice hi lo e ∈ Typ.Bit (Npos hi - Npos lo + 1)%N
| type_cast τ τ' e :
  proper_cast τ' τ ->
  typ_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ τ' ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Cast τ e ∈ τ
| type_uop op τ τ' e :
  una_type op τ τ' ->
  typ_ok Δ τ' ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ τ ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Uop τ' op e ∈ τ'
| type_bop op τ₁ τ₂ τ e₁ e₂ :
  bin_type op τ₁ τ₂ τ ->
  typ_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e₁ ∈ τ₁ ->
  `⟨ Δ, Γ ⟩ ⊢ e₂ ∈ τ₂ ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Bop τ op e₁ e₂ ∈ τ
| type_index e₁ e₂ w τ :
  typ_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e₁ ∈ Typ.Array (Z.to_N (BitArith.upper_bound w)) τ ->
  `⟨ Δ, Γ ⟩ ⊢ e₂ ∈ Typ.Bit w ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Index τ e₁ e₂ ∈ τ
| type_member τ x e τs b :
  nth_error τs x = Some τ ->
  typ_ok Δ τ ->
  `⟨ Δ, Γ ⟩ ⊢ e ∈ Typ.Struct b τs ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Member τ x e ∈ τ
| type_lists ls es τ τs :
  typ_ok_lists Δ ls ->
  type_lst_ok ls τ τs ->
  Forall2 (type_exp Δ Γ) es τs ->
  `⟨ Δ, Γ ⟩ ⊢ Exp.Lists ls es ∈ τ
| type_error err :
  `⟨ Δ, Γ ⟩ ⊢ Exp.Error err ∈ Typ.Error
where "'`⟨' Δ , Γ ⟩ ⊢ e ∈ τ" := (type_exp Δ Γ e τ) : type_scope.
