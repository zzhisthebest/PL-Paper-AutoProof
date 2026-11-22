From Coq Require Import ZArith.BinInt NArith.BinNat.

From Poulet4 Require Import P4cub.Syntax.Syntax P4cub.Semantics.Static.Util P4cub.Semantics.Dynamic.BigStep.Value.Syntax.

Reserved Notation "'⊢ᵥ' V ∈ τ"
         (at level 80, no associativity).

Reserved Notation "Γ '⊢l' LV ∈ τ"
         (at level 80, no associativity).

Local Open Scope val_scope.

Inductive type_val : Val.t -> Typ.t -> Prop :=
| typ_bool (b : bool) :  ⊢ᵥ Val.Bool b ∈ Typ.Bool
| typ_bit w n :
  BitArith.bound w n ->
  ⊢ᵥ w VW n ∈ Typ.Bit w
| typ_int w z :
  IntArith.bound w z ->
  ⊢ᵥ w VS z ∈ Typ.Int w
| typ_varbit m w n :
  N.le w m ->
  BitArith.bound w n ->
  ⊢ᵥ Val.VarBit m w n ∈ Typ.VarBit m
| typ_lists ls vs τ τs :
  type_lst_ok ls τ τs ->
  Forall2 type_val vs τs ->
  ⊢ᵥ Val.Lists ls vs ∈ τ
| typ_error err :
  ⊢ᵥ Val.Error err ∈ Typ.Error
where "'⊢ᵥ' V ∈ τ" := (type_val V τ) : type_scope.
