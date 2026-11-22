From Coq Require Import PArith.BinPos ZArith.BinInt NArith.BinNat.

From Poulet4 Require Export P4cub.Semantics.Climate Utils.P4Arith P4cub.Syntax.Syntax.

Module Signal.

Variant t : Set :=
    | Cnt
    | Ext
    | Ret
    | Trns  .

Definition lub (sg1 sg2 : t) : option t :=
    match sg1, sg2 with
    | Cnt, _
    | _, Cnt => Some Cnt
    | Trns, (Ext | Trns)
    | Ext, Trns => Some Trns
    | Ret, (Ext | Ret)
    | Ext, Ret => Some Ret
    | Ext, Ext => Some Ext
    | Trns, Ret
  | Ret, Trns => None
    end.

End Signal.

Variant numeric_width : N -> Typ.t -> Prop :=
| numeric_width_bit : forall w, numeric_width w (Typ.Bit w)
| numeric_width_int : forall w, numeric_width (Npos w) (Typ.Int w).

Definition numeric (τ : Typ.t) : Prop := exists w, numeric_width w τ.

Variant una_type : Una.t -> Typ.t -> Typ.t -> Prop :=
  | una_Bool :
    una_type `!%una Typ.Bool Typ.Bool
  | una_BitNot τ :
    numeric τ -> una_type `~%una τ τ
  | una_UMinus τ :
    numeric τ -> una_type `-%una τ τ
  | una_IsValid ts :
    una_type Una.IsValid (Typ.Struct true ts) Typ.Bool
  | una_SetValidity b ts :
    una_type (Una.SetValidity b) (Typ.Struct true ts) (Typ.Struct true ts).

Variant bin_type : Bin.t -> Typ.t -> Typ.t -> Typ.t -> Prop :=
  | bin_Plus τ : numeric τ -> bin_type `+%bin τ τ τ
  | bin_PlusSat τ : numeric τ -> bin_type |+|%bin τ τ τ
  | bin_Minus τ : numeric τ -> bin_type `-%bin τ τ τ
  | bin_MinusSat τ : numeric τ -> bin_type |-|%bin τ τ τ
  | bin_Times τ : numeric τ -> bin_type ×%bin τ τ τ
  | bin_Shl τ1 w2 : numeric τ1 -> bin_type <<%bin τ1 (Typ.Bit w2) τ1
  | bin_Shr τ1 w2 : numeric τ1 -> bin_type >>%bin τ1 (Typ.Bit w2) τ1
  | bin_BitAnd τ : numeric τ -> bin_type &%bin τ τ τ
  | bin_BitXor τ : numeric τ -> bin_type ^%bin τ τ τ
  | bin_BitOr τ : numeric τ -> bin_type Bin.BitOr τ τ τ
  | bin_Le τ : numeric τ -> bin_type ≤%bin τ τ Typ.Bool
  | bin_Lt τ : numeric τ -> bin_type `<%bin τ τ Typ.Bool
  | bin_Ge τ : numeric τ -> bin_type ≥%bin τ τ Typ.Bool
  | bin_Gt τ : numeric τ -> bin_type `>%bin τ τ Typ.Bool
  | bin_And : bin_type `&&%bin Typ.Bool Typ.Bool Typ.Bool
  | bin_Or : bin_type `||%bin Typ.Bool Typ.Bool Typ.Bool
  | bin_Eq τ : bin_type `==%bin τ τ Typ.Bool
  | bin_NotEq τ : bin_type !=%bin τ τ Typ.Bool
  | bin_PlusPlusBit w1 w2 τ2 :
    numeric_width w2 τ2 ->
    bin_type `++%bin (Typ.Bit w1) τ2 (Typ.Bit (w1 + w2)%N)
  | bin_PlusPlusInt w1 w2 τ2 :
    numeric_width (Npos w2) τ2 ->
    bin_type `++%bin (Typ.Int w1) τ2 (Typ.Int (w1 + w2)%positive)
  | bin_PlusPlusIntZero w1 τ2 :
    numeric_width N0 τ2 ->
    bin_type `++%bin (Typ.Int w1) τ2 (Typ.Int w1).

Variant proper_cast : Typ.t -> Typ.t -> Prop :=
  | pc_bool_bit : proper_cast Typ.Bool (Typ.Bit 1)
  | pc_bit_bool : proper_cast (Typ.Bit 1) Typ.Bool
  | pc_bit_int w : proper_cast (Typ.Bit (Npos w)) (Typ.Int w)
  | pc_int_bit w : proper_cast (Typ.Int w) (Typ.Bit (Npos w))
  | pc_bit_bit w1 w2 : proper_cast (Typ.Bit w1) (Typ.Bit w2)
  | pc_int_int w1 w2 : proper_cast (Typ.Int w1) (Typ.Int w2)
  | pc_struct_hdr ts :
    proper_cast (Typ.Struct true ts) (Typ.Struct false ts).

Inductive typ_ok (Δ : nat) : Typ.t -> Prop :=
| bool_ok :
  typ_ok Δ Typ.Bool
| bityp_ok w :
  typ_ok Δ (Typ.Bit w)
| intyp_ok w :
  typ_ok Δ (Typ.Int w)
| varbityp_ok w :
  typ_ok Δ (Typ.VarBit w)
| error_ok :
  typ_ok Δ Typ.Error
| array_ok n t :
  typ_ok Δ t ->
  typ_ok Δ (Typ.Array n t)
| structyp_ok b ts :
  Forall (typ_ok Δ) ts ->
  typ_ok Δ (Typ.Struct b ts)
| var_ok T :
  (T < Δ)%nat ->
  typ_ok Δ (Typ.Var T).

Variant typ_ok_lists (Δ : nat) : Lst.t -> Prop :=
  | typ_ok_lists_array τ :
    typ_ok Δ τ -> typ_ok_lists Δ (Lst.Array τ)
  | typ_ok_lists_struct :
    typ_ok_lists Δ Lst.Struct
  | typ_ok_lists_header b :
    typ_ok_lists Δ (Lst.Header b).

Inductive lexpr_ok : Exp.t -> Prop :=
| lexpr_var τ og x :
  lexpr_ok (Exp.Var τ og x)
| lexpr_bit_slice e h l :
  lexpr_ok e ->
  lexpr_ok (Exp.Slice h l e)
| lexpr_index τ e₁ e₂ :
  lexpr_ok e₁ ->
  lexpr_ok (Exp.Index τ e₁ e₂)
| lexpr_member τ x e :
  lexpr_ok e ->
  lexpr_ok (Exp.Member τ x e).

Variant type_lst_ok
  : Lst.t -> Typ.t -> list Typ.t -> Prop :=
  | type_array_ok w τ :
    type_lst_ok
      (Lst.Array τ)
      (Typ.Array w τ)
      (List.repeat τ (N.to_nat w))
  | type_struct_ok τs :
    type_lst_ok
      Lst.Struct
      (Typ.Struct false τs) τs
  | type_header_ok b τs :
    type_lst_ok
      (Lst.Header b)
      (Typ.Struct true τs) τs.
