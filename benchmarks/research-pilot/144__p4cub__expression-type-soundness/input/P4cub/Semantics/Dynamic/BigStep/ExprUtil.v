Require Import Poulet4.Utils.P4Arith Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Syntax Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Equality Coq.Bool.Bool Coq.ZArith.BinInt Coq.NArith.BinNat Coq.Arith.Compare_dec Coq.micromega.Lia Poulet4.P4cub.Syntax.Auxiliary Poulet4.P4cub.Semantics.Climate.

Require Poulet4.P4light.Semantics.Ops.

Require Import Poulet4.P4cub.Syntax.CubNotations.

Local Open Scope val_scope.

Definition eval_slice (hi lo : positive) (v : Val.t) : option Val.t :=
  match v with
  | _ VW z
  | _ VS z
    => let w' := (Npos hi - Npos lo + 1)%N in
      Some $ Val.Bit w' $
           BitArith.mod_bound w' $
           BitArith.bitstring_slice z hi lo
  | _ => None
  end.

Definition slice_val (hi lo : positive) (v : Val.t) : option Val.t :=
  match v with
  | w VW n =>
      let bits := to_lbool w n in
      let bits' := Ops.bitstring_slice bits (Pos.to_nat lo) (Pos.to_nat hi) in
      let (w',n') := BitArith.from_lbool bits' in
      Some $ w' VW n'
  | w VS z =>
      let bits := to_lbool (Npos w) z in
      let bits' := Ops.bitstring_slice bits (Pos.to_nat lo) (Pos.to_nat hi) in
      let (w',z') := BitArith.from_lbool bits' in
      Some $ w' VW z'
  | _ => None
  end.

Definition eval_una (op : Una.t) (v : Val.t) : option Val.t :=
  match op, v with
  | `!%una, Val.Bool b => Some $ Val.Bool  $ negb b
  | `~%una, w VW n => Some $ Val.Bit w $ BitArith.bit_not w n
  | `~%una, w VS n => Some $ Val.Int w $ IntArith.bit_not w n
  | `-%una, w VW z => Some $ Val.Bit w $ BitArith.neg w z
  | `-%una, w VS z => Some $ Val.Int w $ IntArith.neg w z
  | Una.IsValid, Val.Lists (Lst.Header b) _
    => Some (Val.Bool b)
  | Una.SetValidity b, Val.Lists _ vs
    => Some $ Val.Lists (Lst.Header b) vs
  | _, _ => None
  end.

Definition eval_bin (op : Bin.t) (v1 v2 : Val.t) : option Val.t :=
  match op, v1, v2 with
  | `+%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.plus_mod w n1 n2
  | `+%bin, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.plus_mod w z1 z2
  | |+|%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.plus_sat w n1 n2
  | |+|%bin,  w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.plus_sat w z1 z2
  | `-%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.minus_mod w n1 n2
  | `-%bin, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.minus_mod w z1 z2
  | |-|%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.minus_sat w n1 n2
  | |-|%bin, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.minus_sat w z1 z2
  | ×%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.mult_mod w n1 n2
  | ×%bin, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.mult_mod w z1 z2
  | <<%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.shift_left w n1 n2
  | <<%bin, w VS z1, _ VW z2
    => Some $ Val.Int w $ IntArith.shift_left w z1 z2
  | >>%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.shift_right w n1 n2
  | >>%bin, w VS z1, _ VW z2
    => Some $ Val.Int w $ IntArith.shift_right w z1 z2
  | &%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.bit_and w n1 n2
  | &%bin, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.bit_and w z1 z2
  | ^%bin, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.bit_xor w n1 n2
  | ^%bin, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.bit_xor w z1 z2
  | Bin.BitOr, w VW n1, _ VW n2
    => Some $ Val.Bit w $ BitArith.bit_or w n1 n2
  | Bin.BitOr, w VS z1, _ VS z2
    => Some $ Val.Int w $ IntArith.bit_or w z1 z2
  | ≤%bin, w VW n1, _ VW n2 => Some $ Val.Bool (n1 <=? n2)%Z
  | ≤%bin, w VS z1, _ VS z2 => Some $ Val.Bool (z1 <=? z2)%Z
  | `<%bin, w VW n1, _ VW n2 => Some $ Val.Bool (n1 <? n2)%Z
  | `<%bin, w VS z1, _ VS z2 => Some $ Val.Bool (z1 <? z2)%Z
  | ≥%bin, w VW n1, _ VW n2 => Some $ Val.Bool (n2 <=? n1)%Z
  | ≥%bin, w VS z1, _ VS z2 => Some $ Val.Bool (z2 <=? z1)%Z
  | `>%bin, w VW n1, _ VW n2 => Some $ Val.Bool (n2 <? n1)%Z
  | `>%bin, w VS z1, _ VS z2 => Some $ Val.Bool (z2 <? z1)%Z
  | `&&%bin, Val.Bool b1, Val.Bool b2 => Some $ Val.Bool (b1 && b2)
  | `||%bin, Val.Bool b1, Val.Bool b2 => Some $ Val.Bool (b1 || b2)
  | `==%bin, _, _ => Some $ Val.Bool $ eqb_val v1 v2
  | !=%bin, _, _ => Some $ Val.Bool $ negb $ eqb_val v1 v2
  | `++%bin, w1 VW n1, w2 VW n2
    => Some $ Val.Bit (w1 + w2)%N $ BitArith.concat w1 w2 n1 n2
  | `++%bin, w1 VW n1, w2 VS n2
    => Some $ Val.Bit (w1 + Npos w2)%N $ BitArith.concat w1 (Npos w2) n1 n2
  | `++%bin, w1 VS n1, w2 VS n2
    => Some $ Val.Int (w1 + w2)%positive $ IntArith.concat (Npos w1) (Npos w2) n1 n2
  | `++%bin, w1 VS n1, w2 VW n2
    => match w2 with
      | Npos w2 => Some $ Val.Int (w1 + w2)%positive $ IntArith.concat (Npos w1) (Npos w2) n1 n2
      | N0 => Some $ Val.Int w1 n1
      end
  | _, _, _ => None
  end.

Definition eval_cast
           (target : Typ.t) (v : Val.t) : option Val.t :=
  match target, v with
  | Typ.Bit 1%N, Val.Bool b
    => Some $ Val.Bit 1%N $ if b then 1%Z else 0%Z
  | Typ.Bool, Val.Bit 1%N n
    => Some $ Val.Bool
           match n with
           | Z0 => false
           | _  => true
           end
  | Typ.Bit w, _ VS z => Some $ w VW (BitArith.mod_bound w z)
  | Typ.Int w, _ VW n => Some $ w VS (IntArith.mod_bound w n)
  | Typ.Bit w, _ VW n => Some $ w VW (BitArith.mod_bound w n)
  | Typ.Int w, _ VS z => Some $ w VS (IntArith.mod_bound w z)
  | Typ.Struct false _, Val.Lists (Lst.Header _) vs
    => Some $ Val.Lists Lst.Struct vs
  | _, _ => None
  end.
