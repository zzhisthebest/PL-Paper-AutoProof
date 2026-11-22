Require Import Coq.ZArith.ZArith Coq.micromega.Lia Coq.Bool.Bool.

Require Import VST.zlist.Zlist.

Require Import Coq.Lists.List.

Require Import Poulet4.P4light.Syntax.SyntaxUtil.

Import ListNotations.

Open Scope Z_scope.

Module BitArith.

Import Z.

Section Operations.

Variable (width : N).

Definition upper_bound : Z := 2 ^ (Z.of_N width).

Definition maxZ : Z := upper_bound - 1.

Definition bound (n : Z) : Prop := -1 < n < upper_bound.

Definition boundb (n : Z) : bool :=
      (-1 <? n) && (n <? upper_bound).

Definition mod_bound (n : Z) : Z := n mod upper_bound.

Definition sat_bound (n : Z) : Z :=
      if (n >? maxZ)
      then maxZ
      else if (n <? 0) then 0 else n.

Definition neg (n : Z) : Z := mod_bound (Z.opp n).

Definition plus_sat (a b : Z) : Z := sat_bound (a + b).

Definition plus_mod (a b : Z) : Z := mod_bound (a + b).

Definition minus_sat (a b : Z) : Z := sat_bound (a - b).

Definition minus_mod (a b : Z) : Z := mod_bound (a - b).

Definition mult_mod (a b : Z) : Z := mod_bound (a * b).

Definition div_mod (a b : Z) : Z := mod_bound (a / b).

Definition modulo_mod (a b : Z) : Z := mod_bound (a mod b).

Definition shift_right (a b : Z) : Z := mod_bound (Z.shiftr a b).

Definition shift_left (a b : Z) : Z := mod_bound (Z.shiftl a b).

Definition bit_not (a : Z) := mod_bound (maxZ - a).

Definition bit_and (a b : Z) := mod_bound (Z.land a b).

Definition bit_or (a b : Z) := mod_bound (Z.lor a b).

Definition bit_xor (a b : Z) := mod_bound (Z.lxor a b).

End Operations.

Definition bitstring_slice (i : Z) (lo hi : positive) : Z :=
    let mask := (Z.pow 2 (Zpos (hi - lo + 1)) - 1)%Z in
    Z.land (Z.shiftr i (Zpos lo)) mask.

Definition concat (w1 w2 : N) (z1 z2 : Z) : Z :=
    mod_bound (w1 + w2) (Z.shiftl z1 (Z.of_N w2) + (mod_bound w2 z2)).

Fixpoint le_lbool_to_val (bits: list bool) (order: Z) (res : Z) : Z :=
    match bits with
    | [] => res
    | false :: tl => le_lbool_to_val tl (Z.shiftl order 1) res
    | true :: tl => le_lbool_to_val tl (Z.shiftl order 1) (res + order)
    end.

Definition lbool_to_val (bits: list bool) (order: Z) (res : Z) :=
    le_lbool_to_val (rev bits) order res.

Definition le_from_lbool (bits: list bool) : (N * Z) :=
    (Z.to_N (Zlength bits), le_lbool_to_val bits 1 0).

Definition from_lbool (bits: list bool) : (N * Z) :=
    (Z.to_N (Zlength bits), lbool_to_val bits 1 0).

End BitArith.

Module IntArith.

Import Z.

Section Operations.

Variable (width : positive).

Definition mod_amt : Z := 2 ^ (Zpos width).

Definition upper_bound : Z := 2 ^ (Zpos width - 1).

Definition maxZ : Z := upper_bound - 1.

Definition minZ : Z := - upper_bound.

Definition bound (z : Z) : Prop := (minZ <= z <= maxZ)%Z.

Definition mod_bound (n : Z) : Z :=
      let m := n mod mod_amt in
      if (m <? upper_bound) then m else m - mod_amt.

Definition sat_bound (z : Z) :=
      if (z >? maxZ)%Z then maxZ
      else if (z <? minZ)%Z then minZ else z.

Definition neg (z : Z) : Z := mod_bound (Z.opp z).

Definition plus_sat (a b : Z) : Z := sat_bound (a + b).

Definition minus_sat (a b : Z) : Z := sat_bound (a - b).

Definition plus_mod (a b : Z) : Z := mod_bound (a + b).

Definition minus_mod (a b : Z) : Z := mod_bound (a - b).

Definition mult_mod (a b : Z) : Z := mod_bound (a * b).

Definition shift_left (a b : Z) : Z := mod_bound (Z.shiftl a b).

Definition shift_right (a b : Z) : Z := mod_bound (Z.shiftr a b).

Definition bit_not (a : Z) := mod_bound ( - (a + 1)).

Definition bit_and (a b : Z) : Z := mod_bound (Z.land a b).

Definition bit_or (a b : Z) : Z := mod_bound (Z.lor a b).

Definition bit_xor (a b : Z) : Z := mod_bound (Z.lxor a b).

End Operations.

Definition concat (w1 w2 : N) (z1 z2 : Z) : Z :=
    mod_bound (pos_of_N (w1 + w2)) (Z.shiftl z1 (Z.of_N w2) + (BitArith.mod_bound w2 z2)).

Fixpoint le_lbool_to_val (bits: list bool) (order: Z) (res: Z): Z :=
    match bits with
    | []
    | [false] => res
    | [true] => res - order
    | false :: tl => le_lbool_to_val tl (Z.shiftl order 1) res
    | true :: tl => le_lbool_to_val tl (Z.shiftl order 1) (res + order)
    end.

Definition lbool_to_val (bits: list bool) (order: Z) (res: Z): Z :=
    le_lbool_to_val (rev bits) order res.

Definition le_from_lbool (bits: list bool) : (N * Z) :=
    (Z.to_N (Zlength bits), le_lbool_to_val bits 1 0).

Definition from_lbool (bits: list bool) : (N * Z) :=
    (Z.to_N (Zlength bits), lbool_to_val bits 1 0).

End IntArith.

Fixpoint le_to_lbool' (width: nat) (value: Z) (res: list bool) :=
  match width with
  | S n => le_to_lbool' n (value / 2) ((Z.odd value) :: res)
  | O => res
  end.

Definition le_to_lbool (width: N) (value: Z) : list bool :=
  List.rev (le_to_lbool' (N.to_nat width) value []).

Definition to_lbool (width: N) (value: Z) : list bool :=
  le_to_lbool' (N.to_nat width) value [].

Definition to_loptbool (width: N) (value: Z) : list (option bool) :=
  map Some (to_lbool width value).

Definition le_to_loptbool (width: N) (value: Z) : list (option bool) :=
  map Some (le_to_lbool width value).

Fixpoint to_lbool'' (width : nat) (value : Z) : list bool :=
  match width with
  | 0%nat => []
  | S n => Z.odd value :: to_lbool'' n (value / 2)
  end.

Module P4ArithTactics.

End P4ArithTactics.
