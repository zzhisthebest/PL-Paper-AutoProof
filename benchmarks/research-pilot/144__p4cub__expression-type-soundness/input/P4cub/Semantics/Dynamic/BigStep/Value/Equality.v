Require Import Poulet4.P4cub.Semantics.Dynamic.BigStep.Value.Syntax Poulet4.P4cub.Syntax.Equality Coq.ZArith.BinInt Coq.NArith.BinNat.

Fixpoint eqb_val (v1 v2 : Val.t) : bool :=
  let fix lstruct (vs1 vs2 : list Val.t) : bool :=
    match vs1, vs2 with
    | [], [] => true
    | v1::vs1, v2::vs2 => eqb_val v1 v2 && lstruct vs1 vs2
    | [], _::_ | _::_, [] => false
    end in
  match v1, v2 with
  | Val.Bool b1, Val.Bool b2 => eqb b1 b2
  | Val.Int w1 n1, Val.Int w2 n2 => (w1 =? w2)%positive && (n1 =? n2)%Z
  | Val.Bit w1 n1, Val.Bit w2 n2 => (w1 =? w2)%N && (n1 =? n2)%Z
  | Val.VarBit m1 w1 n1, Val.VarBit m2 w2 n2 => (m1 =? m2)%N && (w1 =? w2)%N && (n1 =? n2)%Z
  | Val.Error err1, Val.Error err2
    => if equiv_dec err1 err2 then true else false
  | Val.Lists ls1 vs1, Val.Lists ls2 vs2
    => lists_eqb ls1 ls2 && lstruct vs1 vs2
  | _,          _          => false
  end.
