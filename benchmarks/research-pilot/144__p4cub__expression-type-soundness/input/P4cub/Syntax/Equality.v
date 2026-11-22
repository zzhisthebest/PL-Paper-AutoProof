From Coq Require Import PArith.BinPos ZArith.BinInt NArith.BinNat Bool.Bool.

From Poulet4 Require Import P4cub.Syntax.AST P4cub.Syntax.CubNotations.

Import String.

Reserved Infix "=?" (at level 70).

Fixpoint eqb_typ (τ1 τ2 : Typ.t) {struct τ1} : bool :=
  let fix eqbl (ts1 ts2 : list Typ.t) {struct ts1} : bool :=
    match ts1, ts2 with
    | [], []           => true
    | t1::ts1', t2::ts2' => ((t1 =? t2)%typ && eqbl ts1' ts2')%bool
    | _, _             => false
    end in
  match τ1, τ2 with
  | Typ.Bool, Typ.Bool
  | Typ.Error, Typ.Error                 => true
  | Typ.Var X1, Typ.Var X2               => Nat.eqb X1 X2
  | Typ.Bit w1, Typ.Bit w2               => (w1 =? w2)%N
  | Typ.VarBit w1, Typ.VarBit w2         => (w1 =? w2)%N
  | Typ.Int w1, Typ.Int w2               => (w1 =? w2)%positive
  | Typ.Array n1 t1, Typ.Array n2 t2     => (n1 =? n2)%N && (t1 =? t2)%typ
  | Typ.Struct b1 ts1, Typ.Struct b2 ts2 => (Bool.eqb b1 b2) && eqbl ts1 ts2
  | _, _ => false
  end
where "x '=?' y" := (eqb_typ x y) : typ_scope.

Definition lists_eqb (l1 l2 : Lst.t) : bool :=
  match l1, l2 with
  | Lst.Struct, Lst.Struct => true
  | Lst.Array τ₁, Lst.Array τ₂ => (τ₁ =? τ₂)%typ
  | Lst.Header b₁, Lst.Header b₂ => Bool.eqb b₁ b₂
  | _, _ => false
  end.
