From Stdlib Require Import PeanoNat Lia.

From OLlibs Require Import List_more.

Export ListNotations.

Set Default Proof Using "Type".

Set Implicit Arguments.

Unset Printing Use Implicit Types.

Inductive lform :=
| lvar (_ : comparison) (_ : nat) | lmap (_ _ : lform)
| ltop | lwith (_ _ : lform)
| lzero | lplus (_ _ : lform)
| lone
| lfrl (_ : nat) (_ : lform) | lexs (_ : nat) (_ : lform).

Notation 𝖳 := ltop.

Infix "∧" := lwith (at level 35).

Notation "b / a" := (lmap a b) (left associativity, at level 40, a at next level).

Notation "0" := lzero.

Infix "∨" := lplus (at level 35).

Notation "1" := lone.

Notation cst := (lvar Lt).

Notation dvar := (lvar Eq).

Notation var := (lvar Gt).

Notation "∀" := lfrl.

Notation "∃" := lexs.

Fixpoint fsize a := S
match a with
| lvar _ _ | ltop | lzero | lone => 0
| lmap c d | lwith c d | lplus c d => fsize c + fsize d
| lfrl _ c | lexs _ c => fsize c
end.

Fixpoint subs X F A :=
match A with
| dvar k => dvar k
| var Y => if Nat.eq_dec Y X then F else var Y
| cst R => cst R
| lmap B C => lmap (subs X F B) (subs X F C)
| ltop => ltop
| lwith B C => lwith (subs X F B) (subs X F C)
| lzero => lzero
| lplus B C => lplus (subs X F B) (subs X F C)
| lone => lone
| lfrl Y B => lfrl Y (if Nat.eq_dec Y X then B else subs X F B)
| lexs Y B => lexs Y (if Nat.eq_dec Y X then B else subs X F B)
end.

Fixpoint nsubs n F A :=
match A with
| var X => var X
| dvar k => match n ?= k with
            | Eq => F
            | Lt => dvar (pred k)
            | Gt => dvar k
            end
| cst R => cst R
| lmap B C => lmap (nsubs n F B) (nsubs n F C)
| ltop => ltop
| lwith B C => lwith (nsubs n F B) (nsubs n F C)
| lzero => lzero
| lplus B C => lplus (nsubs n F B) (nsubs n F C)
| lone => lone
| lfrl X B => lfrl X (nsubs n F B)
| lexs X B => lexs X (nsubs n F B)
end.

Fixpoint freevars A :=
match A with
| var X => X :: nil
| dvar _ => nil
| cst _ => nil
| ltop | lzero | lone => nil
| lmap B C | lwith B C | lplus B C => (freevars B) ++ (freevars C)
| lfrl X B | lexs X B => remove Nat.eq_dec X (freevars B)
end.

Notation closed A := (freevars A = nil).

Fixpoint fup k A :=
match A with
| var X => var X
| dvar n => if n <? k then dvar n else dvar (S n)
| cst R => cst R
| lmap B C => lmap (fup k B) (fup k C)
| ltop => ltop
| lwith B C => lwith (fup k B) (fup k C)
| lzero => lzero
| lplus B C => lplus (fup k B) (fup k C)
| lone => lone
| lfrl X B => lfrl X (fup k B)
| lexs X B => lexs X (fup k B)
end.

Notation fupz := (fup 0).
