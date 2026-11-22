From Coq Require Import Bool.Bool ZArith.BinInt.

Require Export Poulet4.P4cub.Syntax.AST.

Import String.

Module Val.

Inductive t : Set :=
  | Bool   (b : bool)
  | Bit    (width : N) (n : Z)
  | Int    (width : positive) (n : Z)
  | VarBit (max_width width : N) (n : Z)
  | Lists  (ls : Lst.t) (fields : list t)
  | Error  (err : string).

End Val.

Module Lval.

Inductive t : Set :=
  | Var (x : nat)
  | Slice (hi lo : positive) (arg : t)
  | Member (x : nat) (arg : t)
  | Index (index : N) (array : t)       .

End  Lval.

Definition Argv : Set := paramarg Val.t Lval.t.

Definition Argsv : Set := list (paramarg Val.t Lval.t).

Declare Scope val_scope.

Delimit Scope val_scope with val.

Notation "w 'VW' n" := (Val.Bit w n) (at level 0) : val_scope.

Notation "w 'VS' n" := (Val.Int w n) (at level 0) : val_scope.

Declare Scope lval_scope.

Delimit Scope lval_scope with lval.

Notation "lval 'DOT' x"
  := (Lval.Member x lval)
       (at level 22, left associativity) : lval_scope.
