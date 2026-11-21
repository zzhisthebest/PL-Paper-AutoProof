Require Import Nbe.Syntax.Def Nbe.Utils.Notations.

Set Implicit Arguments.

Inductive D : Set :=
| Dclo      : forall (t:Tm) (denv:DEnv), D
| DupX      : forall (dT:D) (dnf:DNe), D
| DupN      : forall (dne:DNe), D
| DS        : D -> D
| D0        : D
| Dnat      : D
| Dfun      : forall (DA:D) (DF:D), D
| Dunit     : D
| D1        : D
| Dempty    : D
| Dabsurd   : D -> D
| Duniv     : D
with DNe  : Set :=
| Dvar      : forall (n:nat), DNe
| Dapp      : forall (dne:DNe) (dnf:DNf), DNe
| DneAbsurd : forall (da:DNf) (dne:DNe), DNe
with DNf  : Set :=
| DdownX    : forall (dT:D) (da:D), DNf
| DdownN    : forall (da:D), DNf
with DEnv   : Set :=
| Did       : DEnv
| Dext      : forall (denv:DEnv) (dx:D), DEnv
.

Definition DisFun (d:D) :=
  match d with
  | Dfun _ _ => True
  | _        => False
  end
.

Definition DisUnit (d:D) :=
  match d with
  | Dunit => True
  | _     => False
  end
.
Definition Dup (dT : D) (d : DNe) : D :=
  match dT with
  | Dfun _ _ | Dunit => DupX dT d
  | _ => DupN d
  end.

Definition Ddown (dT d : D) : DNf :=
  match dT with
  | Dfun _ _ | Dunit => DdownX dT d
  | _ => DdownN d
  end.
