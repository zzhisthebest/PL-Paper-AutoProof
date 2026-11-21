Set Implicit Arguments.

Require Import LibExtra.

Require Export SyntaxClasses TransformCollect.

Require Export Vars Types Terms Items AbstractMachine.

Implicit Types (ds : defs) (hds : heap_defs).

Notation ctx := (env typ).
