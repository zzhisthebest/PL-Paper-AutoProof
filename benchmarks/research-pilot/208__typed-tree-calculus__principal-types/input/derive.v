Require Import String Arith Lia Bool List Nat Datatypes.

Require Import terms types subtypes.

Set Default Proof Using "Type".

Open Scope string_scope.

Open Scope nat_scope.

Inductive derive: list (string * dtype) -> Tree -> dtype -> Prop :=
| derive_ref : forall gamma x uty ty, get x gamma = Some uty -> subtype uty ty -> derive gamma (Ref x) ty
| derive_node : forall gamma uty, subtype Leaf uty -> derive gamma Node uty
| derive_app: forall gamma M N ty u, derive gamma M (Funty u ty) -> derive gamma N u -> derive gamma (M@N) ty
.
