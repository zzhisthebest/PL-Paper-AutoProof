Require Import Arith Lia Bool List Nat Datatypes String.

Open Scope string_scope.

Declare Scope tree_scope.
Global Open Scope tree_scope.

Inductive Tree:  Set :=
  | Ref : string -> Tree
  | Node : Tree
  | App : Tree -> Tree -> Tree
.

Notation "△" := Node : tree_scope.

Notation "x @ y" := (App x y) (at level 65, left associativity) : tree_scope.

Definition K := △ @ △.

Definition S1 x := △ @ (△@x).

Definition I := S1 K @ K.

Inductive t_red1 : Tree -> Tree -> Prop :=
| k_red : forall y z, t_red1 (△ @ △ @ y @ z) y
| s_red: forall (x y z : Tree), t_red1 (△ @ (△ @ x) @ y @ z) (x @ z @ (y @ z))
| leaf_red: forall (w x y : Tree), t_red1 (△ @ (△ @ w @ x) @ y @ Node) w
| stem_red: forall (w x y z : Tree), t_red1 (△ @ (△ @ w @ x) @ y @ (Node @ z)) (x @ z)
| fork_red: forall (w x y z1 z2 : Tree), t_red1 (△ @ (△ @ w @ x) @ y @ (Node @ z1 @ z2)) (y @ z1 @ z2)
| appl_red : forall M M' N, t_red1 M M' -> t_red1 (M@N) (M'@N)
| appr_red : forall M N N', t_red1 N N' -> t_red1 (M@N) (M@N')
.

Fixpoint occurs x M :=
  match M with
  | Ref y => eqb x y
  | △ => false
  | M1@ M2 => (occurs x M1) || (occurs x M2)
  end.

Fixpoint star x M :=
  match M with
  | Ref y =>  if eqb x y then I else (K@ (Ref y))
  | △ => K@ △
  | App M1 M2 => if occurs x (M1 @ M2)
                 then S1 (star x M1) @ (star x M2)
                 else K@ (M1 @ M2)
  end.

Notation "\" := star : tree_scope.

Definition wait2 M N x :=  S1 (S1 (S1 (K @ M) @ (K @ N)) @ (K @ x)) @ I.

Definition omega21 := K @ (△ @ (△ @ I)).

Definition omega22 :=  \ "w" (\ "f" (wait2 (Ref "w") (Ref "w") (Ref "f"))).
