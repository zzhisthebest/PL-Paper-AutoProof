Require Import Arith Lia Bool List Nat Datatypes String.

Set Default Proof Using "Type".

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

Definition Sop := S1 (K @ Node) @ Node.

Definition I := S1 K @ K.

Definition KI := K@I.

Inductive program : Tree -> Prop :=
| pr_leaf : program △
| pr_stem : forall M, program M -> program (△ @ M)
| pr_fork : forall M N, program M -> program N -> program (△ @ M@ N)
.

Inductive t_red1 : Tree -> Tree -> Prop :=
| k_red : forall y z, t_red1 (△ @ △ @ y @ z) y
| s_red: forall (x y z : Tree), t_red1 (△ @ (△ @ x) @ y @ z) (x @ z @ (y @ z))
| leaf_red: forall (w x y : Tree), t_red1 (△ @ (△ @ w @ x) @ y @ Node) w
| stem_red: forall (w x y z : Tree), t_red1 (△ @ (△ @ w @ x) @ y @ (Node @ z)) (x @ z)
| fork_red: forall (w x y z1 z2 : Tree), t_red1 (△ @ (△ @ w @ x) @ y @ (Node @ z1 @ z2)) (y @ z1 @ z2)
| appl_red : forall M M' N, t_red1 M M' -> t_red1 (M@N) (M'@N)
| appr_red : forall M N N', t_red1 N N' -> t_red1 (M@N) (M@N')
.

Inductive multi_step : (Tree -> Tree -> Prop) -> Tree -> Tree -> Prop :=
  | zero_red : forall red M, multi_step red M M
  | succ_red : forall (red: Tree-> Tree -> Prop) M N P,
                   red M N -> multi_step red N P -> multi_step red M P
.

Definition t_red := multi_step t_red1.

Definition transitive red := forall (M N P: Tree), red M N -> red N P -> red M P.

Definition preserves_appl (red : Tree -> Tree -> Prop) :=
forall M N M', red M M' -> red (M@N) (M'@ N).

Definition preserves_appr (red : Tree -> Tree -> Prop) :=
forall M N N', red N N' -> red (M@N) (M@N').

Definition preserves_app (red : Tree -> Tree -> Prop) :=
forall M M', red M M' -> forall N N', red N N' -> red (M@N) (M'@N').

Fixpoint substitute M x N :=
  match M with
  | Ref y => if eqb x y then N else Ref y
  | △ => △
  | M1 @ M2 => (substitute M1 x N) @ (substitute M2 x N)
end.

Fixpoint bracket x M :=
match M with
| Ref y =>  if eqb x y then I else (K@ (Ref y))
| △ => K@ △
| App M1 M2 => S1 (bracket x M1) @ (bracket x M2)
end
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

Inductive combination : Tree -> Prop :=
| is_Node : combination △
| is_App : forall M N, combination M -> combination N -> combination (M@ N)
.

Inductive active: Tree -> Prop :=
| active_ref: forall x, active (Ref x)
| active_app: forall M N, active M -> active (M@N)
.

Inductive normal : Tree -> Prop :=
| nf_ref: forall x, normal (Ref x)
| nf_active: forall M N, active M -> normal M -> normal N -> normal (M@N)
| nf_leaf : normal △
| nf_stem : forall M, normal M -> normal (△ @ M)
| nf_fork : forall M N, normal M -> normal N -> normal (△ @ M@ N)
.

Definition self_apply := Eval cbv in \"x" (Ref "x" @ (Ref "x")).

Definition wait M N := S1 (S1 (K@ M) @ (K@ N)) @ I.

Definition omega := \"w" (\"f" (Ref "f" @ (Ref "w" @ Ref "w" @ Ref "f"))).

Definition Yop := omega @ omega.

Definition wait2 M N x :=  S1 (S1 (S1 (K @ M) @ (K @ N)) @ (K @ x)) @ I.

Definition omega2 := \"w" (\"f" (Ref "f" @ (wait2 (Ref "w") (Ref "w") (Ref "f")))).

Definition omega21 := K @ (△ @ (△ @ I)).

Definition omega22 :=  \ "w" (\ "f" (wait2 (Ref "w") (Ref "w") (Ref "f"))).
