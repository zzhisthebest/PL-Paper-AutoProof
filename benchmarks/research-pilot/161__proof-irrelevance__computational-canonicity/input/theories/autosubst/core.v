Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

Require Import List.

Notation "'list_map'" := map.

Definition option_map {A B} (f : A -> B) (p : option A) :
  option B :=
match p with
  | Some a => Some (f a)
  | None => None
end.

Declare Scope fscope.

Declare Scope subst_scope.

Require Import Setoid Morphisms.
