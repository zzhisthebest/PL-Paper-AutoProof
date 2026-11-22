Definition reduction {X Y} (f : X -> Y) (P : X -> Prop) (Q : Y -> Prop) :=
  forall x, P x <-> Q (f x).
(* (reduces P Q) means that
   there exists a (total, computable, many-one) reduction f from P to Q *)
Definition reduces {X Y} (P : X -> Prop) (Q : Y -> Prop) :=
  exists f : X -> Y, reduction f P Q.
Notation "P ⪯ Q" := (reduces P Q) (at level 70).
