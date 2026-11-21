From Declarative Require Import Language.

Definition EProgressive (e : eexpr) :=
  evalue e \/ exists e', ereduce e e'.

Theorem generalized_erased_progress : forall e1 e2 A,
  usub nil e1 e2 A ->
  forall e1' e2', extract e1 = e1' -> extract e2 = e2' ->
    EProgressive e1' /\ EProgressive e2'.

Theorem preservation : forall e1 e2 A,
  usub nil e1 e2 A ->
  forall e1'' e2'', ereduce (extract e1) e1'' -> ereduce (extract e2) e2'' ->
    exists e1' e2', extract e1' = e1''
                 /\ extract e2' = e2''
                 /\ reduce e1 e1'
                 /\ reduce e2 e2'
                 /\ usub nil e1' e2' A.
