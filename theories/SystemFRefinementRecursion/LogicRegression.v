From Stdlib Require Import ZArith.BinInt Lists.List.
From AutoProof.SystemFRefinementRecursion Require Import Syntax RefinementLogic.

Module SystemFRefinementRecursionLogicRegression.
Import SystemFRefinementRecursion SystemFRefinementRecursionLogic.

Fixpoint previous_interpretation (p : qualifier) : Prop :=
  match p with
  | Pred_True => True
  | Pred_False => False
  | Pred_Eq t1 t2 =>
      exists v, predicate_multistep t1 v /\
                predicate_multistep t2 v /\ value v
  | Pred_Lt t1 t2 =>
      exists n1 n2 : Z,
        predicate_multistep t1 (tm_int n1) /\
        predicate_multistep t2 (tm_int n2) /\ (n1 < n2)%Z
  | Pred_Le t1 t2 =>
      exists n1 n2 : Z,
        predicate_multistep t1 (tm_int n1) /\
        predicate_multistep t2 (tm_int n2) /\ (n1 <= n2)%Z
  | Pred_And p1 p2 => previous_interpretation p1 /\ previous_interpretation p2
  | Pred_Or p1 p2 => previous_interpretation p1 \/ previous_interpretation p2
  | Pred_Not p1 => ~ previous_interpretation p1
  end.

Theorem interpretation_preserved : forall p,
  predicate_holds p <-> previous_interpretation p.
Proof.
  induction p; unfold predicate_holds in *; simpl in *; tauto.
Qed.

Example conjunction_distributes_over_disjunction : forall atoms p q r,
  interpret_qualifier atoms (Pred_And p (Pred_Or q r)) <->
  interpret_qualifier atoms (Pred_Or (Pred_And p q) (Pred_And p r)).
Proof. intros. simpl. tauto. Qed.

Example disjunction_distributes_over_conjunction : forall atoms p q r,
  interpret_qualifier atoms (Pred_Or p (Pred_And q r)) <->
  interpret_qualifier atoms (Pred_And (Pred_Or p q) (Pred_Or p r)).
Proof. intros. simpl. tauto. Qed.

Example negated_disjunction : forall atoms p q,
  interpret_qualifier atoms (Pred_Not (Pred_Or p q)) <->
  interpret_qualifier atoms (Pred_And (Pred_Not p) (Pred_Not q)).
Proof. intros. simpl. tauto. Qed.

Example nonzero_integer_formula :
  qualifier_holds (Pred_And
    (Pred_Lt (tm_int 0%Z) (tm_int 2%Z))
    (Pred_Not (Pred_Eq (tm_int 2%Z) (tm_int 0%Z)))).
Proof.
  split.
  - exists 0%Z, 2%Z. repeat split; try constructor; reflexivity.
  - intros [v [Htwo [Hzero Hv]]].
    inversion Htwo; subst.
    + inversion Hzero; subst; try discriminate.
      match goal with H : step (tm_int _) _ |- _ => inversion H end.
    + match goal with H : step (tm_int _) _ |- _ => inversion H end.
Qed.

End SystemFRefinementRecursionLogicRegression.
