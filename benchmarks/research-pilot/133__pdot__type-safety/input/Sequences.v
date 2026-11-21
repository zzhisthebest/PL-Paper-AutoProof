Set Implicit Arguments.

Section SEQUENCES.

Variable A: Type.

Variable R: A -> A -> Prop.

Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Inductive plus: A -> A -> Prop :=
  | plus_left: forall a b c,
      R a b -> star b c -> plus a c.

Definition all_seq_inf (a: A) : Prop :=
  forall b, star a b -> exists c, R b c.

Definition infseq_with_function (a: A) : Prop :=
  exists f: nat -> A, f 0 = a /\ forall i, R (f i) (f (1 + i)).

CoInductive infseq: A -> Prop :=
  | infseq_step: forall a b,
      R a b -> infseq b -> infseq a.

Definition irred (a: A) : Prop := forall b, ~(R a b).

End SEQUENCES.
