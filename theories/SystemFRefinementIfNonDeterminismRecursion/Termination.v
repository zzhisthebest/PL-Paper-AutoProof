From Stdlib Require Import Arith.Wf_nat ZArith.ZArith Lia.

Module SystemFRefinementIfNonDeterminismRecursionTermination.

Definition integer_decreases (next current : Z) : Prop :=
  (0 <= next /\ next < current)%Z.

Lemma integer_decreases_wf : well_founded integer_decreases.
Proof.
  apply (well_founded_lt_compat Z Z.to_nat integer_decreases).
  intros next current [Hnonneg Hlt].
  apply (proj1 (Z2Nat.inj_lt next current Hnonneg ltac:(lia))).
  exact Hlt.
Qed.

Definition measured_decreases {A : Type} (measure : A -> Z)
    (next current : A) : Prop :=
  integer_decreases (measure next) (measure current).

Lemma measured_decreases_wf : forall (A : Type) (measure : A -> Z),
  well_founded (measured_decreases measure).
Proof.
  intros A measure.
  apply (well_founded_lt_compat A (fun x => Z.to_nat (measure x))).
  intros next current [Hnonneg Hlt].
  apply (proj1 (Z2Nat.inj_lt (measure next) (measure current)
    Hnonneg ltac:(lia))).
  exact Hlt.
Qed.

Definition relational_decreases {A : Type} (measure : A -> Z -> Prop)
    (next current : A) : Prop :=
  exists next_rank current_rank,
    measure next next_rank /\ measure current current_rank /\
    integer_decreases next_rank current_rank.

Lemma relational_decreases_wf : forall (A : Type) (measure : A -> Z -> Prop),
  (forall x, exists n, measure x n) ->
  (forall x n m, measure x n -> measure x m -> n = m) ->
  well_founded (relational_decreases measure).
Proof.
  intros A measure Htotal Hunique.
  assert (Hacc : forall n x, measure x n -> Acc (relational_decreases measure) x).
  { intro n. induction n as [n IH] using
      (well_founded_induction integer_decreases_wf).
    intros x Hx. constructor. intros next [m [n' [Hm [Hn' Hlt]]]].
    assert (n' = n) by (eapply Hunique; eauto).
    subst n'. eapply IH; eauto. }
  intro x. destruct (Htotal x) as [n Hn]. eapply Hacc. exact Hn.
Qed.

Definition lexicographic {A B : Type}
    (lessA : A -> A -> Prop) (lessB : B -> B -> Prop)
    (next current : A * B) : Prop :=
  lessA (fst next) (fst current) \/
  (fst next = fst current /\ lessB (snd next) (snd current)).

Lemma lexicographic_wf : forall (A B : Type)
    (lessA : A -> A -> Prop) (lessB : B -> B -> Prop),
  well_founded lessA -> well_founded lessB ->
  well_founded (lexicographic lessA lessB).
Proof.
  intros A B lessA lessB HwfA HwfB [a b].
  revert b.
  induction a as [a IHa] using (well_founded_induction HwfA).
  intro b.
  induction b as [b IHb] using (well_founded_induction HwfB).
  constructor. intros [a' b'] Hlt.
  destruct Hlt as [Ha | [Ha Hb]]; simpl in *.
  - apply IHa. exact Ha.
  - subst a'. apply IHb. exact Hb.
Qed.

Definition lexicographic_integer_decreases : (Z * Z) -> (Z * Z) -> Prop :=
  lexicographic integer_decreases integer_decreases.

Lemma lexicographic_integer_decreases_wf :
  well_founded lexicographic_integer_decreases.
Proof.
  apply lexicographic_wf; apply integer_decreases_wf.
Qed.

Example halving_decreases : forall n : Z,
  (0 < n)%Z -> integer_decreases (n / 2) n.
Proof.
  intros n Hn. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Example increasing_argument_decreases_distance : forall limit i : Z,
  (i < limit)%Z ->
  measured_decreases (fun j => (limit - j)%Z) (i + 1)%Z i.
Proof. intros limit i Hi. unfold measured_decreases, integer_decreases. lia. Qed.

Example lexicographic_first_decreases :
  lexicographic_integer_decreases (2%Z, 100%Z) (3%Z, 0%Z).
Proof. left. unfold integer_decreases. simpl. lia. Qed.

Example lexicographic_second_decreases :
  lexicographic_integer_decreases (3%Z, 4%Z) (3%Z, 5%Z).
Proof. right. unfold integer_decreases. simpl. auto with zarith. Qed.

Example equal_metric_does_not_decrease : forall n : Z,
  ~ integer_decreases n n.
Proof. unfold integer_decreases. intros n H. lia. Qed.

Definition ambiguous_metric (_ : unit) (n : Z) : Prop :=
  n = 0%Z \/ n = 1%Z.

Example existential_comparison_can_decrease_to_itself :
  relational_decreases ambiguous_metric tt tt.
Proof.
  exists 0%Z, 1%Z. unfold ambiguous_metric, integer_decreases.
  repeat split; auto; lia.
Qed.

Example ambiguous_metric_is_not_functional :
  ~ (forall x n m, ambiguous_metric x n -> ambiguous_metric x m -> n = m).
Proof.
  intro H. assert (Hbad : 0%Z = 1%Z).
  { apply (H tt); unfold ambiguous_metric; auto. }
  discriminate Hbad.
Qed.

End SystemFRefinementIfNonDeterminismRecursionTermination.
