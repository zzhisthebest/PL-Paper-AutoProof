Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Language.

Inductive algo_cost : typ -> typ -> Prop :=
  | cint : algo_cost int int
  | candl : forall A B C, algo_cost A C -> algo_cost (and A B) C
  | candr : forall A B C, algo_cost B C -> algo_cost (and A B) C
  | crandl : forall A B C, algo_cost A B -> algo_cost A (and B C)
  | crandr : forall A B C, algo_cost A C -> algo_cost A (and B C)
  | carr : forall A B C D, algo_cost B D -> algo_cost (arr A B) (arr C D)
  | crcd : forall A B l, algo_cost A B -> algo_cost (rcd l A) (rcd l B).

Definition algo_dis A B := ~ (algo_cost A B).

Local Lemma sub_refl : forall A, sub A A.
Proof.
  induction A; eauto using sub.
Qed.

Local Lemma algo_cost_sound : forall A B, algo_cost A B -> cost_spec A B.
Proof.
  intros A B H.
  induction H; try destruct IHalgo_cost as [T [HT [HA HB]]].
  - exists int. eauto using gord, sub.
  - exists T. eauto using sub.
  - exists T. eauto using sub.
  - exists T. eauto using sub.
  - exists T. eauto using sub.
  - exists (arr (and A C) T).
    split; [now apply GO_arrow |].
    split; apply sarr; eauto using sandl, sandr, sub_refl.
  - exists (rcd l T). repeat split; now constructor.
Qed.

Local Lemma gord_common_supertype : forall A T,
  sub A T -> forall B, gord T -> sub B T -> algo_cost A B.
Proof.
  intros A T HA.
  induction HA; intros X HG HB.
  - remember int as T eqn:HT in HB.
    induction HB; inversion HT; subst; eauto using algo_cost.
  - inversion HG.
  - inversion HG.
  - apply candl. eauto.
  - apply candr. eauto.
  - inversion HG; subst.
    remember (rcd x B) as T eqn:HT in HB.
    induction HB; inversion HT; subst; eauto using algo_cost.
  - inversion HG; subst.
    remember (arr C D) as T eqn:HT in HB.
    induction HB; inversion HT; subst; eauto using algo_cost.
Qed.

Theorem algo_dis_eqv: forall A B,
  disjoint A B <-> algo_dis A B.
Proof.
  intros A B. unfold disjoint, algo_dis.
  split.
  - intros Hdis Hcost. apply Hdis. now apply algo_cost_sound.
  - intros Hdis [T [HT [HA HB]]].
    apply Hdis. exact (gord_common_supertype A T HA B HT HB).
Qed.
