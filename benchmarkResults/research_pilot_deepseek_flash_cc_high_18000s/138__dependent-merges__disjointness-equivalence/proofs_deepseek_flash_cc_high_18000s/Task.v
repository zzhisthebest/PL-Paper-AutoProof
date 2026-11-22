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

Lemma sub_refl : forall A, sub A A.
Proof. induction A; eauto using sub. Qed.

Inductive sub_gord : typ -> typ -> Prop :=
  | sg_int : sub_gord int int
  | sg_andl : forall A1 A2 C, sub_gord A1 C -> sub_gord (and A1 A2) C
  | sg_andr : forall A1 A2 C, sub_gord A2 C -> sub_gord (and A1 A2) C
  | sg_arr : forall A1 A2 C1 C2, sub C1 A1 -> sub_gord A2 C2 -> sub_gord (arr A1 A2) (arr C1 C2)
  | sg_rcd : forall x A C, sub_gord A C -> sub_gord (rcd x A) (rcd x C).

Lemma sub_gord_of_sub : forall A C, sub A C -> gord C -> sub_gord A C.
Proof.
  intros A C H. induction H; intros HC.
  - apply sg_int.
  - inversion HC.
  - inversion HC.
  - apply sg_andl. apply IHsub. exact HC.
  - apply sg_andr. apply IHsub. exact HC.
  - inversion HC; subst. apply sg_rcd. apply IHsub. assumption.
  - inversion HC; subst. apply sg_arr with (C1:=C) (A1:=A). exact H. apply IHsub2. assumption.
Qed.

Lemma sg_int_algo : forall B T, sub_gord B T -> T = int -> algo_cost int B.
Proof.
  intros B T HB. induction HB; intros ET; subst.
  - apply cint.
  - apply crandl. apply IHHB. reflexivity.
  - apply crandr. apply IHHB. reflexivity.
  - discriminate ET.
  - discriminate ET.
Qed.

Lemma sg_arr_algo : forall A1 A2 C1 C2,
  (forall B T, sub_gord B T -> T = C2 -> algo_cost A2 B) ->
  forall B T, sub_gord B T -> T = arr C1 C2 -> algo_cost (arr A1 A2) B.
Proof.
  intros A1 A2 C1 C2 IH B T HB. induction HB; intros ET; subst.
  - discriminate ET.
  - apply crandl. apply IHHB. reflexivity.
  - apply crandr. apply IHHB. reflexivity.
  - injection ET as H1 H2. subst.
    apply carr. apply IH with (T:=C2). exact HB. reflexivity.
  - discriminate ET.
Qed.

Lemma sg_rcd_algo : forall x A' C',
  (forall B T, sub_gord B T -> T = C' -> algo_cost A' B) ->
  forall B T, sub_gord B T -> T = rcd x C' -> algo_cost (rcd x A') B.
Proof.
  intros x A' C' IH B T HB. induction HB; intros ET; subst.
  - discriminate ET.
  - apply crandl. apply IHHB. reflexivity.
  - apply crandr. apply IHHB. reflexivity.
  - discriminate ET.
  - injection ET as H1 H2. subst.
    apply crcd. apply IH with (T:=C'). exact HB. reflexivity.
Qed.

Lemma sub_gord_eq_rect : forall B T T', T = T' -> sub_gord B T -> sub_gord B T'.
Proof. intros B T T' E H; subst; exact H. Qed.

Lemma sub_gord_algo : forall A C, sub_gord A C -> forall B, sub_gord B C -> algo_cost A B.
Proof.
  intros A C HA. induction HA; intros B HB.
  - apply (sg_int_algo B int HB eq_refl).
  - apply candl. apply IHHA. exact HB.
  - apply candr. apply IHHA. exact HB.
  - apply (sg_arr_algo A1 A2 C1 C2
             (fun B' T h E => IHHA B' (sub_gord_eq_rect B' T C2 E h))
             B (arr C1 C2) HB eq_refl).
  - apply (sg_rcd_algo x A C
             (fun B' T h E => IHHA B' (sub_gord_eq_rect B' T C E h))
             B (rcd x C) HB eq_refl).
Qed.

Lemma algo_cost_spec : forall A B, algo_cost A B -> cost_spec A B.
Proof.
  intros A B H. induction H.
  - exists int. split. apply GO_int. split; apply sint.
  - destruct IHalgo_cost as [D [Hg [H1 H2]]].
    exists D. split. exact Hg. split. apply sandl. exact H1. exact H2.
  - destruct IHalgo_cost as [D [Hg [H1 H2]]].
    exists D. split. exact Hg. split. apply sandr. exact H1. exact H2.
  - destruct IHalgo_cost as [D [Hg [H1 H2]]].
    exists D. split. exact Hg. split. exact H1. apply sandl. exact H2.
  - destruct IHalgo_cost as [D [Hg [H1 H2]]].
    exists D. split. exact Hg. split. exact H1. apply sandr. exact H2.
  - destruct IHalgo_cost as [E [Hg [H1 H2]]].
    exists (arr (and A C) E). split. apply GO_arrow. exact Hg.
    split.
    + apply sarr with (A:=A) (B:=B) (C:=and A C) (D:=E).
      apply sandl. apply sub_refl. exact H1.
    + apply sarr with (A:=C) (B:=D) (C:=and A C) (D:=E).
      apply sandr. apply sub_refl. exact H2.
  - destruct IHalgo_cost as [D [Hg [H1 H2]]].
    exists (rcd l D). split. apply GO_rcd. exact Hg. split; apply srcd; assumption.
Qed.

Lemma spec_algo : forall A B, cost_spec A B -> algo_cost A B.
Proof.
  intros A B [C [Hg [HA HB]]].
  apply (sub_gord_algo A C).
  - apply sub_gord_of_sub; assumption.
  - apply sub_gord_of_sub; assumption.
Qed.

Theorem algo_dis_eqv: forall A B,
  disjoint A B <-> algo_dis A B.
Proof.
  intros A B. unfold disjoint, algo_dis.
  split; intros H.
  - intro Hc. apply H. apply algo_cost_spec. exact Hc.
  - intros [C [Hg [HA HB]]]. apply H. apply spec_algo. exists C. auto.
Qed.
