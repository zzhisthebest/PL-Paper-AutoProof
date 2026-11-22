Require Import Qual.geq.
Require Import Qual.defeq.

From Stdlib Require Import Lia.

Set Implicit Arguments.
Open Scope grade_scope.

(* ============================================================ *)
(* Infrastructure for the proof of DefEq_Consistent.            *)
(* ============================================================ *)

(* ---------- size ---------- *)
Fixpoint size_tm (u:tm) : nat :=
  match u with
  | a_TyUnit => 1 | a_TmUnit => 1 | a_Type _ => 1 | a_Var_f _ => 1 | a_Var_b _ => 1
  | a_Pi _ A B => 1 + size_tm A + size_tm B
  | a_Abs _ A b => 1 + size_tm A + size_tm b
  | a_App a _ b => 1 + size_tm a + size_tm b
  | a_Sum A B => 1 + size_tm A + size_tm B
  | a_Inj1 a => 1 + size_tm a | a_Inj2 a => 1 + size_tm a
  | a_Case _ a b1 b2 => 1 + size_tm a + size_tm b1 + size_tm b2
  | a_WSigma _ A B => 1 + size_tm A + size_tm B
  | a_WPair a _ b => 1 + size_tm a + size_tm b
  | a_LetPair _ a b => 1 + size_tm a + size_tm b
  | a_SSigma _ A B => 1 + size_tm A + size_tm B
  | a_SPair a _ b => 1 + size_tm a + size_tm b
  | a_Proj1 _ a => 1 + size_tm a | a_Proj2 _ a => 1 + size_tm a
  end.

Lemma size_tm_pos : forall u, (1 <= size_tm u)%nat.
Proof. destruct u; simpl; lia. Qed.

(* ---------- level-indexed local closedness ---------- *)
Fixpoint lc_at (k:nat) (u:tm) : Prop :=
  match u with
  | a_TyUnit => True
  | a_TmUnit => True
  | a_Type _ => True
  | a_Var_f _ => True
  | a_Var_b n => Nat.lt n k
  | a_Pi _ A B => lc_at k A /\ lc_at (S k) B
  | a_Abs _ A b => lc_at k A /\ lc_at (S k) b
  | a_App a _ b => lc_at k a /\ lc_at k b
  | a_Sum A B => lc_at k A /\ lc_at k B
  | a_Inj1 a => lc_at k a
  | a_Inj2 a => lc_at k a
  | a_Case _ a b1 b2 => lc_at k a /\ lc_at k b1 /\ lc_at k b2
  | a_WSigma _ A B => lc_at k A /\ lc_at (S k) B
  | a_WPair a _ b => lc_at k a /\ lc_at k b
  | a_LetPair _ a b => lc_at k a /\ lc_at (S k) b
  | a_SSigma _ A B => lc_at k A /\ lc_at (S k) B
  | a_SPair a _ b => lc_at k a /\ lc_at k b
  | a_Proj1 _ a => lc_at k a
  | a_Proj2 _ a => lc_at k a
  end.

Lemma lc_at_mono : forall u k j, (k <= j)%nat -> lc_at k u -> lc_at j u.
Proof.
  induction u; simpl; intros k j Hle H; auto; try tauto.
  - destruct H as [HA HB]. split; [exact (IHu1 k j Hle HA)|apply (IHu2 (S k) (S j)); [lia|exact HB]].
  - destruct H as [HA HB]. split; [exact (IHu1 k j Hle HA)|apply (IHu2 (S k) (S j)); [lia|exact HB]].
  - destruct H as [Ha Hb]. split; [exact (IHu1 k j Hle Ha)|exact (IHu2 k j Hle Hb)].
  - lia.
  - destruct H as [HA HB]. split; [exact (IHu1 k j Hle HA)|exact (IHu2 k j Hle HB)].
  - apply (IHu k j Hle); auto.
  - apply (IHu k j Hle); auto.
  - destruct H as [Ha [Hb1 Hb2]]. repeat split;
      [exact (IHu1 k j Hle Ha)|exact (IHu2 k j Hle Hb1)|exact (IHu3 k j Hle Hb2)].
  - destruct H as [HA HB]. split; [exact (IHu1 k j Hle HA)|apply (IHu2 (S k) (S j)); [lia|exact HB]].
  - destruct H as [Ha Hb]. split; [exact (IHu1 k j Hle Ha)|exact (IHu2 k j Hle Hb)].
  - destruct H as [Ha Hb]. split; [exact (IHu1 k j Hle Ha)|apply (IHu2 (S k) (S j)); [lia|exact Hb]].
  - destruct H as [HA HB]. split; [exact (IHu1 k j Hle HA)|apply (IHu2 (S k) (S j)); [lia|exact HB]].
  - destruct H as [Ha Hb]. split; [exact (IHu1 k j Hle Ha)|exact (IHu2 k j Hle Hb)].
  - apply (IHu k j Hle); auto.
  - apply (IHu k j Hle); auto.
Qed.
Arguments lc_at_mono : clear implicits.
Arguments lc_at_mono u k j _ _.

Lemma lc_at_open_rec : forall B t k, lc_at 0 t ->
  (lc_at k (open_tm_wrt_tm_rec k t B) <-> lc_at (S k) B).
Proof.
  induction B; intros t k Ht; simpl.
  - tauto. - tauto.
  - (* Pi *) split; intros [HA HB]; split.
    + exact (proj1 (IHB1 t k Ht) HA). + exact (proj1 (IHB2 t (S k) Ht) HB).
    + exact (proj2 (IHB1 t k Ht) HA). + exact (proj2 (IHB2 t (S k) Ht) HB).
  - (* Abs *) split; intros [HA HB]; split.
    + exact (proj1 (IHB1 t k Ht) HA). + exact (proj1 (IHB2 t (S k) Ht) HB).
    + exact (proj2 (IHB1 t k Ht) HA). + exact (proj2 (IHB2 t (S k) Ht) HB).
  - (* App *) split; intros [HA HB]; split.
    + exact (proj1 (IHB1 t k Ht) HA). + exact (proj1 (IHB2 t k Ht) HB).
    + exact (proj2 (IHB1 t k Ht) HA). + exact (proj2 (IHB2 t k Ht) HB).
  - tauto.
  - (* Var_b *) destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt]; simpl.
    + split; intros H; lia.
    + subst n. split; intros H.
      * lia.
      * exact (lc_at_mono t 0 k (Nat.le_0_l k) Ht).
    + split; intros H.
      * assert (Hn : (n - 1 < k)%nat) by lia. lia.
      * assert (Hn : (n < S k)%nat) by lia. destruct k; [lia|]. simpl. lia.
  - tauto.
  - (* Sum *) split; intros [HA HB]; split.
    + exact (proj1 (IHB1 t k Ht) HA). + exact (proj1 (IHB2 t k Ht) HB).
    + exact (proj2 (IHB1 t k Ht) HA). + exact (proj2 (IHB2 t k Ht) HB).
  - (* Inj1 *) split; intros H; [exact (proj1 (IHB t k Ht) H)|exact (proj2 (IHB t k Ht) H)].
  - (* Inj2 *) split; intros H; [exact (proj1 (IHB t k Ht) H)|exact (proj2 (IHB t k Ht) H)].
  - (* Case *) split; intros [HA [HB1 HB2]]; repeat split.
    + exact (proj1 (IHB1 t k Ht) HA). + exact (proj1 (IHB2 t k Ht) HB1). + exact (proj1 (IHB3 t k Ht) HB2).
    + exact (proj2 (IHB1 t k Ht) HA). + exact (proj2 (IHB2 t k Ht) HB1). + exact (proj2 (IHB3 t k Ht) HB2).
  - (* WSigma *) split; intros [HA HB]; split.
    + exact (proj1 (IHB1 t k Ht) HA). + exact (proj1 (IHB2 t (S k) Ht) HB).
    + exact (proj2 (IHB1 t k Ht) HA). + exact (proj2 (IHB2 t (S k) Ht) HB).
  - (* WPair *) split; intros [HA HB]; split.
    + exact (proj1 (IHB1 t k Ht) HA). + exact (proj1 (IHB2 t k Ht) HB).
    + exact (proj2 (IHB1 t k Ht) HA). + exact (proj2 (IHB2 t k Ht) HB).
  - (* LetPair *) split; intros [HA HB]; split.
    + exact (proj1 (IHB1 t k Ht) HA). + exact (proj1 (IHB2 t (S k) Ht) HB).
    + exact (proj2 (IHB1 t k Ht) HA). + exact (proj2 (IHB2 t (S k) Ht) HB).
  - (* SSigma *) split; intros [HA HB]; split.
    + exact (proj1 (IHB1 t k Ht) HA). + exact (proj1 (IHB2 t (S k) Ht) HB).
    + exact (proj2 (IHB1 t k Ht) HA). + exact (proj2 (IHB2 t (S k) Ht) HB).
  - (* SPair *) split; intros [HA HB]; split.
    + exact (proj1 (IHB1 t k Ht) HA). + exact (proj1 (IHB2 t k Ht) HB).
    + exact (proj2 (IHB1 t k Ht) HA). + exact (proj2 (IHB2 t k Ht) HB).
  - (* Proj1 *) split; intros H; [exact (proj1 (IHB t k Ht) H)|exact (proj2 (IHB t k Ht) H)].
  - (* Proj2 *) split; intros H; [exact (proj1 (IHB t k Ht) H)|exact (proj2 (IHB t k Ht) H)].
Qed.
Arguments lc_at_open_rec B t k _.

Lemma lc_at_S_body : forall B, (forall x, lc_at 0 (open_tm_wrt_tm B (a_Var_f x))) -> lc_at 1 B.
Proof.
  intros B H. destruct (atom_fresh (empty : atoms)) as [x _].
  apply (proj1 (lc_at_open_rec B (a_Var_f x) 0 I)). apply H.
Qed.

Lemma lc_tm_lc_at_0 : forall u, lc_tm u -> lc_at 0 u.
Proof.
  induction 1; simpl; auto.
  all: try (split; [auto | apply lc_at_S_body; auto]).
Qed.

Lemma size_open_var : forall B k xx, size_tm (open_tm_wrt_tm_rec k (a_Var_f xx) B) = size_tm B.
Proof.
  induction B; simpl; intros k xx; auto;
  try (rewrite IHB1; auto); try (rewrite IHB2; auto);
  try (rewrite IHB1, IHB2; auto);
  try (rewrite IHB1, IHB2, IHB3; auto);
  try (destruct (lt_eq_lt_dec n k) as [[?|?]|?]; auto).
Qed.

Lemma lc_at_0_lc_tm_aux : forall n u, (size_tm u <= n)%nat -> lc_at 0 u -> lc_tm u.
Proof.
  induction n as [|n IHn].
  - intros u Hn H. exfalso. destruct u; simpl in *; lia.
  - intros u Hn H.
    destruct u as [| |psi A B|psi A bd|fa g fb|s|nb|x|A1 A2|ia|ia|g a b1 b2|psi A B|wa g wb|g wa wb|psi A B|sa g sb|g pa|g pa];
      simpl in H; try (exfalso; lia).
    + apply lc_a_TyUnit.
    + apply lc_a_TmUnit.
    + destruct H as [HA HB]. apply lc_a_Pi.
      * apply IHn; [simpl in *; lia| exact HA].
      * intro x. apply IHn.
        -- unfold open_tm_wrt_tm; rewrite size_open_var; simpl in *; lia.
        -- apply (proj2 (lc_at_open_rec B (a_Var_f x) 0 I) HB).
    + destruct H as [HA Hb]. apply lc_a_Abs.
      * apply IHn; [simpl in *; lia| exact HA].
      * intro x. apply IHn.
        -- unfold open_tm_wrt_tm; rewrite size_open_var; simpl in *; lia.
        -- apply (proj2 (lc_at_open_rec bd (a_Var_f x) 0 I) Hb).
    + destruct H as [Ha Hb]. apply lc_a_App.
      * apply IHn; [simpl in *; lia| exact Ha].
      * apply IHn; [simpl in *; lia| exact Hb].
    + apply lc_a_Type.
    + apply lc_a_Var_f.
    + destruct H as [HA HB]. apply lc_a_Sum.
      * apply IHn; [simpl in *; lia| exact HA]. * apply IHn; [simpl in *; lia| exact HB].
    + apply lc_a_Inj1. apply IHn; [simpl in *; lia|exact H].
    + apply lc_a_Inj2. apply IHn; [simpl in *; lia|exact H].
    + destruct H as [Ha [Hb1 Hb2]]. apply lc_a_Case.
      * apply IHn; [simpl in *; lia|exact Ha]. * apply IHn; [simpl in *; lia|exact Hb1].
      * apply IHn; [simpl in *; lia|exact Hb2].
    + destruct H as [HA HB]. apply lc_a_WSigma.
      * apply IHn; [simpl in *; lia|exact HA].
      * intro x. apply IHn.
        -- unfold open_tm_wrt_tm; rewrite size_open_var; simpl in *; lia.
        -- apply (proj2 (lc_at_open_rec B (a_Var_f x) 0 I) HB).
    + destruct H as [Ha Hb]. apply lc_a_WPair.
      * apply IHn; [simpl in *; lia|exact Ha]. * apply IHn; [simpl in *; lia|exact Hb].
    + destruct H as [Ha Hb]. apply lc_a_LetPair.
      * apply IHn; [simpl in *; lia|exact Ha].
      * intro x. apply IHn.
        -- unfold open_tm_wrt_tm; rewrite size_open_var; simpl in *; lia.
        -- apply (proj2 (lc_at_open_rec wb (a_Var_f x) 0 I) Hb).
    + destruct H as [HA HB]. apply lc_a_SSigma.
      * apply IHn; [simpl in *; lia|exact HA].
      * intro x. apply IHn.
        -- unfold open_tm_wrt_tm; rewrite size_open_var; simpl in *; lia.
        -- apply (proj2 (lc_at_open_rec B (a_Var_f x) 0 I) HB).
    + destruct H as [Ha Hb]. apply lc_a_SPair.
      * apply IHn; [simpl in *; lia|exact Ha]. * apply IHn; [simpl in *; lia|exact Hb].
    + apply lc_a_Proj1. apply IHn; [simpl in *; lia|exact H].
    + apply lc_a_Proj2. apply IHn; [simpl in *; lia|exact H].
Qed.

Lemma lc_at_0_lc_tm : forall u, lc_at 0 u -> lc_tm u.
Proof. intros u H. apply lc_at_0_lc_tm_aux with (n := size_tm u); [lia|exact H]. Qed.

Lemma lc_body_all : forall B x, lc_tm (open_tm_wrt_tm B (a_Var_f x)) -> forall z, lc_tm (open_tm_wrt_tm B (a_Var_f z)).
Proof.
  intros B x Hx z.
  apply lc_at_0_lc_tm.
  apply (proj2 (lc_at_open_rec B (a_Var_f z) 0 I)).
  apply (proj1 (lc_at_open_rec B (a_Var_f x) 0 I)).
  apply lc_tm_lc_at_0. exact Hx.
Qed.
Arguments lc_body_all B x _ z.

Lemma lc_open_term : forall B x a, lc_tm (open_tm_wrt_tm B (a_Var_f x)) -> lc_tm a -> lc_tm (open_tm_wrt_tm B a).
Proof.
  intros B x a HB Ha.
  apply lc_at_0_lc_tm.
  apply (proj2 (lc_at_open_rec B a 0 (lc_tm_lc_at_0 Ha))).
  apply (proj1 (lc_at_open_rec B (a_Var_f x) 0 I)).
  apply lc_tm_lc_at_0. exact HB.
Qed.
Arguments lc_open_term B x a _ _.

Lemma lc_Pi : forall psi A B, lc_tm (a_Pi psi A B) -> lc_tm A /\ (forall x, lc_tm (open_tm_wrt_tm B (a_Var_f x))).
Proof. intros. inversion H. auto. Qed.
Lemma lc_WSigma : forall psi A B, lc_tm (a_WSigma psi A B) -> lc_tm A /\ (forall x, lc_tm (open_tm_wrt_tm B (a_Var_f x))).
Proof. intros. inversion H. auto. Qed.
Lemma lc_SSigma : forall psi A B, lc_tm (a_SSigma psi A B) -> lc_tm A /\ (forall x, lc_tm (open_tm_wrt_tm B (a_Var_f x))).
Proof. intros. inversion H. auto. Qed.
Lemma lc_Sum : forall A B, lc_tm (a_Sum A B) -> lc_tm A /\ lc_tm B.
Proof. intros. inversion H. auto. Qed.
Arguments lc_Pi : clear implicits. Arguments lc_Pi psi A B _.
Arguments lc_WSigma : clear implicits. Arguments lc_WSigma psi A B _.
Arguments lc_SSigma : clear implicits. Arguments lc_SSigma psi A B _.
Arguments lc_Sum : clear implicits. Arguments lc_Sum A B _.

(* ---------- Grade / CGrade : lc and uniq ---------- *)
Scheme Grade_mind := Induction for Grade Sort Prop
  with CGrade_mind := Induction for CGrade Sort Prop.

Lemma Grade_lc : forall (P:econtext) (psi:grade) (a:tm), Grade P psi a -> lc_tm a.
Proof.
  intros P psi a H. induction H using Grade_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a:tm) (_:CGrade P psi phi0 a) => lc_tm a).
  - apply lc_a_Type.
  - apply lc_a_Var_f.
  - apply lc_a_Pi. * exact IHGrade. * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all B x). apply (H0 x Hx).
  - apply lc_a_Abs. * exact IHGrade. * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all b x). apply (H x Hx).
  - apply lc_a_App; assumption.
  - apply lc_a_WSigma. * exact IHGrade. * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all B x). apply (H0 x Hx).
  - apply lc_a_WPair; assumption.
  - apply lc_a_LetPair. * exact IHGrade. * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all c x). apply (H0 x Hx).
  - apply lc_a_SSigma. * exact IHGrade. * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all B x). apply (H0 x Hx).
  - apply lc_a_SPair; assumption.
  - apply lc_a_Proj1. exact IHGrade.
  - apply lc_a_Proj2. exact IHGrade.
  - apply lc_a_Sum; assumption.
  - apply lc_a_Inj1. exact IHGrade.
  - apply lc_a_Inj2. exact IHGrade.
  - apply lc_a_Case; assumption.
  - apply lc_a_TyUnit.
  - apply lc_a_TmUnit.
  - exact IHGrade.
  - assumption.
Qed.
Arguments Grade_lc : clear implicits.
Arguments Grade_lc P psi a _.

Lemma CGrade_lc : forall (P:econtext) (psi phi0:grade) (a:tm), CGrade P psi phi0 a -> lc_tm a.
Proof.
  intros P psi phi0 a H. induction H.
  - exact (Grade_lc P phi a H0).
  - assumption.
Qed.
Arguments CGrade_lc : clear implicits.
Arguments CGrade_lc P psi phi0 a _.

Lemma Grade_uniq : forall (P:econtext) (psi:grade) (a:tm), Grade P psi a -> uniq P.
Proof.
  intros P psi a H. induction H using Grade_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a:tm) (_:CGrade P psi phi0 a) => uniq P).
  all: assumption.
Qed.
Arguments Grade_uniq : clear implicits.
Arguments Grade_uniq P psi a _.

(* ---------- DefEq / CDefEq : lc ---------- *)
Scheme DefEq_mind := Induction for DefEq Sort Prop
  with CDefEq_mind := Induction for CDefEq Sort Prop.

Lemma DefEq_lc : forall (P:econtext) (psi:grade) (a b:tm), DefEq P psi a b -> lc_tm a /\ lc_tm b.
Proof.
  intros P psi a b H. induction H using DefEq_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a b:tm) (_:CDefEq P psi phi0 a b) => lc_tm a /\ lc_tm b).
  - split; apply (Grade_lc P psi); assumption.
  - destruct IHDefEq1 as [Ha Hb]; destruct IHDefEq2 as [Hb' Hc]; split; assumption.
  - destruct IHDefEq as [Ha Hb]; split; assumption.
  - split; apply (Grade_lc P psi); assumption.
  - (* Pi *) split; [apply lc_a_Pi | apply lc_a_Pi].
    * exact (proj1 IHDefEq). * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all B1 x). exact (proj1 (H0 x Hx)).
    * exact (proj2 IHDefEq). * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all B2 x). exact (proj2 (H0 x Hx)).
  - (* Abs *) split; [apply lc_a_Abs | apply lc_a_Abs].
    * exact (proj1 IHDefEq). * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all b1 x). exact (proj1 (H x Hx)).
    * exact (proj2 IHDefEq). * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all b2 x). exact (proj2 (H x Hx)).
  - (* App *) split; [apply lc_a_App | apply lc_a_App].
    * exact (proj1 IHDefEq). * exact (proj1 IHDefEq0).
    * exact (proj2 IHDefEq). * exact (proj2 IHDefEq0).
  - (* PiFst *) destruct IHDefEq as [Hp1 Hp2]; destruct (lc_Pi _ _ _ Hp1) as [HA1 _];
      destruct (lc_Pi _ _ _ Hp2) as [HA2 _]; split; assumption.
  - (* PiSnd *) destruct IHDefEq1 as [Hp1 Hp2]; destruct IHDefEq2 as [Ha1 Ha2].
    destruct (lc_Pi _ _ _ Hp1) as [_ HB1]; destruct (lc_Pi _ _ _ Hp2) as [_ HB2]. split.
    * destruct (atom_fresh (empty:atoms)) as [x _]. exact (@lc_open_term B1 x a1 (HB1 x) Ha1).
    * destruct (atom_fresh (empty:atoms)) as [x _]. exact (@lc_open_term B2 x a2 (HB2 x) Ha2).
  - (* WSigma *) split; [apply lc_a_WSigma | apply lc_a_WSigma].
    * exact (proj1 IHDefEq). * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all B1 x). exact (proj1 (H0 x Hx)).
    * exact (proj2 IHDefEq). * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all B2 x). exact (proj2 (H0 x Hx)).
  - (* WSigmaFst *) destruct IHDefEq as [Hp1 Hp2]; destruct (lc_WSigma _ _ _ Hp1) as [HA1 _];
      destruct (lc_WSigma _ _ _ Hp2) as [HA2 _]; split; assumption.
  - (* WSigmaSnd *) destruct IHDefEq as [Hp1 Hp2];
      destruct (lc_WSigma _ _ _ Hp1) as [_ HB1]; destruct (lc_WSigma _ _ _ Hp2) as [_ HB2].
      pose proof (Grade_lc P psi a g) as Ha. split.
    * destruct (atom_fresh (empty:atoms)) as [x _]. exact (@lc_open_term B1 x a (HB1 x) Ha).
    * destruct (atom_fresh (empty:atoms)) as [x _]. exact (@lc_open_term B2 x a (HB2 x) Ha).
  - (* WPair *) split; [apply lc_a_WPair | apply lc_a_WPair].
    * exact (proj1 IHDefEq). * exact (proj1 IHDefEq0).
    * exact (proj2 IHDefEq). * exact (proj2 IHDefEq0).
  - (* LetPair *) split; [apply lc_a_LetPair | apply lc_a_LetPair].
    * exact (proj1 IHDefEq). * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all b1 x). exact (proj1 (H0 x Hx)).
    * exact (proj2 IHDefEq). * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all b2 x). exact (proj2 (H0 x Hx)).
  - (* SSigma *) split; [apply lc_a_SSigma | apply lc_a_SSigma].
    * exact (proj1 IHDefEq). * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all B1 x). exact (proj1 (H0 x Hx)).
    * exact (proj2 IHDefEq). * destruct (atom_fresh L) as [x Hx]. apply (lc_body_all B2 x). exact (proj2 (H0 x Hx)).
  - (* SSigmaFst *) destruct IHDefEq as [Hp1 Hp2]; destruct (lc_SSigma _ _ _ Hp1) as [HA1 _];
      destruct (lc_SSigma _ _ _ Hp2) as [HA2 _]; split; assumption.
  - (* SSigmaSnd *) destruct IHDefEq1 as [Hp1 Hp2]; destruct IHDefEq2 as [Ha1 Ha2];
      destruct (lc_SSigma _ _ _ Hp1) as [_ HB1]; destruct (lc_SSigma _ _ _ Hp2) as [_ HB2]. split.
    * destruct (atom_fresh (empty:atoms)) as [x _]. exact (@lc_open_term B1 x a1 (HB1 x) Ha1).
    * destruct (atom_fresh (empty:atoms)) as [x _]. exact (@lc_open_term B2 x a2 (HB2 x) Ha2).
  - (* SPair *) split; [apply lc_a_SPair | apply lc_a_SPair].
    * exact (proj1 IHDefEq). * exact (proj1 IHDefEq0).
    * exact (proj2 IHDefEq). * exact (proj2 IHDefEq0).
  - (* Proj1 *) split; [apply lc_a_Proj1 | apply lc_a_Proj1].
    * exact (proj1 IHDefEq). * exact (proj2 IHDefEq).
  - (* Proj2 *) split; [apply lc_a_Proj2 | apply lc_a_Proj2].
    * exact (proj1 IHDefEq). * exact (proj2 IHDefEq).
  - (* Sum *) split; [apply lc_a_Sum | apply lc_a_Sum].
    * exact (proj1 IHDefEq1). * exact (proj1 IHDefEq2).
    * exact (proj2 IHDefEq1). * exact (proj2 IHDefEq2).
  - (* SumFst *) destruct IHDefEq as [Hp1 Hp2]; destruct (lc_Sum _ _ Hp1) as [HA1 _];
      destruct (lc_Sum _ _ Hp2) as [HA2 _]; split; assumption.
  - (* SumSnd *) destruct IHDefEq as [Hp1 Hp2]; destruct (lc_Sum _ _ Hp1) as [_ HB1];
      destruct (lc_Sum _ _ Hp2) as [_ HB2]; split; assumption.
  - (* Inj1 *) split; [apply lc_a_Inj1 | apply lc_a_Inj1].
    * exact (proj1 IHDefEq). * exact (proj2 IHDefEq).
  - (* Inj2 *) split; [apply lc_a_Inj2 | apply lc_a_Inj2].
    * exact (proj1 IHDefEq). * exact (proj2 IHDefEq).
  - (* Case *) split; [apply lc_a_Case | apply lc_a_Case].
    * exact (proj1 IHDefEq1). * exact (proj1 IHDefEq2). * exact (proj1 IHDefEq3).
    * exact (proj2 IHDefEq1). * exact (proj2 IHDefEq2). * exact (proj2 IHDefEq3).
  - (* TyUnit *) split; apply lc_a_TyUnit.
  - (* TmUnit *) split; apply lc_a_TmUnit.
  - (* SubstIrrel *) split.
    * destruct (atom_fresh L) as [x Hx]. exact (@lc_open_term b1 x a1 (proj1 (H x Hx)) l).
    * destruct (atom_fresh L) as [x Hx]. exact (@lc_open_term b2 x a2 (proj2 (H x Hx)) l0).
  - (* CDefEq_Leq *) exact IHDefEq.
  - (* CDefEq_Nleq *) split; assumption.
Qed.
Arguments DefEq_lc : clear implicits.
Arguments DefEq_lc P psi a b _.

Lemma CDefEq_lc : forall (P:econtext) (psi phi0:grade) (a b:tm), CDefEq P psi phi0 a b -> lc_tm a /\ lc_tm b.
Proof.
  intros P psi phi0 a b H. induction H.
  - destruct (DefEq_lc P phi a b H0) as [Ha Hb]; split; assumption.
  - split; assumption.
Qed.
Arguments CDefEq_lc : clear implicits.
Arguments CDefEq_lc P psi phi0 a b _.

(* ---------- reduction facts ---------- *)
(* reduction lemmas *)
Definition redex (a:tm) : bool :=
  match a with
  | a_App _ _ _ => true | a_Case _ _ _ _ => true
  | a_Proj1 _ _ => true | a_Proj2 _ _ => true | a_LetPair _ _ _ => true
  | _ => false
  end.

Lemma step_redex : forall a b, Step a b -> redex a = true.
Proof. intros a b H; destruct H; reflexivity. Qed.

Ltac no_step :=
  exfalso;
  match goal with
  | Hb : Step ?x ?y |- _ => pose proof (step_redex Hb) as Hs; cbv in Hs; discriminate Hs
  end.

Lemma step_det : forall a b c, Step a b -> Step a c -> b = c.
Proof.
  intros a b c H1. revert c. induction H1; intros c H2;
    inversion H2; subst; try reflexivity; try (f_equal; eauto); try no_step.
Qed.

(* ---------- value-type tags and opening head stability ---------- *)
(* Same-head (value-type tag) relation, and stability of the head of [open]. *)
Inductive VtTag : tm -> tm -> Prop :=
 | VtTag_Type : forall s, VtTag (a_Type s) (a_Type s)
 | VtTag_Unit : VtTag a_TyUnit a_TyUnit
 | VtTag_Pi : forall psi A B A' B', VtTag (a_Pi psi A B) (a_Pi psi A' B')
 | VtTag_WSigma : forall psi A B A' B', VtTag (a_WSigma psi A B) (a_WSigma psi A' B')
 | VtTag_SSigma : forall psi A B A' B', VtTag (a_SSigma psi A B) (a_SSigma psi A' B')
 | VtTag_Sum : forall A B A' B', VtTag (a_Sum A B) (a_Sum A' B').

Lemma VtTag_VT : forall a b, VtTag a b -> lc_tm a -> lc_tm b -> ValueType a /\ ValueType b.
Proof.
  intros a b H; induction H; intros Ha Hb; split.
  - apply ValueType_Type. - apply ValueType_Type.
  - apply ValueType_Unit. - apply ValueType_Unit.
  - apply ValueType_Pi. * inversion Ha; assumption. * assumption.
  - apply ValueType_Pi. * inversion Hb; assumption. * assumption.
  - apply ValueType_WSigma. * inversion Ha; assumption. * assumption.
  - apply ValueType_WSigma. * inversion Hb; assumption. * assumption.
  - apply ValueType_SSigma. * inversion Ha; assumption. * assumption.
  - apply ValueType_SSigma. * inversion Hb; assumption. * assumption.
  - apply ValueType_Sum. * inversion Ha; assumption. * inversion Ha; assumption.
  - apply ValueType_Sum. * inversion Hb; assumption. * inversion Hb; assumption.
Qed.
Lemma VtTag_sym : forall a b, VtTag a b -> VtTag b a.
Proof. intros a b H; induction H; econstructor. Qed.
Lemma VtTag_trans : forall a b c, VtTag a b -> VtTag b c -> VtTag a c.
Proof.
  intros a b c H1 H2. revert c H2. induction H1; intros c' H2; inversion H2; subst; econstructor.
Qed.
Lemma VtTag_refl : forall a, ValueType a -> VtTag a a.
Proof. intros a H; induction H; econstructor. Qed.

Lemma open_head_stable : forall B a1 a2,
  B <> a_Var_b 0 -> ValueType (open_tm_wrt_tm B a1) ->
  VtTag (open_tm_wrt_tm B a1) (open_tm_wrt_tm B a2).
Proof.
  intros B. destruct B; intros a1 a2 Hneq HVT.
  - (* TyUnit *) simpl. econstructor.
  - (* TmUnit *) simpl in HVT; inversion HVT.
  - (* Pi *) simpl in *; inversion HVT; subst; econstructor.
  - (* Abs *) simpl in HVT; inversion HVT.
  - (* App *) simpl in HVT; inversion HVT.
  - (* Type *) simpl in *; inversion HVT; subst; econstructor.
  - (* Var_b *) destruct n.
    + exfalso; apply Hneq; reflexivity.
    + simpl in HVT; inversion HVT.
  - (* Var_f *) simpl in HVT; inversion HVT.
  - (* Sum *) simpl in *; inversion HVT; subst; econstructor.
  - (* Inj1 *) simpl in HVT; inversion HVT.
  - (* Inj2 *) simpl in HVT; inversion HVT.
  - (* Case *) simpl in HVT; inversion HVT.
  - (* WSigma *) simpl in *; inversion HVT; subst; econstructor.
  - (* WPair *) simpl in HVT; inversion HVT.
  - (* LetPair *) simpl in HVT; inversion HVT.
  - (* SSigma *) simpl in *; inversion HVT; subst; econstructor.
  - (* SPair *) simpl in HVT; inversion HVT.
  - (* Proj1 *) simpl in HVT; inversion HVT.
  - (* Proj2 *) simpl in HVT; inversion HVT.
Qed.

(* ---------- consistency bookkeeping ---------- *)
(* From agreement of value-type heads (plus local closure) to [Consistent]. *)
Lemma Consistent_of_VtTag : forall a b, VtTag a b -> lc_tm a -> lc_tm b -> Consistent a b.
Proof.
  intros a b H. induction H; intros Ha Hb.
  - apply Consistent_a_Type.
  - apply Consistent_a_Unit.
  - apply Consistent_a_Pi.
    + inversion Ha; assumption. + assumption. + inversion Hb; assumption. + assumption.
  - apply Consistent_a_WSigma.
    + inversion Ha; assumption. + assumption. + inversion Hb; assumption. + assumption.
  - apply Consistent_a_SSigma.
    + inversion Ha; assumption. + assumption. + inversion Hb; assumption. + assumption.
  - apply Consistent_a_Sum.
    + inversion Ha; assumption. + inversion Ha; assumption.
    + inversion Hb; assumption. + inversion Hb; assumption.
Qed.
Arguments Consistent_of_VtTag : clear implicits.
Arguments Consistent_of_VtTag a b _ _ _.

Lemma Consistent_refl : forall a, lc_tm a -> Consistent a a.
Proof.
  intros a H. destruct a; try solve [apply Consistent_a_Step_R; [exact H | intro H'; inversion H']].
  - (* TyUnit *) apply Consistent_a_Unit.
  - (* Pi *) apply Consistent_a_Pi; [inversion H; assumption | assumption | inversion H; assumption | assumption].
  - (* Type *) apply Consistent_a_Type.
  - (* Sum *) apply Consistent_a_Sum; try (inversion H; assumption); try assumption.
  - (* WSigma *) apply Consistent_a_WSigma; [inversion H; assumption | assumption | inversion H; assumption | assumption].
  - (* SSigma *) apply Consistent_a_SSigma; [inversion H; assumption | assumption | inversion H; assumption | assumption].
Qed.

Ltac vt_build :=
  match goal with
  | |- ValueType (a_Type _) => apply ValueType_Type
  | |- ValueType a_TyUnit => apply ValueType_Unit
  | Ha : lc_tm (a_Pi _ _ _) |- ValueType (a_Pi _ _ _) => apply ValueType_Pi; [inversion Ha; assumption | exact Ha]
  | Ha : lc_tm (a_WSigma _ _ _) |- ValueType (a_WSigma _ _ _) => apply ValueType_WSigma; [inversion Ha; assumption | exact Ha]
  | Ha : lc_tm (a_SSigma _ _ _) |- ValueType (a_SSigma _ _ _) => apply ValueType_SSigma; [inversion Ha; assumption | exact Ha]
  | Ha : lc_tm (a_Sum _ _) |- ValueType (a_Sum _ _) => apply ValueType_Sum; [inversion Ha; assumption | inversion Ha; assumption]
  end.

Lemma Consistent_total : forall a b, lc_tm a -> lc_tm b ->
  (ValueType a -> ValueType b -> VtTag a b) -> Consistent a b.
Proof.
  intros a. destruct a; intros b Ha Hb Htag;
    try solve [apply Consistent_a_Step_R; [exact Hb | intro H'; inversion H']];
    destruct b;
    try solve [apply Consistent_a_Step_L; [exact Ha | intro H'; inversion H']].
  all: try solve [exfalso; pose proof (Htag ltac:(vt_build) ltac:(vt_build)) as HT; inversion HT].
  all: apply Consistent_of_VtTag; [ pose proof (Htag ltac:(vt_build) ltac:(vt_build)) as HT; exact HT | exact Ha | exact Hb ].
Qed.

Inductive Steps : tm -> tm -> Prop :=
| Steps_refl : forall a, Steps a a
| Steps_step : forall a b c, Step a b -> Steps b c -> Steps a c.

(* ---------- deep invariant (reduction-aware, inductive carrier) ---------- *)
Inductive Deep (P:econtext) (phi:grade) : tm -> tm -> Prop :=
| Deep_Type : forall s, Deep P phi (a_Type s) (a_Type s)
| Deep_Unit : Deep P phi a_TyUnit a_TyUnit
| Deep_Pi : forall psi A1 B1 A2 B2,
    Deep P phi A1 A2 ->
    (forall x, Deep ((x~phi)++P) phi (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B2 (a_Var_f x))) ->
    Deep P phi (a_Pi psi A1 B1) (a_Pi psi A2 B2)
| Deep_WSigma : forall psi A1 B1 A2 B2,
    Deep P phi A1 A2 ->
    (forall x, Deep ((x~phi)++P) phi (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B2 (a_Var_f x))) ->
    Deep P phi (a_WSigma psi A1 B1) (a_WSigma psi A2 B2)
| Deep_SSigma : forall psi A1 B1 A2 B2,
    Deep P phi A1 A2 ->
    (forall x, Deep ((x~phi)++P) phi (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B2 (a_Var_f x))) ->
    Deep P phi (a_SSigma psi A1 B1) (a_SSigma psi A2 B2)
| Deep_Sum : forall A1 B1 A2 B2,
    Deep P phi A1 A2 -> Deep P phi B1 B2 ->
    Deep P phi (a_Sum A1 B1) (a_Sum A2 B2)
| Deep_NonVT : forall a b,
    lc_tm a -> lc_tm b -> Consistent a b ->
    (forall u, ValueType u -> Steps a u -> exists v, Steps b v /\ ValueType v /\ VtTag u v) ->
    (forall v, ValueType v -> Steps b v -> exists u, Steps a u /\ ValueType u /\ VtTag u v) ->
    (forall psi A1 B1 A2 B2, Steps a (a_Pi psi A1 B1) -> Steps b (a_Pi psi A2 B2) ->
        Deep P phi A1 A2 /\ (forall x, Deep ((x~phi)++P) phi (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B2 (a_Var_f x)))) ->
    (forall psi A1 B1 A2 B2, Steps a (a_WSigma psi A1 B1) -> Steps b (a_WSigma psi A2 B2) ->
        Deep P phi A1 A2 /\ (forall x, Deep ((x~phi)++P) phi (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B2 (a_Var_f x)))) ->
    (forall psi A1 B1 A2 B2, Steps a (a_SSigma psi A1 B1) -> Steps b (a_SSigma psi A2 B2) ->
        Deep P phi A1 A2 /\ (forall x, Deep ((x~phi)++P) phi (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B2 (a_Var_f x)))) ->
    (forall A1 B1 A2 B2, Steps a (a_Sum A1 B1) -> Steps b (a_Sum A2 B2) ->
        Deep P phi A1 A2 /\ Deep P phi B1 B2) ->
    Deep P phi a b.

(* ---------- parallel reduction / Joins -> Consistent ---------- *)

(* ---------- Parallel reduction preserves value-type tags ---------- *)
Lemma Par_VtTag_form : forall (P:econtext) (phi:grade) (a b:tm),
  Par P phi a b -> forall t, VtTag t a -> VtTag t b.
Proof.
  intros P phi a b H. induction H; intros t HT;
    try solve [exfalso; inversion HT];
    try solve [inversion HT; econstructor];
    assumption.
Qed.
Arguments Par_VtTag_form : clear implicits.
Arguments Par_VtTag_form P phi a b _ _ _.

Lemma MultiPar_VtTag : forall (P:econtext) (phi:grade) (a b:tm),
  MultiPar P phi a b -> forall t, VtTag t a -> VtTag t b.
Proof.
  intros P phi a b H. induction H; intros t HT.
  - exact HT.
  - apply IHMultiPar. exact (Par_VtTag_form _ _ _ _ H t HT).
Qed.
Arguments MultiPar_VtTag : clear implicits.
Arguments MultiPar_VtTag P phi a b _ _ _.

Lemma MultiPar_VT : forall (P:econtext) (phi:grade) (a b:tm),
  MultiPar P phi a b -> ValueType a -> VtTag a b.
Proof.
  intros P phi a b H HVT. exact (MultiPar_VtTag _ _ _ _ H a (VtTag_refl HVT)).
Qed.
Arguments MultiPar_VT : clear implicits.
Arguments MultiPar_VT P phi a b _ _.

(* ---------- GEq preserves value-type tags ---------- *)
Lemma GEq_VtTag_form : forall (P:econtext) (phi:grade) (a b:tm),
  GEq P phi a b -> forall t, VtTag t a -> VtTag t b.
Proof.
  intros P phi a b H. induction H; intros t HT;
    try solve [exfalso; inversion HT];
    try solve [inversion HT; econstructor];
    assumption.
Qed.
Arguments GEq_VtTag_form : clear implicits.
Arguments GEq_VtTag_form P phi a b _ _ _.

(* ---------- Joins imply consistency ---------- *)
Lemma Joins_Consistent : forall (P:econtext) (phi:grade) (a b:tm),
  Joins P phi a b -> lc_tm a -> lc_tm b -> Consistent a b.
Proof.
  intros P phi a b H Ha Hb. destruct H as [P0 psi a1 a2 b1 b2 Mp1 Mp2 Ge].
  apply Consistent_total; [exact Ha | exact Hb |].
  intros VTa VTb.
  pose proof (MultiPar_VT P0 psi a1 b1 Mp1 VTa) as H1.
  pose proof (MultiPar_VT P0 psi a2 b2 Mp2 VTb) as H2.
  pose proof (GEq_VtTag_form P0 psi b1 b2 Ge a1 H1) as H3.
  apply VtTag_trans with b2; [exact H3 | apply VtTag_sym; exact H2].
Qed.
Arguments Joins_Consistent : clear implicits.
Arguments Joins_Consistent P phi a b _ _ _.

(* ---------- Grade/Par/LN layer for DefEq -> Joins ---------- *)

(* ---------- Grade/ CGrade yield reflexive GEq/CEq ---------- *)
Lemma Grade_GEq_refl : forall (P:econtext) (psi:grade) (a:tm), Grade P psi a -> GEq P psi a a.
Proof.
  intros P psi a H. induction H using Grade_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a:tm) (_:CGrade P psi phi0 a) => CEq P psi phi0 a a).
  all: try (apply CEq_Nleq; assumption).
  all: try (econstructor; eauto).
  all: assumption.
Qed.
Arguments Grade_GEq_refl : clear implicits.
Arguments Grade_GEq_refl P psi a _.

Lemma CGrade_CEq_refl : forall (P:econtext) (psi phi0:grade) (a:tm), CGrade P psi phi0 a -> CEq P psi phi0 a a.
Proof.
  intros P psi phi0 a H. induction H.
  - apply CEq_Leq; [assumption | apply Grade_GEq_refl; assumption].
  - apply CEq_Nleq; assumption.
Qed.
Arguments CGrade_CEq_refl : clear implicits.
Arguments CGrade_CEq_refl P psi phi0 a _.

Lemma Grade_CPar_refl : forall (P:econtext) (psi phi0:grade) (a:tm), CGrade P psi phi0 a -> CPar P psi phi0 a a.
Proof.
  intros P psi phi0 a H. induction H.
  - apply CPar_Leq; [assumption | apply Par_Refl; assumption].
  - apply CPar_Nleq; assumption.
Qed.
Arguments Grade_CPar_refl : clear implicits.
Arguments Grade_CPar_refl P psi phi0 a _.

(* ---------- Grade inversions (syntactic shape of graded terms) ---------- *)
Lemma Grade_App_inv : forall P psi b psi0 a, Grade P psi (a_App b psi0 a) -> Grade P psi b /\ CGrade P psi psi0 a.
Proof. intros. inversion H. auto. Qed.
Lemma Grade_SPair_inv : forall P psi a psi0 b, Grade P psi (a_SPair a psi0 b) -> CGrade P psi psi0 a /\ Grade P psi b.
Proof. intros. inversion H. auto. Qed.
Lemma Grade_WPair_inv : forall P psi a psi0 b, Grade P psi (a_WPair a psi0 b) -> CGrade P psi psi0 a /\ Grade P psi b.
Proof. intros. inversion H. auto. Qed.
Lemma Grade_Proj1_inv : forall P psi psi0 a, Grade P psi (a_Proj1 psi0 a) -> Grade P psi a /\ psi0 <= psi.
Proof. intros. inversion H. auto. Qed.
Lemma Grade_Proj2_inv : forall P psi psi0 a, Grade P psi (a_Proj2 psi0 a) -> Grade P psi a.
Proof. intros. inversion H. auto. Qed.
Lemma Grade_Inj1_inv : forall P psi a, Grade P psi (a_Inj1 a) -> Grade P psi a.
Proof. intros. inversion H. auto. Qed.
Lemma Grade_Inj2_inv : forall P psi a, Grade P psi (a_Inj2 a) -> Grade P psi a.
Proof. intros. inversion H. auto. Qed.
Lemma Grade_Case_inv : forall P psi psi0 a b1 b2, Grade P psi (a_Case psi0 a b1 b2) -> Grade P psi a /\ Grade P psi b1 /\ Grade P psi b2 /\ psi0 <= psi.
Proof. intros. inversion H. repeat split; auto. Qed.
Lemma Grade_LetPair_inv : forall P psi psi0 a b,
  Grade P psi (a_LetPair psi0 a b) ->
  Grade P psi a /\ (exists L, forall x, x `notin` L -> Grade ((x~psi0)++P) psi (open_tm_wrt_tm b (a_Var_f x))).
Proof. intros. inversion H. split; [assumption| eexists; eauto]. Qed.

(* ---------- a single Step is simulated by Par ---------- *)
Lemma Par_of_Step : forall (P:econtext) (psi:grade) (a b:tm),
  Grade P psi a -> Step a b -> Grade P psi b -> Par P psi a b.
Proof.
  intros P psi a b Ga S Gb. revert Gb. induction S; intros Gb.
  - (* AppCong *) destruct (Grade_App_inv Ga) as [Gf CGfb]; destruct (Grade_App_inv Gb) as [Gf' _].
    eapply Par_App.
    + apply IHS; assumption.
    + apply Grade_CPar_refl; assumption.
  - (* Beta *) destruct (Grade_App_inv Ga) as [Gabs CGarg].
    eapply Par_AppBeta.
    + eapply Par_Refl; assumption.
    + apply Grade_CPar_refl; assumption.
  - (* CaseCong *) destruct (Grade_Case_inv Ga) as [Ga0 [Gb1 [Gb2 Hle]]].
    destruct (Grade_Case_inv Gb) as [Ga' _].
    eapply Par_Case.
    + apply IHS; assumption.
    + eapply Par_Refl; assumption.
    + eapply Par_Refl; assumption.
    + assumption.
  - (* Case1Beta *) destruct (Grade_Case_inv Ga) as [Ginj [Gb1 [Gb2 Hle]]].
    pose proof (Grade_Inj1_inv Ginj) as Gx.
    eapply Par_CaseBeta1.
    + eapply Par_Inj1. eapply Par_Refl; assumption.
    + eapply Par_Refl; assumption.
    + eapply Par_Refl; assumption.
    + assumption.
  - (* Case2Beta *) destruct (Grade_Case_inv Ga) as [Ginj [Gb1 [Gb2 Hle]]].
    pose proof (Grade_Inj2_inv Ginj) as Gx.
    eapply Par_CaseBeta2.
    + eapply Par_Inj2. eapply Par_Refl; assumption.
    + eapply Par_Refl; assumption.
    + eapply Par_Refl; assumption.
    + assumption.
  - (* Proj1Cong *) destruct (Grade_Proj1_inv Ga) as [Ga0 Hle].
    destruct (Grade_Proj1_inv Gb) as [Ga' _].
    eapply Par_Proj1; [apply IHS; assumption | assumption].
  - (* Proj2Cong *) pose proof (Grade_Proj2_inv Ga) as Ga0.
    pose proof (Grade_Proj2_inv Gb) as Ga'.
    eapply Par_Proj2; apply IHS; assumption.
  - (* Proj1Beta *) destruct (Grade_Proj1_inv Ga) as [Gsp Hle].
    destruct (Grade_SPair_inv Gsp) as [CGa1 Ga2].
    eapply Par_Proj1Beta.
    + eapply Par_SPair; [apply Grade_CPar_refl; assumption | eapply Par_Refl; assumption].
    + assumption.
  - (* Proj2Beta *) pose proof (Grade_Proj2_inv Ga) as Gsp.
    destruct (Grade_SPair_inv Gsp) as [CGa1 Ga2].
    eapply Par_Proj2Beta.
    + eapply Par_SPair; [apply Grade_CPar_refl; assumption | eapply Par_Refl; assumption].
  - (* LetPairCong *) destruct (Grade_LetPair_inv Ga) as [Ga0 [L HG]].
    destruct (Grade_LetPair_inv Gb) as [Ga' _].
    eapply Par_LetPair with (L := L).
    + apply IHS; assumption.
    + intros x Hx. eapply Par_Refl. apply HG; assumption.
  - (* LetPairBeta *) destruct (Grade_LetPair_inv Ga) as [Gwp [L HG]].
    destruct (Grade_WPair_inv Gwp) as [CGa1 Ga2].
    eapply Par_WPairBeta with (L := L).
    + eapply Par_WPair; [apply Grade_CPar_refl; assumption | eapply Par_Refl; assumption].
    + intros x Hx. eapply Par_Refl. apply HG; assumption.
Qed.

(* ---------- GEq/CEq symmetry ---------- *)

(* ---------- symmetry of GEq / CEq ---------- *)
Scheme GEq_mind := Induction for GEq Sort Prop
  with CEq_mind := Induction for CEq Sort Prop.

Lemma GEq_sym : forall (P:econtext) (phi:grade) (a b:tm), GEq P phi a b -> GEq P phi b a.
Proof.
  intros P phi a b H. induction H using GEq_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a b:tm) (_:CEq P psi phi0 a b) => CEq P psi phi0 b a).
  all: try (apply CEq_Nleq; assumption).
  all: try (econstructor; eauto).
  all: assumption.
Qed.
Arguments GEq_sym : clear implicits.
Arguments GEq_sym P phi a b _.

Lemma CEq_sym : forall (P:econtext) (phi phi0:grade) (a b:tm), CEq P phi phi0 a b -> CEq P phi phi0 b a.
Proof.
  intros P phi phi0 a b H. induction H.
  - apply CEq_Leq; [assumption | apply GEq_sym; assumption].
  - apply CEq_Nleq; assumption.
Qed.
Arguments CEq_sym : clear implicits.
Arguments CEq_sym P phi phi0 a b _.

(* ---------- DefEq implies a unique context ---------- *)

(* ---------- DefEq endpoints live in unique contexts ---------- *)
Lemma DefEq_uniq : forall (P:econtext) (psi:grade) (a b:tm), DefEq P psi a b -> uniq P.
Proof.
  intros P psi a b H. induction H using DefEq_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a b:tm) (_:CDefEq P psi phi0 a b) => uniq P).
  all: try solve [match goal with Hg : Grade ?P' ?ps ?a' |- uniq ?P' => exact (Grade_uniq P' ps a' Hg) end].
  all: try assumption.
  - (* SubstIrrel *) destruct (atom_fresh L) as [x Hx].
    exact (@uniq_app_2 _ (x ~ psi) P (H x Hx)).
Qed.
Arguments DefEq_uniq : clear implicits.
Arguments DefEq_uniq P psi a b _.

(* ---------- basic Joins facts ---------- *)

(* ---------- basic Joins facts ---------- *)
Lemma Joins_refl : forall (P:econtext) (psi:grade) (a:tm), Grade P psi a -> Joins P psi a a.
Proof.
  intros P psi a G. eapply join with (b1 := a) (b2 := a).
  - apply MP_Refl; assumption.
  - apply MP_Refl; assumption.
  - apply Grade_GEq_refl; assumption.
Qed.
Arguments Joins_refl : clear implicits.
Arguments Joins_refl P psi a _.

Lemma Joins_sym : forall (P:econtext) (psi:grade) (a b:tm), Joins P psi a b -> Joins P psi b a.
Proof.
  intros P psi a b H. destruct H as [P0 ps a1 a2 b1 b2 M1 M2 G].
  eapply join with (b1 := b2) (b2 := b1).
  - exact M2. - exact M1. - apply GEq_sym; exact G.
Qed.
Arguments Joins_sym : clear implicits.
Arguments Joins_sym P psi a b _.

Lemma Joins_beta : forall (P:econtext) (psi:grade) (a b:tm),
  Grade P psi a -> Step a b -> Grade P psi b -> Joins P psi a b.
Proof.
  intros P psi a b Ga S Gb. eapply join with (b1 := b) (b2 := b).
  - apply MP_Step with (b := b); [apply Par_of_Step; assumption | apply MP_Refl; assumption].
  - apply MP_Refl; assumption.
  - apply Grade_GEq_refl; assumption.
Qed.
Arguments Joins_beta : clear implicits.
Arguments Joins_beta P psi a b _ _ _.


(* ---------- Grade inversions for compound types ---------- *)
Lemma Grade_Pi_inv : forall P psi psi0 A B, Grade P psi (a_Pi psi0 A B) -> Grade P psi A.
Proof. intros. inversion H. assumption. Qed.
Lemma Grade_WSigma_inv : forall P psi psi0 A B, Grade P psi (a_WSigma psi0 A B) -> Grade P psi A.
Proof. intros. inversion H. assumption. Qed.
Lemma Grade_SSigma_inv : forall P psi psi0 A B, Grade P psi (a_SSigma psi0 A B) -> Grade P psi A.
Proof. intros. inversion H. assumption. Qed.
Lemma Grade_Sum_inv : forall P psi A B, Grade P psi (a_Sum A B) -> Grade P psi A /\ Grade P psi B.
Proof. intros. inversion H. auto. Qed.
Arguments Grade_Pi_inv : clear implicits. Arguments Grade_Pi_inv P psi psi0 A B _.
Arguments Grade_WSigma_inv : clear implicits. Arguments Grade_WSigma_inv P psi psi0 A B _.
Arguments Grade_SSigma_inv : clear implicits. Arguments Grade_SSigma_inv P psi psi0 A B _.
Arguments Grade_Sum_inv : clear implicits. Arguments Grade_Sum_inv P psi A B _.


(* ---------- shape inversion of MultiPar for compound value types ---------- *)
Lemma MultiPar_Pi_fst : forall P psi a b, MultiPar P psi a b ->
  forall psi0 A1 B1, a = a_Pi psi0 A1 B1 -> exists A1', MultiPar P psi A1 A1'.
Proof.
  intros P psi a b H. induction H; intros psi0 A1 B1 EQ.
  - subst a. eexists. apply MP_Refl. exact (Grade_Pi_inv P psi psi0 A1 B1 H).
  - subst a. inversion H; subst.
    + eapply IHMultiPar. reflexivity.
    + assert (Heq : a_Pi psi0 A2 B2 = a_Pi psi0 A2 B2) by reflexivity; destruct (IHMultiPar psi0 A2 B2 Heq) as [Z Mp].
      exists Z. eapply MP_Step; [exact H7 | exact Mp].
Qed.
Lemma MultiPar_WSigma_fst : forall P psi a b, MultiPar P psi a b ->
  forall psi0 A1 B1, a = a_WSigma psi0 A1 B1 -> exists A1', MultiPar P psi A1 A1'.
Proof.
  intros P psi a b H. induction H; intros psi0 A1 B1 EQ.
  - subst a. eexists. apply MP_Refl. exact (Grade_WSigma_inv P psi psi0 A1 B1 H).
  - subst a. inversion H; subst.
    + eapply IHMultiPar. reflexivity.
    + assert (Heq : a_WSigma psi0 A2 B2 = a_WSigma psi0 A2 B2) by reflexivity; destruct (IHMultiPar psi0 A2 B2 Heq) as [Z Mp].
      exists Z. eapply MP_Step; [exact H7 | exact Mp].
Qed.
Lemma MultiPar_SSigma_fst : forall P psi a b, MultiPar P psi a b ->
  forall psi0 A1 B1, a = a_SSigma psi0 A1 B1 -> exists A1', MultiPar P psi A1 A1'.
Proof.
  intros P psi a b H. induction H; intros psi0 A1 B1 EQ.
  - subst a. eexists. apply MP_Refl. exact (Grade_SSigma_inv P psi psi0 A1 B1 H).
  - subst a. inversion H; subst.
    + eapply IHMultiPar. reflexivity.
    + assert (Heq : a_SSigma psi0 A2 B2 = a_SSigma psi0 A2 B2) by reflexivity; destruct (IHMultiPar psi0 A2 B2 Heq) as [Z Mp].
      exists Z. eapply MP_Step; [exact H7 | exact Mp].
Qed.
Lemma MultiPar_Sum_fst : forall P psi a b, MultiPar P psi a b ->
  forall A1 B1, a = a_Sum A1 B1 -> exists A1', MultiPar P psi A1 A1'.
Proof.
  intros P psi a b H. induction H; intros A1 B1 EQ.
  - subst a. eexists. apply MP_Refl. exact (proj1 (Grade_Sum_inv P psi A1 B1 H)).
  - subst a. inversion H; subst.
    + eapply IHMultiPar. reflexivity.
    + edestruct IHMultiPar as [Z Mp]; [reflexivity |].
      exists Z. eapply MP_Step; [eassumption | exact Mp].
Qed.
Lemma MultiPar_Sum_snd : forall P psi a b, MultiPar P psi a b ->
  forall A1 B1, a = a_Sum A1 B1 -> exists B1', MultiPar P psi B1 B1'.
Proof.
  intros P psi a b H. induction H; intros A1 B1 EQ.
  - subst a. eexists. apply MP_Refl. exact (proj2 (Grade_Sum_inv P psi A1 B1 H)).
  - subst a. inversion H; subst.
    + eapply IHMultiPar. reflexivity.
    + edestruct IHMultiPar as [Z Mp]; [reflexivity |].
      exists Z. eapply MP_Step; [eassumption | exact Mp].
Qed.


(* ================= Stage 1: free variables, opening and substitution ================= *)
Lemma fv_open_rec_in : forall B k u z,
  z \in fv_tm_tm B -> z \in fv_tm_tm (open_tm_wrt_tm_rec k u B) \/ z \in fv_tm_tm u.
Proof.
  intros B. induction B as
    [| |psi A IHA B IHB |psi A IHA b IHb |a IHa psi b IHb |sq |n |x |A1 IHA1 A2 IHA2 |a IHa |a IHa
    |psi a IHa b1 IHb1 b2 IHb2 |psi A IHA B IHB |a IHa psi b IHb |psi a IHa b IHb
    |psi A IHA B IHB |a IHa psi b IHb |psi a IHa |psi a IHa ];
    intros k u z Hx; simpl in *.
  - exfalso; eapply AtomSetImpl.empty_1; eassumption.
  - exfalso; eapply AtomSetImpl.empty_1; eassumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHB (S k) u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb (S k) u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHa k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - exfalso; eapply AtomSetImpl.empty_1; eassumption.
  - exfalso; eapply AtomSetImpl.empty_1; eassumption.
  - left; eapply AtomSetImpl.singleton_2; eapply AtomSetImpl.singleton_1; eassumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA1 k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHA2 k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - exact (IHa k u z Hx).
  - exact (IHa k u z Hx).
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx].
    + destruct (IHa k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right]; assumption.
    + apply AtomSetImpl.union_1 in Hx as [Hx|Hx].
      * destruct (IHb1 k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3; apply AtomSetImpl.union_2 | right]; assumption.
      * destruct (IHb2 k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3; apply AtomSetImpl.union_3 | right]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHB (S k) u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHa k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHa k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb (S k) u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHB (S k) u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHa k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - exact (IHa k u z Hx).
  - exact (IHa k u z Hx).
Qed.

Lemma fv_open_rec_out : forall B k u z,
  z \in fv_tm_tm (open_tm_wrt_tm_rec k u B) -> z \in fv_tm_tm B \/ z \in fv_tm_tm u.
Proof.
  intros B. induction B as
    [| |psi A IHA B IHB |psi A IHA b IHb |a IHa psi b IHb |sq |n |x |A1 IHA1 A2 IHA2 |a IHa |a IHa
    |psi a IHa b1 IHb1 b2 IHb2 |psi A IHA B IHB |a IHa psi b IHb |psi a IHa b IHb
    |psi A IHA B IHB |a IHa psi b IHb |psi a IHa |psi a IHa ];
    intros k u z Hx; simpl in *.
  - exfalso; eapply AtomSetImpl.empty_1; eassumption.
  - exfalso; eapply AtomSetImpl.empty_1; eassumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHB (S k) u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb (S k) u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHa k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - exfalso; eapply AtomSetImpl.empty_1; eassumption.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl in *;
      [left; assumption | right; assumption | left; assumption].
  - left; eapply AtomSetImpl.singleton_2; eapply AtomSetImpl.singleton_1; eassumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA1 k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHA2 k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - exact (IHa k u z Hx).
  - exact (IHa k u z Hx).
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx].
    + destruct (IHa k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right]; assumption.
    + apply AtomSetImpl.union_1 in Hx as [Hx|Hx].
      * destruct (IHb1 k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3; apply AtomSetImpl.union_2 | right]; assumption.
      * destruct (IHb2 k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3; apply AtomSetImpl.union_3 | right]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHB (S k) u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHa k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHa k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb (S k) u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHB (S k) u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHa k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb k u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - exact (IHa k u z Hx).
  - exact (IHa k u z Hx).
Qed.

Lemma fv_open_in : forall B u z,
  z \in fv_tm_tm B -> z \in fv_tm_tm (open_tm_wrt_tm B u) \/ z \in fv_tm_tm u.
Proof. intros; apply (@fv_open_rec_in B 0 u z); assumption. Qed.

Lemma fv_open_out : forall B u z,
  z \in fv_tm_tm (open_tm_wrt_tm B u) -> z \in fv_tm_tm B \/ z \in fv_tm_tm u.
Proof. intros; apply (@fv_open_rec_out B 0 u z); assumption. Qed.

Lemma fv_subst_out : forall B y u z,
  z \in fv_tm_tm (subst_tm_tm u y B) -> z \in fv_tm_tm B \/ z \in fv_tm_tm u.
Proof.
  intros B. induction B as
    [| |psi A IHA B IHB |psi A IHA b IHb |a IHa psi b IHb |sq |n |x |A1 IHA1 A2 IHA2 |a IHa |a IHa
    |psi a IHa b1 IHb1 b2 IHb2 |psi A IHA B IHB |a IHa psi b IHb |psi a IHa b IHb
    |psi A IHA B IHB |a IHa psi b IHb |psi a IHa |psi a IHa ];
    intros y u z Hx; simpl in *.
  - exfalso; eapply AtomSetImpl.empty_1; eassumption.
  - exfalso; eapply AtomSetImpl.empty_1; eassumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHB y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHa y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - exfalso; eapply AtomSetImpl.empty_1; eassumption.
  - left; assumption.
  - destruct (CoqEqDec.eq_dec x y) as [E|E]; simpl in *.
    + right; assumption.
    + left; eapply AtomSetImpl.singleton_2; eapply AtomSetImpl.singleton_1; eassumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA1 y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHA2 y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - exact (IHa y u z Hx).
  - exact (IHa y u z Hx).
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx].
    + destruct (IHa y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right]; assumption.
    + apply AtomSetImpl.union_1 in Hx as [Hx|Hx].
      * destruct (IHb1 y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3; apply AtomSetImpl.union_2 | right]; assumption.
      * destruct (IHb2 y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3; apply AtomSetImpl.union_3 | right]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHB y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHa y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHa y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHA y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHB y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - apply AtomSetImpl.union_1 in Hx as [Hx|Hx];
      [destruct (IHa y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_2 | right] |
       destruct (IHb y u z Hx) as [H|H]; [left; apply AtomSetImpl.union_3 | right]]; assumption.
  - exact (IHa y u z Hx).
  - exact (IHa y u z Hx).
Qed.

Lemma subst_tm_tm_same_f : forall u x, subst_tm_tm u x (a_Var_f x) = u.
Proof.
  intros. simpl. destruct (CoqEqDec.eq_dec x x) as [E|E]; [reflexivity | exfalso; apply E; reflexivity].
Qed.

Lemma subst_open_rec : forall B k u z,
  z \notin fv_tm_tm B ->
  subst_tm_tm u z (open_tm_wrt_tm_rec k (a_Var_f z) B) = open_tm_wrt_tm_rec k u B.
Proof.
  intros B. induction B as
    [| |psi A IHA B IHB |psi A IHA b IHb |a IHa psi b IHb |sq |n |x |A1 IHA1 A2 IHA2 |a IHa |a IHa
    |psi a IHa b1 IHb1 b2 IHb2 |psi A IHA B IHB |a IHa psi b IHb |psi a IHa b IHb
    |psi A IHA B IHB |a IHa psi b IHb |psi a IHa |psi a IHa ];
    intros k u z Hx; simpl in *.
  - reflexivity.
  - reflexivity.
  - assert (xA : z \notin fv_tm_tm A) by (intro HH; apply Hx, AtomSetImpl.union_2; exact HH).
    assert (xB : z \notin fv_tm_tm B) by (intro HH; apply Hx, AtomSetImpl.union_3; exact HH).
    rewrite (IHA k u z xA), (IHB (S k) u z xB). reflexivity.
  - assert (xA : z \notin fv_tm_tm A) by (intro HH; apply Hx, AtomSetImpl.union_2; exact HH).
    assert (xB : z \notin fv_tm_tm b) by (intro HH; apply Hx, AtomSetImpl.union_3; exact HH).
    rewrite (IHA k u z xA), (IHb (S k) u z xB). reflexivity.
  - assert (xA : z \notin fv_tm_tm a) by (intro HH; apply Hx, AtomSetImpl.union_2; exact HH).
    assert (xB : z \notin fv_tm_tm b) by (intro HH; apply Hx, AtomSetImpl.union_3; exact HH).
    rewrite (IHa k u z xA), (IHb k u z xB). reflexivity.
  - reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?].
    + reflexivity.
    + rewrite subst_tm_tm_same_f. reflexivity.
    + reflexivity.
  - destruct (CoqEqDec.eq_dec x z) as [E|E].
    + exfalso; apply Hx; subst; simpl; apply AtomSetImpl.singleton_2; reflexivity.
    + reflexivity.
  - assert (xA : z \notin fv_tm_tm A1) by (intro HH; apply Hx, AtomSetImpl.union_2; exact HH).
    assert (xB : z \notin fv_tm_tm A2) by (intro HH; apply Hx, AtomSetImpl.union_3; exact HH).
    rewrite (IHA1 k u z xA), (IHA2 k u z xB). reflexivity.
  - rewrite (IHa k u z Hx). reflexivity.
  - rewrite (IHa k u z Hx). reflexivity.
  - assert (xA : z \notin fv_tm_tm a) by (intro HH; apply Hx, AtomSetImpl.union_2; exact HH).
    assert (xUnion : z \notin AtomSetImpl.union (fv_tm_tm b1) (fv_tm_tm b2))
      by (intro HH; apply Hx, AtomSetImpl.union_3; exact HH).
    assert (xB : z \notin fv_tm_tm b1) by (intro HH; apply xUnion, AtomSetImpl.union_2; exact HH).
    assert (xC : z \notin fv_tm_tm b2) by (intro HH; apply xUnion, AtomSetImpl.union_3; exact HH).
    rewrite (IHa k u z xA), (IHb1 k u z xB), (IHb2 k u z xC). reflexivity.
  - assert (xA : z \notin fv_tm_tm A) by (intro HH; apply Hx, AtomSetImpl.union_2; exact HH).
    assert (xB : z \notin fv_tm_tm B) by (intro HH; apply Hx, AtomSetImpl.union_3; exact HH).
    rewrite (IHA k u z xA), (IHB (S k) u z xB). reflexivity.
  - assert (xA : z \notin fv_tm_tm a) by (intro HH; apply Hx, AtomSetImpl.union_2; exact HH).
    assert (xB : z \notin fv_tm_tm b) by (intro HH; apply Hx, AtomSetImpl.union_3; exact HH).
    rewrite (IHa k u z xA), (IHb k u z xB). reflexivity.
  - assert (xA : z \notin fv_tm_tm a) by (intro HH; apply Hx, AtomSetImpl.union_2; exact HH).
    assert (xB : z \notin fv_tm_tm b) by (intro HH; apply Hx, AtomSetImpl.union_3; exact HH).
    rewrite (IHa k u z xA), (IHb (S k) u z xB). reflexivity.
  - assert (xA : z \notin fv_tm_tm A) by (intro HH; apply Hx, AtomSetImpl.union_2; exact HH).
    assert (xB : z \notin fv_tm_tm B) by (intro HH; apply Hx, AtomSetImpl.union_3; exact HH).
    rewrite (IHA k u z xA), (IHB (S k) u z xB). reflexivity.
  - assert (xA : z \notin fv_tm_tm a) by (intro HH; apply Hx, AtomSetImpl.union_2; exact HH).
    assert (xB : z \notin fv_tm_tm b) by (intro HH; apply Hx, AtomSetImpl.union_3; exact HH).
    rewrite (IHa k u z xA), (IHb k u z xB). reflexivity.
  - rewrite (IHa k u z Hx). reflexivity.
  - rewrite (IHa k u z Hx). reflexivity.
Qed.

Lemma subst_open_tm_wrt_tm : forall B u z,
  z \notin fv_tm_tm B ->
  subst_tm_tm u z (open_tm_wrt_tm B (a_Var_f z)) = open_tm_wrt_tm B u.
Proof. intros; apply (@subst_open_rec B 0 u z); assumption. Qed.


(* ================= Stage 2a: removal from econtexts, weakening, lc of subst ================= *)
Fixpoint remove_ec (x:atom) (C:econtext) : econtext :=
  match C with
  | nil => nil
  | (y,g) :: C' => if CoqEqDec.eq_dec y x then C' else (y,g) :: remove_ec x C'
  end.

Lemma remove_ec_head_eq : forall x g C, remove_ec x ((x,g) :: C) = C.
Proof. intros. simpl. destruct (CoqEqDec.eq_dec x x) as [E|E]; [reflexivity | exfalso; apply E; reflexivity]. Qed.

Lemma remove_ec_head_neq : forall x y g C, y <> x -> remove_ec x ((y,g) :: C) = (y,g) :: remove_ec x C.
Proof. intros. simpl. destruct (CoqEqDec.eq_dec y x) as [E|E]; [exfalso; apply H; exact E | reflexivity]. Qed.

Lemma binds_remove_ec_imp : forall C x y g, y <> x -> binds y g (remove_ec x C) -> binds y g C.
Proof.
  intros C. induction C as [|(z,h) C' IH]; intros x y g Hne Hb; simpl in *.
  - inversion Hb.
  - destruct (CoqEqDec.eq_dec z x) as [E|E].
    + subst. apply binds_cons. exact Hb.
    + apply binds_cons_1 in Hb as [[? ?]|Hb].
      * subst. apply binds_cons_2; reflexivity.
      * apply binds_cons. apply (IH x y g Hne Hb).
Qed.

Lemma binds_remove_ec_neq : forall C x y g, y <> x -> binds y g C -> binds y g (remove_ec x C).
Proof.
  intros C. induction C as [|(z,h) C' IH]; intros x y g Hne Hb; simpl in *.
  - inversion Hb.
  - destruct (CoqEqDec.eq_dec z x) as [E|E].
    + subst. apply binds_cons_1 in Hb as [[? ?]|Hb].
      * subst. exfalso; apply Hne; reflexivity.
      * exact Hb.
    + apply binds_cons_1 in Hb as [[? ?]|Hb].
      * subst. apply binds_cons_2; reflexivity.
      * apply binds_cons. apply (IH x y g Hne Hb).
Qed.

Lemma notin_dom_remove_self : forall C x, uniq C -> x \notin dom (remove_ec x C).
Proof.
  intros C. induction C as [|(y,g) C' IH]; intros x Hu; simpl.
  - apply notin_empty_1.
  - destruct (CoqEqDec.eq_dec y x) as [E|E].
    + inversion Hu; subst. exact H3.
    + inversion Hu; subst. intro Hin. apply binds_In_inv in Hin as [h Hb].
      apply binds_cons_1 in Hb as [[? ?]|Hb].
      * exfalso; apply E; symmetry; exact H.
      * apply (IH x H1). eapply binds_In. exact Hb.
Qed.

Lemma not_binds_remove_self : forall C x h, x \notin dom C -> ~ binds x h (remove_ec x C).
Proof.
  intros C. induction C as [|(y,g) C' IH]; intros x h Hn Hb; simpl in *.
  - inversion Hb.
  - destruct (CoqEqDec.eq_dec y x) as [E|E].
    + subst. exfalso. apply Hn. apply AtomSetImpl.add_1. reflexivity.
    + apply binds_cons_1 in Hb as [[? ?]|Hb].
      * exfalso; apply E; symmetry; exact H.
      * apply (IH x h).
        -- intro Hin. apply Hn. apply AtomSetImpl.add_2. exact Hin.
        -- exact Hb.
Qed.

Lemma notin_dom_remove_ec : forall C x z, z \notin dom C -> z \notin dom (remove_ec x C).
Proof.
  intros C x z Hn. destruct (CoqEqDec.eq_dec z x) as [E|E].
  - subst. intro Hin. apply binds_In_inv in Hin as [g Hb].
    exact (@not_binds_remove_self C x g Hn Hb).
  - intro Hin. apply Hn. apply binds_In_inv in Hin as [g Hb].
    eapply binds_In. apply (@binds_remove_ec_imp C x z g); [intro E'; exact (E E') | exact Hb].
Qed.

Lemma uniq_remove_ec : forall C x, uniq C -> uniq (remove_ec x C).
Proof.
  intros C. induction C as [|(y,g) C' IH]; intros x Hu; simpl.
  - apply uniq_nil.
  - destruct (CoqEqDec.eq_dec y x) as [E|E].
    + subst. inversion Hu; subst. assumption.
    + inversion Hu; subst. apply uniq_cons; [apply IH; exact H1 | apply notin_dom_remove_ec; exact H3].
Qed.

Lemma lc_at_open_id : forall u k s, lc_at k u -> open_tm_wrt_tm_rec k s u = u.
Proof.
  induction u as
    [| |psi A IHA B IHB |psi A IHA b IHb |a IHa psi b IHb |sq |n |x |A1 IHA1 A2 IHA2 |a IHa |a IHa
    |psi a IHa b1 IHb1 b2 IHb2 |psi A IHA B IHB |a IHa psi b IHb |psi a IHa b IHb
    |psi A IHA B IHB |a IHa psi b IHb |psi a IHa |psi a IHa ];
    intros k s H; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct H as [HA HB]. rewrite (IHA k s HA), (IHB (S k) s HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHA k s HA), (IHb (S k) s HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHa k s HA), (IHb k s HB). reflexivity.
  - reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt]; [reflexivity | lia | lia].
  - reflexivity.
  - destruct H as [HA HB]. rewrite (IHA1 k s HA), (IHA2 k s HB). reflexivity.
  - rewrite (IHa k s H); reflexivity.
  - rewrite (IHa k s H); reflexivity.
  - destruct H as [Ha [Hb1 Hb2]]. rewrite (IHa k s Ha), (IHb1 k s Hb1), (IHb2 k s Hb2). reflexivity.
  - destruct H as [HA HB]. rewrite (IHA k s HA), (IHB (S k) s HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHa k s HA), (IHb k s HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHa k s HA), (IHb (S k) s HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHA k s HA), (IHB (S k) s HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHa k s HA), (IHb k s HB). reflexivity.
  - rewrite (IHa k s H); reflexivity.
  - rewrite (IHa k s H); reflexivity.
Qed.

Lemma lc_open_rec : forall u k s, lc_tm u -> open_tm_wrt_tm_rec k s u = u.
Proof.
  intros. apply lc_at_open_id.
  apply (lc_at_mono u 0 k (Nat.le_0_l k)). apply lc_tm_lc_at_0. assumption.
Qed.

Lemma lc_at_subst_tm_tm : forall u xv s k, lc_at k u -> lc_at 0 s -> lc_at k (subst_tm_tm s xv u).
Proof.
  induction u as
    [| |psi A IHA B IHB |psi A IHA b IHb |a IHa psi b IHb |sq |n |x |A1 IHA1 A2 IHA2 |a IHa |a IHa
    |psi a IHa b1 IHb1 b2 IHb2 |psi A IHA B IHB |a IHa psi b IHb |psi a IHa b IHb
    |psi A IHA B IHB |a IHa psi b IHb |psi a IHa |psi a IHa ];
    intros xv s k H Hs; simpl in *.
  - exact I.
  - exact I.
  - destruct H as [HA HB]. split; [exact (IHA xv s k HA Hs) | exact (IHB xv s (S k) HB Hs)].
  - destruct H as [HA HB]. split; [exact (IHA xv s k HA Hs) | exact (IHb xv s (S k) HB Hs)].
  - destruct H as [HA HB]. split; [exact (IHa xv s k HA Hs) | exact (IHb xv s k HB Hs)].
  - exact I.
  - exact H.
  - destruct (CoqEqDec.eq_dec x xv) as [E|E]; simpl.
    + apply (lc_at_mono s 0 k (Nat.le_0_l k)). exact Hs.
    + exact I.
  - destruct H as [HA HB]. split; [exact (IHA1 xv s k HA Hs) | exact (IHA2 xv s k HB Hs)].
  - exact (IHa xv s k H Hs).
  - exact (IHa xv s k H Hs).
  - destruct H as [Ha' [Hb1 Hb2]]. repeat split;
      [exact (IHa xv s k Ha' Hs) | exact (IHb1 xv s k Hb1 Hs) | exact (IHb2 xv s k Hb2 Hs)].
  - destruct H as [HA HB]. split; [exact (IHA xv s k HA Hs) | exact (IHB xv s (S k) HB Hs)].
  - destruct H as [HA HB]. split; [exact (IHa xv s k HA Hs) | exact (IHb xv s k HB Hs)].
  - destruct H as [HA HB]. split; [exact (IHa xv s k HA Hs) | exact (IHb xv s (S k) HB Hs)].
  - destruct H as [HA HB]. split; [exact (IHA xv s k HA Hs) | exact (IHB xv s (S k) HB Hs)].
  - destruct H as [HA HB]. split; [exact (IHa xv s k HA Hs) | exact (IHb xv s k HB Hs)].
  - exact (IHa xv s k H Hs).
  - exact (IHa xv s k H Hs).
Qed.

Lemma lc_subst_tm_tm : forall u x s, lc_tm u -> lc_tm s -> lc_tm (subst_tm_tm s x u).
Proof.
  intros. apply lc_at_0_lc_tm.
  apply (lc_at_subst_tm_tm u x s 0).
  - apply lc_tm_lc_at_0; assumption.
  - apply lc_tm_lc_at_0; assumption.
Qed.


(* ================= Stage 2b: permutation, weakening, opening/subst commutation ================= *)
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import List.

Definition keys (A:Type) (E:list (atom*A)) : list atom := List.map (@fst atom A) E.
Arguments keys [A] E.

Lemma binds_In_iff : forall A (x:atom) (a:A) (E:list (atom*A)),
  binds x a E <-> In (x,a) E.
Proof.
  intros A x a E. revert x a. induction E as [|(y,b) E IH]; intros x a; simpl.
  - rewrite binds_nil_iff. tauto.
  - rewrite binds_cons_iff. split; intro H.
    + destruct H as [[Heq Ha]|H].
      * left. subst. reflexivity.
      * right. apply (proj1 (IH x a)); exact H.
    + destruct H as [Hin|Hin].
      * left. injection Hin as Heq Ha. auto.
      * right. apply (proj2 (IH x a)); exact Hin.
Qed.

Lemma binds_perm : forall A (E F:list (atom*A)) x a,
  Permutation E F -> binds x a E -> binds x a F.
Proof.
  intros. apply (proj2 (@binds_In_iff A x a F)).
  apply (Permutation_in _ H). apply (proj1 (@binds_In_iff A x a E)). assumption.
Qed.

Lemma In_dom_map_fst : forall A (E:list (atom*A)) x, x \in dom E <-> In x (keys E).
Proof.
  intros A E x. revert x. induction E as [|(y,b) E IH]; intros x; unfold keys in *; simpl.
  - split.
    + intro H; apply AtomSetImpl.empty_1 in H; contradiction.
    + intro H; inversion H.
  - split; intro H.
    + destruct (CoqEqDec.eq_dec y x) as [E'|E'].
      * left. exact E'.
      * right. apply (proj1 (IH x)). apply (@AtomSetImpl.add_3 (dom E) y x).
        -- intro Hc; exact (E' Hc).
        -- exact H.
    + destruct H as [Hin|Hin].
      * subst. apply AtomSetImpl.add_1. reflexivity.
      * apply AtomSetImpl.add_2. apply (proj2 (IH x)). exact Hin.
Qed.

Lemma uniq_NoDup : forall A (E:list (atom*A)), uniq E -> NoDup (keys E).
Proof.
  intros A E H. induction H as [|x a E Hu IH Hnotin]; unfold keys in *; simpl.
  - constructor.
  - constructor; [|exact IH]. intro Hin.
    apply Hnotin. apply (proj2 (@In_dom_map_fst A E x)). exact Hin.
Qed.

Lemma NoDup_uniq : forall A (E:list (atom*A)), NoDup (keys E) -> uniq E.
Proof.
  intros A E. induction E as [|(y,b) E IH]; intros H; unfold keys in *; simpl in *.
  - apply uniq_nil.
  - inversion H as [|? ? Hnotin Hnd]; subst.
    apply uniq_push.
    + apply IH. exact Hnd.
    + intro Hin. apply Hnotin. apply (proj1 (@In_dom_map_fst A E y)). exact Hin.
Qed.

Lemma uniq_perm : forall A (E F:list (atom*A)), Permutation E F -> uniq E -> uniq F.
Proof.
  intros A E F H Hu. unfold keys in *.
  apply NoDup_uniq.
  apply (Permutation_NoDup (Permutation_map (@fst atom A) H)).
  apply uniq_NoDup. exact Hu.
Qed.

Lemma notin_dom_cons : forall A (y:atom) (g:A) (P:list (atom*A)) x,
  x <> y -> x \notin dom P -> x \notin dom ((y,g) :: P).
Proof.
  intros A y g P x Hne Hn Hin. apply binds_In_inv in Hin as [h Hb].
  apply binds_cons_1 in Hb as [[? ?]|Hb].
  - subst. apply Hne; reflexivity.
  - apply Hn. eapply binds_In. exact Hb.
Qed.

Lemma uniq_one : forall A (x:atom) (g:A), uniq ((x,g) :: nil).
Proof.
  intros. apply uniq_push.
  - apply uniq_nil.
  - apply notin_empty_1.
Qed.

Lemma uniq_app_one : forall A (P:list (atom*A)) x g, uniq P -> x \notin dom P -> uniq (P ++ ((x,g)::nil)).
Proof.
  intros. apply (proj2 (@uniq_app_iff A P ((x,g)::nil))). split.
  - exact H.
  - split.
    + apply uniq_one.
    + apply (proj2 (@disjoint_one_r A A x g P)). exact H0.
Qed.

Lemma notin_union_l : forall (s t:atoms) x, x \notin (s \u t) -> x \notin s.
Proof. intros s t x H Hin. apply H. apply AtomSetImpl.union_2. exact Hin. Qed.

Lemma notin_union_r : forall (s t:atoms) x, x \notin (s \u t) -> x \notin t.
Proof. intros s t x H Hin. apply H. apply AtomSetImpl.union_3. exact Hin. Qed.

Lemma neq_of_notin_singleton : forall x y, y \notin {{x}} -> y <> x.
Proof.
  intros x y H E. apply H. subst. apply AtomSetImpl.singleton_2. reflexivity.
Qed.

Lemma subst_open_comm : forall B k xv s z,
  lc_tm s -> z <> xv ->
  subst_tm_tm s xv (open_tm_wrt_tm_rec k (a_Var_f z) B)
  = open_tm_wrt_tm_rec k (a_Var_f z) (subst_tm_tm s xv B).
Proof.
  intros B. induction B as
    [| |psi A IHA B IHB |psi A IHA b IHb |a IHa psi b IHb |sq |n |x |A1 IHA1 A2 IHA2 |a IHa |a IHa
    |psi a IHa b1 IHb1 b2 IHb2 |psi A IHA B IHB |a IHa psi b IHb |psi a IHa b IHb
    |psi A IHA B IHB |a IHa psi b IHb |psi a IHa |psi a IHa ];
    intros k xv s z Hs Hne; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (IHA k xv s z Hs Hne), (IHB (S k) xv s z Hs Hne). reflexivity.
  - rewrite (IHA k xv s z Hs Hne), (IHb (S k) xv s z Hs Hne). reflexivity.
  - rewrite (IHa k xv s z Hs Hne), (IHb k xv s z Hs Hne). reflexivity.
  - reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl;
      destruct (CoqEqDec.eq_dec z xv) as [E|E]; try reflexivity;
      exfalso; apply Hne; exact E.
  - destruct (CoqEqDec.eq_dec x xv) as [E|E]; simpl.
    + subst. rewrite lc_open_rec; [reflexivity | exact Hs].
    + reflexivity.
  - rewrite (IHA1 k xv s z Hs Hne), (IHA2 k xv s z Hs Hne). reflexivity.
  - rewrite (IHa k xv s z Hs Hne). reflexivity.
  - rewrite (IHa k xv s z Hs Hne). reflexivity.
  - rewrite (IHa k xv s z Hs Hne), (IHb1 k xv s z Hs Hne), (IHb2 k xv s z Hs Hne). reflexivity.
  - rewrite (IHA k xv s z Hs Hne), (IHB (S k) xv s z Hs Hne). reflexivity.
  - rewrite (IHa k xv s z Hs Hne), (IHb k xv s z Hs Hne). reflexivity.
  - rewrite (IHa k xv s z Hs Hne), (IHb (S k) xv s z Hs Hne). reflexivity.
  - rewrite (IHA k xv s z Hs Hne), (IHB (S k) xv s z Hs Hne). reflexivity.
  - rewrite (IHa k xv s z Hs Hne), (IHb k xv s z Hs Hne). reflexivity.
  - rewrite (IHa k xv s z Hs Hne). reflexivity.
  - rewrite (IHa k xv s z Hs Hne). reflexivity.
Qed.

(* ---------- grade judgments are invariant under context permutation ---------- *)
Ltac solve_perm_ih :=
  match goal with
  | IH : forall Q, Permutation ?P Q -> Grade Q ?psi ?a |- Grade ?Q ?psi ?a =>
      apply (IH Q); assumption
  | IH : forall Q, Permutation ?P Q -> CGrade Q ?psi ?phi ?a |- CGrade ?Q ?psi ?phi ?a =>
      apply (IH Q); assumption
  end.

Lemma Grade_perm : forall (P:econtext) (psi:grade) (a:tm), Grade P psi a ->
  forall Q, Permutation P Q -> Grade Q psi a.
Proof.
  intros P psi a H. induction H using Grade_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a:tm) (_:CGrade P psi phi0 a) =>
                 forall Q, Permutation P Q -> CGrade Q psi phi0 a).
  all: intros Q Hperm.
  - eapply G_Type. eapply uniq_perm; eassumption.
  - eapply G_Var. exact (@uniq_perm grade P Q Hperm u). exact i. exact (@binds_perm grade P Q x psi0 Hperm b).
  - eapply (@G_Pi L Q psi psi0 A B). solve_perm_ih.
    intros y Hy. apply (H0 y Hy). apply perm_skip. eassumption.
  - eapply (@G_Abs L Q psi psi0 A b).
    + intros y Hy. apply (H y Hy). apply perm_skip. eassumption.
    + solve_perm_ih.
  - eapply G_App. solve_perm_ih. solve_perm_ih.
  - eapply (@G_WSigma L Q psi psi0 A B). solve_perm_ih.
    intros y Hy. apply (H0 y Hy). apply perm_skip. eassumption.
  - eapply G_WPair. solve_perm_ih. solve_perm_ih.
  - eapply (@G_LetPair L Q psi psi0 a c). solve_perm_ih.
    intros y Hy. apply (H0 y Hy). apply perm_skip. eassumption.
  - eapply (@G_SSigma L Q psi psi0 A B). solve_perm_ih.
    intros y Hy. apply (H0 y Hy). apply perm_skip. eassumption.
  - eapply G_SPair. solve_perm_ih. solve_perm_ih.
  - eapply G_Proj1. solve_perm_ih. assumption.
  - eapply G_Proj2. solve_perm_ih.
  - eapply G_Sum. solve_perm_ih. solve_perm_ih.
  - eapply G_Inj1. solve_perm_ih.
  - eapply G_Inj2. solve_perm_ih.
  - eapply G_Case. solve_perm_ih. solve_perm_ih. solve_perm_ih. assumption.
  - eapply G_TyUnit. eapply uniq_perm; eassumption.
  - eapply G_TmUnit. eapply uniq_perm; eassumption.
  - eapply CG_Leq. assumption. solve_perm_ih.
  - eapply CG_Nleq. assumption. assumption. eapply uniq_perm; eassumption.
Qed.

(* ---------- context weakening at the end ---------- *)
Lemma fresh_body_facts : forall (A:Type) (y:atom) (L:atoms) (P:list (atom*A)) x,
  y \notin (L \u (dom P \u {{x}})) ->
  y \notin L /\ y \notin dom P /\ y <> x.
Proof.
  intros A y L P x Hy. repeat split.
  - intro Hc. apply Hy. apply AtomSetImpl.union_2. exact Hc.
  - intro Hc. apply Hy. apply AtomSetImpl.union_3. apply AtomSetImpl.union_2. exact Hc.
  - intro E. subst. apply Hy. apply AtomSetImpl.union_3. apply AtomSetImpl.union_3.
    apply AtomSetImpl.singleton_2. reflexivity.
Qed.

Ltac solve_weak xw gw :=
  first [ match goal with
          | IH : forall y h, uniq ?P -> y \notin dom ?P -> Grade (?P ++ ((y,h)::nil)) ?psi ?a |- Grade ?Q ?psi ?a =>
              apply (IH xw gw); assumption
          end
        | match goal with
          | IH : forall y h, uniq ?P -> y \notin dom ?P -> CGrade (?P ++ ((y,h)::nil)) ?psi ?phi ?a |- CGrade ?Q ?psi ?phi ?a =>
              apply (IH xw gw); assumption
          end ].

Lemma Grade_weaken_end : forall (P:econtext) (psi:grade) (a:tm), Grade P psi a ->
  forall xw gw, uniq P -> xw \notin dom P -> Grade (P ++ ((xw,gw)::nil)) psi a.
Proof.
  intros P psi a H. induction H using Grade_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a:tm) (_:CGrade P psi phi0 a) =>
                 forall xw gw, uniq P -> xw \notin dom P -> CGrade (P ++ ((xw,gw)::nil)) psi phi0 a).
  all: intros xw gw Hu Hn.
  - eapply G_Type. exact (@uniq_app_one grade P xw gw Hu Hn).
  - eapply (@G_Var (P++((xw,gw)::nil)) psi x psi0); [exact (@uniq_app_one grade P xw gw Hu Hn) | assumption | eapply binds_app_2; eassumption].
  - eapply (@G_Pi (L \u (dom P \u {{xw}}))). solve_weak xw gw.
    intros y Hy. destruct (@fresh_body_facts grade y L P xw Hy) as [HL [HdomP Hne]].
    rewrite app_assoc. apply (H0 y HL xw gw).
    + apply uniq_push; assumption.
    + apply notin_dom_cons with (A:=grade) (y:=y) (g:=psi); [symmetry; exact Hne | exact Hn].
  - eapply (@G_Abs (L \u (dom P \u {{xw}}))). 
    + intros y Hy. destruct (@fresh_body_facts grade y L P xw Hy) as [HL [HdomP Hne]].
      rewrite app_assoc. apply (H y HL xw gw).
      * apply uniq_push; assumption.
      * apply notin_dom_cons with (A:=grade) (y:=y) (g:=psi0); [symmetry; exact Hne | exact Hn].
    + solve_weak xw gw.
  - eapply G_App. solve_weak xw gw. solve_weak xw gw.
  - eapply (@G_WSigma (L \u (dom P \u {{xw}}))). solve_weak xw gw.
    intros y Hy. destruct (@fresh_body_facts grade y L P xw Hy) as [HL [HdomP Hne]].
    rewrite app_assoc. apply (H0 y HL xw gw).
    + apply uniq_push; assumption.
    + apply notin_dom_cons with (A:=grade) (y:=y) (g:=psi); [symmetry; exact Hne | exact Hn].
  - eapply G_WPair. solve_weak xw gw. solve_weak xw gw.
  - eapply (@G_LetPair (L \u (dom P \u {{xw}}))). solve_weak xw gw.
    intros y Hy. destruct (@fresh_body_facts grade y L P xw Hy) as [HL [HdomP Hne]].
    rewrite app_assoc. apply (H0 y HL xw gw).
    + apply uniq_push; assumption.
    + apply notin_dom_cons with (A:=grade) (y:=y) (g:=psi0); [symmetry; exact Hne | exact Hn].
  - eapply (@G_SSigma (L \u (dom P \u {{xw}}))). solve_weak xw gw.
    intros y Hy. destruct (@fresh_body_facts grade y L P xw Hy) as [HL [HdomP Hne]].
    rewrite app_assoc. apply (H0 y HL xw gw).
    + apply uniq_push; assumption.
    + apply notin_dom_cons with (A:=grade) (y:=y) (g:=psi); [symmetry; exact Hne | exact Hn].
  - eapply G_SPair. solve_weak xw gw. solve_weak xw gw.
  - eapply G_Proj1. solve_weak xw gw. assumption.
  - eapply G_Proj2. solve_weak xw gw.
  - eapply G_Sum. solve_weak xw gw. solve_weak xw gw.
  - eapply G_Inj1. solve_weak xw gw.
  - eapply G_Inj2. solve_weak xw gw.
  - eapply G_Case. solve_weak xw gw. solve_weak xw gw. solve_weak xw gw. assumption.
  - eapply G_TyUnit. exact (@uniq_app_one grade P xw gw Hu Hn).
  - eapply G_TmUnit. exact (@uniq_app_one grade P xw gw Hu Hn).
  - eapply CG_Leq. assumption. solve_weak xw gw.
  - eapply CG_Nleq. assumption. assumption. exact (@uniq_app_one grade P xw gw Hu Hn).
Qed.

Lemma Grade_weaken_cons : forall (P:econtext) (psi:grade) (a:tm), Grade P psi a ->
  forall x g, uniq P -> x \notin dom P -> Grade ((x,g)::P) psi a.
Proof.
  intros. apply Grade_perm with (P := P ++ ((x,g)::nil)).
  - apply Grade_weaken_end; assumption.
  - apply Permutation_sym. apply Permutation_cons_append.
Qed.


(* ================= Stage 3: substitution into Grade / CGrade ================= *)
Lemma lc_from_side : forall (Q:econtext) (psi psib:grade) (w:tm),
  (psib <= psi -> Grade Q psi w) ->
  (~ (psib <= psi) -> lc_tm w) -> lc_tm w.
Proof.
  intros Q psi psib w Hg Hl.
  destruct (q_leb psib psi).
  - apply (Grade_lc Q psi w). apply Hg. reflexivity.
  - apply Hl. intro Hle. discriminate Hle.
Qed.

Lemma remove_ec_head_neq_not : forall x y g (C:econtext),
  y <> x -> remove_ec x (y ~ g ++ C) = (y,g) :: remove_ec x C.
Proof.
  intros. change (remove_ec x ((y,g)::C) = (y,g)::remove_ec x C).
  apply remove_ec_head_neq. assumption.
Qed.

Lemma subst_open_comm0 : forall B xv s z,
  lc_tm s -> z <> xv ->
  subst_tm_tm s xv (open_tm_wrt_tm B (a_Var_f z))
  = open_tm_wrt_tm (subst_tm_tm s xv B) (a_Var_f z).
Proof. intros. apply subst_open_comm; assumption. Qed.

Ltac solve_subst_ih xv w psib Hu Hb Hgrade Hlc :=
  first [ match goal with
          | IH : forall (a:atom) (s:tm) (g:grade), _ |- Grade (remove_ec ?X ?P) ?ps ?u =>
              apply (@IH X w psib Hu Hb Hgrade Hlc)
          end
        | match goal with
          | IH : forall (a:atom) (s:tm) (g:grade), _ |- CGrade (remove_ec ?X ?P) ?ps ?ph ?u =>
              apply (@IH X w psib Hu Hb Hgrade Hlc)
          end ].

Lemma Grade_subst : forall (C:econtext) (psi:grade) (u:tm), Grade C psi u ->
  forall xv w psib,
    uniq C -> binds xv psib C ->
    (psib <= psi -> Grade (remove_ec xv C) psi w) ->
    (~ (psib <= psi) -> lc_tm w) ->
    Grade (remove_ec xv C) psi (subst_tm_tm w xv u).
Proof.
  intros C psi u H. induction H using Grade_mind
    with (P0 := fun (C:econtext) (psi phi0:grade) (u:tm) (_:CGrade C psi phi0 u) =>
                 forall xv w psib,
                   uniq C -> binds xv psib C ->
                   (psib <= psi -> Grade (remove_ec xv C) psi w) ->
                   (~ (psib <= psi) -> lc_tm w) ->
                   CGrade (remove_ec xv C) psi phi0 (subst_tm_tm w xv u)).
  all: intros xv w psib Hu Hb Hgrade Hlc.
  - (* G_Type *) eapply G_Type. apply uniq_remove_ec. exact Hu.
  - (* G_Var *) simpl. destruct (CoqEqDec.eq_dec x xv) as [E|E].
    + subst. assert (Heq : psib = psi0) by (eapply binds_unique; [exact Hb | exact b | exact Hu]).
      apply Hgrade. rewrite Heq. exact i.
    + eapply (@G_Var (remove_ec xv P) psi x psi0).
      * apply uniq_remove_ec. exact Hu.
      * assumption.
      * apply (@binds_remove_ec_neq P xv x psi0); [exact E | exact b].
  - (* G_Pi *)
    eapply (@G_Pi (L \u (dom P \u {{xv}})) (remove_ec xv P) psi psi0
                   (subst_tm_tm w xv A) (subst_tm_tm w xv B)).
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
    + intros y Hy. destruct (@fresh_body_facts grade y L P xv Hy) as [HL [HdomC Hne]].
      assert (Huniq : uniq ((y,psi)::P)).
      { apply uniq_push; assumption. }
      assert (Hb' : binds xv psib ((y,psi)::P)).
      { apply binds_cons. exact Hb. }
      assert (Hgrade' : psib <= psi -> Grade ((y,psi)::remove_ec xv P) psi w).
      { intro Hle.
        exact (@Grade_weaken_cons (remove_ec xv P) psi w (Hgrade Hle) y psi
                 (@uniq_remove_ec P xv Hu) (@notin_dom_remove_ec P xv y HdomC)). }
      rewrite <- (@remove_ec_head_neq xv y psi P Hne) in Hgrade'.
      pose proof (H0 y HL xv w psib Huniq Hb' Hgrade' Hlc) as Hres.
      rewrite (@remove_ec_head_neq_not xv y psi P Hne) in Hres.
      assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
      rewrite (@subst_open_comm0 B xv w y Hlcw Hne) in Hres.
      exact Hres.
  - (* G_Abs *)
    eapply (@G_Abs (L \u (dom P \u {{xv}})) (remove_ec xv P) psi psi0
                   (subst_tm_tm w xv A) (subst_tm_tm w xv b)).
    + intros y Hy. destruct (@fresh_body_facts grade y L P xv Hy) as [HL [HdomC Hne]].
      assert (Huniq : uniq ((y,psi0)::P)).
      { apply uniq_push; assumption. }
      assert (Hb' : binds xv psib ((y,psi0)::P)).
      { apply binds_cons. exact Hb. }
      assert (Hgrade' : psib <= psi -> Grade ((y,psi0)::remove_ec xv P) psi w).
      { intro Hle.
        exact (@Grade_weaken_cons (remove_ec xv P) psi w (Hgrade Hle) y psi0
                 (@uniq_remove_ec P xv Hu) (@notin_dom_remove_ec P xv y HdomC)). }
      rewrite <- (@remove_ec_head_neq xv y psi0 P Hne) in Hgrade'.
      pose proof (H y HL xv w psib Huniq Hb' Hgrade' Hlc) as Hres.
      rewrite (@remove_ec_head_neq_not xv y psi0 P Hne) in Hres.
      assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
      rewrite (@subst_open_comm0 b xv w y Hlcw Hne) in Hres.
      exact Hres.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
  - (* G_App *)
    simpl. eapply G_App.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
  - (* G_WSigma *)
    eapply (@G_WSigma (L \u (dom P \u {{xv}})) (remove_ec xv P) psi psi0
                   (subst_tm_tm w xv A) (subst_tm_tm w xv B)).
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
    + intros y Hy. destruct (@fresh_body_facts grade y L P xv Hy) as [HL [HdomC Hne]].
      assert (Huniq : uniq ((y,psi)::P)).
      { apply uniq_push; assumption. }
      assert (Hb' : binds xv psib ((y,psi)::P)).
      { apply binds_cons. exact Hb. }
      assert (Hgrade' : psib <= psi -> Grade ((y,psi)::remove_ec xv P) psi w).
      { intro Hle.
        exact (@Grade_weaken_cons (remove_ec xv P) psi w (Hgrade Hle) y psi
                 (@uniq_remove_ec P xv Hu) (@notin_dom_remove_ec P xv y HdomC)). }
      rewrite <- (@remove_ec_head_neq xv y psi P Hne) in Hgrade'.
      pose proof (H0 y HL xv w psib Huniq Hb' Hgrade' Hlc) as Hres.
      rewrite (@remove_ec_head_neq_not xv y psi P Hne) in Hres.
      assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
      rewrite (@subst_open_comm0 B xv w y Hlcw Hne) in Hres.
      exact Hres.
  - (* G_WPair *)
    simpl. eapply G_WPair.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
  - (* G_LetPair *)
    simpl. eapply (@G_LetPair (L \u (dom P \u {{xv}})) (remove_ec xv P) psi psi0
                   (subst_tm_tm w xv a) (subst_tm_tm w xv c)).
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
    + intros y Hy. destruct (@fresh_body_facts grade y L P xv Hy) as [HL [HdomC Hne]].
      assert (Huniq : uniq ((y,psi0)::P)).
      { apply uniq_push; assumption. }
      assert (Hb' : binds xv psib ((y,psi0)::P)).
      { apply binds_cons. exact Hb. }
      assert (Hgrade' : psib <= psi -> Grade ((y,psi0)::remove_ec xv P) psi w).
      { intro Hle.
        exact (@Grade_weaken_cons (remove_ec xv P) psi w (Hgrade Hle) y psi0
                 (@uniq_remove_ec P xv Hu) (@notin_dom_remove_ec P xv y HdomC)). }
      rewrite <- (@remove_ec_head_neq xv y psi0 P Hne) in Hgrade'.
      pose proof (H0 y HL xv w psib Huniq Hb' Hgrade' Hlc) as Hres.
      rewrite (@remove_ec_head_neq_not xv y psi0 P Hne) in Hres.
      assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
      rewrite (@subst_open_comm0 c xv w y Hlcw Hne) in Hres.
      exact Hres.
  - (* G_SSigma *)
    eapply (@G_SSigma (L \u (dom P \u {{xv}})) (remove_ec xv P) psi psi0
                   (subst_tm_tm w xv A) (subst_tm_tm w xv B)).
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
    + intros y Hy. destruct (@fresh_body_facts grade y L P xv Hy) as [HL [HdomC Hne]].
      assert (Huniq : uniq ((y,psi)::P)).
      { apply uniq_push; assumption. }
      assert (Hb' : binds xv psib ((y,psi)::P)).
      { apply binds_cons. exact Hb. }
      assert (Hgrade' : psib <= psi -> Grade ((y,psi)::remove_ec xv P) psi w).
      { intro Hle.
        exact (@Grade_weaken_cons (remove_ec xv P) psi w (Hgrade Hle) y psi
                 (@uniq_remove_ec P xv Hu) (@notin_dom_remove_ec P xv y HdomC)). }
      rewrite <- (@remove_ec_head_neq xv y psi P Hne) in Hgrade'.
      pose proof (H0 y HL xv w psib Huniq Hb' Hgrade' Hlc) as Hres.
      rewrite (@remove_ec_head_neq_not xv y psi P Hne) in Hres.
      assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
      rewrite (@subst_open_comm0 B xv w y Hlcw Hne) in Hres.
      exact Hres.
  - (* G_SPair *)
    simpl. eapply G_SPair.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
  - (* G_Proj1 *) simpl. eapply G_Proj1.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
    + assumption.
  - (* G_Proj2 *) simpl. eapply G_Proj2.
    solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
  - (* G_Sum *) simpl. eapply G_Sum.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
  - (* G_Inj1 *) simpl. eapply G_Inj1. solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
  - (* G_Inj2 *) simpl. eapply G_Inj2. solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
  - (* G_Case *) simpl. eapply G_Case.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
    + assumption.
  - (* G_TyUnit *) eapply G_TyUnit. apply uniq_remove_ec. exact Hu.
  - (* G_TmUnit *) eapply G_TmUnit. apply uniq_remove_ec. exact Hu.
  - (* CG_Leq *) simpl. eapply CG_Leq.
    + assumption.
    + solve_subst_ih xv w psib Hu Hb Hgrade Hlc.
  - (* CG_Nleq *) simpl. eapply CG_Nleq.
    + exact (@lc_subst_tm_tm a xv w l (@lc_from_side (remove_ec xv P) phi psib w Hgrade Hlc)).
    + assumption.
    + apply uniq_remove_ec. exact Hu.
Qed.

Lemma Grade_Pi_body : forall (P:econtext) (psi psi0:grade) (A B:tm),
  Grade P psi (a_Pi psi0 A B) ->
  exists L, forall x, x \notin L -> Grade ((x~psi)++P) psi (open_tm_wrt_tm B (a_Var_f x)).
Proof. intros. inversion H. subst. eexists. eassumption. Qed.

Lemma Grade_WSigma_body : forall (P:econtext) (psi psi0:grade) (A B:tm),
  Grade P psi (a_WSigma psi0 A B) ->
  exists L, forall x, x \notin L -> Grade ((x~psi)++P) psi (open_tm_wrt_tm B (a_Var_f x)).
Proof. intros. inversion H. subst. eexists. eassumption. Qed.

Lemma Grade_SSigma_body : forall (P:econtext) (psi psi0:grade) (A B:tm),
  Grade P psi (a_SSigma psi0 A B) ->
  exists L, forall x, x \notin L -> Grade ((x~psi)++P) psi (open_tm_wrt_tm B (a_Var_f x)).
Proof. intros. inversion H. subst. eexists. eassumption. Qed.

Lemma Grade_body_subst : forall (P:econtext) (psi psi0:grade) (b:tm) (x:atom) (a:tm),
  uniq P -> x \notin dom P ->
  Grade ((x,psi0)::P) psi (open_tm_wrt_tm b (a_Var_f x)) ->
  (psi0 <= psi -> Grade P psi a) ->
  (~ (psi0 <= psi) -> lc_tm a) ->
  x \notin fv_tm_tm b ->
  Grade P psi (open_tm_wrt_tm b a).
Proof.
  intros P psi psi0 b x a Hu Hxdom Hbody Hgrade Hlc Hfv.
  pose proof (@Grade_subst ((x,psi0)::P) psi (open_tm_wrt_tm b (a_Var_f x)) Hbody
                x a psi0) as Hs.
  assert (Hgrade' : psi0 <= psi -> Grade (remove_ec x ((x,psi0)::P)) psi a).
  { intro Hle. rewrite remove_ec_head_eq. apply Hgrade. exact Hle. }
  specialize (Hs (@uniq_cons grade x psi0 P Hu Hxdom) (@binds_cons_2 grade x x psi0 psi0 P (@Logic.eq_refl atom x) (@Logic.eq_refl grade psi0)) Hgrade' Hlc).
  rewrite remove_ec_head_eq in Hs.
  rewrite (@subst_open_tm_wrt_tm b a x Hfv) in Hs.
  exact Hs.
Qed.


Lemma grade_le_refl : forall g:grade, g <= g.
Proof. intro g. apply (leq_join g g). apply join_idem. Qed.

Lemma fresh3_facts : forall (L:atoms) (P:econtext) (B:tm) x,
  x \notin (L \u (dom P \u fv_tm_tm B)) ->
  x \notin L /\ x \notin dom P /\ x \notin fv_tm_tm B.
Proof.
  intros L P B x Hx. repeat split.
  - intro Hc. apply Hx. apply AtomSetImpl.union_2. exact Hc.
  - intro Hc. apply Hx. apply AtomSetImpl.union_3. apply AtomSetImpl.union_2. exact Hc.
  - intro Hc. apply Hx. apply AtomSetImpl.union_3. apply AtomSetImpl.union_3. exact Hc.
Qed.

(* ================= Stage 4: DefEq terms are Grade ================= *)
Lemma uniq_cons_inv : forall (A:Type) (x:atom) (a:A) (C:list (atom*A)),
  uniq ((x,a)::C) -> uniq C.
Proof. intros A x a C H. inversion H. assumption. Qed.

Lemma DefEq_Grade : forall (P:econtext) (psi:grade) (a b:tm),
  DefEq P psi a b -> Grade P psi a /\ Grade P psi b.
Proof.
  intros P psi a b H. induction H using DefEq_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a b:tm) (_:CDefEq P psi phi0 a b) =>
                 CGrade P psi phi0 a /\ CGrade P psi phi0 b).
  - (* Refl *) split; assumption.
  - (* Trans *) destruct IHDefEq1 as [Ha _]. destruct IHDefEq2 as [_ Hc]. split; assumption.
  - (* Sym *) destruct IHDefEq as [Ha Hb]. split; assumption.
  - (* Beta *) split; assumption.
  - (* Pi *)
    split.
    + apply (@G_Pi L P psi psi0 A1 B1).
      * exact (proj1 IHDefEq).
      * intros x Hx. exact (proj1 (H0 x Hx)).
    + apply (@G_Pi L P psi psi0 A2 B2).
      * exact (proj2 IHDefEq).
      * intros x Hx. exact (proj2 (H0 x Hx)).
  - (* Abs *)
    split.
    + apply (@G_Abs L P psi psi0 A1 b1).
      * intros x Hx. exact (proj1 (H x Hx)).
      * exact (proj1 IHDefEq).
    + apply (@G_Abs L P psi psi0 A2 b2).
      * intros x Hx. exact (proj2 (H x Hx)).
      * exact (proj2 IHDefEq).
  - (* App *)
    split.
    + apply (@G_App P psi b1 psi0 a1).
      * exact (proj1 IHDefEq).
      * exact (proj1 IHDefEq0).
    + apply (@G_App P psi b2 psi0 a2).
      * exact (proj2 IHDefEq).
      * exact (proj2 IHDefEq0).
  - (* PiFst *)
    destruct IHDefEq as [Hp1 Hp2]. split.
    + exact (@Grade_Pi_inv P psi psi0 A1 B1 Hp1).
    + exact (@Grade_Pi_inv P psi psi0 A2 B2 Hp2).
  - (* PiSnd *)
    destruct IHDefEq1 as [Hp1 Hp2]. destruct IHDefEq2 as [Ha1 Ha2].
    destruct (@Grade_Pi_body P psi psi0 A1 B1 Hp1) as [L1 HB1].
    destruct (@Grade_Pi_body P psi psi0 A2 B2 Hp2) as [L2 HB2].
    split.
    + destruct (atom_fresh (L1 \u (dom P \u fv_tm_tm B1))) as [x Hx].
      destruct (@fresh3_facts L1 P B1 x Hx) as [HL [Hdom Hfv]].
      exact (@Grade_body_subst P psi psi B1 x a1
               (@Grade_uniq P psi (a_Pi psi0 A1 B1) Hp1) Hdom (HB1 x HL)
               (fun _ => Ha1) (fun Hn => match Hn (grade_le_refl psi) with end) Hfv).
    + destruct (atom_fresh (L2 \u (dom P \u fv_tm_tm B2))) as [x Hx].
      destruct (@fresh3_facts L2 P B2 x Hx) as [HL [Hdom Hfv]].
      exact (@Grade_body_subst P psi psi B2 x a2
               (@Grade_uniq P psi (a_Pi psi0 A2 B2) Hp2) Hdom (HB2 x HL)
               (fun _ => Ha2) (fun Hn => match Hn (grade_le_refl psi) with end) Hfv).
  - (* WSigma *)
    split.
    + apply (@G_WSigma L P psi psi0 A1 B1).
      * exact (proj1 IHDefEq).
      * intros x Hx. exact (proj1 (H0 x Hx)).
    + apply (@G_WSigma L P psi psi0 A2 B2).
      * exact (proj2 IHDefEq).
      * intros x Hx. exact (proj2 (H0 x Hx)).
  - (* WSigmaFst *)
    destruct IHDefEq as [Hp1 Hp2]. split.
    + exact (@Grade_WSigma_inv P psi psi0 A1 B1 Hp1).
    + exact (@Grade_WSigma_inv P psi psi0 A2 B2 Hp2).
  - (* WSigmaSnd *)
    destruct IHDefEq as [Hp1 Hp2].
    destruct (@Grade_WSigma_body P psi psi0 A1 B1 Hp1) as [L1 HB1].
    destruct (@Grade_WSigma_body P psi psi0 A2 B2 Hp2) as [L2 HB2].
    split.
    + destruct (atom_fresh (L1 \u (dom P \u fv_tm_tm B1))) as [x Hx].
      destruct (@fresh3_facts L1 P B1 x Hx) as [HL [Hdom Hfv]].
      exact (@Grade_body_subst P psi psi B1 x a
               (@Grade_uniq P psi (a_WSigma psi0 A1 B1) Hp1) Hdom (HB1 x HL)
               (fun _ => g) (fun Hn => match Hn (grade_le_refl psi) with end) Hfv).
    + destruct (atom_fresh (L2 \u (dom P \u fv_tm_tm B2))) as [x Hx].
      destruct (@fresh3_facts L2 P B2 x Hx) as [HL [Hdom Hfv]].
      exact (@Grade_body_subst P psi psi B2 x a
               (@Grade_uniq P psi (a_WSigma psi0 A2 B2) Hp2) Hdom (HB2 x HL)
               (fun _ => g) (fun Hn => match Hn (grade_le_refl psi) with end) Hfv).
  - (* WPair *)
    split.
    + apply (@G_WPair P psi a1 psi0 b1).
      * exact (proj1 IHDefEq).
      * exact (proj1 IHDefEq0).
    + apply (@G_WPair P psi a2 psi0 b2).
      * exact (proj2 IHDefEq).
      * exact (proj2 IHDefEq0).
  - (* LetPair *)
    split.
    + apply (@G_LetPair L P psi psi0 a1 b1).
      * exact (proj1 IHDefEq).
      * intros x Hx. exact (proj1 (H0 x Hx)).
    + apply (@G_LetPair L P psi psi0 a2 b2).
      * exact (proj2 IHDefEq).
      * intros x Hx. exact (proj2 (H0 x Hx)).
  - (* SSigma *)
    split.
    + apply (@G_SSigma L P psi psi0 A1 B1).
      * exact (proj1 IHDefEq).
      * intros x Hx. exact (proj1 (H0 x Hx)).
    + apply (@G_SSigma L P psi psi0 A2 B2).
      * exact (proj2 IHDefEq).
      * intros x Hx. exact (proj2 (H0 x Hx)).
  - (* SSigmaFst *)
    destruct IHDefEq as [Hp1 Hp2]. split.
    + exact (@Grade_SSigma_inv P psi psi0 A1 B1 Hp1).
    + exact (@Grade_SSigma_inv P psi psi0 A2 B2 Hp2).
  - (* SSigmaSnd *)
    destruct IHDefEq1 as [Hp1 Hp2]. destruct IHDefEq2 as [Ha1 Ha2].
    destruct (@Grade_SSigma_body P psi psi0 A1 B1 Hp1) as [L1 HB1].
    destruct (@Grade_SSigma_body P psi psi0 A2 B2 Hp2) as [L2 HB2].
    split.
    + destruct (atom_fresh (L1 \u (dom P \u fv_tm_tm B1))) as [x Hx].
      destruct (@fresh3_facts L1 P B1 x Hx) as [HL [Hdom Hfv]].
      exact (@Grade_body_subst P psi psi B1 x a1
               (@Grade_uniq P psi (a_SSigma psi0 A1 B1) Hp1) Hdom (HB1 x HL)
               (fun _ => Ha1) (fun Hn => match Hn (grade_le_refl psi) with end) Hfv).
    + destruct (atom_fresh (L2 \u (dom P \u fv_tm_tm B2))) as [x Hx].
      destruct (@fresh3_facts L2 P B2 x Hx) as [HL [Hdom Hfv]].
      exact (@Grade_body_subst P psi psi B2 x a2
               (@Grade_uniq P psi (a_SSigma psi0 A2 B2) Hp2) Hdom (HB2 x HL)
               (fun _ => Ha2) (fun Hn => match Hn (grade_le_refl psi) with end) Hfv).
  - (* SPair *)
    split.
    + apply (@G_SPair P psi a1 psi0 b1).
      * exact (proj1 IHDefEq).
      * exact (proj1 IHDefEq0).
    + apply (@G_SPair P psi a2 psi0 b2).
      * exact (proj2 IHDefEq).
      * exact (proj2 IHDefEq0).
  - (* Proj1 *)
    split.
    + apply (@G_Proj1 P psi psi0 a1). exact (proj1 IHDefEq). assumption.
    + apply (@G_Proj1 P psi psi0 a2). exact (proj2 IHDefEq). assumption.
  - (* Proj2 *)
    split.
    + apply (@G_Proj2 P psi psi0 a1). exact (proj1 IHDefEq).
    + apply (@G_Proj2 P psi psi0 a2). exact (proj2 IHDefEq).
  - (* Sum *)
    split.
    + apply (@G_Sum P psi A1 A2). exact (proj1 IHDefEq1). exact (proj1 IHDefEq2).
    + apply (@G_Sum P psi A1' A2'). exact (proj2 IHDefEq1). exact (proj2 IHDefEq2).
  - (* SumFst *)
    destruct IHDefEq as [Hp1 Hp2].
    destruct (@Grade_Sum_inv P psi A1 A2 Hp1) as [HA1 _].
    destruct (@Grade_Sum_inv P psi A1' A2' Hp2) as [HA1' _]. split; assumption.
  - (* SumSnd *)
    destruct IHDefEq as [Hp1 Hp2].
    destruct (@Grade_Sum_inv P psi A1 A2 Hp1) as [_ HA2].
    destruct (@Grade_Sum_inv P psi A1' A2' Hp2) as [_ HA2']. split; assumption.
  - (* Inj1 *)
    split.
    + eapply G_Inj1. exact (proj1 IHDefEq).
    + eapply G_Inj1. exact (proj2 IHDefEq).
  - (* Inj2 *)
    split.
    + eapply G_Inj2. exact (proj1 IHDefEq).
    + eapply G_Inj2. exact (proj2 IHDefEq).
  - (* Case *)
    split.
    + apply (@G_Case P psi psi0 a b1 b2).
      * exact (proj1 IHDefEq1). * exact (proj1 IHDefEq2). * exact (proj1 IHDefEq3). * assumption.
    + apply (@G_Case P psi psi0 a' b1' b2').
      * exact (proj2 IHDefEq1). * exact (proj2 IHDefEq2). * exact (proj2 IHDefEq3). * assumption.
  - (* TyUnit *)
    split; apply (@G_TyUnit P psi); assumption.
  - (* TmUnit *)
    split; apply (@G_TmUnit P psi); assumption.
  - (* SubstIrrel *)
    split.
    + destruct (atom_fresh (L \u (dom P \u fv_tm_tm b1))) as [x Hx].
      destruct (@fresh3_facts L P b1 x Hx) as [HL [Hdom Hfv]].
      exact (@Grade_body_subst P phi psi b1 x a1
               (@uniq_cons_inv grade x psi P (@Grade_uniq ((x,psi)::P) phi (open_tm_wrt_tm b1 (a_Var_f x)) (proj1 (H x HL)))) Hdom (proj1 (H x HL))
               (fun Hle => match n Hle with end) (fun _ => l) Hfv).
    + destruct (atom_fresh (L \u (dom P \u fv_tm_tm b2))) as [x Hx].
      destruct (@fresh3_facts L P b2 x Hx) as [HL [Hdom Hfv]].
      exact (@Grade_body_subst P phi psi b2 x a2
               (@uniq_cons_inv grade x psi P (@Grade_uniq ((x,psi)::P) phi (open_tm_wrt_tm b2 (a_Var_f x)) (proj2 (H x HL)))) Hdom (proj2 (H x HL))
               (fun Hle => match n Hle with end) (fun _ => l0) Hfv).
  - (* CDefEq_Leq *)
    destruct IHDefEq as [Ha Hb]. split.
    + apply (@CG_Leq P phi phi0); assumption.
    + apply (@CG_Leq P phi phi0); assumption.
  - (* CDefEq_Nleq *)
    split; apply (@CG_Nleq P phi phi0); assumption.
Qed.


(* ================= Stage 5: parallel reduction preserves grades ================= *)
Scheme Par_mind := Induction for Par Sort Prop
  with CPar_mind := Induction for CPar Sort Prop.

Lemma CGrade_leq_Grade : forall (P:econtext) (psi phi0:grade) (a:tm),
  CGrade P psi phi0 a -> phi0 <= psi -> Grade P psi a.
Proof.
  intros P psi phi0 a H Hle. inversion H; subst.
  - assumption.
  - exfalso. match goal with Hn : ~ (_ <= _) |- False => exact (Hn Hle) end.
Qed.

Lemma CGrade_side : forall (P:econtext) (psi phi0:grade) (a:tm),
  CGrade P psi phi0 a ->
  (phi0 <= psi -> Grade P psi a) /\ (~ (phi0 <= psi) -> lc_tm a).
Proof.
  intros P psi phi0 a H. split.
  - apply CGrade_leq_Grade. exact H.
  - intro Hn. inversion H; subst.
    + exfalso. match goal with Hl : _ <= _ |- False => exact (Hn Hl) end.
    + assumption.
Qed.

Lemma CGrade_of_Grade : forall (P:econtext) (psi phi0:grade) (a:tm),
  Grade P psi a -> CGrade P psi phi0 a.
Proof.
  intros P psi phi0 a H. destruct (q_leb phi0 psi) eqn:E.
  - apply CG_Leq. exact E. assumption.
  - apply CG_Nleq.
    + apply (Grade_lc P psi a). assumption.
    + unfold is_true. rewrite E. discriminate.
    + apply (Grade_uniq P psi a). assumption.
Qed.

Lemma Grade_open_arg : forall (P:econtext) (psi psi0:grade) (b:tm) (x:atom) (body:tm),
  uniq P -> x \notin dom P ->
  Grade ((x,psi0)::P) psi (open_tm_wrt_tm body (a_Var_f x)) ->
  CGrade P psi psi0 b ->
  x \notin fv_tm_tm body ->
  Grade P psi (open_tm_wrt_tm body b).
Proof.
  intros P psi psi0 b x body Hu Hxdom Hbody Hc Hfv.
  destruct (@CGrade_side P psi psi0 b Hc) as [Hg Hl].
  apply (@Grade_body_subst P psi psi0 body x b Hu Hxdom Hbody Hg Hl Hfv).
Qed.

Lemma Par_Grade : forall (P:econtext) (psi:grade) (a b:tm),
  Par P psi a b -> Grade P psi a /\ Grade P psi b.
Proof.
  intros P psi a b H. induction H using Par_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a b:tm) (_:CPar P psi phi0 a b) =>
                 CGrade P psi phi0 a /\ CGrade P psi phi0 b).
  - (* Refl *) split; assumption.
  - (* Pi *)
    split.
    + apply (@G_Pi L P psi psi1 A1 B1).
      * exact (proj1 IHPar).
      * intros x Hx. exact (proj1 (H0 x Hx)).
    + apply (@G_Pi L P psi psi1 A2 B2).
      * exact (proj2 IHPar).
      * intros x Hx. exact (proj2 (H0 x Hx)).
  - (* AppBeta *)
    destruct IHPar as [Ha Habs]. destruct IHPar0 as [Hb1 Hb2].
    inversion Habs; subst.
    split.
    + apply (@G_App P psi a psi0 b). exact Ha. exact Hb1.
    + destruct (atom_fresh (L \u (dom P \u fv_tm_tm a'))) as [x Hx].
      destruct (@fresh3_facts L P a' x Hx) as [HL [Hdom Hfv]].
      exact (@Grade_open_arg P psi psi0 b' x a'
               (Grade_uniq P psi a Ha) Hdom (H4 x HL) Hb2 Hfv).
  - (* App *)
    split.
    + apply (@G_App P psi a psi0 b). exact (proj1 IHPar). exact (proj1 IHPar0).
    + apply (@G_App P psi a' psi0 b'). exact (proj2 IHPar). exact (proj2 IHPar0).
  - (* Abs *)
    split.
    + apply (@G_Abs L P psi psi0 A1 b1).
      * intros x Hx. exact (proj1 (H x Hx)).
      * exact (proj1 IHPar).
    + apply (@G_Abs L P psi psi0 A2 b2).
      * intros x Hx. exact (proj2 (H x Hx)).
      * exact (proj2 IHPar).
  - (* WSigma *)
    split.
    + apply (@G_WSigma L P psi psi1 A1 B1).
      * exact (proj1 IHPar).
      * intros x Hx. exact (proj1 (H0 x Hx)).
    + apply (@G_WSigma L P psi psi1 A2 B2).
      * exact (proj2 IHPar).
      * intros x Hx. exact (proj2 (H0 x Hx)).
  - (* WPair *)
    split.
    + apply (@G_WPair P psi a1 psi0 b1). exact (proj1 IHPar). exact (proj1 IHPar0).
    + apply (@G_WPair P psi a2 psi0 b2). exact (proj2 IHPar). exact (proj2 IHPar0).
  - (* WPairBeta *)
    destruct IHPar as [Ha Ha'].
    inversion Ha'; subst.
    split.
    + apply (@G_LetPair L P psi psi0 a1 b1). exact Ha.
      intros x Hx. exact (proj1 (H0 x Hx)).
    + apply (@G_App P psi (open_tm_wrt_tm b2 a1') q_Bot a2').
      * destruct (atom_fresh (L \u (dom P \u fv_tm_tm b2))) as [x Hx].
        destruct (@fresh3_facts L P b2 x Hx) as [HL [Hdom Hfv]].
        exact (@Grade_open_arg P psi psi0 a1' x b2
                 (Grade_uniq P psi a1 Ha) Hdom (proj2 (H0 x HL)) H5 Hfv).
      * apply CGrade_of_Grade. exact H7.
  - (* LetPair *)
    split.
    + apply (@G_LetPair L P psi psi0 a1 b1). exact (proj1 IHPar).
      intros x Hx. exact (proj1 (H0 x Hx)).
    + apply (@G_LetPair L P psi psi0 a2 b2). exact (proj2 IHPar).
      intros x Hx. exact (proj2 (H0 x Hx)).
  - (* SSigma *)
    split.
    + apply (@G_SSigma L P psi psi1 A1 B1).
      * exact (proj1 IHPar).
      * intros x Hx. exact (proj1 (H0 x Hx)).
    + apply (@G_SSigma L P psi psi1 A2 B2).
      * exact (proj2 IHPar).
      * intros x Hx. exact (proj2 (H0 x Hx)).
  - (* SPair *)
    split.
    + apply (@G_SPair P psi a1 psi0 b1). exact (proj1 IHPar). exact (proj1 IHPar0).
    + apply (@G_SPair P psi a2 psi0 b2). exact (proj2 IHPar). exact (proj2 IHPar0).
  - (* Proj1Beta *)
    destruct IHPar as [Ha Ha'].
    inversion Ha'; subst.
    split.
    + apply (@G_Proj1 P psi psi0 a1). exact Ha. assumption.
    + apply (@CGrade_leq_Grade P psi psi0 a1'). exact H4. assumption.
  - (* Proj1 *)
    split.
    + apply (@G_Proj1 P psi psi0 a1). exact (proj1 IHPar). assumption.
    + apply (@G_Proj1 P psi psi0 a2). exact (proj2 IHPar). assumption.
  - (* Proj2Beta *)
    destruct IHPar as [Ha Ha'].
    inversion Ha'; subst.
    split.
    + apply (@G_Proj2 P psi psi0 a1). exact Ha.
    + exact H6.
  - (* Proj2 *)
    split.
    + apply (@G_Proj2 P psi psi0 a1). exact (proj1 IHPar).
    + apply (@G_Proj2 P psi psi0 a2). exact (proj2 IHPar).
  - (* Sum *)
    split.
    + apply (@G_Sum P psi A1 A2). exact (proj1 IHPar1). exact (proj1 IHPar2).
    + apply (@G_Sum P psi A1' A2'). exact (proj2 IHPar1). exact (proj2 IHPar2).
  - (* Inj1 *)
    split.
    + eapply G_Inj1. exact (proj1 IHPar).
    + eapply G_Inj1. exact (proj2 IHPar).
  - (* Inj2 *)
    split.
    + eapply G_Inj2. exact (proj1 IHPar).
    + eapply G_Inj2. exact (proj2 IHPar).
  - (* CaseBeta1 *)
    destruct IHPar1 as [Ha Ha']. destruct IHPar2 as [Hb1 Hb1']. destruct IHPar3 as [Hb2 Hb2'].
    inversion Ha'; subst.
    split.
    + apply (@G_Case P psi psi0 a b1 b2). exact Ha. exact Hb1. exact Hb2. assumption.
    + apply (@G_App P psi b1' psi0 a').
      * exact Hb1'.
      * apply CGrade_of_Grade. exact H5.
  - (* CaseBeta2 *)
    destruct IHPar1 as [Ha Ha']. destruct IHPar2 as [Hb1 Hb1']. destruct IHPar3 as [Hb2 Hb2'].
    inversion Ha'; subst.
    split.
    + apply (@G_Case P psi psi0 a b1 b2). exact Ha. exact Hb1. exact Hb2. assumption.
    + apply (@G_App P psi b2' psi0 a').
      * exact Hb2'.
      * apply CGrade_of_Grade. exact H5.
  - (* Case *)
    split.
    + apply (@G_Case P psi psi0 a b1 b2). exact (proj1 IHPar1). exact (proj1 IHPar2). exact (proj1 IHPar3). assumption.
    + apply (@G_Case P psi psi0 a' b1' b2'). exact (proj2 IHPar1). exact (proj2 IHPar2). exact (proj2 IHPar3). assumption.
  - (* CPar_Leq *)
    split.
    + apply (@CG_Leq P psi psi0); [exact i | exact (proj1 IHPar)].
    + apply (@CG_Leq P psi psi0); [exact i | exact (proj2 IHPar)].
  - (* CPar_Nleq *)
    split; eapply CG_Nleq; assumption.
Qed.


(* ================= Stage 6: multi-parallel reduction grades and GEq transitivity ================= *)
Lemma MultiPar_Grade : forall (P:econtext) (psi:grade) (a b:tm),
  MultiPar P psi a b -> Grade P psi a /\ Grade P psi b.
Proof.
  intros P psi a b H. induction H.
  - split; assumption.
  - apply Par_Grade in H as [Ha Hb]. destruct IHMultiPar as [Hb' Hc].
    split; assumption.
Qed.

Lemma MultiPar_trans : forall (P:econtext) (psi:grade) (a b:tm),
  MultiPar P psi a b -> forall c, MultiPar P psi b c -> MultiPar P psi a c.
Proof.
  intros P psi a b H. induction H; intros c Hc.
  - exact Hc.
  - eapply MP_Step. exact H. apply IHMultiPar. exact Hc.
Qed.

Lemma GEq_trans : forall (P:econtext) (psi:grade) (a b:tm),
  GEq P psi a b -> forall c, GEq P psi b c -> GEq P psi a c.
Proof.
  intros P psi a b H. induction H using GEq_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a b:tm) (_:CEq P psi phi0 a b) =>
                 forall c, CEq P psi phi0 b c -> CEq P psi phi0 a c).
  all: intros c2 Hc; inversion Hc; subst.
  all: try solve [exfalso; match goal with Hl : ?p <= ?q, Hn : ~ (?p <= ?q) |- _ => exact (Hn Hl) end].
  - eapply GEq_Var; eassumption.
  - eapply GEq_Type; eassumption.
  - eapply (@GEq_Pi (L \u L0) P psi psi0 A1 B1 A3 B3).
    + apply (IHGEq A3). assumption.
    + intros x Hx. apply (H0 x (@notin_union_l L L0 x Hx)).
      eauto using notin_union_l, notin_union_r.
  - eapply (@GEq_Abs (L \u L0) P psi psi0 A1 b1 A3 b3).
    + intros x Hx. apply (H x (@notin_union_l L L0 x Hx)).
      eauto using notin_union_l, notin_union_r.
    + eapply IHGEq. eassumption.
  - eapply GEq_App.
    + eapply IHGEq. eassumption.
    + eapply IHGEq0. eassumption.
  - eapply (@GEq_WSigma (L \u L0) P psi psi0 A1 B1 A3 B3).
    + apply (IHGEq A3). assumption.
    + intros x Hx. apply (H0 x (@notin_union_l L L0 x Hx)).
      eauto using notin_union_l, notin_union_r.
  - eapply GEq_WPair.
    + eapply IHGEq. eassumption.
    + eapply IHGEq0. eassumption.
  - eapply (@GEq_LetPair (L \u L0) P psi psi0 a1 b1 a3 b3).
    + apply (IHGEq a3). assumption.
    + intros x Hx. apply (H0 x (@notin_union_l L L0 x Hx)).
      eauto using notin_union_l, notin_union_r.
  - eapply (@GEq_SSigma (L \u L0) P psi psi0 A1 B1 A3 B3).
    + apply (IHGEq A3). assumption.
    + intros x Hx. apply (H0 x (@notin_union_l L L0 x Hx)).
      eauto using notin_union_l, notin_union_r.
  - eapply GEq_SPair.
    + eapply IHGEq. eassumption.
    + eapply IHGEq0. eassumption.
  - eapply GEq_Proj1. eapply IHGEq. eassumption. assumption.
  - eapply GEq_Proj2. eapply IHGEq. eassumption.
  - eapply GEq_Sum. eapply IHGEq1. eassumption. eapply IHGEq2. eassumption.
  - eapply GEq_Inj1. eapply IHGEq. eassumption.
  - eapply GEq_Inj2. eapply IHGEq. eassumption.
  - eapply GEq_Case.
    + eapply IHGEq1. eassumption.
    + eapply IHGEq2. eassumption.
    + eapply IHGEq3. eassumption.
    + assumption.
  - eapply GEq_TyUnit. eassumption.
  - eapply GEq_TmUnit. eassumption.
  - (* CEq_Leq *) eapply CEq_Leq. assumption. eapply IHGEq. eassumption.
  - (* CEq_Nleq *) eapply CEq_Nleq; eassumption.
Qed.


(* ================= Stage 7: shape decomposition of MultiPar on Pi ================= *)
Lemma MultiPar_Pi_decomp : forall (P:econtext) (psi:grade) (a b:tm),
  MultiPar P psi a b ->
  forall psi0 A1 B1, a = a_Pi psi0 A1 B1 ->
  exists A1' B1', b = a_Pi psi0 A1' B1' /\
    MultiPar P psi A1 A1' /\
    exists L, forall x, x \notin L ->
      MultiPar ((x,psi)::P) psi (open_tm_wrt_tm B1 (a_Var_f x))
                                        (open_tm_wrt_tm B1' (a_Var_f x)).
Proof.
  intros P psi a b H. induction H as [P psi a Ha | P psi a a' b Hpar Hmp IH];
    intros psi0 A1 B1 EQ; subst a.
  - (* MP_Refl *)
    destruct (@Grade_Pi_body P psi psi0 A1 B1 Ha) as [Lbody HB].
    exists A1, B1. split.
    + reflexivity.
    + split.
      * apply MP_Refl. exact (@Grade_Pi_inv P psi psi0 A1 B1 Ha).
      * exists Lbody. intros x Hx. apply MP_Refl. exact (HB x Hx).
  - (* MP_Step *)
    inversion Hpar; subst.
    + (* Par_Refl *)
      apply (IH psi0 A1 B1 (@Logic.eq_refl tm (a_Pi psi0 A1 B1))).
    + (* Par_Pi *)
      match goal with
      | HpA : Par P psi A1 ?A2,
        HpB : forall x, x \notin ?L -> Par _ psi
                (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm ?B2 (a_Var_f x)) |- _ =>
          destruct (IH psi0 A2 B2 (@Logic.eq_refl tm (a_Pi psi0 A2 B2)))
            as [A2' [B2' [Eb [MpA MpB]]]];
          destruct MpB as [L2 HB2];
          exists A2', B2'; split; [exact Eb | split];
          [ eapply MP_Step; [exact HpA | exact MpA] |
            exists (L \u L2); intros x Hx; eapply MP_Step;
            [ exact (HpB x (@notin_union_l L L2 x Hx)) |
              exact (HB2 x (@notin_union_r L L2 x Hx)) ] ]
      end.
Qed.


(* ================= Stage 8: single-step reduction preserves Grade ================= *)
Lemma Grade_Abs_body : forall (P:econtext) (psi psi0:grade) (A b:tm),
  Grade P psi (a_Abs psi0 A b) ->
  exists L, CGrade P psi q_Top A /\
    forall x, x \notin L -> Grade ((x,psi0)::P) psi (open_tm_wrt_tm b (a_Var_f x)).
Proof.
  intros. inversion H; subst. eexists. split; eassumption.
Qed.

Lemma Step_Grade : forall (P:econtext) (psi:grade) (a b:tm),
  Step a b -> Grade P psi a -> Grade P psi b.
Proof.
  intros P psi a b H. induction H; intros Ha.
  - (* AppCong *) destruct (@Grade_App_inv P psi a psi0 b Ha) as [Hfa Hcb].
    apply (@G_App P psi a' psi0 b). apply IHStep. exact Hfa. exact Hcb.
  - (* Beta *) destruct (@Grade_App_inv P psi (a_Abs psi0 A a) psi0 b Ha) as [Hfa Hcb].
    destruct (@Grade_Abs_body P psi psi0 A a Hfa) as [L [HcA Hb]].
    destruct (atom_fresh (L \u (dom P \u fv_tm_tm a))) as [x Hx].
    destruct (@fresh3_facts L P a x Hx) as [HL [Hdom Hfv]].
    exact (@Grade_open_arg P psi psi0 b x a (@Grade_uniq P psi (a_Abs psi0 A a) Hfa) Hdom (Hb x HL) Hcb Hfv).
  - (* CaseCong *) destruct (@Grade_Case_inv P psi psi0 a b1 b2 Ha) as [Hca [Hcb1 [Hcb2 Hle]]].
    apply (@G_Case P psi psi0 a' b1 b2). apply IHStep. exact Hca. exact Hcb1. exact Hcb2. exact Hle.
  - (* Case1Beta *) destruct (@Grade_Case_inv P psi psi0 (a_Inj1 a) b1 b2 Ha) as [Hca _].
    apply (@G_App P psi b1 psi0 a).
    + destruct (@Grade_Case_inv P psi psi0 (a_Inj1 a) b1 b2 Ha) as [_ [Hcb1 _]].
      exact Hcb1.
    + apply CGrade_of_Grade. exact (@Grade_Inj1_inv P psi a Hca).
  - (* Case2Beta *) destruct (@Grade_Case_inv P psi psi0 (a_Inj2 a) b1 b2 Ha) as [Hca _].
    apply (@G_App P psi b2 psi0 a).
    + destruct (@Grade_Case_inv P psi psi0 (a_Inj2 a) b1 b2 Ha) as [_ [_ [Hcb2 _]]].
      exact Hcb2.
    + apply CGrade_of_Grade. exact (@Grade_Inj2_inv P psi a Hca).
  - (* Proj1Cong *) destruct (@Grade_Proj1_inv P psi psi0 a Ha) as [Hga Hle].
    apply (@G_Proj1 P psi psi0 a'). apply IHStep. exact Hga. exact Hle.
  - (* Proj2Cong *) pose proof (@Grade_Proj2_inv P psi psi0 a Ha) as Hga.
    apply (@G_Proj2 P psi psi0 a'). apply IHStep. exact Hga.
  - (* Proj1Beta *) destruct (@Grade_Proj1_inv P psi psi0 (a_SPair a1 psi0 a2) Ha) as [Hsp Hle].
    destruct (@Grade_SPair_inv P psi a1 psi0 a2 Hsp) as [Hca1 Hg2].
    exact (@CGrade_leq_Grade P psi psi0 a1 Hca1 Hle).
  - (* Proj2Beta *) pose proof (@Grade_Proj2_inv P psi psi0 (a_SPair a1 psi0 a2) Ha) as Hsp.
    exact (proj2 (@Grade_SPair_inv P psi a1 psi0 a2 Hsp)).
  - (* LetPairCong *) destruct (@Grade_LetPair_inv P psi psi0 a b Ha) as [Hga [L Hbody]].
    apply (@G_LetPair L P psi psi0 a' b). apply IHStep. exact Hga. exact Hbody.
  - (* LetPairBeta *) destruct (@Grade_LetPair_inv P psi psi0 (a_WPair a1 psi0 a2) b Ha) as [Hwp [L Hbody]].
    destruct (@Grade_WPair_inv P psi a1 psi0 a2 Hwp) as [Hca1 Hg2].
    apply (@G_App P psi (open_tm_wrt_tm b a1) q_Bot a2).
    + destruct (atom_fresh (L \u (dom P \u fv_tm_tm b))) as [x Hx].
      destruct (@fresh3_facts L P b x Hx) as [HL [Hdom Hfv]].
      exact (@Grade_open_arg P psi psi0 a1 x b
               (@Grade_uniq P psi (a_LetPair psi0 (a_WPair a1 psi0 a2) b) Ha) Hdom (Hbody x HL) Hca1 Hfv).
    + apply CGrade_of_Grade. exact Hg2.
Qed.


(* ================= Stage 9: closing and opening well-scoped terms ================= *)
Lemma open_close_lc_at : forall u k x,
  lc_at k u ->
  open_tm_wrt_tm_rec k (a_Var_f x) (close_tm_wrt_tm_rec k x u) = u.
Proof.
  induction u as
    [| |psi A IHA B IHB |psi A IHA b IHb |a IHa psi b IHb |sq |m |y |A1 IHA1 A2 IHA2 |a IHa |a IHa
    |psi a IHa b1 IHb1 b2 IHb2 |psi A IHA B IHB |a IHa psi b IHb |psi a IHa b IHb
    |psi A IHA B IHB |a IHa psi b IHb |psi a IHa |psi a IHa ];
    intros k x H; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct H as [HA HB]. rewrite (IHA k x HA), (IHB (S k) x HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHA k x HA), (IHb (S k) x HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHa k x HA), (IHb k x HB). reflexivity.
  - reflexivity.
  - destruct (lt_ge_dec m k) as [Hlt|Hge]; [| exfalso; lia].
    simpl. destruct (lt_eq_lt_dec m k) as [[?|?]|?]; [reflexivity | lia | lia].
  - destruct (CoqEqDec.eq_dec x y) as [E|E].
    + subst. simpl. destruct (lt_eq_lt_dec k k) as [[?|?]|?]; [lia | reflexivity | lia].
    + simpl. destruct (CoqEqDec.eq_dec x y) as [E'|E']; [exfalso; apply E; exact E' | reflexivity].
  - destruct H as [HA HB]. rewrite (IHA1 k x HA), (IHA2 k x HB). reflexivity.
  - rewrite (IHa k x H); reflexivity.
  - rewrite (IHa k x H); reflexivity.
  - destruct H as [Ha [Hb1 Hb2]]. rewrite (IHa k x Ha), (IHb1 k x Hb1), (IHb2 k x Hb2). reflexivity.
  - destruct H as [HA HB]. rewrite (IHA k x HA), (IHB (S k) x HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHa k x HA), (IHb k x HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHa k x HA), (IHb (S k) x HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHA k x HA), (IHB (S k) x HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHa k x HA), (IHb k x HB). reflexivity.
  - rewrite (IHa k x H); reflexivity.
  - rewrite (IHa k x H); reflexivity.
Qed.

Definition rename_tm (x y:atom) (u:tm) : tm := subst_tm_tm (a_Var_f y) x u.

Lemma open_close_lc_at_rename : forall u k x y,
  x <> y -> lc_at k u ->
  open_tm_wrt_tm_rec k (a_Var_f y) (close_tm_wrt_tm_rec k x u) = rename_tm x y u.
Proof.
  induction u as
    [| |psi A IHA B IHB |psi A IHA b IHb |a IHa psi b IHb |sq |m |z |A1 IHA1 A2 IHA2 |a IHa |a IHa
    |psi a IHa b1 IHb1 b2 IHb2 |psi A IHA B IHB |a IHa psi b IHb |psi a IHa b IHb
    |psi A IHA B IHB |a IHa psi b IHb |psi a IHa |psi a IHa ];
    intros k x y Hne H; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct H as [HA HB]. rewrite (IHA k x y Hne HA), (IHB (S k) x y Hne HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHA k x y Hne HA), (IHb (S k) x y Hne HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHa k x y Hne HA), (IHb k x y Hne HB). reflexivity.
  - reflexivity.
  - destruct (lt_ge_dec m k) as [Hlt|Hge]; [| exfalso; lia].
    simpl. destruct (lt_eq_lt_dec m k) as [[?|?]|?]; [reflexivity | lia | lia].
  - destruct (CoqEqDec.eq_dec x z) as [E|E].
    + subst. unfold rename_tm. simpl.
      destruct (lt_eq_lt_dec k k) as [[?|?]|?]; [lia | | lia];
      destruct (CoqEqDec.eq_dec z z) as [E'|E']; [reflexivity | exfalso; apply E'; reflexivity].
    + unfold rename_tm. simpl. destruct (CoqEqDec.eq_dec z x) as [E'|E'].
      * exfalso; apply E; symmetry; exact E'.
      * reflexivity.
  - destruct H as [HA HB]. rewrite (IHA1 k x y Hne HA), (IHA2 k x y Hne HB). reflexivity.
  - rewrite (IHa k x y Hne H). reflexivity.
  - rewrite (IHa k x y Hne H). reflexivity.
  - destruct H as [Ha [Hb1 Hb2]]. rewrite (IHa k x y Hne Ha), (IHb1 k x y Hne Hb1), (IHb2 k x y Hne Hb2). reflexivity.
  - destruct H as [HA HB]. rewrite (IHA k x y Hne HA), (IHB (S k) x y Hne HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHa k x y Hne HA), (IHb k x y Hne HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHa k x y Hne HA), (IHb (S k) x y Hne HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHA k x y Hne HA), (IHB (S k) x y Hne HB). reflexivity.
  - destruct H as [HA HB]. rewrite (IHa k x y Hne HA), (IHb k x y Hne HB). reflexivity.
  - rewrite (IHa k x y Hne H). reflexivity.
  - rewrite (IHa k x y Hne H). reflexivity.
Qed.


(* ================= Stage 10: renaming preserves grading ================= *)
Lemma lc_rename_tm : forall u xr yr, lc_tm u -> lc_tm (rename_tm xr yr u).
Proof.
  intros. unfold rename_tm. apply (@lc_subst_tm_tm u xr (a_Var_f yr)). assumption. apply lc_a_Var_f.
Qed.

Lemma Grade_rename : forall (P:econtext) (psi:grade) (u:tm),
  Grade P psi u ->
  forall xr yr, xr <> yr -> xr \notin dom P -> yr \notin dom P ->
    Grade P psi (rename_tm xr yr u).
Proof.
  intros P psi u H. induction H using Grade_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (u:tm) (_:CGrade P psi phi0 u) =>
                 forall xr yr, xr <> yr -> xr \notin dom P -> yr \notin dom P ->
                   CGrade P psi phi0 (rename_tm xr yr u)).
  all: intros xr yr Hne Hx Hy; unfold rename_tm; simpl.
  - eapply G_Type; eassumption.
  - (* Var *) destruct (CoqEqDec.eq_dec x xr) as [E|E]; simpl in *.
    + exfalso. apply Hx. eapply binds_In. rewrite <- E. exact b.
    + eapply G_Var; [exact u | exact i | exact b].
  - (* Pi *) eapply (@G_Pi (L \u ({{xr}} \u {{yr}})) P psi psi0 (rename_tm xr yr A) (rename_tm xr yr B)).
    + apply IHGrade; assumption.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0. rewrite (@subst_open_comm0 B xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* Abs *) eapply (@G_Abs (L \u ({{xr}} \u {{yr}})) P psi psi0 (rename_tm xr yr A) (rename_tm xr yr b)).
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H. rewrite (@subst_open_comm0 b xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H.
      exact H.
    + apply IHGrade; assumption.
  - (* App *) eapply G_App.
    + apply IHGrade; assumption.
    + apply IHGrade0; assumption.
  - (* WSigma *) eapply (@G_WSigma (L \u ({{xr}} \u {{yr}})) P psi psi0 (rename_tm xr yr A) (rename_tm xr yr B)).
    + apply IHGrade; assumption.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0. rewrite (@subst_open_comm0 B xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* WPair *) eapply G_WPair.
    + apply IHGrade; assumption.
    + apply IHGrade0; assumption.
  - (* LetPair *) eapply (@G_LetPair (L \u ({{xr}} \u {{yr}})) P psi psi0 (rename_tm xr yr a) (rename_tm xr yr c)).
    + apply IHGrade; assumption.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0. rewrite (@subst_open_comm0 c xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* SSigma *) eapply (@G_SSigma (L \u ({{xr}} \u {{yr}})) P psi psi0 (rename_tm xr yr A) (rename_tm xr yr B)).
    + apply IHGrade; assumption.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0. rewrite (@subst_open_comm0 B xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* SPair *) eapply G_SPair.
    + apply IHGrade; assumption.
    + apply IHGrade0; assumption.
  - (* Proj1 *) eapply G_Proj1.
    + apply IHGrade; assumption.
    + assumption.
  - (* Proj2 *) eapply G_Proj2. apply IHGrade; assumption.
  - (* Sum *) eapply G_Sum.
    + apply IHGrade1; assumption.
    + apply IHGrade2; assumption.
  - (* Inj1 *) eapply G_Inj1. apply IHGrade; assumption.
  - (* Inj2 *) eapply G_Inj2. apply IHGrade; assumption.
  - (* Case *) eapply G_Case.
    + apply IHGrade1; assumption.
    + apply IHGrade2; assumption.
    + apply IHGrade3; assumption.
    + assumption.
  - (* TyUnit *) eapply G_TyUnit; eassumption.
  - (* TmUnit *) eapply G_TmUnit; eassumption.
  - (* CG_Leq *) eapply CG_Leq. assumption. apply IHGrade; assumption.
  - (* CG_Nleq *) eapply CG_Nleq.
    + apply lc_rename_tm; assumption.
    + assumption.
    + assumption.
Qed.


(* ================= Stage 11: renaming preserves GEq ================= *)
Lemma GEq_rename : forall (P:econtext) (psi:grade) (a b:tm),
  GEq P psi a b ->
  forall xr yr, xr <> yr -> xr \notin dom P -> yr \notin dom P ->
    GEq P psi (rename_tm xr yr a) (rename_tm xr yr b).
Proof.
  intros P psi a b H. induction H using GEq_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a b:tm) (_:CEq P psi phi0 a b) =>
                 forall xr yr, xr <> yr -> xr \notin dom P -> yr \notin dom P ->
                   CEq P psi phi0 (rename_tm xr yr a) (rename_tm xr yr b)).
  all: intros xr yr Hne Hx Hy; unfold rename_tm; simpl.
  - (* Var *) destruct (CoqEqDec.eq_dec x xr) as [E|E]; simpl in *.
    + exfalso. apply Hx. eapply binds_In. rewrite <- E. exact b.
    + eapply GEq_Var; [exact u | exact b | exact i].
  - (* Type *) eapply GEq_Type; eassumption.
  - (* Pi *) eapply (@GEq_Pi (L \u ({{xr}} \u {{yr}})) P psi psi0
                              (rename_tm xr yr A1) (rename_tm xr yr B1)
                              (rename_tm xr yr A2) (rename_tm xr yr B2)).
    + apply IHGEq; assumption.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0.
      rewrite (@subst_open_comm0 B1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      rewrite (@subst_open_comm0 B2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* Abs *) eapply (@GEq_Abs (L \u ({{xr}} \u {{yr}})) P psi psi0
                              (rename_tm xr yr A1) (rename_tm xr yr b1)
                              (rename_tm xr yr A2) (rename_tm xr yr b2)).
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H.
      rewrite (@subst_open_comm0 b1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H.
      rewrite (@subst_open_comm0 b2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H.
      exact H.
    + apply IHGEq; assumption.
  - (* App *) eapply GEq_App.
    + apply IHGEq; assumption.
    + apply IHGEq0; assumption.
  - (* WSigma *) eapply (@GEq_WSigma (L \u ({{xr}} \u {{yr}})) P psi psi0
                              (rename_tm xr yr A1) (rename_tm xr yr B1)
                              (rename_tm xr yr A2) (rename_tm xr yr B2)).
    + apply IHGEq; assumption.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0.
      rewrite (@subst_open_comm0 B1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      rewrite (@subst_open_comm0 B2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* WPair *) eapply GEq_WPair.
    + apply IHGEq; assumption.
    + apply IHGEq0; assumption.
  - (* LetPair *) eapply (@GEq_LetPair (L \u ({{xr}} \u {{yr}})) P psi psi0
                              (rename_tm xr yr a1) (rename_tm xr yr b1)
                              (rename_tm xr yr a2) (rename_tm xr yr b2)).
    + apply IHGEq; assumption.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0.
      rewrite (@subst_open_comm0 b1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      rewrite (@subst_open_comm0 b2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* SSigma *) eapply (@GEq_SSigma (L \u ({{xr}} \u {{yr}})) P psi psi0
                              (rename_tm xr yr A1) (rename_tm xr yr B1)
                              (rename_tm xr yr A2) (rename_tm xr yr B2)).
    + apply IHGEq; assumption.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0.
      rewrite (@subst_open_comm0 B1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      rewrite (@subst_open_comm0 B2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* SPair *) eapply GEq_SPair.
    + apply IHGEq; assumption.
    + apply IHGEq0; assumption.
  - (* Proj1 *) eapply GEq_Proj1. apply IHGEq; assumption. assumption.
  - (* Proj2 *) eapply GEq_Proj2. apply IHGEq; assumption.
  - (* Sum *) eapply GEq_Sum.
    + apply IHGEq1; assumption.
    + apply IHGEq2; assumption.
  - (* Inj1 *) eapply GEq_Inj1. apply IHGEq; assumption.
  - (* Inj2 *) eapply GEq_Inj2. apply IHGEq; assumption.
  - (* Case *) eapply GEq_Case.
    + apply IHGEq1; assumption.
    + apply IHGEq2; assumption.
    + apply IHGEq3; assumption.
    + assumption.
  - (* TyUnit *) eapply GEq_TyUnit; eassumption.
  - (* TmUnit *) eapply GEq_TmUnit; eassumption.
  - (* CEq_Leq *) eapply CEq_Leq. assumption. apply IHGEq; assumption.
  - (* CEq_Nleq *) eapply CEq_Nleq.
    + apply lc_rename_tm; assumption.
    + apply lc_rename_tm; assumption.
    + assumption.
    + assumption.
Qed.


(* ================= Stage 12: renaming preserves Par ================= *)
Lemma subst_open_rec_term : forall B k arg xr yr,
  xr <> yr ->
  subst_tm_tm (a_Var_f yr) xr (open_tm_wrt_tm_rec k arg B)
  = open_tm_wrt_tm_rec k (subst_tm_tm (a_Var_f yr) xr arg) (subst_tm_tm (a_Var_f yr) xr B).
Proof.
  induction B as
    [| |psi A IHA B IHB |psi A IHA b IHb |a IHa psi b IHb |sq |m |z |A1 IHA1 A2 IHA2 |a IHa |a IHa
    |psi a IHa b1 IHb1 b2 IHb2 |psi A IHA B IHB |a IHa psi b IHb |psi a IHa b IHb
    |psi A IHA B IHB |a IHa psi b IHb |psi a IHa |psi a IHa ];
    intros k arg xr yr Hne; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (IHA k arg xr yr Hne), (IHB (S k) arg xr yr Hne). reflexivity.
  - rewrite (IHA k arg xr yr Hne), (IHb (S k) arg xr yr Hne). reflexivity.
  - rewrite (IHa k arg xr yr Hne), (IHb k arg xr yr Hne). reflexivity.
  - reflexivity.
  - destruct (lt_eq_lt_dec m k) as [[?|?]|?]; simpl in *; try lia; reflexivity.
  - destruct (CoqEqDec.eq_dec z xr) as [E|E]; simpl.
    + subst. destruct (CoqEqDec.eq_dec xr xr) as [E'|E']; [reflexivity | exfalso; apply E'; reflexivity].
    + destruct (CoqEqDec.eq_dec z xr) as [E'|E']; [exfalso; apply E; exact E' | reflexivity].
  - rewrite (IHA1 k arg xr yr Hne), (IHA2 k arg xr yr Hne). reflexivity.
  - rewrite (IHa k arg xr yr Hne). reflexivity.
  - rewrite (IHa k arg xr yr Hne). reflexivity.
  - rewrite (IHa k arg xr yr Hne), (IHb1 k arg xr yr Hne), (IHb2 k arg xr yr Hne). reflexivity.
  - rewrite (IHA k arg xr yr Hne), (IHB (S k) arg xr yr Hne). reflexivity.
  - rewrite (IHa k arg xr yr Hne), (IHb k arg xr yr Hne). reflexivity.
  - rewrite (IHa k arg xr yr Hne), (IHb (S k) arg xr yr Hne). reflexivity.
  - rewrite (IHA k arg xr yr Hne), (IHB (S k) arg xr yr Hne). reflexivity.
  - rewrite (IHa k arg xr yr Hne), (IHb k arg xr yr Hne). reflexivity.
  - rewrite (IHa k arg xr yr Hne). reflexivity.
  - rewrite (IHa k arg xr yr Hne). reflexivity.
Qed.

Lemma subst_open_term : forall B arg xr yr,
  xr <> yr ->
  subst_tm_tm (a_Var_f yr) xr (open_tm_wrt_tm B arg)
  = open_tm_wrt_tm (subst_tm_tm (a_Var_f yr) xr B) (subst_tm_tm (a_Var_f yr) xr arg).
Proof. intros. apply (@subst_open_rec_term B 0 arg xr yr). assumption. Qed.

Lemma Par_rename : forall (P:econtext) (psi:grade) (a b:tm),
  Par P psi a b ->
  forall xr yr, xr <> yr -> xr \notin dom P -> yr \notin dom P ->
    Par P psi (rename_tm xr yr a) (rename_tm xr yr b).
Proof.
  intros P psi a b H. induction H using Par_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a b:tm) (_:CPar P psi phi0 a b) =>
                 forall xr yr, xr <> yr -> xr \notin dom P -> yr \notin dom P ->
                   CPar P psi phi0 (rename_tm xr yr a) (rename_tm xr yr b)).
  all: intros xr yr Hne Hx Hy; unfold rename_tm; simpl.
  - (* Refl *) apply Par_Refl. apply Grade_rename with (xr:=xr) (yr:=yr); assumption.
  - (* Pi *) eapply (@Par_Pi (L \u ({{xr}} \u {{yr}})) P psi psi1
                            (rename_tm xr yr A1) (rename_tm xr yr B1)
                            (rename_tm xr yr A2) (rename_tm xr yr B2)).
    + apply IHPar; assumption.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0.
      rewrite (@subst_open_comm0 B1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      rewrite (@subst_open_comm0 B2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* AppBeta *)
    specialize (IHPar xr yr Hne Hx Hy).
    specialize (IHPar0 xr yr Hne Hx Hy).
    rewrite (@subst_open_term a' b' xr yr Hne).
    eapply Par_AppBeta with (a' := rename_tm xr yr a') (b' := rename_tm xr yr b').
    + unfold rename_tm in IHPar. simpl in IHPar. exact IHPar.
    + exact IHPar0.
  - (* App *) eapply Par_App.
    + apply IHPar; assumption.
    + apply IHPar0; assumption.
  - (* Abs *) eapply (@Par_Abs (L \u ({{xr}} \u {{yr}})) P psi psi0
                            (rename_tm xr yr A1) (rename_tm xr yr b1)
                            (rename_tm xr yr A2) (rename_tm xr yr b2)).
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H.
      rewrite (@subst_open_comm0 b1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H.
      rewrite (@subst_open_comm0 b2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H.
      exact H.
    + apply IHPar; assumption.
  - (* WSigma *) eapply (@Par_WSigma (L \u ({{xr}} \u {{yr}})) P psi psi1
                            (rename_tm xr yr A1) (rename_tm xr yr B1)
                            (rename_tm xr yr A2) (rename_tm xr yr B2)).
    + apply IHPar; assumption.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0.
      rewrite (@subst_open_comm0 B1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      rewrite (@subst_open_comm0 B2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* WPair *) eapply Par_WPair.
    + apply IHPar; assumption.
    + apply IHPar0; assumption.
  - (* WPairBeta *)
    specialize (IHPar xr yr Hne Hx Hy).
    rewrite (@subst_open_term b2 a1' xr yr Hne).
    eapply Par_WPairBeta with (L := L \u ({{xr}} \u {{yr}})).
    + unfold rename_tm in IHPar; simpl in IHPar. exact IHPar.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0.
      rewrite (@subst_open_comm0 b1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      rewrite (@subst_open_comm0 b2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* LetPair *) eapply (@Par_LetPair (L \u ({{xr}} \u {{yr}})) P psi psi0
                            (rename_tm xr yr a1) (rename_tm xr yr b1)
                            (rename_tm xr yr a2) (rename_tm xr yr b2)).
    + apply IHPar; assumption.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0.
      rewrite (@subst_open_comm0 b1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      rewrite (@subst_open_comm0 b2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* SSigma *) eapply (@Par_SSigma (L \u ({{xr}} \u {{yr}})) P psi psi1
                            (rename_tm xr yr A1) (rename_tm xr yr B1)
                            (rename_tm xr yr A2) (rename_tm xr yr B2)).
    + apply IHPar; assumption.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0.
      rewrite (@subst_open_comm0 B1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      rewrite (@subst_open_comm0 B2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* SPair *) eapply Par_SPair.
    + apply IHPar; assumption.
    + apply IHPar0; assumption.
  - (* Proj1Beta *)
    specialize (IHPar xr yr Hne Hx Hy).
    eapply Par_Proj1Beta with (a1' := rename_tm xr yr a1') (a2 := rename_tm xr yr a2).
    + unfold rename_tm in IHPar; simpl in IHPar. exact IHPar.
    + assumption.
  - (* Proj1 *) eapply Par_Proj1.
    + apply IHPar; assumption.
    + assumption.
  - (* Proj2Beta *)
    specialize (IHPar xr yr Hne Hx Hy).
    eapply Par_Proj2Beta with (a1' := rename_tm xr yr a1') (a2 := rename_tm xr yr a2).
    unfold rename_tm in IHPar; simpl in IHPar. exact IHPar.
  - (* Proj2 *) eapply Par_Proj2. apply IHPar; assumption.
  - (* Sum *) eapply Par_Sum.
    + apply IHPar1; assumption.
    + apply IHPar2; assumption.
  - (* Inj1 *) eapply Par_Inj1. apply IHPar; assumption.
  - (* Inj2 *) eapply Par_Inj2. apply IHPar; assumption.
  - (* CaseBeta1 *)
    specialize (IHPar1 xr yr Hne Hx Hy).
    specialize (IHPar2 xr yr Hne Hx Hy).
    specialize (IHPar3 xr yr Hne Hx Hy).
    eapply Par_CaseBeta1 with (b1' := rename_tm xr yr b1') (a' := rename_tm xr yr a').
    + unfold rename_tm in IHPar1; simpl in IHPar1. exact IHPar1.
    + exact IHPar2.
    + exact IHPar3.
    + assumption.
  - (* CaseBeta2 *)
    specialize (IHPar1 xr yr Hne Hx Hy).
    specialize (IHPar2 xr yr Hne Hx Hy).
    specialize (IHPar3 xr yr Hne Hx Hy).
    eapply Par_CaseBeta2 with (b2' := rename_tm xr yr b2') (a' := rename_tm xr yr a').
    + unfold rename_tm in IHPar1; simpl in IHPar1. exact IHPar1.
    + exact IHPar2.
    + exact IHPar3.
    + assumption.
  - (* Case *) eapply Par_Case.
    + apply IHPar1; assumption.
    + apply IHPar2; assumption.
    + apply IHPar3; assumption.
    + assumption.
  - (* CPar_Leq *) eapply CPar_Leq. assumption. apply IHPar; assumption.
  - (* CPar_Nleq *) eapply CPar_Nleq.
    + apply lc_rename_tm; assumption.
    + apply lc_rename_tm; assumption.
    + assumption.
    + assumption.
Qed.

Lemma MultiPar_rename : forall (P:econtext) (psi:grade) (a b:tm),
  MultiPar P psi a b ->
  forall xr yr, xr <> yr -> xr \notin dom P -> yr \notin dom P ->
    MultiPar P psi (rename_tm xr yr a) (rename_tm xr yr b).
Proof.
  intros P psi a b H. induction H as [P psi a Ha | P psi a a' b Hpar Hmp IH];
    intros xr yr Hne Hx Hy.
  - apply MP_Refl. apply Grade_rename with (xr:=xr) (yr:=yr); assumption.
  - eapply MP_Step with (b := rename_tm xr yr b).
    + apply Par_rename with (xr:=xr) (yr:=yr); assumption.
    + apply IH; assumption.
Qed.


(* ================= Stage 14: values are irreducible ================= *)
Lemma ValueType_no_step : forall a, ValueType a -> forall b, ~ Step a b.
Proof.
  intros a H; induction H; intros b S; inversion S.
Qed.

Lemma Value_no_step : forall a, Value a -> forall b, ~ Step a b.
Proof.
  intros a H; induction H; intros y S.
  - exact (ValueType_no_step H S).
  - inversion S.
  - inversion S.
  - inversion S.
  - inversion S.
  - inversion S.
  - inversion S.
Qed.

Lemma Steps_value : forall a b, Value a -> Steps a b -> a = b.
Proof.
  intros a b Hv H; induction H.
  - reflexivity.
  - exfalso. eapply Value_no_step; eauto.
Qed.


(* ================= Stage 15: steps from a common source are linearly ordered ================= *)
Lemma Steps_join : forall a b, Steps a b -> forall c, Steps a c -> Steps b c \/ Steps c b.
Proof.
  intros a b H. induction H as [a | a x b Hs Hrest IH]; intros c Hc.
  - left. exact Hc.
  - inversion Hc; subst.
    + right. eapply Steps_step; [exact Hs | exact Hrest].
    + assert (x = b0) as E by (eapply step_det; eassumption); subst.
      apply (IH c H0).
Qed.


(* ================= Stage 16: consistency when a side is not a value type ================= *)
Lemma Consistent_of_not_value : forall a b, lc_tm a -> lc_tm b ->
  (~ ValueType a \/ ~ ValueType b) -> Consistent a b.
Proof.
  intros a b Ha Hb [Hna|Hnb].
  - apply Consistent_a_Step_R; assumption.
  - apply Consistent_a_Step_L; assumption.
Qed.


(* ================= Stage 17: unique value endpoint of a reduction ================= *)
Lemma Steps_value_unique : forall a b, Steps a b -> Value b ->
  forall c, Steps a c -> Value c -> b = c.
Proof.
  intros a b Hb Hvb c Hc Hvc.
  destruct (@Steps_join a b Hb c Hc) as [Hbc|Hcb].
  - eapply (@Steps_value b c); [exact Hvb | exact Hbc].
  - symmetry. eapply (@Steps_value c b); [exact Hvc | exact Hcb].
Qed.

Lemma Steps_VT_unique : forall a b, Steps a b -> ValueType b ->
  forall c, Steps a c -> ValueType c -> b = c.
Proof.
  intros. eapply Steps_value_unique;
    [exact H | apply V_ValueType; exact H0 | exact H1 | apply V_ValueType; exact H2].
Qed.


(* ================= Stage 18: Steps is transitive ================= *)
Lemma Steps_trans : forall a b, Steps a b -> forall c, Steps b c -> Steps a c.
Proof.
  intros a b H. induction H as [a | a x b Hs Hrest IH]; intros c Hc.
  - exact Hc.
  - eapply Steps_step; [exact Hs | apply IH; exact Hc].
Qed.


(* ================= Stage 19: Steps preserves Grade ================= *)
Lemma Steps_Grade : forall (P:econtext) (psi:grade) (a b:tm),
  Steps a b -> Grade P psi a -> Grade P psi b.
Proof.
  intros P psi a b H. induction H as [a | a x b Hs Hrest IH]; intros Ha.
  - exact Ha.
  - apply IH. apply (Step_Grade Hs Ha).
Qed.





Set Implicit Arguments.
Open Scope grade_scope.

Definition hasV (a:tm) : Prop := exists v, Value v /\ Steps a v.

Inductive R (P:econtext) (phi:grade) : tm -> tm -> Prop :=
| R_intro : forall (a b:tm),
    DefEq P phi a b ->
    Grade P phi a ->
    Grade P phi b ->
    lc_tm a ->
    lc_tm b ->
    (hasV a <-> hasV b) ->
    (forall (v w:tm), Value v -> Steps a v -> Value w -> Steps b w -> VM P phi v w) ->
    R P phi a b
with VM (P:econtext) (phi:grade) : tm -> tm -> Prop :=
| VM_Type : forall (s:sort), VM P phi (a_Type s) (a_Type s)
| VM_Unit : VM P phi a_TyUnit a_TyUnit
| VM_Pi : forall (psi0:grade) (A B A' B':tm),
    R P phi A A' ->
    (forall x:atom, R ((x~phi)++P) phi (open_tm_wrt_tm B (a_Var_f x))
                                         (open_tm_wrt_tm B' (a_Var_f x))) ->
    VM P phi (a_Pi psi0 A B) (a_Pi psi0 A' B')
| VM_WSigma : forall (psi0:grade) (A B A' B':tm),
    R P phi A A' ->
    (forall x:atom, R ((x~phi)++P) phi (open_tm_wrt_tm B (a_Var_f x))
                                         (open_tm_wrt_tm B' (a_Var_f x))) ->
    VM P phi (a_WSigma psi0 A B) (a_WSigma psi0 A' B')
| VM_SSigma : forall (psi0:grade) (A B A' B':tm),
    R P phi A A' ->
    (forall x:atom, R ((x~phi)++P) phi (open_tm_wrt_tm B (a_Var_f x))
                                         (open_tm_wrt_tm B' (a_Var_f x))) ->
    VM P phi (a_SSigma psi0 A B) (a_SSigma psi0 A' B')
| VM_Sum : forall (A B A' B':tm),
    R P phi A A' -> R P phi B B' ->
    VM P phi (a_Sum A B) (a_Sum A' B')
| VM_Abs : forall (psi0:grade) (A b A' b':tm),
    (forall x:atom, R ((x~psi0)++P) phi (open_tm_wrt_tm b (a_Var_f x))
                                          (open_tm_wrt_tm b' (a_Var_f x))) ->
    VM P phi (a_Abs psi0 A b) (a_Abs psi0 A' b')
| VM_WPair : forall (a:tm) (psi0:grade) (b a' b':tm),
    (psi0 <= phi -> R P phi a a') ->
    R P phi b b' ->
    VM P phi (a_WPair a psi0 b) (a_WPair a' psi0 b')
| VM_SPair : forall (a:tm) (psi0:grade) (b a' b':tm),
    (psi0 <= phi -> R P phi a a') ->
    R P phi b b' ->
    VM P phi (a_SPair a psi0 b) (a_SPair a' psi0 b')
| VM_Inj1 : forall a a', R P phi a a' -> VM P phi (a_Inj1 a) (a_Inj1 a')
| VM_Inj2 : forall a a', R P phi a a' -> VM P phi (a_Inj2 a) (a_Inj2 a')
| VM_refl : forall v, Value v -> Grade P phi v -> VM P phi v v.

Scheme R_mut_ind := Induction for R Sort Prop
with VM_mut_ind := Induction for VM Sort Prop.

Lemma R_deq : forall P phi a b, R P phi a b -> DefEq P phi a b.
Proof. intros P phi a b H; destruct H as [a b De Ga Gb lca lcb hv vm]; exact De. Qed.
Lemma R_grade_left : forall P phi a b, R P phi a b -> Grade P phi a.
Proof. intros P phi a b H; destruct H as [a b De Ga Gb lca lcb hv vm]; exact Ga. Qed.
Lemma R_grade_right : forall P phi a b, R P phi a b -> Grade P phi b.
Proof. intros P phi a b H; destruct H as [a b De Ga Gb lca lcb hv vm]; exact Gb. Qed.
Lemma R_lc_left : forall P phi a b, R P phi a b -> lc_tm a.
Proof. intros P phi a b H; destruct H as [a b De Ga Gb lca lcb hv vm]; exact lca. Qed.
Lemma R_lc_right : forall P phi a b, R P phi a b -> lc_tm b.
Proof. intros P phi a b H; destruct H as [a b De Ga Gb lca lcb hv vm]; exact lcb. Qed.
Lemma R_hasV : forall P phi a b, R P phi a b -> (hasV a <-> hasV b).
Proof. intros P phi a b H; destruct H as [a b De Ga Gb lca lcb hv vm]; exact hv. Qed.
Lemma R_vm : forall P phi a b, R P phi a b ->
  forall v w, Value v -> Steps a v -> Value w -> Steps b w -> VM P phi v w.
Proof. intros P phi a b H; destruct H as [a b De Ga Gb lca lcb hv vm]; exact vm. Qed.

Lemma R_intro_trans : forall P phi a b c,
  DefEq P phi a b ->
  Grade P phi a ->
  lc_tm a ->
  (hasV a <-> hasV b) ->
  (forall v w, Value v -> Steps a v -> Value w -> Steps b w -> VM P phi v w) ->
  R P phi b c ->
  (forall v w, Value v -> Steps a v -> Value w -> Steps b w ->
     forall u, VM P phi w u -> VM P phi v u) ->
  R P phi a c.
Proof.
  intros P phi a b c Dab Ga lca hv vm1 Hbc IH.
  apply R_intro.
  - eapply Eq_Trans; [exact Dab | exact (@R_deq P phi b c Hbc)].
  - exact Ga.
  - exact (R_grade_right Hbc).
  - exact lca.
  - exact (R_lc_right Hbc).
  - exact (iff_trans hv (R_hasV Hbc)).
  - intros x y Vx Sax Vy Scy.
    assert (Hax : hasV a) by (exists x; split; assumption).
    destruct ((proj1 hv) Hax) as [z [Vz Sbz]].
    exact (IH x z Vx Sax Vz Sbz y (@R_vm P phi b c Hbc z y Vz Sbz Vy Scy)).
Qed.

Lemma R_trans : forall P phi a b, R P phi a b -> forall c, R P phi b c -> R P phi a c.
Proof.
  intros P phi a b H.
  induction H using R_mut_ind
    with (P := fun P phi a b (_:R P phi a b) => forall c, R P phi b c -> R P phi a c)
         (P0 := fun P phi v w (_:VM P phi v w) => forall u, VM P phi w u -> VM P phi v u).
  - intros c Hbc.
    eapply R_intro_trans; [ exact d | exact g | exact l | exact i | exact v | exact Hbc | exact H ].
  - intros u Hu; exact Hu.
  - intros u Hu; exact Hu.
  - intros u Hu; inversion Hu; subst;
      [ apply VM_Pi; firstorder | apply VM_Pi; [exact H | exact r] ].
  - intros u Hu; inversion Hu; subst;
      [ apply VM_WSigma; firstorder | apply VM_WSigma; [exact H | exact r] ].
  - intros u Hu; inversion Hu; subst;
      [ apply VM_SSigma; firstorder | apply VM_SSigma; [exact H | exact r] ].
  - intros u Hu; inversion Hu; subst;
      [ apply VM_Sum; firstorder | apply VM_Sum; [exact H | exact H0] ].
  - intros u Hu; inversion Hu; subst;
      [ apply VM_Abs; firstorder | apply VM_Abs; exact r ].
  - intros u Hu; inversion Hu; subst.
    + apply VM_WPair.
      * intro i. apply H.
        { exact i. }
        { match goal with Hx : psi0 <= phi -> R P phi a' ?x |- R P phi a' ?x => exact (Hx i) end. }
      * apply IHR.
        match goal with Hx : R P phi b' ?x |- R P phi b' ?x => exact Hx end.
    + apply VM_WPair.
      * intro i. exact (r i).
      * exact H0.
  - intros u Hu; inversion Hu; subst.
    + apply VM_SPair.
      * intro i. apply H.
        { exact i. }
        { match goal with Hx : psi0 <= phi -> R P phi a' ?x |- R P phi a' ?x => exact (Hx i) end. }
      * apply IHR.
        match goal with Hx : R P phi b' ?x |- R P phi b' ?x => exact Hx end.
    + apply VM_SPair.
      * intro i. exact (r i).
      * exact H0.
  - intros u Hu; inversion Hu; subst;
      [ apply VM_Inj1; firstorder | apply VM_Inj1; exact H ].
  - intros u Hu; inversion Hu; subst;
      [ apply VM_Inj2; firstorder | apply VM_Inj2; exact H ].
  - intros u Hu; exact Hu.
Qed.

Lemma VM_trans : forall P phi v w, VM P phi v w -> forall u, VM P phi w u -> VM P phi v u.
Proof.
  intros P phi v w H.
  induction H using VM_mut_ind
    with (P := fun P phi a b (_:R P phi a b) => forall c, R P phi b c -> R P phi a c)
         (P0 := fun P phi v w (_:VM P phi v w) => forall u, VM P phi w u -> VM P phi v u).
  - intros c Hbc.
    eapply R_intro_trans; [ exact d | exact g | exact l | exact i | exact v | exact Hbc | exact H ].
  - intros u Hu; exact Hu.
  - intros u Hu; exact Hu.
  - intros u Hu; inversion Hu; subst;
      [ apply VM_Pi; firstorder | apply VM_Pi; [exact r | exact r0] ].
  - intros u Hu; inversion Hu; subst;
      [ apply VM_WSigma; firstorder | apply VM_WSigma; [exact r | exact r0] ].
  - intros u Hu; inversion Hu; subst;
      [ apply VM_SSigma; firstorder | apply VM_SSigma; [exact r | exact r0] ].
  - intros u Hu; inversion Hu; subst;
      [ apply VM_Sum; firstorder | apply VM_Sum; [exact r | exact r0] ].
  - intros u Hu; inversion Hu; subst;
      [ apply VM_Abs; firstorder | apply VM_Abs; exact r ].
  - intros u Hu; inversion Hu; subst.
    + apply VM_WPair.
      * intro i. apply H.
        { exact i. }
        { match goal with Hx : psi0 <= phi -> R P phi a' ?x |- R P phi a' ?x => exact (Hx i) end. }
      * apply IHVM.
        match goal with Hx : R P phi b' ?x |- R P phi b' ?x => exact Hx end.
    + apply VM_WPair.
      * intro i. exact (r i).
      * exact r0.
  - intros u Hu; inversion Hu; subst.
    + apply VM_SPair.
      * intro i. apply H.
        { exact i. }
        { match goal with Hx : psi0 <= phi -> R P phi a' ?x |- R P phi a' ?x => exact (Hx i) end. }
      * apply IHVM.
        match goal with Hx : R P phi b' ?x |- R P phi b' ?x => exact Hx end.
    + apply VM_SPair.
      * intro i. exact (r i).
      * exact r0.
  - intros u Hu; inversion Hu; subst;
      [ apply VM_Inj1; firstorder | apply VM_Inj1; exact r ].
  - intros u Hu; inversion Hu; subst;
      [ apply VM_Inj2; firstorder | apply VM_Inj2; exact r ].
  - intros u Hu; exact Hu.
Qed.

Lemma R_sym : forall P phi a b, R P phi a b -> R P phi b a.
Proof.
  intros P phi a b H.
  induction H using R_mut_ind
    with (P := fun P phi a b (_:R P phi a b) => R P phi b a)
         (P0 := fun P phi v w (_:VM P phi v w) => VM P phi w v).
  - apply R_intro.
    + eapply Eq_Sym; exact d.
    + exact g0.
    + exact g.
    + exact l0.
    + exact l.
    + split; intros Hx; apply i; assumption.
    + intros x y Vx Sbx Vy Say. exact (H y x Vy Say Vx Sbx).
  - apply VM_Type.
  - apply VM_Unit.
  - apply VM_Pi; assumption.
  - apply VM_WSigma; assumption.
  - apply VM_SSigma; assumption.
  - apply VM_Sum; assumption.
  - apply VM_Abs; assumption.
  - apply VM_WPair; assumption.
  - apply VM_SPair; assumption.
  - apply VM_Inj1; assumption.
  - apply VM_Inj2; assumption.
  - apply VM_refl; assumption.
Qed.

Lemma VM_sym : forall P phi v w, VM P phi v w -> VM P phi w v.
Proof.
  intros P phi v w H.
  induction H using VM_mut_ind
    with (P := fun P phi a b (_:R P phi a b) => R P phi b a)
         (P0 := fun P phi v w (_:VM P phi v w) => VM P phi w v).
  - apply R_intro.
    + eapply Eq_Sym; exact d.
    + exact g0.
    + exact g.
    + exact l0.
    + exact l.
    + split; intros Hx; apply i; assumption.
    + intros x y Vx Sbx Vy Say. exact (H y x Vy Say Vx Sbx).
  - apply VM_Type.
  - apply VM_Unit.
  - apply VM_Pi; assumption.
  - apply VM_WSigma; assumption.
  - apply VM_SSigma; assumption.
  - apply VM_Sum; assumption.
  - apply VM_Abs; assumption.
  - apply VM_WPair; assumption.
  - apply VM_SPair; assumption.
  - apply VM_Inj1; assumption.
  - apply VM_Inj2; assumption.
  - apply VM_refl; assumption.
Qed.

Lemma ValueType_lc : forall a, ValueType a -> lc_tm a.
Proof.
  intros a H; destruct H; auto using lc_a_Type, lc_a_TyUnit.
  apply lc_a_Sum; assumption.
Qed.

Lemma Value_lc : forall a, Value a -> lc_tm a.
Proof.
  intros a H; destruct H.
  - apply ValueType_lc; assumption.
  - apply lc_a_TmUnit.
  - assumption.
  - apply lc_a_WPair; assumption.
  - apply lc_a_SPair; assumption.
  - apply lc_a_Inj1; assumption.
  - apply lc_a_Inj2; assumption.
Qed.

Lemma R_refl : forall P phi a, Grade P phi a -> R P phi a a.
Proof.
  intros P phi a Ga. apply R_intro.
  - eapply Eq_Refl; exact Ga.
  - exact Ga.
  - exact Ga.
  - exact (@Grade_lc P phi a Ga).
  - exact (@Grade_lc P phi a Ga).
  - split; auto.
  - intros v w Vv Sav Vw Saw.
    assert (E : v = w) by exact (@Steps_value_unique a v Sav Vv w Saw Vw).
    subst w. exact (@VM_refl P phi v Vv (@Steps_Grade P phi a v Sav Ga)).
Qed.

Lemma VM_VtTag : forall P phi v w, VM P phi v w -> ValueType v -> ValueType w -> VtTag v w.
Proof.
  intros P phi v w H.
  induction H using VM_mut_ind
    with (P := fun P phi a b (_:R P phi a b) => True)
         (P0 := fun P phi v w (_:VM P phi v w) => ValueType v -> ValueType w -> VtTag v w).
  - exact I.
  - intros; apply VtTag_Type.
  - intros; apply VtTag_Unit.
  - intros; apply VtTag_Pi.
  - intros; apply VtTag_WSigma.
  - intros; apply VtTag_SSigma.
  - intros; apply VtTag_Sum.
  - intros VTv VTw; inversion VTv.
  - intros VTv VTw; inversion VTv.
  - intros VTv VTw; inversion VTv.
  - intros VTv VTw; inversion VTv.
  - intros VTv VTw; inversion VTv.
  - intros VTv VTw; apply VtTag_refl; assumption.
Qed.

Lemma R_Consistent_VT : forall P phi a b,
  R P phi a b -> ValueType a -> ValueType b -> Consistent a b.
Proof.
  intros P phi a b H VTa VTb.
  assert (Hvm : VM P phi a b) by
    exact (@R_vm P phi a b H a b (@V_ValueType a VTa) (Steps_refl a)
             (@V_ValueType b VTb) (Steps_refl b)).
  assert (Htag : VtTag a b) by exact (@VM_VtTag P phi a b Hvm VTa VTb).
  eapply Consistent_of_VtTag.
  - exact Htag.
  - apply ValueType_lc; exact VTa.
  - apply ValueType_lc; exact VTb.
Qed.

Lemma R_of_step : forall P phi a b,
  Grade P phi a -> Step a b -> R P phi a b.
Proof.
  intros P phi a b Ga Sab.
  assert (Gb : Grade P phi b) by exact (@Step_Grade P phi a b Sab Ga).
  apply R_intro.
  - eapply Eq_Beta; [exact Ga | exact Sab | exact Gb].
  - exact Ga.
  - exact Gb.
  - apply (@Grade_lc P phi a Ga).
  - apply (@Grade_lc P phi b Gb).
  - split.
    + intros [v [Vv Sav]].
      destruct (@Steps_join a b (@Steps_step a b b Sab (Steps_refl b)) v Sav)
        as [Sbv | Svb].
      * exists v; split; assumption.
      * assert (E : v = b) by exact (@Steps_value v b Vv Svb).
        subst v. exists b; split; assumption.
    + intros [w [Vw Sbw]].
      exists w; split; [exact Vw | eapply @Steps_step; eassumption].
  - intros v w Vv Sav Vw Sbw.
    destruct (@Steps_join a b (@Steps_step a b b Sab (Steps_refl b)) v Sav)
      as [Sbv | Svb].
    + pose proof (@Steps_value_unique b v Sbv Vv w Sbw Vw) as E.
      subst w. exact (@VM_refl P phi v Vv (@Steps_Grade P phi b v Sbv Gb)).
    + pose proof (@Steps_value v b Vv Svb) as E.
      subst v. pose proof (@Steps_value b w Vv Sbw) as E2.
      subst w. exact (@VM_refl P phi b Vv Gb).
Qed.

Lemma R_Type_TmUnit_false : forall P phi s, ~ R P phi (a_Type s) a_TmUnit.
Proof.
  intros P phi s H.
  pose proof (@R_vm P phi (a_Type s) a_TmUnit H (a_Type s) a_TmUnit
    (@V_ValueType (a_Type s) (ValueType_Type s)) (Steps_refl (a_Type s))
    V_TmUnit (Steps_refl a_TmUnit)) as Hvm.
  inversion Hvm.
Qed.


Set Implicit Arguments.
Open Scope grade_scope.

Lemma Step_rename : forall (a b:tm), Step a b ->
  forall xr yr, xr <> yr ->
    Step (rename_tm xr yr a) (rename_tm xr yr b).
Proof.
  intros a b H. induction H; intros xr yr Hne; unfold rename_tm; simpl.
  - (* AppCong *) eapply S_AppCong.
    + exact (@lc_rename_tm b xr yr H).
    + exact (IHStep xr yr Hne).
  - (* Beta *)
    rewrite (@subst_open_term a b xr yr Hne).
    eapply S_Beta.
    + exact (@lc_rename_tm A xr yr H).
    + exact (@lc_rename_tm (a_Abs psi A a) xr yr H0).
    + exact (@lc_rename_tm b xr yr H1).
  - (* CaseCong *) eapply S_CaseCong.
    + exact (@lc_rename_tm b1 xr yr H).
    + exact (@lc_rename_tm b2 xr yr H0).
    + exact (IHStep xr yr Hne).
  - (* Case1Beta *) eapply S_Case1Beta.
    + exact (@lc_rename_tm b2 xr yr H).
    + exact (@lc_rename_tm b1 xr yr H0).
    + exact (@lc_rename_tm a xr yr H1).
  - (* Case2Beta *) eapply S_Case2Beta.
    + exact (@lc_rename_tm b1 xr yr H).
    + exact (@lc_rename_tm b2 xr yr H0).
    + exact (@lc_rename_tm a xr yr H1).
  - (* Proj1Cong *) eapply S_Proj1Cong. exact (IHStep xr yr Hne).
  - (* Proj2Cong *) eapply S_Proj2Cong. exact (IHStep xr yr Hne).
  - (* Proj1Beta *) eapply S_Proj1Beta.
    + exact (@lc_rename_tm a2 xr yr H).
    + exact (@lc_rename_tm a1 xr yr H0).
  - (* Proj2Beta *) eapply S_Proj2Beta.
    + exact (@lc_rename_tm a1 xr yr H).
    + exact (@lc_rename_tm a2 xr yr H0).
  - (* LetPairCong *) eapply S_LetPairCong.
    + exact (@lc_rename_tm (a_LetPair psi a b) xr yr H).
    + exact (IHStep xr yr Hne).
  - (* LetPairBeta *)
    rewrite (@subst_open_term b a1 xr yr Hne).
    eapply S_LetPairBeta.
    + exact (@lc_rename_tm (a_LetPair psi (a_WPair a1 psi a2) b) xr yr H).
    + exact (@lc_rename_tm a1 xr yr H0).
    + exact (@lc_rename_tm a2 xr yr H1).
Qed.


Set Implicit Arguments.
Open Scope grade_scope.

Lemma DefEq_rename : forall (P:econtext) (psi:grade) (a b:tm),
  DefEq P psi a b ->
  forall xr yr, xr <> yr -> xr \notin dom P -> yr \notin dom P ->
    DefEq P psi (rename_tm xr yr a) (rename_tm xr yr b).
Proof.
  intros P psi a b H. induction H using DefEq_mind
    with (P0 := fun (P:econtext) (psi phi0:grade) (a b:tm) (_:CDefEq P psi phi0 a b) =>
                 forall xr yr, xr <> yr -> xr \notin dom P -> yr \notin dom P ->
                   CDefEq P psi phi0 (rename_tm xr yr a) (rename_tm xr yr b)).
  all: intros xr yr Hne Hx Hy; unfold rename_tm; simpl.
  - (* Refl *) apply Eq_Refl. apply Grade_rename with (xr:=xr) (yr:=yr); assumption.
  - (* Trans *) eapply Eq_Trans; [exact (IHDefEq1 xr yr Hne Hx Hy) | exact (IHDefEq2 xr yr Hne Hx Hy)].
  - (* Sym *) eapply Eq_Sym. exact (IHDefEq xr yr Hne Hx Hy).
  - (* Beta *) eapply Eq_Beta.
    + apply Grade_rename with (xr:=xr) (yr:=yr); assumption.
    + exact (@Step_rename a b s xr yr Hne).
    + apply Grade_rename with (xr:=xr) (yr:=yr); assumption.
  - (* Pi *) eapply (@Eq_Pi (L \u ({{xr}} \u {{yr}})) P psi psi0
                              (rename_tm xr yr A1) (rename_tm xr yr B1)
                              (rename_tm xr yr A2) (rename_tm xr yr B2)).
    + exact (IHDefEq xr yr Hne Hx Hy).
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0.
      rewrite (@subst_open_comm0 B1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      rewrite (@subst_open_comm0 B2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* Abs *) eapply (@Eq_Abs (L \u ({{xr}} \u {{yr}})) P psi psi0
                              (rename_tm xr yr A1) (rename_tm xr yr b1)
                              (rename_tm xr yr A2) (rename_tm xr yr b2)).
    + exact (IHDefEq xr yr Hne Hx Hy).
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H.
      rewrite (@subst_open_comm0 b1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H.
      rewrite (@subst_open_comm0 b2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H.
      exact H.
  - (* App *) eapply (@Eq_App P psi (rename_tm xr yr b1) psi0
                             (rename_tm xr yr a1) (rename_tm xr yr b2) (rename_tm xr yr a2)).
    + exact (IHDefEq xr yr Hne Hx Hy).
    + exact (IHDefEq0 xr yr Hne Hx Hy).
  - (* PiFst *) eapply Eq_PiFst. exact (IHDefEq xr yr Hne Hx Hy).
  - (* PiSnd *)
    rewrite (@subst_open_term B1 a1 xr yr Hne).
    rewrite (@subst_open_term B2 a2 xr yr Hne).
    eapply (@Eq_PiSnd P psi (rename_tm xr yr B1) (rename_tm xr yr a1)
                           (rename_tm xr yr B2) (rename_tm xr yr a2) psi0
                           (rename_tm xr yr A1) (rename_tm xr yr A2)).
    + exact (IHDefEq1 xr yr Hne Hx Hy).
    + exact (IHDefEq2 xr yr Hne Hx Hy).
  - (* WSigma *) eapply (@Eq_WSigma (L \u ({{xr}} \u {{yr}})) P psi psi0
                              (rename_tm xr yr A1) (rename_tm xr yr B1)
                              (rename_tm xr yr A2) (rename_tm xr yr B2)).
    + exact (IHDefEq xr yr Hne Hx Hy).
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0.
      rewrite (@subst_open_comm0 B1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      rewrite (@subst_open_comm0 B2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* WSigmaFst *) eapply Eq_WSigmaFst. exact (IHDefEq xr yr Hne Hx Hy).
  - (* WSigmaSnd *)
    rewrite (@subst_open_term B1 a xr yr Hne).
    rewrite (@subst_open_term B2 a xr yr Hne).
    eapply (@Eq_WSigmaSnd P psi (rename_tm xr yr B1) (rename_tm xr yr a)
                               (rename_tm xr yr B2) psi0
                               (rename_tm xr yr A1) (rename_tm xr yr A2)).
    + exact (IHDefEq xr yr Hne Hx Hy).
    + apply Grade_rename with (xr:=xr) (yr:=yr); assumption.
  - (* WPair *) eapply (@Eq_WPair P psi (rename_tm xr yr a1) psi0 (rename_tm xr yr b1)
                                     (rename_tm xr yr a2) (rename_tm xr yr b2)).
    + exact (IHDefEq xr yr Hne Hx Hy).
    + exact (IHDefEq0 xr yr Hne Hx Hy).
  - (* LetPair *) eapply (@Eq_LetPair (L \u ({{xr}} \u {{yr}})) P psi psi0
                              (rename_tm xr yr a1) (rename_tm xr yr b1)
                              (rename_tm xr yr a2) (rename_tm xr yr b2)).
    + exact (IHDefEq xr yr Hne Hx Hy).
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi0)::P)) by (apply (@notin_dom_cons grade z psi0 P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0.
      rewrite (@subst_open_comm0 b1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      rewrite (@subst_open_comm0 b2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* SSigma *) eapply (@Eq_SSigma (L \u ({{xr}} \u {{yr}})) P psi psi0
                              (rename_tm xr yr A1) (rename_tm xr yr B1)
                              (rename_tm xr yr A2) (rename_tm xr yr B2)).
    + exact (IHDefEq xr yr Hne Hx Hy).
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H0 z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H0.
      rewrite (@subst_open_comm0 B1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      rewrite (@subst_open_comm0 B2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H0.
      exact H0.
  - (* SSigmaFst *) eapply Eq_SSigmaFst. exact (IHDefEq xr yr Hne Hx Hy).
  - (* SSigmaSnd *)
    rewrite (@subst_open_term B1 a1 xr yr Hne).
    rewrite (@subst_open_term B2 a2 xr yr Hne).
    eapply (@Eq_SSigmaSnd P psi (rename_tm xr yr B1) (rename_tm xr yr a1)
                               (rename_tm xr yr B2) (rename_tm xr yr a2) psi0
                               (rename_tm xr yr A1) (rename_tm xr yr A2)).
    + exact (IHDefEq1 xr yr Hne Hx Hy).
    + exact (IHDefEq2 xr yr Hne Hx Hy).
  - (* SPair *) eapply (@Eq_SPair P psi (rename_tm xr yr a1) psi0 (rename_tm xr yr b1)
                                     (rename_tm xr yr a2) (rename_tm xr yr b2)).
    + exact (IHDefEq xr yr Hne Hx Hy).
    + exact (IHDefEq0 xr yr Hne Hx Hy).
  - (* Proj1 *) eapply Eq_Proj1.
    + exact (IHDefEq xr yr Hne Hx Hy).
    + assumption.
  - (* Proj2 *) eapply Eq_Proj2. exact (IHDefEq xr yr Hne Hx Hy).
  - (* Sum *) eapply (@Eq_Sum P psi (rename_tm xr yr A1) (rename_tm xr yr A2)
                                   (rename_tm xr yr A1') (rename_tm xr yr A2')).
    + exact (IHDefEq1 xr yr Hne Hx Hy).
    + exact (IHDefEq2 xr yr Hne Hx Hy).
  - (* SumFst *) eapply Eq_SumFst. exact (IHDefEq xr yr Hne Hx Hy).
  - (* SumSnd *) eapply Eq_SumSnd. exact (IHDefEq xr yr Hne Hx Hy).
  - (* Inj1 *) eapply Eq_Inj1. exact (IHDefEq xr yr Hne Hx Hy).
  - (* Inj2 *) eapply Eq_Inj2. exact (IHDefEq xr yr Hne Hx Hy).
  - (* Case *) eapply (@Eq_Case P psi psi0
                                 (rename_tm xr yr a) (rename_tm xr yr b1) (rename_tm xr yr b2)
                                 (rename_tm xr yr a') (rename_tm xr yr b1') (rename_tm xr yr b2')).
    + exact (IHDefEq1 xr yr Hne Hx Hy).
    + exact (IHDefEq2 xr yr Hne Hx Hy).
    + exact (IHDefEq3 xr yr Hne Hx Hy).
    + assumption.
  - (* TyUnit *) apply Eq_TyUnit. assumption.
  - (* TmUnit *) apply Eq_TmUnit. assumption.
  - (* SubstIrrel *)
    rewrite (@subst_open_term b1 a1 xr yr Hne).
    rewrite (@subst_open_term b2 a2 xr yr Hne).
    eapply (@Eq_SubstIrrel (L \u ({{xr}} \u {{yr}})) P phi
                                 (rename_tm xr yr b1) (rename_tm xr yr a1)
                                 (rename_tm xr yr b2) (rename_tm xr yr a2) psi).
    + exact (@lc_rename_tm a1 xr yr l).
    + exact (@lc_rename_tm a2 xr yr l0).
    + exact I.
    + exact I.
    + intros z Hz.
      assert (HzL : z \notin L) by (apply (@notin_union_l L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzr : z \notin ({{xr}} \u {{yr}})) by (apply (@notin_union_r L ({{xr}} \u {{yr}}) z); exact Hz).
      assert (Hzx : z <> xr) by (intro E; apply Hzr; apply AtomSetImpl.union_2; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hzy : z <> yr) by (intro E; apply Hzr; apply AtomSetImpl.union_3; subst; apply AtomSetImpl.singleton_2; reflexivity).
      assert (Hxd : xr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P xr); [symmetry; exact Hzx | exact Hx]).
      assert (Hyd : yr \notin dom ((z,psi)::P)) by (apply (@notin_dom_cons grade z psi P yr); [symmetry; exact Hzy | exact Hy]).
      specialize (H z HzL xr yr Hne Hxd Hyd).
      unfold rename_tm in H.
      rewrite (@subst_open_comm0 b1 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H.
      rewrite (@subst_open_comm0 b2 xr (a_Var_f yr) z (lc_a_Var_f yr) Hzx) in H.
      exact H.
    + exact n.
  - (* CDefEq_Leq *) eapply CDefEq_Leq.
    + exact i.
    + exact (IHDefEq xr yr Hne Hx Hy).
  - (* CDefEq_Nleq *) eapply CDefEq_Nleq.
    + exact (@lc_rename_tm a xr yr l).
    + exact (@lc_rename_tm b xr yr l0).
    + exact n.
    + exact u.
Qed.


Set Implicit Arguments.
Open Scope grade_scope.

Lemma subst_tm_tm_fresh : forall (u:tm) (x:atom) (a:tm),
  x \notin fv_tm_tm a -> subst_tm_tm u x a = a.
Proof.
  intros w z a0 Hx.
  induction a0 as
    [| |psi A IHA B IHB |psi A IHA b0 IHb |a1 IHa1 psi b1 IHb1 |s |n |xv
    |A1 IHA1 A2 IHA2 |a1 IHa1 |a1 IHa1
    |psi a1 IHa1 b1 IHb1 b2 IHb2 |psi A IHA B IHB |a1 IHa1 psi b1 IHb1
    |psi a1 IHa1 b1 IHb1 |psi A IHA B IHB |a1 IHa1 psi b1 IHb1
    |psi a1 IHa1 |psi a1 IHa1 ];
    simpl in *; try reflexivity.
  - (* Pi *) f_equal.
    + apply IHA. apply (@notin_union_l (fv_tm_tm A) (fv_tm_tm B) z). exact Hx.
    + apply IHB. apply (@notin_union_r (fv_tm_tm A) (fv_tm_tm B) z). exact Hx.
  - (* Abs *) f_equal.
    + apply IHA. apply (@notin_union_l (fv_tm_tm A) (fv_tm_tm b0) z). exact Hx.
    + apply IHb. apply (@notin_union_r (fv_tm_tm A) (fv_tm_tm b0) z). exact Hx.
  - (* App *) f_equal.
    + apply IHa1. apply (@notin_union_l (fv_tm_tm a1) (fv_tm_tm b1) z). exact Hx.
    + apply IHb1. apply (@notin_union_r (fv_tm_tm a1) (fv_tm_tm b1) z). exact Hx.
  - (* Var_f *)
    destruct (CoqEqDec.eq_dec xv z) as [E|E].
    + subst xv. exfalso. apply Hx. simpl. apply AtomSetImpl.singleton_2. reflexivity.
    + reflexivity.
  - (* Sum *) f_equal.
    + apply IHA1. apply (@notin_union_l (fv_tm_tm A1) (fv_tm_tm A2) z). exact Hx.
    + apply IHA2. apply (@notin_union_r (fv_tm_tm A1) (fv_tm_tm A2) z). exact Hx.
  - (* Inj1 *) f_equal. apply IHa1. exact Hx.
  - (* Inj2 *) f_equal. apply IHa1. exact Hx.
  - (* Case *) f_equal.
    + apply IHa1.
      apply (@notin_union_l (fv_tm_tm a1) (fv_tm_tm b1 \u fv_tm_tm b2) z). exact Hx.
    + apply IHb1.
      apply (@notin_union_l (fv_tm_tm b1) (fv_tm_tm b2) z).
      apply (@notin_union_r (fv_tm_tm a1) (fv_tm_tm b1 \u fv_tm_tm b2) z). exact Hx.
    + apply IHb2.
      apply (@notin_union_r (fv_tm_tm b1) (fv_tm_tm b2) z).
      apply (@notin_union_r (fv_tm_tm a1) (fv_tm_tm b1 \u fv_tm_tm b2) z). exact Hx.
  - (* WSigma *) f_equal.
    + apply IHA. apply (@notin_union_l (fv_tm_tm A) (fv_tm_tm B) z). exact Hx.
    + apply IHB. apply (@notin_union_r (fv_tm_tm A) (fv_tm_tm B) z). exact Hx.
  - (* WPair *) f_equal.
    + apply IHa1. apply (@notin_union_l (fv_tm_tm a1) (fv_tm_tm b1) z). exact Hx.
    + apply IHb1. apply (@notin_union_r (fv_tm_tm a1) (fv_tm_tm b1) z). exact Hx.
  - (* LetPair *) f_equal.
    + apply IHa1. apply (@notin_union_l (fv_tm_tm a1) (fv_tm_tm b1) z). exact Hx.
    + apply IHb1. apply (@notin_union_r (fv_tm_tm a1) (fv_tm_tm b1) z). exact Hx.
  - (* SSigma *) f_equal.
    + apply IHA. apply (@notin_union_l (fv_tm_tm A) (fv_tm_tm B) z). exact Hx.
    + apply IHB. apply (@notin_union_r (fv_tm_tm A) (fv_tm_tm B) z). exact Hx.
  - (* SPair *) f_equal.
    + apply IHa1. apply (@notin_union_l (fv_tm_tm a1) (fv_tm_tm b1) z). exact Hx.
    + apply IHb1. apply (@notin_union_r (fv_tm_tm a1) (fv_tm_tm b1) z). exact Hx.
  - (* Proj1 *) f_equal. apply IHa1. exact Hx.
  - (* Proj2 *) f_equal. apply IHa1. exact Hx.
Qed.

Lemma Grade_remove_cons : forall (P:econtext) (g psi:grade) (a:tm) (x:atom),
  uniq P ->
  x \notin dom P ->
  x \notin fv_tm_tm a ->
  Grade ((x,g)::P) psi a ->
  Grade P psi a.
Proof.
  intros P g psi a x Hu Hxdom Hxf HG.
  pose proof (@Grade_subst ((x,g)::P) psi a HG x a_TmUnit g) as Hs.
  assert (Huext : uniq ((x,g)::P)).
  { apply (@uniq_cons grade x g P Hu Hxdom). }
  assert (Hb : binds x g ((x,g)::P)).
  { apply (@binds_cons_2 grade x x g g P (@Logic.eq_refl atom x) (@Logic.eq_refl grade g)). }
  assert (Hg : g <= psi -> Grade (remove_ec x ((x,g)::P)) psi a_TmUnit).
  { intro Hle. rewrite remove_ec_head_eq. apply G_TmUnit. exact Hu. }
  assert (Hl : ~ (g <= psi) -> lc_tm a_TmUnit) by (intro; constructor).
  specialize (Hs Huext Hb Hg Hl).
  rewrite remove_ec_head_eq in Hs.
  rewrite (@subst_tm_tm_fresh a_TmUnit x a Hxf) in Hs.
  exact Hs.
Qed.

Lemma fv_open_rec_keep : forall (B:tm) (k:nat) (u:tm) (z:atom),
  z \in fv_tm_tm B -> z \in fv_tm_tm (open_tm_wrt_tm_rec k u B).
Proof.
  induction B as
    [| |psi A IHA B IHB |psi A IHA b IHb |a IHa psi b IHb |s |n |xv
    |A1 IHA1 A2 IHA2 |a IHa |a IHa
    |psi a IHa b1 IHb1 b2 IHb2 |psi A IHA B IHB |a IHa psi b IHb
    |psi a IHa b IHb |psi A IHA B IHB |a IHa psi b IHb
    |psi a IHa |psi a IHa ];
    intros k u z H; simpl in *.
  - exfalso. eapply AtomSetImpl.empty_1; exact H.
  - exfalso. eapply AtomSetImpl.empty_1; exact H.
  - apply AtomSetImpl.union_1 in H as [H|H].
    + apply AtomSetImpl.union_2. apply IHA. exact H.
    + apply AtomSetImpl.union_3. apply IHB. exact H.
  - apply AtomSetImpl.union_1 in H as [H|H].
    + apply AtomSetImpl.union_2. apply IHA. exact H.
    + apply AtomSetImpl.union_3. apply IHb. exact H.
  - apply AtomSetImpl.union_1 in H as [H|H].
    + apply AtomSetImpl.union_2. apply IHa. exact H.
    + apply AtomSetImpl.union_3. apply IHb. exact H.
  - exfalso. eapply AtomSetImpl.empty_1; exact H.
  - exfalso. eapply AtomSetImpl.empty_1; exact H.
  - exact H.
  - apply AtomSetImpl.union_1 in H as [H|H].
    + apply AtomSetImpl.union_2. apply IHA1. exact H.
    + apply AtomSetImpl.union_3. apply IHA2. exact H.
  - apply IHa. exact H.
  - apply IHa. exact H.
  - apply AtomSetImpl.union_1 in H as [H|H].
    + apply AtomSetImpl.union_2. apply IHa. exact H.
    + apply AtomSetImpl.union_1 in H as [H|H].
      * apply AtomSetImpl.union_3. apply AtomSetImpl.union_2. apply IHb1. exact H.
      * apply AtomSetImpl.union_3. apply AtomSetImpl.union_3. apply IHb2. exact H.
  - apply AtomSetImpl.union_1 in H as [H|H].
    + apply AtomSetImpl.union_2. apply IHA. exact H.
    + apply AtomSetImpl.union_3. apply IHB. exact H.
  - apply AtomSetImpl.union_1 in H as [H|H].
    + apply AtomSetImpl.union_2. apply IHa. exact H.
    + apply AtomSetImpl.union_3. apply IHb. exact H.
  - apply AtomSetImpl.union_1 in H as [H|H].
    + apply AtomSetImpl.union_2. apply IHa. exact H.
    + apply AtomSetImpl.union_3. apply IHb. exact H.
  - apply AtomSetImpl.union_1 in H as [H|H].
    + apply AtomSetImpl.union_2. apply IHA. exact H.
    + apply AtomSetImpl.union_3. apply IHB. exact H.
  - apply AtomSetImpl.union_1 in H as [H|H].
    + apply AtomSetImpl.union_2. apply IHa. exact H.
    + apply AtomSetImpl.union_3. apply IHb. exact H.
  - apply IHa. exact H.
  - apply IHa. exact H.
Qed.

Lemma fv_open_notin : forall (B u:tm) (z:atom),
  z \notin fv_tm_tm B -> z \notin fv_tm_tm u ->
  z \notin fv_tm_tm (open_tm_wrt_tm B u).
Proof.
  intros B u z HB Hu Hin.
  apply (@fv_open_out B u z) in Hin as [Hin|Hin]; contradiction.
Qed.

Lemma Step_fv : forall (a b:tm), Step a b -> forall z, z \notin fv_tm_tm a -> z \notin fv_tm_tm b.
Proof.
  intros a b Hstep.
  induction Hstep as
    [a psi b a' Hlcb Hstep IH
    |psi A a b HlcA HlcAbs Hlcb
    |psi a b1 b2 a' Hlcb1 Hlcb2 Hstep IH
    |psi a b1 b2 Hlcb2 Hlcb1 Hlca
    |psi a b1 b2 Hlcb1 Hlcb2 Hlca
    |psi a a' Hstep IH
    |psi a a' Hstep IH
    |psi a1 a2 Hlca2 Hlca1
    |psi a1 a2 Hlca1 Hlca2
    |psi a b a' HlcLP Hstep IH
    |psi a1 a2 b HlcLP Hlca1 Hlca2];
    intros z Hz; simpl in *.
  - (* AppCong *)
    apply notin_union.
    + apply IH. exact (@notin_union_l (fv_tm_tm a) (fv_tm_tm b) z Hz).
    + exact (@notin_union_r (fv_tm_tm a) (fv_tm_tm b) z Hz).
  - (* Beta *)
    apply (@fv_open_notin a b z).
    + exact (@notin_union_r (fv_tm_tm A) (fv_tm_tm a) z
               (@notin_union_l (fv_tm_tm A \u fv_tm_tm a) (fv_tm_tm b) z Hz)).
    + exact (@notin_union_r (fv_tm_tm A \u fv_tm_tm a) (fv_tm_tm b) z Hz).
  - (* CaseCong *)
    apply notin_union.
    + apply IH. exact (@notin_union_l (fv_tm_tm a) (fv_tm_tm b1 \u fv_tm_tm b2) z Hz).
    + apply notin_union.
      * exact (@notin_union_l (fv_tm_tm b1) (fv_tm_tm b2) z
                 (@notin_union_r (fv_tm_tm a) (fv_tm_tm b1 \u fv_tm_tm b2) z Hz)).
      * exact (@notin_union_r (fv_tm_tm b1) (fv_tm_tm b2) z
                 (@notin_union_r (fv_tm_tm a) (fv_tm_tm b1 \u fv_tm_tm b2) z Hz)).
  - (* Case1Beta *)
    apply notin_union.
    + exact (@notin_union_l (fv_tm_tm b1) (fv_tm_tm b2) z
               (@notin_union_r (fv_tm_tm a) (fv_tm_tm b1 \u fv_tm_tm b2) z Hz)).
    + exact (@notin_union_l (fv_tm_tm a) (fv_tm_tm b1 \u fv_tm_tm b2) z Hz).
  - (* Case2Beta *)
    apply notin_union.
    + exact (@notin_union_r (fv_tm_tm b1) (fv_tm_tm b2) z
               (@notin_union_r (fv_tm_tm a) (fv_tm_tm b1 \u fv_tm_tm b2) z Hz)).
    + exact (@notin_union_l (fv_tm_tm a) (fv_tm_tm b1 \u fv_tm_tm b2) z Hz).
  - (* Proj1Cong *) exact (IH z Hz).
  - (* Proj2Cong *) exact (IH z Hz).
  - (* Proj1Beta *) exact (@notin_union_l (fv_tm_tm a1) (fv_tm_tm a2) z Hz).
  - (* Proj2Beta *) exact (@notin_union_r (fv_tm_tm a1) (fv_tm_tm a2) z Hz).
  - (* LetPairCong *)
    apply notin_union.
    + apply IH. exact (@notin_union_l (fv_tm_tm a) (fv_tm_tm b) z Hz).
    + exact (@notin_union_r (fv_tm_tm a) (fv_tm_tm b) z Hz).
  - (* LetPairBeta *)
    apply notin_union.
    + apply (@fv_open_notin b a1 z).
      * exact (@notin_union_r (fv_tm_tm a1 \u fv_tm_tm a2) (fv_tm_tm b) z Hz).
      * exact (@notin_union_l (fv_tm_tm a1) (fv_tm_tm a2) z
                 (@notin_union_l (fv_tm_tm a1 \u fv_tm_tm a2) (fv_tm_tm b) z Hz)).
    + exact (@notin_union_r (fv_tm_tm a1) (fv_tm_tm a2) z
               (@notin_union_l (fv_tm_tm a1 \u fv_tm_tm a2) (fv_tm_tm b) z Hz)).
Qed.

Lemma Steps_fv : forall (a b:tm), Steps a b -> forall z,
  z \notin fv_tm_tm a -> z \notin fv_tm_tm b.
Proof.
  intros a b Hsteps.
  induction Hsteps as [a0 |a0 b0 c0 S Hsteps IH].
  - intros z Hz. exact Hz.
  - intros z Hz. apply IH. apply (@Step_fv a0 b0 S z Hz).
Qed.

Lemma Grade_remove_ec : forall (Q:econtext) (psi:grade) (a:tm) (x:atom) (g:grade),
  uniq Q ->
  binds x g Q ->
  x \notin fv_tm_tm a ->
  Grade Q psi a ->
  Grade (remove_ec x Q) psi a.
Proof.
  intros Q psi a x g Hu Hb Hfv HG.
  pose proof (@Grade_subst Q psi a HG x a_TmUnit g Hu Hb) as Hs.
  assert (Hg : g <= psi -> Grade (remove_ec x Q) psi a_TmUnit).
  { intro Hle. apply G_TmUnit. apply uniq_remove_ec. exact Hu. }
  assert (Hl : ~ (g <= psi) -> lc_tm a_TmUnit) by (intro; constructor).
  specialize (Hs Hg Hl).
  rewrite (@subst_tm_tm_fresh a_TmUnit x a Hfv) in Hs.
  exact Hs.
Qed.

Lemma Grade_remove_cons' : forall (P:econtext) (g psi:grade) (a:tm) (x:atom),
  uniq P ->
  x \notin dom P ->
  x \notin fv_tm_tm a ->
  Grade ((x,g)::P) psi a ->
  Grade P psi a.
Proof.
  intros. rewrite <- (@remove_ec_head_eq x g P).
  eapply Grade_remove_ec.
  - apply (@uniq_cons grade x g P H H0).
  - apply (@binds_cons_2 grade x x g g P (@Logic.eq_refl atom x) (@Logic.eq_refl grade g)).
  - exact H1.
  - exact H2.
Qed.

Lemma open_rec_lc_at : forall (B:tm) (n:nat), lc_at n B ->
  forall (k:nat) (a:tm), (n <= k)%nat -> open_tm_wrt_tm_rec k a B = B.
Proof.
  induction B as
    [| |psi A IHA B IHB |psi A IHA b IHb |a1 IHa1 psi b1 IHb1 |s |m |xv
    |A1 IHA1 A2 IHA2 |a1 IHa1 |a1 IHa1
    |psi a1 IHa1 b1 IHb1 b2 IHb2 |psi A IHA B IHB |a1 IHa1 psi b1 IHb1
    |psi a1 IHa1 b1 IHb1 |psi A IHA B IHB |a1 IHa1 psi b1 IHb1
    |psi a1 IHa1 |psi a1 IHa1 ];
    intros n Hn k a Hk; simpl.
  - reflexivity.
  - reflexivity.
  - destruct Hn as [HA HB]. f_equal.
    + exact (IHA n HA k a Hk).
    + exact (IHB (S n) HB (S k) a (le_n_S _ _ Hk)).
  - destruct Hn as [HA Hb]. f_equal.
    + exact (IHA n HA k a Hk).
    + exact (IHb (S n) Hb (S k) a (le_n_S _ _ Hk)).
  - destruct Hn as [Ha Hb]. f_equal.
    + exact (IHa1 n Ha k a Hk).
    + exact (IHb1 n Hb k a Hk).
  - reflexivity.
  - simpl in Hn. assert (Nat.lt m k) by lia.
    destruct (lt_eq_lt_dec m k) as [[?|?]|?]; try lia; reflexivity.
  - reflexivity.
  - destruct Hn as [HA1 HA2]. f_equal.
    + exact (IHA1 n HA1 k a Hk).
    + exact (IHA2 n HA2 k a Hk).
  - f_equal. exact (IHa1 n Hn k a Hk).
  - f_equal. exact (IHa1 n Hn k a Hk).
  - destruct Hn as [Ha [Hb1 Hb2]]. f_equal.
    + exact (IHa1 n Ha k a Hk).
    + exact (IHb1 n Hb1 k a Hk).
    + exact (IHb2 n Hb2 k a Hk).
  - destruct Hn as [HA HB]. f_equal.
    + exact (IHA n HA k a Hk).
    + exact (IHB (S n) HB (S k) a (le_n_S _ _ Hk)).
  - destruct Hn as [Ha Hb]. f_equal.
    + exact (IHa1 n Ha k a Hk).
    + exact (IHb1 n Hb k a Hk).
  - destruct Hn as [Ha Hb]. f_equal.
    + exact (IHa1 n Ha k a Hk).
    + exact (IHb1 (S n) Hb (S k) a (le_n_S _ _ Hk)).
  - destruct Hn as [HA HB]. f_equal.
    + exact (IHA n HA k a Hk).
    + exact (IHB (S n) HB (S k) a (le_n_S _ _ Hk)).
  - destruct Hn as [Ha Hb]. f_equal.
    + exact (IHa1 n Ha k a Hk).
    + exact (IHb1 n Hb k a Hk).
  - f_equal. exact (IHa1 n Hn k a Hk).
  - f_equal. exact (IHa1 n Hn k a Hk).
Qed.

Lemma open_rec_lc_tm : forall (w:tm), lc_tm w ->
  forall (k:nat) (a:tm), open_tm_wrt_tm_rec k a w = w.
Proof.
  intros w Hw k a.
  apply (@open_rec_lc_at w 0 (@lc_tm_lc_at_0 w Hw) k a).
  apply Nat.le_0_l.
Qed.

Lemma subst_open_rec_comm_gen : forall (B:tm) (k:nat) (a w:tm) (x:atom),
  lc_tm w ->
  subst_tm_tm w x (open_tm_wrt_tm_rec k a B)
  = open_tm_wrt_tm_rec k (subst_tm_tm w x a) (subst_tm_tm w x B).
Proof.
  induction B as
    [| |psi A IHA B IHB |psi A IHA b IHb |a1 IHa1 psi b1 IHb1 |s |n |xv
    |A1 IHA1 A2 IHA2 |a1 IHa1 |a1 IHa1
    |psi a1 IHa1 b1 IHb1 b2 IHb2 |psi A IHA B IHB |a1 IHa1 psi b1 IHb1
    |psi a1 IHa1 b1 IHb1 |psi A IHA B IHB |a1 IHa1 psi b1 IHb1
    |psi a1 IHa1 |psi a1 IHa1 ];
    intros k a w x Hw; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (IHA k a w x Hw), (IHB (S k) a w x Hw). reflexivity.
  - rewrite (IHA k a w x Hw), (IHb (S k) a w x Hw). reflexivity.
  - rewrite (IHa1 k a w x Hw), (IHb1 k a w x Hw). reflexivity.
  - reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - destruct (CoqEqDec.eq_dec xv x) as [E|E]; simpl.
    + rewrite (@open_rec_lc_tm w Hw k (subst_tm_tm w x a)). reflexivity.
    + reflexivity.
  - rewrite (IHA1 k a w x Hw), (IHA2 k a w x Hw). reflexivity.
  - rewrite (IHa1 k a w x Hw). reflexivity.
  - rewrite (IHa1 k a w x Hw). reflexivity.
  - rewrite (IHa1 k a w x Hw), (IHb1 k a w x Hw), (IHb2 k a w x Hw). reflexivity.
  - rewrite (IHA k a w x Hw), (IHB (S k) a w x Hw). reflexivity.
  - rewrite (IHa1 k a w x Hw), (IHb1 k a w x Hw). reflexivity.
  - rewrite (IHa1 k a w x Hw), (IHb1 (S k) a w x Hw). reflexivity.
  - rewrite (IHA k a w x Hw), (IHB (S k) a w x Hw). reflexivity.
  - rewrite (IHa1 k a w x Hw), (IHb1 k a w x Hw). reflexivity.
  - rewrite (IHa1 k a w x Hw). reflexivity.
  - rewrite (IHa1 k a w x Hw). reflexivity.
Qed.

Lemma Step_subst : forall (a b:tm), Step a b ->
  forall (x:atom) (w:tm), lc_tm w -> Step (subst_tm_tm w x a) (subst_tm_tm w x b).
Proof.
  intros a b H. induction H; intros x w Hw; simpl.
  - eapply S_AppCong.
    + apply (@lc_subst_tm_tm b x w H Hw).
    + exact (IHStep x w Hw).
  - unfold open_tm_wrt_tm.
    rewrite (@subst_open_rec_comm_gen a 0 b w x Hw).
    eapply S_Beta.
    + apply (@lc_subst_tm_tm A x w H Hw).
    + apply (@lc_subst_tm_tm (a_Abs psi A a) x w H0 Hw).
    + apply (@lc_subst_tm_tm b x w H1 Hw).
  - eapply S_CaseCong.
    + apply (@lc_subst_tm_tm b1 x w H Hw).
    + apply (@lc_subst_tm_tm b2 x w H0 Hw).
    + exact (IHStep x w Hw).
  - eapply S_Case1Beta.
    + apply (@lc_subst_tm_tm b2 x w H Hw).
    + apply (@lc_subst_tm_tm b1 x w H0 Hw).
    + apply (@lc_subst_tm_tm a x w H1 Hw).
  - eapply S_Case2Beta.
    + apply (@lc_subst_tm_tm b1 x w H Hw).
    + apply (@lc_subst_tm_tm b2 x w H0 Hw).
    + apply (@lc_subst_tm_tm a x w H1 Hw).
  - eapply S_Proj1Cong. exact (IHStep x w Hw).
  - eapply S_Proj2Cong. exact (IHStep x w Hw).
  - eapply S_Proj1Beta.
    + apply (@lc_subst_tm_tm a2 x w H Hw).
    + apply (@lc_subst_tm_tm a1 x w H0 Hw).
  - eapply S_Proj2Beta.
    + apply (@lc_subst_tm_tm a1 x w H Hw).
    + apply (@lc_subst_tm_tm a2 x w H0 Hw).
  - eapply S_LetPairCong.
    + apply (@lc_subst_tm_tm (a_LetPair psi a b) x w H Hw).
    + exact (IHStep x w Hw).
  - unfold open_tm_wrt_tm.
    rewrite (@subst_open_rec_comm_gen b 0 a1 w x Hw).
    eapply S_LetPairBeta.
    + apply (@lc_subst_tm_tm (a_LetPair psi (a_WPair a1 psi a2) b) x w H Hw).
    + apply (@lc_subst_tm_tm a1 x w H0 Hw).
    + apply (@lc_subst_tm_tm a2 x w H1 Hw).
Qed.


Set Implicit Arguments.
Open Scope grade_scope.

Ltac fresh_subst_facts L C xv :=
  match goal with
  | Hz : ?z \notin (L \u (dom C \u {{xv}})) |- _ =>
      assert (HzL : z \notin L)
        by (apply (@notin_union_l L (dom C \u {{xv}}) z); exact Hz);
      assert (Hzdom' : z \notin (dom C \u {{xv}}))
        by (apply (@notin_union_r L (dom C \u {{xv}}) z); exact Hz);
      assert (Hzdom : z \notin dom C)
        by (apply (@notin_union_l (dom C) {{xv}} z); exact Hzdom');
      assert (Hzne : z <> xv)
        by (intro E; apply (@notin_union_r (dom C) {{xv}} z Hzdom');
            subst; apply AtomSetImpl.singleton_2; reflexivity)
  end.

Lemma DefEq_subst : forall (C:econtext) (psi:grade) (a b:tm),
  DefEq C psi a b ->
  forall xv w psib,
    uniq C -> binds xv psib C ->
    (psib <= psi -> Grade (remove_ec xv C) psi w) ->
    (~ (psib <= psi) -> lc_tm w) ->
    DefEq (remove_ec xv C) psi (subst_tm_tm w xv a) (subst_tm_tm w xv b).
Proof.
  intros C psi a b H. induction H using DefEq_mind
    with (P0 := fun (C:econtext) (psi phi0:grade) (a b:tm) (_:CDefEq C psi phi0 a b) =>
                 forall xv w psib,
                   uniq C -> binds xv psib C ->
                   (psib <= psi -> Grade (remove_ec xv C) psi w) ->
                   (~ (psib <= psi) -> lc_tm w) ->
                   CDefEq (remove_ec xv C) psi phi0
                     (subst_tm_tm w xv a) (subst_tm_tm w xv b)).
  all: intros xv w psib Hu Hb Hgrade Hlc; simpl.
  - (* Refl *) apply Eq_Refl. eapply Grade_subst; eassumption.
  - (* Trans *) eapply Eq_Trans.
    + exact (IHDefEq1 xv w psib Hu Hb Hgrade Hlc).
    + exact (IHDefEq2 xv w psib Hu Hb Hgrade Hlc).
  - (* Sym *) eapply Eq_Sym. exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
  - (* Beta *) eapply Eq_Beta.
    + eapply Grade_subst; eassumption.
    + assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
      exact (@Step_subst a b s xv w Hlcw).
    + eapply Grade_subst; eassumption.
  - (* Pi *)
    eapply (@Eq_Pi (L \u (dom P \u {{xv}})) (remove_ec xv P) psi psi0
                   (subst_tm_tm w xv A1) (subst_tm_tm w xv B1)
                   (subst_tm_tm w xv A2) (subst_tm_tm w xv B2)).
    + exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
    + intros z Hz. fresh_subst_facts L P xv.
      assert (Huniq : uniq ((z,psi)::P)) by (apply uniq_push; assumption).
      assert (Hb' : binds xv psib ((z,psi)::P)) by (apply binds_cons; exact Hb).
      assert (Hgrade' : psib <= psi -> Grade ((z,psi)::remove_ec xv P) psi w).
      { intro Hle.
        exact (@Grade_weaken_cons (remove_ec xv P) psi w (Hgrade Hle) z psi
                 (@uniq_remove_ec P xv Hu) (@notin_dom_remove_ec P xv z Hzdom)). }
      rewrite <- (@remove_ec_head_neq xv z psi P Hzne) in Hgrade'.
      pose proof (H0 z HzL xv w psib Huniq Hb' Hgrade' Hlc) as Hres.
      rewrite (@remove_ec_head_neq_not xv z psi P Hzne) in Hres.
      assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
      rewrite (@subst_open_comm0 B1 xv w z Hlcw Hzne) in Hres.
      rewrite (@subst_open_comm0 B2 xv w z Hlcw Hzne) in Hres.
      exact Hres.
  - (* Abs *)
    eapply (@Eq_Abs (L \u (dom P \u {{xv}})) (remove_ec xv P) psi psi0
                   (subst_tm_tm w xv A1) (subst_tm_tm w xv b1)
                   (subst_tm_tm w xv A2) (subst_tm_tm w xv b2)).
    + exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
    + intros z Hz. fresh_subst_facts L P xv.
      assert (Huniq : uniq ((z,psi0)::P)) by (apply uniq_push; assumption).
      assert (Hb' : binds xv psib ((z,psi0)::P)) by (apply binds_cons; exact Hb).
      assert (Hgrade' : psib <= psi -> Grade ((z,psi0)::remove_ec xv P) psi w).
      { intro Hle.
        exact (@Grade_weaken_cons (remove_ec xv P) psi w (Hgrade Hle) z psi0
                 (@uniq_remove_ec P xv Hu) (@notin_dom_remove_ec P xv z Hzdom)). }
      rewrite <- (@remove_ec_head_neq xv z psi0 P Hzne) in Hgrade'.
      pose proof (H z HzL xv w psib Huniq Hb' Hgrade' Hlc) as Hres.
      rewrite (@remove_ec_head_neq_not xv z psi0 P Hzne) in Hres.
      assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
      rewrite (@subst_open_comm0 b1 xv w z Hlcw Hzne) in Hres.
      rewrite (@subst_open_comm0 b2 xv w z Hlcw Hzne) in Hres.
      exact Hres.
  - (* App *)
    eapply (@Eq_App (remove_ec xv P) psi (subst_tm_tm w xv b1) psi0
                    (subst_tm_tm w xv a1) (subst_tm_tm w xv b2) (subst_tm_tm w xv a2)).
    + exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
    + exact (IHDefEq0 xv w psib Hu Hb Hgrade Hlc).
  - (* PiFst *) eapply Eq_PiFst. exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
  - (* PiSnd *)
    assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
    unfold open_tm_wrt_tm.
    rewrite (@subst_open_rec_comm_gen B1 0 a1 w xv Hlcw).
    rewrite (@subst_open_rec_comm_gen B2 0 a2 w xv Hlcw).
    eapply (@Eq_PiSnd (remove_ec xv P) psi (subst_tm_tm w xv B1)
                      (subst_tm_tm w xv a1) (subst_tm_tm w xv B2)
                      (subst_tm_tm w xv a2) psi0
                      (subst_tm_tm w xv A1) (subst_tm_tm w xv A2)).
    + exact (IHDefEq1 xv w psib Hu Hb Hgrade Hlc).
    + exact (IHDefEq2 xv w psib Hu Hb Hgrade Hlc).
  - (* WSigma *)
    eapply (@Eq_WSigma (L \u (dom P \u {{xv}})) (remove_ec xv P) psi psi0
                   (subst_tm_tm w xv A1) (subst_tm_tm w xv B1)
                   (subst_tm_tm w xv A2) (subst_tm_tm w xv B2)).
    + exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
    + intros z Hz. fresh_subst_facts L P xv.
      assert (Huniq : uniq ((z,psi)::P)) by (apply uniq_push; assumption).
      assert (Hb' : binds xv psib ((z,psi)::P)) by (apply binds_cons; exact Hb).
      assert (Hgrade' : psib <= psi -> Grade ((z,psi)::remove_ec xv P) psi w).
      { intro Hle.
        exact (@Grade_weaken_cons (remove_ec xv P) psi w (Hgrade Hle) z psi
                 (@uniq_remove_ec P xv Hu) (@notin_dom_remove_ec P xv z Hzdom)). }
      rewrite <- (@remove_ec_head_neq xv z psi P Hzne) in Hgrade'.
      pose proof (H0 z HzL xv w psib Huniq Hb' Hgrade' Hlc) as Hres.
      rewrite (@remove_ec_head_neq_not xv z psi P Hzne) in Hres.
      assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
      rewrite (@subst_open_comm0 B1 xv w z Hlcw Hzne) in Hres.
      rewrite (@subst_open_comm0 B2 xv w z Hlcw Hzne) in Hres.
      exact Hres.
  - (* WSigmaFst *) eapply Eq_WSigmaFst. exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
  - (* WSigmaSnd *)
    assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
    unfold open_tm_wrt_tm.
    rewrite (@subst_open_rec_comm_gen B1 0 a w xv Hlcw).
    rewrite (@subst_open_rec_comm_gen B2 0 a w xv Hlcw).
    eapply (@Eq_WSigmaSnd (remove_ec xv P) psi (subst_tm_tm w xv B1)
                          (subst_tm_tm w xv a) (subst_tm_tm w xv B2) psi0
                          (subst_tm_tm w xv A1) (subst_tm_tm w xv A2)).
    + exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
    + exact (@Grade_subst P psi a g xv w psib Hu Hb Hgrade Hlc).
  - (* WPair *)
    eapply (@Eq_WPair (remove_ec xv P) psi (subst_tm_tm w xv a1) psi0
                      (subst_tm_tm w xv b1) (subst_tm_tm w xv a2) (subst_tm_tm w xv b2)).
    + exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
    + exact (IHDefEq0 xv w psib Hu Hb Hgrade Hlc).
  - (* LetPair *)
    eapply (@Eq_LetPair (L \u (dom P \u {{xv}})) (remove_ec xv P) psi psi0
                   (subst_tm_tm w xv a1) (subst_tm_tm w xv b1)
                   (subst_tm_tm w xv a2) (subst_tm_tm w xv b2)).
    + exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
    + intros z Hz. fresh_subst_facts L P xv.
      assert (Huniq : uniq ((z,psi0)::P)) by (apply uniq_push; assumption).
      assert (Hb' : binds xv psib ((z,psi0)::P)) by (apply binds_cons; exact Hb).
      assert (Hgrade' : psib <= psi -> Grade ((z,psi0)::remove_ec xv P) psi w).
      { intro Hle.
        exact (@Grade_weaken_cons (remove_ec xv P) psi w (Hgrade Hle) z psi0
                 (@uniq_remove_ec P xv Hu) (@notin_dom_remove_ec P xv z Hzdom)). }
      rewrite <- (@remove_ec_head_neq xv z psi0 P Hzne) in Hgrade'.
      pose proof (H0 z HzL xv w psib Huniq Hb' Hgrade' Hlc) as Hres.
      rewrite (@remove_ec_head_neq_not xv z psi0 P Hzne) in Hres.
      assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
      rewrite (@subst_open_comm0 b1 xv w z Hlcw Hzne) in Hres.
      rewrite (@subst_open_comm0 b2 xv w z Hlcw Hzne) in Hres.
      exact Hres.
  - (* SSigma *)
    eapply (@Eq_SSigma (L \u (dom P \u {{xv}})) (remove_ec xv P) psi psi0
                   (subst_tm_tm w xv A1) (subst_tm_tm w xv B1)
                   (subst_tm_tm w xv A2) (subst_tm_tm w xv B2)).
    + exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
    + intros z Hz. fresh_subst_facts L P xv.
      assert (Huniq : uniq ((z,psi)::P)) by (apply uniq_push; assumption).
      assert (Hb' : binds xv psib ((z,psi)::P)) by (apply binds_cons; exact Hb).
      assert (Hgrade' : psib <= psi -> Grade ((z,psi)::remove_ec xv P) psi w).
      { intro Hle.
        exact (@Grade_weaken_cons (remove_ec xv P) psi w (Hgrade Hle) z psi
                 (@uniq_remove_ec P xv Hu) (@notin_dom_remove_ec P xv z Hzdom)). }
      rewrite <- (@remove_ec_head_neq xv z psi P Hzne) in Hgrade'.
      pose proof (H0 z HzL xv w psib Huniq Hb' Hgrade' Hlc) as Hres.
      rewrite (@remove_ec_head_neq_not xv z psi P Hzne) in Hres.
      assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
      rewrite (@subst_open_comm0 B1 xv w z Hlcw Hzne) in Hres.
      rewrite (@subst_open_comm0 B2 xv w z Hlcw Hzne) in Hres.
      exact Hres.
  - (* SSigmaFst *) eapply Eq_SSigmaFst. exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
  - (* SSigmaSnd *)
    assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) psi psib w); assumption).
    unfold open_tm_wrt_tm.
    rewrite (@subst_open_rec_comm_gen B1 0 a1 w xv Hlcw).
    rewrite (@subst_open_rec_comm_gen B2 0 a2 w xv Hlcw).
    eapply (@Eq_SSigmaSnd (remove_ec xv P) psi (subst_tm_tm w xv B1)
                          (subst_tm_tm w xv a1) (subst_tm_tm w xv B2)
                          (subst_tm_tm w xv a2) psi0
                          (subst_tm_tm w xv A1) (subst_tm_tm w xv A2)).
    + exact (IHDefEq1 xv w psib Hu Hb Hgrade Hlc).
    + exact (IHDefEq2 xv w psib Hu Hb Hgrade Hlc).
  - (* SPair *)
    eapply (@Eq_SPair (remove_ec xv P) psi (subst_tm_tm w xv a1) psi0
                      (subst_tm_tm w xv b1) (subst_tm_tm w xv a2) (subst_tm_tm w xv b2)).
    + exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
    + exact (IHDefEq0 xv w psib Hu Hb Hgrade Hlc).
  - (* Proj1 *) eapply Eq_Proj1.
    + exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
    + assumption.
  - (* Proj2 *) eapply Eq_Proj2. exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
  - (* Sum *)
    eapply (@Eq_Sum (remove_ec xv P) psi (subst_tm_tm w xv A1) (subst_tm_tm w xv A2)
                    (subst_tm_tm w xv A1') (subst_tm_tm w xv A2')).
    + exact (IHDefEq1 xv w psib Hu Hb Hgrade Hlc).
    + exact (IHDefEq2 xv w psib Hu Hb Hgrade Hlc).
  - (* SumFst *) eapply Eq_SumFst. exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
  - (* SumSnd *) eapply Eq_SumSnd. exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
  - (* Inj1 *) eapply Eq_Inj1. exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
  - (* Inj2 *) eapply Eq_Inj2. exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
  - (* Case *)
    eapply (@Eq_Case (remove_ec xv P) psi psi0
                     (subst_tm_tm w xv a) (subst_tm_tm w xv b1) (subst_tm_tm w xv b2)
                     (subst_tm_tm w xv a') (subst_tm_tm w xv b1') (subst_tm_tm w xv b2')).
    + exact (IHDefEq1 xv w psib Hu Hb Hgrade Hlc).
    + exact (IHDefEq2 xv w psib Hu Hb Hgrade Hlc).
    + exact (IHDefEq3 xv w psib Hu Hb Hgrade Hlc).
    + assumption.
  - (* TyUnit *) apply Eq_TyUnit. apply uniq_remove_ec. exact Hu.
  - (* TmUnit *) apply Eq_TmUnit. apply uniq_remove_ec. exact Hu.
  - (* SubstIrrel *)
    assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) phi psib w); assumption).
    unfold open_tm_wrt_tm.
    rewrite (@subst_open_rec_comm_gen b1 0 a1 w xv Hlcw).
    rewrite (@subst_open_rec_comm_gen b2 0 a2 w xv Hlcw).
    eapply (@Eq_SubstIrrel (L \u (dom P \u {{xv}})) (remove_ec xv P) phi
                            (subst_tm_tm w xv b1) (subst_tm_tm w xv a1)
                            (subst_tm_tm w xv b2) (subst_tm_tm w xv a2) psi).
    + exact (@lc_subst_tm_tm a1 xv w l Hlcw).
    + exact (@lc_subst_tm_tm a2 xv w l0 Hlcw).
    + exact I.
    + exact I.
    + intros z Hz. fresh_subst_facts L P xv.
      assert (Huniq : uniq ((z,psi)::P)) by (apply uniq_push; assumption).
      assert (Hb' : binds xv psib ((z,psi)::P)) by (apply binds_cons; exact Hb).
      assert (Hgrade' : psib <= phi -> Grade ((z,psi)::remove_ec xv P) phi w).
      { intro Hle.
        exact (@Grade_weaken_cons (remove_ec xv P) phi w (Hgrade Hle) z psi
                 (@uniq_remove_ec P xv Hu) (@notin_dom_remove_ec P xv z Hzdom)). }
      rewrite <- (@remove_ec_head_neq xv z psi P Hzne) in Hgrade'.
      pose proof (H z HzL xv w psib Huniq Hb' Hgrade' Hlc) as Hres.
      rewrite (@remove_ec_head_neq_not xv z psi P Hzne) in Hres.
      rewrite (@subst_open_comm0 b1 xv w z Hlcw Hzne) in Hres.
      rewrite (@subst_open_comm0 b2 xv w z Hlcw Hzne) in Hres.
      exact Hres.
    + exact n.
  - (* CDefEq_Leq *) eapply CDefEq_Leq.
    + exact i.
    + exact (IHDefEq xv w psib Hu Hb Hgrade Hlc).
  - (* CDefEq_Nleq *) eapply CDefEq_Nleq.
    + assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) phi psib w); assumption).
      exact (@lc_subst_tm_tm a xv w l Hlcw).
    + assert (Hlcw : lc_tm w) by (apply (@lc_from_side (remove_ec xv P) phi psib w); assumption).
      exact (@lc_subst_tm_tm b xv w l0 Hlcw).
    + exact n.
    + apply uniq_remove_ec. exact u.
Qed.

Set Implicit Arguments.
Open Scope grade_scope.

Lemma DefEq_remove_ec : forall (C:econtext) (phi:grade) (a b:tm),
  DefEq C phi a b ->
  forall xv g, uniq C -> binds xv g C ->
    xv \notin fv_tm_tm a -> xv \notin fv_tm_tm b ->
    DefEq (remove_ec xv C) phi a b.
Proof.
  intros C phi a b H xv g Hu Hb Ha Hbv.
  assert (Hgrade : g <= phi -> Grade (remove_ec xv C) phi a_TmUnit).
  { intro Hle. apply G_TmUnit. apply uniq_remove_ec. exact Hu. }
  assert (Hlc : ~ g <= phi -> lc_tm a_TmUnit).
  { intro Hn. exact lc_a_TmUnit. }
  pose proof (@DefEq_subst C phi a b H xv a_TmUnit g Hu Hb Hgrade Hlc) as Hs.
  rewrite (@subst_tm_tm_fresh a_TmUnit xv a Ha) in Hs.
  rewrite (@subst_tm_tm_fresh a_TmUnit xv b Hbv) in Hs.
  exact Hs.
Qed.

Lemma CDefEq_remove_ec : forall (C:econtext) (phi phi0:grade) (a b:tm),
  CDefEq C phi phi0 a b ->
  forall xv g, uniq C -> binds xv g C ->
    xv \notin fv_tm_tm a -> xv \notin fv_tm_tm b ->
    CDefEq (remove_ec xv C) phi phi0 a b.
Proof.
  intros C phi phi0 a b H.
  destruct H as [C phi phi0 a b Hle Hde
                |C phi phi0 a b Hlca Hlcb Hn Hu].
  - intros xv g Hu' Hb Ha Hbv.
    apply CDefEq_Leq.
    + exact Hle.
    + eapply DefEq_remove_ec; eassumption.
  - intros xv g Hu' Hb Ha Hbv.
    apply CDefEq_Nleq.
    + assumption.
    + assumption.
    + exact Hn.
    + apply uniq_remove_ec. exact Hu'.
Qed.

Set Implicit Arguments.
Open Scope grade_scope.

Lemma uniq_cons_head_notin : forall (A:Type) (x:atom) (a:A) (C:list (atom*A)),
  uniq ((x,a)::C) -> x \notin dom C.
Proof. intros. inversion H. assumption. Qed.

Lemma uniq_cons_tail : forall (A:Type) (x:atom) (a:A) (C:list (atom*A)),
  uniq ((x,a)::C) -> uniq C.
Proof. intros. inversion H. assumption. Qed.

Lemma notin_fv_open_f : forall (B:tm) (y:atom) (x:atom),
  x \notin fv_tm_tm B -> y <> x ->
  x \notin fv_tm_tm (open_tm_wrt_tm B (a_Var_f y)).
Proof.
  intros B y x HxB Hyx.
  apply fv_open_notin; [exact HxB |].
  intro HH. apply AtomSetImpl.singleton_1 in HH. exact (Hyx HH).
Qed.

Lemma VM_remove_ec : forall (C:econtext) (phi:grade) (a b:tm),
  VM C phi a b ->
  forall x gr, uniq C -> binds x gr C ->
    x \notin fv_tm_tm a -> x \notin fv_tm_tm b ->
    VM (remove_ec x C) phi a b.
Proof.
  intros C phi a b H.
  induction H using VM_mut_ind
    with (P := fun (C:econtext) (phi:grade) (a b:tm) (_:R C phi a b) =>
                 forall x gr, uniq C -> binds x gr C ->
                   x \notin fv_tm_tm a -> x \notin fv_tm_tm b ->
                   R (remove_ec x C) phi a b)
         (P0 := fun (C:econtext) (phi:grade) (a b:tm) (_:VM C phi a b) =>
                  forall x gr, uniq C -> binds x gr C ->
                    x \notin fv_tm_tm a -> x \notin fv_tm_tm b ->
                    VM (remove_ec x C) phi a b).
  all: intros x gr Hu Hb Ha Hbv.
  - (* R_intro *)
    apply R_intro.
    + exact (@DefEq_remove_ec P phi a b d x gr Hu Hb Ha Hbv).
    + exact (@Grade_remove_ec P phi a x gr Hu Hb Ha g).
    + exact (@Grade_remove_ec P phi b x gr Hu Hb Hbv g0).
    + exact l.
    + exact l0.
    + exact i.
    + intros vv ww Vv Sav Vw Sbw.
      apply (H vv ww Vv Sav Vw Sbw x gr Hu Hb).
      * apply (@Steps_fv a vv Sav x Ha).
      * apply (@Steps_fv b ww Sbw x Hbv).
  - (* VM_Type *) apply VM_Type.
  - (* VM_Unit *) apply VM_Unit.
  - (* VM_Pi *)
    apply VM_Pi.
    + apply (IHVM x gr Hu Hb).
      * intro HH. apply Ha. simpl. apply AtomSetImpl.union_2. exact HH.
      * intro HH. apply Hbv. simpl. apply AtomSetImpl.union_2. exact HH.
    + intros y.
      assert (Huniq : uniq ((y,phi)::P)).
      { exact (@Grade_uniq ((y,phi)::P) phi (open_tm_wrt_tm B (a_Var_f y))
               (@R_grade_left ((y,phi)::P) phi _ _ (r0 y))). }
      assert (Hyx : y <> x).
      { intro E. subst y.
        apply (@uniq_cons_head_notin grade x phi P Huniq).
        eapply binds_In. exact Hb. }
      assert (Hb' : binds x gr ((y,phi)::P)) by (apply binds_cons; exact Hb).
      assert (HxB : x \notin fv_tm_tm B).
      { intro HH. apply Ha. simpl. apply AtomSetImpl.union_3. exact HH. }
      assert (HxB' : x \notin fv_tm_tm B').
      { intro HH. apply Hbv. simpl. apply AtomSetImpl.union_3. exact HH. }
      assert (Hxby : x \notin fv_tm_tm (open_tm_wrt_tm B (a_Var_f y)))
        by (apply notin_fv_open_f; assumption).
      assert (Hxby' : x \notin fv_tm_tm (open_tm_wrt_tm B' (a_Var_f y)))
        by (apply notin_fv_open_f; assumption).
      pose proof (H y x gr Huniq Hb' Hxby Hxby') as Hbody.
      rewrite (@remove_ec_head_neq_not x y phi P Hyx) in Hbody.
      exact Hbody.
  - (* VM_WSigma *)
    apply VM_WSigma.
    + apply (IHVM x gr Hu Hb).
      * intro HH. apply Ha. simpl. apply AtomSetImpl.union_2. exact HH.
      * intro HH. apply Hbv. simpl. apply AtomSetImpl.union_2. exact HH.
    + intros y.
      assert (Huniq : uniq ((y,phi)::P)).
      { exact (@Grade_uniq ((y,phi)::P) phi (open_tm_wrt_tm B (a_Var_f y))
               (@R_grade_left ((y,phi)::P) phi _ _ (r0 y))). }
      assert (Hyx : y <> x).
      { intro E. subst y.
        apply (@uniq_cons_head_notin grade x phi P Huniq).
        eapply binds_In. exact Hb. }
      assert (Hb' : binds x gr ((y,phi)::P)) by (apply binds_cons; exact Hb).
      assert (HxB : x \notin fv_tm_tm B).
      { intro HH. apply Ha. simpl. apply AtomSetImpl.union_3. exact HH. }
      assert (HxB' : x \notin fv_tm_tm B').
      { intro HH. apply Hbv. simpl. apply AtomSetImpl.union_3. exact HH. }
      assert (Hxby : x \notin fv_tm_tm (open_tm_wrt_tm B (a_Var_f y)))
        by (apply notin_fv_open_f; assumption).
      assert (Hxby' : x \notin fv_tm_tm (open_tm_wrt_tm B' (a_Var_f y)))
        by (apply notin_fv_open_f; assumption).
      pose proof (H y x gr Huniq Hb' Hxby Hxby') as Hbody.
      rewrite (@remove_ec_head_neq_not x y phi P Hyx) in Hbody.
      exact Hbody.
  - (* VM_SSigma *)
    apply VM_SSigma.
    + apply (IHVM x gr Hu Hb).
      * intro HH. apply Ha. simpl. apply AtomSetImpl.union_2. exact HH.
      * intro HH. apply Hbv. simpl. apply AtomSetImpl.union_2. exact HH.
    + intros y.
      assert (Huniq : uniq ((y,phi)::P)).
      { exact (@Grade_uniq ((y,phi)::P) phi (open_tm_wrt_tm B (a_Var_f y))
               (@R_grade_left ((y,phi)::P) phi _ _ (r0 y))). }
      assert (Hyx : y <> x).
      { intro E. subst y.
        apply (@uniq_cons_head_notin grade x phi P Huniq).
        eapply binds_In. exact Hb. }
      assert (Hb' : binds x gr ((y,phi)::P)) by (apply binds_cons; exact Hb).
      assert (HxB : x \notin fv_tm_tm B).
      { intro HH. apply Ha. simpl. apply AtomSetImpl.union_3. exact HH. }
      assert (HxB' : x \notin fv_tm_tm B').
      { intro HH. apply Hbv. simpl. apply AtomSetImpl.union_3. exact HH. }
      assert (Hxby : x \notin fv_tm_tm (open_tm_wrt_tm B (a_Var_f y)))
        by (apply notin_fv_open_f; assumption).
      assert (Hxby' : x \notin fv_tm_tm (open_tm_wrt_tm B' (a_Var_f y)))
        by (apply notin_fv_open_f; assumption).
      pose proof (H y x gr Huniq Hb' Hxby Hxby') as Hbody.
      rewrite (@remove_ec_head_neq_not x y phi P Hyx) in Hbody.
      exact Hbody.
  - (* VM_Sum *)
    apply VM_Sum.
    + apply (IHVM x gr Hu Hb).
      * intro HH. apply Ha. simpl. apply AtomSetImpl.union_2. exact HH.
      * intro HH. apply Hbv. simpl. apply AtomSetImpl.union_2. exact HH.
    + apply (IHVM0 x gr Hu Hb).
      * intro HH. apply Ha. simpl. apply AtomSetImpl.union_3. exact HH.
      * intro HH. apply Hbv. simpl. apply AtomSetImpl.union_3. exact HH.
  - (* VM_Abs *)
    apply VM_Abs.
    intros y.
    assert (Huniq : uniq ((y,psi0)::P)).
    { exact (@Grade_uniq ((y,psi0)::P) phi (open_tm_wrt_tm b (a_Var_f y))
             (@R_grade_left ((y,psi0)::P) phi _ _ (r y))). }
    assert (Hyx : y <> x).
    { intro E. subst y.
      apply (@uniq_cons_head_notin grade x psi0 P Huniq).
      eapply binds_In. exact Hb. }
    assert (Hb' : binds x gr ((y,psi0)::P)) by (apply binds_cons; exact Hb).
    assert (Hxb : x \notin fv_tm_tm b).
    { intro HH. apply Ha. simpl. apply AtomSetImpl.union_3. exact HH. }
    assert (Hxb' : x \notin fv_tm_tm b').
    { intro HH. apply Hbv. simpl. apply AtomSetImpl.union_3. exact HH. }
    assert (Hxby : x \notin fv_tm_tm (open_tm_wrt_tm b (a_Var_f y)))
      by (apply notin_fv_open_f; assumption).
    assert (Hxby' : x \notin fv_tm_tm (open_tm_wrt_tm b' (a_Var_f y)))
      by (apply notin_fv_open_f; assumption).
    pose proof (H y x gr Huniq Hb' Hxby Hxby') as Hbody.
    rewrite (@remove_ec_head_neq_not x y psi0 P Hyx) in Hbody.
    exact Hbody.
  - (* VM_WPair *)
    apply VM_WPair.
    + intro i. apply (H i x gr Hu Hb).
      * intro HH. apply Ha. simpl. apply AtomSetImpl.union_2. exact HH.
      * intro HH. apply Hbv. simpl. apply AtomSetImpl.union_2. exact HH.
    + apply (IHVM x gr Hu Hb).
      * intro HH. apply Ha. simpl. apply AtomSetImpl.union_3. exact HH.
      * intro HH. apply Hbv. simpl. apply AtomSetImpl.union_3. exact HH.
  - (* VM_SPair *)
    apply VM_SPair.
    + intro i. apply (H i x gr Hu Hb).
      * intro HH. apply Ha. simpl. apply AtomSetImpl.union_2. exact HH.
      * intro HH. apply Hbv. simpl. apply AtomSetImpl.union_2. exact HH.
    + apply (IHVM x gr Hu Hb).
      * intro HH. apply Ha. simpl. apply AtomSetImpl.union_3. exact HH.
      * intro HH. apply Hbv. simpl. apply AtomSetImpl.union_3. exact HH.
  - (* VM_Inj1 *)
    apply VM_Inj1. apply (IHVM x gr Hu Hb).
    + intro HH. apply Ha. simpl. exact HH.
    + intro HH. apply Hbv. simpl. exact HH.
  - (* VM_Inj2 *)
    apply VM_Inj2. apply (IHVM x gr Hu Hb).
    + intro HH. apply Ha. simpl. exact HH.
    + intro HH. apply Hbv. simpl. exact HH.
  - (* VM_refl *)
    apply VM_refl.
    + exact v0.
    + exact (@Grade_remove_ec P phi v x gr Hu Hb Ha g).
Qed.

Lemma R_remove_ec : forall (C:econtext) (phi:grade) (a b:tm),
  R C phi a b ->
  forall x gr, uniq C -> binds x gr C ->
    x \notin fv_tm_tm a -> x \notin fv_tm_tm b ->
    R (remove_ec x C) phi a b.
Proof.
  intros C phi a b H.
  destruct H as [a0 b0 d g g0 l l0 i v].
  intros x gr Hu Hb Ha Hbv.
  apply R_intro.
  - exact (@DefEq_remove_ec C phi a0 b0 d x gr Hu Hb Ha Hbv).
  - exact (@Grade_remove_ec C phi a0 x gr Hu Hb Ha g).
  - exact (@Grade_remove_ec C phi b0 x gr Hu Hb Hbv g0).
  - exact l.
  - exact l0.
  - exact i.
  - intros vv ww Vv Sav Vw Sbw.
    apply (@VM_remove_ec C phi vv ww (v vv ww Vv Sav Vw Sbw) x gr Hu Hb
             (@Steps_fv a0 vv Sav x Ha) (@Steps_fv b0 ww Sbw x Hbv)).
Qed.

Set Implicit Arguments.
Open Scope grade_scope.

(* The target is equivalent to head/tag coherence on the two endpoints:
   [Consistent] can only fail when both endpoints are value types with
   different heads.  The prefix already contains [Consistent_total], which
   packages exactly this observation. *)
Theorem DefEq_Consistent_from_VtTag :
  (forall (P:econtext) (phi:grade) (a b:tm),
      DefEq P phi a b -> ValueType a -> ValueType b -> VtTag a b) ->
  forall S D A B, DefEq S D A B -> Consistent A B.
Proof.
  intros HVT S D A B H.
  apply Consistent_total.
  - exact (proj1 (@DefEq_lc S D A B H)).
  - exact (proj2 (@DefEq_lc S D A B H)).
  - intros HA HB. exact (HVT S D A B H HA HB).
Qed.

(* Restatement of the residual invariant as a named proposition. *)
Definition DefEq_VtTag_Coherence : Prop :=
  forall (P:econtext) (phi:grade) (a b:tm),
    DefEq P phi a b -> ValueType a -> ValueType b -> VtTag a b.

(* ============================================================ *)
(* Target                                                       *)
(* ============================================================ *)

Theorem DefEq_Consistent : forall S D A B, DefEq S D A B -> Consistent A B.
Proof.
  intros S D A B H.
