Require Import Metalib.Metatheory.

Require Import syntax_ott.

Require Import List.

Require Import Lia.

Import ListNotations.

Definition applyfs (fs : ls) (A : styp) :=
  fold_right (fun el acc =>
                match el with
                | st_ty A => styp_arrow A acc
                | st_la l => styp_rcd l acc
                end) A fs.

Lemma applyfs_app : forall (fs1 fs2:ls) (B:styp),
    applyfs (fs1 ++ fs2) B = applyfs fs1 (applyfs fs2 B).
Proof.
  intros fs1. induction fs1 as [|x xs IH]; intros fs2 B.
  - simpl. reflexivity.
  - destruct x as [A|l]; simpl; [rewrite IH | rewrite IH]; reflexivity.
Qed.

Lemma applyfs_snoc_ty : forall (fs:ls) (A B:styp),
    applyfs (fs ++ [st_ty A]) B = applyfs fs (styp_arrow A B).
Proof.
  intros. rewrite applyfs_app. simpl. reflexivity.
Qed.

Lemma applyfs_snoc_la : forall (fs:ls) (l:i) (B:styp),
    applyfs (fs ++ [st_la l]) B = applyfs fs (styp_rcd l B).
Proof.
  intros. rewrite applyfs_app. simpl. reflexivity.
Qed.

(* and_left / and_right: the source may be projected *)
Lemma ASub_and_l : forall (fs:ls) (A1 A2 B:styp) (c:co),
    ASub fs A1 B c -> exists c', ASub fs (styp_and A1 A2) B c'.
Proof.
  intros fs A1 A2 B c H. induction H.
  - eexists. apply A_andN1. apply A_nat.
  - eexists. apply A_andN1. apply A_rcdNat. exact H.
  - destruct IHASub as [c' Hc']. eexists. apply A_rcd. exact Hc'.
  - eexists. apply A_top.
  - destruct IHASub1 as [cc1 Hc1]. destruct IHASub2 as [cc2 Hc2].
    eexists. apply A_and; [exact Hc1 | exact Hc2].
  - destruct IHASub as [c' Hc']. eexists. apply A_arr. exact Hc'.
  - eexists. apply A_andN1. apply A_andN1. exact H.
  - eexists. apply A_andN1. apply A_andN2. exact H.
  - eexists. apply A_andN1. apply A_arrNat; [exact H | exact H0].
Qed.

Lemma ASub_and_r : forall (fs:ls) (A1 A2 B:styp) (c:co),
    ASub fs A2 B c -> exists c', ASub fs (styp_and A1 A2) B c'.
Proof.
  intros fs A1 A2 B c H. induction H.
  - eexists. apply A_andN2. apply A_nat.
  - eexists. apply A_andN2. apply A_rcdNat. exact H.
  - destruct IHASub as [c' Hc']. eexists. apply A_rcd. exact Hc'.
  - eexists. apply A_top.
  - destruct IHASub1 as [cc1 Hc1]. destruct IHASub2 as [cc2 Hc2].
    eexists. apply A_and; [exact Hc1 | exact Hc2].
  - destruct IHASub as [c' Hc']. eexists. apply A_arr. exact Hc'.
  - eexists. apply A_andN2. apply A_andN1. exact H.
  - eexists. apply A_andN2. apply A_andN2. exact H.
  - eexists. apply A_andN2. apply A_arrNat; [exact H | exact H0].
Qed.

(* lifting a derivation under an arrow constructor *)
Lemma ASub_arr_lift : forall (B:styp) (fs:ls) (B1 A1 A2:styp) (c1 c2:co),
    ASub nil B1 A1 c1 ->
    ASub fs A2 B c2 ->
    exists c, ASub (st_ty B1 :: fs) (styp_arrow A1 A2) B c.
Proof.
  induction B as [| |B1' IHB1 B2' IHB2|B1' IHB1 B2' IHB2|l B' IHB]; intros fs B1 A1 A2 c1 c2 H1 H2.
  - eexists. apply A_top.
  - eexists. apply A_arrNat; [exact H1 | exact H2].
  - inversion H2; subst; clear H2.
    match goal with HP : ASub _ _ B1' _ |- _ =>
      destruct (IHB1 fs B1 A1 A2 c1 _ H1 HP) as [r1 Hr1] end.
    match goal with HP : ASub _ _ B2' _ |- _ =>
      destruct (IHB2 fs B1 A1 A2 c1 _ H1 HP) as [r2 Hr2] end.
    eexists. apply A_and; [exact Hr1 | exact Hr2].
  - inversion H2; subst; clear H2.
    match goal with HP : ASub _ _ B2' _ |- _ =>
      destruct (IHB2 (fs ++ [st_ty B1']) B1 A1 A2 c1 _ H1 HP) as [r Hr] end.
    eexists. apply A_arr. simpl. exact Hr.
  - inversion H2; subst; clear H2.
    match goal with HP : ASub _ _ B' _ |- _ =>
      destruct (IHB (fs ++ [st_la l]) B1 A1 A2 c1 _ H1 HP) as [r Hr] end.
    eexists. apply A_rcd. simpl. exact Hr.
Qed.

(* lifting a derivation under a record constructor *)
Lemma ASub_rcd_lift : forall (B:styp) (fs:ls) (l:i) (A:styp) (c2:co),
    ASub fs A B c2 ->
    exists c, ASub (st_la l :: fs) (styp_rcd l A) B c.
Proof.
  induction B as [| |B1' IHB1 B2' IHB2|B1' IHB1 B2' IHB2|l' B' IHB]; intros fs l A c2 H2.
  - eexists. apply A_top.
  - eexists. apply A_rcdNat. exact H2.
  - inversion H2; subst; clear H2.
    match goal with HP : ASub _ _ B1' _ |- _ =>
      destruct (IHB1 fs l A _ HP) as [r1 Hr1] end.
    match goal with HP : ASub _ _ B2' _ |- _ =>
      destruct (IHB2 fs l A _ HP) as [r2 Hr2] end.
    eexists. apply A_and; [exact Hr1 | exact Hr2].
  - inversion H2; subst; clear H2.
    match goal with HP : ASub _ _ B2' _ |- _ =>
      destruct (IHB2 (fs ++ [st_ty B1']) l A _ HP) as [r Hr] end.
    eexists. apply A_arr. simpl. exact Hr.
  - inversion H2; subst; clear H2.
    match goal with HP : ASub _ _ B' _ |- _ =>
      destruct (IHB (fs ++ [st_la l']) l A _ HP) as [r Hr] end.
    eexists. apply A_rcd. simpl. exact Hr.
Qed.

(* reflexivity of the algorithmic judgment *)
Lemma ASub_refl : forall (A:styp), exists c, ASub nil A A c.
Proof.
  induction A as [| |A1 IHA1 A2 IHA2|A1 IHA1 A2 IHA2|l A IHA].
  - eexists. apply A_top.
  - eexists. apply A_nat.
  - destruct IHA1 as [c1 H1]. destruct IHA2 as [c2 H2].
    destruct (ASub_and_l nil A1 A2 A1 c1 H1) as [d1 Hd1].
    destruct (ASub_and_r nil A1 A2 A2 c2 H2) as [d2 Hd2].
    eexists. apply A_and; [exact Hd1 | exact Hd2].
  - destruct IHA1 as [c1 H1]. destruct IHA2 as [c2 H2].
    destruct (ASub_arr_lift A2 nil A1 A1 A2 c1 c2 H1 H2) as [c Hc].
    eexists. apply A_arr. exact Hc.
  - destruct IHA as [c H]. destruct (ASub_rcd_lift A nil l A c H) as [c' Hc'].
    eexists. apply A_rcd. exact Hc'.
Qed.

Lemma calTop_sound : forall (fs:ls),
    sub styp_top (applyfs fs styp_top) (calTop fs).
Proof.
  induction fs as [|x xs IH].
  - simpl. apply S_top.
  - destruct x as [A|l].
    + simpl. eapply S_trans with (A2 := styp_arrow A styp_top).
      * apply S_arr; [apply S_refl | exact IH].
      * eapply S_trans with (A2 := styp_arrow styp_top styp_top).
        -- apply S_arr; [apply S_top | apply S_top].
        -- eapply S_trans with (A2 := styp_top).
           ++ apply S_topArr.
           ++ apply S_top.
    + simpl. eapply S_trans with (A2 := styp_rcd l styp_top).
      * apply S_rcd. exact IH.
      * apply S_topRcd.
Qed.

Lemma calAnd_sound : forall (fs:ls) (B1 B2:styp),
    sub (styp_and (applyfs fs B1) (applyfs fs B2)) (applyfs fs (styp_and B1 B2)) (calAnd fs).
Proof.
  induction fs as [|x xs IH]; intros B1 B2.
  - simpl. apply S_refl.
  - destruct x as [A|l].
    + simpl. eapply S_trans with (A2 := styp_arrow A (styp_and (applyfs xs B1) (applyfs xs B2))).
      * apply S_arr; [apply S_refl | exact (IH B1 B2)].
      * apply S_distArr.
    + simpl. eapply S_trans with (A2 := styp_rcd l (styp_and (applyfs xs B1) (applyfs xs B2))).
      * apply S_rcd. exact (IH B1 B2).
      * apply S_distRcd.
Qed.

Theorem ASub2sub : forall fs A B c,
    ASub fs A B c -> sub A (applyfs fs B) c.
Proof.
  intros fs A B c H. induction H.
  - simpl. apply S_refl.
  - simpl. apply S_rcd. exact IHASub.
  - rewrite <- applyfs_snoc_la. exact IHASub.
  - eapply S_trans with (A2 := styp_top).
    + apply calTop_sound.
    + apply S_top.
  - eapply S_trans with (A2 := styp_and (applyfs fs B1) (applyfs fs B2)).
    + apply calAnd_sound.
    + apply S_and; [exact IHASub1 | exact IHASub2].
  - rewrite <- applyfs_snoc_ty. exact IHASub.
  - eapply S_trans with (A2 := A1).
    + exact IHASub.
    + apply S_andl.
  - eapply S_trans with (A2 := A2).
    + exact IHASub.
    + apply S_andr.
  - simpl. apply S_arr; [exact IHASub1 | exact IHASub2].
Qed.

(* Replacing the annotation [st_ty A'] in a stack by [st_ty X], when
   X is a subtype of A'.  The [HTn] hypothesis is the composition property
   for the middle type A' (an instance of the main induction). *)
Lemma shift_app : forall (pre post rest:list st) (x:st),
    (pre ++ x :: post) ++ rest = pre ++ x :: (post ++ rest).
Proof. intros. rewrite <- app_assoc. reflexivity. Qed.

Lemma ASub_ann_change : forall (A' X:styp),
    (forall (fs1:ls) (A1:styp) (fs2:ls) (B:styp) (c1 c2:co),
        ASub fs1 A1 A' c1 -> ASub fs2 A' B c2 -> exists c, ASub (fs1 ++ fs2) A1 B c) ->
    forall (c0:co), ASub nil X A' c0 ->
    forall (fs:ls) (A1' B:styp) (c:co), ASub fs A1' B c ->
    forall pre post, fs = pre ++ [st_ty A'] ++ post ->
    exists c', ASub (pre ++ [st_ty X] ++ post) A1' B c'.
Proof.
  intros A' X HTn c0 EX fs A1' B c H.
  induction H; intros pre post Heq.
  - (* A_nat *)
    destruct pre; simpl in Heq; discriminate Heq.
  - (* A_rcdNat *)
    destruct pre as [|p pre'].
    + simpl in Heq. discriminate Heq.
    + simpl in Heq. injection Heq as Hp Hfs. subst p.
      destruct (IHASub pre' post Hfs) as [d Hd].
      eexists. eapply A_rcdNat. exact Hd.
  - (* A_rcd *)
    destruct (IHASub pre (post ++ [st_la l])) as [d Hd].
    { rewrite Heq. simpl. rewrite shift_app. reflexivity. }
    eexists. eapply A_rcd.
    simpl. rewrite shift_app. exact Hd.
  - (* A_top *)
    eexists. apply A_top.
  - (* A_and *)
    destruct (IHASub1 pre post Heq) as [d1 Hd1].
    destruct (IHASub2 pre post Heq) as [d2 Hd2].
    eexists. apply A_and; [exact Hd1 | exact Hd2].
  - (* A_arr *)
    destruct (IHASub pre (post ++ [st_ty B1])) as [d Hd].
    { rewrite Heq. simpl. rewrite shift_app. reflexivity. }
    eexists. eapply A_arr.
    simpl. rewrite shift_app. exact Hd.
  - (* A_andN1 *)
    destruct (IHASub pre post Heq) as [d Hd].
    eexists. apply A_andN1. exact Hd.
  - (* A_andN2 *)
    destruct (IHASub pre post Heq) as [d Hd].
    eexists. apply A_andN2. exact Hd.
  - (* A_arrNat *)
    destruct pre as [|p pre'].
    + simpl in Heq. injection Heq as HA' Hfs. subst A. subst post.
      destruct (HTn nil X nil A1 c0 c1) as [d Hd].
      * simpl. exact EX.
      * simpl. exact H.
      * simpl in Hd. eexists. eapply A_arrNat.
        -- exact Hd.
        -- exact H0.
    + simpl in Heq. injection Heq as Hp Hfs. subst p.
      destruct (IHASub2 pre' post Hfs) as [d Hd].
      eexists. eapply A_arrNat.
      * exact H.
      * exact Hd.
Qed.

(* size of a type, used as termination measure *)
Fixpoint size (A:styp) : nat :=
  match A with
  | styp_top => 1
  | styp_nat => 1
  | styp_and A B => 1 + size A + size B
  | styp_arrow A B => 1 + size A + size B
  | styp_rcd _ A => 1 + size A
  end.

Lemma snoc_app : forall (a b:list st) (x:st),
    (a ++ [x]) ++ b = a ++ x :: b.
Proof. intros. rewrite shift_app. simpl. reflexivity. Qed.

Lemma size_lt_trans : forall a b c, a < b -> b < c -> a < c.
Proof. intros; lia. Qed.

Lemma size_pos : forall A, 1 <= size A.
Proof. induction A; simpl; lia. Qed.

Lemma size_rcd : forall l A, size A < size (styp_rcd l A).
Proof. intros. simpl. lia. Qed.

Lemma size_and_l : forall A B, size A < size (styp_and A B).
Proof. intros. simpl. lia. Qed.

Lemma size_and_r : forall A B, size B < size (styp_and A B).
Proof. intros. simpl. lia. Qed.

Lemma size_arr_l : forall A B, size A < size (styp_arrow A B).
Proof. intros. simpl. lia. Qed.

Lemma size_arr_r : forall A B, size B < size (styp_arrow A B).
Proof. intros. simpl. lia. Qed.

(* inversion lemmas for the target-directed structure of ASub *)
Lemma ASub_inv_rcd : forall (fs:ls) (A:styp) (l:i) (B:styp) (c:co),
    ASub fs A (styp_rcd l B) c -> exists c', ASub (fs ++ [st_la l]) A B c'.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ASub_inv_arr : forall (fs:ls) (A:styp) (B1 B2:styp) (c:co),
    ASub fs A (styp_arrow B1 B2) c -> exists c', ASub (fs ++ [st_ty B1]) A B2 c'.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma ASub_inv_and : forall (fs:ls) (A:styp) (B1 B2:styp) (c:co),
    ASub fs A (styp_and B1 B2) c ->
    (exists c1, ASub fs A B1 c1) /\ (exists c2, ASub fs A B2 c2).
Proof. intros. inversion H; subst; eauto. Qed.

(* Composition of the algorithmic judgment: stacks concatenate.
   The proof is by induction on the second derivation, with a subordinate
   induction on the size of its source type for the arrow/record cases. *)
Lemma ASub_comp_gen : forall (A:styp),
    (forall (A':styp), size A' < size A ->
        forall (fs1:ls) (A1:styp) (fs2:ls) (B:styp) (c1 c2:co),
        ASub fs1 A1 A' c1 -> ASub fs2 A' B c2 -> exists c, ASub (fs1 ++ fs2) A1 B c) ->
    forall (fs1:ls) (A1:styp) (fs2:ls) (B:styp) (c1 c2:co),
    ASub fs1 A1 A c1 -> ASub fs2 A B c2 -> exists c, ASub (fs1 ++ fs2) A1 B c.
Proof.
  intros A Hsub.
  assert (Main : forall (fs2:ls) (A0:styp) (B:styp) (c2:co),
      ASub fs2 A0 B c2 ->
      (forall (A':styp), size A' < size A0 ->
          forall (fs1:ls) (A1:styp) (fs2':ls) (B':styp) (c1 c2':co),
          ASub fs1 A1 A' c1 -> ASub fs2' A' B' c2' -> exists c, ASub (fs1 ++ fs2') A1 B' c) ->
      forall (fs1:ls) (A1:styp) (c1:co),
      ASub fs1 A1 A0 c1 -> exists c, ASub (fs1 ++ fs2) A1 B c).
  { intros fs2 A0 B c2 D2.
    induction D2; intros HsubA g1 b1 dd D1.
    - (* A_nat *) eexists. rewrite app_nil_r. exact D1.
    - (* A_rcdNat *) destruct (ASub_inv_rcd _ _ _ _ _ D1) as [d0 D1'].
      destruct (IHD2 (fun A' Hlt => HsubA A' (size_lt_trans _ _ _ Hlt (size_rcd l A0))) _ _ _ D1') as [d Hd].
      rewrite snoc_app in Hd. eexists. exact Hd.
    - (* A_rcd *) destruct (IHD2 HsubA _ _ _ D1) as [d Hd].
      eexists. apply A_rcd. rewrite <- app_assoc. exact Hd.
    - (* A_top *) eexists. apply A_top.
    - (* A_and *) destruct (IHD2_1 HsubA _ _ _ D1) as [d1 Hd1].
      destruct (IHD2_2 HsubA _ _ _ D1) as [d2 Hd2].
      eexists. apply A_and; [exact Hd1 | exact Hd2].
    - (* A_arr *) destruct (IHD2 HsubA _ _ _ D1) as [d Hd].
      eexists. apply A_arr. rewrite <- app_assoc. exact Hd.
    - (* A_andN1 *) destruct (ASub_inv_and _ _ _ _ _ D1) as [[ca D1a] [cb D1b]].
      destruct (IHD2 (fun A' Hlt => HsubA A' (size_lt_trans _ _ _ Hlt (size_and_l A1 A2))) _ _ _ D1a) as [d Hd].
      eexists. exact Hd.
    - (* A_andN2 *) destruct (ASub_inv_and _ _ _ _ _ D1) as [[ca D1a] [cb D1b]].
      destruct (IHD2 (fun A' Hlt => HsubA A' (size_lt_trans _ _ _ Hlt (size_and_r A1 A2))) _ _ _ D1b) as [d Hd].
      eexists. exact Hd.
    - (* A_arrNat *) destruct (ASub_inv_arr _ _ _ _ _ D1) as [d0 D1'].
      destruct (IHD2_2 (fun A' Hlt => HsubA A' (size_lt_trans _ _ _ Hlt (size_arr_r A1 A2))) _ _ _ D1') as [d Hd].
      rewrite snoc_app in Hd.
      destruct (ASub_ann_change A1 A0 (HsubA A1 (size_arr_l A1 A2)) c1 D2_1
                 (g1 ++ [st_ty A1] ++ fs) b1 styp_nat d Hd g1 fs) as [e He].
      + reflexivity.
      + eexists. exact He.
  }
  intros fs1 A1 fs2 B c1 c2 D1 D2.
  eapply Main; [exact D2 | exact Hsub | exact D1].
Qed.

Lemma ASub_comp : forall (A:styp) (fs1:ls) (A1:styp) (fs2:ls) (B:styp) (c1 c2:co),
    ASub fs1 A1 A c1 -> ASub fs2 A B c2 ->
    exists c, ASub (fs1 ++ fs2) A1 B c.
Proof.
  assert (H : forall (n:nat) (A:styp), size A <= n ->
      forall (fs1:ls) (A1:styp) (fs2:ls) (B:styp) (c1 c2:co),
      ASub fs1 A1 A c1 -> ASub fs2 A B c2 ->
      exists c, ASub (fs1 ++ fs2) A1 B c).
  { induction n as [|n IH]; intros A Hle.
    - exfalso. assert (1 <= size A) by apply size_pos. lia.
    - intros fs1 A1 fs2 B c1 c2 D1 D2.
      eapply ASub_comp_gen with (A := A).
      + intros A' Hlt. apply IH. lia.
      + exact D1.
      + exact D2. }
  intros A fs1 A1 fs2 B c1 c2 D1 D2.
  exact (H (size A) A (le_n (size A)) fs1 A1 fs2 B c1 c2 D1 D2).
Qed.

Theorem sub2ASub : forall A B c,
    sub A B c -> exists c', ASub nil A B c'.
Proof.
  intros A B c H. induction H.
  - (* S_refl *) apply ASub_refl.
  - (* S_trans *) destruct IHsub1 as [c1' H1].
    destruct IHsub2 as [c2' H2].
    exact (ASub_comp A2 nil A1 nil A3 c2' c1' H2 H1).
  - (* S_top *) eexists. apply A_top.
  - (* S_topArr *) eexists. apply A_arr. apply A_top.
  - (* S_topRcd *) eexists. apply A_rcd. apply A_top.
  - (* S_arr *) destruct IHsub1 as [c1' H1].
    destruct IHsub2 as [c2' H2].
    destruct (ASub_arr_lift B2 nil B1 A1 A2 c1' c2' H1 H2) as [d Hd].
    eexists. apply A_arr. exact Hd.
  - (* S_and *) destruct IHsub1 as [c1' H1].
    destruct IHsub2 as [c2' H2].
    eexists. apply A_and; [exact H1 | exact H2].
  - (* S_andl *) destruct (ASub_refl A1) as [d Hd].
    destruct (ASub_and_l nil A1 A2 A1 d Hd) as [e He].
    eexists. exact He.
  - (* S_andr *) destruct (ASub_refl A2) as [d Hd].
    destruct (ASub_and_r nil A1 A2 A2 d Hd) as [e He].
    eexists. exact He.
  - (* S_distArr *) destruct (ASub_refl A1) as [cA1 HA1].
    destruct (ASub_refl A2) as [cA2 HA2].
    destruct (ASub_refl A3) as [cA3 HA3].
    destruct (ASub_arr_lift A2 nil A1 A1 A2 cA1 cA2 HA1 HA2) as [d2 Hd2].
    destruct (ASub_arr_lift A3 nil A1 A1 A3 cA1 cA3 HA1 HA3) as [d3 Hd3].
    destruct (ASub_and_l (st_ty A1 :: nil) (styp_arrow A1 A2) (styp_arrow A1 A3) A2 d2 Hd2) as [e2 He2].
    destruct (ASub_and_r (st_ty A1 :: nil) (styp_arrow A1 A2) (styp_arrow A1 A3) A3 d3 Hd3) as [e3 He3].
    eexists. apply A_arr. apply A_and; [exact He2 | exact He3].
  - (* S_rcd *) destruct IHsub as [d Hd].
    destruct (ASub_rcd_lift B nil l A d Hd) as [e He].
    eexists. apply A_rcd. exact He.
  - (* S_distRcd *) destruct (ASub_refl A) as [cA HA].
    destruct (ASub_refl B) as [cB HB].
    destruct (ASub_rcd_lift A nil l A cA HA) as [dA HdA].
    destruct (ASub_rcd_lift B nil l B cB HB) as [dB HdB].
    destruct (ASub_and_l (st_la l :: nil) (styp_rcd l A) (styp_rcd l B) A dA HdA) as [eA HeA].
    destruct (ASub_and_r (st_la l :: nil) (styp_rcd l A) (styp_rcd l B) B dB HdB) as [eB HeB].
    eexists. apply A_rcd. apply A_and; [exact HeA | exact HeB].
Qed.
