From Stdlib Require Import PeanoNat Lia Wf_nat.

From OLlibs Require Import Logic_Datatypes_more List_more.

From InterPT Require Export lformulas.

Export LogicNotations ListNotations.

Set Default Proof Using "Type".

Set Implicit Arguments.

Unset Printing Use Implicit Types.

Reserved Notation "l ⎹ bp ⊦ a" (at level 65, format "l ⎹ bp ⊦  a").

Inductive lprove {bp : bool} : list lform -> lform -> Type :=
| lidentity a : [a]⎹bp⊦ a
| ltop_right l : l⎹bp⊦ 𝖳
| lwith_left1 a b c l1 l2 : l1 ++ a :: l2⎹bp⊦ c -> l1 ++ a ∧ b :: l2⎹bp⊦ c
| lwith_left2 a b c l1 l2 : l1 ++ a :: l2⎹bp⊦ c -> l1 ++ b ∧ a :: l2⎹bp⊦ c
| lwith_right a b l : l⎹bp⊦ a -> l⎹bp⊦ b -> l⎹bp⊦ a ∧ b
| lmap_left a b c l1 l2 l3 : (bp = true -> l1 = [] /\ length l2 = 1%nat) ->
    l2⎹bp⊦ a -> l1 ++ b :: l3⎹bp⊦ c -> l1 ++ b / a :: l2 ++ l3⎹bp⊦ c
| lmap_right a b l : l · a⎹bp⊦ b -> l⎹bp⊦ b / a
| lzero_left a l1 l2 : l1 ++ 0 :: l2⎹bp⊦ a
| lplus_left a b c l1 l2 : l1 ++ a :: l2⎹bp⊦ c -> l1 ++ b :: l2⎹bp⊦ c -> l1 ++ a ∨ b :: l2⎹bp⊦ c
| lplus_right1 a b l : l⎹bp⊦ a -> l⎹bp⊦ a ∨ b
| lplus_right2 a b l : l⎹bp⊦ a -> l⎹bp⊦ b ∨ a
| lone_left a l1 l2 : l1 ++ l2⎹bp⊦ a -> l1 ++ 1 :: l2⎹bp⊦ a
| lone_right : nil⎹bp⊦ 1
| lfrl_left a x b c l1 l2 : closed b -> l1 ++ subs x b a :: l2⎹bp⊦ c -> l1 ++ lfrl x a :: l2⎹bp⊦ c
| lfrl_right a x l : map fupz l⎹bp⊦ subs x (dvar 0) (fupz a) -> l⎹bp⊦ lfrl x a
| lexs_left a x c l1 l2 : map fupz l1 ++ subs x (dvar 0) (fupz a) :: map fupz l2⎹bp⊦ fupz c ->
   l1 ++ lexs x a :: l2⎹bp⊦ c
| lexs_right a x b l : closed b -> l⎹bp⊦ subs x b a -> l⎹bp⊦ lexs x a
where "l ⎹ bp ⊦ a" := (@lprove bp l a).

Arguments lidentity {_ _}, [_] _, _ _.

Arguments ltop_right {_ _}, [_] _, _ _.

Arguments lwith_left1 [_ _ _ _ _ _] _, [_ _] _ [_ _ _] _, [_] _ _ _ _ _ _, _ _ _ _ _ _ _.

Arguments lwith_left2 [_ _ _ _ _ _] _, [_ _] _ [_ _ _] _, [_] _ _ _ _ _ _, _ _ _ _ _ _ _.

Arguments lwith_right [_ _ _ _] _ _, [_] _ _ _ _ _, _ _ _ _ _ _.

Arguments lmap_left [_ _ _ _ _ _ _ _] _ _, [_ _ _ _ _ _ _] _ _ _, [_] _ _ _ _ _ _ _ _ _, _ _ _ _ _ _ _ _ _ _.

Arguments lmap_right [_ _ _ _] _, [_] _ _ _ _, _ _ _ _ _.

Arguments lzero_left {_ _ _ _}, [_] _ _ _, _ _ _ _.

Arguments lplus_left [_ _ _ _ _ _] _ _, [_] _ _ _ _ _ _ _, _ _ _ _ _ _ _ _.

Arguments lplus_right1 [_ _ _ _] _, [_ _] _ [_] _, [_] _ _ _ _, _ _ _ _ _.

Arguments lplus_right2 [_ _ _ _] _, [_ _] _ [_] _, [_] _ _ _ _, _ _ _ _ _.

Arguments lone_left [_ _ _ _] _, [_ _] _ _ _, [_] _ _ _ _, _ _ _ _ _.

Arguments lone_right {_}, _.

Arguments lfrl_left [_ _ _ _ _ _ _ _] _, [_ _ _ _ _ _ _] _ _, _ _ _ _ _ _ _ _.

Arguments lfrl_right [_ _ _ _] _, [_ _] _ [_] _, [_] _ _ _ _, _ _ _ _ _.

Arguments lexs_left [_ _ _ _ _ _] _, [_ _] _ [_ _] _, [_] _ _ _ _ _, _ _ _ _ _ _.

Arguments lexs_right [_ _ _ _ _ _] _, [_ _ _ _ _] _ _, _ _ _ _ _ _ _.

Section WithParameter.

Variable bp : bool.

Notation lprove := (@lprove bp).

Notation "l ⊦ a" := (lprove l a) (at level 65, format "l  ⊦  a").

Fixpoint lweight l b (pi : l ⊦ b) := S
match pi with
| lidentity | ltop_right | lzero_left | lone_right => 0
| lwith_left1 pi1 | lwith_left2 pi1 | lmap_right pi1 | lplus_right1 pi1 | lplus_right2 pi1
| lone_left pi1 | lfrl_left pi1 | lfrl_right pi1 | lexs_left pi1 | lexs_right pi1 => lweight pi1
| lwith_right pi1 pi2 | lplus_left pi1 pi2 => max (lweight pi1) (lweight pi2)
| lmap_left pi1 pi2 => lweight pi1 + lweight pi2
end.

Lemma ltb_succ n k : (S n <? S k) = (n <? k).
Proof.
  apply Bool.eq_iff_eq_true. rewrite !Nat.ltb_lt. split; intros H; lia.
Qed.

Lemma subs_notin x F A : ~ In x (freevars A) -> subs x F A = A.
Proof.
  induction A; simpl; intros H; try reflexivity.
  - destruct c; simpl; try reflexivity.
    + (* var *) destruct (Nat.eq_dec n x) as [Heq|Hne].
      * subst. exfalso. apply H. left. reflexivity.
      * reflexivity.
  - (* lmap *)
    assert (H1 : ~ In x (freevars A1)) by (intro Hin; apply H; apply in_app_iff; left; exact Hin).
    assert (H2 : ~ In x (freevars A2)) by (intro Hin; apply H; apply in_app_iff; right; exact Hin).
    rewrite IHA1 by exact H1. rewrite IHA2 by exact H2. reflexivity.
  - (* lwith *)
    assert (H1 : ~ In x (freevars A1)) by (intro Hin; apply H; apply in_app_iff; left; exact Hin).
    assert (H2 : ~ In x (freevars A2)) by (intro Hin; apply H; apply in_app_iff; right; exact Hin).
    rewrite IHA1 by exact H1. rewrite IHA2 by exact H2. reflexivity.
  - (* lplus *)
    assert (H1 : ~ In x (freevars A1)) by (intro Hin; apply H; apply in_app_iff; left; exact Hin).
    assert (H2 : ~ In x (freevars A2)) by (intro Hin; apply H; apply in_app_iff; right; exact Hin).
    rewrite IHA1 by exact H1. rewrite IHA2 by exact H2. reflexivity.
  - (* lfrl *) destruct (Nat.eq_dec n x) as [Heq|Hne].
    + subst. reflexivity.
    + rewrite IHA. reflexivity.
      intro Hin. apply H. apply in_in_remove; auto.
  - (* lexs *) destruct (Nat.eq_dec n x) as [Heq|Hne].
    + subst. reflexivity.
    + rewrite IHA. reflexivity.
      intro Hin. apply H. apply in_in_remove; auto.
Qed.

Lemma fup_comp k A : fup (S k) (fup 0 A) = fup 0 (fup k A).
Proof.
  induction A; simpl; try reflexivity.
  - (* lvar c n *) destruct c; simpl; try reflexivity.
    destruct (n <? 0) eqn:E0; simpl.
    + (* impossible *) apply Nat.ltb_lt in E0; lia.
    + rewrite ltb_succ. destruct (n <? k); reflexivity.
  - (* lmap *) rewrite IHA1, IHA2; reflexivity.
  - (* lwith *) rewrite IHA1, IHA2; reflexivity.
  - (* lplus *) rewrite IHA1, IHA2; reflexivity.
  - (* lfrl *) rewrite IHA; reflexivity.
  - (* lexs *) rewrite IHA; reflexivity.
Qed.

Lemma nsubs_fup k b A : nsubs k b (fup k A) = A.
Proof.
  induction A; simpl; try reflexivity.
  - destruct c; simpl; try reflexivity.
    destruct (n <? k) eqn:E; simpl.
    + apply Nat.ltb_lt in E. 
      replace (k ?= n) with Gt. reflexivity.
      symmetry. apply Nat.compare_gt_iff. lia.
    + apply Nat.ltb_ge in E.
      replace (k ?= S n) with Lt. simpl. reflexivity.
      symmetry. apply Nat.compare_lt_iff. lia.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA; reflexivity.
  - rewrite IHA; reflexivity.
Qed.

Lemma nsubs_subs_fup k x b A : nsubs k b (subs x (dvar k) (fup k A)) = subs x b A.
Proof.
  induction A; simpl; try reflexivity.
  - destruct c; simpl; try reflexivity.
    + (* Eq dvar *) destruct (n <? k) eqn:E; simpl.
      * apply Nat.ltb_lt in E. assert (Hc : (k ?= n) = Gt) by (apply Nat.compare_gt_iff; lia); rewrite Hc; reflexivity.
      * apply Nat.ltb_ge in E. assert (Hc : (k ?= S n) = Lt) by (apply Nat.compare_lt_iff; lia); rewrite Hc; simpl; reflexivity.
    + (* Gt var *) destruct (Nat.eq_dec n x); subst; simpl.
      * rewrite Nat.compare_refl. reflexivity.
      * reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - (* lfrl *) destruct (Nat.eq_dec n x); subst; simpl.
    + rewrite nsubs_fup. reflexivity.
    + rewrite IHA. reflexivity.
  - (* lexs *) destruct (Nat.eq_dec n x); subst; simpl.
    + rewrite nsubs_fup. reflexivity.
    + rewrite IHA. reflexivity.
Qed.

Lemma freevars_fup k A : freevars (fup k A) = freevars A.
Proof.
  induction A; simpl.
  - destruct c; simpl.
    + destruct (n <? k); reflexivity.
    + reflexivity.
    + reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - reflexivity.
  - rewrite IHA; reflexivity.
  - rewrite IHA; reflexivity.
Qed.

Lemma freevars_nsubs k b A : freevars b = nil -> freevars (nsubs k b A) = freevars A.
Proof.
  intros Hb. induction A; simpl.
  - destruct c; simpl.
    + destruct (k ?= n); simpl; [rewrite Hb; reflexivity | reflexivity | reflexivity].
    + reflexivity.
    + reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - reflexivity.
  - rewrite IHA; reflexivity.
  - rewrite IHA; reflexivity.
Qed.

Lemma fup_closed k A : closed A -> closed (fup k A).
Proof. intros H. rewrite (freevars_fup k A). exact H. Qed.

Lemma nsubs_closed k b A : closed b -> closed A -> closed (nsubs k b A).
Proof. intros Hb HA. rewrite (freevars_nsubs k b A Hb). exact HA. Qed.

Lemma nsubs_fup_0 k b A : nsubs (S k) (fup 0 b) (fup 0 A) = fup 0 (nsubs k b A).
Proof.
  induction A; simpl; try reflexivity.
  - destruct c; simpl; try reflexivity.
    destruct (Nat.compare_spec k n) as [Heq|Hlt|Hgt]; simpl.
    * subst. reflexivity.
    * f_equal. lia.
    * reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA; reflexivity.
  - rewrite IHA; reflexivity.
Qed.

Lemma nsubs_subs_fup_0 k x b A : closed b ->
  nsubs (S k) (fup 0 b) (subs x (dvar 0) (fup 0 A)) =
  subs x (dvar 0) (fup 0 (nsubs k b A)).
Proof.
  intros Hb. induction A; simpl; try reflexivity.
  - destruct c; simpl; try reflexivity.
    + (* dvar *)
      destruct (Nat.compare_spec k n) as [Heq|Hlt|Hgt]; simpl.
      * subst. symmetry. apply subs_notin. rewrite freevars_fup, Hb. simpl. auto.
      * f_equal. lia.
      * reflexivity.
    + (* var *) destruct (Nat.eq_dec n x); subst; simpl.
      * (* Eq: nsubs of dvar 0 *) 
        reflexivity.
      * reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - (* lfrl *) destruct (Nat.eq_dec n x); subst; simpl.
    + rewrite nsubs_fup_0. reflexivity.
    + rewrite IHA. reflexivity.
  - (* lexs *) destruct (Nat.eq_dec n x); subst; simpl.
    + rewrite nsubs_fup_0. reflexivity.
    + rewrite IHA. reflexivity.
Qed.

Lemma nsubs_subs k x b F A : closed b ->
  nsubs k b (subs x F A) = subs x (nsubs k b F) (nsubs k b A).
Proof.
  intros Hb. induction A; simpl; try reflexivity.
  - destruct c; simpl; try reflexivity.
    + (* dvar *)
      destruct (Nat.compare_spec k n) as [Heq|Hlt|Hgt]; simpl.
      * subst. symmetry. apply subs_notin. rewrite Hb. simpl. auto.
      * reflexivity.
      * reflexivity.
    + (* var *) destruct (Nat.eq_dec n x) as [Heq|Hne].
      * subst x. reflexivity.
      * reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - destruct (Nat.eq_dec n x); subst; simpl.
    + reflexivity.
    + rewrite IHA. reflexivity.
  - destruct (Nat.eq_dec n x); subst; simpl.
    + reflexivity.
    + rewrite IHA. reflexivity.
Qed.

Lemma fup_subs k x F A :
  fup k (subs x F A) = subs x (fup k F) (fup k A).
Proof.
  induction A; simpl; try reflexivity.
  - destruct c; simpl; try reflexivity.
    + (* dvar *) destruct (n <? k); reflexivity.
    + (* var *) destruct (Nat.eq_dec n x) as [Heq|Hne].
      * subst x. reflexivity.
      * reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - rewrite IHA1, IHA2; reflexivity.
  - destruct (Nat.eq_dec n x); subst; simpl.
    + reflexivity.
    + rewrite IHA. reflexivity.
  - destruct (Nat.eq_dec n x); subst; simpl.
    + reflexivity.
    + rewrite IHA. reflexivity.
Qed.

Lemma nsubs_top k b : nsubs k b ltop = ltop. Proof. reflexivity. Qed.
Lemma nsubs_lzero k b : nsubs k b lzero = lzero. Proof. reflexivity. Qed.
Lemma nsubs_lone k b : nsubs k b lone = lone. Proof. reflexivity. Qed.
Lemma fup_top k : fup k ltop = ltop. Proof. reflexivity. Qed.
Lemma fup_lzero k : fup k lzero = lzero. Proof. reflexivity. Qed.
Lemma fup_lone k : fup k lone = lone. Proof. reflexivity. Qed.


(* ******* Derivation-level infrastructure ******* *)

Definition lprove_cast {L1 L2 : list lform} {a1 a2 : lform}
  (eL : L1 = L2) (ea : a1 = a2) (pi : L1 ⊦ a1) : L2 ⊦ a2 :=
  match eL in (_ = L) return (forall a, a1 = a -> L ⊦ a) with
  | eq_refl => fun a ea => match ea in (_ = A) return (L1 ⊦ A) with eq_refl => pi end
  end a2 ea.

Arguments lprove_cast {_} {_} {_} {_} _ _ _.

Lemma lweight_lprove_cast L1 L2 a1 a2 (eL : L1 = L2) (ea : a1 = a2) pi :
  lweight (lprove_cast eL ea pi) = lweight pi.
Proof. destruct eL, ea. reflexivity. Qed.

Opaque lprove_cast.

Ltac lw_casts := simpl; repeat (rewrite lweight_lprove_cast; simpl).

Lemma fup_dvar0_S k : fup (S k) (dvar 0) = dvar 0.
Proof. simpl. reflexivity. Qed.

Lemma map_fup_comp k (L : list lform) :
  map (fup (S k)) (map fupz L) = map fupz (map (fup k) L).
Proof.
  rewrite !map_map. apply map_ext. intro x. apply fup_comp.
Qed.

Lemma map_fup_app k (L1 L2 : list lform) :
  map (fup k) (L1 ++ L2) = map (fup k) L1 ++ map (fup k) L2.
Proof. apply map_app. Qed.

Lemma map_fup_cons k (L : list lform) a :
  map (fup k) (a :: L) = fup k a :: map (fup k) L.
Proof. reflexivity. Qed.

Lemma lprove_fup_weight : forall k l a (pi : l ⊦ a),
  { pi' : map (fup k) l ⊦ fup k a | lweight pi' <= lweight pi }.
Proof.
  intros k l a pi. revert k.
  induction pi as
    [ a
    | l
    | a b c l1 l2 pi1 IH1
    | a b c l1 l2 pi1 IH1
    | a b l pi1 IH1 pi2 IH2
    | a b c l1 l2 l3 Hc0 pi1 IH1 pi2 IH2
    | a b l pi1 IH1
    | a l1 l2
    | a b c l1 l2 pi1 IH1 pi2 IH2
    | a b l pi1 IH1
    | a b l pi1 IH1
    | a l1 l2 pi1 IH1
    |
    | a x b c l1 l2 Hb pi1 IH1
    | a x l pi1 IH1
    | a x c l1 l2 pi1 IH1
    | a x b l Hb pi1 IH1
    ]; intros k.
  - (* lidentity *) simpl. exists (lidentity (fup k a)). simpl. lia.
  - (* ltop_right *) simpl. exists (ltop_right (map (fup k) l)). simpl. lia.
  - (* lwith_left1 *)
    destruct (IH1 k) as [p Hp].
    assert (e1 : map (fup k) (l1 ++ a :: l2) = map (fup k) l1 ++ fup k a :: map (fup k) l2).
    { rewrite (map_app (fup k) l1 (a :: l2)). reflexivity. }
    assert (e2 : map (fup k) l1 ++ (fup k a ∧ fup k b) :: map (fup k) l2
                 = map (fup k) (l1 ++ (a ∧ b) :: l2)).
    { rewrite (map_app (fup k) l1 ((a ∧ b) :: l2)). reflexivity. }
    exists (lprove_cast e2 eq_refl
              (lwith_left1 (fup k a) (fup k b) (fup k c)
                 (map (fup k) l1) (map (fup k) l2)
                 (lprove_cast e1 eq_refl p))).
    lw_casts. lia.
  - (* lwith_left2 *)
    destruct (IH1 k) as [p Hp].
    assert (e1 : map (fup k) (l1 ++ a :: l2) = map (fup k) l1 ++ fup k a :: map (fup k) l2).
    { rewrite (map_app (fup k) l1 (a :: l2)). reflexivity. }
    assert (e2 : map (fup k) l1 ++ (fup k b ∧ fup k a) :: map (fup k) l2
                 = map (fup k) (l1 ++ (b ∧ a) :: l2)).
    { rewrite (map_app (fup k) l1 ((b ∧ a) :: l2)). reflexivity. }
    exists (lprove_cast e2 eq_refl
              (lwith_left2 (fup k a) (fup k b) (fup k c)
                 (map (fup k) l1) (map (fup k) l2)
                 (lprove_cast e1 eq_refl p))).
    lw_casts. lia.
  - (* lwith_right *)
    destruct (IH1 k) as [p1 Hp1]. destruct (IH2 k) as [p2 Hp2].
    exists (lwith_right (fup k a) (fup k b) (map (fup k) l) p1 p2).
    simpl. lia.
  - (* lmap_left *)
    destruct (IH1 k) as [p1 Hp1]. destruct (IH2 k) as [p2 Hp2].
    assert (H' : bp = true -> map (fup k) l1 = [] /\ length (map (fup k) l2) = 1%nat).
    { intros Hb. specialize (Hc0 Hb). destruct Hc0 as [H1 H2]. split.
      - rewrite H1. reflexivity.
      - rewrite length_map. exact H2. }
    assert (e2 : map (fup k) (l1 ++ b :: l3) = map (fup k) l1 ++ fup k b :: map (fup k) l3).
    { rewrite (map_app (fup k) l1 (b :: l3)). reflexivity. }
    assert (e3 : map (fup k) l1 ++ (fup k b / fup k a) :: (map (fup k) l2 ++ map (fup k) l3)
                 = map (fup k) (l1 ++ (b / a) :: (l2 ++ l3))).
    { rewrite (map_app (fup k) l1 ((b / a) :: (l2 ++ l3))).
      simpl. rewrite (map_app (fup k) l2 l3). reflexivity. }
    exists (lprove_cast e3 eq_refl
              (lmap_left (fup k a) (fup k b) (fup k c)
                 (map (fup k) l1) (map (fup k) l2) (map (fup k) l3)
                 H' p1 (lprove_cast e2 eq_refl p2))).
    lw_casts. lia.
  - (* lmap_right *)
    destruct (IH1 k) as [p Hp].
    assert (e1 : map (fup k) (l ++ [a]) = map (fup k) l ++ [fup k a]).
    { rewrite (map_app (fup k) l [a]). reflexivity. }
    exists (lmap_right (fup k a) (fup k b) (map (fup k) l)
              (lprove_cast e1 eq_refl p)).
    lw_casts. lia.
  - (* lzero_left *)
    assert (e2 : map (fup k) l1 ++ lzero :: map (fup k) l2 = map (fup k) (l1 ++ lzero :: l2)).
    { rewrite (map_app (fup k) l1 (lzero :: l2)). reflexivity. }
    exists (lprove_cast e2 eq_refl
              (lzero_left (fup k a) (map (fup k) l1) (map (fup k) l2))).
    lw_casts. lia.
  - (* lplus_left *)
    destruct (IH1 k) as [p1 Hp1]. destruct (IH2 k) as [p2 Hp2].
    assert (e1 : map (fup k) (l1 ++ a :: l2) = map (fup k) l1 ++ fup k a :: map (fup k) l2).
    { rewrite (map_app (fup k) l1 (a :: l2)). reflexivity. }
    assert (e1b : map (fup k) (l1 ++ b :: l2) = map (fup k) l1 ++ fup k b :: map (fup k) l2).
    { rewrite (map_app (fup k) l1 (b :: l2)). reflexivity. }
    assert (e2 : map (fup k) l1 ++ (fup k a ∨ fup k b) :: map (fup k) l2
                 = map (fup k) (l1 ++ (a ∨ b) :: l2)).
    { rewrite (map_app (fup k) l1 ((a ∨ b) :: l2)). reflexivity. }
    exists (lprove_cast e2 eq_refl
              (lplus_left (fup k a) (fup k b) (fup k c)
                 (map (fup k) l1) (map (fup k) l2)
                 (lprove_cast e1 eq_refl p1) (lprove_cast e1b eq_refl p2))).
    lw_casts. lia.
  - (* lplus_right1 *)
    destruct (IH1 k) as [p Hp].
    exists (lplus_right1 (fup k a) (fup k b) (map (fup k) l) p).
    simpl. lia.
  - (* lplus_right2 *)
    destruct (IH1 k) as [p Hp].
    exists (lplus_right2 (fup k a) (fup k b) (map (fup k) l) p).
    simpl. lia.
  - (* lone_left *)
    destruct (IH1 k) as [p Hp].
    assert (e1 : map (fup k) (l1 ++ l2) = map (fup k) l1 ++ map (fup k) l2).
    { rewrite (map_app (fup k) l1 l2). reflexivity. }
    assert (e2 : map (fup k) l1 ++ lone :: map (fup k) l2 = map (fup k) (l1 ++ lone :: l2)).
    { rewrite (map_app (fup k) l1 (lone :: l2)). reflexivity. }
    exists (lprove_cast e2 eq_refl
              (lone_left (fup k a) (map (fup k) l1) (map (fup k) l2)
                 (lprove_cast e1 eq_refl p))).
    lw_casts. lia.
  - (* lone_right *)
    simpl. exists lone_right. simpl. lia.
  - (* lfrl_left *)
    destruct (IH1 k) as [p Hp].
    assert (Hbf : closed (fup k b)) by (apply fup_closed; exact Hb).
    assert (e1 : map (fup k) (l1 ++ subs x b a :: l2)
                 = map (fup k) l1 ++ subs x (fup k b) (fup k a) :: map (fup k) l2).
    { rewrite (map_app (fup k) l1 (subs x b a :: l2)).
      simpl. rewrite fup_subs. reflexivity. }
    assert (e2 : map (fup k) l1 ++ lfrl x (fup k a) :: map (fup k) l2
                 = map (fup k) (l1 ++ lfrl x a :: l2)).
    { rewrite (map_app (fup k) l1 (lfrl x a :: l2)). reflexivity. }
    exists (lprove_cast e2 eq_refl
              (lfrl_left (a:=fup k a) (x:=x) (b:=fup k b) (c:=fup k c)
                 (l1:=map (fup k) l1) (l2:=map (fup k) l2) Hbf
                 (lprove_cast e1 eq_refl p))).
    lw_casts. lia.
  - (* lfrl_right *)
    destruct (IH1 (S k)) as [p Hp].
    assert (e1 : map (fup (S k)) (map fupz l) = map fupz (map (fup k) l))
      by (apply map_fup_comp).
    assert (e2 : fup (S k) (subs x (dvar 0) (fupz a))
                 = subs x (dvar 0) (fupz (fup k a))).
    { rewrite fup_subs. rewrite fup_dvar0_S. rewrite fup_comp. reflexivity. }
    exists (lfrl_right (fup k a) x (map (fup k) l) (lprove_cast e1 e2 p)).
    lw_casts. lia.
  - (* lexs_left *)
    destruct (IH1 (S k)) as [p Hp].
    assert (eL : map (fup (S k)) (map fupz l1)
                 ++ fup (S k) (subs x (dvar 0) (fupz a))
                    :: map (fup (S k)) (map fupz l2)
                 = map fupz (map (fup k) l1)
                   ++ subs x (dvar 0) (fupz (fup k a))
                      :: map fupz (map (fup k) l2)).
    { rewrite (map_fup_comp k l1). rewrite (map_fup_comp k l2).
      rewrite fup_subs. rewrite fup_dvar0_S. rewrite fup_comp. reflexivity. }
    assert (ea : fup (S k) (fupz c) = fupz (fup k c)).
    { apply fup_comp. }
    assert (ep : map (fup (S k)) (map fupz l1 ++ subs x (dvar 0) (fupz a) :: map fupz l2)
                 = map (fup (S k)) (map fupz l1)
                   ++ fup (S k) (subs x (dvar 0) (fupz a))
                      :: map (fup (S k)) (map fupz l2)).
    { rewrite (map_app (fup (S k)) (map fupz l1)
                 (subs x (dvar 0) (fupz a) :: map fupz l2)). reflexivity. }
    assert (eC : map (fup k) l1 ++ lexs x (fup k a) :: map (fup k) l2
                 = map (fup k) (l1 ++ lexs x a :: l2)).
    { rewrite (map_app (fup k) l1 (lexs x a :: l2)). reflexivity. }
    exists (lprove_cast eC eq_refl
              (lexs_left (fup k a) x (fup k c)
                 (map (fup k) l1) (map (fup k) l2)
                 (lprove_cast eL ea (lprove_cast ep eq_refl p)))).
    lw_casts. lia.
  - (* lexs_right *)
    destruct (IH1 k) as [p Hp].
    assert (Hbf : closed (fup k b)) by (apply fup_closed; exact Hb).
    assert (ea : fup k (subs x b a) = subs x (fup k b) (fup k a)).
    { apply fup_subs. }
    exists (lexs_right (a:=fup k a) (x:=x) (b:=fup k b) (l:=map (fup k) l) Hbf
              (lprove_cast eq_refl ea p)).
    lw_casts. lia.
Qed.

Lemma map_nsubs_fup_0 k b (L : list lform) :
  map (nsubs (S k) (fup 0 b)) (map fupz L) = map fupz (map (nsubs k b) L).
Proof.
  rewrite !map_map. apply map_ext. intro x. apply nsubs_fup_0.
Qed.

Lemma map_nsubs_app k b (L1 L2 : list lform) :
  map (nsubs k b) (L1 ++ L2) = map (nsubs k b) L1 ++ map (nsubs k b) L2.
Proof. apply map_app. Qed.

Lemma lprove_nsubs_weight : forall k t, closed t -> forall l a (pi : l ⊦ a),
  { pi' : map (nsubs k t) l ⊦ nsubs k t a | lweight pi' <= lweight pi }.
Proof.
  intros k t Ht l a pi. revert Ht. revert t. revert k.
  induction pi as
    [ a
    | l
    | a b c l1 l2 pi1 IH1
    | a b c l1 l2 pi1 IH1
    | a b l pi1 IH1 pi2 IH2
    | a b c l1 l2 l3 Hc0 pi1 IH1 pi2 IH2
    | a b l pi1 IH1
    | a l1 l2
    | a b c l1 l2 pi1 IH1 pi2 IH2
    | a b l pi1 IH1
    | a b l pi1 IH1
    | a l1 l2 pi1 IH1
    |
    | a x b0 c l1 l2 Hb0 pi1 IH1
    | a x l pi1 IH1
    | a x c l1 l2 pi1 IH1
    | a x b0 l Hb0 pi1 IH1
    ]; intros k t Ht.
  - (* lidentity *) simpl. exists (lidentity (nsubs k t a)). simpl. lia.
  - (* ltop_right *) simpl. exists (ltop_right (map (nsubs k t) l)). simpl. lia.
  - (* lwith_left1 *)
    destruct (IH1 k t Ht) as [p Hp].
    assert (e1 : map (nsubs k t) (l1 ++ a :: l2)
                 = map (nsubs k t) l1 ++ nsubs k t a :: map (nsubs k t) l2).
    { rewrite (map_app (nsubs k t) l1 (a :: l2)). reflexivity. }
    assert (e2 : map (nsubs k t) l1 ++ (nsubs k t a ∧ nsubs k t b) :: map (nsubs k t) l2
                 = map (nsubs k t) (l1 ++ (a ∧ b) :: l2)).
    { rewrite (map_app (nsubs k t) l1 ((a ∧ b) :: l2)). reflexivity. }
    exists (lprove_cast e2 eq_refl
              (lwith_left1 (nsubs k t a) (nsubs k t b) (nsubs k t c)
                 (map (nsubs k t) l1) (map (nsubs k t) l2)
                 (lprove_cast e1 eq_refl p))).
    lw_casts. lia.
  - (* lwith_left2 *)
    destruct (IH1 k t Ht) as [p Hp].
    assert (e1 : map (nsubs k t) (l1 ++ a :: l2)
                 = map (nsubs k t) l1 ++ nsubs k t a :: map (nsubs k t) l2).
    { rewrite (map_app (nsubs k t) l1 (a :: l2)). reflexivity. }
    assert (e2 : map (nsubs k t) l1 ++ (nsubs k t b ∧ nsubs k t a) :: map (nsubs k t) l2
                 = map (nsubs k t) (l1 ++ (b ∧ a) :: l2)).
    { rewrite (map_app (nsubs k t) l1 ((b ∧ a) :: l2)). reflexivity. }
    exists (lprove_cast e2 eq_refl
              (lwith_left2 (nsubs k t a) (nsubs k t b) (nsubs k t c)
                 (map (nsubs k t) l1) (map (nsubs k t) l2)
                 (lprove_cast e1 eq_refl p))).
    lw_casts. lia.
  - (* lwith_right *)
    destruct (IH1 k t Ht) as [p1 Hp1]. destruct (IH2 k t Ht) as [p2 Hp2].
    exists (lwith_right (nsubs k t a) (nsubs k t b) (map (nsubs k t) l) p1 p2).
    simpl. lia.
  - (* lmap_left *)
    destruct (IH1 k t Ht) as [p1 Hp1]. destruct (IH2 k t Ht) as [p2 Hp2].
    assert (H' : bp = true -> map (nsubs k t) l1 = [] /\ length (map (nsubs k t) l2) = 1%nat).
    { intros Hb'. specialize (Hc0 Hb'). destruct Hc0 as [H1 H2]. split.
      - rewrite H1. reflexivity.
      - rewrite length_map. exact H2. }
    assert (e2 : map (nsubs k t) (l1 ++ b :: l3)
                 = map (nsubs k t) l1 ++ nsubs k t b :: map (nsubs k t) l3).
    { rewrite (map_app (nsubs k t) l1 (b :: l3)). reflexivity. }
    assert (e3 : map (nsubs k t) l1
                 ++ (nsubs k t b / nsubs k t a)
                    :: (map (nsubs k t) l2 ++ map (nsubs k t) l3)
                 = map (nsubs k t) (l1 ++ (b / a) :: (l2 ++ l3))).
    { rewrite (map_app (nsubs k t) l1 ((b / a) :: (l2 ++ l3))).
      simpl. rewrite (map_app (nsubs k t) l2 l3). reflexivity. }
    exists (lprove_cast e3 eq_refl
              (lmap_left (nsubs k t a) (nsubs k t b) (nsubs k t c)
                 (map (nsubs k t) l1) (map (nsubs k t) l2) (map (nsubs k t) l3)
                 H' p1 (lprove_cast e2 eq_refl p2))).
    lw_casts. lia.
  - (* lmap_right *)
    destruct (IH1 k t Ht) as [p Hp].
    assert (e1 : map (nsubs k t) (l ++ [a]) = map (nsubs k t) l ++ [nsubs k t a]).
    { rewrite (map_app (nsubs k t) l [a]). reflexivity. }
    exists (lmap_right (nsubs k t a) (nsubs k t b) (map (nsubs k t) l)
              (lprove_cast e1 eq_refl p)).
    lw_casts. lia.
  - (* lzero_left *)
    assert (e2 : map (nsubs k t) l1 ++ lzero :: map (nsubs k t) l2
                 = map (nsubs k t) (l1 ++ lzero :: l2)).
    { rewrite (map_app (nsubs k t) l1 (lzero :: l2)). reflexivity. }
    exists (lprove_cast e2 eq_refl
              (lzero_left (nsubs k t a) (map (nsubs k t) l1) (map (nsubs k t) l2))).
    lw_casts. lia.
  - (* lplus_left *)
    destruct (IH1 k t Ht) as [p1 Hp1]. destruct (IH2 k t Ht) as [p2 Hp2].
    assert (e1 : map (nsubs k t) (l1 ++ a :: l2)
                 = map (nsubs k t) l1 ++ nsubs k t a :: map (nsubs k t) l2).
    { rewrite (map_app (nsubs k t) l1 (a :: l2)). reflexivity. }
    assert (e1b : map (nsubs k t) (l1 ++ b :: l2)
                  = map (nsubs k t) l1 ++ nsubs k t b :: map (nsubs k t) l2).
    { rewrite (map_app (nsubs k t) l1 (b :: l2)). reflexivity. }
    assert (e2 : map (nsubs k t) l1 ++ (nsubs k t a ∨ nsubs k t b) :: map (nsubs k t) l2
                 = map (nsubs k t) (l1 ++ (a ∨ b) :: l2)).
    { rewrite (map_app (nsubs k t) l1 ((a ∨ b) :: l2)). reflexivity. }
    exists (lprove_cast e2 eq_refl
              (lplus_left (nsubs k t a) (nsubs k t b) (nsubs k t c)
                 (map (nsubs k t) l1) (map (nsubs k t) l2)
                 (lprove_cast e1 eq_refl p1) (lprove_cast e1b eq_refl p2))).
    lw_casts. lia.
  - (* lplus_right1 *)
    destruct (IH1 k t Ht) as [p Hp].
    exists (lplus_right1 (nsubs k t a) (nsubs k t b) (map (nsubs k t) l) p).
    simpl. lia.
  - (* lplus_right2 *)
    destruct (IH1 k t Ht) as [p Hp].
    exists (lplus_right2 (nsubs k t a) (nsubs k t b) (map (nsubs k t) l) p).
    simpl. lia.
  - (* lone_left *)
    destruct (IH1 k t Ht) as [p Hp].
    assert (e1 : map (nsubs k t) (l1 ++ l2)
                 = map (nsubs k t) l1 ++ map (nsubs k t) l2).
    { rewrite (map_app (nsubs k t) l1 l2). reflexivity. }
    assert (e2 : map (nsubs k t) l1 ++ lone :: map (nsubs k t) l2
                 = map (nsubs k t) (l1 ++ lone :: l2)).
    { rewrite (map_app (nsubs k t) l1 (lone :: l2)). reflexivity. }
    exists (lprove_cast e2 eq_refl
              (lone_left (nsubs k t a) (map (nsubs k t) l1) (map (nsubs k t) l2)
                 (lprove_cast e1 eq_refl p))).
    lw_casts. lia.
  - (* lone_right *)
    simpl. exists lone_right. simpl. lia.
  - (* lfrl_left *)
    destruct (IH1 k t Ht) as [p Hp].
    assert (Hb'' : closed (nsubs k t b0)) by (apply nsubs_closed; assumption).
    assert (e1 : map (nsubs k t) (l1 ++ subs x b0 a :: l2)
                 = map (nsubs k t) l1
                   ++ subs x (nsubs k t b0) (nsubs k t a) :: map (nsubs k t) l2).
    { rewrite (map_app (nsubs k t) l1 (subs x b0 a :: l2)).
      simpl. rewrite (nsubs_subs k x t b0 a Ht). reflexivity. }
    assert (e2 : map (nsubs k t) l1 ++ lfrl x (nsubs k t a) :: map (nsubs k t) l2
                 = map (nsubs k t) (l1 ++ lfrl x a :: l2)).
    { rewrite (map_app (nsubs k t) l1 (lfrl x a :: l2)). reflexivity. }
    exists (lprove_cast e2 eq_refl
              (lfrl_left (a:=nsubs k t a) (x:=x) (b:=nsubs k t b0) (c:=nsubs k t c)
                 (l1:=map (nsubs k t) l1) (l2:=map (nsubs k t) l2) Hb''
                 (lprove_cast e1 eq_refl p))).
    lw_casts. lia.
  - (* lfrl_right *)
    destruct (IH1 (S k) (fup 0 t) (fup_closed 0 t Ht)) as [p Hp].
    assert (Hb' : closed (fup 0 t)) by (apply fup_closed; exact Ht).
    assert (e1 : map (nsubs (S k) (fup 0 t)) (map fupz l)
                 = map fupz (map (nsubs k t) l)) by (apply map_nsubs_fup_0).
    assert (e2 : nsubs (S k) (fup 0 t) (subs x (dvar 0) (fupz a))
                 = subs x (dvar 0) (fupz (nsubs k t a))).
    { apply nsubs_subs_fup_0. exact Ht. }
    exists (lfrl_right (nsubs k t a) x (map (nsubs k t) l)
              (lprove_cast e1 e2 p)).
    lw_casts. lia.
  - (* lexs_left *)
    destruct (IH1 (S k) (fup 0 t) (fup_closed 0 t Ht)) as [p Hp].
    assert (ep : map (nsubs (S k) (fup 0 t))
                    (map fupz l1 ++ subs x (dvar 0) (fupz a) :: map fupz l2)
                 = map (nsubs (S k) (fup 0 t)) (map fupz l1)
                   ++ nsubs (S k) (fup 0 t) (subs x (dvar 0) (fupz a))
                      :: map (nsubs (S k) (fup 0 t)) (map fupz l2)).
    { rewrite (map_app (nsubs (S k) (fup 0 t)) (map fupz l1)
                 (subs x (dvar 0) (fupz a) :: map fupz l2)). reflexivity. }
    assert (eL : map (nsubs (S k) (fup 0 t)) (map fupz l1)
                 ++ nsubs (S k) (fup 0 t) (subs x (dvar 0) (fupz a))
                    :: map (nsubs (S k) (fup 0 t)) (map fupz l2)
                 = map fupz (map (nsubs k t) l1)
                   ++ subs x (dvar 0) (fupz (nsubs k t a))
                      :: map fupz (map (nsubs k t) l2)).
    { rewrite (map_nsubs_fup_0 k t l1). rewrite (map_nsubs_fup_0 k t l2).
      rewrite (nsubs_subs_fup_0 k x t a Ht). reflexivity. }
    assert (ea : nsubs (S k) (fup 0 t) (fupz c) = fupz (nsubs k t c)).
    { apply nsubs_fup_0. }
    assert (eC : map (nsubs k t) l1 ++ lexs x (nsubs k t a) :: map (nsubs k t) l2
                 = map (nsubs k t) (l1 ++ lexs x a :: l2)).
    { rewrite (map_app (nsubs k t) l1 (lexs x a :: l2)). reflexivity. }
    exists (lprove_cast eC eq_refl
              (lexs_left (nsubs k t a) x (nsubs k t c)
                 (map (nsubs k t) l1) (map (nsubs k t) l2)
                 (lprove_cast eL ea (lprove_cast ep eq_refl p)))).
    lw_casts. lia.
  - (* lexs_right *)
    destruct (IH1 k t Ht) as [p Hp].
    assert (Hb'' : closed (nsubs k t b0)) by (apply nsubs_closed; assumption).
    assert (ea : nsubs k t (subs x b0 a) = subs x (nsubs k t b0) (nsubs k t a)).
    { apply nsubs_subs. exact Ht. }
    exists (lexs_right (a:=nsubs k t a) (x:=x) (b:=nsubs k t b0) (l:=map (nsubs k t) l)
              Hb'' (lprove_cast eq_refl ea p)).
    lw_casts. lia.
Qed.

Lemma lweight_pos l a (pi : l ⊦ a) : 1 <= lweight pi.
Proof. destruct pi; simpl; lia. Qed.

Lemma app_single_inv (PL : list lform) (FA : lform) (SL : list lform) x :
  PL ++ FA :: SL = [x] -> PL = [] /\ SL = [] /\ FA = x.
Proof.
  intros H.
  assert (Hlen : length (PL ++ FA :: SL) = 1%nat).
  { rewrite H. reflexivity. }
  rewrite length_app in Hlen. simpl in Hlen.
  destruct PL; [| simpl in Hlen; lia].
  destruct SL; [| simpl in Hlen; lia].
  simpl in H. injection H as HFA. subst. auto.
Qed.

Lemma map_fupz_nil_iff (L : list lform) : map fupz L = [] <-> L = [].
Proof. split; [apply map_eq_nil | intros ->; reflexivity]. Qed.

Lemma map_nsubs_nil_iff k b (L : list lform) : map (nsubs k b) L = [] <-> L = [].
Proof. split; [apply map_eq_nil | intros ->; reflexivity]. Qed.

Lemma map_nsubs_fupz b (L : list lform) : map (nsubs 0 b) (map fupz L) = L.
Proof.
  rewrite !map_map.
  assert (e : map (fun x => nsubs 0 b (fup 0 x)) L = map id L)
    by (apply map_ext; intro x; apply nsubs_fup).
  rewrite e, map_id. reflexivity.
Qed.

Lemma lprove_zero_nil (q : ([] : list lform) ⊦ lzero) : False.
Proof.
  remember ([] : list lform) as L eqn:EL.
  remember lzero as F eqn:EF.
  revert EL EF.
  induction q; intros EL EF.
  - (* identity *) exfalso. apply (f_equal (@length lform)) in EL. simpl in EL. lia.
  - (* top *) discriminate EF.
  - (* with_left1 *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* with_left2 *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* with_right *) discriminate EF.
  - (* map_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* map_right *) discriminate EF.
  - (* zero_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* plus_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* plus_right1 *) discriminate EF.
  - (* plus_right2 *) discriminate EF.
  - (* lone_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* lone_right *) discriminate EF.
  - (* frl_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* frl_right *) discriminate EF.
  - (* lexs_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* lexs_right *) discriminate EF.
Qed.

Lemma nil_with_inv a b (q : ([] : list lform) ⊦ a ∧ b) :
  { qa : ([] : list lform) ⊦ a &
    { qb : ([] : list lform) ⊦ b &
      lweight qa <= lweight q /\ lweight qb <= lweight q } }.
Proof.
  remember ([] : list lform) as L eqn:EL.
  remember (a ∧ b) as F eqn:EF.
  revert EL EF.
  induction q; intros EL EF.
  - (* identity *) exfalso. apply (f_equal (@length lform)) in EL. simpl in EL. lia.
  - (* top *) discriminate EF.
  - (* with_left1 *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* with_left2 *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* with_right *) injection EF as -> ->. subst.
    exists q1. exists q2. split; simpl; lia.
  - (* map_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* map_right *) discriminate EF.
  - (* zero_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* plus_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* plus_right1 *) discriminate EF.
  - (* plus_right2 *) discriminate EF.
  - (* lone_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* lone_right *) discriminate EF.
  - (* frl_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* frl_right *) discriminate EF.
  - (* lexs_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* lexs_right *) discriminate EF.
Qed.

Lemma nil_plus_inv a b (q : ([] : list lform) ⊦ a ∨ b) :
  { qa : ([] : list lform) ⊦ a & lweight qa <= lweight q } +
  { qb : ([] : list lform) ⊦ b & lweight qb <= lweight q }.
Proof.
  remember ([] : list lform) as L eqn:EL.
  remember (a ∨ b) as F eqn:EF.
  revert EL EF.
  induction q; intros EL EF.
  - (* identity *) exfalso. apply (f_equal (@length lform)) in EL. simpl in EL. lia.
  - (* top *) discriminate EF.
  - (* with_left1 *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* with_left2 *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* with_right *) discriminate EF.
  - (* map_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* map_right *) discriminate EF.
  - (* zero_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* plus_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* plus_right1 *) injection EF as -> ->. subst. left.
    match goal with qq : [] ⊦ a |- _ => exists qq; simpl; lia end.
  - (* plus_right2 *) injection EF as -> ->. subst. right.
    match goal with qq : [] ⊦ b |- _ => exists qq; simpl; lia end.
  - (* lone_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* lone_right *) discriminate EF.
  - (* frl_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* frl_right *) discriminate EF.
  - (* lexs_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* lexs_right *) discriminate EF.
Qed.

Lemma nil_lfrl_inv x a (q : ([] : list lform) ⊦ lfrl x a) :
  { q' : ([] : list lform) ⊦ subs x (dvar 0) (fupz a) & lweight q' <= lweight q }.
Proof.
  remember ([] : list lform) as L eqn:EL.
  remember (lfrl x a) as F eqn:EF.
  revert EL EF.
  induction q; intros EL EF.
  - (* identity *) exfalso. apply (f_equal (@length lform)) in EL. simpl in EL. lia.
  - (* top *) discriminate EF.
  - (* with_left1 *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* with_left2 *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* with_right *) discriminate EF.
  - (* map_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* map_right *) discriminate EF.
  - (* zero_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* plus_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* plus_right1 *) discriminate EF.
  - (* plus_right2 *) discriminate EF.
  - (* lone_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* lone_right *) discriminate EF.
  - (* frl_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* frl_right *) injection EF as -> ->. subst.
    match goal with qq : map fupz [] ⊦ ?T |- _ => simpl in qq; exists qq; simpl; lia end.
  - (* lexs_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* lexs_right *) discriminate EF.
Qed.

Lemma nil_lexs_inv x a (q : ([] : list lform) ⊦ lexs x a) :
  { b : lform & { Hb : closed b &
    { q' : ([] : list lform) ⊦ subs x b a & lweight q' <= lweight q } } }.
Proof.
  remember ([] : list lform) as L eqn:EL.
  remember (lexs x a) as F eqn:EF.
  revert EL EF.
  induction q; intros EL EF.
  - (* identity *) exfalso. apply (f_equal (@length lform)) in EL. simpl in EL. lia.
  - (* top *) discriminate EF.
  - (* with_left1 *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* with_left2 *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* with_right *) discriminate EF.
  - (* map_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* map_right *) discriminate EF.
  - (* zero_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* plus_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* plus_right1 *) discriminate EF.
  - (* plus_right2 *) discriminate EF.
  - (* lone_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* lone_right *) discriminate EF.
  - (* frl_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* frl_right *) discriminate EF.
  - (* lexs_left *) exfalso. apply (f_equal (@length lform)) in EL. rewrite length_app in EL. simpl in EL. lia.
  - (* lexs_right *) injection EF as -> ->. subst.
    match goal with Hb0 : closed ?b, qq : [] ⊦ ?T |- _ =>
      exists b; exists Hb0; exists qq; simpl; lia end.
Qed.

Definition cut_ok (n : nat) : Type :=
  forall a b l1 l2 l3 (pi1 : l2 ⊦ a) (pi2 : l1 ++ a :: l3 ⊦ b),
    lweight pi1 + lweight pi2 <= n ->
    (bp = true -> l1 <> [] -> length l2 = 1%nat) ->
    { pi' : l1 ++ l2 ++ l3 ⊦ b | lweight pi' < lweight pi1 + lweight pi2 }.

Lemma cut_with_left1 (n : nat) (H : cut_ok n) PL SL (B c : lform)
  (RL1 RL2 : list lform) (x y : lform)
  (q : RL1 ++ x :: RL2 ⊦ c) (pi2 : PL ++ c :: SL ⊦ B)
  (Hle : lweight (lwith_left1 x y c RL1 RL2 q) + lweight pi2 <= S n)
  (Hc : bp = true -> PL <> [] -> length (RL1 ++ x :: RL2) = 1%nat) :
  { r : PL ++ (RL1 ++ (x ∧ y) :: RL2) ++ SL ⊦ B
  | lweight r < lweight (lwith_left1 x y c RL1 RL2 q) + lweight pi2 }.
Proof.
  simpl in Hle.
  assert (Hb : lweight q + lweight pi2 <= n) by lia.
  destruct (H c B PL (RL1 ++ x :: RL2) SL q pi2 Hb Hc) as [r Hr].
  assert (e2 : PL ++ (RL1 ++ x :: RL2) ++ SL = (PL ++ RL1) ++ x :: (RL2 ++ SL)).
  { repeat rewrite <- app_assoc. reflexivity. }
  assert (e3 : (PL ++ RL1) ++ (x ∧ y) :: (RL2 ++ SL)
               = PL ++ (RL1 ++ (x ∧ y) :: RL2) ++ SL).
  { repeat rewrite <- app_assoc. reflexivity. }
  exists (lprove_cast e3 eq_refl
            (lwith_left1 x y B (PL ++ RL1) (RL2 ++ SL) (lprove_cast e2 eq_refl r))).
  lw_casts. simpl. lia.
Qed.

Lemma cut_with_left2 (n : nat) (H : cut_ok n) PL SL (B c : lform)
  (RL1 RL2 : list lform) (x y : lform)
  (q : RL1 ++ x :: RL2 ⊦ c) (pi2 : PL ++ c :: SL ⊦ B)
  (Hle : lweight (lwith_left2 x y c RL1 RL2 q) + lweight pi2 <= S n)
  (Hc : bp = true -> PL <> [] -> length (RL1 ++ x :: RL2) = 1%nat) :
  { r : PL ++ (RL1 ++ (y ∧ x) :: RL2) ++ SL ⊦ B
  | lweight r < lweight (lwith_left2 x y c RL1 RL2 q) + lweight pi2 }.
Proof.
  simpl in Hle.
  assert (Hb : lweight q + lweight pi2 <= n) by lia.
  destruct (H c B PL (RL1 ++ x :: RL2) SL q pi2 Hb Hc) as [r Hr].
  assert (e2 : PL ++ (RL1 ++ x :: RL2) ++ SL = (PL ++ RL1) ++ x :: (RL2 ++ SL)).
  { repeat rewrite <- app_assoc. reflexivity. }
  assert (e3 : (PL ++ RL1) ++ (y ∧ x) :: (RL2 ++ SL)
               = PL ++ (RL1 ++ (y ∧ x) :: RL2) ++ SL).
  { repeat rewrite <- app_assoc. reflexivity. }
  exists (lprove_cast e3 eq_refl
            (lwith_left2 x y B (PL ++ RL1) (RL2 ++ SL) (lprove_cast e2 eq_refl r))).
  lw_casts. simpl. lia.
Qed.

Lemma cut_plus_left (n : nat) (H : cut_ok n) PL SL (B c : lform)
  (RL1 RL2 : list lform) (x y : lform)
  (q1 : RL1 ++ x :: RL2 ⊦ c) (q2 : RL1 ++ y :: RL2 ⊦ c)
  (pi2 : PL ++ c :: SL ⊦ B)
  (Hle : lweight (lplus_left x y c RL1 RL2 q1 q2) + lweight pi2 <= S n)
  (Hc : bp = true -> PL <> [] -> length (RL1 ++ x :: RL2) = 1%nat) :
  { r : PL ++ (RL1 ++ (x ∨ y) :: RL2) ++ SL ⊦ B
  | lweight r < lweight (lplus_left x y c RL1 RL2 q1 q2) + lweight pi2 }.
Proof.
  simpl in Hle.
  assert (Hcx : bp = true -> PL <> [] -> length (RL1 ++ x :: RL2) = 1%nat) by exact Hc.
  assert (Hcy : bp = true -> PL <> [] -> length (RL1 ++ y :: RL2) = 1%nat).
  { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
  assert (Hb1 : lweight q1 + lweight pi2 <= n) by lia.
  assert (Hb2 : lweight q2 + lweight pi2 <= n) by lia.
  destruct (H c B PL (RL1 ++ x :: RL2) SL q1 pi2 Hb1 Hcx) as [r1 Hr1].
  destruct (H c B PL (RL1 ++ y :: RL2) SL q2 pi2 Hb2 Hcy) as [r2 Hr2].
  assert (e2 : PL ++ (RL1 ++ x :: RL2) ++ SL = (PL ++ RL1) ++ x :: (RL2 ++ SL)).
  { repeat rewrite <- app_assoc. reflexivity. }
  assert (e2b : PL ++ (RL1 ++ y :: RL2) ++ SL = (PL ++ RL1) ++ y :: (RL2 ++ SL)).
  { repeat rewrite <- app_assoc. reflexivity. }
  assert (e3 : (PL ++ RL1) ++ (x ∨ y) :: (RL2 ++ SL)
               = PL ++ (RL1 ++ (x ∨ y) :: RL2) ++ SL).
  { repeat rewrite <- app_assoc. reflexivity. }
  exists (lprove_cast e3 eq_refl
            (lplus_left x y B (PL ++ RL1) (RL2 ++ SL)
               (lprove_cast e2 eq_refl r1) (lprove_cast e2b eq_refl r2))).
  lw_casts. simpl. lia.
Qed.

Lemma cut_lfrl_left (n : nat) (H : cut_ok n) PL SL (B c : lform)
  (RL1 RL2 : list lform) (x : nat) (mb ma : lform)
  (Hb0 : closed mb) (q : RL1 ++ subs x mb ma :: RL2 ⊦ c)
  (pi2 : PL ++ c :: SL ⊦ B)
  (Hle : lweight (@lfrl_left bp ma x mb c RL1 RL2 Hb0 q) + lweight pi2 <= S n)
  (Hc : bp = true -> PL <> [] -> length (RL1 ++ subs x mb ma :: RL2) = 1%nat) :
  { r : PL ++ (RL1 ++ lfrl x ma :: RL2) ++ SL ⊦ B
  | lweight r < lweight (@lfrl_left bp ma x mb c RL1 RL2 Hb0 q) + lweight pi2 }.
Proof.
  simpl in Hle.
  assert (Hb : lweight q + lweight pi2 <= n) by lia.
  destruct (H c B PL (RL1 ++ subs x mb ma :: RL2) SL q pi2 Hb Hc) as [r Hr].
  assert (e2 : PL ++ (RL1 ++ subs x mb ma :: RL2) ++ SL
               = (PL ++ RL1) ++ subs x mb ma :: (RL2 ++ SL)).
  { repeat rewrite <- app_assoc. reflexivity. }
  assert (e3 : (PL ++ RL1) ++ lfrl x ma :: (RL2 ++ SL)
               = PL ++ (RL1 ++ lfrl x ma :: RL2) ++ SL).
  { repeat rewrite <- app_assoc. reflexivity. }
  exists (lprove_cast e3 eq_refl
            (@lfrl_left bp ma x mb B (PL ++ RL1) (RL2 ++ SL) Hb0 (lprove_cast e2 eq_refl r))).
  lw_casts. simpl. lia.
Qed.

Lemma cut_lexs_left (n : nat) (H : cut_ok n) PL SL (B c : lform)
  (RL1 RL2 : list lform) (x : nat) (ma : lform)
  (q : map fupz RL1 ++ subs x (dvar 0) (fupz ma) :: map fupz RL2 ⊦ fupz c)
  (pi2 : PL ++ c :: SL ⊦ B)
  (Hle : lweight (lexs_left ma x c RL1 RL2 q) + lweight pi2 <= S n)
  (Hc : bp = true -> PL <> [] -> length (RL1 ++ lexs x ma :: RL2) = 1%nat) :
  { r : PL ++ (RL1 ++ lexs x ma :: RL2) ++ SL ⊦ B
  | lweight r < lweight (lexs_left ma x c RL1 RL2 q) + lweight pi2 }.
Proof.
  simpl in Hle.
  assert (Hcq : bp = true -> PL <> []
                -> length (map fupz RL1 ++ subs x (dvar 0) (fupz ma) :: map fupz RL2) = 1%nat).
  { intros Hb HN. 
    assert (Hlen : length (RL1 ++ lexs x ma :: RL2) = 1%nat) by (apply Hc; assumption).
    repeat rewrite length_app in *. simpl in *.
    repeat rewrite length_map. lia. }
  assert (Hc' : bp = true -> map fupz PL <> []
                -> length (map fupz RL1 ++ subs x (dvar 0) (fupz ma) :: map fupz RL2) = 1%nat).
  { intros Hb HN. apply Hcq; [exact Hb|].
    intro Hnil. apply HN. apply map_fupz_nil_iff in Hnil. rewrite Hnil. reflexivity. }
  destruct (lprove_fup_weight 0 pi2) as [sp Hsp].
  assert (ep : map fupz (PL ++ c :: SL) = map fupz PL ++ fupz c :: map fupz SL).
  { rewrite (map_app (fup 0) PL (c :: SL)). reflexivity. }
  assert (Hb : lweight q + lweight (lprove_cast ep eq_refl sp) <= n).
  { rewrite lweight_lprove_cast. assert (lweight sp <= lweight pi2) by exact Hsp. lia. }
  destruct (H (fup 0 c) (fup 0 B) (map fupz PL)
              (map fupz RL1 ++ subs x (dvar 0) (fupz ma) :: map fupz RL2)
              (map fupz SL) q (lprove_cast ep eq_refl sp) Hb Hc') as [r Hr].
  assert (e2 : map fupz PL
               ++ (map fupz RL1 ++ subs x (dvar 0) (fupz ma) :: map fupz RL2)
               ++ map fupz SL
               = map fupz (PL ++ RL1) ++ subs x (dvar 0) (fupz ma) :: map fupz (RL2 ++ SL)).
  { rewrite (map_app (fup 0) PL RL1). rewrite (map_app (fup 0) RL2 SL).
    repeat rewrite <- app_assoc. reflexivity. }
  assert (e3 : (PL ++ RL1) ++ lexs x ma :: (RL2 ++ SL)
               = PL ++ (RL1 ++ lexs x ma :: RL2) ++ SL).
  { repeat rewrite <- app_assoc. reflexivity. }
  exists (lprove_cast e3 eq_refl
            (lexs_left ma x B (PL ++ RL1) (RL2 ++ SL) (lprove_cast e2 eq_refl r))).
  rewrite lweight_lprove_cast in Hr. lw_casts. simpl. lia.
Qed.

Lemma cut_lmap_left (n : nat) (H : cut_ok n) PL SL (B c : lform)
  (RL1 RL2 RL3 : list lform) (ma mb : lform)
  (Hmap : bp = true -> RL1 = [] /\ length RL2 = 1%nat)
  (qa : RL2 ⊦ ma) (qb : RL1 ++ mb :: RL3 ⊦ c)
  (pi2 : PL ++ c :: SL ⊦ B)
  (Hle : lweight (@lmap_left bp ma mb c RL1 RL2 RL3 Hmap qa qb) + lweight pi2 <= S n)
  (Hc : bp = true -> PL <> [] -> length (RL1 ++ (mb / ma) :: RL2 ++ RL3) = 1%nat) :
  { r : PL ++ (RL1 ++ (mb / ma) :: RL2 ++ RL3) ++ SL ⊦ B
  | lweight r < lweight (@lmap_left bp ma mb c RL1 RL2 RL3 Hmap qa qb) + lweight pi2 }.
Proof.
  simpl in Hle.
  assert (Hcqb : bp = true -> PL <> [] -> length (RL1 ++ mb :: RL3) = 1%nat).
  { intros Hb HN. specialize (Hc Hb HN).
    repeat rewrite length_app in *. simpl in *.
    repeat rewrite length_app in Hc. simpl in Hc. lia. }
  assert (Hb : lweight qb + lweight pi2 <= n) by lia.
  destruct (H c B PL (RL1 ++ mb :: RL3) SL qb pi2 Hb Hcqb) as [r Hr].
  assert (H' : bp = true -> PL ++ RL1 = [] /\ length RL2 = 1%nat).
  { intros Hbp. specialize (Hmap Hbp). destruct Hmap as [H1 H2]. split.
    - destruct PL as [|p PL']; [rewrite H1; reflexivity|].
      exfalso. assert (Hlen : length (RL1 ++ (mb / ma) :: RL2 ++ RL3) = 1%nat)
        by (apply Hc; [exact Hbp| discriminate]).
      subst RL1. simpl in Hlen. rewrite length_app in Hlen. simpl in Hlen. lia.
    - exact H2. }
  assert (e2 : PL ++ (RL1 ++ mb :: RL3) ++ SL
               = (PL ++ RL1) ++ mb :: (RL3 ++ SL)).
  { repeat rewrite <- app_assoc. reflexivity. }
  assert (e3 : (PL ++ RL1) ++ (mb / ma) :: RL2 ++ (RL3 ++ SL)
               = PL ++ (RL1 ++ (mb / ma) :: RL2 ++ RL3) ++ SL).
  { repeat rewrite app_assoc.
    rewrite <- (app_assoc (PL ++ RL1) ((mb / ma) :: (RL2 ++ RL3)) SL). reflexivity. }
  exists (lprove_cast e3 eq_refl
            (lmap_left ma mb B (PL ++ RL1) RL2 (RL3 ++ SL) H' qa (lprove_cast e2 eq_refl r))).
  lw_casts. simpl. lia.
Qed.

Lemma cut_lone_left (n : nat) (H : cut_ok n) PL SL (B c : lform)
  (RL1 RL2 : list lform)
  (q : RL1 ++ RL2 ⊦ c) (pi2 : PL ++ c :: SL ⊦ B)
  (Hle : lweight (lone_left c RL1 RL2 q) + lweight pi2 <= S n)
  (Hc : bp = true -> PL <> [] -> length (RL1 ++ RL2) = 1%nat) :
  { r : PL ++ (RL1 ++ lone :: RL2) ++ SL ⊦ B
  | lweight r < lweight (lone_left c RL1 RL2 q) + lweight pi2 }.
Proof.
  simpl in Hle.
  assert (Hb : lweight q + lweight pi2 <= n) by lia.
  destruct (H c B PL (RL1 ++ RL2) SL q pi2 Hb Hc) as [r Hr].
  assert (e2 : PL ++ (RL1 ++ RL2) ++ SL = (PL ++ RL1) ++ RL2 ++ SL).
  { repeat rewrite app_assoc. reflexivity. }
  assert (e3 : (PL ++ RL1) ++ lone :: (RL2 ++ SL)
               = PL ++ (RL1 ++ lone :: RL2) ++ SL).
  { repeat rewrite app_assoc.
    rewrite <- (app_assoc (PL ++ RL1) (lone :: RL2) SL). reflexivity. }
  exists (lprove_cast e3 eq_refl
            (lone_left B (PL ++ RL1) (RL2 ++ SL) (lprove_cast e2 eq_refl r))).
  lw_casts. simpl. lia.
Qed.

Lemma lprove_trans_aux : forall n a b l1 l2 l3 (pi1 : l2 ⊦ a) (pi2 : l1 ++ a :: l3 ⊦ b),
  lweight pi1 + lweight pi2 <= n ->
  (bp = true -> l1 <> [] -> length l2 = 1%nat) ->
  { pi' : l1 ++ l2 ++ l3 ⊦ b | lweight pi' < lweight pi1 + lweight pi2 }.
Proof.
  induction n as [|n IH].
  - intros a b l1 l2 l3 pi1 pi2 Hle Hc.
    exfalso. pose proof (lweight_pos pi1). pose proof (lweight_pos pi2). lia.
  - intros a b l1 l2 l3 pi1 pi2 Hle Hc.
    remember (l1 ++ a :: l3) as L eqn:HL.
    revert Hle. revert pi1. revert Hc. revert HL.
    revert a. revert l3. revert l2. revert l1.
    induction pi2 as
      [ a0
      | l0
      | a0 b0 c0 l1' l2' q1 IH1
      | a0 b0 c0 l1' l2' q1 IH1
      | a0 b0 l0 q1 IH1 q2 IH2
      | a0 b0 c0 l1' l2' l3' Hmap q1 IH1 q2 IH2
      | a0 b0 l0 q1 IH1
      | a0 l1' l2'
      | a0 b0 c0 l1' l2' q1 IH1 q2 IH2
      | a0 b0 l0 q1 IH1
      | a0 b0 l0 q1 IH1
      | a0 l1' l2' q1 IH1
      |
      | a0 x0 b0 c0 l1' l2' Hb0 q1 IH1
      | a0 x0 l0 q1 IH1
      | a0 x0 c0 l1' l2' q1 IH1
      | a0 x0 b0 l0 Hb0 q1 IH1
      ]; intros PL DL SL FA HL Hc pi1 Hle; pose proof (lweight_pos pi1) as Hpos.
  + (* lidentity *)
    destruct (app_single_inv PL FA SL (eq_sym HL)) as [HPL [HSL HFA]].
    subst PL. subst SL. subst FA.
    exists (lprove_cast (eq_sym (app_nil_r DL)) eq_refl pi1).
    lw_casts. simpl. lia.
  + (* ltop_right *)
    simpl. exists (ltop_right (PL ++ DL ++ SL)). simpl. lia.
  + (* lwith_left1 *)
    simpl in Hle.
    destruct (elt_eq_elt_trichotT PL FA SL l1' (lwith a0 b0) l2' (eq_sym HL))
      as [HA | HC].
    * destruct HA as [H1 | H2].
      -- (* FA in RL1 *)
         destruct H1 as [m HRL1 HSL].
         assert (e1 : l1' ++ a0 :: l2' = PL ++ FA :: (m ++ a0 :: l2')).
         { rewrite <- HRL1. rewrite <- app_assoc. reflexivity. }
         assert (Hb1 : lweight pi1 + lweight (lprove_cast e1 eq_refl q1) <= n).
         { rewrite lweight_lprove_cast. lia. }
         destruct (IH FA c0 PL DL (m ++ a0 :: l2') pi1 (lprove_cast e1 eq_refl q1) Hb1 Hc) as [p Hp].
         rewrite lweight_lprove_cast in Hp.
         assert (e2 : PL ++ DL ++ (m ++ a0 :: l2') = (PL ++ DL ++ m) ++ a0 :: l2').
         { repeat rewrite app_assoc. reflexivity. }
         assert (e3 : (PL ++ DL ++ m) ++ (a0 ∧ b0) :: l2' = PL ++ DL ++ SL).
         { rewrite HSL. repeat rewrite app_assoc. reflexivity. }
         exists (lprove_cast e3 eq_refl
                  (lwith_left1 a0 b0 c0 (PL ++ DL ++ m) l2'
                     (lprove_cast e2 eq_refl p))).
         lw_casts. simpl. lia.
      -- (* principal *)
         destruct H2 as [HPL [HFA HSL]]. subst PL. subst SL.
         assert (eP : l1' ++ (a0 ∧ b0) :: l2' = l1' ++ FA :: l2').
         { rewrite HFA. reflexivity. }
         set (pi2c := lprove_cast eP eq_refl (lwith_left1 a0 b0 c0 l1' l2' q1)).
         destruct pi1 as
           [ x0 | K1 | x0 y0 z0 K1 K2 p0 | x0 y0 z0 K1 K2 p0
           | x0 y0 K1 p0 p1 | x0 y0 z0 K1 K2 K3 Hm p0 p1 | x0 y0 K1 p0
           | x0 K1 K2 | x0 y0 z0 K1 K2 p0 p1 | x0 y0 K1 p0 | x0 y0 K1 p0
           | x0 K1 K2 p0 | | x0 xr y0 z0 K1 K2 Hb0 p0 | x0 xr K1 p0
           | x0 xr z0 K1 K2 p0 | x0 xr y0 K1 Hb0 p0 ].
         ++ (* identity *)
            exists pi2c. unfold pi2c. rewrite lweight_lprove_cast. simpl. lia.
         ++ (* top *) discriminate HFA.
         ++ (* with_left1 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left1 x0 y0 z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left1 n IH l1' l2' c0 _ K1 K2 x0 y0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_left2 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left2 x0 y0 z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left2 n IH l1' l2' c0 _ K1 K2 x0 y0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_right *)
            injection HFA as Hx Hy. subst x0. subst y0.
            simpl in Hle. assert (Hb : lweight p0 + lweight q1 <= n) by lia.
            destruct (IH a0 c0 l1' K1 l2' p0 q1 Hb Hc) as [r Hr].
            exists r. simpl. lia.
         ++ (* map_left *)
            assert (Hle' : lweight (lmap_left x0 y0 z0 K1 K2 K3 Hm p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lmap_left n IH l1' l2' c0 _ K1 K2 K3 x0 y0 Hm p0 p1 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* map_right *) discriminate HFA.
         ++ (* zero_left *)
            assert (Hle' : lweight (lzero_left x0 K1 K2) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            assert (e3 : (l1' ++ K1) ++ lzero :: (K2 ++ l2')
                         = l1' ++ (K1 ++ lzero :: K2) ++ l2').
            { repeat rewrite app_assoc.
              rewrite <- (app_assoc (l1' ++ K1) (lzero :: K2) l2'). reflexivity. }
            assert (Hpos2 : 1 <= lweight (lwith_left1 a0 b0 c0 l1' l2' q1)) by apply lweight_pos.
            exists (lprove_cast e3 eq_refl (lzero_left c0 (l1' ++ K1) (K2 ++ l2'))).
            lw_casts. simpl. lia.
         ++ (* plus_left *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lplus_left x0 y0 z0 K1 K2 p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_plus_left n IH l1' l2' c0 _ K1 K2 x0 y0 p0 p1 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* plus_right1 *) discriminate HFA.
         ++ (* plus_right2 *) discriminate HFA.
         ++ (* lone_left *)
            destruct K1 as [|k1 K1']; destruct K2 as [|k2 K2'].
            ** (* singleton *)
               pose (p0' := lprove_cast (eq_refl : ([] : list lform) = []) HFA p0).
               assert (Hqp : lweight p0' = lweight p0) by (unfold p0'; apply lweight_lprove_cast).
               destruct (nil_with_inv p0') as [qa [qb [Hqa Hqb]]].
               simpl in Hle.
               assert (Hqa2 : lweight qa <= lweight p0) by lia.
               assert (Hb : lweight (lone_left a0 [] [] qa) + lweight q1 <= n).
               { simpl. assert (H1 : lweight p0 + S (lweight q1) <= n).
                 { apply le_S_n. exact Hle. }
                 assert (H2 : lweight qa + lweight q1 < n) by lia.
                 lia. }
               assert (Hc1 : bp = true -> l1' <> [] -> length ([lone] : list lform) = 1%nat)
                 by (intros; reflexivity).
               destruct (IH a0 c0 l1' [lone] l2' (lone_left a0 [] [] qa) q1 Hb Hc1) as [r Hr].
               simpl in Hr. exists r. simpl.
               assert (Hle2 : lweight qa + lweight q1 <= lweight p0 + S (lweight q1)) by lia.
               assert (Hle3 : S (lweight qa + lweight q1) <= S (lweight p0 + S (lweight q1))) by lia.
               eapply Nat.lt_le_trans; [exact Hr | exact Hle3].
            ** assert (Hc1 : bp = true -> l1' <> [] -> length ([] ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 [] (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ [] (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ []) = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 (k1 :: K1') [] p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ (k1 :: K1') [] p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 (k1 :: K1') (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ (k1 :: K1') (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
         ++ (* lone_right *) discriminate HFA.
         ++ (* frl_left *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ subs xr y0 x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (@lfrl_left bp x0 xr y0 z0 K1 K2 Hb0 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lfrl_left n IH l1' l2' c0 _ K1 K2 xr y0 x0 Hb0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* frl_right *) discriminate HFA.
         ++ (* lexs_left *)
            assert (Hle' : lweight (lexs_left x0 xr z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lexs_left n IH l1' l2' c0 _ K1 K2 xr x0 p0 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* lexs_right *) discriminate HFA.
    * (* FA in RL2 *)
      destruct HC as [m HPL HRL2].
      assert (e1 : l1' ++ a0 :: l2' = (l1' ++ a0 :: m) ++ FA :: SL).
      { rewrite <- HRL2. rewrite <- app_assoc. reflexivity. }
      assert (Hb1 : lweight pi1 + lweight (lprove_cast e1 eq_refl q1) <= n).
      { rewrite lweight_lprove_cast. lia. }
      assert (Hc1 : bp = true -> l1' ++ a0 :: m <> [] -> length DL = 1%nat).
      { intros Hb HN. apply Hc; [exact Hb|]. rewrite HPL. intro Hnil. apply (f_equal (@length lform)) in Hnil. rewrite length_app in Hnil. simpl in Hnil. lia. }
      destruct (IH FA c0 (l1' ++ a0 :: m) DL SL pi1 (lprove_cast e1 eq_refl q1) Hb1 Hc1) as [p Hp].
      rewrite lweight_lprove_cast in Hp.
      assert (e2 : (l1' ++ a0 :: m) ++ DL ++ SL = l1' ++ a0 :: (m ++ DL ++ SL)).
      { repeat rewrite <- app_assoc. reflexivity. }
      assert (e3 : l1' ++ (a0 ∧ b0) :: (m ++ DL ++ SL) = PL ++ DL ++ SL).
      { rewrite HPL. repeat rewrite <- app_assoc. reflexivity. }
      exists (lprove_cast e3 eq_refl
               (lwith_left1 a0 b0 c0 l1' (m ++ DL ++ SL)
                  (lprove_cast e2 eq_refl p))).
      lw_casts. simpl. lia.
  + (* lwith_left2 *)
    simpl in Hle.
    destruct (elt_eq_elt_trichotT PL FA SL l1' (lwith b0 a0) l2' (eq_sym HL))
      as [HA | HC].
    * destruct HA as [H1 | H2].
      -- destruct H1 as [m HRL1 HSL].
         assert (e1 : l1' ++ a0 :: l2' = PL ++ FA :: (m ++ a0 :: l2')).
         { rewrite <- HRL1. rewrite <- app_assoc. reflexivity. }
         assert (Hb1 : lweight pi1 + lweight (lprove_cast e1 eq_refl q1) <= n).
         { rewrite lweight_lprove_cast. lia. }
         destruct (IH FA c0 PL DL (m ++ a0 :: l2') pi1 (lprove_cast e1 eq_refl q1) Hb1 Hc) as [p Hp].
         rewrite lweight_lprove_cast in Hp.
         assert (e2 : PL ++ DL ++ (m ++ a0 :: l2') = (PL ++ DL ++ m) ++ a0 :: l2').
         { repeat rewrite app_assoc. reflexivity. }
         assert (e3 : (PL ++ DL ++ m) ++ (b0 ∧ a0) :: l2' = PL ++ DL ++ SL).
         { rewrite HSL. repeat rewrite app_assoc. reflexivity. }
         exists (lprove_cast e3 eq_refl
                  (lwith_left2 a0 b0 c0 (PL ++ DL ++ m) l2'
                     (lprove_cast e2 eq_refl p))).
         lw_casts. simpl. lia.
      -- (* principal *)
         destruct H2 as [HPL [HFA HSL]]. subst PL. subst SL.
         assert (eP : l1' ++ (b0 ∧ a0) :: l2' = l1' ++ FA :: l2').
         { rewrite HFA. reflexivity. }
         set (pi2c := lprove_cast eP eq_refl (lwith_left2 a0 b0 c0 l1' l2' q1)).
         destruct pi1 as
           [ x0 | K1 | x0 y0 z0 K1 K2 p0 | x0 y0 z0 K1 K2 p0
           | x0 y0 K1 p0 p1 | x0 y0 z0 K1 K2 K3 Hm p0 p1 | x0 y0 K1 p0
           | x0 K1 K2 | x0 y0 z0 K1 K2 p0 p1 | x0 y0 K1 p0 | x0 y0 K1 p0
           | x0 K1 K2 p0 | | x0 xr y0 z0 K1 K2 Hb0 p0 | x0 xr K1 p0
           | x0 xr z0 K1 K2 p0 | x0 xr y0 K1 Hb0 p0 ].
         ++ (* identity *)
            exists pi2c. unfold pi2c. rewrite lweight_lprove_cast. simpl. lia.
         ++ (* top *) discriminate HFA.
         ++ (* with_left1 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left1 x0 y0 z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left1 n IH l1' l2' c0 _ K1 K2 x0 y0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_left2 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left2 x0 y0 z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left2 n IH l1' l2' c0 _ K1 K2 x0 y0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_right *)
            injection HFA as Hx Hy. subst x0. subst y0.
            simpl in Hle. assert (Hb : lweight p1 + lweight q1 <= n) by lia.
            destruct (IH a0 c0 l1' K1 l2' p1 q1 Hb Hc) as [r Hr].
            exists r. simpl. lia.
         ++ (* map_left *)
            assert (Hle' : lweight (lmap_left x0 y0 z0 K1 K2 K3 Hm p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lmap_left n IH l1' l2' c0 _ K1 K2 K3 x0 y0 Hm p0 p1 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* map_right *) discriminate HFA.
         ++ (* zero_left *)
            assert (Hle' : lweight (lzero_left x0 K1 K2) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            assert (e3 : (l1' ++ K1) ++ lzero :: (K2 ++ l2')
                         = l1' ++ (K1 ++ lzero :: K2) ++ l2').
            { repeat rewrite app_assoc.
              rewrite <- (app_assoc (l1' ++ K1) (lzero :: K2) l2'). reflexivity. }
            assert (Hpos2 : 1 <= lweight (lwith_left2 a0 b0 c0 l1' l2' q1)) by apply lweight_pos.
            exists (lprove_cast e3 eq_refl (lzero_left c0 (l1' ++ K1) (K2 ++ l2'))).
            lw_casts. simpl. lia.
         ++ (* plus_left *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lplus_left x0 y0 z0 K1 K2 p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_plus_left n IH l1' l2' c0 _ K1 K2 x0 y0 p0 p1 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* plus_right1 *) discriminate HFA.
         ++ (* plus_right2 *) discriminate HFA.
         ++ (* lone_left *)
            destruct K1 as [|k1 K1']; destruct K2 as [|k2 K2'].
            ** (* singleton *)
               pose (p0' := lprove_cast (eq_refl : ([] : list lform) = []) HFA p0).
               assert (Hqp : lweight p0' = lweight p0) by (unfold p0'; apply lweight_lprove_cast).
               destruct (nil_with_inv p0') as [qa [qb [Hqa Hqb]]].
               simpl in Hle.
               assert (Hqb2 : lweight qb <= lweight p0) by lia.
               assert (Hb : lweight (lone_left a0 [] [] qb) + lweight q1 <= n).
               { simpl. assert (H1 : lweight p0 + S (lweight q1) <= n).
                 { apply le_S_n. exact Hle. }
                 assert (H2 : lweight qb + lweight q1 < n) by lia.
                 lia. }
               assert (Hc1 : bp = true -> l1' <> [] -> length ([lone] : list lform) = 1%nat)
                 by (intros; reflexivity).
               destruct (IH a0 c0 l1' [lone] l2' (lone_left a0 [] [] qb) q1 Hb Hc1) as [r Hr].
               simpl in Hr. exists r. simpl.
               assert (Hle2 : lweight qb + lweight q1 <= lweight p0 + S (lweight q1)) by lia.
               assert (Hle3 : S (lweight qb + lweight q1) <= S (lweight p0 + S (lweight q1))) by lia.
               eapply Nat.lt_le_trans; [exact Hr | exact Hle3].
            ** assert (Hc1 : bp = true -> l1' <> [] -> length ([] ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 [] (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ [] (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ []) = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 (k1 :: K1') [] p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ (k1 :: K1') [] p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 (k1 :: K1') (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ (k1 :: K1') (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
         ++ (* lone_right *) discriminate HFA.
         ++ (* frl_left *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ subs xr y0 x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (@lfrl_left bp x0 xr y0 z0 K1 K2 Hb0 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lfrl_left n IH l1' l2' c0 _ K1 K2 xr y0 x0 Hb0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* frl_right *) discriminate HFA.
         ++ (* lexs_left *)
            assert (Hle' : lweight (lexs_left x0 xr z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lexs_left n IH l1' l2' c0 _ K1 K2 xr x0 p0 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* lexs_right *) discriminate HFA.
    * destruct HC as [m HPL HRL2].
      assert (e1 : l1' ++ a0 :: l2' = (l1' ++ a0 :: m) ++ FA :: SL).
      { rewrite <- HRL2. rewrite <- app_assoc. reflexivity. }
      assert (Hb1 : lweight pi1 + lweight (lprove_cast e1 eq_refl q1) <= n).
      { rewrite lweight_lprove_cast. lia. }
      assert (Hc1 : bp = true -> l1' ++ a0 :: m <> [] -> length DL = 1%nat).
      { intros Hb HN. apply Hc; [exact Hb|]. rewrite HPL. intro Hnil.
        apply (f_equal (@length lform)) in Hnil. rewrite length_app in Hnil. simpl in Hnil. lia. }
      destruct (IH FA c0 (l1' ++ a0 :: m) DL SL pi1 (lprove_cast e1 eq_refl q1) Hb1 Hc1) as [p Hp].
      rewrite lweight_lprove_cast in Hp.
      assert (e2 : (l1' ++ a0 :: m) ++ DL ++ SL = l1' ++ a0 :: (m ++ DL ++ SL)).
      { repeat rewrite <- app_assoc. reflexivity. }
      assert (e3 : l1' ++ (b0 ∧ a0) :: (m ++ DL ++ SL) = PL ++ DL ++ SL).
      { rewrite HPL. repeat rewrite <- app_assoc. reflexivity. }
      exists (lprove_cast e3 eq_refl
               (lwith_left2 a0 b0 c0 l1' (m ++ DL ++ SL)
                  (lprove_cast e2 eq_refl p))).
      lw_casts. simpl. lia.
  + (* lwith_right *)
    simpl in Hle.
    assert (Hb1 : lweight pi1 + lweight (lprove_cast HL eq_refl q1) <= n).
    { rewrite lweight_lprove_cast. lia. }
    assert (Hb2 : lweight pi1 + lweight (lprove_cast HL eq_refl q2) <= n).
    { rewrite lweight_lprove_cast. lia. }
    destruct (IH FA a0 PL DL SL pi1 (lprove_cast HL eq_refl q1) Hb1 Hc) as [p1 Hp1].
    destruct (IH FA b0 PL DL SL pi1 (lprove_cast HL eq_refl q2) Hb2 Hc) as [p2 Hp2].
    exists (lwith_right a0 b0 (PL ++ DL ++ SL) p1 p2).
    rewrite lweight_lprove_cast in Hp1, Hp2. lw_casts. lia.
  + (* lmap_left *)
    simpl in Hle.
    destruct (elt_eq_app_app_trichotT PL FA SL l1' ((b0 / a0) :: l2') l3' (eq_sym HL)) as [HA | HC].
    * destruct HA as [H1 | H2].
      -- destruct H1 as [m HRL1 HMSL].
         assert (e1 : l1' ++ b0 :: l3' = PL ++ FA :: (m ++ b0 :: l3')).
         { rewrite <- HRL1. rewrite <- app_assoc. reflexivity. }
         assert (Hb1 : lweight pi1 + lweight (lprove_cast e1 eq_refl q2) <= n).
         { rewrite lweight_lprove_cast. lia. }
         destruct (IH FA c0 PL DL (m ++ b0 :: l3') pi1 (lprove_cast e1 eq_refl q2) Hb1 Hc) as [p Hp].
         rewrite lweight_lprove_cast in Hp.
         assert (H' : bp = true -> PL ++ DL ++ m = [] /\ length l2' = 1%nat).
         { intros Hb. exfalso. specialize (Hmap Hb). destruct Hmap as [Hl1 Hlen].
           rewrite <- HRL1 in Hl1. apply (f_equal (@length lform)) in Hl1.
           rewrite length_app in Hl1. simpl in Hl1. lia. }
         assert (e2 : PL ++ DL ++ (m ++ b0 :: l3') = (PL ++ DL ++ m) ++ b0 :: l3').
         { repeat rewrite app_assoc. reflexivity. }
         assert (e3 : (PL ++ DL ++ m) ++ (b0 / a0) :: l2' ++ l3' = PL ++ DL ++ SL).
         { rewrite HMSL. repeat rewrite <- app_assoc. reflexivity. }
         exists (lprove_cast e3 eq_refl
                  (lmap_left a0 b0 c0 (PL ++ DL ++ m) l2' l3' H' q1
                     (lprove_cast e2 eq_refl p))).
         lw_casts. simpl. lia.
      -- destruct H2 as [[l3'' l4''] HPL HQ]. destruct HQ as [Hmid HSL].
         destruct l3'' as [|p0 l3'''].
         ++ (* principal *)
            rewrite app_nil_r in HPL. subst PL.
            injection Hmid as HFA0 Hl4. subst l4''.
            assert (eP : l1' ++ (b0 / a0) :: l2' ++ l3' = l1' ++ FA :: SL).
            { rewrite HSL. rewrite <- HFA0. reflexivity. }
            set (pi2c := lprove_cast eP eq_refl (lmap_left a0 b0 c0 l1' l2' l3' Hmap q1 q2)).
            destruct pi1 as
              [ z0 | K1 | x1 y1 z1 K1 K2 p1q | x1 y1 z1 K1 K2 p1q
              | x1 y1 K1 p1q p2q | x1 y1 z1 K1 K2 K3 Hm p1q p2q | y1 xr K1 p1q
              | x1 K1 K2 | x1 y1 z1 K1 K2 p1q p2q | x1 y1 K1 p1q | x1 y1 K1 p1q
              | x1 K1 K2 p1q | | y1 xr b1 z1 K1 K2 Hb1 p1q | y1 xr K1 p1q
              | x1 xr z1 K1 K2 p1q | y1 xr b1 K1 Hb1 p1q ].
            ** (* identity *)
               assert (eid : l1' ++ [z0] ++ SL = l1' ++ z0 :: SL).
               { simpl. reflexivity. }
               exists (lprove_cast (eq_sym eid) eq_refl pi2c). unfold pi2c. lw_casts. simpl. lia.
            ** (* top *) discriminate HFA0.
            ** (* with_left1 *)
               assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x1 :: K2) = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
               assert (Hle' : lweight (lwith_left1 x1 y1 z1 K1 K2 p1q) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_with_left1 n IH l1' SL c0 _ K1 K2 x1 y1 p1q pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** (* with_left2 *)
               assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x1 :: K2) = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
               assert (Hle' : lweight (lwith_left2 x1 y1 z1 K1 K2 p1q) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_with_left2 n IH l1' SL c0 _ K1 K2 x1 y1 p1q pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** (* with_right *) discriminate HFA0.
            ** (* map_left *)
               assert (Hle' : lweight (lmap_left x1 y1 z1 K1 K2 K3 Hm p1q p2q) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lmap_left n IH l1' SL c0 _ K1 K2 K3 x1 y1 Hm p1q p2q pi2c Hle' Hc) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** (* map_right *)
               injection HFA0 as -> ->. subst.
               assert (Hc1 : bp = true -> K1 <> [] -> length l2' = 1%nat).
               { intros Hb HN. pose proof (Hmap Hb) as Hm; destruct Hm as [Hnil Hlen]. exact Hlen. }
               simpl in Hle.
               assert (H1 : lweight p1q + lweight q1 + lweight q2 <= n) by lia.
               assert (Hb1 : lweight q1 + lweight p1q <= n) by lia.
               destruct (IH a0 b0 K1 l2' [] q1 p1q Hb1 Hc1) as [r1 Hr1].
               assert (Hc2 : bp = true -> l1' <> [] -> length (K1 ++ l2') = 1%nat).
               { intros Hb HN. exfalso. pose proof (Hmap Hb) as Hm; destruct Hm as [Hnil _].
                 apply HN. exact Hnil. }
               assert (ec1 : K1 ++ l2' ++ [] = K1 ++ l2') by (rewrite app_nil_r; reflexivity).
               pose (r1c := lprove_cast ec1 eq_refl r1).
               assert (Hr1c : lweight r1c = lweight r1) by (unfold r1c; apply lweight_lprove_cast).
               assert (Hb2 : lweight r1c + lweight q2 <= n).
               { assert (Hr1' : lweight r1 < lweight q1 + lweight p1q) by exact Hr1. rewrite Hr1c. lia. }
               destruct (IH b0 c0 l1' (K1 ++ l2') l3' r1c q2 Hb2 Hc2) as [r2 Hr2].
               unfold r1c in Hr2. rewrite lweight_lprove_cast in Hr2. simpl in Hr2.
               assert (ecast : l1' ++ (K1 ++ l2') ++ l3' = l1' ++ K1 ++ (l2' ++ l3')).
               { repeat rewrite app_assoc. reflexivity. }
               exists (lprove_cast ecast eq_refl r2).
               rewrite lweight_lprove_cast. simpl.
               assert (Hfin : lweight r2 < lweight p1q + (lweight q1 + lweight q2)) by lia.
               lia.
            ** (* zero_left *)
               assert (Hle' : lweight (lzero_left x1 K1 K2) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               assert (e3 : (l1' ++ K1) ++ lzero :: (K2 ++ SL)
                            = l1' ++ (K1 ++ lzero :: K2) ++ SL).
               { repeat rewrite app_assoc.
                 rewrite <- (app_assoc (l1' ++ K1) (lzero :: K2) SL). reflexivity. }
               exists (lprove_cast e3 eq_refl (lzero_left c0 (l1' ++ K1) (K2 ++ SL))).
               lw_casts. simpl. lia.
            ** (* plus_left *)
               assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x1 :: K2) = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
               assert (Hle' : lweight (lplus_left x1 y1 z1 K1 K2 p1q p2q) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_plus_left n IH l1' SL c0 _ K1 K2 x1 y1 p1q p2q pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** (* plus_right1 *) discriminate HFA0.
            ** (* plus_right2 *) discriminate HFA0.
            ** (* lone_left *)
               assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ K2) = 1%nat).
               { intros Hb HN. exfalso. pose proof (Hmap Hb) as Hm; destruct Hm as [Hnil _].
                 apply HN. exact Hnil. }
               assert (Hle' : lweight (lone_left x1 K1 K2 p1q) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' SL c0 _ K1 K2 p1q pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** (* lone_right *) discriminate HFA0.
            ** (* frl_left *)
               assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ subs xr b1 y1 :: K2) = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
               assert (Hle' : lweight (@lfrl_left bp y1 xr b1 z1 K1 K2 Hb1 p1q) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lfrl_left n IH l1' SL c0 _ K1 K2 xr b1 y1 Hb1 p1q pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** (* frl_right *) discriminate HFA0.
            ** (* lexs_left *)
               assert (Hle' : lweight (lexs_left x1 xr z1 K1 K2 p1q) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lexs_left n IH l1' SL c0 _ K1 K2 xr x1 p1q pi2c Hle' Hc) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** (* lexs_right *) discriminate HFA0.

         ++ simpl in Hmid. injection Hmid as Hp0 Hrest. subst p0.
            assert (e1 : l3''' ++ FA :: l4'' = l2').
            { exact Hrest. }
            assert (Hb1 : lweight pi1 + lweight (lprove_cast (eq_sym e1) eq_refl q1) <= n).
            { rewrite lweight_lprove_cast. lia. }
            assert (Hc1 : bp = true -> l3''' <> [] -> length DL = 1%nat).
            { intros Hb HN. apply Hc; [exact Hb|]. rewrite HPL. intro Hnil.
              apply (f_equal (@length lform)) in Hnil. rewrite length_app in Hnil. simpl in Hnil. lia. }
            destruct (IH FA a0 l3''' DL l4'' pi1 (lprove_cast (eq_sym e1) eq_refl q1) Hb1 Hc1) as [p Hp].
            rewrite lweight_lprove_cast in Hp.
            assert (H' : bp = true -> l1' = [] /\ length (l3''' ++ DL ++ l4'') = 1%nat).
            { intros Hb. specialize (Hmap Hb). destruct Hmap as [Hl1 Hlen].
              split; [exact Hl1|].
              assert (Hlen' : length (l3''' ++ FA :: l4'') = 1%nat).
              { rewrite Hrest. exact Hlen. }
              rewrite length_app in Hlen'. simpl in Hlen'.
              destruct l3'''; simpl in Hlen'; [| lia].
              destruct l4''; simpl in Hlen'; [| lia].
              simpl. rewrite app_nil_r.
              apply Hc; [exact Hb|]. rewrite HPL.
              intro Hnil. apply (f_equal (@length lform)) in Hnil. rewrite length_app in Hnil. simpl in Hnil. lia. }
            assert (e3 : l1' ++ (b0 / a0) :: (l3''' ++ DL ++ l4'') ++ l3' = PL ++ DL ++ SL).
            { rewrite HPL. rewrite HSL. repeat rewrite <- app_assoc. reflexivity. }
            exists (lprove_cast e3 eq_refl
                     (lmap_left a0 b0 c0 l1' (l3''' ++ DL ++ l4'') l3' H' p q2)).
            lw_casts. simpl. lia.
    * destruct HC as [m HPL HRL3].
      assert (e1 : l1' ++ b0 :: l3' = (l1' ++ b0 :: m) ++ FA :: SL).
      { rewrite <- HRL3. rewrite <- app_assoc. reflexivity. }
      assert (Hb1 : lweight pi1 + lweight (lprove_cast e1 eq_refl q2) <= n).
      { rewrite lweight_lprove_cast. lia. }
      assert (Hc1 : bp = true -> l1' ++ b0 :: m <> [] -> length DL = 1%nat).
      { intros Hb HN. apply Hc; [exact Hb|]. rewrite HPL. intro Hnil.
        apply (f_equal (@length lform)) in Hnil. rewrite length_app in Hnil. simpl in Hnil. lia. }
      destruct (IH FA c0 (l1' ++ b0 :: m) DL SL pi1 (lprove_cast e1 eq_refl q2) Hb1 Hc1) as [p Hp].
      rewrite lweight_lprove_cast in Hp.
      assert (e2 : (l1' ++ b0 :: m) ++ DL ++ SL = l1' ++ b0 :: (m ++ DL ++ SL)).
      { repeat rewrite <- app_assoc. reflexivity. }
      assert (e3 : l1' ++ (b0 / a0) :: l2' ++ (m ++ DL ++ SL) = PL ++ DL ++ SL).
      { rewrite HPL. repeat rewrite <- app_assoc. reflexivity. }
      exists (lprove_cast e3 eq_refl
               (lmap_left a0 b0 c0 l1' l2' (m ++ DL ++ SL) Hmap q1
                  (lprove_cast e2 eq_refl p))).
      lw_casts. simpl. lia.
  + (* lmap_right *)
    simpl in Hle.
    assert (e : l0 ++ [a0] = PL ++ FA :: (SL ++ [a0])).
    { rewrite HL. rewrite <- app_assoc. reflexivity. }
    assert (Hb1 : lweight pi1 + lweight (lprove_cast e eq_refl q1) <= n).
    { rewrite lweight_lprove_cast. lia. }
    destruct (IH FA b0 PL DL (SL ++ [a0]) pi1 (lprove_cast e eq_refl q1) Hb1 Hc) as [p Hp].
    assert (e2 : PL ++ DL ++ (SL ++ [a0]) = (PL ++ DL ++ SL) ++ [a0]).
    { repeat rewrite app_assoc. reflexivity. }
    exists (lmap_right a0 b0 (PL ++ DL ++ SL) (lprove_cast e2 eq_refl p)).
    rewrite lweight_lprove_cast in Hp. lw_casts. simpl. lia.
  + (* lzero_left *)
    simpl in Hle.
    destruct (elt_eq_elt_trichotT PL FA SL l1' lzero l2' (eq_sym HL)) as [HA | HC].
    * destruct HA as [H1 | H2].
      -- destruct H1 as [m HRL1 HSL].
         assert (e3 : (PL ++ DL ++ m) ++ lzero :: l2' = PL ++ DL ++ SL).
         { rewrite HSL. repeat rewrite app_assoc. reflexivity. }
         exists (lprove_cast e3 eq_refl
                  (lzero_left a0 (PL ++ DL ++ m) l2')).
         lw_casts. simpl. lia.
      -- (* principal *)
         destruct H2 as [HPL [HFA HSL]]. subst PL. subst SL.
         assert (eP : l1' ++ lzero :: l2' = l1' ++ FA :: l2').
         { rewrite HFA. reflexivity. }
         set (pi2c := lprove_cast eP eq_refl (lzero_left a0 l1' l2')).
         destruct pi1 as
           [ x0 | K1 | x0 y0 z0 K1 K2 p0 | x0 y0 z0 K1 K2 p0
           | x0 y0 K1 p0 p1 | x0 y0 z0 K1 K2 K3 Hm p0 p1 | x0 y0 K1 p0
           | x0 K1 K2 | x0 y0 z0 K1 K2 p0 p1 | x0 y0 K1 p0 | x0 y0 K1 p0
           | x0 K1 K2 p0 | | x0 xr y0 z0 K1 K2 Hb0 p0 | x0 xr K1 p0
           | x0 xr z0 K1 K2 p0 | x0 xr y0 K1 Hb0 p0 ].
         ++ (* identity *)
            exists pi2c. unfold pi2c. rewrite lweight_lprove_cast. simpl. lia.
         ++ (* top *) discriminate HFA.
         ++ (* with_left1 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left1 x0 y0 z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left1 n IH l1' l2' a0 _ K1 K2 x0 y0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_left2 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left2 x0 y0 z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left2 n IH l1' l2' a0 _ K1 K2 x0 y0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_right *) discriminate HFA.
         ++ (* map_left *)
            assert (Hle' : lweight (lmap_left x0 y0 z0 K1 K2 K3 Hm p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lmap_left n IH l1' l2' a0 _ K1 K2 K3 x0 y0 Hm p0 p1 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* map_right *) discriminate HFA.
         ++ (* zero_left *)
            assert (Hle' : lweight (lzero_left x0 K1 K2) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            assert (e3 : (l1' ++ K1) ++ lzero :: (K2 ++ l2')
                         = l1' ++ (K1 ++ lzero :: K2) ++ l2').
            { repeat rewrite app_assoc.
              rewrite <- (app_assoc (l1' ++ K1) (lzero :: K2) l2'). reflexivity. }
            exists (lprove_cast e3 eq_refl (lzero_left a0 (l1' ++ K1) (K2 ++ l2'))).
            lw_casts. simpl. lia.
         ++ (* plus_left *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lplus_left x0 y0 z0 K1 K2 p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_plus_left n IH l1' l2' a0 _ K1 K2 x0 y0 p0 p1 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* plus_right1 *) discriminate HFA.
         ++ (* plus_right2 *) discriminate HFA.
         ++ (* lone_left *)
            destruct K1 as [|k1 K1']; destruct K2 as [|k2 K2'].
            ** (* singleton *)
               pose (p0' := lprove_cast (eq_refl : ([] : list lform) = []) HFA p0).
               exfalso. apply lprove_zero_nil. exact p0'.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length ([] ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 [] (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' a0 _ [] (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ []) = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 (k1 :: K1') [] p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' a0 _ (k1 :: K1') [] p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 (k1 :: K1') (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' a0 _ (k1 :: K1') (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
         ++ (* lone_right *) discriminate HFA.
         ++ (* frl_left *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ subs xr y0 x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (@lfrl_left bp x0 xr y0 z0 K1 K2 Hb0 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lfrl_left n IH l1' l2' a0 _ K1 K2 xr y0 x0 Hb0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* frl_right *) discriminate HFA.
         ++ (* lexs_left *)
            assert (Hle' : lweight (lexs_left x0 xr z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lexs_left n IH l1' l2' a0 _ K1 K2 xr x0 p0 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* lexs_right *) discriminate HFA.

    * destruct HC as [m HPL HRL2].
      assert (e3 : l1' ++ lzero :: (m ++ DL ++ SL) = PL ++ DL ++ SL).
      { rewrite HPL. repeat rewrite <- app_assoc. reflexivity. }
      exists (lprove_cast e3 eq_refl
               (lzero_left a0 l1' (m ++ DL ++ SL))).
      lw_casts. simpl. lia.
  + (* lplus_left *)
    simpl in Hle.
    destruct (elt_eq_elt_trichotT PL FA SL l1' (lplus a0 b0) l2' (eq_sym HL))
      as [HA | HC].
    * destruct HA as [H1 | H2].
      -- destruct H1 as [m HRL1 HSL].
         assert (e1 : l1' ++ a0 :: l2' = PL ++ FA :: (m ++ a0 :: l2')).
         { rewrite <- HRL1. rewrite <- app_assoc. reflexivity. }
         assert (e1b : l1' ++ b0 :: l2' = PL ++ FA :: (m ++ b0 :: l2')).
         { rewrite <- HRL1. rewrite <- app_assoc. reflexivity. }
         assert (Hb1 : lweight pi1 + lweight (lprove_cast e1 eq_refl q1) <= n).
         { rewrite lweight_lprove_cast. lia. }
         assert (Hb2 : lweight pi1 + lweight (lprove_cast e1b eq_refl q2) <= n).
         { rewrite lweight_lprove_cast. lia. }
         destruct (IH FA c0 PL DL (m ++ a0 :: l2') pi1 (lprove_cast e1 eq_refl q1) Hb1 Hc) as [p1 Hp1].
         destruct (IH FA c0 PL DL (m ++ b0 :: l2') pi1 (lprove_cast e1b eq_refl q2) Hb2 Hc) as [p2 Hp2].
         rewrite lweight_lprove_cast in Hp1, Hp2.
         assert (e2 : PL ++ DL ++ (m ++ a0 :: l2') = (PL ++ DL ++ m) ++ a0 :: l2').
         { repeat rewrite app_assoc. reflexivity. }
         assert (e2b : PL ++ DL ++ (m ++ b0 :: l2') = (PL ++ DL ++ m) ++ b0 :: l2').
         { repeat rewrite app_assoc. reflexivity. }
         assert (e3 : (PL ++ DL ++ m) ++ (a0 ∨ b0) :: l2' = PL ++ DL ++ SL).
         { rewrite HSL. repeat rewrite app_assoc. reflexivity. }
         exists (lprove_cast e3 eq_refl
                  (lplus_left a0 b0 c0 (PL ++ DL ++ m) l2'
                     (lprove_cast e2 eq_refl p1) (lprove_cast e2b eq_refl p2))).
         lw_casts. simpl. lia.
      -- (* principal *)
         destruct H2 as [HPL [HFA HSL]]. subst PL. subst SL.
         assert (eP : l1' ++ (a0 ∨ b0) :: l2' = l1' ++ FA :: l2').
         { rewrite HFA. reflexivity. }
         set (pi2c := lprove_cast eP eq_refl (lplus_left a0 b0 c0 l1' l2' q1 q2)).
         destruct pi1 as
           [ x0 | K1 | x0 y0 z0 K1 K2 p0 | x0 y0 z0 K1 K2 p0
           | x0 y0 K1 p0 p1 | x0 y0 z0 K1 K2 K3 Hm p0 p1 | x0 y0 K1 p0
           | x0 K1 K2 | x0 y0 z0 K1 K2 p0 p1 | x0 y0 K1 p0 | x0 y0 K1 p0
           | x0 K1 K2 p0 | | x0 xr y0 z0 K1 K2 Hb0 p0 | x0 xr K1 p0
           | x0 xr z0 K1 K2 p0 | x0 xr y0 K1 Hb0 p0 ].
         ++ (* identity *)
            exists pi2c. unfold pi2c. rewrite lweight_lprove_cast. simpl. lia.
         ++ (* top *) discriminate HFA.
         ++ (* with_left1 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left1 x0 y0 z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left1 n IH l1' l2' c0 _ K1 K2 x0 y0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_left2 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left2 x0 y0 z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left2 n IH l1' l2' c0 _ K1 K2 x0 y0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_right *) discriminate HFA.
         ++ (* map_left *)
            assert (Hle' : lweight (lmap_left x0 y0 z0 K1 K2 K3 Hm p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lmap_left n IH l1' l2' c0 _ K1 K2 K3 x0 y0 Hm p0 p1 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* map_right *) discriminate HFA.
         ++ (* zero_left *)
            assert (Hle' : lweight (lzero_left x0 K1 K2) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            assert (e3 : (l1' ++ K1) ++ lzero :: (K2 ++ l2')
                         = l1' ++ (K1 ++ lzero :: K2) ++ l2').
            { repeat rewrite app_assoc.
              rewrite <- (app_assoc (l1' ++ K1) (lzero :: K2) l2'). reflexivity. }
            assert (Hpos2 : 1 <= lweight (lplus_left a0 b0 c0 l1' l2' q1 q2)) by apply lweight_pos.
            exists (lprove_cast e3 eq_refl (lzero_left c0 (l1' ++ K1) (K2 ++ l2'))).
            lw_casts. simpl. lia.
         ++ (* plus_left *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lplus_left x0 y0 z0 K1 K2 p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_plus_left n IH l1' l2' c0 _ K1 K2 x0 y0 p0 p1 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* plus_right1 *)
            injection HFA as Hx Hy. subst x0. subst y0.
            simpl in Hle. assert (Hb : lweight p0 + lweight q1 <= n) by lia.
            destruct (IH a0 c0 l1' K1 l2' p0 q1 Hb Hc) as [r Hr].
            exists r. simpl. lia.
         ++ (* plus_right2 *)
            injection HFA as Hx Hy. subst x0. subst y0.
            simpl in Hle. assert (Hb : lweight p0 + lweight q2 <= n) by lia.
            destruct (IH b0 c0 l1' K1 l2' p0 q2 Hb Hc) as [r Hr].
            exists r. simpl. lia.
         ++ (* lone_left *)
            destruct K1 as [|k1 K1']; destruct K2 as [|k2 K2'].
            ** (* singleton *)
               pose (p0' := lprove_cast (eq_refl : ([] : list lform) = []) HFA p0).
               assert (Hqp : lweight p0' = lweight p0) by (unfold p0'; apply lweight_lprove_cast).
               destruct (nil_plus_inv p0') as [[qa Hqa]|[qb Hqb]].
               --- assert (Hqa2 : lweight qa <= lweight p0) by lia.
                   assert (Hb : lweight (lone_left a0 [] [] qa) + lweight q1 <= n).
                   { simpl in Hle. simpl.
                     assert (H1 : lweight p0 + S (Nat.max (lweight q1) (lweight q2)) <= n) by (apply le_S_n; exact Hle).
                     lia. }
                   assert (Hc1 : bp = true -> l1' <> [] -> length ([lone] : list lform) = 1%nat)
                     by (intros; reflexivity).
                   destruct (IH a0 c0 l1' [lone] l2' (lone_left a0 [] [] qa) q1 Hb Hc1) as [r Hr].
                   simpl in Hr. exists r. simpl.
                   assert (Hbound : lweight (lone_left a0 [] [] qa) + lweight q1
                                    <= S (lweight p0) + S (Nat.max (lweight q1) (lweight q2))).
                   { simpl. assert (H1 : lweight q1 <= Nat.max (lweight q1) (lweight q2)) by apply Nat.le_max_l.
                     assert (H2 : S (lweight qa) <= S (lweight p0)) by (exact (proj1 (Nat.succ_le_mono (lweight qa) (lweight p0)) Hqa2)).
                     assert (H4 : S (lweight p0) + Nat.max (lweight q1) (lweight q2)
                                  < S (lweight p0) + S (Nat.max (lweight q1) (lweight q2))) by lia.
                     assert (H5 : S (lweight qa) + lweight q1
                                  <= S (lweight p0) + Nat.max (lweight q1) (lweight q2)) by lia.
                     eapply Nat.le_trans; [exact H5 | apply Nat.lt_le_incl; exact H4]. }
                   eapply Nat.lt_le_trans; [exact Hr | exact Hbound].
               --- assert (Hqb2 : lweight qb <= lweight p0) by lia.
                   assert (Hb : lweight (lone_left b0 [] [] qb) + lweight q2 <= n).
                   { simpl in Hle. simpl.
                     assert (H1 : lweight p0 + S (Nat.max (lweight q1) (lweight q2)) <= n) by (apply le_S_n; exact Hle).
                     lia. }
                   assert (Hc1 : bp = true -> l1' <> [] -> length ([lone] : list lform) = 1%nat)
                     by (intros; reflexivity).
                   destruct (IH b0 c0 l1' [lone] l2' (lone_left b0 [] [] qb) q2 Hb Hc1) as [r Hr].
                   simpl in Hr. exists r. simpl.
                   assert (Hbound : lweight (lone_left b0 [] [] qb) + lweight q2
                                    <= S (lweight p0) + S (Nat.max (lweight q1) (lweight q2))).
                   { simpl. assert (H1 : lweight q2 <= Nat.max (lweight q1) (lweight q2)) by apply Nat.le_max_r.
                     assert (H2 : S (lweight qb) <= S (lweight p0)) by (exact (proj1 (Nat.succ_le_mono (lweight qb) (lweight p0)) Hqb2)).
                     assert (H4 : S (lweight p0) + Nat.max (lweight q1) (lweight q2)
                                  < S (lweight p0) + S (Nat.max (lweight q1) (lweight q2))) by lia.
                     assert (H5 : S (lweight qb) + lweight q2
                                  <= S (lweight p0) + Nat.max (lweight q1) (lweight q2)) by lia.
                     eapply Nat.le_trans; [exact H5 | apply Nat.lt_le_incl; exact H4]. }
                   eapply Nat.lt_le_trans; [exact Hr | exact Hbound].
            ** assert (Hc1 : bp = true -> l1' <> [] -> length ([] ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 [] (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ [] (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ []) = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 (k1 :: K1') [] p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ (k1 :: K1') [] p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 (k1 :: K1') (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ (k1 :: K1') (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
         ++ (* lone_right *) discriminate HFA.
         ++ (* frl_left *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ subs xr y0 x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (@lfrl_left bp x0 xr y0 z0 K1 K2 Hb0 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lfrl_left n IH l1' l2' c0 _ K1 K2 xr y0 x0 Hb0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* frl_right *) discriminate HFA.
         ++ (* lexs_left *)
            assert (Hle' : lweight (lexs_left x0 xr z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lexs_left n IH l1' l2' c0 _ K1 K2 xr x0 p0 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* lexs_right *) discriminate HFA.

    * destruct HC as [m HPL HRL2].
      assert (e1 : l1' ++ a0 :: l2' = (l1' ++ a0 :: m) ++ FA :: SL).
      { rewrite <- HRL2. rewrite <- app_assoc. reflexivity. }
      assert (e1b : l1' ++ b0 :: l2' = (l1' ++ b0 :: m) ++ FA :: SL).
      { rewrite <- HRL2. rewrite <- app_assoc. reflexivity. }
      assert (Hb1 : lweight pi1 + lweight (lprove_cast e1 eq_refl q1) <= n).
      { rewrite lweight_lprove_cast. lia. }
      assert (Hb2 : lweight pi1 + lweight (lprove_cast e1b eq_refl q2) <= n).
      { rewrite lweight_lprove_cast. lia. }
      assert (Hc1 : bp = true -> l1' ++ a0 :: m <> [] -> length DL = 1%nat).
      { intros Hb HN. apply Hc; [exact Hb|]. rewrite HPL. intro Hnil.
        apply (f_equal (@length lform)) in Hnil. rewrite length_app in Hnil. simpl in Hnil. lia. }
      assert (Hc1b : bp = true -> l1' ++ b0 :: m <> [] -> length DL = 1%nat).
      { intros Hb HN. apply Hc; [exact Hb|]. rewrite HPL. intro Hnil.
        apply (f_equal (@length lform)) in Hnil. rewrite length_app in Hnil. simpl in Hnil. lia. }
      destruct (IH FA c0 (l1' ++ a0 :: m) DL SL pi1 (lprove_cast e1 eq_refl q1) Hb1 Hc1) as [p1 Hp1].
      destruct (IH FA c0 (l1' ++ b0 :: m) DL SL pi1 (lprove_cast e1b eq_refl q2) Hb2 Hc1b) as [p2 Hp2].
      rewrite lweight_lprove_cast in Hp1, Hp2.
      assert (e2 : (l1' ++ a0 :: m) ++ DL ++ SL = l1' ++ a0 :: (m ++ DL ++ SL)).
      { repeat rewrite <- app_assoc. reflexivity. }
      assert (e2b : (l1' ++ b0 :: m) ++ DL ++ SL = l1' ++ b0 :: (m ++ DL ++ SL)).
      { repeat rewrite <- app_assoc. reflexivity. }
      assert (e3 : l1' ++ (a0 ∨ b0) :: (m ++ DL ++ SL) = PL ++ DL ++ SL).
      { rewrite HPL. repeat rewrite <- app_assoc. reflexivity. }
      exists (lprove_cast e3 eq_refl
               (lplus_left a0 b0 c0 l1' (m ++ DL ++ SL)
                  (lprove_cast e2 eq_refl p1) (lprove_cast e2b eq_refl p2))).
      lw_casts. simpl. lia.
  + (* lplus_right1 *)
    simpl in Hle.
    assert (Hb1 : lweight pi1 + lweight (lprove_cast HL eq_refl q1) <= n).
    { rewrite lweight_lprove_cast. lia. }
    destruct (IH FA a0 PL DL SL pi1 (lprove_cast HL eq_refl q1) Hb1 Hc) as [p Hp].
    exists (lplus_right1 a0 b0 (PL ++ DL ++ SL) p).
    rewrite lweight_lprove_cast in Hp. lw_casts. simpl. lia.
  + (* lplus_right2 *)
    simpl in Hle.
    assert (Hb1 : lweight pi1 + lweight (lprove_cast HL eq_refl q1) <= n).
    { rewrite lweight_lprove_cast. lia. }
    destruct (IH FA a0 PL DL SL pi1 (lprove_cast HL eq_refl q1) Hb1 Hc) as [p Hp].
    exists (lplus_right2 a0 b0 (PL ++ DL ++ SL) p).
    rewrite lweight_lprove_cast in Hp. lw_casts. simpl. lia.
  + (* lone_left *)
    simpl in Hle.
    destruct (elt_eq_elt_trichotT PL FA SL l1' lone l2' (eq_sym HL)) as [HA | HC].
    * destruct HA as [H1 | H2].
      -- destruct H1 as [m HRL1 HSL].
         assert (e1 : l1' ++ l2' = PL ++ FA :: (m ++ l2')).
         { rewrite <- HRL1. rewrite <- app_assoc. reflexivity. }
         assert (Hb1 : lweight pi1 + lweight (lprove_cast e1 eq_refl q1) <= n).
         { rewrite lweight_lprove_cast. lia. }
         destruct (IH FA a0 PL DL (m ++ l2') pi1 (lprove_cast e1 eq_refl q1) Hb1 Hc) as [p Hp].
         rewrite lweight_lprove_cast in Hp.
         assert (e2 : PL ++ DL ++ (m ++ l2') = (PL ++ DL ++ m) ++ l2').
         { repeat rewrite app_assoc. reflexivity. }
         assert (e3 : (PL ++ DL ++ m) ++ lone :: l2' = PL ++ DL ++ SL).
         { rewrite HSL. repeat rewrite app_assoc. reflexivity. }
         exists (lprove_cast e3 eq_refl
                  (lone_left a0 (PL ++ DL ++ m) l2' (lprove_cast e2 eq_refl p))).
         lw_casts. simpl. lia.
      -- (* principal *)
         destruct H2 as [HPL [HFA HSL]]. subst PL. subst SL.
         assert (eP : l1' ++ lone :: l2' = l1' ++ FA :: l2').
         { rewrite HFA. reflexivity. }
         set (pi2c := lprove_cast eP eq_refl (lone_left a0 l1' l2' q1)).
         destruct pi1 as
           [ x0 | K1 | x0 y0 z0 K1 K2 p0 | x0 y0 z0 K1 K2 p0
           | x0 y0 K1 p0 p1 | x0 y0 z0 K1 K2 K3 Hm p0 p1 | x0 y0 K1 p0
           | x0 K1 K2 | x0 y0 z0 K1 K2 p0 p1 | x0 y0 K1 p0 | x0 y0 K1 p0
           | x0 K1 K2 p0 | | x0 xr y0 z0 K1 K2 Hb0 p0 | x0 xr K1 p0
           | x0 xr z0 K1 K2 p0 | x0 xr y0 K1 Hb0 p0 ].
         ++ (* identity *)
            exists pi2c. unfold pi2c. rewrite lweight_lprove_cast. simpl. lia.
         ++ (* top *) discriminate HFA.
         ++ (* with_left1 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left1 x0 y0 z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left1 n IH l1' l2' a0 _ K1 K2 x0 y0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_left2 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left2 x0 y0 z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left2 n IH l1' l2' a0 _ K1 K2 x0 y0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_right *) discriminate HFA.
         ++ (* map_left *)
            assert (Hle' : lweight (lmap_left x0 y0 z0 K1 K2 K3 Hm p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lmap_left n IH l1' l2' a0 _ K1 K2 K3 x0 y0 Hm p0 p1 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* map_right *) discriminate HFA.
         ++ (* zero_left *)
            assert (Hle' : lweight (lzero_left x0 K1 K2) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            assert (e3 : (l1' ++ K1) ++ lzero :: (K2 ++ l2')
                         = l1' ++ (K1 ++ lzero :: K2) ++ l2').
            { repeat rewrite app_assoc.
              rewrite <- (app_assoc (l1' ++ K1) (lzero :: K2) l2'). reflexivity. }
            exists (lprove_cast e3 eq_refl (lzero_left a0 (l1' ++ K1) (K2 ++ l2'))).
            lw_casts. simpl. lia.
         ++ (* plus_left *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lplus_left x0 y0 z0 K1 K2 p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_plus_left n IH l1' l2' a0 _ K1 K2 x0 y0 p0 p1 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* plus_right1 *) discriminate HFA.
         ++ (* plus_right2 *) discriminate HFA.
         ++ (* lone_left *)
            destruct K1 as [|k1 K1']; destruct K2 as [|k2 K2'].
            ** (* singleton *)
               exists (lprove_cast (f_equal (fun f => l1' ++ f :: l2') HFA) eq_refl pi2c).
               unfold pi2c. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length ([] ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 [] (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' a0 _ [] (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ []) = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 (k1 :: K1') [] p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' a0 _ (k1 :: K1') [] p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x0 (k1 :: K1') (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' a0 _ (k1 :: K1') (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
         ++ (* lone_right *)
            simpl. exists q1. simpl. lia.
         ++ (* frl_left *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ subs xr y0 x0 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (@lfrl_left bp x0 xr y0 z0 K1 K2 Hb0 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lfrl_left n IH l1' l2' a0 _ K1 K2 xr y0 x0 Hb0 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* frl_right *) discriminate HFA.
         ++ (* lexs_left *)
            assert (Hle' : lweight (lexs_left x0 xr z0 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lexs_left n IH l1' l2' a0 _ K1 K2 xr x0 p0 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* lexs_right *) discriminate HFA.

    * destruct HC as [m HPL HRL2].
      assert (e1 : l1' ++ l2' = (l1' ++ m) ++ FA :: SL).
      { rewrite <- HRL2. rewrite <- app_assoc. reflexivity. }
      assert (Hb1 : lweight pi1 + lweight (lprove_cast e1 eq_refl q1) <= n).
      { rewrite lweight_lprove_cast. lia. }
      assert (Hc1 : bp = true -> l1' ++ m <> [] -> length DL = 1%nat).
      { intros Hb HN. apply Hc; [exact Hb|]. rewrite HPL. intro Hnil.
        apply (f_equal (@length lform)) in Hnil. rewrite length_app in Hnil. simpl in Hnil. lia. }
      destruct (IH FA a0 (l1' ++ m) DL SL pi1 (lprove_cast e1 eq_refl q1) Hb1 Hc1) as [p Hp].
      rewrite lweight_lprove_cast in Hp.
      assert (e2 : (l1' ++ m) ++ DL ++ SL = l1' ++ (m ++ DL ++ SL)).
      { repeat rewrite <- app_assoc. reflexivity. }
      assert (e3 : l1' ++ lone :: (m ++ DL ++ SL) = PL ++ DL ++ SL).
      { rewrite HPL. repeat rewrite <- app_assoc. reflexivity. }
      exists (lprove_cast e3 eq_refl
               (lone_left a0 l1' (m ++ DL ++ SL) (lprove_cast e2 eq_refl p))).
      lw_casts. simpl. lia.
  + (* lone_right *)
    destruct PL; simpl in HL; discriminate HL.
  + (* lfrl_left *)
    simpl in Hle.
    destruct (elt_eq_elt_trichotT PL FA SL l1' (lfrl x0 a0) l2' (eq_sym HL)) as [HA | HC].
    * destruct HA as [H1 | H2].
      -- destruct H1 as [m HRL1 HSL].
         assert (e1 : l1' ++ subs x0 b0 a0 :: l2' = PL ++ FA :: (m ++ subs x0 b0 a0 :: l2')).
         { rewrite <- HRL1. rewrite <- app_assoc. reflexivity. }
         assert (Hb1 : lweight pi1 + lweight (lprove_cast e1 eq_refl q1) <= n).
         { rewrite lweight_lprove_cast. lia. }
         destruct (IH FA c0 PL DL (m ++ subs x0 b0 a0 :: l2') pi1 (lprove_cast e1 eq_refl q1) Hb1 Hc) as [p Hp].
         rewrite lweight_lprove_cast in Hp.
         assert (e2 : PL ++ DL ++ (m ++ subs x0 b0 a0 :: l2') = (PL ++ DL ++ m) ++ subs x0 b0 a0 :: l2').
         { repeat rewrite app_assoc. reflexivity. }
         assert (e3 : (PL ++ DL ++ m) ++ lfrl x0 a0 :: l2' = PL ++ DL ++ SL).
         { rewrite HSL. repeat rewrite app_assoc. reflexivity. }
         exists (lprove_cast e3 eq_refl
                  (@lfrl_left bp a0 x0 b0 c0 (PL ++ DL ++ m) l2' Hb0 (lprove_cast e2 eq_refl p))).
         lw_casts. simpl. lia.
      -- (* principal *)
         destruct H2 as [HPL [HFA HSL]]. subst PL. subst SL.
         assert (eP : l1' ++ lfrl x0 a0 :: l2' = l1' ++ FA :: l2').
         { rewrite HFA. reflexivity. }
         set (pi2c := lprove_cast eP eq_refl (@lfrl_left bp a0 x0 b0 c0 l1' l2' Hb0 q1)).
         destruct pi1 as
           [ z0 | K1 | x1 y1 z1 K1 K2 p0 | x1 y1 z1 K1 K2 p0
           | x1 y1 K1 p0 p1 | x1 y1 z1 K1 K2 K3 Hm p0 p1 | x1 y1 K1 p0
           | x1 K1 K2 | x1 y1 z1 K1 K2 p0 p1 | x1 y1 K1 p0 | x1 y1 K1 p0
           | x1 K1 K2 p0 | | y1 xr b1 z1 K1 K2 Hb1 p0 | y1 xr K1 p0
           | x1 xr z1 K1 K2 p0 | x1 xr y1 K1 Hb1 p0 ].
         ++ (* identity *)
            exists pi2c. unfold pi2c. rewrite lweight_lprove_cast. simpl. lia.
         ++ (* top *) discriminate HFA.
         ++ (* with_left1 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x1 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left1 x1 y1 z1 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left1 n IH l1' l2' c0 _ K1 K2 x1 y1 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_left2 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x1 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left2 x1 y1 z1 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left2 n IH l1' l2' c0 _ K1 K2 x1 y1 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_right *) discriminate HFA.
         ++ (* map_left *)
            assert (Hle' : lweight (lmap_left x1 y1 z1 K1 K2 K3 Hm p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lmap_left n IH l1' l2' c0 _ K1 K2 K3 x1 y1 Hm p0 p1 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* map_right *) discriminate HFA.
         ++ (* zero_left *)
            assert (Hle' : lweight (lzero_left x1 K1 K2) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            assert (e3 : (l1' ++ K1) ++ lzero :: (K2 ++ l2')
                         = l1' ++ (K1 ++ lzero :: K2) ++ l2').
            { repeat rewrite app_assoc.
              rewrite <- (app_assoc (l1' ++ K1) (lzero :: K2) l2'). reflexivity. }
            exists (lprove_cast e3 eq_refl (lzero_left c0 (l1' ++ K1) (K2 ++ l2'))).
            lw_casts. simpl. lia.
         ++ (* plus_left *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x1 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lplus_left x1 y1 z1 K1 K2 p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_plus_left n IH l1' l2' c0 _ K1 K2 x1 y1 p0 p1 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* plus_right1 *) discriminate HFA.
         ++ (* plus_right2 *) discriminate HFA.
         ++ (* lone_left *)
            destruct K1 as [|k1 K1']; destruct K2 as [|k2 K2'].
            ** (* singleton *)
               pose (p0' := lprove_cast (eq_refl : ([] : list lform) = []) HFA p0).
               destruct (nil_lfrl_inv p0') as [q' Hq'].
               destruct (lprove_nsubs_weight 0 b0 Hb0 q') as [q'' Hq''].
               assert (eL : map (nsubs 0 b0) (map fupz ([] : list lform)) = []).
               { apply map_nsubs_fupz. }
               assert (ea : nsubs 0 b0 (subs x0 (dvar 0) (fupz a0)) = subs x0 b0 a0)
                 by (apply nsubs_subs_fup).
               pose (q''' := lprove_cast eL ea q'').
               assert (Hq3 : lweight q''' <= lweight p0).
               { unfold q'''; rewrite lweight_lprove_cast.
                 assert (lweight q'' <= lweight q') by exact Hq''.
                 assert (lweight q' <= lweight p0') by exact Hq'.
                 assert (lweight p0' = lweight p0) by (unfold p0'; apply lweight_lprove_cast).
                 assert (Hp : lweight p0' = lweight p0) by (unfold p0'; apply lweight_lprove_cast).
                 assert (Hqq : lweight q'' <= lweight p0) by (rewrite <- Hp; exact (Nat.le_trans _ _ _ Hq'' Hq')).
                 exact Hqq. }
               assert (Hb : lweight (lone_left (subs x0 b0 a0) [] [] q''') + lweight q1 <= n).
               { simpl. simpl in Hle. assert (H1 : lweight p0 + S (lweight q1) <= n) by (apply le_S_n; exact Hle).
                 assert (H2 : S (lweight q''') <= S (lweight p0)) by (exact (proj1 (Nat.succ_le_mono _ _) Hq3)).
                 lia. }
               assert (Hc1 : bp = true -> l1' <> [] -> length ([lone] : list lform) = 1%nat)
                 by (intros; reflexivity).
               destruct (IH (subs x0 b0 a0) c0 l1' [lone] l2' (lone_left (subs x0 b0 a0) [] [] q''') q1 Hb Hc1) as [r Hr].
               simpl in Hr. exists r. simpl.
                assert (Hbound : lweight (lone_left (subs x0 b0 a0) [] [] q''') + lweight q1
                                 <= S (lweight p0) + S (lweight q1)).
                { simpl. assert (H2 : S (lweight q''') <= S (lweight p0)) by (exact (proj1 (Nat.succ_le_mono _ _) Hq3)).
                  assert (H3 : S (lweight p0) + lweight q1 < S (lweight p0) + S (lweight q1)) by lia.
                  assert (H4 : S (lweight q''') + lweight q1 <= S (lweight p0) + lweight q1) by lia.
                  eapply Nat.le_trans; [exact H4 | apply Nat.lt_le_incl; exact H3]. }
               eapply Nat.lt_le_trans; [exact Hr | exact Hbound].
            ** assert (Hc1 : bp = true -> l1' <> [] -> length ([] ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x1 [] (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ [] (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ []) = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x1 (k1 :: K1') [] p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ (k1 :: K1') [] p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x1 (k1 :: K1') (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ (k1 :: K1') (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
         ++ (* lone_right *) discriminate HFA.
          ++ (* frl_left *)
             assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ subs xr b1 y1 :: K2) = 1%nat).
             { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
             assert (Hle' : lweight (@lfrl_left bp y1 xr b1 z1 K1 K2 Hb1 p0) + lweight pi2c <= S n).
             { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
             destruct (@cut_lfrl_left n IH l1' l2' c0 _ K1 K2 xr b1 y1 Hb1 p0 pi2c Hle' Hc1) as [r Hr].
             unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
             exists r. lw_casts. simpl. lia.
         ++ (* frl_right *)
            injection HFA as -> ->. subst.
            destruct (lprove_nsubs_weight 0 b0 Hb0 p0) as [pa Hpa].
            assert (eL : map (nsubs 0 b0) (map fupz K1) = K1) by (apply map_nsubs_fupz).
            assert (ea : nsubs 0 b0 (subs x0 (dvar 0) (fupz a0)) = subs x0 b0 a0)
              by (apply nsubs_subs_fup).
            pose (pac := lprove_cast eL ea pa).
            assert (Hpac : lweight pac <= lweight p0).
            { unfold pac; rewrite lweight_lprove_cast. exact Hpa. }
            assert (Hb : lweight pac + lweight q1 <= n).
             { simpl in Hle. assert (H1 : lweight p0 + S (lweight q1) <= n) by (apply le_S_n; exact Hle). lia. }
            destruct (IH (subs x0 b0 a0) c0 l1' K1 l2' pac q1 Hb Hc) as [r Hr].
            unfold pac in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. simpl. lia.
         ++ (* lexs_left *)
            assert (Hle' : lweight (lexs_left x1 xr z1 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lexs_left n IH l1' l2' c0 _ K1 K2 xr x1 p0 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* lexs_right *) discriminate HFA.

    * destruct HC as [m HPL HRL2].
      assert (e1 : l1' ++ subs x0 b0 a0 :: l2' = (l1' ++ subs x0 b0 a0 :: m) ++ FA :: SL).
      { rewrite <- HRL2. rewrite <- app_assoc. reflexivity. }
      assert (Hb1 : lweight pi1 + lweight (lprove_cast e1 eq_refl q1) <= n).
      { rewrite lweight_lprove_cast. lia. }
      assert (Hc1 : bp = true -> l1' ++ subs x0 b0 a0 :: m <> [] -> length DL = 1%nat).
      { intros Hb HN. apply Hc; [exact Hb|]. rewrite HPL. intro Hnil.
        apply (f_equal (@length lform)) in Hnil. rewrite length_app in Hnil. simpl in Hnil. lia. }
      destruct (IH FA c0 (l1' ++ subs x0 b0 a0 :: m) DL SL pi1 (lprove_cast e1 eq_refl q1) Hb1 Hc1) as [p Hp].
      rewrite lweight_lprove_cast in Hp.
      assert (e2 : (l1' ++ subs x0 b0 a0 :: m) ++ DL ++ SL = l1' ++ subs x0 b0 a0 :: (m ++ DL ++ SL)).
      { repeat rewrite <- app_assoc. reflexivity. }
      assert (e3 : l1' ++ lfrl x0 a0 :: (m ++ DL ++ SL) = PL ++ DL ++ SL).
      { rewrite HPL. repeat rewrite <- app_assoc. reflexivity. }
      exists (lprove_cast e3 eq_refl
               (@lfrl_left bp a0 x0 b0 c0 l1' (m ++ DL ++ SL) Hb0 (lprove_cast e2 eq_refl p))).
      lw_casts. simpl. lia.
  + (* lfrl_right *)
    simpl in Hle.
    destruct (lprove_fup_weight 0 pi1) as [p1 Hp1w].
    assert (e : map fupz l0 = map fupz PL ++ fupz FA :: map fupz SL).
    { rewrite HL. rewrite (map_app (fup 0) PL (FA :: SL)). reflexivity. }
    assert (Hb1 : lweight p1 + lweight (lprove_cast e eq_refl q1) <= n).
    { rewrite lweight_lprove_cast. assert (lweight p1 <= lweight pi1) by exact Hp1w. lia. }
    assert (Hc1 : bp = true -> map fupz PL <> [] -> length (map fupz DL) = 1%nat).
    { intros Hb HN. rewrite length_map. apply Hc; [exact Hb|].
      intro Hnil. apply HN. rewrite Hnil. reflexivity. }
    destruct (IH (fup 0 FA) (subs x0 (dvar 0) (fupz a0))
                (map fupz PL) (map fupz DL) (map fupz SL)
                p1 (lprove_cast e eq_refl q1) Hb1 Hc1) as [p2 Hp2].
    assert (e2 : map fupz (PL ++ DL ++ SL) = map fupz PL ++ map fupz DL ++ map fupz SL).
    { rewrite (map_app (fup 0) PL (DL ++ SL)). rewrite (map_app (fup 0) DL SL). reflexivity. }
    exists (lfrl_right a0 x0 (PL ++ DL ++ SL) (lprove_cast (eq_sym e2) eq_refl p2)).
    rewrite lweight_lprove_cast in Hp2. lw_casts. simpl. lia.
  + (* lexs_left *)
    simpl in Hle.
    destruct (elt_eq_elt_trichotT PL FA SL l1' (lexs x0 a0) l2' (eq_sym HL)) as [HA | HC].
    * destruct HA as [H1 | H2].
      -- destruct H1 as [m HRL1 HSL].
         destruct (lprove_fup_weight 0 pi1) as [p1 Hp1w].
         assert (e1 : map fupz l1' ++ subs x0 (dvar 0) (fupz a0) :: map fupz l2'
                      = map fupz PL ++ fupz FA
                        :: (map fupz m ++ subs x0 (dvar 0) (fupz a0) :: map fupz l2')).
         { rewrite <- HRL1. rewrite (map_app (fup 0) PL (FA :: m)). simpl.
           rewrite <- app_assoc. reflexivity. }
         assert (Hb1 : lweight p1 + lweight (lprove_cast e1 eq_refl q1) <= n).
         { rewrite lweight_lprove_cast. assert (lweight p1 <= lweight pi1) by exact Hp1w. lia. }
         assert (Hc1 : bp = true -> map fupz PL <> [] -> length (map fupz DL) = 1%nat).
         { intros Hb HN. rewrite length_map. apply Hc; [exact Hb|].
           intro Hnil. apply HN. rewrite Hnil. reflexivity. }
         destruct (IH (fup 0 FA) (fup 0 c0) (map fupz PL) (map fupz DL)
                     (map fupz m ++ subs x0 (dvar 0) (fupz a0) :: map fupz l2')
                     p1 (lprove_cast e1 eq_refl q1) Hb1 Hc1) as [p Hp].
         rewrite lweight_lprove_cast in Hp.
         assert (e2 : map fupz PL ++ map fupz DL
                      ++ (map fupz m ++ subs x0 (dvar 0) (fupz a0) :: map fupz l2')
                      = map fupz (PL ++ DL ++ m)
                        ++ subs x0 (dvar 0) (fupz a0) :: map fupz l2').
         { rewrite (map_app (fup 0) PL (DL ++ m)). rewrite (map_app (fup 0) DL m).
           repeat rewrite <- app_assoc. reflexivity. }
         assert (e3 : (PL ++ DL ++ m) ++ lexs x0 a0 :: l2' = PL ++ DL ++ SL).
         { rewrite HSL. repeat rewrite app_assoc. reflexivity. }
         exists (lprove_cast e3 eq_refl
                  (lexs_left a0 x0 c0 (PL ++ DL ++ m) l2'
                     (lprove_cast e2 eq_refl p))).
         lw_casts. simpl. lia.
      -- (* principal *)
         destruct H2 as [HPL [HFA HSL]]. subst PL. subst SL.
         assert (eP : l1' ++ lexs x0 a0 :: l2' = l1' ++ FA :: l2').
         { rewrite HFA. reflexivity. }
         set (pi2c := lprove_cast eP eq_refl (lexs_left a0 x0 c0 l1' l2' q1)).
         destruct pi1 as
           [ z0 | K1 | x1 y1 z1 K1 K2 p0 | x1 y1 z1 K1 K2 p0
           | x1 y1 K1 p0 p1 | x1 y1 z1 K1 K2 K3 Hm p0 p1 | x1 y1 K1 p0
           | x1 K1 K2 | x1 y1 z1 K1 K2 p0 p1 | x1 y1 K1 p0 | x1 y1 K1 p0
           | x1 K1 K2 p0 | | y1 xr b1 z1 K1 K2 Hb1 p0 | y1 xr K1 p0
           | x1 xr z1 K1 K2 p0 | y1 xr b1 K1 Hb1 p0 ].
         ++ (* identity *)
            exists pi2c. unfold pi2c. rewrite lweight_lprove_cast. simpl. lia.
         ++ (* top *) discriminate HFA.
         ++ (* with_left1 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x1 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left1 x1 y1 z1 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left1 n IH l1' l2' c0 _ K1 K2 x1 y1 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_left2 *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x1 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lwith_left2 x1 y1 z1 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_with_left2 n IH l1' l2' c0 _ K1 K2 x1 y1 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* with_right *) discriminate HFA.
         ++ (* map_left *)
            assert (Hle' : lweight (lmap_left x1 y1 z1 K1 K2 K3 Hm p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lmap_left n IH l1' l2' c0 _ K1 K2 K3 x1 y1 Hm p0 p1 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* map_right *) discriminate HFA.
         ++ (* zero_left *)
            assert (Hle' : lweight (lzero_left x1 K1 K2) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            assert (e3 : (l1' ++ K1) ++ lzero :: (K2 ++ l2')
                         = l1' ++ (K1 ++ lzero :: K2) ++ l2').
            { repeat rewrite app_assoc.
              rewrite <- (app_assoc (l1' ++ K1) (lzero :: K2) l2'). reflexivity. }
            exists (lprove_cast e3 eq_refl (lzero_left c0 (l1' ++ K1) (K2 ++ l2'))).
            lw_casts. simpl. lia.
         ++ (* plus_left *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ x1 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (lplus_left x1 y1 z1 K1 K2 p0 p1) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_plus_left n IH l1' l2' c0 _ K1 K2 x1 y1 p0 p1 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* plus_right1 *) discriminate HFA.
         ++ (* plus_right2 *) discriminate HFA.
         ++ (* lone_left *)
            destruct K1 as [|k1 K1']; destruct K2 as [|k2 K2'].
            ** (* singleton *)
               pose (p0' := lprove_cast (eq_refl : ([] : list lform) = []) HFA p0).
               destruct (nil_lexs_inv p0') as [b1 [Hb1' [q' Hq']]].
               destruct (lprove_nsubs_weight 0 b1 Hb1' q1) as [q1r Hq1r].
               assert (eL : map (nsubs 0 b1)
                              (map fupz l1' ++ subs x0 (dvar 0) (fupz a0) :: map fupz l2')
                            = l1' ++ subs x0 b1 a0 :: l2').
               { rewrite (map_app (nsubs 0 b1) (map fupz l1')
                            (subs x0 (dvar 0) (fupz a0) :: map fupz l2')).
                 simpl. rewrite (map_nsubs_fupz b1 l1'). rewrite (map_nsubs_fupz b1 l2').
                 rewrite nsubs_subs_fup. reflexivity. }
               assert (ea : nsubs 0 b1 (fupz c0) = c0) by (apply nsubs_fup).
               pose (q1c := lprove_cast eL ea q1r).
               assert (Hq1c : lweight q1c <= lweight q1).
               { unfold q1c; rewrite lweight_lprove_cast. exact Hq1r. }
               assert (Hq3 : lweight q' <= lweight p0).
               { assert (Hp : lweight p0' = lweight p0) by (unfold p0'; apply lweight_lprove_cast).
                 rewrite <- Hp. exact Hq'. }
               assert (Hb : lweight (lone_left (subs x0 b1 a0) [] [] q') + lweight q1c <= n).
               { simpl. simpl in Hle.
                 assert (H1 : lweight p0 + S (lweight q1) <= n) by (apply le_S_n; exact Hle).
                 assert (H2 : S (lweight q') <= S (lweight p0)) by (exact (proj1 (Nat.succ_le_mono _ _) Hq3)).
                 lia. }
               assert (Hc1 : bp = true -> l1' <> [] -> length ([lone] : list lform) = 1%nat)
                 by (intros; reflexivity).
               destruct (IH (subs x0 b1 a0) c0 l1' [lone] l2' (lone_left (subs x0 b1 a0) [] [] q') q1c Hb Hc1) as [r Hr].
               simpl in Hr. exists r. simpl.
               assert (Hbound : lweight (lone_left (subs x0 b1 a0) [] [] q') + lweight q1c
                                <= S (lweight p0) + S (lweight q1)).
               { simpl. assert (H2 : S (lweight q') <= S (lweight p0)) by (exact (proj1 (Nat.succ_le_mono _ _) Hq3)).
                 assert (H3 : S (lweight p0) + lweight q1c < S (lweight p0) + S (lweight q1)) by lia.
                 assert (H4 : S (lweight q') + lweight q1c <= S (lweight p0) + lweight q1c) by lia.
                 eapply Nat.le_trans; [exact H4 | apply Nat.lt_le_incl; exact H3]. }
               eapply Nat.lt_le_trans; [exact Hr | exact Hbound].
            ** assert (Hc1 : bp = true -> l1' <> [] -> length ([] ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x1 [] (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ [] (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ []) = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x1 (k1 :: K1') [] p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ (k1 :: K1') [] p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
            ** assert (Hc1 : bp = true -> l1' <> [] -> length (k1 :: K1' ++ k2 :: K2') = 1%nat).
               { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in Hc. simpl in Hc. lia. }
               assert (Hle' : lweight (lone_left x1 (k1 :: K1') (k2 :: K2') p0) + lweight pi2c <= S n).
               { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
               destruct (@cut_lone_left n IH l1' l2' c0 _ (k1 :: K1') (k2 :: K2') p0 pi2c Hle' Hc1) as [r Hr].
               unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
               exists r. lw_casts. simpl. lia.
         ++ (* lone_right *) discriminate HFA.
         ++ (* frl_left *)
            assert (Hc1 : bp = true -> l1' <> [] -> length (K1 ++ subs xr b1 y1 :: K2) = 1%nat).
            { intros Hb HN. specialize (Hc Hb HN). repeat rewrite length_app in *. simpl in *. lia. }
            assert (Hle' : lweight (@lfrl_left bp y1 xr b1 z1 K1 K2 Hb1 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lfrl_left n IH l1' l2' c0 _ K1 K2 xr b1 y1 Hb1 p0 pi2c Hle' Hc1) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* frl_right *) discriminate HFA.
         ++ (* lexs_left *)
            assert (Hle' : lweight (lexs_left x1 xr z1 K1 K2 p0) + lweight pi2c <= S n).
            { unfold pi2c. rewrite lweight_lprove_cast. exact Hle. }
            destruct (@cut_lexs_left n IH l1' l2' c0 _ K1 K2 xr x1 p0 pi2c Hle' Hc) as [r Hr].
            unfold pi2c in Hr. rewrite lweight_lprove_cast in Hr. simpl in Hr.
            exists r. lw_casts. simpl. lia.
         ++ (* lexs_right *)
            injection HFA as -> ->. subst.
            destruct (lprove_nsubs_weight 0 b1 Hb1 q1) as [q1r Hq1r].
            assert (eL : map (nsubs 0 b1)
                           (map fupz l1' ++ subs x0 (dvar 0) (fupz a0) :: map fupz l2')
                         = l1' ++ subs x0 b1 a0 :: l2').
            { rewrite (map_app (nsubs 0 b1) (map fupz l1')
                         (subs x0 (dvar 0) (fupz a0) :: map fupz l2')).
              simpl. rewrite (map_nsubs_fupz b1 l1'). rewrite (map_nsubs_fupz b1 l2').
              rewrite nsubs_subs_fup. reflexivity. }
            assert (ea : nsubs 0 b1 (fupz c0) = c0) by (apply nsubs_fup).
            pose (q1c := lprove_cast eL ea q1r).
            assert (Hq1c : lweight q1c <= lweight q1).
            { unfold q1c; rewrite lweight_lprove_cast. exact Hq1r. }
            assert (Hb : lweight p0 + lweight q1c <= n).
            { simpl in Hle. assert (H1 : lweight p0 + S (lweight q1) <= n) by (apply le_S_n; exact Hle).
              assert (H2 : lweight q1c <= lweight q1) by exact Hq1c. lia. }
            destruct (IH (subs x0 b1 a0) c0 l1' K1 l2' p0 q1c Hb Hc) as [r Hr].
            exists r. simpl. lia.

    * destruct HC as [m HPL HRL2].
      destruct (lprove_fup_weight 0 pi1) as [p1 Hp1w].
      assert (e1 : map fupz l1' ++ subs x0 (dvar 0) (fupz a0) :: map fupz l2'
                   = (map fupz l1' ++ subs x0 (dvar 0) (fupz a0) :: map fupz m)
                     ++ fupz FA :: map fupz SL).
      { rewrite <- HRL2. rewrite (map_app (fup 0) m (FA :: SL)). simpl.
        rewrite <- app_assoc. reflexivity. }
      assert (Hb1 : lweight p1 + lweight (lprove_cast e1 eq_refl q1) <= n).
      { rewrite lweight_lprove_cast. assert (lweight p1 <= lweight pi1) by exact Hp1w. lia. }
      assert (Hc1 : bp = true -> (map fupz l1' ++ subs x0 (dvar 0) (fupz a0) :: map fupz m) <> []
                     -> length (map fupz DL) = 1%nat).
      { intros Hb HN. rewrite length_map. apply Hc; [exact Hb|].
        rewrite HPL. intro Hnil. apply HN.
        apply (f_equal (@length lform)) in Hnil. rewrite length_app in Hnil. simpl in Hnil. lia. }
      destruct (IH (fup 0 FA) (fup 0 c0)
                  (map fupz l1' ++ subs x0 (dvar 0) (fupz a0) :: map fupz m)
                  (map fupz DL) (map fupz SL)
                  p1 (lprove_cast e1 eq_refl q1) Hb1 Hc1) as [p Hp].
      rewrite lweight_lprove_cast in Hp.
      assert (e2 : (map fupz l1' ++ subs x0 (dvar 0) (fupz a0) :: map fupz m)
                   ++ map fupz DL ++ map fupz SL
                   = map fupz l1' ++ subs x0 (dvar 0) (fupz a0) :: map fupz (m ++ DL ++ SL)).
      { rewrite (map_app (fup 0) m (DL ++ SL)). rewrite (map_app (fup 0) DL SL).
        repeat rewrite <- app_assoc. reflexivity. }
      assert (e3 : l1' ++ lexs x0 a0 :: (m ++ DL ++ SL) = PL ++ DL ++ SL).
      { rewrite HPL. repeat rewrite <- app_assoc. reflexivity. }
      exists (lprove_cast e3 eq_refl
               (lexs_left a0 x0 c0 l1' (m ++ DL ++ SL) (lprove_cast e2 eq_refl p))).
      lw_casts. simpl. lia.
  + (* lexs_right *)
    simpl in Hle.
    assert (Hb1 : lweight pi1 + lweight (lprove_cast HL eq_refl q1) <= n).
    { rewrite lweight_lprove_cast. lia. }
    destruct (IH FA (subs x0 b0 a0) PL DL SL pi1 (lprove_cast HL eq_refl q1) Hb1 Hc) as [p Hp].
    exists (lexs_right (a:=a0) (x:=x0) (b:=b0) (l:=PL ++ DL ++ SL) Hb0 p).
    rewrite lweight_lprove_cast in Hp. lw_casts. simpl. lia.
Qed.

Theorem lprove_trans_weight a b l1 l2 l3 (pi1 : l2 ⊦ a) (pi2 : l1 ++ a :: l3 ⊦ b) :
  (bp = true -> l1 <> [] -> length l2 = 1%nat) ->
  { pi' : l1 ++ l2 ++ l3 ⊦ b | lweight pi' < lweight pi1 + lweight pi2 }.
Proof.
  intros Hc.
  exact (@lprove_trans_aux (lweight pi1 + lweight pi2) a b l1 l2 l3 pi1 pi2
           (Nat.le_refl _) Hc).
Qed.

End WithParameter.
