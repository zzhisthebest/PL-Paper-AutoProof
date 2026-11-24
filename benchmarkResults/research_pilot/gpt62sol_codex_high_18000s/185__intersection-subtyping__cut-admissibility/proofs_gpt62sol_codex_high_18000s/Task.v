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

(* Replacing bound variables with closed formulas preserves derivation
   weight. The lifted substitution fixes the fresh variable of an
   eigenvariable rule. *)
Local Fixpoint lrename (rho : nat -> lform) (A : lform) : lform :=
  match A with
  | dvar n => rho n
  | lvar c n => lvar c n
  | lmap A B => lmap (lrename rho A) (lrename rho B)
  | A ∧ B => lrename rho A ∧ lrename rho B
  | A ∨ B => lrename rho A ∨ lrename rho B
  | lfrl x A => lfrl x (lrename rho A)
  | lexs x A => lexs x (lrename rho A)
  | _ => A
  end.

Local Definition lrename_lift (rho : nat -> lform) (n : nat) :=
  match n with
  | O => dvar 0
  | S k => fupz (rho k)
  end.

Local Definition lrename_open (F : lform) (n : nat) :=
  match n with
  | O => F
  | S k => dvar k
  end.

Local Lemma lcut_subs_absent x F A :
  ~ In x (freevars A) -> subs x F A = A.
Proof.
  induction A; simpl; intros H; try reflexivity.
  - destruct c; simpl in *; try reflexivity.
    destruct (Nat.eq_dec n x); [exfalso; auto | reflexivity].
  - rewrite IHA1, IHA2; auto using in_or_app.
  - rewrite IHA1, IHA2; auto using in_or_app.
  - rewrite IHA1, IHA2; auto using in_or_app.
  - destruct (Nat.eq_dec n x); [reflexivity |].
    rewrite IHA; auto using in_in_remove.
  - destruct (Nat.eq_dec n x); [reflexivity |].
    rewrite IHA; auto using in_in_remove.
Qed.

Local Lemma lrename_subs rho x F A :
  (forall n, closed (rho n)) ->
  lrename rho (subs x F A) = subs x (lrename rho F) (lrename rho A).
Proof.
  intros Hclosed. induction A; simpl; try congruence.
  - destruct c; simpl; try reflexivity.
    + symmetry. apply lcut_subs_absent. now rewrite Hclosed.
    + destruct (Nat.eq_dec n x); reflexivity.
  - destruct (Nat.eq_dec n x); simpl; congruence.
  - destruct (Nat.eq_dec n x); simpl; congruence.
Qed.

Local Lemma lrename_lift_fup rho A :
  lrename (lrename_lift rho) (fupz A) = fupz (lrename rho A).
Proof.
  induction A; simpl; try congruence.
  destruct c; reflexivity.
Qed.

Local Lemma lrename_shift A :
  lrename (fun n => dvar (S n)) A = fupz A.
Proof.
  induction A; simpl; try congruence.
  destruct c; reflexivity.
Qed.

Local Lemma lrename_open_fup F A :
  lrename (lrename_open F) (fupz A) = A.
Proof.
  induction A; simpl; try congruence.
  destruct c; reflexivity.
Qed.

Local Lemma lrename_freevars rho :
  (forall n, closed (rho n)) -> forall A, freevars (lrename rho A) = freevars A.
Proof.
  intros H A. induction A; simpl; try congruence.
  destruct c; simpl; auto.
Qed.

Local Lemma lcut_fup_freevars A : freevars (fupz A) = freevars A.
Proof.
  rewrite <- lrename_shift. now apply lrename_freevars.
Qed.

Local Lemma lrename_lift_closed rho :
  (forall n, closed (rho n)) -> forall n, closed (lrename_lift rho n).
Proof.
  intros H [|n]; simpl; auto. now rewrite lcut_fup_freevars.
Qed.

Local Lemma lrename_open_closed F :
  closed F -> forall n, closed (lrename_open F n).
Proof. intros H [|n]; simpl; auto. Qed.

Local Lemma lrename_open_map F l :
  map (lrename (lrename_open F)) (map fupz l) = l.
Proof.
  rewrite map_map. rewrite <- (map_id l) at 2.
  apply map_ext. apply lrename_open_fup.
Qed.

Local Lemma lrename_eigen rho x A :
  (forall n, closed (lrename_lift rho n)) ->
  lrename (lrename_lift rho) (subs x (dvar 0) (fupz A)) =
  subs x (dvar 0) (fupz (lrename rho A)).
Proof.
  intros H. now rewrite lrename_subs, lrename_lift_fup.
Qed.

Local Lemma lrename_lift_map rho l :
  map (lrename (lrename_lift rho)) (map fupz l) =
  map fupz (map (lrename rho) l).
Proof.
  rewrite !map_map. apply map_ext. apply lrename_lift_fup.
Qed.

Local Lemma lprove_rename l A (p : l ⊦ A) rho :
  (forall n, closed (rho n)) ->
  {q : map (lrename rho) l ⊦ lrename rho A | lweight q = lweight p}.
Proof.
  revert rho.
  induction p; intros rho Hclosed; simpl.
  - exists lidentity. reflexivity.
  - exists (ltop_right _). reflexivity.
  - pose proof (IHp rho Hclosed) as Q.
    rewrite map_app in Q |- *. simpl in Q |- *.
    destruct Q as [q Hq].
    exists (lwith_left1 q). simpl. now rewrite ?Hq, ?Hq1, ?Hq2.
  - pose proof (IHp rho Hclosed) as Q.
    rewrite map_app in Q |- *. simpl in Q |- *.
    destruct Q as [q Hq].
    exists (lwith_left2 q). simpl. now rewrite ?Hq, ?Hq1, ?Hq2.
  - destruct (IHp1 rho Hclosed) as [q1 Hq1].
    destruct (IHp2 rho Hclosed) as [q2 Hq2].
    exists (lwith_right q1 q2). simpl. now rewrite ?Hq, ?Hq1, ?Hq2.
  - destruct (IHp1 rho Hclosed) as [q1 Hq1].
    pose proof (IHp2 rho Hclosed) as Q2.
    rewrite !map_app in Q2 |- *. simpl in Q2 |- *. rewrite map_app.
    destruct Q2 as [q2 Hq2].
    assert (Hmap : bp = true ->
        map (lrename rho) l1 = [] /\ length (map (lrename rho) l2) = 1%nat).
    { intros Hbp. destruct (a0 Hbp) as [-> Hlen].
      simpl. now rewrite length_map. }
    exists (lmap_left Hmap q1 q2). simpl. now rewrite ?Hq, ?Hq1, ?Hq2.
  - pose proof (IHp rho Hclosed) as Q.
    rewrite map_app in Q. simpl in Q.
    destruct Q as [q Hq].
    exists (lmap_right q). simpl. now rewrite ?Hq, ?Hq1, ?Hq2.
  - rewrite map_app. simpl. exists lzero_left. reflexivity.
  - pose proof (IHp1 rho Hclosed) as Q1.
    pose proof (IHp2 rho Hclosed) as Q2.
    rewrite map_app in Q1, Q2 |- *. simpl in Q1, Q2 |- *.
    destruct Q1 as [q1 Hq1]. destruct Q2 as [q2 Hq2].
    exists (lplus_left q1 q2). simpl. now rewrite ?Hq, ?Hq1, ?Hq2.
  - destruct (IHp rho Hclosed) as [q Hq].
    exists (lplus_right1 q). simpl. now rewrite ?Hq, ?Hq1, ?Hq2.
  - destruct (IHp rho Hclosed) as [q Hq].
    exists (lplus_right2 q). simpl. now rewrite ?Hq, ?Hq1, ?Hq2.
  - pose proof (IHp rho Hclosed) as Q.
    rewrite map_app in Q |- *. simpl.
    destruct Q as [q Hq].
    exists (lone_left q). simpl. now rewrite ?Hq, ?Hq1, ?Hq2.
  - exists lone_right. reflexivity.
  - pose proof (IHp rho Hclosed) as Q.
    rewrite map_app in Q |- *. simpl in Q |- *.
    rewrite lrename_subs in Q by exact Hclosed.
    destruct Q as [q Hq].
    assert (Hinst : closed (lrename rho b)) by (now rewrite lrename_freevars).
    exists (lfrl_left Hinst q). simpl. now rewrite ?Hq, ?Hq1, ?Hq2.
  - pose proof (lrename_lift_closed rho Hclosed) as Hlift.
    pose proof (IHp _ Hlift) as Q.
    rewrite lrename_lift_map, lrename_eigen in Q by exact Hlift.
    destruct Q as [q Hq].
    exists (lfrl_right q). simpl. now rewrite ?Hq, ?Hq1, ?Hq2.
  - pose proof (lrename_lift_closed rho Hclosed) as Hlift.
    pose proof (IHp _ Hlift) as Q.
    rewrite map_app in Q |- *. simpl in Q |- *.
    rewrite !lrename_lift_map, lrename_eigen, lrename_lift_fup in Q by exact Hlift.
    destruct Q as [q Hq].
    exists (lexs_left q). simpl. now rewrite ?Hq, ?Hq1, ?Hq2.
  - pose proof (IHp rho Hclosed) as Q.
    rewrite lrename_subs in Q by exact Hclosed.
    destruct Q as [q Hq].
    assert (Hinst : closed (lrename rho b)) by (now rewrite lrename_freevars).
    exists (lexs_right Hinst q). simpl. now rewrite ?Hq, ?Hq1, ?Hq2.
Qed.

Local Lemma lprove_shift l A (p : l ⊦ A) :
  {q : map fupz l ⊦ fupz A | lweight q = lweight p}.
Proof.
  pose proof (lprove_rename p (fun n => dvar (S n)) (fun _ => eq_refl))
    as Q.
  assert (Heq : map (lrename (fun n => dvar (S n))) l = map fupz l).
  { apply map_ext. apply lrename_shift. }
  now rewrite Heq, lrename_shift in Q.
Qed.

Local Lemma lprove_instantiate l A x F
    (p : map fupz l ⊦ subs x (dvar 0) (fupz A)) :
  closed F -> {q : l ⊦ subs x F A | lweight q = lweight p}.
Proof.
  intros HF.
  pose proof (lrename_open_closed F HF) as Hopen.
  pose proof (lprove_rename p (lrename_open F) Hopen) as Q.
  now rewrite lrename_open_map, lrename_subs, lrename_open_fup in Q by exact Hopen.
Qed.

Local Lemma lprove_instantiate_left L R A B x F
    (p : map fupz L ++ subs x (dvar 0) (fupz A) :: map fupz R ⊦ fupz B) :
  closed F -> {q : L ++ subs x F A :: R ⊦ B | lweight q = lweight p}.
Proof.
  intros HF.
  pose proof (lrename_open_closed F HF) as Hopen.
  pose proof (lprove_rename p (lrename_open F) Hopen) as Q.
  rewrite map_app in Q. simpl in Q.
  now rewrite !lrename_open_map, lrename_subs, !lrename_open_fup in Q by exact Hopen.
Qed.

(* Only a lone_left over the empty context can shorten a singleton
   context. Move that rule above a right introduction before cutting. *)
Local Definition lcut_ready l A (p : l ⊦ A) : Prop :=
  match p with
  | @lone_left _ _ L R _ => L ++ R <> []
  | _ => True
  end.

Local Lemma lcut_pad_unit l A (p : l ⊦ A) :
  l = [] -> {q : [1] ⊦ A | lcut_ready q /\ lweight q <= S (lweight p)}.
Proof.
  destruct p; intros E; simpl in *;
    try discriminate;
    try solve [apply app_eq_nil in E as [_ E]; discriminate].
  - exists (ltop_right _). simpl. auto.
  - subst l.
    exists (lwith_right (lone_left [] [] p1) (lone_left [] [] p2)).
    simpl. split; [exact I | lia].
  - subst l.
    exists (@lmap_right bp a b [1] (lone_left [] [a] p)). simpl. auto.
  - subst l.
    exists (lplus_right1 _ (lone_left [] [] p)). simpl. auto.
  - subst l.
    exists (lplus_right2 _ (lone_left [] [] p)). simpl. auto.
  - exists lidentity. simpl. auto.
  - subst l.
    exists (@lfrl_right bp a x [1] (lone_left [] [] p)). simpl. auto.
  - subst l.
    exists (lexs_right e (lone_left [] [] p)). simpl. auto.
Qed.

Local Lemma lcut_prepare l A (p : l ⊦ A) :
  {q : l ⊦ A | lcut_ready q /\ lweight q <= lweight p}.
Proof.
  destruct p;
    try solve [lazymatch goal with
      | |- {q : _ | _ /\ lweight q <= lweight ?orig} =>
          exists orig; split; [exact I | reflexivity]
      end].
  destruct l1 as [|x L], l2 as [|y R].
  - exact (lcut_pad_unit p eq_refl).
  - exists (lone_left [] (y :: R) p). simpl. split; [discriminate | reflexivity].
  - exists (lone_left (x :: L) [] p). simpl. split; [discriminate | reflexivity].
  - exists (lone_left (x :: L) (y :: R) p). simpl. split; [discriminate | reflexivity].
Qed.

Local Definition lcut_side (L M : list lform) :=
  bp = true -> L <> [] -> length M = 1%nat.

Local Lemma lcut_side_map L M :
  lcut_side L M -> lcut_side (map fupz L) (map fupz M).
Proof.
  intros H Hbp Hne. rewrite length_map. apply (H Hbp).
  intros ->. apply Hne. reflexivity.
Qed.

Local Lemma lcut_weight_pos l A (p : l ⊦ A) : 0 < lweight p.
Proof. destruct p; simpl; lia. Qed.

Local Definition lcut_below n :=
  forall A B L M R (p : M ⊦ A) (q : L ++ A :: R ⊦ B),
    lcut_side L M -> lweight p + lweight q < n ->
    {r : L ++ M ++ R ⊦ B | lweight r < lweight p + lweight q}.

Local Definition lcut_intro l A (p : l ⊦ A) : Prop :=
  match p with
  | ltop_right | lwith_right _ _ | lmap_right _ | lplus_right1 _ | lplus_right2 _
  | lone_right | lfrl_right _ | lexs_right _ => True
  | _ => False
  end.

Local Definition lcut_at_rule l A (q : l ⊦ A) (L : list lform) : Prop :=
  match q with
  | @lwith_left1 _ _ _ _ P _ _ | @lwith_left2 _ _ _ _ P _ _
  | @lmap_left _ _ _ _ P _ _ _ _ _ | @lzero_left _ _ P _
  | @lplus_left _ _ _ _ P _ _ _ | @lone_left _ _ P _ _
  | @lfrl_left _ _ _ _ _ P _ _ _ | @lexs_left _ _ _ _ P _ _ => L = P
  | _ => False
  end.

Local Ltac lcut_use IH L R p q side name :=
  pose proof (IH _ _ L _ R p q side ltac:(cbn [lweight app] in *; lia)) as name.

Local Lemma lcut_principal_reduce n (IH : lcut_below n)
    A B L M R G (p : M ⊦ A) (q : G ⊦ B) :
  G = L ++ A :: R -> lcut_intro p -> lcut_at_rule q L -> lcut_side L M ->
  lweight p + lweight q <= n ->
  {r : L ++ M ++ R ⊦ B | lweight r < lweight p + lweight q}.
Proof.
  revert L R.
  destruct q as [B | G | X Y B P Q q | X Y B P Q q | X Y G q1 q2
    | X Y B P Q T Hmap q1 q2 | X Y G q | B P Q
    | X Y B P Q q1 q2 | X Y G q | X Y G q | B P Q q
    | | X x F B P Q HF q | X x G q | X x B P Q q | X x F G HF q];
    intros L R E Hintro Hrule Hside Hbound;
    cbn [lcut_at_rule] in Hrule; try contradiction;
    subst L; apply app_inv_head in E; injection E as EA ER; subst R;
    destruct p as [A | M | U V A N O p | U V A N O p | U V M p1 p2
    | U V A N O W Hmp p1 p2 | U V M p | A N O
    | U V A N O p1 p2 | U V M p | U V M p | A N O p
    | | U u J A N O HJ p | U u M p | U u A N O p | U u J M HJ p];
    cbn [lcut_intro] in Hintro; try contradiction;
    inversion EA; subst; clear EA.
  - lcut_use IH P Q p1 q Hside Cut.
    destruct Cut as [r Hr]. exists r. cbn [lweight app] in *. lia.
  - lcut_use IH P Q p2 q Hside Cut.
    destruct Cut as [r Hr]. exists r. cbn [lweight app] in *. lia.
  - (* Cut the argument into the map body, then cut into the continuation. *)
    assert (Harg : lcut_side M Q) by (intros Hbp _; exact (proj2 (Hmap Hbp))).
    lcut_use IH M (@nil lform) q1 p Harg Cut.
    rewrite app_nil_r in Cut. destruct Cut as [r Hr].
    assert (Hres : lcut_side P (M ++ Q)).
    { intros Hbp Hne. exfalso. exact (Hne (proj1 (Hmap Hbp))). }
    lcut_use IH P T r q2 Hres Cut.
    rewrite <- app_assoc in Cut.
    destruct Cut as [s Hs]. exists s. cbn [lweight app] in *. lia.
  - lcut_use IH P Q p q1 Hside Cut.
    destruct Cut as [r Hr]. exists r. cbn [lweight app] in *. lia.
  - lcut_use IH P Q p q2 Hside Cut.
    destruct Cut as [r Hr]. exists r. cbn [lweight app] in *. lia.
  - exists q. cbn [lweight app Nat.add]. lia.
  - destruct (lprove_instantiate M U u F p HF) as [p' Hp'].
    lcut_use IH P Q p' q Hside Cut.
    destruct Cut as [r Hr]. exists r. cbn [lweight app] in *. lia.
  - destruct (lprove_instantiate_left P Q U B u J q HJ) as [q' Hq'].
    lcut_use IH P Q p q' Hside Cut.
    destruct Cut as [r Hr]. exists r. cbn [lweight app] in *. lia.
Qed.

(* Locate the cut relative to a left rule's active formula. *)
Local Lemma lcut_split (A : lform) P (X : lform) Q L R (E : P ++ X :: Q = L ++ A :: R) :
  ({K | P = L ++ A :: K /\ R = K ++ X :: Q} +
   (L = P /\ A = X /\ R = Q) +
   {K | Q = K ++ A :: R /\ L = P ++ X :: K})%type.
Proof.
  revert L E.
  induction P as [|Y P IH]; intros [|Z L] E; simpl in E.
  - injection E as -> ->. left. right. auto.
  - injection E as EX EQ. subst Z Q. right. exists L. auto.
  - injection E as EY ER. subst Y R. left. left. exists P. auto.
  - injection E as EY E. subst Y.
    destruct (IH L E) as [[[K [EP ER]] | [EL [EA ER]]] | [K [EQ EL]]].
    + left. left. exists K. simpl. split; congruence.
    + left. right. simpl. subst. auto.
    + right. exists K. simpl. split; congruence.
Qed.

(* For a cut past a map formula, locate it in the argument or the continuation. *)
Local Lemma lcut_split_concat (A : lform) Q T K R (E : Q ++ T = K ++ A :: R) :
  ({U | Q = K ++ A :: U /\ R = U ++ T} +
   {U | T = U ++ A :: R /\ K = Q ++ U})%type.
Proof.
  revert K E.
  induction Q as [|Y Q IH]; intros [|Z K] E; simpl in E.
  - subst T. right. exists []. auto.
  - subst T. right. exists (Z :: K). auto.
  - injection E as EY ER. subst Y R. left. exists Q. auto.
  - injection E as EY E. subst Y.
    destruct (IH K E) as [[U [EQ ER]] | [U [ET EK]]].
    + left. exists U. simpl. split; congruence.
    + right. exists U. simpl. split; congruence.
Qed.

Local Lemma lcut_side_past L X K M :
  lcut_side (L ++ X :: K) M -> forall P, lcut_side P M.
Proof.
  intros H P Hbp _. apply (H Hbp).
  intro E. apply app_eq_nil in E as [_ E]. discriminate.
Qed.

Local Lemma lprove_recontext G G' B (q : G ⊦ B) :
  G = G' -> {q' : G' ⊦ B | lweight q' = lweight q}.
Proof. intros <-. now exists q. Qed.

Local Ltac lcut_lists :=
  repeat first [rewrite <- app_assoc | rewrite map_app | rewrite app_nil_r
               | progress cbn [app map]];
  reflexivity.

Local Ltac lcut_context p ctx q Hq :=
  destruct (@lprove_recontext _ ctx _ p ltac:(lcut_lists)) as [q Hq].

Local Ltac lcut_finish proof :=
  lazymatch goal with
  | |- @sig (?seq ?ctx ?goal) _ =>
      let r := fresh "r" in let Hr := fresh "Hr" in
      lcut_context proof ctx r Hr;
      exists r; cbn [lweight app] in *; lia
  end.

Local Ltac lcut_split_rule A P X Q L R E :=
  let K := fresh "K" in
  let EP := fresh "EP" in let ER := fresh "ER" in
  let EL := fresh "EL" in let EA := fresh "EA" in let EQ := fresh "EQ" in
  destruct (lcut_split A P X Q L R E)
    as [[[K [EP ER]] | [EL [EA ER]]] | [K [EQ EL]]];
  [subst P R | subst L A R | subst Q L].

Local Lemma lcut_through_right n (IH : lcut_below n)
    A B L M R G (p : M ⊦ A) (q : G ⊦ B) :
  G = L ++ A :: R -> lcut_intro p -> lcut_side L M ->
  lweight p + lweight q <= n ->
  {r : L ++ M ++ R ⊦ B | lweight r < lweight p + lweight q}.
Proof.
  revert L R.
  destruct q as [B | G | X Y B P Q q | X Y B P Q q | X Y G q1 q2
    | X Y B P Q T Hmap q1 q2 | X Y G q | B P Q
    | X Y B P Q q1 q2 | X Y G q | X Y G q | B P Q q
    | | X x F B P Q HF q | X x G q | X x B P Q q | X x F G HF q];
    intros L R E Hintro Hside Hbound; pose proof (lcut_weight_pos p) as Hpos.
  - destruct L as [|Z L].
    + injection E as EA ER. subst A R.
      rewrite app_nil_r. exists p. cbn [lweight app]. lia.
    + assert (Hlen := f_equal (@length lform) E).
      simpl in Hlen. rewrite length_app in Hlen. simpl in Hlen. lia.
  - exists (ltop_right _). cbn [lweight app]. lia.
  - lcut_split_rule A P (X ∧ Y) Q L R E.
    + lcut_context q (L ++ A :: (K ++ X :: Q)) q' Hq.
      lcut_use IH L (K ++ X :: Q) p q' Hside Cut.
      destruct Cut as [s Hs].
      lcut_context s ((L ++ M ++ K) ++ X :: Q) s' Hs'.
      lcut_finish (@lwith_left1 bp X Y B (L ++ M ++ K) Q s').
    + eapply lcut_principal_reduce; eauto; reflexivity.
    + assert (Hsub : lcut_side (P ++ X :: K) M) by eauto using lcut_side_past.
      lcut_context q ((P ++ X :: K) ++ A :: R) q' Hq.
      lcut_use IH (P ++ X :: K) R p q' Hsub Cut.
      destruct Cut as [s Hs].
      lcut_context s (P ++ X :: (K ++ M ++ R)) s' Hs'.
      lcut_finish (lwith_left1 (b := Y) s').
  - lcut_split_rule A P (Y ∧ X) Q L R E.
    + lcut_context q (L ++ A :: (K ++ X :: Q)) q' Hq.
      lcut_use IH L (K ++ X :: Q) p q' Hside Cut.
      destruct Cut as [s Hs].
      lcut_context s ((L ++ M ++ K) ++ X :: Q) s' Hs'.
      lcut_finish (@lwith_left2 bp X Y B (L ++ M ++ K) Q s').
    + eapply lcut_principal_reduce; eauto; reflexivity.
    + assert (Hsub : lcut_side (P ++ X :: K) M) by eauto using lcut_side_past.
      lcut_context q ((P ++ X :: K) ++ A :: R) q' Hq.
      lcut_use IH (P ++ X :: K) R p q' Hsub Cut.
      destruct Cut as [s Hs].
      lcut_context s (P ++ X :: (K ++ M ++ R)) s' Hs'.
      lcut_finish (lwith_left2 (b := Y) s').
  - subst G.
    lcut_use IH L R p q1 Hside Cut1.
    lcut_use IH L R p q2 Hside Cut2.
    destruct Cut1 as [s1 Hs1]. destruct Cut2 as [s2 Hs2].
    exists (lwith_right s1 s2). cbn [lweight app] in *. lia.
  - destruct (lcut_split A P (Y / X) (Q ++ T) L R E)
      as [[[K [EP ER]] | [EL [EA ER]]] | [K [EQ EL]]].
    + subst P R. lcut_context q2 (L ++ A :: (K ++ Y :: T)) q' Hq.
      lcut_use IH L (K ++ Y :: T) p q' Hside Cut.
      destruct Cut as [s Hs].
      lcut_context s ((L ++ M ++ K) ++ Y :: T) s' Hs'.
      assert (Hnew : bp = true -> L ++ M ++ K = [] /\ length Q = 1%nat).
      { intros Hbp. destruct (Hmap Hbp) as [Epre _].
        apply app_eq_nil in Epre as [_ Epre]. discriminate. }
      lcut_finish (@lmap_left bp X Y B (L ++ M ++ K) Q T Hnew q1 s').
    + subst L A R. eapply lcut_principal_reduce; eauto; reflexivity.
    + subst L. destruct (lcut_split_concat A Q T K R EQ)
        as [[U [Earg ER]] | [U [ET EK]]].
      * subst Q R.
        assert (Hsub : lcut_side K M) by eauto using lcut_side_past.
        lcut_use IH K U p q1 Hsub Cut.
        destruct Cut as [s Hs].
        assert (Hnew : bp = true -> P = [] /\ length (K ++ M ++ U) = 1%nat).
        { intros Hbp. destruct (Hmap Hbp) as [HP Hlen].
          split; [exact HP |].
          pose proof (Hside Hbp ltac:(intro Epre;
            apply app_eq_nil in Epre as [_ Epre]; discriminate)).
          rewrite !length_app in *. simpl in *. lia. }
        lcut_finish (@lmap_left bp X Y B P (K ++ M ++ U) T Hnew s q2).
      * subst T K.
        assert (Hsub : lcut_side (P ++ Y :: U) M) by eauto using lcut_side_past.
        lcut_context q2 ((P ++ Y :: U) ++ A :: R) q' Hq.
        lcut_use IH (P ++ Y :: U) R p q' Hsub Cut.
        destruct Cut as [s Hs].
        lcut_context s (P ++ Y :: (U ++ M ++ R)) s' Hs'.
        lcut_finish (@lmap_left bp X Y B P Q (U ++ M ++ R) Hmap q1 s').
  - subst G.
    lcut_context q (L ++ A :: (R · X)) q' Hq.
    lcut_use IH L (R · X) p q' Hside Cut.
    destruct Cut as [s Hs].
    lcut_context s ((L ++ M ++ R) · X) s' Hs'.
    exists (lmap_right s'). cbn [lweight app] in *. lia.
  - lcut_split_rule A P 0 Q L R E.
    + lcut_finish (@lzero_left bp B (L ++ M ++ K) Q).
    + eapply lcut_principal_reduce; eauto; reflexivity.
    + lcut_finish (@lzero_left bp B P (K ++ M ++ R)).
  - lcut_split_rule A P (X ∨ Y) Q L R E.
    + lcut_context q1 (L ++ A :: (K ++ X :: Q)) q1' Hq1.
      lcut_context q2 (L ++ A :: (K ++ Y :: Q)) q2' Hq2.
      lcut_use IH L (K ++ X :: Q) p q1' Hside Cut1.
      lcut_use IH L (K ++ Y :: Q) p q2' Hside Cut2.
      destruct Cut1 as [s1 Hs1]. destruct Cut2 as [s2 Hs2].
      lcut_context s1 ((L ++ M ++ K) ++ X :: Q) s1' Hs1'.
      lcut_context s2 ((L ++ M ++ K) ++ Y :: Q) s2' Hs2'.
      lcut_finish (lplus_left s1' s2').
    + eapply lcut_principal_reduce; eauto; reflexivity.
    + assert (Hsub1 : lcut_side (P ++ X :: K) M) by eauto using lcut_side_past.
      assert (Hsub2 : lcut_side (P ++ Y :: K) M) by eauto using lcut_side_past.
      lcut_context q1 ((P ++ X :: K) ++ A :: R) q1' Hq1.
      lcut_context q2 ((P ++ Y :: K) ++ A :: R) q2' Hq2.
      lcut_use IH (P ++ X :: K) R p q1' Hsub1 Cut1.
      lcut_use IH (P ++ Y :: K) R p q2' Hsub2 Cut2.
      destruct Cut1 as [s1 Hs1]. destruct Cut2 as [s2 Hs2].
      lcut_context s1 (P ++ X :: (K ++ M ++ R)) s1' Hs1'.
      lcut_context s2 (P ++ Y :: (K ++ M ++ R)) s2' Hs2'.
      lcut_finish (lplus_left s1' s2').
  - subst G.
    lcut_use IH L R p q Hside Cut.
    destruct Cut as [s Hs]. exists (lplus_right1 Y s). cbn [lweight app] in *. lia.
  - subst G.
    lcut_use IH L R p q Hside Cut.
    destruct Cut as [s Hs]. exists (lplus_right2 Y s). cbn [lweight app] in *. lia.
  - lcut_split_rule A P 1 Q L R E.
    + lcut_context q (L ++ A :: (K ++ Q)) q' Hq.
      lcut_use IH L (K ++ Q) p q' Hside Cut.
      destruct Cut as [s Hs].
      lcut_context s ((L ++ M ++ K) ++ Q) s' Hs'.
      lcut_finish (lone_left (L ++ M ++ K) Q s').
    + eapply lcut_principal_reduce; eauto; reflexivity.
    + assert (Hsub : lcut_side (P ++ K) M) by eauto using lcut_side_past.
      lcut_context q ((P ++ K) ++ A :: R) q' Hq.
      lcut_use IH (P ++ K) R p q' Hsub Cut.
      destruct Cut as [s Hs].
      lcut_context s (P ++ (K ++ M ++ R)) s' Hs'.
      lcut_finish (lone_left P (K ++ M ++ R) s').
  - symmetry in E. apply app_eq_nil in E as [_ E]. discriminate.
  - lcut_split_rule A P (lfrl x X) Q L R E.
    + lcut_context q (L ++ A :: (K ++ subs x F X :: Q)) q' Hq.
      lcut_use IH L (K ++ subs x F X :: Q) p q' Hside Cut.
      destruct Cut as [s Hs].
      lcut_context s ((L ++ M ++ K) ++ subs x F X :: Q) s' Hs'.
      lcut_finish (@lfrl_left bp X x F B (L ++ M ++ K) Q HF s').
    + eapply lcut_principal_reduce; eauto; reflexivity.
    + assert (Hsub : lcut_side (P ++ subs x F X :: K) M) by eauto using lcut_side_past.
      lcut_context q ((P ++ subs x F X :: K) ++ A :: R) q' Hq.
      lcut_use IH (P ++ subs x F X :: K) R p q' Hsub Cut.
      destruct Cut as [s Hs].
      lcut_context s (P ++ subs x F X :: (K ++ M ++ R)) s' Hs'.
      lcut_finish (@lfrl_left bp X x F B P (K ++ M ++ R) HF s').
  - subst G.
    destruct (lprove_shift p) as [p' Hp].
    lcut_context q (map fupz L ++ fupz A :: map fupz R) q' Hq.
    lcut_use IH (map fupz L) (map fupz R) p' q' (lcut_side_map Hside) Cut.
    destruct Cut as [s Hs].
    lcut_context s (map fupz (L ++ M ++ R)) s' Hs'.
    exists (@lfrl_right bp X x (L ++ M ++ R) s'). cbn [lweight app] in *. lia.
  - lcut_split_rule A P (lexs x X) Q L R E.
    + destruct (lprove_shift p) as [p' Hp].
      lcut_context q (map fupz L ++ fupz A :: (map fupz K ++ subs x (dvar 0) (fupz X) :: map fupz Q)) q' Hq.
      lcut_use IH (map fupz L) (map fupz K ++ subs x (dvar 0) (fupz X) :: map fupz Q) p' q'
        (lcut_side_map Hside) Cut.
      destruct Cut as [s Hs].
      lcut_context s (map fupz (L ++ M ++ K) ++ subs x (dvar 0) (fupz X) :: map fupz Q) s' Hs'.
      lcut_finish (@lexs_left bp X x B (L ++ M ++ K) Q s').
    + eapply lcut_principal_reduce; eauto; reflexivity.
    + destruct (lprove_shift p) as [p' Hp].
      assert (Hsub : lcut_side (map fupz P ++ subs x (dvar 0) (fupz X) :: map fupz K) (map fupz M)).
      { intros Hbp _. rewrite length_map.
        apply (Hside Hbp).
        intro Epre. apply app_eq_nil in Epre as [_ Epre]. discriminate. }
      lcut_context q ((map fupz P ++ subs x (dvar 0) (fupz X) :: map fupz K) ++ fupz A :: map fupz R) q' Hq.
      lcut_use IH (map fupz P ++ subs x (dvar 0) (fupz X) :: map fupz K) (map fupz R) p' q' Hsub Cut.
      destruct Cut as [s Hs].
      lcut_context s (map fupz P ++ subs x (dvar 0) (fupz X) :: map fupz (K ++ M ++ R)) s' Hs'.
      lcut_finish (@lexs_left bp X x B P (K ++ M ++ R) s').
  - subst G.
    lcut_use IH L R p q Hside Cut.
    destruct Cut as [s Hs].
    exists (@lexs_right bp X x F (L ++ M ++ R) HF s). cbn [lweight app] in *. lia.
Qed.

Local Lemma lcut_through_left n (IH : lcut_below n)
    A B L M R (p : M ⊦ A) :
  forall (q : L ++ A :: R ⊦ B),
  lcut_ready p -> lcut_side L M -> lweight p + lweight q <= n ->
  {r : L ++ M ++ R ⊦ B | lweight r < lweight p + lweight q}.
Proof.
  destruct p as [A | M | X Y A P Q p | X Y A P Q p | X Y M p1 p2
    | X Y A P Q T Hmap p1 p2 | X Y M p | A P Q
    | X Y A P Q p1 p2 | X Y M p | X Y M p | A P Q p
    | | X x F A P Q HF p | X x M p | X x A P Q p | X x F M HF p];
    intros q Hready Hside Hbound;
    try solve [eapply lcut_through_right;
      [exact IH | reflexivity | exact I | exact Hside | exact Hbound]].
  - exists q. cbn [lweight app Nat.add]. lia.
  - assert (Hsub : lcut_side L (P ++ X :: Q)).
    { intros Hbp Hne. specialize (Hside Hbp Hne).
      now rewrite length_app in *. }
    lcut_use IH L R p q Hsub Cut.
    destruct Cut as [s Hs].
    lcut_context s ((L ++ P) ++ X :: (Q ++ R)) s' Hs'.
    lcut_finish (@lwith_left1 bp X Y B (L ++ P) (Q ++ R) s').
  - assert (Hsub : lcut_side L (P ++ X :: Q)).
    { intros Hbp Hne. specialize (Hside Hbp Hne).
      now rewrite length_app in *. }
    lcut_use IH L R p q Hsub Cut.
    destruct Cut as [s Hs].
    lcut_context s ((L ++ P) ++ X :: (Q ++ R)) s' Hs'.
    lcut_finish (@lwith_left2 bp X Y B (L ++ P) (Q ++ R) s').
  - assert (Hnil : bp = true -> L = []).
    { intros Hbp. destruct L as [|Z L]; [reflexivity |].
      pose proof (Hside Hbp ltac:(discriminate)) as Hlen.
      destruct (Hmap Hbp) as [_ Harg].
      rewrite !length_app in Hlen. simpl in Hlen.
      rewrite length_app in Hlen. lia. }
    assert (Hsub : lcut_side L (P ++ Y :: T)).
    { intros Hbp Hne. contradiction (Hne (Hnil Hbp)). }
    lcut_use IH L R p2 q Hsub Cut.
    destruct Cut as [s Hs].
    lcut_context s ((L ++ P) ++ Y :: (T ++ R)) s' Hs'.
    assert (Hnew : bp = true -> L ++ P = [] /\ length Q = 1%nat).
    { intros Hbp. rewrite (Hnil Hbp). exact (Hmap Hbp). }
    lcut_finish (@lmap_left bp X Y B (L ++ P) Q (T ++ R) Hnew p1 s').
  - pose proof (lcut_weight_pos q).
    lcut_finish (@lzero_left bp B (L ++ P) (Q ++ R)).
  - assert (Hsub1 : lcut_side L (P ++ X :: Q)).
    { intros Hbp Hne. specialize (Hside Hbp Hne).
      now rewrite length_app in *. }
    assert (Hsub2 : lcut_side L (P ++ Y :: Q)).
    { intros Hbp Hne. specialize (Hside Hbp Hne).
      now rewrite length_app in *. }
    lcut_use IH L R p1 q Hsub1 Cut1.
    lcut_use IH L R p2 q Hsub2 Cut2.
    destruct Cut1 as [s1 Hs1]. destruct Cut2 as [s2 Hs2].
    lcut_context s1 ((L ++ P) ++ X :: (Q ++ R)) s1' Hs1'.
    lcut_context s2 ((L ++ P) ++ Y :: (Q ++ R)) s2' Hs2'.
    lcut_finish (lplus_left s1' s2').
  - assert (Hsub : lcut_side L (P ++ Q)).
    { intros Hbp Hne. specialize (Hside Hbp Hne).
      exfalso. apply Hready. apply length_zero_iff_nil.
      rewrite !length_app in *. simpl in *. lia. }
    lcut_use IH L R p q Hsub Cut.
    destruct Cut as [s Hs].
    lcut_context s ((L ++ P) ++ (Q ++ R)) s' Hs'.
    lcut_finish (lone_left (L ++ P) (Q ++ R) s').
  - assert (Hsub : lcut_side L (P ++ subs x F X :: Q)).
    { intros Hbp Hne. specialize (Hside Hbp Hne).
      now rewrite length_app in *. }
    lcut_use IH L R p q Hsub Cut.
    destruct Cut as [s Hs].
    lcut_context s ((L ++ P) ++ subs x F X :: (Q ++ R)) s' Hs'.
    lcut_finish (@lfrl_left bp X x F B (L ++ P) (Q ++ R) HF s').
  - destruct (lprove_shift q) as [q' Hq'].
    lcut_context q' (map fupz L ++ fupz A :: map fupz R) q'' Hq''.
    assert (Hsub : lcut_side (map fupz L)
      (map fupz P ++ subs x (dvar 0) (fupz X) :: map fupz Q)).
    { intros Hbp Hne.
      pose proof (lcut_side_map Hside Hbp Hne) as Hlen.
      rewrite !map_app in Hlen. simpl in Hlen.
      now rewrite length_app in *. }
    lcut_use IH (map fupz L) (map fupz R) p q'' Hsub Cut.
    destruct Cut as [s Hs].
    lcut_context s (map fupz (L ++ P) ++ subs x (dvar 0) (fupz X) ::
                   map fupz (Q ++ R)) s' Hs'.
    lcut_finish (@lexs_left bp X x B (L ++ P) (Q ++ R) s').
Qed.

(* Each recursive call has a strictly smaller sum of derivation weights. *)
Local Lemma lcut_by_weight n : lcut_below (S n).
Proof.
  induction n as [n IH] using lt_wf_rect.
  assert (Hlower : lcut_below n).
  { intros A B L M R p q Hside Hlt.
    exact (IH _ Hlt A B L M R p q Hside (Nat.lt_succ_diag_r _)). }
  intros A B L M R p q Hside Hlt.
  destruct (lcut_prepare p) as [p' [Hready Hweight]].
  assert (Hbound : lweight p' + lweight q <= n) by lia.
  destruct (@lcut_through_left n Hlower A B L M R p' q Hready Hside Hbound) as [r Hr].
  exists r. lia.
Qed.

Theorem lprove_trans_weight a b l1 l2 l3 (pi1 : l2 ⊦ a) (pi2 : l1 ++ a :: l3 ⊦ b) :
  (bp = true -> l1 <> [] -> length l2 = 1%nat) ->
  { pi' : l1 ++ l2 ++ l3 ⊦ b | lweight pi' < lweight pi1 + lweight pi2 }.
Proof.
  intros Hside.
  exact (@lcut_by_weight (lweight pi1 + lweight pi2)
    a b l1 l2 l3 pi1 pi2 Hside (Nat.lt_succ_diag_r _)).
Qed.

End WithParameter.
