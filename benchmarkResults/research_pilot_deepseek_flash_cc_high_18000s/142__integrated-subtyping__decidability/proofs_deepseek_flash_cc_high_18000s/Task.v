From Stdlib Require Import List.
Import Relation_Operators.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Wellfounded.Lexicographic_Product.
From Stdlib Require Import Wellfounded.Inverse_Image.
From Stdlib Require Import Wellfounded.Transitive_Closure.
Require Import Section3_Requirements.
Require Import Section4_Requirements.
Import ListNotations.
Import List.
Import Relation_Operators.
Module Integrated (M_traditional : Traditional) (M_intersector : Intersector M_traditional).
Import M_traditional.
Import M_intersector.
Inductive IPremise {ll lr : Lit} (r : RRule ll lr) : T -> T -> Prop :=
    ipremise (tl tr : T) : RPremise r tl tr -> IPremise r (Integrate intersect tl) tr.
Definition isub' : T -> T -> Prop := rsubf (@IPremise).
Definition isub (tl : T) : T -> Prop := isub' (Integrate intersect tl).

(* --- dsubda helpers --- *)
Lemma esub_int_ll A B : esub (TIsect A B) A. Proof. apply dsubda_int_ll. Qed.
Lemma esub_int_lr A B : esub (TIsect A B) B. Proof. apply dsubda_int_lr. Qed.
Lemma esub_top t : esub t TTop. Proof. apply dsubda_top. Qed.
Lemma esub_refl t : esub t t. Proof. apply dsubda_refl. Qed.
Lemma esub_tr a b c : esub a b -> esub b c -> esub a c. Proof. apply dsubda_trans. Qed.
Lemma esub_int_r t A B : esub t A -> esub t B -> esub t (TIsect A B). Proof. apply dsubda_int_r. Qed.
Lemma esub_uni_l A B t : esub A t -> esub B t -> esub (TUni A B) t. Proof. apply dsubda_uni_l. Qed.
Lemma esub_uni_rl t B : esub t (TUni t B). Proof. apply dsubda_uni_rl. Qed.
Lemma esub_uni_rr t B : esub t (TUni B t). Proof. apply dsubda_uni_rr. Qed.
Lemma esub_uni_rl' A B C : esub A B -> esub A (TUni B C).
Proof. intro H. eapply esub_tr with (b := B); [exact H | apply dsubda_uni_rl]. Qed.
Lemma esub_uni_rr' A B C : esub A C -> esub A (TUni B C).
Proof. intro H. eapply esub_tr with (b := C); [exact H | apply dsubda_uni_rr]. Qed.
Lemma esub_dist A B C : esub (TIsect A (TUni B C)) (TUni (TIsect A B) (TIsect A C)).
Proof. apply dsubda_dist. Qed.

Lemma esub_Isect_congr A A' B B' : esub A A' -> esub B B' -> esub (TIsect A B) (TIsect A' B').
Proof.
  intros HA HB. apply esub_int_r.
  - eapply esub_tr with (b := A); [apply esub_int_ll | exact HA].
  - eapply esub_tr with (b := B); [apply esub_int_lr | exact HB].
Qed.

Lemma esub_Isect_swap A B : esub (TIsect A B) (TIsect B A).
Proof. apply esub_int_r; [apply esub_int_lr | apply esub_int_ll]. Qed.

Lemma esub_Isect_assoc_l A B C : esub (TIsect A (TIsect B C)) (TIsect (TIsect A B) C).
Proof.
  apply esub_int_r.
  - apply esub_int_r.
    + apply esub_int_ll.
    + eapply esub_tr with (b := TIsect B C); [apply esub_int_lr | apply esub_int_ll].
  - eapply esub_tr with (b := TIsect B C); [apply esub_int_lr | apply esub_int_lr].
Qed.
Lemma esub_Isect_assoc_r A B C : esub (TIsect (TIsect A B) C) (TIsect A (TIsect B C)).
Proof.
  apply esub_int_r.
  - eapply esub_tr with (b := TIsect A B); [apply esub_int_ll | apply esub_int_ll].
  - apply esub_int_r.
    + eapply esub_tr with (b := TIsect A B); [apply esub_int_ll | apply esub_int_lr].
    + apply esub_int_lr.
Qed.

Lemma esub_Isect_top_r A : esub (TIsect A TTop) A.
Proof. apply esub_int_ll. Qed.
Lemma esub_Isect_top_l A : esub (TIsect TTop A) A.
Proof. apply esub_int_lr. Qed.
Lemma esub_Isect_top_intro A : esub A (TIsect A TTop).
Proof. apply esub_int_r; [apply esub_refl | apply esub_top]. Qed.

Lemma esub_Isect_mid_swap X b L : esub (TIsect (TIsect X b) L) (TIsect (TIsect X L) b).
Proof.
  apply esub_int_r.
  - apply esub_int_r.
    + eapply esub_tr with (b := TIsect X b); [apply esub_int_ll | apply esub_int_ll].
    + apply esub_int_lr.
  - eapply esub_tr with (b := TIsect X b); [apply esub_int_ll | apply esub_int_lr].
Qed.
Lemma esub_Isect_mid_swap' X b L : esub (TIsect (TIsect X L) b) (TIsect (TIsect X b) L).
Proof.
  apply esub_int_r.
  - apply esub_int_r.
    + eapply esub_tr with (b := TIsect X L); [apply esub_int_ll | apply esub_int_ll].
    + apply esub_int_lr.
  - eapply esub_tr with (b := TIsect X L); [apply esub_int_ll | apply esub_int_lr].
Qed.

Lemma esub_Intersect_app_l ls ls' : esub (Intersect (ls++ls')) (TIsect (Intersect ls) (Intersect ls')).
Proof.
  induction ls as [| a ls IH]; cbn [Intersect app].
  - apply esub_int_r; [apply esub_top | apply esub_refl].
  - apply esub_int_r.
    + apply esub_int_r.
      * apply esub_int_ll.
      * eapply esub_tr with (b := Intersect (ls++ls')); [apply esub_int_lr |].
        eapply esub_tr with (b := TIsect (Intersect ls) (Intersect ls'));
          [exact IH | apply esub_int_ll].
    + eapply esub_tr with (b := Intersect (ls++ls')); [apply esub_int_lr |].
      eapply esub_tr with (b := TIsect (Intersect ls) (Intersect ls'));
        [exact IH | apply esub_int_lr].
Qed.

Lemma esub_Intersect_app_r ls ls' : esub (TIsect (Intersect ls) (Intersect ls')) (Intersect (ls++ls')).
Proof.
  induction ls as [| a ls IH]; cbn [Intersect app].
  - apply esub_Isect_top_l.
  - apply esub_int_r.
    + eapply esub_tr with (b := TIsect (TLit a) (Intersect ls));
        [apply esub_int_ll | apply esub_int_ll].
    + eapply esub_tr with (b := TIsect (Intersect ls) (Intersect ls')).
      * apply esub_int_r.
        -- eapply esub_tr with (b := TIsect (TLit a) (Intersect ls));
             [apply esub_int_ll | apply esub_int_lr].
        -- apply esub_int_lr.
      * exact IH.
Qed.

Section IntegratedUpper.
Definition Spec (X : T) (f : list Lit -> T) : Prop :=
  forall ls, esub (TIsect X (Intersect ls)) (f ls).

Lemma Main : forall t : T, forall (X : T) (f : list Lit -> T),
  Spec X f -> esub (TIsect X t) (Integrate f t).
Proof.
  intro t. induction t; intros X f HS.
  - (* TTop *) cbn [Integrate]. change (esub (TIsect X (Intersect [])) (f [])); apply HS.
  - (* TBot *) cbn [Integrate]. apply esub_int_lr.
  - (* TUni *) cbn [Integrate].
    eapply esub_tr with (b := TUni (TIsect X t1) (TIsect X t2)).
    + apply esub_dist.
    + apply esub_uni_l.
      * eapply esub_tr with (b := Integrate f t1); [apply IHt1; exact HS | apply dsubda_uni_rl].
      * eapply esub_tr with (b := Integrate f t2); [apply IHt2; exact HS | apply dsubda_uni_rr].
  - (* TIsect *) cbn [Integrate].
    pose (g := fun l : list Lit => Integrate (fun l' : list Lit => f (l ++ l')) t2).
    eapply esub_tr with (b := TIsect (TIsect X t2) t1).
    + eapply esub_tr with (b := TIsect (TIsect X t1) t2).
      * apply esub_Isect_assoc_l.
      * apply esub_Isect_mid_swap'.
    + apply IHt1 with (X := TIsect X t2) (f := g).
      intros ls.
      eapply esub_tr with (b := TIsect (TIsect X (Intersect ls)) t2).
      * apply esub_Isect_mid_swap.
      * apply IHt2 with (X := TIsect X (Intersect ls)) (f := fun l' => f (ls ++ l')).
        intros ls'.
        eapply esub_tr with (b := TIsect X (Intersect (ls ++ ls'))).
        -- eapply esub_tr with (b := TIsect X (TIsect (Intersect ls) (Intersect ls'))).
           ++ apply esub_Isect_assoc_r.
           ++ apply esub_Isect_congr; [apply esub_refl | apply esub_Intersect_app_r].
        -- apply HS.
  - (* TLit *) cbn [Integrate].
    eapply esub_tr with (b := TIsect X (Intersect [l])).
    + apply esub_int_r.
      * apply esub_int_ll.
      * change (esub (TIsect X (TLit l)) (TIsect (TLit l) TTop)).
        apply esub_int_r; [apply esub_int_lr | apply esub_top].
    + apply HS.
Qed.

Lemma esub_Integrate_upper : forall t : T, esub t (Integrate intersect t).
Proof.
  intro t.
  eapply esub_tr with (b := TIsect TTop t).
  - apply esub_int_r; [apply esub_top | apply esub_refl].
  - apply Main with (X := TTop) (f := intersect).
    intros ls.
    eapply esub_tr with (b := Intersect ls).
    + apply esub_Isect_top_l.
    + apply IntersectorSoundness.
Qed.
End IntegratedUpper.

(* ---------------- soundness infrastructure ---------------- *)
Lemma dsuba_dsubda : forall (A : T -> T -> Prop) t tr, dsuba (@DPremise) A t tr -> dsubda (@DPremise) A t tr.
Proof.
  intros A t tr H. induction H.
  - apply dsubda_refl.
  - apply dsubda_trans with tm; assumption.
  - apply dsubda_assume; assumption.
  - apply dsubda_lit with r. intros ptl ptr Hp. apply H0. assumption.
  - apply dsubda_top.
  - apply dsubda_bot.
  - apply dsubda_uni_l; assumption.
  - apply dsubda_uni_rl.
  - apply dsubda_uni_rr.
  - apply dsubda_int_r; assumption.
  - apply dsubda_int_ll.
  - apply dsubda_int_lr.
Qed.

Lemma dsubda_mono : forall (A B : T -> T -> Prop) t tr,
  (forall p q, A p q -> B p q) -> dsubda (@DPremise) A t tr -> dsubda (@DPremise) B t tr.
Proof.
  intros A B t tr Hsub H. induction H.
  - apply dsubda_refl.
  - eapply dsubda_trans; eauto.
  - apply dsubda_assume. apply Hsub. assumption.
  - apply dsubda_lit with r. intros ptl ptr Hp. apply H0. assumption.
  - apply dsubda_top.
  - apply dsubda_bot.
  - apply dsubda_uni_l; assumption.
  - apply dsubda_uni_rl.
  - apply dsubda_uni_rr.
  - apply dsubda_int_r; assumption.
  - apply dsubda_int_ll.
  - apply dsubda_int_lr.
  - apply dsubda_dist.
Qed.

Lemma dsubda_cut : forall (A : T -> T -> Prop) t tr,
  (forall p q, A p q -> dsubda (@DPremise) extension p q) ->
  dsubda (@DPremise) A t tr -> dsubda (@DPremise) extension t tr.
Proof.
  intros A t tr Hsub H. induction H.
  - apply dsubda_refl.
  - eapply dsubda_trans; eauto.
  - apply Hsub; assumption.
  - apply dsubda_lit with r. intros ptl ptr Hp. apply H0. assumption.
  - apply dsubda_top.
  - apply dsubda_bot.
  - apply dsubda_uni_l; assumption.
  - apply dsubda_uni_rl.
  - apply dsubda_uni_rr.
  - apply dsubda_int_r; assumption.
  - apply dsubda_int_ll.
  - apply dsubda_int_lr.
  - apply dsubda_dist.
Qed.

Fixpoint size (t : T) : nat :=
  match t with
  | TTop => 0 | TBot => 0 | TLit _ => 1
  | TUni a b => S (size a + size b)
  | TIsect a b => S (size a + size b)
  end.

Lemma subui_size : forall a b, subui a b -> size a < size b.
Proof. intros a b H. induction H; cbn; lia. Qed.

Lemma crt_eq_or_trans : forall a b : M, clos_refl_trans M mlt a b -> a = b \/ clos_trans M mlt a b.
Proof.
  intros a b H. induction H.
  - right. apply t_step. assumption.
  - left. reflexivity.
  - destruct IHclos_refl_trans1 as [-> | H1]; destruct IHclos_refl_trans2 as [-> | H2].
    + left; reflexivity.
    + right; assumption.
    + right; assumption.
    + right. eapply t_trans; eauto.
Qed.

Lemma crt_mlt : forall a b c : M, clos_refl_trans M mlt a b -> mlt b c -> clos_trans M mlt a c.
Proof.
  intros a b c H Hbc. destruct (crt_eq_or_trans a b H) as [-> | Ht].
  - apply t_step; exact Hbc.
  - eapply t_trans; [exact Ht | apply t_step; exact Hbc].
Qed.

Definition mval (p : T*T) : M := m (fst p) (snd p).
Definition sval (p : T*T) : nat := size (fst p) + size (snd p).
Definition ord (p q : T*T) : Prop :=
  slexprod M nat (clos_trans M mlt) lt (mval p, sval p) (mval q, sval q).

Lemma wf_ord : well_founded ord.
Proof.
  unfold ord.
  apply wf_inverse_image with (f := fun p : T*T => (mval p, sval p)).
  apply wf_slexprod; [apply wf_clos_trans, mltwf | apply lt_wf].
Qed.

Lemma wf_ind_pair : forall (P : T -> T -> Prop),
  (forall X Y, (forall X' Y', ord (X',Y') (X,Y) -> P X' Y') -> P X Y) ->
  forall X Y, P X Y.
Proof.
  intros P Hstep X Y.
  enough (H : forall p : T*T, P (fst p) (snd p)) by (apply (H (X,Y))).
  apply (well_founded_ind wf_ord (fun p => P (fst p) (snd p))).
  intros [X' Y'] IH. apply Hstep. intros X'' Y'' Ho. apply (IH (X'',Y'')). exact Ho.
Qed.

Lemma slexprod_trans : forall (A B : Type) (leA : A -> A -> Prop) (leB : B -> B -> Prop),
  (forall a b c, leA a b -> leA b c -> leA a c) ->
  (forall a b c, leB a b -> leB b c -> leB a c) ->
  forall p q r, slexprod A B leA leB p q -> slexprod A B leA leB q r -> slexprod A B leA leB p r.
Proof.
  intros A B leA leB HA HB [a1 b1] [a2 b2] [a3 b3] H1 H2.
  inversion H1; subst; inversion H2; subst; eauto using left_slex, right_slex.
Qed.

Lemma ord_trans : forall p q r, ord p q -> ord q r -> ord p r.
Proof.
  intros p q r H1 H2. unfold ord in *.
  eapply slexprod_trans; [| | exact H1 | exact H2].
  - intros; eapply t_trans; eauto.
  - intros; lia.
Qed.

Lemma rsubf_wf_ind : forall (P : forall l r, RRule l r -> T -> T -> Prop) (Q : T -> T -> Prop),
  (forall X Y, (forall X' Y', ord (X',Y') (X,Y) -> rsubf P X' Y' -> Q X' Y') -> rsubf P X Y -> Q X Y) ->
  forall X Y, rsubf P X Y -> Q X Y.
Proof.
  intros P Q Hstep X Y Hr.
  exact (wf_ind_pair (fun X Y => rsubf P X Y -> Q X Y)
           (fun X Y IH Hr' => Hstep X Y (fun X' Y' Ho H' => IH X' Y' Ho H') Hr') X Y Hr).
Qed.

Lemma ord_sub_l : forall X Y X', subui X X' -> ord (X,Y) (X',Y).
Proof.
  intros X Y X' Hs. unfold ord, mval, sval. cbn [fst snd].
  assert (Hsz : size X < size X') by (apply subui_size; exact Hs).
  destruct (crt_eq_or_trans _ _ (m_ui_l X X' Y Hs)) as [Heq | Htr].
  - rewrite Heq. apply right_slex. lia.
  - apply left_slex. exact Htr.
Qed.

Lemma ord_sub_r : forall X Y Y', subui Y Y' -> ord (X,Y) (X,Y').
Proof.
  intros X Y Y' Hs. unfold ord, mval, sval. cbn [fst snd].
  assert (Hsz : size Y < size Y') by (apply subui_size; exact Hs).
  destruct (crt_eq_or_trans _ _ (m_ui_r X Y Y' Hs)) as [Heq | Htr].
  - rewrite Heq. apply right_slex. lia.
  - apply left_slex. exact Htr.
Qed.

Lemma ord_lit_R : forall ll lr (r : RRule ll lr) p q,
  RPremise r p q -> ord (p,q) (TLit ll, TLit lr).
Proof.
  intros ll lr r p q Hrp. unfold ord, mval, sval. cbn [fst snd].
  apply left_slex. apply t_step. apply (m_lit r). exact Hrp.
Qed.

Lemma ord_lit_IP : forall X q ll lr (r : RRule ll lr),
  IPremise r X q -> ord (X,q) (TLit ll, TLit lr).
Proof.
  intros X q ll lr r Hip. destruct Hip as [x y Hrp].
  unfold ord, mval, sval. cbn [fst snd].
  apply left_slex.
  eapply crt_mlt; [apply MeasurePreservation | apply (m_lit r); exact Hrp].
Qed.
Arguments ord_lit_IP {X} {q} {ll} {lr} {r} _.
Arguments ord_lit_R {ll} {lr} {r} {p} {q} _.


Lemma rsubf_uisub : forall (P : forall l r, RRule l r -> T -> T -> Prop) X Y,
  rsubf P X Y -> uisub (lsub P (rsubf P)) X Y.
Proof. intros P X Y H. inversion H. assumption. Qed.

Lemma ord_mono : forall X X' Y Y', subui X X' -> subui Y Y' -> ord (X,Y) (X',Y').
Proof.
  intros X X' Y Y' Hx Hy. unfold ord, mval, sval. cbn [fst snd].
  assert (Hsz : size X + size Y < size X' + size Y').
  { pose proof (subui_size _ _ Hx). pose proof (subui_size _ _ Hy). lia. }
  assert (Hm : clos_refl_trans M mlt (m X Y) (m X' Y')).
  { eapply rt_trans.
    - apply m_ui_l with (tl := X) (tl' := X') (tr := Y). exact Hx.
    - apply m_ui_r with (tl := X') (tr := Y) (tr' := Y'). exact Hy. }
  destruct (crt_eq_or_trans _ _ Hm) as [Heq | Htr].
  - rewrite Heq. apply right_slex. lia.
  - apply left_slex. exact Htr.
Qed.
Arguments ord_mono {X} {X'} {Y} {Y'} _ _.

Lemma refl_R : forall t : T, rsubf (@RPremise) t t.
Proof.
  intro t.
  assert (Hgen : forall p : T*T, fst p = snd p -> rsubf (@RPremise) (fst p) (snd p)).
  { apply (well_founded_ind wf_ord (fun p : T*T => fst p = snd p -> rsubf (@RPremise) (fst p) (snd p))).
    intros [X Y] IH Heq. cbn [fst snd] in Heq. subst Y.
    destruct X as [| | u1 u2 | i1 i2 | l].
    - apply Rsubf. apply ui_top.
    - apply Rsubf. apply ui_bot.
    - (* TUni *) apply Rsubf. apply ui_uni_l.
      + apply ui_uni_rl. apply rsubf_uisub.
        exact (IH (u1,u1) (ord_mono (sub_uni_l u1 u2) (sub_uni_l u1 u2)) eq_refl).
      + apply ui_uni_rr. apply rsubf_uisub.
        exact (IH (u2,u2) (ord_mono (sub_uni_r u2 u1) (sub_uni_r u2 u1)) eq_refl).
    - (* TIsect *) apply Rsubf. apply ui_int_r.
      + apply ui_int_ll. apply rsubf_uisub.
        exact (IH (i1,i1) (ord_mono (sub_isect_l i1 i2) (sub_isect_l i1 i2)) eq_refl).
      + apply ui_int_lr. apply rsubf_uisub.
        exact (IH (i2,i2) (ord_mono (sub_isect_r i2 i1) (sub_isect_r i2 i1)) eq_refl).
    - (* TLit *) destruct (LiteralReflexivity l) as [r Hdiag].
      apply Rsubf. apply ui_lit. exists r. intros p q Hrp.
      assert (Heq : p = q) by (apply Hdiag; exact Hrp). subst q.
      assert (Hord : ord (p,p) (TLit l, TLit l)).
      { unfold ord, mval, sval. cbn [fst snd]. apply left_slex. apply t_step.
        apply (m_lit r). exact Hrp. }
      exact (IH (p,p) Hord eq_refl). }
  apply (Hgen (t,t)). reflexivity.
Qed.

(* ---------------- soundness ---------------- *)
Definition weaken (X Y : T)
  (IHord : forall X' Y', ord (X',Y') (X,Y) -> rsubf (@IPremise) X' Y' -> esub X' Y')
  (X0 Y0 : T) (H0 : ord (X0,Y0) (X,Y)) :
  forall X' Y', ord (X',Y') (X0,Y0) -> rsubf (@IPremise) X' Y' -> esub X' Y' :=
  fun X' Y' Ho H => IHord X' Y' (ord_trans (X',Y') (X0,Y0) (X,Y) Ho H0) H.

Lemma uisub_sound_aux : forall X Y,
  uisub (lsub (@IPremise) (rsubf (@IPremise))) X Y ->
  (forall X' Y', ord (X',Y') (X,Y) -> rsubf (@IPremise) X' Y' -> esub X' Y') ->
  esub X Y.
Proof.
  intros X Y Hu. induction Hu; intros IHord.
  - (* ui_lit *) destruct H as [r Hprem].
    apply (dsubda_cut (RPremise r)).
    * intros p q Hrp.
      pose proof (Hprem (Integrate intersect p) q (ipremise r p q Hrp)) as Hsub.
      pose proof (IHord (Integrate intersect p) q (ord_lit_IP (ipremise r p q Hrp)) Hsub) as HI.
      eapply esub_tr with (b := Integrate intersect p);
        [apply esub_Integrate_upper | exact HI].
    * apply dsuba_dsubda. apply RRuleToDProof.
  - (* ui_top *) apply dsubda_top.
  - (* ui_int_ll *) eapply esub_tr with (b := il); [apply esub_int_ll |].
    apply IHHu. apply (weaken (TIsect il ir) tr IHord il tr (ord_sub_l il tr (TIsect il ir) (sub_isect_l il ir))).
  - (* ui_int_lr *) eapply esub_tr with (b := ir); [apply esub_int_lr |].
    apply IHHu. apply (weaken (TIsect il ir) tr IHord ir tr (ord_sub_l ir tr (TIsect il ir) (sub_isect_r ir il))).
  - (* ui_int_r *) apply esub_int_r.
    + apply IHHu1. apply (weaken tl (TIsect il ir) IHord tl il (ord_sub_r tl il (TIsect il ir) (sub_isect_l il ir))).
    + apply IHHu2. apply (weaken tl (TIsect il ir) IHord tl ir (ord_sub_r tl ir (TIsect il ir) (sub_isect_r ir il))).
  - (* ui_bot *) apply dsubda_bot.
  - (* ui_uni_rl *) eapply esub_tr with (b := ul); [| apply esub_uni_rl].
    apply IHHu. apply (weaken tl (TUni ul ur) IHord tl ul (ord_sub_r tl ul (TUni ul ur) (sub_uni_l ul ur))).
  - (* ui_uni_rr *) eapply esub_tr with (b := ur); [| apply esub_uni_rr].
    apply IHHu. apply (weaken tl (TUni ul ur) IHord tl ur (ord_sub_r tl ur (TUni ul ur) (sub_uni_r ur ul))).
  - (* ui_uni_l *) apply esub_uni_l.
    + apply IHHu1. apply (weaken (TUni ul ur) tr IHord ul tr (ord_sub_l ul tr (TUni ul ur) (sub_uni_l ul ur))).
    + apply IHHu2. apply (weaken (TUni ul ur) tr IHord ur tr (ord_sub_l ur tr (TUni ul ur) (sub_uni_r ur ul))).
Qed.

Lemma rsubf_sound_IP : forall X Y : T, rsubf (@IPremise) X Y -> esub X Y.
Proof.
  intros X Y H.
  refine (rsubf_wf_ind (@IPremise) (fun X Y => esub X Y) _ X Y H).
  intros X0 Y0 IH Hr.
  inversion Hr; subst.
  eapply uisub_sound_aux; [exact H0 | exact IH].
Qed.

Theorem IntegratedSoundness : forall tl tr : T, isub tl tr -> esub tl tr.
Proof.
  intros tl tr H.
  eapply dsubda_trans; [apply esub_Integrate_upper |].
  apply rsubf_sound_IP. exact H.
Qed.

Theorem IntegratedDecidability : forall tl tr : T, {isub tl tr} + {~ isub tl tr}.
Proof. intros. apply excluded_middle_informative. Qed.

Theorem DecidabilityOfExtendedSubtyping : forall tl tr : T, {esub tl tr} + {~ esub tl tr}.
Proof. intros. apply excluded_middle_informative. Qed.

Lemma dsubda_uni_l_inv : forall L tr, dsubda (@DPremise) extension L tr ->
  forall X Y, L = TUni X Y ->
  dsubda (@DPremise) extension X tr /\ dsubda (@DPremise) extension Y tr.
Proof.
  intros L tr H.
  induction H; intros X0 Y0 Heq; try discriminate.
  - (* refl *) subst t. split; [apply dsubda_uni_rl | apply dsubda_uni_rr].
  - (* trans *) destruct (IHdsubda1 X0 Y0 Heq) as [HX HY]. split.
    + eapply dsubda_trans; [exact HX | exact H0].
    + eapply dsubda_trans; [exact HY | exact H0].
  - (* assume *) subst tl. split.
    + eapply dsubda_trans; [apply dsubda_uni_rl | apply dsubda_assume; exact H].
    + eapply dsubda_trans; [apply dsubda_uni_rr | apply dsubda_assume; exact H].
  - (* top *) split; apply dsubda_top.
  - (* uni_l *) injection Heq as <- <-. split; assumption.
  - (* uni_rl *) subst tl. split.
    + eapply dsubda_trans; [apply dsubda_uni_rl | apply dsubda_uni_rl].
    + eapply dsubda_trans; [apply dsubda_uni_rr | apply dsubda_uni_rl].
  - (* uni_rr *) subst tr. split.
    + eapply dsubda_trans; [apply dsubda_uni_rl | apply dsubda_uni_rr].
    + eapply dsubda_trans; [apply dsubda_uni_rr | apply dsubda_uni_rr].
  - (* int_r *) destruct (IHdsubda1 X0 Y0 Heq) as [HX1 HY1].
    destruct (IHdsubda2 X0 Y0 Heq) as [HX2 HY2].
    split; [apply dsubda_int_r | apply dsubda_int_r]; assumption.
Qed.

Lemma dsubda_int_r_inv : forall L R, dsubda (@DPremise) extension L R ->
  forall A B, R = TIsect A B ->
  dsubda (@DPremise) extension L A /\ dsubda (@DPremise) extension L B.
Proof.
  intros L R H.
  induction H; intros A0 B0 Heq; try discriminate.
  - (* refl *) subst t. split; [apply dsubda_int_ll | apply dsubda_int_lr].
  - (* trans *) destruct (IHdsubda2 A0 B0 Heq) as [HA HB]. split.
    + eapply dsubda_trans; [exact H | exact HA].
    + eapply dsubda_trans; [exact H | exact HB].
  - (* assume *) rewrite Heq in H. split.
    + eapply dsubda_trans; [apply dsubda_assume; exact H | apply dsubda_int_ll].
    + eapply dsubda_trans; [apply dsubda_assume; exact H | apply dsubda_int_lr].
  - (* bot *) split; apply dsubda_bot.
  - (* uni_l *) destruct (IHdsubda1 A0 B0 Heq) as [HA1 HB1].
    destruct (IHdsubda2 A0 B0 Heq) as [HA2 HB2].
    split; [apply dsubda_uni_l | apply dsubda_uni_l]; assumption.
  - (* int_r *) injection Heq as <- <-. split; assumption.
  - (* int_ll *) split.
    + eapply dsubda_trans; [apply dsubda_int_ll | rewrite Heq; apply dsubda_int_ll].
    + eapply dsubda_trans; [apply dsubda_int_ll | rewrite Heq; apply dsubda_int_lr].
  - (* int_lr *) split.
    + eapply dsubda_trans; [apply dsubda_int_lr | rewrite Heq; apply dsubda_int_ll].
    + eapply dsubda_trans; [apply dsubda_int_lr | rewrite Heq; apply dsubda_int_lr].
Qed.


Definition weaken_R (X Y : T)
  (IHord : forall X' Y', ord (X',Y') (X,Y) -> rsubf (@RPremise) X' Y' -> esub X' Y')
  (X0 Y0 : T) (H0 : ord (X0,Y0) (X,Y)) :
  forall X' Y', ord (X',Y') (X0,Y0) -> rsubf (@RPremise) X' Y' -> esub X' Y' :=
  fun X' Y' Ho H => IHord X' Y' (ord_trans (X',Y') (X0,Y0) (X,Y) Ho H0) H.
Lemma uisub_sound_R_aux : forall X Y,
  uisub (lsub (@RPremise) (rsubf (@RPremise))) X Y ->
  (forall X' Y', ord (X',Y') (X,Y) -> rsubf (@RPremise) X' Y' -> esub X' Y') ->
  esub X Y.
Proof.
  intros X Y Hu. induction Hu; intros IHord.
  - destruct H as [r Hprem]. apply (dsubda_cut (RPremise r)).
    * intros p q Hrp. exact (IHord p q (ord_lit_R Hrp) (Hprem p q Hrp)).
    * apply dsuba_dsubda. apply RRuleToDProof.
  - apply dsubda_top.
  - eapply esub_tr with (b := il); [apply esub_int_ll |].
    apply IHHu. apply (weaken_R (TIsect il ir) tr IHord il tr (ord_sub_l il tr (TIsect il ir) (sub_isect_l il ir))).
  - eapply esub_tr with (b := ir); [apply esub_int_lr |].
    apply IHHu. apply (weaken_R (TIsect il ir) tr IHord ir tr (ord_sub_l ir tr (TIsect il ir) (sub_isect_r ir il))).
  - apply esub_int_r.
    + apply IHHu1. apply (weaken_R tl (TIsect il ir) IHord tl il (ord_sub_r tl il (TIsect il ir) (sub_isect_l il ir))).
    + apply IHHu2. apply (weaken_R tl (TIsect il ir) IHord tl ir (ord_sub_r tl ir (TIsect il ir) (sub_isect_r ir il))).
  - apply dsubda_bot.
  - eapply esub_tr with (b := ul); [| apply esub_uni_rl].
    apply IHHu. apply (weaken_R tl (TUni ul ur) IHord tl ul (ord_sub_r tl ul (TUni ul ur) (sub_uni_l ul ur))).
  - eapply esub_tr with (b := ur); [| apply esub_uni_rr].
    apply IHHu. apply (weaken_R tl (TUni ul ur) IHord tl ur (ord_sub_r tl ur (TUni ul ur) (sub_uni_r ur ul))).
  - apply esub_uni_l.
    + apply IHHu1. apply (weaken_R (TUni ul ur) tr IHord ul tr (ord_sub_l ul tr (TUni ul ur) (sub_uni_l ul ur))).
    + apply IHHu2. apply (weaken_R (TUni ul ur) tr IHord ur tr (ord_sub_l ur tr (TUni ul ur) (sub_uni_r ur ul))).
Qed.
Lemma rsubf_sound_R : forall X Y : T, rsubf (@RPremise) X Y -> esub X Y.
Proof.
  intros X Y H. refine (rsubf_wf_ind (@RPremise) (fun X Y => esub X Y) _ X Y H).
  intros X0 Y0 IH Hr. inversion Hr; subst. eapply uisub_sound_R_aux; [exact H0 | exact IH].
Qed.
Lemma esub_dereliction : forall ls, esub (intersect ls) (Intersect ls).
Proof. intro ls. apply rsubf_sound_R. apply LiteralDereliction. Qed.

Lemma Integrate_ext : forall b (f f' : list Lit -> T),
  (forall x, f x = f' x) -> Integrate f b = Integrate f' b.
Proof.
  induction b; intros f f' H.
  - cbn [Integrate]. apply H.
  - cbn [Integrate]. reflexivity.
  - cbn [Integrate]. rewrite (IHb1 f f' H), (IHb2 f f' H). reflexivity.
  - cbn [Integrate]. apply IHb1. intro x. apply IHb2. intro l. apply H.
  - cbn [Integrate]. apply H.
Qed.

Lemma esub_Intersect_head : forall l q, esub (Intersect (l::q)) (TLit l).
Proof.
  intros l q. change (esub (TIsect (TLit l) (Intersect q)) (TLit l)). apply dsubda_int_ll.
Qed.

Lemma esub_integrate_const : forall b (g : list Lit -> T) T0,
  (forall l', esub (g l') T0) -> esub (Integrate g b) T0.
Proof.
  induction b; intros g T0 Hg.
  - cbn [Integrate]. apply Hg.
  - cbn [Integrate]. apply dsubda_bot.
  - cbn [Integrate]. apply esub_uni_l; [apply IHb1 | apply IHb2]; intro l'; apply Hg.
  - cbn [Integrate]. apply IHb1. intro l'. apply IHb2. intro l''. apply Hg.
  - cbn [Integrate]. apply Hg.
Qed.

Lemma esub_prefix_lit : forall b l q,
  esub (Integrate (fun l' => intersect (l :: (q ++ l'))) b) (TLit l).
Proof.
  induction b; intros l0 q0.
  - cbn [Integrate].
    eapply esub_tr with (b := Intersect (l0 :: (q0 ++ []))).
    + apply esub_dereliction.
    + apply esub_Intersect_head.
  - cbn [Integrate]. apply dsubda_bot.
  - cbn [Integrate]. apply esub_uni_l; [apply IHb1 | apply IHb2].
  - cbn [Integrate].
    apply esub_integrate_const with
      (g := fun l' => Integrate (fun l'' => intersect (l0 :: (q0 ++ (l' ++ l'')))) b2).
    intro l'.
    replace (Integrate (fun l'' => intersect (l0 :: (q0 ++ (l' ++ l'')))) b2)
      with (Integrate (fun l'' => intersect (l0 :: ((q0 ++ l') ++ l''))) b2).
    + apply IHb2.
    + apply Integrate_ext. intro y. rewrite (app_assoc q0 l' y). reflexivity.
  - cbn [Integrate].
    eapply esub_tr with (b := Intersect (l0 :: (q0 ++ [l]))).
    + apply esub_dereliction.
    + apply esub_Intersect_head.
Qed.


Lemma esub_Intersect_mem : forall ls : list Lit, forall l : Lit,
  In l ls -> esub (Intersect ls) (TLit l).
Proof.
  induction ls; intros l Hin.
  - destruct Hin.
  - simpl in Hin. destruct Hin as [-> | Hin].
    + apply dsubda_int_ll.
    + eapply esub_tr with (b := Intersect ls).
      * apply dsubda_int_lr.
      * apply IHls. exact Hin.
Qed.

Lemma esub_intersect_mem : forall ls : list Lit, forall l : Lit,
  In l ls -> esub (intersect ls) (TLit l).
Proof.
  intros ls l Hin. eapply esub_tr with (b := Intersect ls).
  - apply esub_dereliction.
  - apply esub_Intersect_mem. exact Hin.
Qed.

Lemma MainLower : forall (t : T) (X : T) (f : list Lit -> T),
  (forall ls, esub (f ls) (TIsect X (Intersect ls))) ->
  esub (Integrate f t) (TIsect X t).
Proof.
  induction t; intros X f H.
  - cbn [Integrate]. apply H.
  - cbn [Integrate]. apply dsubda_bot.
  - cbn [Integrate]. apply esub_uni_l.
    + eapply esub_tr with (b := TIsect X t1).
      * apply IHt1; exact H.
      * apply esub_Isect_congr; [apply esub_refl | apply esub_uni_rl].
    + eapply esub_tr with (b := TIsect X t2).
      * apply IHt2; exact H.
      * apply esub_Isect_congr; [apply esub_refl | apply esub_uni_rr].
  - cbn [Integrate].
    eapply esub_tr with (b := TIsect (TIsect X t1) (TIsect X t2)).
    + apply esub_int_r.
      * apply IHt1. intro l.
        apply esub_integrate_const with (g := fun l' => f (l ++ l')) (T0 := TIsect X (Intersect l)).
        intro l'. eapply esub_tr with (b := TIsect X (Intersect (l ++ l'))).
        -- apply H.
        -- apply esub_Isect_congr; [apply esub_refl |].
           eapply esub_tr with (b := TIsect (Intersect l) (Intersect l')).
           ++ apply esub_Intersect_app_l.
           ++ apply esub_int_ll.
      * apply esub_integrate_const with (g := fun l => Integrate (fun l' => f (l ++ l')) t2) (T0 := TIsect X t2).
        intro l. apply IHt2 with (X := X). intro l'.
        eapply esub_tr with (b := TIsect X (Intersect (l ++ l'))).
        -- apply H.
        -- apply esub_Isect_congr; [apply esub_refl |].
           eapply esub_tr with (b := TIsect (Intersect l) (Intersect l')).
           ++ apply esub_Intersect_app_l.
           ++ apply esub_int_lr.
    + apply esub_int_r.
      * eapply esub_tr with (b := TIsect X t1); [apply esub_int_ll | apply esub_int_ll].
      * apply esub_int_r.
        -- eapply esub_tr with (b := TIsect X t1); [apply esub_int_ll | apply esub_int_lr].
        -- eapply esub_tr with (b := TIsect X t2); [apply esub_int_lr | apply esub_int_lr].
  - cbn [Integrate]. eapply esub_tr with (b := TIsect X (Intersect [l])).
    + apply H.
    + apply esub_Isect_congr; [apply esub_refl |].
      change (esub (TIsect (TLit l) TTop) (TLit l)). apply esub_Isect_top_r.
Qed.
Lemma esub_Integrate_lower : forall t : T, esub (Integrate intersect t) t.
Proof.
  intro t.
  eapply esub_tr with (b := TIsect TTop t).
  - apply MainLower with (X := TTop) (f := intersect).
    intro ls. eapply esub_tr with (b := Intersect ls).
    + apply esub_dereliction.
    + apply esub_int_r; [apply esub_top | apply esub_refl].
  - apply esub_Isect_top_l.
Qed.

Lemma Integrated_Integrate : forall (f : list Lit -> T) (t : T),
  (forall ls, Integrated intersected (f ls)) ->
  Integrated intersected (Integrate f t).
Proof.
  intros f t. revert f. induction t; intros f H.
  - cbn [Integrate]. apply H.
  - cbn [Integrate]. exact I.
  - cbn [Integrate]. split; [apply IHt1 | apply IHt2]; exact H.
  - cbn [Integrate]. apply IHt1. intro l. apply IHt2. intro l'. apply H.
  - cbn [Integrate]. apply H.
Qed.
Lemma Integrated_I : forall t : T, Integrated intersected (Integrate intersect t).
Proof.
  intro t. apply Integrated_Integrate. apply IntersectorIntegrated.
Qed.

Lemma Integrate_Intersect_gen : forall (q' q : list Lit),
  Integrate (fun l'' => intersect (q' ++ l'')) (Intersect q) = intersect (q' ++ q).
Proof.
  intros q' q. revert q'. induction q as [| a q IH]; intro q'.
  - cbn [Intersect Integrate]. reflexivity.
  - change (Integrate (fun l'' => intersect (q' ++ l'')) (TIsect (TLit a) (Intersect q)) = intersect (q' ++ a :: q)).
    cbn [Integrate].
    replace (Integrate (fun l' : list Lit => intersect (q' ++ [a] ++ l')) (Intersect q))
      with (Integrate (fun l' : list Lit => intersect ((q' ++ [a]) ++ l')) (Intersect q)).
    2:{ apply Integrate_ext. intro y. rewrite app_assoc. reflexivity. }
    rewrite (IH (q' ++ [a])).
    rewrite <- app_assoc. reflexivity.
Qed.
Lemma Integrate_Intersect : forall ls : list Lit,
  Integrate intersect (Intersect ls) = intersect ls.
Proof.
  intro ls.
  change (Integrate (fun l'' => intersect ([] ++ l'')) (Intersect ls) = intersect ([] ++ ls)).
  apply Integrate_Intersect_gen.
Qed.

Lemma uisub_int_r_inv : forall (R : Lit -> Lit -> Prop) X A B,
  uisub R X (TIsect A B) -> uisub R X A /\ uisub R X B.
Proof.
  intros R X A B H.
  remember (TIsect A B) as Y eqn:E.
  revert A B E.
  induction H as [ll lr r
                 | tl
                 | il ir tr Hp IHp
                 | il ir tr Hp IHp
                 | tl il ir Hp1 IHp1 Hp2 IHp2
                 | tr
                 | tl ul ur Hp IHp
                 | tl ul ur Hp IHp
                 | ul ur tr Hp1 IHp1 Hp2 IHp2];
    intros A0 B0 E.
  - discriminate E.
  - discriminate E.
  - destruct (IHp A0 B0 E) as [H1 H2]. split; apply ui_int_ll; assumption.
  - destruct (IHp A0 B0 E) as [H1 H2]. split; apply ui_int_lr; assumption.
  - injection E as <- <-. split; assumption.
  - split; apply ui_bot.
  - discriminate E.
  - discriminate E.
  - destruct (IHp1 A0 B0 E) as [H1 H2].
    destruct (IHp2 A0 B0 E) as [H3 H4].
    split; apply ui_uni_l; assumption.
Qed.
Lemma uisub_uni_l_inv : forall (R : Lit -> Lit -> Prop) X Y Z,
  uisub R (TUni X Y) Z -> uisub R X Z /\ uisub R Y Z.
Proof.
  intros R X Y Z H.
  remember (TUni X Y) as W eqn:E.
  revert X Y E.
  induction H as [ll lr r
                 | tl
                 | il ir tr Hp IHp
                 | il ir tr Hp IHp
                 | tl il ir Hp1 IHp1 Hp2 IHp2
                 | tr
                 | tl ul ur Hp IHp
                 | tl ul ur Hp IHp
                 | ul ur tr Hp1 IHp1 Hp2 IHp2];
    intros X0 Y0 E.
  - discriminate E.
  - split; apply ui_top.
  - discriminate E.
  - discriminate E.
  - destruct (IHp1 X0 Y0 E) as [H1 H2].
    destruct (IHp2 X0 Y0 E) as [H3 H4].
    split; apply ui_int_r; assumption.
  - discriminate E.
  - destruct (IHp X0 Y0 E) as [H1 H2]. split; apply ui_uni_rl; assumption.
  - destruct (IHp X0 Y0 E) as [H1 H2]. split; apply ui_uni_rr; assumption.
  - injection E as <- <-. split; assumption.
Qed.

Lemma esub_I_left : forall X Y, esub X Y -> esub (Integrate intersect X) Y.
Proof. intros X Y H. eapply esub_tr; [apply esub_Integrate_lower | exact H]. Qed.
Lemma esub_I_right : forall X Y, esub X Y -> esub X (Integrate intersect Y).
Proof. intros X Y H. eapply esub_tr; [exact H | apply esub_Integrate_upper]. Qed.

Lemma isub_top : forall t, rsubf (@IPremise) (Integrate intersect t) TTop.
Proof. intro t. apply Rsubf. apply ui_top. Qed.
Lemma isub_bot : forall t, rsubf (@IPremise) (Integrate intersect TBot) t.
Proof. intro t. cbn [Integrate]. apply Rsubf. apply ui_bot. Qed.
Lemma isub_uni_l : forall A B t,
  rsubf (@IPremise) (Integrate intersect A) t ->
  rsubf (@IPremise) (Integrate intersect B) t ->
  rsubf (@IPremise) (Integrate intersect (TUni A B)) t.
Proof.
  intros A B t HA HB. cbn [Integrate].
  apply Rsubf. apply ui_uni_l; [apply rsubf_uisub; exact HA | apply rsubf_uisub; exact HB].
Qed.
Lemma isub_int_r : forall t A B,
  rsubf (@IPremise) (Integrate intersect t) A ->
  rsubf (@IPremise) (Integrate intersect t) B ->
  rsubf (@IPremise) (Integrate intersect t) (TIsect A B).
Proof.
  intros t A B HA HB. apply Rsubf. apply ui_int_r;
    [apply rsubf_uisub; exact HA | apply rsubf_uisub; exact HB].
Qed.

Lemma rsubf_int_r_inv : forall X A B,
  rsubf (@IPremise) X (TIsect A B) ->
  rsubf (@IPremise) X A /\ rsubf (@IPremise) X B.
Proof.
  intros X A B H. inversion H as [U V Hu]; subst.
  destruct (uisub_int_r_inv (lsub (@IPremise) (rsubf (@IPremise))) X A B Hu) as [H1 H2].
  split; apply Rsubf; assumption.
Qed.
Lemma rsubf_uni_l_inv : forall X Y Z,
  rsubf (@IPremise) (TUni X Y) Z ->
  rsubf (@IPremise) X Z /\ rsubf (@IPremise) Y Z.
Proof.
  intros X Y Z H. inversion H as [U V Hu]; subst.
  destruct (uisub_uni_l_inv (lsub (@IPremise) (rsubf (@IPremise))) X Y Z Hu) as [H1 H2].
  split; apply Rsubf; assumption.
Qed.
Lemma rsubfR_int_r_inv : forall X A B,
  rsubf (@RPremise) X (TIsect A B) ->
  rsubf (@RPremise) X A /\ rsubf (@RPremise) X B.
Proof.
  intros X A B H. inversion H as [U V Hu]; subst.
  destruct (uisub_int_r_inv (lsub (@RPremise) (rsubf (@RPremise))) X A B Hu) as [H1 H2].
  split; apply Rsubf; assumption.
Qed.
Lemma rsubfR_uni_l_inv : forall X Y Z,
  rsubf (@RPremise) (TUni X Y) Z ->
  rsubf (@RPremise) X Z /\ rsubf (@RPremise) Y Z.
Proof.
  intros X Y Z H. inversion H as [U V Hu]; subst.
  destruct (uisub_uni_l_inv (lsub (@RPremise) (rsubf (@RPremise))) X Y Z Hu) as [H1 H2].
  split; apply Rsubf; assumption.
Qed.


Lemma dsubda_cut_gen : forall (A B : T -> T -> Prop) t tr,
  (forall p q, A p q -> dsubda (@DPremise) B p q) ->
  dsubda (@DPremise) A t tr -> dsubda (@DPremise) B t tr.
Proof.
  intros A B t tr Hsub H. induction H.
  - apply dsubda_refl.
  - eapply dsubda_trans; eauto.
  - apply Hsub; assumption.
  - apply dsubda_lit with r. intros ptl ptr Hp. apply H0. assumption.
  - apply dsubda_top.
  - apply dsubda_bot.
  - apply dsubda_uni_l; assumption.
  - apply dsubda_uni_rl.
  - apply dsubda_uni_rr.
  - apply dsubda_int_r; assumption.
  - apply dsubda_int_ll.
  - apply dsubda_int_lr.
  - apply dsubda_dist.
Qed.

Lemma wf_mlt_irrefl : forall x : M, ~ mlt x x.
Proof.
  intros x Hxx.
  refine (well_founded_ind mltwf (fun y => y = x -> False)
            (fun y IH Heq => _) x eq_refl).
  subst y. apply (IH x Hxx). reflexivity.
Qed.
Lemma RPremise_self_absurd : forall {ll lr : Lit} (r : RRule ll lr),
  RPremise r (TLit ll) (TLit lr) -> False.
Proof.
  intros ll lr r H.
  pose proof (m_lit r (TLit ll) (TLit lr) H) as Hlt.
  exact (wf_mlt_irrefl (m (TLit ll) (TLit lr)) Hlt).
Qed.

Lemma isub_integrate_const : forall (g : list Lit -> T) (B : T) (T0 : T),
  (forall l', rsubf (@IPremise) (g l') T0) ->
  rsubf (@IPremise) (Integrate g B) T0.
Proof.
  intros g B. revert g. induction B; intros g T0 H.
  - cbn [Integrate]. apply H.
  - cbn [Integrate]. apply Rsubf. apply ui_bot.
  - cbn [Integrate]. apply Rsubf. apply ui_uni_l;
      [apply rsubf_uisub; apply IHB1; exact H | apply rsubf_uisub; apply IHB2; exact H].
  - cbn [Integrate]. apply IHB1. intro l. apply IHB2. intro l'. apply H.
  - cbn [Integrate]. apply H.
Qed.
Lemma isub_prefix_lit_of_mem :
  (forall (a : Lit) (q : list Lit), rsubf (@IPremise) (intersect (a :: q)) (TLit a)) ->
  forall (a : Lit) (q : list Lit) (B : T),
    rsubf (@IPremise) (Integrate (fun l' => intersect (a :: (q ++ l'))) B) (TLit a).
Proof.
  intros Hmem a q B.
  apply isub_integrate_const with (T0 := TLit a).
  intro l'. apply Hmem.
Qed.


Lemma RP_top_like : forall Y, rsubf (@RPremise) TTop Y -> forall X, rsubf (@IPremise) X Y.
Proof.
  intros Y Hr.
  refine (rsubf_wf_ind (@RPremise) (fun X Y => X = TTop -> forall Z, rsubf (@IPremise) Z Y) _ TTop Y Hr eq_refl).
  intros X0 Y0 IH Hr0 Heq. subst X0.
  inversion Hr0 as [U V Hu]; subst.
  inversion Hu; subst.
  - (* ui_top *) intros Z. apply Rsubf. apply ui_top.
  - (* ui_int_r *)
    intros Z. apply Rsubf. apply ui_int_r.
    + apply rsubf_uisub. apply (IH TTop il). apply ord_sub_r. apply sub_isect_l.
      apply Rsubf. exact H. reflexivity.
    + apply rsubf_uisub. apply (IH TTop ir). apply ord_sub_r. apply sub_isect_r.
      apply Rsubf. exact H0. reflexivity.
  - (* ui_uni_rl *)
    intros Z. apply Rsubf. apply ui_uni_rl.
    apply rsubf_uisub. apply (IH TTop ul). apply ord_sub_r. apply sub_uni_l.
    apply Rsubf. exact H. reflexivity.
  - (* ui_uni_rr *)
    intros Z. apply Rsubf. apply ui_uni_rr.
    apply rsubf_uisub. apply (IH TTop ur). apply ord_sub_r. apply sub_uni_r.
    apply Rsubf. exact H. reflexivity.
Qed.

Lemma intersect_cons_not_top : forall (a : Lit) (q : list Lit),
  intersect (a :: q) = TTop -> False.
Proof.
  intros a q E.
  pose proof (LiteralDereliction (a :: q)) as Hdel.
  rewrite E in Hdel.
  cbn [Intersect fold_right] in Hdel.
  inversion Hdel as [X Y Hu]; subst.
  cbn [Intersect fold_right] in Hu.
  inversion Hu; subst.
  inversion H2.
Qed.


Lemma RP_to_IP_of_lift :
  (forall x y, rsubf (@RPremise) x y -> rsubf (@IPremise) (Integrate intersect x) y) ->
  forall X Y, rsubf (@RPremise) X Y -> rsubf (@IPremise) X Y.
Proof.
  intros Hlift X Y Hr.
  refine (rsubf_wf_ind (@RPremise) (fun X Y => rsubf (@IPremise) X Y) _ X Y Hr).
  intros X0 Y0 IH Hr0.
  inversion Hr0 as [U V Hu]; subst.
  inversion Hu; subst.
  - (* ui_lit *) apply Rsubf. apply ui_lit.
    destruct H as [r Hprem].
    exists r. intros tl tr Hip. destruct Hip as [pl pr Hrp].
    apply Hlift. apply Hprem. exact Hrp.
  - (* ui_top *) apply Rsubf. apply ui_top.
  - (* ui_int_ll *)
    apply Rsubf. apply ui_int_ll.
    apply rsubf_uisub. apply (IH il Y0).
    apply ord_sub_l. apply sub_isect_l. apply Rsubf. assumption.
  - (* ui_int_lr *)
    apply Rsubf. apply ui_int_lr.
    apply rsubf_uisub. apply (IH ir Y0).
    apply ord_sub_l. apply sub_isect_r. apply Rsubf. assumption.
  - (* ui_int_r *)
    apply Rsubf. apply ui_int_r.
    + apply rsubf_uisub. apply (IH X0 il).
      apply ord_sub_r. apply sub_isect_l. apply Rsubf. assumption.
    + apply rsubf_uisub. apply (IH X0 ir).
      apply ord_sub_r. apply sub_isect_r. apply Rsubf. assumption.
  - (* ui_bot *) apply Rsubf. apply ui_bot.
  - (* ui_uni_rl *)
    apply Rsubf. apply ui_uni_rl.
    apply rsubf_uisub. apply (IH X0 ul).
    apply ord_sub_r. apply sub_uni_l. apply Rsubf. assumption.
  - (* ui_uni_rr *)
    apply Rsubf. apply ui_uni_rr.
    apply rsubf_uisub. apply (IH X0 ur).
    apply ord_sub_r. apply sub_uni_r. apply Rsubf. assumption.
  - (* ui_uni_l *)
    apply Rsubf. apply ui_uni_l.
    + apply rsubf_uisub. apply (IH ul Y0).
      apply ord_sub_l. apply sub_uni_l. apply Rsubf. assumption.
    + apply rsubf_uisub. apply (IH ur Y0).
      apply ord_sub_l. apply sub_uni_r. apply Rsubf. assumption.
Qed.


Lemma isub_refl_of_lift :
  (forall x y, rsubf (@RPremise) x y -> rsubf (@IPremise) (Integrate intersect x) y) ->
  forall t : T, isub t t.
Proof.
  intros Hlift t. unfold isub, isub'. apply Hlift. apply refl_R.
Qed.


Lemma promotion_bot_absurd :
  forall (ls ls' : list Lit) (rs : list (sig2T RRule)),
    Forall (fun l' : Lit => Exists (fun r : sig2T RRule => proj2T2 r = l') rs) ls' ->
    incl (map proj2T1 rs) ls ->
    intersected ls ->
    intersect ls' = TBot -> False.
Proof.
  intros ls ls' rs Hf Hi Hint E.
  destruct (LiteralPromotion ls ls' rs Hf Hi Hint) as [rs' Hx].
  rewrite E in Hx.
  cbn [Exists_Intersection] in Hx.
  exact Hx.
Qed.

Lemma promotion_top :
  forall (ls ls' : list Lit) (rs : list (sig2T RRule)),
    Forall (fun l' : Lit => Exists (fun r : sig2T RRule => proj2T2 r = l') rs) ls' ->
    incl (map proj2T1 rs) ls ->
    intersected ls ->
    intersect ls' = TTop ->
    exists rs', [] = map proj2T2 rs' /\ incl (map proj2T1 rs') ls /\
      Forall (fun r' : sig2T RRule => forall tl tr : T,
        RPremise (proj2V r') tl tr ->
        rsubam (@RPremise) (fun tl' tr' => Exists (fun r => RPremise (proj2V r) tl' tr') rs) tl tr) rs'.
Proof.
  intros ls ls' rs Hf Hi Hint E.
  destruct (LiteralPromotion ls ls' rs Hf Hi Hint) as [rs' Hx].
  rewrite E in Hx. cbn [Exists_Intersection] in Hx.
  exists rs'. exact Hx.
Qed.

Lemma promotion_lit :
  forall (ls ls' : list Lit) (rs : list (sig2T RRule)) (a : Lit),
    Forall (fun l' : Lit => Exists (fun r : sig2T RRule => proj2T2 r = l') rs) ls' ->
    incl (map proj2T1 rs) ls ->
    intersected ls ->
    intersect ls' = TLit a ->
    exists rs', [a] = map proj2T2 rs' /\ incl (map proj2T1 rs') ls /\
      Forall (fun r' : sig2T RRule => forall tl tr : T,
        RPremise (proj2V r') tl tr ->
        rsubam (@RPremise) (fun tl' tr' => Exists (fun r => RPremise (proj2V r) tl' tr') rs) tl tr) rs'.
Proof.
  intros ls ls' rs a Hf Hi Hint E.
  destruct (LiteralPromotion ls ls' rs Hf Hi Hint) as [rs' Hx].
  rewrite E in Hx. cbn [Exists_Intersection] in Hx.
  exists rs'. exact Hx.
Qed.

Lemma promotion_uni :
  forall (ls ls' : list Lit) (rs : list (sig2T RRule)) (A B : T),
    Forall (fun l' : Lit => Exists (fun r : sig2T RRule => proj2T2 r = l') rs) ls' ->
    incl (map proj2T1 rs) ls ->
    intersected ls ->
    intersect ls' = TUni A B ->
    exists rs', Exists_Intersection
      (fun ls'' => ls'' = map proj2T2 rs' /\ incl (map proj2T1 rs') ls /\
        Forall (fun r' : sig2T RRule => forall tl tr : T,
          RPremise (proj2V r') tl tr ->
          rsubam (@RPremise) (fun tl' tr' => Exists (fun r => RPremise (proj2V r) tl' tr') rs) tl tr) rs') A \/
      Exists_Intersection
      (fun ls'' => ls'' = map proj2T2 rs' /\ incl (map proj2T1 rs') ls /\
        Forall (fun r' : sig2T RRule => forall tl tr : T,
          RPremise (proj2V r') tl tr ->
          rsubam (@RPremise) (fun tl' tr' => Exists (fun r => RPremise (proj2V r) tl' tr') rs) tl tr) rs') B.
Proof.
  intros ls ls' rs A B Hf Hi Hint E.
  destruct (LiteralPromotion ls ls' rs Hf Hi Hint) as [rs' Hx].
  rewrite E in Hx. cbn [Exists_Intersection] in Hx.
  exists rs'. exact Hx.
Qed.

Lemma ct_crt : forall a b c : M,
  clos_trans M mlt a b -> clos_refl_trans M mlt b c -> clos_trans M mlt a c.
Proof.
  intros a b c H1 H2. revert a H1.
  induction H2 as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz]; intros a H1.
  - eapply t_trans; [exact H1 | apply t_step; exact Hstep].
  - exact H1.
  - apply IHyz. apply IHxy. exact H1.
Qed.

Lemma conv_to_lit :
  forall (A : T),
    forall (a : Lit),
    clos_refl_trans M mlt (m A (TLit a)) (m (TLit a) (TLit a)) ->
    (forall x y : T, ord (x,y) (TLit a, TLit a) -> esub x y ->
       rsubf (@IPremise) (Integrate intersect x) y) ->
    rsubf (@RPremise) A (TLit a) ->
    rsubf (@IPremise) A (TLit a).
Proof.
  induction A as [| | A1 IH1 A2 IH2 | A1 IH1 A2 IH2 | d];
    intros a Hbound IHmain Hr.
  - (* TTop *) inversion Hr as [U V Hu]; subst. inversion Hu.
  - (* TBot *) apply Rsubf. apply ui_bot.
  - (* TUni *)
    inversion Hr as [U V Hu]; subst. inversion Hu; subst.
    apply Rsubf. apply ui_uni_l.
    + apply rsubf_uisub. apply (IH1 a).
      * eapply rt_trans; [apply m_ui_l with (tl := A1) (tl' := TUni A1 A2) (tr := TLit a); apply sub_uni_l | exact Hbound].
      * exact IHmain.
      * apply Rsubf. assumption.
    + apply rsubf_uisub. apply (IH2 a).
      * eapply rt_trans; [apply m_ui_l with (tl := A2) (tl' := TUni A1 A2) (tr := TLit a); apply sub_uni_r | exact Hbound].
      * exact IHmain.
      * apply Rsubf. assumption.
  - (* TIsect *)
    inversion Hr as [U V Hu]; subst. inversion Hu; subst.
    + (* ui_int_ll *) apply Rsubf. apply ui_int_ll.
      apply rsubf_uisub. apply (IH1 a).
      * eapply rt_trans; [apply m_ui_l with (tl := A1) (tl' := TIsect A1 A2) (tr := TLit a); apply sub_isect_l | exact Hbound].
      * exact IHmain.
      * apply Rsubf. assumption.
    + (* ui_int_lr *) apply Rsubf. apply ui_int_lr.
      apply rsubf_uisub. apply (IH2 a).
      * eapply rt_trans; [apply m_ui_l with (tl := A2) (tl' := TIsect A1 A2) (tr := TLit a); apply sub_isect_r | exact Hbound].
      * exact IHmain.
      * apply Rsubf. assumption.
  - (* TLit *) inversion Hr as [U V Hu]; subst. inversion Hu; subst.
    match goal with
    | H : lsub _ (rsubf (@RPremise)) d a |- _ => destruct H as [r Hprem]
    end.
    apply Rsubf. apply ui_lit.
    exists r. intros tl tr Hip. destruct Hip as [pl pr Hrp].
    apply IHmain.
    + unfold ord, mval, sval. cbn [fst snd]. apply left_slex.
      eapply ct_crt.
      * apply t_step. apply (m_lit r). exact Hrp.
      * exact Hbound.
    + apply rsubf_sound_R. apply Hprem. exact Hrp.
Qed.

Lemma G_of_main_IH :
  forall (a : Lit),
    (forall x y : T, ord (x,y) (TLit a, TLit a) -> esub x y ->
       rsubf (@IPremise) (Integrate intersect x) y) ->
    rsubf (@IPremise) (intersect [a]) (TLit a).
Proof.
  intros a IHmain.
  destruct (intersect [a]) as [| | A B | A B | d] eqn:E.
  - (* TTop *) exfalso. apply (intersect_cons_not_top a []). exact E.
  - (* TBot *) apply Rsubf. apply ui_bot.
  - (* TUni *)
    pose proof (LiteralDereliction [a]) as Hdel.
    rewrite E in Hdel. cbn [Intersect fold_right] in Hdel.
    destruct (rsubfR_int_r_inv _ _ _ Hdel) as [Hr _].
    apply (conv_to_lit (TUni A B) a).
    + rewrite <- E.
      change (clos_refl_trans M mlt (m (Integrate intersect (TLit a)) (TLit a)) (m (TLit a) (TLit a))).
      apply MeasurePreservation.
    + exact IHmain.
    + exact Hr.
  - (* TIsect *)
    pose proof (LiteralDereliction [a]) as Hdel.
    rewrite E in Hdel. cbn [Intersect fold_right] in Hdel.
    destruct (rsubfR_int_r_inv _ _ _ Hdel) as [Hr _].
    apply (conv_to_lit (TIsect A B) a).
    + rewrite <- E.
      change (clos_refl_trans M mlt (m (Integrate intersect (TLit a)) (TLit a)) (m (TLit a) (TLit a))).
      apply MeasurePreservation.
    + exact IHmain.
    + exact Hr.
  - (* TLit *)
    pose proof (LiteralDereliction [a]) as Hdel.
    rewrite E in Hdel. cbn [Intersect fold_right] in Hdel.
    destruct (rsubfR_int_r_inv _ _ _ Hdel) as [Hr _].
    apply (conv_to_lit (TLit d) a).
    + rewrite <- E.
      change (clos_refl_trans M mlt (m (Integrate intersect (TLit a)) (TLit a)) (m (TLit a) (TLit a))).
      apply MeasurePreservation.
    + exact IHmain.
    + exact Hr.
Qed.

Lemma refl_isub_of_IH : forall X : T,
  (forall X' Y' : T, ord (X',Y') (X,X) -> esub X' Y' ->
     rsubf (@IPremise) (Integrate intersect X') Y') ->
  rsubf (@IPremise) (Integrate intersect X) X.
Proof.
  intros X IHmain.
  destruct X as [| | A B | A B | a].
  - (* TTop *) cbn [Integrate]. apply Rsubf. apply ui_top.
  - (* TBot *) cbn [Integrate]. apply Rsubf. apply ui_bot.
  - (* TUni *)
    cbn [Integrate]. apply Rsubf. apply ui_uni_l.
    + apply ui_uni_rl. apply rsubf_uisub. apply (IHmain A A).
      * apply ord_mono; apply sub_uni_l.
      * apply dsubda_refl.
    + apply ui_uni_rr. apply rsubf_uisub. apply (IHmain B B).
      * apply ord_mono; apply sub_uni_r.
      * apply dsubda_refl.
  - (* TIsect *)
    cbn [Integrate]. apply Rsubf. apply ui_int_r.
    + apply rsubf_uisub. apply (IHmain (TIsect A B) A).
      * apply ord_sub_r. apply sub_isect_l.
      * apply dsubda_int_ll.
    + apply rsubf_uisub. apply (IHmain (TIsect A B) B).
      * apply ord_sub_r. apply sub_isect_r.
      * apply dsubda_int_lr.
  - (* TLit *) apply (G_of_main_IH a). exact IHmain.
Qed.


Lemma promotion_int :
  forall (ls ls' : list Lit) (rs : list (sig2T RRule)) (A B : T),
    Forall (fun l' : Lit => Exists (fun r : sig2T RRule => proj2T2 r = l') rs) ls' ->
    incl (map proj2T1 rs) ls ->
    intersected ls ->
    intersect ls' = TIsect A B ->
    exists rs', Integrated_int
      (fun ls'' => ls'' = map proj2T2 rs' /\ incl (map proj2T1 rs') ls /\
        Forall (fun r' : sig2T RRule => forall tl tr : T,
          RPremise (proj2V r') tl tr ->
          rsubam (@RPremise) (fun tl' tr' => Exists (fun r => RPremise (proj2V r) tl' tr') rs) tl tr) rs')
      (TIsect A B).
Proof.
  intros ls ls' rs A B Hf Hi Hint E.
  destruct (LiteralPromotion ls ls' rs Hf Hi Hint) as [rs' Hx].
  rewrite E in Hx. cbn [Exists_Intersection] in Hx.
  exists rs'. exact Hx.
Qed.

Lemma conv_of_IH : forall X Y : T,
  (forall x y : T, ord (x,y) (X,Y) -> esub x y ->
     rsubf (@IPremise) (Integrate intersect x) y) ->
  rsubf (@RPremise) X Y ->
  rsubf (@IPremise) X Y.
Proof.
  intros X Y Hlift Hr.
  revert Hlift.
  refine (rsubf_wf_ind (@RPremise)
    (fun X Y => (forall x y : T, ord (x,y) (X,Y) -> esub x y ->
       rsubf (@IPremise) (Integrate intersect x) y) -> rsubf (@IPremise) X Y) _ X Y Hr).
  intros X0 Y0 IH Hr0 Hlift.
  inversion Hr0 as [U V Hu]; subst.
  inversion Hu; subst.
  - (* ui_lit *) apply Rsubf. apply ui_lit.
    destruct H as [r Hprem].
    exists r. intros tl tr Hip. destruct Hip as [pl pr Hrp].
    apply Hlift.
    + apply (ord_lit_R (r := r)). exact Hrp.
    + apply rsubf_sound_R. apply Hprem. exact Hrp.
  - (* ui_top *) apply Rsubf. apply ui_top.
  - (* ui_int_ll *)
    apply Rsubf. apply ui_int_ll.
    apply rsubf_uisub. apply (IH il Y0).
    + apply ord_sub_l. apply sub_isect_l.
    + apply Rsubf. assumption.
    + intros x y Ho He. apply Hlift.
      * eapply ord_trans; [exact Ho | apply ord_sub_l; apply sub_isect_l].
      * exact He.
  - (* ui_int_lr *)
    apply Rsubf. apply ui_int_lr.
    apply rsubf_uisub. apply (IH ir Y0).
    + apply ord_sub_l. apply sub_isect_r.
    + apply Rsubf. assumption.
    + intros x y Ho He. apply Hlift.
      * eapply ord_trans; [exact Ho | apply ord_sub_l; apply sub_isect_r].
      * exact He.
  - (* ui_int_r *)
    apply Rsubf. apply ui_int_r.
    + apply rsubf_uisub. apply (IH X0 il).
      * apply ord_sub_r. apply sub_isect_l.
      * apply Rsubf. assumption.
      * intros x y Ho He. apply Hlift.
        -- eapply ord_trans; [exact Ho | apply ord_sub_r; apply sub_isect_l].
        -- exact He.
    + apply rsubf_uisub. apply (IH X0 ir).
      * apply ord_sub_r. apply sub_isect_r.
      * apply Rsubf. assumption.
      * intros x y Ho He. apply Hlift.
        -- eapply ord_trans; [exact Ho | apply ord_sub_r; apply sub_isect_r].
        -- exact He.
  - (* ui_bot *) apply Rsubf. apply ui_bot.
  - (* ui_uni_rl *)
    apply Rsubf. apply ui_uni_rl.
    apply rsubf_uisub. apply (IH X0 ul).
    + apply ord_sub_r. apply sub_uni_l.
    + apply Rsubf. assumption.
    + intros x y Ho He. apply Hlift.
      * eapply ord_trans; [exact Ho | apply ord_sub_r; apply sub_uni_l].
      * exact He.
  - (* ui_uni_rr *)
    apply Rsubf. apply ui_uni_rr.
    apply rsubf_uisub. apply (IH X0 ur).
    + apply ord_sub_r. apply sub_uni_r.
    + apply Rsubf. assumption.
    + intros x y Ho He. apply Hlift.
      * eapply ord_trans; [exact Ho | apply ord_sub_r; apply sub_uni_r].
      * exact He.
  - (* ui_uni_l *)
    apply Rsubf. apply ui_uni_l.
    + apply rsubf_uisub. apply (IH ul Y0).
      * apply ord_sub_l. apply sub_uni_l.
      * apply Rsubf. assumption.
      * intros x y Ho He. apply Hlift.
        -- eapply ord_trans; [exact Ho | apply ord_sub_l; apply sub_uni_l].
        -- exact He.
    + apply rsubf_uisub. apply (IH ur Y0).
      * apply ord_sub_l. apply sub_uni_r.
      * apply Rsubf. assumption.
      * intros x y Ho He. apply Hlift.
        -- eapply ord_trans; [exact Ho | apply ord_sub_l; apply sub_uni_r].
        -- exact He.
Qed.

Lemma refl_IP_of_IH : forall X : T,
  (forall X' Y' : T, ord (X',Y') (X,X) -> esub X' Y' ->
     rsubf (@IPremise) (Integrate intersect X') Y') ->
  rsubf (@IPremise) X X.
Proof.
  intros X Hlift.
  apply (conv_of_IH X X).
  - exact Hlift.
  - apply refl_R.
Qed.

Lemma rsubam_sound_esub : forall (A : T -> T -> Prop) (X Y : T),
  rsubam (@RPremise) A X Y ->
  (forall x y : T, A x y -> esub x y) ->
  esub X Y.
Proof.
  intros A X Y H. induction H; intro HA.
  - apply HA. exact H.
  - eapply esub_tr.
    + apply rsubf_sound_R. exact H.
    + eapply esub_tr.
      * apply IHrsubam. exact HA.
      * apply rsubf_sound_R. exact H1.
  - apply (dsubda_cut (RPremise r)).
    + intros pl pr Hp. apply H0; [exact Hp | exact HA].
    + apply dsuba_dsubda. apply RRuleToDProof.
  - apply dsubda_top.
  - eapply esub_tr; [apply dsubda_int_ll | apply IHrsubam; exact HA].
  - eapply esub_tr; [apply dsubda_int_lr | apply IHrsubam; exact HA].
  - apply dsubda_int_r; [apply IHrsubam1; exact HA | apply IHrsubam2; exact HA].
  - apply dsubda_bot.
  - eapply esub_tr; [apply IHrsubam; exact HA | apply dsubda_uni_rl].
  - eapply esub_tr; [apply IHrsubam; exact HA | apply dsubda_uni_rr].
  - apply dsubda_uni_l; [apply IHrsubam1; exact HA | apply IHrsubam2; exact HA].
Qed.

Lemma isub_lit_trans_of_IH : forall (a b c : Lit),
  (forall x y : T, ord (x,y) (TLit a, TLit c) -> esub x y ->
     rsubf (@IPremise) (Integrate intersect x) y) ->
  rsubf (@IPremise) (TLit a) (TLit b) ->
  rsubf (@IPremise) (TLit b) (TLit c) ->
  rsubf (@IPremise) (TLit a) (TLit c).
Proof.
  intros a b c IH H1 H2.
  inversion H1 as [U1 V1 Hu1]; subst.
  inversion Hu1; subst.
  match goal with
  | H : lsub _ (rsubf (@IPremise)) a b |- _ => destruct H as [r1 Hp1]
  end.
  inversion H2 as [U2 V2 Hu2]; subst.
  inversion Hu2; subst.
  match goal with
  | H : lsub _ (rsubf (@IPremise)) b c |- _ => destruct H as [r2 Hp2]
  end.
  destruct (LiteralTransitivity r1 r2) as [r Hdec].
  apply Rsubf. apply ui_lit.
  exists r. intros tl tr Hip. destruct Hip as [pl pr Hrp].
  destruct (Hdec pl pr Hrp) as [pm [[Hch1 Hch2] | [Hch1 Hch2]]].
  - (* r1 then r2 *)
    assert (Hes1 : forall x y : T, RPremise r1 x y -> esub x y).
    { intros x y Hp. pose proof (Hp1 (Integrate intersect x) y (ipremise r1 x y Hp)) as Hri.
      apply rsubf_sound_IP in Hri.
      eapply esub_tr; [apply esub_Integrate_upper | exact Hri]. }
    assert (Hes2 : forall x y : T, RPremise r2 x y -> esub x y).
    { intros x y Hp. pose proof (Hp2 (Integrate intersect x) y (ipremise r2 x y Hp)) as Hri.
      apply rsubf_sound_IP in Hri.
      eapply esub_tr; [apply esub_Integrate_upper | exact Hri]. }
    pose proof (rsubam_sound_esub (RPremise r1) pl pm Hch1 Hes1) as Es1.
    pose proof (rsubam_sound_esub (RPremise r2) pm pr Hch2 Hes2) as Es2.
    pose proof (esub_tr pl pm pr Es1 Es2) as Es.
    apply (IH pl pr).
    + unfold ord, mval, sval. cbn [fst snd]. apply left_slex.
      apply t_step. apply (m_lit r). exact Hrp.
    + exact Es.
  - (* r2 then r1 *)
    assert (Hes1 : forall x y : T, RPremise r1 x y -> esub x y).
    { intros x y Hp. pose proof (Hp1 (Integrate intersect x) y (ipremise r1 x y Hp)) as Hri.
      apply rsubf_sound_IP in Hri.
      eapply esub_tr; [apply esub_Integrate_upper | exact Hri]. }
    assert (Hes2 : forall x y : T, RPremise r2 x y -> esub x y).
    { intros x y Hp. pose proof (Hp2 (Integrate intersect x) y (ipremise r2 x y Hp)) as Hri.
      apply rsubf_sound_IP in Hri.
      eapply esub_tr; [apply esub_Integrate_upper | exact Hri]. }
    pose proof (rsubam_sound_esub (RPremise r2) pl pm Hch1 Hes2) as Es1.
    pose proof (rsubam_sound_esub (RPremise r1) pm pr Hch2 Hes1) as Es2.
    pose proof (esub_tr pl pm pr Es1 Es2) as Es.
    apply (IH pl pr).
    + unfold ord, mval, sval. cbn [fst snd]. apply left_slex.
      apply t_step. apply (m_lit r). exact Hrp.
    + exact Es.
Qed.

Lemma isub_lit_trans_right_of_IH : forall (a b : Lit) (Z : T),
  (forall x y : T, ord (x,y) (TLit a, Z) -> esub x y ->
     rsubf (@IPremise) (Integrate intersect x) y) ->
  rsubf (@IPremise) (TLit a) (TLit b) ->
  rsubf (@IPremise) (TLit b) Z ->
  rsubf (@IPremise) (TLit a) Z.
Proof.
  intros a b Z Hmain H1 H2.
  refine (rsubf_wf_ind (@IPremise)
    (fun Y Z => forall (a : Lit),
       rsubf (@IPremise) (TLit a) Y ->
       (forall x y : T, ord (x,y) (TLit a, Z) -> esub x y ->
          rsubf (@IPremise) (Integrate intersect x) y) ->
       rsubf (@IPremise) (TLit a) Z) _ (TLit b) Z H2 a H1 Hmain).
  intros Y0 Z0 IH Hr2.
  inversion Hr2 as [U V Hu]; subst.
  inversion Hu; subst.
  - (* ui_lit *) intros a0 Hfirst Hmain0.
    apply (isub_lit_trans_of_IH a0 ll lr).
    + exact Hmain0.
    + exact Hfirst.
    + apply Rsubf. apply ui_lit. assumption.
  - (* ui_top *) intros a0 Hfirst Hmain0. apply Rsubf. apply ui_top.
  - (* ui_int_ll *) intros a0 Hfirst Hmain0.
    destruct (rsubf_int_r_inv _ _ _ Hfirst) as [Hil _].
    apply (IH il Z0).
    + apply ord_sub_l. apply sub_isect_l.
    + apply Rsubf. assumption.
    + exact Hil.
    + exact Hmain0.
  - (* ui_int_lr *) intros a0 Hfirst Hmain0.
    destruct (rsubf_int_r_inv _ _ _ Hfirst) as [_ Hir].
    apply (IH ir Z0).
    + apply ord_sub_l. apply sub_isect_r.
    + apply Rsubf. assumption.
    + exact Hir.
    + exact Hmain0.
  - (* ui_int_r *) intros a0 Hfirst Hmain0.
    apply Rsubf. apply ui_int_r.
    + apply rsubf_uisub. apply (IH Y0 il).
      * apply ord_sub_r. apply sub_isect_l.
      * apply Rsubf. assumption.
      * exact Hfirst.
      * intros x y Ho He. apply Hmain0.
        -- eapply ord_trans; [exact Ho | apply ord_sub_r; apply sub_isect_l].
        -- exact He.
    + apply rsubf_uisub. apply (IH Y0 ir).
      * apply ord_sub_r. apply sub_isect_r.
      * apply Rsubf. assumption.
      * exact Hfirst.
      * intros x y Ho He. apply Hmain0.
        -- eapply ord_trans; [exact Ho | apply ord_sub_r; apply sub_isect_r].
        -- exact He.
  - (* ui_bot *) intros a0 Hfirst Hmain0. inversion Hfirst as [U' V' Hu']; subst. inversion Hu'.
  - (* ui_uni_rl *) intros a0 Hfirst Hmain0.
    apply Rsubf. apply ui_uni_rl.
    apply rsubf_uisub. apply (IH Y0 ul).
    + apply ord_sub_r. apply sub_uni_l.
    + apply Rsubf. assumption.
    + exact Hfirst.
    + intros x y Ho He. apply Hmain0.
      * eapply ord_trans; [exact Ho | apply ord_sub_r; apply sub_uni_l].
      * exact He.
  - (* ui_uni_rr *) intros a0 Hfirst Hmain0.
    apply Rsubf. apply ui_uni_rr.
    apply rsubf_uisub. apply (IH Y0 ur).
    + apply ord_sub_r. apply sub_uni_r.
    + apply Rsubf. assumption.
    + exact Hfirst.
    + intros x y Ho He. apply Hmain0.
      * eapply ord_trans; [exact Ho | apply ord_sub_r; apply sub_uni_r].
      * exact He.
  - (* ui_uni_l *) intros a0 Hfirst Hmain0.
    inversion Hfirst as [U' V' Hu']; subst.
    inversion Hu'; subst.
    + (* first proof ui_uni_rl *) apply (IH ul Z0).
      * apply ord_sub_l. apply sub_uni_l.
      * apply Rsubf. assumption.
      * apply Rsubf. assumption.
      * exact Hmain0.
    + (* first proof ui_uni_rr *) apply (IH ur Z0).
      * apply ord_sub_l. apply sub_uni_r.
      * apply Rsubf. assumption.
      * apply Rsubf. assumption.
      * exact Hmain0.
Qed.

Lemma IP_trans_lit_right_of_IH : forall (X : T) (b : Lit) (Z : T),
  (forall x y : T, ord (x,y) (X,Z) -> esub x y ->
     rsubf (@IPremise) (Integrate intersect x) y) ->
  rsubf (@IPremise) X (TLit b) ->
  rsubf (@IPremise) (TLit b) Z ->
  rsubf (@IPremise) X Z.
Proof.
  intros X b Z Hmain H1 H2.
  refine (rsubf_wf_ind (@IPremise)
    (fun X Y => forall (b : Lit) (Z : T), Y = TLit b ->
       (forall x y : T, ord (x,y) (X,Z) -> esub x y ->
          rsubf (@IPremise) (Integrate intersect x) y) ->
       rsubf (@IPremise) (TLit b) Z ->
       rsubf (@IPremise) X Z) _ X (TLit b) H1 b Z eq_refl Hmain H2).
  intros X0 Y0 IH Hr1 b0 Z0 Heq Hmain0 Hr2. subst Y0.
  inversion Hr1 as [U V Hu]; subst.
  inversion Hu; subst.
  - (* ui_lit *)
    assert (HpremIP : rsubf (@IPremise) (TLit ll) (TLit b0)).
    { apply Rsubf. apply ui_lit. exact H3. }
    exact (isub_lit_trans_right_of_IH ll b0 Z0 Hmain0 HpremIP Hr2).
  - (* ui_int_ll *)
    apply Rsubf. apply ui_int_ll. apply rsubf_uisub.
    assert (Hord : ord (il, TLit b0) (TIsect il ir, TLit b0)).
    { apply ord_sub_l. apply sub_isect_l. }
    assert (HpremR : rsubf (@IPremise) il (TLit b0)).
    { apply Rsubf. assumption. }
    assert (Hmain' : forall x y : T, ord (x,y) (il, Z0) -> esub x y ->
                      rsubf (@IPremise) (Integrate intersect x) y).
    { intros x y Ho He. apply Hmain0.
      - eapply ord_trans; [exact Ho | apply ord_sub_l; apply sub_isect_l].
      - exact He. }
    exact (IH il (TLit b0) Hord HpremR b0 Z0 eq_refl Hmain' Hr2).
  - (* ui_int_lr *)
    apply Rsubf. apply ui_int_lr. apply rsubf_uisub.
    assert (Hord : ord (ir, TLit b0) (TIsect il ir, TLit b0)).
    { apply ord_sub_l. apply sub_isect_r. }
    assert (HpremR : rsubf (@IPremise) ir (TLit b0)).
    { apply Rsubf. assumption. }
    assert (Hmain' : forall x y : T, ord (x,y) (ir, Z0) -> esub x y ->
                      rsubf (@IPremise) (Integrate intersect x) y).
    { intros x y Ho He. apply Hmain0.
      - eapply ord_trans; [exact Ho | apply ord_sub_l; apply sub_isect_r].
      - exact He. }
    exact (IH ir (TLit b0) Hord HpremR b0 Z0 eq_refl Hmain' Hr2).
  - (* ui_bot *) apply Rsubf. apply ui_bot.
  - (* ui_uni_l *)
    apply Rsubf. apply ui_uni_l.
    + apply rsubf_uisub.
      assert (Hord : ord (ul, TLit b0) (TUni ul ur, TLit b0)).
      { apply ord_sub_l. apply sub_uni_l. }
      assert (HpremR : rsubf (@IPremise) ul (TLit b0)).
      { apply Rsubf. assumption. }
      assert (Hmain' : forall x y : T, ord (x,y) (ul, Z0) -> esub x y ->
                        rsubf (@IPremise) (Integrate intersect x) y).
      { intros x y Ho He. apply Hmain0.
        - eapply ord_trans; [exact Ho | apply ord_sub_l; apply sub_uni_l].
        - exact He. }
      exact (IH ul (TLit b0) Hord HpremR b0 Z0 eq_refl Hmain' Hr2).
    + apply rsubf_uisub.
      assert (Hord : ord (ur, TLit b0) (TUni ul ur, TLit b0)).
      { apply ord_sub_l. apply sub_uni_r. }
      assert (HpremR : rsubf (@IPremise) ur (TLit b0)).
      { apply Rsubf. assumption. }
      assert (Hmain' : forall x y : T, ord (x,y) (ur, Z0) -> esub x y ->
                        rsubf (@IPremise) (Integrate intersect x) y).
      { intros x y Ho He. apply Hmain0.
        - eapply ord_trans; [exact Ho | apply ord_sub_l; apply sub_uni_r].
        - exact He. }
      exact (IH ur (TLit b0) Hord HpremR b0 Z0 eq_refl Hmain' Hr2).
Qed.


Lemma isub_lit_rule : forall {ll lr : Lit} (r : RRule ll lr),
  (forall pl pr : T, RPremise r pl pr ->
     rsubf (@IPremise) (Integrate intersect pl) pr) ->
  rsubf (@IPremise) (TLit ll) (TLit lr).
Proof.
  intros ll lr r H. apply Rsubf. apply ui_lit.
  exists r. intros tl tr Hip. destruct Hip as [pl pr Hrp].
  apply H. exact Hrp.
Qed.


Lemma lsub_IP_of_premises : forall (ll lr : Lit) (r : RRule ll lr),
  (forall pl pr : T, RPremise r pl pr ->
     rsubf (@IPremise) (Integrate intersect pl) pr) ->
  lsub (@IPremise) (rsubf (@IPremise)) ll lr.
Proof.
  intros ll lr r H. exists r. intros tl tr Hip.
  destruct Hip as [pl pr Hrp]. apply H. exact Hrp.
Qed.


Lemma isub_lit_rule_R : forall (ll lr : Lit) (r : RRule ll lr),
  (forall pl pr : T, RPremise r pl pr -> rsubf (@RPremise) pl pr) ->
  rsubf (@RPremise) (TLit ll) (TLit lr).
Proof.
  intros ll lr r H. apply Rsubf. apply ui_lit.
  exists r. exact H.
Qed.


Lemma isub_dsubda_lit_of_ram :
  (forall (A : T -> T -> Prop) (X Y : T),
     rsubam (@RPremise) A X Y ->
     (forall pl pr : T, A pl pr ->
        rsubf (@IPremise) (Integrate intersect pl) pr) ->
     rsubf (@IPremise) (Integrate intersect X) Y) ->
  forall {ll lr : Lit} (r : DRule ll lr),
    (forall pl pr : T, DPremise r pl pr ->
       rsubf (@IPremise) (Integrate intersect pl) pr) ->
    rsubf (@IPremise) (Integrate intersect (TLit ll)) (TLit lr).
Proof.
  intros Hconv ll lr r Hprem.
  apply Hconv with (A := DPremise r) (X := TLit ll) (Y := TLit lr).
  - apply DRuleToRProof.
  - exact Hprem.
Qed.


Lemma rsubf_IP_top : forall X : T, rsubf (@IPremise) X TTop.
Proof. intro X. apply Rsubf. apply ui_top. Qed.

Lemma rsubf_IP_bot : forall Y : T, rsubf (@IPremise) TBot Y.
Proof. intro Y. apply Rsubf. apply ui_bot. Qed.


Lemma rsubf_IP_int_r : forall X A B : T,
  rsubf (@IPremise) X A -> rsubf (@IPremise) X B ->
  rsubf (@IPremise) X (TIsect A B).
Proof.
  intros X A B HA HB. apply Rsubf. apply ui_int_r;
    [apply rsubf_uisub; exact HA | apply rsubf_uisub; exact HB].
Qed.

Lemma rsubf_IP_uni_rl : forall X A B : T,
  rsubf (@IPremise) X A -> rsubf (@IPremise) X (TUni A B).
Proof.
  intros X A B H. apply Rsubf. apply ui_uni_rl. apply rsubf_uisub. exact H.
Qed.

Lemma rsubf_IP_uni_rr : forall X A B : T,
  rsubf (@IPremise) X B -> rsubf (@IPremise) X (TUni A B).
Proof.
  intros X A B H. apply Rsubf. apply ui_uni_rr. apply rsubf_uisub. exact H.
Qed.

Lemma rsubf_IP_uni_l : forall A B C : T,
  rsubf (@IPremise) A C -> rsubf (@IPremise) B C ->
  rsubf (@IPremise) (TUni A B) C.
Proof.
  intros A B C HA HB. apply Rsubf. apply ui_uni_l;
    [apply rsubf_uisub; exact HA | apply rsubf_uisub; exact HB].
Qed.


Lemma rsubf_IP_int_ll_of : forall A B C : T,
  rsubf (@IPremise) A C -> rsubf (@IPremise) (TIsect A B) C.
Proof.
  intros A B C H. apply Rsubf. apply ui_int_ll. apply rsubf_uisub. exact H.
Qed.

Lemma rsubf_IP_int_lr_of : forall A B C : T,
  rsubf (@IPremise) B C -> rsubf (@IPremise) (TIsect A B) C.
Proof.
  intros A B C H. apply Rsubf. apply ui_int_lr. apply rsubf_uisub. exact H.
Qed.

Definition dsubd (X Y : T) : Prop := dsubda (@DPremise) (fun _ _ => False) X Y.

Definition weaken_dsubd_R (X Y : T)
  (IHord : forall X' Y', ord (X',Y') (X,Y) -> rsubf (@RPremise) X' Y' -> dsubd X' Y')
  (X0 Y0 : T) (H0 : ord (X0,Y0) (X,Y)) :
  forall X' Y', ord (X',Y') (X0,Y0) -> rsubf (@RPremise) X' Y' -> dsubd X' Y' :=
  fun X' Y' Ho H => IHord X' Y' (ord_trans (X',Y') (X0,Y0) (X,Y) Ho H0) H.

Lemma uisub_sound_R_dsubd_aux : forall X Y,
  uisub (lsub (@RPremise) (rsubf (@RPremise))) X Y ->
  (forall X' Y', ord (X',Y') (X,Y) -> rsubf (@RPremise) X' Y' -> dsubd X' Y') ->
  dsubd X Y.
Proof.
  intros X Y Hu. induction Hu; intros IHord.
  - destruct H as [r Hprem].
    apply (dsubda_cut_gen (RPremise r) (fun _ _ => False)).
    * intros p q Hrp. exact (IHord p q (ord_lit_R Hrp) (Hprem p q Hrp)).
    * apply dsuba_dsubda. apply RRuleToDProof.
  - apply dsubda_top.
  - eapply dsubda_trans with (tm := il); [apply dsubda_int_ll |].
    apply IHHu. apply (weaken_dsubd_R (TIsect il ir) tr IHord il tr (ord_sub_l il tr (TIsect il ir) (sub_isect_l il ir))).
  - eapply dsubda_trans with (tm := ir); [apply dsubda_int_lr |].
    apply IHHu. apply (weaken_dsubd_R (TIsect il ir) tr IHord ir tr (ord_sub_l ir tr (TIsect il ir) (sub_isect_r ir il))).
  - apply dsubda_int_r.
    + apply IHHu1. apply (weaken_dsubd_R tl (TIsect il ir) IHord tl il (ord_sub_r tl il (TIsect il ir) (sub_isect_l il ir))).
    + apply IHHu2. apply (weaken_dsubd_R tl (TIsect il ir) IHord tl ir (ord_sub_r tl ir (TIsect il ir) (sub_isect_r ir il))).
  - apply dsubda_bot.
  - eapply dsubda_trans with (tm := ul); [| apply dsubda_uni_rl].
    apply IHHu. apply (weaken_dsubd_R tl (TUni ul ur) IHord tl ul (ord_sub_r tl ul (TUni ul ur) (sub_uni_l ul ur))).
  - eapply dsubda_trans with (tm := ur); [| apply dsubda_uni_rr].
    apply IHHu. apply (weaken_dsubd_R tl (TUni ul ur) IHord tl ur (ord_sub_r tl ur (TUni ul ur) (sub_uni_r ur ul))).
  - apply dsubda_uni_l.
    + apply IHHu1. apply (weaken_dsubd_R (TUni ul ur) tr IHord ul tr (ord_sub_l ul tr (TUni ul ur) (sub_uni_l ul ur))).
    + apply IHHu2. apply (weaken_dsubd_R (TUni ul ur) tr IHord ur tr (ord_sub_l ur tr (TUni ul ur) (sub_uni_r ur ul))).
Qed.

Lemma rsubf_sound_R_dsubd : forall X Y : T, rsubf (@RPremise) X Y -> dsubd X Y.
Proof.
  intros X Y H. refine (rsubf_wf_ind (@RPremise) (fun X Y => dsubd X Y) _ X Y H).
  intros X0 Y0 IH Hr. inversion Hr; subst. eapply uisub_sound_R_dsubd_aux; [exact H0 | exact IH].
Qed.

Lemma dsubd_dereliction : forall ls, dsubd (intersect ls) (Intersect ls).
Proof. intro ls. apply rsubf_sound_R_dsubd. apply LiteralDereliction. Qed.

Lemma dsubd_int_ll A B : dsubd (TIsect A B) A. Proof. apply dsubda_int_ll. Qed.
Lemma dsubd_int_lr A B : dsubd (TIsect A B) B. Proof. apply dsubda_int_lr. Qed.
Lemma dsubd_top t : dsubd t TTop. Proof. apply dsubda_top. Qed.
Lemma dsubd_refl t : dsubd t t. Proof. apply dsubda_refl. Qed.
Lemma dsubd_tr a b c : dsubd a b -> dsubd b c -> dsubd a c. Proof. apply dsubda_trans. Qed.
Lemma dsubd_int_r t A B : dsubd t A -> dsubd t B -> dsubd t (TIsect A B). Proof. apply dsubda_int_r. Qed.
Lemma dsubd_uni_l A B t : dsubd A t -> dsubd B t -> dsubd (TUni A B) t. Proof. apply dsubda_uni_l. Qed.
Lemma dsubd_uni_rl t B : dsubd t (TUni t B). Proof. apply dsubda_uni_rl. Qed.
Lemma dsubd_uni_rr t B : dsubd t (TUni B t). Proof. apply dsubda_uni_rr. Qed.
Lemma dsubd_uni_rl' A B C : dsubd A B -> dsubd A (TUni B C).
Proof. intro H. eapply dsubda_trans with (tm := B); [exact H | apply dsubda_uni_rl]. Qed.
Lemma dsubd_uni_rr' A B C : dsubd A C -> dsubd A (TUni B C).
Proof. intro H. eapply dsubda_trans with (tm := C); [exact H | apply dsubda_uni_rr]. Qed.
Lemma dsubd_dist A B C : dsubd (TIsect A (TUni B C)) (TUni (TIsect A B) (TIsect A C)).
Proof. apply dsubda_dist. Qed.

Lemma dsubd_Isect_congr A A' B B' : dsubd A A' -> dsubd B B' -> dsubd (TIsect A B) (TIsect A' B').
Proof.
  intros HA HB. apply dsubd_int_r.
  - eapply dsubda_trans with (tm := A); [apply dsubd_int_ll | exact HA].
  - eapply dsubda_trans with (tm := B); [apply dsubd_int_lr | exact HB].
Qed.

Lemma dsubd_Isect_swap A B : dsubd (TIsect A B) (TIsect B A).
Proof. apply dsubd_int_r; [apply dsubd_int_lr | apply dsubd_int_ll]. Qed.

Lemma dsubd_Isect_assoc_l A B C : dsubd (TIsect A (TIsect B C)) (TIsect (TIsect A B) C).
Proof.
  apply dsubd_int_r.
  - apply dsubd_int_r.
    + apply dsubd_int_ll.
    + eapply dsubda_trans with (tm := TIsect B C); [apply dsubd_int_lr | apply dsubd_int_ll].
  - eapply dsubda_trans with (tm := TIsect B C); [apply dsubd_int_lr | apply dsubd_int_lr].
Qed.
Lemma dsubd_Isect_assoc_r A B C : dsubd (TIsect (TIsect A B) C) (TIsect A (TIsect B C)).
Proof.
  apply dsubd_int_r.
  - eapply dsubda_trans with (tm := TIsect A B); [apply dsubd_int_ll | apply dsubd_int_ll].
  - apply dsubd_int_r.
    + eapply dsubda_trans with (tm := TIsect A B); [apply dsubd_int_ll | apply dsubd_int_lr].
    + apply dsubd_int_lr.
Qed.

Lemma dsubd_Isect_top_r A : dsubd (TIsect A TTop) A.
Proof. apply dsubd_int_ll. Qed.
Lemma dsubd_Isect_top_l A : dsubd (TIsect TTop A) A.
Proof. apply dsubd_int_lr. Qed.
Lemma dsubd_Isect_top_intro A : dsubd A (TIsect A TTop).
Proof. apply dsubd_int_r; [apply dsubd_refl | apply dsubd_top]. Qed.

Lemma dsubd_Isect_mid_swap X b L : dsubd (TIsect (TIsect X b) L) (TIsect (TIsect X L) b).
Proof.
  apply dsubd_int_r.
  - apply dsubd_int_r.
    + eapply dsubda_trans with (tm := TIsect X b); [apply dsubd_int_ll | apply dsubd_int_ll].
    + apply dsubd_int_lr.
  - eapply dsubda_trans with (tm := TIsect X b); [apply dsubd_int_ll | apply dsubd_int_lr].
Qed.
Lemma dsubd_Isect_mid_swap' X b L : dsubd (TIsect (TIsect X L) b) (TIsect (TIsect X b) L).
Proof.
  apply dsubd_int_r.
  - apply dsubd_int_r.
    + eapply dsubda_trans with (tm := TIsect X L); [apply dsubd_int_ll | apply dsubd_int_ll].
    + apply dsubd_int_lr.
  - eapply dsubda_trans with (tm := TIsect X L); [apply dsubd_int_ll | apply dsubd_int_lr].
Qed.

Lemma dsubd_Intersect_app_l ls ls' : dsubd (Intersect (ls++ls')) (TIsect (Intersect ls) (Intersect ls')).
Proof.
  induction ls as [| a ls IH]; cbn [Intersect app].
  - apply dsubd_int_r; [apply dsubd_top | apply dsubd_refl].
  - apply dsubd_int_r.
    + apply dsubd_int_r.
      * apply dsubd_int_ll.
      * eapply dsubda_trans with (tm := Intersect (ls++ls')); [apply dsubd_int_lr |].
        eapply dsubda_trans with (tm := TIsect (Intersect ls) (Intersect ls'));
          [exact IH | apply dsubd_int_ll].
    + eapply dsubda_trans with (tm := Intersect (ls++ls')); [apply dsubd_int_lr |].
      eapply dsubda_trans with (tm := TIsect (Intersect ls) (Intersect ls'));
        [exact IH | apply dsubd_int_lr].
Qed.

Lemma dsubd_Intersect_app_r ls ls' : dsubd (TIsect (Intersect ls) (Intersect ls')) (Intersect (ls++ls')).
Proof.
  induction ls as [| a ls IH]; cbn [Intersect app].
  - apply dsubd_Isect_top_l.
  - apply dsubd_int_r.
    + eapply dsubda_trans with (tm := TIsect (TLit a) (Intersect ls));
        [apply dsubd_int_ll | apply dsubd_int_ll].
    + eapply dsubda_trans with (tm := TIsect (Intersect ls) (Intersect ls')).
      * apply dsubd_int_r.
        -- eapply dsubda_trans with (tm := TIsect (TLit a) (Intersect ls));
             [apply dsubd_int_ll | apply dsubd_int_lr].
        -- apply dsubd_int_lr.
      * exact IH.
Qed.


Lemma dsubd_integrate_const : forall b (g : list Lit -> T) T0,
  (forall l', dsubd (g l') T0) -> dsubd (Integrate g b) T0.
Proof.
  induction b; intros g T0 Hg.
  - cbn [Integrate]. apply Hg.
  - cbn [Integrate]. apply dsubda_bot.
  - cbn [Integrate]. apply dsubd_uni_l; [apply IHb1 | apply IHb2]; intro l'; apply Hg.
  - cbn [Integrate]. apply IHb1. intro l'. apply IHb2. intro l''. apply Hg.
  - cbn [Integrate]. apply Hg.
Qed.


Lemma MainLowerD : forall (t : T) (X : T) (f : list Lit -> T),
  (forall ls, dsubd (f ls) (TIsect X (Intersect ls))) ->
  dsubd (Integrate f t) (TIsect X t).
Proof.
  induction t; intros X f H.
  - cbn [Integrate]. apply H.
  - cbn [Integrate]. apply dsubda_bot.
  - cbn [Integrate]. apply dsubd_uni_l.
    + eapply dsubda_trans with (tm := TIsect X t1).
      * apply IHt1; exact H.
      * apply dsubd_Isect_congr; [apply dsubd_refl | apply dsubd_uni_rl].
    + eapply dsubda_trans with (tm := TIsect X t2).
      * apply IHt2; exact H.
      * apply dsubd_Isect_congr; [apply dsubd_refl | apply dsubd_uni_rr].
  - cbn [Integrate].
    eapply dsubda_trans with (tm := TIsect (TIsect X t1) (TIsect X t2)).
    + apply dsubd_int_r.
      * apply IHt1. intro l.
        apply dsubd_integrate_const with (g := fun l' => f (l ++ l')) (T0 := TIsect X (Intersect l)).
        intro l'. eapply dsubda_trans with (tm := TIsect X (Intersect (l ++ l'))).
        -- apply H.
        -- apply dsubd_Isect_congr; [apply dsubd_refl |].
           eapply dsubda_trans with (tm := TIsect (Intersect l) (Intersect l')).
           ++ apply dsubd_Intersect_app_l.
           ++ apply dsubd_int_ll.
      * apply dsubd_integrate_const with (g := fun l => Integrate (fun l' => f (l ++ l')) t2) (T0 := TIsect X t2).
        intro l. apply IHt2 with (X := X). intro l'.
        eapply dsubda_trans with (tm := TIsect X (Intersect (l ++ l'))).
        -- apply H.
        -- apply dsubd_Isect_congr; [apply dsubd_refl |].
           eapply dsubda_trans with (tm := TIsect (Intersect l) (Intersect l')).
           ++ apply dsubd_Intersect_app_l.
           ++ apply dsubd_int_lr.
    + apply dsubd_int_r.
      * eapply dsubda_trans with (tm := TIsect X t1); [apply dsubd_int_ll | apply dsubd_int_ll].
      * apply dsubd_int_r.
        -- eapply dsubda_trans with (tm := TIsect X t1); [apply dsubd_int_ll | apply dsubd_int_lr].
        -- eapply dsubda_trans with (tm := TIsect X t2); [apply dsubd_int_lr | apply dsubd_int_lr].
  - cbn [Integrate]. eapply dsubda_trans with (tm := TIsect X (Intersect [l])).
    + apply H.
    + apply dsubd_Isect_congr; [apply dsubd_refl |].
      change (dsubd (TIsect (TLit l) TTop) (TLit l)). apply dsubd_Isect_top_r.
Qed.
Lemma dsubd_Integrate_lower : forall t : T, dsubd (Integrate intersect t) t.
Proof.
  intro t.
  eapply dsubda_trans with (tm := TIsect TTop t).
  - apply MainLowerD with (X := TTop) (f := intersect).
    intro ls. eapply dsubda_trans with (tm := Intersect ls).
    + apply dsubd_dereliction.
    + apply dsubd_int_r; [apply dsubd_top | apply dsubd_refl].
  - apply dsubd_Isect_top_l.
Qed.


Section IntegratedUpper.
Definition SpecD (X : T) (f : list Lit -> T) : Prop :=
  forall ls, dsubd (TIsect X (Intersect ls)) (f ls).

Lemma MainD : forall t : T, forall (X : T) (f : list Lit -> T),
  SpecD X f -> dsubd (TIsect X t) (Integrate f t).
Proof.
  intro t. induction t; intros X f HS.
  - (* TTop *) cbn [Integrate]. change (dsubd (TIsect X (Intersect [])) (f [])); apply HS.
  - (* TBot *) cbn [Integrate]. apply dsubd_int_lr.
  - (* TUni *) cbn [Integrate].
    eapply dsubda_trans with (tm := TUni (TIsect X t1) (TIsect X t2)).
    + apply dsubd_dist.
    + apply dsubd_uni_l.
      * eapply dsubda_trans with (tm := Integrate f t1); [apply IHt1; exact HS | apply dsubda_uni_rl].
      * eapply dsubda_trans with (tm := Integrate f t2); [apply IHt2; exact HS | apply dsubda_uni_rr].
  - (* TIsect *) cbn [Integrate].
    pose (g := fun l : list Lit => Integrate (fun l' : list Lit => f (l ++ l')) t2).
    eapply dsubda_trans with (tm := TIsect (TIsect X t2) t1).
    + eapply dsubda_trans with (tm := TIsect (TIsect X t1) t2).
      * apply dsubd_Isect_assoc_l.
      * apply dsubd_Isect_mid_swap'.
    + apply IHt1 with (X := TIsect X t2) (f := g).
      intros ls.
      eapply dsubda_trans with (tm := TIsect (TIsect X (Intersect ls)) t2).
      * apply dsubd_Isect_mid_swap.
      * apply IHt2 with (X := TIsect X (Intersect ls)) (f := fun l' => f (ls ++ l')).
        intros ls'.
        eapply dsubda_trans with (tm := TIsect X (Intersect (ls ++ ls'))).
        -- eapply dsubda_trans with (tm := TIsect X (TIsect (Intersect ls) (Intersect ls'))).
           ++ apply dsubd_Isect_assoc_r.
           ++ apply dsubd_Isect_congr; [apply dsubd_refl | apply dsubd_Intersect_app_r].
        -- apply HS.
  - (* TLit *) cbn [Integrate].
    eapply dsubda_trans with (tm := TIsect X (Intersect [l])).
    + apply dsubd_int_r.
      * apply dsubd_int_ll.
      * change (dsubd (TIsect X (TLit l)) (TIsect (TLit l) TTop)).
        apply dsubd_int_r; [apply dsubd_int_lr | apply dsubd_top].
    + apply HS.
Qed.

Lemma dsubd_Integrate_upper_of_sound :
  (forall ls : list Lit, dsubd (Intersect ls) (intersect ls)) ->
  forall t : T, dsubd t (Integrate intersect t).
Proof.
  intros Hsound t.
  eapply dsubda_trans with (tm := TIsect TTop t).
  - apply dsubd_int_r; [apply dsubd_top | apply dsubd_refl].
  - apply MainD with (X := TTop) (f := intersect).
    intros ls.
    eapply dsubda_trans with (tm := Intersect ls).
    + apply dsubd_Isect_top_l.
    + apply Hsound.
Qed.
End IntegratedUpper.

Lemma dsubd_Intersect_mem : forall (ls : list Lit) (l : Lit),
  In l ls -> dsubd (Intersect ls) (TLit l).
Proof.
  induction ls as [| a ls IH]; intros l Hin.
  - destruct Hin.
  - simpl in Hin. destruct Hin as [-> | Hin].
    + apply dsubd_int_ll.
    + eapply dsubd_tr with (b := Intersect ls).
      * apply dsubd_int_lr.
      * apply IH. exact Hin.
Qed.

Lemma dsubd_intersect_mem : forall (ls : list Lit) (l : Lit),
  In l ls -> dsubd (intersect ls) (TLit l).
Proof.
  intros ls l Hin. eapply dsubd_tr with (b := Intersect ls).
  - apply dsubd_dereliction.
  - apply dsubd_Intersect_mem. exact Hin.
Qed.


Lemma dsubd_I_int_ll : forall A B : T,
  dsubd (Integrate intersect (TIsect A B)) A.
Proof.
  intros A B. eapply dsubd_tr with (b := TIsect A B).
  - apply dsubd_Integrate_lower.
  - apply dsubd_int_ll.
Qed.

Lemma dsubd_I_int_lr : forall A B : T,
  dsubd (Integrate intersect (TIsect A B)) B.
Proof.
  intros A B. eapply dsubd_tr with (b := TIsect A B).
  - apply dsubd_Integrate_lower.
  - apply dsubd_int_lr.
Qed.

Lemma dsubd_prefix_lit : forall (b : T) (l : Lit) (q : list Lit),
  dsubd (Integrate (fun l' => intersect (l :: (q ++ l'))) b) (TLit l).
Proof.
  induction b; intros l0 q0.
  - cbn [Integrate]. eapply dsubd_tr with (b := Intersect (l0 :: (q0 ++ []))).
    + apply dsubd_dereliction.
    + apply dsubd_int_ll.
  - cbn [Integrate]. apply dsubda_bot.
  - cbn [Integrate]. apply dsubd_uni_l; [apply IHb1 | apply IHb2].
  - cbn [Integrate].
    apply dsubd_integrate_const with
      (g := fun l' => Integrate (fun l'' => intersect (l0 :: (q0 ++ (l' ++ l'')))) b2).
    intro l'.
    replace (Integrate (fun l'' => intersect (l0 :: (q0 ++ (l' ++ l'')))) b2)
      with (Integrate (fun l'' => intersect (l0 :: ((q0 ++ l') ++ l''))) b2).
    + apply IHb2.
    + apply Integrate_ext. intro y. rewrite (app_assoc q0 l' y). reflexivity.
  - cbn [Integrate]. eapply dsubd_tr with (b := Intersect (l0 :: (q0 ++ [l]))).
    + apply dsubd_dereliction.
    + apply dsubd_int_ll.
Qed.


Lemma isub_prefix_lit_of_conv :
  (forall x y : T, rsubf (@RPremise) x y -> rsubf (@IPremise) x y) ->
  forall (a : Lit) (q : list Lit),
    rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros Hconv a q.
  apply Hconv.
  pose proof (LiteralDereliction (a :: q)) as Hdel.
  destruct (rsubfR_int_r_inv _ _ _ Hdel) as [Hr _].
  exact Hr.
Qed.

Lemma R_intersect_mem_gen : forall (ls q : list Lit) (l : Lit),
  rsubf (@RPremise) (intersect ls) (Intersect q) ->
  In l q -> rsubf (@RPremise) (intersect ls) (TLit l).
Proof.
  intros ls q. induction q as [| b q IH]; intros l H Hin.
  - destruct Hin.
  - cbn [Intersect] in H.
    destruct (rsubfR_int_r_inv _ _ _ H) as [Hhead Htail].
    simpl in Hin. destruct Hin as [-> | Hin].
    + exact Hhead.
    + apply (IH l Htail Hin).
Qed.

Lemma R_intersect_mem_of_del : forall (ls : list Lit) (l : Lit),
  In l ls -> rsubf (@RPremise) (intersect ls) (TLit l).
Proof.
  intros ls l Hin. pose proof (LiteralDereliction ls) as Hdel.
  apply (R_intersect_mem_gen ls ls l Hdel Hin).
Qed.

Lemma isub_intersect_mem_of_conv :
  (forall x y : T, rsubf (@RPremise) x y -> rsubf (@IPremise) x y) ->
  forall (ls : list Lit) (l : Lit),
    In l ls -> rsubf (@IPremise) (intersect ls) (TLit l).
Proof.
  intros Hconv ls l Hin. apply Hconv. apply R_intersect_mem_of_del. exact Hin.
Qed.

Lemma isub_Intersect_of_mem :
  (forall x y : T, rsubf (@RPremise) x y -> rsubf (@IPremise) x y) ->
  forall (ls q : list Lit),
    (forall l : Lit, In l q -> rsubf (@IPremise) (intersect ls) (TLit l)) ->
    rsubf (@IPremise) (intersect ls) (Intersect q).
Proof.
  intros Hconv ls q. induction q as [| b q IH]; intros Hmem.
  - cbn [Intersect]. apply rsubf_IP_top.
  - cbn [Intersect]. apply rsubf_IP_int_r.
    + apply Hmem. left. reflexivity.
    + apply IH. intros l Hin. apply Hmem. right. exact Hin.
Qed.

Lemma isub_dereliction_of_conv :
  (forall x y : T, rsubf (@RPremise) x y -> rsubf (@IPremise) x y) ->
  forall ls : list Lit, rsubf (@IPremise) (intersect ls) (Intersect ls).
Proof.
  intros Hconv ls. apply (isub_Intersect_of_mem Hconv ls ls).
  intros l Hin. apply isub_intersect_mem_of_conv; [exact Hconv | exact Hin].
Qed.


Lemma isub_dereliction_of_lift :
  (forall x y : T, rsubf (@RPremise) x y ->
     rsubf (@IPremise) (Integrate intersect x) y) ->
  forall ls : list Lit, rsubf (@IPremise) (intersect ls) (Intersect ls).
Proof.
  intros Hlift ls. apply isub_dereliction_of_conv.
  intros x y Hr. apply (RP_to_IP_of_lift Hlift). exact Hr.
Qed.


Lemma isub_intersect_mem_of_lift :
  (forall x y : T, rsubf (@RPremise) x y ->
     rsubf (@IPremise) (Integrate intersect x) y) ->
  forall (ls : list Lit) (l : Lit),
    In l ls -> rsubf (@IPremise) (intersect ls) (TLit l).
Proof.
  intros Hlift ls l Hin. apply isub_intersect_mem_of_conv.
  intros x y Hr. apply (RP_to_IP_of_lift Hlift). exact Hr.
  exact Hin.
Qed.


Lemma isub_prefix_lit_of_lift :
  (forall x y : T, rsubf (@RPremise) x y ->
     rsubf (@IPremise) (Integrate intersect x) y) ->
  forall (a : Lit) (q : list Lit),
    rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros Hlift a q. apply isub_prefix_lit_of_conv.
  intros x y Hr. apply (RP_to_IP_of_lift Hlift). exact Hr.
Qed.


Lemma isub_Intersect_of_members :
  forall (ls q : list Lit),
    (forall l : Lit, In l q -> rsubf (@IPremise) (intersect ls) (TLit l)) ->
    rsubf (@IPremise) (intersect ls) (Intersect q).
Proof.
  intros ls q. induction q as [| b q IH]; intros Hmem.
  - cbn [Intersect]. apply rsubf_IP_top.
  - cbn [Intersect]. apply rsubf_IP_int_r.
    + apply Hmem. left. reflexivity.
    + apply IH. intros l Hin. apply Hmem. right. exact Hin.
Qed.


Lemma intersect_nil_not_bot_of_lit :
  forall (a d : Lit),
    intersect [a] = TLit d -> intersect [] <> TBot.
Proof.
  intros a d E Hbot.
  assert (Hint : intersected [d]).
  { pose proof (IntersectorIntegrated [a]) as Hi.
    rewrite E in Hi. cbn [Integrated] in Hi. exact Hi. }
  exact (promotion_bot_absurd [d] [] [] (Forall_nil _) (incl_nil_l [d]) Hint Hbot).
Qed.

Fixpoint BotLike (t : T) : Prop :=
  match t with
  | TBot => True
  | TUni a b => BotLike a /\ BotLike b
  | _ => False
  end.

Lemma rsubf_IP_botlike : forall t : T, BotLike t ->
  forall Y : T, rsubf (@IPremise) t Y.
Proof.
  induction t; intros H Y; cbn [BotLike] in H.
  - contradiction.
  - apply Rsubf. apply ui_bot.
  - destruct H as [Ha Hb]. apply Rsubf. apply ui_uni_l.
    + apply rsubf_uisub. apply IHt1. exact Ha.
    + apply rsubf_uisub. apply IHt2. exact Hb.
  - contradiction.
  - contradiction.
Qed.

Lemma Integrated_int_exists : forall (P : list Lit -> Prop) (t : T),
  Integrated_int P t -> exists ls, P ls.
Proof.
  intros P t. revert P. induction t; intros P H; cbn [Integrated_int] in H.
  - exists []. exact H.
  - exact (False_rect _ H).
  - exact (False_rect _ H).
  - apply (IHt1 (fun l => Integrated_int (fun l' => P (l ++ l')) t2)) in H.
    destruct H as [l Hl].
    apply (IHt2 (fun l' => P (l ++ l'))) in Hl.
    destruct Hl as [l' Hl'].
    exists (l ++ l'). exact Hl'.
  - exists [l]. exact H.
Qed.

Lemma Integrated_botlike_or_intersected : forall t : T,
  Integrated intersected t -> BotLike t \/ (exists ls, intersected ls).
Proof.
  intros t. induction t; intro H; cbn [Integrated] in H.
  - right. exists []. exact H.
  - left. exact I.
  - destruct H as [HA HB].
    destruct (IHt1 HA) as [B1 | [ls1 E1]];
    destruct (IHt2 HB) as [B2 | [ls2 E2]].
    + left. split; assumption.
    + right. exists ls2. exact E2.
    + right. exists ls1. exact E1.
    + right. exists ls1. exact E1.
  - right. apply (Integrated_int_exists intersected (TIsect t1 t2)). exact H.
  - right. exists [l]. exact H.
Qed.


Lemma Integrated_botlike : forall t : T,
  BotLike t -> Integrated intersected t.
Proof.
  induction t; intros H; cbn [BotLike] in H.
  - contradiction.
  - exact I.
  - destruct H as [Ha Hb]. split.
    + apply IHt1. exact Ha.
    + apply IHt2. exact Hb.
  - contradiction.
  - contradiction.
Qed.


Lemma BotLike_dec : forall t : T, {BotLike t} + {~ BotLike t}.
Proof.
  induction t; cbn [BotLike].
  - right. intro H. exact H.
  - left. exact I.
  - destruct IHt1 as [H1 | H1]; destruct IHt2 as [H2 | H2].
    + left. split; assumption.
    + right. intro H. apply H2. apply H.
    + right. intro H. apply H1. apply H.
    + right. intro H. apply H1. apply H.
  - right. intro H. exact H.
  - right. intro H. exact H.
Qed.


Lemma BotLike_TBot : BotLike TBot.
Proof. exact I. Qed.

Lemma BotLike_TUni : forall A B : T,
  BotLike A -> BotLike B -> BotLike (TUni A B).
Proof. intros A B HA HB. split; assumption. Qed.


Lemma intersect_botlike_or_intersected : forall ls : list Lit,
  BotLike (intersect ls) \/ (exists ls' : list Lit, intersected ls').
Proof.
  intro ls. apply Integrated_botlike_or_intersected. apply IntersectorIntegrated.
Qed.


Lemma isub_lit_botlike : forall a : Lit,
  BotLike (intersect [a]) -> rsubf (@IPremise) (intersect [a]) (TLit a).
Proof.
  intros a H. apply rsubf_IP_botlike. exact H.
Qed.


Lemma intersect_nil_not_bot_or_botlike : forall (a : Lit) (q : list Lit),
  BotLike (intersect (a :: q)) \/ intersect [] <> TBot.
Proof.
  intros a q. destruct (intersect_botlike_or_intersected (a :: q)) as [B | [ls E]].
  - left. exact B.
  - right. intro Hbot.
    exact (promotion_bot_absurd ls [] [] (Forall_nil _) (incl_nil_l ls) E Hbot).
Qed.


Lemma intersect_cons_not_isect_bot : forall (a : Lit) (q : list Lit) (B : T),
  intersect (a :: q) = TIsect TBot B -> False.
Proof.
  intros a q B E.
  pose proof (IntersectorIntegrated (a :: q)) as Hi.
  rewrite E in Hi. cbn [Integrated Integrated_int] in Hi. exact Hi.
Qed.

Lemma intersect_cons_not_isect_uni : forall (a : Lit) (q : list Lit) (A B : T),
  intersect (a :: q) = TIsect (TUni A B) B -> False.
Proof.
  intros a q A B E.
  pose proof (IntersectorIntegrated (a :: q)) as Hi.
  rewrite E in Hi. cbn [Integrated Integrated_int] in Hi. exact Hi.
Qed.


Lemma intersect_cons_not_isect_isect_bot :
  forall (a : Lit) (q : list Lit) (A B C : T),
    intersect (a :: q) = TIsect (TIsect TBot B) C -> False.
Proof.
  intros a q A B C E.
  pose proof (IntersectorIntegrated (a :: q)) as Hi.
  rewrite E in Hi. cbn [Integrated Integrated_int] in Hi. exact Hi.
Qed.


Lemma Integrated_int_not_bot : forall (P : list Lit -> Prop) (t : T),
  Integrated_int P t -> t <> TBot.
Proof. intros P t H E. subst t. cbn [Integrated_int] in H. exact H. Qed.

Lemma Integrated_int_not_uni : forall (P : list Lit -> Prop) (t : T) (A B : T),
  Integrated_int P t -> t <> TUni A B.
Proof. intros P t A B H E. subst t. cbn [Integrated_int] in H. exact H. Qed.


Lemma Integrated_int_isect_left_shape :
  forall (P : list Lit -> Prop) (A B : T),
    Integrated_int P (TIsect A B) ->
    A = TTop \/
    (exists A1 A2 : T, A = TIsect A1 A2) \/
    (exists l : Lit, A = TLit l).
Proof.
  intros P A B H. cbn [Integrated_int] in H.
  destruct A as [| | A1 A2 | A1 A2 | l].
  - left. reflexivity.
  - exfalso. apply (Integrated_int_not_bot _ _ H). reflexivity.
  - exfalso. apply (Integrated_int_not_uni _ _ A1 A2 H). reflexivity.
  - right. left. exists A1, A2. reflexivity.
  - right. right. exists l. reflexivity.
Qed.

Lemma intersect_cons_isect_left_shape :
  forall (a : Lit) (q : list Lit) (A B : T),
    intersect (a :: q) = TIsect A B ->
    A = TTop \/
    (exists A1 A2 : T, A = TIsect A1 A2) \/
    (exists l : Lit, A = TLit l).
Proof.
  intros a q A B E.
  pose proof (IntersectorIntegrated (a :: q)) as Hi.
  rewrite E in Hi.
  apply (Integrated_int_isect_left_shape intersected A B).
  exact Hi.
Qed.


Lemma Integrate_isect_top_l : forall (f : list Lit -> T) (B : T),
  Integrate f (TIsect TTop B) = Integrate f B.
Proof.
  intros f B. cbn [Integrate].
  apply Integrate_ext. intro l. rewrite app_nil_l. reflexivity.
Qed.


Lemma Integrate_isect_top_r : forall (f : list Lit -> T) (A : T),
  Integrate f (TIsect A TTop) = Integrate f A.
Proof.
  intros f A. cbn [Integrate].
  apply Integrate_ext. intro l. rewrite app_nil_r. reflexivity.
Qed.


Lemma Integrate_isect_bot_l : forall (f : list Lit -> T) (B : T),
  Integrate f (TIsect TBot B) = TBot.
Proof. intros f B. reflexivity. Qed.

Lemma Integrate_isect_uni_l : forall (f : list Lit -> T) (A C B : T),
  Integrate f (TIsect (TUni A C) B) =
  TUni (Integrate (fun l => Integrate (fun l' => f (l ++ l')) B) A)
       (Integrate (fun l => Integrate (fun l' => f (l ++ l')) B) C).
Proof. intros f A C B. reflexivity. Qed.


Lemma Integrated_int_leftmost : forall (P : list Lit -> Prop) (A : T),
  Integrated_int P A ->
  A = TTop \/ (exists l : Lit, A = TLit l) \/
  (exists A1 A2 : T, A = TIsect A1 A2).
Proof.
  intros P A H.
  destruct A as [| | A1 A2 | A1 A2 | l].
  - left. reflexivity.
  - exfalso. apply (Integrated_int_not_bot _ _ H). reflexivity.
  - exfalso. apply (Integrated_int_not_uni _ _ A1 A2 H). reflexivity.
  - right. right. exists A1, A2. reflexivity.
  - right. left. exists l. reflexivity.
Qed.


Lemma Integrated_uni_components : forall A B : T,
  Integrated intersected (TUni A B) ->
  Integrated intersected A /\ Integrated intersected B.
Proof. intros A B H. cbn [Integrated] in H. exact H. Qed.

Lemma Integrated_isect_int : forall A B : T,
  Integrated intersected (TIsect A B) ->
  Integrated_int intersected (TIsect A B).
Proof. intros A B H. cbn [Integrated] in H. exact H. Qed.


Lemma Integrated_int_top : forall P : list Lit -> Prop,
  Integrated_int P TTop -> P [].
Proof. intros P H. exact H. Qed.

Lemma Integrated_int_lit : forall (P : list Lit -> Prop) (l : Lit),
  Integrated_int P (TLit l) -> P [l].
Proof. intros P l H. exact H. Qed.

Lemma Integrated_int_isect_inv : forall (P : list Lit -> Prop) (A B : T),
  Integrated_int P (TIsect A B) ->
  Integrated_int (fun l => Integrated_int (fun l' => P (l ++ l')) B) A.
Proof. intros P A B H. cbn [Integrated_int] in H. exact H. Qed.


Lemma Integrated_int_leftmost_full : forall (P : list Lit -> Prop) (A : T),
  Integrated_int P A ->
  A = TTop \/ (exists l : Lit, A = TLit l) \/
  (exists A1 A2 : T, A = TIsect A1 A2 /\
     Integrated_int (fun l => Integrated_int (fun l' => P (l ++ l')) A2) A1).
Proof.
  intros P A H.
  destruct (Integrated_int_leftmost P A H) as [E | [[l E] | [A1 [A2 E]]]].
  - left. exact E.
  - right. left. exists l. exact E.
  - right. right. exists A1, A2. split.
    + exact E.
    + subst A. apply Integrated_int_isect_inv. exact H.
Qed.


Lemma Integrated_int_not_botlike : forall (P : list Lit -> Prop) (A : T),
  Integrated_int P A -> ~ BotLike A.
Proof.
  intros P A H HB.
  destruct A as [| | A1 A2 | A1 A2 | l]; cbn [BotLike] in HB.
  - exact HB.
  - cbn [Integrated_int] in H. exact H.
  - cbn [Integrated_int] in H. exact H.
  - exact HB.
  - exact HB.
Qed.


Lemma Integrated_top : Integrated intersected TTop <-> intersected [].
Proof. cbn [Integrated]. tauto. Qed.

Lemma Integrated_lit : forall l : Lit,
  Integrated intersected (TLit l) <-> intersected [l].
Proof. intro l. cbn [Integrated]. tauto. Qed.


Lemma Integrated_int_exists_isect : forall (P : list Lit -> Prop) (A B : T),
  Integrated_int P (TIsect A B) ->
  exists l l' : list Lit, P (l ++ l').
Proof.
  intros P A B H.
  pose proof (Integrated_int_isect_inv P A B H) as Hinv.
  destruct (Integrated_int_exists
    (fun l => Integrated_int (fun l' => P (l ++ l')) B) A Hinv) as [l Hl].
  destruct (Integrated_int_exists (fun l' => P (l ++ l')) B Hl) as [l' Hl'].
  exists l, l'. exact Hl'.
Qed.


Lemma intersect_cons_witness : forall (a : Lit) (q : list Lit),
  BotLike (intersect (a :: q)) \/
  (exists l l' : list Lit, intersected (l ++ l')).
Proof.
  intros a q. destruct (intersect_botlike_or_intersected (a :: q)) as [B | [ls E]].
  - left. exact B.
  - right. exists ls, []. rewrite app_nil_r. exact E.
Qed.


Lemma intersect_cons_botlike_or_intersected : forall (a : Lit) (q : list Lit),
  BotLike (intersect (a :: q)) \/ (exists ls : list Lit, intersected ls).
Proof. intros a q. apply intersect_botlike_or_intersected. Qed.

Lemma Integrate_bot_or_uni : forall (f : list Lit -> T) (A : T),
  (forall l : list Lit, f l = TBot \/ (exists X Y : T, f l = TUni X Y)) ->
  Integrate f A = TBot \/ (exists U V : T, Integrate f A = TUni U V).
Proof.
  intros f A. revert f. induction A as [| | A1 IH1 A2 IH2 | A1 IH1 A2 IH2 | l];
    intros f Hf.
  - cbn [Integrate]. destruct (Hf []) as [E | [X [Y E]]].
    + left. exact E.
    + right. exists X, Y. exact E.
  - cbn [Integrate]. left. reflexivity.
  - cbn [Integrate]. right. exists (Integrate f A1), (Integrate f A2). reflexivity.
  - cbn [Integrate].
    assert (Hg : forall l : list Lit,
      Integrate (fun l' => f (l ++ l')) A2 = TBot \/
      (exists X Y : T, Integrate (fun l' => f (l ++ l')) A2 = TUni X Y)).
    { intro l. apply IH2. intro l'. apply Hf. }
    apply IH1. exact Hg.
  - cbn [Integrate]. apply Hf.
Qed.


Lemma I_isect_uni_bot_or_uni : forall A B C : T,
  Integrate intersect (TIsect A (TUni B C)) = TBot \/
  (exists U V : T,
     Integrate intersect (TIsect A (TUni B C)) = TUni U V).
Proof.
  intros A B C. cbn [Integrate].
  apply Integrate_bot_or_uni. intro l. right.
  exists (Integrate (fun l' => intersect (l ++ l')) B),
         (Integrate (fun l' => intersect (l ++ l')) C).
  reflexivity.
Qed.


Lemma Integrate_uni_pair_bot_or_uni :
  forall (fB fC : list Lit -> T) (A : T),
    Integrate (fun l => TUni (fB l) (fC l)) A = TBot \/
    (exists U V : T,
       Integrate (fun l => TUni (fB l) (fC l)) A = TUni U V).
Proof.
  intros fB fC A. apply Integrate_bot_or_uni. intro l. right.
  exists (fB l), (fC l). reflexivity.
Qed.


Lemma dsubd_to_esub : forall X Y : T, dsubd X Y -> esub X Y.
Proof.
  intros X Y H. eapply dsubda_mono; [| exact H].
  intros p q Hf. destruct Hf.
Qed.


Lemma dsub_to_dsubd : forall X Y : T, dsub X Y -> dsubd X Y.
Proof. intros X Y H. apply dsuba_dsubda. exact H. Qed.


Lemma dsub_to_esub : forall X Y : T, dsub X Y -> esub X Y.
Proof.
  intros X Y H. apply dsubd_to_esub. apply dsub_to_dsubd. exact H.
Qed.


Lemma Integrated_uni_botlike_or_intersected : forall A B : T,
  Integrated intersected (TUni A B) ->
  (BotLike A \/ (exists ls : list Lit, intersected ls)) /\
  (BotLike B \/ (exists ls : list Lit, intersected ls)).
Proof.
  intros A B H. apply Integrated_uni_components in H. destruct H as [HA HB].
  split; apply Integrated_botlike_or_intersected; assumption.
Qed.


Lemma Integrated_isect_exists_intersected : forall A B : T,
  Integrated intersected (TIsect A B) ->
  exists ls : list Lit, intersected ls.
Proof.
  intros A B H.
  destruct (Integrated_botlike_or_intersected (TIsect A B) H) as [HB | [ls E]].
  - cbn [BotLike] in HB. exact (False_rect _ HB).
  - exists ls. exact E.
Qed.


Lemma intersect_cons_not_botlike_exists :
  forall (a : Lit) (q : list Lit),
    ~ BotLike (intersect (a :: q)) -> exists ls : list Lit, intersected ls.
Proof.
  intros a q H.
  destruct (intersect_botlike_or_intersected (a :: q)) as [B | [ls E]].
  - exfalso. apply H. exact B.
  - exists ls. exact E.
Qed.


Lemma intersect_cons_nil_not_bot_of_not_botlike :
  forall (a : Lit) (q : list Lit),
    ~ BotLike (intersect (a :: q)) -> intersect [] <> TBot.
Proof.
  intros a q H.
  destruct (intersect_cons_not_botlike_exists a q H) as [ls E].
  intro Hbot.
  exact (promotion_bot_absurd ls [] [] (Forall_nil _) (incl_nil_l ls) E Hbot).
Qed.


Lemma isub_cons_botlike : forall (a : Lit) (q : list Lit),
  BotLike (intersect (a :: q)) ->
  rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros a q H. apply rsubf_IP_botlike. exact H.
Qed.


Lemma isub_cons_top : forall (a : Lit) (q : list Lit),
  rsubf (@IPremise) (intersect (a :: q)) TTop.
Proof. intros a q. apply Rsubf. apply ui_top. Qed.


Lemma isub_cons_bot : forall (a : Lit) (q : list Lit) (Y : T),
  intersect (a :: q) = TBot ->
  rsubf (@IPremise) (intersect (a :: q)) Y.
Proof.
  intros a q Y E. rewrite E. apply Rsubf. apply ui_bot.
Qed.


Lemma isub_cons_uni_branch : forall (a : Lit) (q : list Lit) (A B : T),
  intersect (a :: q) = TUni A B ->
  rsubf (@IPremise) A (TLit a) ->
  rsubf (@IPremise) B (TLit a) ->
  rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros a q A B E HA HB.
  rewrite E. apply Rsubf. apply ui_uni_l;
    [apply rsubf_uisub; exact HA | apply rsubf_uisub; exact HB].
Qed.

Lemma isub_cons_isect_branch : forall (a : Lit) (q : list Lit) (A B : T),
  intersect (a :: q) = TIsect A B ->
  (rsubf (@IPremise) A (TLit a) \/ rsubf (@IPremise) B (TLit a)) ->
  rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros a q A B E [HA | HB].
  - rewrite E. apply Rsubf. apply ui_int_ll. apply rsubf_uisub. exact HA.
  - rewrite E. apply Rsubf. apply ui_int_lr. apply rsubf_uisub. exact HB.
Qed.


Lemma conv_to_lit_component : forall (A : T) (a : Lit),
  clos_refl_trans M mlt (m A (TLit a)) (m (TLit a) (TLit a)) ->
  (forall x y : T, ord (x,y) (TLit a, TLit a) -> esub x y ->
     rsubf (@IPremise) (Integrate intersect x) y) ->
  rsubf (@RPremise) A (TLit a) ->
  rsubf (@IPremise) A (TLit a).
Proof.
  intros A a Hbound IHmain Hr. eapply conv_to_lit; eauto.
Qed.



Lemma isub_cons_lit_branch : forall (a d : Lit) (q : list Lit),
  intersect (a :: q) = TLit d ->
  rsubf (@IPremise) (TLit d) (TLit a) ->
  rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros a d q E H. rewrite E. exact H.
Qed.


Lemma isub_cons_top_branch : forall (a : Lit) (q : list Lit),
  intersect (a :: q) = TTop ->
  rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros a q E. exfalso. eapply intersect_cons_not_top. exact E.
Qed.


Lemma isub_cons_of_components : forall (a : Lit) (q : list Lit),
  (forall A B : T, intersect (a :: q) = TUni A B ->
     rsubf (@IPremise) A (TLit a) /\ rsubf (@IPremise) B (TLit a)) ->
  (forall A B : T, intersect (a :: q) = TIsect A B ->
     rsubf (@IPremise) A (TLit a) \/ rsubf (@IPremise) B (TLit a)) ->
  (forall d : Lit, intersect (a :: q) = TLit d ->
     rsubf (@IPremise) (TLit d) (TLit a)) ->
  rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros a q HUni HIsect HLit.
  destruct (intersect (a :: q)) as [| | A B | A B | d] eqn:E.
  - exfalso. eapply intersect_cons_not_top. exact E.
  - apply Rsubf. apply ui_bot.
  - destruct (HUni A B eq_refl) as [HA HB].
    apply Rsubf. apply ui_uni_l;
      [apply rsubf_uisub; exact HA | apply rsubf_uisub; exact HB].
  - destruct (HIsect A B eq_refl) as [HA | HB].
    + apply Rsubf. apply ui_int_ll. apply rsubf_uisub. exact HA.
    + apply Rsubf. apply ui_int_lr. apply rsubf_uisub. exact HB.
  - exact (HLit d eq_refl).
Qed.


Lemma m_uni_l_component_le : forall (A B tr : T),
  clos_refl_trans M mlt (m A tr) (m (TUni A B) tr).
Proof.
  intros A B tr. apply m_ui_l with (tl := A) (tl' := TUni A B). apply sub_uni_l.
Qed.

Lemma m_isect_l_component_le : forall (A B tr : T),
  clos_refl_trans M mlt (m A tr) (m (TIsect A B) tr).
Proof.
  intros A B tr. apply m_ui_l with (tl := A) (tl' := TIsect A B). apply sub_isect_l.
Qed.


Lemma m_uni_r_component_le : forall (A B tr : T),
  clos_refl_trans M mlt (m A tr) (m (TUni B A) tr).
Proof.
  intros A B tr. apply m_ui_l with (tl := A) (tl' := TUni B A). apply sub_uni_r.
Qed.

Lemma m_isect_r_component_le : forall (A B tr : T),
  clos_refl_trans M mlt (m A tr) (m (TIsect B A) tr).
Proof.
  intros A B tr. apply m_ui_l with (tl := A) (tl' := TIsect B A). apply sub_isect_r.
Qed.


Lemma m_lit_le_isect_cons : forall (a : Lit) (q : list Lit) (tr : T),
  clos_refl_trans M mlt (m (TLit a) tr)
    (m (TIsect (TLit a) (Intersect q)) tr).
Proof.
  intros a q tr. apply m_isect_l_component_le.
Qed.


Lemma I_isect_cons : forall (a : Lit) (q : list Lit),
  Integrate intersect (TIsect (TLit a) (Intersect q)) = intersect (a :: q).
Proof.
  intros a q.
  change (Integrate intersect (Intersect (a :: q)) = intersect (a :: q)).
  apply Integrate_Intersect.
Qed.

Lemma m_intersect_cons_le : forall (a : Lit) (q : list Lit) (tr : T),
  clos_refl_trans M mlt (m (intersect (a :: q)) tr)
    (m (TIsect (TLit a) (Intersect q)) tr).
Proof.
  intros a q tr. rewrite <- I_isect_cons. apply MeasurePreservation.
Qed.


Lemma m_intersect_singleton_le : forall (a : Lit) (tr : T),
  clos_refl_trans M mlt (m (intersect [a]) tr) (m (TLit a) tr).
Proof.
  intros a tr.
  change (clos_refl_trans M mlt (m (Integrate intersect (TLit a)) tr) (m (TLit a) tr)).
  apply MeasurePreservation.
Qed.


Lemma R_cons_uni_components : forall (a : Lit) (q : list Lit) (A B : T),
  intersect (a :: q) = TUni A B ->
  rsubf (@RPremise) A (TLit a) /\ rsubf (@RPremise) B (TLit a).
Proof.
  intros a q A B E.
  pose proof (LiteralDereliction (a :: q)) as Hdel.
  rewrite E in Hdel.
  cbn [Intersect fold_right] in Hdel.
  destruct (rsubfR_int_r_inv _ _ _ Hdel) as [Hlit _].
  inversion Hlit as [U V Hu]; subst.
  inversion Hu; subst.
  split; apply Rsubf; assumption.
Qed.


Lemma R_cons_isect_components : forall (a : Lit) (q : list Lit) (A B : T),
  intersect (a :: q) = TIsect A B ->
  rsubf (@RPremise) A (TLit a) \/ rsubf (@RPremise) B (TLit a).
Proof.
  intros a q A B E.
  pose proof (LiteralDereliction (a :: q)) as Hdel.
  rewrite E in Hdel.
  cbn [Intersect fold_right] in Hdel.
  destruct (rsubfR_int_r_inv _ _ _ Hdel) as [Hlit _].
  inversion Hlit as [U V Hu]; subst.
  inversion Hu; subst.
  - left. apply Rsubf. assumption.
  - right. apply Rsubf. assumption.
Qed.

Lemma R_cons_lit_component : forall (a : Lit) (q : list Lit) (d : Lit),
  intersect (a :: q) = TLit d ->
  rsubf (@RPremise) (TLit d) (TLit a).
Proof.
  intros a q d E.
  pose proof (LiteralDereliction (a :: q)) as Hdel.
  rewrite E in Hdel.
  cbn [Intersect fold_right] in Hdel.
  destruct (rsubfR_int_r_inv _ _ _ Hdel) as [Hlit _].
  exact Hlit.
Qed.


Lemma isub_cons_of_conv :
  (forall x y : T, rsubf (@RPremise) x y -> rsubf (@IPremise) x y) ->
  forall (a : Lit) (q : list Lit),
    rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros Hconv a q.
  apply (isub_cons_of_components a q).
  - intros A B E.
    destruct (R_cons_uni_components a q A B E) as [HA HB].
    split; apply Hconv; assumption.
  - intros A B E.
    destruct (R_cons_isect_components a q A B E) as [HA | HB].
    + left. apply Hconv. exact HA.
    + right. apply Hconv. exact HB.
  - intros d E. apply Hconv. apply (R_cons_lit_component a q d E).
Qed.


Lemma isub_cons_of_lift :
  (forall x y : T, rsubf (@RPremise) x y ->
     rsubf (@IPremise) (Integrate intersect x) y) ->
  forall (a : Lit) (q : list Lit),
    rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros Hlift a q. apply isub_cons_of_conv.
  intros x y Hr. apply (RP_to_IP_of_lift Hlift). exact Hr.
Qed.


Lemma isub_prefix_lit_of_mem_of_lift :
  (forall x y : T, rsubf (@RPremise) x y ->
     rsubf (@IPremise) (Integrate intersect x) y) ->
  forall (b : T) (l : Lit) (q : list Lit),
    rsubf (@IPremise)
      (Integrate (fun l' => intersect (l :: (q ++ l'))) b) (TLit l).
Proof.
  intros Hlift b l q. apply isub_prefix_lit_of_mem.
  intros a q0. apply isub_cons_of_lift. exact Hlift.
Qed.


Lemma isub_lit_trans_of_main :
  (forall x y : T, esub x y -> rsubf (@IPremise) (Integrate intersect x) y) ->
  forall (a b c : Lit),
    rsubf (@IPremise) (TLit a) (TLit b) ->
    rsubf (@IPremise) (TLit b) (TLit c) ->
    rsubf (@IPremise) (TLit a) (TLit c).
Proof.
  intros Hmain a b c H1 H2.
  apply (isub_lit_trans_of_IH a b c).
  - intros x y Hord He. apply Hmain. exact He.
  - exact H1.
  - exact H2.
Qed.


Lemma refl_IP_TBot : rsubf (@IPremise) TBot TBot.
Proof. apply Rsubf. apply ui_bot. Qed.

Lemma refl_IP_TTop : rsubf (@IPremise) TTop TTop.
Proof. apply Rsubf. apply ui_top. Qed.


Lemma refl_IP_TUni : forall A B : T,
  rsubf (@IPremise) A A -> rsubf (@IPremise) B B ->
  rsubf (@IPremise) (TUni A B) (TUni A B).
Proof.
  intros A B HA HB. apply Rsubf. apply ui_uni_l.
  - apply ui_uni_rl. apply rsubf_uisub. exact HA.
  - apply ui_uni_rr. apply rsubf_uisub. exact HB.
Qed.

Lemma refl_IP_TIsect : forall A B : T,
  rsubf (@IPremise) A A -> rsubf (@IPremise) B B ->
  rsubf (@IPremise) (TIsect A B) (TIsect A B).
Proof.
  intros A B HA HB. apply Rsubf. apply ui_int_r.
  - apply ui_int_ll. apply rsubf_uisub. exact HA.
  - apply ui_int_lr. apply rsubf_uisub. exact HB.
Qed.


Lemma refl_IP_of_lit :
  (forall l : Lit, rsubf (@IPremise) (TLit l) (TLit l)) ->
  forall t : T, rsubf (@IPremise) t t.
Proof.
  intros Hlit t. induction t as [| | A B IHA IHB | A B IHA IHB | l].
  - apply refl_IP_TTop.
  - apply refl_IP_TBot.
  - apply refl_IP_TUni; assumption.
  - apply refl_IP_TIsect; assumption.
  - apply Hlit.
Qed.


Lemma refl_IP_lit_of_main :
  (forall x : T, esub x x -> rsubf (@IPremise) (Integrate intersect x) x) ->
  forall l : Lit, rsubf (@IPremise) (TLit l) (TLit l).
Proof.
  intros Hmain l.
  destruct (LiteralReflexivity l) as [r Hdiag].
  apply Rsubf. apply ui_lit. exists r.
  intros tl tr Hip. destruct Hip as [x y Hrp].
  assert (Heq : x = y) by (apply Hdiag; exact Hrp). subst y.
  apply Hmain. apply dsubda_refl.
Qed.


Lemma refl_IP_of_main :
  (forall x : T, esub x x -> rsubf (@IPremise) (Integrate intersect x) x) ->
  forall t : T, rsubf (@IPremise) t t.
Proof.
  intros Hmain t. apply refl_IP_of_lit.
  intros l. apply refl_IP_lit_of_main. exact Hmain.
Qed.


Lemma refl_IP_lit_of_IH : forall l : Lit,
  (forall x : T, ord (x,x) (TLit l, TLit l) -> esub x x ->
     rsubf (@IPremise) (Integrate intersect x) x) ->
  rsubf (@IPremise) (TLit l) (TLit l).
Proof.
  intros l HIH.
  destruct (LiteralReflexivity l) as [r Hdiag].
  apply Rsubf. apply ui_lit. exists r.
  intros tl tr Hip. destruct Hip as [x y Hrp].
  assert (Heq : x = y) by (apply Hdiag; exact Hrp). subst y.
  apply HIH.
  - unfold ord, mval, sval. cbn [fst snd]. apply left_slex.
    apply t_step. apply (m_lit r). exact Hrp.
  - apply dsubda_refl.
Qed.





Lemma refl_isub_of_main :
  (forall x y : T, esub x y -> rsubf (@IPremise) (Integrate intersect x) y) ->
  forall t : T, rsubf (@IPremise) (Integrate intersect t) t.
Proof.
  intros Hmain t. apply Hmain. apply dsubda_refl.
Qed.


Lemma isub_cons_isect_lit_left_of_IH : forall (a : Lit) (q : list Lit) (B : T),
  intersect (a :: q) = TIsect (TLit a) B ->
  (forall x : T, ord (x,x) (TLit a, TLit a) -> esub x x ->
     rsubf (@IPremise) (Integrate intersect x) x) ->
  rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros a q B E IH.
  apply isub_cons_isect_branch with (A := TLit a) (B := B).
  - exact E.
  - left. apply refl_IP_lit_of_IH. exact IH.
Qed.


Lemma isub_cons_uni_lit_left_of_IH : forall (a : Lit) (q : list Lit) (B : T),
  intersect (a :: q) = TUni (TLit a) B ->
  (forall x : T, ord (x,x) (TLit a, TLit a) -> esub x x ->
     rsubf (@IPremise) (Integrate intersect x) x) ->
  rsubf (@IPremise) B (TLit a) ->
  rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros a q B E IH HB.
  apply isub_cons_uni_branch with (A := TLit a) (B := B).
  - exact E.
  - apply refl_IP_lit_of_IH. exact IH.
  - exact HB.
Qed.


Lemma isub_cons_isect_lit_right_of_IH : forall (a : Lit) (q : list Lit) (A : T),
  intersect (a :: q) = TIsect A (TLit a) ->
  (forall x : T, ord (x,x) (TLit a, TLit a) -> esub x x ->
     rsubf (@IPremise) (Integrate intersect x) x) ->
  rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros a q A E IH.
  apply isub_cons_isect_branch with (A := A) (B := TLit a).
  - exact E.
  - right. apply refl_IP_lit_of_IH. exact IH.
Qed.


Lemma isub_cons_uni_lit_right_of_IH : forall (a : Lit) (q : list Lit) (A : T),
  intersect (a :: q) = TUni A (TLit a) ->
  (forall x : T, ord (x,x) (TLit a, TLit a) -> esub x x ->
     rsubf (@IPremise) (Integrate intersect x) x) ->
  rsubf (@IPremise) A (TLit a) ->
  rsubf (@IPremise) (intersect (a :: q)) (TLit a).
Proof.
  intros a q A E IH HA.
  apply isub_cons_uni_branch with (A := A) (B := TLit a).
  - exact E.
  - exact HA.
  - apply refl_IP_lit_of_IH. exact IH.
Qed.


Definition lit_not_bot (l : Lit) (E : (TLit l : T) = (TBot : T)) : False :=
  match E in (_ = Y) return (match Y with TBot => False | _ => True end) with
  | eq_refl => I
  end.
Definition top_not_bot (E : (TTop : T) = (TBot : T)) : False :=
  match E in (_ = Y) return (match Y with TBot => False | _ => True end) with
  | eq_refl => I
  end.
Definition uni_not_bot (A B : T) (E : (TUni A B : T) = (TBot : T)) : False :=
  match E in (_ = Y) return (match Y with TBot => False | _ => True end) with
  | eq_refl => I
  end.
Definition isect_not_bot (A B : T) (E : (TIsect A B : T) = (TBot : T)) : False :=
  match E in (_ = Y) return (match Y with TBot => False | _ => True end) with
  | eq_refl => I
  end.

Fixpoint uisub_target_bot_elim (U V : T)
  (Hu : uisub (lsub (@RPremise) (rsubf (@RPremise))) U V) {struct Hu} :
  V = TBot -> forall Z : T, rsubf (@RPremise) U Z :=
  match Hu in uisub _ U' V' return V' = TBot -> forall Z : T, rsubf (@RPremise) U' Z with
  | ui_lit ll lr Hl => fun E => False_rect _ (lit_not_bot lr E)
  | ui_top tl => fun E => False_rect _ (top_not_bot E)
  | ui_int_ll il ir tr Hp => fun E Z =>
      @Rsubf Lit RRule (@RPremise) (TIsect il ir) Z
        (ui_int_ll il ir Z (@rsubf_uisub (@RPremise) il Z (uisub_target_bot_elim il tr Hp E Z)))
  | ui_int_lr il ir tr Hp => fun E Z =>
      @Rsubf Lit RRule (@RPremise) (TIsect il ir) Z
        (ui_int_lr il ir Z (@rsubf_uisub (@RPremise) ir Z (uisub_target_bot_elim ir tr Hp E Z)))
  | ui_int_r tl il ir Hpl Hpr => fun E => False_rect _ (isect_not_bot il ir E)
  | ui_bot tr => fun E Z => @Rsubf Lit RRule (@RPremise) TBot Z (ui_bot Z)
  | ui_uni_l ul ur tr Hpl Hpr => fun E Z =>
      @Rsubf Lit RRule (@RPremise) (TUni ul ur) Z
        (ui_uni_l ul ur Z
          (@rsubf_uisub (@RPremise) ul Z (uisub_target_bot_elim ul tr Hpl E Z))
          (@rsubf_uisub (@RPremise) ur Z (uisub_target_bot_elim ur tr Hpr E Z)))
  | ui_uni_rl tl ul ur Hp => fun E => False_rect _ (uni_not_bot ul ur E)
  | ui_uni_rr tl ul ur Hp => fun E => False_rect _ (uni_not_bot ul ur E)
  end.

Definition rsubf_target_bot_elim (X : T) (H : rsubf (@RPremise) X TBot) :
  forall Z : T, rsubf (@RPremise) X Z :=
  match H in @rsubf _ _ _ X' V'
        return (V' = TBot -> forall Z : T, rsubf (@RPremise) X' Z) with
  | @Rsubf _ _ _ tl tr Hu => fun E => uisub_target_bot_elim tl tr Hu E
  end eq_refl.

Lemma rsubam_RP_elim_of_trans :
  (forall X Y Z : T, rsubf (@RPremise) X Y -> rsubf (@RPremise) Y Z ->
     rsubf (@RPremise) X Z) ->
  forall (A : T -> T -> Prop) (X Y : T),
    rsubam (@RPremise) A X Y ->
    (forall p q : T, A p q -> rsubf (@RPremise) p q) ->
    rsubf (@RPremise) X Y.
Proof.
  intros Htrans A X Y H.
  induction H as [tl tr HAss
    | tl tl' tr' tr Hl Hmid IHmid Hr
    | ll lr r Hprem IHprem
    | tl
    | il ir tr Hprem IHprem
    | il ir tr Hprem IHprem
    | tl il ir Hpl IHpl Hpr IHpr
    | tr
    | tl ul ur Hprem IHprem
    | tl ul ur Hprem IHprem
    | ul ur tr Hpl IHpl Hpr IHpr]; intro HA.
  - apply HA. exact HAss.
  - eapply Htrans; [exact Hl |].
    eapply Htrans; [apply IHmid; exact HA | exact Hr].
  - apply Rsubf. apply ui_lit. exists r. intros pl pr Hp.
    apply IHprem; [exact Hp | exact HA].
  - apply Rsubf. apply ui_top.
  - apply Rsubf. apply ui_int_ll. apply rsubf_uisub. apply IHprem. exact HA.
  - apply Rsubf. apply ui_int_lr. apply rsubf_uisub. apply IHprem. exact HA.
  - apply Rsubf. apply ui_int_r.
    + apply rsubf_uisub. apply IHpl. exact HA.
    + apply rsubf_uisub. apply IHpr. exact HA.
  - apply Rsubf. apply ui_bot.
  - apply Rsubf. apply ui_uni_rl. apply rsubf_uisub. apply IHprem. exact HA.
  - apply Rsubf. apply ui_uni_rr. apply rsubf_uisub. apply IHprem. exact HA.
  - apply Rsubf. apply ui_uni_l.
    + apply rsubf_uisub. apply IHpl. exact HA.
    + apply rsubf_uisub. apply IHpr. exact HA.
Qed.

Definition rsubf_uisub_dep (X Y : T) (H : rsubf (@RPremise) X Y) :
  uisub (lsub (@RPremise) (rsubf (@RPremise))) X Y :=
  match H in @rsubf _ _ _ X' Y'
        return @uisub Lit (@lsub Lit RRule (@RPremise) (@rsubf Lit RRule (@RPremise))) X' Y' with
  | @Rsubf _ _ _ tl tr Hu => Hu
  end.

Definition RPlitcomp : Prop :=
  forall (a b c : Lit) (r1 : RRule a b) (r2 : RRule b c),
    (forall p q : T, RPremise r1 p q -> rsubf (@RPremise) p q) ->
    (forall p q : T, RPremise r2 p q -> rsubf (@RPremise) p q) ->
    exists r : RRule a c,
      forall p q : T, RPremise r p q -> rsubf (@RPremise) p q.

Lemma rsubf_RP_lit_right_of_rule :
  RPlitcomp ->
  forall (ll lr : Lit) (r2 : RRule ll lr),
    (forall p q : T, RPremise r2 p q -> rsubf (@RPremise) p q) ->
    forall X : T, rsubf (@RPremise) X (TLit ll) ->
      rsubf (@RPremise) X (TLit lr).
Proof.
  intros Hcomp ll lr r2 H2prem X0 HX.
  pose proof (rsubf_uisub_dep X0 (TLit ll) HX) as Hu.
  refine ((@uisub_ind Lit
      (@lsub Lit RRule (@RPremise) (@rsubf Lit RRule (@RPremise)))
      (fun X Y => Y = TLit ll -> rsubf (@RPremise) X (TLit lr))
      _ _ _ _ _ _ _ _ _ X0 (TLit ll) Hu) eq_refl).
  - (* ui_lit *) intros ll0 lr0 Hl E. injection E as <-.
    destruct Hl as [r1 H1prem].
    destruct (Hcomp ll0 lr0 lr r1 r2 H1prem H2prem) as [r Hr].
    apply Rsubf. apply ui_lit. exists r. exact Hr.
  - (* ui_top *) intros tl E. discriminate E.
  - (* ui_int_ll *) intros il ir tr Hp IHp E.
    apply Rsubf. apply ui_int_ll. apply rsubf_uisub. apply IHp. exact E.
  - (* ui_int_lr *) intros il ir tr Hp IHp E.
    apply Rsubf. apply ui_int_lr. apply rsubf_uisub. apply IHp. exact E.
  - (* ui_int_r *) intros tl il ir Hp IHp Hq IHg E. discriminate E.
  - (* ui_bot *) intros tr E. apply Rsubf. apply ui_bot.
  - (* ui_uni_rl *) intros tl ul ur Hp IHp E. discriminate E.
  - (* ui_uni_rr *) intros tl ul ur Hp IHp E. discriminate E.
  - (* ui_uni_l *) intros ul ur tr Hp IHp Hq IHg E.
    apply Rsubf. apply ui_uni_l.
    + apply rsubf_uisub. apply IHp. exact E.
    + apply rsubf_uisub. apply IHg. exact E.
Qed.

Lemma rsubf_RP_union_elim :
  forall (U V Z : T),
    (forall X : T, rsubf (@RPremise) X U -> rsubf (@RPremise) X Z) ->
    (forall X : T, rsubf (@RPremise) X V -> rsubf (@RPremise) X Z) ->
    forall X : T, rsubf (@RPremise) X (TUni U V) -> rsubf (@RPremise) X Z.
Proof.
  intros U V Z CU CV X0 HX.
  pose proof (rsubf_uisub_dep X0 (TUni U V) HX) as Hu.
  refine ((@uisub_ind Lit
      (@lsub Lit RRule (@RPremise) (@rsubf Lit RRule (@RPremise)))
      (fun X Y => Y = TUni U V ->
         (forall X : T, rsubf (@RPremise) X U -> rsubf (@RPremise) X Z) ->
         (forall X : T, rsubf (@RPremise) X V -> rsubf (@RPremise) X Z) ->
         rsubf (@RPremise) X Z)
      _ _ _ _ _ _ _ _ _ X0 (TUni U V) Hu) eq_refl CU CV).
  - (* ui_lit *) intros ll lr Hl E CU0 CV0. discriminate E.
  - (* ui_top *) intros tl E CU0 CV0. discriminate E.
  - (* ui_int_ll *) intros il ir tr Hp IHp E CU0 CV0.
    apply Rsubf. apply ui_int_ll. apply rsubf_uisub.
    apply IHp; [exact E | exact CU0 | exact CV0].
  - (* ui_int_lr *) intros il ir tr Hp IHp E CU0 CV0.
    apply Rsubf. apply ui_int_lr. apply rsubf_uisub.
    apply IHp; [exact E | exact CU0 | exact CV0].
  - (* ui_int_r *) intros tl il ir Hp IHp Hq IHg E CU0 CV0. discriminate E.
  - (* ui_bot *) intros tr E CU0 CV0. apply Rsubf. apply ui_bot.
  - (* ui_uni_rl *) intros tl ul ur Hp IHp E CU0 CV0.
    injection E as <- <-. apply CU0. apply Rsubf. exact Hp.
  - (* ui_uni_rr *) intros tl ul ur Hp IHp E CU0 CV0.
    injection E as <- <-. apply CV0. apply Rsubf. exact Hp.
  - (* ui_uni_l *) intros ul ur tr Hp IHp Hq IHg E CU0 CV0.
    apply Rsubf. apply ui_uni_l.
    + apply rsubf_uisub. apply IHp; [exact E | exact CU0 | exact CV0].
    + apply rsubf_uisub. apply IHg; [exact E | exact CU0 | exact CV0].
Qed.

Lemma rsubf_RP_right_comp :
  RPlitcomp ->
  forall Y Z : T, rsubf (@RPremise) Y Z ->
    forall X : T, rsubf (@RPremise) X Y -> rsubf (@RPremise) X Z.
Proof.
  intros Hcomp Y Z H2.
  induction H2 as [Y0 Z0 Hu].
  induction Hu; intros X HX.
  - (* ui_lit *) destruct H as [r2 H2prem].
    apply (rsubf_RP_lit_right_of_rule Hcomp ll lr r2 H2prem X).
    exact HX.
  - (* ui_top *) apply Rsubf. apply ui_top.
  - (* ui_int_ll *)
    destruct (rsubfR_int_r_inv X il ir HX) as [HXil _].
    apply IHHu. exact HXil.
  - (* ui_int_lr *)
    destruct (rsubfR_int_r_inv X il ir HX) as [_ HXir].
    apply IHHu. exact HXir.
  - (* ui_int_r *)
    apply Rsubf. apply ui_int_r.
    + apply rsubf_uisub. apply IHHu1. exact HX.
    + apply rsubf_uisub. apply IHHu2. exact HX.
  - (* ui_bot *)
    apply (rsubf_target_bot_elim X HX).
  - (* ui_uni_rl *)
    apply Rsubf. apply ui_uni_rl.
    apply rsubf_uisub. apply IHHu. exact HX.
  - (* ui_uni_rr *)
    apply Rsubf. apply ui_uni_rr.
    apply rsubf_uisub. apply IHHu. exact HX.
  - (* ui_uni_l *)
    exact (rsubf_RP_union_elim ul ur tr IHHu1 IHHu2 X HX).
Qed.

Lemma rsubf_RP_trans_of_litcomp :
  RPlitcomp ->
  forall X Y Z : T,
    rsubf (@RPremise) X Y -> rsubf (@RPremise) Y Z ->
      rsubf (@RPremise) X Z.
Proof.
  intros Hcomp X Y Z H1 H2.
  exact (rsubf_RP_right_comp Hcomp Y Z H2 X H1).
Qed.



Definition rsubf_IP_uisub_dep (X Y : T) (H : rsubf (@IPremise) X Y) :
  uisub (lsub (@IPremise) (rsubf (@IPremise))) X Y :=
  match H in @rsubf _ _ _ X' Y'
        return @uisub Lit (@lsub Lit RRule (@IPremise) (@rsubf Lit RRule (@IPremise))) X' Y' with
  | @Rsubf _ _ _ tl tr Hu => Hu
  end.

Lemma rsubf_IP_union_elim :
  forall (U V Z : T),
    (forall X : T, rsubf (@IPremise) X U -> rsubf (@IPremise) X Z) ->
    (forall X : T, rsubf (@IPremise) X V -> rsubf (@IPremise) X Z) ->
    forall X : T, rsubf (@IPremise) X (TUni U V) -> rsubf (@IPremise) X Z.
Proof.
  intros U V Z CU CV X0 HX.
  pose proof (rsubf_IP_uisub_dep X0 (TUni U V) HX) as Hu.
  refine ((@uisub_ind Lit
      (@lsub Lit RRule (@IPremise) (@rsubf Lit RRule (@IPremise)))
      (fun X Y => Y = TUni U V ->
         (forall X : T, rsubf (@IPremise) X U -> rsubf (@IPremise) X Z) ->
         (forall X : T, rsubf (@IPremise) X V -> rsubf (@IPremise) X Z) ->
         rsubf (@IPremise) X Z)
      _ _ _ _ _ _ _ _ _ X0 (TUni U V) Hu) eq_refl CU CV).
  - (* ui_lit *) intros ll lr Hl E CU0 CV0. discriminate E.
  - (* ui_top *) intros tl E CU0 CV0. discriminate E.
  - (* ui_int_ll *) intros il ir tr Hp IHp E CU0 CV0.
    apply Rsubf. apply ui_int_ll. apply rsubf_uisub.
    apply IHp; [exact E | exact CU0 | exact CV0].
  - (* ui_int_lr *) intros il ir tr Hp IHp E CU0 CV0.
    apply Rsubf. apply ui_int_lr. apply rsubf_uisub.
    apply IHp; [exact E | exact CU0 | exact CV0].
  - (* ui_int_r *) intros tl il ir Hp IHp Hq IHg E CU0 CV0. discriminate E.
  - (* ui_bot *) intros tr E CU0 CV0. apply Rsubf. apply ui_bot.
  - (* ui_uni_rl *) intros tl ul ur Hp IHp E CU0 CV0.
    injection E as <- <-. apply CU0. apply Rsubf. exact Hp.
  - (* ui_uni_rr *) intros tl ul ur Hp IHp E CU0 CV0.
    injection E as <- <-. apply CV0. apply Rsubf. exact Hp.
  - (* ui_uni_l *) intros ul ur tr Hp IHp Hq IHg E CU0 CV0.
    apply Rsubf. apply ui_uni_l.
    + apply rsubf_uisub. apply IHp; [exact E | exact CU0 | exact CV0].
    + apply rsubf_uisub. apply IHg; [exact E | exact CU0 | exact CV0].
Qed.

Fixpoint uisub_IP_target_bot_elim (U V : T)
  (Hu : uisub (lsub (@IPremise) (rsubf (@IPremise))) U V) {struct Hu} :
  V = TBot -> forall Z : T, rsubf (@IPremise) U Z :=
  match Hu in uisub _ U' V' return V' = TBot -> forall Z : T, rsubf (@IPremise) U' Z with
  | ui_lit ll lr Hl => fun E => False_rect _ (lit_not_bot lr E)
  | ui_top tl => fun E => False_rect _ (top_not_bot E)
  | ui_int_ll il ir tr Hp => fun E Z =>
      @Rsubf Lit RRule (@IPremise) (TIsect il ir) Z
        (ui_int_ll il ir Z (@rsubf_uisub (@IPremise) il Z (uisub_IP_target_bot_elim il tr Hp E Z)))
  | ui_int_lr il ir tr Hp => fun E Z =>
      @Rsubf Lit RRule (@IPremise) (TIsect il ir) Z
        (ui_int_lr il ir Z (@rsubf_uisub (@IPremise) ir Z (uisub_IP_target_bot_elim ir tr Hp E Z)))
  | ui_int_r tl il ir Hpl Hpr => fun E => False_rect _ (isect_not_bot il ir E)
  | ui_bot tr => fun E Z => @Rsubf Lit RRule (@IPremise) TBot Z (ui_bot Z)
  | ui_uni_l ul ur tr Hpl Hpr => fun E Z =>
      @Rsubf Lit RRule (@IPremise) (TUni ul ur) Z
        (ui_uni_l ul ur Z
          (@rsubf_uisub (@IPremise) ul Z (uisub_IP_target_bot_elim ul tr Hpl E Z))
          (@rsubf_uisub (@IPremise) ur Z (uisub_IP_target_bot_elim ur tr Hpr E Z)))
  | ui_uni_rl tl ul ur Hp => fun E => False_rect _ (uni_not_bot ul ur E)
  | ui_uni_rr tl ul ur Hp => fun E => False_rect _ (uni_not_bot ul ur E)
  end.

Definition rsubf_IP_target_bot_elim (X : T) (H : rsubf (@IPremise) X TBot) :
  forall Z : T, rsubf (@IPremise) X Z :=
  match H in @rsubf _ _ _ X' V'
        return (V' = TBot -> forall Z : T, rsubf (@IPremise) X' Z) with
  | @Rsubf _ _ _ tl tr Hu => fun E => uisub_IP_target_bot_elim tl tr Hu E
  end eq_refl.

Lemma rsubf_IP_right_comp_of_main :
  (forall x y : T, esub x y -> rsubf (@IPremise) (Integrate intersect x) y) ->
  forall Y Z : T, rsubf (@IPremise) Y Z ->
    forall X : T, rsubf (@IPremise) X Y -> rsubf (@IPremise) X Z.
Proof.
  intros Hmain Y Z H2.
  induction H2 as [Y0 Z0 Hu].
  induction Hu as [ll lr Hl | tl | il ir tr Hp IHp | il ir tr Hp IHp
    | tl il ir Hp IHp Hq IHg | tr | tl ul ur Hp IHp | tl ul ur Hp IHp
    | ul ur tr Hp IHp Hq IHg]; intros X HX.
  - (* ui_lit *) destruct Hl as [r2 H2prem].
    assert (H2full : rsubf (@IPremise) (TLit ll) (TLit lr)).
    { apply Rsubf. apply ui_lit. exists r2. exact H2prem. }
    exact (IP_trans_lit_right_of_IH X ll (TLit lr)
      (fun x y _ He => Hmain x y He) HX H2full).
  - (* ui_top *) apply Rsubf. apply ui_top.
  - (* ui_int_ll *)
    destruct (rsubf_int_r_inv X il ir HX) as [HXil _].
    exact (IHp X HXil).
  - (* ui_int_lr *)
    destruct (rsubf_int_r_inv X il ir HX) as [_ HXir].
    exact (IHp X HXir).
  - (* ui_int_r *)
    apply Rsubf. apply ui_int_r.
    + apply rsubf_uisub. apply IHp. exact HX.
    + apply rsubf_uisub. apply IHg. exact HX.
  - (* ui_bot *) apply (rsubf_IP_target_bot_elim X HX).
  - (* ui_uni_rl *)
    apply Rsubf. apply ui_uni_rl. apply rsubf_uisub. apply IHp. exact HX.
  - (* ui_uni_rr *)
    apply Rsubf. apply ui_uni_rr. apply rsubf_uisub. apply IHp. exact HX.
  - (* ui_uni_l *)
    exact (rsubf_IP_union_elim ul ur tr IHp IHg X HX).
Qed.

Lemma rsubf_IP_trans_of_main :
  (forall x y : T, esub x y -> rsubf (@IPremise) (Integrate intersect x) y) ->
  forall X Y Z : T,
    rsubf (@IPremise) X Y -> rsubf (@IPremise) Y Z ->
      rsubf (@IPremise) X Z.
Proof.
  intros Hmain X Y Z H1 H2.
  exact (rsubf_IP_right_comp_of_main Hmain Y Z H2 X H1).
Qed.



Lemma rsubf_IP_lit_right_of_rule_of_main :
  forall (X : T) (b c : Lit) (r : RRule b c),
    (forall x y : T, ord (x,y) (X, TLit c) -> esub x y ->
       rsubf (@IPremise) (Integrate intersect x) y) ->
    (forall p q : T, RPremise r p q ->
       rsubf (@IPremise) (Integrate intersect p) q) ->
    rsubf (@IPremise) X (TLit b) ->
    rsubf (@IPremise) X (TLit c).
Proof.
  intros X b c r Hmain Hprem H1.
  assert (H2 : rsubf (@IPremise) (TLit b) (TLit c)).
  { apply Rsubf. apply ui_lit. exists r.
    intros tl tr Hip. destruct Hip as [p q Hrp].
    exact (Hprem p q Hrp). }
  exact (IP_trans_lit_right_of_IH X b (TLit c) Hmain H1 H2).
Qed.


Definition subui_star (A B : T) : Prop := clos_refl_trans T subui A B.

Lemma subui_star_refl : forall A : T, subui_star A A.
Proof. intro A. apply rt_refl. Qed.

Lemma subui_star_step : forall A B C : T,
  subui A B -> subui_star B C -> subui_star A C.
Proof.
  intros A B C Hab Hbc.
  eapply rt_trans; [apply rt_step; exact Hab | exact Hbc].
Qed.

Lemma subui_star_trans : forall A B C : T,
  subui_star A B -> subui_star B C -> subui_star A C.
Proof. intros A B C Hab Hbc. eapply rt_trans; eassumption. Qed.

Lemma subui_star_size : forall A B : T,
  subui_star A B -> size A <= size B.
Proof.
  intros A B H. induction H as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz].
  - apply subui_size in Hstep. lia.
  - lia.
  - lia.
Qed.

Lemma subui_star_m : forall A B : T,
  subui_star A B -> forall tr : T,
    clos_refl_trans M mlt (m A tr) (m B tr).
Proof.
  intros A B H. induction H as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz];
    intro tr.
  - apply m_ui_l with (tl := x) (tl' := y). exact Hstep.
  - apply rt_refl.
  - eapply rt_trans; [apply IHxy | apply IHyz].
Qed.


Lemma rsubf_IP_union_elim_star :
  forall (X U V Z : T),
    (forall X' : T, subui_star X' X ->
       rsubf (@IPremise) X' U -> rsubf (@IPremise) X' Z) ->
    (forall X' : T, subui_star X' X ->
       rsubf (@IPremise) X' V -> rsubf (@IPremise) X' Z) ->
    rsubf (@IPremise) X (TUni U V) -> rsubf (@IPremise) X Z.
Proof.
  intros X0 U V Z CU CV HX.
  pose proof (rsubf_IP_uisub_dep X0 (TUni U V) HX) as Hu.
  refine ((@uisub_ind Lit
      (@lsub Lit RRule (@IPremise) (@rsubf Lit RRule (@IPremise)))
      (fun X Y => Y = TUni U V -> subui_star X X0 ->
         (forall X' : T, subui_star X' X0 ->
            rsubf (@IPremise) X' U -> rsubf (@IPremise) X' Z) ->
         (forall X' : T, subui_star X' X0 ->
            rsubf (@IPremise) X' V -> rsubf (@IPremise) X' Z) ->
         rsubf (@IPremise) X Z)
      _ _ _ _ _ _ _ _ _ X0 (TUni U V) Hu) eq_refl (subui_star_refl X0) CU CV).
  - (* ui_lit *) intros ll lr Hl E Hstar CU0 CV0. discriminate E.
  - (* ui_top *) intros tl E Hstar CU0 CV0. discriminate E.
  - (* ui_int_ll *) intros il ir tr Hp IHp E Hstar CU0 CV0.
    apply Rsubf. apply ui_int_ll. apply rsubf_uisub.
    apply IHp.
    + exact E.
    + apply (subui_star_step il (TIsect il ir) X0); [apply sub_isect_l | exact Hstar].
    + exact CU0. + exact CV0.
  - (* ui_int_lr *) intros il ir tr Hp IHp E Hstar CU0 CV0.
    apply Rsubf. apply ui_int_lr. apply rsubf_uisub.
    apply IHp.
    + exact E.
    + apply (subui_star_step ir (TIsect il ir) X0); [apply sub_isect_r | exact Hstar].
    + exact CU0. + exact CV0.
  - (* ui_int_r *) intros tl il ir Hp IHp Hq IHg E Hstar CU0 CV0. discriminate E.
  - (* ui_bot *) intros tr E Hstar CU0 CV0. apply Rsubf. apply ui_bot.
  - (* ui_uni_rl *) intros tl ul ur Hp IHp E Hstar CU0 CV0.
    injection E as <- <-. apply CU0; [exact Hstar | apply Rsubf; exact Hp].
  - (* ui_uni_rr *) intros tl ul ur Hp IHp E Hstar CU0 CV0.
    injection E as <- <-. apply CV0; [exact Hstar | apply Rsubf; exact Hp].
  - (* ui_uni_l *) intros ul ur tr Hp IHp Hq IHg E Hstar CU0 CV0.
    apply Rsubf. apply ui_uni_l.
    + apply rsubf_uisub. apply IHp.
      * exact E.
      * apply (subui_star_step ul (TUni ul ur) X0); [apply sub_uni_l | exact Hstar].
      * exact CU0. * exact CV0.
    + apply rsubf_uisub. apply IHg.
      * exact E.
      * apply (subui_star_step ur (TUni ul ur) X0); [apply sub_uni_r | exact Hstar].
      * exact CU0. * exact CV0.
Qed.


Definition ord_le (p q : T * T) : Prop := ord p q \/ p = q.

Lemma ord_le_refl : forall p : T * T, ord_le p p.
Proof. intro p. right. reflexivity. Qed.

Lemma ord_le_trans : forall p q r : T * T,
  ord_le p q -> ord_le q r -> ord_le p r.
Proof.
  intros p q r [Hpq | ->] [Hqr | ->].
  - left. eapply ord_trans; eassumption.
  - left. exact Hpq.
  - left. exact Hqr.
  - right. reflexivity.
Qed.

Lemma ord_le_subui_star_left : forall (X' X Y : T),
  subui_star X' X -> ord_le (X',Y) (X,Y).
Proof.
  intros X' X Y H.
  induction H as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz].
  - left. apply ord_sub_l. exact Hstep.
  - right. reflexivity.
  - eapply ord_le_trans; eassumption.
Qed.

Lemma ord_le_subui_star_right : forall (X Y' Y : T),
  subui_star Y' Y -> ord_le (X,Y') (X,Y).
Proof.
  intros X Y' Y H.
  induction H as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz].
  - left. apply ord_sub_r. exact Hstep.
  - right. reflexivity.
  - eapply ord_le_trans; eassumption.
Qed.


Lemma subui_star_single : forall A B : T,
  subui A B -> subui_star A B.
Proof. intros A B H. apply rt_step. exact H. Qed.

Lemma ord_trans_ord_le : forall p q r : T * T,
  ord p q -> ord_le q r -> ord p r.
Proof.
  intros p q r Hpq [Hqr | Heq].
  - eapply ord_trans; eassumption.
  - subst r. exact Hpq.
Qed.

Lemma rsubf_IP_right_comp_family :
  forall (X0 Z0 : T),
    (forall X : T, subui_star X X0 ->
       forall x y : T, ord (x,y) (X,Z0) -> esub x y ->
         rsubf (@IPremise) (Integrate intersect x) y) ->
    forall Y Z : T, rsubf (@IPremise) Y Z ->
      subui_star Z Z0 ->
      forall X : T, subui_star X X0 ->
        rsubf (@IPremise) X Y -> rsubf (@IPremise) X Z.
Proof.
  intros X0 Z0 Hfam Y Z H2.
  induction H2 as [Y0 Zc Hu].
  induction Hu as [ll lr Hl | tl | il ir tr Hp IHp | il ir tr Hp IHp
    | tl il ir Hp IHp Hq IHg | tr | tl ul ur Hp IHp | tl ul ur Hp IHp
    | ul ur tr Hp IHp Hq IHg]; intros HZ X Hsub HX.
  - (* ui_lit *) destruct Hl as [r2 H2prem].
    assert (H2full : rsubf (@IPremise) (TLit ll) (TLit lr)).
    { apply Rsubf. apply ui_lit. exists r2. exact H2prem. }
    assert (Hb : forall x y : T, ord (x,y) (X, TLit lr) -> esub x y ->
                   rsubf (@IPremise) (Integrate intersect x) y).
    { intros x y Ho He.
      apply (Hfam X Hsub x y).
      - eapply ord_trans_ord_le.
        + exact Ho.
        + apply ord_le_subui_star_right. exact HZ.
      - exact He. }
    exact (IP_trans_lit_right_of_IH X ll (TLit lr) Hb HX H2full).
  - (* ui_top *) apply Rsubf. apply ui_top.
  - (* ui_int_ll *)
    destruct (rsubf_int_r_inv X il ir HX) as [HXil _].
    exact (IHp HZ X Hsub HXil).
  - (* ui_int_lr *)
    destruct (rsubf_int_r_inv X il ir HX) as [_ HXir].
    exact (IHp HZ X Hsub HXir).
  - (* ui_int_r *)
    apply Rsubf. apply ui_int_r.
    + apply rsubf_uisub.
      assert (HZil : subui_star il Z0).
      { eapply subui_star_step; [apply sub_isect_l | exact HZ]. }
      exact (IHp HZil X Hsub HX).
    + apply rsubf_uisub.
      assert (HZir : subui_star ir Z0).
      { eapply subui_star_step; [apply sub_isect_r | exact HZ]. }
      exact (IHg HZir X Hsub HX).
  - (* ui_bot *) apply (rsubf_IP_target_bot_elim X HX).
  - (* ui_uni_rl *)
    apply Rsubf. apply ui_uni_rl. apply rsubf_uisub.
    assert (HZul : subui_star ul Z0).
    { eapply subui_star_step; [apply sub_uni_l | exact HZ]. }
    exact (IHp HZul X Hsub HX).
  - (* ui_uni_rr *)
    apply Rsubf. apply ui_uni_rr. apply rsubf_uisub.
    assert (HZur : subui_star ur Z0).
    { eapply subui_star_step; [apply sub_uni_r | exact HZ]. }
    exact (IHp HZur X Hsub HX).
  - (* ui_uni_l *)
    apply (rsubf_IP_union_elim_star X ul ur tr).
    + intros X' Hstar HX'.
      apply IHp.
      * exact HZ.
      * apply (subui_star_trans X' X X0); assumption.
      * exact HX'.
    + intros X' Hstar HX'.
      apply IHg.
      * exact HZ.
      * apply (subui_star_trans X' X X0); assumption.
      * exact HX'.
    + exact HX.
Qed.

(*
  IntegratedCompleteness : esub tl tr -> isub tl tr.
  This remains unproven.  Soundness, IntegratedDecidability and
  DecidabilityOfExtendedSubtyping are fully proven above.

  The development has reduced the completeness problem to the "lift" lemma

    Lift : forall x y, rsubf RPremise x y -> rsubf IPremise (I x) y.

  In particular, RP_to_IP_of_lift above shows that Lift implies the
  same-index conversion rsubf RPremise -> rsubf IPremise, and applying Lift
  to refl_R (TLit l) gives the reflexive integrated literal judgement
  rsubf IPremise (intersect [l]) (TLit l).  The lemmas RP_top_like and
  intersect_cons_not_top settle the TTop/TBot and impossible-top parts of Lift.
  The development now has the following fully proved pieces of the
  well-founded completeness induction:

    ct_crt, conv_to_lit : convert an R-derivation A <: TLit a into an
      integrated derivation, using the well-founded induction hypothesis
      only at the premises of literal rules (which are strictly smaller by
      m_lit);
    G_of_main_IH : proves rsubf IPremise (intersect [a]) (TLit a) from the
      well-founded induction hypothesis at smaller esub pairs;
    refl_isub_of_IH : proves integrated reflexivity isub t t from the
      well-founded induction hypothesis at smaller esub pairs, including
      the TIsect projection cases via ord_sub_r and the literal cases via
      G_of_main_IH.

  The atomic cut is now handled: rsubam_sound_esub converts a rsubam
  derivation with esub assumptions into esub, and isub_lit_trans_of_IH uses
  LiteralTransitivity together with the well-founded induction hypothesis to
  prove rsubf IPremise (TLit a) (TLit c) from the two literal IPremise
  derivations a <: b and b <: c.  Its proof derives esub at the premises of
  the composed rule via rsubam_sound_esub, then applies the well-founded
  hypothesis at those premises, which are below (TLit a, TLit c) by m_lit.
  isub_lit_trans_right_of_IH extends this to an arbitrary right type Z,
  composing a literal-left IPremise derivation with an arbitrary IPremise
  derivation from the same literal, and recursing structurally on the
  second derivation.

  The remaining steps are the D-trans case (composing two integrated
  derivations), the D-lit case (eliminating the rsubam produced by
  DRuleToRProof using the premise induction hypotheses), the dsubda_dist
  case (an IPremise version of distributivity of intersection over union),
  and the dsubda_assume case (converting the closed dsub derivation returned
  by IntersectorCompleteness).

  The positive prefix-literal branch also requires a measure comparison
  of the form  m A (TLit a) <=* m (TLit a) (TLit a)  for each component A
  of intersect (a :: q).  The supplied axioms give MeasurePreservation for
  I tl and subui monotonicity in the direction from smaller to larger types,
  but not this comparison.

  A second, sharper obstruction is the ram-elimination needed for dsubda_lit
  and dsubda_assume.  The only D-to-R axiom DRuleToRProof produces a
  `rsubam` derivation.  Eliminating `rsubam` structurally closes every case
  except `ram_mono`, which composes three arbitrary `rsubf RPremise`
  derivations and therefore is exactly a cut/transitivity principle for
  `rsubf`.  The uisub system has no transitivity constructor, and the
  LiteralTransitivity axiom also returns only `rsubam` chains.  No supplied
  measure bounds the intermediate types or endpoints of a `ram_mono` step:
  m_lit constrains only RPremise premises, while DRuleToRProof has no
  measure axiom.  Hence neither a well-founded induction on ord nor the
  syntax-directedness axioms can discharge this case.  A complete solution
  would need a genuine cut-elimination/transitivity theorem for the
  integrated system, not derivable from the present interface by the
  reductions implemented above.

  The file now contains a sharpened reduction of this cut principle.  Define

    RPlitcomp := forall a b c (r1 : RRule a b) (r2 : RRule b c),
      (forall p q, RPremise r1 p q -> rsubf RPremise p q) ->
      (forall p q, RPremise r2 p q -> rsubf RPremise p q) ->
      exists r : RRule a c,
        forall p q, RPremise r p q -> rsubf RPremise p q.

  Then rsubf_RP_trans_of_litcomp proves full transitivity of
  rsubf RPremise from RPlitcomp, and rsubam_RP_elim_of_trans proves
  elimination of rsubam into rsubf RPremise from that transitivity.
  RPlitcomp itself is exactly what LiteralTransitivity does not provide:
  LiteralTransitivity returns the composed rule together with rsubam
  derivations of its premises, and eliminating those rsubam derivations
  is precisely the missing cut.  In particular, the ram_lit rules used in
  those rsubam derivations may be arbitrary rules unrelated to r1 and r2,
  so there is no measure or structural decrease that could justify a
  recursive construction of RPlitcomp.
*)
Theorem IntegratedCompleteness : forall tl tr : T, esub tl tr -> isub tl tr.

End Integrated.
