Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export LinearRule.

Inductive binding : Set :=
  | bind_sub : binding
  | bind_typ : typ -> binding.

Definition env := list (atom * binding).

Notation empty := (@nil (atom * binding)).

Inductive WFS : env -> typ -> Prop :=
| WFS_top : forall E, WFS E typ_top
| WFS_nat : forall E, WFS E typ_nat
| WFS_fvar : forall X E ,
    binds X (bind_sub) E ->
    WFS E (typ_fvar X)
| WFS_arrow : forall E A B,
    WFS E A ->
    WFS E B ->
    WFS E (typ_arrow A B)
| WFS_rec : forall L E A,


      (forall  X , X \notin L ->
        WFS (X ~ bind_sub ++ E) (open_tt A X)) ->
      WFS E (typ_mu A).

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) ,
      wf_env E ->
      X \notin dom E ->
      wf_env (X ~ bind_sub ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      WFS E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E).

Inductive sub_amber2: env -> typ -> typ -> Prop :=
| sam2_nat: forall E,
    wf_env E ->
    sub_amber2 E typ_nat typ_nat
| sam2_top: forall E A,
    WFS E A ->
    wf_env E ->
    sub_amber2 E A typ_top
| sam2_fvar: forall E X,
    binds X (bind_sub) E ->
    wf_env E ->
    sub_amber2 E (typ_fvar X) (typ_fvar X)
| sam2_arrow: forall E A1 A2 B1 B2,
    sub_amber2 E B1 A1 ->
    sub_amber2 E A2 B2 ->
    sub_amber2 E (typ_arrow A1 A2) (typ_arrow B1 B2)
| sam2_rec: forall E A B L,
    (forall X , X \notin L ->
                sub_amber2 (X ~ bind_sub ++ E) (open_tt A X) (open_tt B X)) ->
    (forall X , X \notin L ->
                posvar Pos X (typ_mu A) (typ_mu B)) ->
    sub_amber2 E (typ_mu A) (typ_mu B)
.

Definition drop_im b :=
  match b with
  | Rules.bind_sub _ => bind_sub
  | Rules.bind_typ t => bind_typ t
  end.

Definition drop_im_env := map drop_im.

(* ============================================================ *)
(* Basic facts about modes and environments                     *)
(* ============================================================ *)

Lemma flip_im_invol : forall im, flip_im (flip_im im) = im.
Proof. destruct im; reflexivity. Qed.

Lemma flip_im_neq : forall im, im <> flip_im im.
Proof. destruct im; discriminate. Qed.

Lemma drop_im_env_cons : forall (x:atom) (b:Rules.binding) (E:Rules.env),
  drop_im_env (x ~ b ++ E) = x ~ drop_im b ++ drop_im_env E.
Proof. intros. unfold drop_im_env. simpl. reflexivity. Qed.

Lemma dom_drop_im_env : forall E, dom (drop_im_env E) = dom E.
Proof.
  intros E. unfold drop_im_env. induction E as [| (x,b) E IH]; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma binds_drop_im : forall (X:atom) (b:Rules.binding) (E:Rules.env),
  binds X b E -> binds X (drop_im b) (drop_im_env E).
Proof.
  intros. unfold drop_im_env. eapply binds_map_2. eauto.
Qed.

(* environment lift from Task bindings to Rules bindings, all bind_sub Pos *)
Definition epos_bind (b : binding) : Rules.binding :=
  match b with
  | bind_sub => Rules.bind_sub Pos
  | bind_typ t => Rules.bind_typ t
  end.

Definition epos_env : env -> Rules.env := map epos_bind.

Lemma epos_env_cons : forall (x:atom) (b:binding) (E:env),
  epos_env (x ~ b ++ E) = x ~ epos_bind b ++ epos_env E.
Proof. intros. unfold epos_env. simpl. reflexivity. Qed.

Lemma epos_env_cons_sub : forall (x:atom) (E:env),
  epos_env (x ~ bind_sub ++ E) = x ~ Rules.bind_sub Pos ++ epos_env E.
Proof.
  intros. unfold epos_env. simpl. reflexivity.
Qed.

Lemma dom_epos_env : forall E, dom (epos_env E) = dom E.
Proof.
  intros E. unfold epos_env. induction E as [| (x,b) E IH]; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma binds_epos : forall (X:atom) (b:binding) (E:env),
  binds X b E -> binds X (epos_bind b) (epos_env E).
Proof.
  intros. unfold epos_env. eapply binds_map_2. eauto.
Qed.

Lemma binds_epos_sub : forall (X:atom) (E:env),
  binds X bind_sub E -> binds X (Rules.bind_sub Pos) (epos_env E).
Proof.
  intros. change (binds X (epos_bind bind_sub) (epos_env E)).
  apply binds_epos. auto.
Qed.

(* wf_env is unique *)
Lemma wf_env_uniq : forall E, Rules.wf_env E -> uniq E.
Proof.
  intros E H. induction H.
  - constructor.
  - simpl. constructor; auto.
  - simpl. constructor; auto.
Qed.

(* rules WFS -> type *)
Lemma Rules_WFS_type : forall E A, Rules.WFS E A -> type A.
Proof.
  intros E A H. induction H.
  - apply type_top.
  - apply type_nat.
  - apply type_var.
  - apply type_arrow; auto.
  - apply type_mu with (L := L). auto.
Qed.

(* ============================================================ *)
(* WFS and wf_env transport                                     *)
(* ============================================================ *)

Lemma Rules_WFS_drop : forall E A, Rules.WFS E A -> WFS (drop_im_env E) A.
Proof.
  intros E A H.
  induction H as [E | E | X E im Hb | E A B HW1 IH1 HW2 IH2
                  | L E A im Hf IHf].
  - apply WFS_top.
  - apply WFS_nat.
  - apply WFS_fvar. eapply binds_drop_im with (b := Rules.bind_sub im). auto.
  - apply WFS_arrow; auto.
  - apply WFS_rec with (L := L). intros X HX.
    specialize (IHf X HX). rewrite drop_im_env_cons in IHf. exact IHf.
Qed.

Lemma Task_WFS_epos : forall E A, WFS E A -> Rules.WFS (epos_env E) A.
Proof.
  intros E A H.
  induction H as [E | E | X E Hb | E A B HW1 IH1 HW2 IH2
                  | L E A Hf IHf].
  - apply Rules.WFS_top.
  - apply Rules.WFS_nat.
  - eapply Rules.WFS_fvar. apply binds_epos_sub. auto.
  - apply Rules.WFS_arrow; auto.
  - apply Rules.WFS_rec with (L := L) (im := Pos). intros X HX.
    specialize (IHf X HX). rewrite epos_env_cons_sub in IHf. exact IHf.
Qed.

Lemma Rules_wf_env_drop : forall E, Rules.wf_env E -> wf_env (drop_im_env E).
Proof.
  intros E H. induction H.
  - simpl. apply wf_env_empty.
  - rewrite drop_im_env_cons. apply wf_env_sub; auto.
    rewrite dom_drop_im_env. auto.
  - rewrite drop_im_env_cons. apply wf_env_typ; auto.
    * apply Rules_WFS_drop. auto.
    * rewrite dom_drop_im_env. auto.
Qed.

Lemma Task_wf_env_epos : forall E, wf_env E -> Rules.wf_env (epos_env E).
Proof.
  intros E H. induction H.
  - simpl. apply Rules.wf_env_empty.
  - rewrite epos_env_cons_sub. apply Rules.wf_env_sub; auto.
    rewrite dom_epos_env. auto.
  - rewrite epos_env_cons. apply Rules.wf_env_typ; auto.
    * apply Task_WFS_epos. auto.
    * rewrite dom_epos_env. auto.
Qed.

(* ============================================================ *)
(* Sub derives well-typed endpoints, and Eq derivations relate  *)
(* syntactically equal types.                                   *)
(* ============================================================ *)

Lemma Sub_type : forall im cm evs E A B,
  Rules.Sub im cm evs E A B -> type A /\ type B.
Proof.
  intros im cm evs E A B H.
  induction H as
    [ E im Hwf
    | E im Hwf
    | E im A Hwf HWFS Hne
    | E X im Hwf Hb
    | E X im Hwf Hb
    | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm im H1 IH1 H2 IH2 Hcomp
    | L A1 A2 evs E im Hf IHf
    | L A1 A2 evs E im Hf IHf
    | L A1 A2 evs E im Hf IHf
    | im cm evs evs' E A1 A2 H1 IH1 Heq ].
  - split; apply type_nat.
  - split; apply type_top.
  - split. apply Rules_WFS_type with (E := E); auto. apply type_top.
  - split; apply type_var.
  - split; apply type_var.
  - destruct IH1 as [HB1 HA1]. destruct IH2 as [HA2 HB2].
    split; apply type_arrow; auto.
  - split; apply type_mu with (L := L); intros X HX;
      destruct (IHf X HX) as [T1 T2]; assumption.
  - split; apply type_mu with (L := L); intros X HX;
      destruct (IHf X HX) as [T1 T2]; assumption.
  - split; apply type_mu with (L := L); intros X HX;
      destruct (IHf X HX) as [T1 T2]; assumption.
  - auto.
Qed.

(* Closing a fresh free variable back into a bound variable. *)
Fixpoint close_tt_rec (K : nat) (Z : atom) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_nat => typ_nat
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then typ_bvar K else typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (close_tt_rec K Z T1) (close_tt_rec K Z T2)
  | typ_mu T => typ_mu (close_tt_rec (S K) Z T)
  end.

Lemma close_open_tt : forall K Z T,
  Z \notin fv_tt T ->
  close_tt_rec K Z (open_tt_rec K (typ_fvar Z) T) = T.
Proof.
  intros K Z T. revert K.
  induction T as [ | | n | a | T1 IH1 | T1 IH1 T2 IH2 ]; intros K HZ.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. destruct (K === n) as [E|E]; simpl.
    + subst. destruct (Z == Z) as [E2|E2]; [ reflexivity | exfalso; apply E2; reflexivity ].
    + reflexivity.
  - simpl. destruct (a == Z) as [E|E]; simpl.
    + exfalso. apply HZ. subst a. apply AtomSetImpl.singleton_2. reflexivity.
    + reflexivity.
  - simpl. f_equal. apply IH1. simpl in HZ. exact HZ.
  - simpl in HZ.
    pose proof (notin_union_1 Z (fv_tt T1) (fv_tt T2) HZ) as HZ1.
    pose proof (notin_union_2 Z (fv_tt T1) (fv_tt T2) HZ) as HZ2.
    simpl. rewrite (IH1 K HZ1). rewrite (IH2 K HZ2). reflexivity.
Qed.

(* Injectivity of opening at a fresh variable. *)
Lemma open_tt_rec_inj : forall K X A,
  X \notin fv_tt A ->
  forall B, X \notin fv_tt B ->
    open_tt_rec K (typ_fvar X) A = open_tt_rec K (typ_fvar X) B -> A = B.
Proof.
  intros K X A HA B HB Heq.
  assert (H := f_equal (close_tt_rec K X) Heq).
  rewrite (close_open_tt K X A HA) in H.
  rewrite (close_open_tt K X B HB) in H.
  exact H.
Qed.

(* ============================================================ *)
(* Positivity facts                                             *)
(* ============================================================ *)

Lemma fv_open_tt_rec : forall X Y K A,
  X \notin fv_tt A -> X <> Y ->
  X \notin fv_tt (open_tt_rec K (typ_fvar Y) A).
Proof.
  intros X Y K A. revert K.
  induction A as [ | | n | a | A1 IH1 | A1 IH1 A2 IH2 ]; intros K HA HXY.
  - simpl. apply notin_empty_1.
  - simpl. apply notin_empty_1.
  - simpl. destruct (K === n); simpl.
    + apply notin_singleton. intro H; apply HXY; symmetry; auto.
    + apply notin_empty_1.
  - simpl in HA. simpl. exact HA.
  - simpl in HA. simpl. apply IH1; auto.
  - simpl in HA.
    pose proof (notin_union_1 X (fv_tt A1) (fv_tt A2) HA) as HA1.
    pose proof (notin_union_2 X (fv_tt A1) (fv_tt A2) HA) as HA2.
    simpl. apply notin_union.
    + apply IH1; auto.
    + apply IH2; auto.
Qed.

Lemma fv_open_tt : forall X Y A,
  X \notin fv_tt A -> X <> Y ->
  X \notin fv_tt (open_tt A Y).
Proof. intros. apply fv_open_tt_rec with (K := 0); auto. Qed.

Lemma posvar_flip_notin : forall m X A B,
  posvar m X A B ->
  X \notin fv_tt A -> X \notin fv_tt B ->
  posvar (flip_im m) X A B.
Proof.
  intros m X A B H.
  induction H as
    [ X m
    | X A m Hty
    | X A m Hty
    | X
    | X Y m HXY
    | X m A1 A2 B1 B2 Hp1 IH1 Hp2 IH2
    | X m A B L H1 IH1 H2 IH2
    | A X m L HX H1 IH1 ];
    intros HA HB.
  - apply pos_nat.
  - apply pos_top. auto.
  - apply pos_top_flip. auto.
  - simpl in HA. exfalso. apply HA. apply AtomSetImpl.singleton_2. reflexivity.
  - apply pos_fvar_y. auto.
  - simpl in HA. simpl in HB.
    pose proof (notin_union_1 X (fv_tt A1) (fv_tt A2) HA) as HA1.
    pose proof (notin_union_2 X (fv_tt A1) (fv_tt A2) HA) as HA2.
    pose proof (notin_union_1 X (fv_tt B1) (fv_tt B2) HB) as HB1.
    pose proof (notin_union_2 X (fv_tt B1) (fv_tt B2) HB) as HB2.
    apply pos_arrow.
    + apply IH1; auto.
    + apply IH2; auto.
  - simpl in HA. simpl in HB.
    assert (HXY : forall Y, Y \notin L \u {{X}} -> X <> Y).
    { intros Y HY. apply (notin_singleton_1 X Y).
      apply (notin_union_2 Y L (singleton X)). exact HY. }
    apply pos_rec with (L := L).
    + intros Y HY. apply IH1.
      * exact HY.
      * apply fv_open_tt_rec; auto.
      * apply fv_open_tt_rec; auto.
    + intros Y HY. apply H2. exact HY.
  - apply pos_rec_t with (L := L); auto.
Qed.

Lemma posvar_to_Pos : forall m X A B,
  posvar m X A B ->
  X \notin fv_tt A -> X \notin fv_tt B ->
  posvar Pos X A B.
Proof.
  intros m X A B H HA HB. destruct m.
  - simpl. apply posvar_flip_notin with (m := Neg); auto.
  - exact H.
Qed.

(* ============================================================ *)
(* The soundness invariant                                      *)
(* ============================================================ *)

Definition K (im : IsoMode) (evs : atoms) (E : Rules.env) (A B : typ) : Prop :=
  (forall X, X \notin evs -> X \notin dom E -> posvar im X A B)
  /\ (forall Z, binds Z (Rules.bind_sub im) E -> Z \notin evs -> posvar Pos Z A B)
  /\ (forall Z, binds Z (Rules.bind_sub (flip_im im)) E -> Z \notin evs
                -> posvar Neg Z A B).

Lemma compose_cm_Eq : forall cm1 cm2 evs1 evs2,
  compose_cm cm1 cm2 evs1 evs2 = Some Eq -> cm1 = Eq /\ cm2 = Eq.
Proof.
  intros cm1 cm2 evs1 evs2 H. destruct cm1, cm2; simpl in *; try discriminate.
  - destruct (AtomSetImpl.is_empty evs2); discriminate.
  - destruct (AtomSetImpl.is_empty evs1); discriminate.
  - auto.
Qed.

Lemma open_tt_inj : forall X A B,
  X \notin fv_tt A -> X \notin fv_tt B ->
  open_tt A X = open_tt B X -> A = B.
Proof. intros. eapply open_tt_rec_inj; eauto. Qed.

Lemma Sub_eq_implies_eq : forall im cm evs E A B,
  Rules.Sub im cm evs E A B -> cm = Eq -> A = B.
Proof.
  intros im cm evs E A B H.
  induction H as
    [ E im Hwf
    | E im Hwf
    | E im A Hwf HWFS Hne
    | E X im Hwf Hb
    | E X im Hwf Hb
    | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm im H1 IH1 H2 IH2 Hcomp
    | L A1 A2 evs E im Hf IHf
    | L A1 A2 evs E im Hf IHf
    | L A1 A2 evs E im Hf IHf
    | im cm evs evs' E A1 A2 H1 IH1 Heq ];
    intros Hcm; try discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite Hcm in Hcomp. apply compose_cm_Eq in Hcomp. destruct Hcomp as [E1 E2].
    f_equal.
    + symmetry. apply IH1. exact E1.
    + apply IH2. exact E2.
  - (* rec_eq_notin *)
    destruct (atom_fresh ((L \u fv_tt A1) \u fv_tt A2)) as [X HX].
    pose proof (notin_union_1 X (L \u fv_tt A1) (fv_tt A2) HX) as HXa.
    pose proof (notin_union_2 X (L \u fv_tt A1) (fv_tt A2) HX) as HXb.
    pose proof (notin_union_1 X L (fv_tt A1) HXa) as HXL.
    pose proof (notin_union_2 X L (fv_tt A1) HXa) as HX1.
    assert (Hop : open_tt A1 X = open_tt A2 X) by (apply IHf; auto).
    f_equal. eapply open_tt_inj; eauto.
  - (* rec_eq_in *)
    destruct (atom_fresh ((L \u fv_tt A1) \u fv_tt A2)) as [X HX].
    pose proof (notin_union_1 X (L \u fv_tt A1) (fv_tt A2) HX) as HXa.
    pose proof (notin_union_2 X (L \u fv_tt A1) (fv_tt A2) HX) as HXb.
    pose proof (notin_union_1 X L (fv_tt A1) HXa) as HXL.
    pose proof (notin_union_2 X L (fv_tt A1) HXa) as HX1.
    assert (Hop : open_tt A1 X = open_tt A2 X) by (apply IHf; auto).
    f_equal. eapply open_tt_inj; eauto.
  - auto.
Qed.

(* ============================================================ *)
(* Helper sets and the soundness induction                      *)
(* ============================================================ *)

Definition Lbig (L evs : atoms) (E : Rules.env) (A1 A2 : typ) : atoms :=
  (((L \u evs) \u dom E) \u fv_tt A1) \u fv_tt A2.

Lemma notin5 : forall (x:atom) (A B C D E : atoms),
  x \notin (((A \u B) \u C) \u D) \u E ->
  x \notin A /\ x \notin B /\ x \notin C /\ x \notin D /\ x \notin E.
Proof.
  intros x A B C D E H.
  pose proof (notin_union_1 x (((A \u B) \u C) \u D) E H) as H1.
  pose proof (notin_union_2 x (((A \u B) \u C) \u D) E H) as H2.
  pose proof (notin_union_1 x ((A \u B) \u C) D H1) as H3.
  pose proof (notin_union_2 x ((A \u B) \u C) D H1) as H4.
  pose proof (notin_union_1 x (A \u B) C H3) as H5.
  pose proof (notin_union_2 x (A \u B) C H3) as H6.
  pose proof (notin_union_1 x A B H5) as H7.
  pose proof (notin_union_2 x A B H5) as H8.
  repeat split; auto.
Qed.

(* Common reasoning for the two "notin" recursive rules. *)
Lemma sound_rec_common : forall (im:IsoMode) (evs:atoms) (E:Rules.env)
  (A1 A2:typ) (L:atoms),
  (forall X, X \notin L ->
     Rules.wf_env (X ~ Rules.bind_sub im ++ E) /\
     type (open_tt A1 X) /\ type (open_tt A2 X) /\
     sub_amber2 (drop_im_env (X ~ Rules.bind_sub im ++ E))
                (open_tt A1 X) (open_tt A2 X) /\
     K im evs (X ~ Rules.bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->
  Rules.wf_env E /\ type (typ_mu A1) /\ type (typ_mu A2) /\
  sub_amber2 (drop_im_env E) (typ_mu A1) (typ_mu A2) /\
  K im evs E (typ_mu A1) (typ_mu A2).
Proof.
  intros im evs E A1 A2 L IHf.
  destruct (atom_fresh (Lbig L evs E A1 A2)) as [X0 HX0].
  unfold Lbig in HX0. apply notin5 in HX0.
  destruct HX0 as [HX0L [HX0e [HX0d [HX0f1 HX0f2]]]].
  pose proof (IHf X0 HX0L) as IH0.
  destruct IH0 as [HwfX [HT1 [HT2 [HsubX HKX]]]].
  assert (HwfE : Rules.wf_env E).
  { simpl in HwfX. inversion HwfX. assumption. }
  assert (HK : K im evs E (typ_mu A1) (typ_mu A2)).
  { unfold K. repeat split.
    - (* free clause *) intros X HXe HXd.
      apply pos_rec with (L := Lbig L evs E A1 A2).
      + intros Y HYraw.
        pose proof (notin_union_1 Y (Lbig L evs E A1 A2) (singleton X) HYraw) as HYbig.
        pose proof (notin_union_2 Y (Lbig L evs E A1 A2) (singleton X) HYraw) as HYX.
        assert (HXY : X <> Y) by (apply (notin_singleton_1 X Y); exact HYX).
        unfold Lbig in HYbig. apply notin5 in HYbig.
        destruct HYbig as [HYL [HYe [HYd [HYf1 HYf2]]]].
        destruct (IHf Y HYL) as [_ [_ [_ [_ HKY]]]].
        destruct HKY as [HKYf [HKYa HKYn]].
        apply HKYf.
        * exact HXe.
        * simpl. apply notin_add; auto.
      + intros Y HYraw.
        pose proof (notin_union_1 Y (Lbig L evs E A1 A2) (singleton X) HYraw) as HYbig.
        pose proof (notin_union_2 Y (Lbig L evs E A1 A2) (singleton X) HYraw) as HYX.
        unfold Lbig in HYbig. apply notin5 in HYbig.
        destruct HYbig as [HYL [HYe [HYd [HYf1 HYf2]]]].
        destruct (IHf Y HYL) as [_ [_ [_ [_ HKY]]]].
        destruct HKY as [HKYf [HKYa HKYn]].
        apply HKYa.
        * simpl. left. reflexivity.
        * exact HYe.
    - (* aligned clause *) intros Z HbZ HZe.
      apply pos_rec with (L := Lbig L evs E A1 A2).
      + intros Y HYraw.
        pose proof (notin_union_1 Y (Lbig L evs E A1 A2) (singleton Z) HYraw) as HYbig.
        pose proof (notin_union_2 Y (Lbig L evs E A1 A2) (singleton Z) HYraw) as HYX.
        unfold Lbig in HYbig. apply notin5 in HYbig.
        destruct HYbig as [HYL [HYe [HYd [HYf1 HYf2]]]].
        destruct (IHf Y HYL) as [_ [_ [_ [_ HKY]]]].
        destruct HKY as [HKYf [HKYa HKYn]].
        apply HKYa.
        * simpl. apply binds_cons_3. exact HbZ.
        * exact HZe.
      + intros Y HYraw.
        pose proof (notin_union_1 Y (Lbig L evs E A1 A2) (singleton Z) HYraw) as HYbig.
        pose proof (notin_union_2 Y (Lbig L evs E A1 A2) (singleton Z) HYraw) as HYX.
        unfold Lbig in HYbig. apply notin5 in HYbig.
        destruct HYbig as [HYL [HYe [HYd [HYf1 HYf2]]]].
        destruct (IHf Y HYL) as [_ [_ [_ [_ HKY]]]].
        destruct HKY as [HKYf [HKYa HKYn]].
        apply HKYa.
        * simpl. left. reflexivity.
        * exact HYe.
    - (* anti clause *) intros Z HbZ HZe.
      apply pos_rec with (L := Lbig L evs E A1 A2).
      + intros Y HYraw.
        pose proof (notin_union_1 Y (Lbig L evs E A1 A2) (singleton Z) HYraw) as HYbig.
        pose proof (notin_union_2 Y (Lbig L evs E A1 A2) (singleton Z) HYraw) as HYX.
        unfold Lbig in HYbig. apply notin5 in HYbig.
        destruct HYbig as [HYL [HYe [HYd [HYf1 HYf2]]]].
        destruct (IHf Y HYL) as [_ [_ [_ [_ HKY]]]].
        destruct HKY as [HKYf [HKYa HKYn]].
        apply HKYn.
        * simpl. apply binds_cons_3. exact HbZ.
        * exact HZe.
      + intros Y HYraw.
        pose proof (notin_union_1 Y (Lbig L evs E A1 A2) (singleton Z) HYraw) as HYbig.
        pose proof (notin_union_2 Y (Lbig L evs E A1 A2) (singleton Z) HYraw) as HYX.
        unfold Lbig in HYbig. apply notin5 in HYbig.
        destruct HYbig as [HYL [HYe [HYd [HYf1 HYf2]]]].
        destruct (IHf Y HYL) as [_ [_ [_ [_ HKY]]]].
        destruct HKY as [HKYf [HKYa HKYn]].
        apply HKYa.
        * simpl. left. reflexivity.
        * exact HYe.
  }
  destruct HK as [HKf [HKa HKn]].
  split.
  { exact HwfE. }
  split.
  { apply type_mu with (L := L). intros X HX.
    destruct (IHf X HX) as [_ [T1 _]]. exact T1. }
  split.
  { apply type_mu with (L := L). intros X HX.
    destruct (IHf X HX) as [_ [_ [T2 _]]]. exact T2. }
  split.
  { apply sam2_rec with (L := Lbig L evs E A1 A2).
    + intros X HX.
      unfold Lbig in HX. apply notin5 in HX.
      destruct HX as [HXL [HXe [HXd [HXf1 HXf2]]]].
      destruct (IHf X HXL) as [_ [_ [_ [Hsub _]]]].
      rewrite drop_im_env_cons in Hsub. simpl in Hsub. exact Hsub.
    + intros X HX.
      unfold Lbig in HX. apply notin5 in HX.
      destruct HX as [HXL [HXe [HXd [HXf1 HXf2]]]].
      apply posvar_to_Pos with (m := im).
      * apply HKf. exact HXe. exact HXd.
      * exact HXf1.
      * exact HXf2. }
  { unfold K. split.
    + exact HKf.
    + split; [exact HKa | exact HKn]. }
Qed.

(* The "in" recursive rule, where the body may use the recursion variable
   non-positively.  Then the two bodies must be syntactically equal and the
   positivity of the fresh variable follows from pos_rec_t. *)
Lemma sound_rec_in : forall (im:IsoMode) (evs:atoms) (E:Rules.env)
  (A1 A2:typ) (L:atoms),
  (forall X, X \notin L ->
     Rules.Sub im Eq (add X evs) (X ~ Rules.bind_sub im ++ E)
               (open_tt A1 X) (open_tt A2 X)) ->
  (forall X, X \notin L ->
     Rules.wf_env (X ~ Rules.bind_sub im ++ E) /\
     type (open_tt A1 X) /\ type (open_tt A2 X) /\
     sub_amber2 (drop_im_env (X ~ Rules.bind_sub im ++ E))
                (open_tt A1 X) (open_tt A2 X) /\
     K im (add X evs) (X ~ Rules.bind_sub im ++ E) (open_tt A1 X) (open_tt A2 X)) ->
  Rules.wf_env E /\ type (typ_mu A1) /\ type (typ_mu A2) /\
  sub_amber2 (drop_im_env E) (typ_mu A1) (typ_mu A2) /\
  K im (evs \u fv_tt A1) E (typ_mu A1) (typ_mu A2).
Proof.
  intros im evs E A1 A2 L Hbody IHf.
  destruct (atom_fresh ((L \u fv_tt A1) \u fv_tt A2)) as [X0 HX0].
  pose proof (notin_union_1 X0 (L \u fv_tt A1) (fv_tt A2) HX0) as HXa.
  pose proof (notin_union_2 X0 (L \u fv_tt A1) (fv_tt A2) HX0) as HXb.
  pose proof (notin_union_1 X0 L (fv_tt A1) HXa) as HX0L.
  pose proof (notin_union_2 X0 L (fv_tt A1) HXa) as HX0f1.
  assert (HA12 : A1 = A2).
  { eapply open_tt_inj.
    - exact HX0f1.
    - exact HXb.
    - eapply Sub_eq_implies_eq.
      + apply Hbody. exact HX0L.
      + reflexivity. }
  subst A2.
  pose proof (IHf X0 HX0L) as IH0.
  destruct IH0 as [HwfX [HT1 [HT2 [HsubX HKX]]]].
  assert (HwfE : Rules.wf_env E) by (simpl in HwfX; inversion HwfX; assumption).
  assert (HK : K im (evs \u fv_tt A1) E (typ_mu A1) (typ_mu A1)).
  { unfold K. split.
    - intros X HXe HXd.
      pose proof (notin_union_2 X evs (fv_tt A1) HXe) as HXfv.
      apply pos_rec_t with (L := L).
      + exact HXfv.
      + intros Y HY. apply notin_union_1 in HY.
        destruct (IHf Y HY) as [_ [T1 _]]. exact T1.
    - split.
      + intros Z HbZ HZe.
        pose proof (notin_union_2 Z evs (fv_tt A1) HZe) as HZfv.
        apply pos_rec_t with (L := L).
        * exact HZfv.
        * intros Y HY. apply notin_union_1 in HY.
          destruct (IHf Y HY) as [_ [T1 _]]. exact T1.
      + intros Z HbZ HZe.
        pose proof (notin_union_2 Z evs (fv_tt A1) HZe) as HZfv.
        apply pos_rec_t with (L := L).
        * exact HZfv.
        * intros Y HY. apply notin_union_1 in HY.
          destruct (IHf Y HY) as [_ [T1 _]]. exact T1. }
  destruct HK as [HKf [HKa HKn]].
  split. { exact HwfE. }
  split.
  { apply type_mu with (L := L). intros X HX.
    destruct (IHf X HX) as [_ [T1 _]]. exact T1. }
  split.
  { apply type_mu with (L := L). intros X HX.
    destruct (IHf X HX) as [_ [_ [T2 _]]]. exact T2. }
  split.
  { apply sam2_rec with (L := (L \u evs) \u fv_tt A1).
    + intros X HX.
      pose proof (notin_union_1 X (L \u evs) (fv_tt A1) HX) as HXa2.
      apply notin_union_1 in HXa2.
      destruct (IHf X HXa2) as [_ [_ [_ [Hsub _]]]].
      rewrite drop_im_env_cons in Hsub. simpl in Hsub. exact Hsub.
    + intros X HX.
      pose proof (notin_union_2 X (L \u evs) (fv_tt A1) HX) as HXf.
      pose proof (notin_union_1 X (L \u evs) (fv_tt A1) HX) as HXa2.
      apply notin_union_1 in HXa2.
      apply pos_rec_t with (L := L).
      * exact HXf.
      * intros Y HY. apply notin_union_1 in HY.
        destruct (IHf Y HY) as [_ [T1 _]]. exact T1. }
  { unfold K. split.
    + exact HKf.
    + split; [exact HKa | exact HKn]. }
Qed.

(* ============================================================ *)
(* Syntactic parity of occurrences                              *)
(* ============================================================ *)

(* Occurrence of a free variable at a given (arrow-domain) parity *)
Inductive occurs (X:atom) : typ -> nat -> Prop :=
| occurs_here : occurs X (typ_fvar X) 0
| occurs_arrow_l : forall A1 A2 q,
    occurs X A1 q -> occurs X (typ_arrow A1 A2) (S q)
| occurs_arrow_r : forall A1 A2 q,
    occurs X A2 q -> occurs X (typ_arrow A1 A2) q
| occurs_mu : forall A q,
    occurs X A q -> occurs X (typ_mu A) q.

Fixpoint flipn (q:nat) (m:IsoMode) : IsoMode :=
  match q with
  | 0 => m
  | S q' => flip_im (flipn q' m)
  end.

Lemma flipn_flip : forall q m, flipn q (flip_im m) = flip_im (flipn q m).
Proof.
  induction q; intros m; simpl; auto.
  rewrite IHq. rewrite flip_im_invol. reflexivity.
Qed.

Lemma flipn_neg_of_flipn : forall q m, flipn q m = Neg -> flipn (S q) m = Pos.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma flip_im_eq_Pos : forall m, flip_im m = Pos -> m = Neg.
Proof. destruct m; simpl; auto; discriminate. Qed.

Lemma flip_im_eq_Neg : forall m, flip_im m = Neg -> m = Pos.
Proof. destruct m; simpl; auto; discriminate. Qed.

Lemma occurs_fv : forall X A q, occurs X A q -> X \in fv_tt A.
Proof.
  intros X A q H.
  induction H as [ | A1 A2 q Hocc IHH | A1 A2 q Hocc IHH | A q Hocc IHH ];
    simpl.
  - apply AtomSetImpl.singleton_2. reflexivity.
  - apply AtomSetImpl.union_2. exact IHH.
  - apply AtomSetImpl.union_3. exact IHH.
  - exact IHH.
Qed.

(* More parity facts *)

Lemma occurs_open_rec : forall X Y K A q,
  occurs X A q -> X <> Y -> occurs X (open_tt_rec K (typ_fvar Y) A) q.
Proof.
  intros X Y K A q H. revert K Y.
  induction H as [ | A1 A2 q Hocc IHH | A1 A2 q Hocc IHH | A q Hocc IHH ];
    intros K Y HXY.
  - simpl. apply occurs_here.
  - simpl. apply occurs_arrow_l. apply IHH. auto.
  - simpl. apply occurs_arrow_r. apply IHH. auto.
  - simpl. apply occurs_mu. apply IHH. auto.
Qed.

Lemma occurs_open_rec_inv : forall X Y K A q,
  X <> Y -> occurs X (open_tt_rec K (typ_fvar Y) A) q -> occurs X A q.
Proof.
  intros X Y K0 A. revert K0.
  induction A as [ | | n | a | A1 IH1 | A1 IH1 A2 IH2 ];
    intros K q HXY Hocc.
  - simpl in Hocc. inversion Hocc.
  - simpl in Hocc. inversion Hocc.
  - simpl in Hocc. destruct (K === n) as [E|E]; simpl in Hocc.
    + exfalso. apply HXY. symmetry. inversion Hocc. reflexivity.
    + inversion Hocc.
  - simpl in Hocc. inversion Hocc. subst. apply occurs_here.
  - simpl in Hocc. inversion Hocc. subst. apply occurs_mu. eapply IH1; eauto.
  - simpl in Hocc. inversion Hocc; subst.
    + apply occurs_arrow_l. eapply IH1; eauto.
    + apply occurs_arrow_r. eapply IH2; eauto.
Qed.

Lemma occurs_fvar_inv : forall X Y q, occurs X (typ_fvar Y) q -> X = Y /\ q = 0.
Proof. intros. inversion H. auto. Qed.

Lemma occurs_arrow_inv : forall X A1 A2 q,
  occurs X (typ_arrow A1 A2) q ->
  (exists q', q = S q' /\ occurs X A1 q') \/ occurs X A2 q.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma occurs_mu_inv : forall X A q, occurs X (typ_mu A) q -> occurs X A q.
Proof. intros. inversion H; subst; auto. Qed.

Lemma occurs_nat_false : forall X q, occurs X typ_nat q -> False.
Proof. intros. inversion H. Qed.

Lemma occurs_top_false : forall X q, occurs X typ_top q -> False.
Proof. intros. inversion H. Qed.

Lemma posvar_same_occurs_aux : forall m X A B,
  posvar m X A B ->
  forall q C, A = C -> B = C -> occurs X C q -> flipn q m = Pos.
Proof.
  intros m X A B Hpos. induction Hpos as
    [ X m
    | X A m Hty
    | X A m Hty
    | X
    | X Y m HXY
    | X m A1 A2 B1 B2 Hp1 IH1 Hp2 IH2
    | X m A B L H1 IH1 H2 IH2
    | A X m L Hfv H1 IH1 ];
    intros q C HC1 HC2 Hocc.
  - (* nat *) subst. exfalso. eapply occurs_nat_false; eauto.
  - (* top *) subst. exfalso. eapply occurs_top_false; eauto.
  - (* top_flip *) subst. exfalso. eapply occurs_top_false; eauto.
  - (* fvar_x *) subst. destruct (occurs_fvar_inv X X q Hocc) as [_ Hq].
    subst. reflexivity.
  - (* fvar_y *) subst. destruct (occurs_fvar_inv X Y q Hocc) as [HX _].
    subst. exfalso. apply HXY. reflexivity.
  - (* arrow *)
    subst. injection HC2 as HB1 HB2.
    destruct (occurs_arrow_inv X A1 A2 q Hocc) as [[q' [Hq Hc]] | Hc].
    + subst q. specialize (IH1 q' A1 HB1 eq_refl Hc).
      rewrite flipn_flip in IH1. simpl. exact IH1.
    + specialize (IH2 q A2 eq_refl HB2 Hc). exact IH2.
  - (* rec *)
    subst. injection HC2 as HAB. subst B.
    eapply occurs_mu_inv in Hocc.
    destruct (atom_fresh (L \u {{X}})) as [Y HY].
    pose proof (notin_union_2 Y L (singleton X) HY) as HYX.
    assert (HXY : X <> Y) by (apply (notin_singleton_1 X Y); exact HYX).
    specialize (H1 Y HY).
    specialize (IH1 Y HY q (open_tt A Y) eq_refl eq_refl).
    apply IH1. apply occurs_open_rec; auto.
  - (* rec_t *)
    subst. eapply occurs_mu_inv in Hocc.
    exfalso. apply Hfv. eapply occurs_fv. exact Hocc.
Qed.

Lemma posvar_same_occurs : forall m X C q,
  posvar m X C C -> occurs X C q -> flipn q m = Pos.
Proof. intros. eapply posvar_same_occurs_aux; eauto. Qed.

Lemma sub_sound_aux : forall im cm evs E A B,
  Rules.Sub im cm evs E A B ->
  Rules.wf_env E /\ type A /\ type B /\
  sub_amber2 (drop_im_env E) A B /\ K im evs E A B.
Proof.
  intros im cm evs E A B H.
  induction H as
    [ E im Hwf
    | E im Hwf
    | E im A Hwf HWFS Hne
    | E X im Hwf Hb
    | E X im Hwf Hb
    | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm im H1 IH1 H2 IH2 Hcomp
    | L A1 A2 evs E im Hf IHf
    | L A1 A2 evs E im Hf IHf
    | L A1 A2 evs E im Hf IHf
    | im cm evs evs' E A1 A2 H1 IH1 Heq ].
  - (* Sa_nat *)
    split. { exact Hwf. }
    split. { apply type_nat. }
    split. { apply type_nat. }
    split. { apply sam2_nat. apply Rules_wf_env_drop. exact Hwf. }
    { unfold K. split.
      + intros X HXe HXd. apply pos_nat.
      + split; intros; apply pos_nat. }
  - (* Sa_top_eq *)
    split. { exact Hwf. }
    split. { apply type_top. }
    split. { apply type_top. }
    split. { apply sam2_top. apply WFS_top. apply Rules_wf_env_drop. exact Hwf. }
    { unfold K. split.
      + intros X HXe HXd. apply pos_top. apply type_top.
      + split; intros; apply pos_top; apply type_top. }
  - (* Sa_top_lt *)
    split. { exact Hwf. }
    split. { apply Rules_WFS_type with (E := E). exact HWFS. }
    split. { apply type_top. }
    split. { apply sam2_top. apply Rules_WFS_drop. exact HWFS.
             apply Rules_wf_env_drop. exact Hwf. }
    { unfold K. split.
      + intros X HXe HXd. apply pos_top.
        apply Rules_WFS_type with (E := E). exact HWFS.
      + split; intros; apply pos_top;
          apply Rules_WFS_type with (E := E); exact HWFS. }
  - (* Sa_fvar_pos *)
    split. { exact Hwf. }
    split. { apply type_var. }
    split. { apply type_var. }
    split. { apply sam2_fvar.
             eapply binds_drop_im with (b := Rules.bind_sub im). exact Hb.
             apply Rules_wf_env_drop. exact Hwf. }
    { unfold K. split.
      + intros Y HYe HYd. apply pos_fvar_y.
        intro HYX. subst Y. apply HYd. eapply binds_In. exact Hb.
      + split.
        * intros Z HbZ HZe. destruct (Z == X) as [HZx|HZx].
          -- subst Z. apply pos_fvar_x.
          -- apply pos_fvar_y. auto.
        * intros Z HbZ HZe. destruct (Z == X) as [HZx|HZx].
          -- subst Z. exfalso.
             pose proof (binds_unique Rules.binding X (Rules.bind_sub im)
                           (Rules.bind_sub (flip_im im)) E Hb HbZ
                           (wf_env_uniq E Hwf)) as Hbeq.
             injection Hbeq as Hfim. apply flip_im_neq with im. exact Hfim.
          -- apply pos_fvar_y. auto. }
  - (* Sa_fvar_neg *)
    split. { exact Hwf. }
    split. { apply type_var. }
    split. { apply type_var. }
    split. { apply sam2_fvar.
             eapply binds_drop_im with (b := Rules.bind_sub (flip_im im)). exact Hb.
             apply Rules_wf_env_drop. exact Hwf. }
    { unfold K. split.
      + intros Y HYe HYd. apply pos_fvar_y.
        intro HYx. apply (notin_singleton_1 X Y HYe). symmetry. exact HYx.
      + split.
        * intros Z HbZ HZe. apply pos_fvar_y.
          intro HZx. apply (notin_singleton_1 X Z HZe). symmetry. exact HZx.
        * intros Z HbZ HZe. apply pos_fvar_y.
          intro HZx. apply (notin_singleton_1 X Z HZe). symmetry. exact HZx. }
  - (* Sa_arrow *)
    destruct IH1 as [Hwf1 [HB1 [HA1 [Hsub1 HK1]]]].
    destruct IH2 as [Hwf2 [HA2 [HB2 [Hsub2 HK2]]]].
    destruct HK1 as [HK1f [HK1a HK1n]].
    destruct HK2 as [HK2f [HK2a HK2n]].
    split. { exact Hwf1. }
    split. { apply type_arrow; auto. }
    split. { apply type_arrow; auto. }
    split. { apply sam2_arrow; auto. }
    { unfold K. split.
      + intros X HXe HXd.
        pose proof (notin_union_1 X evs1 evs2 HXe) as HX1.
        pose proof (notin_union_2 X evs1 evs2 HXe) as HX2.
        apply pos_arrow.
        * apply HK1f; auto.
        * apply HK2f; auto.
      + split.
        * intros Z HbZ HZe.
          pose proof (notin_union_1 Z evs1 evs2 HZe) as HZ1.
          pose proof (notin_union_2 Z evs1 evs2 HZe) as HZ2.
          apply pos_arrow.
          -- apply HK1n. rewrite flip_im_invol. exact HbZ. exact HZ1.
          -- apply HK2a. exact HbZ. exact HZ2.
        * intros Z HbZ HZe.
          pose proof (notin_union_1 Z evs1 evs2 HZe) as HZ1.
          pose proof (notin_union_2 Z evs1 evs2 HZe) as HZ2.
          apply pos_arrow.
          -- apply HK1a. exact HbZ. exact HZ1.
          -- apply HK2n. exact HbZ. exact HZ2. }
  - (* Sa_rec_lt *)
    apply sound_rec_common with (L := L). exact IHf.
  - (* Sa_rec_eq_notin *)
    apply sound_rec_common with (L := L). exact IHf.
  - (* Sa_rec_eq_in *)
    apply sound_rec_in with (L := L).
    + exact Hf.
    + exact IHf.
  - (* Sa_evs_proper *)
    destruct IH1 as [Hwf [HA [HB [Hsub HK]]]].
    destruct HK as [HKf [HKa HKn]].
    split. { exact Hwf. }
    split. { exact HA. }
    split. { exact HB. }
    split. { exact Hsub. }
    { unfold K. split.
      + intros X HXe HXd. apply HKf; auto.
        intro Hx. apply HXe. apply (proj1 (Heq X)). exact Hx.
      + split.
        * intros Z HbZ HZe. apply HKa; auto.
          intro Hx. apply HZe. apply (proj1 (Heq Z)). exact Hx.
        * intros Z HbZ HZe. apply HKn; auto.
          intro Hx. apply HZe. apply (proj1 (Heq Z)). exact Hx. }
Qed.

Theorem pos_esa_sound: forall im cm evs E A B,
  Sub im cm evs E A B ->
  sub_amber2 (map drop_im E) A B.
Proof.
  intros im cm evs E A B H.
  destruct (sub_sound_aux im cm evs E A B H) as [_ [_ [_ [Hs _]]]].
  exact Hs.
Qed.

(* ============================================================ *)
(* Completeness infrastructure                                   *)
(* ============================================================ *)

Fixpoint lookup (X:atom) (E:Rules.env) : option Rules.binding :=
  match E with
  | nil => None
  | (Y,b) :: E' => if X == Y then Some b else lookup X E'
  end.

Lemma lookup_cons_eq : forall X E b, lookup X (X ~ b ++ E) = Some b.
Proof. intros. simpl. destruct (X == X) as [E0|E0]; auto. exfalso; apply E0; reflexivity. Qed.
Lemma lookup_cons_neq : forall X Y E b, X <> Y -> lookup X (Y ~ b ++ E) = lookup X E.
Proof. intros. simpl. destruct (X == Y) as [E0|E0]; auto. exfalso; apply H; exact E0. Qed.
Lemma lookup_binds : forall X E b, lookup X E = Some b -> binds X b E.
Proof.
  intros X E. induction E as [| (Y,c) E' IH]; intros b H; simpl in H; try discriminate.
  destruct (X == Y) as [E0|E0].
  - injection H as ->. left. subst. reflexivity.
  - right. apply IH. exact H.
Qed.

Fixpoint occ_parity (k:nat) (p:bool) (A:typ) : bool :=
  match A with
  | typ_top => false | typ_nat => false
  | typ_bvar n => if k === n then p else false
  | typ_fvar _ => false
  | typ_arrow A1 A2 => orb (occ_parity k (negb p) A1) (occ_parity k p A2)
  | typ_mu B => occ_parity (S k) p B
  end.
Definition occ_any (k:nat) (A:typ) : bool :=
  orb (occ_parity k false A) (occ_parity k true A).
Lemma occ_any_arrow : forall k A1 A2,
  occ_any k (typ_arrow A1 A2) = orb (occ_any k A1) (occ_any k A2).
Proof.
  intros. unfold occ_any. simpl.
  destruct (occ_parity k false A1); destruct (occ_parity k true A1);
  destruct (occ_parity k false A2); destruct (occ_parity k true A2);
  simpl; try reflexivity.
Qed.
Lemma occ_any_bvar : forall k n,
  occ_any k (typ_bvar n) = if k === n then true else false.
Proof.
  intros. unfold occ_any. simpl.
  destruct (k === n) as [E|E]; simpl; destruct (k === n) as [E2|E2]; simpl; auto.
Qed.
Lemma neq_succ : forall a b, a <> b -> S a <> S b.
Proof. intros a b H0 H1. apply H0. injection H1. auto. Qed.
Lemma zero_neq_succ : forall b, 0 <> S b.
Proof. intros. discriminate. Qed.

Lemma occ_parity_self_open : forall k p X A,
  occ_parity k p (open_tt_rec k (typ_fvar X) A) = false.
Proof.
  intros k p X A. revert k p.
  induction A as [ | | n | a | A1 IH1 | A1 IH1 A2 IH2 ]; intros k p.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. destruct (k === n) as [E|E].
    + simpl. reflexivity.
    + simpl. destruct (k === n) as [E2|E2]; [exfalso; apply E; exact E2 | reflexivity].
  - simpl. reflexivity.
  - simpl. rewrite IH1. reflexivity.
  - simpl. rewrite IH1, IH2. reflexivity.
Qed.
Lemma occ_parity_open_neq : forall k L p X A, k <> L ->
  occ_parity k p (open_tt_rec L (typ_fvar X) A) = occ_parity k p A.
Proof.
  intros k L p X A HKL. revert k L p HKL.
  induction A as [ | | n | a | A1 IH1 | A1 IH1 A2 IH2 ]; intros k L p HKL.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. destruct (L === n) as [E1|E1]; simpl.
    + destruct (k === n) as [E2|E2]; simpl.
      * exfalso. apply HKL. transitivity n; auto.
      * reflexivity.
    + reflexivity.
  - simpl. reflexivity.
  - simpl. eapply IH1. apply neq_succ. exact HKL.
  - simpl. rewrite (IH1 k L (negb p) HKL). rewrite (IH2 k L p HKL). reflexivity.
Qed.
Lemma occ_parity_open : forall k p L X A,
  occ_parity k p (open_tt_rec L (typ_fvar X) A)
    = if k === L then false else occ_parity k p A.
Proof.
  intros. destruct (k === L) as [E|E].
  - subst. apply occ_parity_self_open.
  - apply occ_parity_open_neq. auto.
Qed.
Lemma occ_any_open : forall k L X A,
  occ_any k (open_tt_rec L (typ_fvar X) A)
    = if k === L then false else occ_any k A.
Proof.
  intros. unfold occ_any. rewrite occ_parity_open, occ_parity_open.
  destruct (k === L); simpl; [reflexivity|].
  destruct (occ_parity k false A); destruct (occ_parity k true A); reflexivity.
Qed.
Lemma occ_any_open_neq : forall k L X A, k <> L ->
  occ_any k (open_tt_rec L (typ_fvar X) A) = occ_any k A.
Proof.
  intros. rewrite occ_any_open. destruct (k === L) as [E|E]; auto.
  exfalso. apply H. exact E.
Qed.
Lemma occ_any_self_open : forall k X A,
  occ_any k (open_tt_rec k (typ_fvar X) A) = false.
Proof.
  intros. rewrite occ_any_open. destruct (k === k) as [E|E]; auto.
  exfalso. apply E. reflexivity.
Qed.

Lemma fv_open_rec : forall L X A,
  fv_tt (open_tt_rec L (typ_fvar X) A)
    [=] union (fv_tt A) (if occ_any L A then singleton X else emp).
Proof.
  intros L X A. revert L.
  induction A as [ | | n | a | A1 IH1 | A1 IH1 A2 IH2 ]; intros L.
  - simpl. fsetdec.
  - simpl. fsetdec.
  - simpl. rewrite occ_any_bvar.
    destruct (L === n) as [E|E]; simpl;
    destruct (L === n) as [E2|E2]; simpl; fsetdec.
  - simpl. fsetdec.
  - simpl. apply IH1.
  - simpl. rewrite IH1, IH2, occ_any_arrow.
    destruct (occ_any L A1); destruct (occ_any L A2); simpl; fsetdec.
Qed.

Fixpoint contam (k:nat) (p:bool) (A:typ) : bool :=
  match A with
  | typ_top => false | typ_nat => false | typ_fvar _ => false
  | typ_bvar n => if k === n then p else false
  | typ_arrow A1 A2 => orb (contam k (negb p) A1) (contam k p A2)
  | typ_mu B =>
      if contam 0 false B
      then orb (contam (S k) p B) (occ_any (S k) B)
      else contam (S k) p B
  end.

Fixpoint reflEvs (m:IsoMode) (E:Rules.env) (A:typ) : atoms :=
  match A with
  | typ_top => emp | typ_nat => emp | typ_bvar _ => emp
  | typ_fvar X =>
      match lookup X E with
      | Some (Rules.bind_sub a) =>
          match a, m with Neg,Neg => emp | Pos,Pos => emp | _,_ => singleton X end
      | _ => emp
      end
  | typ_arrow A1 A2 => union (reflEvs (flip_im m) E A1) (reflEvs m E A2)
  | typ_mu B => if contam 0 false B
                then union (reflEvs m E B) (fv_tt B)
                else reflEvs m E B
  end.

Lemma reflEvs_fvar : forall mi E X,
  reflEvs mi E (typ_fvar X) =
  match lookup X E with
  | Some (Rules.bind_sub a) =>
      match a, mi with Neg,Neg => emp | Pos,Pos => emp | _,_ => singleton X end
  | _ => emp
  end.
Proof. reflexivity. Qed.
Lemma reflEvs_bvar : forall mi E n, reflEvs mi E (typ_bvar n) = emp.
Proof. reflexivity. Qed.
Lemma reflEvs_top : forall mi E, reflEvs mi E typ_top = emp.
Proof. reflexivity. Qed.
Lemma reflEvs_nat : forall mi E, reflEvs mi E typ_nat = emp.
Proof. reflexivity. Qed.
Lemma reflEvs_mu : forall m E T,
  reflEvs m E (typ_mu T)
  = if contam 0 false T then union (reflEvs m E T) (fv_tt T)
    else reflEvs m E T.
Proof. reflexivity. Qed.
Lemma reflEvs_arrow : forall m E A1 A2,
  reflEvs m E (typ_arrow A1 A2)
  = union (reflEvs (flip_im m) E A1) (reflEvs m E A2).
Proof. reflexivity. Qed.
Lemma contam_bvar_eq : forall k p n, k = n -> contam k p (typ_bvar n) = p.
Proof. intros. subst. simpl. destruct (n === n) as [E|E]; auto. exfalso; apply E; reflexivity. Qed.
Lemma contam_bvar_neq : forall k p n, k <> n -> contam k p (typ_bvar n) = false.
Proof. intros. simpl. destruct (k === n) as [E|E]; auto. exfalso; apply H; exact E. Qed.

Lemma contam_open_neq : forall k L p X A, k <> L ->
  contam k p (open_tt_rec L (typ_fvar X) A) = contam k p A.
Proof.
  intros k L p X A HKL. revert k L p HKL.
  induction A as [ | | n | a | A1 IH1 | A1 IH1 A2 IH2 ]; intros k L p HKL.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. destruct (L === n) as [E1|E1]; simpl.
    + destruct (k === n) as [E2|E2]; simpl.
      * exfalso. apply HKL. transitivity n; auto.
      * reflexivity.
    + reflexivity.
  - simpl. reflexivity.
  - simpl.
    rewrite (IH1 0 (S L) false (zero_neq_succ L)).
    rewrite (IH1 (S k) (S L) p (neq_succ _ _ HKL)).
    rewrite (occ_any_open_neq (S k) (S L) X A1 (neq_succ _ _ HKL)).
    destruct (contam 0 false A1); simpl; reflexivity.
  - simpl. rewrite (IH1 k L (negb p) HKL). rewrite (IH2 k L p HKL). reflexivity.
Qed.
Lemma contam_self_open : forall k p X A,
  contam k p (open_tt_rec k (typ_fvar X) A) = false.
Proof.
  intros k p X A. revert k p.
  induction A as [ | | n | a | A1 IH1 | A1 IH1 A2 IH2 ]; intros k p.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. destruct (k === n) as [E|E].
    + simpl. reflexivity.
    + simpl. destruct (k === n) as [E2|E2]; [exfalso; apply E; exact E2 | reflexivity].
  - simpl. reflexivity.
  - simpl.
    rewrite (contam_open_neq 0 (S k) false X A1 (zero_neq_succ k)).
    rewrite (IH1 (S k) p).
    rewrite (occ_any_self_open (S k) X A1).
    destruct (contam 0 false A1); simpl; reflexivity.
  - simpl. rewrite IH1, IH2. reflexivity.
Qed.
Lemma contam_open : forall k p L X A,
  contam k p (open_tt_rec L (typ_fvar X) A)
    = if k === L then false else contam k p A.
Proof.
  intros. destruct (k === L) as [E|E].
  - subst. apply contam_self_open.
  - apply contam_open_neq. auto.
Qed.

Definition fb (p:bool) (m:IsoMode) : IsoMode := if p then flip_im m else m.
Lemma fb_negb : forall p m, fb (negb p) m = flip_im (fb p m).
Proof. intros. destruct p; simpl; [rewrite flip_im_invol|]; reflexivity. Qed.
Lemma contam_open_zero_succ : forall k X B,
  contam 0 false (open_tt_rec (S k) (typ_fvar X) B) = contam 0 false B.
Proof.
  intros. rewrite contam_open. destruct (0 === S k) as [E|E]; auto.
  exfalso. apply (zero_neq_succ k). exact E.
Qed.

Lemma reflEvs_open_gen : forall m mi p E X k A,
  mi = fb p m ->
  X \notin fv_tt A ->
  reflEvs mi (X ~ Rules.bind_sub m ++ E) (open_tt_rec k (typ_fvar X) A)
   [=] union (reflEvs mi E A) (if contam k p A then singleton X else emp).
Proof.
  intros m mi p E X k A Hmi HX. revert k p mi m Hmi.
  induction A as [ | | n | a | A1 IH1 | A1 IH1 A2 IH2 ];
    intros k p mi m Hmi.
  - simpl. fsetdec.
  - simpl. fsetdec.
  - (* bvar *)
    destruct (k === n) as [E1|E1].
    + subst k. cbn [open_tt_rec].
      destruct (n === n) as [E2|E2]; [| exfalso; apply E2; reflexivity].
      rewrite reflEvs_fvar. rewrite lookup_cons_eq. rewrite Hmi.
      rewrite reflEvs_bvar. rewrite (contam_bvar_eq n p n eq_refl).
      destruct p; destruct m; simpl; fsetdec.
    + cbn [open_tt_rec].
      destruct (k === n) as [E2|E2]; [exfalso; apply E1; exact E2 |].
      rewrite reflEvs_bvar. rewrite reflEvs_bvar.
      rewrite (contam_bvar_neq k p n E1).
      simpl. fsetdec.
  - (* fvar a *)
    cbn [open_tt_rec].
    assert (HaX : a <> X).
    { intro H. apply HX. subst a. apply AtomSetImpl.singleton_2. reflexivity. }
    rewrite reflEvs_fvar. rewrite reflEvs_fvar.
    rewrite (lookup_cons_neq a X E (Rules.bind_sub m) HaX).
    replace (contam k p (typ_fvar a)) with false by reflexivity.
    simpl. fsetdec.
  - (* mu A1 *)
    simpl in HX. simpl.
    rewrite (contam_open_zero_succ k X A1).
    pose proof (IH1 HX (S k) p mi m Hmi) as Hsub.
    pose proof (fv_open_rec (S k) X A1) as Hfv.
    destruct (contam 0 false A1) eqn:Eb;
    destruct (contam (S k) p A1) eqn:Ex;
    destruct (occ_any (S k) A1) eqn:Ea; simpl; fsetdec.
  - (* arrow A1 A2 *)
    simpl in HX.
    pose proof (notin_union_1 X (fv_tt A1) (fv_tt A2) HX) as HA1.
    pose proof (notin_union_2 X (fv_tt A1) (fv_tt A2) HX) as HA2.
    simpl.
    assert (Hmi1 : flip_im mi = fb (negb p) m).
    { rewrite fb_negb. rewrite <- Hmi. reflexivity. }
    pose proof (IH1 HA1 k (negb p) (flip_im mi) m Hmi1) as Hs1.
    pose proof (IH2 HA2 k p mi m Hmi) as Hs2.
    destruct (contam k (negb p) A1) eqn:E1;
    destruct (contam k p A2) eqn:E2; simpl; fsetdec.
Qed.

Lemma Sub_reflect_spec : forall m E A,
  Rules.wf_env E -> type A ->
  (forall Y, Y \in fv_tt A -> exists a, lookup Y E = Some (Rules.bind_sub a)) ->
  Rules.Sub m Eq (reflEvs m E A) E A A.
Proof.
  intros m E A Hwf Hty. revert m E Hwf.
  induction Hty as [ | | X | T1 T2 Ht1 IH1 Ht2 IH2 | L T Ht IH ];
    intros m E Hwf Hfv.
  - rewrite reflEvs_top. apply Sa_top_eq. exact Hwf.
  - rewrite reflEvs_nat. apply Sa_nat. exact Hwf.
  - rewrite reflEvs_fvar.
    destruct (lookup X E) as [b|] eqn:Eb.
    + destruct b as [a|T].
      * destruct a, m; simpl.
        -- apply Sa_fvar_pos. exact Hwf. apply lookup_binds. exact Eb.
        -- apply Sa_fvar_neg with (im := Pos). exact Hwf.
           simpl. apply lookup_binds. exact Eb.
        -- apply Sa_fvar_neg with (im := Neg). exact Hwf.
           simpl. apply lookup_binds. exact Eb.
        -- apply Sa_fvar_pos. exact Hwf. apply lookup_binds. exact Eb.
      * exfalso. destruct (Hfv X) as [a Ha].
        { apply AtomSetImpl.singleton_2. reflexivity. }
        rewrite Eb in Ha. discriminate.
    + exfalso. destruct (Hfv X) as [a Ha].
      { apply AtomSetImpl.singleton_2. reflexivity. }
      rewrite Eb in Ha. discriminate.
  - rewrite reflEvs_arrow.
    eapply Sa_arrow with (cm1 := Eq) (cm2 := Eq)
      (evs1 := reflEvs (flip_im m) E T1) (evs2 := reflEvs m E T2).
    + apply IH1; auto. intros Y HY. apply Hfv.
      apply AtomSetImpl.union_2. exact HY.
    + apply IH2; auto. intros Y HY. apply Hfv.
      apply AtomSetImpl.union_3. exact HY.
    + simpl. destruct (AtomSetImpl.is_empty (reflEvs (flip_im m) E T1)); reflexivity.
  - rewrite reflEvs_mu.
    destruct (contam 0 false T) eqn:Ec.
    + (* eq_in *)
      remember (reflEvs m E T) as S0 eqn:ES0.
      eapply Sa_rec_eq_in with (L := (L \u dom E) \u fv_tt T) (evs := S0).
      intros X HX.
      pose proof (notin_union_1 X (L \u dom E) (fv_tt T) HX) as HXa.
      pose proof (notin_union_2 X (L \u dom E) (fv_tt T) HX) as HXf.
      pose proof (notin_union_1 X L (dom E) HXa) as HXL.
      pose proof (notin_union_2 X L (dom E) HXa) as HXd.
      assert (Hwf' : Rules.wf_env (X ~ Rules.bind_sub m ++ E)).
      { apply Rules.wf_env_sub; auto. }
      assert (Hfv' : forall Y, Y \in fv_tt (open_tt T X) ->
              exists a, lookup Y (X ~ Rules.bind_sub m ++ E) = Some (Rules.bind_sub a)).
      { intros Y HY.
        pose proof (proj1 (fv_open_rec 0 X T Y) HY) as HYr.
        apply AtomSetImpl.union_1 in HYr. destruct HYr as [HYT|HYrest].
        - destruct (Hfv Y HYT) as [a Ha].
          exists a. rewrite (lookup_cons_neq Y X E (Rules.bind_sub m)); auto.
          intro Hcontra. subst Y. apply HXf. exact HYT.
        - destruct (occ_any 0 T) eqn:Eo.
          + apply AtomSetImpl.singleton_1 in HYrest. subst Y.
            exists m. apply lookup_cons_eq.
          + exfalso. apply (notin_empty_1 Y). exact HYrest. }
      pose proof (IH X HXL m (X ~ Rules.bind_sub m ++ E) Hwf' Hfv') as HsubX.
      pose proof (reflEvs_open_gen m m false E X 0 T eq_refl HXf) as Hgen.
      simpl in Hgen. rewrite <- ES0 in Hgen.
      eapply Sa_evs_proper.
      * exact HsubX.
      * etransitivity.
        -- exact Hgen.
        -- rewrite Ec. fsetdec.
    + (* eq_notin *)
      remember (reflEvs m E T) as S0 eqn:ES0.
      eapply Sa_rec_eq_notin with (L := (L \u dom E) \u fv_tt T) (evs := S0).
      intros X HX.
      pose proof (notin_union_1 X (L \u dom E) (fv_tt T) HX) as HXa.
      pose proof (notin_union_2 X (L \u dom E) (fv_tt T) HX) as HXf.
      pose proof (notin_union_1 X L (dom E) HXa) as HXL.
      pose proof (notin_union_2 X L (dom E) HXa) as HXd.
      assert (Hwf' : Rules.wf_env (X ~ Rules.bind_sub m ++ E)).
      { apply Rules.wf_env_sub; auto. }
      assert (Hfv' : forall Y, Y \in fv_tt (open_tt T X) ->
              exists a, lookup Y (X ~ Rules.bind_sub m ++ E) = Some (Rules.bind_sub a)).
      { intros Y HY.
        pose proof (proj1 (fv_open_rec 0 X T Y) HY) as HYr.
        apply AtomSetImpl.union_1 in HYr. destruct HYr as [HYT|HYrest].
        - destruct (Hfv Y HYT) as [a Ha].
          exists a. rewrite (lookup_cons_neq Y X E (Rules.bind_sub m)); auto.
          intro Hcontra. subst Y. apply HXf. exact HYT.
        - destruct (occ_any 0 T) eqn:Eo.
          + apply AtomSetImpl.singleton_1 in HYrest. subst Y.
            exists m. apply lookup_cons_eq.
          + exfalso. apply (notin_empty_1 Y). exact HYrest. }
      pose proof (IH X HXL m (X ~ Rules.bind_sub m ++ E) Hwf' Hfv') as HsubX.
      pose proof (reflEvs_open_gen m m false E X 0 T eq_refl HXf) as Hgen.
      simpl in Hgen. rewrite <- ES0 in Hgen.
      eapply Sa_evs_proper.
      * exact HsubX.
      * etransitivity.
        -- exact Hgen.
        -- rewrite Ec. fsetdec.
Qed.

(* ============================================================ *)
(* Posvar inversion and free-variable bounds                    *)
(* ============================================================ *)

Lemma posvar_arrow_inv : forall q X A1 A2 B1 B2,
  posvar q X (typ_arrow A1 A2) (typ_arrow B1 B2) ->
  posvar (flip_im q) X B1 A1 /\ posvar q X A2 B2.
Proof. intros. inversion H. auto. Qed.

Lemma posvar_mu_inv : forall q X A B,
  posvar q X (typ_mu A) (typ_mu B) ->
  (exists L, B = A /\ X \notin fv_tt A /\
             (forall Y, Y \notin L \u {{X}} -> type (open_tt A Y)))
  \/
  (exists L,
     (forall Y, Y \notin L \u {{X}} -> posvar q X (open_tt A Y) (open_tt B Y))
     /\ (forall Y, Y \notin L \u {{X}} -> posvar Pos Y (open_tt A Y) (open_tt B Y))).
Proof.
  intros q X A B H.
  inversion H as [ | | | | | | X0 m0 A0 B0 L0 H1 H2 | A0 X0 m0 L0 Hfv H1 ]; subst.
  - right. exists L0. auto.
  - left. exists L0. auto.
Qed.

Lemma fv_open_in : forall X Y A,
  X \in fv_tt A -> X <> Y -> X \in fv_tt (open_tt A Y).
Proof.
  intros. apply (proj2 (fv_open_rec 0 Y A X)). apply AtomSetImpl.union_2. exact H.
Qed.

Lemma binds_sub_inv_dom : forall (X:atom) (b:Rules.binding) (E:Rules.env), binds X b E -> X \in dom E.
Proof. intros. eapply binds_In. exact H. Qed.

Lemma fv_dom_opens : forall L (E:env) A,
  (forall Y, Y \notin L -> forall X, X \in fv_tt (open_tt A Y) ->
      X \in dom (Y ~ bind_sub ++ E)) ->
  forall X, X \in fv_tt A -> X \in dom E.
Proof.
  intros L E A H X HX.
  destruct (atom_fresh ((L \u {{X}}) \u dom E)) as [Y HY].
  pose proof (notin_union_1 Y (L \u {{X}}) (dom E) HY) as HYa.
  pose proof (notin_union_2 Y (L \u {{X}}) (dom E) HY) as HYd.
  pose proof (notin_union_1 Y L (singleton X) HYa) as HYL.
  pose proof (notin_union_2 Y L (singleton X) HYa) as HYX.
  assert (HXY : X <> Y) by (apply (notin_singleton_1 X Y); exact HYX).
  pose proof (H Y HYL X (fv_open_in X Y A HX HXY)) as Hdom.
  simpl in Hdom.
  apply (AtomSetImpl.add_3 (s:=dom E) (x:=Y) (y:=X)).
  - intro Hcontra. apply HXY. symmetry. exact Hcontra.
  - exact Hdom.
Qed.

Lemma WFS_fv_dom : forall (E:env) A,
  WFS E A -> forall X, X \in fv_tt A -> X \in dom E.
Proof.
  intros E A H. induction H as
    [ E | E | X E Hb | E A B HA IHA HB IHB | L E A Hf IHf ];
    intros Y HY.
  - simpl in HY. exfalso. apply (notin_empty_1 Y). exact HY.
  - simpl in HY. exfalso. apply (notin_empty_1 Y). exact HY.
  - simpl in HY. apply AtomSetImpl.singleton_1 in HY. subst Y.
    eapply binds_In. exact Hb.
  - simpl in HY. apply AtomSetImpl.union_1 in HY. destruct HY as [H1|H2].
    + apply IHA. exact H1.
    + apply IHB. exact H2.
  - eapply fv_dom_opens with (L := L) (A := A). intros Z HZ. apply IHf. exact HZ. exact HY.
Qed.

Lemma sub_amber2_fv_dom : forall (E:env) A B,
  sub_amber2 E A B ->
  (forall X, X \in fv_tt A -> X \in dom E) /\
  (forall X, X \in fv_tt B -> X \in dom E).
Proof.
  intros E A B H. induction H as
    [ E Hwf
    | E A HWFS Hwf
    | E X Hb Hwf
    | E A1 A2 B1 B2 H1 IH1 H2 IH2
    | E A B L H1 IH1 H2 IH2 ].
  - split; intros X HX; simpl in HX;
      exfalso; apply (notin_empty_1 X); exact HX.
  - split.
    + intros X HX. eapply WFS_fv_dom; eauto.
    + intros X HX. simpl in HX. exfalso. apply (notin_empty_1 X). exact HX.
  - split; intros Y HY; simpl in HY; apply AtomSetImpl.singleton_1 in HY; subst Y;
      eapply binds_In; exact Hb.
  - split.
    + intros X HX. simpl in HX. apply AtomSetImpl.union_1 in HX.
      destruct HX as [HX|HX]; [ apply (proj2 IH1) | apply (proj1 IH2) ]; exact HX.
    + intros X HX. simpl in HX. apply AtomSetImpl.union_1 in HX.
      destruct HX as [HX|HX]; [ apply (proj1 IH1) | apply (proj2 IH2) ]; exact HX.
  - split.
    + eapply fv_dom_opens with (L := L) (A := A).
      intros Y HY X HX. exact ((proj1 (IH1 Y HY)) X HX).
    + eapply fv_dom_opens with (L := L) (A := B).
      intros Y HY X HX. exact ((proj2 (IH1 Y HY)) X HX).
Qed.

(* ============================================================ *)
(* Endpoint well-typedness for sub_amber2                       *)
(* ============================================================ *)

Lemma Task_WFS_type : forall (E:env) A, WFS E A -> type A.
Proof.
  intros E A H. induction H as
    [ E | E | X E Hb | E A B HA IHA HB IHB | L E A Hf IHf ].
  - apply type_top.
  - apply type_nat.
  - apply type_var.
  - apply type_arrow; auto.
  - apply type_mu with (L := L). auto.
Qed.

Lemma sub_amber2_type : forall (E:env) A B,
  sub_amber2 E A B -> type A /\ type B.
Proof.
  intros E A B H. induction H as
    [ E Hwf
    | E A HWFS Hwf
    | E X Hb Hwf
    | E A1 A2 B1 B2 H1 IH1 H2 IH2
    | E A B L H1 IH1 H2 IH2 ].
  - split; apply type_nat.
  - split. apply Task_WFS_type with (E := E); exact HWFS. apply type_top.
  - split; apply type_var.
  - destruct IH1 as [HB1 HA1]. destruct IH2 as [HA2 HB2].
    split; apply type_arrow; auto.
  - split; apply type_mu with (L := L);
      intros X HX; [ apply (proj1 (IH1 X HX)) | apply (proj2 (IH1 X HX)) ].
Qed.

(* ============================================================ *)
(* reflEvs is contained in fv                                   *)
(* ============================================================ *)

Lemma reflEvs_fv_subset : forall m E A X,
  X \in reflEvs m E A -> X \in fv_tt A.
Proof.
  intros m E A. revert m E.
  induction A as [ | | n | a | A1 IH1 | A1 IH1 A2 IH2 ];
    intros m E X HX.
  - rewrite reflEvs_top in HX. exfalso. apply (notin_empty_1 X). exact HX.
  - rewrite reflEvs_nat in HX. exfalso. apply (notin_empty_1 X). exact HX.
  - rewrite reflEvs_bvar in HX. exfalso. apply (notin_empty_1 X). exact HX.
  - rewrite reflEvs_fvar in HX.
    destruct (lookup a E) as [b|] eqn:Eb.
    + destruct b as [im|T]; [| exfalso; apply (notin_empty_1 X); exact HX].
      destruct im, m; simpl in HX.
      * exfalso. apply (notin_empty_1 X). exact HX.
      * apply AtomSetImpl.singleton_1 in HX. subst X.
        simpl. apply AtomSetImpl.singleton_2. reflexivity.
      * apply AtomSetImpl.singleton_1 in HX. subst X.
        simpl. apply AtomSetImpl.singleton_2. reflexivity.
      * exfalso. apply (notin_empty_1 X). exact HX.
    + exfalso. apply (notin_empty_1 X). exact HX.
  - rewrite reflEvs_mu in HX. simpl.
    destruct (contam 0 false A1) eqn:Ec.
    + apply AtomSetImpl.union_1 in HX. destruct HX as [HX|HX].
      * apply (IH1 m E X). exact HX.
      * exact HX.
    + apply (IH1 m E X). exact HX.
  - rewrite reflEvs_arrow in HX. simpl.
    apply AtomSetImpl.union_1 in HX. destruct HX as [HX|HX].
    + apply AtomSetImpl.union_2. apply (IH1 (flip_im m) E X). exact HX.
    + apply AtomSetImpl.union_3. apply (IH2 m E X). exact HX.
Qed.

Lemma reflEvs_fv_empty : forall m E A,
  fv_tt A [=] emp -> reflEvs m E A [=] emp.
Proof.
  intros m E A Hfv. intros X. split.
  - intro HX. pose proof (reflEvs_fv_subset m E A X HX) as Hmem.
    pose proof (proj1 (Hfv X) Hmem) as Hemp.
    exfalso. apply (notin_empty_1 X). exact Hemp.
  - intro HX. exfalso. apply (notin_empty_1 X). exact HX.
Qed.

(* ============================================================ *)
(* The protected-environment invariant                          *)
(* ============================================================ *)

Definition PC (m:IsoMode) (E:Rules.env) (A B:typ) : Prop :=
  forall Y a, lookup Y E = Some (Rules.bind_sub a) ->
    Y \in fv_tt A \u fv_tt B ->
    (a = m -> posvar Pos Y A B) /\ (a = flip_im m -> posvar Neg Y A B).

Lemma PC_arrow_l : forall m E A1 A2 B1 B2,
  PC m E (typ_arrow A1 A2) (typ_arrow B1 B2) ->
  PC (flip_im m) E B1 A1.
Proof.
  intros m E A1 A2 B1 B2 H. unfold PC in *.
  intros Y a Hlk HY.
  assert (Hpar : Y \in fv_tt (typ_arrow A1 A2) \u fv_tt (typ_arrow B1 B2)).
  { simpl. apply AtomSetImpl.union_1 in HY. destruct HY as [HY|HY].
    - apply AtomSetImpl.union_3. apply AtomSetImpl.union_2. exact HY.
    - apply AtomSetImpl.union_2. apply AtomSetImpl.union_2. exact HY. }
  destruct (H Y a Hlk Hpar) as [Hpos Hneg]. split.
  - intro Ha. subst a.
    apply (proj1 (posvar_arrow_inv Neg Y A1 A2 B1 B2 (Hneg eq_refl))).
  - intro Ha. rewrite flip_im_invol in Ha.
    apply (proj1 (posvar_arrow_inv Pos Y A1 A2 B1 B2 (Hpos Ha))).
Qed.

Lemma PC_arrow_r : forall m E A1 A2 B1 B2,
  PC m E (typ_arrow A1 A2) (typ_arrow B1 B2) ->
  PC m E A2 B2.
Proof.
  intros m E A1 A2 B1 B2 H. unfold PC in *.
  intros Y a Hlk HY.
  assert (Hpar : Y \in fv_tt (typ_arrow A1 A2) \u fv_tt (typ_arrow B1 B2)).
  { simpl. apply AtomSetImpl.union_1 in HY. destruct HY as [HY|HY].
    - apply AtomSetImpl.union_2. apply AtomSetImpl.union_3. exact HY.
    - apply AtomSetImpl.union_3. apply AtomSetImpl.union_3. exact HY. }
  destruct (H Y a Hlk Hpar) as [Hpos Hneg]. split.
  - intro Ha. apply (proj2 (posvar_arrow_inv Pos Y A1 A2 B1 B2 (Hpos Ha))).
  - intro Ha. apply (proj2 (posvar_arrow_inv Neg Y A1 A2 B1 B2 (Hneg Ha))).
Qed.

(* ============================================================ *)
(* Accumulating the cofinite freshness sets of posvar facts     *)
(* ============================================================ *)

Definition pmode (a m:IsoMode) : IsoMode :=
  match a, m with
  | Neg, Neg => Pos | Pos, Pos => Pos | _,_ => Neg
  end.

Lemma pmode_posvar_split : forall a m W C D,
  posvar (pmode a m) W C D ->
  (a = m -> posvar Pos W C D) /\ (a = flip_im m -> posvar Neg W C D).
Proof.
  intros a m W C D H. unfold pmode in H. destruct a, m; simpl in *;
    split; intros Hx; try exact H; try discriminate Hx.
Qed.

Lemma PC_fact : forall m E A B W a,
  PC m E A B -> lookup W E = Some (Rules.bind_sub a) ->
  W \in fv_tt A \u fv_tt B ->
  posvar (pmode a m) W A B.
Proof.
  intros. unfold PC in H. destruct (H W a H0 H1) as [Hp Hn].
  unfold pmode. destruct a, m; simpl.
  - apply Hp. reflexivity.
  - apply Hn. reflexivity.
  - apply Hn. reflexivity.
  - apply Hp. reflexivity.
Qed.

Definition PCopen (m:IsoMode) (E:Rules.env) (A B:typ) (Y:atom) : Prop :=
  forall W a, lookup W E = Some (Rules.bind_sub a) ->
    W \in fv_tt (open_tt A Y) \u fv_tt (open_tt B Y) ->
    (a = m -> posvar Pos W (open_tt A Y) (open_tt B Y)) /\
    (a = flip_im m -> posvar Neg W (open_tt A Y) (open_tt B Y)).

Lemma PCopen_collect_list : forall (l:list atom) m E A B Lacc,
  PC m E (typ_mu A) (typ_mu B) ->
  (forall W, InA eq W l -> W \in fv_tt A \u fv_tt B ->
      exists a, lookup W E = Some (Rules.bind_sub a)) ->
  exists L, (forall X, X \in Lacc -> X \in L) /\
    forall Y, Y \notin L -> forall W a,
      InA eq W l -> W \in fv_tt A \u fv_tt B ->
      lookup W E = Some (Rules.bind_sub a) ->
      (a = m -> posvar Pos W (open_tt A Y) (open_tt B Y)) /\
      (a = flip_im m -> posvar Neg W (open_tt A Y) (open_tt B Y)).
Proof.
  intros l. induction l as [| W0 l' IH];
    intros m E A B Lacc Hpc Hcov.
  - exists Lacc. split; [intros X HX; exact HX | intros Y HY W a Hin].
    inversion Hin.
  - destruct (AtomSetImpl.mem W0 (fv_tt A \u fv_tt B)) eqn:Emem.
    + assert (HmemS : W0 \in fv_tt A \u fv_tt B).
      { apply (proj2 (AtomSetProperties.FM.mem_iff (fv_tt A \u fv_tt B) W0)). exact Emem. }
      assert (Hin0 : InA eq W0 (W0 :: l')) by (apply InA_cons_hd; reflexivity).
      destruct (Hcov W0 Hin0 HmemS) as [a0 Hlk0].
      pose proof (PC_fact m E (typ_mu A) (typ_mu B) W0 a0 Hpc Hlk0 HmemS) as Hposv.
      destruct (posvar_mu_inv (pmode a0 m) W0 A B Hposv) as
        [[L0 [HBA [Hnotin _]]] | [L0 [H1 H2]]].
      * (* pos_rec_t is impossible because W0 is free *)
        exfalso. subst B. apply Hnotin.
        apply AtomSetImpl.union_1 in HmemS. destruct HmemS as [H|H]; exact H.
      * (* pos_rec *)
        destruct (IH m E A B (union (union Lacc L0) (singleton W0))
                   Hpc
                   (fun W Hin Hmem => Hcov W (@InA_cons_tl atom eq W W0 l' Hin) Hmem))
          as [L [Hsub Hfacts]].
        exists L. split.
        -- intros X HX. apply Hsub. apply AtomSetImpl.union_2.
           apply AtomSetImpl.union_2. exact HX.
        -- intros Y HY W a Hin HmemW Hlk.
           apply (@InA_cons atom eq W W0 l') in Hin. destruct Hin as [Heq|Hin'].
           ++ subst W.
              assert (HYbad : Y \notin L0 \u {{W0}}).
              { intro Hc. apply HY. apply Hsub.
                apply AtomSetImpl.union_1 in Hc. destruct Hc as [Hc0|Hcs].
                - apply AtomSetImpl.union_2. apply AtomSetImpl.union_3. exact Hc0.
                - apply AtomSetImpl.union_3. exact Hcs. }
              pose proof (H1 Y HYbad) as Hbody.
              assert (Haeq : a = a0).
              { rewrite Hlk0 in Hlk. injection Hlk. auto. }
              subst a. apply (pmode_posvar_split a0 m W0 (open_tt A Y) (open_tt B Y) Hbody).
           ++ apply Hfacts with (W := W) (a := a); auto.
    + (* W0 not free: ignore it *)
      assert (HnotS : ~ (W0 \in fv_tt A \u fv_tt B)).
      { intro Hc. apply (proj1 (AtomSetProperties.FM.mem_iff (fv_tt A \u fv_tt B) W0)) in Hc.
        rewrite Emem in Hc. discriminate. }
      destruct (IH m E A B Lacc Hpc
                 (fun W Hin Hmem => Hcov W (@InA_cons_tl atom eq W W0 l' Hin) Hmem))
        as [L [Hsub Hfacts]].
      exists L. split; [exact Hsub |].
      intros Y HY W a Hin HmemW Hlk.
      apply (@InA_cons atom eq W W0 l') in Hin. destruct Hin as [Heq|Hin'].
      * subst W. exfalso. apply HnotS. exact HmemW.
      * apply Hfacts with (W := W) (a := a); auto.
Qed.

Lemma fv_open_inv : forall (W:atom) (Y:atom) (A:typ),
  W \in fv_tt (open_tt A Y) -> W <> Y -> W \in fv_tt A.
Proof.
  intros W Y A H Hneq.
  pose proof (proj1 (fv_open_rec 0 Y A W) H) as Hr.
  apply AtomSetImpl.union_1 in Hr. destruct Hr as [HA|Hsing].
  - exact HA.
  - destruct (occ_any 0 A) eqn:Eo.
    + apply AtomSetImpl.singleton_1 in Hsing. subst W.
      exfalso. apply Hneq. reflexivity.
    + exfalso. apply (notin_empty_1 W). exact Hsing.
Qed.

Lemma PCopen_collect : forall m E A B,
  PC m E (typ_mu A) (typ_mu B) ->
  (forall W, W \in fv_tt A \u fv_tt B ->
      exists a, lookup W E = Some (Rules.bind_sub a)) ->
  exists L, forall Y, Y \notin L -> PCopen m E A B Y.
Proof.
  intros m E A B Hpc Hbound.
  destruct (PCopen_collect_list (AtomSetImpl.elements (fv_tt A \u fv_tt B))
              m E A B emp Hpc
              (fun W Hin Hmem => Hbound W Hmem)) as [L [Hsub Hfacts]].
  exists (union L (dom E)). intros Y HY W a Hlk HmemW.
  assert (HYL : Y \notin L) by (apply (notin_union_1 Y L (dom E) HY)).
  assert (HYd : Y \notin dom E) by (apply (notin_union_2 Y L (dom E) HY)).
  assert (HWY : W <> Y).
  { intro Heq. subst W. apply HYd. eapply binds_In. eapply lookup_binds. exact Hlk. }
  assert (HmemAB : W \in fv_tt A \u fv_tt B).
  { apply AtomSetImpl.union_1 in HmemW. destruct HmemW as [HWA|HWB].
    - apply AtomSetImpl.union_2. apply (fv_open_inv W Y A). exact HWA. exact HWY.
    - apply AtomSetImpl.union_3. apply (fv_open_inv W Y B). exact HWB. exact HWY. }
  apply Hfacts with (W := W) (a := a); auto.
  apply (proj1 (AtomSetProperties.FM.elements_iff (fv_tt A \u fv_tt B) W)). exact HmemAB.
Qed.

(* ============================================================ *)
(* Helpers for the recursive completeness case                  *)
(* ============================================================ *)

Lemma Task_WFS_drop_inv : forall (E0:env) (E:Rules.env) A,
  drop_im_env E = E0 -> WFS E0 A -> Rules.WFS E A.
Proof.
  intros E0 E A Hdrop H. revert E Hdrop.
  induction H as [E0 | E0 | X E0 Hb | E0 A B HA IHA HB IHB | L E0 A Hf IHf ];
    intros E Hdrop.
  - apply Rules.WFS_top.
  - apply Rules.WFS_nat.
  - rewrite <- Hdrop in Hb. apply binds_map_3 in Hb.
    destruct Hb as [b0 [Hdb Hbe]]. destruct b0 as [im|T]; simpl in Hdb.
    + eapply Rules.WFS_fvar. exact Hbe.
    + discriminate Hdb.
  - apply Rules.WFS_arrow; [ apply IHA | apply IHB ]; auto.
  - apply Rules.WFS_rec with (L := L) (im := Pos). intros X HX.
    apply (IHf X HX (X ~ Rules.bind_sub Pos ++ E)).
    rewrite drop_im_env_cons. simpl. rewrite Hdrop. reflexivity.
Qed.

Lemma is_empty_emp : AtomSetImpl.is_empty emp = true.
Proof.
  apply AtomSetImpl.is_empty_1. unfold AtomSetImpl.Empty.
  intros a H. apply (notin_empty_1 a). exact H.
Qed.

Lemma compose_cm_emp_some : forall cm1 cm2,
  exists cm, compose_cm cm1 cm2 emp emp = Some cm.
Proof.
  intros. destruct cm1, cm2; simpl; try (rewrite is_empty_emp);
    eexists; reflexivity.
Qed.

Lemma fv_empty_choose_None : forall A,
  AtomSetImpl.choose (fv_tt A) = None -> fv_tt A [=] emp.
Proof.
  intros. apply AtomSetProperties.empty_is_empty_1.
  apply AtomSetImpl.choose_2. exact H.
Qed.

Lemma fv_witness_choose_Some : forall A W,
  AtomSetImpl.choose (fv_tt A) = Some W -> W \in fv_tt A.
Proof. intros. eapply AtomSetImpl.choose_1. exact H. Qed.

Lemma fvbound_open : forall (m:IsoMode) (E:Rules.env) (A B:typ) (Y:atom),
  (forall Z, Z \in fv_tt A \u fv_tt B ->
      exists a, lookup Z E = Some (Rules.bind_sub a)) ->
  forall Z, Z \in fv_tt (open_tt A Y) \u fv_tt (open_tt B Y) ->
    exists a, lookup Z (Y ~ Rules.bind_sub m ++ E) = Some (Rules.bind_sub a).
Proof.
  intros m E A B Y Hbound Z HZ.
  destruct (Z == Y) as [Heq|Hne].
  - subst Z. exists m. apply lookup_cons_eq.
  - rewrite (lookup_cons_neq Z Y E (Rules.bind_sub m) Hne).
    apply Hbound.
    apply AtomSetImpl.union_1 in HZ. destruct HZ as [HZA|HZB].
    + apply AtomSetImpl.union_2. apply (fv_open_inv Z Y A). exact HZA. exact Hne.
    + apply AtomSetImpl.union_3. apply (fv_open_inv Z Y B). exact HZB. exact Hne.
Qed.

Lemma PC_body_of : forall (m:IsoMode) (E:Rules.env) (A B:typ) (Y:atom),
  (forall W a, lookup W E = Some (Rules.bind_sub a) ->
     W \in fv_tt (open_tt A Y) \u fv_tt (open_tt B Y) ->
     (a = m -> posvar Pos W (open_tt A Y) (open_tt B Y)) /\
     (a = flip_im m -> posvar Neg W (open_tt A Y) (open_tt B Y))) ->
  posvar Pos Y (open_tt A Y) (open_tt B Y) ->
  PC m (Y ~ Rules.bind_sub m ++ E) (open_tt A Y) (open_tt B Y).
Proof.
  intros m E A B Y Hfacts HposY. unfold PC.
  intros W a Hlk Hmem.
  destruct (W == Y) as [Heq|Hne].
  - subst W. rewrite lookup_cons_eq in Hlk. injection Hlk as Hm.
    subst a. split.
    + intro Hx0. exact HposY.
    + intro Hc. exfalso. exact (flip_im_neq m Hc).
  - rewrite (lookup_cons_neq W Y E (Rules.bind_sub m) Hne) in Hlk.
    apply Hfacts with (a := a); auto.
Qed.

Lemma posvar_fvar_neg_false : forall X, ~ posvar Neg X (typ_fvar X) (typ_fvar X).
Proof.
  intros X H. inversion H.
  match goal with Hne : ?a <> ?a |- _ => exact (Hne eq_refl) end.
Qed.

Lemma complete_prot : forall (E0:env) (A B:typ),
  sub_amber2 E0 A B ->
  forall (m:IsoMode) (E:Rules.env),
    drop_im_env E = E0 -> Rules.wf_env E -> PC m E A B ->
    (forall Y, Y \in fv_tt A \u fv_tt B ->
        exists a, lookup Y E = Some (Rules.bind_sub a)) ->
    exists cm evs, Rules.Sub m cm evs E A B /\ evs [=] emp /\
      (A = B <-> cm = Eq).
Proof.
  intros E0 A B H. induction H as
    [ E0 Hwf0
    | E0 A HWFS Hwf0
    | E0 X Hb Hwf0
    | E0 A1 A2 B1 B2 H1 IH1 H2 IH2
    | E0 A B L Hbody IHbody Hpos ];
    intros m E Hdrop Hwf Hpc Hfv.
  - (* nat *)
    exists Eq, emp. split. { apply Sa_nat. exact Hwf. }
    split. { reflexivity. }
    split; intro; reflexivity.
  - (* top *)
    destruct A as [ | | n | X | A1 | A1 A2].
    + exists Eq, emp. split. { apply Sa_top_eq. exact Hwf. }
      split. { reflexivity. } split; intro; reflexivity.
    + exists Lt, emp. split.
      { apply Sa_top_lt. exact Hwf.
        apply Task_WFS_drop_inv with (E0 := E0); auto. discriminate. }
      split. { reflexivity. } split; intro Hc; discriminate Hc.
    + exists Lt, emp. split.
      { apply Sa_top_lt. exact Hwf.
        apply Task_WFS_drop_inv with (E0 := E0); auto. discriminate. }
      split. { reflexivity. } split; intro Hc; discriminate Hc.
    + exists Lt, emp. split.
      { apply Sa_top_lt. exact Hwf.
        apply Task_WFS_drop_inv with (E0 := E0); auto. discriminate. }
      split. { reflexivity. } split; intro Hc; discriminate Hc.
    + exists Lt, emp. split.
      { apply Sa_top_lt. exact Hwf.
        apply Task_WFS_drop_inv with (E0 := E0); auto. discriminate. }
      split. { reflexivity. } split; intro Hc; discriminate Hc.
    + exists Lt, emp. split.
      { apply Sa_top_lt. exact Hwf.
        apply Task_WFS_drop_inv with (E0 := E0); auto. discriminate. }
      split. { reflexivity. } split; intro Hc; discriminate Hc.
  - (* fvar *)
    assert (Hmem : X \in fv_tt (typ_fvar X) \u fv_tt (typ_fvar X)).
    { apply AtomSetImpl.union_2. apply AtomSetImpl.singleton_2. reflexivity. }
    destruct (Hfv X Hmem) as [a Ha].
    destruct a, m; simpl.
    + exists Eq, emp. split.
      { eapply Sa_fvar_pos. exact Hwf. apply lookup_binds. exact Ha. }
      split. { reflexivity. } split; intro; reflexivity.
    + exfalso.
      pose proof (proj2 (Hpc X Neg Ha Hmem) eq_refl) as Hbad.
      exact (posvar_fvar_neg_false X Hbad).
    + exfalso.
      pose proof (proj2 (Hpc X Pos Ha Hmem) eq_refl) as Hbad.
      exact (posvar_fvar_neg_false X Hbad).
    + exists Eq, emp. split.
      { eapply Sa_fvar_pos. exact Hwf. apply lookup_binds. exact Ha. }
      split. { reflexivity. } split; intro; reflexivity.
  - (* arrow *)
    assert (Hpc1 : PC (flip_im m) E B1 A1) by (apply (PC_arrow_l m E A1 A2 B1 B2 Hpc)).
    assert (Hpc2 : PC m E A2 B2) by (apply (PC_arrow_r m E A1 A2 B1 B2 Hpc)).
    assert (Hfv1 : forall Y, Y \in fv_tt B1 \u fv_tt A1 ->
              exists a, lookup Y E = Some (Rules.bind_sub a)).
    { intros Y HY. apply Hfv. apply AtomSetImpl.union_1 in HY.
      destruct HY as [HY|HY].
      - apply AtomSetImpl.union_3. apply AtomSetImpl.union_2. exact HY.
      - apply AtomSetImpl.union_2. apply AtomSetImpl.union_2. exact HY. }
    assert (Hfv2 : forall Y, Y \in fv_tt A2 \u fv_tt B2 ->
              exists a, lookup Y E = Some (Rules.bind_sub a)).
    { intros Y HY. apply Hfv. apply AtomSetImpl.union_1 in HY.
      destruct HY as [HY|HY].
      - apply AtomSetImpl.union_2. apply AtomSetImpl.union_3. exact HY.
      - apply AtomSetImpl.union_3. apply AtomSetImpl.union_3. exact HY. }
    destruct (IH1 (flip_im m) E Hdrop Hwf Hpc1 Hfv1) as
      (cm1 & evs1 & Hsub1 & Hevs1 & Hcan1).
    destruct (IH2 m E Hdrop Hwf Hpc2 Hfv2) as
      (cm2 & evs2 & Hsub2 & Hevs2 & Hcan2).
    assert (Hsub1' : Rules.Sub (flip_im m) cm1 emp E B1 A1).
    { eapply Sa_evs_proper. exact Hsub1. exact Hevs1. }
    assert (Hsub2' : Rules.Sub m cm2 emp E A2 B2).
    { eapply Sa_evs_proper. exact Hsub2. exact Hevs2. }
    destruct (compose_cm_emp_some cm1 cm2) as [cm Hcomp].
    exists cm, (union emp emp). split.
    + eapply Sa_arrow with (cm1 := cm1) (cm2 := cm2) (evs1 := emp) (evs2 := emp).
      * exact Hsub1'. * exact Hsub2'. * exact Hcomp.
    + split.
      * fsetdec.
      * destruct cm1, cm2; simpl in Hcomp;
          try (rewrite is_empty_emp in Hcomp);
          injection Hcomp as Hcm; subst cm.
        -- split; intro Hc.
           ++ injection Hc as HA1 HA2.
              discriminate (proj1 Hcan1 (eq_sym HA1)).
           ++ discriminate Hc.
        -- split; intro Hc.
           ++ injection Hc as HA1 HA2.
              discriminate (proj1 Hcan1 (eq_sym HA1)).
           ++ discriminate Hc.
        -- split; intro Hc.
           ++ injection Hc as HA1 HA2.
              discriminate (proj1 Hcan2 HA2).
           ++ discriminate Hc.
        -- split.
           ++ intro Hc. reflexivity.
           ++ intro Hc. pose proof (proj2 Hcan1 eq_refl) as HB1.
              pose proof (proj2 Hcan2 eq_refl) as HB2. rewrite HB1, HB2. reflexivity.
  - (* rec *)
    destruct (atom_fresh (L \u dom E)) as [X0 HX0].
    assert (HX0L : X0 \notin L) by (apply (notin_union_1 X0 L (dom E) HX0)).
    assert (HX0d : X0 \notin dom E) by (apply (notin_union_2 X0 L (dom E) HX0)).
    pose proof (Hpos X0 HX0L) as Hpos0.
    destruct (posvar_mu_inv Pos X0 A B Hpos0) as
      [ [Lp [HBeq [HX0fv Htypes]]] | [Lp [Hp1 Hp2]] ].
    + (* pos_rec_t: A = B, reflexive mu *)
      subst B.
      assert (HboundAA : forall Z, Z \in fv_tt A \u fv_tt A ->
                exists a, lookup Z E = Some (Rules.bind_sub a)).
      { intros Z HZ. apply Hfv. simpl. exact HZ. }
      destruct (AtomSetImpl.choose (fv_tt A)) as [W|] eqn:Ech.
      * (* fv A nonempty: use protected IH on the body *)
        pose proof (fv_witness_choose_Some A W Ech) as HW.
        assert (HWmem : W \in fv_tt (typ_mu A) \u fv_tt (typ_mu A)).
        { simpl. apply AtomSetImpl.union_2. exact HW. }
        destruct (Hfv W HWmem) as [aW Hlk0].
        pose proof (PC_fact m E (typ_mu A) (typ_mu A) W aW Hpc Hlk0 HWmem) as HposvW.
        destruct (posvar_mu_inv (pmode aW m) W A A HposvW) as
          [ [Lw [HBA [Hnotin _]]] | [Lw [H1w H2w]] ].
        -- exfalso. apply Hnotin. exact HW.
        -- destruct (PCopen_collect m E A A Hpc HboundAA) as [Lcoll Hcoll].
           set (LQ := union (union (union (union L Lcoll) Lw) (singleton W)) (dom E)).
           exists Eq, emp. split.
           ++ eapply Sa_rec_eq_notin with (L := LQ) (evs := emp) (A1 := A) (A2 := A).
              intros Y HY. unfold LQ in HY.
              pose proof (notin_union_1 Y (union (union (union L Lcoll) Lw) (singleton W)) (dom E) HY) as Hbig.
              pose proof (notin_union_2 Y (union (union (union L Lcoll) Lw) (singleton W)) (dom E) HY) as HYd.
              pose proof (notin_union_1 Y (union (union L Lcoll) Lw) (singleton W) Hbig) as Ha.
              pose proof (notin_union_2 Y (union (union L Lcoll) Lw) (singleton W) Hbig) as HYW.
              pose proof (notin_union_1 Y (union L Lcoll) Lw Ha) as Hb.
              pose proof (notin_union_2 Y (union L Lcoll) Lw Ha) as HYLw.
              pose proof (notin_union_1 Y L Lcoll Hb) as HYL.
              pose proof (notin_union_2 Y L Lcoll Hb) as HYLcoll.
              pose proof (Hbody Y HYL) as HbodyY.
              assert (HdropY : drop_im_env (Y ~ Rules.bind_sub m ++ E) = Y ~ bind_sub ++ E0).
              { rewrite drop_im_env_cons. simpl. rewrite Hdrop. reflexivity. }
              assert (HwfY : Rules.wf_env (Y ~ Rules.bind_sub m ++ E)).
              { apply Rules.wf_env_sub; auto. }
              assert (HcollY : PCopen m E A A Y) by (apply Hcoll; exact HYLcoll).
              assert (HYW' : Y \notin Lw \u {{W}})
                by (apply notin_union; [ exact HYLw | exact HYW ]).
              assert (HYfact : posvar Pos Y (open_tt A Y) (open_tt A Y))
                by (apply H2w; exact HYW').
              assert (PCY : PC m (Y ~ Rules.bind_sub m ++ E) (open_tt A Y) (open_tt A Y))
                by (apply (PC_body_of m E A A Y HcollY HYfact)).
              assert (HfvY : forall Z, Z \in fv_tt (open_tt A Y) \u fv_tt (open_tt A Y) ->
                        exists a, lookup Z (Y ~ Rules.bind_sub m ++ E) = Some (Rules.bind_sub a))
                by (apply (fvbound_open m E A A Y HboundAA)).
              destruct (IHbody Y HYL m (Y ~ Rules.bind_sub m ++ E) HdropY HwfY PCY HfvY)
                as (cmY & evsY & HsubY & HevsY & HcanY).
              assert (HcmY : cmY = Eq) by (apply (proj1 HcanY); reflexivity).
              assert (Hfin : Rules.Sub m Eq emp (Y ~ Rules.bind_sub m ++ E)
                               (open_tt A Y) (open_tt A Y)).
              { assert (Htmp : Rules.Sub m cmY emp (Y ~ Rules.bind_sub m ++ E)
                                 (open_tt A Y) (open_tt A Y))
                  by (eapply Sa_evs_proper; [ exact HsubY | exact HevsY ]).
                rewrite HcmY in Htmp. exact Htmp. }
              exact Hfin.
           ++ split; [reflexivity|]. split; intro; reflexivity.
      * (* fv A empty: reflexivity path *)
        pose proof (fv_empty_choose_None A Ech) as HfvEmpty.
        set (LQ := union L (dom E)).
        exists Eq, emp. split.
        -- destruct (contam 0 false A) eqn:Ec.
           ++ (* eq_in *)
              eapply Sa_evs_proper.
              ** eapply Sa_rec_eq_in with (L := LQ) (evs := emp) (A1 := A) (A2 := A).
                 intros Y HY. unfold LQ in HY.
                 pose proof (notin_union_1 Y L (dom E) HY) as HYL.
                 pose proof (notin_union_2 Y L (dom E) HY) as HYd.
                 pose proof (Hbody Y HYL) as HbodyY.
                 assert (HdropY : drop_im_env (Y ~ Rules.bind_sub m ++ E) = Y ~ bind_sub ++ E0).
                 { rewrite drop_im_env_cons. simpl. rewrite Hdrop. reflexivity. }
                 assert (HwfY : Rules.wf_env (Y ~ Rules.bind_sub m ++ E)).
                 { apply Rules.wf_env_sub; auto. }
                 assert (HtypeY : type (open_tt A Y)).
                 { apply (proj1 (sub_amber2_type (Y ~ bind_sub ++ E0) (open_tt A Y) (open_tt A Y) HbodyY)). }
                 assert (HfvY : forall Z, Z \in fv_tt (open_tt A Y) \u fv_tt (open_tt A Y) ->
                           exists a, lookup Z (Y ~ Rules.bind_sub m ++ E) = Some (Rules.bind_sub a))
                   by (apply (fvbound_open m E A A Y HboundAA)).
                 assert (HfvY1 : forall Z, Z \in fv_tt (open_tt A Y) ->
                            exists a, lookup Z (Y ~ Rules.bind_sub m ++ E) = Some (Rules.bind_sub a))
                   by (intros Z HZ; apply HfvY; apply AtomSetImpl.union_2; exact HZ).
                 pose proof (Sub_reflect_spec m (Y ~ Rules.bind_sub m ++ E) (open_tt A Y)
                               HwfY HtypeY HfvY1) as Hrefl.
                 assert (HYnotinA : Y \notin fv_tt A).
                 { intro Hc. pose proof (proj1 (HfvEmpty Y) Hc) as Hemp.
                   apply (notin_empty_1 Y). exact Hemp. }
                 pose proof (reflEvs_open_gen m m false E Y 0 A eq_refl HYnotinA) as Hgen.
                 rewrite Ec in Hgen. simpl in Hgen.
                 assert (HS0 : reflEvs m E A [=] emp) by (apply reflEvs_fv_empty; exact HfvEmpty).
                 assert (Hevseq : reflEvs m (Y ~ Rules.bind_sub m ++ E)
                                    (open_tt_rec 0 (typ_fvar Y) A) [=] add Y emp)
                   by fsetdec.
                 eapply Sa_evs_proper. exact Hrefl. exact Hevseq.
              ** fsetdec.
           ++ (* eq_notin *)
              eapply Sa_rec_eq_notin with (L := LQ) (evs := emp) (A1 := A) (A2 := A).
              intros Y HY. unfold LQ in HY.
              pose proof (notin_union_1 Y L (dom E) HY) as HYL.
              pose proof (notin_union_2 Y L (dom E) HY) as HYd.
              pose proof (Hbody Y HYL) as HbodyY.
              assert (HdropY : drop_im_env (Y ~ Rules.bind_sub m ++ E) = Y ~ bind_sub ++ E0).
              { rewrite drop_im_env_cons. simpl. rewrite Hdrop. reflexivity. }
              assert (HwfY : Rules.wf_env (Y ~ Rules.bind_sub m ++ E)).
              { apply Rules.wf_env_sub; auto. }
              assert (HtypeY : type (open_tt A Y)).
              { apply (proj1 (sub_amber2_type (Y ~ bind_sub ++ E0) (open_tt A Y) (open_tt A Y) HbodyY)). }
              assert (HfvY : forall Z, Z \in fv_tt (open_tt A Y) \u fv_tt (open_tt A Y) ->
                        exists a, lookup Z (Y ~ Rules.bind_sub m ++ E) = Some (Rules.bind_sub a))
                by (apply (fvbound_open m E A A Y HboundAA)).
              assert (HfvY1 : forall Z, Z \in fv_tt (open_tt A Y) ->
                          exists a, lookup Z (Y ~ Rules.bind_sub m ++ E) = Some (Rules.bind_sub a))
                by (intros Z HZ; apply HfvY; apply AtomSetImpl.union_2; exact HZ).
              pose proof (Sub_reflect_spec m (Y ~ Rules.bind_sub m ++ E) (open_tt A Y)
                            HwfY HtypeY HfvY1) as Hrefl.
              assert (HYnotinA : Y \notin fv_tt A).
              { intro Hc. pose proof (proj1 (HfvEmpty Y) Hc) as Hemp.
                apply (notin_empty_1 Y). exact Hemp. }
              pose proof (reflEvs_open_gen m m false E Y 0 A eq_refl HYnotinA) as Hgen.
              rewrite Ec in Hgen. simpl in Hgen.
              assert (HS0 : reflEvs m E A [=] emp) by (apply reflEvs_fv_empty; exact HfvEmpty).
              assert (Hevseq : reflEvs m (Y ~ Rules.bind_sub m ++ E)
                                 (open_tt_rec 0 (typ_fvar Y) A) [=] emp)
                by fsetdec.
              eapply Sa_evs_proper. exact Hrefl. exact Hevseq.
        -- split; [reflexivity|]. split; intro; reflexivity.
    + (* pos_rec: general A, B *)
      assert (HboundAB : forall Z, Z \in fv_tt A \u fv_tt B ->
                exists a, lookup Z E = Some (Rules.bind_sub a)).
      { intros Z HZ. apply Hfv. simpl. exact HZ. }
      destruct (PCopen_collect m E A B Hpc HboundAB) as [Lcoll Hcoll].
      set (S := fv_tt A \u fv_tt B).
      set (LQ := union (union (union (union (union L Lcoll) Lp) (dom E)) (singleton X0)) S).
      assert (Hbuild : forall Y, Y \notin LQ ->
        exists cmY evsY, Rules.Sub m cmY evsY (Y ~ Rules.bind_sub m ++ E)
           (open_tt A Y) (open_tt B Y) /\ evsY [=] emp /\
           (open_tt A Y = open_tt B Y <-> cmY = Eq)).
      { intros Y HY. unfold LQ in HY.
        pose proof (notin_union_1 Y (union (union (union (union L Lcoll) Lp) (dom E)) (singleton X0)) S HY) as Hbig.
        pose proof (notin_union_2 Y (union (union (union (union L Lcoll) Lp) (dom E)) (singleton X0)) S HY) as HYS.
        pose proof (notin_union_1 Y (union (union (union L Lcoll) Lp) (dom E)) (singleton X0) Hbig) as Ha.
        pose proof (notin_union_2 Y (union (union (union L Lcoll) Lp) (dom E)) (singleton X0) Hbig) as HYX0.
        pose proof (notin_union_1 Y (union (union L Lcoll) Lp) (dom E) Ha) as Hb.
        pose proof (notin_union_2 Y (union (union L Lcoll) Lp) (dom E) Ha) as HYd.
        pose proof (notin_union_1 Y (union L Lcoll) Lp Hb) as Hc.
        pose proof (notin_union_2 Y (union L Lcoll) Lp Hb) as HYLp.
        pose proof (notin_union_1 Y L Lcoll Hc) as HYL.
        pose proof (notin_union_2 Y L Lcoll Hc) as HYLcoll.
        pose proof (Hbody Y HYL) as HbodyY.
        assert (HdropY : drop_im_env (Y ~ Rules.bind_sub m ++ E) = Y ~ bind_sub ++ E0).
        { rewrite drop_im_env_cons. simpl. rewrite Hdrop. reflexivity. }
        assert (HwfY : Rules.wf_env (Y ~ Rules.bind_sub m ++ E)).
        { apply Rules.wf_env_sub; auto. }
        assert (HcollY : PCopen m E A B Y) by (apply Hcoll; exact HYLcoll).
        assert (HYX0' : Y \notin Lp \u {{X0}})
          by (apply notin_union; [ exact HYLp | exact HYX0 ]).
        assert (HYfact : posvar Pos Y (open_tt A Y) (open_tt B Y))
          by (apply Hp2; exact HYX0').
        assert (PCY : PC m (Y ~ Rules.bind_sub m ++ E) (open_tt A Y) (open_tt B Y))
          by (apply (PC_body_of m E A B Y HcollY HYfact)).
        assert (HfvY : forall Z, Z \in fv_tt (open_tt A Y) \u fv_tt (open_tt B Y) ->
                  exists a, lookup Z (Y ~ Rules.bind_sub m ++ E) = Some (Rules.bind_sub a))
          by (apply (fvbound_open m E A B Y HboundAB)).
        exact (IHbody Y HYL m (Y ~ Rules.bind_sub m ++ E) HdropY HwfY PCY HfvY). }
      destruct (atom_fresh LQ) as [Y0 HY0].
      destruct (Hbuild Y0 HY0) as (cm0 & evs0 & Hsub0 & Hevs0 & Hcan0).
      destruct cm0.
      * (* Lt *)
        assert (HAB : A <> B).
        { intro Heq. assert (Hop : open_tt A Y0 = open_tt B Y0) by (rewrite Heq; reflexivity).
          pose proof (proj1 Hcan0 Hop) as Hbad. discriminate Hbad. }
        exists Lt, emp. split.
        -- eapply Sa_rec_lt with (L := LQ) (evs := emp) (A1 := A) (A2 := B).
           intros Y HY. destruct (Hbuild Y HY) as (cmY & evsY & HsubY & HevsY & HcanY).
           assert (HcmY : cmY = Lt).
           { destruct cmY; [reflexivity|].
             exfalso. apply HAB. apply (open_tt_inj Y A B).
             + unfold LQ in HY.
               pose proof (notin_union_2 Y (union (union (union (union L Lcoll) Lp) (dom E)) (singleton X0)) S HY) as HYS.
               unfold S in HYS. intro Hc. apply HYS. apply AtomSetImpl.union_2. exact Hc.
             + unfold LQ in HY.
               pose proof (notin_union_2 Y (union (union (union (union L Lcoll) Lp) (dom E)) (singleton X0)) S HY) as HYS.
               unfold S in HYS. intro Hc. apply HYS. apply AtomSetImpl.union_3. exact Hc.
             + apply (proj2 HcanY); reflexivity. }
           assert (Htmp : Rules.Sub m cmY emp (Y ~ Rules.bind_sub m ++ E)
                             (open_tt A Y) (open_tt B Y))
             by (eapply Sa_evs_proper; [ exact HsubY | exact HevsY ]).
           rewrite HcmY in Htmp. exact Htmp.
        -- split; [reflexivity|]. split; intro Hc.
           ++ exfalso. apply HAB. injection Hc. auto.
           ++ discriminate Hc.
      * (* Eq *)
        assert (HAB : A = B).
        { apply (open_tt_inj Y0 A B).
          - unfold LQ in HY0.
            pose proof (notin_union_2 Y0 (union (union (union (union L Lcoll) Lp) (dom E)) (singleton X0)) S HY0) as HYS.
            unfold S in HYS. intro Hc. apply HYS. apply AtomSetImpl.union_2. exact Hc.
          - unfold LQ in HY0.
            pose proof (notin_union_2 Y0 (union (union (union (union L Lcoll) Lp) (dom E)) (singleton X0)) S HY0) as HYS.
            unfold S in HYS. intro Hc. apply HYS. apply AtomSetImpl.union_3. exact Hc.
          - apply (proj2 Hcan0); reflexivity. }
        subst B.
        exists Eq, emp. split.
        -- eapply Sa_rec_eq_notin with (L := LQ) (evs := emp) (A1 := A) (A2 := A).
           intros Y HY. destruct (Hbuild Y HY) as (cmY & evsY & HsubY & HevsY & HcanY).
           assert (HcmY : cmY = Eq) by (apply (proj1 HcanY); reflexivity).
           assert (Htmp : Rules.Sub m cmY emp (Y ~ Rules.bind_sub m ++ E)
                             (open_tt A Y) (open_tt A Y))
             by (eapply Sa_evs_proper; [ exact HsubY | exact HevsY ]).
           rewrite HcmY in Htmp. exact Htmp.
        -- split; [reflexivity|]. split; intro; reflexivity.
Qed.

Theorem pos_esa_complete_final: forall A B,
    sub_amber2 nil A B ->
    exists cm evs, Sub Pos cm evs nil A B.
Proof.
  intros A B Hsub.
  assert (Hpc : PC Pos nil A B).
  { intros Y a Hlk Hmem. simpl in Hlk. discriminate Hlk. }
  assert (Hfv : forall Y, Y \in fv_tt A \u fv_tt B ->
      exists a, lookup Y nil = Some (Rules.bind_sub a)).
  { intros Y Hmem. exfalso.
    destruct (sub_amber2_fv_dom nil A B Hsub) as [HA HB].
    apply AtomSetImpl.union_1 in Hmem. destruct Hmem as [H|H].
    - apply (notin_empty_1 Y). specialize (HA Y H). simpl in HA. exact HA.
    - apply (notin_empty_1 Y). specialize (HB Y H). simpl in HB. exact HB. }
  destruct (complete_prot nil A B Hsub Pos nil eq_refl Rules.wf_env_empty Hpc Hfv)
    as (cm & evs & Hsub' & _ & _).
  exists cm, evs. exact Hsub'.
Qed.
