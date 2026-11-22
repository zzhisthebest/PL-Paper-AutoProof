Require Import erasure.

Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Lia.

Require Import Relation_Operators.

Require Import Operators_Properties.

Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.

Definition terminate (e:exp) : Prop :=
  exists v, value v /\ e ==>* v.

Definition diverge (e:exp) : Prop :=
  ~ (exists v, value v /\ e ==>* v).

(* ------------------------------------------------------------------ *)
(* Basic syntactic lemmas                                             *)
(* ------------------------------------------------------------------ *)

Lemma size_exp_open_var : forall e x k,
  size_exp (open_exp_wrt_exp_rec k (e_var_f x) e) = size_exp e.
Proof.
  induction e; intros x k; simpl; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
Qed.

Lemma size_exp_open_var' : forall e x,
  size_exp (open_exp_wrt_exp e (e_var_f x)) = size_exp e.
Proof. intros. unfold open_exp_wrt_exp. apply size_exp_open_var. Qed.

Lemma size_typ_pos : forall A, 1 <= size_typ A.
Proof. destruct A; simpl; lia. Qed.

Lemma erase_open_exp_rec : forall k v e,
  erase (open_exp_wrt_exp_rec k v e) =
  open_exp_wrt_exp_rec k (erase v) (erase e).
Proof.
  intros k v e; revert k v.
  induction e; intros k v; simpl.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
  - auto.
  - auto.
  - rewrite IHe. auto.
  - rewrite IHe1, IHe2. auto.
  - rewrite IHe. auto.
Qed.

Lemma erase_open_exp : forall e v,
  erase (open_exp_wrt_exp e v) =
  open_exp_wrt_exp (erase e) (erase v).
Proof. intros; apply erase_open_exp_rec. Qed.

Lemma erase_open_exp_var : forall e x,
  erase (open_exp_wrt_exp e (e_var_f x)) =
  open_exp_wrt_exp (erase e) (e_var_f x).
Proof. intros. rewrite erase_open_exp. simpl. reflexivity. Qed.

Lemma erase_subst_exp : forall v x e,
  erase (subst_exp v x e) = subst_exp (erase v) x (erase e).
Proof.
  intros v x e; revert v x.
  induction e as [n|y|i|A e IHe|e1 IHe1 e2 IHe2|c e IHe]; intros v x; simpl.
  - auto.
  - destruct (eq_var y x); simpl; auto.
  - auto.
  - rewrite IHe; auto.
  - rewrite IHe1, IHe2; auto.
  - rewrite IHe; auto.
Qed.

Lemma lc_exp_erase : forall e, lc_exp e -> lc_exp (erase e).
Proof.
  intros e. remember (size_exp e) as n eqn:En. revert e En.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros e En Hlc.
  destruct e; simpl in *.
  - inversion Hlc.
  - constructor.
  - constructor.
  - (* abs *)
    inversion Hlc as [| |A body HA Hbody| |]; subst.
    constructor; auto.
    intros x.
    match goal with
    | |- lc_exp (open_exp_wrt_exp (erase ?b) (e_var_f x)) =>
        rewrite <- (erase_open_exp_var b x);
        apply IH with (size_exp (open_exp_wrt_exp b (e_var_f x)));
        [ rewrite (size_exp_open_var' b x); simpl;
          pose proof (size_typ_pos t); lia
        | reflexivity
        | apply Hbody ]
    end.
  - (* app *)
    inversion Hlc as [| | |a b Ha Hb|]; subst.
    constructor.
    all: match goal with
         | |- lc_exp (erase ?x) =>
             apply IH with (size_exp x); [ simpl; lia | reflexivity | assumption ]
         end.
  - (* cast *)
    inversion Hlc as [| | | |cc ee Hc He]; subst.
    match goal with
    | |- lc_exp (erase ?x) =>
        apply IH with (size_exp x); [ simpl; lia | reflexivity | assumption ]
    end.
Qed.

Lemma value_erase : forall v, value v -> value (erase v).
Proof.
  intros v Hv; induction Hv.
  - simpl. constructor.
  - simpl. constructor.
    + assumption.
    + exact (lc_exp_erase (e_abs A e) H0).
  - simpl. apply IHHv.
  - simpl. apply IHHv.
Qed.

(* ------------------------------------------------------------------ *)
(* Degree / locally-closed bridges                                    *)
(* ------------------------------------------------------------------ *)

Lemma degree_exp_open_self : forall nn e x,
  degree_exp_wrt_exp nn (open_exp_wrt_exp_rec nn (e_var_f x) e) <->
  degree_exp_wrt_exp (S nn) e.
Proof.
  intros nn e; revert nn.
  induction e; intros nn x; simpl.
  - destruct (lt_eq_lt_dec n nn) as [[Hlt|Heq]|Hgt]; simpl.
    + split; intros H; apply degree_wrt_exp_e_var_b; lia.
    + subst n. split; intros H.
      * apply degree_wrt_exp_e_var_b. lia.
      * apply degree_wrt_exp_e_var_f.
    + split; intros H;
        inversion H as [|m Hm| | | |]; subst; lia.
  - split; intros H; apply degree_wrt_exp_e_var_f.
  - split; intros H; apply degree_wrt_exp_e_lit.
  - (* abs *)
    split; intros H.
    + inversion H as [| | | | |nn0 AA bb Hd]; subst.
      apply degree_wrt_exp_e_abs. apply (proj1 (IHe (S nn) x)). assumption.
    + inversion H as [| | | | |nn0 AA bb Hd]; subst.
      apply degree_wrt_exp_e_abs. apply (proj2 (IHe (S nn) x)). assumption.
  - (* app *)
    split; intros H.
    + inversion H as [| | | |nn0 aa bb H1 H2|]; subst.
      apply degree_wrt_exp_e_app;
        [ apply (proj1 (IHe1 nn x)) | apply (proj1 (IHe2 nn x)) ]; assumption.
    + inversion H as [| | | |nn0 aa bb H1 H2|]; subst.
      apply degree_wrt_exp_e_app;
        [ apply (proj2 (IHe1 nn x)) | apply (proj2 (IHe2 nn x)) ]; assumption.
  - (* cast *)
    split; intros H.
    + inversion H as [| | | | |nn0 cc bb H1]; subst.
      apply degree_wrt_exp_e_cast. apply (proj1 (IHe nn x)). assumption.
    + inversion H as [| | | | |nn0 cc bb H1]; subst.
      apply degree_wrt_exp_e_cast. apply (proj2 (IHe nn x)). assumption.
Qed.

Lemma degree_typ_open_self : forall nn A X,
  degree_typ_wrt_typ nn (open_typ_wrt_typ_rec nn (t_var_f X) A) <->
  degree_typ_wrt_typ (S nn) A.
Proof.
  intros nn A; revert nn.
  induction A; intros nn X; simpl.
  - destruct (lt_eq_lt_dec n nn) as [[Hlt|Heq]|Hgt]; simpl.
    + split; intros H; apply degree_wrt_typ_t_var_b; lia.
    + subst n. split; intros H.
      * apply degree_wrt_typ_t_var_b. lia.
      * apply degree_wrt_typ_t_var_f.
    + split; intros H;
        inversion H as [|m Hm| | |]; subst; lia.
  - split; intros H; apply degree_wrt_typ_t_var_f.
  - split; intros H; apply degree_wrt_typ_t_int.
  - split; intros H.
    + inversion H as [| | |A0 B0 H1 H2|]; subst.
      apply degree_wrt_typ_t_arrow;
        [ apply (proj1 (IHA1 nn X)) | apply (proj1 (IHA2 nn X)) ]; assumption.
    + inversion H as [| | |A0 B0 H1 H2|]; subst.
      apply degree_wrt_typ_t_arrow;
        [ apply (proj2 (IHA1 nn X)) | apply (proj2 (IHA2 nn X)) ]; assumption.
  - split; intros H.
    + inversion H as [| | | |nn0 AA Hd]; subst.
      apply degree_wrt_typ_t_mu. apply (proj1 (IHA (S nn) X)). assumption.
    + inversion H as [| | | |nn0 AA Hd]; subst.
      apply degree_wrt_typ_t_mu. apply (proj2 (IHA (S nn) X)). assumption.
Qed.

(* An "annotation" predicate: all type annotations and cast operators are lc. *)
Fixpoint lc_annot_exp (e:exp) : Prop :=
  match e with
  | e_var_b _ => True
  | e_var_f _ => True
  | e_lit _ => True
  | e_abs A b => lc_typ A /\ lc_annot_exp b
  | e_app a b => lc_annot_exp a /\ lc_annot_exp b
  | e_cast c b => lc_castop c /\ lc_annot_exp b
  end.

Lemma lc_annot_open_var : forall e x k,
  lc_annot_exp (open_exp_wrt_exp_rec k (e_var_f x) e) <-> lc_annot_exp e.
Proof.
  induction e; intros x k; simpl.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; tauto.
  - tauto.
  - tauto.
  - split; intros [HA Hb]; split; auto;
      apply (proj1 (IHe x (S k))) in Hb || apply (proj2 (IHe x (S k))) in Hb;
      assumption.
  - split; intros [H1 H2]; split;
      [ apply (proj1 (IHe1 x k)) | apply (proj1 (IHe2 x k))
      | apply (proj2 (IHe1 x k)) | apply (proj2 (IHe2 x k)) ]; assumption.
  - split; intros [Hc Hb]; split; auto;
      apply (proj1 (IHe x k)) in Hb || apply (proj2 (IHe x k)) in Hb;
      assumption.
Qed.

Lemma size_open_lt_abs : forall A b z,
  size_exp (open_exp_wrt_exp b (e_var_f z)) < size_exp (e_abs A b).
Proof.
  intros. rewrite size_exp_open_var'. simpl. pose proof (size_typ_pos A). lia.
Qed.

Lemma lc_exp_degree_annot : forall e,
  lc_exp e <-> degree_exp_wrt_exp 0 e /\ lc_annot_exp e.
Proof.
  intros e. remember (size_exp e) as n eqn:En. revert e En.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros e En.
  destruct e as [nb|y|i|A b|e1 e2|co b]; simpl.
  - (* var_b *)
    split.
    + intro H; inversion H.
    + intros [Hd _]; inversion Hd as [|m Hm| | | |]; lia.
  - (* var_f *)
    split.
    + intro H; split; [constructor | exact I].
    + intros [Hd Ha]; constructor.
  - (* lit *)
    split.
    + intro H; split; [constructor | exact I].
    + intros [Hd Ha]; constructor.
  - (* abs *)
    split.
    + intro Hlc.
      inversion Hlc as [| |A0 b0 HA Hb| |]; subst.
      split.
      * apply degree_wrt_exp_e_abs.
        set (z := fresh (@nil atom)).
        pose proof (Hb z) as Hz.
        destruct (proj1 (IH (size_exp (open_exp_wrt_exp b (e_var_f z)))
                            (size_open_lt_abs A b z)
                            (open_exp_wrt_exp b (e_var_f z)) eq_refl) Hz) as [Hd _].
        apply (proj1 (degree_exp_open_self 0 b z)). exact Hd.
      * simpl. split; auto.
        set (z := fresh (@nil atom)).
        pose proof (Hb z) as Hz.
        destruct (proj1 (IH (size_exp (open_exp_wrt_exp b (e_var_f z)))
                            (size_open_lt_abs A b z)
                            (open_exp_wrt_exp b (e_var_f z)) eq_refl) Hz) as [_ Ha].
        apply (proj1 (lc_annot_open_var b z 0)). exact Ha.
    + intros [Hd Ha]. simpl in Hd, Ha. destruct Ha as [HA Hb].
      constructor; auto.
      intros x.
      apply (proj2 (IH (size_exp (open_exp_wrt_exp b (e_var_f x)))
                       ltac:(rewrite En; apply size_open_lt_abs)
                       (open_exp_wrt_exp b (e_var_f x)) eq_refl)).
      split.
      * apply (proj2 (degree_exp_open_self 0 b x)).
        inversion Hd as [| | |nn0 a0 b0 H1| |]; subst. exact H1.
      * apply (proj2 (lc_annot_open_var b x 0)). exact Hb.
  - (* app *)
    split.
    + intro Hlc.
      inversion Hlc as [| | |a0 b0 Ha Hb|]; subst.
      split.
      * apply degree_wrt_exp_e_app.
        -- destruct (proj1 (IH (size_exp e1) ltac:(simpl; lia) e1 eq_refl) Ha) as [H1 _]; exact H1.
        -- destruct (proj1 (IH (size_exp e2) ltac:(simpl; lia) e2 eq_refl) Hb) as [H2 _]; exact H2.
      * simpl. split.
        -- destruct (proj1 (IH (size_exp e1) ltac:(simpl; lia) e1 eq_refl) Ha) as [_ H1]; exact H1.
        -- destruct (proj1 (IH (size_exp e2) ltac:(simpl; lia) e2 eq_refl) Hb) as [_ H2]; exact H2.
    + intros [Hd Ha]. simpl in Hd, Ha. inversion Hd as [| | | |nn0 a0 b0 H1 H2|]; subst.
      destruct Ha as [Ha1 Ha2].
      constructor.
      * apply (proj2 (IH (size_exp e1) ltac:(simpl; lia) e1 eq_refl)). split; assumption.
      * apply (proj2 (IH (size_exp e2) ltac:(simpl; lia) e2 eq_refl)). split; assumption.
  - (* cast *)
    split.
    + intro Hlc.
      inversion Hlc as [| | | |c0 b0 Hc Hb]; subst.
      split.
      * apply degree_wrt_exp_e_cast.
        destruct (proj1 (IH (size_exp b) ltac:(simpl; lia) b eq_refl) Hb) as [H1 _]; exact H1.
      * simpl. split; auto.
        destruct (proj1 (IH (size_exp b) ltac:(simpl; lia) b eq_refl) Hb) as [_ H1]; exact H1.
    + intros [Hd Ha]. simpl in Hd, Ha. inversion Hd as [| | | | |nn0 c0 b0 H1]; subst.
      destruct Ha as [Hc Ha].
      constructor; auto.
      apply (proj2 (IH (size_exp b) ltac:(simpl; lia) b eq_refl)). split; assumption.
Qed.



Lemma lc_open_indep : forall body y z,
  lc_exp (open_exp_wrt_exp body (e_var_f y)) ->
  lc_exp (open_exp_wrt_exp body (e_var_f z)).
Proof.
  intros body y z H.
  destruct (proj1 (lc_exp_degree_annot (open_exp_wrt_exp body (e_var_f y))) H) as [Hd Ha].
  apply (proj2 (lc_exp_degree_annot (open_exp_wrt_exp body (e_var_f z)))).
  split.
  - apply (proj2 (degree_exp_open_self 0 body z)).
    apply (proj1 (degree_exp_open_self 0 body y)). exact Hd.
  - apply (proj2 (lc_annot_open_var body z 0)).
    apply (proj1 (lc_annot_open_var body y 0)). exact Ha.
Qed.

Lemma CE_lc_back : forall G e A e',
  EquiTypingC G e A e' -> lc_exp e' -> lc_exp e.
Proof.
  intros G e A e' H.
  induction H as [G0 i Hwf
                 |G0 x A0 Hwf Hbinds
                 |L G0 A1 e0 A2 e0' Hbody IHbody
                 |G0 a b A2 a' b' A1 Ha IHa Hb IHb
                 |G0 a B c a' A0 Ha IHa Hcast]; intro Hlc.
  - inversion Hlc. constructor.
  - constructor.
  - (* abs *)
    inversion Hlc as [| |AA bb HA Hb| |]; subst.
    constructor; [ assumption | intros x ].
    pick fresh x0 for L.
    apply (lc_open_indep e0 x0 x).
    apply IHbody; auto.
  - (* app *)
    inversion Hlc as [| | |aa bb Ha0 Hb0|]; subst.
    constructor.
    + apply IHa. assumption.
    + apply IHb. assumption.
  - (* eq *)
    inversion Hlc as [| | | |cc bb Hc Hb]; subst.
    apply IHa. assumption.
Qed.


Lemma CE_value_back : forall G e A v,
  EquiTypingC G e A v -> value v -> value e.
Proof.
  intros G e A v H.
  induction H as [G0 i Hwf
                 |G0 x A0 Hwf Hbinds
                 |L G0 A1 e0 A2 e0' Hbody IHbody
                 |G0 a b A2 a' b' A1 Ha IHa Hb IHb
                 |G0 a B c a' A0 Ha IHa Hcast]; intro Hv.
  - inversion Hv. constructor.
  - inversion Hv.
  - inversion Hv as [|AA bb Hl Hlc| |]; subst.
    apply V_abs.
    + assumption.
    + apply (CE_lc_back G0 (e_abs A1 e0) (t_arrow A1 A2) (e_abs A1 e0')).
      * apply (ECTyping_abs L G0 A1 e0 A2 e0' Hbody).
      * assumption.
  - inversion Hv.
  - inversion Hv as [| |AA bb Hl Hval|c1 c2 bb Hc1 Hc2 Hval]; subst.
    + apply IHa. assumption.
    + apply IHa. assumption.
Qed.

Lemma app_l_star : forall e1 e1' e2,
  (e1 ==>* e1') -> lc_exp e2 -> (e_app e1 e2 ==>* e_app e1' e2).
Proof.
  intros e1 e1' e2 H Hlc.
  induction H using clos_refl_trans_ind.
  - apply rt_step. apply Red_appl; assumption.
  - apply rt_refl.
  - eauto using rt_trans.
Qed.

Lemma app_r_star : forall v1 e2 e2',
  value v1 -> (e2 ==>* e2') -> (e_app v1 e2 ==>* e_app v1 e2').
Proof.
  intros v1 e2 e2' Hv H.
  induction H using clos_refl_trans_ind.
  - apply rt_step. apply Red_appr; assumption.
  - apply rt_refl.
  - eauto using rt_trans.
Qed.

Lemma cast_star : forall c e e',
  lc_castop c -> (e ==>* e') -> (e_cast c e ==>* e_cast c e').
Proof.
  intros c e e' Hc H.
  induction H using clos_refl_trans_ind.
  - apply rt_step. apply Red_cast; assumption.
  - apply rt_refl.
  - eauto using rt_trans.
Qed.

Lemma erase_step : forall a b,
  Reduction a b -> (erase a ==>* erase b).
Proof.
  intros a b Hred.
  induction Hred as [A e e' HlcA Hlce Hval
                    |e1 e2 e1' Hlc2 Hred IHred
                    |v1 e2 e2' Hval Hred IHred
                    |c1 c2 e1 e2 Hlc2 Hlc1 Hv1 Hv2
                    |c1 c2 e Hlc2 Hlc1 Hv
                    |c e e' Hlc Hred IHred
                    |A v Hlc Hv
                    |v Hv
                    |c e Hlc Hv].
  - simpl. rewrite erase_open_exp. apply rt_step. apply Red_beta.
    + assumption.
    + exact (lc_exp_erase (e_abs A e) Hlce).
    + apply value_erase. assumption.
  - simpl. apply app_l_star.
    + exact IHred.
    + exact (lc_exp_erase e2 Hlc2).
  - simpl. apply app_r_star.
    + apply value_erase. assumption.
    + exact IHred.
  - simpl. apply rt_refl.
  - simpl. apply rt_refl.
  - simpl. exact IHred.
  - simpl. apply rt_refl.
  - simpl. apply rt_refl.
  - simpl. apply rt_refl.
Qed.

Lemma erase_steps : forall a b,
  (a ==>* b) ->
  (erase a ==>* erase b).
Proof.
  intros a b H.
  induction H using clos_refl_trans_ind.
  - apply erase_step. assumption.
  - apply rt_refl.
  - eauto using rt_trans.
Qed.



(* ------------------------------------------------------------------ *)
(* Locally-closed types and cast operators                            *)
(* ------------------------------------------------------------------ *)

Lemma size_typ_open_var : forall A X k,
  size_typ (open_typ_wrt_typ_rec k (t_var_f X) A) = size_typ A.
Proof.
  induction A; intros X k; simpl; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
Qed.

Lemma size_typ_open_var' : forall A X,
  size_typ (open_typ_wrt_typ A (t_var_f X)) = size_typ A.
Proof. intros. unfold open_typ_wrt_typ. apply size_typ_open_var. Qed.

Lemma size_open_typ_lt : forall A X,
  size_typ (open_typ_wrt_typ A (t_var_f X)) < S (size_typ A).
Proof. intros. rewrite size_typ_open_var'. lia. Qed.

Lemma lc_typ_degree : forall A, lc_typ A <-> degree_typ_wrt_typ 0 A.
Proof.
  intros A. remember (size_typ A) as n eqn:En. revert A En.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros A En. destruct A as [m|X| |A1 A2|A0]; simpl.
  - (* t_var_b *) split; intros H; [inversion H | inversion H as [|m0 Hm| | |]; lia].
  - split; intros H; constructor.
  - split; intros H; constructor.
  - (* arrow *)
    split.
    + intros H. inversion H as [| |B C HB HC|]; subst.
      constructor.
      * apply (proj1 (IH (size_typ A1) ltac:(simpl; lia) A1 eq_refl)). assumption.
      * apply (proj1 (IH (size_typ A2) ltac:(simpl; lia) A2 eq_refl)). assumption.
    + intros H. inversion H as [| | |B C HB HC|]; subst.
      constructor.
      * apply (proj2 (IH (size_typ A1) ltac:(simpl; lia) A1 eq_refl)). assumption.
      * apply (proj2 (IH (size_typ A2) ltac:(simpl; lia) A2 eq_refl)). assumption.
  - (* mu *)
    split; intros H.
    + inversion H as [| | |B HB]; subst.
      apply degree_wrt_typ_t_mu.
      set (z := fresh (@nil atom)).
      apply (proj1 (degree_typ_open_self 0 A0 z)).
      apply (proj1 (IH (size_typ (open_typ_wrt_typ A0 (t_var_f z)))
                      ltac:(try rewrite En; try rewrite <- En; apply size_open_typ_lt)
                      (open_typ_wrt_typ A0 (t_var_f z)) eq_refl)).
      apply HB.
    + inversion H as [| | | |n0 B HB]; subst.
      constructor. intros X.
      apply (proj2 (IH (size_typ (open_typ_wrt_typ A0 (t_var_f X)))
                      ltac:(try rewrite En; try rewrite <- En; apply size_open_typ_lt)
                      (open_typ_wrt_typ A0 (t_var_f X)) eq_refl)).
      apply (proj2 (degree_typ_open_self 0 A0 X)). exact HB.
Qed.

Lemma lc_typ_open_indep : forall A X Y,
  lc_typ (open_typ_wrt_typ A (t_var_f X)) ->
  lc_typ (open_typ_wrt_typ A (t_var_f Y)).
Proof.
  intros A X Y H.
  apply (proj2 (lc_typ_degree (open_typ_wrt_typ A (t_var_f Y)))).
  apply (proj2 (degree_typ_open_self 0 A Y)).
  apply (proj1 (degree_typ_open_self 0 A X)).
  apply (proj1 (lc_typ_degree (open_typ_wrt_typ A (t_var_f X)))). assumption.
Qed.

Lemma WFT_lc_typ : forall D A, WFT D A -> lc_typ A.
Proof.
  intros D A H.
  induction H as [D0
                 |D0 X Hin
                 |D0 A0 B0 HA IHA HB IHB
                 |L D0 A0 Hbody IHbody].
  - constructor.
  - constructor.
  - constructor; assumption.
  - (* rec *)
    constructor. intros X.
    pick fresh z for L.
    apply (lc_typ_open_indep A0 z X).
    apply IHbody. assumption.
Qed.

Lemma size_castop_open_var : forall c cx k,
  size_castop (open_castop_wrt_castop_rec k (c_var_f cx) c) = size_castop c.
Proof.
  induction c; intros cx k; simpl; auto.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
Qed.

Lemma degree_castop_open_self : forall nn c cx,
  degree_castop_wrt_castop nn (open_castop_wrt_castop_rec nn (c_var_f cx) c) <->
  degree_castop_wrt_castop (S nn) c.
Proof.
  intros nn c; revert nn.
  induction c; intros nn cx; simpl.
  - destruct (lt_eq_lt_dec n nn) as [[Hlt|Heq]|Hgt]; simpl.
    + split; intros H; apply degree_wrt_castop_c_var_b; lia.
    + subst n. split; intros H.
      * apply degree_wrt_castop_c_var_b. lia.
      * apply degree_wrt_castop_c_var_f.
    + split; intros H;
        inversion H as [|m Hm| | | | | |]; subst; lia.
  - split; intros H; apply degree_wrt_castop_c_var_f.
  - split; intros H; apply degree_wrt_castop_c_id.
  - split; intros H; apply degree_wrt_castop_c_unfold.
  - split; intros H; apply degree_wrt_castop_c_fold.
  - (* arrow *)
    split; intros H.
    + inversion H as [|m Hm| | | |a0 b0 H1 H2| |]; subst.
      apply degree_wrt_castop_c_arrow;
        [ apply (proj1 (IHc1 nn cx)) | apply (proj1 (IHc2 nn cx)) ]; assumption.
    + inversion H as [|m Hm| | | |a0 b0 H1 H2| |]; subst.
      apply degree_wrt_castop_c_arrow;
        [ apply (proj2 (IHc1 nn cx)) | apply (proj2 (IHc2 nn cx)) ]; assumption.
  - (* seq *)
    split; intros H.
    + inversion H as [|m Hm| | | | |a0 b0 H1 H2|]; subst.
      apply degree_wrt_castop_c_seq;
        [ apply (proj1 (IHc1 nn cx)) | apply (proj1 (IHc2 nn cx)) ]; assumption.
    + inversion H as [|m Hm| | | | |a0 b0 H1 H2|]; subst.
      apply degree_wrt_castop_c_seq;
        [ apply (proj2 (IHc1 nn cx)) | apply (proj2 (IHc2 nn cx)) ]; assumption.
  - (* fixc *)
    split; intros H.
    + inversion H as [|m Hm| | | | | |nn0 cc Hd]; subst.
      apply degree_wrt_castop_c_fixc.
      apply (proj1 (IHc (S nn) cx)). assumption.
    + inversion H as [|m Hm| | | | | |nn0 cc Hd]; subst.
      apply degree_wrt_castop_c_fixc.
      apply (proj2 (IHc (S nn) cx)). assumption.
Qed.

Fixpoint lc_annot_castop (c:castop) : Prop :=
  match c with
  | c_var_b _ => True
  | c_var_f _ => True
  | c_id => True
  | c_unfold A => lc_typ A
  | c_fold A => lc_typ A
  | c_arrow a b => lc_annot_castop a /\ lc_annot_castop b
  | c_seq a b => lc_annot_castop a /\ lc_annot_castop b
  | c_fixc a => lc_annot_castop a
  end.

Lemma lc_annot_castop_open : forall c cx k,
  lc_annot_castop (open_castop_wrt_castop_rec k (c_var_f cx) c) <->
  lc_annot_castop c.
Proof.
  induction c; intros cx k; simpl.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; tauto.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - split; intros [H1 H2]; split;
      [ apply (proj1 (IHc1 cx k)) | apply (proj1 (IHc2 cx k))
      | apply (proj2 (IHc1 cx k)) | apply (proj2 (IHc2 cx k)) ]; assumption.
  - split; intros [H1 H2]; split;
      [ apply (proj1 (IHc1 cx k)) | apply (proj1 (IHc2 cx k))
      | apply (proj2 (IHc1 cx k)) | apply (proj2 (IHc2 cx k)) ]; assumption.
  - split; intros H; [apply (proj1 (IHc cx (S k))) | apply (proj2 (IHc cx (S k)))]; assumption.
Qed.

Lemma size_castop_open : forall c cx,
  size_castop (open_castop_wrt_castop c (c_var_f cx)) = size_castop c.
Proof. intros. unfold open_castop_wrt_castop. apply size_castop_open_var. Qed.

Lemma lc_castop_degree_annot : forall c,
  lc_castop c <-> degree_castop_wrt_castop 0 c /\ lc_annot_castop c.
Proof.
  intros c. remember (size_castop c) as n eqn:En. revert c En.
  induction n as [n IH] using (well_founded_induction lt_wf).
  intros c En.
  destruct c as [nb|cx| |A0|A0|a b|a b|c0]; simpl.
  - (* c_var_b *)
    split.
    + intro H; inversion H.
    + intros [Hd _]; inversion Hd as [|m Hm| | | | | |]; lia.
  - (* c_var_f *)
    split.
    + intro H; split; [constructor | exact I].
    + intros [Hd Ha]; constructor.
  - (* c_id *)
    split.
    + intro H; split; [constructor | exact I].
    + intros [Hd Ha]; constructor.
  - (* c_unfold *)
    split.
    + intro H; inversion H as [| |A1 HA| | | |]; subst.
      split; [constructor | assumption].
    + intros [Hd Ha]; simpl in Ha. constructor. assumption.
  - (* c_fold *)
    split.
    + intro H; inversion H as [| | |A1 HA| | |]; subst.
      split; [constructor | assumption].
    + intros [Hd Ha]; simpl in Ha. constructor. assumption.
  - (* c_arrow *)
    split.
    + intro H; inversion H as [| | | |a0 b0 Ha Hb| |]; subst.
      split.
      * constructor.
        -- apply (proj1 (IH (size_castop a) ltac:(simpl; lia) a eq_refl)); assumption.
        -- apply (proj1 (IH (size_castop b) ltac:(simpl; lia) b eq_refl)); assumption.
      * simpl. split.
        -- apply (proj1 (IH (size_castop a) ltac:(simpl; lia) a eq_refl)); assumption.
        -- apply (proj1 (IH (size_castop b) ltac:(simpl; lia) b eq_refl)); assumption.
    + intros [Hd Ha]; simpl in Hd, Ha.
      inversion Hd as [| | | | |a0 b0 H1 H2| |]; subst.
      destruct Ha as [Ha1 Ha2].
      constructor.
      * apply (proj2 (IH (size_castop a) ltac:(simpl; lia) a eq_refl)). split; assumption.
      * apply (proj2 (IH (size_castop b) ltac:(simpl; lia) b eq_refl)). split; assumption.
  - (* c_seq *)
    split.
    + intro H; inversion H as [| | | | |a0 b0 Ha Hb|]; subst.
      split.
      * constructor.
        -- apply (proj1 (IH (size_castop a) ltac:(simpl; lia) a eq_refl)); assumption.
        -- apply (proj1 (IH (size_castop b) ltac:(simpl; lia) b eq_refl)); assumption.
      * simpl. split.
        -- apply (proj1 (IH (size_castop a) ltac:(simpl; lia) a eq_refl)); assumption.
        -- apply (proj1 (IH (size_castop b) ltac:(simpl; lia) b eq_refl)); assumption.
    + intros [Hd Ha]; simpl in Hd, Ha.
      inversion Hd as [|m Hm| | | | |a0 b0 H1 H2|]; subst.
      destruct Ha as [Ha1 Ha2].
      constructor.
      * apply (proj2 (IH (size_castop a) ltac:(simpl; lia) a eq_refl)). split; assumption.
      * apply (proj2 (IH (size_castop b) ltac:(simpl; lia) b eq_refl)). split; assumption.
  - (* c_fixc *)
    split.
    + intro H; inversion H as [| | | | | |c1 Hfa]; subst.
      set (z := fresh (@nil atom)).
      destruct (proj1 (IH (size_castop (open_castop_wrt_castop c0 (c_var_f z)))
                         ltac:(rewrite size_castop_open; simpl; lia)
                         (open_castop_wrt_castop c0 (c_var_f z)) eq_refl)
                        (Hfa z)) as [Hd Ha].
      split.
      * apply degree_wrt_castop_c_fixc.
        apply (proj1 (degree_castop_open_self 0 c0 z)). exact Hd.
      * simpl. apply (proj1 (lc_annot_castop_open c0 z 0)). exact Ha.
    + intros [Hd Ha]; simpl in Hd, Ha.
      inversion Hd as [| | | | | | |nn0 c1 Hb]; subst.
      constructor. intros x.
      apply (proj2 (IH (size_castop (open_castop_wrt_castop c0 (c_var_f x)))
                       ltac:(rewrite size_castop_open; simpl; lia)
                       (open_castop_wrt_castop c0 (c_var_f x)) eq_refl)).
      split.
      * apply (proj2 (degree_castop_open_self 0 c0 x)). exact Hb.
      * apply (proj2 (lc_annot_castop_open c0 x 0)). exact Ha.
Qed.

Lemma lc_castop_open_indep : forall c x y,
  lc_castop (open_castop_wrt_castop c (c_var_f x)) ->
  lc_castop (open_castop_wrt_castop c (c_var_f y)).
Proof.
  intros c x y H.
  destruct (proj1 (lc_castop_degree_annot (open_castop_wrt_castop c (c_var_f x))) H) as [Hd Ha].
  apply (proj2 (lc_castop_degree_annot (open_castop_wrt_castop c (c_var_f y)))).
  split.
  - apply (proj2 (degree_castop_open_self 0 c y)).
    apply (proj1 (degree_castop_open_self 0 c x)). exact Hd.
  - apply (proj2 (lc_annot_castop_open c y 0)).
    apply (proj1 (lc_annot_castop_open c x 0)). exact Ha.
Qed.

Lemma TypCast_lc : forall D E A B c,
  TypCast D E A B c -> lc_castop c.
Proof.
  intros D E A B c H.
  induction H as [D0 E0 A0 Hwf Hu
                 |D0 E0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2
                 |D0 E0 A0 Hwf Hu
                 |D0 E0 A0 Hwf Hu
                 |D0 E0 A0 C0 c1 c2 B0 H1 IH1 H2 IH2
                 |D0 E0 A0 B0 cx Hwa Hwb Hu Hin
                 |L D0 E0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2].
  - constructor.
  - constructor; assumption.
  - apply lc_c_unfold. apply (WFT_lc_typ D0). assumption.
  - apply lc_c_fold. apply (WFT_lc_typ D0). assumption.
  - constructor; assumption.
  - constructor.
  - (* fix *)
    apply lc_c_fixc. intros x.
    simpl. apply lc_c_arrow.
    + pick fresh z for L.
      apply (lc_castop_open_indep c1 z x). apply IH1. assumption.
    + pick fresh z for L.
      apply (lc_castop_open_indep c2 z x). apply IH2. assumption.
Qed.

Lemma CE_lc_fwd : forall G e A e',
  EquiTypingC G e A e' -> lc_exp e -> lc_exp e'.
Proof.
  intros G e A e' H.
  induction H as [G0 i Hwf
                 |G0 x A0 Hwf Hbinds
                 |L G0 A1 e0 A2 e0' Hbody IHbody
                 |G0 a b A2 a' b' A1 Ha IHa Hb IHb
                 |G0 a B c a' A0 Ha IHa Hcast]; intro Hlc.
  - constructor.
  - constructor.
  - (* abs *)
    inversion Hlc as [| |AA bb HA Hb0| |]; subst.
    constructor; auto.
    intros x.
    pick fresh z for L.
    apply (lc_open_indep e0' z x).
    apply IHbody.
    + assumption.
    + apply Hb0.
  - (* app *)
    inversion Hlc as [| | |aa bb Ha0 Hb0|]; subst.
    constructor.
    + apply IHa. assumption.
    + apply IHb. assumption.
  - (* eq *)
    constructor.
    + exact (TypCast_lc nil nil A0 B c Hcast).
    + apply IHa. assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Inversions for TypCast                                             *)
(* ------------------------------------------------------------------ *)

Lemma TCast_id_inv : forall D E A B,
  TypCast D E A B c_id -> A = B.
Proof.
  intros D E A B H.
  inversion H as [D0 E0 A0 Hwf Hu| | | | | |]; subst. reflexivity.
Qed.

Lemma TCast_arrow_inv : forall D E A B c1 c2,
  TypCast D E A B (c_arrow c1 c2) ->
  exists A1 B1 A2 B2,
    A = t_arrow A1 B1 /\ B = t_arrow A2 B2 /\
    TypCast D E A1 A2 c1 /\ TypCast D E B1 B2 c2.
Proof.
  intros D E A B c1 c2 H.
  inversion H as [|D0 E0 A1 B1 A2 B2 c1' c2' H1 H2| | | | |]; subst.
  exists A1, B1, A2, B2. repeat split; auto.
Qed.

Lemma TCast_unfold_inv : forall D E A B X,
  TypCast D E A B (c_unfold X) ->
  exists A0, X = t_mu A0 /\ A = t_mu A0 /\ B = unfold_mu A0.
Proof.
  intros D E A B X H.
  inversion H as [| |D0 E0 A0 Hwf Hu| | | |]; subst. eauto.
Qed.

Lemma TCast_fold_inv : forall D E A B X,
  TypCast D E A B (c_fold X) ->
  exists A0, X = t_mu A0 /\ A = unfold_mu A0 /\ B = t_mu A0.
Proof.
  intros D E A B X H.
  inversion H as [| | |D0 E0 A0 Hwf Hu| | |]; subst. eauto.
Qed.

Lemma TCast_seq_inv : forall D E A C c1 c2,
  TypCast D E A C (c_seq c1 c2) ->
  exists B, TypCast D E A B c1 /\ TypCast D E B C c2.
Proof.
  intros D E A C c1 c2 H.
  inversion H as [| | | |D0 E0 A0 C0 c1' c2' B0 H1 H2| |]; subst. eauto.
Qed.

Lemma TCast_var_inv : forall D E A B cx,
  TypCast D E A B (c_var_f cx) ->
  WFT D A /\ WFT D B /\ uniq E /\ In (cx, (A,B)) E.
Proof.
  intros D E A B cx H.
  inversion H as [| | | | |D0 E0 A0 B0 cx0 Hwa Hwb Hu Hin|]; subst.
  eauto.
Qed.

Lemma TCast_fix_inv : forall D E A B c,
  TypCast D E A B (c_fixc c) ->
  exists L A1 B1 A2 B2 c1 c2,
    c = c_arrow c1 c2 /\
    A = t_arrow A1 B1 /\ B = t_arrow A2 B2 /\
    (forall cx, cx \notin L ->
       TypCast D ((cx, (t_arrow A1 B1, t_arrow A2 B2)) :: E) A1 A2
         (open_castop_wrt_castop c1 (c_var_f cx))) /\
    (forall cx, cx \notin L ->
       TypCast D ((cx, (t_arrow A1 B1, t_arrow A2 B2)) :: E) B1 B2
         (open_castop_wrt_castop c2 (c_var_f cx))).
Proof.
  intros D E A B c H.
  inversion H as [| | | | | |L D0 E0 A1 B1 A2 B2 c1 c2 Q1 Q2]; subst.
  exists L, A1, B1, A2, B2, c1, c2. repeat split; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Reversal of casts and contexts                                     *)
(* ------------------------------------------------------------------ *)

Definition rev_pair (p:typ*typ) : typ*typ := (snd p, fst p).
Definition rev_cctx (E:cctx) : cctx :=
  map (fun q => (fst q, rev_pair (snd q))) E.

Lemma dom_rev_cctx : forall E, dom (rev_cctx E) = dom E.
Proof.
  induction E as [|[x p] E IH]; simpl; auto.
  destruct p as [A B]; simpl. rewrite IH. reflexivity.
Qed.

Lemma uniq_rev_cctx : forall E, uniq (rev_cctx E) <-> uniq E.
Proof.
  induction E as [|[x p] E IH]; simpl.
  - split; constructor.
  - destruct p as [A B]; simpl.
    rewrite uniq_cons_iff, uniq_cons_iff, dom_rev_cctx, IH. tauto.
Qed.

Lemma In_rev_cctx : forall E cx A B,
  In (cx, (A,B)) (rev_cctx E) <-> In (cx, (B,A)) E.
Proof.
  induction E as [|[y p] E IH]; intros cx A B; simpl.
  - split; intros [].
  - destruct p as [P Q]; simpl.
    split; intros [H|H].
    + left. injection H as ? ?. subst. reflexivity.
    + right. apply IH. assumption.
    + left. injection H as ? ?. subst. reflexivity.
    + right. apply IH. assumption.
Qed.

Lemma rev_cast_open_var : forall c v k,
  rev_cast (open_castop_wrt_castop_rec k v c) =
  open_castop_wrt_castop_rec k (rev_cast v) (rev_cast c).
Proof.
  induction c; intros v k; simpl.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; auto.
  - auto.
  - auto.
  - auto.
  - auto.
  - rewrite IHc1, IHc2. auto.
  - rewrite IHc1, IHc2. auto.
  - rewrite IHc. auto.
Qed.

Lemma rev_cast_open_var' : forall c cx,
  rev_cast (open_castop_wrt_castop c (c_var_f cx)) =
  open_castop_wrt_castop (rev_cast c) (c_var_f cx).
Proof. intros. unfold open_castop_wrt_castop. apply rev_cast_open_var. Qed.

Lemma TypCast_rev : forall D E A B c,
  TypCast D E A B c -> TypCast D (rev_cctx E) B A (rev_cast c).
Proof.
  intros D E A B c H.
  induction H as [D0 E0 A0 Hwf Hu
                 |D0 E0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2
                 |D0 E0 A0 Hwf Hu
                 |D0 E0 A0 Hwf Hu
                 |D0 E0 A0 C0 c1 c2 B0 H1 IH1 H2 IH2
                 |D0 E0 A0 B0 cx Hwa Hwb Hu Hin
                 |L D0 E0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2].
  - (* id *) simpl. apply TCast_id; auto. apply (proj2 (uniq_rev_cctx E0)). assumption.
  - (* arrow *) simpl. apply TCast_arrow; assumption.
  - (* unfold *) simpl. apply TCast_fold.
    + assumption.
    + apply (proj2 (uniq_rev_cctx E0)). assumption.
  - (* fold *) simpl. apply TCast_unfold.
    + assumption.
    + apply (proj2 (uniq_rev_cctx E0)). assumption.
  - (* seq *) simpl. eapply TCast_seq; [exact IH2 | exact IH1].
  - (* var *) simpl. apply TCast_var.
    + exact Hwb.
    + exact Hwa.
    + apply (proj2 (uniq_rev_cctx E0)). exact Hu.
    + apply (proj2 (In_rev_cctx E0 cx B0 A0)). exact Hin.
  - (* fix *) simpl. apply TCast_fix with (L := L).
    + intros cx Hcx. rewrite <- rev_cast_open_var'.
      apply IH1. assumption.
    + intros cx Hcx. rewrite <- rev_cast_open_var'.
      apply IH2. assumption.
Qed.

Lemma open_castop_degree_id : forall c d,
  degree_castop_wrt_castop d c ->
  forall k v, open_castop_wrt_castop_rec (d + k) v c = c.
Proof.
  intros c. induction c; intros d Hd k v; simpl in *.
  - (* var_b *)
    inversion Hd as [|n1 n2 Hlt| | | | | |]; subst.
    destruct (lt_eq_lt_dec n (d + k)) as [[Hlt0|Heq]|Hgt]; simpl.
    + auto.
    + subst n. exfalso. lia.
    + exfalso. lia.
  - auto.
  - auto.
  - auto.
  - auto.
  - inversion Hd as [| | | | |nn0 a0 b0 H1 H2| |]; subst.
    rewrite (IHc1 d H1 k v), (IHc2 d H2 k v). auto.
  - inversion Hd as [| | | | | |nn0 a0 b0 H1 H2|]; subst.
    rewrite (IHc1 d H1 k v), (IHc2 d H2 k v). auto.
  - inversion Hd as [| | | | | | |nn0 c1 H1]; subst.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite (IHc (S d) H1 k v). auto.
Qed.

Lemma open_castop_lc_id : forall c,
  lc_castop c -> forall k v, open_castop_wrt_castop_rec k v c = c.
Proof.
  intros c Hlc k v.
  destruct ((proj1 (lc_castop_degree_annot c)) Hlc) as [Hd _].
  exact (open_castop_degree_id c 0 Hd k v).
Qed.

Lemma castsubst_open_rec : forall kk c cval cx cy,
  lc_castop cval -> cy <> cx ->
  castsubst_castop cval cx (open_castop_wrt_castop_rec kk (c_var_f cy) c) =
  open_castop_wrt_castop_rec kk (c_var_f cy) (castsubst_castop cval cx c).
Proof.
  intros kk c. revert kk.
  induction c as [nb
                |cz
                | |A0|A0
                |a IHa b IHb
                |a IHa b IHb
                |c0 IHc];
    intros kk cval cx cy Hlc Hneq; simpl.
  - destruct (lt_eq_lt_dec nb kk) as [[Hlt|Heq]|Hgt]; simpl.
    + reflexivity.
    + destruct (eq_var cy cx) as [->|Hne].
      * exfalso; auto.
      * reflexivity.
    + reflexivity.
  - destruct (eq_var cz cx) as [Heq|Hne].
    + subst. simpl. symmetry. apply open_castop_lc_id. assumption.
    + simpl. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IHa kk cval cx cy Hlc Hneq), (IHb kk cval cx cy Hlc Hneq).
    reflexivity.
  - rewrite (IHa kk cval cx cy Hlc Hneq), (IHb kk cval cx cy Hlc Hneq).
    reflexivity.
  - rewrite (IHc (S kk) cval cx cy Hlc Hneq). reflexivity.
Qed.


Lemma castsubst_open_var : forall c cval cx cy,
  lc_castop cval -> cy <> cx ->
  castsubst_castop cval cx (open_castop_wrt_castop c (c_var_f cy)) =
  open_castop_wrt_castop (castsubst_castop cval cx c) (c_var_f cy).
Proof. intros. unfold open_castop_wrt_castop. apply castsubst_open_rec; auto. Qed.

Lemma In_dom_perm : forall (A:Type) (E E':list (atom*A)),
  Permutation E E' -> forall x, x `in` dom E <-> x `in` dom E'.
Proof.
  intros A E E' Hp. induction Hp as [|x l l' Hp IHp|x y l|l l' l'' Hp1 IH1 Hp2 IH2];
    intro x0.
  - simpl. tauto.
  - destruct x as [a b]. simpl. rewrite add_iff, add_iff, IHp. tauto.
  - destruct x as [a b], y as [c d]. simpl. rewrite !add_iff. tauto.
  - simpl. rewrite IH1, IH2. tauto.
Qed.

Lemma uniq_perm : forall (A:Type) (E E':list (atom*A)),
  Permutation E E' -> uniq E -> uniq E'.
Proof.
  intros A E E' Hp.
  induction Hp as [|x l l' Hp IHp|x y l|l l' l'' Hp1 IH1 Hp2 IH2];
    intro Hu.
  - assumption.
  - (* skip *)
    destruct x as [a b].
    destruct (proj1 (uniq_cons_iff A a b l) Hu) as [Hu' Hx].
    apply (proj2 (uniq_cons_iff A a b l')). split.
    + apply IHp. assumption.
    + intro Hbad. apply Hx.
      apply (proj2 (In_dom_perm A l l' Hp a)). assumption.
  - (* swap *)
    destruct x as [a b], y as [c d].
    destruct (proj1 (uniq_cons_iff A c d ((a,b) :: l)) Hu) as [Hu1 Hc].
    destruct (proj1 (uniq_cons_iff A a b l) Hu1) as [Hu2 Ha].
    assert (Hca : c <> a).
    { intro Heq. subst c. apply Hc. simpl. rewrite add_iff. left. reflexivity. }
    assert (Hcl : c \notin dom l).
    { intro Hbad. apply Hc. simpl. rewrite add_iff. right. assumption. }
    apply (proj2 (uniq_cons_iff A a b ((c,d) :: l))). split.
    + apply (proj2 (uniq_cons_iff A c d l)). split; assumption.
    + intro Hbad. simpl in Hbad. rewrite add_iff in Hbad.
      destruct Hbad as [Heq|Hin]; auto.
  - (* trans *)
    apply IH2. apply IH1. assumption.
Qed.


Lemma TypCast_perm : forall D E E' A B c,
  Permutation E E' -> TypCast D E A B c -> TypCast D E' A B c.
Proof.
  intros D E E' A B c Hp H. revert E' Hp.
  induction H as [D0 E0 A0 Hwf Hu
                 |D0 E0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2
                 |D0 E0 A0 Hwf Hu
                 |D0 E0 A0 Hwf Hu
                 |D0 E0 A0 C0 c1 c2 B0 H1 IH1 H2 IH2
                 |D0 E0 A0 B0 cx Hwa Hwb Hu Hin
                 |L D0 E0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2];
    intros E' Hp.
  - apply TCast_id; auto. apply (uniq_perm _ _ _ Hp Hu).
  - apply TCast_arrow; [apply IH1|apply IH2]; assumption.
  - apply TCast_unfold; auto. apply (uniq_perm _ _ _ Hp Hu).
  - apply TCast_fold; auto. apply (uniq_perm _ _ _ Hp Hu).
  - eapply TCast_seq; [apply IH1|apply IH2]; assumption.
  - apply TCast_var; auto.
    + apply (uniq_perm _ _ _ Hp Hu).
    + apply (Permutation_in _ Hp Hin).
  - apply (TCast_fix L D0 E' A1 B1 A2 B2 c1 c2).
    + intros cx Hcx.
      apply (IH1 cx Hcx ((cx, (t_arrow A1 B1, t_arrow A2 B2)) :: E')).
      apply perm_skip. assumption.
    + intros cx Hcx.
      apply (IH2 cx Hcx ((cx, (t_arrow A1 B1, t_arrow A2 B2)) :: E')).
      apply perm_skip. assumption.
Qed.

Lemma TypCast_weak : forall D E y C A B c,
  y \notin dom E -> TypCast D E A B c -> TypCast D (cons (y,C) E) A B c.
Proof.
  intros D E y C A B c Hfresh H. revert y C Hfresh.
  induction H as [D0 E0 A0 Hwf Hu
                 |D0 E0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2
                 |D0 E0 A0 Hwf Hu
                 |D0 E0 A0 Hwf Hu
                 |D0 E0 A0 C0 c1 c2 B0 H1 IH1 H2 IH2
                 |D0 E0 A0 B0 cx Hwa Hwb Hu Hin
                 |L D0 E0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2];
    intros y C Hfresh.
  - apply TCast_id; auto.
  - apply TCast_arrow; [apply IH1|apply IH2]; assumption.
  - apply TCast_unfold; auto.
  - apply TCast_fold; auto.
  - eapply TCast_seq; [apply IH1|apply IH2]; assumption.
  - apply TCast_var; auto.
    simpl. right. assumption.
  - (* fix *)
    apply (TCast_fix (L \u {{y}}) D0 (cons (y,C) E0) A1 B1 A2 B2 c1 c2).
    + intros cx Hcx.
      assert (HcxL : cx \notin L) by fsetdec.
      assert (Hcxy : cx <> y) by (intro Heq; subst; fsetdec).
      apply (TypCast_perm D0 ((y,C) :: (cx, (t_arrow A1 B1, t_arrow A2 B2)) :: E0)
                           ((cx, (t_arrow A1 B1, t_arrow A2 B2)) :: (y,C) :: E0)).
      * apply perm_swap.
      * apply IH1.
        -- fsetdec.
        -- simpl. fsetdec.
    + intros cx Hcx.
      assert (HcxL : cx \notin L) by fsetdec.
      assert (Hcxy : cx <> y) by (intro Heq; subst; fsetdec).
      apply (TypCast_perm D0 ((y,C) :: (cx, (t_arrow A1 B1, t_arrow A2 B2)) :: E0)
                           ((cx, (t_arrow A1 B1, t_arrow A2 B2)) :: (y,C) :: E0)).
      * apply perm_swap.
      * apply IH2.
        -- fsetdec.
        -- simpl. fsetdec.
Qed.

Lemma TypCast_subst_perm : forall D G A B c,
  TypCast D G A B c ->
  forall E cx X Y cval,
    TypCast D E X Y cval ->
    Permutation G (cons (cx, (X,Y)) E) ->
    TypCast D E A B (castsubst_castop cval cx c).
Proof.
  intros D G A B c H.
  induction H as [D0 G0 A0 Hwf Hu
                 |D0 G0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2
                 |D0 G0 A0 Hwf Hu
                 |D0 G0 A0 Hwf Hu
                 |D0 G0 A0 C0 c1 c2 B0 H1 IH1 H2 IH2
                 |D0 G0 A0 B0 cy Hwa Hwb Hu Hin
                 |L D0 G0 A1 B1 A2 B2 c1 c2 H1 IH1 H2 IH2];
    intros E cx X Y cval Hcval Hperm.
  - (* id *)
    simpl. apply TCast_id; auto.
    pose proof (uniq_perm _ _ _ Hperm Hu) as Hu'.
    exact (uniq_cons_1 (typ*typ) cx (X,Y) E Hu').
  - (* arrow *)
    simpl. apply TCast_arrow.
    + apply (IH1 E cx X Y cval Hcval Hperm).
    + apply (IH2 E cx X Y cval Hcval Hperm).
  - (* unfold *)
    simpl. apply TCast_unfold; auto.
    pose proof (uniq_perm _ _ _ Hperm Hu) as Hu'.
    exact (uniq_cons_1 (typ*typ) cx (X,Y) E Hu').
  - (* fold *)
    simpl. apply TCast_fold; auto.
    pose proof (uniq_perm _ _ _ Hperm Hu) as Hu'.
    exact (uniq_cons_1 (typ*typ) cx (X,Y) E Hu').
  - (* seq *)
    simpl. eapply TCast_seq.
    + apply (IH1 E cx X Y cval Hcval Hperm).
    + apply (IH2 E cx X Y cval Hcval Hperm).
  - (* var *)
    simpl.
    assert (Hin' : In (cy, (A0,B0)) (cons (cx, (X,Y)) E)).
    { apply (Permutation_in _ Hperm Hin). }
    assert (Hu' : uniq (cons (cx, (X,Y)) E)).
    { apply (uniq_perm _ _ _ Hperm Hu). }
    destruct (eq_var cy cx) as [Heq|Hne].
    + (* cy = cx *)
      subst cy.
      assert (Hin2 : In (cx, (X,Y)) (cons (cx, (X,Y)) E)).
      { simpl. auto. }
      pose proof (binds_unique _ _ _ _ _ Hin' Hin2 Hu') as HeqP.
      injection HeqP as HAX HBY. subst A0 B0.
      exact Hcval.
    + (* cy <> cx *)
      apply TCast_var.
      * exact Hwa.
      * exact Hwb.
      * exact (uniq_cons_1 (typ*typ) cx (X,Y) E Hu').
      * simpl in Hin'. destruct Hin' as [Heq|HinE].
        -- injection Heq as Hcy Hp. exfalso. congruence.
        -- assumption.
  - (* fix *)
    simpl.
    apply (TCast_fix (L \u {{cx}} \u dom E) D0 E A1 B1 A2 B2
                     (castsubst_castop cval cx c1)
                     (castsubst_castop cval cx c2)).
    + intros cy Hcy.
      assert (HcyL : cy \notin L) by fsetdec.
      assert (Hcycx : cy <> cx) by (intro Heq; subst; fsetdec).
      assert (Hcydom : cy \notin dom E) by fsetdec.
      assert (Hcw : TypCast D0 (cons (cy, (t_arrow A1 B1, t_arrow A2 B2)) E)
                           X Y cval).
      { apply (TypCast_weak D0 E cy (t_arrow A1 B1, t_arrow A2 B2) X Y cval); assumption. }
      assert (Hperm' : Permutation ((cy, (t_arrow A1 B1, t_arrow A2 B2)) :: G0)
                       (cons (cx, (X,Y)) (cons (cy, (t_arrow A1 B1, t_arrow A2 B2)) E))).
      { eapply perm_trans.
        - apply perm_skip. exact Hperm.
        - apply perm_swap. }
      rewrite <- (castsubst_open_var c1 cval cx cy (TypCast_lc D0 E X Y cval Hcval) Hcycx).
      apply (IH1 cy HcyL (cons (cy, (t_arrow A1 B1, t_arrow A2 B2)) E) cx X Y cval Hcw Hperm').
    + intros cy Hcy.
      assert (HcyL : cy \notin L) by fsetdec.
      assert (Hcycx : cy <> cx) by (intro Heq; subst; fsetdec).
      assert (Hcydom : cy \notin dom E) by fsetdec.
      assert (Hcw : TypCast D0 (cons (cy, (t_arrow A1 B1, t_arrow A2 B2)) E)
                           X Y cval).
      { apply (TypCast_weak D0 E cy (t_arrow A1 B1, t_arrow A2 B2) X Y cval); assumption. }
      assert (Hperm' : Permutation ((cy, (t_arrow A1 B1, t_arrow A2 B2)) :: G0)
                       (cons (cx, (X,Y)) (cons (cy, (t_arrow A1 B1, t_arrow A2 B2)) E))).
      { eapply perm_trans.
        - apply perm_skip. exact Hperm.
        - apply perm_swap. }
      rewrite <- (castsubst_open_var c2 cval cx cy (TypCast_lc D0 E X Y cval Hcval) Hcycx).
      apply (IH2 cy HcyL (cons (cy, (t_arrow A1 B1, t_arrow A2 B2)) E) cx X Y cval Hcw Hperm').
Qed.


Lemma if_eq_var_self : forall (A:Type) (a b:A) (x:atom),
  (if eq_var x x then a else b) = a.
Proof. intros. destruct (eq_var x x) as [Heq|Hne]. - reflexivity. - exfalso. auto. Qed.

Lemma castsubst_var_self : forall cval (cx:atom),
  castsubst_castop cval cx (c_var_f cx) = cval.
Proof. intros. simpl. apply if_eq_var_self. Qed.

Lemma if_eq_var_neq : forall (A:Type) (a b:A) (x y:atom),
  x <> y -> (if eq_var x y then a else b) = b.
Proof. intros. destruct (eq_var x y) as [Heq|Hne]; [exfalso;auto|reflexivity]. Qed.

Lemma castsubst_var_other : forall cval (cx cz:atom),
  cz <> cx -> castsubst_castop cval cx (c_var_f cz) = c_var_f cz.
Proof.
  intros. simpl. apply if_eq_var_neq. assumption.
Qed.

Lemma castsubst_open_same_rec : forall k c cval cx,
  cx \notin castfv_castop c ->
  castsubst_castop cval cx (open_castop_wrt_castop_rec k (c_var_f cx) c) =
  open_castop_wrt_castop_rec k cval c.
Proof.
  intros k c. revert k.
  induction c as [nb|cz| |A0|A0|a IHa b IHb|a IHa b IHb|c0 IHc];
    intros k cval cx Hfresh; simpl in *.
  - destruct (lt_eq_lt_dec nb k) as [[Hlt|Heq]|Hgt]; simpl.
    + reflexivity.
    + subst nb. change (castsubst_castop cval cx (c_var_f cx) = cval).
      apply castsubst_var_self.
    + reflexivity.
  - destruct (eq_var cz cx) as [Heq|Hne].
    + subst. exfalso. apply Hfresh. simpl. fsetdec.
    + reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (Hfa : cx \notin castfv_castop a) by fsetdec.
    assert (Hfb : cx \notin castfv_castop b) by fsetdec.
    rewrite (IHa k cval cx Hfa), (IHb k cval cx Hfb). reflexivity.
  - assert (Hfa : cx \notin castfv_castop a) by fsetdec.
    assert (Hfb : cx \notin castfv_castop b) by fsetdec.
    rewrite (IHa k cval cx Hfa), (IHb k cval cx Hfb). reflexivity.
  - rewrite (IHc (S k) cval cx Hfresh). reflexivity.
Qed.

Lemma castsubst_open_same : forall c cval cx,
  cx \notin castfv_castop c ->
  castsubst_castop cval cx (open_castop_wrt_castop c (c_var_f cx)) =
  open_castop_wrt_castop c cval.
Proof. intros. unfold open_castop_wrt_castop. apply castsubst_open_same_rec. assumption. Qed.

Lemma TypCast_open_fix : forall D E L A1 B1 A2 B2 c1 c2,
  (forall cy, cy \notin L ->
     TypCast D (cons (cy, (t_arrow A1 B1, t_arrow A2 B2)) E) A1 A2
       (open_castop_wrt_castop c1 (c_var_f cy))) ->
  (forall cy, cy \notin L ->
     TypCast D (cons (cy, (t_arrow A1 B1, t_arrow A2 B2)) E) B1 B2
       (open_castop_wrt_castop c2 (c_var_f cy))) ->
  TypCast D E (t_arrow A1 B1) (t_arrow A2 B2)
    (open_castop_wrt_castop (c_arrow c1 c2) (c_fixc (c_arrow c1 c2))).
Proof.
  intros D E L A1 B1 A2 B2 c1 c2 Q1 Q2.
  pose proof (TCast_fix L D E A1 B1 A2 B2 c1 c2 Q1 Q2) as Hfix.
  simpl.
  apply (TCast_arrow D E A1 B1 A2 B2
           (open_castop_wrt_castop c1 (c_fixc (c_arrow c1 c2)))
           (open_castop_wrt_castop c2 (c_fixc (c_arrow c1 c2)))).
  - set (Lz := L \u castfv_castop c1).
    pick fresh cy for Lz.
    assert (HcyL : cy \notin L) by fsetdec.
    assert (Hfresh : cy \notin castfv_castop c1) by fsetdec.
    rewrite <- (castsubst_open_same c1 (c_fixc (c_arrow c1 c2)) cy Hfresh).
    exact (TypCast_subst_perm D (cons (cy, (t_arrow A1 B1, t_arrow A2 B2)) E)
             A1 A2 (open_castop_wrt_castop c1 (c_var_f cy))
             (Q1 cy HcyL) E cy (t_arrow A1 B1) (t_arrow A2 B2)
             (c_fixc (c_arrow c1 c2)) Hfix (@Permutation_refl _ _)).
  - set (Lz := L \u castfv_castop c2).
    pick fresh cy for Lz.
    assert (HcyL : cy \notin L) by fsetdec.
    assert (Hfresh : cy \notin castfv_castop c2) by fsetdec.
    rewrite <- (castsubst_open_same c2 (c_fixc (c_arrow c1 c2)) cy Hfresh).
    exact (TypCast_subst_perm D (cons (cy, (t_arrow A1 B1, t_arrow A2 B2)) E)
             B1 B2 (open_castop_wrt_castop c2 (c_var_f cy))
             (Q2 cy HcyL) E cy (t_arrow A1 B1) (t_arrow A2 B2)
             (c_fixc (c_arrow c1 c2)) Hfix (@Permutation_refl _ _)).
Qed.

(* ------------------------------------------------------------------ *)
(* Well-formed term contexts and permutation                          *)
(* ------------------------------------------------------------------ *)

Lemma WFTmE_uniq : forall G, WFTmE G -> uniq G.
Proof.
  intros G H. induction H as [|G x A HG IH HA Hfresh].
  - constructor.
  - apply uniq_cons_iff. split; assumption.
Qed.

Lemma WFTmE_types : forall G, WFTmE G ->
  forall x A, binds x A G -> WFT nil A.
Proof.
  intros G H. induction H as [|G x A HG IH HA Hfresh]; intros y B Hy.
  - inversion Hy.
  - simpl in Hy. destruct Hy as [Heq|Hy].
    + injection Heq as -> ->. assumption.
    + apply (IH y B Hy).
Qed.

Lemma WFTmE_intro : forall G,
  uniq G -> (forall x A, binds x A G -> WFT nil A) -> WFTmE G.
Proof.
  induction G as [|[x A] G IH]; intros Hu Htypes.
  - constructor.
  - apply WFTmE_cons.
    + apply IH.
      * exact (uniq_cons_1 typ x A G Hu).
      * intros y B Hy. apply (Htypes y B). simpl. right. assumption.
    + apply (Htypes x A). simpl. left. reflexivity.
    + exact (uniq_cons_2 typ x A G Hu).
Qed.

Lemma WFTmE_perm : forall G G',
  Permutation G G' -> WFTmE G -> WFTmE G'.
Proof.
  intros G G' Hp HG.
  apply WFTmE_intro.
  - apply (uniq_perm _ _ _ Hp (WFTmE_uniq G HG)).
  - intros x A Hx.
    apply (WFTmE_types G HG x A).
    apply (Permutation_in (x,A) (Permutation_sym Hp) Hx).
Qed.

Lemma WFTmE_prefix : forall G F, WFTmE (G ++ F) -> WFTmE G.
Proof.
  intros G F H.
  apply WFTmE_intro.
  - apply (uniq_app_1 typ G F (WFTmE_uniq (G++F) H)).
  - intros x A Hx.
    apply (WFTmE_types (G++F) H x A).
    apply in_app_iff. left. assumption.
Qed.

Lemma open_exp_degree_id : forall e d,
  degree_exp_wrt_exp d e ->
  forall k v, open_exp_wrt_exp_rec (d + k) v e = e.
Proof.
  intros e. induction e as [nb|y|i|A b IHb|a IHa b IHb|c b IHb];
    intros d Hd k v; simpl in *.
  - inversion Hd as [|m Hm| | | |]; subst.
    destruct (lt_eq_lt_dec nb (d + k)) as [[Hlt|Heq]|Hgt]; simpl.
    + reflexivity.
    + subst nb. exfalso. lia.
    + exfalso. lia.
  - reflexivity.
  - reflexivity.
  - inversion Hd as [| | |nn0 A0 e0 H1| |]; subst.
    replace (S (d + k)) with (S d + k) by lia.
    rewrite (IHb (S d) H1 k v). reflexivity.
  - inversion Hd as [| | | |nn0 e1 e2 H1 H2|]; subst.
    rewrite (IHa d H1 k v), (IHb d H2 k v). reflexivity.
  - inversion Hd as [| | | | |nn0 c0 e0 H1]; subst.
    rewrite (IHb d H1 k v). reflexivity.
Qed.

Lemma open_exp_lc_id : forall e,
  lc_exp e -> forall k v, open_exp_wrt_exp_rec k v e = e.
Proof.
  intros e Hlc k v.
  destruct ((proj1 (lc_exp_degree_annot e)) Hlc) as [Hd _].
  exact (open_exp_degree_id e 0 Hd k v).
Qed.

Lemma if_eq_var_self_exp : forall (a b:exp) (x:atom),
  (if eq_var x x then a else b) = a.
Proof. intros. apply if_eq_var_self. Qed.

Lemma subst_exp_var_self : forall v (x:atom),
  subst_exp v x (e_var_f x) = v.
Proof. intros. simpl. apply if_eq_var_self. Qed.

Lemma subst_exp_var_other : forall v (x y:atom),
  y <> x -> subst_exp v x (e_var_f y) = e_var_f y.
Proof. intros. simpl. apply if_eq_var_neq. assumption. Qed.

Lemma subst_open_exp_rec : forall k body v x y,
  lc_exp v -> y <> x ->
  subst_exp v x (open_exp_wrt_exp_rec k (e_var_f y) body) =
  open_exp_wrt_exp_rec k (e_var_f y) (subst_exp v x body).
Proof.
  intros k body. revert k.
  induction body as [nb|z|i|A b IHb|a IHa b IHb|c b IHb];
    intros k v x y Hlc Hne; simpl in *.
  - destruct (lt_eq_lt_dec nb k) as [[Hlt|Heq]|Hgt]; simpl.
    + reflexivity.
    + subst nb. destruct (eq_var y x) as [Heq|Hne2].
      * exfalso. auto.
      * reflexivity.
    + reflexivity.
  - destruct (eq_var z x) as [Heq|Hne2].
    + subst z. simpl. symmetry. apply open_exp_lc_id. assumption.
    + simpl. reflexivity.
  - reflexivity.
  - rewrite IHb; auto.
  - rewrite IHa, IHb; auto.
  - rewrite IHb; auto.
Qed.

Lemma subst_open_exp : forall body v x y,
  lc_exp v -> y <> x ->
  subst_exp v x (open_exp_wrt_exp body (e_var_f y)) =
  open_exp_wrt_exp (subst_exp v x body) (e_var_f y).
Proof. intros. unfold open_exp_wrt_exp. apply subst_open_exp_rec; auto. Qed.


Lemma WFTmE_tail : forall (x:atom) (A:typ) (G:ctx),
  WFTmE (cons (x,A) G) -> WFTmE G.
Proof.
  intros x A G H.
  inversion H as [|G0 x0 A0 H1 H2 H3]; subst. assumption.
Qed.

Lemma CE_WFTmE : forall G e A e',
  EquiTypingC G e A e' -> WFTmE G.
Proof.
  intros G e A e' H.
  induction H as [G1 i Hwf
                 |G1 y A1 Hwf Hbinds
                 |L G1 A1 body A2 body' Hbody IHbody
                 |G1 a b A2 a' b' A0 Ha IHa Hb IHb
                 |G1 a B0 c a' A0 Ha IHa Hcast].
  - assumption.
  - assumption.
  - pick fresh z for L.
    apply (WFTmE_tail z A1 G1).
    apply IHbody. assumption.
  - apply IHa.
  - apply IHa.
Qed.

Lemma CE_perm : forall G G' e A e',
  Permutation G G' -> EquiTypingC G e A e' -> EquiTypingC G' e A e'.
Proof.
  intros G G' e A e' Hp H. revert G' Hp.
  induction H as [G1 i Hwf
                 |G1 y A1 Hwf Hbinds
                 |L G1 A1 body A2 body' Hbody IHbody
                 |G1 a b A2 a' b' A0 Ha IHa Hb IHb
                 |G1 a B0 c a' A0 Ha IHa Hcast];
    intros G' Hp.
  - apply ECTyping_int. apply (WFTmE_perm G1 G' Hp Hwf).
  - apply ECTyping_var.
    + apply (WFTmE_perm G1 G' Hp Hwf).
    + apply (Permutation_in (y,A1) Hp Hbinds).
  - apply (ECTyping_abs L G' A1 body A2 body').
    intros x Hx.
    apply (IHbody x Hx).
    apply perm_skip. assumption.
  - apply (ECTyping_app G' a b A2 a' b' A0).
    + apply (IHa G' Hp).
    + apply (IHb G' Hp).
  - apply (ECTyping_eq G' a B0 c a' A0).
    + apply (IHa G' Hp).
    + assumption.
Qed.

Lemma CE_weak_wf : forall G y C e A e',
  WFTmE (cons (y,C) G) ->
  EquiTypingC G e A e' ->
  EquiTypingC (cons (y,C) G) e A e'.
Proof.
  intros G y C e A e' Hwf H. revert y C Hwf.
  induction H as [G1 i Hwf0
                 |G1 z A1 Hwf0 Hbinds
                 |L G1 A1 body A2 body' Hbody IHbody
                 |G1 a b A2 a' b' A0 Ha IHa Hb IHb
                 |G1 a B0 c a' A0 Ha IHa Hcast];
    intros y C Hwf.
  - apply ECTyping_int. assumption.
  - apply ECTyping_var.
    + assumption.
    + simpl. right. assumption.
  - (* abs *)
    apply (ECTyping_abs (L \u {{y}} \u dom G1) (cons (y,C) G1) A1
                        body A2 body').
    intros z Hz.
    assert (HzL : z \notin L) by fsetdec.
    assert (Hzy : z <> y) by (intro Heq; subst; fsetdec).
    assert (Hzdom : z \notin dom G1) by fsetdec.
    assert (HA1 : WFT nil A1).
    { apply (WFTmE_types ((z,A1)::G1)
              (CE_WFTmE ((z,A1)::G1) (open_exp_wrt_exp body (e_var_f z))
                        A2 (open_exp_wrt_exp body' (e_var_f z)) (Hbody z HzL))
              z A1). simpl. left. reflexivity. }
    assert (Huniqy : uniq ((y,C)::G1)) by exact (WFTmE_uniq _ Hwf).
    assert (Huniqz : uniq ((z,A1)::G1)) by
      exact (WFTmE_uniq _ (CE_WFTmE ((z,A1)::G1)
              (open_exp_wrt_exp body (e_var_f z)) A2
              (open_exp_wrt_exp body' (e_var_f z)) (Hbody z HzL))).
    assert (HynG1 : y \notin dom G1) by
      exact (uniq_cons_2 typ y C G1 Huniqy).
    assert (Hwfz : WFTmE ((y,C)::(z,A1)::G1)).
    { apply WFTmE_intro.
      - apply uniq_cons_iff. split.
        + exact Huniqz.
        + intro Hbad. simpl in Hbad. rewrite add_iff in Hbad.
          destruct Hbad as [Heq|Hin].
          * exact (Hzy Heq).
          * exact (HynG1 Hin).
      - intros a0 B0 Ha0. simpl in Ha0.
        destruct Ha0 as [Heq|[Heq|Hin]].
        + injection Heq as Ha HB. subst a0. subst B0.
          apply (WFTmE_types ((y,C)::G1) Hwf y C).
          simpl. left. reflexivity.
        + injection Heq as Ha HB. subst a0. subst B0. exact HA1.
        + apply (WFTmE_types G1 (WFTmE_tail y C G1 Hwf) a0 B0). assumption. }
    apply (CE_perm ((y,C)::(z,A1)::G1) ((z,A1)::(y,C)::G1)).
    * apply perm_swap.
    * apply (IHbody z HzL y C Hwfz).
  - apply (ECTyping_app (cons (y,C) G1) a b A2 a' b' A0).
    + apply (IHa y C Hwf).
    + apply (IHb y C Hwf).
  - apply (ECTyping_eq (cons (y,C) G1) a B0 c a' A0).
    + apply (IHa y C Hwf).
    + assumption.
Qed.
Lemma CE_subst_end : forall G e A e',
  EquiTypingC G e A e' ->
  forall G0 x B v v',
    EquiTypingC G0 v B v' ->
    lc_exp v -> lc_exp v' ->
    Permutation G (G0 ++ [(x,B)]) ->
    EquiTypingC G0 (subst_exp v x e) A (subst_exp v' x e').
Proof.
  intros G e A e' H.
  induction H as [G1 i Hwf
                 |G1 y A1 Hwf Hbinds
                 |L G1 A1 body A2 body' Hbody IHbody
                 |G1 a b A2 a' b' A0 Ha IHa Hb IHb
                 |G1 a B0 c a' A0 Ha IHa Hcast];
    intros G0 x B v v' Hv Hlc Hlc' Hperm.
  - (* int *) apply ECTyping_int.
    apply (WFTmE_prefix G0 [(x,B)]).
    apply (WFTmE_perm G1 (G0 ++ [(x,B)]) Hperm).
    assumption.
  - (* var *)
    assert (Hin : In (y, A1) (G0 ++ [(x,B)])).
    { apply (Permutation_in (y,A1) Hperm). assumption. }
    assert (Hwf0 : WFTmE G0).
    { apply (WFTmE_prefix G0 [(x,B)]).
      apply (WFTmE_perm G1 (G0 ++ [(x,B)]) Hperm).
      assumption. }
    assert (Huniq : uniq (G0 ++ [(x,B)])).
    { apply (WFTmE_uniq (G0 ++ [(x,B)])).
      apply (WFTmE_perm G1 (G0 ++ [(x,B)]) Hperm).
      assumption. }
    destruct (eq_var y x) as [Heq|Hne].
    + (* y = x *)
      subst y.
      assert (HinB : In (x, B) (G0 ++ [(x,B)])).
      { apply in_app_iff. right. simpl. auto. }
      pose proof (binds_unique _ _ _ _ _ Hin HinB Huniq) as HAB.
      subst A1.
      rewrite subst_exp_var_self, subst_exp_var_self. exact Hv.
    + (* y <> x *)
      assert (HinG0 : In (y, A1) G0).
      { apply in_app_iff in Hin. destruct Hin as [HG|HS].
        + assumption.
        + simpl in HS. destruct HS as [Heq|[]].
          injection Heq as Hy _. exfalso. auto. }
      rewrite (subst_exp_var_other v x y Hne), (subst_exp_var_other v' x y Hne).
      apply ECTyping_var.
      * exact Hwf0.
      * exact HinG0.
  - (* abs *)
    apply (ECTyping_abs (L \u {{x}} \u termfv_exp v \u termfv_exp v')
                       G0 A1 (subst_exp v x body) A2 (subst_exp v' x body')).
    intros y Hy.
    assert (HyL : y \notin L) by fsetdec.
    assert (Hyx : y <> x) by (intro Heq; subst; fsetdec).
    assert (Hperm' : Permutation ((y, A1) :: G1)
                                    (((y, A1) :: G0) ++ [(x,B)])).
    { replace (((y, A1) :: G0) ++ [(x,B)])
        with ((y, A1) :: (G0 ++ [(x,B)])) by reflexivity.
      apply perm_skip. assumption. }
    rewrite <- (subst_open_exp body v x y Hlc Hyx).
    rewrite <- (subst_open_exp body' v' x y Hlc' Hyx).
    assert (Hwfcons : WFTmE (cons (y,A1) G0)).
    { apply (WFTmE_prefix ((y,A1) :: G0) [(x,B)]).
      apply (WFTmE_perm ((y,A1) :: G1) (((y,A1) :: G0) ++ [(x,B)]) Hperm').
      exact (CE_WFTmE ((y,A1) :: G1)
                       (open_exp_wrt_exp body (e_var_f y)) A2
                       (open_exp_wrt_exp body' (e_var_f y)) (Hbody y HyL)). }
    assert (Hvw : EquiTypingC (cons (y,A1) G0) v B v').
    { apply (CE_weak_wf G0 y A1 v B v' Hwfcons Hv). }
    apply (IHbody y HyL (cons (y,A1) G0) x B v v' Hvw Hlc Hlc' Hperm').
  - (* app *)
    simpl. apply (ECTyping_app G0 (subst_exp v x a) (subst_exp v x b) A2
                               (subst_exp v' x a') (subst_exp v' x b') A0).
    + apply (IHa G0 x B v v' Hv Hlc Hlc' Hperm).
    + apply (IHb G0 x B v v' Hv Hlc Hlc' Hperm).
  - (* eq *)
    simpl. apply (ECTyping_eq G0 (subst_exp v x a) B0 c (subst_exp v' x a') A0).
    + apply (IHa G0 x B v v' Hv Hlc Hlc' Hperm).
    + assumption.
Qed.


Lemma CE_lc_both : forall G e A e',
  EquiTypingC G e A e' -> lc_exp e /\ lc_exp e'.
Proof.
  intros G e A e' H.
  induction H as [G1 i Hwf
                 |G1 y A1 Hwf Hbinds
                 |L G1 A1 body A2 body' Hbody IHbody
                 |G1 a b A2 a' b' A0 Ha IHa Hb IHb
                 |G1 a B0 c a' A0 Ha IHa Hcast].
  - split; constructor.
  - split; constructor.
  - (* abs *)
    assert (HA1 : lc_typ A1).
    { pick fresh z for L.
      assert (HzL : z \notin L) by assumption.
      apply (WFT_lc_typ nil A1).
      apply (WFTmE_types ((z,A1)::G1)
              (CE_WFTmE ((z,A1)::G1) (open_exp_wrt_exp body (e_var_f z)) A2
                        (open_exp_wrt_exp body' (e_var_f z)) (Hbody z HzL))
              z A1). simpl. left. reflexivity. }
    split.
    + constructor; auto. intros x.
      pick fresh z for L.
      assert (HzL : z \notin L) by assumption.
      assert (Hlz : lc_exp (open_exp_wrt_exp body (e_var_f z))).
      { apply (proj1 (IHbody z HzL)). }
      apply (lc_open_indep body z x). assumption.
    + constructor; auto. intros x.
      pick fresh z for L.
      assert (HzL : z \notin L) by assumption.
      assert (Hlz : lc_exp (open_exp_wrt_exp body' (e_var_f z))).
      { apply (proj2 (IHbody z HzL)). }
      apply (lc_open_indep body' z x). assumption.
  - (* app *)
    destruct IHa as [H1 H1']. destruct IHb as [H2 H2'].
    split; constructor; assumption.
  - (* eq *)
    destruct IHa as [H1 H1']. split.
    + assumption.
    + apply lc_e_cast.
      * apply (TypCast_lc nil nil A0 B0 c Hcast).
      * assumption.
Qed.

Inductive cast_free : exp -> Prop :=
 | cf_var_b : forall n, cast_free (e_var_b n)
 | cf_var_f : forall x, cast_free (e_var_f x)
 | cf_lit : forall i, cast_free (e_lit i)
 | cf_abs : forall A e, cast_free e -> cast_free (e_abs A e)
 | cf_app : forall a b, cast_free a -> cast_free b -> cast_free (e_app a b).

Lemma cast_free_open_rec_inv : forall k e x,
  cast_free (open_exp_wrt_exp_rec k (e_var_f x) e) -> cast_free e.
Proof.
  intros k e; revert k.
  induction e as [nb|y|i|A b IHb|a IHa b IHb|c b IHb]; intros k x H; simpl in H.
  - destruct (lt_eq_lt_dec nb k) as [[?|?]|?]; simpl in H; exact (cf_var_b nb).
  - exact (cf_var_f y).
  - exact (cf_lit i).
  - inversion H as [| | |A0 b0 Hb|]; subst. constructor. apply (IHb (S k) x). assumption.
  - inversion H as [| | | |a0 b0 H1 H2]; subst. constructor.
    + apply (IHa k x). assumption.
    + apply (IHb k x). assumption.
  - inversion H.
Qed.

Lemma CE_cast_free : forall G e A e',
  EquiTypingC G e A e' -> cast_free e.
Proof.
  intros G e A e' H.
  induction H as [G1 i Hwf
                 |G1 y A1 Hwf Hbinds
                 |L G1 A1 body A2 body' Hbody IHbody
                 |G1 a b A2 a' b' A0 Ha IHa Hb IHb
                 |G1 a B0 c a' A0 Ha IHa Hcast].
  - apply cf_lit.
  - apply cf_var_f.
  - apply cf_abs. pick fresh z for L.
    assert (HzL : z \notin L) by assumption.
    apply (cast_free_open_rec_inv 0 body z).
    apply (IHbody z HzL).
  - apply cf_app; [apply IHa|apply IHb].
  - apply IHa.
Qed.

Lemma CE_mu_value : forall G e A v,
  EquiTypingC G e (t_mu A) v -> value v ->
  exists v1, value v1 /\
    EquiTypingC G e (unfold_mu A) v1 /\
    v = e_cast (c_fold (t_mu A)) v1.
Proof.
  intros G e A v H Hval.
  dependent destruction H.
  - inversion Hval.
  - inversion Hval.
  - inversion Hval as [| |AA bb Hlt Hvl|c1 c2 bb Hlc1 Hlc2 Hvl]; subst.
    + inversion H0 as [| | |D0 E0 A0' Hwf Hu| | |]; subst.
      exists e'. split; [assumption|split; [assumption|reflexivity]].
    + inversion H0 as [|D0 E0 A1' B1' A2' B2' cc1 cc2 H1 H2| | | | |]; subst.
Qed.





Lemma lc_castop_arrow_inv : forall a b,
  lc_castop (c_arrow a b) -> lc_castop a /\ lc_castop b.
Proof. intros a b H. inversion H as [| | | |a0 b0 H1 H2| |]; subst. auto. Qed.

Lemma CE_cast_value : forall c A0 B,
  TypCast nil nil A0 B c ->
  forall G e v0, EquiTypingC G e A0 v0 -> value v0 ->
  exists w, value w /\
    EquiTypingC G e B w /\
    (e_cast c v0 ==>* w).
Proof.
  intros c. induction c as [nb|cx| |A|A|a IHa b IHb|a IHa b IHb|c0 IHc];
    intros A0 B Hcast G e v0 HCE Hval.
  - (* var_b *) inversion Hcast.
  - (* var_f *)
    destruct (TCast_var_inv nil nil A0 B cx Hcast) as [_ [_ [_ Hin]]].
    inversion Hin.
  - (* id *)
    assert (HAB : A0 = B) by (apply (TCast_id_inv nil nil A0 B Hcast)).
    subst B.
    exists v0. split; [assumption|split; [assumption|]].
    apply rt_step. apply Red_castid. assumption.
  - (* unfold *)
    inversion Hcast as [| |D E A' Hwf Hu| | | |]; subst.
    destruct (CE_mu_value G e A' v0 HCE Hval) as [v1 [Hv1 [HCE1 Heq]]].
    subst v0.
    exists v1. split; [assumption|split; [assumption|]].
    apply rt_step. apply Red_castelim.
    + apply (WFT_lc_typ nil (t_mu A')). assumption.
    + assumption.
  - (* fold *)
    inversion Hcast as [| | |D E A' Hwf Hu| | |]; subst.
    exists (e_cast (c_fold (t_mu A')) v0). split; [|split].
    + apply V_fold.
      * apply (WFT_lc_typ nil (t_mu A')). assumption.
      * assumption.
    + apply (ECTyping_eq G e (t_mu A') (c_fold (t_mu A')) v0 (unfold_mu A')).
      * assumption.
      * exact (TCast_fold nil nil A' Hwf Hu).
    + apply rt_refl.
  - (* arrow *)
    destruct (TCast_arrow_inv nil nil A0 B a b Hcast) as
        [A1 [B1 [A2 [B2 [HA0 [HB [Hca Hcb]]]]]]].
    subst A0. subst B.
    exists (e_cast (c_arrow a b) v0). split; [|split].
    + apply V_arrow.
      * exact (TypCast_lc _ _ _ _ _ Hca).
      * exact (TypCast_lc _ _ _ _ _ Hcb).
      * assumption.
    + apply (ECTyping_eq G e (t_arrow A2 B2) (c_arrow a b) v0 (t_arrow A1 B1)).
      * assumption.
      * assumption.
    + apply rt_refl.
  - (* seq *)
    destruct (TCast_seq_inv nil nil A0 B a b Hcast) as [C [Hca Hcb]].
    destruct (IHa A0 C Hca G e v0 HCE Hval) as [w1 [Hv1 [HCE1 Hstep1]]].
    destruct (IHb C B Hcb G e w1 HCE1 Hv1) as [w2 [Hv2 [HCE2 Hstep2]]].
    exists w2. split; [assumption|split; [assumption|]].
    apply rt_trans with (y := e_cast b (e_cast a v0)).
    + apply rt_step. apply Red_cast_seq.
      * exact (TypCast_lc _ _ _ _ _ Hcb).
      * exact (TypCast_lc _ _ _ _ _ Hca).
      * assumption.
    + apply rt_trans with (y := e_cast b w1).
      * apply cast_star.
        -- exact (TypCast_lc _ _ _ _ _ Hcb).
        -- assumption.
      * assumption.
  - (* fixc *)
    destruct (TCast_fix_inv nil nil A0 B c0 Hcast) as
        [L [A1 [B1 [A2 [B2 [c1 [c2 [Hc [HA0 [HB [Q1 Q2]]]]]]]]]]].
    subst A0. subst B. subst c0.
    pose proof (TCast_fix L nil nil A1 B1 A2 B2 c1 c2 Q1 Q2) as Hfix.
    pose proof (TypCast_open_fix nil nil L A1 B1 A2 B2 c1 c2 Q1 Q2) as Hopen.
    simpl in Hopen.
    destruct (lc_castop_arrow_inv _ _ (TypCast_lc _ _ _ _ _ Hopen)) as [Hlca Hlcb].
    exists (e_cast (open_castop_wrt_castop (c_arrow c1 c2)
                    (c_fixc (c_arrow c1 c2))) v0).
    split; [|split].
    + apply V_arrow; [exact Hlca|exact Hlcb|assumption].
    + apply (ECTyping_eq G e (t_arrow A2 B2)
             (open_castop_wrt_castop (c_arrow c1 c2) (c_fixc (c_arrow c1 c2)))
             v0 (t_arrow A1 B1)).
      * assumption.
      * exact Hopen.
    + apply rt_step. apply Red_castfix.
      * exact (TypCast_lc _ _ _ _ _ Hfix).
      * assumption.
Qed.


Lemma CE_value_term : forall G e A e',
  EquiTypingC G e A e' -> value e ->
  exists v', value v' /\ EquiTypingC G e A v' /\ (e' ==>* v').
Proof.
  intros G e A e' H.
  induction H as [G1 i Hwf
                 |G1 y A1 Hwf Hbinds
                 |L G1 A1 body A2 body' Hbody IHbody
                 |G1 a b A2 a' b' A0 Ha IHa Hb IHb
                 |G1 a B0 c a' A0 Ha IHa Hcast]; intro Hval.
  - (* int *)
    exists (e_lit i). split; [apply V_lit|split; [apply ECTyping_int; assumption|apply rt_refl]].
  - (* var *) inversion Hval.
  - (* abs *)
    inversion Hval as [|A1' b' Hlt Hlc| |]; subst.
    assert (Hlc' : lc_exp (e_abs A1 body')).
    { apply (CE_lc_fwd G1 (e_abs A1 body) (t_arrow A1 A2) (e_abs A1 body')).
      - apply (ECTyping_abs L G1 A1 body A2 body' Hbody).
      - assumption. }
    exists (e_abs A1 body'). split; [apply V_abs; assumption|split].
    + apply (ECTyping_abs L G1 A1 body A2 body' Hbody).
    + apply rt_refl.
  - (* app *) inversion Hval.
  - (* eq *)
    destruct (IHa Hval) as [v0 [Hv0 [HCE0 Hstep0]]].
    destruct (CE_cast_value c A0 B0 Hcast G1 a v0 HCE0 Hv0) as [w [Hw [HCEw Hstepw]]].
    exists w. split; [assumption|split; [assumption|]].
    apply rt_trans with (y := e_cast c v0).
    + apply cast_star.
      * exact (TypCast_lc nil nil A0 B0 c Hcast).
      * assumption.
    + assumption.
Qed.

Lemma perm_cons_app_last : forall (A:Type) (p:A) (G:list A),
  Permutation (p :: G) (G ++ [p]).
Proof.
  intros A p G. induction G as [|a G IH].
  - simpl. apply Permutation_refl.
  - simpl. eapply perm_trans.
    + apply perm_swap.
    + apply perm_skip. exact IH.
Qed.

Lemma value_lc : forall v, value v -> lc_exp v.
Proof.
  intros v Hv. induction Hv.
  - constructor.
  - assumption.
  - apply lc_e_cast.
    + apply lc_c_fold. assumption.
    + assumption.
  - apply lc_e_cast.
    + apply lc_c_arrow; assumption.
    + assumption.
Qed.

Lemma open_subst_self_gen : forall k body v x,
  x \notin termfv_exp body ->
  subst_exp v x (open_exp_wrt_exp_rec k (e_var_f x) body) =
  open_exp_wrt_exp_rec k v body.
Proof.
  intros k body. revert k.
  induction body as [nb|y|i|A b IHb|a IHa b IHb|c b IHb];
    intros k v x Hfresh.
  - simpl. destruct (lt_eq_lt_dec nb k) as [[Hlt|Heq]|Hgt]; simpl.
    + reflexivity.
    + subst nb. apply subst_exp_var_self.
    + reflexivity.
  - assert (Hyx : y <> x).
    { intro Heq. subst y. apply Hfresh. simpl. fsetdec. }
    simpl. apply (subst_exp_var_other v x y Hyx).
  - reflexivity.
  - simpl. rewrite (IHb (S k) v x Hfresh). reflexivity.
  - assert (Hfa : x \notin termfv_exp a) by
      exact (notin_union_1 x (termfv_exp a) (termfv_exp b) Hfresh).
    assert (Hfb : x \notin termfv_exp b) by
      exact (notin_union_2 x (termfv_exp a) (termfv_exp b) Hfresh).
    simpl. rewrite (IHa k v x Hfa), (IHb k v x Hfb). reflexivity.
  - simpl. rewrite (IHb k v x Hfresh). reflexivity.
Qed.

Lemma open_subst_self : forall body v x,
  x \notin termfv_exp body ->
  subst_exp v x (open_exp_wrt_exp body (e_var_f x)) =
  open_exp_wrt_exp body v.
Proof. intros. unfold open_exp_wrt_exp. apply open_subst_self_gen. assumption. Qed.

Lemma CE_beta_gen : forall G e T f,
  EquiTypingC G e T f -> value f ->
  forall A1 A2 body X, T = t_arrow X A2 -> e = e_abs A1 body ->
  forall arg arg', value arg -> EquiTypingC G arg X arg' ->
  exists r, (e_app f arg' ==>* r) /\
    EquiTypingC G (open_exp_wrt_exp body arg) A2 r.
Proof.
  intros G e T f H.
  induction H as [G1 i Hwf
                 |G1 y A0 Hwf Hbinds
                 |L G1 B1 body0 B2 body' Hbody IHbody
                 |G1 a b A2' a' b' A0 Ha IHa Hb IHb
                 |G1 a B0 c a' A0 Ha IHa Hcast];
    intros Hval A1 A2 body X HT He arg arg' Hargval Harg.
  - (* int *) discriminate HT.
  - (* var *) discriminate He.
  - (* abs *)
    injection HT as HB1 HB2. injection He as HA1 Hbodyeq. subst.
    destruct (CE_value_term G1 arg A1 arg' Harg Hargval) as [av [Hav [HCEav Hstepav]]].
    inversion Hval as [|A1' b' Hlt Hlc| |]; subst.
    exists (open_exp_wrt_exp body' av). split.
    + apply rt_trans with (y := e_app (e_abs A1 body') av).
      * apply (app_r_star (e_abs A1 body') arg' av).
        -- apply V_abs; assumption.
        -- assumption.
      * apply rt_step. apply Red_beta.
        -- assumption.
        -- assumption.
        -- assumption.
    + set (Lz := L \u termfv_exp body \u termfv_exp body').
      pick fresh x for Lz.
      assert (HxL : x \notin L) by fsetdec.
      assert (Hxb : x \notin termfv_exp body) by fsetdec.
      assert (Hxb' : x \notin termfv_exp body') by fsetdec.
      pose proof (Hbody x HxL) as Hb.
      rewrite <- (open_subst_self body arg x Hxb).
      rewrite <- (open_subst_self body' av x Hxb').
      apply (CE_subst_end (cons (x,A1) G1)
                          (open_exp_wrt_exp body (e_var_f x)) A2
                          (open_exp_wrt_exp body' (e_var_f x)) Hb
                          G1 x A1 arg av HCEav).
      * apply value_lc. exact Hargval.
      * apply value_lc. assumption.
      * apply perm_cons_app_last.
  - (* app *) discriminate He.
  - (* eq *)
    inversion Hval as [| |AA bb Hlt Hvl|c1 c2 bb Hlc1 Hlc2 Hvl].
    + (* fold impossible *)
      rewrite <- H in Hcast.
      destruct (TCast_fold_inv nil nil A0 _ AA Hcast) as [A' [HA [HA0 HB]]].
      assert (Hbad : t_mu A' = t_arrow X A2) by (rewrite <- HB; exact HT).
      discriminate Hbad.
    + (* arrow *)
      rewrite <- H in Hcast.
      destruct (TCast_arrow_inv nil nil A0 _ c1 c2 Hcast) as
          [X1 [Y1 [X2 [Y2 [HA0 [HB0 [Hc1 Hc2]]]]]]].
      subst A0.
      assert (HT' : t_arrow X2 Y2 = t_arrow X A2) by (rewrite <- HB0; exact HT).
      injection HT' as HX2 HY2. subst X2. subst Y2.
      (* Harg : CE G1 arg A1 arg' ; Hc1 : TypCast X1 A1 c1 *)
      assert (Hrev : TypCast nil nil X X1 (rev_cast c1)).
      { exact (TypCast_rev nil nil X1 X c1 Hc1). }
      assert (HCC1 : EquiTypingC G1 arg X1 (e_cast (rev_cast c1) arg')).
      { apply (ECTyping_eq G1 arg X1 (rev_cast c1) arg' X).
        - assumption.
        - exact Hrev. }
      destruct (CE_value_term G1 arg X arg' Harg Hargval) as [av0 [Hav0 [HCEav0 Hstepav0]]].
      assert (HCC2 : EquiTypingC G1 arg X1 (e_cast (rev_cast c1) av0)).
      { apply (ECTyping_eq G1 arg X1 (rev_cast c1) av0 X).
        - exact HCEav0.
        - exact Hrev. }
      destruct (CE_value_term G1 arg X1 (e_cast (rev_cast c1) av0) HCC2 Hargval)
        as [av1 [Hav1 [HCEav1 Hstepav1]]].
      destruct (IHa Hvl A1 Y1 body X1 eq_refl He arg av1 Hargval HCEav1)
        as [r [Hrstep HrCE]].
      exists (e_cast c2 r). split.
      { apply rt_trans with (y := e_app (e_cast (c_arrow c1 c2) a') av0).
        { apply (app_r_star (e_cast (c_arrow c1 c2) a') arg' av0).
          - apply V_arrow; [exact Hlc1|exact Hlc2|exact Hvl].
          - exact Hstepav0. }
        { apply rt_trans with (y := e_cast c2 (e_app a' (e_cast (rev_cast c1) av0))).
          { apply rt_step. apply Red_cast_arr.
            - exact Hlc2.
            - exact Hlc1.
            - exact Hvl.
            - exact Hav0. }
          { apply rt_trans with (y := e_cast c2 (e_app a' av1)).
            { apply cast_star.
              - exact Hlc2.
              - apply (app_r_star a' (e_cast (rev_cast c1) av0) av1).
                + exact Hvl.
                + exact Hstepav1. }
            { apply cast_star.
              - exact Hlc2.
              - exact Hrstep. } } } }
      { apply (ECTyping_eq G1 (open_exp_wrt_exp body arg) A2 c2 r Y1).
        - exact HrCE.
        - exact Hc2. }
Qed.

Lemma CE_cast_inv : forall G e A c e',
  EquiTypingC G e A (e_cast c e') ->
  exists A0, EquiTypingC G e A0 e' /\ TypCast nil nil A0 A c.
Proof.
  intros G e A c e' H. dependent destruction H.
  exists A. auto.
Qed.

Lemma CE_beta : forall G A1 A2 body f arg arg',
  EquiTypingC G (e_abs A1 body) (t_arrow A1 A2) f -> value f ->
  EquiTypingC G arg A1 arg' -> value arg ->
  exists r, (e_app f arg' ==>* r) /\
    EquiTypingC G (open_exp_wrt_exp body arg) A2 r.
Proof.
  intros G A1 A2 body f arg arg' Hf Hvf Harg Hva.
  apply (CE_beta_gen G (e_abs A1 body) (t_arrow A1 A2) f Hf Hvf
                    A1 A2 body A1 eq_refl eq_refl arg arg' Hva Harg).
Qed.

Lemma sim_right : forall G e A e',
  EquiTypingC G e A e' ->
  forall e1', Reduction e' e1' ->
  exists e1, (e ==>* e1) /\ EquiTypingC G e1 A e1'.
Proof.
  intros G e A e' HCE.
  induction HCE as [G i Hwf
                  |G y A0 Hwf Hbinds
                  |L G A1 body A2 body' Hbody IHbody
                  |G a b A2 a' b' A0 Ha IHa Hb IHb
                  |G a B0 c a' A0 Ha IHa Hcast];
    intros e1' Hred.
  - (* int *) inversion Hred.
  - (* var *) inversion Hred.
  - (* abs *) inversion Hred.
  - (* app *)
    dependent destruction Hred.
    + (* red beta *)
      dependent destruction Ha.
      assert (Hvalb : value b) by (apply (CE_value_back G b A b'); assumption).
      assert (Hlcs : lc_exp (e_abs A e0)).
      { apply (proj1 (CE_lc_both G (e_abs A e0) (t_arrow A A2) (e_abs A e)
                (ECTyping_abs L G A e0 A2 e H))). }
      exists (open_exp_wrt_exp e0 b). split.
      * apply rt_step. apply Red_beta.
        -- assumption.
        -- exact Hlcs.
        -- exact Hvalb.
      * set (Lz := L \u termfv_exp e0 \u termfv_exp e).
        pick fresh x for Lz.
        assert (HxL : x \notin L) by fsetdec.
        assert (Hxb : x \notin termfv_exp e0) by fsetdec.
        assert (Hxb' : x \notin termfv_exp e) by fsetdec.
        pose proof (H x HxL) as Hbod.
        rewrite <- (open_subst_self e0 b x Hxb).
        rewrite <- (open_subst_self e b' x Hxb').
        apply (CE_subst_end (cons (x,A) G) (open_exp_wrt_exp e0 (e_var_f x)) A2
                            (open_exp_wrt_exp e (e_var_f x)) Hbod
                            G x A b b' Hb).
        -- apply value_lc. exact Hvalb.
        -- apply value_lc. assumption.
        -- apply perm_cons_app_last.
    + (* red appl *)
      destruct (IHa e1' Hred) as [a2 [Hastep HCEa2]].
      assert (Hlcb : lc_exp b)
        by (apply (CE_lc_back G b A0 b'); assumption).
      exists (e_app a2 b). split.
      * apply (app_l_star a a2 b); assumption.
      * apply (ECTyping_app G a2 b A2 e1' b' A0); assumption.
    + (* red appr *)
      destruct (IHb e2' Hred) as [b2 [Hbstep HCEb2]].
      assert (Hvala : value a)
        by (apply (CE_value_back G a (t_arrow A0 A2) a'); assumption).
      exists (e_app a b2). split.
      * apply (app_r_star a b b2); assumption.
      * apply (ECTyping_app G a b2 A2 a' e2' A0); assumption.
    + (* red cast arr *)
      destruct (CE_cast_inv G a (t_arrow A0 A2) (c_arrow c1 c2) e1 Ha) as [Apr [Ha0 Hcasta]].
      destruct (TCast_arrow_inv nil nil Apr (t_arrow A0 A2) c1 c2 Hcasta)
        as [X1 [Y1 [X2 [Y2 [HApr [HB [Hc1 Hc2]]]]]]].
      subst Apr.
      injection HB as HX2 HY2. subst X2. subst Y2.
      assert (Hrev : TypCast nil nil A0 X1 (rev_cast c1)).
      { exact (TypCast_rev nil nil X1 A0 c1 Hc1). }
      assert (Hargrev : EquiTypingC G b X1 (e_cast (rev_cast c1) b')).
      { apply (ECTyping_eq G b X1 (rev_cast c1) b' A0).
        - exact Hb.
        - exact Hrev. }
      assert (HCEapp : EquiTypingC G (e_app a b) Y1
                        (e_app e1 (e_cast (rev_cast c1) b'))).
      { apply (ECTyping_app G a b Y1 e1 (e_cast (rev_cast c1) b') X1).
        - exact Ha0.
        - exact Hargrev. }
      exists (e_app a b). split.
      * apply rt_refl.
      * apply (ECTyping_eq G (e_app a b) A2 c2
               (e_app e1 (e_cast (rev_cast c1) b')) Y1).
        -- exact HCEapp.
        -- exact Hc2.
  - (* eq *)
    dependent destruction Hred.
    + (* cast seq *)
      destruct (TCast_seq_inv nil nil A0 B0 c1 c2 Hcast) as [C [Hc1 Hc2]].
      exists a. split; [apply rt_refl|].
      apply (ECTyping_eq G a B0 c2 (e_cast c1 a') C).
      * apply (ECTyping_eq G a C c1 a' A0); assumption.
      * exact Hc2.
    + (* red cast : step inside *)
      destruct (IHa e' Hred) as [a2 [Hastep HCEa2]].
      exists a2. split; [assumption|].
      apply (ECTyping_eq G a2 B0 c e' A0); assumption.
    + (* cast elim *)
      destruct (TCast_unfold_inv nil nil A0 B0 A Hcast) as [A' [HA [HA0 HB]]].
      destruct (CE_cast_inv G a A0 (c_fold A) v Ha) as [Bmid [Ha0 Hcast2]].
      destruct (TCast_fold_inv nil nil Bmid A0 A Hcast2) as [A'' [HA2 [HBmid HA0']]].
      subst A. subst A0. subst B0. subst Bmid.
      exists a. split; [apply rt_refl|].
      injection HA2 as HAeq. subst A''. exact Ha0.
    + (* cast id *)
      assert (HAB : A0 = B0) by (apply (TCast_id_inv nil nil A0 B0 Hcast)).
      subst B0.
      exists a. split; [apply rt_refl|]. exact Ha.
    + (* cast fix *)
      destruct (TCast_fix_inv nil nil A0 B0 c0 Hcast) as
          [Lf [A1 [B1 [A2 [B2 [c1 [c2 [Hc [HA0 [HB [Q1 Q2]]]]]]]]]]].
      subst A0. subst B0. subst c0.
      pose proof (TypCast_open_fix nil nil Lf A1 B1 A2 B2 c1 c2 Q1 Q2) as Hopen.
      exists a. split; [apply rt_refl|].
      apply (ECTyping_eq G a (t_arrow A2 B2)
               (open_castop_wrt_castop (c_arrow c1 c2) (c_fixc (c_arrow c1 c2))) a'
               (t_arrow A1 B1)).
      * exact Ha.
      * exact Hopen.
Qed.


Lemma sim_left : forall G e A e',
  EquiTypingC G e A e' ->
  forall e1, Reduction e e1 ->
  exists e1', (e' ==>* e1') /\ EquiTypingC G e1 A e1'.
Proof.
  intros G e A e' HCE.
  induction HCE as [G i Hwf
                  |G y A0 Hwf Hbinds
                  |L G A1 body A2 body' Hbody IHbody
                  |G a b A2 a' b' A0 Ha IHa Hb IHb
                  |G a B0 c a' A0 Ha IHa Hcast];
    intros e1 Hred.
  - (* int *) inversion Hred.
  - (* var *) inversion Hred.
  - (* abs *) inversion Hred.
  - (* app *)
    pose proof (CE_cast_free G a (t_arrow A0 A2) a' Ha) as Hcf.
    dependent destruction Hred.
    + (* beta *)
      assert (Hvalb : value b) by assumption.
      assert (Hlcabs : lc_exp (e_abs A e)) by assumption.
      assert (Hlctyp : lc_typ A) by assumption.
      destruct (CE_value_term G (e_abs A e) (t_arrow A0 A2) a' Ha
                 (V_abs A e Hlctyp Hlcabs))
        as [fv [Hvf [HCEf Hstepf]]].
      destruct (CE_beta_gen G (e_abs A e) (t_arrow A0 A2) fv HCEf Hvf
                 A A2 e A0 eq_refl eq_refl b b' Hvalb Hb)
        as [r [Hrstep HrCE]].
      assert (Hlcb : lc_exp b').
      { exact (proj2 (CE_lc_both G b A0 b' Hb)). }
      exists r. split.
      * apply rt_trans with (y := e_app fv b').
        -- apply (app_l_star a' fv b'); assumption.
        -- exact Hrstep.
      * exact HrCE.
    + (* appl *)
      destruct (IHa e1' Hred) as [a2 [Hastep HCEa2]].
      assert (Hlcb : lc_exp b').
      { exact (proj2 (CE_lc_both G b A0 b' Hb)). }
      exists (e_app a2 b'). split.
      * apply (app_l_star a' a2 b'); assumption.
      * apply (ECTyping_app G e1' b A2 a2 b' A0); assumption.
    + (* appr *)
      destruct (IHb e2' Hred) as [b2 [Hbstep HCEb2]].
      destruct (CE_value_term G a (t_arrow A0 A2) a' Ha H)
        as [av [Hav [HCEav Hstepav]]].
      assert (Hlcb : lc_exp b').
      { exact (proj2 (CE_lc_both G b A0 b' Hb)). }
      exists (e_app av b2). split.
      * apply rt_trans with (y := e_app av b').
        -- apply (app_l_star a' av b'); assumption.
        -- apply (app_r_star av b' b2); assumption.
      * apply (ECTyping_app G a e2' A2 av b2 A0); assumption.
    + (* cast arr impossible *)
      inversion Hcf.
  - (* eq *)
    destruct (IHa e1 Hred) as [a2 [Hastep HCEa2]].
    exists (e_cast c a2). split.
    + apply cast_star.
      * exact (TypCast_lc nil nil A0 B0 c Hcast).
      * assumption.
    + apply (ECTyping_eq G e1 B0 c a2 A0).
      * exact HCEa2.
      * exact Hcast.
Qed.

Lemma sim_left_star : forall G a A a' b,
  (a ==>* b) ->
  EquiTypingC G a A a' ->
  exists b', (a' ==>* b') /\ EquiTypingC G b A b'.
Proof.
  intros G a A a' b Hstep HCE.
  apply clos_rt_rt1n in Hstep.
  revert a' HCE.
  induction Hstep; intros a' HCE.
  - exists a'. split; [apply rt_refl|assumption].
  - destruct (sim_left G _ A a' HCE _ H) as [m [Hm HCEm]].
    destruct (IHHstep m HCEm) as [b' [Hb' HCEb']].
    exists b'. split; [|assumption].
    apply rt_trans with (y := m); assumption.
Qed.

Lemma sim_right_star : forall G a A a' b',
  (a' ==>* b') ->
  EquiTypingC G a A a' ->
  exists b, (a ==>* b) /\ EquiTypingC G b A b'.
Proof.
  intros G a A a' b' Hstep HCE.
  apply clos_rt_rt1n in Hstep.
  revert a HCE.
  induction Hstep; intros a HCE.
  - exists a. split; [apply rt_refl|assumption].
  - destruct (sim_right G _ A x HCE _ H) as [m [Hm HCEm]].
    destruct (IHHstep m HCEm) as [b [Hb HCEb]].
    exists b. split; [|assumption].
    apply rt_trans with (y := m); assumption.
Qed.

Lemma terminate_fwd : forall G e A e',
  EquiTypingC G e A e' -> terminate e -> terminate e'.
Proof.
  intros G e A e' HCE [v [Hv Hstep]].
  destruct (sim_left_star G e A e' v Hstep HCE) as [v' [Hstep' HCE']].
  destruct (CE_value_term G v A v' HCE' Hv) as [vv [Hvv [HCEvv Hstepvv]]].
  exists vv. split; [assumption|].
  apply rt_trans with (y := v'); assumption.
Qed.

Lemma terminate_bwd : forall G e A e',
  EquiTypingC G e A e' -> terminate e' -> terminate e.
Proof.
  intros G e A e' HCE [v' [Hv' Hstep']].
  destruct (sim_right_star G e A e' v' Hstep' HCE) as [v [Hstep HCEv]].
  pose proof (CE_value_back G v A v' HCEv Hv') as Hv.
  exists v. split; assumption.
Qed.

Theorem behavior_equiv: forall e t e',
  EquiTypingC nil e t e' ->
  (terminate e <-> terminate e') /\
  (diverge e <-> diverge e').
Proof.
  intros e t e' HCE. split.
  - split.
    + intro H. apply (terminate_fwd nil e t e'); assumption.
    + intro H. apply (terminate_bwd nil e t e'); assumption.
  - unfold diverge. split.
    + intros H Hc. apply H. apply (terminate_bwd nil e t e'); assumption.
    + intros H Hc. apply H. apply (terminate_fwd nil e t e'); assumption.
Qed.
