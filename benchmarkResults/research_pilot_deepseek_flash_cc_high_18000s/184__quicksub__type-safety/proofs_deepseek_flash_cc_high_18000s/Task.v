Require Import Metalib.Metatheory.
Require Import Rules.
From Stdlib Require Import List Arith PeanoNat Bool.
Import ListNotations.

(* Left-to-right list associativity (stdlib app_assoc has the other orientation). *)
Lemma app_assoc_lr : forall (A:Type) (l1 l2 l3:list A),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof. intros A l1. induction l1 as [| a l1 IH]; intros l2 l3; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* ============================================================ *)
(* Mode duality for environments                                 *)
(* ============================================================ *)

Definition flip_binding (b : binding) : binding :=
  match b with
  | bind_sub im => bind_sub (flip_im im)
  | bind_typ T => bind_typ T
  end.

Definition flip_env (E : env) : env :=
  map (fun xb => (fst xb, flip_binding (snd xb))) E.

Lemma flip_im_invol : forall im, flip_im (flip_im im) = im.
Proof. intros [] ; reflexivity. Qed.

Lemma flip_env_cons : forall (x:atom) b E,
  flip_env (x ~ b ++ E) = x ~ flip_binding b ++ flip_env E.
Proof. intros. reflexivity. Qed.

Lemma dom_flip_env : forall E, dom (flip_env E) = dom E.
Proof.
  induction E as [| [x b] E IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma binds_flip_env : forall E x b,
  binds x b E -> binds x (flip_binding b) (flip_env E).
Proof.
  induction E as [| [y c] E IH]; intros x b Hb; simpl in *.
  - destruct Hb.
  - destruct Hb as [Heq|Hb].
    + injection Heq as -> ->. simpl. left. reflexivity.
    + right. apply IH. assumption.
Qed.

Lemma flip_env_invol : forall E, flip_env (flip_env E) = E.
Proof.
  induction E as [| [x b] E IH]; simpl.
  - reflexivity.
  - destruct b as [im|T]; simpl; [rewrite flip_im_invol |]; rewrite IH; reflexivity.
Qed.

Definition NoSubBind (E : env) : Prop :=
  forall (x:atom) (im:IsoMode), ~ binds x (bind_sub im) E.

Lemma flip_env_id : forall E, NoSubBind E -> flip_env E = E.
Proof.
  induction E as [| [x b] E IH]; intros H; simpl.
  - reflexivity.
  - destruct b as [im|T].
    + exfalso. apply (H x im). simpl. left. reflexivity.
    + simpl. rewrite IH; [reflexivity|].
      intros y i Hy. apply (H y i). simpl. right. assumption.
Qed.

Lemma NoSubBind_cons_typ : forall x T E,
  NoSubBind E -> NoSubBind (x ~ bind_typ T ++ E).
Proof.
  intros x T E H y i Hy. apply (H y i). simpl in Hy.
  destruct Hy as [Heq|Hy].
  - injection Heq as _ Hc. discriminate Hc.
  - assumption.
Qed.

Lemma NoSubBind_app : forall E1 E2,
  NoSubBind (E1 ++ E2) -> NoSubBind E2.
Proof.
  intros E1 E2 H y i Hy. apply (H y i). apply binds_app_3. assumption.
Qed.

Lemma binds_cons_typ_inv : forall (x y:atom) (T:typ) (E:env) b,
  binds x b (y ~ bind_typ T ++ E) ->
  (x = y /\ b = bind_typ T) \/ binds x b E.
Proof.
  intros. apply binds_cons_iff in H. destruct H as [[Heq Hb]|H].
  - left. auto.
  - right. assumption.
Qed.

Lemma binds_cons_sub_inv : forall (x y:atom) (im:IsoMode) (E:env) b,
  binds x b (y ~ bind_sub im ++ E) ->
  (x = y /\ b = bind_sub im) \/ binds x b E.
Proof.
  intros. apply binds_cons_iff in H. destruct H as [[Heq Hb]|H].
  - left. auto.
  - right. assumption.
Qed.

Lemma binds_cons_typ_sub : forall (x y:atom) (T:typ) (im:IsoMode) (E:env),
  binds x (bind_sub im) (y ~ bind_typ T ++ E) -> binds x (bind_sub im) E.
Proof.
  intros x y T im E H. apply binds_cons_typ_inv in H.
  destruct H as [[Heq Hb]|H].
  - discriminate Hb.
  - assumption.
Qed.

Lemma binds_typ_swap : forall (x y:atom) (Tx Ty:typ) (E:env) (z:atom) b,
  x <> y ->
  binds z b (x ~ bind_typ Tx ++ y ~ bind_typ Ty ++ E) ->
  binds z b (y ~ bind_typ Ty ++ x ~ bind_typ Tx ++ E).
Proof.
  intros x y Tx Ty E z b Hxy Hb.
  apply binds_cons_iff in Hb. destruct Hb as [[Heq Hb]|Hb].
  - subst z. subst b. apply binds_cons_3. left. auto.
  - apply binds_cons_iff in Hb. destruct Hb as [[Heq Hb]|Hb].
    + subst. left. auto.
    + apply binds_cons_3. apply binds_cons_3. assumption.
Qed.

(* ============================================================ *)
(* WFS: monotonicity, weakening, strengthening, duality          *)
(* ============================================================ *)

Lemma WFS_env_impl : forall E T, WFS E T ->
  forall E', (forall X im, binds X (bind_sub im) E -> binds X (bind_sub im) E') ->
  WFS E' T.
Proof.
  intros E T H.
  induction H as [E | E | X E im Hb | E A B HA IHA HB IHB | L E A im HP IH];
    intros E' Himp.
  - constructor.
  - constructor.
  - apply WFS_fvar with (im:=im). auto.
  - apply WFS_arrow; auto.
  - apply WFS_rec with (im:=im) (L:=L). intros X Hx.
    eapply IH. exact Hx. intros Y i Hy.
    apply binds_cons_sub_inv in Hy. destruct Hy as [[Heq Hb]|Hy].
    + subst Y. injection Hb as Hi. subst i. left. reflexivity.
    + apply binds_cons_3. auto.
Qed.

Lemma WFS_env_iff : forall E T, WFS E T ->
  forall E', (forall X im, binds X (bind_sub im) E <-> binds X (bind_sub im) E') ->
  WFS E' T.
Proof.
  intros E T H E' Heq.
  apply WFS_env_impl with (E:=E); auto.
  intros. apply Heq. auto.
Qed.

Lemma WFS_weaken : forall E T, WFS E T -> forall (x:atom) b,
  WFS (x ~ b ++ E) T.
Proof.
  intros E T H x b.
  apply WFS_env_impl with (E:=E).
  - assumption.
  - intros. apply binds_cons_3. auto.
Qed.

Lemma binds_sub_cons_typ_iff : forall (z:atom) (i:IsoMode) (x:atom) (T:typ) (E:env),
  binds z (bind_sub i) (x ~ bind_typ T ++ E) <-> binds z (bind_sub i) E.
Proof.
  split.
  - apply binds_cons_typ_sub.
  - apply binds_cons_3.
Qed.

Lemma WFS_strengthen_typ : forall (x:atom) (T:typ) (E:env) A,
  WFS (x ~ bind_typ T ++ E) A -> WFS E A.
Proof.
  intros. eapply WFS_env_iff; [exact H|].
  intros. apply binds_sub_cons_typ_iff.
Qed.

Lemma WFS_flip : forall E T, WFS E T -> WFS (flip_env E) T.
Proof.
  intros E T H.
  induction H as [E | E | X E im Hb | E A B HA IHA HB IHB | L E A im HP IH].
  - constructor.
  - constructor.
  - apply WFS_fvar with (im:=flip_im im).
    apply binds_flip_env with (b:=bind_sub im). auto.
  - apply WFS_arrow; auto.
  - apply WFS_rec with (im:=flip_im im) (L:=L). intros X Hx.
    change (WFS (flip_env (X ~ bind_sub im ++ E)) (open_tt A X)).
    eapply IH. exact Hx.
Qed.

Lemma wf_env_cons_inv : forall (x:atom) b (E:env),
  wf_env (x ~ b ++ E) -> wf_env E.
Proof.
  intros x b E H. remember (x ~ b ++ E) as F eqn:HF.
  induction H; subst; try discriminate.
  - inversion HF. subst. assumption.
  - inversion HF. subst. assumption.
Qed.

Lemma wf_env_bind_typ_wfs : forall (x:atom) (T:typ) (E:env),
  wf_env (x ~ bind_typ T ++ E) -> WFS E T.
Proof.
  intros x T E H. remember (x ~ bind_typ T ++ E) as F eqn:HF.
  induction H.
  - discriminate HF.
  - injection HF as HX Hb HE. discriminate Hb.
  - injection HF as Hy HT0 HE. subst. assumption.
Qed.

Lemma wf_env_flip : forall E, wf_env E -> wf_env (flip_env E).
Proof.
  induction 1 as [| E X im Hwf IH Hdom | E x T Hwf IH HW Hdom].
  - simpl. constructor.
  - simpl. apply wf_env_sub.
    + apply IH.
    + rewrite dom_flip_env. assumption.
  - simpl. apply wf_env_typ.
    + apply IH.
    + apply WFS_flip. assumption.
    + rewrite dom_flip_env. assumption.
Qed.

(* ============================================================ *)
(* Subtyping duality                                             *)
(* ============================================================ *)

Lemma Sub_dual : forall im cm evs E A B, Sub im cm evs E A B ->
   Sub (flip_im im) cm evs (flip_env E) A B.
Proof.
  intros im cm evs E A B H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E X im0 Hwf Hb
                 | E X im0 Hwf Hb
                 | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm0 im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | im0 cm0 evs0 evs' E A1 A2 Hs IHs Heq].
  - apply Sa_nat. apply wf_env_flip. assumption.
  - apply Sa_top_eq. apply wf_env_flip. assumption.
  - apply Sa_top_lt; [ apply wf_env_flip | apply WFS_flip | ]; assumption.
  - apply Sa_fvar_pos.
    + apply wf_env_flip. assumption.
    + apply binds_flip_env with (b:=bind_sub im0). assumption.
  - apply Sa_fvar_neg.
    + apply wf_env_flip. assumption.
    + apply binds_flip_env with (b:=bind_sub (flip_im im0)). assumption.
  - eapply Sa_arrow.
    + apply IH1.
    + apply IH2.
    + apply Hc.
  - apply Sa_rec_lt with (L:=L). intros X Hx.
    change (Sub (flip_im im0) Lt evs0 (flip_env (X ~ bind_sub im0 ++ E))
                (open_tt A1 X) (open_tt A2 X)).
    apply IH. assumption.
  - apply Sa_rec_eq_notin with (L:=L). intros X Hx.
    change (Sub (flip_im im0) Eq evs0 (flip_env (X ~ bind_sub im0 ++ E))
                (open_tt A1 X) (open_tt A2 X)).
    apply IH. assumption.
  - apply Sa_rec_eq_in with (L:=L). intros X Hx.
    change (Sub (flip_im im0) Eq (add X evs0) (flip_env (X ~ bind_sub im0 ++ E))
                (open_tt A1 X) (open_tt A2 X)).
    apply IH. assumption.
  - apply Sa_evs_proper with (evs:=evs0); assumption.
Qed.

Lemma Sub_neg_pos : forall E A B cm evs,
  NoSubBind E -> Sub Neg cm evs E A B -> Sub Pos cm evs E A B.
Proof.
  intros E A B cm evs Hn Hs.
  assert (Hd := Sub_dual _ _ _ _ _ _ Hs).
  rewrite flip_env_id in Hd by assumption.
  simpl in Hd. exact Hd.
Qed.

(* ============================================================ *)
(* Subtyping: well-formedness and shape inversion                *)
(* ============================================================ *)

Lemma exists_fresh_notin : forall (L:atoms), exists X:atom, X \notin L.
Proof.
  intros L. destruct (atom_fresh L) as [x Hx]. exists x. assumption.
Qed.

Lemma Sub_wf_env : forall im cm evs E A B, Sub im cm evs E A B -> wf_env E.
Proof.
  intros im cm evs E A B H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E X im0 Hwf Hb
                 | E X im0 Hwf Hb
                 | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm0 im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | im0 cm0 evs0 evs' E A1 A2 Hs IHs Heq].
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - destruct (exists_fresh_notin L) as [X Hx].
    apply wf_env_cons_inv with (x:=X) (b:=bind_sub im0). apply IH. assumption.
  - destruct (exists_fresh_notin L) as [X Hx].
    apply wf_env_cons_inv with (x:=X) (b:=bind_sub im0). apply IH. assumption.
  - destruct (exists_fresh_notin L) as [X Hx].
    apply wf_env_cons_inv with (x:=X) (b:=bind_sub im0). apply IH. assumption.
  - assumption.
Qed.

Lemma Sub_wfs : forall im cm evs E A B, Sub im cm evs E A B -> WFS E A /\ WFS E B.
Proof.
  intros im cm evs E A B H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E X im0 Hwf Hb
                 | E X im0 Hwf Hb
                 | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm0 im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | im0 cm0 evs0 evs' E A1 A2 Hs IHs Heq].
  - split; constructor.
  - split; constructor.
  - split; [assumption|constructor].
  - split; apply WFS_fvar with (im:=im0); assumption.
  - split; apply WFS_fvar with (im:=flip_im im0); assumption.
  - destruct IH1 as [HB1 HA1]. destruct IH2 as [HA2 HB2].
    split; apply WFS_arrow; assumption.
  - split; apply WFS_rec with (L:=L) (im:=im0).
    + intros X Hx. apply (IH X Hx).
    + intros X Hx. apply (IH X Hx).
  - split; apply WFS_rec with (L:=L) (im:=im0).
    + intros X Hx. apply (IH X Hx).
    + intros X Hx. apply (IH X Hx).
  - split; apply WFS_rec with (L:=L) (im:=im0).
    + intros X Hx. apply (IH X Hx).
    + intros X Hx. apply (IH X Hx).
  - assumption.
Qed.

(* Shape inversion lemmas for Sub *)

Lemma Sub_top_inv : forall im cm evs E A B,
  Sub im cm evs E A B -> A = typ_top -> B = typ_top.
Proof.
  intros im cm evs E A B H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E X im0 Hwf Hb
                 | E X im0 Hwf Hb
                 | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm0 im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | im0 cm0 evs0 evs' E A1 A2 Hs IHs Heq];
  intros HA; try inversion HA; try reflexivity; try (apply IHs; assumption).
Qed.

Lemma Sub_nat_inv : forall im cm evs E A B,
  Sub im cm evs E A B -> A = typ_nat -> B = typ_nat \/ B = typ_top.
Proof.
  intros im cm evs E A B H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E X im0 Hwf Hb
                 | E X im0 Hwf Hb
                 | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm0 im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | im0 cm0 evs0 evs' E A1 A2 Hs IHs Heq];
  intros HA; try inversion HA; try (left; reflexivity); try (right; reflexivity);
  try (apply IHs; assumption).
Qed.

Lemma Sub_nat_right_inv : forall im cm evs E A B,
  Sub im cm evs E A B -> B = typ_nat -> A = typ_nat.
Proof.
  intros im cm evs E A B H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E X im0 Hwf Hb
                 | E X im0 Hwf Hb
                 | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm0 im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | im0 cm0 evs0 evs' E A1 A2 Hs IHs Heq];
  intros HB; try inversion HB; try reflexivity; try (apply IHs; assumption).
Qed.

Lemma Sub_fvar_left_inv : forall im cm evs E A B X,
  Sub im cm evs E A B -> A = typ_fvar X -> B = typ_fvar X \/ B = typ_top.
Proof.
  intros im cm evs E A B X H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E X0 im0 Hwf Hb
                 | E X0 im0 Hwf Hb
                 | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm0 im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | im0 cm0 evs0 evs' E A1 A2 Hs IHs Heq];
  intros HA; try inversion HA; try (right; reflexivity); try (left; reflexivity);
  try (apply IHs; assumption).
Qed.

Lemma Sub_arrow_left_inv : forall im cm evs E A B,
  Sub im cm evs E A B ->
  forall A1 A2, A = typ_arrow A1 A2 ->
  B = typ_top \/ exists B1 B2 cm1 cm2 evs1 evs2,
     B = typ_arrow B1 B2 /\
     Sub (flip_im im) cm1 evs1 E B1 A1 /\
     Sub im cm2 evs2 E A2 B2.
Proof.
  intros im cm evs E A B H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E X0 im0 Hwf Hb
                 | E X0 im0 Hwf Hb
                 | E a1 a2 b1 b2 c1 c2 e1 e2 c0 im0 H1 IH1 H2 IH2 Hc
                 | L r1 r2 e0 E im0 HP IH
                 | L r1 r2 e0 E im0 HP IH
                 | L r1 r2 e0 E im0 HP IH
                 | im0 c0 e0 e' E a1 a2 Hs IHs Heq];
  intros X1 X2 HA.
- inversion HA.
- inversion HA.
- left; reflexivity.
- inversion HA.
- inversion HA.
- injection HA as E1 E2; subst. right.
  exists b1, b2, c1, c2, e1, e2. auto.
- inversion HA.
- inversion HA.
- inversion HA.
- apply IHs. assumption.
Qed.

Lemma Sub_arrow_right_inv : forall im cm evs E A B,
  Sub im cm evs E A B ->
  forall B1 B2, B = typ_arrow B1 B2 ->
  exists A1 A2 cm1 cm2 evs1 evs2,
     A = typ_arrow A1 A2 /\
     Sub (flip_im im) cm1 evs1 E B1 A1 /\
     Sub im cm2 evs2 E A2 B2.
Proof.
  intros im cm evs E A B H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E X0 im0 Hwf Hb
                 | E X0 im0 Hwf Hb
                 | E a1 a2 b1 b2 c1 c2 e1 e2 c0 im0 H1 IH1 H2 IH2 Hc
                 | L r1 r2 e0 E im0 HP IH
                 | L r1 r2 e0 E im0 HP IH
                 | L r1 r2 e0 E im0 HP IH
                 | im0 c0 e0 e' E a1 a2 Hs IHs Heq];
  intros Y1 Y2 HB.
- inversion HB.
- inversion HB.
- inversion HB.
- inversion HB.
- inversion HB.
- injection HB as E1 E2; subst.
  exists a1, a2, c1, c2, e1, e2. auto.
- inversion HB.
- inversion HB.
- inversion HB.
- apply IHs. assumption.
Qed.

Lemma Sub_mu_left_inv : forall im cm evs E A B Z,
  Sub im cm evs E A B -> A = typ_mu Z -> B = typ_top \/ exists B2, B = typ_mu B2.
Proof.
  intros im cm evs E A B Z H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E X0 im0 Hwf Hb
                 | E X0 im0 Hwf Hb
                 | E a1 a2 b1 b2 c1 c2 e1 e2 c0 im0 H1 IH1 H2 IH2 Hc
                 | L r1 r2 e0 E im0 HP IH
                 | L r1 r2 e0 E im0 HP IH
                 | L r1 r2 e0 E im0 HP IH
                 | im0 c0 e0 e' E a1 a2 Hs IHs Heq];
  intros HA.
- inversion HA.
- inversion HA.
- left; reflexivity.
- inversion HA.
- inversion HA.
- inversion HA.
- right; eexists; reflexivity.
- right; eexists; reflexivity.
- right; eexists; reflexivity.
- apply IHs. assumption.
Qed.

Lemma Sub_mu_right_inv : forall im cm evs E A B Z,
  Sub im cm evs E A B -> B = typ_mu Z -> exists A1, A = typ_mu A1.
Proof.
  intros im cm evs E A B Z H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E X0 im0 Hwf Hb
                 | E X0 im0 Hwf Hb
                 | E a1 a2 b1 b2 c1 c2 e1 e2 c0 im0 H1 IH1 H2 IH2 Hc
                 | L r1 r2 e0 E im0 HP IH
                 | L r1 r2 e0 E im0 HP IH
                 | L r1 r2 e0 E im0 HP IH
                 | im0 c0 e0 e' E a1 a2 Hs IHs Heq];
  intros HB.
- inversion HB.
- inversion HB.
- inversion HB.
- inversion HB.
- inversion HB.
- inversion HB.
- eexists; reflexivity.
- eexists; reflexivity.
- eexists; reflexivity.
- apply IHs. assumption.
Qed.

(* ============================================================ *)
(* Closed types: no free bound variables                         *)
(* ============================================================ *)

Lemma WFS_type : forall E A, WFS E A -> type A.
Proof.
  intros E A H. induction H as [E | E | X E im Hb | E A B HA IHA HB IHB | L E A im HP IH].
  - constructor.
  - constructor.
  - apply type_var.
  - apply type_arrow; assumption.
  - apply type_mu with (L:=L). intros X Hx. apply IH. assumption.
Qed.

Fixpoint has_bvar_tt (k:nat) (T:typ) {struct T} : bool :=
  match T with
  | typ_top => false
  | typ_nat => false
  | typ_fvar _ => false
  | typ_bvar j => if k == j then true else false
  | typ_arrow T1 T2 => orb (has_bvar_tt k T1) (has_bvar_tt k T2)
  | typ_mu T0 => has_bvar_tt (S k) T0
  end.

Lemma open_tt_no_bvar : forall T k u,
  has_bvar_tt k T = false -> open_tt_rec k u T = T.
Proof.
  induction T; intros k u H; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct (k == n); [discriminate H | reflexivity].
  - reflexivity.
  - rewrite IHT; [reflexivity|assumption].
  - apply orb_false_iff in H. destruct H as [H1 H2].
    rewrite (IHT1 k u H1), (IHT2 k u H2). reflexivity.
Qed.

Lemma has_bvar_open_fvar : forall T k X i,
  i <> k -> has_bvar_tt i (open_tt_rec k (typ_fvar X) T) = has_bvar_tt i T.
Proof.
  induction T; intros k X i Hneq; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (k == n) as [e|e].
    + assert (n = k) by (symmetry; exact e). subst n.
      destruct (i == k) as [e2|e2].
      * exfalso. apply Hneq. exact e2.
      * reflexivity.
    + reflexivity.
  - reflexivity.
  - apply IHT. intro Hc. apply Hneq. inversion Hc. reflexivity.
  - rewrite IHT1; [|assumption]. rewrite IHT2; [|assumption]. reflexivity.
Qed.

Lemma type_no_bvar : forall T, type T -> forall k, has_bvar_tt k T = false.
Proof.
  intros T H. induction H as [ | | X | T1 T2 HT1 IH1 HT2 IH2 | L T0 HP IH].
  - intros k; reflexivity.
  - intros k; reflexivity.
  - intros k; reflexivity.
  - intros k; simpl; rewrite IH1, IH2; reflexivity.
  - intros k.
    destruct (exists_fresh_notin L) as [X Hx].
    specialize (IH X Hx (S k)).
    assert (Hopen : has_bvar_tt (S k) (open_tt_rec 0 (typ_fvar X) T0) = false)
      by exact IH.
    rewrite (has_bvar_open_fvar T0 0 X (S k)) in Hopen by discriminate.
    simpl. exact Hopen.
Qed.

Lemma type_open_tt_id : forall T, type T -> forall k u, open_tt_rec k u T = T.
Proof.
  intros T HT k u. apply open_tt_no_bvar. apply type_no_bvar. assumption.
Qed.

Lemma open_tt_subst_tt : forall A X U Y, X <> Y -> type U ->
  forall k, open_tt_rec k (typ_fvar Y) (subst_tt X U A) =
          subst_tt X U (open_tt_rec k (typ_fvar Y) A).
Proof.
  induction A; intros X U Y Hneq HU k; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (k == n) as [keq|kneq].
    + simpl. destruct (Y == X) as [e|ne].
      * exfalso. apply Hneq. symmetry. exact e.
      * reflexivity.
    + reflexivity.
  - destruct (a == X) as [e|ne].
    + simpl. rewrite type_open_tt_id; [reflexivity|assumption].
    + simpl. reflexivity.
  - rewrite (IHA X U Y Hneq HU (S k)). reflexivity.
  - rewrite (IHA1 X U Y Hneq HU k). rewrite (IHA2 X U Y Hneq HU k). reflexivity.
Qed.

Lemma subst_tt_open_tt_self : forall T X U k,
  X \notin fv_tt T ->
  subst_tt X U (open_tt_rec k (typ_fvar X) T) = open_tt_rec k U T.
Proof.
  induction T; intros X U k Hfv; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct (k == n) as [keq|kneq].
    + simpl. destruct (X == X) as [e|ne].
      * reflexivity.
      * exfalso. apply ne. reflexivity.
    + reflexivity.
  - destruct (a == X) as [e|ne].
    + subst a. exfalso. apply (test_solve_notin_7 X). exact Hfv.
    + simpl. reflexivity.
  - rewrite (IHT X U (S k) Hfv). reflexivity.
  - apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite (IHT1 X U k H1). rewrite (IHT2 X U k H2). reflexivity.
Qed.

(* ============================================================ *)
(* WFS: membership-sensitive monotonicity and substitution       *)
(* ============================================================ *)

Lemma fv_tt_open_rec : forall A k U Z,
  Z \in fv_tt (open_tt_rec k U A) -> Z \in fv_tt A \/ Z \in fv_tt U.
Proof.
  induction A; intros k U Z H; simpl in *.
  - exfalso. exact (AtomSetImpl.empty_1 H).
  - exfalso. exact (AtomSetImpl.empty_1 H).
  - destruct (k == n) as [e|ne].
    + right. exact H.
    + exfalso. exact (AtomSetImpl.empty_1 H).
  - left. exact H.
  - apply IHA in H. destruct H as [H|H]; [left|right]; exact H.
  - apply AtomSetImpl.union_1 in H. destruct H as [H|H].
    + apply IHA1 in H. destruct H as [H|H].
      * left. apply AtomSetImpl.union_2. exact H.
      * right. exact H.
    + apply IHA2 in H. destruct H as [H|H].
      * left. apply AtomSetImpl.union_3. exact H.
      * right. exact H.
Qed.

Lemma WFS_env_impl_on : forall E A, WFS E A ->
  forall E', (forall X im, X \in fv_tt A ->
                binds X (bind_sub im) E -> binds X (bind_sub im) E') ->
  WFS E' A.
Proof.
  intros E A H.
  induction H as [E | E | X E im Hb | E A B HA IHA HB IHB | L E A im HP IH];
    intros E' Himp.
  - constructor.
  - constructor.
  - apply WFS_fvar with (im:=im).
    apply Himp.
    + simpl. apply AtomSetImpl.singleton_2. reflexivity.
    + assumption.
  - apply WFS_arrow.
    + apply IHA. intros Z i HZ. apply Himp.
      simpl. apply AtomSetImpl.union_2. exact HZ.
    + apply IHB. intros Z i HZ. apply Himp.
      simpl. apply AtomSetImpl.union_3. exact HZ.
  - apply WFS_rec with (im:=im) (L:= L \u dom E). intros Y HY.
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HYdom : Y \notin dom E) by (apply notin_union_2 in HY; exact HY).
    apply (IH Y HYL). intros Z i HZ Hb.
    destruct (Z == Y) as [e|ne].
    + subst Z. apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
      * left. rewrite Hbe. reflexivity.
      * exfalso. eapply binds_dom_contradiction; [exact Hb|exact HYdom].
    + apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
      * exfalso. apply ne. exact Heq.
      * apply binds_cons_3.
        apply Himp with (X:=Z) (im:=i).
        -- apply fv_tt_open_rec in HZ. destruct HZ as [HZ|HZ]; [exact HZ|].
           exfalso. apply ne. apply AtomSetImpl.singleton_1 in HZ.
           symmetry. exact HZ.
        -- exact Hb.
Qed.

Lemma WFS_strengthen_sub_notin : forall (x:atom) im E A,
  WFS (x ~ bind_sub im ++ E) A -> x \notin fv_tt A -> WFS E A.
Proof.
  intros x im E A H Hfv.
  eapply WFS_env_impl_on; [exact H|].
  intros Z i HZ Hb. simpl in Hb.
  apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
  - subst Z. exfalso. apply Hfv. exact HZ.
  - exact Hb.
Qed.

Lemma WFS_subst : forall E A, WFS E A ->
  forall X im U, binds X (bind_sub im) E -> WFS E U -> WFS E (subst_tt X U A).
Proof.
  intros E A H.
  induction H as [E | E | Y E im0 Hb0 | E A B HA IHA HB IHB | L E A im0 HP IH];
    intros X im U Hb HU.
  - constructor.
  - constructor.
  - simpl. destruct (Y == X) as [e|ne].
    + subst Y. exact HU.
    + apply WFS_fvar with (im:=im0). exact Hb0.
  - simpl. apply WFS_arrow.
    + apply IHA with (im:=im); assumption.
    + apply IHB with (im:=im); assumption.
  - simpl. apply WFS_rec with (L:= L \u {{ X }}) (im:=im0). intros Y HY.
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HXY : X <> Y).
    { intro Hc. apply HY. simpl. apply AtomSetImpl.union_3.
      apply AtomSetImpl.singleton_2. exact Hc. }
    assert (HTU : type U) by (apply (WFS_type E U HU)).
    change (WFS (Y ~ bind_sub im0 ++ E) (open_tt_rec 0 (typ_fvar Y) (subst_tt X U A))).
    rewrite (open_tt_subst_tt A X U Y HXY HTU 0).
    apply (IH Y HYL) with (im:=im).
    + apply binds_cons_3. exact Hb.
    + apply WFS_weaken. exact HU.
Qed.

Lemma fv_tt_open_notin : forall T U (X:atom) k,
  X \notin fv_tt T -> X \notin fv_tt U -> X \notin fv_tt (open_tt_rec k U T).
Proof.
  induction T; intros U X k HT HU; simpl in *.
  - apply notin_empty_1.
  - apply notin_empty_1.
  - destruct (k == n) as [e|ne].
    + simpl. exact HU.
    + apply notin_empty_1.
  - simpl. exact HT.
  - apply IHT. exact HT. exact HU.
  - simpl. apply notin_union_3.
    + apply IHT1. apply notin_union_1 in HT. exact HT. exact HU.
    + apply IHT2. apply notin_union_2 in HT. exact HT. exact HU.
Qed.

Lemma fv_tt_open_mu_notin : forall T (X:atom) k,
  X \notin fv_tt T -> X \notin fv_tt (open_tt_rec k (typ_mu T) T).
Proof.
  intros T X k H. apply fv_tt_open_notin; [exact H|].
  simpl. exact H.
Qed.

Lemma WFS_unfold : forall E T, WFS E (typ_mu T) -> WFS E (open_tt T (typ_mu T)).
Proof.
  intros E T H. assert (Hmu : WFS E (typ_mu T)) by exact H.
  inversion H as [| | | | L E0 A im HP]; subst.
  destruct (atom_fresh (L \u fv_tt T)) as [X HX].
  assert (HXL : X \notin L) by (apply notin_union_1 in HX; exact HX).
  assert (HXfv : X \notin fv_tt T) by (apply notin_union_2 in HX; exact HX).
  assert (HWs : WFS (X ~ bind_sub im ++ E) (open_tt T X)) by (apply HP; exact HXL).
  pose proof (WFS_subst (X ~ bind_sub im ++ E) (open_tt T X) HWs
              X im (typ_mu T)) as Hsub.
  assert (Hb : binds X (bind_sub im) (X ~ bind_sub im ++ E)) by (left; reflexivity).
  assert (HWu : WFS (X ~ bind_sub im ++ E) (typ_mu T))
    by (apply WFS_weaken with (x:=X) (b:=bind_sub im); exact Hmu).
  specialize (Hsub Hb HWu).
  change (WFS (X ~ bind_sub im ++ E)
            (subst_tt X (typ_mu T) (open_tt_rec 0 (typ_fvar X) T))) in Hsub.
  rewrite (subst_tt_open_tt_self T X (typ_mu T) 0 HXfv) in Hsub.
  apply WFS_strengthen_sub_notin with (x:=X) (im:=im) in Hsub.
  - exact Hsub.
  - apply fv_tt_open_mu_notin. exact HXfv.
Qed.

(* ============================================================ *)
(* Environment binding lemmas for wf_env                        *)
(* ============================================================ *)

Lemma wf_env_binds_wfs : forall E x T, wf_env E -> binds x (bind_typ T) E -> WFS E T.
Proof.
  intros E x T Hwf.
  induction Hwf as [| E0 X im HwfE IHE Hdom | E0 y T0 HwfE IHE HW Hdom];
    intros Hb.
  - rewrite binds_nil_iff in Hb. destruct Hb.
  - apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
    + subst X. discriminate Hbe.
    + apply WFS_weaken with (x:=X) (b:=bind_sub im). apply IHE. exact Hb.
  - apply binds_cons_typ_inv in Hb. destruct Hb as [[Heq Hb0]|Hb].
    + subst y. injection Hb0 as HT. subst T0.
      apply WFS_weaken with (x:=x) (b:=bind_typ T). exact HW.
    + apply WFS_weaken with (x:=y) (b:=bind_typ T0). apply IHE. exact Hb.
Qed.

(* ============================================================ *)
(* Typing metatheory                                             *)
(* ============================================================ *)

Lemma typing_wf_env : forall G e T, typing G e T -> wf_env G.
Proof.
  intros G e T H.
  induction H as [G Hwf
                 | G x T0 Hwf Hb
                 | L G T1 e0 T2 HP IH
                 | G e1 e2 T2 T1 H1 IH1 H2 IH2
                 | G A e0 H1 IH1 Hw
                 | G T0 e0 H1 IH1
                 | G T0 e0 S evs cm H1 IH1 Hs].
  - assumption.
  - assumption.
  - destruct (exists_fresh_notin L) as [x Hx].
    apply wf_env_cons_inv with (x:=x) (b:=bind_typ T1). apply IH. assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma typing_wfs : forall G e T, typing G e T -> WFS G T.
Proof.
  intros G e T H.
  induction H as [G Hwf
                 | G x T0 Hwf Hb
                 | L G T1 e0 T2 HP IH
                 | G e1 e2 T2 T1 H1 IH1 H2 IH2
                 | G A e0 H1 IH1 Hw
                 | G T0 e0 H1 IH1
                 | G T0 e0 S evs cm H1 IH1 Hs].
  - apply WFS_nat.
  - apply wf_env_binds_wfs with (x:=x); assumption.
  - destruct (exists_fresh_notin L) as [x Hx].
    assert (Hwf : wf_env ((x ~ bind_typ T1) ++ G)) by (apply (typing_wf_env ((x ~ bind_typ T1) ++ G) (open_ee e0 x) T2); apply HP; assumption).
    apply WFS_arrow.
    + apply wf_env_bind_typ_wfs with (x:=x). exact Hwf.
    + apply WFS_strengthen_typ with (x:=x) (T:=T1). apply IH. assumption.
  - inversion IH1. subst. assumption.
  - exact Hw.
  - apply WFS_unfold. exact IH1.
  - apply Sub_wfs in Hs. destruct Hs as [_ Hs2]. exact Hs2.
Qed.

Lemma typing_expr : forall G e T, typing G e T -> expr e.
Proof.
  intros G e T H.
  induction H as [G Hwf
                 | G x T0 Hwf Hb
                 | L G T1 e0 T2 HP IH
                 | G e1 e2 T2 T1 H1 IH1 H2 IH2
                 | G A e0 H1 IH1 Hw
                 | G T0 e0 H1 IH1
                 | G T0 e0 S evs cm H1 IH1 Hs].
  - apply lc_nat.
  - apply lc_fvar.
  - apply lc_abs with (L:=L) (T:=T1).
    + intros x Hx. apply IH. assumption.
    + destruct (exists_fresh_notin L) as [x Hx].
      assert (Hwf : wf_env ((x ~ bind_typ T1) ++ G))
        by (apply (typing_wf_env ((x ~ bind_typ T1) ++ G) (open_ee e0 x) T2);
            apply HP; assumption).
      apply (WFS_type G T1). apply wf_env_bind_typ_wfs with (x:=x). exact Hwf.
  - apply lc_app; assumption.
  - apply lc_fold with (T:=typ_mu A).
    + apply (WFS_type G (typ_mu A)). exact Hw.
    + assumption.
  - apply lc_unfold with (T:=typ_mu T0).
    + apply (WFS_type G (typ_mu T0)). apply (typing_wfs G e0 (typ_mu T0)). exact H1.
    + assumption.
  - assumption.
Qed.

Lemma typing_nat_shape : forall G e T, typing G e T -> e = exp_nat ->
  T = typ_nat \/ T = typ_top.
Proof.
  intros G e T H.
  induction H as [G Hwf
                 | G x T0 Hwf Hb
                 | L G T1 e0 T2 HP IH
                 | G e1 e2 T2 T1 H1 IH1 H2 IH2
                 | G A e0 H1 IH1 Hw
                 | G T0 e0 H1 IH1
                 | G T0 e0 S evs cm H1 IH1 Hs];
    intros He.
  - left. reflexivity.
  - discriminate He.
  - discriminate He.
  - discriminate He.
  - discriminate He.
  - discriminate He.
  - destruct (IH1 He) as [HS|HS].
    + apply (Sub_nat_inv Pos cm evs G S T0 Hs HS).
    + right. apply (Sub_top_inv Pos cm evs G S T0 Hs HS).
Qed.

Lemma typing_fold_ann_wfs : forall G e U, typing G e U ->
  forall T0 v, e = exp_fold T0 v -> exists A, T0 = typ_mu A /\ WFS G (typ_mu A).
Proof.
  intros G e U H.
  induction H as [G Hwf
                 | G x T0' Hwf Hb
                 | L G T1 e0 T2 HP IH
                 | G e1 e2 T2 T1 H1 IH1 H2 IH2
                 | G A e0 H1 IH1 Hw
                 | G T0' e0 H1 IH1
                 | G T0' e0 S evs cm H1 IH1 Hs];
    intros T0 v He.
  - discriminate He.
  - discriminate He.
  - discriminate He.
  - discriminate He.
  - injection He as HT Hv. subst T0. exists A. split; [reflexivity|exact Hw].
  - discriminate He.
  - exact (IH1 T0 v He).
Qed.

Lemma typing_fold_shape : forall G e T, typing G e T ->
  forall T0 v, e = exp_fold T0 v ->
  T = typ_top \/ (exists A, T = typ_mu A).
Proof.
  intros G e T H.
  induction H as [G Hwf
                 | G x T0' Hwf Hb
                 | L G T1 e0 T2 HP IH
                 | G e1 e2 T2 T1 H1 IH1 H2 IH2
                 | G A e0 H1 IH1 Hw
                 | G T0' e0 H1 IH1
                 | G T0' e0 S evs cm H1 IH1 Hs];
    intros Tu v He.
  - discriminate He.
  - discriminate He.
  - discriminate He.
  - discriminate He.
  - injection He as HT Hv. right. eexists. reflexivity.
  - discriminate He.
  - destruct (IH1 Tu v He) as [HS|HS].
    + left. apply (Sub_top_inv Pos cm evs G S T0' Hs HS).
    + destruct HS as [A HA].
      apply (Sub_mu_left_inv Pos cm evs G S T0' A Hs HA).
Qed.

Lemma typing_abs_shape : forall G e T, typing G e T ->
  forall T1 b, e = exp_abs T1 b ->
  T = typ_top \/ (exists B1 B2, T = typ_arrow B1 B2).
Proof.
  intros G e T H.
  induction H as [G Hwf
                 | G x T0' Hwf Hb
                 | L G Ta e0 T2 HP IH
                 | G e1 e2 T2c T1c H1 IH1 H2 IH2
                 | G A e0 H1 IH1 Hw
                 | G T0' e0 H1 IH1
                 | G T0' e0 S evs cm H1 IH1 Hs];
    intros T1 b He.
  - discriminate He.
  - discriminate He.
  - injection He as HT Hb'. subst Ta. right. eexists. eexists. reflexivity.
  - discriminate He.
  - discriminate He.
  - discriminate He.
  - destruct (IH1 T1 b He) as [HS|HS].
    + left. apply (Sub_top_inv Pos cm evs G S T0' Hs HS).
    + destruct HS as [B1 [B2 HB]].
      destruct (Sub_arrow_left_inv Pos cm evs G S T0' Hs B1 B2 HB) as [HT|HT].
      * left. exact HT.
      * right. destruct HT as [C1 [C2 [cm1 [cm2 [evs1 [evs2 [HT0 _]]]]]]].
        eexists C1. eexists C2. exact HT0.
Qed.

Lemma value_arrow_abs : forall v G A B, value v -> typing G v (typ_arrow A B) ->
  exists T e, v = exp_abs T e.
Proof.
  intros v G A B HV HT.
  destruct HV as [t1 T' Hexpr | | T' e' Htype HV'].
  - exists T', t1. reflexivity.
  - destruct (typing_nat_shape G exp_nat (typ_arrow A B) HT eq_refl) as [H|H];
      discriminate H.
  - destruct (typing_fold_shape G (exp_fold T' e') (typ_arrow A B) HT T' e' eq_refl)
      as [H|H]; [discriminate H|].
    destruct H as [A' HA]. discriminate HA.
Qed.

Lemma value_mu_fold : forall v G A, value v -> typing G v (typ_mu A) ->
  exists T e, v = exp_fold T e.
Proof.
  intros v G A HV HT.
  destruct HV as [t1 T' Hexpr | | T' e' Htype HV'].
  - destruct (typing_abs_shape G (exp_abs T' t1) (typ_mu A) HT T' t1 eq_refl)
      as [H|H]; [discriminate H|].
    destruct H as [B1 [B2 HB]]. discriminate HB.
  - destruct (typing_nat_shape G exp_nat (typ_mu A) HT eq_refl) as [H|H];
      discriminate H.
  - exists T', e'. reflexivity.
Qed.

Lemma progress_gen : forall G e T, typing G e T -> G = empty ->
  value e \/ exists e', step e e'.
Proof.
  intros G e T H.
  induction H as [G Hwf
                 | G x T0 Hwf Hb
                 | L G T1 e0 T2 HP IH
                 | G e1 e2 T2 T1 H1 IH1 H2 IH2
                 | G A e0 H1 IH1 Hw
                 | G T0 e0 H1 IH1
                 | G T0 e0 S evs cm H1 IH1 Hs];
    intros HG.
  - left. apply value_nat.
  - subst G. rewrite binds_nil_iff in Hb. destruct Hb.
  - left. apply value_abs.
    apply lc_abs with (L:=L) (T:=T1).
    + intros x Hx. apply (typing_expr ((x ~ bind_typ T1) ++ G) (open_ee e0 x) T2).
      apply HP. assumption.
    + destruct (exists_fresh_notin L) as [x Hx].
      assert (Hwf' : wf_env ((x ~ bind_typ T1) ++ G))
        by (apply (typing_wf_env ((x ~ bind_typ T1) ++ G) (open_ee e0 x) T2);
            apply HP; assumption).
      apply (WFS_type G T1). apply wf_env_bind_typ_wfs with (x:=x). exact Hwf'.
  - subst G.
    destruct (IH1 eq_refl) as [Hv1|Hs1].
    + destruct (IH2 eq_refl) as [Hv2|Hs2].
      * destruct (value_arrow_abs e1 empty T1 T2 Hv1 H1) as [T' [body Heq]].
        subst e1. right. exists (open_ee body e2).
        apply step_beta.
        -- apply (typing_expr empty (exp_abs T' body) (typ_arrow T1 T2)). exact H1.
        -- exact Hv2.
      * destruct Hs2 as [e2' Hstep]. right. exists (exp_app e1 e2').
        apply step_app2; assumption.
    + destruct Hs1 as [e1' Hstep].
      destruct (IH2 eq_refl) as [Hv2|Hs2].
      * right. exists (exp_app e1' e2). apply step_app1.
        -- apply (typing_expr empty e2 T1). exact H2.
        -- exact Hstep.
      * right. exists (exp_app e1' e2). apply step_app1.
        -- apply (typing_expr empty e2 T1). exact H2.
        -- exact Hstep.
  - subst G. destruct (IH1 eq_refl) as [Hv|Hs].
    + left. apply value_fold.
      * apply (WFS_type empty (typ_mu A)). exact Hw.
      * exact Hv.
    + right. destruct Hs as [e' Hstep]. exists (exp_fold (typ_mu A) e').
      apply step_fold.
      * exact Hstep.
      * apply (WFS_type empty (typ_mu A)). exact Hw.
  - subst G. destruct (IH1 eq_refl) as [Hv|Hs].
    + destruct (value_mu_fold e0 empty T0 Hv H1) as [T' [v' Heq]]. subst e0.
      destruct (typing_fold_ann_wfs empty (exp_fold T' v') (typ_mu T0) H1 T' v' eq_refl)
        as [A [HA HW]].
      right. exists v'. apply step_fld.
      * inversion Hv; assumption.
      * rewrite HA. apply (WFS_type empty (typ_mu A)). exact HW.
      * apply (WFS_type empty (typ_mu T0)).
        apply (typing_wfs empty (exp_fold T' v') (typ_mu T0)). exact H1.
    + destruct Hs as [e' Hstep]. right. exists (exp_unfold (typ_mu T0) e').
      apply step_unfold.
      * exact Hstep.
      * apply (WFS_type empty (typ_mu T0)).
        apply (typing_wfs empty e0 (typ_mu T0)). exact H1.
  - subst G. exact (IH1 eq_refl).
Qed.



(* ============================================================ *)
(* Removing an irrelevant term binding from environments         *)
(* ============================================================ *)

Lemma binds_insert_mid : forall (Δ:env) (x:atom) (T:typ) (E0:env) y b,
  binds y b (Δ ++ E0) -> binds y b (Δ ++ x ~ bind_typ T ++ E0).
Proof.
  intros. apply binds_app_iff in H. apply binds_app_iff.
  destruct H as [H|H]; [left; exact H|right].
  apply binds_cons_3. exact H.
Qed.

Lemma binds_sub_remove_typ : forall Δ (x:atom) (T1:typ) E0 Y i,
  binds Y (bind_sub i) (Δ ++ x ~ bind_typ T1 ++ E0) <->
  binds Y (bind_sub i) (Δ ++ E0).
Proof.
  intros. split.
  - intro H. apply binds_app_iff in H. destruct H as [H|H].
    + apply binds_app_iff. left. exact H.
    + apply binds_sub_cons_typ_iff in H. apply binds_app_iff. right. exact H.
  - intro H. apply binds_app_iff in H. destruct H as [H|H].
    + apply binds_app_iff. left. exact H.
    + apply binds_app_iff. right. apply binds_sub_cons_typ_iff. exact H.
Qed.

Lemma notin_dom_smaller : forall (Δ:env) (x:atom) (T:typ) (E0:env) y,
  y \notin dom (Δ ++ x ~ bind_typ T ++ E0) -> y \notin dom (Δ ++ E0).
Proof.
  intros Δ x T E0 y H Hc.
  apply binds_In_inv in Hc. destruct Hc as [b Hb].
  apply H. apply binds_In with (a:=b). apply binds_insert_mid. exact Hb.
Qed.

Lemma WFS_remove_typ : forall Δ (x:atom) (T1:typ) E0 A,
  WFS (Δ ++ x ~ bind_typ T1 ++ E0) A -> WFS (Δ ++ E0) A.
Proof.
  intros. eapply WFS_env_iff; [exact H|].
  intros. apply binds_sub_remove_typ.
Qed.

Lemma env_cons_inv : forall (y:atom) (b:binding) (E:env) (z:atom) (c:binding) (F:env),
  (y,b) :: E = (z,c) :: F -> y = z /\ b = c /\ E = F.
Proof.
  intros. injection H as H1 H2 H3. auto.
Qed.

Lemma wf_env_remove_typ : forall E, wf_env E ->
  forall Δ (x:atom) (T1:typ) E0, E = Δ ++ x ~ bind_typ T1 ++ E0 ->
  wf_env (Δ ++ E0).
Proof.
  intros E H.
  induction H as [| E1 Y im Hwf IH Hdom | E1 Y T Hwf IH HW Hdom];
    intros Δ x T1 E0 HE.
  - destruct Δ as [| [y b] Δ']; simpl in HE; discriminate HE.
  - destruct Δ as [| [y b] Δ']; simpl in HE.
    + destruct (env_cons_inv _ _ _ _ _ _ HE) as [HY [Hb HE1]]. discriminate Hb.
    + destruct (env_cons_inv _ _ _ _ _ _ HE) as [HY [Hb HE1]].
      destruct b as [im0|Ty].
      * injection Hb as Hii. subst im0. rewrite HY in Hdom. apply wf_env_sub.
        -- apply IH with (x:=x) (T1:=T1) (E0:=E0). exact HE1.
        -- intro Hc. apply Hdom. rewrite HE1.
           apply binds_In_inv in Hc. destruct Hc as [b' Hb'].
           exact (binds_In binding y b' (Δ' ++ x ~ bind_typ T1 ++ E0)
                    (binds_insert_mid Δ' x T1 E0 y b' Hb')).
      * discriminate Hb.
  - destruct Δ as [| [y b] Δ']; simpl in HE.
    + destruct (env_cons_inv _ _ _ _ _ _ HE) as [HY [Hb HE1]].
      injection Hb as HT. subst T. simpl. rewrite <- HE1. exact Hwf.
    + destruct (env_cons_inv _ _ _ _ _ _ HE) as [HY [Hb HE1]].
      destruct b as [im0|Ty].
      * discriminate Hb.
      * injection Hb as HT. subst Ty. rewrite HY in Hdom.
        apply wf_env_typ.
        -- apply IH with (x:=x) (T1:=T1) (E0:=E0). exact HE1.
        -- apply WFS_remove_typ with (Δ:=Δ') (x:=x) (T1:=T1) (E0:=E0).
           rewrite HE1 in HW. exact HW.
        -- intro Hc. apply Hdom. rewrite HE1.
           apply binds_In_inv in Hc. destruct Hc as [b' Hb'].
           exact (binds_In binding y b' (Δ' ++ x ~ bind_typ T1 ++ E0)
                    (binds_insert_mid Δ' x T1 E0 y b' Hb')).
Qed.

Lemma Sub_strengthen_typ_gen : forall im cm evs E A B, Sub im cm evs E A B ->
  forall (Δ:env) (x:atom) (T1:typ) (E0:env), E = Δ ++ x ~ bind_typ T1 ++ E0 ->
  Sub im cm evs (Δ ++ E0) A B.
Proof.
  intros im cm evs E A B H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E X im0 Hwf Hb
                 | E X im0 Hwf Hb
                 | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm0 im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | im0 cm0 evs0 evs' E A1 A2 Hs IHs Heq];
    intros Δ x T1 E0 HE.
  - apply Sa_nat. exact (wf_env_remove_typ E Hwf Δ x T1 E0 HE).
  - apply Sa_top_eq. exact (wf_env_remove_typ E Hwf Δ x T1 E0 HE).
  - apply Sa_top_lt.
    + exact (wf_env_remove_typ E Hwf Δ x T1 E0 HE).
    + apply WFS_remove_typ with (Δ:=Δ) (x:=x) (T1:=T1) (E0:=E0). rewrite HE in HW. exact HW.
    + assumption.
  - apply Sa_fvar_pos.
    + exact (wf_env_remove_typ E Hwf Δ x T1 E0 HE).
    + rewrite HE in Hb. apply binds_sub_remove_typ in Hb. exact Hb.
  - apply Sa_fvar_neg.
    + exact (wf_env_remove_typ E Hwf Δ x T1 E0 HE).
    + rewrite HE in Hb. apply binds_sub_remove_typ in Hb. exact Hb.
  - eapply Sa_arrow.
    + apply (IH1 Δ x T1 E0). exact HE.
    + apply (IH2 Δ x T1 E0). exact HE.
    + apply Hc.
  - apply Sa_rec_lt with (L:=L). intros Y HY.
    apply (IH Y HY (Y ~ bind_sub im0 ++ Δ) x T1 E0). rewrite HE. reflexivity.
  - apply Sa_rec_eq_notin with (L:=L). intros Y HY.
    apply (IH Y HY (Y ~ bind_sub im0 ++ Δ) x T1 E0). rewrite HE. reflexivity.
  - apply Sa_rec_eq_in with (L:=L). intros Y HY.
    apply (IH Y HY (Y ~ bind_sub im0 ++ Δ) x T1 E0). rewrite HE. reflexivity.
  - apply Sa_evs_proper with (evs:=evs0); [apply (IHs Δ x T1 E0); exact HE|exact Heq].
Qed.

Lemma Sub_strengthen_typ : forall (x:atom) (T1:typ) (G:env) im cm evs A B,
  Sub im cm evs (x ~ bind_typ T1 ++ G) A B -> Sub im cm evs G A B.
Proof.
  intros x T1 G im cm evs A B H.
  change (Sub im cm evs (nil ++ G) A B).
  apply (Sub_strengthen_typ_gen im cm evs (x ~ bind_typ T1 ++ G) A B H nil x T1 G).
  reflexivity.
Qed.

(* ============================================================ *)
(* Freshness facts for wf environments with a middle binder      *)
(* ============================================================ *)

Lemma wf_env_head_fresh : forall (z:atom) c (E:env), wf_env ((z,c)::E) -> z \notin dom E.
Proof.
  intros z c E H. inversion H; subst; assumption.
Qed.

Lemma wf_env_prefix_fresh : forall (Δ:env) (x:atom) (T1:typ) (G:env) y b,
  wf_env (Δ ++ x ~ bind_typ T1 ++ G) -> binds y b Δ ->
  y \notin dom (x ~ bind_typ T1 ++ G).
Proof.
  induction Δ as [| [z c] Δ' IH]; intros x T1 G y b Hwf Hb.
  - rewrite binds_nil_iff in Hb. destruct Hb.
  - simpl in Hb. destruct Hb as [Heq|Hb].
    + injection Heq as Hy Hc. subst y. subst b.
      assert (Hfr : z \notin dom (Δ' ++ x ~ bind_typ T1 ++ G)).
      { apply wf_env_head_fresh with (c:=c). simpl. exact Hwf. }
      intro Hc'. apply Hfr.
      apply binds_In_inv in Hc'. destruct Hc' as [b' Hb'].
      exact (binds_In binding z b' (Δ' ++ x ~ bind_typ T1 ++ G)
               (binds_app_3 binding z b' Δ' (x ~ bind_typ T1 ++ G) Hb')).
    + apply (IH x T1 G y b).
      * apply wf_env_cons_inv with (x:=z) (b:=c). simpl. exact Hwf.
      * exact Hb.
Qed.

Lemma wf_env_mid_notin_prefix : forall (Δ:env) (x:atom) (T1:typ) (G:env),
  wf_env (Δ ++ x ~ bind_typ T1 ++ G) -> x \notin dom Δ.
Proof.
  intros Δ x T1 G H Hc.
  apply binds_In_inv in Hc. destruct Hc as [b Hb].
  pose proof (wf_env_prefix_fresh Δ x T1 G x b H Hb) as Hx.
  apply Hx. simpl. apply AtomSetImpl.add_1. reflexivity.
Qed.

Lemma wf_env_mid_notin_suffix : forall (Δ:env) (x:atom) (T1:typ) (G:env),
  wf_env (Δ ++ x ~ bind_typ T1 ++ G) -> x \notin dom G.
Proof.
  induction Δ as [| [z c] Δ' IH]; intros x T1 G Hwf.
  - apply wf_env_head_fresh with (c:=bind_typ T1). exact Hwf.
  - apply IH with (x:=x) (T1:=T1).
    apply wf_env_cons_inv with (x:=z) (b:=c). exact Hwf.
Qed.

Lemma binds_typ_mid : forall (Δ:env) (x:atom) (T1:typ) (G:env) T2,
  wf_env (Δ ++ x ~ bind_typ T1 ++ G) ->
  binds x (bind_typ T2) (Δ ++ x ~ bind_typ T1 ++ G) -> T2 = T1.
Proof.
  intros Δ x T1 G T2 Hwf Hb.
  apply binds_app_iff in Hb. destruct Hb as [Hb|Hb].
  - exfalso. apply (wf_env_mid_notin_prefix Δ x T1 G Hwf).
    exact (binds_In binding x (bind_typ T2) Δ Hb).
  - apply binds_cons_typ_inv in Hb. destruct Hb as [[Heq Hb]|Hb].
    + injection Hb as HT. exact HT.
    + exfalso. apply (wf_env_mid_notin_suffix Δ x T1 G Hwf).
      exact (binds_In binding x (bind_typ T2) G Hb).
Qed.

(* ============================================================ *)
(* Term-level opening and substitution identities                *)
(* ============================================================ *)

Fixpoint has_bvar_exp (k:nat) (e:exp) {struct e} : bool :=
  match e with
  | exp_bvar i => if k == i then true else false
  | exp_fvar _ => false
  | exp_abs _ e0 => has_bvar_exp (S k) e0
  | exp_app e1 e2 => orb (has_bvar_exp k e1) (has_bvar_exp k e2)
  | exp_nat => false
  | exp_unfold _ e0 => has_bvar_exp k e0
  | exp_fold _ e0 => has_bvar_exp k e0
  end.

Lemma open_ee_no_bvar : forall e k u, has_bvar_exp k e = false ->
  open_ee_rec k u e = e.
Proof.
  induction e; intros k u H; simpl in *.
  - destruct (k == n); [discriminate H|reflexivity].
  - reflexivity.
  - rewrite IHe. reflexivity. assumption.
  - apply orb_false_iff in H. destruct H as [H1 H2].
    rewrite (IHe1 k u H1), (IHe2 k u H2). reflexivity.
  - reflexivity.
  - rewrite IHe. reflexivity. assumption.
  - rewrite IHe. reflexivity. assumption.
Qed.

Lemma has_bvar_exp_open_fvar : forall e k x i, i <> k ->
  has_bvar_exp i (open_ee_rec k (exp_fvar x) e) = has_bvar_exp i e.
Proof.
  induction e; intros k x i Hneq; simpl.
  - destruct (k == n) as [e1|ne1].
    + assert (n = k) by (symmetry; exact e1). subst n.
      destruct (i == k) as [e2|ne2].
      * exfalso. apply Hneq. exact e2.
      * reflexivity.
    + reflexivity.
  - reflexivity.
  - apply IHe. intro Hc. apply Hneq. inversion Hc. reflexivity.
  - rewrite IHe1 by exact Hneq. rewrite IHe2 by exact Hneq. reflexivity.
  - reflexivity.
  - apply IHe. intro Hc. apply Hneq. inversion Hc. reflexivity.
  - apply IHe. intro Hc. apply Hneq. inversion Hc. reflexivity.
Qed.

Lemma expr_no_bvar : forall e, expr e -> forall k, has_bvar_exp k e = false.
Proof.
  intros e H.
  induction H as [x | e0 L T Hpre IH Ht | e1 e2 H1 IH1 H2 IH2 | | T e0 Ht Hpre IH | T e0 Ht Hpre IH].
  - intros k. reflexivity.
  - intros k. destruct (exists_fresh_notin L) as [x Hx].
    specialize (IH x Hx (S k)).
    assert (Hopen : has_bvar_exp (S k) (open_ee_rec 0 (exp_fvar x) e0) = false)
      by exact IH.
    rewrite (has_bvar_exp_open_fvar e0 0 x (S k)) in Hopen by discriminate.
    exact Hopen.
  - intros k. simpl. rewrite IH1, IH2. reflexivity.
  - intros k. reflexivity.
  - intros k. exact (IH k).
  - intros k. exact (IH k).
Qed.

Lemma expr_open_fvar_id : forall e, expr e -> forall k x,
  open_ee_rec k (exp_fvar x) e = e.
Proof.
  intros. apply open_ee_no_bvar. apply expr_no_bvar. assumption.
Qed.

Lemma open_ee_eq_subst_ee : forall e x v,
  x \notin fv_exp e ->
  forall k, open_ee_rec k v e = subst_ee x v (open_ee_rec k (exp_fvar x) e).
Proof.
  induction e; intros x v Hfv k; simpl in *.
  - destruct (k == n) as [e1|ne1].
    + simpl. destruct (x == x) as [e2|ne2]; [reflexivity|exfalso; apply ne2; reflexivity].
    + reflexivity.
  - destruct (a == x) as [e1|ne1].
    + exfalso. apply Hfv. rewrite e1. apply AtomSetImpl.singleton_2. reflexivity.
    + reflexivity.
  - rewrite (IHe x v Hfv (S k)). reflexivity.
  - rewrite (IHe1 x v) by (apply notin_union_1 in Hfv; exact Hfv).
    rewrite (IHe2 x v) by (apply notin_union_2 in Hfv; exact Hfv).
    reflexivity.
  - reflexivity.
  - rewrite (IHe x v Hfv k). reflexivity.
  - rewrite (IHe x v Hfv k). reflexivity.
Qed.

Lemma open_ee_subst_ee_comm : forall e x v y,
  y <> x -> y \notin fv_exp v -> y \notin fv_exp e -> expr v ->
  forall k, open_ee_rec k (exp_fvar y) (subst_ee x v e) =
            subst_ee x v (open_ee_rec k (exp_fvar y) e).
Proof.
  induction e; intros x v y Hxy Hyv Hye HvEv k; simpl in *.
  - destruct (k == n) as [e1|ne1].
    + simpl. destruct (y == x) as [e2|ne2].
      * exfalso. apply Hxy. exact e2.
      * reflexivity.
    + reflexivity.
  - destruct (a == x) as [e1|ne1].
    + subst a. simpl. rewrite expr_open_fvar_id; [|exact HvEv].
      destruct (x == x) as [e2|ne2]; [reflexivity|exfalso; apply ne2; reflexivity].
    + simpl. destruct (y == x) as [e2|ne2].
      * exfalso. apply Hxy. exact e2.
      * reflexivity.
  - rewrite (IHe x v y Hxy Hyv Hye HvEv (S k)). reflexivity.
  - assert (H1 : y \notin fv_exp e1) by (apply notin_union_1 in Hye; exact Hye).
    assert (H2 : y \notin fv_exp e2) by (apply notin_union_2 in Hye; exact Hye).
    rewrite (IHe1 x v y Hxy Hyv H1 HvEv k).
    rewrite (IHe2 x v y Hxy Hyv H2 HvEv k).
    reflexivity.
  - reflexivity.
  - rewrite (IHe x v y Hxy Hyv Hye HvEv k). reflexivity.
  - rewrite (IHe x v y Hxy Hyv Hye HvEv k). reflexivity.
Qed.

Lemma value_expr : forall v, value v -> expr v.
Proof.
  intros v H. induction H as [t1 T Hexpr | | T e Ht Hve IH].
  - exact Hexpr.
  - apply lc_nat.
  - apply lc_fold with (T:=T); assumption.
Qed.

Lemma subst_ee_neq : forall (x y:atom) v, y <> x -> subst_ee x v (exp_fvar y) = exp_fvar y.
Proof.
  intros. simpl. destruct (y == x) as [e|ne].
  - exfalso. apply H. exact e.
  - reflexivity.
Qed.

Lemma subst_ee_same : forall (x:atom) v, subst_ee x v (exp_fvar x) = v.
Proof.
  intros. simpl. rewrite eq_dec_refl. reflexivity.
Qed.


(* ============================================================ *)
(* Closedness of subtyping judgements in the empty environment   *)
(* ============================================================ *)

Lemma fv_tt_mem_open : forall A k U X,
  X \in fv_tt A -> X \in fv_tt (open_tt_rec k U A) \/ X \in fv_tt U.
Proof.
  induction A; intros k U X HX; simpl in *.
  - exfalso. exact (AtomSetImpl.empty_1 HX).
  - exfalso. exact (AtomSetImpl.empty_1 HX).
  - exfalso. exact (AtomSetImpl.empty_1 HX).
  - left. exact HX.
  - apply IHA. exact HX.
  - apply AtomSetImpl.union_1 in HX. destruct HX as [HX|HX].
    + destruct (IHA1 k U X HX) as [HX'|HX'].
      * left. apply AtomSetImpl.union_2. exact HX'.
      * right. exact HX'.
    + destruct (IHA2 k U X HX) as [HX'|HX'].
      * left. apply AtomSetImpl.union_3. exact HX'.
      * right. exact HX'.
Qed.

Lemma WFS_fv_binds : forall E A, WFS E A -> forall X, X \in fv_tt A ->
  exists im, binds X (bind_sub im) E.
Proof.
  intros E A H.
  induction H as [E | E | Y E im Hb | E A B HA IHA HB IHB | L E A im HP IH];
    intros X HX.
  - exfalso. exact (AtomSetImpl.empty_1 HX).
  - exfalso. exact (AtomSetImpl.empty_1 HX).
  - apply AtomSetImpl.singleton_1 in HX. subst Y. exists im. exact Hb.
  - apply AtomSetImpl.union_1 in HX. destruct HX as [HX|HX].
    + apply IHA. exact HX.
    + apply IHB. exact HX.
  - destruct (exists_fresh_notin (L \u fv_tt A)) as [Y HY].
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HYfv : Y \notin fv_tt A) by (apply notin_union_2 in HY; exact HY).
    assert (HX' : X \in fv_tt (open_tt A Y)).
    { destruct (fv_tt_mem_open A 0 (typ_fvar Y) X HX) as [HX0|HX0]; [exact HX0|].
      exfalso. apply HYfv. apply AtomSetImpl.singleton_1 in HX0.
      rewrite <- HX0 in HX. exact HX. }
    destruct (IH Y HYL X HX') as [im0 Hb].
    apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
    + exfalso. apply HYfv. subst X. exact HX.
    + exists im0. exact Hb.
Qed.

Lemma Sub_fv_bound : forall im cm evs E A B, Sub im cm evs E A B ->
  (forall X, X \in fv_tt A -> exists i, binds X (bind_sub i) E) /\
  (forall X, X \in fv_tt B -> exists i, binds X (bind_sub i) E).
Proof.
  intros im cm evs E A B H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E Xa im0 Hwf Hb
                 | E Xa im0 Hwf Hb
                 | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm0 im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | im0 cm0 evs0 evs' E A1 A2 Hs IHs Heq].
  - split; [intros X HX; exfalso; exact (AtomSetImpl.empty_1 HX)|].
    intros X HX. exfalso. exact (AtomSetImpl.empty_1 HX).
  - split; [intros X HX; exfalso; exact (AtomSetImpl.empty_1 HX)|].
    intros X HX. exfalso. exact (AtomSetImpl.empty_1 HX).
  - split; [intros X HX; apply (WFS_fv_binds E A0 HW X HX)|].
    intros X HX. exfalso. exact (AtomSetImpl.empty_1 HX).
  - split; intros X HX.
    + apply AtomSetImpl.singleton_1 in HX. exists im0. rewrite <- HX. exact Hb.
    + apply AtomSetImpl.singleton_1 in HX. exists im0. rewrite <- HX. exact Hb.
  - split; intros X HX.
    + apply AtomSetImpl.singleton_1 in HX. exists (flip_im im0). rewrite <- HX. exact Hb.
    + apply AtomSetImpl.singleton_1 in HX. exists (flip_im im0). rewrite <- HX. exact Hb.
  - destruct IH1 as [IHB1 IHA1]. destruct IH2 as [IHA2 IHB2]. split.
    + intros X HX. apply AtomSetImpl.union_1 in HX. destruct HX as [HX|HX].
      * apply IHA1. exact HX.
      * apply IHA2. exact HX.
    + intros X HX. apply AtomSetImpl.union_1 in HX. destruct HX as [HX|HX].
      * apply IHB1. exact HX.
      * apply IHB2. exact HX.
  - split; intros X HX; simpl in HX.
    + destruct (exists_fresh_notin (L \u fv_tt A1)) as [Y HY].
      assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
      assert (HYfv : Y \notin fv_tt A1) by (apply notin_union_2 in HY; exact HY).
      assert (HX' : X \in fv_tt (open_tt A1 Y)).
      { destruct (fv_tt_mem_open A1 0 (typ_fvar Y) X HX) as [HX0|HX0]; [exact HX0|].
        exfalso. apply HYfv. apply AtomSetImpl.singleton_1 in HX0.
        rewrite <- HX0 in HX. exact HX. }
      destruct (proj1 (IH Y HYL) X HX') as [i Hb].
      apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
      * exfalso. apply HYfv. subst X. exact HX.
      * exists i. exact Hb.
    + destruct (exists_fresh_notin (L \u fv_tt A2)) as [Y HY].
      assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
      assert (HYfv : Y \notin fv_tt A2) by (apply notin_union_2 in HY; exact HY).
      assert (HX' : X \in fv_tt (open_tt A2 Y)).
      { destruct (fv_tt_mem_open A2 0 (typ_fvar Y) X HX) as [HX0|HX0]; [exact HX0|].
        exfalso. apply HYfv. apply AtomSetImpl.singleton_1 in HX0.
        rewrite <- HX0 in HX. exact HX. }
      destruct (proj2 (IH Y HYL) X HX') as [i Hb].
      apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
      * exfalso. apply HYfv. subst X. exact HX.
      * exists i. exact Hb.
  - split; intros X HX; simpl in HX.
    + destruct (exists_fresh_notin (L \u fv_tt A1)) as [Y HY].
      assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
      assert (HYfv : Y \notin fv_tt A1) by (apply notin_union_2 in HY; exact HY).
      assert (HX' : X \in fv_tt (open_tt A1 Y)).
      { destruct (fv_tt_mem_open A1 0 (typ_fvar Y) X HX) as [HX0|HX0]; [exact HX0|].
        exfalso. apply HYfv. apply AtomSetImpl.singleton_1 in HX0.
        rewrite <- HX0 in HX. exact HX. }
      destruct (proj1 (IH Y HYL) X HX') as [i Hb].
      apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
      * exfalso. apply HYfv. subst X. exact HX.
      * exists i. exact Hb.
    + destruct (exists_fresh_notin (L \u fv_tt A2)) as [Y HY].
      assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
      assert (HYfv : Y \notin fv_tt A2) by (apply notin_union_2 in HY; exact HY).
      assert (HX' : X \in fv_tt (open_tt A2 Y)).
      { destruct (fv_tt_mem_open A2 0 (typ_fvar Y) X HX) as [HX0|HX0]; [exact HX0|].
        exfalso. apply HYfv. apply AtomSetImpl.singleton_1 in HX0.
        rewrite <- HX0 in HX. exact HX. }
      destruct (proj2 (IH Y HYL) X HX') as [i Hb].
      apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
      * exfalso. apply HYfv. subst X. exact HX.
      * exists i. exact Hb.
  - split; intros X HX; simpl in HX.
    + destruct (exists_fresh_notin (L \u fv_tt A1)) as [Y HY].
      assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
      assert (HYfv : Y \notin fv_tt A1) by (apply notin_union_2 in HY; exact HY).
      assert (HX' : X \in fv_tt (open_tt A1 Y)).
      { destruct (fv_tt_mem_open A1 0 (typ_fvar Y) X HX) as [HX0|HX0]; [exact HX0|].
        exfalso. apply HYfv. apply AtomSetImpl.singleton_1 in HX0.
        rewrite <- HX0 in HX. exact HX. }
      destruct (proj1 (IH Y HYL) X HX') as [i Hb].
      apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
      * exfalso. apply HYfv. subst X. exact HX.
      * exists i. exact Hb.
    + destruct (exists_fresh_notin (L \u fv_tt A2)) as [Y HY].
      assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
      assert (HYfv : Y \notin fv_tt A2) by (apply notin_union_2 in HY; exact HY).
      assert (HX' : X \in fv_tt (open_tt A2 Y)).
      { destruct (fv_tt_mem_open A2 0 (typ_fvar Y) X HX) as [HX0|HX0]; [exact HX0|].
        exfalso. apply HYfv. apply AtomSetImpl.singleton_1 in HX0.
        rewrite <- HX0 in HX. exact HX. }
      destruct (proj2 (IH Y HYL) X HX') as [i Hb].
      apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
      * exfalso. apply HYfv. subst X. exact HX.
      * exists i. exact Hb.
  - exact IHs.
Qed.

Lemma Sub_closed_nil_left : forall im cm evs A B,
  Sub im cm evs nil A B -> forall X, X \notin fv_tt A.
Proof.
  intros im cm evs A B H X HX.
  destruct (proj1 (Sub_fv_bound im cm evs nil A B H) X HX) as [i Hb].
  rewrite binds_nil_iff in Hb. exact Hb.
Qed.

Lemma Sub_closed_nil_right : forall im cm evs A B,
  Sub im cm evs nil A B -> forall X, X \notin fv_tt B.
Proof.
  intros im cm evs A B H X HX.
  destruct (proj2 (Sub_fv_bound im cm evs nil A B H) X HX) as [i Hb].
  rewrite binds_nil_iff in Hb. exact Hb.
Qed.

(* Evidence variables of a subtyping derivation are bound as subtypes. *)
Lemma Sub_evs_bound : forall im cm evs E A B, Sub im cm evs E A B ->
  forall Y, Y \in evs -> exists i, binds Y (bind_sub i) E.
Proof.
  intros im cm evs E A B H.
  induction H as [E im0 Hwf
                 | E im0 Hwf
                 | E im0 A0 Hwf HW Hne
                 | E Xa im0 Hwf Hb
                 | E Xa im0 Hwf Hb
                 | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm0 im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | L A1 A2 evs0 E im0 HP IH
                 | im0 cm0 evs0 evs' E A1 A2 Hs IHs Heq];
    intros Y HY.
  - exfalso. exact (AtomSetImpl.empty_1 HY).
  - exfalso. exact (AtomSetImpl.empty_1 HY).
  - exfalso. exact (AtomSetImpl.empty_1 HY).
  - exfalso. exact (AtomSetImpl.empty_1 HY).
  - apply AtomSetImpl.singleton_1 in HY. subst Xa. exists (flip_im im0). exact Hb.
  - apply AtomSetImpl.union_1 in HY. destruct HY as [HY|HY].
    + apply IH1. exact HY.
    + apply IH2. exact HY.
  - (* rec_lt : conclusion evs = evs0 *)
    destruct (exists_fresh_notin (L \u evs0 \u dom E)) as [Z HZ].
    assert (HZL : Z \notin L) by (apply notin_union_1 in HZ; exact HZ).
    assert (HZe : Z \notin evs0)
      by (apply notin_union_2 in HZ; apply notin_union_1 in HZ; exact HZ).
    assert (HZd : Z \notin dom E)
      by (apply notin_union_2 in HZ; apply notin_union_2 in HZ; exact HZ).
    destruct (IH Z HZL Y HY) as [i Hb].
    apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
    + exfalso. apply HZe. subst Y. exact HY.
    + exists i. exact Hb.
  - (* rec_eq_notin *)
    destruct (exists_fresh_notin (L \u evs0 \u dom E)) as [Z HZ].
    assert (HZL : Z \notin L) by (apply notin_union_1 in HZ; exact HZ).
    assert (HZe : Z \notin evs0)
      by (apply notin_union_2 in HZ; apply notin_union_1 in HZ; exact HZ).
    assert (HZd : Z \notin dom E)
      by (apply notin_union_2 in HZ; apply notin_union_2 in HZ; exact HZ).
    destruct (IH Z HZL Y HY) as [i Hb].
    apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
    + exfalso. apply HZe. subst Y. exact HY.
    + exists i. exact Hb.
  - (* rec_eq_in : conclusion evs = evs0 union fv_tt A1 *)
    apply AtomSetImpl.union_1 in HY. destruct HY as [HY|HY].
    + destruct (exists_fresh_notin (L \u evs0 \u dom E)) as [Z HZ].
      assert (HZL : Z \notin L) by (apply notin_union_1 in HZ; exact HZ).
      assert (HZe : Z \notin evs0)
        by (apply notin_union_2 in HZ; apply notin_union_1 in HZ; exact HZ).
      assert (HZd : Z \notin dom E)
        by (apply notin_union_2 in HZ; apply notin_union_2 in HZ; exact HZ).
      destruct (IH Z HZL Y (AtomSetImpl.add_2 Z HY)) as [i Hb].
      apply binds_cons_sub_inv in Hb. destruct Hb as [[Heq Hbe]|Hb].
      * exfalso. apply HZe. subst Y. exact HY.
      * exists i. exact Hb.
    + (* Y in fv_tt A1 = fv_tt (mu A1) : use Sub_fv_bound of the conclusion *)
      exact (proj1 (Sub_fv_bound im0 Eq (AtomSetImpl.union evs0 (fv_tt A1)) E (typ_mu A1) (typ_mu A2)
                     (Sa_rec_eq_in L A1 A2 evs0 E im0 HP)) Y HY).
  - apply (IHs Y). apply Heq. exact HY.
Qed.

Lemma Sub_evs_nil : forall im cm evs A B, Sub im cm evs nil A B ->
  forall Y, Y \notin evs.
Proof.
  intros im cm evs A B H Y HY.
  destruct (Sub_evs_bound im cm evs nil A B H Y HY) as [i Hb].
  rewrite binds_nil_iff in Hb. exact Hb.
Qed.

(* The argument of a typed fold has the folding annotation's unfolding type. *)
Lemma typing_fold_arg : forall G e T, typing G e T ->
  forall A v, e = exp_fold (typ_mu A) v -> typing G v (open_tt A (typ_mu A)).
Proof.
  intros G e T H.
  induction H as [G0 Hwf
                 | G0 x0 T0 Hwf Hb
                 | L G0 T1 e0 T2 HP IH
                 | G0 e1 e2 T2 T1 H1 IH1 H2 IH2
                 | G0 AA e0 H1 IH1 Hw
                 | G0 T0 e0 H1 IH1
                 | G0 T0 e0 S evs cm H1 IH1 Hs];
    intros A v He.
  - discriminate He.
  - discriminate He.
  - discriminate He.
  - discriminate He.
  - injection He as HA Hv. subst AA. subst e0. exact H1.
  - discriminate He.
  - apply (IH1 A v He).
Qed.

(* Removing a fresh subtype binder from the middle of an environment. *)
Lemma binds_sub_remove_sub : forall (Δ:env) (x:atom) (im0:IsoMode) (E0:env) Z i,
  Z <> x ->
  (binds Z (bind_sub i) (Δ ++ x ~ bind_sub im0 ++ E0) <->
   binds Z (bind_sub i) (Δ ++ E0)).
Proof.
  intros Δ x im0 E0 Z i Hne. split.
  - intro H1. apply binds_app_iff in H1. destruct H1 as [H1|H1].
    + apply binds_app_iff. left. exact H1.
    + apply binds_cons_sub_inv in H1. destruct H1 as [[Heq Hbe]|H1].
      * exfalso. apply Hne. exact Heq.
      * apply binds_app_iff. right. exact H1.
  - intro H1. apply binds_app_iff in H1. destruct H1 as [H1|H1].
    + apply binds_app_iff. left. exact H1.
    + apply binds_app_iff. right. apply binds_cons_3. exact H1.
Qed.

Lemma WFS_remove_sub_notin : forall (Δ:env) (x:atom) (im0:IsoMode) (E0:env) A,
  WFS (Δ ++ x ~ bind_sub im0 ++ E0) A -> x \notin fv_tt A -> WFS (Δ ++ E0) A.
Proof.
  intros. eapply WFS_env_impl_on; [exact H|].
  intros Z i HZ Hb.
  eapply binds_sub_remove_sub; [|exact Hb].
  intro Hc. apply H0. subst Z. exact HZ.
Qed.

Lemma binds_insert_mid_any : forall (Δ:env) (x:atom) (b:binding) (E0:env) y c,
  binds y c (Δ ++ E0) -> binds y c (Δ ++ x ~ b ++ E0).
Proof.
  intros. apply binds_app_iff in H. apply binds_app_iff.
  destruct H as [H|H]; [left; exact H|right].
  apply binds_cons_3. exact H.
Qed.

Lemma WFS_insert_mid : forall (Δ:env) (x:atom) b (E0:env) A,
  WFS (Δ ++ E0) A -> WFS (Δ ++ x ~ b ++ E0) A.
Proof.
  intros. eapply WFS_env_impl_on; [exact H|].
  intros Z i HZ Hb. apply binds_insert_mid_any. exact Hb.
Qed.

Lemma Sub_insert : forall im cm evs (E:env) A B, Sub im cm evs E A B ->
  forall (Δ:env) (x:atom) (b:binding) (E0:env), E = Δ ++ E0 ->
  wf_env (Δ ++ x ~ b ++ E0) -> Sub im cm evs (Δ ++ x ~ b ++ E0) A B.
Proof.
  intros im cm evs E A B H.
  induction H as [Ec im0 Hwf
                 | Ec im0 Hwf
                 | Ec im0 A0 Hwf HW Hne
                 | Ec X0 im0 Hwf Hb
                 | Ec X0 im0 Hwf Hb
                 | Ec A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm0 im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 Ec im0 HP IH
                 | L A1 A2 evs0 Ec im0 HP IH
                 | L A1 A2 evs0 Ec im0 HP IH
                 | im0 cm0 evs0 evs' Ec A1 A2 Hs IHs Heq];
    intros Δ x b E0 HE Hwf2.
  - apply Sa_nat. exact Hwf2.
  - apply Sa_top_eq. exact Hwf2.
  - apply Sa_top_lt.
    + exact Hwf2.
    + apply WFS_insert_mid. rewrite <- HE. exact HW.
    + exact Hne.
  - apply Sa_fvar_pos.
    + exact Hwf2.
    + rewrite HE in Hb. apply binds_insert_mid_any. exact Hb.
  - apply Sa_fvar_neg.
    + exact Hwf2.
    + rewrite HE in Hb. apply binds_insert_mid_any. exact Hb.
  - eapply Sa_arrow.
    + apply (IH1 Δ x b E0 HE Hwf2).
    + apply (IH2 Δ x b E0 HE Hwf2).
    + exact Hc.
  - apply Sa_rec_lt with (L := L \u dom (Δ ++ x ~ b ++ E0)). intros Y HY.
    apply (IH Y) with (Δ := Y ~ bind_sub im0 ++ Δ) (x:=x) (b:=b) (E0:=E0).
    + apply notin_union_1 in HY. exact HY.
    + rewrite HE. reflexivity.
    + apply wf_env_sub with (X:=Y) (im:=im0). exact Hwf2.
      apply notin_union_2 in HY. exact HY.
  - apply Sa_rec_eq_notin with (L := L \u dom (Δ ++ x ~ b ++ E0)). intros Y HY.
    apply (IH Y) with (Δ := Y ~ bind_sub im0 ++ Δ) (x:=x) (b:=b) (E0:=E0).
    + apply notin_union_1 in HY. exact HY.
    + rewrite HE. reflexivity.
    + apply wf_env_sub with (X:=Y) (im:=im0). exact Hwf2.
      apply notin_union_2 in HY. exact HY.
  - apply Sa_rec_eq_in with (L := L \u dom (Δ ++ x ~ b ++ E0)). intros Y HY.
    apply (IH Y) with (Δ := Y ~ bind_sub im0 ++ Δ) (x:=x) (b:=b) (E0:=E0).
    + apply notin_union_1 in HY. exact HY.
    + rewrite HE. reflexivity.
    + apply wf_env_sub with (X:=Y) (im:=im0). exact Hwf2.
      apply notin_union_2 in HY. exact HY.
  - apply Sa_evs_proper with (evs:=evs0).
    + apply (IHs Δ x b E0 HE Hwf2).
    + exact Heq.
Qed.

Lemma subst_tt_top_inv : forall A X U,
  U <> typ_top -> subst_tt X U A = typ_top -> A = typ_top.
Proof.
  induction A; intros X U HU H; simpl in *.
  - reflexivity.
  - discriminate H.
  - discriminate H.
  - destruct (a == X) as [e|ne].
    + subst a. rewrite H in HU. exfalso. apply HU. reflexivity.
    + discriminate H.
  - discriminate H.
  - discriminate H.
Qed.

Lemma WFS_subst_mid : forall (Ec:env) A, WFS Ec A ->
  forall (Δ:env) (X:atom) (im:IsoMode) (E0:env), Ec = Δ ++ X ~ bind_sub im ++ E0 ->
  forall U, type U -> WFS (Δ ++ E0) U -> WFS (Δ ++ E0) (subst_tt X U A).
Proof.
  intros Ec A H.
  induction H as [Ec0 | Ec0 | Y Ec0 im0 Hb | Ec0 A1 A2 HA IHA HB IHB | L Ec0 A0 im0 HP IH];
    intros Δ X im E0 HE U HTU HWU.
  - constructor.
  - constructor.
  - simpl. destruct (Y == X) as [e|ne].
    + subst Y. exact HWU.
    + apply WFS_fvar with (im:=im0). rewrite HE in Hb.
      exact (proj1 (binds_sub_remove_sub Δ X im E0 Y im0 ne) Hb).
  - simpl. apply WFS_arrow; [apply (IHA Δ X im E0 HE U HTU HWU)|apply (IHB Δ X im E0 HE U HTU HWU)].
  - simpl. apply WFS_rec with (L:= L \u {{ X }}) (im:=im0). intros Z HZ.
    assert (HZX : Z <> X).
    { intro Hc. apply HZ. simpl. apply AtomSetImpl.union_3.
      apply AtomSetImpl.singleton_2. symmetry. exact Hc. }
    assert (HZL : Z \notin L) by (apply notin_union_1 in HZ; exact HZ).
    change (WFS (Z ~ bind_sub im0 ++ Δ ++ E0)
              (open_tt_rec 0 (typ_fvar Z) (subst_tt X U A0))).
    rewrite open_tt_subst_tt; [| intro Hc; apply HZX; symmetry; exact Hc | exact HTU].
    apply (IH Z HZL (Z ~ bind_sub im0 ++ Δ) X im E0).
    + rewrite HE. reflexivity.
    + exact HTU.
    + apply WFS_weaken with (x:=Z) (b:=bind_sub im0). exact HWU.
Qed.

Lemma wf_env_mid_fresh : forall (Δ:env) (x:atom) b (E0:env),
  wf_env (Δ ++ x ~ b ++ E0) -> x \notin dom Δ.
Proof.
  induction Δ as [| [y c] Δ' IH]; intros x b E0 Hwf.
  - simpl. apply notin_empty_1.
  - simpl. intro Hc.
    assert (Hy : y \notin dom (Δ' ++ x ~ b ++ E0)).
    { apply wf_env_head_fresh with (c:=c). simpl. exact Hwf. }
    assert (Hxy : x <> y).
    { intro Hc2. apply Hy. rewrite <- Hc2.
      exact (binds_In binding x b (Δ' ++ x ~ b ++ E0)
               (binds_app_3 binding x b Δ' (x ~ b ++ E0) (or_introl eq_refl))). }
    assert (Hx' : x \in dom Δ') by (exact (AtomSetImpl.add_3 (s:=dom Δ') (x:=y) (y:=x) (fun Hc3 => Hxy (eq_sym Hc3)) Hc)).
    exact (IH x b E0 (wf_env_cons_inv y c (Δ' ++ x ~ b ++ E0) Hwf) Hx').
Qed.

Lemma subst_tt_notin : forall T X U,
  X \notin fv_tt T -> subst_tt X U T = T.
Proof.
  induction T; intros X U H; simpl in *.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (a == X) as [e|ne]; [|reflexivity].
    exfalso. apply H. rewrite e. apply AtomSetImpl.singleton_2. reflexivity.
  - rewrite (IHT X U H). reflexivity.
  - rewrite (IHT1 X U (notin_union_1 X (fv_tt T1) (fv_tt T2) H)).
    rewrite (IHT2 X U (notin_union_2 X (fv_tt T1) (fv_tt T2) H)). reflexivity.
Qed.

Definition sL (im : IsoMode) (U V : typ) : typ :=
  match im with Pos => U | Neg => V end.
Definition sR (im : IsoMode) (U V : typ) : typ :=
  match im with Pos => V | Neg => U end.

Lemma Sub_subst_mode : forall (X:atom) im cm evs (Ec:env) A B, Sub im cm evs Ec A B ->
  forall (Δ:env), Ec = Δ ++ X ~ bind_sub Pos ->
  X \notin evs ->
  forall U V, type U -> type V -> X \notin fv_tt U -> X \notin fv_tt V ->
  U <> typ_top -> V <> typ_top ->
  WFS Δ U -> WFS Δ V -> Sub Pos Eq emp Δ U V ->
  Sub im cm evs Δ (subst_tt X (sL im U V) A) (subst_tt X (sR im U V) B).
Proof.
  intros X im cm evs Ec A B H.
  induction H as [Ec0 im0 Hwf
                 | Ec0 im0 Hwf
                 | Ec0 im0 A0 Hwf HW Hne
                 | Ec0 X0 im0 Hwf Hb
                 | Ec0 X0 im0 Hwf Hb
                 | Ec0 A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm0 im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 Ec0 im0 HP IH
                 | L A1 A2 evs0 Ec0 im0 HP IH
                 | L A1 A2 evs0 Ec0 im0 HP IH
                 | im0 cm0 evs0 evs' Ec0 A1 A2 Hs IHs Heq];
    intros Δ HE HX U V HTU HTV HXU HXV HUt HVt HWU HWV HUV.
  - apply Sa_nat. exact (Sub_wf_env _ _ _ _ _ _ HUV).
  - apply Sa_top_eq. exact (Sub_wf_env _ _ _ _ _ _ HUV).
  - apply Sa_top_lt.
    + exact (Sub_wf_env _ _ _ _ _ _ HUV).
    + destruct im0.
      * (* Neg *) simpl. rewrite HE in HW.
        rewrite <- (app_nil_r Δ).
        eapply WFS_subst_mid with (X:=X) (im:=Pos) (E0:=nil) (U:=V) (A:=A0).
        -- exact HW.
        -- reflexivity.
        -- exact HTV.
        -- rewrite app_nil_r. exact HWV.
      * (* Pos *) simpl. rewrite HE in HW.
        rewrite <- (app_nil_r Δ).
        eapply WFS_subst_mid with (X:=X) (im:=Pos) (E0:=nil) (U:=U) (A:=A0).
        -- exact HW.
        -- reflexivity.
        -- exact HTU.
        -- rewrite app_nil_r. exact HWU.
    + destruct im0.
      * (* Neg *) simpl. intro Hc. apply Hne. exact (subst_tt_top_inv A0 X V HVt Hc).
      * (* Pos *) simpl. intro Hc. apply Hne. exact (subst_tt_top_inv A0 X U HUt Hc).
  - (* fvar_pos *)
    rewrite HE in Hb.
    assert (HXΔ : X \notin dom Δ).
    { apply (wf_env_mid_fresh Δ X (bind_sub Pos) empty). simpl.
      exact (eq_rect Ec0 (fun e => wf_env e) Hwf (Δ ++ X ~ bind_sub Pos) HE). }
    destruct (X0 == X) as [Heq|Hne] eqn:Hd.
    + simpl. rewrite Hd. simpl. subst X0.
      rewrite (binds_app_iff binding X (bind_sub im0) Δ (X ~ bind_sub Pos)) in Hb.
      destruct Hb as [HbΔ | HbX].
      * exfalso. exact (binds_dom_contradiction binding X (bind_sub im0) Δ HbΔ HXΔ).
      * apply binds_cons_iff in HbX. destruct HbX as [[Heq2 Hbe]|Hc].
        -- injection Hbe as Him. subst im0. simpl. exact HUV.
        -- destruct Hc.
    + simpl. rewrite Hd. simpl.
      apply Sa_fvar_pos.
      * exact (Sub_wf_env _ _ _ _ _ _ HUV).
      * rewrite (binds_app_iff binding X0 (bind_sub im0) Δ (X ~ bind_sub Pos)) in Hb.
        destruct Hb as [HbΔ | HbX].
        -- exact HbΔ.
        -- apply binds_cons_iff in HbX. destruct HbX as [[Heq2 Hbe]|Hc].
           ++ exfalso. apply Hne. exact Heq2.
           ++ destruct Hc.
  - (* fvar_neg *)
    rewrite HE in Hb. destruct (X0 == X) as [Heq|Hne] eqn:Hd.
    + subst X0. exfalso. apply HX.
      apply AtomSetImpl.singleton_2. reflexivity.
    + simpl. rewrite Hd. simpl.
      apply Sa_fvar_neg.
      * exact (Sub_wf_env _ _ _ _ _ _ HUV).
      * rewrite (binds_app_iff binding X0 (bind_sub (flip_im im0)) Δ (X ~ bind_sub Pos)) in Hb.
        destruct Hb as [HbΔ | HbX].
        -- exact HbΔ.
        -- apply binds_cons_iff in HbX. destruct HbX as [[Heq2 Hbe]|Hc].
           ++ exfalso. apply Hne. exact Heq2.
           ++ destruct Hc.
  - (* arrow *)
    destruct im0.
    + (* im0 = Neg *) simpl. eapply Sa_arrow.
      * apply (IH1 Δ HE). apply notin_union_1 in HX. exact HX.
        all: assumption.
      * apply (IH2 Δ HE). apply notin_union_2 in HX. exact HX.
        all: assumption.
      * exact Hc.
    + (* im0 = Pos *) simpl. eapply Sa_arrow.
      * apply (IH1 Δ HE). apply notin_union_1 in HX. exact HX.
        all: assumption.
      * apply (IH2 Δ HE). apply notin_union_2 in HX. exact HX.
        all: assumption.
      * exact Hc.
  - (* rec_lt *)
    apply Sa_rec_lt with (L := L \u {{ X }} \u dom Δ). intros Y HY.
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HYX : Y \notin {{ X }})
      by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
    assert (HYd : Y \notin dom Δ)
      by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
    assert (HYXeq : Y <> X)
      by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
    change (Sub im0 Lt evs0 (Y ~ bind_sub im0 ++ Δ)
              (open_tt (subst_tt X (sL im0 U V) A1) Y)
              (open_tt (subst_tt X (sR im0 U V) A2) Y)).
    assert (Heq1 : open_tt (subst_tt X (sL im0 U V) A1) Y =
                   subst_tt X (sL im0 U V) (open_tt A1 Y)).
    { unfold open_tt. apply open_tt_subst_tt.
      - symmetry. exact HYXeq.
      - destruct im0; simpl; assumption. }
    assert (Heq2 : open_tt (subst_tt X (sR im0 U V) A2) Y =
                   subst_tt X (sR im0 U V) (open_tt A2 Y)).
    { unfold open_tt. apply open_tt_subst_tt.
      - symmetry. exact HYXeq.
      - destruct im0; simpl; assumption. }
    rewrite Heq1, Heq2.
    apply (IH Y HYL (Y ~ bind_sub im0 ++ Δ)).
    + rewrite HE. rewrite app_assoc. reflexivity.
    + exact HX.
    + exact HTU.
    + exact HTV.
    + exact HXU.
    + exact HXV.
    + exact HUt.
    + exact HVt.
    + apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWU.
    + apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWV.
    + eapply (Sub_insert Pos Eq emp Δ U V HUV empty Y (bind_sub im0) Δ).
      * reflexivity.
      * apply wf_env_sub with (X:=Y) (im:=im0).
        -- exact (Sub_wf_env _ _ _ _ _ _ HUV).
        -- exact HYd.
  - (* rec_eq_notin *)
    apply Sa_rec_eq_notin with (L := L \u {{ X }} \u dom Δ). intros Y HY.
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HYX : Y \notin {{ X }})
      by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
    assert (HYd : Y \notin dom Δ)
      by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
    assert (HYXeq : Y <> X)
      by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
    simpl. unfold open_tt.
    rewrite open_tt_subst_tt; [| |].
    + rewrite open_tt_subst_tt; [| |].
      * apply (IH Y HYL (Y ~ bind_sub im0 ++ Δ)).
        -- rewrite HE. reflexivity.
        -- exact HX.
        -- exact HTU. -- exact HTV. -- exact HXU. -- exact HXV. -- exact HUt. -- exact HVt.
        -- apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWU.
        -- apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWV.
        -- eapply (Sub_insert Pos Eq emp Δ U V HUV empty Y (bind_sub im0) Δ).
           ++ reflexivity.
           ++ apply wf_env_sub with (X:=Y) (im:=im0).
              ** exact (Sub_wf_env _ _ _ _ _ _ HUV).
              ** exact HYd.
      * destruct im0; simpl in *; intro Hc; apply HYXeq; symmetry; exact Hc.
      * destruct im0; simpl in *; assumption.
    + destruct im0; simpl in *; intro Hc; apply HYXeq; symmetry; exact Hc.
    + destruct im0; simpl in *; assumption.
  - (* rec_eq_in *)
    assert (HXe : X \notin evs0) by (apply notin_union_1 in HX; exact HX).
    assert (HXa : X \notin fv_tt A1) by (apply notin_union_2 in HX; exact HX).
    simpl.
    rewrite (subst_tt_notin A1 X (sL im0 U V) HXa).
    simpl.
    apply Sa_rec_eq_in with (L := L \u {{ X }} \u dom Δ). intros Y HY.
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HYX : Y \notin {{ X }})
      by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
    assert (HYd : Y \notin dom Δ)
      by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
    assert (HYXeq : Y <> X)
      by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
    assert (HXA1o : X \notin fv_tt (open_tt A1 Y)).
    { apply fv_tt_open_notin.
      - exact HXa.
      - apply notin_singleton_2. exact HYXeq. }
    rewrite <- (subst_tt_notin (open_tt A1 Y) X (sL im0 U V) HXA1o).
    unfold open_tt.
    rewrite open_tt_subst_tt.
    + apply (IH Y HYL (Y ~ bind_sub im0 ++ Δ)).
      * rewrite HE. rewrite app_assoc. reflexivity.
      * apply (notin_add_3 Y X evs0).
        -- exact HYXeq.
        -- exact HXe.
      * exact HTU.
      * exact HTV.
      * exact HXU.
      * exact HXV.
      * exact HUt.
      * exact HVt.
      * apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWU.
      * apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWV.
      * eapply (Sub_insert Pos Eq emp Δ U V HUV empty Y (bind_sub im0) Δ).
        -- reflexivity.
        -- apply wf_env_sub with (X:=Y) (im:=im0).
           ++ exact (Sub_wf_env _ _ _ _ _ _ HUV).
           ++ exact HYd.
    + symmetry. exact HYXeq.
    + destruct im0; simpl; assumption.
  - (* evs_proper *)
    apply Sa_evs_proper with (evs:=evs0).
    + apply (IHs Δ HE).
      * intro Hc. apply HX. apply (proj1 (Heq X)). exact Hc.
      * exact HTU.
      * exact HTV.
      * exact HXU.
      * exact HXV.
      * exact HUt.
      * exact HVt.
      * exact HWU.
      * exact HWV.
      * exact HUV.
    + exact Heq.
Qed.

Lemma typing_insert_typ : forall G e T, typing G e T ->
  forall (Δ:env) (x:atom) (Ti:typ) (E0:env), G = Δ ++ E0 ->
    wf_env (Δ ++ x ~ bind_typ Ti ++ E0) ->
    typing (Δ ++ x ~ bind_typ Ti ++ E0) e T.
Proof.
  intros G e T H.
  induction H as [G0 Hwf
                 | G0 y T0 Hwf Hb
                 | L G0 T2 b T3 HP IH
                 | G0 e1 e2 T2 T1 H1 IH1 H2 IH2
                 | G0 A e0 H1 IH1 Hw
                 | G0 T0 e0 H1 IH1
                 | G0 T0 e0 S evs cm H1 IH1 Hs];
    intros Δ x Ti E0 HE Hwf2.
  - apply typing_nat. exact Hwf2.
  - apply typing_var with (x:=y) (T:=T0).
    + exact Hwf2.
    + rewrite HE in Hb. apply binds_insert_mid. exact Hb.
  - (* abs *)
    set (newG := Δ ++ x ~ bind_typ Ti ++ E0).
    destruct (exists_fresh_notin (L \u dom newG)) as [z Hz].
    assert (HzL : z \notin L) by (apply notin_union_1 in Hz; exact Hz).
    assert (Hzd : z \notin dom newG) by (apply notin_union_2 in Hz; exact Hz).
    apply typing_abs with (L := L \u dom newG).
    intros z' Hz'.
    assert (Hz'L : z' \notin L) by (apply notin_union_1 in Hz'; exact Hz').
    assert (Hz'd : z' \notin dom newG) by (apply notin_union_2 in Hz'; exact Hz').
    assert (HPz : typing (z' ~ bind_typ T2 ++ G0) (open_ee b z') T3)
      by (apply HP; exact Hz'L).
    assert (Hwfz : wf_env (z' ~ bind_typ T2 ++ G0))
      by (apply (typing_wf_env (z' ~ bind_typ T2 ++ G0) (open_ee b z') T3); exact HPz).
    assert (HWFG : WFS G0 T2) by (apply (wf_env_bind_typ_wfs z' T2 G0); exact Hwfz).
    assert (HWFnew : WFS newG T2).
    { unfold newG. rewrite HE in HWFG. apply WFS_insert_mid with (Δ:=Δ) (x:=x) (b:=bind_typ Ti) (E0:=E0). exact HWFG. }
    assert (Hwfznew : wf_env (z' ~ bind_typ T2 ++ newG))
      by (apply wf_env_typ; [unfold newG in *; exact Hwf2 | exact HWFnew | exact Hz'd]).
    assert (Hp : typing ((z' ~ bind_typ T2 ++ Δ) ++ x ~ bind_typ Ti ++ E0) (open_ee b z') T3).
    { apply (IH z' Hz'L (z' ~ bind_typ T2 ++ Δ) x Ti E0).
      - rewrite HE. rewrite app_assoc_lr. reflexivity.
      - rewrite app_assoc_lr. fold newG. exact Hwfznew. }
    rewrite app_assoc_lr in Hp. fold newG in Hp.
    change (typing (z' ~ bind_typ T2 ++ newG) (open_ee b z') T3) in Hp.
    exact Hp.
  - eapply typing_app.
    + apply (IH1 Δ x Ti E0 HE Hwf2).
    + apply (IH2 Δ x Ti E0 HE Hwf2).
  - eapply typing_fold.
    + apply (IH1 Δ x Ti E0 HE Hwf2).
    + rewrite HE in Hw. apply WFS_insert_mid with (Δ:=Δ) (x:=x) (b:=bind_typ Ti) (E0:=E0). exact Hw.
  - eapply typing_unfold.
    apply (IH1 Δ x Ti E0 HE Hwf2).
  - eapply typing_sub.
    + apply (IH1 Δ x Ti E0 HE Hwf2).
    + rewrite HE in Hs. apply (Sub_insert Pos cm evs (Δ ++ E0) S T0 Hs Δ x (bind_typ Ti) E0 eq_refl Hwf2).
Qed.

Lemma typing_subst_ee_gen : forall E e T, typing E e T ->
  forall (Δ:env) (x:atom) (S:typ) (G:env) (u:exp),
    E = Δ ++ x ~ bind_typ S ++ G ->
    x \notin dom Δ ->
    typing (Δ ++ G) u S ->
    expr u ->
    typing (Δ ++ G) (subst_ee x u e) T.
Proof.
  intros E e T H.
  induction H as [Ec Hwf
                 | Ec y T0 Hwf Hb
                 | L Ec T2 b T3 HP IH
                 | Ec e1 e2 T2 T1 H1 IH1 H2 IH2
                 | Ec A e0 H1 IH1 Hw
                 | Ec T0 e0 H1 IH1
                 | Ec T0 e0 Sp evsp cmp H1 IH1 Hs];
    intros Δ x S G u HE Hx Hu HuEx.
  - (* nat *) apply typing_nat. apply (wf_env_remove_typ Ec Hwf Δ x S G HE).
  - (* var *)
    assert (HxG : x \notin dom G) by (apply (wf_env_mid_notin_suffix Δ x S G); rewrite <- HE; exact Hwf).
    assert (Hwf' : wf_env (Δ ++ G)) by (apply (wf_env_remove_typ Ec Hwf Δ x S G HE)).
    destruct (y == x) as [Hyx|Hyx].
    + subst y. simpl. rewrite eq_dec_refl. simpl. rewrite HE in Hb.
      rewrite (binds_app_iff binding x (bind_typ T0) Δ (x ~ bind_typ S ++ G)) in Hb.
      destruct Hb as [HbΔ | HbxG].
      * exfalso. apply (binds_dom_contradiction binding x (bind_typ T0) Δ HbΔ Hx).
      * apply binds_cons_iff in HbxG. destruct HbxG as [[Heq HbT]|HbG].
        -- injection HbT as HTS. subst T0. exact Hu.
        -- exfalso. exact (binds_dom_contradiction binding x (bind_typ T0) G HbG HxG).
    + rewrite (subst_ee_neq x y u Hyx). simpl.
      apply typing_var with (x:=y) (T:=T0).
      * exact Hwf'.
      * rewrite HE in Hb.
        rewrite (binds_app_iff binding y (bind_typ T0) Δ (x ~ bind_typ S ++ G)) in Hb.
        destruct Hb as [HbΔ | HbxG].
        -- apply binds_app_iff. left. exact HbΔ.
        -- apply binds_cons_iff in HbxG. destruct HbxG as [[Hyx' _]|HbG].
           ++ exfalso. apply Hyx. exact Hyx'.
           ++ apply binds_app_iff. right. exact HbG.
  - (* abs *)
    simpl.
    set (newG := Δ ++ G).
    apply typing_abs with (L := L \u {{x}} \u dom newG \u fv_exp b \u fv_exp u).
    intros z Hz.
    assert (HzL : z \notin L) by (apply notin_union_1 in Hz; exact Hz).
    assert (Hzx : z \notin {{x}}) by (apply notin_union_2 in Hz; apply notin_union_1 in Hz; exact Hz).
    assert (Hznew : z \notin dom newG) by (apply notin_union_2 in Hz; apply notin_union_2 in Hz; apply notin_union_1 in Hz; exact Hz).
    assert (Hzb : z \notin fv_exp b) by (apply notin_union_2 in Hz; apply notin_union_2 in Hz; apply notin_union_2 in Hz; apply notin_union_1 in Hz; exact Hz).
    assert (Hzu : z \notin fv_exp u) by (apply notin_union_2 in Hz; apply notin_union_2 in Hz; apply notin_union_2 in Hz; apply notin_union_2 in Hz; exact Hz).
    assert (Hzxe : z <> x) by (intro Hc; apply Hzx; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
    assert (HPz : typing (z ~ bind_typ T2 ++ Ec) (open_ee b z) T3) by (apply HP; exact HzL).
    assert (Hwfz : wf_env (z ~ bind_typ T2 ++ Ec))
      by (apply (typing_wf_env (z ~ bind_typ T2 ++ Ec) (open_ee b z) T3); exact HPz).
    assert (HzΔ : x \notin dom (z ~ bind_typ T2 ++ Δ)).
    { simpl. apply (notin_add_3 z x (dom Δ)). - intro Hc; apply Hzxe; exact Hc. - exact Hx. }
    assert (Hwf_rem : wf_env ((z ~ bind_typ T2 ++ Δ) ++ G)).
    { apply (wf_env_remove_typ (z ~ bind_typ T2 ++ Ec) Hwfz (z ~ bind_typ T2 ++ Δ) x S G).
      rewrite HE.
      exact (eq_sym (@app_assoc_lr (atom*binding) (z ~ bind_typ T2) Δ (x ~ bind_typ S ++ G))). }
    assert (Hue : typing ((z ~ bind_typ T2 ++ Δ) ++ G) u S).
    { assert (Hins : typing (nil ++ z ~ bind_typ T2 ++ (Δ ++ G)) u S).
      { apply (typing_insert_typ (Δ ++ G) u S Hu nil z T2 (Δ ++ G) eq_refl).
        rewrite <- app_assoc_lr. exact Hwf_rem. }
      assert (Heqenv : nil ++ z ~ bind_typ T2 ++ (Δ ++ G) = (z ~ bind_typ T2 ++ Δ) ++ G).
      { simpl. reflexivity. }
      rewrite Heqenv in Hins. exact Hins. }
    assert (Hbody : typing ((z ~ bind_typ T2 ++ Δ) ++ G) (subst_ee x u (open_ee b z)) T3).
    { apply (IH z HzL (z ~ bind_typ T2 ++ Δ) x S G u).
      - rewrite HE.
        exact (eq_sym (@app_assoc_lr (atom*binding) (z ~ bind_typ T2) Δ (x ~ bind_typ S ++ G))).
      - exact HzΔ.
      - exact Hue.
      - exact HuEx. }
    rewrite <- (open_ee_subst_ee_comm b x u z Hzxe Hzu Hzb HuEx 0) in Hbody.
    assert (Heqenv2 : (z ~ bind_typ T2 ++ Δ) ++ G = z ~ bind_typ T2 ++ newG).
    { unfold newG. rewrite app_assoc_lr. reflexivity. }
    rewrite Heqenv2 in Hbody.
    exact Hbody.
  - (* app *) simpl. eapply typing_app.
    + apply (IH1 Δ x S G u HE Hx Hu HuEx).
    + apply (IH2 Δ x S G u HE Hx Hu HuEx).
  - (* fold *) simpl. eapply typing_fold.
    + apply (IH1 Δ x S G u HE Hx Hu HuEx).
    + apply (WFS_remove_typ Δ x S G (typ_mu A)). rewrite <- HE. exact Hw.
  - (* unfold *) simpl. eapply typing_unfold.
    apply (IH1 Δ x S G u HE Hx Hu HuEx).
  - (* sub *) eapply typing_sub.
    + apply (IH1 Δ x S G u HE Hx Hu HuEx).
    + apply (Sub_strengthen_typ_gen Pos cmp evsp Ec Sp T0 Hs Δ x S G HE).
Qed.

Lemma typing_subst_ee_ax : forall (G:env) (x:atom) (u:exp) (S:typ) e T,
  typing (x ~ bind_typ S ++ G) e T ->
  typing G u S ->
  expr u ->
  typing G (subst_ee x u e) T.
Proof.
  intros G x u S e T He Hu HuEx.
  apply (typing_subst_ee_gen (x ~ bind_typ S ++ G) e T He nil x S G u).
  - reflexivity.
  - simpl. apply notin_empty_1.
  - exact Hu.
  - exact HuEx.
Qed.

Lemma typing_abs_beta_gen : forall G e U,
  typing G e U -> G = nil ->
  forall dom body A B, e = exp_abs dom body -> U = typ_arrow A B ->
  forall e2, typing nil e2 A -> typing nil (open_ee body e2) B.
Proof.
  intros G e U H.
  induction H as [G0 Hwf
                 | G0 x T0 Hwf Hb
                 | L G0 T1 b T2 HP IH
                 | G0 e1 e2 T2 T1 H1 IH1 H2 IH2
                 | G0 A0 e0 H1 IH1 Hw
                 | G0 T0 e0 H1 IH1
                 | G0 T0 e0 S evs cm H1 IH1 Hs];
    intros HG dom body A B He HU u2 He2.
  - discriminate He.
  - discriminate He.
  - subst G0.
    inversion He; subst. inversion HU; subst.
    assert (Hexpr : expr u2) by (apply (typing_expr nil u2 A); exact He2).
    destruct (exists_fresh_notin (L \u fv_exp body \u fv_exp u2)) as [z Hz].
    assert (HzL : z \notin L) by (apply notin_union_1 in Hz; exact Hz).
    assert (Hzb : z \notin fv_exp body)
      by (apply notin_union_2 in Hz; apply notin_union_1 in Hz; exact Hz).
    assert (Hze : z \notin fv_exp u2)
      by (apply notin_union_2 in Hz; apply notin_union_2 in Hz; exact Hz).
    assert (Hbody : typing (z ~ bind_typ A ++ empty) (open_ee body z) B)
      by (apply HP; exact HzL).
    assert (Hsub : typing empty (subst_ee z u2 (open_ee body z)) B).
    { apply (typing_subst_ee_ax empty z u2 A (open_ee body z) B).
      - exact Hbody.
      - exact He2.
      - exact Hexpr. }
    rewrite <- (open_ee_eq_subst_ee body z u2 Hzb 0) in Hsub.
    exact Hsub.
  - discriminate He.
  - discriminate He.
  - discriminate He.
  - subst G0. subst T0.
    destruct (typing_abs_shape empty e0 S H1 dom body He) as [Htop|Harr].
    + assert (Hbad : typ_arrow A B = typ_top)
        by exact (Sub_top_inv Pos cm evs empty S (typ_arrow A B) Hs Htop).
      discriminate Hbad.
    + destruct Harr as [A' [B' HS]]. subst S.
      destruct (Sub_arrow_left_inv Pos cm evs empty (typ_arrow A' B') (typ_arrow A B) Hs A' B' eq_refl) as [Hbad|Hdec].
      * discriminate Hbad.
      * destruct Hdec as [B1 [B2 [cm1 [cm2 [evs1 [evs2 [HB [Hcontrav Hcov]]]]]]]].
        injection HB as HB1 HB2. subst B1 B2.
        assert (Hn : NoSubBind empty)
          by (unfold NoSubBind; intros z i Hb; apply binds_nil_iff in Hb; destruct Hb).
        assert (Hneg : Sub Pos cm1 evs1 empty A A')
          by (apply (Sub_neg_pos empty A A' cm1 evs1); assumption).
        assert (He2' : typing empty u2 A') by (eapply typing_sub; [exact He2|exact Hneg]).
        assert (Hbody : typing empty (open_ee body u2) B')
          by (apply (IH1 eq_refl dom body A' B' He eq_refl); exact He2').
        eapply typing_sub; [exact Hbody | exact Hcov].
Qed.

Lemma typing_abs_beta : forall dom body A B,
  typing nil (exp_abs dom body) (typ_arrow A B) ->
  forall u2, typing nil u2 A -> typing nil (open_ee body u2) B.
Proof.
  intros dom body A B H u2 He2.
  apply (typing_abs_beta_gen nil (exp_abs dom body) (typ_arrow A B) H eq_refl dom body A B eq_refl eq_refl u2 He2).
Qed.

(* ============================================================ *)
(* Injectivity of opening with a fresh free variable             *)
(* ============================================================ *)

Ltac close_shape :=
  solve [
    repeat match goal with
    | H : context [if ?a == ?b then _ else _] |- _ => destruct (a == b)
    end;
    simpl in *;
    inversion Heq
  ].

Lemma open_tt_rec_fvar_inj : forall A k X,
  X \notin fv_tt A ->
  forall B, X \notin fv_tt B ->
  open_tt_rec k (typ_fvar X) A = open_tt_rec k (typ_fvar X) B -> A = B.
Proof.
  induction A as [| | nA | aA | A IHA | A1 IH1 A2 IH2];
    intros k X HA B HB Heq; destruct B as [| | mB | bB | Bm | B1 B2]; simpl in *;
    try close_shape.
  - reflexivity.
  - reflexivity.
  - (* bvar / bvar *)
    destruct (k == nA) as [e1|n1]; destruct (k == mB) as [e2|n2]; simpl in *.
    + subst. reflexivity.
    + inversion Heq.
    + inversion Heq.
    + injection Heq as Hnm. subst. reflexivity.
  - (* bvar / fvar *)
    destruct (k == nA) as [e1|n1]; simpl in *.
    + injection Heq as HXb. exfalso. apply HB.
      rewrite <- HXb. apply AtomSetImpl.singleton_2. reflexivity.
    + inversion Heq.
  - (* fvar / bvar *)
    destruct (k == mB) as [e2|n2]; simpl in *.
    + injection Heq as HXa. exfalso. apply HA.
      rewrite <- HXa. apply AtomSetImpl.singleton_2. reflexivity.
    + inversion Heq.
  - (* fvar / fvar *)
    injection Heq as H. subst. reflexivity.
  - (* mu / mu *)
    injection Heq as H. f_equal. apply (IHA (S k) X HA Bm HB H).
  - (* arrow / arrow *)
    injection Heq as H1 H2.
    assert (HA1 : X \notin fv_tt A1) by (apply notin_union_1 in HA; exact HA).
    assert (HA2 : X \notin fv_tt A2) by (apply notin_union_2 in HA; exact HA).
    assert (HB1 : X \notin fv_tt B1) by (apply notin_union_1 in HB; exact HB).
    assert (HB2 : X \notin fv_tt B2) by (apply notin_union_2 in HB; exact HB).
    rewrite (IH1 k X HA1 B1 HB1 H1).
    rewrite (IH2 k X HA2 B2 HB2 H2). reflexivity.
Qed.

(* ============================================================ *)
(* Eq-mode subtyping is syntactic equality                       *)
(* ============================================================ *)

Lemma compose_cm_eq_inv : forall cm1 cm2 evs1 evs2,
  compose_cm cm1 cm2 evs1 evs2 = Some Eq -> cm1 = Eq /\ cm2 = Eq.
Proof.
  intros cm1 cm2 evs1 evs2 H.
  destruct cm1, cm2; simpl in H.
  - discriminate H.
  - destruct (AtomSetImpl.is_empty evs2); simpl in H; discriminate H.
  - destruct (AtomSetImpl.is_empty evs1); simpl in H; discriminate H.
  - split; reflexivity.
Qed.

Lemma Sub_eq_syntactic : forall im cm evs E A B,
  Sub im cm evs E A B -> cm = Eq -> A = B.
Proof.
  intros im cm evs E A B H.
  induction H as [E im Hwf
                 | E im Hwf
                 | E im A Hwf Hw Hne
                 | E X im Hwf Hb
                 | E X im Hwf Hb
                 | E A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm im
                     Hsub1 IHsub1 Hsub2 IHsub2 Hcomp
                 | L A1 A2 evs E im HP IHP
                 | L A1 A2 evs E im HP IHP
                 | L A1 A2 evs E im HP IHP
                 | im cm evs evs' E A1 A2 Hsub IHsub Heqv];
    intro Hcm.
  - reflexivity.
  - reflexivity.
  - discriminate Hcm.
  - reflexivity.
  - reflexivity.
  - (* arrow *)
    rewrite Hcm in Hcomp. apply compose_cm_eq_inv in Hcomp.
    destruct Hcomp as [-> ->].
    simpl. rewrite (IHsub1 eq_refl). rewrite (IHsub2 eq_refl). reflexivity.
  - (* rec_lt *)
    discriminate Hcm.
  - (* rec_eq_notin *)
    destruct (exists_fresh_notin (L \u fv_tt A1 \u fv_tt A2)) as [X HX].
    assert (HXL : X \notin L) by (apply notin_union_1 in HX; exact HX).
    assert (HX1 : X \notin fv_tt A1)
      by (apply notin_union_2 in HX; apply notin_union_1 in HX; exact HX).
    assert (HX2 : X \notin fv_tt A2)
      by (apply notin_union_2 in HX; apply notin_union_2 in HX; exact HX).
    assert (Hopen : open_tt_rec 0 (typ_fvar X) A1 = open_tt_rec 0 (typ_fvar X) A2)
      by (apply (IHP X HXL eq_refl)).
    f_equal. apply (open_tt_rec_fvar_inj A1 0 X HX1 A2 HX2 Hopen).
  - (* rec_eq_in *)
    destruct (exists_fresh_notin (L \u fv_tt A1 \u fv_tt A2)) as [X HX].
    assert (HXL : X \notin L) by (apply notin_union_1 in HX; exact HX).
    assert (HX1 : X \notin fv_tt A1)
      by (apply notin_union_2 in HX; apply notin_union_1 in HX; exact HX).
    assert (HX2 : X \notin fv_tt A2)
      by (apply notin_union_2 in HX; apply notin_union_2 in HX; exact HX).
    assert (Hopen : open_tt_rec 0 (typ_fvar X) A1 = open_tt_rec 0 (typ_fvar X) A2)
      by (apply (IHP X HXL eq_refl)).
    f_equal. apply (open_tt_rec_fvar_inj A1 0 X HX1 A2 HX2 Hopen).
  - (* evs_proper *)
    apply IHsub. exact Hcm.
Qed.

Lemma WFS_remove_sub_nil : forall (Δ:env) (X:atom) (im:IsoMode) A,
  WFS (Δ ++ X ~ bind_sub im) A -> X \notin fv_tt A -> WFS Δ A.
Proof.
  intros Δ X im A H Hx.
  pose proof (WFS_remove_sub_notin Δ X im nil A) as Hres.
  specialize (Hres ltac:(rewrite app_nil_r; exact H) Hx).
  rewrite app_nil_r in Hres. exact Hres.
Qed.

(* ============================================================ *)
(* Strengthening: AtomSetImpl.remove a trailing subtype binder              *)
(* ============================================================ *)

Lemma Sub_strengthen_sub_notin : forall im cm evs Ec A B, Sub im cm evs Ec A B ->
  forall Δ X, Ec = Δ ++ X ~ bind_sub Pos -> wf_env Δ ->
  X \notin evs -> X \notin fv_tt A -> X \notin fv_tt B ->
  Sub im cm evs Δ A B.
Proof.
  intros im cm evs Ec A B H.
  induction H as [Ec im0 Hwf
                 | Ec im0 Hwf
                 | Ec im0 A0 Hwf HW Hne
                 | Ec X0 im0 Hwf Hb
                 | Ec X0 im0 Hwf Hb
                 | Ec A1 A2 B1 B2 cm1 cm2 evs1 evs2 cm0 im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 Ec im0 HP IH
                 | L A1 A2 evs0 Ec im0 HP IH
                 | L A1 A2 evs0 Ec im0 HP IH
                 | im0 cm0 evs0 evs' Ec A1 A2 Hs IHs Heq];
    intros Δ X HE HwfΔ HX HXA HXB.
  - apply Sa_nat. exact HwfΔ.
  - apply Sa_top_eq. exact HwfΔ.
  - apply Sa_top_lt.
    + exact HwfΔ.
    + apply (WFS_remove_sub_nil Δ X Pos A0).
      * rewrite <- HE. exact HW.
      * exact HXA.
    + exact Hne.
  - (* fvar_pos *)
    destruct (X0 == X) as [Heq|Hne] eqn:Hd.
    + subst X0. exfalso. apply HXA. apply AtomSetImpl.singleton_2. reflexivity.
    + apply Sa_fvar_pos.
      * exact HwfΔ.
      * rewrite HE in Hb.
        pose proof (proj1 (binds_sub_remove_sub Δ X Pos nil X0 im0 Hne) Hb) as Hb'.
        rewrite app_nil_r in Hb'. exact Hb'.
  - (* fvar_neg *)
    destruct (X0 == X) as [Heq|Hne] eqn:Hd.
    + subst X0. exfalso. apply HX. apply AtomSetImpl.singleton_2. reflexivity.
    + apply Sa_fvar_neg.
      * exact HwfΔ.
      * rewrite HE in Hb.
        pose proof (proj1 (binds_sub_remove_sub Δ X Pos nil X0 (flip_im im0) Hne) Hb) as Hb'.
        rewrite app_nil_r in Hb'. exact Hb'.
  - (* arrow *)
    assert (HX1 : X \notin evs1) by (apply notin_union_1 in HX; exact HX).
    assert (HX2 : X \notin evs2) by (apply notin_union_2 in HX; exact HX).
    eapply Sa_arrow.
    + apply (IH1 Δ X HE HwfΔ).
      * exact HX1.
      * apply notin_union_1 in HXB. exact HXB.
      * apply notin_union_1 in HXA. exact HXA.
    + apply (IH2 Δ X HE HwfΔ).
      * exact HX2.
      * apply notin_union_2 in HXA. exact HXA.
      * apply notin_union_2 in HXB. exact HXB.
    + exact Hc.
  - (* rec_lt *)
    apply Sa_rec_lt with (L := L \u {{X}} \u dom Δ). intros Y HY.
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HYX : Y \notin {{X}})
      by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
    assert (HYd : Y \notin dom Δ)
      by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
    assert (HYXeq : Y <> X)
      by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
    apply (IH Y HYL (Y ~ bind_sub im0 ++ Δ) X).
    + rewrite HE. rewrite app_assoc_lr. reflexivity.
    + apply wf_env_sub with (X:=Y) (im:=im0).
      * exact HwfΔ.
      * exact HYd.
    + exact HX.
    + apply fv_tt_open_notin.
      * exact HXA.
      * apply notin_singleton_2. exact HYXeq.
    + apply fv_tt_open_notin.
      * exact HXB.
      * apply notin_singleton_2. exact HYXeq.
  - (* rec_eq_notin *)
    apply Sa_rec_eq_notin with (L := L \u {{X}} \u dom Δ). intros Y HY.
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HYX : Y \notin {{X}})
      by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
    assert (HYd : Y \notin dom Δ)
      by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
    assert (HYXeq : Y <> X)
      by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
    apply (IH Y HYL (Y ~ bind_sub im0 ++ Δ) X).
    + rewrite HE. rewrite app_assoc_lr. reflexivity.
    + apply wf_env_sub with (X:=Y) (im:=im0).
      * exact HwfΔ.
      * exact HYd.
    + exact HX.
    + apply fv_tt_open_notin.
      * exact HXA.
      * apply notin_singleton_2. exact HYXeq.
    + apply fv_tt_open_notin.
      * exact HXB.
      * apply notin_singleton_2. exact HYXeq.
  - (* rec_eq_in *)
    assert (HXe : X \notin evs0) by (apply notin_union_1 in HX; exact HX).
    assert (HXa : X \notin fv_tt A1) by (apply notin_union_2 in HX; exact HX).
    assert (HXb : X \notin fv_tt A2).
    { (* X notin fv (mu A2) = fv A2 *) exact HXB. }
    apply Sa_rec_eq_in with (L := L \u {{X}} \u dom Δ). intros Y HY.
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HYX : Y \notin {{X}})
      by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
    assert (HYd : Y \notin dom Δ)
      by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
    assert (HYXeq : Y <> X)
      by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
    apply (IH Y HYL (Y ~ bind_sub im0 ++ Δ) X).
    + rewrite HE. rewrite app_assoc_lr. reflexivity.
    + apply wf_env_sub with (X:=Y) (im:=im0).
      * exact HwfΔ.
      * exact HYd.
    + apply (notin_add_3 Y X evs0).
      * exact HYXeq.
      * exact HXe.
    + apply fv_tt_open_notin.
      * exact HXa.
      * apply notin_singleton_2. exact HYXeq.
    + apply fv_tt_open_notin.
      * exact HXb.
      * apply notin_singleton_2. exact HYXeq.
  - (* evs_proper *)
    apply Sa_evs_proper with (evs:=evs0).
    + apply (IHs Δ X HE HwfΔ).
      * intro Hc. apply HX. apply (proj1 (Heq X)). exact Hc.
      * exact HXA.
      * exact HXB.
    + exact Heq.
Qed.

(* ============================================================ *)
(* Helper facts for the occurrence substitution lemma           *)
(* ============================================================ *)

Lemma fv_tt_open_in : forall A k Y X,
  X <> Y -> X \in fv_tt A -> X \in fv_tt (open_tt_rec k (typ_fvar Y) A).
Proof.
  induction A as [| | n | a | A IHA | A1 IH1 A2 IH2]; intros k Y X HXY HX; simpl in *.
  - exfalso. exact (AtomSetImpl.empty_1 HX).
  - exfalso. exact (AtomSetImpl.empty_1 HX).
  - destruct (k == n); [exfalso; exact (AtomSetImpl.empty_1 HX)|].
    exfalso. exact (AtomSetImpl.empty_1 HX).
  - simpl. destruct (a == Y).
    + exfalso. apply HXY.
      assert (HaX : a = X) by exact (@AtomSetImpl.singleton_1 a X HX).
      rewrite <- HaX. exact e.
    + exact HX.
  - apply IHA; assumption.
  - apply AtomSetImpl.union_1 in HX. destruct HX as [HX|HX].
    + apply AtomSetImpl.union_2. apply IH1; assumption.
    + apply AtomSetImpl.union_3. apply IH2; assumption.
Qed.

Lemma in_dec : forall (X:atom) (s:atoms), { X \in s } + { X \notin s }.
Proof.
  intros X s. destruct (AtomSetImpl.mem X s) eqn:E.
  - left. apply (proj2 (mem_iff s X)). exact E.
  - right. apply (proj2 (not_mem_iff s X)). exact E.
Qed.

Lemma union_empty_l : forall s1 s2 : atoms, s1 \u s2 [=] Metatheory.empty -> s1 [=] Metatheory.empty.
Proof.
  intros s1 s2 H a. split.
  - intro Ha. apply (proj1 (H a)). apply AtomSetImpl.union_2. exact Ha.
  - intro Ha. exfalso. exact (AtomSetImpl.empty_1 Ha).
Qed.

Lemma union_empty_r : forall s1 s2 : atoms, s1 \u s2 [=] Metatheory.empty -> s2 [=] Metatheory.empty.
Proof.
  intros s1 s2 H a. split.
  - intro Ha. apply (proj1 (H a)). apply AtomSetImpl.union_3. exact Ha.
  - intro Ha. exfalso. exact (AtomSetImpl.empty_1 Ha).
Qed.

Lemma union_eq_empty : forall s1 s2 : atoms,
  s1 [=] Metatheory.empty -> s2 [=] Metatheory.empty -> s1 \u s2 [=] Metatheory.empty.
Proof.
  intros s1 s2 H1 H2 a. split.
  - intro Ha. apply AtomSetImpl.union_1 in Ha. destruct Ha as [Ha|Ha].
    + exact (proj1 (H1 a) Ha).
    + exact (proj1 (H2 a) Ha).
  - intro Ha. exfalso. exact (AtomSetImpl.empty_1 Ha).
Qed.

Lemma compose_cm_occ_lt : forall cm1 cm2 evs1 evs2,
  evs1 [=] Metatheory.empty -> evs2 [=] Metatheory.empty -> (cm1 = Lt \/ cm2 = Lt) ->
  compose_cm cm1 cm2 evs1 evs2 = Some Lt.
Proof.
  intros cm1 cm2 evs1 evs2 He1 He2 Hlt.
  destruct cm1, cm2; simpl.
  - reflexivity.
  - rewrite (AtomSetImpl.is_empty_1 (AtomSetProperties.empty_is_empty_2 He2)). reflexivity.
  - rewrite (AtomSetImpl.is_empty_1 (AtomSetProperties.empty_is_empty_2 He1)). reflexivity.
  - destruct Hlt as [H|H]; discriminate H.
Qed.

Lemma WFS_subst_nil : forall (Ec:env) A (Δ:env) (X:atom) (im:IsoMode) U,
  WFS Ec A -> Ec = Δ ++ X ~ bind_sub im -> type U -> WFS Δ U ->
  WFS Δ (subst_tt X U A).
Proof.
  intros Ec A Δ X im U HW HE HTU HWU.
  pose proof (WFS_subst_mid Ec A HW Δ X im nil HE U HTU ltac:(rewrite app_nil_r; exact HWU)) as Hres.
  rewrite app_nil_r in Hres. exact Hres.
Qed.

Lemma Sub_evs_empty : forall im cm evs A B,
  Sub im cm evs nil A B -> evs [=] Metatheory.empty.
Proof.
  intros im cm evs A B H a. split.
  - intro Ha. exfalso. exact (Sub_evs_nil im cm evs A B H a Ha).
  - intro Ha. exfalso. exact (AtomSetImpl.empty_1 Ha).
Qed.

Lemma sL_flip_sR : forall im U V, sL (flip_im im) U V = sR im U V.
Proof. intros [] U V; reflexivity. Qed.

Lemma sR_flip_sL : forall im U V, sR (flip_im im) U V = sL im U V.
Proof. intros [] U V; reflexivity. Qed.

Lemma eq_empty_refl : Metatheory.empty [=] Metatheory.empty.
Proof. intro a; split; intro Ha; exact Ha. Qed.

Lemma is_empty_empty : AtomSetImpl.is_empty Metatheory.empty = true.
Proof.
  apply AtomSetImpl.is_empty_1.
  intro a. apply AtomSetImpl.empty_1.
Qed.

Lemma compose_cm_empty : forall cm1 cm2,
  exists cm, compose_cm cm1 cm2 Metatheory.empty Metatheory.empty = Some cm.
Proof.
  intros [] []; simpl; try rewrite is_empty_empty; eexists; reflexivity.
Qed.

(* ============================================================ *)
(* Flexible substitution lemma: the mode/evidence may change,   *)
(* and the self-assumption only needs to be at Pos.              *)
(* ============================================================ *)

Lemma Sub_subst_empty : forall (X:atom) im cm evs (Ec:env) A B,
  Sub im cm evs Ec A B -> evs [=] Metatheory.empty ->
  forall (Δ:env), Ec = Δ ++ X ~ bind_sub Pos -> wf_env Δ ->
  forall U V, type U -> type V -> X \notin fv_tt U -> X \notin fv_tt V ->
    U <> typ_top -> V <> typ_top ->
    WFS Δ U -> WFS Δ V -> Sub Pos Eq emp Δ U V ->
  Sub im cm emp Δ (subst_tt X (sL im U V) A) (subst_tt X (sR im U V) B).
Proof.
  intros X im cm evs Ec A B H.
  induction H as [Ec0 im0 Hwf
                 | Ec0 im0 Hwf
                 | Ec0 im0 A0 Hwf HW Hne
                 | Ec0 X0 im0 Hwf Hb
                 | Ec0 X0 im0 Hwf Hb
                 | Ec0 A1 A2 B1 B2 cm1 cm2 evs1 evs2 cmi im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 Ec0 im0 HP IH
                 | L A1 A2 evs0 Ec0 im0 HP IH
                 | L A1 A2 evs0 Ec0 im0 HP IH
                 | im0 cm0 evs0 evs' Ec0 A1 A2 Hs IHs Heq];
    intros Hev Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV HUV.
  - (* nat *)
    apply Sa_nat. exact (Sub_wf_env _ _ _ _ _ _ HUV).
  - (* top_eq *)
    apply Sa_top_eq. exact (Sub_wf_env _ _ _ _ _ _ HUV).
  - (* top_lt *)
    rewrite HE in HW.
    apply Sa_top_lt.
    + exact (Sub_wf_env _ _ _ _ _ _ HUV).
    + destruct im0.
      * simpl. eapply (WFS_subst_nil (Δ ++ X ~ bind_sub Pos) A0 Δ X Pos V).
        -- exact HW.
        -- reflexivity.
        -- exact HTV.
        -- exact HWV.
      * simpl. eapply (WFS_subst_nil (Δ ++ X ~ bind_sub Pos) A0 Δ X Pos U).
        -- exact HW.
        -- reflexivity.
        -- exact HTU.
        -- exact HWU.
    + destruct im0; simpl; intro Hc.
      * apply Hne. exact (subst_tt_top_inv A0 X V HVt Hc).
      * apply Hne. exact (subst_tt_top_inv A0 X U HUt Hc).
  - (* fvar_pos *)
    rewrite HE in Hb.
    assert (HXΔ : X \notin dom Δ).
    { apply (wf_env_mid_fresh Δ X (bind_sub Pos) empty). simpl.
      exact (eq_rect Ec0 (fun e => wf_env e) Hwf (Δ ++ X ~ bind_sub Pos) HE). }
    destruct (X0 == X) as [Heq|HneX] eqn:Hd.
    + simpl. rewrite Hd. simpl. subst X0.
      rewrite (binds_app_iff binding X (bind_sub im0) Δ (X ~ bind_sub Pos)) in Hb.
      destruct Hb as [HbΔ | HbX].
      * exfalso. exact (binds_dom_contradiction binding X (bind_sub im0) Δ HbΔ HXΔ).
      * apply binds_cons_iff in HbX. destruct HbX as [[Heq2 Hbe]|Hc].
        -- injection Hbe as Him. subst im0. simpl. exact HUV.
        -- destruct Hc.
    + simpl. rewrite Hd. simpl.
      apply Sa_fvar_pos.
      * exact (Sub_wf_env _ _ _ _ _ _ HUV).
      * rewrite (binds_app_iff binding X0 (bind_sub im0) Δ (X ~ bind_sub Pos)) in Hb.
        destruct Hb as [HbΔ | HbX].
        -- exact HbΔ.
        -- apply binds_cons_iff in HbX. destruct HbX as [[Heq2 Hbe]|Hc].
           ++ exfalso. apply HneX. exact Heq2.
           ++ destruct Hc.
  - (* fvar_neg : evidence singleton X0, cannot be empty *)
    exfalso.
    assert (HEmpty : AtomSetImpl.Empty (singleton X0)).
    { apply AtomSetProperties.empty_is_empty_2. exact Hev. }
    exact (HEmpty X0 (@AtomSetImpl.singleton_2 X0 X0 eq_refl)).
  - (* arrow *)
    assert (He1 : evs1 [=] Metatheory.empty) by (apply (union_empty_l evs1 evs2); exact Hev).
    assert (He2 : evs2 [=] Metatheory.empty) by (apply (union_empty_r evs1 evs2); exact Hev).
    assert (Hs1e : Sub (flip_im im0) cm1 emp Δ
                    (subst_tt X (sR im0 U V) B1)
                    (subst_tt X (sL im0 U V) A1)).
    { rewrite <- (sL_flip_sR im0 U V), <- (sR_flip_sL im0 U V).
      apply (IH1 He1 Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV HUV). }
    assert (Hs2e : Sub im0 cm2 emp Δ
                    (subst_tt X (sL im0 U V) A2)
                    (subst_tt X (sR im0 U V) B2)).
    { apply (IH2 He2 Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV HUV). }
    eapply Sa_evs_proper with (evs := evs1 \u evs2).
    + eapply Sa_arrow with (cm1:=cm1) (cm2:=cm2).
      * apply Sa_evs_proper with (evs:=emp). 
        -- exact Hs1e.
        -- symmetry. exact He1.
      * apply Sa_evs_proper with (evs:=emp).
        -- exact Hs2e.
        -- symmetry. exact He2.
      * exact Hc.
    + exact Hev.
  - (* rec_lt *)
    apply Sa_rec_lt with (L := L \u {{X}} \u dom Δ). intros Y HY.
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HYX : Y \notin {{X}})
      by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
    assert (HYd : Y \notin dom Δ)
      by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
    assert (HYXeq : Y <> X)
      by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
    assert (HwfΔ' : wf_env (Y ~ bind_sub im0 ++ Δ)).
    { apply wf_env_sub with (X:=Y) (im:=im0).
      - exact (Sub_wf_env _ _ _ _ _ _ HUV).
      - exact HYd. }
    assert (HUV' : Sub Pos Eq emp (Y ~ bind_sub im0 ++ Δ) U V).
    { eapply (Sub_insert Pos Eq emp Δ U V HUV empty Y (bind_sub im0) Δ).
      - reflexivity.
      - exact HwfΔ'. }
    assert (HE' : Y ~ bind_sub im0 ++ Ec0 = (Y ~ bind_sub im0 ++ Δ) ++ X ~ bind_sub Pos).
    { rewrite HE. rewrite app_assoc_lr. reflexivity. }
    assert (Hprem : Sub im0 Lt emp (Y ~ bind_sub im0 ++ Δ)
              (subst_tt X (sL im0 U V) (open_tt A1 Y))
              (subst_tt X (sR im0 U V) (open_tt A2 Y))).
    { apply (IH Y HYL Hev (Y ~ bind_sub im0 ++ Δ) HE' HwfΔ' U V HTU HTV HXU HXV HUt HVt).
      - apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWU.
      - apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWV.
      - exact HUV'. }
    change (Sub im0 Lt emp (Y ~ bind_sub im0 ++ Δ)
              (open_tt (subst_tt X (sL im0 U V) A1) Y)
              (open_tt (subst_tt X (sR im0 U V) A2) Y)).
    assert (Heq1 : open_tt (subst_tt X (sL im0 U V) A1) Y =
                   subst_tt X (sL im0 U V) (open_tt A1 Y)).
    { unfold open_tt. apply open_tt_subst_tt.
      - symmetry. exact HYXeq.
      - destruct im0; simpl; assumption. }
    assert (Heq2 : open_tt (subst_tt X (sR im0 U V) A2) Y =
                   subst_tt X (sR im0 U V) (open_tt A2 Y)).
    { unfold open_tt. apply open_tt_subst_tt.
      - symmetry. exact HYXeq.
      - destruct im0; simpl; assumption. }
    rewrite Heq1, Heq2. exact Hprem.
  - (* rec_eq_notin *)
    apply Sa_rec_eq_notin with (L := L \u {{X}} \u dom Δ). intros Y HY.
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HYX : Y \notin {{X}})
      by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
    assert (HYd : Y \notin dom Δ)
      by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
    assert (HYXeq : Y <> X)
      by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
    assert (HwfΔ' : wf_env (Y ~ bind_sub im0 ++ Δ)).
    { apply wf_env_sub with (X:=Y) (im:=im0).
      - exact (Sub_wf_env _ _ _ _ _ _ HUV).
      - exact HYd. }
    assert (HUV' : Sub Pos Eq emp (Y ~ bind_sub im0 ++ Δ) U V).
    { eapply (Sub_insert Pos Eq emp Δ U V HUV empty Y (bind_sub im0) Δ).
      - reflexivity.
      - exact HwfΔ'. }
    assert (HE' : Y ~ bind_sub im0 ++ Ec0 = (Y ~ bind_sub im0 ++ Δ) ++ X ~ bind_sub Pos).
    { rewrite HE. rewrite app_assoc_lr. reflexivity. }
    assert (Hprem : Sub im0 Eq emp (Y ~ bind_sub im0 ++ Δ)
              (subst_tt X (sL im0 U V) (open_tt A1 Y))
              (subst_tt X (sR im0 U V) (open_tt A2 Y))).
    { apply (IH Y HYL Hev (Y ~ bind_sub im0 ++ Δ) HE' HwfΔ' U V HTU HTV HXU HXV HUt HVt).
      - apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWU.
      - apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWV.
      - exact HUV'. }
    change (Sub im0 Eq emp (Y ~ bind_sub im0 ++ Δ)
              (open_tt (subst_tt X (sL im0 U V) A1) Y)
              (open_tt (subst_tt X (sR im0 U V) A2) Y)).
    assert (Heq1 : open_tt (subst_tt X (sL im0 U V) A1) Y =
                   subst_tt X (sL im0 U V) (open_tt A1 Y)).
    { unfold open_tt. apply open_tt_subst_tt.
      - symmetry. exact HYXeq.
      - destruct im0; simpl; assumption. }
    assert (Heq2 : open_tt (subst_tt X (sR im0 U V) A2) Y =
                   subst_tt X (sR im0 U V) (open_tt A2 Y)).
    { unfold open_tt. apply open_tt_subst_tt.
      - symmetry. exact HYXeq.
      - destruct im0; simpl; assumption. }
    rewrite Heq1, Heq2. exact Hprem.
  - (* rec_eq_in *)
    assert (Hev0 : evs0 [=] Metatheory.empty)
      by (apply (union_empty_l evs0 (fv_tt A1)); exact Hev).
    assert (HXe : X \notin evs0)
      by (intro Hc; exact (AtomSetImpl.empty_1 (proj1 (Hev0 X) Hc))).
    assert (HfvA1 : fv_tt A1 [=] Metatheory.empty).
    { apply (union_empty_r evs0 (fv_tt A1)). exact Hev. }
    assert (HXa : X \notin fv_tt A1).
    { intro Hc. exact (AtomSetImpl.empty_1 (proj1 (HfvA1 X) Hc)). }
    assert (Hself : Sub im0 Eq (evs0 \u fv_tt A1) Ec0 (typ_mu A1) (typ_mu A2)).
    { apply Sa_rec_eq_in with (L:=L). exact HP. }
    assert (Hmu : typ_mu A1 = typ_mu A2)
      by (apply (Sub_eq_syntactic im0 Eq (evs0 \u fv_tt A1) Ec0 (typ_mu A1)(typ_mu A2));
          [exact Hself|reflexivity]).
    injection Hmu as HAeq.
    assert (HXa2 : X \notin fv_tt A2) by (rewrite <- HAeq; exact HXa).
    eapply Sa_evs_proper with (evs := evs0 \u fv_tt A1).
    + simpl. rewrite (subst_tt_notin A1 X (sL im0 U V) HXa).
      rewrite (subst_tt_notin A2 X (sR im0 U V) HXa2).
      apply Sa_rec_eq_in with (L := L \u {{X}} \u dom Δ). intros Y HY.
      assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
      assert (HYX : Y \notin {{X}})
        by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
      assert (HYd : Y \notin dom Δ)
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
      assert (HYXeq : Y <> X)
        by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
      assert (HwfΔ' : wf_env (Y ~ bind_sub im0 ++ Δ)).
      { apply wf_env_sub with (X:=Y) (im:=im0).
        - exact (Sub_wf_env _ _ _ _ _ _ HUV).
        - exact HYd. }
      assert (HXA1o : X \notin fv_tt (open_tt A1 Y)).
      { apply fv_tt_open_notin; [exact HXa | apply notin_singleton_2; exact HYXeq]. }
      assert (HXA2o : X \notin fv_tt (open_tt A2 Y)).
      { apply fv_tt_open_notin; [exact HXa2 | apply notin_singleton_2; exact HYXeq]. }
      assert (HEpres : Y ~ bind_sub im0 ++ Ec0 = (Y ~ bind_sub im0 ++ Δ) ++ X ~ bind_sub Pos).
      { rewrite HE. rewrite app_assoc_lr. reflexivity. }
      eapply (Sub_strengthen_sub_notin im0 Eq (add Y evs0) (Y ~ bind_sub im0 ++ Ec0)
                (open_tt A1 Y) (open_tt A2 Y)).
      * apply HP. exact HYL.
      * exact HEpres.
      * exact HwfΔ'.
      * apply (notin_add_3 Y X evs0); [exact HYXeq|exact HXe].
      * exact HXA1o.
      * exact HXA2o.
    + exact Hev.
  - (* evs_proper *)
    assert (Hev0 : evs0 [=] Metatheory.empty).
    { intro a; split.
      - intro Ha. exact (proj1 (Hev a) (proj1 (Heq a) Ha)).
      - intro Ha. apply (proj2 (Heq a)). apply (proj2 (Hev a)). exact Ha. }
    apply (IHs Hev0 Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV HUV).
Qed.


(* ============================================================ *)
(* A deterministic result mode for substitution.                *)
(*                                                              *)
(* For an empty-evidence derivation:                            *)
(*  - Lt-rooted derivations stay Lt;                            *)
(*  - Eq-rooted derivations stay Eq, except that if the         *)
(*    self-substitution is Lt and the replaced variable occurs, *)
(*    some reflexive Eq leaf becomes an Lt leaf.                *)
(* ============================================================ *)

Definition res_cm (cm cm0 : CmpMode) (X : atom) (A B : typ) : CmpMode :=
  match cm with
  | Lt => Lt
  | Eq =>
      match cm0 with
      | Eq => Eq
      | Lt =>
          if in_dec X (AtomSetImpl.union (fv_tt A) (fv_tt B))
          then Lt else Eq
      end
  end.

Lemma res_cm_lt : forall cm0 X A B, res_cm Lt cm0 X A B = Lt.
Proof. reflexivity. Qed.

Lemma res_cm_eq_eq : forall X A B, res_cm Eq Eq X A B = Eq.
Proof. reflexivity. Qed.

Lemma res_cm_eq_mem : forall X A B,
  X \in fv_tt A \/ X \in fv_tt B ->
  res_cm Eq Lt X A B = Lt.
Proof.
  intros X A B H. unfold res_cm.
  destruct (in_dec X (AtomSetImpl.union (fv_tt A) (fv_tt B))) as [Hi|Hi].
  - reflexivity.
  - exfalso. apply Hi.
    destruct H as [H|H]; [apply AtomSetImpl.union_2|apply AtomSetImpl.union_3]; exact H.
Qed.

Lemma res_cm_eq_notin : forall X A B,
  X \notin fv_tt A -> X \notin fv_tt B ->
  res_cm Eq Lt X A B = Eq.
Proof.
  intros X A B HA HB. unfold res_cm.
  destruct (in_dec X (AtomSetImpl.union (fv_tt A) (fv_tt B))) as [Hi|Hi].
  - exfalso. apply AtomSetImpl.union_1 in Hi. destruct Hi as [H|H]; [exact (HA H)|exact (HB H)].
  - reflexivity.
Qed.

Lemma fv_tt_open_iff : forall A Y X,
  X <> Y -> (X \in fv_tt (open_tt A Y) <-> X \in fv_tt A).
Proof.
  intros A Y X HXY. split.
  - intro HX.
    destruct (fv_tt_open_rec A 0 (typ_fvar Y) X HX) as [H|H]; [exact H|].
    exfalso. apply HXY. apply AtomSetImpl.singleton_1 in H. symmetry. exact H.
  - intro HX. apply (fv_tt_open_in A 0 Y X HXY HX).
Qed.

Lemma res_cm_mu_open : forall cm0 X Y A B,
  X <> Y ->
  res_cm Eq cm0 X (open_tt A Y) (open_tt B Y) =
  res_cm Eq cm0 X (typ_mu A) (typ_mu B).
Proof.
  intros cm0 X Y A B HXY.
  destruct cm0; [|reflexivity].
  unfold res_cm. simpl.
  destruct (in_dec X (AtomSetImpl.union (fv_tt (open_tt A Y)) (fv_tt (open_tt B Y)))) as [Hi|Ni];
  destruct (in_dec X (AtomSetImpl.union (fv_tt A) (fv_tt B))) as [Ho|No];
  try reflexivity; exfalso.
  - apply No. apply AtomSetImpl.union_1 in Hi. destruct Hi as [H|H].
    + apply AtomSetImpl.union_2. exact (proj1 (fv_tt_open_iff A Y X HXY) H).
    + apply AtomSetImpl.union_3. exact (proj1 (fv_tt_open_iff B Y X HXY) H).
  - apply Ni. apply AtomSetImpl.union_1 in Ho. destruct Ho as [H|H].
    + apply AtomSetImpl.union_2. exact (proj2 (fv_tt_open_iff A Y X HXY) H).
    + apply AtomSetImpl.union_3. exact (proj2 (fv_tt_open_iff B Y X HXY) H).
Qed.

(* compose_cm with empty evidences is Some Lt whenever either input is Lt. *)
Lemma compose_cm_some_lt : forall cm1 cm2,
  (cm1 = Lt \/ cm2 = Lt) ->
  compose_cm cm1 cm2 Metatheory.empty Metatheory.empty = Some Lt.
Proof.
  intros cm1 cm2 H. destruct H as [Heq|Heq].
  - subst cm1. destruct cm2; simpl; try reflexivity; rewrite is_empty_empty; reflexivity.
  - subst cm2. destruct cm1; simpl; try reflexivity; rewrite is_empty_empty; reflexivity.
Qed.

Lemma compose_cm_lt_side : forall cm1 cm2 e1 e2,
  compose_cm cm1 cm2 e1 e2 = Some Lt -> cm1 = Lt \/ cm2 = Lt.
Proof.
  intros cm1 cm2 e1 e2 H.
  destruct cm1, cm2; simpl in H; try discriminate; auto.
Qed.

(* Mode calculation for arrow when the result mode is Eq. *)
Lemma res_cm_arrow_compose_eq : forall cm0 X A1 A2 B1 B2,
  compose_cm
    (res_cm Eq cm0 X B1 A1)
    (res_cm Eq cm0 X A2 B2)
    Metatheory.empty Metatheory.empty =
  Some (res_cm Eq cm0 X (typ_arrow A1 A2) (typ_arrow B1 B2)).
Proof.
  intros cm0 X A1 A2 B1 B2.
  destruct cm0.
  - (* Lt *)
    unfold res_cm. cbn [fv_tt compose_cm].
    destruct (in_dec X (AtomSetImpl.union (fv_tt B1) (fv_tt A1))) as [H1|N1];
    destruct (in_dec X (AtomSetImpl.union (fv_tt A2) (fv_tt B2))) as [H2|N2];
    destruct (in_dec X (AtomSetImpl.union
                         (AtomSetImpl.union (fv_tt A1) (fv_tt A2))
                         (AtomSetImpl.union (fv_tt B1) (fv_tt B2)))) as [Ho|No].
    + reflexivity.
    + exfalso. apply No.
      apply AtomSetImpl.union_1 in H1. destruct H1 as [H1|H1].
      * apply AtomSetImpl.union_3. apply AtomSetImpl.union_2. exact H1.
      * apply AtomSetImpl.union_2. apply AtomSetImpl.union_2. exact H1.
    + unfold compose_cm. simpl. rewrite is_empty_empty. reflexivity.
    + exfalso. apply No.
      apply AtomSetImpl.union_1 in H1. destruct H1 as [H1|H1].
      * apply AtomSetImpl.union_3. apply AtomSetImpl.union_2. exact H1.
      * apply AtomSetImpl.union_2. apply AtomSetImpl.union_2. exact H1.
    + unfold compose_cm. simpl. rewrite is_empty_empty. reflexivity.
    + exfalso. apply No.
      apply AtomSetImpl.union_1 in H2. destruct H2 as [H2|H2].
      * apply AtomSetImpl.union_2. apply AtomSetImpl.union_3. exact H2.
      * apply AtomSetImpl.union_3. apply AtomSetImpl.union_3. exact H2.
    + exfalso.
      apply AtomSetImpl.union_1 in Ho. destruct Ho as [Ho|Ho].
      * apply AtomSetImpl.union_1 in Ho. destruct Ho as [Ho|Ho].
        -- apply N1. apply AtomSetImpl.union_3. exact Ho.
        -- apply N2. apply AtomSetImpl.union_2. exact Ho.
      * apply AtomSetImpl.union_1 in Ho. destruct Ho as [Ho|Ho].
        -- apply N1. apply AtomSetImpl.union_2. exact Ho.
        -- apply N2. apply AtomSetImpl.union_3. exact Ho.
    + reflexivity.
  - reflexivity.
Qed.

Lemma res_cm_nat : forall cmS X, res_cm Eq cmS X typ_nat typ_nat = Eq.
Proof.
  intros [|] X.
  - apply res_cm_eq_notin; simpl; intro H; exact (AtomSetImpl.empty_1 H).
  - reflexivity.
Qed.

Lemma res_cm_top : forall cmS X, res_cm Eq cmS X typ_top typ_top = Eq.
Proof.
  intros [|] X.
  - apply res_cm_eq_notin; simpl; intro H; exact (AtomSetImpl.empty_1 H).
  - reflexivity.
Qed.

(* ============================================================ *)
(* The mode-flexible substitution lemma.                        *)
(* ============================================================ *)

Lemma Sub_subst_empty_gen : forall (X:atom) im cm evs (Ec:env) A B,
  Sub im cm evs Ec A B -> evs [=] Metatheory.empty ->
  forall (Δ:env), Ec = Δ ++ X ~ bind_sub Pos -> wf_env Δ ->
  forall U V, type U -> type V -> X \notin fv_tt U -> X \notin fv_tt V ->
    U <> typ_top -> V <> typ_top ->
    WFS Δ U -> WFS Δ V ->
  forall cmS, Sub Pos cmS emp Δ U V ->
  Sub im (res_cm cm cmS X A B) emp Δ
    (subst_tt X (sL im U V) A) (subst_tt X (sR im U V) B).
Proof.
  intros X im cm evs Ec A B H.
  induction H as [Ec0 im0 Hwf
                 | Ec0 im0 Hwf
                 | Ec0 im0 A0 Hwf HW Hne
                 | Ec0 X0 im0 Hwf Hb
                 | Ec0 X0 im0 Hwf Hb
                 | Ec0 A1 A2 B1 B2 cm1 cm2 evs1 evs2 cmi im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 Ec0 im0 HP IH
                 | L A1 A2 evs0 Ec0 im0 HP IH
                 | L A1 A2 evs0 Ec0 im0 HP IH
                 | im0 cm0 evs0 evs' Ec0 A1 A2 Hs IHs Heq];
    intros Hev Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV cmS HUV.
  - (* nat *)
    rewrite res_cm_nat. apply Sa_nat.
    exact (Sub_wf_env _ _ _ _ _ _ HUV).
  - (* top_eq *)
    rewrite res_cm_top. apply Sa_top_eq.
    exact (Sub_wf_env _ _ _ _ _ _ HUV).
  - (* top_lt *)
    change (Sub im0 Lt emp Δ
      (subst_tt X (sL im0 U V) A0) (subst_tt X (sR im0 U V) typ_top)).
    rewrite HE in HW.
    apply Sa_top_lt.
    + exact (Sub_wf_env _ _ _ _ _ _ HUV).
    + destruct im0.
      * simpl. eapply (WFS_subst_nil (Δ ++ X ~ bind_sub Pos) A0 Δ X Pos V).
        -- exact HW.
        -- reflexivity.
        -- exact HTV.
        -- exact HWV.
      * simpl. eapply (WFS_subst_nil (Δ ++ X ~ bind_sub Pos) A0 Δ X Pos U).
        -- exact HW.
        -- reflexivity.
        -- exact HTU.
        -- exact HWU.
    + destruct im0; simpl; intro Hc.
      * apply Hne. exact (subst_tt_top_inv A0 X V HVt Hc).
      * apply Hne. exact (subst_tt_top_inv A0 X U HUt Hc).
  - (* fvar_pos *)
    rewrite HE in Hb.
    assert (HwfE : wf_env (Δ ++ X ~ bind_sub Pos)) by (rewrite <- HE; exact Hwf).
    assert (HXΔ : X \notin dom Δ).
    { apply (wf_env_mid_fresh Δ X (bind_sub Pos) empty). exact HwfE. }
    destruct (X0 == X) as [Heq|HneX] eqn:Hd.
    + simpl. rewrite Hd. simpl. subst X0.
      rewrite (binds_app_iff binding X (bind_sub im0) Δ (X ~ bind_sub Pos)) in Hb.
      destruct Hb as [HbΔ | HbX].
      * exfalso. exact (binds_dom_contradiction binding X (bind_sub im0) Δ HbΔ HXΔ).
      * apply binds_cons_iff in HbX. destruct HbX as [[Heq2 Hbe]|Hc].
        -- destruct im0.
           ++ (* Neg : impossible against the trailing Pos binder *)
              injection Hbe as Him. discriminate Him.
           ++ (* Pos : exactly the assumed self-subtyping *)
              destruct cmS.
              ** simpl.
                 assert (Hin : X \in AtomSetImpl.union (singleton X) (singleton X)).
                 { apply AtomSetImpl.union_2.
                   apply AtomSetImpl.singleton_2. reflexivity. }
                 destruct (in_dec X (AtomSetImpl.union (singleton X) (singleton X)))
                   as [Hi|Ni].
                 --- exact HUV.
                 --- exfalso. exact (Ni Hin).
              ** simpl. exact HUV.
        -- destruct Hc.
    + simpl. rewrite Hd. simpl.
      assert (Hres :
        (match cmS with
         | Lt => if in_dec X (AtomSetImpl.union (singleton X0) (singleton X0))
                 then Lt else Eq
         | Eq => Eq
         end) = Eq).
      { destruct cmS; [|reflexivity].
        destruct (in_dec X (AtomSetImpl.union (singleton X0) (singleton X0))) as [Hi|Ni].
        - exfalso. apply AtomSetImpl.union_1 in Hi. destruct Hi as [Hc|Hc].
          + apply HneX. exact (@AtomSetImpl.singleton_1 X0 X Hc).
          + apply HneX. exact (@AtomSetImpl.singleton_1 X0 X Hc).
        - reflexivity. }
      rewrite Hres.
      apply Sa_fvar_pos.
      * exact (Sub_wf_env _ _ _ _ _ _ HUV).
      * rewrite (binds_app_iff binding X0 (bind_sub im0) Δ (X ~ bind_sub Pos)) in Hb.
        destruct Hb as [HbΔ | HbX].
        -- exact HbΔ.
        -- apply binds_cons_iff in HbX. destruct HbX as [[Heq2 Hbe]|Hc].
           ++ exfalso. apply HneX. exact Heq2.
           ++ destruct Hc.
  - (* fvar_neg : evidence singleton X0, cannot be empty *)
    exfalso.
    assert (HEmpty : AtomSetImpl.Empty (singleton X0)).
    { apply AtomSetProperties.empty_is_empty_2. exact Hev. }
    exact (HEmpty X0 (@AtomSetImpl.singleton_2 X0 X0 eq_refl)).
  - (* arrow *)
    assert (He1 : evs1 [=] Metatheory.empty) by (apply (union_empty_l evs1 evs2); exact Hev).
    assert (He2 : evs2 [=] Metatheory.empty) by (apply (union_empty_r evs1 evs2); exact Hev).
    destruct cmi.
    + (* result mode Lt *)
      assert (Hlt : cm1 = Lt \/ cm2 = Lt)
        by (apply (compose_cm_lt_side cm1 cm2 evs1 evs2); exact Hc).
      destruct cm1 as [|], cm2 as [|].
      * (* Lt , Lt *)
        assert (H1' : Sub (flip_im im0) Lt emp Δ
            (subst_tt X (sR im0 U V) B1) (subst_tt X (sL im0 U V) A1)).
        { rewrite <- (sL_flip_sR im0 U V), <- (sR_flip_sL im0 U V).
          apply (IH1 He1 Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV cmS HUV). }
        assert (H2' : Sub im0 Lt emp Δ
            (subst_tt X (sL im0 U V) A2) (subst_tt X (sR im0 U V) B2)).
        { apply (IH2 He2 Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV cmS HUV). }
        eapply Sa_evs_proper with (evs := emp \u emp).
        -- eapply Sa_arrow with (cm1:=Lt) (cm2:=Lt).
           ++ exact H1'.
           ++ exact H2'.
           ++ apply (compose_cm_some_lt Lt Lt (or_introl eq_refl)).
        -- apply union_eq_empty; apply eq_empty_refl.
      * (* Lt , Eq *)
        assert (H1' : Sub (flip_im im0) Lt emp Δ
            (subst_tt X (sR im0 U V) B1) (subst_tt X (sL im0 U V) A1)).
        { rewrite <- (sL_flip_sR im0 U V), <- (sR_flip_sL im0 U V).
          apply (IH1 He1 Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV cmS HUV). }
        assert (H2' : Sub im0 (res_cm Eq cmS X A2 B2) emp Δ
            (subst_tt X (sL im0 U V) A2) (subst_tt X (sR im0 U V) B2)).
        { apply (IH2 He2 Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV cmS HUV). }
        eapply Sa_evs_proper with (evs := emp \u emp).
        -- eapply Sa_arrow with (cm1:=Lt) (cm2:=res_cm Eq cmS X A2 B2).
           ++ exact H1'.
           ++ exact H2'.
           ++ apply (compose_cm_some_lt Lt (res_cm Eq cmS X A2 B2) (or_introl eq_refl)).
        -- apply union_eq_empty; apply eq_empty_refl.
      * (* Eq , Lt *)
        assert (H1' : Sub (flip_im im0) (res_cm Eq cmS X B1 A1) emp Δ
            (subst_tt X (sR im0 U V) B1) (subst_tt X (sL im0 U V) A1)).
        { rewrite <- (sL_flip_sR im0 U V), <- (sR_flip_sL im0 U V).
          apply (IH1 He1 Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV cmS HUV). }
        assert (H2' : Sub im0 Lt emp Δ
            (subst_tt X (sL im0 U V) A2) (subst_tt X (sR im0 U V) B2)).
        { apply (IH2 He2 Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV cmS HUV). }
        eapply Sa_evs_proper with (evs := emp \u emp).
        -- eapply Sa_arrow with (cm1:=res_cm Eq cmS X B1 A1) (cm2:=Lt).
           ++ exact H1'.
           ++ exact H2'.
           ++ apply (compose_cm_some_lt (res_cm Eq cmS X B1 A1) Lt (or_intror eq_refl)).
        -- apply union_eq_empty; apply eq_empty_refl.
      * (* Eq , Eq contradicts the Lt conclusion *)
        destruct Hlt as [Hlt|Hlt]; discriminate Hlt.
    + (* result mode Eq *)
      assert (HcEq : cm1 = Eq /\ cm2 = Eq)
        by (apply (compose_cm_eq_inv cm1 cm2 evs1 evs2); exact Hc).
      destruct HcEq as [Hcm1 Hcm2]; subst cm1; subst cm2.
      assert (H1' : Sub (flip_im im0) (res_cm Eq cmS X B1 A1) emp Δ
          (subst_tt X (sR im0 U V) B1) (subst_tt X (sL im0 U V) A1)).
      { rewrite <- (sL_flip_sR im0 U V), <- (sR_flip_sL im0 U V).
        apply (IH1 He1 Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV cmS HUV). }
      assert (H2' : Sub im0 (res_cm Eq cmS X A2 B2) emp Δ
          (subst_tt X (sL im0 U V) A2) (subst_tt X (sR im0 U V) B2)).
      { apply (IH2 He2 Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV cmS HUV). }
      eapply Sa_evs_proper with (evs := emp \u emp).
      * eapply Sa_arrow with
          (cm1:=res_cm Eq cmS X B1 A1) (cm2:=res_cm Eq cmS X A2 B2).
        -- exact H1'.
        -- exact H2'.
        -- apply (res_cm_arrow_compose_eq cmS X A1 A2 B1 B2).
      * apply union_eq_empty; apply eq_empty_refl.
  - (* rec_lt *)
    apply Sa_rec_lt with (L := L \u {{X}} \u dom Δ). intros Y HY.
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HYX : Y \notin {{X}})
      by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
    assert (HYd : Y \notin dom Δ)
      by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
    assert (HYXeq : Y <> X)
      by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
    assert (HwfΔ' : wf_env (Y ~ bind_sub im0 ++ Δ)).
    { apply wf_env_sub with (X:=Y) (im:=im0).
      - exact (Sub_wf_env _ _ _ _ _ _ HUV).
      - exact HYd. }
    assert (HUV' : Sub Pos cmS emp (Y ~ bind_sub im0 ++ Δ) U V).
    { eapply (Sub_insert Pos cmS emp Δ U V HUV empty Y (bind_sub im0) Δ).
      - reflexivity.
      - exact HwfΔ'. }
    assert (HE' : Y ~ bind_sub im0 ++ Ec0 = (Y ~ bind_sub im0 ++ Δ) ++ X ~ bind_sub Pos).
    { rewrite HE. rewrite app_assoc_lr. reflexivity. }
    assert (Hprem : Sub im0 Lt emp (Y ~ bind_sub im0 ++ Δ)
              (subst_tt X (sL im0 U V) (open_tt A1 Y))
              (subst_tt X (sR im0 U V) (open_tt A2 Y))).
    { change (Sub im0 (res_cm Lt cmS X (open_tt A1 Y) (open_tt A2 Y)) emp
              (Y ~ bind_sub im0 ++ Δ)
              (subst_tt X (sL im0 U V) (open_tt A1 Y))
              (subst_tt X (sR im0 U V) (open_tt A2 Y))).
      apply (IH Y HYL Hev (Y ~ bind_sub im0 ++ Δ) HE' HwfΔ' U V HTU HTV HXU HXV HUt HVt).
      - apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWU.
      - apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWV.
      - exact HUV'. }
    change (Sub im0 Lt emp (Y ~ bind_sub im0 ++ Δ)
              (open_tt (subst_tt X (sL im0 U V) A1) Y)
              (open_tt (subst_tt X (sR im0 U V) A2) Y)).
    assert (Heq1 : open_tt (subst_tt X (sL im0 U V) A1) Y =
                   subst_tt X (sL im0 U V) (open_tt A1 Y)).
    { unfold open_tt. apply open_tt_subst_tt.
      - symmetry. exact HYXeq.
      - destruct im0; simpl; assumption. }
    assert (Heq2 : open_tt (subst_tt X (sR im0 U V) A2) Y =
                   subst_tt X (sR im0 U V) (open_tt A2 Y)).
    { unfold open_tt. apply open_tt_subst_tt.
      - symmetry. exact HYXeq.
      - destruct im0; simpl; assumption. }
    rewrite Heq1, Heq2. exact Hprem.
  - (* rec_eq_notin *)
    remember (res_cm Eq cmS X (typ_mu A1) (typ_mu A2)) as r eqn:Hr.
    destruct r as [|].
    + (* output Lt: rebuild the recursive node as rec_lt *)
      apply Sa_rec_lt with (L := L \u {{X}} \u dom Δ). intros Y HY.
      assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
      assert (HYX : Y \notin {{X}})
        by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
      assert (HYd : Y \notin dom Δ)
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
      assert (HYXeq : Y <> X)
        by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
      assert (HwfΔ' : wf_env (Y ~ bind_sub im0 ++ Δ)).
      { apply wf_env_sub with (X:=Y) (im:=im0).
        - exact (Sub_wf_env _ _ _ _ _ _ HUV).
        - exact HYd. }
      assert (HUV' : Sub Pos cmS emp (Y ~ bind_sub im0 ++ Δ) U V).
      { eapply (Sub_insert Pos cmS emp Δ U V HUV empty Y (bind_sub im0) Δ).
        - reflexivity.
        - exact HwfΔ'. }
      assert (HE' : Y ~ bind_sub im0 ++ Ec0 = (Y ~ bind_sub im0 ++ Δ) ++ X ~ bind_sub Pos).
      { rewrite HE. rewrite app_assoc_lr. reflexivity. }
      assert (Hprem0 : Sub im0
        (res_cm Eq cmS X (open_tt A1 Y) (open_tt A2 Y)) emp
        (Y ~ bind_sub im0 ++ Δ)
        (subst_tt X (sL im0 U V) (open_tt A1 Y))
        (subst_tt X (sR im0 U V) (open_tt A2 Y))).
      { apply (IH Y HYL Hev (Y ~ bind_sub im0 ++ Δ) HE' HwfΔ' U V HTU HTV HXU HXV HUt HVt).
        - apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWU.
        - apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWV.
        - exact HUV'. }
      assert (Hmode : res_cm Eq cmS X (open_tt A1 Y) (open_tt A2 Y) = Lt).
      { rewrite (res_cm_mu_open cmS X Y A1 A2 (fun Hc => HYXeq (eq_sym Hc))). symmetry. exact Hr. }
      rewrite Hmode in Hprem0.
      change (Sub im0 Lt emp (Y ~ bind_sub im0 ++ Δ)
                (open_tt (subst_tt X (sL im0 U V) A1) Y)
                (open_tt (subst_tt X (sR im0 U V) A2) Y)).
      assert (Heq1 : open_tt (subst_tt X (sL im0 U V) A1) Y =
                     subst_tt X (sL im0 U V) (open_tt A1 Y)).
      { unfold open_tt. apply open_tt_subst_tt.
        - symmetry. exact HYXeq.
        - destruct im0; simpl; assumption. }
      assert (Heq2 : open_tt (subst_tt X (sR im0 U V) A2) Y =
                     subst_tt X (sR im0 U V) (open_tt A2 Y)).
      { unfold open_tt. apply open_tt_subst_tt.
        - symmetry. exact HYXeq.
        - destruct im0; simpl; assumption. }
      rewrite Heq1, Heq2. exact Hprem0.
    + (* output Eq: rebuild the recursive node as rec_eq_notin *)
      apply Sa_rec_eq_notin with (L := L \u {{X}} \u dom Δ). intros Y HY.
      assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
      assert (HYX : Y \notin {{X}})
        by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
      assert (HYd : Y \notin dom Δ)
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
      assert (HYXeq : Y <> X)
        by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
      assert (HwfΔ' : wf_env (Y ~ bind_sub im0 ++ Δ)).
      { apply wf_env_sub with (X:=Y) (im:=im0).
        - exact (Sub_wf_env _ _ _ _ _ _ HUV).
        - exact HYd. }
      assert (HUV' : Sub Pos cmS emp (Y ~ bind_sub im0 ++ Δ) U V).
      { eapply (Sub_insert Pos cmS emp Δ U V HUV empty Y (bind_sub im0) Δ).
        - reflexivity.
        - exact HwfΔ'. }
      assert (HE' : Y ~ bind_sub im0 ++ Ec0 = (Y ~ bind_sub im0 ++ Δ) ++ X ~ bind_sub Pos).
      { rewrite HE. rewrite app_assoc_lr. reflexivity. }
      assert (Hprem0 : Sub im0
        (res_cm Eq cmS X (open_tt A1 Y) (open_tt A2 Y)) emp
        (Y ~ bind_sub im0 ++ Δ)
        (subst_tt X (sL im0 U V) (open_tt A1 Y))
        (subst_tt X (sR im0 U V) (open_tt A2 Y))).
      { apply (IH Y HYL Hev (Y ~ bind_sub im0 ++ Δ) HE' HwfΔ' U V HTU HTV HXU HXV HUt HVt).
        - apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWU.
        - apply WFS_weaken with (x:=Y) (b:=bind_sub im0). exact HWV.
        - exact HUV'. }
      assert (Hmode : res_cm Eq cmS X (open_tt A1 Y) (open_tt A2 Y) = Eq).
      { rewrite (res_cm_mu_open cmS X Y A1 A2 (fun Hc => HYXeq (eq_sym Hc))). symmetry. exact Hr. }
      rewrite Hmode in Hprem0.
      change (Sub im0 Eq emp (Y ~ bind_sub im0 ++ Δ)
                (open_tt (subst_tt X (sL im0 U V) A1) Y)
                (open_tt (subst_tt X (sR im0 U V) A2) Y)).
      assert (Heq1 : open_tt (subst_tt X (sL im0 U V) A1) Y =
                     subst_tt X (sL im0 U V) (open_tt A1 Y)).
      { unfold open_tt. apply open_tt_subst_tt.
        - symmetry. exact HYXeq.
        - destruct im0; simpl; assumption. }
      assert (Heq2 : open_tt (subst_tt X (sR im0 U V) A2) Y =
                     subst_tt X (sR im0 U V) (open_tt A2 Y)).
      { unfold open_tt. apply open_tt_subst_tt.
        - symmetry. exact HYXeq.
        - destruct im0; simpl; assumption. }
      rewrite Heq1, Heq2. exact Hprem0.
  - (* rec_eq_in *)
    assert (Hev0 : evs0 [=] Metatheory.empty)
      by (apply (union_empty_l evs0 (fv_tt A1)); exact Hev).
    assert (HXe : X \notin evs0)
      by (intro Hc; exact (AtomSetImpl.empty_1 (proj1 (Hev0 X) Hc))).
    assert (HfvA1 : fv_tt A1 [=] Metatheory.empty).
    { apply (union_empty_r evs0 (fv_tt A1)). exact Hev. }
    assert (HXa : X \notin fv_tt A1).
    { intro Hc. exact (AtomSetImpl.empty_1 (proj1 (HfvA1 X) Hc)). }
    assert (Hself : Sub im0 Eq (evs0 \u fv_tt A1) Ec0 (typ_mu A1) (typ_mu A2)).
    { apply Sa_rec_eq_in with (L:=L). exact HP. }
    assert (Hmu : typ_mu A1 = typ_mu A2)
      by (apply (Sub_eq_syntactic im0 Eq (evs0 \u fv_tt A1) Ec0 (typ_mu A1)(typ_mu A2));
          [exact Hself|reflexivity]).
    injection Hmu as HAeq.
    assert (HXa2 : X \notin fv_tt A2) by (rewrite <- HAeq; exact HXa).
    assert (HresEq : res_cm Eq cmS X (typ_mu A1) (typ_mu A2) = Eq).
    { destruct cmS.
      - apply res_cm_eq_notin.
        + simpl. exact HXa.
        + simpl. exact HXa2.
      - reflexivity. }
    rewrite HresEq.
    eapply Sa_evs_proper with (evs := evs0 \u fv_tt A1).
    + simpl. rewrite (subst_tt_notin A1 X (sL im0 U V) HXa).
      rewrite (subst_tt_notin A2 X (sR im0 U V) HXa2).
      apply Sa_rec_eq_in with (L := L \u {{X}} \u dom Δ). intros Y HY.
      assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
      assert (HYX : Y \notin {{X}})
        by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
      assert (HYd : Y \notin dom Δ)
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
      assert (HYXeq : Y <> X)
        by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
      assert (HwfΔ' : wf_env (Y ~ bind_sub im0 ++ Δ)).
      { apply wf_env_sub with (X:=Y) (im:=im0).
        - exact (Sub_wf_env _ _ _ _ _ _ HUV).
        - exact HYd. }
      assert (HXA1o : X \notin fv_tt (open_tt A1 Y)).
      { apply fv_tt_open_notin; [exact HXa | apply notin_singleton_2; exact HYXeq]. }
      assert (HXA2o : X \notin fv_tt (open_tt A2 Y)).
      { apply fv_tt_open_notin; [exact HXa2 | apply notin_singleton_2; exact HYXeq]. }
      assert (HEpres : Y ~ bind_sub im0 ++ Ec0 = (Y ~ bind_sub im0 ++ Δ) ++ X ~ bind_sub Pos).
      { rewrite HE. rewrite app_assoc_lr. reflexivity. }
      eapply (Sub_strengthen_sub_notin im0 Eq (add Y evs0) (Y ~ bind_sub im0 ++ Ec0)
                (open_tt A1 Y) (open_tt A2 Y)).
      * apply HP. exact HYL.
      * exact HEpres.
      * exact HwfΔ'.
      * apply (notin_add_3 Y X evs0); [exact HYXeq|exact HXe].
      * exact HXA1o.
      * exact HXA2o.
    + exact Hev.
  - (* evs_proper *)
    assert (Hev0 : evs0 [=] Metatheory.empty).
    { intro a; split.
      - intro Ha. exact (proj1 (Hev a) (proj1 (Heq a) Ha)).
      - intro Ha. apply (proj2 (Heq a)). apply (proj2 (Hev a)). exact Ha. }
    apply (IHs Hev0 Δ HE HwfΔ U V HTU HTV HXU HXV HUt HVt HWU HWV cmS HUV).
Qed.


(* ============================================================ *)
(* Removing the substituted atom from evidence.                 *)
(* ============================================================ *)

Lemma eq_atoms_trans : forall s1 s2 s3 : atoms,
  s1 [=] s2 -> s2 [=] s3 -> s1 [=] s3.
Proof.
  intros s1 s2 s3 H12 H23 a. split; intro H.
  - apply (proj1 (H23 a)). apply (proj1 (H12 a)). exact H.
  - apply (proj2 (H12 a)). apply (proj2 (H23 a)). exact H.
Qed.

Lemma union_atoms_congr : forall s1 s2 t1 t2 : atoms,
  s1 [=] t1 -> s2 [=] t2 -> s1 \u s2 [=] t1 \u t2.
Proof.
  intros s1 s2 t1 t2 H1 H2 a. split; intro H.
  - apply AtomSetImpl.union_1 in H. destruct H as [H|H].
    + apply AtomSetImpl.union_2. exact (proj1 (H1 a) H).
    + apply AtomSetImpl.union_3. exact (proj1 (H2 a) H).
  - apply AtomSetImpl.union_1 in H. destruct H as [H|H].
    + apply AtomSetImpl.union_2. exact (proj2 (H1 a) H).
    + apply AtomSetImpl.union_3. exact (proj2 (H2 a) H).
Qed.

Lemma remove_empty_eq : forall X, AtomSetImpl.remove X Metatheory.empty [=] Metatheory.empty.
Proof.
  intros X a. split.
  - intro H. exfalso. apply AtomSetImpl.remove_3 in H. exact (AtomSetImpl.empty_1 H).
  - intro H. exfalso. exact (AtomSetImpl.empty_1 H).
Qed.

Lemma remove_singleton_same_eq : forall X,
  AtomSetImpl.remove X (singleton X) [=] Metatheory.empty.
Proof.
  intros X a. split.
  - intro H. apply remove_iff in H. destruct H as [Hin Hneq].
    exfalso. apply Hneq. exact (@AtomSetImpl.singleton_1 X a Hin).
  - intro H. exfalso. exact (AtomSetImpl.empty_1 H).
Qed.

Lemma remove_singleton_other_eq : forall X Y,
  X <> Y -> AtomSetImpl.remove X (singleton Y) [=] singleton Y.
Proof.
  intros X Y HXY a. split.
  - intro H. exact (AtomSetImpl.remove_3 H).
  - intro H. apply remove_iff. split; [exact H|].
    intro HXa. apply HXY.
    assert (HYa : Y = a) by exact (@AtomSetImpl.singleton_1 Y a H).
    transitivity a; [exact HXa|symmetry; exact HYa].
Qed.

Lemma remove_union_eq : forall X s1 s2,
  AtomSetImpl.remove X (s1 \u s2) [=] AtomSetImpl.union (AtomSetImpl.remove X s1) (AtomSetImpl.remove X s2).
Proof.
  intros X s1 s2 a. split.
  - intro H. apply remove_iff in H. destruct H as [Hin Hneq].
    apply AtomSetImpl.union_1 in Hin. destruct Hin as [Hin|Hin].
    + apply AtomSetImpl.union_2. apply remove_iff. split; assumption.
    + apply AtomSetImpl.union_3. apply remove_iff. split; assumption.
  - intro H. apply AtomSetImpl.union_1 in H. destruct H as [H|H].
    + apply remove_iff in H. destruct H as [Hin Hneq].
      apply remove_iff. split; [apply AtomSetImpl.union_2; exact Hin|exact Hneq].
    + apply remove_iff in H. destruct H as [Hin Hneq].
      apply remove_iff. split; [apply AtomSetImpl.union_3; exact Hin|exact Hneq].
Qed.

Lemma remove_add_other : forall Z X s,
  Z <> X ->
  AtomSetImpl.remove X (AtomSetImpl.add Z s) [=]
  AtomSetImpl.add Z (AtomSetImpl.remove X s).
Proof.
  intros Z X s HZX a. split.
  - intro H. apply remove_iff in H. destruct H as [Hin HneqX].
    apply add_iff in Hin. destruct Hin as [HZa|Hs].
    + apply AtomSetImpl.add_1. exact HZa.
    + apply AtomSetImpl.add_2. apply remove_iff. split; assumption.
  - intro H. apply add_iff in H. destruct H as [HZa|Hr].
    + apply remove_iff. split.
      * apply add_iff. left. exact HZa.
      * intro HXa. apply HZX.
        transitivity a; [exact HZa|symmetry; exact HXa].
    + apply remove_iff in Hr. destruct Hr as [Hin HneqX].
      apply remove_iff. split.
      * apply add_iff. right. exact Hin.
      * exact HneqX.
Qed.

Lemma is_empty_remove : forall X s,
  AtomSetImpl.is_empty s = true ->
  AtomSetImpl.is_empty (AtomSetImpl.remove X s) = true.
Proof.
  intros X s HE.
  apply AtomSetImpl.is_empty_1. intros y Hy.
  apply (@AtomSetImpl.is_empty_2 s HE y).
  exact (AtomSetImpl.remove_3 Hy).
Qed.

Lemma compose_cm_remove : forall X cm1 cm2 e1 e2 cm,
  compose_cm cm1 cm2 e1 e2 = Some cm ->
  compose_cm cm1 cm2 (AtomSetImpl.remove X e1) (AtomSetImpl.remove X e2) = Some cm.
Proof.
  intros X cm1 cm2 e1 e2 cm H.
  destruct cm1, cm2, cm; simpl in *; try discriminate;
  destruct (AtomSetImpl.is_empty e1) eqn:E1;
  destruct (AtomSetImpl.is_empty e2) eqn:E2;
  simpl in *; try discriminate; try reflexivity.
  all: try (rewrite (is_empty_remove X e1 E1));
       try (rewrite (is_empty_remove X e2 E2));
       reflexivity.
Qed.

Lemma fv_tt_subst_remove : forall A X U,
  fv_tt U [=] Metatheory.empty ->
  fv_tt (subst_tt X U A) [=] AtomSetImpl.remove X (fv_tt A).
Proof.
  induction A as [| | n | a | A IHA | A1 IH1 A2 IH2];
    intros X U HfvU; simpl in *.
  - symmetry. apply remove_empty_eq.
  - symmetry. apply remove_empty_eq.
  - symmetry. apply remove_empty_eq.
  - destruct (a == X) as [e|ne].
    + subst a. simpl.
      apply eq_atoms_trans with (s2 := Metatheory.empty).
      * exact HfvU.
      * symmetry. apply remove_singleton_same_eq.
    + simpl.
      symmetry. apply remove_singleton_other_eq. symmetry. exact ne.
  - apply IHA. exact HfvU.
  - apply eq_atoms_trans with
      (s2 := AtomSetImpl.union (AtomSetImpl.remove X (fv_tt A1)) (AtomSetImpl.remove X (fv_tt A2))).
    + apply union_atoms_congr; [apply IH1|apply IH2]; exact HfvU.
    + symmetry. apply remove_union_eq.
Qed.

(* ============================================================ *)
(* Substitution by a closed type, deleting the evidence atom.   *)
(* ============================================================ *)

Lemma Sub_subst_remove : forall (X:atom) im cm evs (Ec:env) A B,
  Sub im cm evs Ec A B ->
  forall (Δ:env), Ec = Δ ++ X ~ bind_sub Pos -> wf_env Δ ->
  forall U, type U -> fv_tt U [=] Metatheory.empty -> U <> typ_top ->
    WFS Δ U ->
    Sub Pos Eq emp Δ U U -> Sub Neg Eq emp Δ U U ->
  Sub im cm (AtomSetImpl.remove X evs) Δ
    (subst_tt X U A) (subst_tt X U B).
Proof.
  intros X im cm evs Ec A B H.
  induction H as [Ec0 im0 Hwf
                 | Ec0 im0 Hwf
                 | Ec0 im0 A0 Hwf HW Hne
                 | Ec0 X0 im0 Hwf Hb
                 | Ec0 X0 im0 Hwf Hb
                 | Ec0 A1 A2 B1 B2 cm1 cm2 evs1 evs2 cmi im0 H1 IH1 H2 IH2 Hc
                 | L A1 A2 evs0 Ec0 im0 HP IH
                 | L A1 A2 evs0 Ec0 im0 HP IH
                 | L A1 A2 evs0 Ec0 im0 HP IH
                 | im0 cm0 evs0 evs' Ec0 A1 A2 Hs IHs Heq];
    intros Δ HE HwfΔ U HTU HfvU HUt HWU HselfP HselfN.
  - (* nat *)
    eapply Sa_evs_proper with (evs := emp).
    + apply Sa_nat. exact (Sub_wf_env _ _ _ _ _ _ HselfP).
    + symmetry. apply remove_empty_eq.
  - (* top_eq *)
    eapply Sa_evs_proper with (evs := emp).
    + apply Sa_top_eq. exact (Sub_wf_env _ _ _ _ _ _ HselfP).
    + symmetry. apply remove_empty_eq.
  - (* top_lt *)
    eapply Sa_evs_proper with (evs := emp).
    + rewrite HE in HW.
      apply Sa_top_lt.
      * exact (Sub_wf_env _ _ _ _ _ _ HselfP).
      * eapply (WFS_subst_nil (Δ ++ X ~ bind_sub Pos) A0 Δ X Pos U).
        -- exact HW.
        -- reflexivity.
        -- exact HTU.
        -- exact HWU.
      * intro Hc. apply Hne. exact (subst_tt_top_inv A0 X U HUt Hc).
    + symmetry. apply remove_empty_eq.
  - (* fvar_pos *)
    rewrite HE in Hb.
    assert (HwfE : wf_env (Δ ++ X ~ bind_sub Pos)) by (rewrite <- HE; exact Hwf).
    assert (HXΔ : X \notin dom Δ).
    { apply (wf_env_mid_fresh Δ X (bind_sub Pos) empty). exact HwfE. }
    destruct (X0 == X) as [Heq|HneX] eqn:Hd.
    + simpl. rewrite Hd. simpl. subst X0.
      rewrite (binds_app_iff binding X (bind_sub im0) Δ (X ~ bind_sub Pos)) in Hb.
      destruct Hb as [HbΔ | HbX].
      * exfalso. exact (binds_dom_contradiction binding X (bind_sub im0) Δ HbΔ HXΔ).
      * apply binds_cons_iff in HbX. destruct HbX as [[Heq2 Hbe]|Hc].
        -- destruct im0.
           ++ injection Hbe as Him. discriminate Him.
           ++ eapply Sa_evs_proper with (evs := emp).
              ** exact HselfP.
              ** symmetry. apply remove_empty_eq.
        -- destruct Hc.
    + simpl. rewrite Hd. simpl.
      eapply Sa_evs_proper with (evs := emp).
      * apply Sa_fvar_pos.
        -- exact (Sub_wf_env _ _ _ _ _ _ HselfP).
        -- rewrite (binds_app_iff binding X0 (bind_sub im0) Δ (X ~ bind_sub Pos)) in Hb.
           destruct Hb as [HbΔ | HbX].
           ++ exact HbΔ.
           ++ apply binds_cons_iff in HbX. destruct HbX as [[Heq2 Hbe]|Hc].
              ** exfalso. apply HneX. exact Heq2.
              ** destruct Hc.
      * symmetry. apply remove_empty_eq.
  - (* fvar_neg *)
    rewrite HE in Hb.
    assert (HwfE : wf_env (Δ ++ X ~ bind_sub Pos)) by (rewrite <- HE; exact Hwf).
    assert (HXΔ : X \notin dom Δ).
    { apply (wf_env_mid_fresh Δ X (bind_sub Pos) empty). exact HwfE. }
    destruct (X0 == X) as [Heq|HneX] eqn:Hd.
    + simpl. rewrite Hd. simpl. subst X0.
      rewrite (binds_app_iff binding X (bind_sub (flip_im im0)) Δ (X ~ bind_sub Pos)) in Hb.
      destruct Hb as [HbΔ | HbX].
      * exfalso. exact (binds_dom_contradiction binding X (bind_sub (flip_im im0)) Δ HbΔ HXΔ).
      * apply binds_cons_iff in HbX. destruct HbX as [[Heq2 Hbe]|Hc].
        -- injection Hbe as Hflip.
           destruct im0.
           ++ eapply Sa_evs_proper with (evs := emp).
              ** exact HselfN.
              ** symmetry. apply remove_singleton_same_eq.
           ++ simpl in Hflip. discriminate Hflip.
        -- destruct Hc.
    + simpl. rewrite Hd. simpl.
      eapply Sa_evs_proper with (evs := singleton X0).
      * apply Sa_fvar_neg.
        -- exact (Sub_wf_env _ _ _ _ _ _ HselfP).
        -- rewrite (binds_app_iff binding X0 (bind_sub (flip_im im0)) Δ (X ~ bind_sub Pos)) in Hb.
           destruct Hb as [HbΔ | HbX].
           ++ exact HbΔ.
           ++ apply binds_cons_iff in HbX. destruct HbX as [[Heq2 Hbe]|Hc].
              ** exfalso. apply HneX. exact Heq2.
              ** destruct Hc.
      * symmetry. apply remove_singleton_other_eq. symmetry. exact HneX.
  - (* arrow *)
    assert (H1' : Sub (flip_im im0) cm1 (AtomSetImpl.remove X evs1) Δ
        (subst_tt X U B1) (subst_tt X U A1)).
    { apply (IH1 Δ HE HwfΔ U HTU HfvU HUt HWU HselfP HselfN). }
    assert (H2' : Sub im0 cm2 (AtomSetImpl.remove X evs2) Δ
        (subst_tt X U A2) (subst_tt X U B2)).
    { apply (IH2 Δ HE HwfΔ U HTU HfvU HUt HWU HselfP HselfN). }
    assert (Hcomp : compose_cm cm1 cm2 (AtomSetImpl.remove X evs1) (AtomSetImpl.remove X evs2) = Some cmi)
      by (apply (compose_cm_remove X cm1 cm2 evs1 evs2 cmi); exact Hc).
    eapply Sa_evs_proper with
      (evs := AtomSetImpl.union (AtomSetImpl.remove X evs1) (AtomSetImpl.remove X evs2)).
    + eapply Sa_arrow; [exact H1'|exact H2'|exact Hcomp].
    + symmetry. apply remove_union_eq.
  - (* rec_lt *)
    apply Sa_rec_lt with (L := L \u {{X}} \u dom Δ). intros Y HY.
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HYX : Y \notin {{X}})
      by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
    assert (HYd : Y \notin dom Δ)
      by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
    assert (HYXeq : Y <> X)
      by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
    assert (HwfΔ' : wf_env (Y ~ bind_sub im0 ++ Δ)).
    { apply wf_env_sub with (X:=Y) (im:=im0).
      - exact (Sub_wf_env _ _ _ _ _ _ HselfP).
      - exact HYd. }
    assert (HselfP' : Sub Pos Eq emp (Y ~ bind_sub im0 ++ Δ) U U).
    { eapply (Sub_insert Pos Eq emp Δ U U HselfP empty Y (bind_sub im0) Δ).
      - reflexivity.
      - exact HwfΔ'. }
    assert (HselfN' : Sub Neg Eq emp (Y ~ bind_sub im0 ++ Δ) U U).
    { eapply (Sub_insert Neg Eq emp Δ U U HselfN empty Y (bind_sub im0) Δ).
      - reflexivity.
      - exact HwfΔ'. }
    assert (HWU' : WFS (Y ~ bind_sub im0 ++ Δ) U)
      by (apply WFS_weaken with (x:=Y) (b:=bind_sub im0); exact HWU).
    assert (HE' : Y ~ bind_sub im0 ++ Ec0 = (Y ~ bind_sub im0 ++ Δ) ++ X ~ bind_sub Pos).
    { rewrite HE. rewrite app_assoc_lr. reflexivity. }
    assert (Hprem : Sub im0 Lt (AtomSetImpl.remove X evs0) (Y ~ bind_sub im0 ++ Δ)
              (subst_tt X U (open_tt A1 Y))
              (subst_tt X U (open_tt A2 Y))).
    { apply (IH Y HYL (Y ~ bind_sub im0 ++ Δ) HE' HwfΔ' U HTU HfvU HUt HWU' HselfP' HselfN'). }
    change (Sub im0 Lt (AtomSetImpl.remove X evs0) (Y ~ bind_sub im0 ++ Δ)
              (open_tt (subst_tt X U A1) Y)
              (open_tt (subst_tt X U A2) Y)).
    assert (Heq1 : open_tt (subst_tt X U A1) Y = subst_tt X U (open_tt A1 Y)).
    { unfold open_tt. apply open_tt_subst_tt; [symmetry; exact HYXeq|exact HTU]. }
    assert (Heq2 : open_tt (subst_tt X U A2) Y = subst_tt X U (open_tt A2 Y)).
    { unfold open_tt. apply open_tt_subst_tt; [symmetry; exact HYXeq|exact HTU]. }
    rewrite Heq1, Heq2. exact Hprem.
  - (* rec_eq_notin *)
    apply Sa_rec_eq_notin with (L := L \u {{X}} \u dom Δ). intros Y HY.
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HYX : Y \notin {{X}})
      by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
    assert (HYd : Y \notin dom Δ)
      by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
    assert (HYXeq : Y <> X)
      by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
    assert (HwfΔ' : wf_env (Y ~ bind_sub im0 ++ Δ)).
    { apply wf_env_sub with (X:=Y) (im:=im0).
      - exact (Sub_wf_env _ _ _ _ _ _ HselfP).
      - exact HYd. }
    assert (HselfP' : Sub Pos Eq emp (Y ~ bind_sub im0 ++ Δ) U U).
    { eapply (Sub_insert Pos Eq emp Δ U U HselfP empty Y (bind_sub im0) Δ).
      - reflexivity.
      - exact HwfΔ'. }
    assert (HselfN' : Sub Neg Eq emp (Y ~ bind_sub im0 ++ Δ) U U).
    { eapply (Sub_insert Neg Eq emp Δ U U HselfN empty Y (bind_sub im0) Δ).
      - reflexivity.
      - exact HwfΔ'. }
    assert (HWU' : WFS (Y ~ bind_sub im0 ++ Δ) U)
      by (apply WFS_weaken with (x:=Y) (b:=bind_sub im0); exact HWU).
    assert (HE' : Y ~ bind_sub im0 ++ Ec0 = (Y ~ bind_sub im0 ++ Δ) ++ X ~ bind_sub Pos).
    { rewrite HE. rewrite app_assoc_lr. reflexivity. }
    assert (Hprem : Sub im0 Eq (AtomSetImpl.remove X evs0) (Y ~ bind_sub im0 ++ Δ)
              (subst_tt X U (open_tt A1 Y))
              (subst_tt X U (open_tt A2 Y))).
    { apply (IH Y HYL (Y ~ bind_sub im0 ++ Δ) HE' HwfΔ' U HTU HfvU HUt HWU' HselfP' HselfN'). }
    change (Sub im0 Eq (AtomSetImpl.remove X evs0) (Y ~ bind_sub im0 ++ Δ)
              (open_tt (subst_tt X U A1) Y)
              (open_tt (subst_tt X U A2) Y)).
    assert (Heq1 : open_tt (subst_tt X U A1) Y = subst_tt X U (open_tt A1 Y)).
    { unfold open_tt. apply open_tt_subst_tt; [symmetry; exact HYXeq|exact HTU]. }
    assert (Heq2 : open_tt (subst_tt X U A2) Y = subst_tt X U (open_tt A2 Y)).
    { unfold open_tt. apply open_tt_subst_tt; [symmetry; exact HYXeq|exact HTU]. }
    rewrite Heq1, Heq2. exact Hprem.
  - (* rec_eq_in *)
    assert (Hself : Sub im0 Eq (evs0 \u fv_tt A1) Ec0 (typ_mu A1) (typ_mu A2)).
    { apply Sa_rec_eq_in with (L:=L). exact HP. }
    assert (Hmu : typ_mu A1 = typ_mu A2)
      by (apply (Sub_eq_syntactic im0 Eq (evs0 \u fv_tt A1) Ec0 (typ_mu A1)(typ_mu A2));
          [exact Hself|reflexivity]).
    injection Hmu as HAeq. subst A2.
    eapply Sa_evs_proper with
      (evs := AtomSetImpl.union (AtomSetImpl.remove X evs0) (fv_tt (subst_tt X U A1))).
    + apply Sa_rec_eq_in with (L := L \u {{X}} \u dom Δ). intros Y HY.
      assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
      assert (HYX : Y \notin {{X}})
        by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
      assert (HYd : Y \notin dom Δ)
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
      assert (HYXeq : Y <> X)
        by (intro Hc; apply HYX; apply AtomSetImpl.singleton_2; symmetry; exact Hc).
      assert (HwfΔ' : wf_env (Y ~ bind_sub im0 ++ Δ)).
      { apply wf_env_sub with (X:=Y) (im:=im0).
        - exact (Sub_wf_env _ _ _ _ _ _ HselfP).
        - exact HYd. }
      assert (HselfP' : Sub Pos Eq emp (Y ~ bind_sub im0 ++ Δ) U U).
      { eapply (Sub_insert Pos Eq emp Δ U U HselfP empty Y (bind_sub im0) Δ).
        - reflexivity.
        - exact HwfΔ'. }
      assert (HselfN' : Sub Neg Eq emp (Y ~ bind_sub im0 ++ Δ) U U).
      { eapply (Sub_insert Neg Eq emp Δ U U HselfN empty Y (bind_sub im0) Δ).
        - reflexivity.
        - exact HwfΔ'. }
      assert (HWU' : WFS (Y ~ bind_sub im0 ++ Δ) U)
        by (apply WFS_weaken with (x:=Y) (b:=bind_sub im0); exact HWU).
      assert (HE' : Y ~ bind_sub im0 ++ Ec0 = (Y ~ bind_sub im0 ++ Δ) ++ X ~ bind_sub Pos).
      { rewrite HE. rewrite app_assoc_lr. reflexivity. }
      assert (Hprem0 : Sub im0 Eq (AtomSetImpl.remove X (add Y evs0)) (Y ~ bind_sub im0 ++ Δ)
                (subst_tt X U (open_tt A1 Y))
                (subst_tt X U (open_tt A1 Y))).
      { apply (IH Y HYL (Y ~ bind_sub im0 ++ Δ) HE' HwfΔ' U HTU HfvU HUt HWU' HselfP' HselfN'). }
      assert (Hprem : Sub im0 Eq (add Y (AtomSetImpl.remove X evs0)) (Y ~ bind_sub im0 ++ Δ)
                (subst_tt X U (open_tt A1 Y))
                (subst_tt X U (open_tt A1 Y))).
      { eapply Sa_evs_proper with (evs := AtomSetImpl.remove X (add Y evs0)).
        - exact Hprem0.
        - apply remove_add_other. exact HYXeq. }
      change (Sub im0 Eq (add Y (AtomSetImpl.remove X evs0)) (Y ~ bind_sub im0 ++ Δ)
                (open_tt (subst_tt X U A1) Y)
                (open_tt (subst_tt X U A1) Y)).
      assert (Heq1 : open_tt (subst_tt X U A1) Y = subst_tt X U (open_tt A1 Y)).
      { unfold open_tt. apply open_tt_subst_tt; [symmetry; exact HYXeq|exact HTU]. }
      rewrite Heq1. exact Hprem.
    + apply eq_atoms_trans with
        (s2 := AtomSetImpl.union (AtomSetImpl.remove X evs0)
                 (AtomSetImpl.remove X (fv_tt A1))).
      * apply union_atoms_congr.
        -- reflexivity.
        -- apply fv_tt_subst_remove. exact HfvU.
      * symmetry. apply remove_union_eq.
  - (* evs_proper *)
    eapply Sa_evs_proper with (evs := AtomSetImpl.remove X evs0).
    + apply (IHs Δ HE HwfΔ U HTU HfvU HUt HWU HselfP HselfN).
    + apply AtomSetProperties.Equal_remove. exact Heq.
Qed.


(* ============================================================ *)
(* Unfolding at the top level.                                  *)
(* ============================================================ *)

Lemma Sub_unfold_nil_aux : forall im cm evs A B MA MB E,
  im = Pos -> E = nil ->
  MA = typ_mu A -> MB = typ_mu B ->
  Sub im cm evs E MA MB ->
  exists cm' evs', Sub Pos cm' evs' nil
    (open_tt A MA) (open_tt B MB).
Proof.
  intros im cm evs A B MA MB E Him HE EA EB Hroot.
  induction Hroot.
  - (* nat *)
    discriminate EA.
  - (* top_eq *)
    discriminate EA.
  - (* top_lt *)
    discriminate EB.
  - (* fvar_pos *)
    discriminate EA.
  - (* fvar_neg *)
    discriminate EA.
  - (* arrow *)
    discriminate EA.
  - (* rec_lt *)
    injection EA as HA. injection EB as HB.
    subst A. subst B. subst E. subst im.
    assert (Hfull : Sub Pos Lt evs nil (typ_mu A1) (typ_mu A2)).
    { apply Sa_rec_lt with (L:=L). intros X HX. exact (H X HX). }
    assert (Hev : evs [=] Metatheory.empty).
    { intro a. split.
      - intro Ha. exfalso.
        exact (Sub_evs_nil Pos Lt evs (typ_mu A1) (typ_mu A2) Hfull a Ha).
      - intro Ha. exfalso. exact (AtomSetImpl.empty_1 Ha). }
    assert (Hemp : Sub Pos Lt emp nil (typ_mu A1) (typ_mu A2)).
    { eapply Sa_evs_proper; [exact Hfull | exact Hev]. }
    destruct (Sub_wfs Pos Lt emp nil (typ_mu A1) (typ_mu A2) Hemp)
      as [HWU HWV].
    assert (HTU : type (typ_mu A1)) by (apply (WFS_type nil); exact HWU).
    assert (HTV : type (typ_mu A2)) by (apply (WFS_type nil); exact HWV).
    assert (HUt : typ_mu A1 <> typ_top) by (intro Hc; discriminate Hc).
    assert (HVt : typ_mu A2 <> typ_top) by (intro Hc; discriminate Hc).
    destruct (exists_fresh_notin (L \u fv_tt A1 \u fv_tt A2)) as [Y HY].
    assert (HYL : Y \notin L)
      by (apply notin_union_1 in HY; exact HY).
    assert (HY1 : Y \notin fv_tt A1)
      by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
    assert (HY2 : Y \notin fv_tt A2)
      by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
    assert (HYU : Y \notin fv_tt (typ_mu A1)) by (simpl; exact HY1).
    assert (HYV : Y \notin fv_tt (typ_mu A2)) by (simpl; exact HY2).
    pose proof (Sub_subst_empty_gen Y Pos Lt evs (Y ~ bind_sub Pos ++ nil)
                  (open_tt A1 Y) (open_tt A2 Y) (H Y HYL) Hev
                  nil eq_refl wf_env_empty
                  (typ_mu A1) (typ_mu A2) HTU HTV HYU HYV HUt HVt HWU HWV
                  Lt Hemp) as Hsub.
    simpl in Hsub.
    unfold open_tt in Hsub.
    rewrite (subst_tt_open_tt_self A1 Y (typ_mu A1) 0 HY1) in Hsub.
    rewrite (subst_tt_open_tt_self A2 Y (typ_mu A2) 0 HY2) in Hsub.
    unfold open_tt. exists Lt, emp. exact Hsub.
  - (* rec_eq_notin *)
    injection EA as HA. injection EB as HB.
    subst A. subst B. subst E. subst im.
    assert (Hfull : Sub Pos Eq evs nil (typ_mu A1) (typ_mu A2)).
    { apply Sa_rec_eq_notin with (L:=L). intros X HX. exact (H X HX). }
    assert (Hev : evs [=] Metatheory.empty).
    { intro a. split.
      - intro Ha. exfalso.
        exact (Sub_evs_nil Pos Eq evs (typ_mu A1) (typ_mu A2) Hfull a Ha).
      - intro Ha. exfalso. exact (AtomSetImpl.empty_1 Ha). }
    assert (Hemp : Sub Pos Eq emp nil (typ_mu A1) (typ_mu A2)).
    { eapply Sa_evs_proper; [exact Hfull | exact Hev]. }
    destruct (Sub_wfs Pos Eq emp nil (typ_mu A1) (typ_mu A2) Hemp)
      as [HWU HWV].
    assert (HTU : type (typ_mu A1)) by (apply (WFS_type nil); exact HWU).
    assert (HTV : type (typ_mu A2)) by (apply (WFS_type nil); exact HWV).
    assert (HUt : typ_mu A1 <> typ_top) by (intro Hc; discriminate Hc).
    assert (HVt : typ_mu A2 <> typ_top) by (intro Hc; discriminate Hc).
    destruct (exists_fresh_notin (L \u fv_tt A1 \u fv_tt A2)) as [Y HY].
    assert (HYL : Y \notin L)
      by (apply notin_union_1 in HY; exact HY).
    assert (HY1 : Y \notin fv_tt A1)
      by (apply notin_union_2 in HY; apply notin_union_1 in HY; exact HY).
    assert (HY2 : Y \notin fv_tt A2)
      by (apply notin_union_2 in HY; apply notin_union_2 in HY; exact HY).
    assert (HYU : Y \notin fv_tt (typ_mu A1)) by (simpl; exact HY1).
    assert (HYV : Y \notin fv_tt (typ_mu A2)) by (simpl; exact HY2).
    pose proof (Sub_subst_empty_gen Y Pos Eq evs (Y ~ bind_sub Pos ++ nil)
                  (open_tt A1 Y) (open_tt A2 Y) (H Y HYL) Hev
                  nil eq_refl wf_env_empty
                  (typ_mu A1) (typ_mu A2) HTU HTV HYU HYV HUt HVt HWU HWV
                  Eq Hemp) as Hsub.
    simpl in Hsub.
    unfold open_tt in Hsub.
    rewrite (subst_tt_open_tt_self A1 Y (typ_mu A1) 0 HY1) in Hsub.
    rewrite (subst_tt_open_tt_self A2 Y (typ_mu A2) 0 HY2) in Hsub.
    unfold open_tt. exists Eq, emp. exact Hsub.
  - (* rec_eq_in *)
    injection EA as HA. injection EB as HB.
    subst A. subst B. subst E. subst im.
    assert (Hfull : Sub Pos Eq (evs \u fv_tt A1) nil
                      (typ_mu A1) (typ_mu A2)).
    { apply Sa_rec_eq_in with (L:=L). exact H. }
    assert (Hevfull : (evs \u fv_tt A1) [=] Metatheory.empty).
    { intro a. split.
      - intro Ha. exfalso.
        exact (Sub_evs_nil Pos Eq (evs \u fv_tt A1)
                 (typ_mu A1) (typ_mu A2) Hfull a Ha).
      - intro Ha. exfalso. exact (AtomSetImpl.empty_1 Ha). }
    assert (Hemp : Sub Pos Eq emp nil (typ_mu A1) (typ_mu A2)).
    { eapply Sa_evs_proper; [exact Hfull | exact Hevfull]. }
    assert (Hmu : typ_mu A1 = typ_mu A2)
      by (apply (Sub_eq_syntactic Pos Eq emp nil (typ_mu A1) (typ_mu A2));
          [exact Hemp | reflexivity]).
    injection Hmu as HA2. subst A2.
    (* Now A1 = A2, and Hemp is the reflexive premise at U = mu A1. *)
    pose proof (Sub_wfs Pos Eq emp nil (typ_mu A1) (typ_mu A1) Hemp)
      as HF.
    destruct HF as [HWU _].
    assert (HTU : type (typ_mu A1)) by (apply (WFS_type nil); exact HWU).
    assert (HUt : typ_mu A1 <> typ_top) by (intro Hc; discriminate Hc).
    assert (HfvU : fv_tt (typ_mu A1) [=] Metatheory.empty).
    { intro a. split.
      - intro Ha. exfalso.
        exact (Sub_closed_nil_left Pos Eq emp (typ_mu A1) (typ_mu A1)
                 Hemp a Ha).
      - intro Ha. exfalso. exact (AtomSetImpl.empty_1 Ha). }
    assert (HselfN : Sub Neg Eq emp nil (typ_mu A1) (typ_mu A1)).
    { pose proof (Sub_dual Pos Eq emp nil (typ_mu A1) (typ_mu A1) Hemp)
        as Hd.
      simpl in Hd. exact Hd. }
    destruct (exists_fresh_notin (L \u fv_tt A1)) as [Y HY].
    assert (HYL : Y \notin L) by (apply notin_union_1 in HY; exact HY).
    assert (HY1 : Y \notin fv_tt A1) by (apply notin_union_2 in HY; exact HY).
    pose proof (Sub_subst_remove Y Pos Eq (add Y evs)
                  (Y ~ bind_sub Pos ++ nil)
                  (open_tt A1 Y) (open_tt A1 Y) (H Y HYL)
                  nil eq_refl wf_env_empty (typ_mu A1)
                  HTU HfvU HUt HWU Hemp HselfN) as Hsub.
    simpl in Hsub.
    unfold open_tt in Hsub.
    rewrite (subst_tt_open_tt_self A1 Y (typ_mu A1) 0 HY1) in Hsub.
    unfold open_tt. exists Eq, (AtomSetImpl.remove Y (add Y evs)). exact Hsub.
  - (* evs_proper *)
    exact (IHHroot Him HE EA EB).
Qed.

Lemma Sub_unfold_nil_pos : forall cm evs A B,
  Sub Pos cm evs nil (typ_mu A) (typ_mu B) ->
  exists cm' evs', Sub Pos cm' evs' nil
    (open_tt A (typ_mu A)) (open_tt B (typ_mu B)).
Proof.
  intros cm evs A B H.
  exact (Sub_unfold_nil_aux Pos cm evs A B (typ_mu A) (typ_mu B) nil
           eq_refl eq_refl eq_refl eq_refl H).
Qed.

Lemma Sub_unfold_nil : forall im cm evs A B,
  Sub im cm evs nil (typ_mu A) (typ_mu B) ->
  exists cm' evs', Sub im cm' evs' nil
    (open_tt A (typ_mu A)) (open_tt B (typ_mu B)).
Proof.
  intros im cm evs A B H.
  assert (Hpos : Sub Pos cm evs nil (typ_mu A) (typ_mu B)).
  { destruct im.
    - apply Sub_dual in H. simpl in H. exact H.
    - exact H. }
  destruct (Sub_unfold_nil_pos cm evs A B Hpos) as [cm' [evs' Hsub]].
  exists cm', evs'.
  destruct im.
  - apply Sub_dual in Hsub. simpl in Hsub. exact Hsub.
  - exact Hsub.
Qed.

Lemma typing_fold_inv_mu_gen : forall G e U,
  typing G e U ->
  G = nil ->
  forall A v T, e = exp_fold (typ_mu A) v -> U = typ_mu T ->
  typing G v (open_tt T (typ_mu T)).
Proof.
  intros G e U H.
  induction H as [G0 Hwf
                 | G0 x T0 Hwf Hb
                 | L G0 T1 e0 T2 HP IH
                 | G0 e1 e2 T2 T1 H1 IH1 H2 IH2
                 | G0 A0 e0 H1 IH1 Hw
                 | G0 T0 e0 H1 IH1
                 | G0 T0 e0 S evs cm H1 IH1 Hs];
    intros HG A v T He HU.
  - discriminate He.
  - discriminate He.
  - discriminate He.
  - discriminate He.
  - inversion He; subst. inversion HU; subst. exact H1.
  - discriminate He.
  - subst G0. subst T0.
    destruct (typing_fold_shape empty e0 S H1 (typ_mu A) v He) as [Htop|Hmu].
    + assert (Hbad : typ_mu T = typ_top)
        by exact (Sub_top_inv Pos cm evs empty S (typ_mu T) Hs Htop).
      discriminate Hbad.
    + destruct Hmu as [T' HT]. subst S.
      destruct (Sub_unfold_nil Pos cm evs T' T Hs) as [cm' [evs' Hsub]].
      eapply typing_sub with (S := open_tt T' (typ_mu T')).
      * apply (IH1 eq_refl A v T' He eq_refl).
      * exact Hsub.
Qed.

Lemma typing_fold_inv_mu_nil : forall A v T,
  typing nil (exp_fold (typ_mu A) v) (typ_mu T) ->
  typing nil v (open_tt T (typ_mu T)).
Proof.
  intros A v T H.
  apply (typing_fold_inv_mu_gen nil (exp_fold (typ_mu A) v) (typ_mu T) H eq_refl A v T eq_refl eq_refl).
Qed.

Lemma preservation_gen : forall G e T,
  typing G e T -> G = nil -> forall e', step e e' -> typing G e' T.
Proof.
  intros G e T H.
  induction H as [G0 Hwf
                 | G0 x T0 Hwf Hb
                 | L G0 T1 e0 T2 HP IH
                 | G0 e1 e2 T2 T1 H1 IH1 H2 IH2
                 | G0 A e0 H1 IH1 Hw
                 | G0 T0 e0 H1 IH1
                 | G0 T0 e0 S evs cm H1 IH1 Hs];
    intros HG e' Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - subst G0.
    inversion Hstep; subst.
    + exact (typing_abs_beta T e0 T1 T2 H1 e2 H2).
    + eapply typing_app.
      * apply (IH1 eq_refl). exact H5.
      * exact H2.
    + eapply typing_app.
      * exact H1.
      * apply (IH2 eq_refl). exact H5.
  - subst G0.
    inversion Hstep; subst.
    apply typing_fold with (A:=A).
    + apply (IH1 eq_refl). exact H2.
    + exact Hw.
  - subst G0.
    inversion Hstep; subst.
    + destruct (typing_fold_ann_wfs empty (exp_fold T e') (typ_mu T0) H1 T e' eq_refl) as [A [HT HWFA]].
      subst T.
      exact (typing_fold_inv_mu_nil A e' T0 H1).
    + apply typing_unfold. apply (IH1 eq_refl). exact H2.
  - subst G0. apply typing_sub with (S:=S) (cm:=cm) (evs:=evs).
    + exact (IH1 eq_refl e' Hstep).
    + exact Hs.
Qed.

Theorem preservation : forall e e' T,
    typing nil e T ->
    step e e' ->
    typing nil e' T.
Proof.
  intros e e' T H Hstep.
  exact (preservation_gen nil e T H eq_refl e' Hstep).
Qed.

Theorem progress : forall e T,
  typing empty e T ->
  value e \/ exists e', step e e'.
Proof.
  intros e T H. apply (progress_gen empty e T H). reflexivity.
Qed.
