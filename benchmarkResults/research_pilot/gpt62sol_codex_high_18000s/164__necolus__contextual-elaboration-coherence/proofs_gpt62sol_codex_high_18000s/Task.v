Require Import Metalib.Metatheory.

Require Import Observations Infrastructure target_inf.

Definition ctx_equiv Γ E1 E2 A := forall e1 e2 dir dir' C c,
    has_type Γ E1 dir A e1 ->
    has_type Γ E2 dir A e2 ->
    CTyp C Γ dir A nil dir' styp_nat c ->
    kleene_equiv (appctx c e1) (appctx c e2).

From Stdlib Require Import Lia.

Local Hint Constructors Infrastructure.star lc_exp value step degree_exp_wrt_exp : necolus.

Lemma ne_star_trans : forall e f g, e ->* f -> f ->* g -> e ->* g.
Proof. intros e f g H; induction H; eauto with necolus. Qed.

Lemma ne_star_step : forall e f, step e f -> e ->* f.
Proof. eauto with necolus. Qed.

Lemma ne_star_map : forall (F : exp -> exp),
    (forall e f, step e f -> step (F e) (F f)) ->
    forall e f, e ->* f -> F e ->* F f.
Proof. intros F HF e f H; induction H; eauto with necolus. Qed.

Lemma ne_value_lc : forall v, value v -> lc_exp v.
Proof. induction 1; auto with necolus. Qed.

Lemma ne_value_irred : forall v, value v -> forall t, ~ step v t.
Proof. induction 1; intros t Hs; inversion Hs; subst; firstorder. Qed.

Lemma ne_step_det : forall e f, step e f -> forall g, step e g -> f = g.
Proof.
  induction 1; intros g Hg; inversion Hg; subst;
    try reflexivity; try solve [f_equal; eauto];
    repeat match goal with
    | H : value (trm_pair _ _) |- _ => inversion H; clear H; subst
    | H : value (trm_rcd _ _) |- _ => inversion H; clear H; subst
    end;
    try match goal with
    | Hs : step ?v ?w |- _ =>
        let Hv := fresh in
        assert (Hv : value v) by (eauto 8 with necolus);
        exact (False_rect _ (ne_value_irred v Hv w Hs))
    end.
Qed.

Lemma ne_eval_unique : forall e v w,
    e ->* v -> e ->* w -> value v -> value w -> v = w.
Proof.
  intros e v w H; revert w.
  induction H; intros w Hw Hv Hwv; inversion Hw; subst; auto.
  - exfalso; match goal with Hv : value ?v, Hs : step ?v ?w |- _ => exact (ne_value_irred v Hv w Hs) end.
  - exfalso; match goal with Hv : value ?v, Hs : step ?v ?w |- _ => exact (ne_value_irred v Hv w Hs) end.
  - assert (b = b0) by (eapply ne_step_det; eauto). subst; eauto.
Qed.

Lemma ne_app_steps : forall e f v w,
    lc_exp f -> value v -> e ->* v -> f ->* w ->
    trm_app e f ->* trm_app v w.
Proof.
  intros; eapply ne_star_trans.
  - apply (ne_star_map (fun t => trm_app t f)); eauto with necolus.
  - apply (ne_star_map (trm_app v)); eauto with necolus.
Qed.

Lemma ne_pair_steps : forall e f v w,
    lc_exp f -> value v -> e ->* v -> f ->* w ->
    trm_pair e f ->* trm_pair v w.
Proof.
  intros; eapply ne_star_trans.
  - apply (ne_star_map (fun t => trm_pair t f)); eauto with necolus.
  - apply (ne_star_map (trm_pair v)); eauto with necolus.
Qed.

Lemma ne_capp_steps : forall c e v, e ->* v -> trm_capp c e ->* trm_capp c v.
Proof. intros; apply ne_star_map; eauto with necolus. Qed.

Lemma ne_rcd_steps : forall l e v, e ->* v -> trm_rcd l e ->* trm_rcd l v.
Proof. intros; apply ne_star_map; eauto with necolus. Qed.

Lemma ne_proj_steps : forall l e v, e ->* v -> trm_proj e l ->* trm_proj v l.
Proof. intros; apply (ne_star_map (fun t => trm_proj t l)); eauto with necolus. Qed.

Definition ne_first v := match v with trm_pair a _ => a | _ => trm_unit end.
Definition ne_second v := match v with trm_pair _ b => b | _ => trm_unit end.
Definition ne_field v := match v with trm_rcd _ a => a | _ => trm_unit end.

Definition ne_eval (P : exp -> Prop) e := exists v, e ->* v /\ P v.

(* Unary reducibility supplies terminating applications even when an argument
   has no related counterpart. *)
Fixpoint ne_good (A : styp) (v : exp) : Prop :=
  match A with
  | styp_top => v = trm_unit
  | styp_nat => exists n, v = trm_lit n
  | styp_and B C =>
      exists b c, v = trm_pair b c /\ ne_good B b /\ ne_good C c
  | styp_arrow B C =>
      value v /\ forall b, ne_good B b -> ne_eval (ne_good C) (trm_app v b)
  | styp_rcd l B =>
      exists b, v = trm_rcd l b /\ ne_good B b
  end.

Lemma ne_good_value : forall A v, ne_good A v -> value v.
Proof.
  induction A; simpl; intros v H.
  - subst; constructor.
  - destruct H as [n ->]; constructor.
  - destruct H as (a & b & -> & ? & ?); eauto with necolus.
  - tauto.
  - destruct H as (a & -> & ?); eauto with necolus.
Qed.

Local Hint Resolve ne_good_value ne_value_lc ne_star_step ne_star_trans
  ne_app_steps ne_pair_steps ne_capp_steps ne_rcd_steps ne_proj_steps : necolus.

Definition ne_eval2 (R : exp -> exp -> Prop) e f :=
  exists v w, e ->* v /\ f ->* w /\ value v /\ value w /\ R v w.

Fixpoint ne_split (P : styp -> exp -> Prop) (B : styp) (w : exp) : Prop :=
  match B with
  | styp_and B1 B2 => ne_split P B1 (ne_first w) /\ ne_split P B2 (ne_second w)
  | _ => P B w
  end.

(* Two values agree at every shared sequence of applications and field
   selections leading to a number. Intersections expose both components. *)
Fixpoint ne_rel (A B : styp) (v w : exp) {struct A} : Prop :=
  match A with
  | styp_top => True
  | styp_nat =>
      ne_split (fun X u => match X with styp_nat => v = u | _ => True end) B w
  | styp_and A1 A2 => ne_rel A1 B (ne_first v) w /\ ne_rel A2 B (ne_second v) w
  | styp_arrow A1 A2 =>
      ne_split (fun X u =>
        match X with
        | styp_arrow X1 X2 =>
            forall a x, ne_good A1 a -> ne_good X1 x -> ne_rel A1 X1 a x ->
              ne_eval2 (ne_rel A2 X2) (trm_app v a) (trm_app u x)
        | _ => True
        end) B w
  | styp_rcd l A1 =>
      ne_split (fun X u =>
        match X with
        | styp_rcd k X1 => l = k -> ne_rel A1 X1 (ne_field v) (ne_field u)
        | _ => True
        end) B w
  end.

Lemma ne_rel_right_pair : forall A B C v w,
    ne_rel A (styp_and B C) v w <->
    ne_rel A B v (ne_first w) /\ ne_rel A C v (ne_second w).
Proof.
  induction A; intros; simpl; try tauto.
  rewrite IHA1, IHA2; tauto.
Qed.

Lemma ne_rel_right_top : forall A v w, ne_rel A styp_top v w.
Proof. induction A; simpl; auto. Qed.

Lemma ne_rel_left_pair : forall A B C v w,
    ne_rel (styp_and A B) C v w <->
    ne_rel A C (ne_first v) w /\ ne_rel B C (ne_second v) w.
Proof. reflexivity. Qed.

Lemma ne_rel_flip : forall A B v w, ne_rel A B v w <-> ne_rel B A w v.
Proof.
  induction A; induction B; intros v w;
    try solve [split; intros; first [exact I | apply ne_rel_right_top]];
    try solve [
      progress (repeat (rewrite ne_rel_left_pair || rewrite ne_rel_right_pair));
      try rewrite IHA1; try rewrite IHA2;
      try rewrite IHB1; try rewrite IHB2; tauto];
    simpl; try tauto; try solve [split; congruence].
  - repeat rewrite ne_rel_right_pair.
    rewrite !IHA1, !IHA2. tauto.
  - split; intros H x a Hx Ha Hax.
    + destruct (H a x Ha Hx (proj2 (IHA1 _ _ _) Hax))
        as (u & z & ? & ? & ? & ? & ?).
      exists z, u; repeat split; auto; apply IHA2; assumption.
    + destruct (H a x Ha Hx (proj1 (IHA1 _ _ _) Hax))
        as (u & z & ? & ? & ? & ? & ?).
      exists z, u; repeat split; auto; apply IHA2; assumption.
  - split; intros H E; apply IHA, H; congruence.
Qed.

Lemma ne_rel_sym : forall A B v w, ne_rel A B v w -> ne_rel B A w v.
Proof. intros; apply ne_rel_flip; assumption. Qed.


(* A property of the right-hand component that respects intersections can
   be proved by considering each of its non-intersection components. *)
Lemma ne_right_cases : forall (P : styp -> exp -> Prop),
    (forall A B a b, P A a -> P B b -> P (styp_and A B) (trm_pair a b)) ->
    (forall X w, (forall A B, X <> styp_and A B) -> ne_good X w -> P X w) ->
    forall X w, ne_good X w -> P X w.
Proof.
  intros P Hpair Hleaf X; induction X; intros w Hw;
    try solve [apply Hleaf; [intros; discriminate | assumption]].
  destruct Hw as (a & b & -> & Ha & Hb); auto.
Qed.

Lemma ne_disjoint_rel : forall A B, disjoint A B ->
    forall v w, ne_good A v -> ne_good B w -> ne_rel A B v w.
Proof.
  induction 1; intros v w Hv Hw; try exact I.
  - apply ne_rel_right_top.
  - intros a b Ha Hb _.
    destruct Hv as [Hv HF]; destruct Hw as [Hw HG].
    destruct (HF _ Ha) as (r & Hr & Hgr).
    destruct (HG _ Hb) as (s & Hs & Hgs).
    exists r, s; repeat split; eauto with necolus.
  - destruct Hv as (a & b & -> & Ha & Hb); simpl; auto.
  - destruct Hw as (a & b & -> & Ha & Hb).
    apply ne_rel_right_pair; simpl; auto.
  - destruct Hv as (a & -> & Ha), Hw as (b & -> & Hb); simpl; auto.
  - simpl; congruence.
Qed.

Lemma ne_app_cast_steps : forall c1 c2 f a b r s,
    value f -> value a ->
    trm_capp c1 a ->* b -> trm_app f b ->* r -> trm_capp c2 r ->* s ->
    trm_app (trm_capp (co_arr c1 c2) f) a ->* s.
Proof.
  intros; eapply star_step; [apply step_arr; assumption |].
  eapply ne_star_trans; [apply ne_capp_steps | eassumption].
  eapply ne_star_trans; [apply (ne_star_map (trm_app f)) | eassumption].
  - eauto with necolus.
  - assumption.
Qed.

Lemma ne_eval2_sync : forall A B e f v w,
    e ->* v -> f ->* w -> ne_good A v -> ne_good B w ->
    ne_eval2 (ne_rel A B) e f -> ne_rel A B v w.
Proof.
  intros A B e f v w He Hf Hv Hw (a & b & Hea & Hfb & Ha & Hb & Hr).
  assert (v = a) by (eapply ne_eval_unique; eauto with necolus).
  assert (w = b) by (eapply ne_eval_unique; eauto with necolus).
  now subst.
Qed.

Local Ltac ne_co_leaf X Hleaf :=
  destruct X; try exact I; try solve [exfalso; eapply Hleaf; reflexivity];
  try solve [intro; congruence].

(* A coercion preserves reducibility and each comparison with another type.
   Symmetry then allows coercions on both sides of a comparison. *)
Lemma ne_sub_transport : forall A B c, sub A B c ->
    forall v, ne_good A v ->
    exists w, trm_capp c v ->* w /\ ne_good B w /\
      forall X u, ne_good X u -> ne_rel A X v u -> ne_rel B X w u.
Proof.
  induction 1; intros v Hv.
  - exists v; repeat split; eauto with necolus.
  - destruct (IHsub2 _ Hv) as (m & Hm & Hgm & Hrm).
    destruct (IHsub1 _ Hgm) as (w & Hw & Hgw & Hrw).
    exists w; split.
    + eapply star_step; [apply step_trans; eauto with necolus |].
      eauto using ne_star_trans, ne_capp_steps.
    + split; eauto.
  - exists trm_unit; repeat split; eauto with necolus.
  - change (v = trm_unit) in Hv; subst.
    exists (trm_capp co_topArr trm_unit); split; [constructor |].
    split.
    + split; [eauto with necolus |].
      intros a Ha; change (a = trm_unit) in Ha; subst.
      exists trm_unit; split; [eauto with necolus | reflexivity].
    + refine (ne_right_cases (fun X u =>
        ne_rel styp_top X trm_unit u ->
        ne_rel (styp_arrow styp_top styp_top) X (trm_capp co_topArr trm_unit) u) _ _).
      * intros C D a b Ha Hb Hr; apply ne_rel_right_pair; auto.
      * intros X u Hleaf Hu Hr; ne_co_leaf X Hleaf.
        intros a b Ha Hb Hab; change (a = trm_unit) in Ha; subst.
        destruct Hu as [Hu HF].
        destruct (HF _ Hb) as (r & Hr' & Hgr).
        exists trm_unit, r; repeat split; eauto with necolus.
  - change (v = trm_unit) in Hv; subst.
    exists (trm_rcd l trm_unit); split; [eauto with necolus |].
    split; [exists trm_unit; split; reflexivity |].
    refine (ne_right_cases (fun X u =>
        ne_rel styp_top X trm_unit u -> ne_rel (styp_rcd l styp_top) X (trm_rcd l trm_unit) u) _ _).
    + intros C D a b Ha Hb Hr; apply ne_rel_right_pair; auto.
    + intros X u Hleaf Hu Hr; ne_co_leaf X Hleaf. exact (fun _ => I).
  - destruct Hv as [Hv HF].
    exists (trm_capp (co_arr c1 c2) v); split; [constructor |].
    split.
    + split; [auto with necolus |].
      intros a Ha.
      destruct (IHsub1 _ Ha) as (b & Hb & Hgb & _).
      destruct (HF _ Hgb) as (r & Hr & Hgr).
      destruct (IHsub2 _ Hgr) as (s & Hs & Hgs & _).
      exists s; split; eauto using ne_app_cast_steps with necolus.
    + refine (ne_right_cases (fun X u =>
        ne_rel (styp_arrow A1 A2) X v u -> ne_rel (styp_arrow B1 B2) X (trm_capp (co_arr c1 c2) v) u) _ _).
      * intros C D a b Ha Hb Hr; apply ne_rel_right_pair; split;
          [apply Ha | apply Hb]; apply ne_rel_right_pair in Hr; tauto.
      * intros X u Hleaf Hu Hvu; ne_co_leaf X Hleaf.
        intros a x Ha Hx Hax.
        destruct (IHsub1 _ Ha) as (b & Hb & Hgb & Hrb).
        destruct (HF _ Hgb) as (r & Hr & Hgr).
        destruct (IHsub2 _ Hgr) as (s & Hs & Hgs & Hrs).
        destruct Hu as [Hu HG].
        destruct (HG _ Hx) as (q & Hq & Hgq).
        assert (Hrel : ne_rel A2 X2 r q).
        { eapply ne_eval2_sync; try eassumption.
          apply Hvu; auto. apply Hrb; assumption. }
        exists s, q; repeat split; eauto using ne_app_cast_steps with necolus.
  - destruct (IHsub1 _ Hv) as (a & Ha & Hga & Hra).
    destruct (IHsub2 _ Hv) as (b & Hb & Hgb & Hrb).
    exists (trm_pair a b); split.
    + eapply star_step; [apply step_pair; eauto with necolus |].
      eapply ne_pair_steps; eauto 8 with necolus.
    + split; [exists a, b; auto |]; simpl; auto.
  - destruct Hv as (a & b & -> & Ha & Hb).
    exists a; repeat split; eauto with necolus; intros; simpl in *; tauto.
  - destruct Hv as (a & b & -> & Ha & Hb).
    exists b; repeat split; eauto with necolus; intros; simpl in *; tauto.
  - destruct Hv as (f & g & -> & [Hf HF] & [Hg HG]).
    exists (trm_capp co_distArr (trm_pair f g)); split; [constructor |].
    split.
    + split; [eauto with necolus |].
      intros a Ha.
      destruct (HF _ Ha) as (r & Hr & Hgr).
      destruct (HG _ Ha) as (s & Hs & Hgs).
      exists (trm_pair r s); split.
      * eapply star_step; [apply step_distArr; eauto with necolus |].
        eapply ne_pair_steps; eauto 8 with necolus.
      * exists r, s; auto.
    + refine (ne_right_cases (fun X u =>
        ne_rel (styp_and (styp_arrow A1 A2) (styp_arrow A1 A3)) X (trm_pair f g) u ->
        ne_rel (styp_arrow A1 (styp_and A2 A3)) X
          (trm_capp co_distArr (trm_pair f g)) u) _ _).
      * intros C D a b Ha Hb Hr; apply ne_rel_right_pair; split;
          [apply Ha | apply Hb]; apply ne_rel_right_pair in Hr; tauto.
      * intros X u Hleaf Hu Hvu; ne_co_leaf X Hleaf.
        destruct Hvu as [Hfu Hgu].
        intros a x Ha Hx Hax.
        destruct (HF _ Ha) as (r & Hr & Hgr).
        destruct (HG _ Ha) as (s & Hs & Hgs).
        destruct Hu as [Hu HU].
        destruct (HU _ Hx) as (q & Hq & Hgq).
        exists (trm_pair r s), q; repeat split.
        -- eapply star_step; [apply step_distArr; eauto with necolus |].
           eapply ne_pair_steps; eauto 8 with necolus.
        -- exact Hq.
        -- eauto with necolus.
        -- eauto with necolus.
        -- eapply ne_eval2_sync; eauto.
        -- eapply ne_eval2_sync; eauto.
  - destruct Hv as (a & -> & Ha).
    destruct (IHsub _ Ha) as (b & Hb & Hgb & Hrb).
    exists (trm_rcd l b); split.
    + eapply star_step; [apply step_crcd; eauto with necolus |].
      eauto with necolus.
    + split; [exists b; auto |].
      refine (ne_right_cases (fun X u =>
        ne_rel (styp_rcd l A) X (trm_rcd l a) u -> ne_rel (styp_rcd l B) X (trm_rcd l b) u) _ _).
      * intros C D p q Hp Hq Hr; apply ne_rel_right_pair; split;
          [apply Hp | apply Hq]; apply ne_rel_right_pair in Hr; tauto.
      * intros X u Hleaf Hu Hvu; ne_co_leaf X Hleaf.
        intro E; subst. destruct Hu as (x & -> & Hx).
        apply Hrb; auto.
  - destruct Hv as (a & b & -> & (p & -> & Hp) & (q & -> & Hq)).
    exists (trm_rcd l (trm_pair p q)); split; [eauto with necolus |].
    split; [exists (trm_pair p q); split; [reflexivity | exists p, q; auto] |].
    refine (ne_right_cases (fun X u =>
        ne_rel (styp_and (styp_rcd l A) (styp_rcd l B)) X
          (trm_pair (trm_rcd l p) (trm_rcd l q)) u ->
        ne_rel (styp_rcd l (styp_and A B)) X (trm_rcd l (trm_pair p q)) u) _ _).
    + intros C D a b Ha Hb Hr; apply ne_rel_right_pair; split;
        [apply Ha | apply Hb]; apply ne_rel_right_pair in Hr; tauto.
    + intros X u Hleaf Hu Hvu; ne_co_leaf X Hleaf.
      intro E; subst; simpl in *; intuition.
Qed.

Lemma ne_sub_good : forall A B c v, sub A B c -> ne_good A v ->
    ne_eval (ne_good B) (trm_capp c v).
Proof.
  intros A B c v H Hv; destruct (ne_sub_transport _ _ _ H _ Hv)
    as (w & Hw & Hg & _); exists w; auto.
Qed.

Definition ne_related A B e f :=
  lc_exp e /\ lc_exp f /\
  exists v w, e ->* v /\ f ->* w /\ ne_good A v /\ ne_good B w /\ ne_rel A B v w.

Lemma ne_related_value : forall A B v w,
    ne_good A v -> ne_good B w -> ne_rel A B v w -> ne_related A B v w.
Proof. intros; repeat split; eauto with necolus; exists v, w; eauto with necolus. Qed.

Lemma ne_related_app : forall A B C D f g a b,
    ne_related (styp_arrow A B) (styp_arrow C D) f g ->
    ne_related A C a b ->
    ne_related B D (trm_app f a) (trm_app g b).
Proof.
  intros A B C D f g a b
    (Hf & Hg & v & w & Hfv & Hgw & [Hv HF] & [Hw HG] & Hvw)
    (Ha & Hb & x & y & Hax & Hby & Hgx & Hgy & Hxy).
  destruct (HF _ Hgx) as (r & Hr & Hgr).
  destruct (HG _ Hgy) as (s & Hs & Hgs).
  assert (Hrs : ne_rel B D r s).
  { eapply ne_eval2_sync; try eassumption. apply Hvw; assumption. }
  repeat split; eauto with necolus.
  exists r, s; repeat split; eauto with necolus.
Qed.

Lemma ne_related_pair : forall A B e f g h,
    disjoint A B -> ne_related A A e f -> ne_related B B g h ->
    ne_related (styp_and A B) (styp_and A B) (trm_pair e g) (trm_pair f h).
Proof.
  intros A B e f g h Hd H1 H2.
  destruct H1 as (He & Hf & a & a' & Hea & Hfa & Hga & Hga' & Haa).
  destruct H2 as (Hg & Hh & b & b' & Hgb & Hhb & Hgoodb & Hgoodb' & Hbb).
  repeat split; eauto with necolus.
  exists (trm_pair a b), (trm_pair a' b'); repeat split; eauto with necolus.
  - exists a, b; auto.
  - exists a', b'; auto.
  - apply ne_rel_right_pair; simpl; split; auto using ne_disjoint_rel.
  - apply ne_rel_right_pair; simpl; split; auto using ne_disjoint_rel.
    apply ne_rel_sym; eauto using ne_disjoint_rel.
Qed.

Lemma ne_related_rcd : forall A l e f,
    ne_related A A e f ->
    ne_related (styp_rcd l A) (styp_rcd l A) (trm_rcd l e) (trm_rcd l f).
Proof.
  intros A l e f (He & Hf & a & b & Hea & Hfb & Ha & Hb & Hab).
  repeat split; eauto with necolus.
  exists (trm_rcd l a), (trm_rcd l b); repeat split; eauto with necolus.
  - exists a; auto.
  - exists b; auto.
  - intro; exact Hab.
Qed.

Lemma ne_related_proj : forall A l e f,
    ne_related (styp_rcd l A) (styp_rcd l A) e f ->
    ne_related A A (trm_proj e l) (trm_proj f l).
Proof.
  intros A l e f (He & Hf & a & b & Hea & Hfb & (x & -> & Hx) & (y & -> & Hy) & Hxy).
  repeat split; eauto with necolus.
  exists x, y; repeat split; eauto with necolus.
  - eapply ne_star_trans; [apply ne_proj_steps; exact Hea | eauto with necolus].
  - eapply ne_star_trans; [apply ne_proj_steps; exact Hfb | eauto with necolus].
Qed.

Lemma ne_related_cast : forall A B C D c d e f,
    sub A B c -> sub C D d -> ne_related A C e f ->
    ne_related B D (trm_capp c e) (trm_capp d f).
Proof.
  intros A B C D c d e f Hc Hd (He & Hf & a & b & Hea & Hfb & Hga & Hgb & Hab).
  destruct (ne_sub_transport _ _ _ Hc _ Hga) as (x & Hax & Hgx & Hrx).
  destruct (ne_sub_transport _ _ _ Hd _ Hgb) as (y & Hby & Hgy & Hry).
  repeat split; eauto with necolus.
  exists x, y; repeat split; eauto with necolus.
  apply ne_rel_sym, Hry; auto. apply ne_rel_sym, Hrx; assumption.
Qed.

Lemma ne_related_abs : forall A B e f,
    lc_exp (trm_abs e) -> lc_exp (trm_abs f) ->
    (forall a, ne_good A a ->
      ne_eval (ne_good B) (e ^^ a) /\ ne_eval (ne_good B) (f ^^ a)) ->
    (forall a b, ne_good A a -> ne_good A b -> ne_rel A A a b ->
      ne_related B B (e ^^ a) (f ^^ b)) ->
    ne_related (styp_arrow A B) (styp_arrow A B) (trm_abs e) (trm_abs f).
Proof.
  intros A B e f He Hf Hunary Hbinary.
  repeat split; auto.
  exists (trm_abs e), (trm_abs f); split; [constructor |]; split; [constructor |].
  split; [| split].
  - split; eauto with necolus.
    intros a Ha; destruct (Hunary _ Ha) as [(r & Hr & Hgr) _].
    exists r; eauto with necolus.
  - split; eauto with necolus.
    intros a Ha; destruct (Hunary _ Ha) as [_ (r & Hr & Hgr)].
    exists r; eauto with necolus.
  - intros a b Ha Hb Hab.
    destruct (Hbinary _ _ Ha Hb Hab) as (_ & _ & r & s & Hr & Hs & Hgr & Hgs & Hrs).
    exists r, s; repeat split; eauto with necolus.
Qed.

Lemma ne_degree_weaken : forall k e, degree_exp_wrt_exp k e ->
    forall n, k <= n -> degree_exp_wrt_exp n e.
Proof. induction 1; intros n Hle; constructor; eauto with arith; try lia. Qed.

Local Ltac ne_open_index :=
  destruct (lt_eq_lt_dec _ _) as [[? | ?] | ?]; simpl in *.

Lemma ne_degree_open_id : forall k e, degree_exp_wrt_exp k e ->
    forall u, open_exp_wrt_exp_rec k u e = e.
Proof.
  induction 1; intros; simpl; try (f_equal; auto).
  ne_open_index; try reflexivity; lia.
Qed.

Lemma ne_degree_open : forall e k u, degree_exp_wrt_exp (S k) e ->
    degree_exp_wrt_exp 0 u -> degree_exp_wrt_exp k (open_exp_wrt_exp_rec k u e).
Proof.
  induction e; intros k u He Hu; inversion He; subst; simpl;
    try solve [constructor; eauto].
  ne_open_index.
  - constructor; lia.
  - eapply ne_degree_weaken; [exact Hu | lia].
  - lia.
Qed.

Lemma ne_degree_open_inv : forall e k x,
    degree_exp_wrt_exp k (open_exp_wrt_exp_rec k (trm_var_f x) e) ->
    degree_exp_wrt_exp (S k) e.
Proof.
  induction e; intros k z H; simpl in *; try solve [inversion H; constructor; eauto].
  ne_open_index; constructor; try lia; inversion H; lia.
Qed.

Lemma ne_degree_close : forall e k x, degree_exp_wrt_exp k e ->
    degree_exp_wrt_exp (S k) (close_exp_wrt_exp_rec k x e).
Proof.
  induction e; intros k z H; inversion H; subst; simpl;
    try solve [constructor; eauto].
  - destruct (lt_ge_dec n k); constructor; lia.
  - destruct (z == x); constructor; lia.
Qed.

Lemma ne_size_open_var : forall e k x,
    size_exp (open_exp_wrt_exp_rec k (trm_var_f x) e) = size_exp e.
Proof.
  induction e; intros; simpl; repeat rewrite IHe || rewrite IHe1 || rewrite IHe2;
    try reflexivity.
  ne_open_index; reflexivity.
Qed.

Lemma ne_degree_lc : forall e, degree_exp_wrt_exp 0 e -> lc_exp e.
Proof.
  induction e using (well_founded_induction (well_founded_ltof exp size_exp)).
  intros He; inversion He; subst; try solve [constructor];
    try solve [constructor; (apply H; [unfold ltof; simpl; lia | assumption])].
  - lia.
  - constructor; intro x.
    apply H.
    + unfold ltof, open_exp_wrt_exp; rewrite ne_size_open_var; simpl; lia.
    + apply ne_degree_open; eauto with necolus.
Qed.

Lemma ne_lc_degree : forall e, lc_exp e -> degree_exp_wrt_exp 0 e.
Proof.
  induction 1; try solve [constructor; auto].
  destruct (atom_fresh_for_list nil) as [x _].
  constructor. exact (ne_degree_open_inv _ 0 x (H0 x)).
Qed.

Local Hint Resolve ne_degree_lc ne_lc_degree : necolus.

(* Instantiation replaces free atoms simultaneously. Opening and closing
   interact with it by updating the assignment at the binder. *)
Definition ne_assignment := var -> exp.

Definition ne_update (rho : ne_assignment) x a : ne_assignment :=
  fun y => if x == y then a else rho y.

Fixpoint ne_instantiate (rho : ne_assignment) (e : exp) : exp :=
  match e with
  | trm_var_f x => rho x
  | trm_abs b => trm_abs (ne_instantiate rho b)
  | trm_app f a => trm_app (ne_instantiate rho f) (ne_instantiate rho a)
  | trm_pair a b => trm_pair (ne_instantiate rho a) (ne_instantiate rho b)
  | trm_rcd l a => trm_rcd l (ne_instantiate rho a)
  | trm_proj a l => trm_proj (ne_instantiate rho a) l
  | trm_capp c a => trm_capp c (ne_instantiate rho a)
  | _ => e
  end.

Definition ne_scoped (rho : ne_assignment) :=
  forall x, degree_exp_wrt_exp 0 (rho x).

Lemma ne_instantiate_degree : forall e k rho, ne_scoped rho ->
    degree_exp_wrt_exp k e -> degree_exp_wrt_exp k (ne_instantiate rho e).
Proof.
  intros e k rho Hr H; induction H; simpl; try solve [constructor; auto].
  eapply ne_degree_weaken; [apply Hr | lia].
Qed.

Lemma ne_instantiate_lc : forall e rho, ne_scoped rho ->
    lc_exp e -> lc_exp (ne_instantiate rho e).
Proof. eauto using ne_degree_lc, ne_instantiate_degree, ne_lc_degree. Qed.

Lemma ne_update_hit : forall rho x a, ne_update rho x a x = a.
Proof. intros; unfold ne_update; destruct (x == x); congruence. Qed.

Lemma ne_update_miss : forall rho x y a, x <> y -> ne_update rho x a y = rho y.
Proof. intros; unfold ne_update; destruct (x == y); congruence. Qed.

Lemma ne_scoped_update : forall rho x a,
    ne_scoped rho -> lc_exp a -> ne_scoped (ne_update rho x a).
Proof.
  unfold ne_scoped, ne_update; intros; destruct (x == x0); eauto with necolus.
Qed.

Lemma ne_instantiate_open : forall e k rho x a,
    ne_scoped rho -> x \notin fv_exp e ->
    ne_instantiate (ne_update rho x a) (open_exp_wrt_exp_rec k (trm_var_f x) e)
    = open_exp_wrt_exp_rec k a (ne_instantiate rho e).
Proof.
  induction e; intros k rho z a Hr Hz; simpl in *;
    try solve [f_equal; eauto; try (apply IHe1 || apply IHe2); auto; fsetdec].
  - ne_open_index; auto using ne_update_hit.
  - rewrite ne_update_miss by fsetdec.
    symmetry; apply ne_degree_open_id, ne_degree_weaken with (k := 0); auto with arith.
Qed.

Lemma ne_instantiate_close : forall e k rho x a, ne_scoped rho ->
    ne_instantiate (ne_update rho x a) e =
    open_exp_wrt_exp_rec k a (ne_instantiate rho (close_exp_wrt_exp_rec k x e)).
Proof.
  induction e; intros k rho z a Hr; simpl;
    try solve [f_equal; eauto].
  - destruct (lt_ge_dec n k) as [Hlt | Hge];
      cbn [ne_instantiate open_exp_wrt_exp_rec].
    + destruct (lt_eq_lt_dec n k) as [[? | ?] | ?]; try reflexivity; lia.
    + destruct (lt_eq_lt_dec (S n) k) as [[? | ?] | ?]; try lia.
      f_equal; lia.
  - destruct (z == x) as [E | E]; subst; simpl.
    + rewrite ne_update_hit. ne_open_index; auto; lia.
    + rewrite ne_update_miss by assumption.
      symmetry; apply ne_degree_open_id, ne_degree_weaken with (k := 0); auto with arith.
Qed.

Lemma ne_instantiate_id : forall e, ne_instantiate trm_var_f e = e.
Proof. induction e; simpl; congruence. Qed.

Lemma ne_source_degree : forall G E d A e, has_type G E d A e ->
    degree_exp_wrt_exp 0 e.
Proof.
  induction 1; eauto with necolus.
  pick fresh x for L.
  constructor. eapply ne_degree_open_inv; eauto.
Qed.

Definition ne_good_env (G : sctx) rho :=
  ne_scoped rho /\ forall x A, binds x A G -> ne_good A (rho x).

Definition ne_rel_env (G : sctx) rho sigma :=
  ne_good_env G rho /\ ne_good_env G sigma /\
  forall x A, binds x A G -> ne_rel A A (rho x) (sigma x).

Lemma ne_binds_cons : forall (G : sctx) x y A B,
    binds y B ((x ~ A) ++ G) ->
    (y = x /\ B = A) \/ binds y B G.
Proof.
  unfold binds; simpl; intros G x y A B [H | H]; [left; split; congruence | auto].
Qed.

Lemma ne_good_env_update : forall G rho x A a,
    x \notin dom G -> ne_good_env G rho -> ne_good A a ->
    ne_good_env ((x ~ A) ++ G) (ne_update rho x a).
Proof.
  intros G rho x A a Hfresh [Hs HG] Ha.
  split; [eapply ne_scoped_update; eauto with necolus |].
  intros y B Hy. apply ne_binds_cons in Hy.
  destruct Hy as [[-> ->] | Hy].
  - rewrite ne_update_hit; assumption.
  - rewrite ne_update_miss; auto.
    intro E; subst; apply Hfresh; eauto using binds_In.
Qed.

Lemma ne_rel_env_update : forall G rho sigma x A a b,
    x \notin dom G -> ne_rel_env G rho sigma ->
    ne_good A a -> ne_good A b -> ne_rel A A a b ->
    ne_rel_env ((x ~ A) ++ G) (ne_update rho x a) (ne_update sigma x b).
Proof.
  intros G rho sigma x A a b Hfresh (Hr & Hs & Hrs) Ha Hb Hab.
  split; [eauto using ne_good_env_update |].
  split; [eauto using ne_good_env_update |].
  intros y B Hy. apply ne_binds_cons in Hy.
  destruct Hy as [[-> ->] | Hy].
  - rewrite !ne_update_hit; assumption.
  - assert (x <> y) by (intro E; subst; apply Hfresh; eauto using binds_In).
    rewrite !ne_update_miss by assumption; auto.
Qed.

Definition ne_terminates A e := lc_exp e /\ ne_eval (ne_good A) e.

Lemma ne_terminates_value : forall A v, ne_good A v -> ne_terminates A v.
Proof. intros; split; eauto with necolus; exists v; eauto with necolus. Qed.

Lemma ne_terminates_app : forall A B f a,
    ne_terminates (styp_arrow A B) f -> ne_terminates A a ->
    ne_terminates B (trm_app f a).
Proof.
  intros A B f a (Hf & v & Hfv & Hv & HF) (Ha & w & Haw & Hw).
  destruct (HF _ Hw) as (q & Hq & Hgq).
  split; eauto with necolus. exists q; split; eauto with necolus.
Qed.

Lemma ne_terminates_pair : forall A B e f,
    ne_terminates A e -> ne_terminates B f ->
    ne_terminates (styp_and A B) (trm_pair e f).
Proof.
  intros A B e f (He & a & Hea & Ha) (Hf & b & Hfb & Hb).
  split; eauto with necolus.
  exists (trm_pair a b); split; eauto with necolus.
  exists a, b; auto.
Qed.

Lemma ne_terminates_rcd : forall A l e,
    ne_terminates A e -> ne_terminates (styp_rcd l A) (trm_rcd l e).
Proof.
  intros A l e (He & a & Hea & Ha); split; eauto with necolus.
  exists (trm_rcd l a); split; eauto with necolus.
  exists a; auto.
Qed.

Lemma ne_terminates_proj : forall A l e,
    ne_terminates (styp_rcd l A) e -> ne_terminates A (trm_proj e l).
Proof.
  intros A l e (He & a & Hea & b & -> & Hb); split; eauto with necolus.
  exists b; split; [| exact Hb].
  eapply ne_star_trans; [apply ne_proj_steps; exact Hea | eauto with necolus].
Qed.

Lemma ne_terminates_cast : forall A B c e,
    sub A B c -> ne_terminates A e -> ne_terminates B (trm_capp c e).
Proof.
  intros A B c e Hc (He & a & Hea & Ha).
  destruct (ne_sub_good _ _ _ _ Hc Ha) as (b & Hab & Hb).
  split; eauto with necolus. exists b; eauto with necolus.
Qed.

Lemma ne_terminates_abs : forall A B e,
    lc_exp (trm_abs e) ->
    (forall a, ne_good A a -> ne_eval (ne_good B) (e ^^ a)) ->
    ne_terminates (styp_arrow A B) (trm_abs e).
Proof.
  intros A B e He H; apply ne_terminates_value.
  split; eauto with necolus.
  intros a Ha; destruct (H _ Ha) as (r & Hr & Hgr); exists r; eauto with necolus.
Qed.

Local Hint Resolve ne_terminates_app ne_terminates_pair ne_terminates_rcd
  ne_terminates_proj ne_terminates_cast ne_terminates_value : necolus.
Local Hint Resolve ne_related_app ne_related_pair ne_related_rcd
  ne_related_proj ne_related_cast ne_related_value : necolus.

Lemma ne_abs_lc_under : forall e rho x,
    ne_scoped rho -> degree_exp_wrt_exp 0 (e ^ x) ->
    lc_exp (trm_abs (ne_instantiate rho e)).
Proof.
  intros e rho x Hr He.
  change (lc_exp (ne_instantiate rho (trm_abs e))).
  apply ne_instantiate_lc; auto.
  apply ne_degree_lc; constructor; eapply ne_degree_open_inv; eauto.
Qed.

Lemma ne_source_terminates : forall G E d A e, has_type G E d A e ->
    forall rho, ne_good_env G rho -> ne_terminates A (ne_instantiate rho e).
Proof.
  induction 1; intros rho Hr; simpl.
  - apply ne_terminates_value; reflexivity.
  - apply ne_terminates_value; exists i5; reflexivity.
  - apply ne_terminates_value; apply Hr; assumption.
  - eauto with necolus.
  - eauto with necolus.
  - eauto with necolus.
  - eauto with necolus.
  - auto.
  - pick fresh x for (L \u dom GG \u fv_exp e).
    assert (HxL : x \notin L) by fsetdec.
    assert (Hxs : x \notin fv_exp e) by fsetdec.
    assert (Hxd : x \notin dom GG) by fsetdec.
    destruct Hr as [Hscope Hbinds].
    apply ne_terminates_abs.
    + apply (ne_abs_lc_under _ _ x); auto. eapply ne_source_degree; eauto.
    + intros a Ha.
      unfold open_exp_wrt_exp.
      rewrite <- (ne_instantiate_open e 0 rho x a Hscope Hxs).
      apply (proj2 (H0 x HxL _ (ne_good_env_update _ _ _ _ _ Hxd (conj Hscope Hbinds) Ha))).
  - eauto with necolus.
Qed.

Lemma ne_inferred_type : forall G E A B e f,
    has_type G E Inf A e -> has_type G E Inf B f -> A = B.
Proof.
  intros G E A B e f H.
  remember Inf as d eqn:Hd; revert B f Hd.
  induction H; intros T t Hd Ht; subst;
    try discriminate; inversion Ht; subst; try reflexivity;
    try solve [match goal with
      | H1 : binds ?x _ ?G, H2 : binds ?x _ ?G, Hu : uniq ?G |- _ =>
          exact (binds_unique _ _ _ _ _ H1 H2 Hu)
      end];
    repeat match goal with
    | IH : forall (B : styp) (f : exp), Inf = Inf -> has_type _ ?E Inf B f -> _,
      Hother : has_type _ ?E Inf _ _ |- _ =>
        let Eqt := fresh "Htype" in
        pose proof (IH _ _ eq_refl Hother) as Eqt;
        clear IH
    end; congruence.
Qed.

(* Two elaborations of the same judgment are related under related
   assignments to the source environment. *)
Lemma ne_source_related : forall G E d A e, has_type G E d A e ->
    forall f, has_type G E d A f ->
    forall rho sigma, ne_rel_env G rho sigma ->
      ne_related A A (ne_instantiate rho e) (ne_instantiate sigma f).
Proof.
  induction 1; intros f Hf rho sigma Henv; inversion Hf; subst; simpl.
  - apply ne_related_value; simpl; auto.
  - apply ne_related_value; simpl; eauto.
  - destruct Henv as [Hr [Hs Hrs]].
    apply ne_related_value; [apply Hr | apply Hs | apply Hrs]; assumption.
  - match goal with
    | He : has_type _ ee1 Inf (styp_arrow A1 A2) e1,
      Hother : has_type _ ee1 Inf (styp_arrow ?B A2) _ |- _ =>
        assert (A1 = B) by (injection (ne_inferred_type _ _ _ _ _ _ He Hother); auto)
    end.
    subst; eauto with necolus.
  - eauto with necolus.
  - eauto with necolus.
  - eauto with necolus.
  - auto.
  - pick fresh x for (L \u L0 \u dom GG \u fv_exp e \u fv_exp e0).
    assert (HxL : x \notin L) by fsetdec.
    assert (HxL0 : x \notin L0) by fsetdec.
    assert (Hxd : x \notin dom GG) by fsetdec.
    assert (Hxe : x \notin fv_exp e) by fsetdec.
    assert (Hxf : x \notin fv_exp e0) by fsetdec.
    pose proof (proj1 Henv) as Hr; pose proof (proj1 (proj2 Henv)) as Hs.
    pose proof (H x HxL) as Hleft; pose proof (H5 x HxL0) as Hright.
    apply ne_related_abs.
    + apply (ne_abs_lc_under _ _ x); [apply Hr | eauto using ne_source_degree].
    + apply (ne_abs_lc_under _ _ x); [apply Hs | eauto using ne_source_degree].
    + intros a Ha; unfold open_exp_wrt_exp.
      rewrite <- (ne_instantiate_open e 0 rho x a (proj1 Hr) Hxe).
      rewrite <- (ne_instantiate_open e0 0 sigma x a (proj1 Hs) Hxf).
      split.
      * exact (proj2 (ne_source_terminates _ _ _ _ _ Hleft _
          (ne_good_env_update _ _ _ _ _ Hxd Hr Ha))).
      * exact (proj2 (ne_source_terminates _ _ _ _ _ Hright _
          (ne_good_env_update _ _ _ _ _ Hxd Hs Ha))).
    + intros a b Ha Hb Hab; unfold open_exp_wrt_exp.
      rewrite <- (ne_instantiate_open e 0 rho x a (proj1 Hr) Hxe).
      rewrite <- (ne_instantiate_open e0 0 sigma x b (proj1 Hs) Hxf).
      apply H0; auto using ne_rel_env_update.
  - match goal with Hbad : has_type _ (e_abs _) Inf _ _ |- _ => inversion Hbad end.
  - match goal with Hbad : has_type _ (e_abs _) Inf _ _ |- _ => inversion Hbad end.
  - match goal with
    | H1 : has_type _ ?S Inf B e, H2 : has_type _ ?S Inf ?B' _ |- _ =>
        assert (B = B') by (eapply ne_inferred_type; [exact H1 | exact H2])
    end.
    subst; eauto with necolus.
Qed.

Lemma ne_close_abs_lc : forall e x, lc_exp e -> lc_exp (trm_abs (close_exp_wrt_exp x e)).
Proof.
  intros; apply ne_degree_lc; constructor.
  apply ne_degree_close; auto with necolus.
Qed.

Lemma ne_context_lc : forall C G d A D d' B c,
    CTyp C G d A D d' B c ->
    forall e, lc_exp e -> lc_exp (appctx c e).
Proof.
  induction 1; intros t Hlc; simpl;
    eauto using ne_degree_lc, ne_source_degree, ne_close_abs_lc with necolus.
Qed.

Lemma ne_context_abs_lc : forall e x rho,
    ne_scoped rho -> lc_exp e ->
    lc_exp (trm_abs (ne_instantiate rho (close_exp_wrt_exp x e))).
Proof.
  intros e x rho Hr He.
  exact (ne_instantiate_lc _ _ Hr (ne_close_abs_lc e x He)).
Qed.

Local Hint Resolve ne_source_terminates ne_source_related : necolus.

Lemma ne_context_terminates : forall C G d A D d' B c,
    CTyp C G d A D d' B c ->
    forall e,
      lc_exp e ->
      (forall rho, ne_good_env G rho -> ne_terminates A (ne_instantiate rho e)) ->
      forall rho, ne_good_env D rho -> ne_terminates B (ne_instantiate rho (appctx c e)).
Proof.
  induction 1; intros t Hlc Hhole rho Hr; simpl;
    try solve [eauto 7 with necolus].
  all: apply ne_terminates_abs.
  all: try solve [apply ne_context_abs_lc; [exact (proj1 Hr) |
    eapply ne_context_lc; eassumption]].
  all: intros a Ha; unfold open_exp_wrt_exp, close_exp_wrt_exp;
    rewrite <- (ne_instantiate_close _ 0 rho x a (proj1 Hr));
    apply (proj2 (IHCTyp t Hlc Hhole _
      (ne_good_env_update _ _ _ _ _ H0 Hr Ha))).
Qed.

(* The context uses its output environment for the fixed subterms and
   updates that environment under a lambda. The hole keeps its own judgment. *)
Lemma ne_context_related : forall C G d A D d' B c,
    CTyp C G d A D d' B c ->
    forall e f,
      lc_exp e -> lc_exp f ->
      (forall rho, ne_good_env G rho -> ne_terminates A (ne_instantiate rho e)) ->
      (forall sigma, ne_good_env G sigma -> ne_terminates A (ne_instantiate sigma f)) ->
      (forall rho sigma, ne_rel_env G rho sigma ->
        ne_related A A (ne_instantiate rho e) (ne_instantiate sigma f)) ->
      forall rho sigma, ne_rel_env D rho sigma ->
        ne_related B B (ne_instantiate rho (appctx c e))
                       (ne_instantiate sigma (appctx c f)).
Proof.
  induction 1; intros t u Ht Hu Hleft Hright Hhole rho sigma Henv; simpl;
    try solve [eauto 8 with necolus].
  all: pose proof (proj1 Henv) as Hr;
    pose proof (proj1 (proj2 Henv)) as Hs;
    apply ne_related_abs.
  all: try solve [apply ne_context_abs_lc;
    [first [exact (proj1 Hr) | exact (proj1 Hs)] |
     eapply ne_context_lc; eassumption]].
  all: try solve [
    intros a Ha; unfold open_exp_wrt_exp, close_exp_wrt_exp;
    rewrite <- (ne_instantiate_close _ 0 rho x a (proj1 Hr));
    rewrite <- (ne_instantiate_close _ 0 sigma x a (proj1 Hs));
    split;
    [ apply (proj2 (ne_context_terminates _ _ _ _ _ _ _ _ H t Ht Hleft _
        (ne_good_env_update _ _ _ _ _ H0 Hr Ha)))
    | apply (proj2 (ne_context_terminates _ _ _ _ _ _ _ _ H u Hu Hright _
        (ne_good_env_update _ _ _ _ _ H0 Hs Ha))) ]].
  all: intros a b Ha Hb Hab; unfold open_exp_wrt_exp, close_exp_wrt_exp;
    rewrite <- (ne_instantiate_close _ 0 rho x a (proj1 Hr));
    rewrite <- (ne_instantiate_close _ 0 sigma x b (proj1 Hs));
    apply IHCTyp; auto using ne_rel_env_update.
Qed.

Lemma ne_empty_rel_env : ne_rel_env nil trm_var_f trm_var_f.
Proof.
  assert (H : ne_good_env nil trm_var_f).
  { split; [intro; constructor | intros x A Hbind; inversion Hbind]. }
  split; [exact H | split; [exact H | intros x A Hbind; inversion Hbind]].
Qed.

Theorem coherence_thm : forall Γ E A,
    ctx_equiv Γ E E A.
Proof.
  intros G E A e f d d' C c He Hf HC.
  assert (Hobs : ne_related styp_nat styp_nat
      (ne_instantiate trm_var_f (appctx c e))
      (ne_instantiate trm_var_f (appctx c f))).
  { eapply ne_context_related;
    eauto using ne_source_degree, ne_degree_lc, ne_source_terminates,
      ne_source_related, ne_empty_rel_env. }
  rewrite !ne_instantiate_id in Hobs.
  destruct Hobs as (_ & _ & v & w & Hev & Hfw & (k & ->) & _ & Hvw).
  change (trm_lit k = w) in Hvw; subst.
  exists k; auto.
Qed.
