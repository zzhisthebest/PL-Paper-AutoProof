Require Import Metalib.Metatheory.
Require Import Rules.

Local Lemma qs_flip : forall im, flip_im (flip_im im) = im.
Proof. destruct im; reflexivity. Qed.

Local Lemma qs_fv_open : forall T k (x : atom),
    fv_tt (open_tt_rec k x T) [<=] add x (fv_tt T).
Proof.
  induction T; intros k x; simpl; try fsetdec.
  - destruct (k === n); simpl; fsetdec.
  - specialize (IHT (S k) x); fsetdec.
  - specialize (IHT1 k x); specialize (IHT2 k x); fsetdec.
Qed.

Local Lemma qs_subst_tt_fresh : forall T x U,
    x \notin fv_tt T -> subst_tt x U T = T.
Proof.
  induction T; intros x U H; simpl in *; try reflexivity.
  - destruct (a == x); subst; try reflexivity; fsetdec.
  - rewrite IHT by fsetdec; reflexivity.
  - rewrite IHT1, IHT2 by fsetdec; reflexivity.
Qed.

Local Lemma qs_subst_tt_intro : forall T k x U,
    x \notin fv_tt T ->
    subst_tt x U (open_tt_rec k x T) = open_tt_rec k U T.
Proof.
  induction T; intros k x U H; simpl in *; try reflexivity.
  - destruct (k === n); simpl; [destruct (x == x); congruence | reflexivity].
  - destruct (a == x); subst; try reflexivity; fsetdec.
  - rewrite IHT by fsetdec; reflexivity.
  - rewrite IHT1, IHT2 by fsetdec; reflexivity.
Qed.

Local Lemma qs_open_tt_inj : forall A B k (x : atom),
    x \notin fv_tt A -> x \notin fv_tt B ->
    open_tt_rec k x A = open_tt_rec k x B -> A = B.
Proof.
  induction A; destruct B; intros k x HA HB H; simpl in *;
    try (destruct (k === n) in H);
    try (destruct (k === n0) in H);
    try discriminate; try reflexivity; try congruence.
  - inversion H; subst; fsetdec.
  - inversion H; subst; fsetdec.
  - inversion H; subst; f_equal; eapply IHA; eauto.
  - inversion H; subst; f_equal; [eapply IHA1 | eapply IHA2]; eauto; fsetdec.
Qed.

Local Lemma qs_env_ok : forall E, wf_env E -> uniq E.
Proof. induction 1; auto. Qed.

Local Lemma qs_wfs_map : forall E T, WFS E T ->
    forall F,
      (forall x im, x `in` fv_tt T -> binds x (bind_sub im) E ->
                    exists jm, binds x (bind_sub jm) F) ->
      WFS F T.
Proof.
  induction 1 as [E|E|x E im Hb|E A B HA IHA HB IHB|L E A im HA IH];
    intros F Hmap; simpl in *.
  - constructor.
  - constructor.
  - destruct (Hmap x im) as [jm Hj]; auto.
    eapply WFS_fvar; eauto.
  - constructor; [apply IHA | apply IHB]; intros; eapply Hmap; eauto; fsetdec.
  - apply WFS_rec with (L := L) (im := im).
    intros x Hx. apply IH; auto.
    intros y jm Hy Hb. destruct (y == x) as [->|Hne].
    + exists im; auto.
    + apply binds_cons_1 in Hb as [[Heq _]|Hb]; try congruence.
      pose proof (qs_fv_open A 0 x) as Hfv.
      destruct (Hmap y jm) as [km Hkm]; auto.
      * unfold open_tt in Hy; fsetdec.
      * exists km; auto.
Qed.

Local Lemma qs_wfs_type : forall E T, WFS E T -> type T.
Proof. induction 1; eauto using type. Qed.

Local Lemma qs_sub_wfs : forall im cm es E A B, Sub im cm es E A B ->
    WFS E A /\ WFS E B.
Proof.
  induction 1; try solve [intuition eauto using WFS].
  all: split; eapply WFS_rec with (L := L) (im := im); intros x Hx;
    match goal with
    | H : forall _, _ -> _ /\ _ |- _ => specialize (H x Hx); tauto
    end.
Qed.

Local Lemma qs_sub_eq : forall im cm es E A B,
    Sub im cm es E A B -> cm = Eq -> A = B.
Proof.
  induction 1; intros Heq; try discriminate; try reflexivity; auto.
  - subst cm. destruct cm1, cm2; simpl in *; repeat
      match goal with H : context [if ?b then _ else _] |- _ => destruct b eqn:? end;
      try discriminate; f_equal; auto; symmetry; auto.
  - pick fresh x for (L \u fv_tt A1 \u fv_tt A2).
    f_equal; eapply qs_open_tt_inj with (x := x) (k := 0); eauto.
  - pick fresh x for (L \u fv_tt A1 \u fv_tt A2).
    f_equal; eapply qs_open_tt_inj with (x := x) (k := 0); eauto.
Qed.

Local Lemma qs_sub_lt_empty : forall im cm es E A B,
    Sub im cm es E A B -> cm = Lt -> es [=] emp.
Proof.
  induction 1; intros Hcm; try discriminate; auto; try solve [fsetdec].
  - destruct cm1, cm2; simpl in H1;
      repeat match type of H1 with
      | context [if ?b then _ else _] =>
          let He := fresh "He" in destruct b eqn:He;
          try apply AtomSetImpl.is_empty_2 in He
      end; inversion H1; subst; try discriminate;
      try specialize (IHSub1 eq_refl); try specialize (IHSub2 eq_refl); fsetdec.
  - pick fresh x for L. eauto.
  - specialize (IHSub Hcm); fsetdec.
Qed.

(* Subtyping depends only on the relevant type bindings. The mode map also
   allows all polarities to be flipped together. *)
Local Lemma qs_sub_map : forall im cm es E A B, Sub im cm es E A B ->
    forall (r : IsoMode -> IsoMode) F,
      (forall m, r (flip_im m) = flip_im (r m)) ->
      wf_env F ->
      (forall x m, x `in` fv_tt A \u fv_tt B -> binds x (bind_sub m) E ->
                   binds x (bind_sub (r m)) F) ->
      Sub (r im) cm es F A B.
Proof.
  induction 1; intros r F Hr HF Hmap; simpl in Hmap.
  { constructor; auto. }
  { constructor; auto. }
  { apply Sa_top_lt; auto.
    eapply qs_wfs_map; [eassumption |].
    intros x m Hx Hb. exists (r m); apply Hmap; auto; fsetdec. }
  { apply Sa_fvar_pos; auto. }
  { apply Sa_fvar_neg; auto. rewrite <- Hr. apply Hmap; auto; fsetdec. }
  { eapply Sa_arrow; [rewrite <- Hr; eapply IHSub1 | eapply IHSub2 | eassumption];
      eauto; intros; apply Hmap; auto; fsetdec. }
  all: try solve [eapply Sa_evs_proper; eauto].
  all: let L' := constr:(L \u dom F \u dom E) in
       let recurse := (intros x Hx; eapply H0; eauto using wf_env) in
       first [apply Sa_rec_lt with (L := L'); recurse |
              apply Sa_rec_eq_notin with (L := L'); recurse |
              apply Sa_rec_eq_in with (L := L'); recurse].
  all: intros y m Hy Hb; apply binds_cons_1 in Hb as [[-> Hm]|Hb];
    [injection Hm as ->; auto |].
  all: assert (y <> x) by (intros ->; apply binds_In in Hb; fsetdec);
    pose proof (qs_fv_open A1 0 x);
    pose proof (qs_fv_open A2 0 x);
    apply binds_cons; apply Hmap; auto;
    unfold open_tt in Hy; fsetdec.
Qed.

Local Lemma qs_subst_tt_open : forall T k x (y : atom) U,
    y <> x -> (forall k V, open_tt_rec k V U = U) ->
    subst_tt x U (open_tt_rec k y T) = open_tt_rec k y (subst_tt x U T).
Proof.
  induction T; intros k x y U Hne HU; simpl; try reflexivity.
  - destruct (k === n); simpl; [destruct (y == x); congruence | reflexivity].
  - destruct (a == x); simpl; auto.
  - rewrite IHT by auto; reflexivity.
  - rewrite IHT1, IHT2 by auto; reflexivity.
Qed.


Local Lemma qs_wfs_subst : forall E T, WFS E T ->
    forall x U F, WFS F U ->
      (forall y m, y <> x -> binds y (bind_sub m) E -> binds y (bind_sub m) F) ->
      (forall k V, open_tt_rec k V U = U) ->
      WFS F (subst_tt x U T).
Proof.
  induction 1 as [E|E|y E im Hb|E A B HA IHA HB IHB|L E A im HA IH];
    intros x U F HU Hmap Hlc; simpl.
  - constructor.
  - constructor.
  - destruct (y == x); eauto using WFS.
  - constructor; eauto.
  - apply WFS_rec with (L := L \u {{x}}) (im := im).
    intros y Hy. unfold open_tt. rewrite <- qs_subst_tt_open by (auto; fsetdec).
    eapply IH; auto.
    + eapply qs_wfs_map; eauto.
    + intros z m Hz Hb. apply binds_cons_1 in Hb as [[-> Hm]|Hb]; [injection Hm as ->; auto | eauto].
Qed.

Local Lemma qs_open_tt_stable : forall T, type T ->
    forall k U, open_tt_rec k U T = T.
Proof.
  assert (Hinv : forall T j k (x : atom) U,
      j <> k ->
      open_tt_rec k U (open_tt_rec j x T) = open_tt_rec j x T ->
      open_tt_rec k U T = T).
  { induction T; intros j k x U Hne H; simpl in *; try reflexivity.
    - destruct (j === n) as [Hj|Hj]; simpl in H;
      destruct (k === n) as [Hk|Hk]; try congruence.
    - inversion H; f_equal; eapply IHT with (j := S j) (x := x); eauto.
    - inversion H; f_equal; [eapply IHT1 with (j := j) (x := x) | eapply IHT2 with (j := j) (x := x)]; eauto. }
  induction 1; intros k U; simpl; try reflexivity.
  - rewrite IHtype1, IHtype2; reflexivity.
  - pick fresh x for L. f_equal. eapply Hinv with (j := 0) (x := x); eauto.
Qed.

Local Lemma qs_sub_empty_evidence : forall im cm es E A B,
    Sub im cm es E A B -> es [=] emp -> Sub im cm emp E A B.
Proof. intros; eauto using Sa_evs_proper. Qed.

Local Lemma qs_sub_closed_weak : forall im cm es A B F,
    Sub im cm es nil A B -> wf_env F -> Sub im cm es F A B.
Proof.
  intros. eapply (qs_sub_map _ _ _ _ _ _ H (fun m => m)); eauto.
  intros; inversion H2.
Qed.

Local Lemma qs_sub_lt_distinct : forall im cm es E A B,
    Sub im cm es E A B -> cm = Lt -> A <> B.
Proof.
  induction 1; intros Hcm Heq; try discriminate; try contradiction; eauto.
  - subst cm. inversion Heq; subst.
    destruct cm1, cm2; simpl in H1; try discriminate;
      first [exact (IHSub1 eq_refl eq_refl) | exact (IHSub2 eq_refl eq_refl)].
  - inversion Heq; subst.
    pick fresh x for L. eapply (H0 x); eauto.
  - exact (IHSub Hcm Heq).
Qed.

(* The opened comparisons have one common mode, determined by equality of
   the recursive bodies. *)
Local Lemma qs_rec_empty : forall L E im A B,
    (forall x, x \notin L ->
       exists cm, Sub im cm emp (x ~ bind_sub im ++ E) (open_tt A x) (open_tt B x)) ->
    exists cm, Sub im cm emp E (typ_mu A) (typ_mu B).
Proof.
  intros L E im A B H.
  assert (Hdec : forall T U : typ, {T = U} + {T <> U}).
  { decide equality; apply eq_dec. }
  destruct (Hdec A B) as [->|Hne].
  - exists Eq. apply Sa_rec_eq_notin with (L := L).
    intros x Hx. destruct (H x Hx) as [cm Hsub].
    destruct cm; auto. exfalso. eapply qs_sub_lt_distinct; eauto.
  - exists Lt. apply Sa_rec_lt with (L := L \u fv_tt A \u fv_tt B).
    intros x Hx. destruct (H x ltac:(auto)) as [cm Hsub].
    destruct cm; auto. exfalso. apply Hne.
    eapply qs_open_tt_inj with (x := x) (k := 0); eauto using qs_sub_eq.
Qed.

Local Definition qs_at_mode (im : IsoMode) (U V : typ) :=
  match im with Pos => U | Neg => V end.

Local Lemma qs_sub_arrow_empty : forall F im A1 A2 B1 B2 cm1 cm2,
    Sub (flip_im im) cm1 emp F B1 A1 ->
    Sub im cm2 emp F A2 B2 ->
    exists cm, (cm1 = Lt \/ cm2 = Lt -> cm = Lt) /\
      Sub im cm emp F (typ_arrow A1 A2) (typ_arrow B1 B2).
Proof.
  assert (Hempty : AtomSetImpl.is_empty emp = true)
    by (apply AtomSetImpl.is_empty_1; fsetdec).
  intros. destruct cm1, cm2;
    [exists Lt | exists Lt | exists Lt | exists Eq]; split.
  all: try solve [intuition discriminate].
  all: eapply qs_sub_empty_evidence;
      [eapply Sa_arrow; [eassumption | eassumption | simpl; now rewrite ?Hempty] | fsetdec].
Qed.

(* A strict recursive comparison can be substituted for a positive variable.
   Empty evidence rules out a changed occurrence in a negative position. *)
Local Lemma qs_sub_substitute : forall im cm es E A B, Sub im cm es E A B ->
    forall x U V F,
      es [=] emp ->
      binds x (bind_sub Pos) E ->
      Sub Pos Lt emp nil U V ->
      U <> typ_top -> V <> typ_top ->
      wf_env F ->
      (forall y m, y <> x -> binds y (bind_sub m) E -> binds y (bind_sub m) F) ->
      exists cm', (cm = Lt -> cm' = Lt) /\
        Sub im cm' emp F (subst_tt x (qs_at_mode im U V) A)
                         (subst_tt x (qs_at_mode (flip_im im) U V) B).
Proof.
  induction 1 as
    [E im HE |E im HE |E im A HE HA Htop
    |E y im HE Hy |E y im HE Hy
    |E A1 A2 B1 B2 cm1 cm2 es1 es2 cm im H1 IH1 H2 IH2 Hcm
    |L A B es E im H IH |L A B es E im H IH |L A B es E im H IH
    |im cm es es' E A B H IH Hes];
    intros x U V F Hempty Hx HUV HU HV HF Hmap.
  - exists Eq; split; [discriminate | constructor; auto].
  - exists Eq; split; [discriminate | constructor; auto].
  - exists Lt; split; [auto | simpl].
    apply Sa_top_lt; auto.
    + eapply qs_wfs_subst; eauto.
      * destruct (qs_sub_wfs _ _ _ _ _ _ (qs_sub_closed_weak _ _ _ _ _ _ HUV HF)).
        destruct im; assumption.
      * apply qs_open_tt_stable. eapply qs_wfs_type.
        destruct (qs_sub_wfs _ _ _ _ _ _ HUV). destruct im; eassumption.
    + destruct A; simpl in *; try discriminate; try contradiction.
      destruct (a == x); [destruct im; assumption | discriminate].
  - simpl. destruct (y == x) as [->|Hne].
    + assert (Heq : bind_sub im = bind_sub Pos)
        by (eapply binds_unique; eauto using qs_env_ok).
      injection Heq as ->. exists Lt; split; auto.
      eauto using qs_sub_closed_weak.
    + exists Eq; split; [discriminate | constructor; eauto].
  - exfalso. unfold emp in Hempty.
    assert (Hyin : y `in` singleton y) by fsetdec. fsetdec.
  - assert (He1 : es1 [=] emp) by fsetdec.
    assert (He2 : es2 [=] emp) by fsetdec.
    destruct (IH1 x U V F He1 Hx HUV HU HV HF Hmap) as [c1 [Hc1 HS1]].
    destruct (IH2 x U V F He2 Hx HUV HU HV HF Hmap) as [c2 [Hc2 HS2]].
    rewrite qs_flip in HS1. simpl.
    destruct (qs_sub_arrow_empty _ _ _ _ _ _ _ _ HS1 HS2) as [c [Hc HS]].
    exists c; split; auto.
    intro Hstrict. apply Hc. subst cm.
    destruct cm1, cm2; simpl in Hcm; try discriminate; auto.
  - exists Lt; split; [auto | simpl].
    apply Sa_rec_lt with (L := L \u dom F \u {{x}}).
    intros y Hy.
    assert (Hkeep : forall z m, z <> x ->
        binds z (bind_sub m) (y ~ bind_sub im ++ E) ->
        binds z (bind_sub m) (y ~ bind_sub im ++ F)).
    { intros z m Hz Hb. apply binds_cons_1 in Hb as [[-> Hm]|Hb];
        [injection Hm as ->; auto | eauto]. }
    destruct (IH y ltac:(auto) x U V (y ~ bind_sub im ++ F)) as [c [Hc HS]];
      eauto using wf_env.
    rewrite (Hc eq_refl) in HS. unfold open_tt in *.
    rewrite <- !qs_subst_tt_open; auto.
    all: apply qs_open_tt_stable; eapply qs_wfs_type;
      destruct (qs_sub_wfs _ _ _ _ _ _ HUV); destruct im; eassumption.
  - simpl.
    destruct (qs_rec_empty (L \u dom F \u {{x}}) F im
       (subst_tt x (qs_at_mode im U V) A) (subst_tt x (qs_at_mode (flip_im im) U V) B))
       as [c HS].
    + intros y Hy.
      assert (Hkeep : forall z m, z <> x ->
          binds z (bind_sub m) (y ~ bind_sub im ++ E) ->
          binds z (bind_sub m) (y ~ bind_sub im ++ F)).
      { intros z m Hz Hb. apply binds_cons_1 in Hb as [[-> Hm]|Hb];
          [injection Hm as ->; auto | eauto]. }
      destruct (IH y ltac:(auto) x U V (y ~ bind_sub im ++ F)) as [c [Hc HS]];
        eauto using wf_env.
      exists c. unfold open_tt in *.
      rewrite <- !qs_subst_tt_open; auto.
      all: apply qs_open_tt_stable; eapply qs_wfs_type;
        destruct (qs_sub_wfs _ _ _ _ _ _ HUV); destruct im; eassumption.
    + exists c; split; [discriminate | assumption].
  - assert (HAB : A = B).
    { pick fresh y for (L \u fv_tt A \u fv_tt B).
      eapply qs_open_tt_inj with (x := y) (k := 0); eauto using qs_sub_eq. }
    subst B. simpl.
    rewrite !qs_subst_tt_fresh by fsetdec.
    exists Eq; split; [discriminate |].
    eapply qs_sub_empty_evidence; [|exact Hempty].
    apply (qs_sub_map _ _ _ _ _ _
      (Sa_rec_eq_in L A A es E im H) (fun m => m) F); auto.
    simpl. intros y m Hy Hb. apply Hmap; auto; fsetdec.
  - eapply IH; eauto; fsetdec.
Qed.

Local Lemma qs_sub_arrow_inv : forall im cm es E A B, Sub im cm es E A B ->
    forall B1 B2, B = typ_arrow B1 B2 ->
      exists A1 A2 c1 s1 c2 s2, A = typ_arrow A1 A2 /\
        Sub (flip_im im) c1 s1 E B1 A1 /\ Sub im c2 s2 E A2 B2.
Proof.
  induction 1; intros B1' B2' HB; try discriminate; eauto.
  inversion HB; subst. do 6 eexists. intuition eauto.
Qed.

Local Lemma qs_sub_mu_inv : forall im cm es E A B, Sub im cm es E A B ->
    forall B', B = typ_mu B' -> exists A', A = typ_mu A'.
Proof. induction 1; intros; try discriminate; eauto. Qed.

Local Lemma qs_sub_mu_body : forall im cm es E A B, Sub im cm es E A B ->
    cm = Lt -> forall A' B', A = typ_mu A' -> B = typ_mu B' ->
    exists L, forall x, x \notin L ->
        Sub im Lt emp (x ~ bind_sub im ++ E) (open_tt A' x) (open_tt B' x).
Proof.
  induction 1; intros Hcm A' B' HA HB; try discriminate; eauto.
  inversion HA; inversion HB; subst.
  exists L. intros x Hx.
  eapply qs_sub_empty_evidence; [apply H; auto |].
  eapply qs_sub_lt_empty; eauto.
Qed.

Local Lemma qs_sub_unfold_lt : forall A B es,
    Sub Pos Lt es nil (typ_mu A) (typ_mu B) ->
    Sub Pos Lt emp nil (open_tt A (typ_mu A)) (open_tt B (typ_mu B)).
Proof.
  intros A B es H.
  destruct (qs_sub_mu_body _ _ _ _ _ _ H eq_refl _ _ eq_refl eq_refl) as [L HL].
  pick fresh x for (L \u fv_tt A \u fv_tt B).
  pose proof (HL x ltac:(auto)) as Hbody.
  pose proof (qs_sub_empty_evidence _ _ _ _ _ _ H (qs_sub_lt_empty _ _ _ _ _ _ H eq_refl)) as Hmu.
  destruct (qs_sub_substitute _ _ _ _ _ _ Hbody x (typ_mu A) (typ_mu B) nil)
    as [cm [Hcm Hsub]]; eauto using wf_env; try discriminate.
  - fsetdec.
  - intros y m Hne Hb. apply binds_cons_1 in Hb as [[Heq _]|Hb]; congruence.
  - rewrite (Hcm eq_refl) in Hsub. simpl in Hsub.
    unfold open_tt in *. rewrite !qs_subst_tt_intro in Hsub by auto. exact Hsub.
Qed.

Local Lemma qs_sub_neg_closed : forall cm es A B,
    Sub Neg cm es nil A B -> Sub Pos cm es nil A B.
Proof.
  intros cm es A B H.
  apply (qs_sub_map _ _ _ _ _ _ H flip_im nil); auto using wf_env.
Qed.

Local Lemma qs_wfs_unfold : forall E A, WFS E (typ_mu A) ->
    WFS E (open_tt A (typ_mu A)).
Proof.
  intros E A HW. inversion HW; subst.
  pick fresh x for (L \u fv_tt A).
  unfold open_tt. rewrite <- qs_subst_tt_intro with (x := x) by auto.
  eapply qs_wfs_subst.
  - eauto.
  - exact HW.
  - intros y m Hne Hb. apply binds_cons_1 in Hb as [[Heq _]|Hb]; congruence.
  - eauto using qs_open_tt_stable, qs_wfs_type.
Qed.

Local Lemma qs_typing_env : forall E e T, typing E e T -> wf_env E.
Proof.
  induction 1; auto.
  pick fresh x for L. specialize (H0 x ltac:(auto)); inversion H0; auto.
Qed.

Local Lemma qs_bind_type_wfs : forall E, wf_env E ->
    forall x T, binds x (bind_typ T) E -> WFS E T.
Proof.
  induction 1; intros y U Hb.
  - inversion Hb.
  - apply binds_cons_1 in Hb as [[_ Hcontra]|Hb]; try discriminate.
    eapply qs_wfs_map; eauto.
  - apply binds_cons_1 in Hb as [[_ Heq]|Hb].
    + inversion Heq; subst. eapply qs_wfs_map; eauto.
    + eapply qs_wfs_map; eauto.
Qed.

Local Lemma qs_typing_wfs : forall E e T, typing E e T -> WFS E T.
Proof.
  induction 1; eauto using WFS, qs_bind_type_wfs, qs_wfs_unfold.
  - pick fresh x for L.
    pose proof (qs_typing_env _ _ _ (H x ltac:(auto))) as HE.
    inversion HE; subst. constructor; auto.
    eapply qs_wfs_map; [apply H0; auto |].
    intros y im Hy Hb. apply binds_cons_1 in Hb as [[_ Hcontra]|Hb]; try discriminate; eauto.
  - inversion IHtyping1; auto.
  - apply (qs_sub_wfs _ _ _ _ _ _ H0).
Qed.

Local Lemma qs_typing_expr : forall E e T, typing E e T -> expr e.
Proof.
  induction 1; eauto using expr, qs_wfs_type, qs_typing_wfs.
  pick fresh x for L.
  pose proof (qs_typing_env _ _ _ (H x ltac:(auto))) as HE.
  inversion HE; subst. eauto using expr, qs_wfs_type.
Qed.

Local Lemma qs_open_ee_stable : forall e, expr e ->
    forall k u, open_ee_rec k u e = e.
Proof.
  assert (Hinv : forall e j k (x : atom) u,
      j <> k ->
      open_ee_rec k u (open_ee_rec j x e) = open_ee_rec j x e ->
      open_ee_rec k u e = e).
  { induction e; intros j k x u Hne H; simpl in *; try reflexivity.
    - destruct (j == n); simpl in H; destruct (k == n); congruence.
    - inversion H; f_equal; eapply IHe with (j := S j) (x := x); eauto.
    - inversion H; f_equal; [eapply IHe1 with (j := j) (x := x) | eapply IHe2 with (j := j) (x := x)]; eauto.
    - inversion H; f_equal; eapply IHe with (j := j) (x := x); eauto.
    - inversion H; f_equal; eapply IHe with (j := j) (x := x); eauto. }
  induction 1; intros k u; simpl; try reflexivity.
  - pick fresh x for L. f_equal. eapply Hinv with (j := 0) (x := x); eauto.
  - rewrite IHexpr1, IHexpr2; reflexivity.
  - rewrite IHexpr; reflexivity.
  - rewrite IHexpr; reflexivity.
Qed.

Local Lemma qs_subst_ee_open : forall e k x (y : atom) u,
    y <> x -> expr u ->
    subst_ee x u (open_ee_rec k y e) = open_ee_rec k y (subst_ee x u e).
Proof.
  induction e; intros k x y u Hne Hu; simpl; try reflexivity.
  - destruct (k == n); simpl; [destruct (y == x); congruence | reflexivity].
  - destruct (a == x); simpl; [symmetry; apply qs_open_ee_stable; auto | reflexivity].
  - rewrite IHe by auto; reflexivity.
  - rewrite IHe1, IHe2 by auto; reflexivity.
  - rewrite IHe by auto; reflexivity.
  - rewrite IHe by auto; reflexivity.
Qed.

Local Lemma qs_subst_ee_intro : forall e k (x : atom) u,
    x \notin fv_exp e ->
    subst_ee x u (open_ee_rec k x e) = open_ee_rec k u e.
Proof.
  induction e; intros k x u Hx; simpl in *; try reflexivity.
  - destruct (k == n); simpl; [destruct (x == x); congruence | reflexivity].
  - destruct (a == x); subst; try reflexivity; fsetdec.
  - rewrite IHe by auto; reflexivity.
  - rewrite IHe1, IHe2 by fsetdec; reflexivity.
  - rewrite IHe by auto; reflexivity.
  - rewrite IHe by auto; reflexivity.
Qed.

Local Lemma qs_typing_map : forall E e T, typing E e T ->
    forall F, wf_env F ->
      (forall x b, binds x b E -> binds x b F) ->
      typing F e T.
Proof.
  induction 1 as [E HE|E x T HE Hb|L E A e B H IH
      |E e1 e2 B A H1 IH1 H2 IH2|E A e H IH HA|E T e H IH
      |E T e S es cm H IH HS]; intros F HF Hmap;
    eauto using typing.
  - apply typing_abs with (L := L \u dom F).
    intros x Hx. apply IH; auto.
    + apply wf_env_typ; auto.
      pose proof (qs_typing_env _ _ _ (H x ltac:(auto))) as HE.
      inversion HE; subst. eapply qs_wfs_map; eauto.
    + intros y b Hb. apply binds_cons_1 in Hb as [[-> ->]|Hb]; auto.
  - apply typing_fold; auto. eapply qs_wfs_map; eauto.
  - eapply typing_sub; [apply IH; auto |].
    apply (qs_sub_map _ _ _ _ _ _ HS (fun m => m)); auto.
Qed.

Local Lemma qs_typing_subst : forall E e T, typing E e T ->
    forall F x u, wf_env F -> expr u ->
      (forall y im, binds y (bind_sub im) E -> binds y (bind_sub im) F) ->
      (forall y A, y <> x -> binds y (bind_typ A) E -> binds y (bind_typ A) F) ->
      (forall A, binds x (bind_typ A) E -> typing F u A) ->
      typing F (subst_ee x u e) T.
Proof.
  induction 1 as [E HE|E y T HE Hb|L E A e B H IH
      |E e1 e2 B A H1 IH1 H2 IH2|E A e H IH HA|E T e H IH
      |E T e S es cm H IH HS]; intros F x u HF Hu Hsub Htyp Hreplace;
    simpl; eauto using typing.
  - destruct (y == x) as [->|Hne]; eauto using typing.
  - apply typing_abs with (L := L \u dom F \u {{x}}).
    intros y Hy. rewrite <- qs_subst_ee_open by (auto; fsetdec).
    assert (HF' : wf_env (y ~ bind_typ A ++ F)).
    { apply wf_env_typ; auto.
      pose proof (qs_typing_env _ _ _ (H y ltac:(auto))) as HE.
      inversion HE; subst. eapply qs_wfs_map; eauto. }
    apply IH; auto.
    + intros z m Hb. apply binds_cons_1 in Hb as [[_ Hcontra]|Hb]; try discriminate; auto.
    + intros z Z Hne Hb. apply binds_cons_1 in Hb as [[-> HZ]|Hb];
        [injection HZ as ->; auto | auto].
    + intros Z Hb. apply binds_cons_1 in Hb as [[Heq _]|Hb].
      * exfalso; fsetdec.
      * eapply qs_typing_map; eauto.
  - apply typing_fold; auto. eapply qs_wfs_map; eauto.
  - eapply typing_sub; [apply IH; auto |].
    apply (qs_sub_map _ _ _ _ _ _ HS (fun m => m)); auto.
Qed.

Local Lemma qs_abs_apply : forall E e T, typing E e T ->
    E = nil ->
    forall V body A B u,
      e = exp_abs V body -> T = typ_arrow A B ->
      typing nil u A -> typing nil (open_ee body u) B.
Proof.
  induction 1 as [E HE|E y T HE Hb|L E A e B H IH
      |E e1 e2 B A H1 IH1 H2 IH2|E A e H IH HA|E T e H IH
      |E T e S es cm H IH HS];
    intros HE' V body A' B' u He HT Hu; subst E; try discriminate.
  - inversion He; inversion HT; subst.
    pick fresh x for (L \u fv_exp body).
    rewrite <- qs_subst_ee_intro with (x := x) by auto.
    eapply qs_typing_subst; eauto using wf_env, qs_typing_expr.
    + intros y im Hb. apply binds_cons_1 in Hb as [[_ Hcontra]|Hb];
        [discriminate | inversion Hb].
    + intros y Z Hne Hb. apply binds_cons_1 in Hb as [[Heq _]|Hb]; congruence.
    + intros Z Hb. apply binds_cons_1 in Hb as [[_ Heq]|Hb]; [inversion Heq; subst; auto | inversion Hb].
  - destruct (qs_sub_arrow_inv _ _ _ _ _ _ HS A' B' HT)
      as [A [B [c1 [s1 [c2 [s2 [-> [Hdom Hcod]]]]]]]].
    eapply typing_sub; [eapply IH; eauto | exact Hcod].
    eapply typing_sub; eauto using qs_sub_neg_closed.
Qed.

Local Lemma qs_fold_content : forall E e T, typing E e T ->
    E = nil ->
    forall V v B, e = exp_fold V v -> T = typ_mu B ->
      typing nil v (open_tt B (typ_mu B)).
Proof.
  induction 1 as [E HE|E y T HE Hb|L E A e B H IH
      |E e1 e2 B A H1 IH1 H2 IH2|E A e H IH HA|E T e H IH
      |E T e S es cm H IH HS];
    intros HE' V v B' He HT; subst E; try discriminate.
  - inversion He; inversion HT; subst; auto.
  - destruct (qs_sub_mu_inv _ _ _ _ _ _ HS B' HT) as [A ->].
    subst T. specialize (IH eq_refl V v A He eq_refl).
    destruct cm.
    + eapply typing_sub; eauto using qs_sub_unfold_lt.
    + pose proof (qs_sub_eq _ _ _ _ _ _ HS eq_refl) as Heq.
      inversion Heq; subst; auto.
Qed.

Theorem preservation : forall e e' T,
    typing nil e T ->
    step e e' ->
    typing nil e' T.
Proof.
  intros e e' T Hty.
  remember (@nil (atom * binding)) as E.
  revert e'. induction Hty; intros e' Hstep; subst; try solve [inversion Hstep].
  - inversion Hstep; subst.
    + eapply qs_abs_apply; eauto.
    + eapply typing_app; eauto.
    + eapply typing_app; eauto.
  - inversion Hstep; subst. eapply typing_fold; eauto.
  - inversion Hstep; subst.
    + eapply qs_fold_content; eauto.
    + eapply typing_unfold; eauto.
  - eapply typing_sub; eauto.
Qed.

Local Lemma qs_canonical_arrow : forall E v T, typing E v T ->
    value v -> forall A B, T = typ_arrow A B ->
      exists V body, v = exp_abs V body.
Proof.
  induction 1; intros Hv A' B' HT; try discriminate; eauto;
    try solve [inversion Hv].
  destruct (qs_sub_arrow_inv _ _ _ _ _ _ H0 A' B' HT)
    as [A [B [c1 [s1 [c2 [s2 [-> _]]]]]]].
  eauto.
Qed.

Local Lemma qs_canonical_mu : forall E v T, typing E v T ->
    value v -> forall A, T = typ_mu A ->
      exists V u, v = exp_fold V u.
Proof.
  induction 1; intros Hv A' HT; try discriminate; eauto;
    try solve [inversion Hv].
  destruct (qs_sub_mu_inv _ _ _ _ _ _ H0 A' HT) as [A ->].
  eauto.
Qed.

Theorem progress : forall e T,
  typing empty e T ->
  value e \/ exists e', step e e'.
Proof.
  intros e T Hty.
  remember (@nil (atom * binding)) as E.
  induction Hty; subst.
  - left; constructor.
  - inversion H0.
  - left. apply value_abs.
    eapply qs_typing_expr. eapply typing_abs with (L := L); eauto.
  - right. destruct IHHty1 as [Hv1 | [e1' Hs1]]; auto.
    + destruct IHHty2 as [Hv2 | [e2' Hs2]]; auto.
      * destruct (qs_canonical_arrow _ _ _ Hty1 Hv1 _ _ eq_refl) as [V [body ->]].
        eexists. eapply step_beta; eauto using qs_typing_expr.
      * eexists. eapply step_app2; eauto.
    + eexists. eapply step_app1; eauto using qs_typing_expr.
  - destruct IHHty as [Hv | [e' Hs]]; auto.
    + left. apply value_fold; eauto using qs_wfs_type.
    + right. eexists. apply step_fold; eauto using qs_wfs_type.
  - right. pose proof (qs_wfs_type _ _ (qs_typing_wfs _ _ _ Hty)) as Hann.
    destruct IHHty as [Hv | [e' Hs]]; auto.
    + destruct (qs_canonical_mu _ _ _ Hty Hv _ eq_refl) as [V [u ->]].
      inversion Hv; subst. eexists. eapply step_fld; eauto.
    + eexists. eapply step_unfold; eauto.
  - auto.
Qed.
