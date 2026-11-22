From Fsub Require Import Fm_Definitions.

Set Warnings "-unused-intro-pattern".



(* ---------------------------------------------------------------- *)
(* Basic list / environment facts                                    *)
(* ---------------------------------------------------------------- *)

Lemma Dev__binds_app_1 : forall (E F : env) x (b : binding),
  binds x b E -> binds x b (E ++ F).
Proof. intros. apply in_or_app. left. assumption. Qed.

Lemma Dev__binds_app_2 : forall (E F : env) x (b : binding),
  binds x b F -> binds x b (E ++ F).
Proof. intros. apply in_or_app. right. assumption. Qed.

Lemma Dev__binds_cons_1 : forall (E : env) x (b : binding),
  binds x b ((x,b)::E).
Proof. intros. simpl. left. reflexivity. Qed.

Lemma Dev__binds_cons_2 : forall (E : env) x y (a b : binding),
  binds x a E -> binds x a ((y,b)::E).
Proof. intros. simpl. right. assumption. Qed.

Lemma Dev__binds_cons_inv : forall (E : env) x y (a b : binding),
  binds x a ((y,b)::E) -> (x,a) = (y,b) \/ binds x a E.
Proof. intros. simpl in H. destruct H; auto. Qed.

Lemma Dev__binds_cons_neq : forall (E : env) x y (a b : binding),
  x <> y -> binds x a ((y,b)::E) -> binds x a E.
Proof.
  intros. apply Dev__binds_cons_inv in H0. destruct H0 as [Heq | Hin].
  inversion Heq. subst. exfalso. apply H. reflexivity. assumption.
Qed.

Lemma Dev__in_dom_cons : forall (E : env) x y (b : binding),
  x `in` dom ((y,b)::E) <-> x = y \/ x `in` dom E.
Proof. intros. simpl. rewrite add_iff. split; intros [H|H].
  - left. symmetry. assumption.
  - right. assumption.
  - left. symmetry. assumption.
  - right. assumption.
Qed.

Lemma Dev__in_dom_binds : forall (E : env) x (b : binding),
  binds x b E -> x `in` dom E.
Proof.
  induction E as [| [y b'] E IH]; intros x b Hb.
  - inversion Hb.
  - apply (Dev__in_dom_cons E x y b'). simpl in Hb. destruct Hb as [Heq | Hin].
    + inversion Heq. subst. left. reflexivity.
    + right. apply (IH x b). assumption.
Qed.

(* ---------------------------------------------------------------- *)
(* Free atoms of a type                                              *)
(* ---------------------------------------------------------------- *)

Fixpoint Dev__fv_typ (T : typ) : atoms :=
  match T with
  | typ_top => {}
  | typ_bvar _ => {}
  | typ_fvar X => {{ X }}
  | typ_arrow T1 T2 => Dev__fv_typ T1 `union` Dev__fv_typ T2
  | typ_all T1 T2 => Dev__fv_typ T1 `union` Dev__fv_typ T2
  | typ_box T1 => Dev__fv_typ T1
  | typ_mut _ T1 => Dev__fv_typ T1
  | typ_int T1 T2 => Dev__fv_typ T1 `union` Dev__fv_typ T2
  | typ_record _ T1 => Dev__fv_typ T1
  end.

Lemma Dev__fv_typ_open_tt : forall (T : typ) K (U : typ) X,
  X `notin` Dev__fv_typ T -> X `notin` Dev__fv_typ U ->
  X `notin` Dev__fv_typ (open_tt_rec K U T).
Proof.
  induction T; intros K U X HT HU; simpl in *.
  - auto.
  - destruct (K == n) eqn:E; simpl.
    + assumption.
    + auto.
  - auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
Qed.

Lemma Dev__fv_typ_open_tt_fvar : forall (T : typ) K (Y X : atom),
  X `notin` Dev__fv_typ T -> X <> Y ->
  X `notin` Dev__fv_typ (open_tt_rec K (typ_fvar Y) T).
Proof.
  intros T K Y X HT HXY.
  assert (Hnot : X `notin` Dev__fv_typ (typ_fvar Y)).
  { simpl. apply notin_singleton. auto. }
  eapply Dev__fv_typ_open_tt; eauto.
Qed.

(* ---------------------------------------------------------------- *)
(* Well-formed types depend only on the bindings available           *)
(* ---------------------------------------------------------------- *)

Lemma Dev__wf_typ_binds_iff : forall (E1 : env) T,
  wf_typ E1 T ->
  forall (E2 : env), (forall x b, binds x b E1 <-> binds x b E2) -> wf_typ E2 T.
Proof.
  intros E1 T H. induction H; intros E2 Hiff.
  - constructor.
  - apply (wf_typ_var U E2 X). apply (proj1 (Hiff X (bind_sub U))). assumption.
  - constructor; auto.
  - apply wf_typ_all with (L := L); auto.
    intros X HX. apply (H1 X HX (X ~ bind_sub T1 ++ E2)).
    intros y b. simpl. split; intros [Heq | Hin].
    + left; assumption.
    + right. apply (proj1 (Hiff y b)); assumption.
    + left; assumption.
    + right. apply (proj2 (Hiff y b)); assumption.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma Dev__binds_cons_app_iff : forall (E E' : env) X (T : binding) y (b : binding),
  binds y b (((X,T)::E') ++ ((X,T)::E)) <-> binds y b ((X,T)::(E'++E)).
Proof. intros. unfold binds. repeat rewrite in_app_iff. simpl. rewrite in_app_iff. tauto. Qed.

Lemma Dev__wf_typ_weaken : forall (E : env) T,
  wf_typ E T -> forall (E' : env), wf_typ (E' ++ E) T.
Proof.
  intros E T H. induction H; intros E'.
  - constructor.
  - apply (wf_typ_var U (E' ++ E) X). apply Dev__binds_app_2. assumption.
  - constructor; auto.
  - apply wf_typ_all with (L := L).
    + auto.
    + intros X HX. eapply Dev__wf_typ_binds_iff.
      * apply (H1 X HX (((X, bind_sub T1) :: E'))).
      * apply Dev__binds_cons_app_iff.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma Dev__wf_typ_weaken_cons1 : forall (E : env) X (b : binding) T,
  wf_typ E T -> wf_typ ((X,b)::E) T.
Proof. intros E X b T H. apply (Dev__wf_typ_weaken E T H ((X,b)::nil)). Qed.

(* ---------------------------------------------------------------- *)
(* wf_env                                                           *)
(* ---------------------------------------------------------------- *)

Lemma Dev__wf_sig_wf_env : forall (E : env) (R : sig),
  wf_sig E R -> wf_env E.
Proof. intros E R H. induction H. assumption. assumption. Qed.

Lemma Dev__wf_env_cons_bind_typ : forall (E : env) x T,
  wf_env (x ~ bind_typ T ++ E) -> wf_env E /\ wf_typ E T.
Proof.
  intros. inversion H; subst; try discriminate.
  split; assumption.
Qed.

Lemma Dev__wf_env_cons_bind_sub : forall (E : env) x T,
  wf_env (x ~ bind_sub T ++ E) -> wf_env E /\ wf_typ E T.
Proof.
  intros. inversion H; subst; try discriminate.
  split; assumption.
Qed.

Lemma Dev__wf_env_binds_typ : forall (E : env), wf_env E ->
  forall x T, binds x (bind_typ T) E -> wf_typ E T.
Proof.
  intros E H. induction H; intros y Ty Hy.
  - inversion Hy.
  - apply Dev__binds_cons_inv in Hy. destruct Hy as [Heq | Hin].
    + inversion Heq.
    + eapply Dev__wf_typ_weaken_cons1; eauto.
  - apply Dev__binds_cons_inv in Hy. destruct Hy as [Heq | Hin].
    + injection Heq as Hy' Hu. subst. eapply Dev__wf_typ_weaken_cons1; eauto.
    + eapply Dev__wf_typ_weaken_cons1; eauto.
Qed.

Lemma Dev__wf_env_binds_sub : forall (E : env), wf_env E ->
  forall x T, binds x (bind_sub T) E -> wf_typ E T.
Proof.
  intros E H. induction H; intros y Ty Hy.
  - inversion Hy.
  - apply Dev__binds_cons_inv in Hy. destruct Hy as [Heq | Hin].
    + injection Heq as Hy' Hu. subst. eapply Dev__wf_typ_weaken_cons1; eauto.
    + eapply Dev__wf_typ_weaken_cons1; eauto.
  - apply Dev__binds_cons_inv in Hy. destruct Hy as [Heq | Hin].
    + inversion Heq.
    + eapply Dev__wf_typ_weaken_cons1; eauto.
Qed.

(* ---------------------------------------------------------------- *)
(* Strengthening wf_typ                                              *)
(* ---------------------------------------------------------------- *)

Lemma Dev__binds_cons_iff_lift : forall (E1 E2 : env) (Y : atom) (T : binding),
  (forall y b, binds y b E1 <-> binds y b E2) ->
  forall y b, binds y b ((Y,T)::E1) <-> binds y b ((Y,T)::E2).
Proof.
  intros E1 E2 Y T Hiff y b. simpl. split; intros [Hc|Hin].
  - left; assumption.
  - right. apply (proj1 (Hiff y b)); assumption.
  - left; assumption.
  - right. apply (proj2 (Hiff y b)); assumption.
Qed.

Lemma Dev__binds_swap_cons : forall (E : env) X (T : binding) Y (U : binding) y b,
  binds y b ((X,T)::(Y,U)::E) <-> binds y b ((Y,U)::(X,T)::E).
Proof. intros. unfold binds. simpl. tauto. Qed.

Lemma Dev__binds_cons_bind_typ_app : forall (E1 E2 : env) x V (Y : atom) (U : binding) y b,
  (forall z c, binds z c E1 <-> binds z c (x ~ bind_typ V ++ E2)) ->
  (binds y b ((Y,U)::E1) <-> binds y b ((x, bind_typ V)::(Y,U)::E2)).
Proof.
  intros E1 E2 x V Y U y b Hiff.
  etransitivity.
  - apply (Dev__binds_cons_iff_lift E1 (x ~ bind_typ V ++ E2) Y U Hiff).
  - apply Dev__binds_swap_cons.
Qed.

Lemma Dev__wf_typ_remove_bind_typ : forall (E1 : env) T,
  wf_typ E1 T ->
  forall (E2 : env) x V,
    (forall y b, binds y b E1 <-> binds y b (x ~ bind_typ V ++ E2)) ->
    x `notin` Dev__fv_typ T ->
    wf_typ E2 T.
Proof.
  intros E1 T H.
  induction H as [ E
                  | U E X Hb
                  | E T1 T2 H1 IH1 H2 IH2
                  | L E T1 T2 H1 IH1 H0 IH0
                  | E T H1 IH1
                  | E T H1 IH1
                  | E T1 T2 H1 IH1 H2 IH2
                  | E a T1 H1 IH1 ];
  intros E2 x V Hiff Hfv.
  - constructor.
  - apply (wf_typ_var U E2 X).
    apply (proj1 (Hiff X (bind_sub U))) in Hb.
    destruct Hb as [Heq | Hin].
    + inversion Heq.
    + assumption.
  - constructor.
    + apply IH1 with (x := x) (V := V).
      * assumption.
      * apply notin_union_1 in Hfv. assumption.
    + apply IH2 with (x := x) (V := V).
      * assumption.
      * apply notin_union_2 in Hfv. assumption.
  - apply wf_typ_all with (L := L `union` {{ x }}).
    + apply IH1 with (x := x) (V := V).
      * assumption.
      * apply notin_union_1 in Hfv. assumption.
    + intros Y HY.
      assert (HYL : Y `notin` L) by (apply notin_union_1 in HY; assumption).
      assert (HYx : Y <> x).
      { assert (Hny : Y `notin` {{ x }}) by (apply notin_union_2 in HY; assumption).
        apply notin_singleton_1' in Hny. symmetry. exact Hny. }
      assert (HfvT2 : x `notin` Dev__fv_typ T2) by (apply notin_union_2 in Hfv; assumption).
      assert (Hfvo : x `notin` Dev__fv_typ (open_tt T2 Y)).
      { apply Dev__fv_typ_open_tt_fvar; auto. }
      apply (IH0 Y HYL (Y ~ bind_sub T1 ++ E2) x V).
      * intros y b. eapply Dev__binds_cons_bind_typ_app. exact Hiff.
      * assumption.
  - constructor.
    + apply IH1 with (x := x) (V := V); auto.
  - constructor.
    + apply IH1 with (x := x) (V := V); auto.
  - constructor.
    + apply IH1 with (x := x) (V := V).
      * assumption.
      * apply notin_union_1 in Hfv. assumption.
    + apply IH2 with (x := x) (V := V).
      * assumption.
      * apply notin_union_2 in Hfv. assumption.
  - constructor.
    + apply IH1 with (x := x) (V := V); auto.
Qed.

(* ---------------------------------------------------------------- *)
(* wf_typ inversion                                                  *)
(* ---------------------------------------------------------------- *)

Lemma Dev__wf_typ_inv_fvar : forall (E : env) (X : atom),
  wf_typ E (typ_fvar X) -> exists U, binds X (bind_sub U) E.
Proof. intros. inversion H; subst. eauto. Qed.

Lemma Dev__wf_typ_inv_arrow : forall (E : env) T1 T2,
  wf_typ E (typ_arrow T1 T2) -> wf_typ E T1 /\ wf_typ E T2.
Proof. intros. inversion H; subst. auto. Qed.

Lemma Dev__wf_typ_inv_all : forall (E : env) T1 T2,
  wf_typ E (typ_all T1 T2) ->
  exists L, wf_typ E T1 /\
    (forall X : atom, X `notin` L -> wf_typ (X ~ bind_sub T1 ++ E) (open_tt T2 X)).
Proof. intros. inversion H; subst. eauto. Qed.

Lemma Dev__wf_typ_inv_box : forall (E : env) T,
  wf_typ E (typ_box T) -> wf_typ E T.
Proof. intros. inversion H; subst. assumption. Qed.

Lemma Dev__wf_typ_inv_readonly : forall (E : env) m T,
  wf_typ E (typ_mut m T) -> wf_typ E T.
Proof. intros. inversion H; subst. assumption. Qed.

Lemma Dev__wf_typ_inv_inter : forall (E : env) T1 T2,
  wf_typ E (typ_int T1 T2) -> wf_typ E T1 /\ wf_typ E T2.
Proof. intros. inversion H; subst. auto. Qed.

Lemma Dev__wf_typ_inv_record : forall (E : env) a T,
  wf_typ E (typ_record a T) -> wf_typ E T.
Proof. intros. inversion H; subst. assumption. Qed.

(* ---------------------------------------------------------------- *)
(* Subtyping basics                                                 *)
(* ---------------------------------------------------------------- *)

(* ---------------------------------------------------------------- *)
(* Environment equivalence for wf_typ                                *)
(* ---------------------------------------------------------------- *)

Definition Dev__same_kinds (E1 E2 : env) : Prop :=
  forall X, (exists U, binds X (bind_sub U) E1) <-> (exists U, binds X (bind_sub U) E2).

Lemma Dev__same_kinds_refl : forall E, Dev__same_kinds E E.
Proof. intros. intros X. reflexivity. Qed.

Lemma Dev__same_kinds_cons_sub : forall (E1 E2 : env) X U,
  Dev__same_kinds E1 E2 -> Dev__same_kinds ((X, bind_sub U)::E1) ((X, bind_sub U)::E2).
Proof.
  intros E1 E2 X U Hsk Y. simpl. split; intros [V HV].
  - destruct HV as [Heq | Hin].
    + exists V. left. exact Heq.
    + destruct (proj1 (Hsk Y) (ex_intro _ V Hin)) as [V' HV'].
      exists V'. right. assumption.
  - destruct HV as [Heq | Hin].
    + exists V. left. exact Heq.
    + destruct (proj2 (Hsk Y) (ex_intro _ V Hin)) as [V' HV'].
      exists V'. right. assumption.
Qed.

Lemma Dev__same_kinds_cons_sub_any : forall (E1 E2 : env) X U U',
  Dev__same_kinds E1 E2 -> Dev__same_kinds ((X, bind_sub U)::E1) ((X, bind_sub U')::E2).
Proof.
  intros E1 E2 X U U' Hsk Y. simpl. split; intros [V HV].
  - destruct HV as [Heq | Hin].
    + injection Heq as HXY HV'. subst. exists U'. left. reflexivity.
    + destruct (proj1 (Hsk Y) (ex_intro _ V Hin)) as [V' HV'].
      exists V'. right. assumption.
  - destruct HV as [Heq | Hin].
    + injection Heq as HXY HV'. subst. exists U. left. reflexivity.
    + destruct (proj2 (Hsk Y) (ex_intro _ V Hin)) as [V' HV'].
      exists V'. right. assumption.
Qed.

Lemma Dev__same_kinds_cons_typ : forall (E1 E2 : env) X U,
  Dev__same_kinds E1 E2 -> Dev__same_kinds ((X, bind_typ U)::E1) ((X, bind_typ U)::E2).
Proof.
  intros E1 E2 X U Hsk Y. simpl. split; intros [V HV].
  - destruct HV as [Heq | Hin].
    + inversion Heq.
    + destruct (proj1 (Hsk Y) (ex_intro _ V Hin)) as [V' HV'].
      exists V'. right. assumption.
  - destruct HV as [Heq | Hin].
    + inversion Heq.
    + destruct (proj2 (Hsk Y) (ex_intro _ V Hin)) as [V' HV'].
      exists V'. right. assumption.
Qed.

Lemma Dev__wf_typ_kind : forall (E1 : env) T,
  wf_typ E1 T -> forall (E2 : env), Dev__same_kinds E1 E2 -> wf_typ E2 T.
Proof.
  intros E1 T H. induction H; intros E2 Hsk.
  - constructor.
  - destruct (proj1 (Hsk X) (ex_intro _ U H)) as [U' HU'].
    apply (wf_typ_var U' E2 X). assumption.
  - constructor; auto.
  - apply wf_typ_all with (L := L); auto.
    intros X HX. apply (H1 X HX (X ~ bind_sub T1 ++ E2)). apply Dev__same_kinds_cons_sub. assumption.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma Dev__sub_wf_both : forall (E : env) S T, sub E S T ->
  (wf_env E -> wf_typ E S -> wf_typ E T) /\
  (wf_env E -> wf_typ E T -> wf_typ E S).
Proof.
  intros E S T H.
  induction H as [ E0 S0 HE0 HS0
                 | E0 X HE0 HS0
                 | U E0 T0 X Hb Hsub IHsub
                 | E0 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E0 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 T1 T2 HE0 HS1 HS2
                 | E0 T1 T2 HE0 HS1 HS2
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1
                 | E0 T1 T2 HS1 HS2 Hsub IHsub ].
  - (* top *) split; intros HE Hx; [constructor | exact HS0].
  - (* refl tvar *) split; intros; assumption.
  - (* trans tvar *) split.
    + intros HE HS. destruct IHsub as [IH1 _].
      apply (IH1 HE). apply (Dev__wf_env_binds_sub _ HE X U Hb).
    + intros HE HT. apply (wf_typ_var U E0 X Hb).
  - (* arrow *) split.
    + intros HE HS. destruct (Dev__wf_typ_inv_arrow _ _ _ HS) as [HS1 HS2].
      destruct IH1 as [_ IH1b]. destruct IH2 as [IH2a _].
      apply wf_typ_arrow; [apply IH1b | apply IH2a]; assumption.
    + intros HE HT. destruct (Dev__wf_typ_inv_arrow _ _ _ HT) as [HT1 HT2].
      destruct IH1 as [IH1a _]. destruct IH2 as [_ IH2b].
      apply wf_typ_arrow; [apply IH1a | apply IH2b]; assumption.
  - (* all *) split.
    + intros HE HS. destruct (Dev__wf_typ_inv_all _ _ _ HS) as [Ls [HS1 HS2]].
      assert (HT1 : wf_typ E0 T1).
      { destruct IH1 as [_ IH1b]. apply (IH1b HE HS1). }
      apply wf_typ_all with (L := L0 `union` Ls `union` dom E0).
      * exact HT1.
      * intros X HX.
        assert (HXL0 : X `notin` L0) by (apply notin_union_1 in HX; assumption).
        assert (HXLs : X `notin` Ls) by (apply notin_union_2 in HX; apply notin_union_1 in HX; assumption).
        assert (HXd : X `notin` dom E0) by (apply notin_union_2 in HX; apply notin_union_2 in HX; assumption).
        assert (Hwe : wf_env (X ~ bind_sub T1 ++ E0)).
        { apply (wf_env_sub E0 X T1); auto. }
        assert (Hws0 : wf_typ (X ~ bind_sub S1 ++ E0) (open_tt S2 X)).
        { apply HS2. assumption. }
        assert (Hws : wf_typ (X ~ bind_sub T1 ++ E0) (open_tt S2 X)).
        { eapply Dev__wf_typ_kind.
          - exact Hws0.
          - intros Y. apply Dev__same_kinds_cons_sub_any. apply Dev__same_kinds_refl. }
        destruct (IH0 X HXL0) as [IH0a _]. apply (IH0a Hwe Hws).
    + intros HE HT. destruct (Dev__wf_typ_inv_all _ _ _ HT) as [Lt [HT1 HT2]].
      apply wf_typ_all with (L := L0 `union` Lt `union` dom E0).
      * destruct IH1 as [IH1a _]. apply (IH1a HE HT1).
      * intros X HX.
        assert (HXL0 : X `notin` L0) by (apply notin_union_1 in HX; assumption).
        assert (HXLt : X `notin` Lt) by (apply notin_union_2 in HX; apply notin_union_1 in HX; assumption).
        assert (HXd : X `notin` dom E0) by (apply notin_union_2 in HX; apply notin_union_2 in HX; assumption).
        assert (Hwe : wf_env (X ~ bind_sub T1 ++ E0)).
        { apply (wf_env_sub E0 X T1); auto. }
        assert (Hwt : wf_typ (X ~ bind_sub T1 ++ E0) (open_tt T2 X)).
        { apply HT2. assumption. }
        destruct (IH0 X HXL0) as [_ IH0b].
        eapply Dev__wf_typ_kind.
        { apply (IH0b Hwe Hwt). }
        intros Y. apply Dev__same_kinds_cons_sub_any. apply Dev__same_kinds_refl.
  - (* box *) split.
    + intros HE HS. destruct IH1 as [IH1a _].
      apply wf_typ_box. apply IH1a; [exact HE | apply (Dev__wf_typ_inv_box _ _ HS)].
    + intros HE HT. destruct IH1 as [_ IH1b].
      apply wf_typ_box. apply IH1b; [exact HE | apply (Dev__wf_typ_inv_box _ _ HT)].
  - (* readonly *) split.
    + intros HE HS. destruct IH1 as [IH1a _].
      apply wf_typ_readonly. apply IH1a; [exact HE | apply (Dev__wf_typ_inv_readonly _ _ _ HS)].
    + intros HE HT. destruct IH1 as [_ IH1b].
      apply wf_typ_readonly. apply IH1b; [exact HE | apply (Dev__wf_typ_inv_readonly _ _ _ HT)].
  - (* readonly mutable *) split.
    + intros HE HS. destruct IH1 as [IH1a _].
      apply wf_typ_readonly. apply IH1a; [exact HE | assumption].
    + intros HE HT. destruct IH1 as [_ IH1b].
      apply IH1b; [exact HE | apply (Dev__wf_typ_inv_readonly _ _ _ HT)].
  - (* trans *) split.
    + intros HE HS. destruct IH1 as [IH1a _]. destruct IH2 as [IH2a _].
      apply IH2a; [exact HE | apply IH1a; [exact HE | assumption]].
    + intros HE HT. destruct IH2 as [_ IH2b]. destruct IH1 as [_ IH1b].
      apply IH1b; [exact HE | apply IH2b; [exact HE | assumption]].
  - (* inter left *) split.
    + intros HE HS. apply (Dev__wf_typ_inv_inter _ _ _ HS).
    + intros HE HT. apply wf_typ_intersect; assumption.
  - (* inter right *) split.
    + intros HE HS. apply (proj2 (Dev__wf_typ_inv_inter _ _ _ HS)).
    + intros HE HT. apply wf_typ_intersect; assumption.
  - (* inter *) split.
    + intros HE HS. destruct IH1 as [IH1a _]. destruct IH2 as [IH2a _].
      apply wf_typ_intersect; auto.
    + intros HE HT. destruct (Dev__wf_typ_inv_inter _ _ _ HT) as [HT2 HT3].
      destruct IH1 as [_ IH1b]. apply (IH1b HE HT2).
  - (* record *) split.
    + intros HE HS. destruct IH1 as [IH1a _].
      apply wf_typ_record. apply IH1a; [exact HE | apply (Dev__wf_typ_inv_record _ _ _ HS)].
    + intros HE HT. destruct IH1 as [_ IH1b].
      apply wf_typ_record. apply IH1b; [exact HE | apply (Dev__wf_typ_inv_record _ _ _ HT)].
  - (* readonly record *) split.
    + intros HE HS. destruct IH1 as [IH1a _].
      apply wf_typ_readonly. apply wf_typ_record. apply IH1a; [exact HE | apply (Dev__wf_typ_inv_record _ _ _ (Dev__wf_typ_inv_readonly _ _ _ HS))].
    + intros HE HT. destruct IH1 as [_ IH1b].
      apply wf_typ_readonly. apply wf_typ_record. apply IH1b; [exact HE | apply (Dev__wf_typ_inv_record _ _ _ (Dev__wf_typ_inv_readonly _ _ _ HT))].
  - (* denormalize *) split; intros; assumption.
Qed.

Lemma Dev__sub_wf_target : forall (E : env) S T,
  wf_env E -> wf_typ E S -> sub E S T -> wf_typ E T.
Proof. intros. apply (proj1 (Dev__sub_wf_both E S T H1)); assumption. Qed.

Lemma Dev__sub_wf_source : forall (E : env) S T,
  wf_env E -> wf_typ E T -> sub E S T -> wf_typ E S.
Proof. intros. apply (proj2 (Dev__sub_wf_both E S T H1)); assumption. Qed.

(* ---------------------------------------------------------------- *)
(* Normal forms and merge_mutability                                *)
(* ---------------------------------------------------------------- *)

Lemma Dev__merge_top : forall m, merge_mutability typ_top m = typ_top.
Proof. reflexivity. Qed.
Lemma Dev__merge_bvar : forall J m, merge_mutability (typ_bvar J) m = typ_mut m (typ_bvar J).
Proof. reflexivity. Qed.
Lemma Dev__merge_fvar : forall X m, merge_mutability (typ_fvar X) m = typ_mut m (typ_fvar X).
Proof. reflexivity. Qed.
Lemma Dev__merge_arrow : forall T1 T2 m, merge_mutability (typ_arrow T1 T2) m = typ_arrow T1 T2.
Proof. reflexivity. Qed.
Lemma Dev__merge_all : forall T1 T2 m, merge_mutability (typ_all T1 T2) m = typ_all T1 T2.
Proof. reflexivity. Qed.
Lemma Dev__merge_box : forall T m, merge_mutability (typ_box T) m = typ_mut m (typ_box T).
Proof. reflexivity. Qed.
Lemma Dev__merge_mut : forall M T m, merge_mutability (typ_mut M T) m = typ_mut M T.
Proof. reflexivity. Qed.
Lemma Dev__merge_int : forall T1 T2 m,
  merge_mutability (typ_int T1 T2) m = typ_int (merge_mutability T1 m) (merge_mutability T2 m).
Proof. reflexivity. Qed.
Lemma Dev__merge_record : forall a T m, merge_mutability (typ_record a T) m = typ_mut m (typ_record a T).
Proof. reflexivity. Qed.

Lemma Dev__nf_top : normal_form_typing typ_top = typ_top.
Proof. reflexivity. Qed.
Lemma Dev__nf_bvar : forall J, normal_form_typing (typ_bvar J) = typ_bvar J.
Proof. reflexivity. Qed.
Lemma Dev__nf_fvar : forall X, normal_form_typing (typ_fvar X) = typ_fvar X.
Proof. reflexivity. Qed.
Lemma Dev__nf_arrow : forall T1 T2,
  normal_form_typing (typ_arrow T1 T2) = typ_arrow (normal_form_typing T1) (normal_form_typing T2).
Proof. reflexivity. Qed.
Lemma Dev__nf_all : forall T1 T2,
  normal_form_typing (typ_all T1 T2) = typ_all (normal_form_typing T1) (normal_form_typing T2).
Proof. reflexivity. Qed.
Lemma Dev__nf_box : forall T, normal_form_typing (typ_box T) = typ_box (normal_form_typing T).
Proof. reflexivity. Qed.
Lemma Dev__nf_mut : forall M T, normal_form_typing (typ_mut M T) = merge_mutability (normal_form_typing T) M.
Proof. reflexivity. Qed.
Lemma Dev__nf_int : forall T1 T2,
  normal_form_typing (typ_int T1 T2) = typ_int (normal_form_typing T1) (normal_form_typing T2).
Proof. reflexivity. Qed.
Lemma Dev__nf_record : forall a T, normal_form_typing (typ_record a T) = typ_record a (normal_form_typing T).
Proof. reflexivity. Qed.

Lemma Dev__merge_merge : forall (T : typ) m m',
  merge_mutability (merge_mutability T m) m' = merge_mutability T m.
Proof.
  induction T; intros mm mm'; cbn [merge_mutability].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHT1. rewrite IHT2. reflexivity.
  - reflexivity.
Qed.

Lemma Dev__merge_wf : forall (E : env) T,
  wf_typ E T -> forall m, wf_typ E (merge_mutability T m).
Proof.
  intros E T H. induction H; intros mm.
  - rewrite Dev__merge_top. constructor.
  - rewrite Dev__merge_fvar. destruct mm. apply wf_typ_readonly. apply (wf_typ_var U E X). assumption.
  - rewrite Dev__merge_arrow. constructor; assumption.
  - rewrite Dev__merge_all. apply wf_typ_all with (L := L); auto.
  - rewrite Dev__merge_box. destruct mm. apply wf_typ_readonly. apply wf_typ_box. assumption.
  - rewrite Dev__merge_mut. apply wf_typ_readonly. assumption.
  - rewrite Dev__merge_int. constructor; [apply IHwf_typ1 | apply IHwf_typ2].
  - rewrite Dev__merge_record. destruct mm. apply wf_typ_readonly. apply wf_typ_record. assumption.
Qed.

Lemma Dev__open_tt_merge : forall K (Y : atom) (T : typ) m,
  open_tt_rec K (typ_fvar Y) (merge_mutability T m)
  = merge_mutability (open_tt_rec K (typ_fvar Y) T) m.
Proof.
  induction T; intros mm; cbn [open_tt_rec merge_mutability].
  - reflexivity.
  - destruct (K == n); reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHT1. rewrite IHT2. reflexivity.
  - reflexivity.
Qed.

Lemma Dev__nf_merge : forall (T : typ) m,
  normal_form_typing (merge_mutability T m) = merge_mutability (normal_form_typing T) m.
Proof.
  induction T; intros mm; cbn [normal_form_typing merge_mutability].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite Dev__merge_merge. reflexivity.
  - rewrite IHT1. rewrite IHT2. reflexivity.
  - reflexivity.
Qed.

Lemma Dev__nf_idem : forall (T : typ),
  normal_form_typing (normal_form_typing T) = normal_form_typing T.
Proof.
  induction T.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - change (typ_arrow (normal_form_typing (normal_form_typing T1))
                      (normal_form_typing (normal_form_typing T2))
            = typ_arrow (normal_form_typing T1) (normal_form_typing T2)).
    rewrite IHT1. rewrite IHT2. reflexivity.
  - change (typ_all (normal_form_typing (normal_form_typing T1))
                    (normal_form_typing (normal_form_typing T2))
            = typ_all (normal_form_typing T1) (normal_form_typing T2)).
    rewrite IHT1. rewrite IHT2. reflexivity.
  - change (typ_box (normal_form_typing (normal_form_typing T))
            = typ_box (normal_form_typing T)).
    rewrite IHT. reflexivity.
  - rewrite Dev__nf_mut. rewrite Dev__nf_merge. rewrite IHT. reflexivity.
  - change (typ_int (normal_form_typing (normal_form_typing T1))
                    (normal_form_typing (normal_form_typing T2))
            = typ_int (normal_form_typing T1) (normal_form_typing T2)).
    rewrite IHT1. rewrite IHT2. reflexivity.
  - change (typ_record a (normal_form_typing (normal_form_typing T))
            = typ_record a (normal_form_typing T)).
    rewrite IHT. reflexivity.
Qed.

Lemma Dev__nf_open_tt : forall K (Y : atom) (T : typ),
  normal_form_typing (open_tt_rec K (typ_fvar Y) T)
  = open_tt_rec K (typ_fvar Y) (normal_form_typing T).
Proof.
  intros K Y T. revert K. induction T; intros K.
  - cbn [open_tt_rec normal_form_typing merge_mutability]. reflexivity.
  - cbn [open_tt_rec normal_form_typing merge_mutability]. destruct (K == n); reflexivity.
  - cbn [open_tt_rec normal_form_typing merge_mutability]. reflexivity.
  - cbn [open_tt_rec]. rewrite Dev__nf_arrow. rewrite Dev__nf_arrow. cbn [open_tt_rec].
    rewrite (IHT1 K). rewrite (IHT2 K). reflexivity.
  - cbn [open_tt_rec]. rewrite Dev__nf_all. rewrite Dev__nf_all. cbn [open_tt_rec].
    rewrite (IHT1 K). rewrite (IHT2 (S K)). reflexivity.
  - cbn [open_tt_rec]. rewrite Dev__nf_box. rewrite Dev__nf_box. cbn [open_tt_rec].
    rewrite (IHT K). reflexivity.
  - cbn [open_tt_rec]. rewrite Dev__nf_mut. rewrite Dev__nf_mut. rewrite Dev__open_tt_merge.
    rewrite (IHT K). reflexivity.
  - cbn [open_tt_rec]. rewrite Dev__nf_int. rewrite Dev__nf_int. cbn [open_tt_rec].
    rewrite (IHT1 K). rewrite (IHT2 K). reflexivity.
  - cbn [open_tt_rec]. rewrite Dev__nf_record. rewrite Dev__nf_record. cbn [open_tt_rec].
    rewrite (IHT K). reflexivity.
Qed.

Lemma Dev__wf_typ_nf_gen : forall (E : env) T,
  wf_typ E T ->
  forall (E' : env), Dev__same_kinds E E' -> wf_typ E' (normal_form_typing T).
Proof.
  intros E T H. induction H; intros E' Hsk.
  - rewrite Dev__nf_top. constructor.
  - rewrite Dev__nf_fvar. destruct (proj1 (Hsk X) (ex_intro _ U H)) as [U' HU'].
    apply (wf_typ_var U' E' X). assumption.
  - rewrite Dev__nf_arrow. constructor; auto.
  - rewrite Dev__nf_all. apply wf_typ_all with (L := L).
    + apply IHwf_typ. assumption.
    + intros X HX.
      specialize (H1 X HX (X ~ bind_sub (normal_form_typing T1) ++ E')).
      assert (Heq : open_tt (normal_form_typing T2) X = normal_form_typing (open_tt T2 X)).
      { symmetry. apply (Dev__nf_open_tt 0 X T2). }
      rewrite Heq. apply H1. apply Dev__same_kinds_cons_sub_any. assumption.
  - rewrite Dev__nf_box. constructor. apply IHwf_typ. assumption.
  - rewrite Dev__nf_mut. apply Dev__merge_wf. apply IHwf_typ. assumption.
  - rewrite Dev__nf_int. constructor; auto.
  - rewrite Dev__nf_record. constructor. apply IHwf_typ. assumption.
Qed.

Lemma Dev__wf_typ_nf : forall (E : env) T,
  wf_typ E T -> wf_typ E (normal_form_typing T).
Proof. intros. apply (Dev__wf_typ_nf_gen _ _ H E). apply Dev__same_kinds_refl. Qed.

(* ---------------------------------------------------------------- *)
(* Reflexivity of subtyping and normal-form conversion              *)
(* ---------------------------------------------------------------- *)

Lemma Dev__sub_refl : forall (E : env) T,
  wf_env E -> wf_typ E T -> sub E T T.
Proof.
  intros E T HE H. revert HE.
  induction H as [ E0
                 | U E0 X Hb
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | L E0 T1 T2 H1 IH1 H0 IH0
                 | E0 T H1 IH1
                 | E0 T H1 IH1
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 H1 IH1 ]; intros HE.
  - apply sub_top; [assumption | constructor].
  - apply sub_refl_tvar; [assumption | eapply wf_typ_var; eauto].
  - apply sub_arrow; auto.
  - apply (sub_all (L `union` dom E0) E0 T1 T2 T1 T2).
    + apply IH1; assumption.
    + intros X HX.
      apply (IH0 X).
      * apply notin_union_1 in HX. assumption.
      * apply (wf_env_sub E0 X T1); auto.
  - apply sub_box; [apply IH1; assumption | apply IH1; assumption].
  - apply sub_readonly; apply IH1; assumption.
  - apply sub_inter.
    + apply (sub_inter_left E0 T1 T2); assumption.
    + apply (sub_inter_right E0 T1 T2); assumption.
  - apply sub_record; [apply IH1; assumption | apply IH1; assumption].
Qed.

Lemma Dev__sub_to_nf : forall (E : env) T,
  wf_env E -> wf_typ E T -> sub E T (normal_form_typing T).
Proof.
  intros. apply (sub_denormalize E T (normal_form_typing T)); auto.
  - apply Dev__wf_typ_nf. assumption.
  - rewrite Dev__nf_idem. apply Dev__sub_refl; auto. apply Dev__wf_typ_nf. assumption.
Qed.

Lemma Dev__sub_of_nf : forall (E : env) T,
  wf_env E -> wf_typ E T -> sub E (normal_form_typing T) T.
Proof.
  intros. apply (sub_denormalize E (normal_form_typing T) T); auto.
  - apply Dev__wf_typ_nf. assumption.
  - rewrite Dev__nf_idem. apply Dev__sub_refl; auto. apply Dev__wf_typ_nf. assumption.
Qed.

(* ---------------------------------------------------------------- *)
(* Arrow-component analysis of subtyping                            *)
(* ---------------------------------------------------------------- *)

Inductive Dev__ArrComp : typ -> typ -> typ -> Prop :=
  | Dev__arr_comp_arrow : forall A B, Dev__ArrComp (typ_arrow A B) A B
  | Dev__arr_comp_fvar : forall X A B, Dev__ArrComp (typ_fvar X) A B
  | Dev__arr_comp_rofvar : forall m X A B, Dev__ArrComp (typ_mut m (typ_fvar X)) A B
  | Dev__arr_comp_int_l : forall X Y A B, Dev__ArrComp X A B -> Dev__ArrComp (typ_int X Y) A B
  | Dev__arr_comp_int_r : forall X Y A B, Dev__ArrComp Y A B -> Dev__ArrComp (typ_int X Y) A B
  | Dev__arr_comp_mut : forall m X A B, Dev__ArrComp X A B -> Dev__ArrComp (typ_mut m X) A B.

Lemma Dev__ArrComp_merge_fwd : forall (T : typ) m A B,
  Dev__ArrComp T A B -> Dev__ArrComp (merge_mutability T m) A B.
Proof.
  intros T m A B H. induction H.
  - rewrite Dev__merge_arrow. apply Dev__arr_comp_arrow.
  - rewrite Dev__merge_fvar. apply Dev__arr_comp_rofvar.
  - rewrite Dev__merge_mut. apply Dev__arr_comp_rofvar.
  - rewrite Dev__merge_int. apply Dev__arr_comp_int_l. assumption.
  - rewrite Dev__merge_int. apply Dev__arr_comp_int_r. assumption.
  - rewrite Dev__merge_mut. apply Dev__arr_comp_mut. assumption.
Qed.

Lemma Dev__ArrComp_merge_rev : forall (E : env) T m A B,
  wf_env E -> wf_typ E T -> wf_typ E A -> wf_typ E B ->
  Dev__ArrComp (merge_mutability T m) A B ->
  exists A' B', wf_typ E A' /\ wf_typ E B' /\ Dev__ArrComp T A' B' /\ sub E A A' /\ sub E B' B.
Proof.
  intros E T. induction T; intros mm A B HE HT HA HB Hac.
  - rewrite Dev__merge_top in Hac. inversion Hac.
  - rewrite Dev__merge_bvar in Hac. inversion Hac; subst; try discriminate; try (inversion H3).
  - rewrite Dev__merge_fvar in Hac. exists A, B. repeat split; auto; try apply Dev__arr_comp_fvar; try (apply Dev__sub_refl; assumption).
  - rewrite Dev__merge_arrow in Hac. exists A, B. repeat split; auto; try exact Hac; try (apply Dev__sub_refl; assumption).
  - rewrite Dev__merge_all in Hac. inversion Hac.
  - rewrite Dev__merge_box in Hac. inversion Hac; subst; try discriminate; try (inversion H3).
  - rewrite Dev__merge_mut in Hac. exists A, B. repeat split; auto; try exact Hac; try (apply Dev__sub_refl; assumption).
  - rewrite Dev__merge_int in Hac. inversion Hac; subst.
    + destruct (IHT1 mm A B HE (proj1 (Dev__wf_typ_inv_inter _ _ _ HT)) HA HB H3)
        as [A' [B' [HA' [HB' [Hac' [HA'' HB'']]]]]].
      exists A', B'. repeat split; auto. apply Dev__arr_comp_int_l. assumption.
    + destruct (IHT2 mm A B HE (proj2 (Dev__wf_typ_inv_inter _ _ _ HT)) HA HB H3)
        as [A' [B' [HA' [HB' [Hac' [HA'' HB'']]]]]].
      exists A', B'. repeat split; auto. apply Dev__arr_comp_int_r. assumption.
  - rewrite Dev__merge_record in Hac. inversion Hac; subst; try discriminate; try (inversion H3).
Qed.

Lemma Dev__ArrComp_pair_lift : forall (E : env) T A B,
  wf_env E -> wf_typ E T -> wf_typ E A -> wf_typ E B ->
  Dev__ArrComp T A B ->
  exists A0 B0, wf_typ E A0 /\ wf_typ E B0 /\
    Dev__ArrComp (normal_form_typing T) A0 B0 /\ sub E A A0 /\ sub E B0 B.
Proof.
  intros E T. induction T; intros A B HE HT HA HB Hac.
  - inversion Hac.
  - inversion Hac; subst; try (inversion H3).
  - rewrite Dev__nf_fvar. exists A, B.
    repeat split; auto; try apply Dev__arr_comp_fvar; try (apply Dev__sub_refl; assumption).
  - inversion Hac; subst. rewrite Dev__nf_arrow. exists (normal_form_typing A), (normal_form_typing B).
    repeat split; auto.
    + apply Dev__wf_typ_nf. apply (proj1 (Dev__wf_typ_inv_arrow _ _ _ HT)).
    + apply Dev__wf_typ_nf. apply (proj2 (Dev__wf_typ_inv_arrow _ _ _ HT)).
    + apply Dev__arr_comp_arrow.
    + apply Dev__sub_to_nf; auto.
    + apply Dev__sub_of_nf; auto.
  - inversion Hac.
  - inversion Hac.
  - inversion Hac; subst.
    + rewrite Dev__nf_mut. rewrite Dev__nf_fvar. rewrite Dev__merge_fvar. exists A, B.
      repeat split; auto; try apply Dev__arr_comp_rofvar; try (apply Dev__sub_refl; assumption).
    + destruct (IHT A B HE (Dev__wf_typ_inv_readonly _ _ _ HT) HA HB H3)
        as [A0 [B0 [HA0 [HB0 [Hac0 [HA' HB']]]]]].
      rewrite Dev__nf_mut. exists A0, B0.
      repeat split; auto.
      * apply Dev__ArrComp_merge_fwd with (m := m). assumption.
  - inversion Hac; subst.
    + destruct (IHT1 A B HE (proj1 (Dev__wf_typ_inv_inter _ _ _ HT)) HA HB H3)
        as [A0 [B0 [HA0 [HB0 [Hac0 [HA' HB']]]]]].
      rewrite Dev__nf_int. exists A0, B0.
      repeat split; auto.
      * apply Dev__arr_comp_int_l. assumption.
    + destruct (IHT2 A B HE (proj2 (Dev__wf_typ_inv_inter _ _ _ HT)) HA HB H3)
        as [A0 [B0 [HA0 [HB0 [Hac0 [HA' HB']]]]]].
      rewrite Dev__nf_int. exists A0, B0.
      repeat split; auto.
      * apply Dev__arr_comp_int_r. assumption.
  - inversion Hac.
Qed.

Lemma Dev__ArrComp_src_lift : forall (E : env) T A B,
  wf_env E -> wf_typ E T -> wf_typ E A -> wf_typ E B ->
  Dev__ArrComp (normal_form_typing T) A B ->
  exists A' B', wf_typ E A' /\ wf_typ E B' /\
    Dev__ArrComp T A' B' /\ sub E A A' /\ sub E B' B.
Proof.
  intros E T. induction T; intros A B HE HT HA HB Hac.
  - rewrite Dev__nf_top in Hac. inversion Hac.
  - rewrite Dev__nf_bvar in Hac. inversion Hac; subst; try (inversion H3).
  - rewrite Dev__nf_fvar in Hac. exists A, B.
    repeat split; auto; try apply Dev__arr_comp_fvar; try (apply Dev__sub_refl; assumption).
  - rewrite Dev__nf_arrow in Hac. inversion Hac; subst. exists T1, T2.
    split.
    + apply (proj1 (Dev__wf_typ_inv_arrow _ _ _ HT)).
    + split.
      * apply (proj2 (Dev__wf_typ_inv_arrow _ _ _ HT)).
      * split.
        -- apply Dev__arr_comp_arrow.
        -- split.
           ++ apply Dev__sub_of_nf; auto. apply (proj1 (Dev__wf_typ_inv_arrow _ _ _ HT)).
           ++ apply Dev__sub_to_nf; auto. apply (proj2 (Dev__wf_typ_inv_arrow _ _ _ HT)).
  - rewrite Dev__nf_all in Hac. inversion Hac.
  - rewrite Dev__nf_box in Hac. inversion Hac.
  - rewrite Dev__nf_mut in Hac.
    destruct (Dev__ArrComp_merge_rev E (normal_form_typing T) m A B HE (Dev__wf_typ_nf _ _ (Dev__wf_typ_inv_readonly _ _ _ HT)) HA HB Hac)
      as [A1 [B1 [HA1 [HB1 [Hac1 [HA1' HB1']]]]]].
    destruct (IHT A1 B1 HE (Dev__wf_typ_inv_readonly _ _ _ HT) HA1 HB1 Hac1)
      as [A' [B' [HA' [HB' [Hac' [HA'' HB'']]]]]].
    exists A', B'. repeat split; auto.
    + apply Dev__arr_comp_mut. assumption.
    + eapply sub_trans; eauto.
    + eapply sub_trans; eauto.
  - rewrite Dev__nf_int in Hac. inversion Hac; subst.
    + destruct (IHT1 A B HE (proj1 (Dev__wf_typ_inv_inter _ _ _ HT)) HA HB H3)
        as [A' [B' [HA' [HB' [Hac' [HA'' HB'']]]]]].
      exists A', B'. repeat split; auto. apply Dev__arr_comp_int_l. assumption.
    + destruct (IHT2 A B HE (proj2 (Dev__wf_typ_inv_inter _ _ _ HT)) HA HB H3)
        as [A' [B' [HA' [HB' [Hac' [HA'' HB'']]]]]].
      exists A', B'. repeat split; auto. apply Dev__arr_comp_int_r. assumption.
  - rewrite Dev__nf_record in Hac. inversion Hac; subst; try (inversion H3).
Qed.

Lemma Dev__sub_arrcomp : forall (E : env) S T,
  wf_env E -> wf_typ E S -> sub E S T ->
  forall A B, wf_typ E A -> wf_typ E B -> Dev__ArrComp T A B ->
  exists A' B', wf_typ E A' /\ wf_typ E B' /\
    Dev__ArrComp S A' B' /\ sub E A A' /\ sub E B' B.
Proof.
  intros E S T HE HS Hsub.
  induction Hsub as [ E0 S0 HE0 HS0
                 | E0 X HE0 HS0
                 | U E0 T0 X Hb Hsub IHsub
                 | E0 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E0 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 T1 T2 HE0 HS1 HS2
                 | E0 T1 T2 HE0 HS1 HS2
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1
                 | E0 T1 T2 HS1 HS2 Hsub IHsub ];
  intros A B HA HB Hac.
  - (* top *) inversion Hac.
  - (* refl tvar *) exists A, B. repeat split; auto; try apply Dev__arr_comp_fvar; try (apply Dev__sub_refl; assumption).
  - (* trans tvar *) exists A, B. repeat split; auto; try apply Dev__arr_comp_fvar; try (apply Dev__sub_refl; assumption).
  - (* arrow *) inversion Hac; subst. exists S1, S2.
    assert (HS1 : wf_typ E0 S1) by apply (proj1 (Dev__wf_typ_inv_arrow _ _ _ HS)).
    assert (HS2 : wf_typ E0 S2) by apply (proj2 (Dev__wf_typ_inv_arrow _ _ _ HS)).
    repeat split; auto; try apply Dev__arr_comp_arrow.
  - (* all *) inversion Hac.
  - (* box *) inversion Hac.
  - (* readonly *) inversion Hac; subst.
    + assert (Hacf : Dev__ArrComp X A B) by apply Dev__arr_comp_fvar.
      destruct (IH1 HE (Dev__wf_typ_inv_readonly _ _ _ HS) A B HA HB Hacf)
        as [A' [B' [HA' [HB' [Hac' [HA'' HB'']]]]]].
      exists A', B'. repeat split; auto. apply Dev__arr_comp_mut. assumption.
    + destruct (IH1 HE (Dev__wf_typ_inv_readonly _ _ _ HS) A B HA HB H4)
        as [A' [B' [HA' [HB' [Hac' [HA'' HB'']]]]]].
      exists A', B'. repeat split; auto. apply Dev__arr_comp_mut. assumption.
  - (* readonly mutable *) inversion Hac; subst.
    + assert (Hacf : Dev__ArrComp X A B) by (apply Dev__arr_comp_fvar).
      destruct (IH1 HE HS A B HA HB Hacf)
        as [A' [B' [HA' [HB' [Hac' [HA'' HB'']]]]]].
      exists A', B'. repeat split; auto.
    + destruct (IH1 HE HS A B HA HB H4)
        as [A' [B' [HA' [HB' [Hac' [HA'' HB'']]]]]].
      exists A', B'. repeat split; auto.
  - (* trans *) assert (HT2 : wf_typ E0 T2).
    { apply (proj1 (Dev__sub_wf_both E0 T1 T2 H1)); assumption. }
    destruct (IH2 HE HT2 A B HA HB Hac) as [A1 [B1 [HA1 [HB1 [Hac1 [HA1' HB1']]]]]].
    destruct (IH1 HE HS A1 B1 HA1 HB1 Hac1) as [A2 [B2 [HA2 [HB2 [Hac2 [HA2' HB2']]]]]].
    exists A2, B2. repeat split; auto.
    + eapply sub_trans; eauto.
    + eapply sub_trans; eauto.
  - (* inter left *) exists A, B. repeat split; auto.
    + apply Dev__arr_comp_int_l. assumption.
    + apply Dev__sub_refl; assumption.
    + apply Dev__sub_refl; assumption.
  - (* inter right *) exists A, B. repeat split; auto.
    + apply Dev__arr_comp_int_r. assumption.
    + apply Dev__sub_refl; assumption.
    + apply Dev__sub_refl; assumption.
  - (* inter *) inversion Hac; subst.
    + destruct (IH1 HE HS A B HA HB H5) as [A' [B' [HA' [HB' [Hac' [HA'' HB'']]]]]].
      exists A', B'. repeat split; auto.
    + destruct (IH2 HE HS A B HA HB H5) as [A' [B' [HA' [HB' [Hac' [HA'' HB'']]]]]].
      exists A', B'. repeat split; auto.
  - (* record *) inversion Hac.
  - (* readonly record *) inversion Hac; subst; try (inversion H4).
  - (* denormalize *)
    assert (Hnf : wf_typ E0 (normal_form_typing T1)) by (apply Dev__wf_typ_nf; assumption).
    destruct (Dev__ArrComp_pair_lift E0 T2 A B HE HS2 HA HB Hac)
      as [A0 [B0 [HA0 [HB0 [Hac0 [HA0' HB0']]]]]].
    destruct (IHsub HE Hnf A0 B0 HA0 HB0 Hac0)
      as [A1 [B1 [HA1 [HB1 [Hac1 [HA1' HB1']]]]]].
    destruct (Dev__ArrComp_src_lift E0 T1 A1 B1 HE HS1 HA1 HB1 Hac1)
      as [A' [B' [HA' [HB' [Hac' [HA'' HB'']]]]]].
    exists A', B'. repeat split; auto.
    + eapply sub_trans; [exact HA0' | eapply sub_trans; [exact HA1' | exact HA'']].
    + eapply sub_trans; [exact HB'' | eapply sub_trans; [exact HB1' | exact HB0']].
Qed.




(* ---------------------------------------------------------------- *)
(* Inclusion/weakening for wf_typ and sub                           *)
(* ---------------------------------------------------------------- *)

Lemma MyWork__wf_typ_incl : forall (E1 : env) T,
  wf_typ E1 T ->
  forall (E2 : env),
    (forall X U, binds X (bind_sub U) E1 -> binds X (bind_sub U) E2) ->
    wf_typ E2 T.
Proof.
  intros E1 T H. induction H; intros E2 Hincl.
  - constructor.
  - apply (wf_typ_var U E2 X). apply Hincl. assumption.
  - constructor; auto.
  - apply wf_typ_all with (L := L); auto.
    intros X HX. apply (H1 X HX (X ~ bind_sub T1 ++ E2)).
    intros Y U Hb. destruct Hb as [Heq | Hin].
    + injection Heq as HY HU. subst. left. reflexivity.
    + right. apply Hincl. assumption.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma MyWork__wf_typ_incl_all : forall (E1 E2 : env) T,
  (forall x b, binds x b E1 -> binds x b E2) ->
  wf_typ E1 T -> wf_typ E2 T.
Proof.
  intros. eapply MyWork__wf_typ_incl; eauto.
Qed.


(* ---------------------------------------------------------------- *)
(* Box-component analysis of subtyping                              *)
(* ---------------------------------------------------------------- *)

Inductive MyWork__BoxComp : typ -> typ -> Prop :=
  | MyWork__box_comp_box : forall A, MyWork__BoxComp (typ_box A) A
  | MyWork__box_comp_fvar : forall X A, MyWork__BoxComp (typ_fvar X) A
  | MyWork__box_comp_rofvar : forall m X A, MyWork__BoxComp (typ_mut m (typ_fvar X)) A
  | MyWork__box_comp_int_l : forall X Y A, MyWork__BoxComp X A -> MyWork__BoxComp (typ_int X Y) A
  | MyWork__box_comp_int_r : forall X Y A, MyWork__BoxComp Y A -> MyWork__BoxComp (typ_int X Y) A
  | MyWork__box_comp_mut : forall m X A, MyWork__BoxComp X A -> MyWork__BoxComp (typ_mut m X) A.

Lemma MyWork__BoxComp_merge_fwd : forall (T : typ) m A,
  MyWork__BoxComp T A -> MyWork__BoxComp (merge_mutability T m) A.
Proof.
  intros T m A H. induction H.
  - rewrite Dev__merge_box. apply MyWork__box_comp_mut. apply MyWork__box_comp_box.
  - rewrite Dev__merge_fvar. apply MyWork__box_comp_rofvar.
  - rewrite Dev__merge_mut. apply MyWork__box_comp_rofvar.
  - rewrite Dev__merge_int. apply MyWork__box_comp_int_l. assumption.
  - rewrite Dev__merge_int. apply MyWork__box_comp_int_r. assumption.
  - rewrite Dev__merge_mut. apply MyWork__box_comp_mut. assumption.
Qed.

Lemma MyWork__BoxComp_merge_rev : forall (E : env) T m A,
  wf_env E -> wf_typ E T -> wf_typ E A ->
  MyWork__BoxComp (merge_mutability T m) A ->
  exists A', wf_typ E A' /\ MyWork__BoxComp T A' /\ sub E A A' /\ sub E A' A.
Proof.
  intros E T. induction T; intros mm A HE HT HA Hac.
  - rewrite Dev__merge_top in Hac. inversion Hac.
  - rewrite Dev__merge_bvar in Hac. inversion Hac; subst; try (inversion H2); try (inversion H3); try (inversion H4).
  - rewrite Dev__merge_fvar in Hac. exists A. repeat split; auto; try apply MyWork__box_comp_fvar; try (apply Dev__sub_refl; assumption).
  - rewrite Dev__merge_arrow in Hac. inversion Hac.
  - rewrite Dev__merge_all in Hac. inversion Hac.
  - rewrite Dev__merge_box in Hac. inversion Hac; subst; try (inversion H3); subst.
    exists A. repeat split; auto; try apply MyWork__box_comp_box; try (apply Dev__sub_refl; assumption).
  - rewrite Dev__merge_mut in Hac. exists A. repeat split; auto; try assumption; try (apply Dev__sub_refl; assumption).
  - rewrite Dev__merge_int in Hac. inversion Hac; subst.
    + destruct (IHT1 mm A HE (proj1 (Dev__wf_typ_inv_inter _ _ _ HT)) HA H2)
        as [A' [HA' [Hac' [HA'' HA''']]]].
      exists A'. repeat split; auto. apply MyWork__box_comp_int_l. assumption.
    + destruct (IHT2 mm A HE (proj2 (Dev__wf_typ_inv_inter _ _ _ HT)) HA H2)
        as [A' [HA' [Hac' [HA'' HA''']]]].
      exists A'. repeat split; auto. apply MyWork__box_comp_int_r. assumption.
  - rewrite Dev__merge_record in Hac. inversion Hac; subst; try (inversion H2); try (inversion H3); try (inversion H4).
Qed.


Lemma MyWork__to_nf_lem : forall (E : env) T, wf_env E -> wf_typ E T -> sub E T (normal_form_typing T).
Proof. intros. apply Dev__sub_to_nf; assumption. Qed.
Lemma MyWork__of_nf_lem : forall (E : env) T, wf_env E -> wf_typ E T -> sub E (normal_form_typing T) T.
Proof. intros. apply Dev__sub_of_nf; assumption. Qed.

Lemma MyWork__BoxComp_pair_lift : forall (E : env) T A,
  wf_env E -> wf_typ E T -> wf_typ E A -> MyWork__BoxComp T A ->
  exists A0, wf_typ E A0 /\ MyWork__BoxComp (normal_form_typing T) A0 /\
    sub E A A0 /\ sub E A0 A.
Proof.
  intros E T. induction T; intros A HE HT HA Hac.
  - inversion Hac.
  - inversion Hac; subst; try (inversion H2); try (inversion H3).
  - rewrite Dev__nf_fvar. exists A. repeat split; auto; try apply MyWork__box_comp_fvar; try (apply Dev__sub_refl; assumption).
  - inversion Hac.
  - inversion Hac.
  - inversion Hac; subst; try (inversion H2).
    rewrite Dev__nf_box. exists (normal_form_typing A).
    repeat split; auto; try apply MyWork__box_comp_box.
    + apply Dev__wf_typ_nf. apply (Dev__wf_typ_inv_box _ _ HT).
    + apply MyWork__to_nf_lem; auto.
    + apply MyWork__of_nf_lem; auto.
  - inversion Hac; subst.
    + rewrite Dev__nf_mut. rewrite Dev__nf_fvar. rewrite Dev__merge_fvar. exists A.
      repeat split; auto; try apply MyWork__box_comp_rofvar; try (apply Dev__sub_refl; assumption).
    + destruct (IHT A HE (Dev__wf_typ_inv_readonly _ _ _ HT) HA H2)
        as [A0 [HA0 [Hac0 [HA0' HA0'']]]].
      rewrite Dev__nf_mut. exists A0. repeat split; auto.
      apply MyWork__BoxComp_merge_fwd with (m := m). assumption.
  - inversion Hac; subst.
    + destruct (IHT1 A HE (proj1 (Dev__wf_typ_inv_inter _ _ _ HT)) HA H2)
        as [A0 [HA0 [Hac0 [HA0' HA0'']]]].
      rewrite Dev__nf_int. exists A0. repeat split; auto. apply MyWork__box_comp_int_l. assumption.
    + destruct (IHT2 A HE (proj2 (Dev__wf_typ_inv_inter _ _ _ HT)) HA H2)
        as [A0 [HA0 [Hac0 [HA0' HA0'']]]].
      rewrite Dev__nf_int. exists A0. repeat split; auto. apply MyWork__box_comp_int_r. assumption.
  - inversion Hac.
Qed.

Lemma MyWork__BoxComp_src_lift : forall (E : env) T A,
  wf_env E -> wf_typ E T -> wf_typ E A -> MyWork__BoxComp (normal_form_typing T) A ->
  exists A', wf_typ E A' /\ MyWork__BoxComp T A' /\ sub E A A' /\ sub E A' A.
Proof.
  intros E T. induction T; intros A HE HT HA Hac.
  - rewrite Dev__nf_top in Hac. inversion Hac.
  - rewrite Dev__nf_bvar in Hac. inversion Hac; subst; try (inversion H2); try (inversion H3); try (inversion H4).
  - rewrite Dev__nf_fvar in Hac. exists A. repeat split; auto; try apply MyWork__box_comp_fvar; try (apply Dev__sub_refl; assumption).
  - rewrite Dev__nf_arrow in Hac. inversion Hac.
  - rewrite Dev__nf_all in Hac. inversion Hac.
  - rewrite Dev__nf_box in Hac. inversion Hac; subst; try (inversion H2); subst.
    exists T. split.
    + apply (Dev__wf_typ_inv_box _ _ HT).
    + split.
      * apply MyWork__box_comp_box.
      * split.
        -- apply MyWork__of_nf_lem; auto. apply (Dev__wf_typ_inv_box _ _ HT).
        -- apply MyWork__to_nf_lem; auto. apply (Dev__wf_typ_inv_box _ _ HT).
  - rewrite Dev__nf_mut in Hac.
    destruct (MyWork__BoxComp_merge_rev E (normal_form_typing T) m A HE
                (Dev__wf_typ_nf _ _ (Dev__wf_typ_inv_readonly _ _ _ HT)) HA Hac)
      as [A1 [HA1 [Hac1 [HA1' HA1'']]]].
    destruct (IHT A1 HE (Dev__wf_typ_inv_readonly _ _ _ HT) HA1 Hac1)
      as [A' [HA' [Hac' [HA'' HA''']]]].
    exists A'. repeat split; auto.
    + apply MyWork__box_comp_mut. assumption.
    + eapply sub_trans; eauto.
    + eapply sub_trans; eauto.
  - rewrite Dev__nf_int in Hac. inversion Hac; subst.
    + destruct (IHT1 A HE (proj1 (Dev__wf_typ_inv_inter _ _ _ HT)) HA H2)
        as [A' [HA' [Hac' [HA'' HA''']]]].
      exists A'. repeat split; auto. apply MyWork__box_comp_int_l. assumption.
    + destruct (IHT2 A HE (proj2 (Dev__wf_typ_inv_inter _ _ _ HT)) HA H2)
        as [A' [HA' [Hac' [HA'' HA''']]]].
      exists A'. repeat split; auto. apply MyWork__box_comp_int_r. assumption.
  - rewrite Dev__nf_record in Hac. inversion Hac; subst; try (inversion H2); try (inversion H3).
Qed.


Lemma MyWork__BoxComp_mut_inv : forall m T A, MyWork__BoxComp (typ_mut m T) A -> MyWork__BoxComp T A.
Proof. intros. inversion H; subst. - apply MyWork__box_comp_fvar. - assumption. Qed.

Lemma MyWork__BoxComp_int_inv : forall X Y A, MyWork__BoxComp (typ_int X Y) A -> MyWork__BoxComp X A \/ MyWork__BoxComp Y A.
Proof. intros. inversion H; subst. - left; assumption. - right; assumption. Qed.

Lemma MyWork__BoxComp_box_inv : forall A B, MyWork__BoxComp (typ_box A) B -> B = A.
Proof. intros. inversion H; subst. reflexivity. Qed.

Lemma MyWork__sub_boxcomp : forall (E : env) S T,
  wf_env E -> wf_typ E S -> sub E S T ->
  forall A, wf_typ E A -> MyWork__BoxComp T A ->
  exists A', wf_typ E A' /\ MyWork__BoxComp S A' /\ sub E A A' /\ sub E A' A.
Proof.
  intros E S T HE HS Hsub.
  induction Hsub as [ E0 S0 HE0 HS0
                 | E0 X HE0 HS0
                 | U E0 T0 X Hb Hsub IHsub
                 | E0 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E0 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 T1 T2 HEi1 HSi1 HSi2
                 | E0 T1 T2 HEi2 HSi2b HSi2c
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1
                 | E0 T1 T2 HSd1 HSd2 Hsub IHsub ];
  intros A HA Hac.
  - inversion Hac.
  - exists A. repeat split; auto; try apply MyWork__box_comp_fvar; try (apply Dev__sub_refl; assumption).
  - exists A. repeat split; auto; try apply MyWork__box_comp_fvar; try (apply Dev__sub_refl; assumption).
  - inversion Hac.
  - inversion Hac.
  - inversion Hac; subst. exists T1.
    split; [apply (Dev__wf_typ_inv_box _ _ HS)|].
    split.
    + apply MyWork__box_comp_box.
    + split.
      * exact H2.
      * exact H1.
  - assert (Hac2 := MyWork__BoxComp_mut_inv _ _ _ Hac).
    destruct (IH1 HE (Dev__wf_typ_inv_readonly _ _ _ HS) A HA Hac2)
      as [A' [HA' [Hac' [HA'' HA''']]]].
    exists A'. repeat split; auto. apply MyWork__box_comp_mut. assumption.
  - assert (Hac2 := MyWork__BoxComp_mut_inv _ _ _ Hac).
    destruct (IH1 HE HS A HA Hac2) as [A' [HA' [Hac' [HA'' HA''']]]].
    exists A'. repeat split; auto.
  - assert (HT2 : wf_typ E0 T2).
    { apply (proj1 (Dev__sub_wf_both E0 T1 T2 H1)); assumption. }
    destruct (IH2 HE HT2 A HA Hac) as [A1 [HA1 [Hac1 [HA1' HA1'']]]].
    destruct (IH1 HE HS A1 HA1 Hac1) as [A2 [HA2 [Hac2 [HA2' HA2'']]]].
    exists A2. repeat split; auto.
    + eapply sub_trans; eauto.
    + eapply sub_trans; eauto.
  - exists A. repeat split; auto.
    + apply MyWork__box_comp_int_l. assumption.
    + apply Dev__sub_refl; assumption.
    + apply Dev__sub_refl; assumption.
  - exists A. repeat split; auto.
    + apply MyWork__box_comp_int_r. assumption.
    + apply Dev__sub_refl; assumption.
    + apply Dev__sub_refl; assumption.
  - destruct (MyWork__BoxComp_int_inv _ _ _ Hac) as [Hac2 | Hac2].
    + destruct (IH1 HE HS A HA Hac2) as [A' [HA' [Hac' [HA'' HA''']]]].
      exists A'. repeat split; auto.
    + destruct (IH2 HE HS A HA Hac2) as [A' [HA' [Hac' [HA'' HA''']]]].
      exists A'. repeat split; auto.
  - inversion Hac.
  - inversion Hac; subst; try (inversion H2); try (inversion H3); try (inversion H4).
  - destruct (MyWork__BoxComp_pair_lift E0 T2 A HE HSd2 HA Hac) as [A0 [HA0 [Hac0 [HA0' HA0'']]]].
    assert (Hnf : wf_typ E0 (normal_form_typing T1)) by (apply Dev__wf_typ_nf; assumption).
    destruct (IHsub HE Hnf A0 HA0 Hac0) as [A1 [HA1 [Hac1 [HA1' HA1'']]]].
    destruct (MyWork__BoxComp_src_lift E0 T1 A1 HE HSd1 HA1 Hac1) as [A' [HA' [Hac' [HA'' HA''']]]].
    exists A'. repeat split; auto.
    + eapply sub_trans; [exact HA0' | eapply sub_trans; [exact HA1' | exact HA'']].
    + eapply sub_trans; [exact HA''' | eapply sub_trans; [exact HA1'' | exact HA0'']].
Qed.

Lemma MyWork__sub_box_box : forall (E : env) A B,
  wf_env E -> wf_typ E (typ_box A) -> wf_typ E (typ_box B) ->
  sub E (typ_box A) (typ_box B) -> sub E A B /\ sub E B A.
Proof.
  intros E A B HE HA HB Hsub.
  destruct (MyWork__sub_boxcomp E (typ_box A) (typ_box B) HE HA Hsub B
              (Dev__wf_typ_inv_box _ _ HB) (MyWork__box_comp_box B))
    as [A' [HA' [Hac' [H1 H2]]]].
  assert (Heq : A' = A) by (apply (MyWork__BoxComp_box_inv _ _ Hac')).
  subst A'. split; assumption.
Qed.

Lemma MyWork__ArrComp_arrow_inv : forall A B X Y,
  Dev__ArrComp (typ_arrow A B) X Y -> X = A /\ Y = B.
Proof. intros. inversion H; subst. auto. Qed.

Lemma MyWork__sub_arrow_arrow : forall (E : env) A B C D,
  wf_env E -> wf_typ E (typ_arrow A B) -> wf_typ E (typ_arrow C D) ->
  sub E (typ_arrow A B) (typ_arrow C D) -> sub E C A /\ sub E B D.
Proof.
  intros E A B C D HE HA HB Hsub.
  destruct (Dev__sub_arrcomp E (typ_arrow A B) (typ_arrow C D) HE HA Hsub C D
              (proj1 (Dev__wf_typ_inv_arrow _ _ _ HB)) (proj2 (Dev__wf_typ_inv_arrow _ _ _ HB))
              (Dev__arr_comp_arrow C D))
    as [X [Y [HX [HY [Hac [H1 H2]]]]]].
  destruct (MyWork__ArrComp_arrow_inv _ _ _ _ Hac) as [HXA HYB].
  subst X. subst Y. split; assumption.
Qed.

Lemma MyWork__my_wf_sig_binds : forall (E : env) (R : sig),
  wf_sig E R -> forall l T, Signatures.binds l (bind_sig T) R -> wf_typ E T.
Proof.
  intros E R H.
  induction H as [ E0 HE0 | E0 R0 l0 T0 Hpre IHpre HT Hnotin ]; intros l1 T1 Hb.
  - simpl in Hb. destruct Hb.
  - simpl in Hb. destruct Hb as [Heq | Hin].
    + injection Heq as Hl HT'. subst. assumption.
    + apply (IHpre l1 T1). assumption.
Qed.

Lemma MyWork__typing_ref_inv : forall (E : env) (R : sig) l S,
  typing E R (exp_ref l) S ->
  exists T, Signatures.binds l (bind_sig T) R /\ sub E (typ_box T) S.
Proof.
  intros E R l S H.
  remember (exp_ref l) as e eqn:He.
  revert l He.
  induction H; intros l0 He; try discriminate He.
  - (* typing_sub *) destruct (IHtyping l0 He) as [T0 [Hb Hsub]].
    exists T0. split.
    + assumption.
    + eapply sub_trans; eauto.
  - (* typing_ref *) injection He as Hl. subst l0.
    exists T. split.
    + assumption.
    + apply Dev__sub_refl.
      * assumption.
      * apply wf_typ_box. eapply MyWork__my_wf_sig_binds; eauto.
Qed.

Lemma MyWork__typing_wf_sig : forall (E : env) (R : sig) e T,
  typing E R e T -> wf_sig E R
with MyWork__typing_record_comp_wf_sig : forall (E : env) (R : sig) r T,
  typing_record_comp E R r T -> wf_sig E R.
Proof.
  - intros E R e T H. induction H; eauto.
  - intros E R r T H. induction H; eauto.
Qed.

Lemma MyWork__typing_unbox_ref_inv : forall (E : env) (R : sig) l T,
  typing E R (exp_unbox (exp_ref l)) T ->
  exists T0, Signatures.binds l (bind_sig T0) R /\ sub E T0 T.
Proof.
  intros E R l T H.
  remember (exp_unbox (exp_ref l)) as e0 eqn:He.
  revert l He.
  induction H; intros l0 He; try discriminate He.
  - (* typing_sub *) destruct (IHtyping l0 He) as [T0 [Hb Hsub]].
    exists T0. split.
    + assumption.
    + eapply sub_trans; eauto.
  - (* typing_unbox *) injection He as He1. subst e.
    assert (HE : wf_env E) by (apply (Dev__wf_sig_wf_env E R); apply (MyWork__typing_wf_sig E R _ _ H0)).
    destruct (MyWork__typing_ref_inv _ _ _ _ H0) as [T0 [Hb Hsub]].
    assert (Hws : wf_typ E (typ_box T0)).
    { apply wf_typ_box. apply (MyWork__my_wf_sig_binds E R H l0 T0 Hb). }
    assert (Hwt : wf_typ E (typ_box T)).
    { apply (Dev__sub_wf_target E (typ_box T0) (typ_box T) HE Hws Hsub). }
    destruct (MyWork__sub_box_box E T0 T HE Hws Hwt Hsub) as [H01 H10].
    exists T0. split; assumption.
  - (* typing_unbox_readonly *) injection He as He1. subst e.
    assert (HE : wf_env E) by (apply (Dev__wf_sig_wf_env E R); apply (MyWork__typing_wf_sig E R _ _ H)).
    destruct (MyWork__typing_ref_inv _ _ _ _ H) as [T0 [Hb Hsub]].
    assert (Hws : wf_typ E (typ_box T0)).
    { apply wf_typ_box. apply (MyWork__my_wf_sig_binds E R (MyWork__typing_wf_sig E R _ _ H) l0 T0 Hb). }
    assert (Hwt : wf_typ E (typ_mut mut_readonly (typ_box T))).
    { apply (Dev__sub_wf_target E (typ_box T0) (typ_mut mut_readonly (typ_box T)) HE Hws Hsub). }
    assert (Hwtb : wf_typ E (typ_box T)).
    { apply (Dev__wf_typ_inv_readonly E mut_readonly (typ_box T) Hwt). }
    destruct (MyWork__sub_boxcomp E (typ_box T0) (typ_mut mut_readonly (typ_box T))
                HE Hws Hsub T (Dev__wf_typ_inv_box _ _ Hwtb)
                (MyWork__box_comp_mut mut_readonly (typ_box T) T (MyWork__box_comp_box T)))
      as [A' [HA' [Hac' [H1 H2]]]].
    assert (Heq : A' = T0) by (apply (MyWork__BoxComp_box_inv _ _ Hac')).
    subst A'.
    exists T0. split.
    + assumption.
    + apply (sub_readonly_mutable E T0 T H2).
Qed.
(* ---------------------------------------------------------------- *)
(* Record-field component analysis of subtyping (one direction)    *)
(* ---------------------------------------------------------------- *)

Section RecordComp.

Variable a : atom.

Inductive MyWork__RComp : typ -> typ -> Prop :=
  | MyWork__rc_here : forall A, MyWork__RComp (typ_record a A) A
  | MyWork__rc_fvar : forall X A, MyWork__RComp (typ_fvar X) A
  | MyWork__rc_rofvar : forall m X A, MyWork__RComp (typ_mut m (typ_fvar X)) A
  | MyWork__rc_int_l : forall X Y A, MyWork__RComp X A -> MyWork__RComp (typ_int X Y) A
  | MyWork__rc_int_r : forall X Y A, MyWork__RComp Y A -> MyWork__RComp (typ_int X Y) A
  | MyWork__rc_mut : forall m X A, MyWork__RComp X A -> MyWork__RComp (typ_mut m X) A.

Lemma MyWork__RComp_mut_inv : forall m T A, MyWork__RComp (typ_mut m T) A -> MyWork__RComp T A.
Proof. intros. inversion H; subst. - apply MyWork__rc_fvar. - assumption. Qed.

Lemma MyWork__RComp_int_inv : forall X Y A, MyWork__RComp (typ_int X Y) A -> MyWork__RComp X A \/ MyWork__RComp Y A.
Proof. intros. inversion H; subst. - left; assumption. - right; assumption. Qed.

Lemma MyWork__RComp_record_inv : forall A B, MyWork__RComp (typ_record a A) B -> B = A.
Proof. intros. inversion H; subst. reflexivity. Qed.

Lemma MyWork__RComp_mut_record_inv : forall m a0 T A,
  MyWork__RComp (typ_mut m (typ_record a0 T)) A -> A = T /\ a0 = a.
Proof.
  intros. inversion H; subst; try (inversion H2); try (inversion H3); auto;
  split; reflexivity.
Qed.

Lemma MyWork__RComp_merge_fwd : forall (T : typ) m A,
  MyWork__RComp T A -> MyWork__RComp (merge_mutability T m) A.
Proof.
  intros T m A H. induction H.
  - rewrite Dev__merge_record. apply MyWork__rc_mut. apply MyWork__rc_here.
  - rewrite Dev__merge_fvar. apply MyWork__rc_rofvar.
  - rewrite Dev__merge_mut. apply MyWork__rc_rofvar.
  - rewrite Dev__merge_int. apply MyWork__rc_int_l. assumption.
  - rewrite Dev__merge_int. apply MyWork__rc_int_r. assumption.
  - rewrite Dev__merge_mut. apply MyWork__rc_mut. assumption.
Qed.

Lemma MyWork__RComp_merge_rev : forall (E : env) T m A,
  wf_env E -> wf_typ E T -> wf_typ E A ->
  MyWork__RComp (merge_mutability T m) A ->
  exists A', wf_typ E A' /\ MyWork__RComp T A' /\ sub E A' A.
Proof.
  intros E T. induction T; intros mm A HE HT HA Hac.
  - rewrite Dev__merge_top in Hac. inversion Hac.
  - rewrite Dev__merge_bvar in Hac. inversion Hac; subst; try (inversion H2); try (inversion H3); try (inversion H4).
  - rewrite Dev__merge_fvar in Hac. exists A. repeat split; auto; try apply MyWork__rc_fvar; try (apply Dev__sub_refl; assumption).
  - rewrite Dev__merge_arrow in Hac. inversion Hac.
  - rewrite Dev__merge_all in Hac. inversion Hac.
  - rewrite Dev__merge_box in Hac. inversion Hac; subst; try (inversion H2); try (inversion H3).
  - rewrite Dev__merge_mut in Hac. assert (Hc := MyWork__RComp_mut_inv m T A Hac).
    exists A. repeat split; auto; try assumption; try (apply Dev__sub_refl; assumption).
  - rewrite Dev__merge_int in Hac. inversion Hac; subst.
    + destruct (IHT1 mm A HE (proj1 (Dev__wf_typ_inv_inter _ _ _ HT)) HA H2)
        as [A' [HA' [Hac' HA'']]].
      exists A'. repeat split; auto. apply MyWork__rc_int_l. assumption.
    + destruct (IHT2 mm A HE (proj2 (Dev__wf_typ_inv_inter _ _ _ HT)) HA H2)
        as [A' [HA' [Hac' HA'']]].
      exists A'. repeat split; auto. apply MyWork__rc_int_r. assumption.
  - rewrite Dev__merge_record in Hac. inversion Hac; subst; try (inversion H2); subst.
    exists A. repeat split; auto; try apply MyWork__rc_here; try (apply Dev__sub_refl; assumption).
Qed.

Lemma MyWork__RComp_pair_lift : forall (E : env) T A,
  wf_env E -> wf_typ E T -> wf_typ E A -> MyWork__RComp T A ->
  exists A0, wf_typ E A0 /\ MyWork__RComp (normal_form_typing T) A0 /\ sub E A0 A.
Proof.
  intros E T. induction T; intros A HE HT HA Hac.
  - inversion Hac.
  - inversion Hac; subst; try (inversion H2); try (inversion H3).
  - rewrite Dev__nf_fvar. exists A. repeat split; auto; try apply MyWork__rc_fvar; try (apply Dev__sub_refl; assumption).
  - inversion Hac.
  - inversion Hac.
  - inversion Hac.
  - inversion Hac; subst.
    + rewrite Dev__nf_mut. rewrite Dev__nf_fvar. rewrite Dev__merge_fvar. exists A.
      repeat split; auto; try apply MyWork__rc_rofvar; try (apply Dev__sub_refl; assumption).
    + destruct (IHT A HE (Dev__wf_typ_inv_readonly _ _ _ HT) HA H2)
        as [A0 [HA0 [Hac0 HA0']]].
      rewrite Dev__nf_mut. exists A0. repeat split; auto.
      apply MyWork__RComp_merge_fwd with (m := m). assumption.
  - inversion Hac; subst.
    + destruct (IHT1 A HE (proj1 (Dev__wf_typ_inv_inter _ _ _ HT)) HA H2)
        as [A0 [HA0 [Hac0 HA0']]].
      rewrite Dev__nf_int. exists A0. repeat split; auto. apply MyWork__rc_int_l. assumption.
    + destruct (IHT2 A HE (proj2 (Dev__wf_typ_inv_inter _ _ _ HT)) HA H2)
        as [A0 [HA0 [Hac0 HA0']]].
      rewrite Dev__nf_int. exists A0. repeat split; auto. apply MyWork__rc_int_r. assumption.
  - inversion Hac; subst; try (inversion H2); subst.
    rewrite Dev__nf_record. exists (normal_form_typing A).
    split.
    + apply Dev__wf_typ_nf. apply (Dev__wf_typ_inv_record _ _ _ HT).
    + split.
      * apply MyWork__rc_here.
      * apply (MyWork__of_nf_lem E A HE (Dev__wf_typ_inv_record _ _ _ HT)).
Qed.

Lemma MyWork__RComp_src_lift : forall (E : env) T A,
  wf_env E -> wf_typ E T -> wf_typ E A -> MyWork__RComp (normal_form_typing T) A ->
  exists A', wf_typ E A' /\ MyWork__RComp T A' /\ sub E A' A.
Proof.
  intros E T. induction T; intros A HE HT HA Hac.
  - rewrite Dev__nf_top in Hac. inversion Hac.
  - rewrite Dev__nf_bvar in Hac. inversion Hac; subst; try (inversion H2); try (inversion H3); try (inversion H4).
  - rewrite Dev__nf_fvar in Hac. exists A. repeat split; auto; try apply MyWork__rc_fvar; try (apply Dev__sub_refl; assumption).
  - rewrite Dev__nf_arrow in Hac. inversion Hac.
  - rewrite Dev__nf_all in Hac. inversion Hac.
  - rewrite Dev__nf_box in Hac. inversion Hac; subst; try (inversion H2); try (inversion H3).
  - rewrite Dev__nf_mut in Hac.
    destruct (MyWork__RComp_merge_rev E (normal_form_typing T) m A HE
                (Dev__wf_typ_nf _ _ (Dev__wf_typ_inv_readonly _ _ _ HT)) HA Hac)
      as [A1 [HA1 [Hac1 HA1']]].
    destruct (IHT A1 HE (Dev__wf_typ_inv_readonly _ _ _ HT) HA1 Hac1)
      as [A' [HA' [Hac' HA'']]].
    exists A'. repeat split; auto.
    + apply MyWork__rc_mut. assumption.
    + eapply sub_trans; eauto.
  - rewrite Dev__nf_int in Hac. inversion Hac; subst.
    + destruct (IHT1 A HE (proj1 (Dev__wf_typ_inv_inter _ _ _ HT)) HA H2)
        as [A' [HA' [Hac' HA'']]].
      exists A'. repeat split; auto. apply MyWork__rc_int_l. assumption.
    + destruct (IHT2 A HE (proj2 (Dev__wf_typ_inv_inter _ _ _ HT)) HA H2)
        as [A' [HA' [Hac' HA'']]].
      exists A'. repeat split; auto. apply MyWork__rc_int_r. assumption.
  - rewrite Dev__nf_record in Hac. inversion Hac; subst; try (inversion H2); subst.
    exists T. split.
    + apply (Dev__wf_typ_inv_record _ _ _ HT).
    + split.
      * apply MyWork__rc_here.
      * apply (MyWork__to_nf_lem E T HE (Dev__wf_typ_inv_record _ _ _ HT)).
Qed.

Lemma MyWork__sub_rcomp : forall (E : env) S T,
  wf_env E -> wf_typ E S -> sub E S T ->
  forall A, wf_typ E A -> MyWork__RComp T A ->
  exists A', wf_typ E A' /\ MyWork__RComp S A' /\ sub E A' A.
Proof.
  intros E S T HE HS Hsub.
  induction Hsub as [ E0 S0 HE0 HS0
                 | E0 X HE0 HS0
                 | U E0 T0 X Hb Hsub IHsub
                 | E0 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E0 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 T1 T2 HEi1 HSi1 HSi2
                 | E0 T1 T2 HEi2 HSi2b HSi2c
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 a0 T1 T2 H1 IH1 H2 IH2
                 | E0 a0 T1 T2 H1 IH1
                 | E0 T1 T2 HSd1 HSd2 Hsub IHsub ];
  intros A HA Hac.
  - inversion Hac.
  - exists A. repeat split; auto; try apply MyWork__rc_fvar; try (apply Dev__sub_refl; assumption).
  - exists A. repeat split; auto; try apply MyWork__rc_fvar; try (apply Dev__sub_refl; assumption).
  - inversion Hac.
  - inversion Hac.
  - inversion Hac.
  - assert (Hac2 := MyWork__RComp_mut_inv mut_readonly T2 A Hac).
    destruct (IH1 HE (Dev__wf_typ_inv_readonly _ _ _ HS) A HA Hac2)
      as [A' [HA' [Hac' HA'']]].
    exists A'. repeat split; auto. apply MyWork__rc_mut. assumption.
  - assert (Hac2 := MyWork__RComp_mut_inv mut_readonly T2 A Hac).
    destruct (IH1 HE HS A HA Hac2) as [A' [HA' [Hac' HA'']]].
    exists A'. repeat split; auto.
  - assert (HT2 : wf_typ E0 T2).
    { apply (proj1 (Dev__sub_wf_both E0 T1 T2 H1)); assumption. }
    destruct (IH2 HE HT2 A HA Hac) as [A1 [HA1 [Hac1 HA1']]].
    destruct (IH1 HE HS A1 HA1 Hac1) as [A2 [HA2 [Hac2 HA2']]].
    exists A2. repeat split; auto.
    eapply sub_trans; eauto.
  - exists A. repeat split; auto.
    + apply MyWork__rc_int_l. assumption.
    + apply Dev__sub_refl; assumption.
  - exists A. repeat split; auto.
    + apply MyWork__rc_int_r. assumption.
    + apply Dev__sub_refl; assumption.
  - destruct (MyWork__RComp_int_inv _ _ _ Hac) as [Hac2 | Hac2].
    + destruct (IH1 HE HS A HA Hac2) as [A' [HA' [Hac' HA'']]].
      exists A'. repeat split; auto.
    + destruct (IH2 HE HS A HA Hac2) as [A' [HA' [Hac' HA'']]].
      exists A'. repeat split; auto.
  - inversion Hac; subst.
    exists T1. split.
    + apply (Dev__wf_typ_inv_record _ _ _ HS).
    + split.
      * apply MyWork__rc_here.
      * exact H1.
  - destruct (MyWork__RComp_mut_record_inv mut_readonly a0 T2 A Hac) as [HeqA Heqa].
    subst A. subst a0.
    exists T1. split.
    + apply (Dev__wf_typ_inv_record _ _ _ (Dev__wf_typ_inv_readonly _ _ _ HS)).
    + split.
      * apply MyWork__rc_mut. apply MyWork__rc_here.
      * exact H1.
  - destruct (MyWork__RComp_pair_lift E0 T2 A HE HSd2 HA Hac) as [A0 [HA0 [Hac0 HA0']]].
    assert (Hnf : wf_typ E0 (normal_form_typing T1)) by (apply Dev__wf_typ_nf; assumption).
    destruct (IHsub HE Hnf A0 HA0 Hac0) as [A1 [HA1 [Hac1 HA1']]].
    destruct (MyWork__RComp_src_lift E0 T1 A1 HE HSd1 HA1 Hac1) as [A' [HA' [Hac' HA'']]].
    exists A'. repeat split; auto.
    eapply sub_trans; [exact HA'' | eapply sub_trans; [exact HA1' | exact HA0']].
Qed.

End RecordComp.

Lemma MyWork__sub_record_record : forall (E : env) (a : atom) A B,
  wf_env E -> wf_typ E (typ_record a A) -> wf_typ E (typ_record a B) ->
  sub E (typ_record a A) (typ_record a B) -> sub E A B.
Proof.
  intros E a A B HE HA HB Hsub.
  destruct (MyWork__sub_rcomp a E (typ_record a A) (typ_record a B) HE HA Hsub B
              (Dev__wf_typ_inv_record _ _ _ HB) (MyWork__rc_here a B))
    as [A' [HA' [Hac' H1]]].
  assert (Heq : A' = A) by (apply (MyWork__RComp_record_inv _ _ _ Hac')).
  subst A'. exact H1.
Qed.

Lemma MyWork__wf_typ_type : forall (E : env) T,
  wf_typ E T -> type T.
Proof.
  intros E T H. induction H.
  - apply type_top.
  - apply type_var.
  - apply type_arrow; assumption.
  - apply type_all with (L := L); auto.
  - apply type_box; assumption.
  - apply type_readonly; assumption.
  - apply type_intersect; assumption.
  - apply type_record; assumption.
Qed.




Lemma SubWeaken__sub_weaken_incl : forall (E1 : env) S T,
  wf_env E1 -> wf_typ E1 S -> sub E1 S T ->
  forall (E2 : env), wf_env E2 ->
  (forall x b, binds x b E1 -> binds x b E2) ->
  sub E2 S T.
Proof.
  intros E1 S T HE1 HS1 Hsub.
  revert HE1 HS1.
  induction Hsub as [ E1 S HE0 HS0
                 | E1 X HE0 HS0
                 | U E1 T0 X Hb Hsub IHsub
                 | E1 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E1 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E1 T1 T2 H1 IH1 H2 IH2
                 | E1 T1 T2 H1 IH1
                 | E1 T1 T2 H1 IH1
                 | E1 T1 T2 T3 H1 IH1 H2 IH2
                 | E1 T1 T2 HEi1 HSi1 HSi2
                 | E1 T1 T2 HEi2 HSi2b HSi2c
                 | E1 T1 T2 T3 H1 IH1 H2 IH2
                 | E1 a T1 T2 H1 IH1 H2 IH2
                 | E1 a T1 T2 H1 IH1
                 | E1 T1 T2 HSd1 HSd2 Hsub IHsub ];
    intros HE1 HS1 E2 HE2 Hincl.
  - apply sub_top; [assumption |].
    apply (MyWork__wf_typ_incl E1 S HS1 E2). intros X U Hb. apply Hincl. assumption.
  - apply sub_refl_tvar; [assumption |].
    apply (MyWork__wf_typ_incl E1 (typ_fvar X) HS1 E2). intros Y U Hb. apply Hincl. assumption.
  - apply (sub_trans_tvar U E2 T0 X).
    + apply Hincl. assumption.
    + apply (IHsub HE1 (Dev__wf_env_binds_sub _ HE1 X U Hb) E2 HE2 Hincl).
  - destruct (Dev__wf_typ_inv_arrow _ _ _ HS1) as [HSa HSb].
    assert (HT1 : wf_typ E1 T1) by (apply (Dev__sub_wf_source E1 T1 S1 HE1 HSa H1)).
    apply sub_arrow.
    + apply (IH1 HE1 HT1 E2 HE2 Hincl).
    + apply (IH2 HE1 HSb E2 HE2 Hincl).
  - destruct (Dev__wf_typ_inv_all _ _ _ HS1) as [L1 [HSa HSb]].
    apply (sub_all (L0 `union` L1 `union` dom E1 `union` dom E2) E2 S1 S2 T1 T2).
    + assert (HT1 : wf_typ E1 T1) by (apply (Dev__sub_wf_source E1 T1 S1 HE1 HSa H1)).
      apply (IH1 HE1 HT1 E2 HE2 Hincl).
    + intros Y HY.
      assert (HYL0 : Y `notin` L0) by (apply notin_union_1 in HY; assumption).
      assert (HYL1 : Y `notin` L1) by (apply notin_union_2 in HY; apply notin_union_1 in HY; assumption).
      assert (HYd1 : Y `notin` dom E1)
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; apply notin_union_1 in HY; assumption).
      assert (HYd : Y `notin` dom E2)
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; apply notin_union_2 in HY; assumption).
      assert (HT1s : wf_typ E1 T1) by (apply (Dev__sub_wf_source E1 T1 S1 HE1 HSa H1)).
      assert (HT1 : wf_typ E2 T1).
      { apply (MyWork__wf_typ_incl E1 T1 HT1s E2). intros X U Hb. apply Hincl. assumption. }
      assert (Hwe1 : wf_env (Y ~ bind_sub T1 ++ E1)).
      { apply (wf_env_sub E1 Y T1); [exact HE1 | exact HT1s | exact HYd1]. }
      assert (Hwe2 : wf_env (Y ~ bind_sub T1 ++ E2)).
      { apply (wf_env_sub E2 Y T1); [exact HE2 | exact HT1 | exact HYd]. }
      assert (HSbT : wf_typ (Y ~ bind_sub T1 ++ E1) (open_tt S2 Y)).
      { eapply Dev__wf_typ_kind. exact (HSb Y HYL1).
        intros Z. apply Dev__same_kinds_cons_sub_any. apply Dev__same_kinds_refl. }
      apply (IH0 Y HYL0 Hwe1 HSbT (Y ~ bind_sub T1 ++ E2) Hwe2).
      intros x b Hb.
      destruct Hb as [Heq | Hin].
      * left; assumption.
      * right. apply Hincl. assumption.
  - assert (HwT1 : wf_typ E1 T1) by (apply (Dev__wf_typ_inv_box _ _ HS1)).
    assert (HwT2 : wf_typ E1 T2).
    { apply (Dev__sub_wf_target E1 T1 T2 HE1 HwT1 H1). }
    apply sub_box.
    + apply (IH1 HE1 HwT1 E2 HE2 Hincl).
    + apply (IH2 HE1 HwT2 E2 HE2 Hincl).
  - apply sub_readonly. apply (IH1 HE1 (Dev__wf_typ_inv_readonly _ _ _ HS1) E2 HE2 Hincl).
  - apply sub_readonly_mutable. apply (IH1 HE1 HS1 E2 HE2 Hincl).
  - assert (HT2 : wf_typ E1 T2) by (apply (Dev__sub_wf_target E1 T1 T2 HE1 HS1 H1)).
    apply sub_trans with (T2 := T2).
    + apply (IH1 HE1 HS1 E2 HE2 Hincl).
    + apply (IH2 HE1 HT2 E2 HE2 Hincl).
  - apply (sub_inter_left E2 T1 T2); [assumption | |].
    + apply (MyWork__wf_typ_incl E1 T1 HSi1 E2); intros X U Hb; apply Hincl; assumption.
    + apply (MyWork__wf_typ_incl E1 T2 HSi2 E2); intros X U Hb; apply Hincl; assumption.
  - apply (sub_inter_right E2 T1 T2); [assumption | |].
    + apply (MyWork__wf_typ_incl E1 T1 HSi2b E2); intros X U Hb; apply Hincl; assumption.
    + apply (MyWork__wf_typ_incl E1 T2 HSi2c E2); intros X U Hb; apply Hincl; assumption.
  - apply sub_inter.
    + apply (IH1 HE1 HS1 E2 HE2 Hincl).
    + apply (IH2 HE1 HS1 E2 HE2 Hincl).
  - assert (HwT1 : wf_typ E1 T1) by (apply (Dev__wf_typ_inv_record _ _ _ HS1)).
    assert (HwT2 : wf_typ E1 T2) by (apply (Dev__sub_wf_target E1 T1 T2 HE1 HwT1 H1)).
    apply sub_record.
    + apply (IH1 HE1 HwT1 E2 HE2 Hincl).
    + apply (IH2 HE1 HwT2 E2 HE2 Hincl).
  - apply sub_readonly_record.
    apply (IH1 HE1 (Dev__wf_typ_inv_record _ _ _ (Dev__wf_typ_inv_readonly _ _ _ HS1)) E2 HE2 Hincl).
  - apply (sub_denormalize E2 T1 T2).
    + apply (MyWork__wf_typ_incl E1 T1 HSd1 E2); intros X U Hb; apply Hincl; assumption.
    + apply (MyWork__wf_typ_incl E1 T2 HSd2 E2); intros X U Hb; apply Hincl; assumption.
    + apply (IHsub HE1 (Dev__wf_typ_nf _ _ HSd1) E2 HE2 Hincl).
Qed.




Lemma Narrow__same_kinds_narrow : forall (E1 E2 : env) X U U',
  Dev__same_kinds (E1 ++ X ~ bind_sub U ++ E2) (E1 ++ X ~ bind_sub U' ++ E2).
Proof.
  intros E1. induction E1 as [| [Y b] E1 IH]; intros E2 X U U'; simpl.
  - apply (Dev__same_kinds_cons_sub_any E2 E2 X U U'). apply Dev__same_kinds_refl.
  - destruct b as [U0 | T0].
    + apply Dev__same_kinds_cons_sub_any. apply IH.
    + apply Dev__same_kinds_cons_typ. apply IH.
Qed.

Lemma Narrow__dom_narrow_eq : forall (E1 E2 : env) X U U',
  dom (E1 ++ X ~ bind_sub U ++ E2) [=] dom (E1 ++ X ~ bind_sub U' ++ E2).
Proof.
  intros E1. induction E1 as [| [Y b] E1 IH]; intros E2 X U U'; simpl.
  - reflexivity.
  - assert (H := IH E2 X U U'). fsetdec.
Qed.

Lemma Narrow__notin_dom_eq : forall (E1 E2 : env) (x : atom),
  dom E1 [=] dom E2 -> x `notin` dom E1 -> x `notin` dom E2.
Proof. intros. fsetdec. Qed.

Lemma Narrow__wf_env_cons_bind_sub_full : forall (E : env) X T,
  wf_env (X ~ bind_sub T ++ E) -> wf_env E /\ wf_typ E T /\ X `notin` dom E.
Proof. intros. inversion H; subst; try discriminate. auto. Qed.

Lemma Narrow__wf_env_cons_bind_typ_full : forall (E : env) X T,
  wf_env (X ~ bind_typ T ++ E) -> wf_env E /\ wf_typ E T /\ X `notin` dom E.
Proof. intros. inversion H; subst; try discriminate. auto. Qed.

Lemma Narrow__wf_env_narrow : forall (E1 E2 : env) X U U',
  X `notin` dom E1 -> X `notin` dom E2 ->
  wf_env (E1 ++ X ~ bind_sub U ++ E2) ->
  wf_typ E2 U' ->
  wf_env (E1 ++ X ~ bind_sub U' ++ E2).
Proof.
  intros E1. induction E1 as [| [Y b] E1 IH]; intros E2 X U U' Hnd1 Hnd2 Hwf HU'; simpl in *.
  - destruct (Dev__wf_env_cons_bind_sub _ _ _ Hwf) as [Hwe HwU].
    apply (wf_env_sub E2 X U' Hwe HU' Hnd2).
  - destruct b as [U0 | T0].
    + destruct (Narrow__wf_env_cons_bind_sub_full _ _ _ Hwf) as [Hwe [Hwt Ynotin]].
      assert (Hwe' : wf_env (E1 ++ X ~ bind_sub U' ++ E2)).
      { apply (IH E2 X U U').
        - intro Hc. apply Hnd1. apply (proj2 (Dev__in_dom_cons E1 X Y (bind_sub U0))). right. assumption.
        - exact Hnd2. - exact Hwe. - exact HU'. }
      assert (Hwt' : wf_typ (E1 ++ X ~ bind_sub U' ++ E2) U0).
      { eapply Dev__wf_typ_kind. exact Hwt.
        intros Z. apply Narrow__same_kinds_narrow. }
      assert (Hnot : Y `notin` dom (E1 ++ X ~ bind_sub U' ++ E2)).
      { apply (Narrow__notin_dom_eq (E1 ++ X ~ bind_sub U ++ E2)).
        - apply Narrow__dom_narrow_eq. - exact Ynotin. }
      apply (wf_env_sub (E1 ++ X ~ bind_sub U' ++ E2) Y U0); assumption.
    + destruct (Narrow__wf_env_cons_bind_typ_full _ _ _ Hwf) as [Hwe [Hwt Ynotin]].
      assert (Hwe' : wf_env (E1 ++ X ~ bind_sub U' ++ E2)).
      { apply (IH E2 X U U').
        - intro Hc. apply Hnd1. apply (proj2 (Dev__in_dom_cons E1 X Y (bind_typ T0))). right. assumption.
        - exact Hnd2. - exact Hwe. - exact HU'. }
      assert (Hwt' : wf_typ (E1 ++ X ~ bind_sub U' ++ E2) T0).
      { eapply Dev__wf_typ_kind. exact Hwt.
        intros Z. apply Narrow__same_kinds_narrow. }
      assert (Hnot : Y `notin` dom (E1 ++ X ~ bind_sub U' ++ E2)).
      { apply (Narrow__notin_dom_eq (E1 ++ X ~ bind_sub U ++ E2)).
        - apply Narrow__dom_narrow_eq. - exact Ynotin. }
      apply (wf_env_typ (E1 ++ X ~ bind_sub U' ++ E2) Y T0); assumption.
Qed.

Lemma Narrow__binds_narrow_neq : forall (E1 E2 : env) X U U' Y b,
  Y <> X ->
  (binds Y b (E1 ++ X ~ bind_sub U ++ E2) <->
   binds Y b (E1 ++ X ~ bind_sub U' ++ E2)).
Proof.
  intros E1. induction E1 as [| [Z c] E1 IH]; intros E2 X U U' Y b Hne; simpl.
  - split; intros [Heq | Hin].
    + injection Heq as HY Hb. subst Y. exfalso. apply Hne. reflexivity.
    + right. assumption.
    + injection Heq as HY Hb. subst Y. exfalso. apply Hne. reflexivity.
    + right. assumption.
  - split; intros [Heq | Hin].
    + left; assumption.
    + right. apply (proj1 (IH E2 X U U' Y b Hne)); assumption.
    + left; assumption.
    + right. apply (proj2 (IH E2 X U U' Y b Hne)); assumption.
Qed.

Lemma Narrow__binds_mid_eq : forall (E1 E2 : env) X U U0,
  binds X (bind_sub U0) (E1 ++ X ~ bind_sub U ++ E2) ->
  X `notin` dom E1 -> X `notin` dom E2 -> U0 = U.
Proof.
  intros E1. induction E1 as [| [Z c] E1 IH]; intros E2 X U U0 Hb Hnd1 Hnd2; simpl in *.
  - destruct Hb as [Heq | Hin].
    + inversion Heq. reflexivity.
    + exfalso. apply Hnd2. apply Dev__in_dom_binds in Hin. assumption.
  - destruct Hb as [Heq | Hin].
    + injection Heq as HX Hc. exfalso. apply Hnd1.
      apply (proj2 (Dev__in_dom_cons E1 X Z c)). left. symmetry. exact HX.
    + apply (IH E2 X U U0 Hin).
      * intro Hc. apply Hnd1. apply (proj2 (Dev__in_dom_cons E1 X Z c)). right. assumption.
      * assumption.
Qed.

Lemma Narrow__binds_mid_self : forall (E1 E2 : env) X (b : binding),
  binds X b (E1 ++ X ~ b ++ E2).
Proof.
  intros E1. induction E1 as [| [Y c] E1 IH]; intros E2 X b; simpl.
  - left. reflexivity.
  - right. apply IH.
Qed.

Lemma Narrow__wf_env_app_mid : forall (E1 E2 : env) X (b : binding),
  wf_env (E1 ++ X ~ b ++ E2) -> wf_env E2.
Proof.
  intros E1. induction E1 as [| [Y c] E1 IH]; intros E2 X b Hwf; simpl in *.
  - destruct b as [U0|T0];
    [ destruct (Narrow__wf_env_cons_bind_sub_full _ _ _ Hwf) as [H _] |
      destruct (Narrow__wf_env_cons_bind_typ_full _ _ _ Hwf) as [H _] ]; exact H.
  - destruct c as [U0|T0].
    + destruct (Narrow__wf_env_cons_bind_sub_full _ _ _ Hwf) as [H _].
      apply (IH E2 X b H).
    + destruct (Narrow__wf_env_cons_bind_typ_full _ _ _ Hwf) as [H _].
      apply (IH E2 X b H).
Qed.

Lemma Narrow__wf_typ_app_mid : forall (E1 E2 : env) X U T,
  wf_typ E1 T -> wf_typ (E1 ++ X ~ bind_sub U ++ E2) T.
Proof.
  intros. apply (MyWork__wf_typ_incl E1 T H (E1 ++ X ~ bind_sub U ++ E2)).
  intros Y U0 Hb. apply in_or_app. left. exact Hb.
Qed.

Lemma Narrow__dom_app : forall (E1 E2 : env),
  dom (E1 ++ E2) [=] dom E1 `union` dom E2.
Proof.
  intros E1. induction E1 as [| [Y b] E1 IH]; intros E2; simpl.
  - fsetdec.
  - assert (H := IH E2). fsetdec.
Qed.

Lemma Narrow__notin_dom_mid : forall (E1 E2 : env) X U x,
  x <> X -> x `notin` dom E1 -> x `notin` dom E2 ->
  x `notin` dom (E1 ++ X ~ bind_sub U ++ E2).
Proof.
  intros. rewrite Narrow__dom_app. assert (Hd : dom ((X, bind_sub U) :: E2) [=] add X (dom E2))
    by reflexivity.
  rewrite Hd. fsetdec.
Qed.

Lemma Narrow__notin_dom_cons : forall (E : env) x (y : atom) (b : binding),
  x <> y -> x `notin` dom E -> x `notin` dom ((y,b)::E).
Proof.
  intros. rewrite Dev__in_dom_cons. intros [Heq | Hin].
  - apply H. exact Heq.
  - apply H0. exact Hin.
Qed.

Lemma Narrow__notin_dom_mid_cons : forall (E1 E2 : env) (X0 : atom) (T1 : typ) X U x,
  x <> X -> x <> X0 -> x `notin` dom E1 -> x `notin` dom E2 ->
  x `notin` dom (((X0, bind_sub T1) :: E1) ++ X ~ bind_sub U ++ E2).
Proof.
  intros. apply Narrow__notin_dom_mid.
  - exact H.
  - apply Narrow__notin_dom_cons; assumption.
  - exact H2.
Qed.




Lemma SubNarrow__sub_narrow : forall (E1 E2 : env) X U U' S T,
  X `notin` dom E1 -> X `notin` dom E2 ->
  wf_env (E1 ++ X ~ bind_sub U ++ E2) ->
  wf_typ (E1 ++ X ~ bind_sub U ++ E2) S ->
  wf_typ E2 U' ->
  sub E2 U' U ->
  sub (E1 ++ X ~ bind_sub U ++ E2) S T ->
  sub (E1 ++ X ~ bind_sub U' ++ E2) S T.
Proof.
  intros E1 E2 X U U' S T Hnd1 Hnd2 Hwf HS1 HU' HsubU Hsub.
  remember (E1 ++ X ~ bind_sub U ++ E2) as E0 eqn:He.
  revert E1 E2 X U U' Hnd1 Hnd2 Hwf HS1 HU' HsubU He.
  induction Hsub as [ E0 S HE0 HS0
                 | E0 Y HE0 HS0
                 | U0 E0 T0 Y Hb Hpre IHpre
                 | E0 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E0 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 T1 T2 HEi1 HSi1 HSi2
                 | E0 T1 T2 HEi2 HSi2b HSi2c
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1
                 | E0 T1 T2 HSd1 HSd2 Hsub IHsub ];
    intros E1 E2 X U U' Hnd1 Hnd2 Hwf HS1 HU' HsubU He; subst E0.
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    apply sub_top; [assumption |].
    eapply Dev__wf_typ_kind.
    + exact HS1.
    + intros Z. apply Narrow__same_kinds_narrow.
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    apply sub_refl_tvar; [assumption |].
    eapply Dev__wf_typ_kind.
    + exact HS1.
    + intros Z. apply Narrow__same_kinds_narrow.
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    destruct (Y == X) as [Heq | Hneq].
    + subst Y.
      assert (HeqU : U0 = U) by (apply (Narrow__binds_mid_eq E1 E2 X U U0 Hb); assumption).
      subst U0.
      assert (HUold : wf_typ (E1 ++ X ~ bind_sub U ++ E2) U).
      { apply (Dev__wf_env_binds_sub (E1 ++ X ~ bind_sub U ++ E2) Hwf X U Hb). }
      assert (HpreU : sub (E1 ++ X ~ bind_sub U' ++ E2) U T0)
        by (apply (IHpre E1 E2 X U U' Hnd1 Hnd2 Hwf HUold HU' HsubU eq_refl)).
      apply (sub_trans_tvar U' (E1 ++ X ~ bind_sub U' ++ E2) T0 X).
      * apply (Narrow__binds_mid_self E1 E2 X (bind_sub U')).
      * eapply sub_trans; [| exact HpreU].
        apply (SubWeaken__sub_weaken_incl E2 U' U (Narrow__wf_env_app_mid E1 E2 X (bind_sub U) Hwf) HU' HsubU
                 (E1 ++ X ~ bind_sub U' ++ E2) Hwfnew).
        intros x b Hx. apply Dev__binds_app_2. apply Dev__binds_cons_2. assumption.
    + assert (Hbnew : binds Y (bind_sub U0) (E1 ++ X ~ bind_sub U' ++ E2)).
      { apply (proj1 (Narrow__binds_narrow_neq E1 E2 X U U' Y (bind_sub U0) Hneq)). assumption. }
      assert (HUold : wf_typ (E1 ++ X ~ bind_sub U ++ E2) U0)
        by (apply (Dev__wf_env_binds_sub (E1 ++ X ~ bind_sub U ++ E2) Hwf Y U0 Hb)).
      apply (sub_trans_tvar U0 (E1 ++ X ~ bind_sub U' ++ E2) T0 Y Hbnew).
      apply (IHpre E1 E2 X U U' Hnd1 Hnd2 Hwf HUold HU' HsubU eq_refl).
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    destruct (Dev__wf_typ_inv_arrow _ _ _ HS1) as [HSa HSb].
    assert (HT1 : wf_typ (E1 ++ X ~ bind_sub U ++ E2) T1)
      by (apply (Dev__sub_wf_source _ T1 S1 Hwf HSa H1)).
    apply sub_arrow.
    + apply (IH1 E1 E2 X U U' Hnd1 Hnd2 Hwf HT1 HU' HsubU eq_refl).
    + apply (IH2 E1 E2 X U U' Hnd1 Hnd2 Hwf HSb HU' HsubU eq_refl).
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    destruct (Dev__wf_typ_inv_all _ _ _ HS1) as [L1 [HSa HSb]].
    assert (HT1 : wf_typ (E1 ++ X ~ bind_sub U ++ E2) T1)
      by (apply (Dev__sub_wf_source _ T1 S1 Hwf HSa H1)).
    assert (HT1new : wf_typ (E1 ++ X ~ bind_sub U' ++ E2) T1).
    { eapply Dev__wf_typ_kind. exact HT1. intros Z. apply Narrow__same_kinds_narrow. }
    apply (sub_all (L0 `union` L1 `union` dom E1 `union` dom E2 `union` {{ X }})
              (E1 ++ X ~ bind_sub U' ++ E2) S1 S2 T1 T2).
    + apply (IH1 E1 E2 X U U' Hnd1 Hnd2 Hwf HT1 HU' HsubU eq_refl).
    + intros Y HY.
      assert (HYL0 : Y `notin` L0) by (apply notin_union_1 in HY; assumption).
      assert (HYL1 : Y `notin` L1)
        by (apply notin_union_2 in HY; apply notin_union_1 in HY; assumption).
      assert (HYd1 : Y `notin` dom E1)
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; apply notin_union_1 in HY; assumption).
      assert (HYd2 : Y `notin` dom E2)
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; apply notin_union_2 in HY; apply notin_union_1 in HY; assumption).
      assert (HYX : Y `notin` {{ X }})
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; apply notin_union_2 in HY; apply notin_union_2 in HY; assumption).
      assert (HYne : Y <> X).
      { apply notin_singleton_1' in HYX. symmetry. exact HYX. }
      assert (HXY1 : X `notin` dom ((Y, bind_sub T1) :: E1)).
      { apply Narrow__notin_dom_cons; [symmetry; exact HYne | exact Hnd1]. }
      assert (HYold : Y `notin` dom (E1 ++ X ~ bind_sub U ++ E2)).
      { apply (Narrow__notin_dom_mid E1 E2 X U Y); assumption. }
      assert (Hwe_old : wf_env ((Y, bind_sub T1) :: E1 ++ X ~ bind_sub U ++ E2)).
      { apply (wf_env_sub (E1 ++ X ~ bind_sub U ++ E2) Y T1); assumption. }
      assert (Hwsrc : wf_typ ((Y, bind_sub T1) :: E1 ++ X ~ bind_sub U ++ E2)
                           (open_tt S2 Y)).
      { eapply Dev__wf_typ_kind. exact (HSb Y HYL1).
        intros Z. apply Dev__same_kinds_cons_sub_any. apply Dev__same_kinds_refl. }
      apply (IH0 Y HYL0 ((Y, bind_sub T1) :: E1) E2 X U U'
                HXY1 Hnd2 Hwe_old Hwsrc HU' HsubU eq_refl).
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    assert (HwT1 : wf_typ (E1 ++ X ~ bind_sub U ++ E2) T1)
      by (apply (Dev__wf_typ_inv_box _ _ HS1)).
    assert (HwT2 : wf_typ (E1 ++ X ~ bind_sub U ++ E2) T2)
      by (apply (Dev__sub_wf_target _ T1 T2 Hwf HwT1 H1)).
    apply sub_box.
    + apply (IH1 E1 E2 X U U' Hnd1 Hnd2 Hwf HwT1 HU' HsubU eq_refl).
    + apply (IH2 E1 E2 X U U' Hnd1 Hnd2 Hwf HwT2 HU' HsubU eq_refl).
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    apply sub_readonly. apply (IH1 E1 E2 X U U' Hnd1 Hnd2 Hwf
      (Dev__wf_typ_inv_readonly _ _ _ HS1) HU' HsubU eq_refl).
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    apply sub_readonly_mutable. apply (IH1 E1 E2 X U U' Hnd1 Hnd2 Hwf HS1 HU' HsubU eq_refl).
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    assert (HT2 : wf_typ (E1 ++ X ~ bind_sub U ++ E2) T2)
      by (apply (Dev__sub_wf_target _ T1 T2 Hwf HS1 H1)).
    apply sub_trans with (T2 := T2).
    + apply (IH1 E1 E2 X U U' Hnd1 Hnd2 Hwf HS1 HU' HsubU eq_refl).
    + apply (IH2 E1 E2 X U U' Hnd1 Hnd2 Hwf HT2 HU' HsubU eq_refl).
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    apply (sub_inter_left (E1 ++ X ~ bind_sub U' ++ E2) T1 T2); [assumption | |].
    + eapply Dev__wf_typ_kind; [exact HSi1 |]. intros Z; apply Narrow__same_kinds_narrow.
    + eapply Dev__wf_typ_kind; [exact HSi2 |]. intros Z; apply Narrow__same_kinds_narrow.
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    apply (sub_inter_right (E1 ++ X ~ bind_sub U' ++ E2) T1 T2); [assumption | |].
    + eapply Dev__wf_typ_kind; [exact HSi2b |]. intros Z; apply Narrow__same_kinds_narrow.
    + eapply Dev__wf_typ_kind; [exact HSi2c |]. intros Z; apply Narrow__same_kinds_narrow.
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    apply sub_inter.
    + apply (IH1 E1 E2 X U U' Hnd1 Hnd2 Hwf HS1 HU' HsubU eq_refl).
    + apply (IH2 E1 E2 X U U' Hnd1 Hnd2 Hwf HS1 HU' HsubU eq_refl).
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    assert (HwT1 : wf_typ (E1 ++ X ~ bind_sub U ++ E2) T1)
      by (apply (Dev__wf_typ_inv_record _ _ _ HS1)).
    assert (HwT2 : wf_typ (E1 ++ X ~ bind_sub U ++ E2) T2)
      by (apply (Dev__sub_wf_target _ T1 T2 Hwf HwT1 H1)).
    apply sub_record.
    + apply (IH1 E1 E2 X U U' Hnd1 Hnd2 Hwf HwT1 HU' HsubU eq_refl).
    + apply (IH2 E1 E2 X U U' Hnd1 Hnd2 Hwf HwT2 HU' HsubU eq_refl).
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    apply sub_readonly_record. apply (IH1 E1 E2 X U U' Hnd1 Hnd2 Hwf
      (Dev__wf_typ_inv_record _ _ _ (Dev__wf_typ_inv_readonly _ _ _ HS1)) HU' HsubU eq_refl).
  - assert (Hwfnew : wf_env (E1 ++ X ~ bind_sub U' ++ E2))
      by (apply (Narrow__wf_env_narrow E1 E2 X U U'); assumption).
    apply (sub_denormalize (E1 ++ X ~ bind_sub U' ++ E2) T1 T2).
    + eapply Dev__wf_typ_kind; [exact HSd1 |]. intros Z; apply Narrow__same_kinds_narrow.
    + eapply Dev__wf_typ_kind; [exact HSd2 |]. intros Z; apply Narrow__same_kinds_narrow.
    + apply (IHsub E1 E2 X U U' Hnd1 Hnd2 Hwf (Dev__wf_typ_nf _ _ HSd1) HU' HsubU eq_refl).
Qed.




(* ================================================================ *)
(* 1. Well-formed signatures: binding inversion and uniqueness      *)
(* ================================================================ *)

Lemma Store__wf_sig_binds : forall (E : env) (R : sig) (l : label) (T : typ),
  wf_sig E R -> Signatures.binds l (bind_sig T) R -> wf_typ E T.
Proof.
  intros E R l T H. induction H as [E0 Hwe | E0 R0 l0 T0 Hws IH Hwt Hnot];
    intro Hb.
  - (* empty signature *)
    simpl in Hb. inversion Hb.
  - (* l0 ~ bind_sig T0 ++ R0 *)
    apply Signatures.binds_cons_iff in Hb.
    destruct Hb as [[Heql HeqT] | Hin].
    + injection HeqT as HT. subst. exact Hwt.
    + apply IH. exact Hin.
Qed.

Lemma Store__wf_sig_uniq : forall (E : env) (R : sig),
  wf_sig E R -> Signatures.uniq R.
Proof.
  intros E R H. induction H as [E0 Hwe | E0 R0 l0 T0 Hws IH Hwt Hnot].
  - constructor.
  - apply Signatures.uniq_push; assumption.
Qed.

Lemma Store__wf_sig_binds_uniq : forall (E : env) (R : sig) (l : label) (T1 T2 : typ),
  wf_sig E R ->
  Signatures.binds l (bind_sig T1) R ->
  Signatures.binds l (bind_sig T2) R -> T1 = T2.
Proof.
  intros E R l T1 T2 Hws Hb1 Hb2.
  assert (Hu : Signatures.uniq R) by (exact (Store__wf_sig_uniq E R Hws)).
  pose proof (Signatures.binds_unique signature l (bind_sig T1) (bind_sig T2) R
                Hb1 Hb2 Hu) as Heq.
  injection Heq as HT. exact HT.
Qed.

(* ================================================================ *)
(* 2. Domination lemmas for signature concatenation                 *)
(* ================================================================ *)

Lemma Store__sig_dom_app : forall (R1 R2 : sig) (l : label),
  LabelSetImpl.In l (Signatures.dom (R1 ++ R2)) <->
  LabelSetImpl.In l (Signatures.dom R1) \/ LabelSetImpl.In l (Signatures.dom R2).
Proof.
  intros R1 R2 l.
  pose proof (@Signatures.dom_app signature R1 R2) as Heq.
  pose proof (@LabelSetFacts.In_m l l eq_refl
                (Signatures.dom (R1 ++ R2))
                (LabelSetImpl.union (Signatures.dom R1)
                                    (Signatures.dom R2)) Heq) as Hm.
  split; intro H.
  - apply LabelSetFacts.union_iff. apply (proj1 Hm). exact H.
  - apply (proj2 Hm). apply LabelSetFacts.union_iff. exact H.
Qed.

Lemma Store__binds_sig_cons : forall (R : sig) (l0 : label) (T0 : typ)
                              (l : label) (T : typ),
  Signatures.binds l (bind_sig T) (l0 ~ bind_sig T0 ++ R) <->
  (l = l0 /\ T = T0) \/ Signatures.binds l (bind_sig T) R.
Proof.
  intros.
  change (Signatures.binds l (bind_sig T) ((l0, bind_sig T0) :: R) <->
          (l = l0 /\ T = T0) \/ Signatures.binds l (bind_sig T) R).
  rewrite Signatures.binds_cons_iff.
  split; intro H.
  - destruct H as [[Hl Hs] | H].
    + left. split; auto. injection Hs as HT. exact HT.
    + right. exact H.
  - destruct H as [[Hl HT] | H].
    + left. split; auto. rewrite HT. reflexivity.
    + right. exact H.
Qed.

Lemma Store__wf_sig_app : forall (E : env) (R1 R2 : sig),
  wf_sig E R1 -> wf_sig E R2 ->
  (forall (l : label) (T : typ),
      Signatures.binds l (bind_sig T) R1 ->
      ~ (LabelSetImpl.In l (Signatures.dom R2))) ->
  wf_sig E (R1 ++ R2).
Proof.
  intros E R1 R2 H1.
  induction H1 as [E0 Hwe | E0 R0 l0 T0 Hws IH Hwt Hnot];
    intros H2 Hdisj.
  - simpl. exact H2.
  - change (wf_sig E0 ((l0 ~ bind_sig T0 ++ R0) ++ R2)).
    simpl. apply wf_sig_typ.
    + apply IH.
      * exact H2.
      * intros l T Hb.
        exact (Hdisj l T
                 (proj2 (Store__binds_sig_cons R0 l0 T0 l T) (or_intror Hb))).
    + exact Hwt.
    + intro Hin. apply (proj1 (Store__sig_dom_app R0 R2 l0)) in Hin.
      destruct Hin as [Hin1 | Hin2].
      * exact (Hnot Hin1).
      * exact (Hdisj l0 T0
                 (proj2 (Store__binds_sig_cons R0 l0 T0 l0 T0)
                        (or_introl (conj eq_refl eq_refl))) Hin2).
Qed.

(* ================================================================ *)
(* 3. Fresh label properties                                         *)
(* ================================================================ *)

Lemma Store__InA_eq_key_elt_fst : forall (p : label * exp)
                                  (l : list (label * exp)),
  InA (LabelMapImpl.eq_key_elt (elt := exp)) p l ->
  In (fst p) (List.map fst l).
Proof.
  intros p l H. induction H as [y l0 HR | y l0 HR IH].
  - unfold LabelMapImpl.eq_key_elt in HR. simpl in HR.
    destruct HR as [Hfst _]. simpl. left. symmetry. exact Hfst.
  - simpl. right. exact IH.
Qed.

Lemma Store__fresh_label_not_maps : forall (s : store) (l : label) (v : exp),
  fresh_label_for_store s = l ->
  LabelMapImpl.MapsTo l v s -> False.
Proof.
  intros s l v Hfresh HMaps.
  apply LabelMapFacts.elements_mapsto_iff in HMaps.
  pose proof (Store__InA_eq_key_elt_fst (l, v) (LabelMapImpl.elements s) HMaps) as Hin.
  pose proof (Label.fresh_not_in (List.map fst (LabelMapImpl.elements s))) as Hnot.
  unfold fresh_label_for_store in Hfresh.
  rewrite <- Hfresh in Hin. exact (Hnot Hin).
Qed.

Lemma Store__fresh_label_neq : forall (s : store) (l : label) (v : exp) (l0 : label),
  fresh_label_for_store s = l ->
  LabelMapImpl.MapsTo l0 v s -> l <> l0.
Proof.
  intros s l v l0 Hfresh HMaps Heq.
  subst l0.
  exact (Store__fresh_label_not_maps s l v Hfresh HMaps).
Qed.

Lemma Store__typing_store_dom : forall (E : env) (R : sig) (s : store)
                                (l : label) (T : typ),
  typing_store E R s ->
  Signatures.binds l (bind_sig T) R ->
  exists v, LabelMapImpl.MapsTo l v s.
Proof.
  intros E R s l T Hts Hb.
  unfold typing_store in Hts.
  destruct (Hts l) as [Hfst _].
  destruct (Hfst T Hb) as [v [HMaps _]]. exists v. exact HMaps.
Qed.

Lemma Store__fresh_label_notin_sig_dom : forall (E : env) (R : sig)
                                        (s : store) (l : label),
  typing_store E R s ->
  l = fresh_label_for_store s ->
  ~ LabelSetImpl.In l (Signatures.dom R).
Proof.
  intros E R s l Hts Hfresh Hin.
  apply Signatures.binds_In_inv in Hin.
  destruct Hin as [S Hb]. destruct S as [T].
  destruct (Store__typing_store_dom E R s l T Hts Hb) as [v HMaps].
  apply (Store__fresh_label_not_maps s l v).
  - symmetry. exact Hfresh.
  - exact HMaps.
Qed.

(* ================================================================ *)
(* Auxiliary: typing entails well-formedness of the signature       *)
(* ================================================================ *)

Lemma Store__typing_wf_sig_mut : forall (E : env) (R : sig) (e : exp) (T : typ),
  typing E R e T -> wf_sig E R
with Store__typing_record_wf_sig_mut : forall (E : env) (R : sig) (r : rec_comp) (T : typ),
  typing_record_comp E R r T -> wf_sig E R.
Proof.
  - intros E R e T Hty. induction Hty; eauto.
  - intros E R r T Htr. induction Htr; eauto.
Qed.

(* Extending the environment with one binding preserves a wf signature. *)
Lemma Store__wf_sig_env_weaken_cons : forall (E : env) (R : sig)
                                     (X : atom) (b : binding),
  wf_sig E R -> wf_env (X ~ b ++ E) -> wf_sig (X ~ b ++ E) R.
Proof.
  intros E R X b Hws Hwe. revert Hwe.
  induction Hws as [E0 Hwe0 | E0 R0 l0 T0 Hws0 IH Hwt Hnot];
    intro Hwe'.
  - apply wf_sig_empty. exact Hwe'.
  - apply wf_sig_typ.
    + apply IH. exact Hwe'.
    + apply Dev__wf_typ_weaken_cons1. exact Hwt.
    + exact Hnot.
Qed.

(* ================================================================ *)
(* Signature weakening for typing                                   *)
(* ================================================================ *)

Scheme Store__typing_mut := Induction for typing Sort Prop
with Store__typing_record_mut := Induction for typing_record_comp Sort Prop.

Lemma Store__typing_sig_weaken_aux : forall (E : env) (R : sig) (e : exp) (T : typ),
  typing E R e T ->
  forall (R2 : sig), wf_sig E (R2 ++ R) -> typing E (R2 ++ R) e T.
Proof.
  intros E0 R0 e0 T0 Hty0.
  pose (P := fun (E : env) (R : sig) (e : exp) (T : typ)
                   (_ : typing E R e T) =>
               forall R2, wf_sig E (R2 ++ R) -> typing E (R2 ++ R) e T).
  pose (Q := fun (E : env) (R : sig) (r : rec_comp) (T : typ)
                   (_ : typing_record_comp E R r T) =>
               forall R2, wf_sig E (R2 ++ R) ->
                         typing_record_comp E (R2 ++ R) r T).
  change (P E0 R0 e0 T0 Hty0).
  apply (Store__typing_mut P Q).
  - (* var *) intros E R x T Hwe Hws Hbind R2 Hws'.
    apply (typing_var E (R2 ++ R) x T Hwe Hws' Hbind).
  - (* abs *) intros L E R V e1 T1 Hws Hbody IHbody R2 Hws'.
    apply (typing_abs L E (R2 ++ R) V e1 T1 Hws').
    intros x Hx.
    apply (IHbody x Hx R2).
    apply (Store__wf_sig_env_weaken_cons E (R2 ++ R) x (bind_typ V) Hws').
    apply (Dev__wf_sig_wf_env (x ~ bind_typ V ++ E) R).
    apply (Store__typing_wf_sig_mut (x ~ bind_typ V ++ E) R (open_ee e1 x) T1).
    apply Hbody. exact Hx.
  - (* app *) intros T1 E R e1 e2 T2 Hws Hbody1 IH1 Hbody2 IH2 R2 Hws'.
    apply (typing_app T1 E (R2 ++ R) e1 e2 T2 Hws'
             (IH1 R2 Hws') (IH2 R2 Hws')).
  - (* tabs *) intros L E R V e1 T1 Hws Hbody IHbody R2 Hws'.
    apply (typing_tabs L E (R2 ++ R) V e1 T1 Hws').
    intros X HX.
    apply (IHbody X HX R2).
    apply (Store__wf_sig_env_weaken_cons E (R2 ++ R) X (bind_sub V) Hws').
    apply (Dev__wf_sig_wf_env (X ~ bind_sub V ++ E) R).
    apply (Store__typing_wf_sig_mut (X ~ bind_sub V ++ E) R
             (open_te e1 X) (open_tt T1 X)).
    apply Hbody. exact HX.
  - (* tapp *) intros T1 E R e1 T T2 Hws Hbody IH Hsub R2 Hws'.
    apply (typing_tapp T1 E (R2 ++ R) e1 T T2 Hws'
             (IH R2 Hws') Hsub).
  - (* sub *) intros S E R e T Hws Hbody IH Hsub R2 Hws'.
    apply (typing_sub S E (R2 ++ R) e T Hws' (IH R2 Hws') Hsub).
  - (* let *) intros L T1 T2 e1 e2 E R Hws Hbody1 IH1 Hbody2 IH2 R2 Hws'.
    apply (typing_let L T1 T2 e1 e2 E (R2 ++ R) Hws' (IH1 R2 Hws')).
    intros x Hx.
    apply (IH2 x Hx R2).
    apply (Store__wf_sig_env_weaken_cons E (R2 ++ R) x (bind_typ T1) Hws').
    apply (Dev__wf_sig_wf_env (x ~ bind_typ T1 ++ E) R).
    apply (Store__typing_wf_sig_mut (x ~ bind_typ T1 ++ E) R (open_ee e2 x) T2).
    apply Hbody2. exact Hx.
  - (* box *) intros E R e T Hws Hbody IH R2 Hws'.
    apply (typing_box E (R2 ++ R) e T Hws' (IH R2 Hws')).
  - (* unbox *) intros E R e T Hws Hbody IH R2 Hws'.
    apply (typing_unbox E (R2 ++ R) e T Hws' (IH R2 Hws')).
  - (* set_box *) intros E R e1 e2 T Hws Hbody1 IH1 Hbody2 IH2 R2 Hws'.
    apply (typing_set_box E (R2 ++ R) e1 e2 T Hws'
             (IH1 R2 Hws') (IH2 R2 Hws')).
  - (* ref *) intros E R l T Hwe Hws Hbind R2 Hws'.
    apply (typing_ref E (R2 ++ R) l T Hwe Hws').
    apply Signatures.binds_app_3. exact Hbind.
  - (* seal *) intros E R e T Hbody IH R2 Hws'.
    apply (typing_seal E (R2 ++ R) e T (IH R2 Hws')).
  - (* unbox_readonly *) intros E R e T Hbody IH R2 Hws'.
    apply (typing_unbox_readonly E (R2 ++ R) e T (IH R2 Hws')).
  - (* record *) intros E R r T Hrecord IHrecord R2 Hws'.
    apply (typing_record E (R2 ++ R) r T (IHrecord R2 Hws')).
  - (* record_read *) intros E R e a T Hbody IH R2 Hws'.
    apply (typing_record_read E (R2 ++ R) e a T (IH R2 Hws')).
  - (* record_read_readonly *) intros E R e a T Hbody IH R2 Hws'.
    apply (typing_record_read_readonly E (R2 ++ R) e a T (IH R2 Hws')).
  - (* record_write *) intros E R e1 a e2 T Hbody1 IH1 Hbody2 IH2 R2 Hws'.
    apply (typing_record_write E (R2 ++ R) e1 a e2 T (IH1 R2 Hws')
             (IH2 R2 Hws')).
  - (* record_empty *) intros E R Hwe Hws R2 Hws'.
    apply (typing_record_empty E (R2 ++ R) Hwe Hws').
  - (* record_exp *) intros E R a e r T Tr Hnd Hrec IHrec Hbody IHbody R2 Hws'.
    apply (typing_record_exp E (R2 ++ R) a e r T Tr Hnd
             (IHrec R2 Hws') (IHbody R2 Hws')).
  - (* record_ref *) intros E R a l r T Tr Hnd Hrec IHrec Hbind R2 Hws'.
    apply (typing_record_ref E (R2 ++ R) a l r T Tr Hnd
             (IHrec R2 Hws')).
    apply Signatures.binds_app_3. exact Hbind.
Qed.

Lemma Store__typing_sig_weaken : forall (E : env) (R : sig) (e : exp) (T : typ),
  typing E R e T ->
  forall (R2 : sig), wf_sig E (R2 ++ R) -> typing E (R2 ++ R) e T.
Proof.
  intros E R e T Hty R2 Hws.
  exact (Store__typing_sig_weaken_aux E R e T Hty R2 Hws).
Qed.

(* ================================================================ *)
(* Store lemmas                                                     *)
(* ================================================================ *)

(* A label absent from the store cannot be bound by the signature. *)
Lemma Store__typing_store_notin_dom : forall (E : env) (R : sig) (s : store)
                                      (l : label),
  typing_store E R s ->
  (forall v, ~ LabelMapImpl.MapsTo l v s) ->
  ~ LabelSetImpl.In l (Signatures.dom R).
Proof.
  intros E R s l Hts Hnot Hin.
  apply Signatures.binds_In_inv in Hin.
  destruct Hin as [S Hb]. destruct S as [T].
  destruct (Store__typing_store_dom E R s l T Hts Hb) as [v HM].
  exact (Hnot v HM).
Qed.

(* Generic signature extension for store typings.  The signature grows
   from [R1] to [R2 ++ R1]; the store grows from [s] to [s'].  Old entries
   persist ([Hmono]); every binding in [R2] has a typed entry in [s']
   ([Hext]); and every entry of [s'] is either such a new typed entry or
   an old entry.  Old values are retyped under the extended signature via
   [Store__typing_sig_weaken]. *)
Lemma Store__typing_store_mono_sig : forall (E : env) (R1 R2 : sig)
                                     (s s' : store),
  wf_sig E (R2 ++ R1) ->
  typing_store E R1 s ->
  (forall (l : label) (v : exp),
      LabelMapImpl.MapsTo l v s -> LabelMapImpl.MapsTo l v s') ->
  (forall (l : label) (T : typ),
      Signatures.binds l (bind_sig T) R2 ->
      exists v, LabelMapImpl.MapsTo l v s' /\
                typing E (R2 ++ R1) v T /\ value v) ->
  (forall (l : label) (v : exp),
      LabelMapImpl.MapsTo l v s' ->
      (exists T, Signatures.binds l (bind_sig T) R2 /\
                 typing E (R2 ++ R1) v T /\ value v) \/
      LabelMapImpl.MapsTo l v s) ->
  typing_store E (R2 ++ R1) s'.
Proof.
  intros E R1 R2 s s' Hws Hts Hmono Hext Hdec.
  unfold typing_store in *.
  intro l0. split.
  - intros T0 Hb.
    apply Signatures.binds_app_iff in Hb.
    destruct Hb as [Hb2 | Hb1].
    + exact (Hext l0 T0 Hb2).
    + destruct (Hts l0) as [Hf _].
      destruct (Hf T0 Hb1) as [v [HM [Hty Hval]]].
      exists v. split.
      * exact (Hmono l0 v HM).
      * split.
        -- exact (Store__typing_sig_weaken E R1 v T0 Hty R2 Hws).
        -- exact Hval.
  - intros v HM.
    destruct (Hdec l0 v HM) as [[T0 [Hb2 [Hty Hval]]] | HM0].
    + exists T0. split; [exact Hval |]. split.
      * exact Hty.
      * exact (Signatures.binds_app_2 signature l0 (bind_sig T0) R2 R1 Hb2).
    + destruct (Hts l0) as [_ Hg].
      destruct (Hg v HM0) as [T0 [Hval [Hty Hb]]].
      exists T0. split; [exact Hval |]. split.
      * exact (Store__typing_sig_weaken E R1 v T0 Hty R2 Hws).
      * exact (Signatures.binds_app_3 signature l0 (bind_sig T0) R2 R1 Hb).
Qed.

(* Add one fresh label/entry, extending the signature with its type.
   [wf_typ E T] is genuinely needed: [typing] does not imply [wf_typ]
   (e.g. [typing_abs] accepts an arbitrary annotation), while [wf_sig_typ]
   does require it.  The absence of [l] from the store is what lets us
   derive [l] notin dom R, so no separate disjointness hypothesis is
   needed. *)
Lemma Store__typing_store_add : forall (E : env) (R : sig) (s : store)
                                (l : label) (v : exp) (T : typ),
  wf_typ E T ->
  typing_store E R s ->
  (forall v0, ~ LabelMapImpl.MapsTo l v0 s) ->
  typing E R v T ->
  value v ->
  typing_store E (l ~ bind_sig T ++ R) (LabelMapImpl.add l v s).
Proof.
  intros E R s l v T Hwt Hts Hfresh Hty Hval.
  assert (Hws : wf_sig E R) by
    (exact (Store__typing_wf_sig_mut E R v T Hty)).
  assert (Hnot : ~ LabelSetImpl.In l (Signatures.dom R)) by
    (apply (Store__typing_store_notin_dom E R s l Hts); exact Hfresh).
  assert (Hwf : wf_sig E (l ~ bind_sig T ++ R)) by
    (apply wf_sig_typ; [exact Hws | exact Hwt | exact Hnot]).
  unfold typing_store in *.
  intro l0. split.
  - intros T0 Hb.
    apply (proj1 (Store__binds_sig_cons R l T l0 T0)) in Hb.
    destruct Hb as [[Hl HT] | Hb1].
    + subst l0. subst T0.
      exists v. split.
      * apply LabelMapFacts.add_mapsto_iff. left. split; reflexivity.
      * split.
        -- exact (Store__typing_sig_weaken E R v T Hty (l ~ bind_sig T) Hwf).
        -- exact Hval.
    + assert (Hneq : l <> l0).
      { intro Heq. subst l0.
        apply Hnot.
        exact (Signatures.binds_In signature l (bind_sig T0) R Hb1). }
      destruct (Hts l0) as [Hf _].
      destruct (Hf T0 Hb1) as [v0 [HM [Hty0 Hval0]]].
      exists v0. split.
      * exact (proj2 (@LabelMapFacts.add_neq_mapsto_iff exp s l l0 v v0
                       Hneq) HM).
      * split.
        -- exact (Store__typing_sig_weaken E R v0 T0 Hty0 (l ~ bind_sig T) Hwf).
        -- exact Hval0.
  - intros v0 HM.
    apply (proj1 (LabelMapFacts.add_mapsto_iff (elt := exp)
                    s l l0 v v0)) in HM.
    destruct HM as [[Hl Hveq] | [Hneq HM0]].
    + subst l0. subst v0.
      exists T. split; [exact Hval |]. split.
      * exact (Store__typing_sig_weaken E R v T Hty (l ~ bind_sig T) Hwf).
      * apply (proj2 (Store__binds_sig_cons R l T l T)). left.
        split; reflexivity.
    + destruct (Hts l0) as [_ Hg].
      destruct (Hg v0 HM0) as [T0 [Hval0 [Hty0 Hb0]]].
      exists T0. split; [exact Hval0 |]. split.
      * exact (Store__typing_sig_weaken E R v0 T0 Hty0 (l ~ bind_sig T) Hwf).
      * apply (proj2 (Store__binds_sig_cons R l T l0 T0)). right. exact Hb0.
Qed.

(* Replace/insert the store entry at an already-bound label.  The type
   is forced by the signature (using well-formedness/uniqueness of
   bindings), so the new value simply has to inhabit that type. *)
Lemma Store__typing_store_update : forall (E : env) (R : sig) (s : store)
                                   (l : label) (v : exp) (T : typ),
  typing_store E R s ->
  Signatures.binds l (bind_sig T) R ->
  typing E R v T ->
  value v ->
  typing_store E R (LabelMapImpl.add l v s).
Proof.
  intros E R s l v T Hts Hb Hty Hval.
  assert (Hws : wf_sig E R) by
    (exact (Store__typing_wf_sig_mut E R v T Hty)).
  unfold typing_store in *.
  intro l0. split.
  - intros T0 Hb0.
    destruct (LabelMapFacts.eq_dec l l0) as [Heq | Hneq].
    + subst l0.
      assert (HT : T0 = T) by
        (exact (Store__wf_sig_binds_uniq E R l T0 T Hws Hb0 Hb)).
      subst T0.
      exists v. split.
      * apply LabelMapFacts.add_mapsto_iff. left. split; reflexivity.
      * split; [exact Hty | exact Hval].
    + destruct (Hts l0) as [Hf _].
      destruct (Hf T0 Hb0) as [v0 [HM [Hty0 Hval0]]].
      exists v0. split.
      * exact (proj2 (@LabelMapFacts.add_neq_mapsto_iff exp s l l0 v v0
                       Hneq) HM).
      * split; [exact Hty0 | exact Hval0].
  - intros v0 HM.
    apply LabelMapFacts.add_mapsto_iff in HM.
    destruct HM as [[Heq Hveq] | [Hneq HM0]].
    + subst l0. subst v0.
      exists T. split; [exact Hval |]. split; [exact Hty | exact Hb].
    + destruct (Hts l0) as [_ Hg].
      destruct (Hg v0 HM0) as [T0 [Hval0 [Hty0 Hb0]]].
      exists T0. split; [exact Hval0 |]. split; [exact Hty0 | exact Hb0].
Qed.




(* ================================================================== *)
(* Type substitution for the locally nameless System F<: variant     *)
(* ================================================================== *)

(* Substitute the free type variable X by U in T.  Because type      *)
(* binders are de Bruijn indices there is no capture problem.        *)
Fixpoint SubstTTSnap__subst_tt (X : atom) (U T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar Y => if (Y === X) then U else typ_fvar Y
  | typ_arrow T1 T2 => typ_arrow (SubstTTSnap__subst_tt X U T1) (SubstTTSnap__subst_tt X U T2)
  | typ_all T1 T2 => typ_all (SubstTTSnap__subst_tt X U T1) (SubstTTSnap__subst_tt X U T2)
  | typ_box T1 => typ_box (SubstTTSnap__subst_tt X U T1)
  | typ_mut M T1 => typ_mut M (SubstTTSnap__subst_tt X U T1)
  | typ_int T1 T2 => typ_int (SubstTTSnap__subst_tt X U T1) (SubstTTSnap__subst_tt X U T2)
  | typ_record a T1 => typ_record a (SubstTTSnap__subst_tt X U T1)
  end.

(* Apply SubstTTSnap__subst_tt to every type annotation of an expression.         *)
Fixpoint SubstTTSnap__subst_te (X : atom) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs (SubstTTSnap__subst_tt X U V) (SubstTTSnap__subst_te X U e1)
  | exp_app e1 e2 => exp_app (SubstTTSnap__subst_te X U e1) (SubstTTSnap__subst_te X U e2)
  | exp_tabs V e1 => exp_tabs (SubstTTSnap__subst_tt X U V) (SubstTTSnap__subst_te X U e1)
  | exp_tapp e1 V => exp_tapp (SubstTTSnap__subst_te X U e1) (SubstTTSnap__subst_tt X U V)
  | exp_let e1 e2 => exp_let (SubstTTSnap__subst_te X U e1) (SubstTTSnap__subst_te X U e2)
  | exp_box e => exp_box (SubstTTSnap__subst_te X U e)
  | exp_unbox e => exp_unbox (SubstTTSnap__subst_te X U e)
  | exp_set_box b e => exp_set_box (SubstTTSnap__subst_te X U b) (SubstTTSnap__subst_te X U e)
  | exp_ref l => exp_ref l
  | exp_seal e => exp_seal (SubstTTSnap__subst_te X U e)
  | exp_record r => exp_record (SubstTTSnap__subst_te_record X U r)
  | exp_record_read e a => exp_record_read (SubstTTSnap__subst_te X U e) a
  | exp_record_write e1 a e2 => exp_record_write (SubstTTSnap__subst_te X U e1) a (SubstTTSnap__subst_te X U e2)
  end
with SubstTTSnap__subst_te_record (X : atom) (U : typ) (r : rec_comp) {struct r} : rec_comp :=
  match r with
  | rec_empty => rec_empty
  | rec_exp a e r => rec_exp a (SubstTTSnap__subst_te X U e) (SubstTTSnap__subst_te_record X U r)
  | rec_ref a l r => rec_ref a l (SubstTTSnap__subst_te_record X U r)
  end.

(* Apply SubstTTSnap__subst_tt to the type of a binding, preserving its kind.     *)
Definition SubstTTSnap__subst_binding (X : atom) (U : typ) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (SubstTTSnap__subst_tt X U T)
  | bind_typ T => bind_typ (SubstTTSnap__subst_tt X U T)
  end.

Fixpoint SubstTTSnap__subst_tt_env (X : atom) (U : typ) (E : env) {struct E} : env :=
  match E with
  | nil => nil
  | (x, b) :: E' => (x, SubstTTSnap__subst_binding X U b) :: SubstTTSnap__subst_tt_env X U E'
  end.

(* Free type-variable atoms occurring in the type annotations of an  *)
(* expression / record component.                                    *)
Fixpoint SubstTTSnap__fv_te (e : exp) : atoms :=
  match e with
  | exp_bvar _ => {}
  | exp_fvar _ => {}
  | exp_abs V e1 => Dev__fv_typ V `union` SubstTTSnap__fv_te e1
  | exp_app e1 e2 => SubstTTSnap__fv_te e1 `union` SubstTTSnap__fv_te e2
  | exp_tabs V e1 => Dev__fv_typ V `union` SubstTTSnap__fv_te e1
  | exp_tapp e1 V => SubstTTSnap__fv_te e1 `union` Dev__fv_typ V
  | exp_let e1 e2 => SubstTTSnap__fv_te e1 `union` SubstTTSnap__fv_te e2
  | exp_box e => SubstTTSnap__fv_te e
  | exp_unbox e => SubstTTSnap__fv_te e
  | exp_set_box b e => SubstTTSnap__fv_te b `union` SubstTTSnap__fv_te e
  | exp_ref _ => {}
  | exp_seal e => SubstTTSnap__fv_te e
  | exp_record r => SubstTTSnap__fv_te_record r
  | exp_record_read e _ => SubstTTSnap__fv_te e
  | exp_record_write e1 _ e2 => SubstTTSnap__fv_te e1 `union` SubstTTSnap__fv_te e2
  end
with SubstTTSnap__fv_te_record (r : rec_comp) : atoms :=
  match r with
  | rec_empty => {}
  | rec_exp _ e r => SubstTTSnap__fv_te e `union` SubstTTSnap__fv_te_record r
  | rec_ref _ _ r => SubstTTSnap__fv_te_record r
  end.

(* ------------------------------------------------------------------ *)
(* Simple commutation / identity facts                                *)
(* ------------------------------------------------------------------ *)

Lemma SubstTTSnap__subst_tt_fvar_eq : forall (X : atom) U,
  SubstTTSnap__subst_tt X U (typ_fvar X) = U.
Proof.
  intros. simpl. destruct (X === X) as [Heq|Hneq].
  - reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

Lemma SubstTTSnap__subst_tt_fvar_neq : forall (X Y : atom) U,
  Y <> X -> SubstTTSnap__subst_tt X U (typ_fvar Y) = typ_fvar Y.
Proof.
  intros X Y U Hneq. simpl.
  destruct (Y === X) as [Heq|Hneq'].
  - exfalso. apply Hneq. exact Heq.
  - reflexivity.
Qed.

Lemma SubstTTSnap__subst_tt_id : forall (X : atom) U T,
  X `notin` Dev__fv_typ T -> SubstTTSnap__subst_tt X U T = T.
Proof.
  intros X U T. induction T; simpl; intros H.
  - reflexivity.
  - reflexivity.
  - destruct (a === X) as [Heq|Hneq].
    + subst a. exfalso. apply (notin_singleton_1 X X H). reflexivity.
    + reflexivity.
  - pose proof (notin_union_1 X _ _ H) as H1.
    pose proof (notin_union_2 X _ _ H) as H2.
    rewrite (IHT1 H1). rewrite (IHT2 H2). reflexivity.
  - pose proof (notin_union_1 X _ _ H) as H1.
    pose proof (notin_union_2 X _ _ H) as H2.
    rewrite (IHT1 H1). rewrite (IHT2 H2). reflexivity.
  - rewrite IHT by assumption. reflexivity.
  - rewrite IHT by assumption. reflexivity.
  - pose proof (notin_union_1 X _ _ H) as H1.
    pose proof (notin_union_2 X _ _ H) as H2.
    rewrite (IHT1 H1). rewrite (IHT2 H2). reflexivity.
  - rewrite IHT by assumption. reflexivity.
Qed.

Lemma SubstTTSnap__subst_tt_bvar : forall (X : atom) U J,
  SubstTTSnap__subst_tt X U (typ_bvar J) = typ_bvar J.
Proof. reflexivity. Qed.

(* A syntactic closedness predicate sufficient for all the opening   *)
(* commutations below.                                               *)
Fixpoint SubstTTSnap__no_bvar (T : typ) : Prop :=
  match T with
  | typ_top => True
  | typ_bvar _ => False
  | typ_fvar _ => True
  | typ_arrow T1 T2 => SubstTTSnap__no_bvar T1 /\ SubstTTSnap__no_bvar T2
  | typ_all T1 T2 => SubstTTSnap__no_bvar T1 /\ SubstTTSnap__no_bvar T2
  | typ_box T1 => SubstTTSnap__no_bvar T1
  | typ_mut _ T1 => SubstTTSnap__no_bvar T1
  | typ_int T1 T2 => SubstTTSnap__no_bvar T1 /\ SubstTTSnap__no_bvar T2
  | typ_record _ T1 => SubstTTSnap__no_bvar T1
  end.

Lemma SubstTTSnap__no_bvar_open_tt : forall (V : typ), SubstTTSnap__no_bvar V ->
  forall K (U : typ), open_tt_rec K U V = V.
Proof.
  intros V. induction V; intros H K Y; simpl in *.
  - reflexivity.
  - destruct H.
  - reflexivity.
  - destruct H as [H1 H2]. rewrite (IHV1 H1). rewrite (IHV2 H2). reflexivity.
  - destruct H as [H1 H2]. rewrite (IHV1 H1). rewrite (IHV2 H2). reflexivity.
  - rewrite (IHV H). reflexivity.
  - rewrite (IHV H). reflexivity.
  - destruct H as [H1 H2]. rewrite (IHV1 H1). rewrite (IHV2 H2). reflexivity.
  - rewrite (IHV H). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Opening and substitution commute (both directions)                 *)
(* ------------------------------------------------------------------ *)

Lemma SubstTTSnap__open_tt_rec_subst_comm : forall K (T : typ) (X : atom) (V : typ) (Y : atom),
  SubstTTSnap__no_bvar V -> Y <> X ->
  open_tt_rec K Y (SubstTTSnap__subst_tt X V T) = SubstTTSnap__subst_tt X V (open_tt_rec K Y T).
Proof.
  intros K T. revert K. induction T; intros K X V Y Hb Hneq; simpl.
  - reflexivity.
  - (* bvar *) destruct (K == n) eqn:E.
    + rewrite SubstTTSnap__subst_tt_fvar_neq; [reflexivity | assumption].
    + reflexivity.
  - (* fvar *) destruct (a === X) as [Heq|Hneq'].
    + subst a. rewrite (SubstTTSnap__no_bvar_open_tt V Hb K Y). reflexivity.
    + reflexivity.
  - rewrite (IHT1 K X V Y Hb Hneq). rewrite (IHT2 K X V Y Hb Hneq). reflexivity.
  - rewrite (IHT1 K X V Y Hb Hneq). rewrite (IHT2 (S K) X V Y Hb Hneq). reflexivity.
  - rewrite (IHT K X V Y Hb Hneq). reflexivity.
  - rewrite (IHT K X V Y Hb Hneq). reflexivity.
  - rewrite (IHT1 K X V Y Hb Hneq). rewrite (IHT2 K X V Y Hb Hneq). reflexivity.
  - rewrite (IHT K X V Y Hb Hneq). reflexivity.
Qed.

(* Substuting T for the opened variable and also substituting inside T. *)
Lemma SubstTTSnap__open_tt_rec_subst2 : forall K (T2 : typ) (X : atom) (V : typ) (T : typ),
  SubstTTSnap__no_bvar V ->
  SubstTTSnap__subst_tt X V (open_tt_rec K T T2)
  = open_tt_rec K (SubstTTSnap__subst_tt X V T) (SubstTTSnap__subst_tt X V T2).
Proof.
  intros K T2. revert K. induction T2; intros K X V T Hb; simpl.
  - reflexivity.
  - destruct (K == n) eqn:E; reflexivity.
  - destruct (a === X) as [Heq|Hneq].
    + subst a. rewrite (SubstTTSnap__no_bvar_open_tt V Hb K (SubstTTSnap__subst_tt X V T)). reflexivity.
    + reflexivity.
  - rewrite IHT2_1; auto. rewrite IHT2_2; auto.
  - rewrite IHT2_1; auto. rewrite IHT2_2; auto.
  - rewrite IHT2; auto.
  - rewrite IHT2; auto.
  - rewrite IHT2_1; auto. rewrite IHT2_2; auto.
  - rewrite IHT2; auto.
Qed.

(* The type-level version of the requested open/subst identity.      *)
Lemma SubstTTSnap__open_tt_rec_subst_tt : forall K (T : typ) (X : atom) U,
  X `notin` Dev__fv_typ T ->
  open_tt_rec K U T = SubstTTSnap__subst_tt X U (open_tt_rec K X T).
Proof.
  intros K T. revert K. induction T; intros K X U H; simpl in *.
  - reflexivity.
  - destruct (K == n) eqn:E.
    + rewrite SubstTTSnap__subst_tt_fvar_eq. reflexivity.
    + reflexivity.
  - destruct (a === X) as [Heq|Hneq].
    + subst a. exfalso. apply (notin_singleton_1 X X H). reflexivity.
    + reflexivity.
  - pose proof (notin_union_1 X _ _ H) as H1.
    pose proof (notin_union_2 X _ _ H) as H2.
    rewrite (IHT1 K X U H1). rewrite (IHT2 K X U H2). reflexivity.
  - pose proof (notin_union_1 X _ _ H) as H1.
    pose proof (notin_union_2 X _ _ H) as H2.
    rewrite (IHT1 K X U H1). rewrite (IHT2 (S K) X U H2). reflexivity.
  - rewrite (IHT K X U H). reflexivity.
  - rewrite (IHT K X U H). reflexivity.
  - pose proof (notin_union_1 X _ _ H) as H1.
    pose proof (notin_union_2 X _ _ H) as H2.
    rewrite (IHT1 K X U H1). rewrite (IHT2 K X U H2). reflexivity.
  - rewrite (IHT K X U H). reflexivity.
Qed.

Lemma SubstTTSnap__open_tt_subst_tt : forall (T : typ) (X : atom) U,
  X `notin` Dev__fv_typ T ->
  open_tt T U = SubstTTSnap__subst_tt X U (open_tt T X).
Proof.
  intros. unfold open_tt. apply SubstTTSnap__open_tt_rec_subst_tt. assumption.
Qed.

(* Expression (and record component) version of open/subst identity. *)
Fixpoint SubstTTSnap__open_te_rec_subst_te (e : exp) {struct e} :
  forall K (X : atom) V,
    X `notin` SubstTTSnap__fv_te e ->
    open_te_rec K V e = SubstTTSnap__subst_te X V (open_te_rec K X e)
with SubstTTSnap__open_te_record_rec_subst_te (r : rec_comp) {struct r} :
  forall K (X : atom) V,
    X `notin` SubstTTSnap__fv_te_record r ->
    open_te_record_rec K V r = SubstTTSnap__subst_te_record X V (open_te_record_rec K X r).
Proof.
  - destruct e; intros K X V H; simpl in *; try reflexivity.
    + (* abs *) pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTTSnap__open_tt_rec_subst_tt K t X V H1).
      rewrite (SubstTTSnap__open_te_rec_subst_te e K X V H2). reflexivity.
    + pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTTSnap__open_te_rec_subst_te e1 K X V H1).
      rewrite (SubstTTSnap__open_te_rec_subst_te e2 K X V H2). reflexivity.
    + (* tabs *) pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTTSnap__open_tt_rec_subst_tt K t X V H1).
      rewrite (SubstTTSnap__open_te_rec_subst_te e (S K) X V H2). reflexivity.
    + pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTTSnap__open_te_rec_subst_te e K X V H1).
      rewrite (SubstTTSnap__open_tt_rec_subst_tt K t X V H2). reflexivity.
    + pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTTSnap__open_te_rec_subst_te e1 K X V H1).
      rewrite (SubstTTSnap__open_te_rec_subst_te e2 K X V H2). reflexivity.
    + simpl. rewrite (SubstTTSnap__open_te_rec_subst_te e K X V H). reflexivity.
    + simpl. rewrite (SubstTTSnap__open_te_rec_subst_te e K X V H). reflexivity.
    + pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTTSnap__open_te_rec_subst_te e1 K X V H1).
      rewrite (SubstTTSnap__open_te_rec_subst_te e2 K X V H2). reflexivity.
    + simpl. rewrite (SubstTTSnap__open_te_rec_subst_te e K X V H). reflexivity.
    + simpl. rewrite (SubstTTSnap__open_te_record_rec_subst_te r K X V H). reflexivity.
    + simpl. rewrite (SubstTTSnap__open_te_rec_subst_te e K X V H). reflexivity.
    + pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTTSnap__open_te_rec_subst_te e1 K X V H1).
      rewrite (SubstTTSnap__open_te_rec_subst_te e2 K X V H2). reflexivity.
  - destruct r; intros K X V H; simpl in *.
    + reflexivity.
    + pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTTSnap__open_te_rec_subst_te e K X V H1).
      rewrite (SubstTTSnap__open_te_record_rec_subst_te r K X V H2). reflexivity.
    + simpl. rewrite (SubstTTSnap__open_te_record_rec_subst_te r K X V H). reflexivity.
Qed.

Lemma SubstTTSnap__open_te_subst_te : forall (e : exp) (X : atom) U,
  X `notin` SubstTTSnap__fv_te e ->
  open_te e U = SubstTTSnap__subst_te X U (open_te e X).
Proof.
  intros. unfold open_te. apply SubstTTSnap__open_te_rec_subst_te. assumption.
Qed.

Lemma SubstTTSnap__open_te_record_subst_te : forall (r : rec_comp) (X : atom) U,
  X `notin` SubstTTSnap__fv_te_record r ->
  open_te_record_rec 0 U r = SubstTTSnap__subst_te_record X U (open_te_record_rec 0 X r).
Proof. intros. apply SubstTTSnap__open_te_record_rec_subst_te. assumption. Qed.

(* Expression version of the commutation used when going under a      *)
(* type-binder in the typing substitution induction.                  *)
Fixpoint SubstTTSnap__open_te_rec_comm (e : exp) {struct e} :
  forall K (X : atom) V (Y : atom),
    SubstTTSnap__no_bvar V -> Y <> X ->
    open_te_rec K Y (SubstTTSnap__subst_te X V e) = SubstTTSnap__subst_te X V (open_te_rec K Y e)
with SubstTTSnap__open_te_record_rec_comm (r : rec_comp) {struct r} :
  forall K (X : atom) V (Y : atom),
    SubstTTSnap__no_bvar V -> Y <> X ->
    open_te_record_rec K Y (SubstTTSnap__subst_te_record X V r)
    = SubstTTSnap__subst_te_record X V (open_te_record_rec K Y r).
Proof.
  - destruct e; intros K X V Y Hb Hneq; simpl; try reflexivity.
    + rewrite (SubstTTSnap__open_tt_rec_subst_comm K t X V Y Hb Hneq).
      rewrite (SubstTTSnap__open_te_rec_comm e K X V Y Hb Hneq). reflexivity.
    + rewrite (SubstTTSnap__open_te_rec_comm e1 K X V Y Hb Hneq).
      rewrite (SubstTTSnap__open_te_rec_comm e2 K X V Y Hb Hneq). reflexivity.
    + rewrite (SubstTTSnap__open_tt_rec_subst_comm K t X V Y Hb Hneq).
      rewrite (SubstTTSnap__open_te_rec_comm e (S K) X V Y Hb Hneq). reflexivity.
    + rewrite (SubstTTSnap__open_te_rec_comm e K X V Y Hb Hneq).
      rewrite (SubstTTSnap__open_tt_rec_subst_comm K t X V Y Hb Hneq). reflexivity.
    + rewrite (SubstTTSnap__open_te_rec_comm e1 K X V Y Hb Hneq).
      rewrite (SubstTTSnap__open_te_rec_comm e2 K X V Y Hb Hneq). reflexivity.
    + rewrite (SubstTTSnap__open_te_rec_comm e K X V Y Hb Hneq). reflexivity.
    + rewrite (SubstTTSnap__open_te_rec_comm e K X V Y Hb Hneq). reflexivity.
    + rewrite (SubstTTSnap__open_te_rec_comm e1 K X V Y Hb Hneq).
      rewrite (SubstTTSnap__open_te_rec_comm e2 K X V Y Hb Hneq). reflexivity.
    + rewrite (SubstTTSnap__open_te_rec_comm e K X V Y Hb Hneq). reflexivity.
    + rewrite (SubstTTSnap__open_te_record_rec_comm r K X V Y Hb Hneq). reflexivity.
    + rewrite (SubstTTSnap__open_te_rec_comm e K X V Y Hb Hneq). reflexivity.
    + rewrite (SubstTTSnap__open_te_rec_comm e1 K X V Y Hb Hneq).
      rewrite (SubstTTSnap__open_te_rec_comm e2 K X V Y Hb Hneq). reflexivity.
  - destruct r; intros K X V Y Hb Hneq; simpl.
    + reflexivity.
    + rewrite (SubstTTSnap__open_te_rec_comm e K X V Y Hb Hneq).
      rewrite (SubstTTSnap__open_te_record_rec_comm r K X V Y Hb Hneq). reflexivity.
    + rewrite (SubstTTSnap__open_te_record_rec_comm r K X V Y Hb Hneq). reflexivity.
Qed.





Lemma TypeOpen__open_tt_fvar_comm : forall K1 K2 (p q : atom) T,
  K1 <> K2 ->
  open_tt_rec K1 (typ_fvar p) (open_tt_rec K2 (typ_fvar q) T)
  = open_tt_rec K2 (typ_fvar q) (open_tt_rec K1 (typ_fvar p) T).
Proof.
  intros KA KB p q T. revert KA KB p q. induction T; intros KA KB p q Hne; simpl.
  - reflexivity.
  - cbn [open_tt_rec].
    destruct (KB == n) as [eB | eB]; destruct (KA == n) as [eA | eA].
    + exfalso. apply Hne. transitivity n; [exact eA | symmetry; exact eB].
    + subst n. cbn [open_tt_rec]. destruct (KA == KB) as [c | c].
      * exfalso. apply eA. exact c.
      * destruct (KB == KB) as [c2 | c2]; [reflexivity | exfalso; apply c2; reflexivity].
    + subst n. cbn [open_tt_rec]. destruct (KB == KA) as [c | c].
      * exfalso. apply Hne. symmetry. exact c.
      * destruct (KA == KA) as [c2 | c2]; [reflexivity | exfalso; apply c2; reflexivity].
    + cbn [open_tt_rec]. destruct (KA == n) as [c | c].
      * exfalso. apply eA. exact c.
      * destruct (KB == n) as [c2 | c2].
        -- exfalso. apply eB. exact c2.
        -- reflexivity.
  - reflexivity.
  - rewrite IHT1; auto. rewrite IHT2; auto.
  - rewrite IHT1; auto. rewrite IHT2; auto.
  - rewrite IHT; auto.
  - rewrite IHT; auto.
  - rewrite IHT1; auto. rewrite IHT2; auto.
  - rewrite IHT; auto.
Qed.




Fixpoint TypeOpen2__close_tt_rec (K : nat) (Y : atom) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar Z => if Z == Y then typ_bvar K else typ_fvar Z
  | typ_arrow T1 T2 => typ_arrow (TypeOpen2__close_tt_rec K Y T1) (TypeOpen2__close_tt_rec K Y T2)
  | typ_all T1 T2 => typ_all (TypeOpen2__close_tt_rec K Y T1) (TypeOpen2__close_tt_rec (S K) Y T2)
  | typ_box T1 => typ_box (TypeOpen2__close_tt_rec K Y T1)
  | typ_mut M T1 => typ_mut M (TypeOpen2__close_tt_rec K Y T1)
  | typ_int T1 T2 => typ_int (TypeOpen2__close_tt_rec K Y T1) (TypeOpen2__close_tt_rec K Y T2)
  | typ_record a T1 => typ_record a (TypeOpen2__close_tt_rec K Y T1)
  end.

Definition TypeOpen2__close_tt Y T := TypeOpen2__close_tt_rec 0 Y T.

Lemma TypeOpen2__close_tt_open : forall K (Y : atom) T,
  Y `notin` Dev__fv_typ T ->
  TypeOpen2__close_tt_rec K Y (open_tt_rec K (typ_fvar Y) T) = T.
Proof.
  intros K Y T. revert K Y. induction T; intros K0 Y0 Hnot; simpl in *.
  - reflexivity.
  - destruct (K0 == n) as [e | e].
    + assert (Heq : K0 = n) by exact e. subst n. simpl.
      destruct (Y0 == Y0) as [c | c]; [reflexivity | exfalso; apply c; reflexivity].
    + reflexivity.
  - destruct (a == Y0) as [c | c].
    + simpl in Hnot. exfalso. apply Hnot. rewrite singleton_iff. exact c.
    + reflexivity.
  - rewrite IHT1; auto. rewrite IHT2; auto.
  - rewrite IHT1; auto. rewrite IHT2; auto.
  - rewrite IHT; auto.
  - rewrite IHT; auto.
  - rewrite IHT1; auto. rewrite IHT2; auto.
  - rewrite IHT; auto.
Qed.

Lemma TypeOpen2__notin_fv_open_fvar : forall (T : typ) K (Y W : atom),
  W `notin` Dev__fv_typ T -> W <> Y -> W `notin` Dev__fv_typ (open_tt_rec K (typ_fvar Y) T).
Proof. intros. eapply Dev__fv_typ_open_tt_fvar; eauto. Qed.

Lemma TypeOpen2__open_tt_fvar_inj : forall (X : atom) A B,
  X `notin` Dev__fv_typ A -> X `notin` Dev__fv_typ B ->
  open_tt_rec 0 (typ_fvar X) A = open_tt_rec 0 (typ_fvar X) B -> A = B.
Proof.
  intros X A B HA HB Heq.
  destruct (atom_fresh (Dev__fv_typ A `union` Dev__fv_typ B `union` {{ X }})) as [Y HY].
  assert (HYB : Y `notin` Dev__fv_typ B).
  { apply notin_union_2 in HY. apply notin_union_1 in HY. assumption. }
  assert (HYA : Y `notin` Dev__fv_typ A).
  { apply notin_union_1 in HY. assumption. }
  assert (HYX : Y <> X).
  { apply notin_union_2 in HY. apply notin_union_2 in HY. assert (Hny : Y `notin` {{ X }}) by assumption.
    apply notin_singleton_1' in Hny. symmetry. exact Hny. }
  assert (E1 : open_tt_rec 0 (typ_fvar Y) A
               = SubstTTSnap__subst_tt X (typ_fvar Y) (open_tt_rec 0 (typ_fvar X) A)).
  { apply (SubstTTSnap__open_tt_rec_subst_tt 0 A X (typ_fvar Y) HA). }
  assert (E2 : open_tt_rec 0 (typ_fvar Y) B
               = SubstTTSnap__subst_tt X (typ_fvar Y) (open_tt_rec 0 (typ_fvar X) B)).
  { apply (SubstTTSnap__open_tt_rec_subst_tt 0 B X (typ_fvar Y) HB). }
  assert (E : open_tt_rec 0 (typ_fvar Y) A = open_tt_rec 0 (typ_fvar Y) B).
  { rewrite E1. rewrite E2. rewrite Heq. reflexivity. }
  assert (C1 := TypeOpen2__close_tt_open 0 Y A HYA).
  assert (C2 := TypeOpen2__close_tt_open 0 Y B HYB).
  rewrite <- C1. rewrite <- C2. rewrite E. reflexivity.
Qed.

Lemma TypeOpen2__open_tt_rec_id_type : forall (T : typ),
  type T -> forall K (Y : atom), open_tt_rec K (typ_fvar Y) T = T.
Proof.
  intros T HT.
  induction HT as [ | X | T1 T2 H1 IH1 H2 IH2 | L T1 T2 H1 IH1 H0 IH0
                  | T1 H1 IH1 | T1 H1 IH1 | T1 T2 H1 IH1 H2 IH2 | a T1 H1 IH1 ];
  intros K YY; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
  - rewrite IH1.
    destruct (atom_fresh (L `union` Dev__fv_typ T2 `union` {{ YY }})) as [Z HZ].
    assert (HZL : Z `notin` L).
    { apply notin_union_1 in HZ. assumption. }
    assert (HZT2 : Z `notin` Dev__fv_typ T2).
    { apply notin_union_2 in HZ. apply notin_union_1 in HZ. assumption. }
    assert (HZY : Z <> YY).
    { apply notin_union_2 in HZ. apply notin_union_2 in HZ.
      assert (Hny : Z `notin` {{ YY }}) by assumption.
      apply notin_singleton_1' in Hny. symmetry. exact Hny. }
    assert (H0SK : 0 <> S K) by (intro e; inversion e).
    assert (HIH := IH0 Z HZL (S K) YY).
    assert (Hcomm : open_tt_rec 0 Z (open_tt_rec (S K) YY T2)
                  = open_tt_rec (S K) YY (open_tt T2 Z)).
    { apply (TypeOpen__open_tt_fvar_comm 0 (S K) Z YY T2 H0SK). }
    rewrite <- Hcomm in HIH.
    assert (HZI : Z `notin` Dev__fv_typ (open_tt_rec (S K) (typ_fvar YY) T2)).
    { apply TypeOpen2__notin_fv_open_fvar; auto. }
    assert (Hinj := TypeOpen2__open_tt_fvar_inj Z (open_tt_rec (S K) (typ_fvar YY) T2) T2 HZI HZT2).
    apply Hinj in HIH.
    rewrite HIH. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
  - rewrite IH1. reflexivity.
Qed.

Lemma TypeOpen2__open_tt_subst_comm_type : forall (T : typ) X (V : typ) Y K,
  type V -> Y <> X ->
  open_tt_rec K (typ_fvar Y) (SubstTTSnap__subst_tt X V T)
  = SubstTTSnap__subst_tt X V (open_tt_rec K (typ_fvar Y) T).
Proof.
  induction T; intros X V Y K HV HYX; simpl.
  - reflexivity.
  - destruct (K == n) as [e | e].
    + subst n. simpl. destruct (Y == X) as [c | c].
      * exfalso. apply HYX. exact c.
      * reflexivity.
    + reflexivity.
  - destruct (a == X) as [e | e].
    + subst a. destruct (X == X) as [c | c]; [| exfalso; apply c; reflexivity].
      cbn [SubstTTSnap__subst_tt open_tt_rec]. apply TypeOpen2__open_tt_rec_id_type; assumption.
    + reflexivity.
  - rewrite IHT1; auto. rewrite IHT2; auto.
  - rewrite IHT1; auto. rewrite IHT2; auto.
  - rewrite IHT; auto.
  - rewrite IHT; auto.
  - rewrite IHT1; auto. rewrite IHT2; auto.
  - rewrite IHT; auto.
Qed.




Lemma WfSubst__binds_remove_mid : forall (E1 E2 : env) X U Y b,
  Y <> X ->
  (binds Y b (E1 ++ (X, bind_sub U) :: E2) <-> binds Y b (E1 ++ E2)).
Proof.
  intros E1. induction E1 as [| [Z c] E1 IH]; intros E2 X U Y b Hne; simpl.
  - split; intros Hz.
    + destruct Hz as [Heq | Hin].
      * inversion Heq. subst. contradiction.
      * assumption.
    + right. assumption.
  - split; intros Hz.
    + destruct Hz as [Heq | Hin].
      * left. assumption.
      * right. apply (proj1 (IH E2 X U Y b Hne)). assumption.
    + destruct Hz as [Heq | Hin].
      * left. assumption.
      * right. apply (proj2 (IH E2 X U Y b Hne)). assumption.
Qed.

Lemma WfSubst__binds_subst_env_l : forall (E : env) X V Y U,
  Y <> X -> binds Y (bind_sub U) E ->
  exists U', binds Y (bind_sub U') (SubstTTSnap__subst_tt_env X V E).
Proof.
  intros E. induction E as [| [Z c] E IH]; intros X V Y U Hne Hb; simpl in *.
  - inversion Hb.
  - destruct Hb as [Heq | Hin].
    + injection Heq as HY HU. subst.
      exists (SubstTTSnap__subst_tt X V U). left. reflexivity.
    + destruct (IH X V Y U Hne Hin) as [U' HU'].
      destruct c; simpl; exists U'; right; assumption.
Qed.

Lemma WfSubst__wf_typ_subst_tt_gen : forall (E1 : env) X U (E2 : env) T,
  X `notin` dom E1 -> X `notin` dom E2 ->
  wf_typ (E1 ++ X ~ bind_sub U ++ E2) T ->
  forall V, type V -> wf_typ (SubstTTSnap__subst_tt_env X V E1 ++ E2) V ->
  wf_typ (SubstTTSnap__subst_tt_env X V E1 ++ E2) (SubstTTSnap__subst_tt X V T).
Proof.
  intros E1 X U E2 T Hnd1 Hnd2 H.
  remember (E1 ++ X ~ bind_sub U ++ E2) as E0 eqn:He.
  revert E1 X U E2 He Hnd1 Hnd2.
  induction H as [ E0
                 | U0 E0 Y Hb
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | L E0 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 H1 IH1
                 | E0 T1 H1 IH1
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 H1 IH1 ];
  intros E1 X U E2 He Hnd1 Hnd2 V HTV HV.
  - simpl. constructor.
  - subst E0. destruct (Y == X) as [Heq | Hneq].
    + subst Y. rewrite SubstTTSnap__subst_tt_fvar_eq. assumption.
    + rewrite SubstTTSnap__subst_tt_fvar_neq; auto.
      assert (Hb' : binds Y (bind_sub U0) (E1 ++ E2)).
      { apply (proj1 (WfSubst__binds_remove_mid E1 E2 X U Y (bind_sub U0) Hneq)). assumption. }
      apply in_app_or in Hb'. destruct Hb' as [Hin1 | Hin2].
      * destruct (WfSubst__binds_subst_env_l E1 X V Y U0 Hneq Hin1) as [U' HU'].
        apply (wf_typ_var U' (SubstTTSnap__subst_tt_env X V E1 ++ E2) Y).
        apply Dev__binds_app_1. assumption.
      * apply (wf_typ_var U0 (SubstTTSnap__subst_tt_env X V E1 ++ E2) Y).
        apply Dev__binds_app_2. assumption.
  - simpl. constructor;
    [apply (IH1 E1 X U E2 He Hnd1 Hnd2 V HTV HV) |
     apply (IH2 E1 X U E2 He Hnd1 Hnd2 V HTV HV)].
  - subst E0.
    change (wf_typ (SubstTTSnap__subst_tt_env X V E1 ++ E2)
              (typ_all (SubstTTSnap__subst_tt X V T1) (SubstTTSnap__subst_tt X V T2))).
    apply wf_typ_all with (L := L `union` {{ X }}).
    + apply (IH1 E1 X U E2 eq_refl Hnd1 Hnd2 V HTV HV).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (apply notin_union_1 in HY; assumption).
      assert (HYX : Y <> X).
      { assert (Hny : Y `notin` {{ X }}) by (apply notin_union_2 in HY; assumption).
        apply notin_singleton_1' in Hny. symmetry. exact Hny. }
      assert (HndY1 : X `notin` dom ((Y, bind_sub T1) :: E1)).
      { simpl. rewrite add_iff. intros [Heq | Hin].
        - apply HYX. exact Heq.
        - apply Hnd1. exact Hin. }
      assert (HV' : wf_typ (SubstTTSnap__subst_tt_env X V ((Y, bind_sub T1) :: E1) ++ E2) V).
      { simpl. apply Dev__wf_typ_weaken_cons1 with (X := Y) (b := bind_sub (SubstTTSnap__subst_tt X V T1)).
        exact HV. }
      assert (Hbody : wf_typ (SubstTTSnap__subst_tt_env X V ((Y, bind_sub T1) :: E1) ++ E2)
                (SubstTTSnap__subst_tt X V (open_tt_rec 0 (typ_fvar Y) T2))).
      { apply (IH0 Y HYL ((Y, bind_sub T1) :: E1) X U E2 eq_refl HndY1 Hnd2 V HTV HV'). }
      assert (Hcomm : open_tt_rec 0 (typ_fvar Y) (SubstTTSnap__subst_tt X V T2)
                    = SubstTTSnap__subst_tt X V (open_tt_rec 0 (typ_fvar Y) T2)).
      { apply (TypeOpen2__open_tt_subst_comm_type T2 X V Y 0 HTV HYX). }
      rewrite <- Hcomm in Hbody. exact Hbody.
  - simpl. apply wf_typ_box. apply (IH1 E1 X U E2 He Hnd1 Hnd2 V HTV HV).
  - simpl. apply wf_typ_readonly. apply (IH1 E1 X U E2 He Hnd1 Hnd2 V HTV HV).
  - simpl. apply wf_typ_intersect;
    [apply (IH1 E1 X U E2 He Hnd1 Hnd2 V HTV HV) |
     apply (IH2 E1 X U E2 He Hnd1 Hnd2 V HTV HV)].
  - simpl. apply wf_typ_record. apply (IH1 E1 X U E2 He Hnd1 Hnd2 V HTV HV).
Qed.

Lemma WfSubst__wf_typ_subst_tt : forall (E : env) X U T,
  X `notin` dom E ->
  wf_typ (X ~ bind_sub U ++ E) T ->
  forall V, type V -> wf_typ E V ->
  wf_typ E (SubstTTSnap__subst_tt X V T).
Proof.
  intros E X U T Hnd H V HTV HV.
  change E with (SubstTTSnap__subst_tt_env X V (@nil (atom * binding)) ++ E).
  eapply WfSubst__wf_typ_subst_tt_gen; eauto.
Qed.




Lemma WfTyping__typing_wf_typ : forall (E : env) (R : sig) e T,
  typing E R e T -> wf_typ E T
with WfTyping__typing_record_comp_wf_typ : forall (E : env) (R : sig) r T,
  typing_record_comp E R r T -> wf_typ E T.
Proof.
  - intros E R e T Hty. induction Hty as
      [ E0 R0 x T0 Hwe Hws Hb
      | L E0 R0 V e1 T1 Hws Hbody IHbody
      | T1 E0 R0 e1 e2 T2 Hws H1 IH1 H2 IH2
      | L E0 R0 V e1 T1 Hws Hbody IHbody
      | T1 E0 R0 e1 T T2 Hws H1 IH1 Hsub
      | S E0 R0 e T Hws H1 IH1 Hsub
      | L T1 T2 e1 e2 E0 R0 Hws H1 IH1 Hbody IHbody
      | E0 R0 e T Hws H1 IH1
      | E0 R0 e T Hws H1 IH1
      | E0 R0 e1 e2 T Hws H1 IH1 H2 IH2
      | E0 R0 l T Hwe Hws Hb
      | E0 R0 e T H1 IH1
      | E0 R0 e T H1 IH1
      | E0 R0 r T Hr IHr
      | E0 R0 e a T H1 IH1
      | E0 R0 e a T H1 IH1
      | E0 R0 e1 a e2 T H1 IH1 H2 IH2 ].
    + apply (Dev__wf_env_binds_typ _ Hwe x T0 Hb).
    + destruct (atom_fresh (L `union` dom E0 `union` Dev__fv_typ T1)) as [x Hx].
      assert (HxL : x `notin` L) by (apply notin_union_1 in Hx; assumption).
      assert (HxE : x `notin` dom E0) by (apply notin_union_2 in Hx; apply notin_union_1 in Hx; assumption).
      assert (HxT : x `notin` Dev__fv_typ T1) by (apply notin_union_2 in Hx; apply notin_union_2 in Hx; assumption).
      assert (Hwb : wf_typ (x ~ bind_typ V ++ E0) T1) by (apply IHbody; assumption).
      assert (Hwenv : wf_env (x ~ bind_typ V ++ E0))
        by (apply (Dev__wf_sig_wf_env (x ~ bind_typ V ++ E0) R0);
            apply (MyWork__typing_wf_sig (x ~ bind_typ V ++ E0) R0 (open_ee e1 x) T1);
            apply Hbody; assumption).
      destruct (Dev__wf_env_cons_bind_typ _ _ _ Hwenv) as [HweE HwV].
      assert (HwT1 : wf_typ E0 T1).
      { eapply Dev__wf_typ_remove_bind_typ; eauto. intros y b; reflexivity. }
      apply wf_typ_arrow; assumption.
    + apply (proj2 (Dev__wf_typ_inv_arrow _ _ _ IH1)).
    + destruct (atom_fresh (L `union` dom E0)) as [X HX].
      assert (HXL : X `notin` L) by (apply notin_union_1 in HX; assumption).
      assert (HXE : X `notin` dom E0) by (apply notin_union_2 in HX; assumption).
      assert (Hwenv : wf_env (X ~ bind_sub V ++ E0))
        by (apply (Dev__wf_sig_wf_env (X ~ bind_sub V ++ E0) R0);
            apply (MyWork__typing_wf_sig (X ~ bind_sub V ++ E0) R0 (open_te e1 X) (open_tt T1 X));
            apply Hbody; assumption).
      destruct (Dev__wf_env_cons_bind_sub _ _ _ Hwenv) as [HweE HwV].
      apply wf_typ_all with (L := L).
      * exact HwV.
      * intros X0 HX0. apply IHbody. assumption.
    + destruct (Dev__wf_typ_inv_all _ _ _ IH1) as [L0 [HwT1 Hwbody]].
      assert (Hwe : wf_env E0) by (apply Dev__wf_sig_wf_env with (R := R0); assumption).
      assert (HwT : wf_typ E0 T)
        by (apply (Dev__sub_wf_source E0 T T1 Hwe HwT1 Hsub)).
      destruct (atom_fresh (L0 `union` dom E0 `union` Dev__fv_typ T2)) as [X HX].
      assert (HXL0 : X `notin` L0) by (apply notin_union_1 in HX; assumption).
      assert (HXE : X `notin` dom E0) by (apply notin_union_2 in HX; apply notin_union_1 in HX; assumption).
      assert (HXT2 : X `notin` Dev__fv_typ T2) by (apply notin_union_2 in HX; apply notin_union_2 in HX; assumption).
      assert (HbodyX : wf_typ (X ~ bind_sub T1 ++ E0) (open_tt T2 X)) by (apply Hwbody; assumption).
      pose (Hres := WfSubst__wf_typ_subst_tt E0 X T1 (open_tt T2 X) HXE HbodyX T (MyWork__wf_typ_type _ _ HwT) HwT).
      assert (Heq : open_tt T2 T = SubstTTSnap__subst_tt X T (open_tt T2 X)).
      { apply (SubstTTSnap__open_tt_rec_subst_tt 0 T2 X T HXT2). }
      rewrite Heq. exact Hres.
    + apply (Dev__sub_wf_target E0 S T (Dev__wf_sig_wf_env E0 R0 Hws) IH1 Hsub).
    + destruct (atom_fresh (L `union` Dev__fv_typ T2)) as [x Hx].
      assert (HxL : x `notin` L) by (apply notin_union_1 in Hx; assumption).
      assert (HxT : x `notin` Dev__fv_typ T2) by (apply notin_union_2 in Hx; assumption).
      assert (Hwb : wf_typ (x ~ bind_typ T1 ++ E0) T2) by (apply IHbody; assumption).
      eapply Dev__wf_typ_remove_bind_typ; eauto. intros y b; reflexivity.
    + apply wf_typ_box; assumption.
    + apply (Dev__wf_typ_inv_box _ _ IH1).
    + apply (Dev__wf_typ_inv_box _ _ IH1).
    + apply wf_typ_box. apply (Store__wf_sig_binds E0 R0 l T Hws Hb).
    + apply wf_typ_readonly; assumption.
    + apply wf_typ_readonly.
      apply (Dev__wf_typ_inv_box _ _ (Dev__wf_typ_inv_readonly _ _ _ IH1)).
    + apply (WfTyping__typing_record_comp_wf_typ E0 R0 r T Hr).
    + apply (Dev__wf_typ_inv_record _ _ _ IH1).
    + apply wf_typ_readonly. apply (Dev__wf_typ_inv_record _ _ _ (Dev__wf_typ_inv_readonly _ _ _ IH1)).
    + apply (Dev__wf_typ_inv_record _ _ _ IH1).
  - intros E R r T Htr. induction Htr as
      [ E0 R0 Hwe Hws
      | E0 R0 a e r T Tr Hnotin Hr IHr He IHe
      | E0 R0 a l r T Tr Hnotin Hr IHr Hb ].
    + constructor.
    + apply wf_typ_intersect.
      * constructor. apply (WfTyping__typing_wf_typ E0 R0 e T He).
      * apply IHr.
    + apply wf_typ_intersect.
      * constructor. apply (Store__wf_sig_binds E0 R0 l T (MyWork__typing_record_comp_wf_sig E0 R0 r Tr Hr) Hb).
      * apply IHr.
Qed.




Lemma TypingExpr__typing_expr : forall (E : env) (R : sig) e T,
  typing E R e T -> expr e
with TypingExpr__typing_record_comp_expr : forall (E : env) (R : sig) r T,
  typing_record_comp E R r T -> record_comp r.
Proof.
  - intros E R e T Hty. induction Hty as
      [ E0 R0 x T0 Hwe Hws Hb
      | L E0 R0 V e1 T1 Hws Hbody IHbody
      | T1 E0 R0 e1 e2 T2 Hws H1 IH1 H2 IH2
      | L E0 R0 V e1 T1 Hws Hbody IHbody
      | T1 E0 R0 e1 T T2 Hws H1 IH1 Hsub
      | S E0 R0 e T Hws H1 IH1 Hsub
      | L T1 T2 e1 e2 E0 R0 Hws H1 IH1 Hbody IHbody
      | E0 R0 e T Hws H1 IH1
      | E0 R0 e T Hws H1 IH1
      | E0 R0 e1 e2 T Hws H1 IH1 H2 IH2
      | E0 R0 l T Hwe Hws Hb
      | E0 R0 e T H1 IH1
      | E0 R0 e T H1 IH1
      | E0 R0 r T Hr IHr
      | E0 R0 e a T H1 IH1
      | E0 R0 e a T H1 IH1
      | E0 R0 e1 a e2 T H1 IH1 H2 IH2 ].
    + apply expr_var.
    + destruct (atom_fresh L) as [x Hx].
      assert (Hwenv : wf_env (x ~ bind_typ V ++ E0))
        by (apply (Dev__wf_sig_wf_env (x ~ bind_typ V ++ E0) R0);
            apply (MyWork__typing_wf_sig (x ~ bind_typ V ++ E0) R0 (open_ee e1 x) T1);
            apply Hbody; assumption).
      destruct (Dev__wf_env_cons_bind_typ _ _ _ Hwenv) as [HweE HwV].
      apply (expr_abs L V e1). apply (MyWork__wf_typ_type E0 V HwV).
      intros x0 Hx0. apply IHbody. assumption.
    + apply expr_app; assumption.
    + destruct (atom_fresh L) as [X HX].
      assert (Hwenv : wf_env (X ~ bind_sub V ++ E0))
        by (apply (Dev__wf_sig_wf_env (X ~ bind_sub V ++ E0) R0);
            apply (MyWork__typing_wf_sig (X ~ bind_sub V ++ E0) R0 (open_te e1 X) (open_tt T1 X));
            apply Hbody; assumption).
      destruct (Dev__wf_env_cons_bind_sub _ _ _ Hwenv) as [HweE HwV].
      apply (expr_tabs L V e1). apply (MyWork__wf_typ_type E0 V HwV).
      intros X0 HX0. apply IHbody. assumption.
    + assert (HwAll : wf_typ E0 (typ_all T1 T2)) by (apply (WfTyping__typing_wf_typ E0 R0 e1 (typ_all T1 T2) H1)).
      destruct (Dev__wf_typ_inv_all _ _ _ HwAll) as [L0 [HwT1 _]].
      assert (Hwe : wf_env E0) by (apply Dev__wf_sig_wf_env with (R := R0); assumption).
      assert (HwT : wf_typ E0 T) by (apply (Dev__sub_wf_source E0 T T1 Hwe HwT1 Hsub)).
      apply (expr_tapp e1 T). assumption. apply (MyWork__wf_typ_type E0 T HwT).
    + assumption.
    + apply (expr_let L e1 e2).
      * assumption.
      * intros x Hx. apply IHbody. assumption.
    + apply expr_box. assumption.
    + apply expr_unbox. assumption.
    + apply expr_set_box; assumption.
    + apply expr_ref.
    + apply expr_seal. assumption.
    + apply expr_unbox. assumption.
    + apply expr_record. apply (TypingExpr__typing_record_comp_expr E0 R0 r T Hr).
    + apply expr_record_read. assumption.
    + apply expr_record_read. assumption.
    + apply expr_record_write; assumption.
  - intros E R r T Htr. induction Htr as
      [ E0 R0 Hwe Hws
      | E0 R0 a e r T Tr Hnotin Hr IHr He IHe
      | E0 R0 a l r T Tr Hnotin Hr IHr Hb ].
    + apply record_comp_empty.
    + apply record_comp_exp.
      * apply (TypingExpr__typing_expr E0 R0 e T He).
      * apply IHr.
    + apply record_comp_ref. apply IHr.
Qed.




(* Types reachable as targets of a subtyping derivation whose source is
   "readonly-like" (top, a mut type, an arrow, an all, or an intersection of
   such types).  Boxes and records are deliberately excluded: normalization
   keeps readonly in front of boxes/records, so readonly cannot be erased to
   reach them.  (For arrows and alls the normal form does erase readonly,
   hence they are included.) *)

Inductive Readonly__NR : typ -> Prop :=
  | Readonly__NR_top : Readonly__NR typ_top
  | Readonly__NR_mut : forall m T, Readonly__NR (typ_mut m T)
  | Readonly__NR_arrow : forall T1 T2, Readonly__NR (typ_arrow T1 T2)
  | Readonly__NR_all : forall T1 T2, Readonly__NR (typ_all T1 T2)
  | Readonly__NR_int : forall T1 T2, Readonly__NR T1 -> Readonly__NR T2 -> Readonly__NR (typ_int T1 T2).

(* Any type whatsoever is Readonly__NR after merging a mutability into it. *)
Lemma Readonly__NR_merge : forall T m, Readonly__NR (merge_mutability T m).
Proof.
  induction T; intros mm; simpl.
  - apply Readonly__NR_top.
  - apply Readonly__NR_mut.
  - apply Readonly__NR_mut.
  - apply Readonly__NR_arrow.
  - apply Readonly__NR_all.
  - apply Readonly__NR_mut.
  - apply Readonly__NR_mut.
  - apply Readonly__NR_int.
    + apply (IHT1 mm).
    + apply (IHT2 mm).
  - apply Readonly__NR_mut.
Qed.

Lemma Readonly__NR_nf : forall T, Readonly__NR T -> Readonly__NR (normal_form_typing T).
Proof.
  intros T H. induction H.
  - rewrite Dev__nf_top. apply Readonly__NR_top.
  - rewrite Dev__nf_mut. apply Readonly__NR_merge.
  - rewrite Dev__nf_arrow. apply Readonly__NR_arrow.
  - rewrite Dev__nf_all. apply Readonly__NR_all.
  - rewrite Dev__nf_int. apply Readonly__NR_int; assumption.
Qed.

Lemma Readonly__NR_of_nf : forall T, Readonly__NR (normal_form_typing T) -> Readonly__NR T.
Proof.
  induction T; simpl; intros H.
  - exact H.
  - inversion H.
  - inversion H.
  - apply Readonly__NR_arrow.
  - apply Readonly__NR_all.
  - inversion H.
  - apply Readonly__NR_mut.
  - apply Readonly__NR_int.
    + apply IHT1. inversion H; subst; assumption.
    + apply IHT2. inversion H; subst; assumption.
  - inversion H.
Qed.

Lemma Readonly__sub_nr_closed : forall E S T,
  Readonly__NR S -> sub E S T -> Readonly__NR T.
Proof.
  intros E S T HNR Hsub. revert HNR.
  induction Hsub as [ E0 S0 HE0 HS0
                 | E0 X HE0 HS0
                 | U E0 T0 X Hb Hsub IHsub
                 | E0 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E0 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 T1 T2 HEi1 HSi1 HSi2
                 | E0 T1 T2 HEi2 HSi2b HSi2c
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1
                 | E0 T1 T2 HSd1 HSd2 Hsub IHsub ];
  intros HNR.
  - apply Readonly__NR_top.
  - inversion HNR.
  - inversion HNR.
  - apply Readonly__NR_arrow.
  - apply Readonly__NR_all.
  - inversion HNR.
  - apply Readonly__NR_mut.
  - apply Readonly__NR_mut.
  - assert (H2' : Readonly__NR T2) by (apply IH1; assumption).
    apply (IH2 H2').
  - inversion HNR; subst. assumption.
  - inversion HNR; subst. assumption.
  - apply Readonly__NR_int.
    + apply (IH1 HNR).
    + apply (IH2 HNR).
  - inversion HNR.
  - apply Readonly__NR_mut.
  - assert (Hnf : Readonly__NR (normal_form_typing T1)) by (apply Readonly__NR_nf; assumption).
    assert (Hnft : Readonly__NR (normal_form_typing T2)) by (apply IHsub; assumption).
    apply Readonly__NR_of_nf. assumption.
Qed.

Lemma Readonly__sub_readonly_nr : forall E U T,
  sub E (typ_mut mut_readonly U) T -> Readonly__NR T.
Proof.
  intros. apply (Readonly__sub_nr_closed E (typ_mut mut_readonly U) T).
  - apply Readonly__NR_mut.
  - assumption.
Qed.

Lemma Readonly__sub_readonly_box_false : forall E U B,
  sub E (typ_mut mut_readonly U) (typ_box B) -> False.
Proof.
  intros E U B H. assert (HNR := Readonly__sub_readonly_nr E U (typ_box B) H).
  inversion HNR.
Qed.

Lemma Readonly__sub_readonly_record_false : forall E U a B,
  sub E (typ_mut mut_readonly U) (typ_record a B) -> False.
Proof.
  intros E U a B H. assert (HNR := Readonly__sub_readonly_nr E U (typ_record a B) H).
  inversion HNR.
Qed.

Lemma Readonly__sub_readonly_fvar_false : forall E U X,
  sub E (typ_mut mut_readonly U) (typ_fvar X) -> False.
Proof.
  intros E U X H. assert (HNR := Readonly__sub_readonly_nr E U (typ_fvar X) H).
  inversion HNR.
Qed.




(* Shape-directed inversions of typing, stripping any outer typing_sub. *)

Lemma TypingInv__typing_app_inv : forall E R e1 e2 T,
  typing E R (exp_app e1 e2) T ->
  wf_env E -> wf_typ E T ->
  exists A B, typing E R e1 (typ_arrow A B) /\
    typing E R e2 A /\ sub E B T.
Proof.
  intros E R e1 e2 T H. remember (exp_app e1 e2) as e eqn:He.
  revert He.
  induction H as [ E0 R0 x T0 Hwe Hws Hb
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targ T2 Hws H1 IH1 Hsub
                 | S E0 R0 e0 T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e0 T0 Hws H1 IH1
                 | E0 R0 e0 T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 l T0 Hwe Hws Hb
                 | E0 R0 e0 T0 H1 IH1
                 | E0 R0 e0 T0 H1 IH1
                 | E0 R0 r T0 Hr IHr
                 | E0 R0 e0 a T0 H1 IH1
                 | E0 R0 e0 a T0 H1 IH1
                 | E0 R0 e1b a e2b T0 H1 IH1 H2 IH2 ];
  intros He HE Ht; try discriminate.
  - injection He as Hx Hy. subst e1b e2b.
    exists T1, T2. split; [assumption|split; [assumption|]].
    apply (Dev__sub_refl E0 T2 HE Ht).
  - destruct (IH1 He HE (WfTyping__typing_wf_typ E0 R0 e0 S H1))
      as [A [B [HA [HB Hs]]]].
    exists A, B. split; [assumption|split; [assumption|]].
    eapply sub_trans; eauto.
Qed.

Lemma TypingInv__typing_box_inv : forall E R e T,
  typing E R (exp_box e) T ->
  wf_env E -> wf_typ E T ->
  exists S, typing E R e S /\ sub E (typ_box S) T.
Proof.
  intros E R e T H. remember (exp_box e) as e0 eqn:He.
  revert He.
  induction H as [ E0 R0 x T0 Hwe Hws Hb
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targ T2 Hws H1 IH1 Hsub
                 | S E0 R0 e1b T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 l T0 Hwe Hws Hb
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 r T0 Hr IHr
                 | E0 R0 e1b a T0 H1 IH1
                 | E0 R0 e1b a T0 H1 IH1
                 | E0 R0 e1b a e2b T0 H1 IH1 H2 IH2 ];
  intros He HE Ht; try discriminate.
  - destruct (IH1 He HE (WfTyping__typing_wf_typ E0 R0 e1b S H1))
      as [S0 [Hty Hs]].
    exists S0. split; [assumption|].
    eapply sub_trans; eauto.
  - injection He as Hx. subst e1b.
    exists T0. split; [assumption|].
    apply (Dev__sub_refl E0 (typ_box T0) HE Ht).
Qed.

Lemma TypingInv__typing_unbox_inv : forall E R e T,
  typing E R (exp_unbox e) T ->
  wf_env E -> wf_typ E T ->
  (exists S, typing E R e (typ_box S) /\ sub E S T) \/
  (exists S, typing E R e (typ_mut mut_readonly (typ_box S)) /\
     sub E (typ_mut mut_readonly S) T).
Proof.
  intros E R e T H. remember (exp_unbox e) as e0 eqn:He.
  revert He.
  induction H as [ E0 R0 x T0 Hwe Hws Hb
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targ T2 Hws H1 IH1 Hsub
                 | S E0 R0 e1b T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 l T0 Hwe Hws Hb
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 r T0 Hr IHr
                 | E0 R0 e1b a T0 H1 IH1
                 | E0 R0 e1b a T0 H1 IH1
                 | E0 R0 e1b a e2b T0 H1 IH1 H2 IH2 ];
  intros He HE Ht; try discriminate.
  - destruct (IH1 He HE (WfTyping__typing_wf_typ E0 R0 e1b S H1))
      as [[S0 [Hty Hs]] | [S0 [Hty Hs]]].
    + left. exists S0. split; [assumption|]. eapply sub_trans; eauto.
    + right. exists S0. split; [assumption|]. eapply sub_trans; eauto.
  - injection He as Hx. subst e1b.
    left. exists T0. split; [assumption|].
    apply (Dev__sub_refl E0 T0 HE Ht).
  - injection He as Hx. subst e1b.
    right. exists T0. split; [assumption|].
    apply (Dev__sub_refl E0 (typ_mut mut_readonly T0) HE Ht).
Qed.

Lemma TypingInv__typing_set_box_inv : forall E R e1 e2 T,
  typing E R (exp_set_box e1 e2) T ->
  wf_env E -> wf_typ E T ->
  exists S, typing E R e1 (typ_box S) /\
    typing E R e2 S /\ sub E S T.
Proof.
  intros E R e1 e2 T H. remember (exp_set_box e1 e2) as e0 eqn:He.
  revert He.
  induction H as [ E0 R0 x T0 Hwe Hws Hb
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targ T2 Hws H1 IH1 Hsub
                 | S E0 R0 e1b T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 l T0 Hwe Hws Hb
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 r T0 Hr IHr
                 | E0 R0 e1b a T0 H1 IH1
                 | E0 R0 e1b a T0 H1 IH1
                 | E0 R0 e1b a e2b T0 H1 IH1 H2 IH2 ];
  intros He HE Ht; try discriminate.
  - destruct (IH1 He HE (WfTyping__typing_wf_typ E0 R0 e1b S H1))
      as [S0 [H1' [H2' Hs]]].
    exists S0. split; [assumption|split; [assumption|]].
    eapply sub_trans; eauto.
  - injection He as Hx Hy. subst e1b e2b.
    exists T0. split; [assumption|split; [assumption|]].
    apply (Dev__sub_refl E0 T0 HE Ht).
Qed.

Lemma TypingInv__typing_seal_inv : forall E R e T,
  typing E R (exp_seal e) T ->
  wf_env E -> wf_typ E T ->
  exists S, typing E R e S /\ sub E (typ_mut mut_readonly S) T.
Proof.
  intros E R e T H. remember (exp_seal e) as e0 eqn:He.
  revert He.
  induction H as [ E0 R0 x T0 Hwe Hws Hb
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targ T2 Hws H1 IH1 Hsub
                 | S E0 R0 e1b T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 l T0 Hwe Hws Hb
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 r T0 Hr IHr
                 | E0 R0 e1b a T0 H1 IH1
                 | E0 R0 e1b a T0 H1 IH1
                 | E0 R0 e1b a e2b T0 H1 IH1 H2 IH2 ];
  intros He HE Ht; try discriminate.
  - destruct (IH1 He HE (WfTyping__typing_wf_typ E0 R0 e1b S H1))
      as [S0 [Hty Hs]].
    exists S0. split; [assumption|].
    eapply sub_trans; eauto.
  - injection He as Hx. subst e1b.
    exists T0. split; [assumption|].
    apply (Dev__sub_refl E0 (typ_mut mut_readonly T0) HE Ht).
Qed.

Lemma TypingInv__typing_record_inv : forall E R r T,
  typing E R (exp_record r) T ->
  wf_env E -> wf_typ E T ->
  exists Tr, typing_record_comp E R r Tr /\ sub E Tr T.
Proof.
  intros E R r T H. remember (exp_record r) as e0 eqn:He.
  revert He.
  induction H as [ E0 R0 x T0 Hwe Hws Hb
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targ T2 Hws H1 IH1 Hsub
                 | S E0 R0 e1b T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 l T0 Hwe Hws Hb
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 rb T0 Hr IHr
                 | E0 R0 e1b a T0 H1 IH1
                 | E0 R0 e1b a T0 H1 IH1
                 | E0 R0 e1b a e2b T0 H1 IH1 H2 IH2 ];
  intros He HE Ht; try discriminate.
  - destruct (IH1 He HE (WfTyping__typing_wf_typ E0 R0 e1b S H1))
      as [Tr [Hr' Hs]].
    exists Tr. split; [assumption|]. eapply sub_trans; eauto.
  - injection He as Hx. subst rb.
    exists T0. split; [assumption|].
    apply (Dev__sub_refl E0 T0 HE Ht).
Qed.

Lemma TypingInv__typing_record_read_inv : forall E R e a T,
  typing E R (exp_record_read e a) T ->
  wf_env E -> wf_typ E T ->
  (exists S, typing E R e (typ_record a S) /\ sub E S T) \/
  (exists S, typing E R e (typ_mut mut_readonly (typ_record a S)) /\
     sub E (typ_mut mut_readonly S) T).
Proof.
  intros E R e a T H. remember (exp_record_read e a) as e0 eqn:He.
  revert He.
  induction H as [ E0 R0 x T0 Hwe Hws Hb
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targ T2 Hws H1 IH1 Hsub
                 | S E0 R0 e1b T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 l T0 Hwe Hws Hb
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 rb T0 Hr IHr
                 | E0 R0 e1b a0 T0 H1 IH1
                 | E0 R0 e1b a0 T0 H1 IH1
                 | E0 R0 e1b a0 e2b T0 H1 IH1 H2 IH2 ];
  intros He HE Ht; try discriminate.
  - destruct (IH1 He HE (WfTyping__typing_wf_typ E0 R0 e1b S H1))
      as [[S0 [Hty Hs]] | [S0 [Hty Hs]]].
    + left. exists S0. split; [assumption|]. eapply sub_trans; eauto.
    + right. exists S0. split; [assumption|]. eapply sub_trans; eauto.
  - injection He as Hx Hy. subst e1b a0.
    left. exists T0. split; [assumption|].
    apply (Dev__sub_refl E0 T0 HE Ht).
  - injection He as Hx Hy. subst e1b a0.
    right. exists T0. split; [assumption|].
    apply (Dev__sub_refl E0 (typ_mut mut_readonly T0) HE Ht).
Qed.

Lemma TypingInv__typing_record_write_inv : forall E R e1 a e2 T,
  typing E R (exp_record_write e1 a e2) T ->
  wf_env E -> wf_typ E T ->
  exists S, typing E R e1 (typ_record a S) /\
    typing E R e2 S /\ sub E S T.
Proof.
  intros E R e1 a e2 T H. remember (exp_record_write e1 a e2) as e0 eqn:He.
  revert He.
  induction H as [ E0 R0 x T0 Hwe Hws Hb
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targ T2 Hws H1 IH1 Hsub
                 | S E0 R0 e1b T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 l T0 Hwe Hws Hb
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 rb T0 Hr IHr
                 | E0 R0 e1b a0 T0 H1 IH1
                 | E0 R0 e1b a0 T0 H1 IH1
                 | E0 R0 e1b a0 e2b T0 H1 IH1 H2 IH2 ];
  intros He HE Ht; try discriminate.
  - destruct (IH1 He HE (WfTyping__typing_wf_typ E0 R0 e1b S H1))
      as [S0 [H1' [H2' Hs]]].
    exists S0. split; [assumption|split; [assumption|]].
    eapply sub_trans; eauto.
  - injection He as Hx Hy Hz. subst e1b a0 e2b.
    exists T0. split; [assumption|split; [assumption|]].
    apply (Dev__sub_refl E0 T0 HE Ht).
Qed.

Lemma TypingInv__typing_var_inv : forall E R x T,
  typing E R (exp_fvar x) T ->
  wf_env E -> wf_typ E T ->
  exists S, binds x (bind_typ S) E /\ sub E S T.
Proof.
  intros E R x T H. remember (exp_fvar x) as e0 eqn:He.
  revert He.
  induction H as [ E0 R0 x0 T0 Hwe Hws Hb
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targ T2 Hws H1 IH1 Hsub
                 | S E0 R0 e1b T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 l T0 Hwe Hws Hb
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 rb T0 Hr IHr
                 | E0 R0 e1b a0 T0 H1 IH1
                 | E0 R0 e1b a0 T0 H1 IH1
                 | E0 R0 e1b a0 e2b T0 H1 IH1 H2 IH2 ];
  intros He HE Ht; try discriminate.
  - injection He as Hx. subst x0.
    exists T0. split; [assumption|].
    apply (Dev__sub_refl E0 T0 HE Ht).
  - destruct (IH1 He HE (WfTyping__typing_wf_typ E0 R0 e1b S H1))
      as [S0 [Hb Hs]].
    exists S0. split; [assumption|]. eapply sub_trans; eauto.
Qed.

Lemma TypingInv__typing_abs_inv : forall E R V e1 T,
  typing E R (exp_abs V e1) T ->
  wf_env E -> wf_typ E T ->
  exists T1 L, sub E (typ_arrow V T1) T /\
    (forall x, x `notin` L ->
      typing (x ~ bind_typ V ++ E) R (open_ee e1 x) T1).
Proof.
  intros E R V e1 T H. remember (exp_abs V e1) as e0 eqn:He.
  revert He.
  induction H as [ E0 R0 x T0 Hwe Hws Hb
                 | L E0 R0 V0 e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V0 e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targ T2 Hws H1 IH1 Hsub
                 | S E0 R0 e1b T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 l T0 Hwe Hws Hb
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 rb T0 Hr IHr
                 | E0 R0 e1b a0 T0 H1 IH1
                 | E0 R0 e1b a0 T0 H1 IH1
                 | E0 R0 e1b a0 e2b T0 H1 IH1 H2 IH2 ];
  intros He HE Ht; try discriminate.
  - injection He as HV Hee. subst V0 e1b.
    exists T1, L. split; [|assumption].
    apply (Dev__sub_refl E0 (typ_arrow V T1) HE Ht).
  - destruct (IH1 He HE (WfTyping__typing_wf_typ E0 R0 e1b S H1))
      as [T1 [L [Hs Hbody]]].
    exists T1, L. split; [|assumption].
    eapply sub_trans; eauto.
Qed.

Lemma TypingInv__typing_tabs_inv : forall E R V e1 T,
  typing E R (exp_tabs V e1) T ->
  wf_env E -> wf_typ E T ->
  exists T1 L, sub E (typ_all V T1) T /\
    (forall X, X `notin` L ->
      typing (X ~ bind_sub V ++ E) R (open_te e1 X) (open_tt T1 X)).
Proof.
  intros E R V e1 T H. remember (exp_tabs V e1) as e0 eqn:He.
  revert He.
  induction H as [ E0 R0 x T0 Hwe Hws Hb
                 | L E0 R0 V0 e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V0 e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targ T2 Hws H1 IH1 Hsub
                 | S E0 R0 e1b T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 l T0 Hwe Hws Hb
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 rb T0 Hr IHr
                 | E0 R0 e1b a0 T0 H1 IH1
                 | E0 R0 e1b a0 T0 H1 IH1
                 | E0 R0 e1b a0 e2b T0 H1 IH1 H2 IH2 ];
  intros He HE Ht; try discriminate.
  - injection He as HV Hee. subst V0 e1b.
    exists T1, L. split; [|assumption].
    apply (Dev__sub_refl E0 (typ_all V T1) HE Ht).
  - destruct (IH1 He HE (WfTyping__typing_wf_typ E0 R0 e1b S H1))
      as [T1 [L [Hs Hbody]]].
    exists T1, L. split; [|assumption].
    eapply sub_trans; eauto.
Qed.

Lemma TypingInv__typing_let_inv : forall E R e1 e2 T,
  typing E R (exp_let e1 e2) T ->
  wf_env E -> wf_typ E T ->
  exists T1 T2 L,
    typing E R e1 T1 /\
    (forall x, x `notin` L ->
      typing (x ~ bind_typ T1 ++ E) R (open_ee e2 x) T2) /\
    sub E T2 T.
Proof.
  intros E R e1 e2 T H. remember (exp_let e1 e2) as e0 eqn:He.
  revert He.
  induction H as [ E0 R0 x T0 Hwe Hws Hb
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targ T2 Hws H1 IH1 Hsub
                 | S E0 R0 e1b T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 l T0 Hwe Hws Hb
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 e1b T0 H1 IH1
                 | E0 R0 rb T0 Hr IHr
                 | E0 R0 e1b a0 T0 H1 IH1
                 | E0 R0 e1b a0 T0 H1 IH1
                 | E0 R0 e1b a0 e2b T0 H1 IH1 H2 IH2 ];
  intros He HE Ht; try discriminate.
  - destruct (IH1 He HE (WfTyping__typing_wf_typ E0 R0 e1b S H1))
      as [T1 [T2 [L [H1' [Hbody Hs]]]]].
    exists T1, T2, L. split; [assumption|split; [assumption|]].
    eapply sub_trans; eauto.
  - injection He as Hx Hy. subst e1b e2b.
    exists T1, T2, L. split; [assumption|split; [assumption|]].
    apply (Dev__sub_refl E0 T2 HE Ht).
Qed.




Lemma Canonical__ArrComp_mut_inv : forall m T A B,
  Dev__ArrComp (typ_mut m T) A B -> Dev__ArrComp T A B.
Proof. intros. inversion H; subst. - apply Dev__arr_comp_fvar. - assumption. Qed.

Lemma Canonical__ArrComp_record_comp_false : forall E R r Tr A B,
  typing_record_comp E R r Tr -> Dev__ArrComp Tr A B -> False.
Proof.
  intros E R r Tr A B H. induction H as
    [ E0 R0 HE HS
    | E0 R0 a e rb T Tr Hnot Hr IHr Hty
    | E0 R0 a l rb T Tr Hnot Hr IHr Hb ];
    intros Hac.
  - inversion Hac.
  - inversion Hac; subst;
      try match goal with H : Dev__ArrComp (typ_record _ _) _ _ |- False => inversion H end;
      auto.
  - inversion Hac; subst;
      try match goal with H : Dev__ArrComp (typ_record _ _) _ _ |- False => inversion H end;
      auto.
Qed.

Lemma Canonical__BoxComp_record_comp_false : forall E R r Tr A,
  typing_record_comp E R r Tr -> MyWork__BoxComp Tr A -> False.
Proof.
  intros E R r Tr A H. induction H as
    [ E0 R0 HE HS
    | E0 R0 a e rb T Tr Hnot Hr IHr Hty
    | E0 R0 a l rb T Tr Hnot Hr IHr Hb ];
    intros Hac.
  - inversion Hac.
  - inversion Hac; subst;
      try match goal with H : MyWork__BoxComp (typ_record _ _) _ |- False => inversion H end;
      auto.
  - inversion Hac; subst;
      try match goal with H : MyWork__BoxComp (typ_record _ _) _ |- False => inversion H end;
      auto.
Qed.

(* A value of arrow type is an abstraction. *)
Lemma Canonical__value_arrow_abs : forall E R e A B,
  value e -> typing E R e (typ_arrow A B) -> wf_env E ->
  exists V body, e = exp_abs V body.
Proof.
  intros E R e A B Hv Hty HE.
  assert (HWf : wf_typ E (typ_arrow A B)) by (apply (WfTyping__typing_wf_typ E R e (typ_arrow A B)); assumption).
  assert (HA : wf_typ E A) by (apply (proj1 (Dev__wf_typ_inv_arrow E A B HWf))).
  assert (HB : wf_typ E B) by (apply (proj2 (Dev__wf_typ_inv_arrow E A B HWf))).
  induction Hv as [ V0 body Hexpr | V0 body Hexpr | l | l | r Hvr | r Hvr ].
  - exists V0, body. reflexivity.
  - exfalso.
    destruct (TypingInv__typing_tabs_inv E R V0 body (typ_arrow A B) Hty HE HWf)
      as [T1 [L [Hs _]]].
    assert (HWS : wf_typ E (typ_all V0 T1)) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (Dev__sub_arrcomp E (typ_all V0 T1) (typ_arrow A B) HE HWS Hs A B HA HB
                (Dev__arr_comp_arrow A B)) as [A' [B' [HA' [HB' [Hc _]]]]].
    inversion Hc.
  - exfalso.
    destruct (MyWork__typing_ref_inv E R l (typ_arrow A B) Hty) as [T0 [Hb Hs]].
    assert (HWS : wf_typ E (typ_box T0)) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (Dev__sub_arrcomp E (typ_box T0) (typ_arrow A B) HE HWS Hs A B HA HB
                (Dev__arr_comp_arrow A B)) as [A' [B' [HA' [HB' [Hc _]]]]].
    inversion Hc.
  - exfalso.
    destruct (TypingInv__typing_seal_inv E R (exp_ref l) (typ_arrow A B) Hty HE HWf)
      as [St [Href Hs]].
    assert (HWS : wf_typ E (typ_mut mut_readonly St))
      by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (Dev__sub_arrcomp E (typ_mut mut_readonly St) (typ_arrow A B) HE HWS Hs A B HA HB
                (Dev__arr_comp_arrow A B)) as [A0 [B0 [HA0 [HB0 [Hc0 _]]]]].
    assert (Hc0' : Dev__ArrComp St A0 B0) by (apply (Canonical__ArrComp_mut_inv mut_readonly St A0 B0 Hc0)).
    destruct (MyWork__typing_ref_inv E R l St Href) as [T0 [Hb Hs0]].
    assert (HWB : wf_typ E (typ_box T0)) by (apply (Dev__sub_wf_source E _ _ HE
      (WfTyping__typing_wf_typ E R (exp_ref l) St Href) Hs0)).
    destruct (Dev__sub_arrcomp E (typ_box T0) St HE HWB Hs0 A0 B0 HA0 HB0 Hc0')
      as [A' [B' [HA' [HB' [Hc _]]]]].
    inversion Hc.
  - exfalso.
    destruct (TypingInv__typing_record_inv E R r (typ_arrow A B) Hty HE HWf) as [Tr [Hr Hs]].
    assert (HWS : wf_typ E Tr) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (Dev__sub_arrcomp E Tr (typ_arrow A B) HE HWS Hs A B HA HB
                (Dev__arr_comp_arrow A B)) as [A' [B' [HA' [HB' [Hc _]]]]].
    eapply Canonical__ArrComp_record_comp_false; eauto.
  - exfalso.
    destruct (TypingInv__typing_seal_inv E R (exp_record r) (typ_arrow A B) Hty HE HWf)
      as [St [Hrec Hs]].
    assert (HWS : wf_typ E (typ_mut mut_readonly St))
      by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (Dev__sub_arrcomp E (typ_mut mut_readonly St) (typ_arrow A B) HE HWS Hs A B HA HB
                (Dev__arr_comp_arrow A B)) as [A0 [B0 [HA0 [HB0 [Hc0 _]]]]].
    assert (Hc0' : Dev__ArrComp St A0 B0) by (apply (Canonical__ArrComp_mut_inv mut_readonly St A0 B0 Hc0)).
    destruct (TypingInv__typing_record_inv E R r St Hrec HE
                (WfTyping__typing_wf_typ E R (exp_record r) St Hrec)) as [Tr [Hr Hs0]].
    assert (HWSr : wf_typ E Tr) by (apply (Dev__sub_wf_source E _ _ HE
      (WfTyping__typing_wf_typ E R (exp_record r) St Hrec) Hs0)).
    destruct (Dev__sub_arrcomp E Tr St HE HWSr Hs0 A0 B0 HA0 HB0 Hc0')
      as [A' [B' [HA' [HB' [Hc _]]]]].
    eapply Canonical__ArrComp_record_comp_false; eauto.
Qed.

(* A value of box type is a reference. *)
Lemma Canonical__value_box_ref : forall E R e B,
  value e -> typing E R e (typ_box B) -> wf_env E ->
  exists l, e = exp_ref l.
Proof.
  intros E R e B Hv Hty HE.
  assert (HWf : wf_typ E (typ_box B)) by (apply (WfTyping__typing_wf_typ E R e (typ_box B)); assumption).
  assert (HB : wf_typ E B) by (apply (Dev__wf_typ_inv_box E B HWf)).
  induction Hv as [ V0 body Hexpr | V0 body Hexpr | l | l | r Hvr | r Hvr ].
  - exfalso.
    destruct (TypingInv__typing_abs_inv E R V0 body (typ_box B) Hty HE HWf)
      as [T1 [L [Hs _]]].
    assert (HWS : wf_typ E (typ_arrow V0 T1)) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_boxcomp E (typ_arrow V0 T1) (typ_box B) HE HWS Hs B HB
                (MyWork__box_comp_box B)) as [A' [HA' [Hc _]]].
    inversion Hc.
  - exfalso.
    destruct (TypingInv__typing_tabs_inv E R V0 body (typ_box B) Hty HE HWf)
      as [T1 [L [Hs _]]].
    assert (HWS : wf_typ E (typ_all V0 T1)) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_boxcomp E (typ_all V0 T1) (typ_box B) HE HWS Hs B HB
                (MyWork__box_comp_box B)) as [A' [HA' [Hc _]]].
    inversion Hc.
  - exists l. reflexivity.
  - exfalso.
    destruct (TypingInv__typing_seal_inv E R (exp_ref l) (typ_box B) Hty HE HWf)
      as [St [Href Hs]].
    eapply Readonly__sub_readonly_box_false; eauto.
  - exfalso.
    destruct (TypingInv__typing_record_inv E R r (typ_box B) Hty HE HWf) as [Tr [Hr Hs]].
    assert (HWS : wf_typ E Tr) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_boxcomp E Tr (typ_box B) HE HWS Hs B HB
                (MyWork__box_comp_box B)) as [A' [HA' [Hc _]]].
    eapply Canonical__BoxComp_record_comp_false; eauto.
  - exfalso.
    destruct (TypingInv__typing_seal_inv E R (exp_record r) (typ_box B) Hty HE HWf)
      as [St [Hrec Hs]].
    eapply Readonly__sub_readonly_box_false; eauto.
Qed.

(* A value of non-readonly record type is a record literal. *)
Lemma Canonical__value_record_lit : forall E R e a T,
  value e -> typing E R e (typ_record a T) -> wf_env E ->
  exists r, e = exp_record r.
Proof.
  intros E R e a T Hv Hty HE.
  assert (HWf : wf_typ E (typ_record a T))
    by (apply (WfTyping__typing_wf_typ E R e (typ_record a T)); assumption).
  assert (HT : wf_typ E T) by (apply (Dev__wf_typ_inv_record E a T HWf)).
  induction Hv as [ V0 body Hexpr | V0 body Hexpr | l | l | r Hvr | r Hvr ].
  - exfalso.
    destruct (TypingInv__typing_abs_inv E R V0 body (typ_record a T) Hty HE HWf)
      as [T1 [L [Hs _]]].
    assert (HWS : wf_typ E (typ_arrow V0 T1)) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_rcomp a E (typ_arrow V0 T1) (typ_record a T) HE HWS Hs T HT
                (MyWork__rc_here a T)) as [A' [HA' [Hc _]]].
    inversion Hc.
  - exfalso.
    destruct (TypingInv__typing_tabs_inv E R V0 body (typ_record a T) Hty HE HWf)
      as [T1 [L [Hs _]]].
    assert (HWS : wf_typ E (typ_all V0 T1)) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_rcomp a E (typ_all V0 T1) (typ_record a T) HE HWS Hs T HT
                (MyWork__rc_here a T)) as [A' [HA' [Hc _]]].
    inversion Hc.
  - exfalso.
    destruct (MyWork__typing_ref_inv E R l (typ_record a T) Hty) as [T0 [Hb Hs]].
    assert (HWS : wf_typ E (typ_box T0)) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_rcomp a E (typ_box T0) (typ_record a T) HE HWS Hs T HT
                (MyWork__rc_here a T)) as [A' [HA' [Hc _]]].
    inversion Hc.
  - exfalso.
    destruct (TypingInv__typing_seal_inv E R (exp_ref l) (typ_record a T) Hty HE HWf)
      as [St [Href Hs]].
    eapply Readonly__sub_readonly_record_false; eauto.
  - exists r. reflexivity.
  - exfalso.
    destruct (TypingInv__typing_seal_inv E R (exp_record r) (typ_record a T) Hty HE HWf)
      as [St [Hrec Hs]].
    eapply Readonly__sub_readonly_record_false; eauto.
Qed.

(* A value of readonly record type is either a record literal or a sealed one. *)
Lemma Canonical__value_record_readonly_lit : forall E R e a T,
  value e -> typing E R e (typ_mut mut_readonly (typ_record a T)) -> wf_env E ->
  (exists r, e = exp_record r) \/ (exists r, e = exp_seal (exp_record r)).
Proof.
  intros E R e a T Hv Hty HE.
  assert (HWf : wf_typ E (typ_mut mut_readonly (typ_record a T)))
    by (apply (WfTyping__typing_wf_typ E R e (typ_mut mut_readonly (typ_record a T))); assumption).
  assert (HT : wf_typ E T) by (apply (Dev__wf_typ_inv_record E a T
    (Dev__wf_typ_inv_readonly E mut_readonly (typ_record a T) HWf))).
  induction Hv as [ V0 body Hexpr | V0 body Hexpr | l | l | r Hvr | r Hvr ].
  - exfalso.
    destruct (TypingInv__typing_abs_inv E R V0 body (typ_mut mut_readonly (typ_record a T)) Hty HE HWf)
      as [T1 [L [Hs _]]].
    assert (HWS : wf_typ E (typ_arrow V0 T1)) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_rcomp a E (typ_arrow V0 T1) (typ_mut mut_readonly (typ_record a T))
                HE HWS Hs T HT (MyWork__rc_mut a mut_readonly (typ_record a T) T (MyWork__rc_here a T)))
      as [A' [HA' [Hc _]]].
    inversion Hc.
  - exfalso.
    destruct (TypingInv__typing_tabs_inv E R V0 body (typ_mut mut_readonly (typ_record a T)) Hty HE HWf)
      as [T1 [L [Hs _]]].
    assert (HWS : wf_typ E (typ_all V0 T1)) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_rcomp a E (typ_all V0 T1) (typ_mut mut_readonly (typ_record a T))
                HE HWS Hs T HT (MyWork__rc_mut a mut_readonly (typ_record a T) T (MyWork__rc_here a T)))
      as [A' [HA' [Hc _]]].
    inversion Hc.
  - exfalso.
    destruct (MyWork__typing_ref_inv E R l (typ_mut mut_readonly (typ_record a T)) Hty)
      as [T0 [Hb Hs]].
    assert (HWS : wf_typ E (typ_box T0)) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_rcomp a E (typ_box T0) (typ_mut mut_readonly (typ_record a T))
                HE HWS Hs T HT (MyWork__rc_mut a mut_readonly (typ_record a T) T (MyWork__rc_here a T)))
      as [A' [HA' [Hc _]]].
    inversion Hc.
  - exfalso.
    destruct (TypingInv__typing_seal_inv E R (exp_ref l) (typ_mut mut_readonly (typ_record a T))
                Hty HE HWf) as [St [Href Hs]].
    assert (HWS : wf_typ E (typ_mut mut_readonly St))
      by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_rcomp a E (typ_mut mut_readonly St)
                (typ_mut mut_readonly (typ_record a T)) HE HWS Hs T HT
                (MyWork__rc_mut a mut_readonly (typ_record a T) T (MyWork__rc_here a T))) as [A' [HA' [Hc _]]].
    assert (Hc' : MyWork__RComp a St A') by (apply (MyWork__RComp_mut_inv a mut_readonly St A' Hc)).
    destruct (MyWork__typing_ref_inv E R l St Href) as [T0 [Hb Hs0]].
    assert (HWB : wf_typ E (typ_box T0)) by (apply (Dev__sub_wf_source E _ _ HE
      (WfTyping__typing_wf_typ E R (exp_ref l) St Href) Hs0)).
    destruct (MyWork__sub_rcomp a E (typ_box T0) St HE HWB Hs0 A' HA' Hc')
      as [A'' [HA'' [Hc'' _]]].
    inversion Hc''.
  - left. exists r. reflexivity.
  - right. exists r. reflexivity.
Qed.

(* A value of readonly box type is a reference or a sealed reference. *)
Lemma Canonical__value_readonly_box : forall E R e B,
  value e -> typing E R e (typ_mut mut_readonly (typ_box B)) -> wf_env E ->
  (exists l, e = exp_ref l) \/ (exists l, e = exp_seal (exp_ref l)).
Proof.
  intros E R e B Hv Hty HE.
  assert (HWf : wf_typ E (typ_mut mut_readonly (typ_box B)))
    by (apply (WfTyping__typing_wf_typ E R e (typ_mut mut_readonly (typ_box B))); assumption).
  assert (HWb : wf_typ E (typ_box B)) by (apply (Dev__wf_typ_inv_readonly E mut_readonly (typ_box B) HWf)).
  assert (HB : wf_typ E B) by (apply (Dev__wf_typ_inv_box E B HWb)).
  induction Hv as [ V0 body Hexpr | V0 body Hexpr | l | l | r Hvr | r Hvr ].
  - exfalso.
    destruct (TypingInv__typing_abs_inv E R V0 body (typ_mut mut_readonly (typ_box B)) Hty HE HWf)
      as [T1 [L [Hs _]]].
    assert (HWS : wf_typ E (typ_arrow V0 T1)) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_boxcomp E (typ_arrow V0 T1) (typ_mut mut_readonly (typ_box B)) HE HWS Hs B HB
                (MyWork__box_comp_mut mut_readonly (typ_box B) B (MyWork__box_comp_box B)))
      as [A' [HA' [Hc _]]].
    inversion Hc.
  - exfalso.
    destruct (TypingInv__typing_tabs_inv E R V0 body (typ_mut mut_readonly (typ_box B)) Hty HE HWf)
      as [T1 [L [Hs _]]].
    assert (HWS : wf_typ E (typ_all V0 T1)) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_boxcomp E (typ_all V0 T1) (typ_mut mut_readonly (typ_box B)) HE HWS Hs B HB
                (MyWork__box_comp_mut mut_readonly (typ_box B) B (MyWork__box_comp_box B)))
      as [A' [HA' [Hc _]]].
    inversion Hc.
  - left. exists l. reflexivity.
  - right. exists l. reflexivity.
  - exfalso.
    destruct (TypingInv__typing_record_inv E R r (typ_mut mut_readonly (typ_box B)) Hty HE HWf)
      as [Tr [Hr Hs]].
    assert (HWS : wf_typ E Tr) by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_boxcomp E Tr (typ_mut mut_readonly (typ_box B)) HE HWS Hs B HB
                (MyWork__box_comp_mut mut_readonly (typ_box B) B (MyWork__box_comp_box B)))
      as [A' [HA' [Hc _]]].
    eapply Canonical__BoxComp_record_comp_false; eauto.
  - exfalso.
    destruct (TypingInv__typing_seal_inv E R (exp_record r) (typ_mut mut_readonly (typ_box B)) Hty HE HWf)
      as [St [Hrec Hs]].
    assert (HWS : wf_typ E (typ_mut mut_readonly St))
      by (apply (Dev__sub_wf_source E _ _ HE HWf Hs)).
    destruct (MyWork__sub_boxcomp E (typ_mut mut_readonly St)
                (typ_mut mut_readonly (typ_box B)) HE HWS Hs B HB
                (MyWork__box_comp_mut mut_readonly (typ_box B) B (MyWork__box_comp_box B)))
      as [A' [HA' [Hc _]]].
    assert (Hc' : MyWork__BoxComp St A') by (apply (MyWork__BoxComp_mut_inv mut_readonly St A' Hc)).
    destruct (TypingInv__typing_record_inv E R r St Hrec HE
                (WfTyping__typing_wf_typ E R (exp_record r) St Hrec)) as [Tr [Hr Hs0]].
    assert (HWSr : wf_typ E Tr) by (apply (Dev__sub_wf_source E _ _ HE
      (WfTyping__typing_wf_typ E R (exp_record r) St Hrec) Hs0)).
    destruct (MyWork__sub_boxcomp E Tr St HE HWSr Hs0 A' HA' Hc')
      as [A'' [HA'' [Hc'' _]]].
    eapply Canonical__BoxComp_record_comp_false; eauto.
Qed.




(* Existence-only all-component analysis.  This is the part needed to show
   that a subtyping derivation with an all target must start from a type
   with an all component; no body relations are tracked. *)

Inductive AllCompEx__AComp : typ -> typ -> typ -> Prop :=
  | AllCompEx__ac_all : forall A B, AllCompEx__AComp (typ_all A B) A B
  | AllCompEx__ac_fvar : forall X A B, AllCompEx__AComp (typ_fvar X) A B
  | AllCompEx__ac_rofvar : forall m X A B, AllCompEx__AComp (typ_mut m (typ_fvar X)) A B
  | AllCompEx__ac_int_l : forall X Y A B, AllCompEx__AComp X A B -> AllCompEx__AComp (typ_int X Y) A B
  | AllCompEx__ac_int_r : forall X Y A B, AllCompEx__AComp Y A B -> AllCompEx__AComp (typ_int X Y) A B
  | AllCompEx__ac_mut : forall m X A B, AllCompEx__AComp X A B -> AllCompEx__AComp (typ_mut m X) A B.

Lemma AllCompEx__AComp_mut_inv : forall m T A B, AllCompEx__AComp (typ_mut m T) A B -> AllCompEx__AComp T A B.
Proof. intros. inversion H; subst. - apply AllCompEx__ac_fvar. - assumption. Qed.

Lemma AllCompEx__AComp_int_inv : forall X Y A B,
  AllCompEx__AComp (typ_int X Y) A B -> AllCompEx__AComp X A B \/ AllCompEx__AComp Y A B.
Proof. intros. inversion H; subst. - left; assumption. - right; assumption. Qed.

Lemma AllCompEx__AComp_all_inv : forall A B C D,
  AllCompEx__AComp (typ_all A B) C D -> C = A /\ D = B.
Proof. intros. inversion H; subst. auto. Qed.

(* Merging a mutability preserves the existence of a component. *)
Lemma AllCompEx__AComp_merge_fwd : forall T m A B,
  AllCompEx__AComp T A B -> exists A' B', AllCompEx__AComp (merge_mutability T m) A' B'.
Proof.
  intros T m A B H. induction H as
    [A0 B0 | X A0 B0 | m0 X A0 B0 | X Y A0 B0 H IH | X Y A0 B0 H IH | m0 X A0 B0 H IH].
  - rewrite Dev__merge_all. exists A0, B0. apply AllCompEx__ac_all.
  - rewrite Dev__merge_fvar. exists A0, B0. apply AllCompEx__ac_rofvar.
  - rewrite Dev__merge_mut. exists A0, B0. apply AllCompEx__ac_rofvar.
  - rewrite Dev__merge_int. destruct IH as [A' [B' Hc]]. exists A', B'. apply AllCompEx__ac_int_l. assumption.
  - rewrite Dev__merge_int. destruct IH as [A' [B' Hc]]. exists A', B'. apply AllCompEx__ac_int_r. assumption.
  - rewrite Dev__merge_mut. exists A0, B0. apply AllCompEx__ac_mut. assumption.
Qed.

Lemma AllCompEx__AComp_merge_rev_exists : forall T m A B,
  AllCompEx__AComp (merge_mutability T m) A B -> exists A' B', AllCompEx__AComp T A' B'.
Proof.
  induction T; intros mm A B H.
  - simpl in H. inversion H.
  - simpl in H. inversion H; subst;
      try match goal with H' : AllCompEx__AComp (typ_bvar _) _ _ |- _ => inversion H' end.
  - simpl in H. exists A, B. apply AllCompEx__ac_fvar.
  - simpl in H. inversion H.
  - simpl in H. destruct (AllCompEx__AComp_all_inv T1 T2 A B H) as [HA HB]. subst A B. exists T1, T2. apply AllCompEx__ac_all.
  - simpl in H. inversion H; subst;
      try match goal with H' : AllCompEx__AComp (typ_box _) _ _ |- _ => inversion H' end.
  - simpl in H. exists A, B. exact H.
  - simpl in H. destruct (AllCompEx__AComp_int_inv _ _ _ _ H) as [Hc | Hc].
    + destruct (IHT1 mm A B Hc) as [A' [B' Hc']].
      exists A', B'. apply AllCompEx__ac_int_l. assumption.
    + destruct (IHT2 mm A B Hc) as [A' [B' Hc']].
      exists A', B'. apply AllCompEx__ac_int_r. assumption.
  - simpl in H. inversion H; subst;
      try match goal with H' : AllCompEx__AComp (typ_record _ _) _ _ |- _ => inversion H' end.
Qed.

(* normal_form_typing preserves a component in both directions (existence). *)
Lemma AllCompEx__AComp_nf_fwd : forall T A B,
  AllCompEx__AComp T A B -> exists A' B', AllCompEx__AComp (normal_form_typing T) A' B'.
Proof.
  induction T; intros A B H.
  - rewrite Dev__nf_top. inversion H.
  - rewrite Dev__nf_bvar. inversion H.
  - rewrite Dev__nf_fvar. exists A, B. apply AllCompEx__ac_fvar.
  - rewrite Dev__nf_arrow. inversion H.
  - rewrite Dev__nf_all. exists (normal_form_typing T1), (normal_form_typing T2). apply AllCompEx__ac_all.
  - rewrite Dev__nf_box. inversion H.
  - rewrite Dev__nf_mut.
    assert (Hc : AllCompEx__AComp T A B) by (apply (AllCompEx__AComp_mut_inv m T A B); assumption).
    destruct (IHT A B Hc) as [A0 [B0 Hc0]].
    destruct (AllCompEx__AComp_merge_fwd (normal_form_typing T) m A0 B0 Hc0)
      as [A' [B' Hc']].
    exists A', B'. assumption.
  - rewrite Dev__nf_int. destruct (AllCompEx__AComp_int_inv _ _ _ _ H) as [Hc | Hc].
    + destruct (IHT1 A B Hc) as [A' [B' Hc']].
      exists A', B'. apply AllCompEx__ac_int_l. assumption.
    + destruct (IHT2 A B Hc) as [A' [B' Hc']].
      exists A', B'. apply AllCompEx__ac_int_r. assumption.
  - rewrite Dev__nf_record. inversion H.
Qed.

Lemma AllCompEx__AComp_nf_rev : forall T A B,
  AllCompEx__AComp (normal_form_typing T) A B -> exists A' B', AllCompEx__AComp T A' B'.
Proof.
  induction T; intros A B H.
  - rewrite Dev__nf_top in H. inversion H.
  - rewrite Dev__nf_bvar in H. inversion H.
  - rewrite Dev__nf_fvar in H. exists A, B. apply AllCompEx__ac_fvar.
  - rewrite Dev__nf_arrow in H. inversion H.
  - rewrite Dev__nf_all in H. destruct (AllCompEx__AComp_all_inv _ _ _ _ H) as [HA HB]. subst A B. exists T1, T2. apply AllCompEx__ac_all.
  - rewrite Dev__nf_box in H. inversion H.
  - rewrite Dev__nf_mut in H.
    destruct (AllCompEx__AComp_merge_rev_exists (normal_form_typing T) m A B H)
      as [A0 [B0 Hc]].
    destruct (IHT A0 B0 Hc) as [A' [B' Hc']].
    exists A', B'. apply AllCompEx__ac_mut. assumption.
  - rewrite Dev__nf_int in H. destruct (AllCompEx__AComp_int_inv _ _ _ _ H) as [Hc | Hc].
    + destruct (IHT1 A B Hc) as [A' [B' Hc']].
      exists A', B'. apply AllCompEx__ac_int_l. assumption.
    + destruct (IHT2 A B Hc) as [A' [B' Hc']].
      exists A', B'. apply AllCompEx__ac_int_r. assumption.
  - rewrite Dev__nf_record in H. inversion H.
Qed.

(* Lifting a target component through a subtyping derivation. *)
Lemma AllCompEx__AComp_lift_sub : forall E S T,
  sub E S T -> forall A B, AllCompEx__AComp T A B -> exists A' B', AllCompEx__AComp S A' B'.
Proof.
  intros E S T Hsub.
  induction Hsub as [ E0 S0 HE0 HS0
                 | E0 X HE0 HS0
                 | U E0 T0 X Hb Hsub IHsub
                 | E0 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E0 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 T1 T2 HEi1 HSi1 HSi2
                 | E0 T1 T2 HEi2 HSi2b HSi2c
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1
                 | E0 T1 T2 HSd1 HSd2 Hsub IHsub ];
  intros A B Hac.
  - inversion Hac.
  - exists A, B. apply AllCompEx__ac_fvar.
  - exists A, B. apply AllCompEx__ac_fvar.
  - inversion Hac.
  - exists S1, S2. apply AllCompEx__ac_all.
  - inversion Hac.
  - destruct (IH1 A B (AllCompEx__AComp_mut_inv mut_readonly T2 A B Hac))
      as [A' [B' Hc]].
    exists A', B'. apply AllCompEx__ac_mut. assumption.
  - destruct (IH1 A B (AllCompEx__AComp_mut_inv mut_readonly T2 A B Hac))
      as [A' [B' Hc]]. exact (ex_intro _ A' (ex_intro _ B' Hc)).
  - destruct (IH2 A B Hac) as [A0 [B0 Hc]].
    destruct (IH1 A0 B0 Hc) as [A' [B' Hc']].
    exists A', B'. assumption.
  - exists A, B. apply AllCompEx__ac_int_l. assumption.
  - exists A, B. apply AllCompEx__ac_int_r. assumption.
  - destruct (AllCompEx__AComp_int_inv _ _ _ _ Hac) as [Hc | Hc].
    + destruct (IH1 A B Hc) as [A' [B' Hc']]. exists A', B'. assumption.
    + destruct (IH2 A B Hc) as [A' [B' Hc']]. exists A', B'. assumption.
  - inversion Hac.
  - inversion Hac; subst;
      try match goal with H' : AllCompEx__AComp (typ_record _ _) _ _ |- _ => inversion H' end.
  - destruct (AllCompEx__AComp_nf_fwd T2 A B Hac) as [A0 [B0 Hc]].
    destruct (IHsub A0 B0 Hc) as [A1 [B1 Hc1]].
    destruct (AllCompEx__AComp_nf_rev T1 A1 B1 Hc1) as [A' [B' Hc']].
    exists A', B'. assumption.
Qed.

Lemma AllCompEx__sub_to_all_comp : forall E S A B,
  sub E S (typ_all A B) -> exists A' B', AllCompEx__AComp S A' B'.
Proof.
  intros. apply (AllCompEx__AComp_lift_sub E S (typ_all A B) H A B (AllCompEx__ac_all A B)).
Qed.

Lemma AllCompEx__AComp_record_comp_false : forall E R r Tr A B,
  typing_record_comp E R r Tr -> AllCompEx__AComp Tr A B -> False.
Proof.
  intros E R r Tr A B H. induction H as
    [ E0 R0 HE HS
    | E0 R0 a e rb T Tr Hnot Hr IHr Hty
    | E0 R0 a l rb T Tr Hnot Hr IHr Hb ];
    intros Hac.
  - inversion Hac.
  - inversion Hac; subst;
      try match goal with H : AllCompEx__AComp (typ_record _ _) _ _ |- False => inversion H end;
      auto.
  - inversion Hac; subst;
      try match goal with H : AllCompEx__AComp (typ_record _ _) _ _ |- False => inversion H end;
      auto.
Qed.




(* ---------------------------------------------------------------- *)
(* All-component analysis of subtyping                              *)
(* ---------------------------------------------------------------- *)

Inductive AllComp__AllComp : typ -> typ -> typ -> Prop :=
  | AllComp__all_comp_all : forall A B, AllComp__AllComp (typ_all A B) A B
  | AllComp__all_comp_fvar : forall X A B, AllComp__AllComp (typ_fvar X) A B
  | AllComp__all_comp_rofvar : forall m X A B, AllComp__AllComp (typ_mut m (typ_fvar X)) A B
  | AllComp__all_comp_int_l : forall X Y A B, AllComp__AllComp X A B -> AllComp__AllComp (typ_int X Y) A B
  | AllComp__all_comp_int_r : forall X Y A B, AllComp__AllComp Y A B -> AllComp__AllComp (typ_int X Y) A B
  | AllComp__all_comp_mut : forall m X A B, AllComp__AllComp X A B -> AllComp__AllComp (typ_mut m X) A B.

Lemma AllComp__AllComp_merge_fwd : forall (T : typ) m A B,
  AllComp__AllComp T A B -> AllComp__AllComp (merge_mutability T m) A B.
Proof.
  intros T m A B H. induction H.
  - rewrite Dev__merge_all. apply AllComp__all_comp_all.
  - rewrite Dev__merge_fvar. apply AllComp__all_comp_rofvar.
  - rewrite Dev__merge_mut. apply AllComp__all_comp_rofvar.
  - rewrite Dev__merge_int. apply AllComp__all_comp_int_l. assumption.
  - rewrite Dev__merge_int. apply AllComp__all_comp_int_r. assumption.
  - rewrite Dev__merge_mut. apply AllComp__all_comp_mut. assumption.
Qed.

Lemma AllComp__AllComp_mut_inv : forall m T A B, AllComp__AllComp (typ_mut m T) A B -> AllComp__AllComp T A B.
Proof. intros. inversion H; subst. - apply AllComp__all_comp_fvar. - assumption. Qed.

Lemma AllComp__AllComp_int_inv : forall X Y A B,
  AllComp__AllComp (typ_int X Y) A B -> AllComp__AllComp X A B \/ AllComp__AllComp Y A B.
Proof. intros. inversion H; subst. - left; assumption. - right; assumption. Qed.

Lemma AllComp__AllComp_all_inv : forall A B C D,
  AllComp__AllComp (typ_all A B) C D -> C = A /\ D = B.
Proof. intros. inversion H; subst. auto. Qed.

(* ---------------------------------------------------------------- *)
(* Basic body-relation helpers                                      *)
(* ---------------------------------------------------------------- *)

Lemma AllComp__wf_body_kind : forall (E : env) A A' B L0,
  (forall X, X `notin` L0 -> wf_typ (X ~ bind_sub A ++ E) (open_tt B X)) ->
  exists L, forall X, X `notin` L ->
    wf_typ (X ~ bind_sub A' ++ E) (open_tt B X).
Proof.
  intros E A A' B L0 H. exists L0. intros X HX.
  eapply Dev__wf_typ_kind.
  - apply H. assumption.
  - intros Z. apply Dev__same_kinds_cons_sub_any. apply Dev__same_kinds_refl.
Qed.

Lemma AllComp__body_sub_refl : forall (E : env) A B L0,
  wf_env E -> wf_typ E A ->
  (forall X, X `notin` L0 -> wf_typ (X ~ bind_sub A ++ E) (open_tt B X)) ->
  exists L, forall X, X `notin` L ->
    sub (X ~ bind_sub A ++ E) (open_tt B X) (open_tt B X).
Proof.
  intros E A B L0 HE HA Hbody.
  exists (L0 `union` dom E). intros X HX.
  assert (HX0 : X `notin` L0) by (apply notin_union_1 in HX; assumption).
  assert (HXd : X `notin` dom E) by (apply notin_union_2 in HX; assumption).
  apply Dev__sub_refl.
  - apply (wf_env_sub E X A HE HA HXd).
  - apply Hbody. assumption.
Qed.

Lemma AllComp__body_wf_of_sub : forall (E : env) A B' B L0 L1,
  wf_env E -> wf_typ E A ->
  (forall X, X `notin` L1 ->
    wf_typ (X ~ bind_sub A ++ E) (open_tt B X)) ->
  (forall X, X `notin` L0 ->
    sub (X ~ bind_sub A ++ E) (open_tt B' X) (open_tt B X)) ->
  exists L, forall X, X `notin` L ->
    wf_typ (X ~ bind_sub A ++ E) (open_tt B' X).
Proof.
  intros E A B' B L0 L1 HE HA HwB Hsub.
  exists ((L0 `union` L1) `union` dom E). intros X HX.
  assert (HX01 : X `notin` (L0 `union` L1))
    by (apply notin_union_1 in HX; assumption).
  assert (HX0 : X `notin` L0) by (apply notin_union_1 in HX01; assumption).
  assert (HX1 : X `notin` L1) by (apply notin_union_2 in HX01; assumption).
  assert (HXd : X `notin` dom E) by (apply notin_union_2 in HX; assumption).
  apply (Dev__sub_wf_source (X ~ bind_sub A ++ E) (open_tt B' X) (open_tt B X)).
  - apply (wf_env_sub E X A HE HA HXd).
  - apply HwB. assumption.
  - apply Hsub. assumption.
Qed.

Lemma AllComp__body_sub_narrow : forall (E1 E2 : env) X U U' B' B,
  X `notin` dom E1 -> X `notin` dom E2 ->
  wf_env (E1 ++ X ~ bind_sub U ++ E2) ->
  wf_typ (E1 ++ X ~ bind_sub U ++ E2) (open_tt B' X) ->
  wf_typ E2 U' ->
  sub E2 U' U ->
  sub (E1 ++ X ~ bind_sub U ++ E2) (open_tt B' X) (open_tt B X) ->
  sub (E1 ++ X ~ bind_sub U' ++ E2) (open_tt B' X) (open_tt B X).
Proof.
  intros. eapply SubNarrow__sub_narrow; eauto.
Qed.


Lemma body_sub_narrow' : forall (E : env) A A' B' B L0 L1,
  wf_env E -> wf_typ E A -> wf_typ E A' -> sub E A A' ->
  (forall X, X `notin` L1 -> wf_typ (X ~ bind_sub A' ++ E) (open_tt B' X)) ->
  (forall X, X `notin` L0 ->
    sub (X ~ bind_sub A' ++ E) (open_tt B' X) (open_tt B X)) ->
  exists L, forall X, X `notin` L ->
    sub (X ~ bind_sub A ++ E) (open_tt B' X) (open_tt B X).
Proof.
  intros E A A' B' B L0 L1 HE HA HA' HsubA Hws Hsub.
  exists ((L0 `union` L1) `union` dom E). intros X HX.
  assert (HX01 : X `notin` (L0 `union` L1))
    by (apply notin_union_1 in HX; assumption).
  assert (HX0 : X `notin` L0) by (apply notin_union_1 in HX01; assumption).
  assert (HX1 : X `notin` L1) by (apply notin_union_2 in HX01; assumption).
  assert (HXd : X `notin` dom E) by (apply notin_union_2 in HX; assumption).
  change (sub (empty ++ X ~ bind_sub A ++ E) (open_tt B' X) (open_tt B X)).
  apply (SubNarrow__sub_narrow empty E X A' A (open_tt B' X) (open_tt B X)).
  - simpl. fsetdec.
  - exact HXd.
  - change (wf_env (X ~ bind_sub A' ++ E)).
    apply (wf_env_sub E X A' HE HA' HXd).
  - change (wf_typ (X ~ bind_sub A' ++ E) (open_tt B' X)).
    apply Hws. assumption.
  - exact HA.
  - exact HsubA.
  - change (sub (X ~ bind_sub A' ++ E) (open_tt B' X) (open_tt B X)).
    apply Hsub. assumption.
Qed.

Lemma AllComp__body_sub_trans : forall (E : env) A B1 B2 B3 L1 L2,
  (forall X, X `notin` L1 ->
    sub (X ~ bind_sub A ++ E) (open_tt B1 X) (open_tt B2 X)) ->
  (forall X, X `notin` L2 ->
    sub (X ~ bind_sub A ++ E) (open_tt B2 X) (open_tt B3 X)) ->
  exists L, forall X, X `notin` L ->
    sub (X ~ bind_sub A ++ E) (open_tt B1 X) (open_tt B3 X).
Proof.
  intros E A B1 B2 B3 L1 L2 H1 H2.
  exists (L1 `union` L2). intros X HX.
  assert (HX1 : X `notin` L1) by (apply notin_union_1 in HX; assumption).
  assert (HX2 : X `notin` L2) by (apply notin_union_2 in HX; assumption).
  eapply sub_trans.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

(* ---------------------------------------------------------------- *)
(* merge_mutability inversion                                       *)
(* ---------------------------------------------------------------- *)

Ltac solve_allcomp_impossible :=
  match goal with
  | H : AllComp__AllComp (typ_bvar _) _ _ |- _ => inversion H
  | H : AllComp__AllComp typ_top _ _ |- _ => inversion H
  | H : AllComp__AllComp (typ_arrow _ _) _ _ |- _ => inversion H
  | H : AllComp__AllComp (typ_box _) _ _ |- _ => inversion H
  | H : AllComp__AllComp (typ_record _ _) _ _ |- _ => inversion H
  | H : AllComp__AllComp (typ_mut _ (typ_bvar _)) _ _ |- _ =>
      inversion H; try solve_allcomp_impossible
  | H : AllComp__AllComp (typ_mut _ (typ_box _)) _ _ |- _ =>
      inversion H; try solve_allcomp_impossible
  | H : AllComp__AllComp (typ_mut _ (typ_record _ _)) _ _ |- _ =>
      inversion H; try solve_allcomp_impossible
  end.

Lemma AllComp__AllComp_merge_rev : forall (E : env) T m A B L0,
  wf_env E -> wf_typ E T -> wf_typ E A ->
  (forall X, X `notin` L0 -> wf_typ (X ~ bind_sub A ++ E) (open_tt B X)) ->
  AllComp__AllComp (merge_mutability T m) A B ->
  exists A' B' L, wf_typ E A' /\ AllComp__AllComp T A' B' /\ sub E A A' /\
    (forall X, X `notin` L -> sub (X ~ bind_sub A ++ E) (open_tt B' X) (open_tt B X)).
Proof.
  intros E T. induction T; intros mm A B L0 HE HT HA Hbody Hac.
  - (* top *) rewrite Dev__merge_top in Hac. inversion Hac.
  - (* bvar *) rewrite Dev__merge_bvar in Hac.
    inversion Hac; subst; try discriminate; try solve_allcomp_impossible.
  - (* fvar *) rewrite Dev__merge_fvar in Hac.
    inversion Hac; subst.
    + destruct (AllComp__body_sub_refl E A B L0 HE HA Hbody) as [L HL].
      exists A, B, L. split.
      * exact HA.
      * split.
        -- apply AllComp__all_comp_fvar.
        -- split.
           ++ apply Dev__sub_refl; assumption.
           ++ apply HL.
    + destruct (AllComp__body_sub_refl E A B L0 HE HA Hbody) as [L HL].
      exists A, B, L. split.
      * exact HA.
      * split.
        -- assumption.
        -- split.
           ++ apply Dev__sub_refl; assumption.
           ++ apply HL.
  - (* arrow *) rewrite Dev__merge_arrow in Hac. inversion Hac.
  - (* all *) rewrite Dev__merge_all in Hac. inversion Hac; subst.
    destruct (AllComp__body_sub_refl E A B L0 HE HA Hbody) as [L HL].
    exists A, B, L. split.
    + exact HA.
    + split.
      * apply AllComp__all_comp_all.
      * split.
        -- apply Dev__sub_refl; assumption.
        -- apply HL.
  - (* box *) rewrite Dev__merge_box in Hac.
    inversion Hac; subst; try discriminate; try solve_allcomp_impossible.
  - (* mut *) rewrite Dev__merge_mut in Hac.
    assert (Hac0 : AllComp__AllComp T A B)
      by (apply AllComp__AllComp_mut_inv with (m := m); exact Hac).
    destruct (AllComp__body_sub_refl E A B L0 HE HA Hbody) as [L HL].
    exists A, B, L. split.
    + exact HA.
    + split.
      * exact Hac.
      * split.
        -- apply Dev__sub_refl; assumption.
        -- apply HL.
  - (* int *) rewrite Dev__merge_int in Hac.
    destruct (AllComp__AllComp_int_inv _ _ _ _ Hac) as [Hc1 | Hc2].
    + destruct (IHT1 mm A B L0 HE (proj1 (Dev__wf_typ_inv_inter _ _ _ HT)) HA Hbody Hc1)
        as [A' [B' [L [HA' [Hac' [HA'' HB']]]]]].
      exists A', B', L. split.
      * exact HA'.
      * split.
        -- apply AllComp__all_comp_int_l. assumption.
        -- split.
           ++ exact HA''.
           ++ exact HB'.
    + destruct (IHT2 mm A B L0 HE (proj2 (Dev__wf_typ_inv_inter _ _ _ HT)) HA Hbody Hc2)
        as [A' [B' [L [HA' [Hac' [HA'' HB']]]]]].
      exists A', B', L. split.
      * exact HA'.
      * split.
        -- apply AllComp__all_comp_int_r. assumption.
        -- split.
           ++ exact HA''.
           ++ exact HB'.
  - (* record *) rewrite Dev__merge_record in Hac.
    inversion Hac; subst; try discriminate; try solve_allcomp_impossible.
Qed.

(* ---------------------------------------------------------------- *)
(* Lifting components to/from normal forms                          *)
(* ---------------------------------------------------------------- *)

Lemma AllComp__AllComp_pair_lift : forall (E : env) T A B L0,
  wf_env E -> wf_typ E T -> wf_typ E A ->
  (forall X, X `notin` L0 -> wf_typ (X ~ bind_sub A ++ E) (open_tt B X)) ->
  AllComp__AllComp T A B ->
  exists A0 B0 L, wf_typ E A0 /\
    AllComp__AllComp (normal_form_typing T) A0 B0 /\
    sub E A A0 /\
    (forall X, X `notin` L -> sub (X ~ bind_sub A ++ E) (open_tt B0 X) (open_tt B X)).
Proof.
  intros E T. induction T; intros A B L0 HE HT HA Hbody Hac.
  - (* top *) inversion Hac.
  - (* bvar *) inversion Hac.
  - (* fvar *) rewrite Dev__nf_fvar.
    destruct (AllComp__body_sub_refl E A B L0 HE HA Hbody) as [L HL].
    exists A, B, L. split.
    + exact HA.
    + split.
      * apply AllComp__all_comp_fvar.
      * split.
        -- apply Dev__sub_refl; assumption.
        -- apply HL.
  - (* arrow *) inversion Hac.
  - (* all *) destruct (AllComp__AllComp_all_inv _ _ _ _ Hac) as [HeqA HeqB].
    subst A. subst B.
    destruct (Dev__wf_typ_inv_all E T1 T2 HT) as [L1 [HwT1 HwT2]].
    exists (normal_form_typing T1), (normal_form_typing T2), (L0 `union` dom E).
    split.
    + apply Dev__wf_typ_nf. assumption.
    + split.
      * rewrite Dev__nf_all. apply AllComp__all_comp_all.
      * split.
        -- apply Dev__sub_to_nf; assumption.
        -- intros X HX.
           assert (HX0 : X `notin` L0) by (apply notin_union_1 in HX; assumption).
           assert (HXd : X `notin` dom E) by (apply notin_union_2 in HX; assumption).
           unfold open_tt. rewrite <- (Dev__nf_open_tt 0 X T2).
           fold open_tt. apply Dev__sub_of_nf.
           ++ apply (wf_env_sub E X T1 HE HwT1 HXd).
           ++ apply Hbody. assumption.
  - (* box *) inversion Hac.
  - (* mut *) assert (Hc : AllComp__AllComp T A B)
        by (apply AllComp__AllComp_mut_inv with (m := m); exact Hac).
    destruct (IHT A B L0 HE (Dev__wf_typ_inv_readonly _ _ _ HT) HA Hbody Hc)
      as [A0 [B0 [L [HA0 [Hac0 [HA0' HB0']]]]]].
    rewrite Dev__nf_mut.
    exists A0, B0, L. split.
    + exact HA0.
    + split.
      * apply AllComp__AllComp_merge_fwd with (m := m). assumption.
      * split; assumption.
  - (* int *) destruct (AllComp__AllComp_int_inv _ _ _ _ Hac) as [Hc | Hc].
    + destruct (IHT1 A B L0 HE (proj1 (Dev__wf_typ_inv_inter _ _ _ HT)) HA Hbody Hc)
        as [A0 [B0 [L [HA0 [Hac0 [HA0' HB0']]]]]].
      rewrite Dev__nf_int. exists A0, B0, L. split.
      * exact HA0.
      * split.
        -- apply AllComp__all_comp_int_l. assumption.
        -- split; assumption.
    + destruct (IHT2 A B L0 HE (proj2 (Dev__wf_typ_inv_inter _ _ _ HT)) HA Hbody Hc)
        as [A0 [B0 [L [HA0 [Hac0 [HA0' HB0']]]]]].
      rewrite Dev__nf_int. exists A0, B0, L. split.
      * exact HA0.
      * split.
        -- apply AllComp__all_comp_int_r. assumption.
        -- split; assumption.
  - (* record *) inversion Hac.
Qed.

Lemma AllComp__AllComp_src_lift : forall (E : env) T A B L0,
  wf_env E -> wf_typ E T -> wf_typ E A ->
  (forall X, X `notin` L0 -> wf_typ (X ~ bind_sub A ++ E) (open_tt B X)) ->
  AllComp__AllComp (normal_form_typing T) A B ->
  exists A' B' L, wf_typ E A' /\ AllComp__AllComp T A' B' /\ sub E A A' /\
    (forall X, X `notin` L -> sub (X ~ bind_sub A ++ E) (open_tt B' X) (open_tt B X)).
Proof.
  intros E T. induction T; intros A B L0 HE HT HA Hbody Hac.
  - (* top *) rewrite Dev__nf_top in Hac. inversion Hac.
  - (* bvar *) rewrite Dev__nf_bvar in Hac. inversion Hac.
  - (* fvar *) rewrite Dev__nf_fvar in Hac.
    destruct (AllComp__body_sub_refl E A B L0 HE HA Hbody) as [L HL].
    exists A, B, L. split.
    + exact HA.
    + split.
      * apply AllComp__all_comp_fvar.
      * split.
        -- apply Dev__sub_refl; assumption.
        -- apply HL.
  - (* arrow *) rewrite Dev__nf_arrow in Hac. inversion Hac.
  - (* all *) rewrite Dev__nf_all in Hac.
    destruct (AllComp__AllComp_all_inv _ _ _ _ Hac) as [HeqA HeqB].
    subst A. subst B.
    destruct (Dev__wf_typ_inv_all E T1 T2 HT) as [L1 [HwT1 HwT2]].
    destruct (AllComp__wf_body_kind E T1 (normal_form_typing T1) T2 L1 HwT2) as [Lw HwT2nf].
    exists T1, T2, (Lw `union` dom E). split.
    + exact HwT1.
    + split.
      * apply AllComp__all_comp_all.
      * split.
        -- apply Dev__sub_of_nf; assumption.
        -- intros X HX.
           assert (HXw : X `notin` Lw) by (apply notin_union_1 in HX; assumption).
           assert (HXd : X `notin` dom E) by (apply notin_union_2 in HX; assumption).
           unfold open_tt. rewrite <- (Dev__nf_open_tt 0 X T2).
           fold open_tt. apply Dev__sub_to_nf.
           ++ apply (wf_env_sub E X (normal_form_typing T1) HE (Dev__wf_typ_nf _ _ HwT1) HXd).
           ++ apply HwT2nf. assumption.
  - (* box *) rewrite Dev__nf_box in Hac. inversion Hac.
  - (* mut *) rewrite Dev__nf_mut in Hac.
    destruct (AllComp__AllComp_merge_rev E (normal_form_typing T) m A B L0 HE
                (Dev__wf_typ_nf _ _ (Dev__wf_typ_inv_readonly _ _ _ HT)) HA Hbody Hac)
      as [A1 [B1 [L1 [HA1 [Hac1 [HA1' HB1']]]]]].
    destruct (AllComp__body_wf_of_sub E A B1 B L1 L0 HE HA Hbody HB1') as [Lw HwA].
    destruct (AllComp__wf_body_kind E A A1 B1 Lw HwA) as [Lw' HwA1].
    destruct (IHT A1 B1 Lw' HE (Dev__wf_typ_inv_readonly _ _ _ HT) HA1 HwA1 Hac1)
      as [A' [B' [L' [HA' [Hac' [HA'' HB']]]]]].
    destruct (AllComp__body_wf_of_sub E A1 B' B1 L' Lw' HE HA1 HwA1 HB') as [Ls Hws].
    destruct (body_sub_narrow' E A A1 B' B1 L' Ls HE HA HA1 HA1' Hws HB')
      as [Ln Hn].
    destruct (AllComp__body_sub_trans E A B' B1 B Ln L1 Hn HB1') as [Lf Hf].
    exists A', B', Lf. split.
    + exact HA'.
    + split.
      * apply AllComp__all_comp_mut. assumption.
      * split.
        -- eapply sub_trans; eauto.
        -- exact Hf.
  - (* int *) rewrite Dev__nf_int in Hac.
    destruct (AllComp__AllComp_int_inv _ _ _ _ Hac) as [Hc | Hc].
    + destruct (IHT1 A B L0 HE (proj1 (Dev__wf_typ_inv_inter _ _ _ HT)) HA Hbody Hc)
        as [A' [B' [L [HA' [Hac' [HA'' HB']]]]]].
      exists A', B', L. split.
      * exact HA'.
      * split.
        -- apply AllComp__all_comp_int_l. assumption.
        -- split; assumption.
    + destruct (IHT2 A B L0 HE (proj2 (Dev__wf_typ_inv_inter _ _ _ HT)) HA Hbody Hc)
        as [A' [B' [L [HA' [Hac' [HA'' HB']]]]]].
      exists A', B', L. split.
      * exact HA'.
      * split.
        -- apply AllComp__all_comp_int_r. assumption.
        -- split; assumption.
  - (* record *) rewrite Dev__nf_record in Hac. inversion Hac.
Qed.

(* ---------------------------------------------------------------- *)
(* Component analysis of subtyping for all-types                    *)
(* ---------------------------------------------------------------- *)

Lemma AllComp__sub_allcomp : forall (E : env) S T,
  wf_env E -> wf_typ E S -> sub E S T ->
  forall A B L0, wf_typ E A ->
    (forall X, X `notin` L0 -> wf_typ (X ~ bind_sub A ++ E) (open_tt B X)) ->
    AllComp__AllComp T A B ->
    exists A' B' L, wf_typ E A' /\ AllComp__AllComp S A' B' /\ sub E A A' /\
      (forall X, X `notin` L -> sub (X ~ bind_sub A ++ E) (open_tt B' X) (open_tt B X)).
Proof.
  intros E S T HE HS Hsub.
  induction Hsub as [ E0 S0 HE0 HS0
                 | E0 X HE0 HS0
                 | U E0 T0 X Hb Hsub0 IHsub0
                 | E0 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | Lr E0 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 T1 T2 HEi1 HSi1 HSi2
                 | E0 T1 T2 HEi2 HSi2a HSi2b
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1
                 | E0 T1 T2 HSd1 HSd2 Hsub0 IHsub0 ];
  intros A B L0 HA Hbody Hac.
  - (* top *) inversion Hac.
  - (* refl tvar *) destruct (AllComp__body_sub_refl E0 A B L0 HE0 HA Hbody) as [L HL].
    exists A, B, L. split.
    + exact HA.
    + split.
      * apply AllComp__all_comp_fvar.
      * split.
        -- apply Dev__sub_refl; assumption.
        -- apply HL.
  - (* trans tvar *) destruct (AllComp__body_sub_refl E0 A B L0 HE HA Hbody) as [L HL].
    exists A, B, L. split.
    + exact HA.
    + split.
      * apply AllComp__all_comp_fvar.
      * split.
        -- apply Dev__sub_refl; assumption.
        -- apply HL.
  - (* arrow *) inversion Hac.
  - (* all *) destruct (AllComp__AllComp_all_inv _ _ _ _ Hac) as [HeqA HeqB].
    subst A. subst B.
    exists S1, S2, (Lr `union` L0). split.
    + apply (Dev__sub_wf_target E0 T1 S1 HE HA H1).
    + split.
      * apply AllComp__all_comp_all.
      * split.
        -- exact H1.
        -- intros X HX.
           assert (HXr : X `notin` Lr) by (apply notin_union_1 in HX; assumption).
           apply H0. assumption.
  - (* box *) inversion Hac.
  - (* readonly *) assert (Hc : AllComp__AllComp T2 A B)
      by (apply AllComp__AllComp_mut_inv with (m := mut_readonly); exact Hac).
    destruct (IH1 HE (Dev__wf_typ_inv_readonly _ _ _ HS) A B L0 HA Hbody Hc)
      as [A' [B' [L [HA' [Hac' [HA'' HB']]]]]].
    exists A', B', L. split.
    + exact HA'.
    + split.
      * apply AllComp__all_comp_mut. assumption.
      * split; assumption.
  - (* readonly mutable *) assert (Hc : AllComp__AllComp T2 A B)
      by (apply AllComp__AllComp_mut_inv with (m := mut_readonly); exact Hac).
    destruct (IH1 HE HS A B L0 HA Hbody Hc)
      as [A' [B' [L [HA' [Hac' [HA'' HB']]]]]].
    exists A', B', L. split.
    + exact HA'.
    + split.
      * exact Hac'.
      * split; assumption.
  - (* trans *) assert (HT2 : wf_typ E0 T2).
    { apply (proj1 (Dev__sub_wf_both E0 T1 T2 H1)); assumption. }
    destruct (IH2 HE HT2 A B L0 HA Hbody Hac)
      as [A1 [B1 [L1 [HA1 [Hac1 [HA1' HB1']]]]]].
    destruct (AllComp__body_wf_of_sub E0 A B1 B L1 L0 HE HA Hbody HB1')
      as [Lw HwA].
    destruct (AllComp__wf_body_kind E0 A A1 B1 Lw HwA) as [Lw' HwA1].
    destruct (IH1 HE HS A1 B1 Lw' HA1 HwA1 Hac1)
      as [A2 [B2 [L2 [HA2 [Hac2 [HA2' HB2']]]]]].
    destruct (AllComp__body_wf_of_sub E0 A1 B2 B1 L2 Lw' HE HA1 HwA1 HB2')
      as [Ls Hws].
    destruct (body_sub_narrow' E0 A A1 B2 B1 L2 Ls HE HA HA1 HA1' Hws HB2')
      as [Ln Hn].
    destruct (AllComp__body_sub_trans E0 A B2 B1 B Ln L1 Hn HB1') as [Lf Hf].
    exists A2, B2, Lf. split.
    + exact HA2.
    + split.
      * exact Hac2.
      * split.
        -- eapply sub_trans; eauto.
        -- exact Hf.
  - (* inter left *) destruct (AllComp__body_sub_refl E0 A B L0 HEi1 HA Hbody) as [L HL].
    exists A, B, L. split.
    + exact HA.
    + split.
      * apply AllComp__all_comp_int_l. assumption.
      * split.
        -- apply Dev__sub_refl; assumption.
        -- apply HL.
  - (* inter right *) destruct (AllComp__body_sub_refl E0 A B L0 HEi2 HA Hbody) as [L HL].
    exists A, B, L. split.
    + exact HA.
    + split.
      * apply AllComp__all_comp_int_r. assumption.
      * split.
        -- apply Dev__sub_refl; assumption.
        -- apply HL.
  - (* inter *) destruct (AllComp__AllComp_int_inv _ _ _ _ Hac) as [Hc | Hc].
    + destruct (IH1 HE HS A B L0 HA Hbody Hc)
        as [A' [B' [L [HA' [Hac' [HA'' HB']]]]]].
      exists A', B', L. split.
      * exact HA'.
      * split.
        -- assumption.
        -- split; assumption.
    + destruct (IH2 HE HS A B L0 HA Hbody Hc)
        as [A' [B' [L [HA' [Hac' [HA'' HB']]]]]].
      exists A', B', L. split.
      * exact HA'.
      * split.
        -- assumption.
        -- split; assumption.
  - (* record *) inversion Hac.
  - (* readonly record *) inversion Hac; subst;
      try discriminate; try solve_allcomp_impossible.
  - (* denormalize *)
    destruct (AllComp__AllComp_pair_lift E0 T2 A B L0 HE HSd2 HA Hbody Hac)
      as [A0 [B0 [L1 [HA0 [Hac0 [HA0' HB0']]]]]].
    destruct (AllComp__body_wf_of_sub E0 A B0 B L1 L0 HE HA Hbody HB0')
      as [Lw HwA].
    destruct (AllComp__wf_body_kind E0 A A0 B0 Lw HwA) as [Lw' HwA0].
    destruct (IHsub0 HE (Dev__wf_typ_nf _ _ HSd1) A0 B0 Lw' HA0 HwA0 Hac0)
      as [A1 [B1 [L2 [HA1 [Hac1 [HA1' HB1']]]]]].
    destruct (AllComp__body_wf_of_sub E0 A0 B1 B0 L2 Lw' HE HA0 HwA0 HB1')
      as [Ls Hws].
    destruct (AllComp__wf_body_kind E0 A0 A1 B1 Ls Hws) as [Ls' Hws1].
    destruct (AllComp__AllComp_src_lift E0 T1 A1 B1 Ls' HE HSd1 HA1 Hws1 Hac1)
      as [A' [B' [L3 [HA' [Hac' [HA'' HB']]]]]].
    destruct (AllComp__body_wf_of_sub E0 A1 B' B1 L3 Ls' HE HA1 Hws1 HB')
      as [Lp Hwp].
    destruct (body_sub_narrow' E0 A0 A1 B' B1 L3 Lp HE HA0 HA1 HA1' Hwp HB')
      as [Lq Hq].
    destruct (AllComp__body_wf_of_sub E0 A0 B1 B0 L2 Lw' HE HA0 HwA0 HB1')
      as [Lr Hwr].
    destruct (body_sub_narrow' E0 A A0 B1 B0 L2 Lr HE HA HA0 HA0' Hwr HB1')
      as [Ls2 Hs2].
    destruct (AllComp__body_wf_of_sub E0 A0 B' B1 Lq Lr HE HA0 Hwr Hq) as [Lq' Hwq].
    destruct (body_sub_narrow' E0 A A0 B' B1 Lq Lq' HE HA HA0 HA0' Hwq Hq)
      as [Lq2 Hq2].
    destruct (AllComp__body_sub_trans E0 A B' B1 B0 Lq2 Ls2 Hq2 Hs2) as [Lm Hm].
    destruct (AllComp__body_sub_trans E0 A B' B0 B Lm L1 Hm HB0') as [Lf Hf].
    exists A', B', Lf. split.
    + exact HA'.
    + split.
      * exact Hac'.
      * split.
        -- eapply sub_trans; [exact HA0' | eapply sub_trans; [exact HA1' | exact HA'']].
        -- exact Hf.
Qed.

(* ---------------------------------------------------------------- *)
(* Inversion of subtyping between two all-types                     *)
(* ---------------------------------------------------------------- *)

Lemma AllComp__sub_all_all : forall (E : env) A B C D,
  wf_env E -> wf_typ E (typ_all A B) -> wf_typ E (typ_all C D) ->
  sub E (typ_all A B) (typ_all C D) ->
  wf_typ E C /\ sub E C A /\
    exists L, forall X, X `notin` L ->
      sub (X ~ bind_sub C ++ E) (open_tt B X) (open_tt D X).
Proof.
  intros E A B C D HE HA HB Hsub.
  destruct (Dev__wf_typ_inv_all E C D HB) as [L0 [HwC HbodyD]].
  destruct (AllComp__sub_allcomp E (typ_all A B) (typ_all C D) HE HA Hsub C D L0
              HwC HbodyD (AllComp__all_comp_all C D))
    as [A' [B' [L [HA' [Hac' [HCA HB']]]]]].
  destruct (AllComp__AllComp_all_inv _ _ _ _ Hac') as [HeqA HeqB].
  subst A'. subst B'.
  split.
  - exact HwC.
  - split.
    + exact HCA.
    + exists L. exact HB'.
Qed.

(* ---------------------------------------------------------------- *)
(* Convenient specialised form with an all-type target              *)
(* ---------------------------------------------------------------- *)

Lemma AllComp__sub_allcomp_target_all : forall (E : env) S A B L0,
  wf_env E -> wf_typ E S -> wf_typ E A ->
  (forall X, X `notin` L0 -> wf_typ (X ~ bind_sub A ++ E) (open_tt B X)) ->
  sub E S (typ_all A B) ->
  exists A' B' L, wf_typ E A' /\ AllComp__AllComp S A' B' /\ sub E A A' /\
    (forall X, X `notin` L -> sub (X ~ bind_sub A ++ E) (open_tt B' X) (open_tt B X)).
Proof.
  intros E S A B L0 HE HS HA Hbody Hsub.
  eapply AllComp__sub_allcomp; eauto.
  apply AllComp__all_comp_all.
Qed.




Lemma Helpers__well_formed_store_of_typing_store : forall E R s,
  typing_store E R s -> well_formed_store s.
Proof.
  intros E R s H l v Hmap.
  destruct (proj2 (H l) v Hmap) as [T [Hval _]]. exact Hval.
Qed.

Lemma Helpers__typing_body_e : forall E R L e T,
  (forall x, x `notin` L -> typing E R (open_ee e x) T) -> body_e e.
Proof.
  intros E R L e T H. exists L. intros x Hx.
  apply (TypingExpr__typing_expr E R (open_ee e x) T (H x Hx)).
Qed.

Lemma Helpers__typing_record_comp_record : forall E R r T,
  typing_record_comp E R r T -> record_comp r.
Proof.
  intros E R r T H. induction H as
    [ E0 R0 HE HS
    | E0 R0 a e rb T0 Tr Hnot Hr IHr Hty
    | E0 R0 a l rb T0 Tr Hnot Hr IHr Hb ].
  - apply record_comp_empty.
  - apply record_comp_exp.
    + apply (TypingExpr__typing_expr E0 R0 e T0 Hty).
    + apply IHr.
  - apply record_comp_ref. apply IHr.
Qed.

Lemma Helpers__no_binds_empty : forall (x : atom) (b : binding),
  binds x b empty -> False.
Proof.
  intros x b H. inversion H.
Qed.

Lemma Helpers__typing_record_comp_sig_weaken : forall E R r T,
  typing_record_comp E R r T ->
  forall R2, wf_sig E (R2 ++ R) -> typing_record_comp E (R2 ++ R) r T.
Proof.
  intros E R r T H. induction H as
    [ E0 R0 HE HS
    | E0 R0 a e rb T0 Tr Hnot Hr IHr Hty
    | E0 R0 a l rb T0 Tr Hnot Hr IHr Hb ];
    intros R2 Hws.
  - apply typing_record_empty; assumption.
  - apply (typing_record_exp E0 (R2 ++ R0) a e rb T0 Tr Hnot
             (IHr R2 Hws) (Store__typing_sig_weaken E0 R0 e T0 Hty R2 Hws)).
  - apply (typing_record_ref E0 (R2 ++ R0) a l rb T0 Tr Hnot
             (IHr R2 Hws)).
    apply Signatures.binds_app_3. exact Hb.
Qed.

Lemma Helpers__typing_readonly_wrap : forall E R e S,
  typing E R e S -> typing E R e (typ_mut mut_readonly S).
Proof.
  intros E R e S Hty.
  assert (Hws : wf_sig E R) by (apply (Store__typing_wf_sig_mut E R e S); assumption).
  assert (HE : wf_env E) by (apply (Dev__wf_sig_wf_env E R); assumption).
  assert (HS : wf_typ E S) by (apply (WfTyping__typing_wf_typ E R e S); assumption).
  apply (typing_sub S E R e (typ_mut mut_readonly S) Hws Hty).
  apply sub_readonly_mutable.
  apply (Dev__sub_refl E S HE HS).
Qed.




(* ================================================================= *)
(* Part A: record field invariance.                                   *)
(*                                                                    *)
(* We introduce a "plain" record-component relation [SubInv__RCompP] which     *)
(* is like [MyWork__RComp] but has no constructor descending under [typ_mut].  *)
(* This is the relation along which record subtyping is genuinely      *)
(* invariant.  (The unrestricted [MyWork__RComp] forgets the reverse subtyping *)
(* at [sub_readonly_record], where records are covariant in the mut    *)
(* wrapper.)                                                          *)
(* ================================================================= *)

Inductive SubInv__RCompP (a : atom) : typ -> typ -> Prop :=
  | SubInv__rcp_here : forall A, SubInv__RCompP a (typ_record a A) A
  | SubInv__rcp_fvar : forall (X : atom) A, SubInv__RCompP a X A
  | SubInv__rcp_int_l : forall X Y A, SubInv__RCompP a X A -> SubInv__RCompP a (typ_int X Y) A
  | SubInv__rcp_int_r : forall X Y A, SubInv__RCompP a Y A -> SubInv__RCompP a (typ_int X Y) A.

Lemma SubInv__RCompP_int_inv : forall (a : atom) X Y A,
  SubInv__RCompP a (typ_int X Y) A -> SubInv__RCompP a X A \/ SubInv__RCompP a Y A.
Proof.
  intros. inversion H; subst. - left; assumption. - right; assumption.
Qed.

Lemma SubInv__RCompP_record_inv : forall (a a0 : atom) A B,
  SubInv__RCompP a (typ_record a0 A) B -> B = A /\ a0 = a.
Proof.
  intros. inversion H; subst. auto.
Qed.

Lemma SubInv__RCompP_heads : forall (a : atom) S C,
  SubInv__RCompP a S C ->
  (exists A, S = typ_record a A /\ C = A) \/
  (exists X, S = typ_fvar X) \/
  (exists U V, S = typ_int U V).
Proof.
  intros a S C H. induction H.
  - left. exists A. split; reflexivity.
  - right. left. exists X. reflexivity.
  - right. right. exists X, Y. reflexivity.
  - right. right. exists X, Y. reflexivity.
Qed.

(* A merge_mutability result never has a plain record component. *)
Lemma SubInv__RCompP_merge_false : forall (a : atom) W m C,
  SubInv__RCompP a (merge_mutability W m) C -> False.
Proof.
  intros a W. induction W; intros mm C Hac.
  - rewrite Dev__merge_top in Hac. inversion Hac.
  - rewrite Dev__merge_bvar in Hac. inversion Hac.
  - rewrite Dev__merge_fvar in Hac. inversion Hac.
  - rewrite Dev__merge_arrow in Hac. inversion Hac.
  - rewrite Dev__merge_all in Hac. inversion Hac.
  - rewrite Dev__merge_box in Hac. inversion Hac.
  - rewrite Dev__merge_mut in Hac. inversion Hac.
  - rewrite Dev__merge_int in Hac.
    destruct (SubInv__RCompP_int_inv a (merge_mutability W1 mm) (merge_mutability W2 mm) C Hac)
      as [Hc | Hc].
    + apply (IHW1 mm C Hc).
    + apply (IHW2 mm C Hc).
  - rewrite Dev__merge_record in Hac. inversion Hac.
Qed.

(* Lifting a plain component through normalisation, preserving the
   component up to subtyping in both directions. *)
Lemma SubInv__RCompP_pair_lift_both : forall (a : atom) (E : env) T A,
  wf_env E -> wf_typ E T -> wf_typ E A -> SubInv__RCompP a T A ->
  exists A0, wf_typ E A0 /\ SubInv__RCompP a (normal_form_typing T) A0 /\
    sub E A A0 /\ sub E A0 A.
Proof.
  intros a E T. induction T; intros A HE HT HA Hac.
  - (* top *) inversion Hac.
  - (* bvar *) inversion Hac.
  - (* fvar *) rewrite Dev__nf_fvar. exists A.
    repeat split; auto; try apply SubInv__rcp_fvar; try (apply Dev__sub_refl; assumption).
  - (* arrow *) inversion Hac.
  - (* all *) inversion Hac.
  - (* box *) inversion Hac.
  - (* mut *) inversion Hac.
  - (* int *) rewrite Dev__nf_int.
    destruct (SubInv__RCompP_int_inv a T1 T2 A Hac) as [Hac2 | Hac2].
    + destruct (IHT1 A HE (proj1 (Dev__wf_typ_inv_inter E T1 T2 HT)) HA Hac2)
        as [A0 [HA0 [Hac0 [Hsub1 Hsub2]]]].
      exists A0. repeat split; auto. apply SubInv__rcp_int_l. assumption.
    + destruct (IHT2 A HE (proj2 (Dev__wf_typ_inv_inter E T1 T2 HT)) HA Hac2)
        as [A0 [HA0 [Hac0 [Hsub1 Hsub2]]]].
      exists A0. repeat split; auto. apply SubInv__rcp_int_r. assumption.
  - (* record *) rewrite Dev__nf_record.
    inversion Hac; subst; try (inversion H2).
    exists (normal_form_typing A). repeat split; auto.
    + apply (Dev__wf_typ_nf E A HA).
    + apply SubInv__rcp_here.
    + apply (Dev__sub_to_nf E A HE HA).
    + apply (Dev__sub_of_nf E A HE HA).
Qed.

(* Lifting a plain component out of a normal form.  The [mut] case is
   vacuous: merging a mutability never produces a plain component. *)
Lemma SubInv__RCompP_src_lift_both : forall (a : atom) (E : env) T A,
  wf_env E -> wf_typ E T -> wf_typ E A ->
  SubInv__RCompP a (normal_form_typing T) A ->
  exists A', wf_typ E A' /\ SubInv__RCompP a T A' /\ sub E A' A /\ sub E A A'.
Proof.
  intros a E T. induction T; intros A HE HT HA Hac.
  - (* top *) rewrite Dev__nf_top in Hac. inversion Hac.
  - (* bvar *) rewrite Dev__nf_bvar in Hac. inversion Hac.
  - (* fvar *) rewrite Dev__nf_fvar in Hac. exists A.
    repeat split; auto; try apply SubInv__rcp_fvar; try (apply Dev__sub_refl; assumption).
  - (* arrow *) rewrite Dev__nf_arrow in Hac. inversion Hac.
  - (* all *) rewrite Dev__nf_all in Hac. inversion Hac.
  - (* box *) rewrite Dev__nf_box in Hac. inversion Hac.
  - (* mut *) rewrite Dev__nf_mut in Hac.
    exfalso. apply (SubInv__RCompP_merge_false a (normal_form_typing T) m A Hac).
  - (* int *) rewrite Dev__nf_int in Hac.
    destruct (SubInv__RCompP_int_inv a (normal_form_typing T1) (normal_form_typing T2) A Hac)
      as [Hac2 | Hac2].
    + destruct (IHT1 A HE (proj1 (Dev__wf_typ_inv_inter E T1 T2 HT)) HA Hac2)
        as [A' [HA' [Hac' [Hsub1 Hsub2]]]].
      exists A'. repeat split; auto. apply SubInv__rcp_int_l. assumption.
    + destruct (IHT2 A HE (proj2 (Dev__wf_typ_inv_inter E T1 T2 HT)) HA Hac2)
        as [A' [HA' [Hac' [Hsub1 Hsub2]]]].
      exists A'. repeat split; auto. apply SubInv__rcp_int_r. assumption.
  - (* record *) rewrite Dev__nf_record in Hac.
    inversion Hac; subst; try (inversion H2).
    exists T. repeat split; auto.
    + apply (Dev__wf_typ_inv_record E a0 T HT).
    + apply SubInv__rcp_here.
    + apply (Dev__sub_to_nf E T HE (Dev__wf_typ_inv_record E a0 T HT)).
    + apply (Dev__sub_of_nf E T HE (Dev__wf_typ_inv_record E a0 T HT)).
Qed.

(* Reverse-directed transport of a plain component along a subtyping. *)
Lemma SubInv__RCompP_rev_transport : forall (a : atom) (E : env) S T,
  wf_env E -> wf_typ E S -> sub E S T ->
  forall C, wf_typ E C -> SubInv__RCompP a T C ->
  exists C', wf_typ E C' /\ SubInv__RCompP a S C' /\ sub E C' C /\ sub E C C'.
Proof.
  intros a E S T HE HS Hsub.
  induction Hsub as [ E0 S0 HE0 HS0
                 | E0 X HE0 HS0
                 | U E0 T0 X Hb Hpre IHpre
                 | E0 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E0 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 T1 T2 HEi1 HSi1 HSi2
                 | E0 T1 T2 HEi2 HSi2b HSi2c
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 a0 T1 T2 H1 IH1 H2 IH2
                 | E0 a0 T1 T2 H1 IH1
                 | E0 T1 T2 HSd1 HSd2 Hsub0 IHsub0 ];
  intros C HC Hac.
  - (* top *) inversion Hac.
  - (* refl tvar *) exists C. repeat split; auto; try apply SubInv__rcp_fvar;
      try (apply Dev__sub_refl; assumption).
  - (* trans tvar *) exists C. repeat split; auto; try apply SubInv__rcp_fvar;
      try (apply Dev__sub_refl; assumption).
  - (* arrow *) inversion Hac.
  - (* all *) inversion Hac.
  - (* box *) inversion Hac.
  - (* readonly *) inversion Hac.
  - (* readonly mutable *) inversion Hac.
  - (* trans *)
    assert (HwT2 : wf_typ E0 T2) by (apply (Dev__sub_wf_target E0 T1 T2 HE HS H1)).
    destruct (IH2 HE HwT2 C HC Hac) as [C2 [HC2 [Hcp2 [Hsub1 Hsub2]]]].
    destruct (IH1 HE HS C2 HC2 Hcp2) as [C' [HC' [Hcp' [Hsub3 Hsub4]]]].
    exists C'. repeat split; auto.
    + eapply sub_trans; eauto.
    + eapply sub_trans; eauto.
  - (* inter left *) exists C. repeat split; auto.
    + apply SubInv__rcp_int_l. assumption.
    + apply Dev__sub_refl; assumption.
    + apply Dev__sub_refl; assumption.
  - (* inter right *) exists C. repeat split; auto.
    + apply SubInv__rcp_int_r. assumption.
    + apply Dev__sub_refl; assumption.
    + apply Dev__sub_refl; assumption.
  - (* inter *) destruct (SubInv__RCompP_int_inv a T2 T3 C Hac) as [Hac2 | Hac2].
    + destruct (IH1 HE HS C HC Hac2) as [C' [HC' [Hcp' [Hsub1 Hsub2]]]].
      exists C'. repeat split; auto.
    + destruct (IH2 HE HS C HC Hac2) as [C' [HC' [Hcp' [Hsub1 Hsub2]]]].
      exists C'. repeat split; auto.
  - (* record *)
    destruct (SubInv__RCompP_record_inv a a0 T2 C Hac) as [HeqC Heqa].
    subst C. subst a0.
    exists T1. split.
    + apply (Dev__wf_typ_inv_record E0 a T1 HS).
    + split.
      * apply SubInv__rcp_here.
      * split; assumption.
  - (* readonly record *) inversion Hac.
  - (* denormalize *)
    destruct (SubInv__RCompP_pair_lift_both a E0 T2 C HE HSd2 HC Hac)
      as [C0 [HC0 [Hcp0 [HsubC1 HsubC2]]]].
    assert (Hnf1 : wf_typ E0 (normal_form_typing T1)) by (apply Dev__wf_typ_nf; assumption).
    destruct (IHsub0 HE Hnf1 C0 HC0 Hcp0) as [C1 [HC1 [Hcp1 [Hsub1 Hsub2]]]].
    destruct (SubInv__RCompP_src_lift_both a E0 T1 C1 HE HSd1 HC1 Hcp1)
      as [C' [HC' [Hcp' [Hsub3 Hsub4]]]].
    exists C'. repeat split; auto.
    + eapply sub_trans; [exact Hsub3 | eapply sub_trans; [exact Hsub1 | exact HsubC2]].
    + eapply sub_trans; [exact HsubC1 | eapply sub_trans; [exact Hsub2 | exact Hsub4]].
Qed.

(* Main inversion: if a *record* subtypes something with a plain component
   [C], then its field is equivalent to [C]. *)
Lemma SubInv__record_src_rcompp : forall (E : env) (S T : typ),
  wf_env E -> wf_typ E S -> sub E S T ->
  forall (a : atom) A C,
    S = typ_record a A -> wf_typ E C -> SubInv__RCompP a T C ->
    sub E A C /\ sub E C A.
Proof.
  intros E S T HE HS Hsub.
  induction Hsub as [ E0 S0 HE0 HS0
                 | E0 X HE0 HS0
                 | U E0 T0 X Hb Hpre IHpre
                 | E0 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E0 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 T1 T2 HEi1 HSi1 HSi2
                 | E0 T1 T2 HEi2 HSi2b HSi2c
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 a0 T1 T2 H1 IH1 H2 IH2
                 | E0 a0 T1 T2 H1 IH1
                 | E0 T1 T2 HSd1 HSd2 Hsub0 IHsub0 ];
  intros a A C Heq HC Hac.
  - (* top *) inversion Hac.
  - (* refl tvar *) discriminate Heq.
  - (* trans tvar *) discriminate Heq.
  - (* arrow *) discriminate Heq.
  - (* all *) discriminate Heq.
  - (* box *) discriminate Heq.
  - (* readonly *) discriminate Heq.
  - (* readonly mutable *) inversion Hac.
  - (* trans *)
    subst T1.
    assert (HwT2 : wf_typ E0 T2)
      by (apply (Dev__sub_wf_target E0 (typ_record a A) T2 HE HS H1)).
    destruct (SubInv__RCompP_rev_transport a E0 T2 T3 HE HwT2 H2 C HC Hac)
      as [C2 [HC2 [Hcp2 [Hsub1 Hsub2]]]].
    destruct (IH1 HE HS a A C2 eq_refl HC2 Hcp2) as [HAC2 HCA2].
    split.
    + eapply sub_trans; eauto.
    + eapply sub_trans; eauto.
  - (* inter left *) discriminate Heq.
  - (* inter right *) discriminate Heq.
  - (* inter *)
    subst T1.
    destruct (SubInv__RCompP_int_inv a T2 T3 C Hac) as [Hac2 | Hac2].
    + apply (IH1 HE HS a A C eq_refl HC Hac2).
    + apply (IH2 HE HS a A C eq_refl HC Hac2).
  - (* record *)
    inversion Heq; subst.
    destruct (SubInv__RCompP_record_inv a a T2 C Hac) as [HeqC _].
    subst C. split; assumption.
  - (* readonly record *) discriminate Heq.
  - (* denormalize *)
    subst T1.
    assert (HA : wf_typ E0 A) by (apply (Dev__wf_typ_inv_record E0 a A HSd1)).
    rewrite Dev__nf_record in Hsub0.
    destruct (SubInv__RCompP_pair_lift_both a E0 T2 C HE HSd2 HC Hac)
      as [C0 [HC0 [Hcp0 [HsubC1 HsubC2]]]].
    assert (HnfS : wf_typ E0 (normal_form_typing (typ_record a A)))
      by (apply Dev__wf_typ_nf; exact HS).
    destruct (IHsub0 HE HnfS a (normal_form_typing A) C0 (Dev__nf_record a A) HC0 Hcp0)
      as [HAC0 HCA0].
    split.
    + eapply sub_trans; [apply (Dev__sub_to_nf E0 A HE HA) |].
      eapply sub_trans; [exact HAC0 | exact HsubC2].
    + eapply sub_trans; [exact HsubC1 |].
      eapply sub_trans; [exact HCA0 | apply (Dev__sub_of_nf E0 A HE HA)].
Qed.

Lemma SubInv__sub_record_record_both : forall (E : env) (a : atom) A B,
  wf_env E -> wf_typ E (typ_record a A) -> wf_typ E (typ_record a B) ->
  sub E (typ_record a A) (typ_record a B) ->
  sub E A B /\ sub E B A.
Proof.
  intros E a A B HE HA HB Hsub.
  apply (SubInv__record_src_rcompp E (typ_record a A) (typ_record a B) HE HA Hsub
           a A B eq_refl (Dev__wf_typ_inv_record E a B HB) (SubInv__rcp_here a B)).
Qed.

(* Precise source characterisation of a record target: the source has a
   plain record component equivalent to the target field.  The naive
   "record or fvar" disjunction is false (e.g. the source may be
   [typ_int (typ_record a B) typ_top]); [SubInv__RCompP] is the correct shape. *)
Lemma SubInv__sub_to_record_src : forall (E : env) (S : typ) (a : atom) B,
  wf_env E -> wf_typ E S -> sub E S (typ_record a B) ->
  exists C, wf_typ E C /\ SubInv__RCompP a S C /\ sub E C B /\ sub E B C.
Proof.
  intros E S a B HE HS Hsub.
  apply (SubInv__RCompP_rev_transport a E S (typ_record a B) HE HS Hsub B
           (Dev__wf_typ_inv_record E a B (Dev__sub_wf_target E S (typ_record a B) HE HS Hsub))
           (SubInv__rcp_here a B)).
Qed.

(* Weaker head-shape corollary. *)
Lemma SubInv__sub_to_record_src_shapes : forall (E : env) (S : typ) (a : atom) B,
  wf_env E -> wf_typ E S -> sub E S (typ_record a B) ->
  (exists C, S = typ_record a C /\ sub E C B /\ sub E B C) \/
  (exists X, S = typ_fvar X) \/
  (exists U V, S = typ_int U V).
Proof.
  intros E S a B HE HS Hsub.
  destruct (SubInv__sub_to_record_src E S a B HE HS Hsub) as [C [HC [Hcp [H1 H2]]]].
  destruct (SubInv__RCompP_heads a S C Hcp) as [Hrec | [Hfvar | Hint]].
  - destruct Hrec as [A [HeqS HeqC]]. subst S. subst C.
    left. exists A. split; [reflexivity | split; assumption].
  - right. left. assumption.
  - right. right. assumption.
Qed.

(* A record never subtypes a type variable.  We use a reachability
   predicate for targets of record-headed sources. *)
Inductive SubInv__RR : typ -> Prop :=
  | SubInv__RR_top : SubInv__RR typ_top
  | SubInv__RR_record : forall (a : atom) C, SubInv__RR (typ_record a C)
  | SubInv__RR_int : forall U V, SubInv__RR U -> SubInv__RR V -> SubInv__RR (typ_int U V)
  | SubInv__RR_mut : forall m T, SubInv__RR T -> SubInv__RR (typ_mut m T).

Lemma SubInv__RR_merge : forall T m, SubInv__RR T -> SubInv__RR (merge_mutability T m).
Proof.
  intros T m H. induction H.
  - rewrite Dev__merge_top. apply SubInv__RR_top.
  - rewrite Dev__merge_record. apply SubInv__RR_mut. apply SubInv__RR_record.
  - rewrite Dev__merge_int. apply SubInv__RR_int; assumption.
  - rewrite Dev__merge_mut. apply SubInv__RR_mut. assumption.
Qed.

Lemma SubInv__RR_merge_rev : forall T m, SubInv__RR (merge_mutability T m) -> SubInv__RR T.
Proof.
  intros T. induction T; intros mm H.
  - rewrite Dev__merge_top in H. exact H.
  - rewrite Dev__merge_bvar in H. inversion H; subst;
      try match goal with H' : SubInv__RR (typ_bvar _) |- _ => inversion H' end.
  - rewrite Dev__merge_fvar in H. inversion H; subst;
      try match goal with H' : SubInv__RR (typ_fvar _) |- _ => inversion H' end.
  - rewrite Dev__merge_arrow in H. inversion H.
  - rewrite Dev__merge_all in H. inversion H.
  - rewrite Dev__merge_box in H. inversion H; subst;
      try match goal with H' : SubInv__RR (typ_box _) |- _ => inversion H' end.
  - rewrite Dev__merge_mut in H. inversion H; subst. apply SubInv__RR_mut. assumption.
  - rewrite Dev__merge_int in H. inversion H; subst. apply SubInv__RR_int.
    + apply (IHT1 mm). assumption.
    + apply (IHT2 mm). assumption.
  - rewrite Dev__merge_record in H. inversion H; assumption.
Qed.

Lemma SubInv__RR_nf : forall T, SubInv__RR T -> SubInv__RR (normal_form_typing T).
Proof.
  intros T H. induction H.
  - rewrite Dev__nf_top. apply SubInv__RR_top.
  - rewrite Dev__nf_record. apply SubInv__RR_record.
  - rewrite Dev__nf_int. apply SubInv__RR_int; assumption.
  - rewrite Dev__nf_mut. apply SubInv__RR_merge. assumption.
Qed.

Lemma SubInv__RR_of_nf : forall T, SubInv__RR (normal_form_typing T) -> SubInv__RR T.
Proof.
  induction T; simpl; intros H.
  - exact H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - apply SubInv__RR_mut. apply IHT. apply (SubInv__RR_merge_rev (normal_form_typing T) m H).
  - inversion H; subst. apply SubInv__RR_int.
    + apply IHT1. assumption.
    + apply IHT2. assumption.
  - apply SubInv__RR_record.
Qed.

Lemma SubInv__sub_rr_closed : forall E S T, SubInv__RR S -> sub E S T -> SubInv__RR T.
Proof.
  intros E S T HNR Hsub. revert HNR.
  induction Hsub as [ E0 S0 HE0 HS0
                 | E0 X HE0 HS0
                 | U E0 T0 X Hb Hpre IHpre
                 | E0 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E0 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 T1 T2 HEi1 HSi1 HSi2
                 | E0 T1 T2 HEi2 HSi2b HSi2c
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1
                 | E0 T1 T2 HSd1 HSd2 Hsub0 IHsub0 ];
  intros HNR.
  - apply SubInv__RR_top.
  - inversion HNR.
  - inversion HNR.
  - inversion HNR.
  - inversion HNR.
  - inversion HNR.
  - inversion HNR; subst. apply SubInv__RR_mut. apply (IH1 H0).
  - apply SubInv__RR_mut. apply (IH1 HNR).
  - assert (H2' : SubInv__RR T2) by (apply IH1; assumption).
    apply (IH2 H2').
  - inversion HNR; subst. assumption.
  - inversion HNR; subst. assumption.
  - apply SubInv__RR_int.
    + apply (IH1 HNR).
    + apply (IH2 HNR).
  - apply SubInv__RR_record.
  - apply SubInv__RR_mut. apply SubInv__RR_record.
  - assert (Hnf : SubInv__RR (normal_form_typing T1)) by (apply SubInv__RR_nf; assumption).
    assert (Hnft : SubInv__RR (normal_form_typing T2)) by (apply (IHsub0 Hnf)).
    apply SubInv__RR_of_nf. exact Hnft.
Qed.

Lemma SubInv__sub_record_fvar_false : forall E (a : atom) A X,
  sub E (typ_record a A) (typ_fvar X) -> False.
Proof.
  intros E a A X H.
  assert (HRR : SubInv__RR (typ_fvar X)).
  { apply (SubInv__sub_rr_closed E (typ_record a A) (typ_fvar X)).
    - apply SubInv__RR_record.
    - exact H. }
  inversion HRR.
Qed.

(* ================================================================= *)
(* Part B: dropping readonly from a source.                           *)
(* ================================================================= *)


(* The universal form [sub E (readonly T) T' -> sub E T T'] is FALSE in
   general: with [T = typ_record a (typ_arrow A B)] and
   [T' = typ_mut mut_readonly (typ_record a typ_top)], the premise holds via
   [sub_readonly_record] from [typ_arrow A B <: typ_top], but the conclusion
   would force [typ_record a (typ_arrow A B) <: typ_record a typ_top], hence
   [typ_top <: typ_arrow A B] by record invariance.  The strongest clean true
   form is therefore the one below: [T] must not itself be a record.  (The
   problematic constructor is precisely [sub_readonly_record].) *)


Lemma SubInv__sub_to_merge_readonly : forall (E : env) U,
  wf_env E -> wf_typ E U -> sub E U (merge_mutability U mut_readonly).
Proof.
  intros E U HE H. induction H as [ E0
                 | U0 E0 X Hb
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | L E0 T1 T2 H1 IH1 H0 IH0
                 | E0 T H1 IH1
                 | E0 T H1 IH1
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 H1 IH1 ].
  - rewrite Dev__merge_top. apply sub_top; [assumption | constructor].
  - rewrite Dev__merge_fvar. apply sub_readonly_mutable.
    apply sub_refl_tvar; [assumption | exact (wf_typ_var U0 E0 X Hb)].
  - rewrite Dev__merge_arrow. apply (Dev__sub_refl E0 (typ_arrow T1 T2) HE
      (wf_typ_arrow E0 T1 T2 H1 H2)).
  - rewrite Dev__merge_all. apply (Dev__sub_refl E0 (typ_all T1 T2) HE
      (wf_typ_all L E0 T1 T2 H1 H0)).
  - rewrite Dev__merge_box. apply sub_readonly_mutable.
    apply (Dev__sub_refl E0 (typ_box T) HE (wf_typ_box E0 T H1)).
  - rewrite Dev__merge_mut. apply (Dev__sub_refl E0 (typ_mut mut_readonly T) HE
      (wf_typ_readonly E0 T H1)).
  - rewrite Dev__merge_int.
    apply sub_inter.
    + eapply sub_trans.
      * apply (sub_inter_left E0 T1 T2); assumption.
      * apply (IH1 HE).
    + eapply sub_trans.
      * apply (sub_inter_right E0 T1 T2); assumption.
      * apply (IH2 HE).
  - rewrite Dev__merge_record. apply sub_readonly_mutable.
    apply Dev__sub_refl; [assumption | apply wf_typ_record; assumption].
Qed.

Lemma SubInv__sub_readonly_drop_top : forall (E : env) T,
  wf_env E -> wf_typ E T ->
  sub E (typ_mut mut_readonly T) typ_top -> sub E T typ_top.
Proof. intros. apply sub_top; assumption. Qed.

Lemma SubInv__sub_readonly_drop_fvar : forall (E : env) T X,
  wf_env E -> wf_typ E T ->
  sub E (typ_mut mut_readonly T) (typ_fvar X) -> sub E T (typ_fvar X).
Proof.
  intros. exfalso. eapply Readonly__sub_readonly_fvar_false; eauto.
Qed.

Lemma SubInv__sub_readonly_drop_box : forall (E : env) T B,
  wf_env E -> wf_typ E T ->
  sub E (typ_mut mut_readonly T) (typ_box B) -> sub E T (typ_box B).
Proof.
  intros. exfalso. eapply Readonly__sub_readonly_box_false; eauto.
Qed.

Lemma SubInv__sub_readonly_drop_record : forall (E : env) T (a : atom) B,
  wf_env E -> wf_typ E T ->
  sub E (typ_mut mut_readonly T) (typ_record a B) -> sub E T (typ_record a B).
Proof.
  intros. exfalso. eapply Readonly__sub_readonly_record_false; eauto.
Qed.

Lemma SubInv__sub_readonly_drop_nonrecord : forall (E : env) T T',
  (forall (a : atom) C, T <> typ_record a C) ->
  wf_env E -> wf_typ E T -> wf_typ E T' ->
  sub E (typ_mut mut_readonly T) T' -> sub E T T'.
Proof.
  intros E T T' Hnr HE HT HT' H.
  remember (typ_mut mut_readonly T) as S eqn:HS.
  revert T Hnr HT HT' HS.
  induction H as [ E0 S0 HE0 HS0
                 | E0 X HE0 HS0
                 | U0 E0 T0 X Hb Hpre IHpre
                 | E0 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E0 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 T1 T2 HEi1 HSi1 HSi2
                 | E0 T1 T2 HEi2 HSi2b HSi2c
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1
                 | E0 T1 T2 HSd1 HSd2 Hsub0 IHsub0 ];
  intros T Hnr HT HT' HS.
  - (* top *) apply sub_top; assumption.
  - (* refl tvar *) discriminate HS.
  - (* trans tvar *) discriminate HS.
  - (* arrow *) discriminate HS.
  - (* all *) discriminate HS.
  - (* box *) discriminate HS.
  - (* readonly *)
    injection HS as Heq. subst T1.
    apply sub_readonly_mutable. exact H1.
  - (* readonly mutable *)
    subst T1.
    assert (HwT2 : wf_typ E0 T2)
      by (apply (Dev__wf_typ_inv_readonly E0 mut_readonly T2 HT')).
    apply sub_readonly_mutable.
    apply (IH1 HE T Hnr HT HwT2 eq_refl).
  - (* trans *)
    subst T1.
    assert (HwT2 : wf_typ E0 T2)
      by (apply (Dev__sub_wf_target E0 (typ_mut mut_readonly T) T2 HE
              (wf_typ_readonly E0 T HT) H1)).
    eapply sub_trans.
    + apply (IH1 HE T Hnr HT HwT2 eq_refl).
    + exact H2.
  - (* inter left *) discriminate HS.
  - (* inter right *) discriminate HS.
  - (* inter *)
    subst T1.
    destruct (Dev__wf_typ_inv_inter E0 T2 T3 HT') as [HwT2 HwT3].
    apply sub_inter.
    + apply (IH1 HE T Hnr HT HwT2 eq_refl).
    + apply (IH2 HE T Hnr HT HwT3 eq_refl).
  - (* record *) discriminate HS.
  - (* readonly record *)
    injection HS as Heq.
    exfalso. apply (Hnr a T1). symmetry. exact Heq.
  - (* denormalize *)
    subst T1.
    assert (Hnf : wf_typ E0 (normal_form_typing T))
      by (apply (Dev__wf_typ_nf E0 T); assumption).
    assert (Hmt : sub E0 (normal_form_typing T)
                    (merge_mutability (normal_form_typing T) mut_readonly))
      by (apply (SubInv__sub_to_merge_readonly E0 (normal_form_typing T)); assumption).
    rewrite Dev__nf_mut in Hsub0.
    eapply sub_trans.
    + apply (Dev__sub_to_nf E0 T HE HT).
    + eapply sub_trans.
      * exact Hmt.
      * eapply sub_trans.
        -- exact Hsub0.
        -- apply (Dev__sub_of_nf E0 T2 HE HSd2).
Qed.

(* ================================================================= *)
(* Part C: target box characterisation.                               *)
(* ================================================================= *)

Lemma SubInv__sub_to_box : forall (E : env) S B,
  wf_env E -> wf_typ E S -> wf_typ E (typ_box B) ->
  sub E S (typ_box B) ->
  exists A, wf_typ E A /\ sub E A B /\ sub E B A /\
    (S = typ_box A \/ MyWork__BoxComp S A).
Proof.
  intros E S B HE HS HB Hsub.
  destruct (MyWork__sub_boxcomp E S (typ_box B) HE HS Hsub B
              (Dev__wf_typ_inv_box E B HB) (MyWork__box_comp_box B))
    as [A [HA [Hac [HAB HBA]]]].
  exists A. repeat split; auto.
Qed.

(* ================================================================= *)
(* Part D: target arrow characterisation.                             *)
(* ================================================================= *)

Lemma SubInv__sub_to_arrow : forall (E : env) S A B,
  wf_env E -> wf_typ E S -> wf_typ E (typ_arrow A B) ->
  sub E S (typ_arrow A B) ->
  exists A' B', wf_typ E A' /\ wf_typ E B' /\
    Dev__ArrComp S A' B' /\ sub E A A' /\ sub E B' B.
Proof.
  intros E S A B HE HS HA Hsub.
  destruct (Dev__wf_typ_inv_arrow E A B HA) as [HA1 HB1].
  apply (Dev__sub_arrcomp E S (typ_arrow A B) HE HS Hsub A B HA1 HB1
           (Dev__arr_comp_arrow A B)).
Qed.




(* ================================================================ *)
(* Basic facts about [record_lookup_ref] and [record_dom]           *)
(* ================================================================ *)

Lemma RecordInv__record_lookup_ref_in_dom : forall (a : atom) (r : rec_comp) (l : label),
  record_lookup_ref a r = Some l -> a `in` record_dom r.
Proof.
  intros a r. induction r as [| a' e r IH | a' l' r IH]; intros l H;
    simpl in *.
  - discriminate H.
  - discriminate H.
  - destruct (a === a') as [Heq | Hneq].
    + apply union_iff. left. apply singleton_iff. symmetry. exact Heq.
    + apply union_iff. right. apply (IH l H).
Qed.

Lemma RecordInv__record_lookup_ref_here : forall (a : atom) (l : label) (r : rec_comp),
  record_lookup_ref a (rec_ref a l r) = Some l.
Proof.
  intros. simpl. rewrite eq_dec_refl. reflexivity.
Qed.

Lemma RecordInv__record_lookup_ref_neq : forall (a a' : atom) (l : label) (r : rec_comp),
  a <> a' ->
  record_lookup_ref a (rec_ref a' l r) = record_lookup_ref a r.
Proof.
  intros a a' l r Hneq. simpl.
  destruct (a === a') as [Heq | Hn].
  - exfalso. apply Hneq. exact Heq.
  - reflexivity.
Qed.

Lemma RecordInv__RComp_record_inv_label : forall (a a0 : atom) (A B : typ),
  MyWork__RComp a (typ_record a0 A) B -> B = A /\ a0 = a.
Proof.
  intros a a0 A B H. inversion H; subst; auto.
Qed.

(* ================================================================ *)
(* Stripping [typing_sub] from a typing of a record literal.        *)
(* ================================================================ *)

Lemma RecordInv__typing_exp_record_inv : forall (E : env) (R : sig) (r : rec_comp) (T : typ),
  typing E R (exp_record r) T ->
  exists Tr, typing_record_comp E R r Tr /\ sub E Tr T.
Proof.
  intros E R r T Hty.
  remember (exp_record r) as e eqn:He.
  revert He.
  revert r.
  induction Hty; intros rr Heq; try discriminate Heq.
  - (* typing_sub *)
    destruct (IHHty rr Heq) as [Tr [Hrc Hsub]].
    exists Tr. split; [exact Hrc | eapply sub_trans; eauto].
  - (* typing_record *)
    injection Heq as Hrr. subst rr.
    exists T. split.
    + exact H.
    + apply Dev__sub_refl.
      * apply (Dev__wf_sig_wf_env E R).
        apply (MyWork__typing_record_comp_wf_sig E R r T H).
      * apply (WfTyping__typing_record_comp_wf_typ E R r T H).
Qed.

(* ================================================================ *)
(* Component analysis: a ref field of a value record component.     *)
(*                                                                  *)
(* If a value record [r] (whose components are all [rec_ref]) has a *)
(* component [A] at label [a], then [a] is a ref field of [r] whose *)
(* label is bound in [R] with some type [Tf], and [Tf] is a         *)
(* subtype of [A].                                                  *)
(* ================================================================ *)

Lemma RecordInv__typing_record_comp_ref_field :
  forall (E : env) (R : sig) (r : rec_comp) (Tr : typ) (a : atom) (A : typ),
    typing_record_comp E R r Tr ->
    value_record_comp r ->
    MyWork__RComp a Tr A ->
    exists l Tf,
      record_lookup_ref a r = Some l /\
      Signatures.binds l (bind_sig Tf) R /\
      sub E Tf A.
Proof.
  intros E R r Tr a A Hrc.
  revert a A.
  induction Hrc as
    [ E0 R0 Hwe Hws
    | E0 R0 a0 e r0 T0 Tr0 Hnotin Hrc0 IH Hty
    | E0 R0 a0 l0 r0 T0 Tr0 Hnotin Hrc0 IH Hb ];
    intros a A Hval Hac.
  - (* rec_empty *) inversion Hac.
  - (* rec_exp: impossible for a value *) inversion Hval.
  - (* rec_ref *)
    inversion Hval as [| a1 l1 r1 Hval0]; subst.
    destruct (MyWork__RComp_int_inv a (typ_record a0 T0) Tr0 A Hac)
      as [Hac1 | Hac1].
    + (* component is the record field of the head *)
      destruct (RecordInv__RComp_record_inv_label a a0 T0 A Hac1) as [HA Ha0].
      subst A. subst a0.
      exists l0, T0. split; [| split].
      * apply RecordInv__record_lookup_ref_here.
      * exact Hb.
      * apply Dev__sub_refl.
        -- apply (Dev__wf_sig_wf_env E0 R0).
           apply (MyWork__typing_record_comp_wf_sig E0 R0 r0 Tr0 Hrc0).
        -- apply (Store__wf_sig_binds E0 R0 l0 T0).
           ++ apply (MyWork__typing_record_comp_wf_sig E0 R0 r0 Tr0 Hrc0).
           ++ exact Hb.
    + (* component comes from the tail *)
      destruct (IH a A Hval0 Hac1)
        as [l [Tf [Hlook [Hbind Hsub]]]].
      exists l, Tf. split; [| split].
      * assert (Hneq : a <> a0).
        { intro Heq. apply Hnotin. rewrite <- Heq.
          exact (RecordInv__record_lookup_ref_in_dom a r0 l Hlook). }
        rewrite (RecordInv__record_lookup_ref_neq a a0 l0 r0 Hneq).
        exact Hlook.
      * exact Hbind.
      * exact Hsub.
Qed.

(* ================================================================ *)
(* Uniqueness of the component carried by a well-typed record at a  *)
(* given label.  These facts let us identify the component [C]      *)
(* produced by the reverse record-subtyping analysis with the       *)
(* actual field type [Tf] of the record literal.                    *)
(* ================================================================ *)

Lemma RecordInv__typing_record_comp_RComp_in_dom :
  forall (E : env) (R : sig) (r : rec_comp) (Tr : typ),
    typing_record_comp E R r Tr ->
    forall (a : atom) (A : typ),
      MyWork__RComp a Tr A -> a `in` record_dom r.
Proof.
  intros E R r Tr Hrc.
  induction Hrc as
    [ E0 R0 Hwe Hws
    | E0 R0 a0 e r0 T0 Tr0 Hnotin Hrc0 IH Hty
    | E0 R0 a0 l0 r0 T0 Tr0 Hnotin Hrc0 IH Hb ];
    intros a A Hac.
  - (* rec_empty *) inversion Hac.
  - (* rec_exp *)
    destruct (MyWork__RComp_int_inv a (typ_record a0 T0) Tr0 A Hac) as [H1 | H1].
    + destruct (RecordInv__RComp_record_inv_label a a0 T0 A H1) as [HA Ha0].
      subst A. subst a0.
      apply union_iff. left. apply singleton_iff. reflexivity.
    + apply union_iff. right. apply (IH a A H1).
  - (* rec_ref *)
    destruct (MyWork__RComp_int_inv a (typ_record a0 T0) Tr0 A Hac) as [H1 | H1].
    + destruct (RecordInv__RComp_record_inv_label a a0 T0 A H1) as [HA Ha0].
      subst A. subst a0.
      apply union_iff. left. apply singleton_iff. reflexivity.
    + apply union_iff. right. apply (IH a A H1).
Qed.

Lemma RecordInv__typing_record_comp_RComp_unique :
  forall (E : env) (R : sig) (r : rec_comp) (Tr : typ),
    typing_record_comp E R r Tr ->
    forall (a : atom) (A B : typ),
      MyWork__RComp a Tr A -> MyWork__RComp a Tr B -> A = B.
Proof.
  intros E R r Tr Hrc.
  induction Hrc as
    [ E0 R0 Hwe Hws
    | E0 R0 a0 e r0 T0 Tr0 Hnotin Hrc0 IH Hty
    | E0 R0 a0 l0 r0 T0 Tr0 Hnotin Hrc0 IH Hb ];
    intros a A B HA HB.
  - (* rec_empty *) inversion HA.
  - (* rec_exp *)
    destruct (MyWork__RComp_int_inv a (typ_record a0 T0) Tr0 A HA) as [HA1 | HA1];
    destruct (MyWork__RComp_int_inv a (typ_record a0 T0) Tr0 B HB) as [HB1 | HB1].
    + destruct (RecordInv__RComp_record_inv_label a a0 T0 A HA1) as [HeqA _].
      destruct (RecordInv__RComp_record_inv_label a a0 T0 B HB1) as [HeqB _].
      subst A. subst B. reflexivity.
    + destruct (RecordInv__RComp_record_inv_label a a0 T0 A HA1) as [HeqA Ha0].
      subst A. subst a0.
      exfalso. apply Hnotin.
      exact (RecordInv__typing_record_comp_RComp_in_dom E0 R0 r0 Tr0 Hrc0 a B HB1).
    + destruct (RecordInv__RComp_record_inv_label a a0 T0 B HB1) as [HeqB Ha0].
      subst B. subst a0.
      exfalso. apply Hnotin.
      exact (RecordInv__typing_record_comp_RComp_in_dom E0 R0 r0 Tr0 Hrc0 a A HA1).
    + apply (IH a A B HA1 HB1).
  - (* rec_ref *)
    destruct (MyWork__RComp_int_inv a (typ_record a0 T0) Tr0 A HA) as [HA1 | HA1];
    destruct (MyWork__RComp_int_inv a (typ_record a0 T0) Tr0 B HB) as [HB1 | HB1].
    + destruct (RecordInv__RComp_record_inv_label a a0 T0 A HA1) as [HeqA _].
      destruct (RecordInv__RComp_record_inv_label a a0 T0 B HB1) as [HeqB _].
      subst A. subst B. reflexivity.
    + destruct (RecordInv__RComp_record_inv_label a a0 T0 A HA1) as [HeqA Ha0].
      subst A. subst a0.
      exfalso. apply Hnotin.
      exact (RecordInv__typing_record_comp_RComp_in_dom E0 R0 r0 Tr0 Hrc0 a B HB1).
    + destruct (RecordInv__RComp_record_inv_label a a0 T0 B HB1) as [HeqB Ha0].
      subst B. subst a0.
      exfalso. apply Hnotin.
      exact (RecordInv__typing_record_comp_RComp_in_dom E0 R0 r0 Tr0 Hrc0 a A HA1).
    + apply (IH a A B HA1 HB1).
Qed.

(* A successful lookup exposes the corresponding component of the
   record's type.  Only [rec_ref] nodes are visible to
   [record_lookup_ref]; a [rec_exp] node in front makes the lookup
   fail. *)
Lemma RecordInv__typing_record_comp_lookup_RComp :
  forall (E : env) (R : sig) (r : rec_comp) (Tr : typ),
    typing_record_comp E R r Tr ->
    forall (a : atom) (l : label) (Tf : typ),
      record_lookup_ref a r = Some l ->
      Signatures.binds l (bind_sig Tf) R ->
      MyWork__RComp a Tr Tf.
Proof.
  intros E R r Tr Hrc.
  induction Hrc as
    [ E0 R0 Hwe Hws
    | E0 R0 a0 e r0 T0 Tr0 Hnotin Hrc0 IH Hty
    | E0 R0 a0 l0 r0 T0 Tr0 Hnotin Hrc0 IH Hb ];
    intros a l Tf Hlook Hbind.
  - (* rec_empty *) simpl in Hlook. discriminate.
  - (* rec_exp *) simpl in Hlook. discriminate.
  - (* rec_ref *)
    simpl in Hlook.
    destruct (a === a0) as [Heq | Hneq].
    + injection Hlook as Hl. subst l. subst a0.
      assert (HTf : T0 = Tf).
      { eapply (Store__wf_sig_binds_uniq E0 R0 l0 T0 Tf).
        - apply (MyWork__typing_record_comp_wf_sig E0 R0 r0 Tr0 Hrc0).
        - exact Hb.
        - exact Hbind. }
      subst Tf. apply MyWork__rc_int_l. apply MyWork__rc_here.
    + apply MyWork__rc_int_r. apply (IH a l Tf Hlook Hbind).
Qed.

(* ================================================================ *)
(* Every [rec_ref] occurring in a well-typed record component is     *)
(* bound in the signature.                                           *)
(* ================================================================ *)

Inductive RecordInv__rec_ref_occ : rec_comp -> atom -> label -> rec_comp -> Prop :=
  | RecordInv__rec_ref_occ_here : forall (a : atom) (l : label) (r : rec_comp),
      RecordInv__rec_ref_occ (rec_ref a l r) a l r
  | RecordInv__rec_ref_occ_exp : forall (a : atom) (e : exp) (r : rec_comp)
                             (a0 : atom) (l : label) (r0 : rec_comp),
      RecordInv__rec_ref_occ r a0 l r0 ->
      RecordInv__rec_ref_occ (rec_exp a e r) a0 l r0
  | RecordInv__rec_ref_occ_ref : forall (a : atom) (l : label) (r : rec_comp)
                             (a0 : atom) (l0 : label) (r0 : rec_comp),
      RecordInv__rec_ref_occ r a0 l0 r0 ->
      RecordInv__rec_ref_occ (rec_ref a l r) a0 l0 r0.

Lemma RecordInv__typing_record_comp_ref_binds :
  forall (E : env) (R : sig) (r : rec_comp) (Tr : typ),
    typing_record_comp E R r Tr ->
    forall (a : atom) (l : label) (r0 : rec_comp),
      RecordInv__rec_ref_occ r a l r0 ->
      exists T, Signatures.binds l (bind_sig T) R.
Proof.
  intros E R r Tr Hrc.
  induction Hrc as
    [ E0 R0 Hwe Hws
    | E0 R0 a0 e r0 T0 Tr0 Hnotin Hrc0 IH Hty
    | E0 R0 a0 l0 r0 T0 Tr0 Hnotin Hrc0 IH Hb ];
    intros a l rr Hocc.
  - inversion Hocc.
  - inversion Hocc; subst. apply (IH a l rr). assumption.
  - inversion Hocc; subst.
    + exists T0. exact Hb.
    + apply (IH a l rr). assumption.
Qed.

(* ================================================================ *)
(* Main lemmas                                                      *)
(* ================================================================ *)

(* Non-readonly record: weak, one-directional form.  The field is a
   ref field, its label is bound in the signature, and its field type
   is a subtype of the field type of the ascribed record type.

   This weak form is kept for compatibility.  Write preservation needs
   to retype the new value at the *literal's* field type [Tf], so the
   reverse component direction [sub E T Tf] and the record-level
   derivation are also required; see [RecordInv__record_field_nonro_strong]
   below. *)
Lemma RecordInv__record_field_nonro : forall (E : env) (R : sig) (r : rec_comp)
                                  (a : atom) (T : typ),
  value_record_comp r ->
  typing E R (exp_record r) (typ_record a T) ->
  exists l Tf,
    record_lookup_ref a r = Some l /\
    Signatures.binds l (bind_sig Tf) R /\
    sub E Tf T.
Proof.
  intros E R r a T Hval Hty.
  destruct (RecordInv__typing_exp_record_inv E R r (typ_record a T) Hty)
    as [Tr [Hrc Hsub]].
  assert (Hws : wf_sig E R)
    by (apply (MyWork__typing_record_comp_wf_sig E R r Tr Hrc)).
  assert (HE : wf_env E) by (apply (Dev__wf_sig_wf_env E R Hws)).
  assert (HTr : wf_typ E Tr)
    by (apply (WfTyping__typing_record_comp_wf_typ E R r Tr Hrc)).
  assert (Hrec : wf_typ E (typ_record a T))
    by (apply (WfTyping__typing_wf_typ E R (exp_record r) (typ_record a T) Hty)).
  assert (HT : wf_typ E T)
    by (apply (Dev__wf_typ_inv_record E a T Hrec)).
  destruct (MyWork__sub_rcomp a E Tr (typ_record a T) HE HTr Hsub T HT
              (MyWork__rc_here a T)) as [A' [HA' [Hac' HsubA]]].
  destruct (RecordInv__typing_record_comp_ref_field E R r Tr a A' Hrc Hval Hac')
    as [l [Tf [Hlook [Hbind HsubT]]]].
  exists l, Tf. split; [exact Hlook | split; [exact Hbind |]].
  eapply sub_trans; eauto.
Qed.

(* Readonly record: the field is a ref field, its label is bound in
   the signature, and its field type is a subtype of the readonly
   record's field type.

   No reverse direction or record-level invariant can be added here:
   unlike [sub_record], [sub_readonly_record] is covariant.  A plain
   record [Tr] can satisfy
     [sub E Tr (typ_mut mut_readonly (typ_record a T))]
   via [sub_readonly_mutable] followed by [sub_readonly_record] using
   only [sub E Tf T]; see the comment on [RecordInv__record_field_nonro_strong]. *)
Lemma RecordInv__record_field_readonly : forall (E : env) (R : sig) (r : rec_comp)
                                     (a : atom) (T : typ),
  value_record_comp r ->
  typing E R (exp_record r) (typ_mut mut_readonly (typ_record a T)) ->
  exists l Tf,
    record_lookup_ref a r = Some l /\
    Signatures.binds l (bind_sig Tf) R /\
    sub E Tf T.
Proof.
  intros E R r a T Hval Hty.
  destruct (RecordInv__typing_exp_record_inv E R r (typ_mut mut_readonly (typ_record a T)) Hty)
    as [Tr [Hrc Hsub]].
  assert (Hws : wf_sig E R)
    by (apply (MyWork__typing_record_comp_wf_sig E R r Tr Hrc)).
  assert (HE : wf_env E) by (apply (Dev__wf_sig_wf_env E R Hws)).
  assert (HTr : wf_typ E Tr)
    by (apply (WfTyping__typing_record_comp_wf_typ E R r Tr Hrc)).
  assert (Hrec : wf_typ E (typ_mut mut_readonly (typ_record a T)))
    by (apply (WfTyping__typing_wf_typ E R (exp_record r)
                 (typ_mut mut_readonly (typ_record a T)) Hty)).
  assert (Hrec' : wf_typ E (typ_record a T))
    by (apply (Dev__wf_typ_inv_readonly E mut_readonly (typ_record a T) Hrec)).
  assert (HT : wf_typ E T)
    by (apply (Dev__wf_typ_inv_record E a T Hrec')).
  destruct (MyWork__sub_rcomp a E Tr (typ_mut mut_readonly (typ_record a T))
              HE HTr Hsub T HT
              (MyWork__rc_mut a mut_readonly (typ_record a T) T (MyWork__rc_here a T)))
    as [A' [HA' [Hac' HsubA]]].
  destruct (RecordInv__typing_record_comp_ref_field E R r Tr a A' Hrc Hval Hac')
    as [l [Tf [Hlook [Hbind HsubT]]]].
  exists l, Tf. split; [exact Hlook | split; [exact Hbind |]].
  eapply sub_trans; eauto.
Qed.

(* ================================================================ *)
(* Strengthened non-readonly field lemma.                            *)
(*                                                                  *)
(* Plain record subtyping is invariant: [sub_record] requires both  *)
(* component directions.  Consequently the component [C] found by   *)
(* [SubInv__sub_to_record_src] at label [a] is equivalent to the target      *)
(* field [T], and uniqueness of record components identifies it      *)
(* with the actual field type [Tf] of the literal.  This yields the  *)
(* missing reverse component subtyping [sub E T Tf] as well as the   *)
(* record-level derivation [sub E (typ_record a Tf) (typ_record a T)]. *)
(*                                                                  *)
(* No analogous reverse fact is available for the readonly target:   *)
(* readonly record subtyping is covariant through                    *)
(* [sub_readonly_record], so a plain record can be ascribed to       *)
(* [typ_mut mut_readonly (typ_record a T)] using only [Tf <: T].     *)
(* ================================================================ *)

Lemma RecordInv__RCompP_RComp : forall (a : atom) (S C : typ),
  SubInv__RCompP a S C -> MyWork__RComp a S C.
Proof.
  intros a S C H. induction H.
  - apply MyWork__rc_here.
  - apply MyWork__rc_fvar.
  - apply MyWork__rc_int_l. assumption.
  - apply MyWork__rc_int_r. assumption.
Qed.

Lemma RecordInv__record_field_nonro_strong :
  forall (E : env) (R : sig) (r : rec_comp) (a : atom) (T : typ),
    value_record_comp r ->
    typing E R (exp_record r) (typ_record a T) ->
    exists l Tf,
      record_lookup_ref a r = Some l /\
      Signatures.binds l (bind_sig Tf) R /\
      sub E Tf T /\
      sub E T Tf /\
      sub E (typ_record a Tf) (typ_record a T).
Proof.
  intros E R r a T Hval Hty.
  destruct (RecordInv__typing_exp_record_inv E R r (typ_record a T) Hty)
    as [Tr [Hrc Hsub]].
  assert (Hws : wf_sig E R)
    by (apply (MyWork__typing_record_comp_wf_sig E R r Tr Hrc)).
  assert (HE : wf_env E) by (apply (Dev__wf_sig_wf_env E R Hws)).
  assert (HTr : wf_typ E Tr)
    by (apply (WfTyping__typing_record_comp_wf_typ E R r Tr Hrc)).
  (* Reverse record-subtyping analysis: [Tr] has a plain component
     [C] at [a], and [C] is equivalent to the target field [T]. *)
  destruct (SubInv__sub_to_record_src E Tr a T HE HTr Hsub)
    as [C [HC [Hcp [HsubCT HsubTC]]]].
  assert (HRCompC : MyWork__RComp a Tr C) by (apply RecordInv__RCompP_RComp; exact Hcp).
  (* The actual field type [Tf] is the component carried at [a]. *)
  destruct (RecordInv__typing_record_comp_ref_field E R r Tr a C Hrc Hval HRCompC)
    as [l [Tf [Hlook [Hbind HsubTfC]]]].
  assert (HRCompTf : MyWork__RComp a Tr Tf)
    by (eapply RecordInv__typing_record_comp_lookup_RComp; eauto).
  assert (Heq : C = Tf)
    by (eapply RecordInv__typing_record_comp_RComp_unique; eauto).
  subst C.
  exists l, Tf. split.
  - exact Hlook.
  - split.
    + exact Hbind.
    + split.
      * (* [Tf <: T] is exactly the reverse-analysis equivalence. *)
        exact HsubCT.
      * split.
        -- (* [T <: Tf] is the missing direction. *)
           exact HsubTC.
        -- (* Record-level invariance follows from both directions. *)
           apply sub_record; assumption.
Qed.




Lemma RecordStrong__RCompP_RComp : forall (a : atom) S A,
  SubInv__RCompP a S A -> MyWork__RComp a S A.
Proof.
  intros a S A H. induction H.
  - apply MyWork__rc_here.
  - apply MyWork__rc_fvar.
  - apply MyWork__rc_int_l. assumption.
  - apply MyWork__rc_int_r. assumption.
Qed.

(* For a non-readonly record target, the store field type and the target
   field type are equivalent: both directions are available. *)
Lemma RecordStrong__record_field_nonro_both : forall (E : env) (R : sig) (r : rec_comp)
                                       (a : atom) (T : typ),
  value_record_comp r ->
  typing E R (exp_record r) (typ_record a T) ->
  exists l Tf,
    record_lookup_ref a r = Some l /\
    Signatures.binds l (bind_sig Tf) R /\
    sub E Tf T /\ sub E T Tf.
Proof.
  intros E R r a T Hval Hty.
  destruct (RecordInv__record_field_nonro E R r a T Hval Hty)
    as [l [Tf [Hlook [Hbind HsubT]]]].
  destruct (RecordInv__typing_exp_record_inv E R r (typ_record a T) Hty)
    as [Tr [Hrc Hsub]].
  assert (Hws : wf_sig E R)
    by (apply (MyWork__typing_record_comp_wf_sig E R r Tr Hrc)).
  assert (HE : wf_env E) by (apply (Dev__wf_sig_wf_env E R Hws)).
  assert (HTr : wf_typ E Tr)
    by (apply (WfTyping__typing_record_comp_wf_typ E R r Tr Hrc)).
  destruct (SubInv__sub_to_record_src E Tr a T HE HTr Hsub)
    as [C [HC [Hcp [HCT HTC]]]].
  assert (HcR : MyWork__RComp a Tr C) by (apply (RecordStrong__RCompP_RComp a Tr C); assumption).
  assert (HfR : MyWork__RComp a Tr Tf)
    by (apply (RecordInv__typing_record_comp_lookup_RComp E R r Tr Hrc a l Tf Hlook Hbind)).
  assert (Heq : C = Tf) by (apply (RecordInv__typing_record_comp_RComp_unique E R r Tr Hrc a C Tf HcR HfR)).
  subst C.
  exists l, Tf. split; [exact Hlook | split; [exact Hbind | split; [exact HCT | exact HTC]]].
Qed.




Lemma CanonicalAll__value_all_tabs : forall E R e A B,
  value e -> typing E R e (typ_all A B) -> wf_env E ->
  exists V body, e = exp_tabs V body.
Proof.
  intros E R e A B Hv Hty HE.
  assert (HWf : wf_typ E (typ_all A B))
    by (apply (WfTyping__typing_wf_typ E R e (typ_all A B)); assumption).
  induction Hv as [ V0 body Hexpr | V0 body Hexpr | l | l | r Hvr | r Hvr ].
  - exfalso.
    destruct (TypingInv__typing_abs_inv E R V0 body (typ_all A B) Hty HE HWf)
      as [T1 [L [Hs _]]].
    destruct (AllCompEx__sub_to_all_comp E (typ_arrow V0 T1) A B Hs) as [A' [B' Hc]].
    inversion Hc.
  - exists V0, body. reflexivity.
  - exfalso.
    destruct (MyWork__typing_ref_inv E R l (typ_all A B) Hty) as [T0 [Hb Hs]].
    destruct (AllCompEx__sub_to_all_comp E (typ_box T0) A B Hs) as [A' [B' Hc]].
    inversion Hc.
  - exfalso.
    destruct (TypingInv__typing_seal_inv E R (exp_ref l) (typ_all A B) Hty HE HWf)
      as [St [Href Hs]].
    destruct (AllCompEx__sub_to_all_comp E (typ_mut mut_readonly St) A B Hs)
      as [A' [B' Hc]].
    assert (Hc' : AllCompEx__AComp St A' B') by (apply (AllCompEx__AComp_mut_inv mut_readonly St A' B' Hc)).
    destruct (MyWork__typing_ref_inv E R l St Href) as [T0 [Hb Hs0]].
    destruct (AllCompEx__AComp_lift_sub E (typ_box T0) St Hs0 A' B' Hc')
      as [A'' [B'' Hc'']].
    inversion Hc''.
  - exfalso.
    destruct (TypingInv__typing_record_inv E R r (typ_all A B) Hty HE HWf) as [Tr [Hr Hs]].
    destruct (AllCompEx__sub_to_all_comp E Tr A B Hs) as [A' [B' Hc]].
    eapply AllCompEx__AComp_record_comp_false; eauto.
  - exfalso.
    destruct (TypingInv__typing_seal_inv E R (exp_record r) (typ_all A B) Hty HE HWf)
      as [St [Hrec Hs]].
    destruct (AllCompEx__sub_to_all_comp E (typ_mut mut_readonly St) A B Hs)
      as [A' [B' Hc]].
    assert (Hc' : AllCompEx__AComp St A' B') by (apply (AllCompEx__AComp_mut_inv mut_readonly St A' B' Hc)).
    destruct (TypingInv__typing_record_inv E R r St Hrec HE
                (WfTyping__typing_wf_typ E R (exp_record r) St Hrec)) as [Tr [Hr Hs0]].
    destruct (AllCompEx__AComp_lift_sub E Tr St Hs0 A' B' Hc') as [A'' [B'' Hc'']].
    eapply AllCompEx__AComp_record_comp_false; eauto.
Qed.




(* ================================================================== *)
(* Type substitution for the locally nameless System F<: variant     *)
(* ================================================================== *)

(* Substitute the free type variable X by U in T.  Because type      *)
(* binders are de Bruijn indices there is no capture problem.        *)
Fixpoint SubstTT__subst_tt (X : atom) (U T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar Y => if (Y === X) then U else typ_fvar Y
  | typ_arrow T1 T2 => typ_arrow (SubstTT__subst_tt X U T1) (SubstTT__subst_tt X U T2)
  | typ_all T1 T2 => typ_all (SubstTT__subst_tt X U T1) (SubstTT__subst_tt X U T2)
  | typ_box T1 => typ_box (SubstTT__subst_tt X U T1)
  | typ_mut M T1 => typ_mut M (SubstTT__subst_tt X U T1)
  | typ_int T1 T2 => typ_int (SubstTT__subst_tt X U T1) (SubstTT__subst_tt X U T2)
  | typ_record a T1 => typ_record a (SubstTT__subst_tt X U T1)
  end.

(* Apply SubstTT__subst_tt to every type annotation of an expression.         *)
Fixpoint SubstTT__subst_te (X : atom) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs (SubstTT__subst_tt X U V) (SubstTT__subst_te X U e1)
  | exp_app e1 e2 => exp_app (SubstTT__subst_te X U e1) (SubstTT__subst_te X U e2)
  | exp_tabs V e1 => exp_tabs (SubstTT__subst_tt X U V) (SubstTT__subst_te X U e1)
  | exp_tapp e1 V => exp_tapp (SubstTT__subst_te X U e1) (SubstTT__subst_tt X U V)
  | exp_let e1 e2 => exp_let (SubstTT__subst_te X U e1) (SubstTT__subst_te X U e2)
  | exp_box e => exp_box (SubstTT__subst_te X U e)
  | exp_unbox e => exp_unbox (SubstTT__subst_te X U e)
  | exp_set_box b e => exp_set_box (SubstTT__subst_te X U b) (SubstTT__subst_te X U e)
  | exp_ref l => exp_ref l
  | exp_seal e => exp_seal (SubstTT__subst_te X U e)
  | exp_record r => exp_record (SubstTT__subst_te_record X U r)
  | exp_record_read e a => exp_record_read (SubstTT__subst_te X U e) a
  | exp_record_write e1 a e2 => exp_record_write (SubstTT__subst_te X U e1) a (SubstTT__subst_te X U e2)
  end
with SubstTT__subst_te_record (X : atom) (U : typ) (r : rec_comp) {struct r} : rec_comp :=
  match r with
  | rec_empty => rec_empty
  | rec_exp a e r => rec_exp a (SubstTT__subst_te X U e) (SubstTT__subst_te_record X U r)
  | rec_ref a l r => rec_ref a l (SubstTT__subst_te_record X U r)
  end.

(* Apply SubstTT__subst_tt to the type of a binding, preserving its kind.     *)
Definition SubstTT__subst_binding (X : atom) (U : typ) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (SubstTT__subst_tt X U T)
  | bind_typ T => bind_typ (SubstTT__subst_tt X U T)
  end.

Fixpoint SubstTT__subst_tt_env (X : atom) (U : typ) (E : env) {struct E} : env :=
  match E with
  | nil => nil
  | (x, b) :: E' => (x, SubstTT__subst_binding X U b) :: SubstTT__subst_tt_env X U E'
  end.

(* Free type-variable atoms occurring in the type annotations of an  *)
(* expression / record component.                                    *)
Fixpoint SubstTT__fv_te (e : exp) : atoms :=
  match e with
  | exp_bvar _ => {}
  | exp_fvar _ => {}
  | exp_abs V e1 => Dev__fv_typ V `union` SubstTT__fv_te e1
  | exp_app e1 e2 => SubstTT__fv_te e1 `union` SubstTT__fv_te e2
  | exp_tabs V e1 => Dev__fv_typ V `union` SubstTT__fv_te e1
  | exp_tapp e1 V => SubstTT__fv_te e1 `union` Dev__fv_typ V
  | exp_let e1 e2 => SubstTT__fv_te e1 `union` SubstTT__fv_te e2
  | exp_box e => SubstTT__fv_te e
  | exp_unbox e => SubstTT__fv_te e
  | exp_set_box b e => SubstTT__fv_te b `union` SubstTT__fv_te e
  | exp_ref _ => {}
  | exp_seal e => SubstTT__fv_te e
  | exp_record r => SubstTT__fv_te_record r
  | exp_record_read e _ => SubstTT__fv_te e
  | exp_record_write e1 _ e2 => SubstTT__fv_te e1 `union` SubstTT__fv_te e2
  end
with SubstTT__fv_te_record (r : rec_comp) : atoms :=
  match r with
  | rec_empty => {}
  | rec_exp _ e r => SubstTT__fv_te e `union` SubstTT__fv_te_record r
  | rec_ref _ _ r => SubstTT__fv_te_record r
  end.

(* ------------------------------------------------------------------ *)
(* Simple commutation / identity facts                                *)
(* ------------------------------------------------------------------ *)

Lemma SubstTT__subst_tt_fvar_eq : forall (X : atom) U,
  SubstTT__subst_tt X U (typ_fvar X) = U.
Proof.
  intros. simpl. destruct (X === X) as [Heq|Hneq].
  - reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

Lemma SubstTT__subst_tt_fvar_neq : forall (X Y : atom) U,
  Y <> X -> SubstTT__subst_tt X U (typ_fvar Y) = typ_fvar Y.
Proof.
  intros X Y U Hneq. simpl.
  destruct (Y === X) as [Heq|Hneq'].
  - exfalso. apply Hneq. exact Heq.
  - reflexivity.
Qed.

Lemma SubstTT__subst_tt_id : forall (X : atom) U T,
  X `notin` Dev__fv_typ T -> SubstTT__subst_tt X U T = T.
Proof.
  intros X U T. induction T; simpl; intros H.
  - reflexivity.
  - reflexivity.
  - destruct (a === X) as [Heq|Hneq].
    + subst a. exfalso. apply (notin_singleton_1 X X H). reflexivity.
    + reflexivity.
  - pose proof (notin_union_1 X _ _ H) as H1.
    pose proof (notin_union_2 X _ _ H) as H2.
    rewrite (IHT1 H1). rewrite (IHT2 H2). reflexivity.
  - pose proof (notin_union_1 X _ _ H) as H1.
    pose proof (notin_union_2 X _ _ H) as H2.
    rewrite (IHT1 H1). rewrite (IHT2 H2). reflexivity.
  - rewrite IHT by assumption. reflexivity.
  - rewrite IHT by assumption. reflexivity.
  - pose proof (notin_union_1 X _ _ H) as H1.
    pose proof (notin_union_2 X _ _ H) as H2.
    rewrite (IHT1 H1). rewrite (IHT2 H2). reflexivity.
  - rewrite IHT by assumption. reflexivity.
Qed.

Lemma SubstTT__subst_tt_bvar : forall (X : atom) U J,
  SubstTT__subst_tt X U (typ_bvar J) = typ_bvar J.
Proof. reflexivity. Qed.

(* A syntactic closedness predicate sufficient for all the opening   *)
(* commutations below.                                               *)
Fixpoint SubstTT__no_bvar (T : typ) : Prop :=
  match T with
  | typ_top => True
  | typ_bvar _ => False
  | typ_fvar _ => True
  | typ_arrow T1 T2 => SubstTT__no_bvar T1 /\ SubstTT__no_bvar T2
  | typ_all T1 T2 => SubstTT__no_bvar T1 /\ SubstTT__no_bvar T2
  | typ_box T1 => SubstTT__no_bvar T1
  | typ_mut _ T1 => SubstTT__no_bvar T1
  | typ_int T1 T2 => SubstTT__no_bvar T1 /\ SubstTT__no_bvar T2
  | typ_record _ T1 => SubstTT__no_bvar T1
  end.

Lemma SubstTT__no_bvar_open_tt : forall (V : typ), SubstTT__no_bvar V ->
  forall K (U : typ), open_tt_rec K U V = V.
Proof.
  intros V. induction V; intros H K Y; simpl in *.
  - reflexivity.
  - destruct H.
  - reflexivity.
  - destruct H as [H1 H2]. rewrite (IHV1 H1). rewrite (IHV2 H2). reflexivity.
  - destruct H as [H1 H2]. rewrite (IHV1 H1). rewrite (IHV2 H2). reflexivity.
  - rewrite (IHV H). reflexivity.
  - rewrite (IHV H). reflexivity.
  - destruct H as [H1 H2]. rewrite (IHV1 H1). rewrite (IHV2 H2). reflexivity.
  - rewrite (IHV H). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Locally closed types: `type` is the right closedness condition.    *)
(* It permits bound de Bruijn variables but no free ones, which is     *)
(* exactly what is needed for opening to leave a type unchanged.       *)
(* ------------------------------------------------------------------ *)

Definition SubstTT__closed_typ (T : typ) : Prop :=
  forall K (U : typ), open_tt_rec K U T = T.

Fixpoint SubstTT__lc_at (d : nat) (T : typ) : Prop :=
  match T with
  | typ_top => True
  | typ_bvar J => J < d
  | typ_fvar _ => True
  | typ_arrow T1 T2 => SubstTT__lc_at d T1 /\ SubstTT__lc_at d T2
  | typ_all T1 T2 => SubstTT__lc_at d T1 /\ SubstTT__lc_at (S d) T2
  | typ_box T1 => SubstTT__lc_at d T1
  | typ_mut _ T1 => SubstTT__lc_at d T1
  | typ_int T1 T2 => SubstTT__lc_at d T1 /\ SubstTT__lc_at d T2
  | typ_record _ T1 => SubstTT__lc_at d T1
  end.

Lemma SubstTT__lc_at_open_iff : forall (T : typ) K Y,
  SubstTT__lc_at K (open_tt_rec K (typ_fvar Y) T) <-> SubstTT__lc_at (S K) T.
Proof.
  induction T; intros K Y; simpl.
  - tauto.
  - destruct (K == n) as [e|Hne]; simpl.
    + subst n. split; intros; [exact (Nat.lt_succ_diag_r K) | exact I].
    + split; intros H.
      * exact (Nat.lt_lt_succ_r n K H).
      * assert (Hle : n <= K) by exact (proj1 (Nat.lt_succ_r n K) H).
        destruct (proj1 (Nat.lt_eq_cases n K) Hle) as [Hlt | Heq].
        -- exact Hlt.
        -- exfalso. apply Hne. symmetry. exact Heq.
  - tauto.
  - rewrite IHT1, IHT2. tauto.
  - rewrite IHT1, IHT2. tauto.
  - rewrite IHT. tauto.
  - rewrite IHT. tauto.
  - rewrite IHT1, IHT2. tauto.
  - rewrite IHT. tauto.
Qed.

Lemma SubstTT__type_lc : forall (T : typ), type T -> SubstTT__lc_at 0 T.
Proof.
  intros T H. induction H as [ | X
    | T1 T2 H1 IH1 H2 IH2
    | L T1 T2 H1 IH1 Hbody IHbody
    | T H1 IH1
    | T H1 IH1
    | T1 T2 H1 IH1 H2 IH2
    | a T1 H1 IH1 ].
  - simpl. exact I.
  - simpl. exact I.
  - simpl. split; assumption.
  - simpl. split.
    + exact IH1.
    + destruct (atom_fresh L) as [X HX].
      exact (proj1 (SubstTT__lc_at_open_iff T2 0 X) (IHbody X HX)).
  - simpl. assumption.
  - simpl. assumption.
  - simpl. split; assumption.
  - simpl. assumption.
Qed.

Lemma SubstTT__lc_at_open_id : forall (T : typ) d, SubstTT__lc_at d T ->
  forall K (U : typ), d <= K -> open_tt_rec K U T = T.
Proof.
  induction T; intros d Hc K U HK; simpl in *.
  - reflexivity.
  - destruct (K == n) eqn:E.
    + exfalso. subst n.
      exact (Nat.lt_irrefl K (Nat.lt_le_trans K d K Hc HK)).
    + reflexivity.
  - reflexivity.
  - destruct Hc as [H1 H2].
    rewrite (IHT1 d H1 K U HK). rewrite (IHT2 d H2 K U HK). reflexivity.
  - destruct Hc as [H1 H2].
    rewrite (IHT1 d H1 K U HK).
    rewrite (IHT2 (S d) H2 (S K) U ltac:(apply le_n_S; exact HK)). reflexivity.
  - rewrite (IHT d Hc K U HK). reflexivity.
  - rewrite (IHT d Hc K U HK). reflexivity.
  - destruct Hc as [H1 H2].
    rewrite (IHT1 d H1 K U HK). rewrite (IHT2 d H2 K U HK). reflexivity.
  - rewrite (IHT d Hc K U HK). reflexivity.
Qed.

Lemma SubstTT__lc_at_closed : forall T, SubstTT__lc_at 0 T -> SubstTT__closed_typ T.
Proof. intros T H K U. apply (SubstTT__lc_at_open_id T 0 H K U). apply Nat.le_0_l. Qed.

Lemma SubstTT__type_closed : forall T, type T -> SubstTT__closed_typ T.
Proof. intros T H. apply SubstTT__lc_at_closed. apply SubstTT__type_lc. assumption. Qed.

Lemma SubstTT__wf_typ_lc : forall (E : env) T, wf_typ E T -> SubstTT__lc_at 0 T.
Proof.
  intros E T H. induction H as [ E
    | U E X Hb
    | E T1 T2 H1 IH1 H2 IH2
    | L E T1 T2 H1 IH1 Hbody IHbody
    | E T H1 IH1
    | E T H1 IH1
    | E T1 T2 H1 IH1 H2 IH2
    | E a T1 H1 IH1 ].
  - simpl. exact I.
  - simpl. exact I.
  - simpl. split; assumption.
  - simpl. split.
    + exact IH1.
    + destruct (atom_fresh L) as [X HX].
      exact (proj1 (SubstTT__lc_at_open_iff T2 0 X) (IHbody X HX)).
  - simpl. assumption.
  - simpl. assumption.
  - simpl. split; assumption.
  - simpl. assumption.
Qed.

Lemma SubstTT__wf_typ_closed : forall (E : env) T, wf_typ E T -> SubstTT__closed_typ T.
Proof. intros E T H. apply SubstTT__lc_at_closed. apply (SubstTT__wf_typ_lc E T H). Qed.


(* ------------------------------------------------------------------ *)
(* Opening and substitution commute (both directions)                 *)
(* ------------------------------------------------------------------ *)

Lemma SubstTT__open_tt_rec_subst_comm : forall K (T : typ) (X : atom) (V : typ) (Y : atom),
  SubstTT__closed_typ V -> Y <> X ->
  open_tt_rec K Y (SubstTT__subst_tt X V T) = SubstTT__subst_tt X V (open_tt_rec K Y T).
Proof.
  intros K T. revert K. induction T; intros K X V Y Hc Hneq; simpl.
  - reflexivity.
  - (* bvar *) destruct (K == n) eqn:E.
    + rewrite SubstTT__subst_tt_fvar_neq; [reflexivity | assumption].
    + reflexivity.
  - (* fvar *) destruct (a === X) as [Heq|Hneq'].
    + subst a. rewrite (Hc K Y). reflexivity.
    + reflexivity.
  - rewrite (IHT1 K X V Y Hc Hneq). rewrite (IHT2 K X V Y Hc Hneq). reflexivity.
  - rewrite (IHT1 K X V Y Hc Hneq). rewrite (IHT2 (S K) X V Y Hc Hneq). reflexivity.
  - rewrite (IHT K X V Y Hc Hneq). reflexivity.
  - rewrite (IHT K X V Y Hc Hneq). reflexivity.
  - rewrite (IHT1 K X V Y Hc Hneq). rewrite (IHT2 K X V Y Hc Hneq). reflexivity.
  - rewrite (IHT K X V Y Hc Hneq). reflexivity.
Qed.

(* Substuting T for the opened variable and also substituting inside T. *)
Lemma SubstTT__open_tt_rec_subst2 : forall K (T2 : typ) (X : atom) (V : typ) (T : typ),
  SubstTT__closed_typ V ->
  SubstTT__subst_tt X V (open_tt_rec K T T2)
  = open_tt_rec K (SubstTT__subst_tt X V T) (SubstTT__subst_tt X V T2).
Proof.
  intros K T2. revert K. induction T2; intros K X V T Hc; simpl.
  - reflexivity.
  - destruct (K == n) eqn:E; reflexivity.
  - destruct (a === X) as [Heq|Hneq].
    + subst a. rewrite (Hc K (SubstTT__subst_tt X V T)). reflexivity.
    + reflexivity.
  - rewrite IHT2_1; auto. rewrite IHT2_2; auto.
  - rewrite IHT2_1; auto. rewrite IHT2_2; auto.
  - rewrite IHT2; auto.
  - rewrite IHT2; auto.
  - rewrite IHT2_1; auto. rewrite IHT2_2; auto.
  - rewrite IHT2; auto.
Qed.

(* The type-level version of the requested open/subst identity.      *)
Lemma SubstTT__open_tt_rec_subst_tt : forall K (T : typ) (X : atom) U,
  X `notin` Dev__fv_typ T ->
  open_tt_rec K U T = SubstTT__subst_tt X U (open_tt_rec K X T).
Proof.
  intros K T. revert K. induction T; intros K X U H; simpl in *.
  - reflexivity.
  - destruct (K == n) eqn:E.
    + rewrite SubstTT__subst_tt_fvar_eq. reflexivity.
    + reflexivity.
  - destruct (a === X) as [Heq|Hneq].
    + subst a. exfalso. apply (notin_singleton_1 X X H). reflexivity.
    + reflexivity.
  - pose proof (notin_union_1 X _ _ H) as H1.
    pose proof (notin_union_2 X _ _ H) as H2.
    rewrite (IHT1 K X U H1). rewrite (IHT2 K X U H2). reflexivity.
  - pose proof (notin_union_1 X _ _ H) as H1.
    pose proof (notin_union_2 X _ _ H) as H2.
    rewrite (IHT1 K X U H1). rewrite (IHT2 (S K) X U H2). reflexivity.
  - rewrite (IHT K X U H). reflexivity.
  - rewrite (IHT K X U H). reflexivity.
  - pose proof (notin_union_1 X _ _ H) as H1.
    pose proof (notin_union_2 X _ _ H) as H2.
    rewrite (IHT1 K X U H1). rewrite (IHT2 K X U H2). reflexivity.
  - rewrite (IHT K X U H). reflexivity.
Qed.

Lemma SubstTT__open_tt_subst_tt : forall (T : typ) (X : atom) U,
  X `notin` Dev__fv_typ T ->
  open_tt T U = SubstTT__subst_tt X U (open_tt T X).
Proof.
  intros. unfold open_tt. apply SubstTT__open_tt_rec_subst_tt. assumption.
Qed.

(* Expression (and record component) version of open/subst identity. *)
Fixpoint SubstTT__open_te_rec_subst_te (e : exp) {struct e} :
  forall K (X : atom) V,
    X `notin` SubstTT__fv_te e ->
    open_te_rec K V e = SubstTT__subst_te X V (open_te_rec K X e)
with SubstTT__open_te_record_rec_subst_te (r : rec_comp) {struct r} :
  forall K (X : atom) V,
    X `notin` SubstTT__fv_te_record r ->
    open_te_record_rec K V r = SubstTT__subst_te_record X V (open_te_record_rec K X r).
Proof.
  - destruct e; intros K X V H; simpl in *; try reflexivity.
    + (* abs *) pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTT__open_tt_rec_subst_tt K t X V H1).
      rewrite (SubstTT__open_te_rec_subst_te e K X V H2). reflexivity.
    + pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTT__open_te_rec_subst_te e1 K X V H1).
      rewrite (SubstTT__open_te_rec_subst_te e2 K X V H2). reflexivity.
    + (* tabs *) pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTT__open_tt_rec_subst_tt K t X V H1).
      rewrite (SubstTT__open_te_rec_subst_te e (S K) X V H2). reflexivity.
    + pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTT__open_te_rec_subst_te e K X V H1).
      rewrite (SubstTT__open_tt_rec_subst_tt K t X V H2). reflexivity.
    + pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTT__open_te_rec_subst_te e1 K X V H1).
      rewrite (SubstTT__open_te_rec_subst_te e2 K X V H2). reflexivity.
    + simpl. rewrite (SubstTT__open_te_rec_subst_te e K X V H). reflexivity.
    + simpl. rewrite (SubstTT__open_te_rec_subst_te e K X V H). reflexivity.
    + pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTT__open_te_rec_subst_te e1 K X V H1).
      rewrite (SubstTT__open_te_rec_subst_te e2 K X V H2). reflexivity.
    + simpl. rewrite (SubstTT__open_te_rec_subst_te e K X V H). reflexivity.
    + simpl. rewrite (SubstTT__open_te_record_rec_subst_te r K X V H). reflexivity.
    + simpl. rewrite (SubstTT__open_te_rec_subst_te e K X V H). reflexivity.
    + pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTT__open_te_rec_subst_te e1 K X V H1).
      rewrite (SubstTT__open_te_rec_subst_te e2 K X V H2). reflexivity.
  - destruct r; intros K X V H; simpl in *.
    + reflexivity.
    + pose proof (notin_union_1 X _ _ H) as H1.
      pose proof (notin_union_2 X _ _ H) as H2.
      simpl. rewrite (SubstTT__open_te_rec_subst_te e K X V H1).
      rewrite (SubstTT__open_te_record_rec_subst_te r K X V H2). reflexivity.
    + simpl. rewrite (SubstTT__open_te_record_rec_subst_te r K X V H). reflexivity.
Qed.

Lemma SubstTT__open_te_subst_te : forall (e : exp) (X : atom) U,
  X `notin` SubstTT__fv_te e ->
  open_te e U = SubstTT__subst_te X U (open_te e X).
Proof.
  intros. unfold open_te. apply SubstTT__open_te_rec_subst_te. assumption.
Qed.

Lemma SubstTT__open_te_record_subst_te : forall (r : rec_comp) (X : atom) U,
  X `notin` SubstTT__fv_te_record r ->
  open_te_record_rec 0 U r = SubstTT__subst_te_record X U (open_te_record_rec 0 X r).
Proof. intros. apply SubstTT__open_te_record_rec_subst_te. assumption. Qed.

(* Expression version of the commutation used when going under a      *)
(* type-binder in the typing substitution induction.                  *)
Fixpoint SubstTT__open_te_rec_comm (e : exp) {struct e} :
  forall K (X : atom) V (Y : atom),
    SubstTT__closed_typ V -> Y <> X ->
    open_te_rec K Y (SubstTT__subst_te X V e) = SubstTT__subst_te X V (open_te_rec K Y e)
with SubstTT__open_te_record_rec_comm (r : rec_comp) {struct r} :
  forall K (X : atom) V (Y : atom),
    SubstTT__closed_typ V -> Y <> X ->
    open_te_record_rec K Y (SubstTT__subst_te_record X V r)
    = SubstTT__subst_te_record X V (open_te_record_rec K Y r).
Proof.
  - destruct e; intros K X V Y Hc Hneq; simpl; try reflexivity.
    + rewrite (SubstTT__open_tt_rec_subst_comm K t X V Y Hc Hneq).
      rewrite (SubstTT__open_te_rec_comm e K X V Y Hc Hneq). reflexivity.
    + rewrite (SubstTT__open_te_rec_comm e1 K X V Y Hc Hneq).
      rewrite (SubstTT__open_te_rec_comm e2 K X V Y Hc Hneq). reflexivity.
    + rewrite (SubstTT__open_tt_rec_subst_comm K t X V Y Hc Hneq).
      rewrite (SubstTT__open_te_rec_comm e (S K) X V Y Hc Hneq). reflexivity.
    + rewrite (SubstTT__open_te_rec_comm e K X V Y Hc Hneq).
      rewrite (SubstTT__open_tt_rec_subst_comm K t X V Y Hc Hneq). reflexivity.
    + rewrite (SubstTT__open_te_rec_comm e1 K X V Y Hc Hneq).
      rewrite (SubstTT__open_te_rec_comm e2 K X V Y Hc Hneq). reflexivity.
    + rewrite (SubstTT__open_te_rec_comm e K X V Y Hc Hneq). reflexivity.
    + rewrite (SubstTT__open_te_rec_comm e K X V Y Hc Hneq). reflexivity.
    + rewrite (SubstTT__open_te_rec_comm e1 K X V Y Hc Hneq).
      rewrite (SubstTT__open_te_rec_comm e2 K X V Y Hc Hneq). reflexivity.
    + rewrite (SubstTT__open_te_rec_comm e K X V Y Hc Hneq). reflexivity.
    + rewrite (SubstTT__open_te_record_rec_comm r K X V Y Hc Hneq). reflexivity.
    + rewrite (SubstTT__open_te_rec_comm e K X V Y Hc Hneq). reflexivity.
    + rewrite (SubstTT__open_te_rec_comm e1 K X V Y Hc Hneq).
      rewrite (SubstTT__open_te_rec_comm e2 K X V Y Hc Hneq). reflexivity.
  - destruct r; intros K X V Y Hc Hneq; simpl.
    + reflexivity.
    + rewrite (SubstTT__open_te_rec_comm e K X V Y Hc Hneq).
      rewrite (SubstTT__open_te_record_rec_comm r K X V Y Hc Hneq). reflexivity.
    + rewrite (SubstTT__open_te_record_rec_comm r K X V Y Hc Hneq). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Well-formedness is preserved by type substitution (the environment *)
(* prefix `A` is substituted; the trailing `E` is unchanged).          *)
(* ------------------------------------------------------------------ *)

Lemma SubstTT__binds_subst_env_A : forall (A : env) E X V Y (b : binding),
  binds Y b A ->
  binds Y (SubstTT__subst_binding X V b) (SubstTT__subst_tt_env X V A ++ E).
Proof.
  induction A as [| [Z c] A IH]; intros E X V Y b Hb; simpl in *.
  - inversion Hb.
  - apply Dev__binds_cons_inv in Hb. destruct Hb as [Heq | Hin].
    + inversion Heq. subst. simpl. left. reflexivity.
    + simpl. right. apply (IH E X V Y b Hin).
Qed.

Lemma SubstTT__binds_subst_env_E : forall (A E : env) X V Y (b : binding),
  binds Y b E ->
  binds Y b (SubstTT__subst_tt_env X V A ++ E).
Proof.
  intros A E X V Y b H. unfold binds. apply in_or_app. right. exact H.
Qed.

Lemma SubstTT__binds_in_A_or_E : forall (A E : env) X U Y (b : binding),
  Y <> X ->
  binds Y b (A ++ X ~ bind_sub U ++ E) ->
  binds Y b A \/ binds Y b E.
Proof.
  intros A E X U Y b Hne H. apply in_app_iff in H. destruct H as [HA | HXE].
  - left. assumption.
  - right. apply in_app_iff in HXE. destruct HXE as [HX | HE].
    + apply Dev__binds_cons_inv in HX. destruct HX as [Heq | Hin].
      * inversion Heq. subst. exfalso. apply Hne. reflexivity.
      * inversion Hin.
    + assumption.
Qed.

Lemma SubstTT__wf_typ_subst_gen : forall (A : env) X U (E : env) T,
  X `notin` dom A ->
  X `notin` dom E ->
  wf_typ (A ++ X ~ bind_sub U ++ E) T ->
  forall V, SubstTT__closed_typ V ->
    wf_typ (SubstTT__subst_tt_env X V A ++ E) V ->
    wf_typ (SubstTT__subst_tt_env X V A ++ E) (SubstTT__subst_tt X V T).
Proof.
  intros A X U E T HndA HndE H.
  remember (A ++ X ~ bind_sub U ++ E) as E0 eqn:He.
  revert A E He HndA HndE.
  induction H as [ E0
                 | U0 E0 Y Hb
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | L E0 T1 T2 H1 IH1 Hbody IHbody
                 | E0 T1 H1 IH1
                 | E0 T1 H1 IH1
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 H1 IH1 ];
    intros A E He HndA HndE V Hclosed HV.
  - constructor.
  - destruct (Y === X) as [Heq | Hneq].
    + subst Y. rewrite SubstTT__subst_tt_fvar_eq. exact HV.
    + rewrite SubstTT__subst_tt_fvar_neq by auto.
      rewrite He in Hb.
      destruct (SubstTT__binds_in_A_or_E A E X U Y (bind_sub U0) Hneq Hb) as [HA | HE].
      * apply (wf_typ_var (SubstTT__subst_tt X V U0) (SubstTT__subst_tt_env X V A ++ E) Y).
        apply (SubstTT__binds_subst_env_A A E X V Y (bind_sub U0) HA).
      * apply (wf_typ_var U0 (SubstTT__subst_tt_env X V A ++ E) Y).
        apply (SubstTT__binds_subst_env_E A E X V Y (bind_sub U0) HE).
  - simpl. constructor.
    + apply (IH1 A E He HndA HndE V Hclosed HV).
    + apply (IH2 A E He HndA HndE V Hclosed HV).
  - simpl.
    set (out := SubstTT__subst_tt_env X V A ++ E).
    apply wf_typ_all with (L := (L `union` {{ X }}) `union` dom out).
    + apply (IH1 A E He HndA HndE V Hclosed HV).
    + intros Y HY.
      pose proof (notin_union_1 Y (L `union` {{ X }}) (dom out) HY) as HYleft.
      pose proof (notin_union_2 Y (L `union` {{ X }}) (dom out) HY) as HYdom.
      pose proof (notin_union_1 Y L {{ X }} HYleft) as HYL.
      pose proof (notin_union_2 Y L {{ X }} HYleft) as HYXmem.
      assert (HYX : Y <> X).
      { apply notin_singleton_1' in HYXmem. symmetry. exact HYXmem. }
      assert (HndA' : X `notin` dom ((Y, bind_sub T1) :: A)).
      { simpl. rewrite add_iff. intros [Heq | Hin].
        - apply HYX. subst. reflexivity.
        - apply HndA. exact Hin. }
      assert (He' : (Y, bind_sub T1) :: E0
                    = ((Y, bind_sub T1) :: A) ++ X ~ bind_sub U ++ E).
      { rewrite He. reflexivity. }
      assert (HV' : wf_typ (SubstTT__subst_tt_env X V ((Y, bind_sub T1) :: A) ++ E) V).
      { simpl. apply Dev__wf_typ_weaken_cons1. exact HV. }
      specialize (IHbody Y HYL ((Y, bind_sub T1) :: A) E He' HndA' HndE V Hclosed HV').
      assert (Hcomm : SubstTT__subst_tt X V (open_tt_rec 0 Y T2)
                      = open_tt_rec 0 Y (SubstTT__subst_tt X V T2)).
      { symmetry. apply (SubstTT__open_tt_rec_subst_comm 0 T2 X V Y Hclosed HYX). }
      unfold open_tt in IHbody.
      rewrite Hcomm in IHbody.
      unfold out. exact IHbody.
  - simpl. constructor. apply (IH1 A E He HndA HndE V Hclosed HV).
  - simpl. constructor. apply (IH1 A E He HndA HndE V Hclosed HV).
  - simpl. constructor.
    + apply (IH1 A E He HndA HndE V Hclosed HV).
    + apply (IH2 A E He HndA HndE V Hclosed HV).
  - simpl. constructor. apply (IH1 A E He HndA HndE V Hclosed HV).
Qed.


Lemma SubstTT__test_in_dom_subst_env : forall (A E : env) X V Y,
  Y `in` dom (SubstTT__subst_tt_env X V A ++ E) <->
  Y `in` dom A \/ Y `in` dom E.
Proof.
  induction A as [| [Z b] A IH]; intros E X V Y; simpl.
  - split; intro H.
    + right. exact H.
    + destruct H as [H|H]; [|exact H].
      exfalso. exact (notin_empty Y H).
  - change (Y `in` dom ((Z, SubstTT__subst_binding X V b) :: (SubstTT__subst_tt_env X V A ++ E))
            <-> Y `in` dom ((Z,b)::A) \/ Y `in` dom E).
    rewrite (Dev__in_dom_cons (SubstTT__subst_tt_env X V A ++ E) Y Z (SubstTT__subst_binding X V b)).
    rewrite (Dev__in_dom_cons A Y Z b).
    rewrite (IH E X V Y).
    tauto.
Qed.

Lemma SubstTT__test_in_dom_app : forall (E F : env) Y,
  Y `in` dom (E ++ F) <-> Y `in` dom E \/ Y `in` dom F.
Proof.
  intros E F Y. rewrite Narrow__dom_app.
  apply union_iff.
Qed.

Lemma SubstTT__test_notin_dom_app : forall (E F : env) Y,
  Y `notin` dom (E ++ F) -> Y `notin` dom E /\ Y `notin` dom F.
Proof.
  intros E F Y H. rewrite Narrow__dom_app in H.
  split; [apply notin_union_1 in H|apply notin_union_2 in H]; exact H.
Qed.

Lemma SubstTT__test_notin_dom_subst_env : forall (A E : env) X V Y,
  Y `notin` dom (SubstTT__subst_tt_env X V A ++ E) <->
  Y `notin` dom A /\ Y `notin` dom E.
Proof.
  intros. split.
  - intro H. split; intro Hin.
    + apply H. apply (proj2 (SubstTT__test_in_dom_subst_env A E X V Y)). left. exact Hin.
    + apply H. apply (proj2 (SubstTT__test_in_dom_subst_env A E X V Y)). right. exact Hin.
  - intros [HA HE] Hin.
    destruct (proj1 (SubstTT__test_in_dom_subst_env A E X V Y) Hin) as [H|H]; auto.
Qed.

Lemma SubstTT__test_binds_mid_sub : forall (A E : env) X U (b : binding),
  X `notin` dom A -> X `notin` dom E ->
  binds X b (A ++ X ~ bind_sub U ++ E) -> b = bind_sub U.
Proof.
  induction A as [| [Z c] A IH]; intros E X U b HA HE Hb; simpl in *.
  - apply Dev__binds_cons_inv in Hb. destruct Hb as [Heq|Hin].
    + inversion Heq. reflexivity.
    + apply Dev__in_dom_binds in Hin. contradiction.
  - apply Dev__binds_cons_inv in Hb. destruct Hb as [Heq|Hin].
    + inversion Heq. subst. simpl in HA. rewrite add_iff in HA.
      exfalso. apply HA. left. reflexivity.
    + simpl in HA. rewrite add_iff in HA.
      apply (IH E X U b).
      * intro Hc. apply HA. right. exact Hc.
      * exact HE.
      * exact Hin.
Qed.

Lemma SubstTT__test_wf_env_cons_bind_sub_inv : forall (E : env) X T,
  wf_env (X ~ bind_sub T ++ E) ->
  wf_env E /\ wf_typ E T /\ X `notin` dom E.
Proof.
  intros. inversion H; subst. repeat split; assumption.
Qed.

Lemma SubstTT__test_wf_env_cons_bind_typ_inv : forall (E : env) x T,
  wf_env (x ~ bind_typ T ++ E) ->
  wf_env E /\ wf_typ E T /\ x `notin` dom E.
Proof.
  intros. inversion H; subst. repeat split; assumption.
Qed.

Lemma SubstTT__wf_env_mid_notin : forall (A E : env) X U,
  wf_env (A ++ X ~ bind_sub U ++ E) ->
  X `notin` dom A /\ X `notin` dom E.
Proof.
  induction A as [| [Y b] A IH]; intros E X U H; simpl in *.
  - destruct (SubstTT__test_wf_env_cons_bind_sub_inv E X U H) as [_ [_ Hnot]].
    split; [simpl; apply notin_empty | exact Hnot].
  - destruct b.
    + destruct (SubstTT__test_wf_env_cons_bind_sub_inv (A ++ X ~ bind_sub U ++ E) Y t H)
        as [Htail [Htyp HnotY]].
      destruct (IH E X U Htail) as [HnotA HnotE].
      split; [|exact HnotE].
      simpl. rewrite add_iff. intros [Heq|Hin].
      * rewrite Heq in HnotY.
        apply HnotY.
        apply (proj2 (SubstTT__test_in_dom_app A (X ~ bind_sub U ++ E) X)). right.
        apply Dev__in_dom_cons. left. reflexivity.
      * apply HnotA. exact Hin.
    + destruct (SubstTT__test_wf_env_cons_bind_typ_inv (A ++ X ~ bind_sub U ++ E) Y t H)
        as [Htail [Htyp HnotY]].
      destruct (IH E X U Htail) as [HnotA HnotE].
      split; [|exact HnotE].
      simpl. rewrite add_iff. intros [Heq|Hin].
      * rewrite Heq in HnotY.
        apply HnotY.
        apply (proj2 (SubstTT__test_in_dom_app A (X ~ bind_sub U ++ E) X)). right.
        apply Dev__in_dom_cons. left. reflexivity.
      * apply HnotA. exact Hin.
Qed.

Lemma SubstTT__wf_env_tail_mid : forall (A E : env) X U,
  wf_env (A ++ X ~ bind_sub U ++ E) -> wf_env E.
Proof.
  induction A as [| [Y b] A IH]; intros E X U H; simpl in *.
  - apply (proj1 (SubstTT__test_wf_env_cons_bind_sub_inv E X U H)).
  - destruct b.
    + apply (IH E X U (proj1 (SubstTT__test_wf_env_cons_bind_sub_inv (A ++ X ~ bind_sub U ++ E) Y t H))).
    + apply (IH E X U (proj1 (SubstTT__test_wf_env_cons_bind_typ_inv (A ++ X ~ bind_sub U ++ E) Y t H))).
Qed.

Lemma SubstTT__wf_env_mid_typ : forall (A E : env) X U,
  wf_env (A ++ X ~ bind_sub U ++ E) -> wf_typ E U.
Proof.
  induction A as [| [Y b] A IH]; intros E X U H; simpl in *.
  - apply (proj1 (proj2 (SubstTT__test_wf_env_cons_bind_sub_inv E X U H))).
  - destruct b.
    + apply (IH E X U (proj1 (SubstTT__test_wf_env_cons_bind_sub_inv (A ++ X ~ bind_sub U ++ E) Y t H))).
    + apply (IH E X U (proj1 (SubstTT__test_wf_env_cons_bind_typ_inv (A ++ X ~ bind_sub U ++ E) Y t H))).
Qed.

Lemma SubstTT__wf_env_subst_gen : forall (A E : env) X U,
  wf_env (A ++ X ~ bind_sub U ++ E) ->
  forall V, SubstTT__closed_typ V -> wf_typ E V ->
  wf_env (SubstTT__subst_tt_env X V A ++ E).
Proof.
  induction A as [| [Y b] A IH]; intros E X U H V Hc HV; simpl in *.
  - apply (proj1 (SubstTT__test_wf_env_cons_bind_sub_inv E X U H)).
  - destruct b as [T|T].
    + destruct (SubstTT__test_wf_env_cons_bind_sub_inv (A ++ X ~ bind_sub U ++ E) Y T H)
        as [Htail [Htyp HnotY]].
      destruct (SubstTT__wf_env_mid_notin A E X U Htail) as [HnotA HnotE].
      apply wf_env_sub.
      * apply (IH E X U Htail V Hc HV).
      * apply (SubstTT__wf_typ_subst_gen A X U E T HnotA HnotE Htyp V Hc).
        apply (Dev__wf_typ_weaken E V HV (SubstTT__subst_tt_env X V A)).
      * apply (proj2 (SubstTT__test_notin_dom_subst_env A E X V Y)).
        split.
        -- destruct (SubstTT__test_notin_dom_app A (X ~ bind_sub U ++ E) Y HnotY) as [HA _].
           exact HA.
        -- destruct (SubstTT__test_notin_dom_app A (X ~ bind_sub U ++ E) Y HnotY) as [_ HXE].
           destruct (SubstTT__test_notin_dom_app (X ~ bind_sub U) E Y HXE) as [_ HE].
           exact HE.
    + destruct (SubstTT__test_wf_env_cons_bind_typ_inv (A ++ X ~ bind_sub U ++ E) Y T H)
        as [Htail [Htyp HnotY]].
      destruct (SubstTT__wf_env_mid_notin A E X U Htail) as [HnotA HnotE].
      apply wf_env_typ.
      * apply (IH E X U Htail V Hc HV).
      * apply (SubstTT__wf_typ_subst_gen A X U E T HnotA HnotE Htyp V Hc).
        apply (Dev__wf_typ_weaken E V HV (SubstTT__subst_tt_env X V A)).
      * apply (proj2 (SubstTT__test_notin_dom_subst_env A E X V Y)).
        split.
        -- destruct (SubstTT__test_notin_dom_app A (X ~ bind_sub U ++ E) Y HnotY) as [HA _].
           exact HA.
        -- destruct (SubstTT__test_notin_dom_app A (X ~ bind_sub U ++ E) Y HnotY) as [_ HXE].
           destruct (SubstTT__test_notin_dom_app (X ~ bind_sub U) E Y HXE) as [_ HE].
           exact HE.
Qed.

Lemma SubstTT__fv_typ_open_tt_fvar_in : forall (T : typ) K (Y X : atom),
  X `in` Dev__fv_typ T -> X `in` Dev__fv_typ (open_tt_rec K (typ_fvar Y) T).
Proof.
  induction T; intros K Y X H.
  - simpl in H. exfalso. exact (notin_empty X H).
  - simpl in H. exfalso. exact (notin_empty X H).
  - simpl. exact H.
  - simpl in H. apply union_iff in H. destruct H as [H|H].
    + simpl. rewrite union_iff. left. apply IHT1 with (K := K). exact H.
    + simpl. rewrite union_iff. right. apply IHT2 with (K := K). exact H.
  - simpl in H. apply union_iff in H. destruct H as [H|H].
    + simpl. rewrite union_iff. left. apply IHT1 with (K := K). exact H.
    + simpl. rewrite union_iff. right. apply IHT2 with (K := S K). exact H.
  - simpl in H. simpl. apply IHT with (K := K). exact H.
  - simpl in H. simpl. apply IHT with (K := K). exact H.
  - simpl in H. apply union_iff in H. destruct H as [H|H].
    + simpl. rewrite union_iff. left. apply IHT1 with (K := K). exact H.
    + simpl. rewrite union_iff. right. apply IHT2 with (K := K). exact H.
  - simpl in H. simpl. apply IHT with (K := K). exact H.
Qed.

Lemma SubstTT__fv_typ_dom : forall (E : env) T,
  wf_typ E T -> forall X, X `in` Dev__fv_typ T -> X `in` dom E.
Proof.
  intros E T H. induction H as [ E
    | U E Z Hb
    | E T1 T2 H1 IH1 H2 IH2
    | L E T1 T2 H1 IH1 Hbody IHbody
    | E T1 H1 IH1
    | E T1 H1 IH1
    | E T1 T2 H1 IH1 H2 IH2
    | E a T1 H1 IH1 ]; intros X Hfv.
  - simpl in Hfv. exfalso. exact (notin_empty X Hfv).
  - simpl in Hfv. apply singleton_iff in Hfv. subst X.
    apply (Dev__in_dom_binds E Z (bind_sub U) Hb).
  - simpl in Hfv. apply union_iff in Hfv. destruct Hfv as [Hfv|Hfv].
    + apply IH1. exact Hfv.
    + apply IH2. exact Hfv.
  - simpl in Hfv. apply union_iff in Hfv. destruct Hfv as [Hfv|Hfv].
    + apply IH1. exact Hfv.
    + destruct (atom_fresh (L `union` {{ X }})) as [Y HY].
      assert (HYL : Y `notin` L) by (apply notin_union_1 in HY; assumption).
      assert (HYX : Y <> X)
        by (apply notin_union_2 in HY; apply notin_singleton_1' in HY; symmetry; exact HY).
      assert (Hfvo : X `in` Dev__fv_typ (open_tt T2 Y))
        by (apply (SubstTT__fv_typ_open_tt_fvar_in T2 0 Y X Hfv)).
      pose proof (IHbody Y HYL X Hfvo) as Hdom.
      simpl in Hdom. rewrite add_iff in Hdom. destruct Hdom as [Heq|Hin].
      * exfalso. exact (HYX Heq).
      * exact Hin.
  - simpl in Hfv. apply IH1. exact Hfv.
  - simpl in Hfv. apply IH1. exact Hfv.
  - simpl in Hfv. apply union_iff in Hfv. destruct Hfv as [Hfv|Hfv].
    + apply IH1. exact Hfv.
    + apply IH2. exact Hfv.
  - simpl in Hfv. apply IH1. exact Hfv.
Qed.

Lemma SubstTT__wf_sig_weaken_prefix : forall (E : env) (R : sig),
  wf_sig E R ->
  forall (F : env), wf_env (F ++ E) -> wf_sig (F ++ E) R.
Proof.
  intros E R H. induction H as [ E0 HE0 | E0 R0 l T Hpre IHpre HT Hnotin ].
  - intros F HF. apply wf_sig_empty. exact HF.
  - intros F HF. apply wf_sig_typ.
    + apply IHpre. exact HF.
    + apply (Dev__wf_typ_weaken E0 T HT F).
    + exact Hnotin.
Qed.

Fixpoint SubstTT__fv_sig (R : sig) : atoms :=
  match R with
  | nil => {}
  | (l, bind_sig T) :: R' => Dev__fv_typ T `union` SubstTT__fv_sig R'
  end.

Lemma SubstTT__wf_sig_subst_gen : forall (A E : env) (R : sig) X U,
  wf_env (A ++ X ~ bind_sub U ++ E) ->
  wf_sig (A ++ X ~ bind_sub U ++ E) R ->
  X `notin` SubstTT__fv_sig R ->
  forall V, SubstTT__closed_typ V -> wf_typ E V ->
  wf_sig (SubstTT__subst_tt_env X V A ++ E) R.
Proof.
  intros A E R X U Hwf H Hfv V Hc HV.
  remember (A ++ X ~ bind_sub U ++ E) as E0 eqn:He.
  revert A E X U Hwf Hfv V Hc HV He.
  induction H as [ E0 HE0 | E0 R0 l T Hpre IHpre HT Hnotin ];
    intros A E X U Hwf Hfv V Hc HV He.
  - subst E0. apply wf_sig_empty.
    apply (SubstTT__wf_env_subst_gen A E X U Hwf V Hc HV).
  - subst E0. apply wf_sig_typ.
    + apply (IHpre A E X U Hwf).
      * simpl in Hfv. apply notin_union_2 in Hfv. exact Hfv.
      * exact Hc.
      * exact HV.
      * reflexivity.

    + assert (HnotinT : X `notin` Dev__fv_typ T)
        by (simpl in Hfv; apply notin_union_1 in Hfv; exact Hfv).
      assert (Heq : SubstTT__subst_tt X V T = T) by (apply SubstTT__subst_tt_id; exact HnotinT).
      rewrite <- Heq.
      destruct (SubstTT__wf_env_mid_notin A E X U Hwf) as [HnotA HnotE].
      apply (SubstTT__wf_typ_subst_gen A X U E T HnotA HnotE HT V Hc).
      apply (Dev__wf_typ_weaken E V HV (SubstTT__subst_tt_env X V A)).
    + exact Hnotin.
Qed.

Lemma SubstTT__wf_typ_incl : forall (E1 : env) T,
  wf_typ E1 T ->
  forall (E2 : env),
    (forall X U, binds X (bind_sub U) E1 -> binds X (bind_sub U) E2) ->
    wf_typ E2 T.
Proof.
  intros E1 T H. induction H; intros E2 Hincl.
  - constructor.
  - apply (wf_typ_var U E2 X). apply Hincl. assumption.
  - constructor; auto.
  - apply wf_typ_all with (L := L); auto.
    intros X HX. apply (H1 X HX (X ~ bind_sub T1 ++ E2)).
    intros Y U Hb. destruct Hb as [Heq | Hin].
    + injection Heq as HY HU. subst. left. reflexivity.
    + right. apply Hincl. assumption.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma SubstTT__sub_weaken_incl : forall (E1 : env) S T,
  wf_env E1 -> wf_typ E1 S -> sub E1 S T ->
  forall (E2 : env), wf_env E2 ->
  (forall x b, binds x b E1 -> binds x b E2) ->
  sub E2 S T.
Proof.
  intros E1 S T HE1 HS1 Hsub.
  revert HE1 HS1.
  induction Hsub as [ E1 S HE0 HS0
                 | E1 X HE0 HS0
                 | U E1 T0 X Hb Hsub IHsub
                 | E1 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E1 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E1 T1 T2 H1 IH1 H2 IH2
                 | E1 T1 T2 H1 IH1
                 | E1 T1 T2 H1 IH1
                 | E1 T1 T2 T3 H1 IH1 H2 IH2
                 | E1 T1 T2 HEi1 HSi1 HSi2
                 | E1 T1 T2 HEi2 HSi2b HSi2c
                 | E1 T1 T2 T3 H1 IH1 H2 IH2
                 | E1 a T1 T2 H1 IH1 H2 IH2
                 | E1 a T1 T2 H1 IH1
                 | E1 T1 T2 HSd1 HSd2 Hsub IHsub ];
    intros HE1 HS1 E2 HE2 Hincl.
  - apply sub_top; [assumption |].
    apply (SubstTT__wf_typ_incl E1 S HS1 E2). intros X U Hb. apply Hincl. assumption.
  - apply sub_refl_tvar; [assumption |].
    apply (SubstTT__wf_typ_incl E1 (typ_fvar X) HS1 E2). intros Y U Hb. apply Hincl. assumption.
  - apply (sub_trans_tvar U E2 T0 X).
    + apply Hincl. assumption.
    + apply (IHsub HE1 (Dev__wf_env_binds_sub _ HE1 X U Hb) E2 HE2 Hincl).
  - destruct (Dev__wf_typ_inv_arrow _ _ _ HS1) as [HSa HSb].
    assert (HT1 : wf_typ E1 T1) by (apply (Dev__sub_wf_source E1 T1 S1 HE1 HSa H1)).
    apply sub_arrow.
    + apply (IH1 HE1 HT1 E2 HE2 Hincl).
    + apply (IH2 HE1 HSb E2 HE2 Hincl).
  - destruct (Dev__wf_typ_inv_all _ _ _ HS1) as [L1 [HSa HSb]].
    apply (sub_all (L0 `union` L1 `union` dom E1 `union` dom E2) E2 S1 S2 T1 T2).
    + assert (HT1 : wf_typ E1 T1) by (apply (Dev__sub_wf_source E1 T1 S1 HE1 HSa H1)).
      apply (IH1 HE1 HT1 E2 HE2 Hincl).
    + intros Y HY.
      assert (HYL0 : Y `notin` L0) by (apply notin_union_1 in HY; assumption).
      assert (HYL1 : Y `notin` L1) by (apply notin_union_2 in HY; apply notin_union_1 in HY; assumption).
      assert (HYd1 : Y `notin` dom E1)
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; apply notin_union_1 in HY; assumption).
      assert (HYd : Y `notin` dom E2)
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; apply notin_union_2 in HY; assumption).
      assert (HT1s : wf_typ E1 T1) by (apply (Dev__sub_wf_source E1 T1 S1 HE1 HSa H1)).
      assert (HT1 : wf_typ E2 T1).
      { apply (SubstTT__wf_typ_incl E1 T1 HT1s E2). intros X U Hb. apply Hincl. assumption. }
      assert (Hwe1 : wf_env (Y ~ bind_sub T1 ++ E1)).
      { apply (wf_env_sub E1 Y T1); [exact HE1 | exact HT1s | exact HYd1]. }
      assert (Hwe2 : wf_env (Y ~ bind_sub T1 ++ E2)).
      { apply (wf_env_sub E2 Y T1); [exact HE2 | exact HT1 | exact HYd]. }
      assert (HSbT : wf_typ (Y ~ bind_sub T1 ++ E1) (open_tt S2 Y)).
      { apply (Dev__wf_typ_kind (Y ~ bind_sub S1 ++ E1) (open_tt S2 Y) (HSb Y HYL1)
                 (Y ~ bind_sub T1 ++ E1)).
        apply Dev__same_kinds_cons_sub_any. apply Dev__same_kinds_refl. }
      apply (IH0 Y HYL0 Hwe1 HSbT (Y ~ bind_sub T1 ++ E2) Hwe2).
      intros x b Hb.
      destruct Hb as [Heq | Hin].
      * left; assumption.
      * right. apply Hincl. assumption.
  - pose proof (Dev__wf_typ_inv_box _ _ HS1) as HwT1.
    assert (HwT2 : wf_typ E1 T2).
    { apply (Dev__sub_wf_target E1 T1 T2 HE1 HwT1 H1). }
    apply sub_box.
    + apply (IH1 HE1 HwT1 E2 HE2 Hincl).
    + apply (IH2 HE1 HwT2 E2 HE2 Hincl).
  - apply sub_readonly. apply (IH1 HE1 (Dev__wf_typ_inv_readonly _ _ _ HS1) E2 HE2 Hincl).
  - apply sub_readonly_mutable. apply (IH1 HE1 HS1 E2 HE2 Hincl).
  - assert (HT2 : wf_typ E1 T2) by (apply (Dev__sub_wf_target E1 T1 T2 HE1 HS1 H1)).
    apply sub_trans with (T2 := T2).
    + apply (IH1 HE1 HS1 E2 HE2 Hincl).
    + apply (IH2 HE1 HT2 E2 HE2 Hincl).
  - apply (sub_inter_left E2 T1 T2); [assumption | |].
    + apply (SubstTT__wf_typ_incl E1 T1 HSi1 E2); intros X U Hb; apply Hincl; assumption.
    + apply (SubstTT__wf_typ_incl E1 T2 HSi2 E2); intros X U Hb; apply Hincl; assumption.
  - apply (sub_inter_right E2 T1 T2); [assumption | |].
    + apply (SubstTT__wf_typ_incl E1 T1 HSi2b E2); intros X U Hb; apply Hincl; assumption.
    + apply (SubstTT__wf_typ_incl E1 T2 HSi2c E2); intros X U Hb; apply Hincl; assumption.
  - apply sub_inter.
    + apply (IH1 HE1 HS1 E2 HE2 Hincl).
    + apply (IH2 HE1 HS1 E2 HE2 Hincl).
  - pose proof (Dev__wf_typ_inv_record _ _ _ HS1) as HwT1.
    assert (HwT2 : wf_typ E1 T2) by (apply (Dev__sub_wf_target E1 T1 T2 HE1 HwT1 H1)).
    apply sub_record.
    + apply (IH1 HE1 HwT1 E2 HE2 Hincl).
    + apply (IH2 HE1 HwT2 E2 HE2 Hincl).
  - apply sub_readonly_record.
    apply (IH1 HE1 (Dev__wf_typ_inv_record _ _ _ (Dev__wf_typ_inv_readonly _ _ _ HS1)) E2 HE2 Hincl).
  - apply (sub_denormalize E2 T1 T2).
    + apply (SubstTT__wf_typ_incl E1 T1 HSd1 E2); intros X U Hb; apply Hincl; assumption.
    + apply (SubstTT__wf_typ_incl E1 T2 HSd2 E2); intros X U Hb; apply Hincl; assumption.
    + apply (IHsub HE1 (Dev__wf_typ_nf _ _ HSd1) E2 HE2 Hincl).
Qed.

Lemma SubstTT__merge_absorb : forall (T : typ) m m',
  merge_mutability (merge_mutability T m) m' = merge_mutability T m.
Proof.
  intros T m m'. induction T; simpl; auto.
  - exact (f_equal2 typ_int IHT1 IHT2).
Qed.

Lemma SubstTT__nf_subst_merge : forall (X : atom) (V T : typ) m,
  normal_form_typing (SubstTT__subst_tt X V (merge_mutability T m))
  = merge_mutability (normal_form_typing (SubstTT__subst_tt X V T)) m.
Proof.
  intros X V T m. induction T; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (a === X); reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - symmetry. apply SubstTT__merge_absorb.
  - apply f_equal2; [exact IHT1 | exact IHT2].
  - reflexivity.
Qed.

Lemma SubstTT__open_merge : forall (T : typ) K (Y : atom) m,
  open_tt_rec K (typ_fvar Y) (merge_mutability T m)
  = merge_mutability (open_tt_rec K (typ_fvar Y) T) m.
Proof.
  intros T K Y m. induction T; simpl.
  - reflexivity.
  - destruct (K == n); reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply f_equal2; [exact IHT1 | exact IHT2].
  - reflexivity.
Qed.

Lemma SubstTT__nf_merge : forall (T : typ) m,
  normal_form_typing (merge_mutability T m)
  = merge_mutability (normal_form_typing T) m.
Proof.
  intros T m. induction T; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - symmetry. apply SubstTT__merge_absorb.
  - apply f_equal2; [exact IHT1 | exact IHT2].
  - reflexivity.
Qed.

Lemma SubstTT__nf_open_tt_rec : forall (T : typ) K (Y : atom),
  normal_form_typing (open_tt_rec K (typ_fvar Y) T)
  = open_tt_rec K (typ_fvar Y) (normal_form_typing T).
Proof.
  intros T. induction T; intros K Y; simpl; try fold normal_form_typing; try fold merge_mutability.
  - reflexivity.
  - destruct (K == n); reflexivity.
  - reflexivity.
  - apply f_equal2; [exact (IHT1 K Y) | exact (IHT2 K Y)].
  - apply f_equal2; [exact (IHT1 K Y) | exact (IHT2 (S K) Y)].
  - apply f_equal. exact (IHT K Y).
  - transitivity (merge_mutability (open_tt_rec K (typ_fvar Y) (normal_form_typing T)) m).
    + apply (f_equal (fun Z => merge_mutability Z m)).
      exact (IHT K Y).
    + symmetry. apply (SubstTT__open_merge (normal_form_typing T) K Y m).
  - apply f_equal2; [exact (IHT1 K Y) | exact (IHT2 K Y)].
  - apply f_equal. exact (IHT K Y).
Qed.

Lemma SubstTT__nf_open_tt : forall (T : typ) (Y : atom),
  normal_form_typing (open_tt T Y)
  = open_tt (normal_form_typing T) Y.
Proof. intros. unfold open_tt. apply SubstTT__nf_open_tt_rec. Qed.

Lemma SubstTT__nf_subst_nf : forall (X : atom) (V T : typ),
  normal_form_typing (SubstTT__subst_tt X V (normal_form_typing T))
  = normal_form_typing (SubstTT__subst_tt X V T).
Proof.
  intros X V T. induction T; simpl; try fold normal_form_typing; try fold merge_mutability.
  - reflexivity.
  - reflexivity.
  - destruct (a === X); reflexivity.
  - apply f_equal2; [exact IHT1 | exact IHT2].
  - apply f_equal2; [exact IHT1 | exact IHT2].
  - fold normal_form_typing. rewrite IHT. reflexivity.
  - fold normal_form_typing. fold merge_mutability. rewrite SubstTT__nf_subst_merge. rewrite IHT. reflexivity.
  - apply f_equal2; [exact IHT1 | exact IHT2].
  - fold normal_form_typing. rewrite IHT. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Environment / binding facts used by subtyping substitution          *)
(* ------------------------------------------------------------------ *)

Definition SubstTT__fv_binding (b : binding) : atoms :=
  match b with
  | bind_sub T => Dev__fv_typ T
  | bind_typ T => Dev__fv_typ T
  end.

Lemma SubstTT__subst_binding_id : forall (X : atom) V (b : binding),
  X `notin` SubstTT__fv_binding b ->
  SubstTT__subst_binding X V b = b.
Proof.
  intros X V [T|T]; simpl; intros H; rewrite SubstTT__subst_tt_id; auto.
Qed.

Lemma SubstTT__wf_env_binding_fv : forall (E : env) X y (b : binding),
  wf_env E -> X `notin` dom E -> binds y b E ->
  X `notin` SubstTT__fv_binding b.
Proof.
  intros E. induction E as [| [z c] E IH]; intros X y b Hwf Hnot Hb; simpl in *.
  - destruct Hb.
  - assert (HnotE : X `notin` dom E).
    { intro Hc. apply Hnot. apply (proj2 (Dev__in_dom_cons E X z c)). right. exact Hc. }
    apply Dev__binds_cons_inv in Hb. destruct Hb as [Heq | Hin].
    + inversion Heq. subst y b. simpl in *.
      destruct c as [T|T].
      * destruct (SubstTT__test_wf_env_cons_bind_sub_inv E z T Hwf) as [_ [Htyp Hz]].
        intro Hfv. apply HnotE. apply (SubstTT__fv_typ_dom E T Htyp X Hfv).
      * destruct (SubstTT__test_wf_env_cons_bind_typ_inv E z T Hwf) as [_ [Htyp Hz]].
        intro Hfv. apply HnotE. apply (SubstTT__fv_typ_dom E T Htyp X Hfv).
    + destruct c as [T|T].
      * destruct (SubstTT__test_wf_env_cons_bind_sub_inv E z T Hwf) as [Hwf' _].
        apply (IH X y b Hwf' HnotE Hin).
      * destruct (SubstTT__test_wf_env_cons_bind_typ_inv E z T Hwf) as [Hwf' _].
        apply (IH X y b Hwf' HnotE Hin).
Qed.

Lemma SubstTT__subst_tt_id_dom : forall (E : env) X V T,
  wf_typ E T -> X `notin` dom E -> SubstTT__subst_tt X V T = T.
Proof.
  intros. apply SubstTT__subst_tt_id. intro Hfv.
  exact (H0 (SubstTT__fv_typ_dom E T H X Hfv)).
Qed.

Lemma SubstTT__binds_subst_env_target_sub : forall (A E : env) X U V Y W,
  X `notin` dom E ->
  wf_env (A ++ X ~ bind_sub U ++ E) ->
  binds Y (bind_sub W) (A ++ X ~ bind_sub U ++ E) ->
  Y <> X ->
  binds Y (bind_sub (SubstTT__subst_tt X V W)) (SubstTT__subst_tt_env X V A ++ E).
Proof.
  intros A E X U V Y W HnotE Hwf Hb HYX.
  destruct (SubstTT__binds_in_A_or_E A E X U Y (bind_sub W) HYX Hb) as [HA | HE].
  - apply (SubstTT__binds_subst_env_A A E X V Y (bind_sub W) HA).
  - pose proof (SubstTT__wf_env_binding_fv E X Y (bind_sub W) (SubstTT__wf_env_tail_mid A E X U Hwf) HnotE HE)
      as Hfv.
    simpl in Hfv. rewrite (SubstTT__subst_tt_id X V W Hfv).
    apply (SubstTT__binds_subst_env_E A E X V Y (bind_sub W) HE).
Qed.

(* ------------------------------------------------------------------ *)
(* Subtyping is preserved by type substitution.  The prefix `A` is     *)
(* substituted, the trailing `E` is unchanged, and the removed binding  *)
(* for X is replaced by the subtype relation `sub E V U`.               *)
(* ------------------------------------------------------------------ *)

Lemma SubstTT__sub_subst_gen : forall (A E : env) X U V,
  X `notin` dom A ->
  X `notin` dom E ->
  wf_env (A ++ X ~ bind_sub U ++ E) ->
  wf_typ E V ->
  SubstTT__closed_typ V ->
  wf_typ (SubstTT__subst_tt_env X V A ++ E) V ->
  sub E V U ->
  forall S T,
    wf_typ (A ++ X ~ bind_sub U ++ E) S ->
    sub (A ++ X ~ bind_sub U ++ E) S T ->
    sub (SubstTT__subst_tt_env X V A ++ E) (SubstTT__subst_tt X V S) (SubstTT__subst_tt X V T).
Proof.
  intros A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU S T HS Hsub.
  remember (A ++ X ~ bind_sub U ++ E) as E0 eqn:He.
  revert A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HS He.
  induction Hsub as [ E0 S0 HE0 HS0
                 | E0 Y HE0 HS0
                 | U0 E0 T0 Y Hb Hsub IHsub
                 | E0 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E0 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E0 T1 T2 H1 IH1 H2 IH2
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 H1 IH1
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 T1 T2 HEi1 HSi1 HSi2
                 | E0 T1 T2 HEi2 HSi2b HSi2c
                 | E0 T1 T2 T3 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1 H2 IH2
                 | E0 a T1 T2 H1 IH1
                 | E0 T1 T2 HSd1 HSd2 Hsub IHsub ];
    intros A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HSsrc He;
    subst E0.
  - (* sub_top *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    apply sub_top; [exact HwfTarget|].
    apply (SubstTT__wf_typ_subst_gen A X U E S0 HnotA HnotE HS0 V Hclosed HwVt).
  - (* sub_refl_tvar *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    destruct (Y === X) as [Heq | Hneq].
    + subst Y. rewrite SubstTT__subst_tt_fvar_eq.
      apply (Dev__sub_refl (SubstTT__subst_tt_env X V A ++ E) V HwfTarget HwVt).
    + rewrite (SubstTT__subst_tt_fvar_neq X Y V Hneq).
      apply (sub_refl_tvar (SubstTT__subst_tt_env X V A ++ E) Y HwfTarget).
      rewrite <- (SubstTT__subst_tt_fvar_neq X Y V Hneq).
      apply (SubstTT__wf_typ_subst_gen A X U E (typ_fvar Y) HnotA HnotE HS0 V Hclosed HwVt).
  - (* sub_trans_tvar *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    pose proof (SubstTT__wf_env_tail_mid A E X U HwfENT) as HwfE.
    pose proof (SubstTT__wf_env_mid_typ A E X U HwfENT) as HwU.
    assert (HsubVU' : sub (SubstTT__subst_tt_env X V A ++ E) V U).
    { apply (SubstTT__sub_weaken_incl E V U HwfE HwVE HsubVU (SubstTT__subst_tt_env X V A ++ E) HwfTarget).
      intros x b HbE. apply (SubstTT__binds_subst_env_E A E X V x b HbE). }
    destruct (Y === X) as [Heq | Hneq].
    + subst Y.
      assert (HbU : bind_sub U0 = bind_sub U)
        by (apply (SubstTT__test_binds_mid_sub A E X U (bind_sub U0) HnotA HnotE Hb)).
      injection HbU as HU0. subst U0.
      rewrite SubstTT__subst_tt_fvar_eq.
      apply (sub_trans (SubstTT__subst_tt_env X V A ++ E) V U (SubstTT__subst_tt X V T0)).
      * exact HsubVU'.
      * rewrite <- (SubstTT__subst_tt_id_dom E X V U HwU HnotE).
        apply (IHsub A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU).
        -- apply (Dev__wf_env_binds_sub (A ++ X ~ bind_sub U ++ E) HwfENT X U).
           exact Hb.
        -- reflexivity.
    + rewrite (SubstTT__subst_tt_fvar_neq X Y V Hneq).
      assert (HbTarget : binds Y (bind_sub (SubstTT__subst_tt X V U0))
                           (SubstTT__subst_tt_env X V A ++ E)).
      { apply (SubstTT__binds_subst_env_target_sub A E X U V Y U0 HnotE HwfENT Hb Hneq). }
      apply (sub_trans_tvar (SubstTT__subst_tt X V U0) (SubstTT__subst_tt_env X V A ++ E)
               (SubstTT__subst_tt X V T0) Y HbTarget).
      apply (IHsub A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU).
      * apply (Dev__wf_env_binds_sub (A ++ X ~ bind_sub U ++ E) HwfENT Y U0).
        exact Hb.
      * reflexivity.
  - (* sub_arrow *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    destruct (Dev__wf_typ_inv_arrow _ _ _ HSsrc) as [HSa HSb].
    assert (HT1 : wf_typ (A ++ X ~ bind_sub U ++ E) T1)
      by (apply (Dev__sub_wf_source (A ++ X ~ bind_sub U ++ E) T1 S1 HwfENT HSa H1)).
    apply sub_arrow.
    + apply (IH1 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HT1).
      reflexivity.
    + apply (IH2 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HSb).
      reflexivity.
  - (* sub_all *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    destruct (Dev__wf_typ_inv_all _ _ _ HSsrc) as [L1 [HSa HSb]].
    assert (HT1 : wf_typ (A ++ X ~ bind_sub U ++ E) T1)
      by (apply (Dev__sub_wf_source (A ++ X ~ bind_sub U ++ E) T1 S1 HwfENT HSa H1)).
    eapply (sub_all (L0 `union` L1 `union` dom A `union` dom E `union` {{X}})
              (SubstTT__subst_tt_env X V A ++ E)
              (SubstTT__subst_tt X V S1) (SubstTT__subst_tt X V S2)
              (SubstTT__subst_tt X V T1) (SubstTT__subst_tt X V T2)).
    + apply (IH1 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HT1).
      reflexivity.
    + intros Y0 HY0.
      assert (HYL0 : Y0 `notin` L0) by (apply notin_union_1 in HY0; assumption).
      assert (HYL1 : Y0 `notin` L1)
        by (apply notin_union_2 in HY0; apply notin_union_1 in HY0; assumption).
      assert (HYdA : Y0 `notin` dom A)
        by (apply notin_union_2 in HY0; apply notin_union_2 in HY0;
            apply notin_union_1 in HY0; assumption).
      assert (HYdE : Y0 `notin` dom E)
        by (apply notin_union_2 in HY0; apply notin_union_2 in HY0;
            apply notin_union_2 in HY0; apply notin_union_1 in HY0; assumption).
      assert (HYX : Y0 <> X)
        by (apply notin_union_2 in HY0; apply notin_union_2 in HY0;
            apply notin_union_2 in HY0; apply notin_union_2 in HY0;
            apply notin_singleton_1' in HY0; symmetry; exact HY0).
      assert (HnotA0 : X `notin` dom (Y0 ~ bind_sub T1 ++ A)).
      { intro Hin. simpl in Hin. rewrite add_iff in Hin.
        destruct Hin as [Heq | Hin].
        - apply HYX. exact Heq.
        - apply HnotA. exact Hin. }
      assert (HwVt0 : wf_typ (SubstTT__subst_tt_env X V (Y0 ~ bind_sub T1 ++ A) ++ E) V).
      { change (wf_typ ((Y0, bind_sub (SubstTT__subst_tt X V T1)) :: (SubstTT__subst_tt_env X V A ++ E)) V).
        apply (Dev__wf_typ_weaken (SubstTT__subst_tt_env X V A ++ E) V HwVt
                 ((Y0, bind_sub (SubstTT__subst_tt X V T1)) :: nil)). }
      assert (Hsrc : wf_typ ((Y0 ~ bind_sub T1 ++ A) ++ X ~ bind_sub U ++ E)
                       (open_tt S2 Y0)).
      { change (wf_typ (Y0 ~ bind_sub T1 ++ (A ++ X ~ bind_sub U ++ E)) (open_tt S2 Y0)).
        apply (Dev__wf_typ_kind (Y0 ~ bind_sub S1 ++ (A ++ X ~ bind_sub U ++ E))
                 (open_tt S2 Y0) (HSb Y0 HYL1)
                 (Y0 ~ bind_sub T1 ++ (A ++ X ~ bind_sub U ++ E))).
        apply Dev__same_kinds_cons_sub_any. apply Dev__same_kinds_refl. }
      assert (HYdXE : Y0 `notin` dom (X ~ bind_sub U ++ E)).
      { intro Hin. apply (proj1 (SubstTT__test_in_dom_app (X ~ bind_sub U) E Y0)) in Hin.
        destruct Hin as [Hin | Hin].
        - simpl in Hin. rewrite add_iff in Hin.
          destruct Hin as [Heq | Hin].
          + apply HYX. symmetry. exact Heq.
          + exact (notin_empty Y0 Hin).
        - apply HYdE. exact Hin. }
      assert (HYdom : Y0 `notin` dom (A ++ X ~ bind_sub U ++ E)).
      { intro Hin. apply (proj1 (SubstTT__test_in_dom_app A (X ~ bind_sub U ++ E) Y0)) in Hin.
        destruct Hin as [Hin | Hin].
        - apply HYdA. exact Hin.
        - apply HYdXE. exact Hin. }
      assert (HwfBody0 : wf_env ((Y0 ~ bind_sub T1 ++ A) ++ X ~ bind_sub U ++ E)).
      { change (wf_env (Y0 ~ bind_sub T1 ++ (A ++ X ~ bind_sub U ++ E))).
        apply (wf_env_sub (A ++ X ~ bind_sub U ++ E) Y0 T1 HwfENT HT1 HYdom). }
      assert (HsubBody : sub ((Y0 ~ bind_sub T1 ++ A) ++ X ~ bind_sub U ++ E)
                           (open_tt S2 Y0) (open_tt T2 Y0))
        by (exact (H0 Y0 HYL0)).
      specialize (IH0 Y0 HYL0 (Y0 ~ bind_sub T1 ++ A) E X U V
                    HnotA0 HnotE HwfBody0 HwVE Hclosed HwVt0 HsubVU
                    Hsrc eq_refl).
      unfold open_tt in IH0.
      rewrite <- (SubstTT__open_tt_rec_subst_comm 0 S2 X V Y0 Hclosed HYX) in IH0.
      rewrite <- (SubstTT__open_tt_rec_subst_comm 0 T2 X V Y0 Hclosed HYX) in IH0.
      change (sub ((Y0, bind_sub (SubstTT__subst_tt X V T1)) :: (SubstTT__subst_tt_env X V A ++ E))
                (open_tt (SubstTT__subst_tt X V S2) Y0)
                (open_tt (SubstTT__subst_tt X V T2) Y0)).
      exact IH0.
  - (* sub_box *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    pose proof (Dev__wf_typ_inv_box _ _ HSsrc) as HwT1.
    assert (HwT2 : wf_typ (A ++ X ~ bind_sub U ++ E) T2)
      by (apply (Dev__sub_wf_target (A ++ X ~ bind_sub U ++ E) T1 T2 HwfENT HwT1 H1)).
    apply sub_box.
    + apply (IH1 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HwT1).
      reflexivity.
    + apply (IH2 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HwT2).
      reflexivity.
  - (* sub_readonly *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    apply sub_readonly.
    apply (IH1 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU
            (Dev__wf_typ_inv_readonly _ _ _ HSsrc)).
    reflexivity.
  - (* sub_readonly_mutable *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    apply sub_readonly_mutable.
    apply (IH1 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HSsrc).
    reflexivity.
  - (* sub_trans *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    assert (HT2 : wf_typ (A ++ X ~ bind_sub U ++ E) T2)
      by (apply (Dev__sub_wf_target (A ++ X ~ bind_sub U ++ E) T1 T2 HwfENT HSsrc H1)).
    apply (sub_trans (SubstTT__subst_tt_env X V A ++ E)
             (SubstTT__subst_tt X V T1) (SubstTT__subst_tt X V T2) (SubstTT__subst_tt X V T3)).
    + apply (IH1 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HSsrc).
      reflexivity.
    + apply (IH2 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HT2).
      reflexivity.
  - (* sub_inter_left *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    apply (sub_inter_left (SubstTT__subst_tt_env X V A ++ E)
             (SubstTT__subst_tt X V T1) (SubstTT__subst_tt X V T2) HwfTarget).
    + apply (SubstTT__wf_typ_subst_gen A X U E T1 HnotA HnotE HSi1 V Hclosed HwVt).
    + apply (SubstTT__wf_typ_subst_gen A X U E T2 HnotA HnotE HSi2 V Hclosed HwVt).
  - (* sub_inter_right *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    apply (sub_inter_right (SubstTT__subst_tt_env X V A ++ E)
             (SubstTT__subst_tt X V T1) (SubstTT__subst_tt X V T2) HwfTarget).
    + apply (SubstTT__wf_typ_subst_gen A X U E T1 HnotA HnotE HSi2b V Hclosed HwVt).
    + apply (SubstTT__wf_typ_subst_gen A X U E T2 HnotA HnotE HSi2c V Hclosed HwVt).
  - (* sub_inter *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    apply sub_inter.
    + apply (IH1 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HSsrc).
      reflexivity.
    + apply (IH2 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HSsrc).
      reflexivity.
  - (* sub_record *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    pose proof (Dev__wf_typ_inv_record _ _ _ HSsrc) as HwT1.
    assert (HwT2 : wf_typ (A ++ X ~ bind_sub U ++ E) T2)
      by (apply (Dev__sub_wf_target (A ++ X ~ bind_sub U ++ E) T1 T2 HwfENT HwT1 H1)).
    apply sub_record.
    + apply (IH1 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HwT1).
      reflexivity.
    + apply (IH2 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU HwT2).
      reflexivity.
  - (* sub_readonly_record *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    apply sub_readonly_record.
    apply (IH1 A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU
            (Dev__wf_typ_inv_record _ _ _ (Dev__wf_typ_inv_readonly _ _ _ HSsrc))).
    reflexivity.
  - (* sub_denormalize *)
    assert (HwfTarget : wf_env (SubstTT__subst_tt_env X V A ++ E))
      by (apply (SubstTT__wf_env_subst_gen A E X U HwfENT V Hclosed HwVE)).
    assert (HwT1 : wf_typ (SubstTT__subst_tt_env X V A ++ E) (SubstTT__subst_tt X V T1))
      by (apply (SubstTT__wf_typ_subst_gen A X U E T1 HnotA HnotE HSd1 V Hclosed HwVt)).
    assert (HwT2 : wf_typ (SubstTT__subst_tt_env X V A ++ E) (SubstTT__subst_tt X V T2))
      by (apply (SubstTT__wf_typ_subst_gen A X U E T2 HnotA HnotE HSd2 V Hclosed HwVt)).
    assert (HwN1 : wf_typ (SubstTT__subst_tt_env X V A ++ E)
                     (SubstTT__subst_tt X V (normal_form_typing T1))).
    { apply (SubstTT__wf_typ_subst_gen A X U E (normal_form_typing T1) HnotA HnotE
               (Dev__wf_typ_nf (A ++ X ~ bind_sub U ++ E) T1 HSd1) V Hclosed HwVt). }
    assert (HwN2 : wf_typ (SubstTT__subst_tt_env X V A ++ E)
                     (SubstTT__subst_tt X V (normal_form_typing T2))).
    { apply (SubstTT__wf_typ_subst_gen A X U E (normal_form_typing T2) HnotA HnotE
               (Dev__wf_typ_nf (A ++ X ~ bind_sub U ++ E) T2 HSd2) V Hclosed HwVt). }
    assert (HIH : sub (SubstTT__subst_tt_env X V A ++ E)
                    (SubstTT__subst_tt X V (normal_form_typing T1))
                    (SubstTT__subst_tt X V (normal_form_typing T2))).
    { apply (IHsub A E X U V HnotA HnotE HwfENT HwVE Hclosed HwVt HsubVU
               (Dev__wf_typ_nf (A ++ X ~ bind_sub U ++ E) T1 HSd1)).
      reflexivity. }
    assert (Hnf0 : sub (SubstTT__subst_tt_env X V A ++ E)
                    (normal_form_typing (SubstTT__subst_tt X V (normal_form_typing T1)))
                    (normal_form_typing (SubstTT__subst_tt X V (normal_form_typing T2)))).
    { apply (sub_trans (SubstTT__subst_tt_env X V A ++ E)
               (normal_form_typing (SubstTT__subst_tt X V (normal_form_typing T1)))
               (SubstTT__subst_tt X V (normal_form_typing T1))
               (normal_form_typing (SubstTT__subst_tt X V (normal_form_typing T2)))).
      - apply (Dev__sub_of_nf (SubstTT__subst_tt_env X V A ++ E)
                 (SubstTT__subst_tt X V (normal_form_typing T1)) HwfTarget HwN1).
      - apply (sub_trans (SubstTT__subst_tt_env X V A ++ E)
                 (SubstTT__subst_tt X V (normal_form_typing T1))
                 (SubstTT__subst_tt X V (normal_form_typing T2))
                 (normal_form_typing (SubstTT__subst_tt X V (normal_form_typing T2)))).
        + exact HIH.
        + apply (Dev__sub_to_nf (SubstTT__subst_tt_env X V A ++ E)
                   (SubstTT__subst_tt X V (normal_form_typing T2)) HwfTarget HwN2). }
    rewrite (SubstTT__nf_subst_nf X V T1) in Hnf0.
    rewrite (SubstTT__nf_subst_nf X V T2) in Hnf0.
    apply (sub_denormalize (SubstTT__subst_tt_env X V A ++ E) (SubstTT__subst_tt X V T1) (SubstTT__subst_tt X V T2));
      assumption.
Qed.

Scheme SubstTT__typing_mut := Induction for typing Sort Prop
with SubstTT__typing_record_mut := Induction for typing_record_comp Sort Prop.

Lemma SubstTT__wf_sig_binds : forall (E : env) (R : sig) (l : label) (T : typ),
  wf_sig E R -> Signatures.binds l (bind_sig T) R -> wf_typ E T.
Proof.
  intros E R l T H. induction H as [E0 Hwe | E0 R0 l0 T0 Hws IH Hwt Hnot];
    intro Hb.
  - simpl in Hb. inversion Hb.
  - apply Signatures.binds_cons_iff in Hb.
    destruct Hb as [[Heql HeqT] | Hin].
    + injection HeqT as HT. subst. exact Hwt.
    + apply IH. exact Hin.
Qed.

Lemma SubstTT__wf_typ_type : forall (E : env) T,
  wf_typ E T -> type T.
Proof.
  intros E T H. induction H.
  - apply type_top.
  - apply type_var.
  - apply type_arrow; assumption.
  - apply type_all with (L := L); auto.
  - apply type_box; assumption.
  - apply type_readonly; assumption.
  - apply type_intersect; assumption.
  - apply type_record; assumption.
Qed.

Lemma SubstTT__typing_wf_sig : forall (E : env) (R : sig) e T,
  typing E R e T -> wf_sig E R
with SubstTT__typing_record_comp_wf_sig : forall (E : env) (R : sig) r T,
  typing_record_comp E R r T -> wf_sig E R.
Proof.
  - intros E R e T H. induction H; eauto.
  - intros E R r T H. induction H; eauto.
Qed.

Lemma SubstTT__typing_wf_typ : forall (E : env) (R : sig) e T,
  typing E R e T -> wf_typ E T
with SubstTT__typing_record_comp_wf_typ : forall (E : env) (R : sig) r T,
  typing_record_comp E R r T -> wf_typ E T.
Proof.
  - intros E R e T Hty. induction Hty as
      [ E0 R0 x T0 Hwe Hws Hb
      | L E0 R0 V e1 T1 Hws Hbody IHbody
      | T1 E0 R0 e1 e2 T2 Hws H1 IH1 H2 IH2
      | L E0 R0 V e1 T1 Hws Hbody IHbody
      | T1 E0 R0 e1 T T2 Hws H1 IH1 Hsub
      | S E0 R0 e T Hws H1 IH1 Hsub
      | L T1 T2 e1 e2 E0 R0 Hws H1 IH1 Hbody IHbody
      | E0 R0 e T Hws H1 IH1
      | E0 R0 e T Hws H1 IH1
      | E0 R0 e1 e2 T Hws H1 IH1 H2 IH2
      | E0 R0 l T Hwe Hws Hb
      | E0 R0 e T H1 IH1
      | E0 R0 e T H1 IH1
      | E0 R0 r T Hr IHr
      | E0 R0 e a T H1 IH1
      | E0 R0 e a T H1 IH1
      | E0 R0 e1 a e2 T H1 IH1 H2 IH2 ].
    + apply (Dev__wf_env_binds_typ _ Hwe x T0 Hb).
    + destruct (atom_fresh (L `union` dom E0 `union` Dev__fv_typ T1)) as [x Hx].
      assert (HxL : x `notin` L) by (apply notin_union_1 in Hx; assumption).
      assert (HxE : x `notin` dom E0)
        by (apply notin_union_2 in Hx; apply notin_union_1 in Hx; assumption).
      assert (HxT : x `notin` Dev__fv_typ T1)
        by (apply notin_union_2 in Hx; apply notin_union_2 in Hx; assumption).
      assert (Hwb : wf_typ (x ~ bind_typ V ++ E0) T1) by (apply IHbody; assumption).
      assert (Hwenv : wf_env (x ~ bind_typ V ++ E0))
        by (apply (Dev__wf_sig_wf_env (x ~ bind_typ V ++ E0) R0);
            apply (SubstTT__typing_wf_sig (x ~ bind_typ V ++ E0) R0 (open_ee e1 x) T1);
            apply Hbody; assumption).
      destruct (Dev__wf_env_cons_bind_typ _ _ _ Hwenv) as [HweE HwV].
      assert (HwT1 : wf_typ E0 T1).
      { eapply Dev__wf_typ_remove_bind_typ; eauto. intros y b; reflexivity. }
      apply wf_typ_arrow; assumption.
    + apply (proj2 (Dev__wf_typ_inv_arrow _ _ _ IH1)).
    + destruct (atom_fresh (L `union` dom E0)) as [X HX].
      assert (HXL : X `notin` L) by (apply notin_union_1 in HX; assumption).
      assert (HXE : X `notin` dom E0) by (apply notin_union_2 in HX; assumption).
      assert (Hwenv : wf_env (X ~ bind_sub V ++ E0))
        by (apply (Dev__wf_sig_wf_env (X ~ bind_sub V ++ E0) R0);
            apply (SubstTT__typing_wf_sig (X ~ bind_sub V ++ E0) R0 (open_te e1 X) (open_tt T1 X));
            apply Hbody; assumption).
      destruct (Dev__wf_env_cons_bind_sub _ _ _ Hwenv) as [HweE HwV].
      apply wf_typ_all with (L := L).
      * exact HwV.
      * intros X0 HX0. apply IHbody. assumption.
    + destruct (Dev__wf_typ_inv_all _ _ _ IH1) as [L0 [HwT1 Hwbody]].
      assert (Hwe : wf_env E0) by (apply Dev__wf_sig_wf_env with (R := R0); assumption).
      assert (HwT : wf_typ E0 T)
        by (apply (Dev__sub_wf_source E0 T T1 Hwe HwT1 Hsub)).
      destruct (atom_fresh (L0 `union` dom E0 `union` Dev__fv_typ T2)) as [X HX].
      assert (HXL0 : X `notin` L0) by (apply notin_union_1 in HX; assumption).
      assert (HXE : X `notin` dom E0)
        by (apply notin_union_2 in HX; apply notin_union_1 in HX; assumption).
      assert (HXT2 : X `notin` Dev__fv_typ T2)
        by (apply notin_union_2 in HX; apply notin_union_2 in HX; assumption).
      assert (HbodyX : wf_typ (X ~ bind_sub T1 ++ E0) (open_tt T2 X))
        by (apply Hwbody; assumption).
      pose proof (SubstTT__wf_typ_subst_gen nil X T1 E0 (open_tt T2 X)
                    (notin_empty X) HXE HbodyX T
                    (SubstTT__wf_typ_closed E0 T HwT) HwT) as Hres.
      simpl in Hres.
      assert (Heq : open_tt T2 T = SubstTT__subst_tt X T (open_tt T2 X)).
      { apply (SubstTT__open_tt_rec_subst_tt 0 T2 X T HXT2). }
      rewrite Heq. exact Hres.
    + apply (Dev__sub_wf_target E0 S T (Dev__wf_sig_wf_env E0 R0 Hws) IH1 Hsub).
    + destruct (atom_fresh (L `union` Dev__fv_typ T2)) as [x Hx].
      assert (HxL : x `notin` L) by (apply notin_union_1 in Hx; assumption).
      assert (HxT : x `notin` Dev__fv_typ T2) by (apply notin_union_2 in Hx; assumption).
      assert (Hwb : wf_typ (x ~ bind_typ T1 ++ E0) T2) by (apply IHbody; assumption).
      eapply Dev__wf_typ_remove_bind_typ; eauto. intros y b; reflexivity.
    + apply wf_typ_box; assumption.
    + apply (Dev__wf_typ_inv_box _ _ IH1).
    + apply (Dev__wf_typ_inv_box _ _ IH1).
    + apply wf_typ_box. apply (SubstTT__wf_sig_binds E0 R0 l T Hws Hb).
    + apply wf_typ_readonly; assumption.
    + apply wf_typ_readonly.
      apply (Dev__wf_typ_inv_box _ _ (Dev__wf_typ_inv_readonly _ _ _ IH1)).
    + apply (SubstTT__typing_record_comp_wf_typ E0 R0 r T Hr).
    + apply (Dev__wf_typ_inv_record _ _ _ IH1).
    + apply wf_typ_readonly.
      apply (Dev__wf_typ_inv_record _ _ _ (Dev__wf_typ_inv_readonly _ _ _ IH1)).
    + apply (Dev__wf_typ_inv_record _ _ _ IH1).
  - intros E R r T Htr. induction Htr as
      [ E0 R0 Hwe Hws
      | E0 R0 a e r T Tr Hnotin Hr IHr He IHe
      | E0 R0 a l r T Tr Hnotin Hr IHr Hb ].
    + constructor.
    + apply wf_typ_intersect.
      * constructor. apply (SubstTT__typing_wf_typ E0 R0 e T He).
      * apply IHr.
    + apply wf_typ_intersect.
      * constructor. apply (SubstTT__wf_sig_binds E0 R0 l T
          (SubstTT__typing_record_comp_wf_sig E0 R0 r Tr Hr) Hb).
      * apply IHr.
Qed.


(* SubstTT__subst_te commutes with opening a term variable. *)
Fixpoint SubstTT__subst_te_open_ee_rec (e : exp) {struct e} :
  forall k (f : exp) X V,
    SubstTT__subst_te X V (open_ee_rec k f e)
    = open_ee_rec k (SubstTT__subst_te X V f) (SubstTT__subst_te X V e)
with SubstTT__subst_te_record_open_ee_record_rec (r : rec_comp) {struct r} :
  forall k (f : exp) X V,
    SubstTT__subst_te_record X V (open_ee_record_rec k f r)
    = open_ee_record_rec k (SubstTT__subst_te X V f) (SubstTT__subst_te_record X V r).
Proof.
  - destruct e; intros k f X V; simpl; try reflexivity.
    + destruct (k == n); reflexivity.
    + rewrite (SubstTT__subst_te_open_ee_rec e (S k) f X V). reflexivity.
    + rewrite (SubstTT__subst_te_open_ee_rec e1 k f X V).
      rewrite (SubstTT__subst_te_open_ee_rec e2 k f X V). reflexivity.
    + rewrite (SubstTT__subst_te_open_ee_rec e k f X V). reflexivity.
    + rewrite (SubstTT__subst_te_open_ee_rec e k f X V). reflexivity.
    + rewrite (SubstTT__subst_te_open_ee_rec e1 k f X V).
      rewrite (SubstTT__subst_te_open_ee_rec e2 (S k) f X V). reflexivity.
    + rewrite (SubstTT__subst_te_open_ee_rec e k f X V). reflexivity.
    + rewrite (SubstTT__subst_te_open_ee_rec e k f X V). reflexivity.
    + rewrite (SubstTT__subst_te_open_ee_rec e1 k f X V).
      rewrite (SubstTT__subst_te_open_ee_rec e2 k f X V). reflexivity.
    + rewrite (SubstTT__subst_te_open_ee_rec e k f X V). reflexivity.
    + rewrite (SubstTT__subst_te_record_open_ee_record_rec r k f X V). reflexivity.
    + rewrite (SubstTT__subst_te_open_ee_rec e k f X V). reflexivity.
    + rewrite (SubstTT__subst_te_open_ee_rec e1 k f X V).
      rewrite (SubstTT__subst_te_open_ee_rec e2 k f X V). reflexivity.
  - destruct r; intros k f X V; simpl.
    + reflexivity.
    + rewrite (SubstTT__subst_te_open_ee_rec e k f X V).
      rewrite (SubstTT__subst_te_record_open_ee_record_rec r k f X V). reflexivity.
    + rewrite (SubstTT__subst_te_record_open_ee_record_rec r k f X V). reflexivity.
Qed.

Lemma SubstTT__subst_te_open_ee : forall (e : exp) (x : atom) X V,
  SubstTT__subst_te X V (open_ee e x) = open_ee (SubstTT__subst_te X V e) x.
Proof.
  intros. unfold open_ee.
  apply (SubstTT__subst_te_open_ee_rec e 0 (exp_fvar x) X V).
Qed.

Lemma SubstTT__record_dom_subst_te_record : forall (r : rec_comp) X V,
  record_dom (SubstTT__subst_te_record X V r) = record_dom r.
Proof.
  induction r; intros X V; simpl.
  - reflexivity.
  - rewrite IHr. reflexivity.
  - rewrite IHr. reflexivity.
Qed.

(* A free signature atom does not occur in a type bound by a label. *)
Lemma SubstTT__fv_sig_binds_typ : forall (R : sig) l T X,
  Signatures.binds l (bind_sig T) R -> X `notin` SubstTT__fv_sig R -> X `notin` Dev__fv_typ T.
Proof.
  intros R. induction R as [| [l0 b] R IH]; intros l T X Hb Hfv.
  - simpl in Hb. inversion Hb.
  - destruct b as [T0].
    simpl in Hfv.
    pose proof (notin_union_1 X (Dev__fv_typ T0) (SubstTT__fv_sig R) Hfv) as HT0.
    pose proof (notin_union_2 X (Dev__fv_typ T0) (SubstTT__fv_sig R) Hfv) as HR.
    apply Signatures.binds_cons_iff in Hb.
    destruct Hb as [[Heql HeqT] | Hin].
    + inversion HeqT as [[HT]]. subst. exact HT0.
    + apply (IH l T X Hin HR).
Qed.

(* ================================================================== *)
(* Typing is preserved by type substitution.                          *)
(* ================================================================== *)

Definition SubstTT__typing_subst_P (Env0 : env) (R : sig) (e : exp) (T : typ)
    (H : typing Env0 R e T) : Prop :=
  forall (A E : env) (X : atom) (U V : typ),
    X `notin` dom A ->
    X `notin` dom E ->
    wf_env (A ++ X ~ bind_sub U ++ E) ->
    wf_typ E V ->
    SubstTT__closed_typ V ->
    sub E V U ->
    X `notin` SubstTT__fv_sig R ->
    Env0 = A ++ X ~ bind_sub U ++ E ->
    typing (SubstTT__subst_tt_env X V A ++ E) R (SubstTT__subst_te X V e) (SubstTT__subst_tt X V T).

Definition SubstTT__typing_subst_P0 (Env0 : env) (R : sig) (r : rec_comp) (T : typ)
    (H : typing_record_comp Env0 R r T) : Prop :=
  forall (A E : env) (X : atom) (U V : typ),
    X `notin` dom A ->
    X `notin` dom E ->
    wf_env (A ++ X ~ bind_sub U ++ E) ->
    wf_typ E V ->
    SubstTT__closed_typ V ->
    sub E V U ->
    X `notin` SubstTT__fv_sig R ->
    Env0 = A ++ X ~ bind_sub U ++ E ->
    typing_record_comp (SubstTT__subst_tt_env X V A ++ E) R
      (SubstTT__subst_te_record X V r) (SubstTT__subst_tt X V T).

Definition SubstTT__typing_subst_P_true (Env0 : env) (R : sig) (e : exp) (T : typ)
    (H : typing Env0 R e T) : Prop := True.

Definition SubstTT__typing_subst_P0_true (Env0 : env) (R : sig) (r : rec_comp) (T : typ)
    (H : typing_record_comp Env0 R r T) : Prop := True.

Lemma SubstTT__typing_subst_te_gen : forall (A E : env) (X : atom) U R e T V,
  X `notin` dom A ->
  X `notin` dom E ->
  wf_env (A ++ X ~ bind_sub U ++ E) ->
  wf_typ E V ->
  SubstTT__closed_typ V ->
  sub E V U ->
  X `notin` SubstTT__fv_sig R ->
  typing (A ++ X ~ bind_sub U ++ E) R e T ->
  typing (SubstTT__subst_tt_env X V A ++ E) R (SubstTT__subst_te X V e) (SubstTT__subst_tt X V T)
with SubstTT__typing_record_comp_subst_te_gen : forall (A E : env) (X : atom) U R r T V,
  X `notin` dom A ->
  X `notin` dom E ->
  wf_env (A ++ X ~ bind_sub U ++ E) ->
  wf_typ E V ->
  SubstTT__closed_typ V ->
  sub E V U ->
  X `notin` SubstTT__fv_sig R ->
  typing_record_comp (A ++ X ~ bind_sub U ++ E) R r T ->
  typing_record_comp (SubstTT__subst_tt_env X V A ++ E) R
    (SubstTT__subst_te_record X V r) (SubstTT__subst_tt X V T).
Proof.
  - intros A E X U R eout Tout V HnotA HnotE Hwf HV Hc Hsub Hfv Hty.
    assert (Hgen : SubstTT__typing_subst_P (A ++ X ~ bind_sub U ++ E) R eout Tout Hty).
    { apply (SubstTT__typing_mut SubstTT__typing_subst_P SubstTT__typing_subst_P0_true).
      - (* typing_var *)
        intros Env0 R0 x T0 Hwe Hws Hb.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        assert (Hws0 : wf_sig (A0 ++ X0 ~ bind_sub U0 ++ E0) R0)
          by (rewrite <- HE; exact Hws).
        assert (Hb0 : binds x (bind_typ T0) (A0 ++ X0 ~ bind_sub U0 ++ E0))
          by (rewrite <- HE; exact Hb).
        assert (HxX : x <> X0).
        { intro Heq. subst x.
          pose proof (SubstTT__test_binds_mid_sub A0 E0 X0 U0 (bind_typ T0) HnotA0 HnotE0 Hb0)
            as Hbmid.
          discriminate Hbmid. }
        destruct (SubstTT__binds_in_A_or_E A0 E0 X0 U0 x (bind_typ T0) HxX Hb0) as [HA | HEb].
        + assert (Hbt : binds x (bind_typ (SubstTT__subst_tt X0 V0 T0))
                        (SubstTT__subst_tt_env X0 V0 A0 ++ E0)).
          { change (binds x (SubstTT__subst_binding X0 V0 (bind_typ T0))
                      (SubstTT__subst_tt_env X0 V0 A0 ++ E0)).
            apply (SubstTT__binds_subst_env_A A0 E0 X0 V0 x (bind_typ T0) HA). }
          apply typing_var.
          * apply (SubstTT__wf_env_subst_gen A0 E0 X0 U0 Hwf0 V0 Hc0 HV0).
          * apply (SubstTT__wf_sig_subst_gen A0 E0 R0 X0 U0 Hwf0 Hws0 Hfv0 V0 Hc0 HV0).
          * exact Hbt.
        + assert (HnotX : X0 `notin` Dev__fv_typ T0).
          { pose proof (SubstTT__wf_env_binding_fv E0 X0 x (bind_typ T0)
                          (SubstTT__wf_env_tail_mid A0 E0 X0 U0 Hwf0) HnotE0 HEb) as Hfvb.
            simpl in Hfvb. exact Hfvb. }
          assert (HeqT : SubstTT__subst_tt X0 V0 T0 = T0)
            by (apply SubstTT__subst_tt_id; exact HnotX).
          assert (Hbt : binds x (bind_typ (SubstTT__subst_tt X0 V0 T0))
                        (SubstTT__subst_tt_env X0 V0 A0 ++ E0)).
          { rewrite HeqT. apply (SubstTT__binds_subst_env_E A0 E0 X0 V0 x (bind_typ T0) HEb). }
          apply typing_var.
          * apply (SubstTT__wf_env_subst_gen A0 E0 X0 U0 Hwf0 V0 Hc0 HV0).
          * apply (SubstTT__wf_sig_subst_gen A0 E0 R0 X0 U0 Hwf0 Hws0 Hfv0 V0 Hc0 HV0).
          * exact Hbt.
      - (* typing_abs *)
        intros L Env0 R0 V0 e1 T1 Hws Hbody IHbody.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V1 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        assert (Hws0 : wf_sig (A0 ++ X0 ~ bind_sub U0 ++ E0) R0)
          by (rewrite <- HE; exact Hws).
        assert (HweEnv0 : wf_env Env0) by (rewrite HE; exact Hwf0).
        assert (HwfAbs : wf_typ Env0 (typ_arrow V0 T1))
          by (apply (SubstTT__typing_wf_typ Env0 R0 (exp_abs V0 e1) (typ_arrow V0 T1));
              apply (typing_abs L Env0 R0 V0 e1 T1 Hws Hbody)).
        destruct (Dev__wf_typ_inv_arrow Env0 V0 T1 HwfAbs) as [HwV0 _].
        assert (HwsT : wf_sig (SubstTT__subst_tt_env X0 V1 A0 ++ E0) R0)
          by (apply (SubstTT__wf_sig_subst_gen A0 E0 R0 X0 U0 Hwf0 Hws0 Hfv0 V1 Hc0 HV0)).
        apply (typing_abs (L `union` ({{X0}} `union` (dom Env0 `union` dom A0)))
                 (SubstTT__subst_tt_env X0 V1 A0 ++ E0) R0 (SubstTT__subst_tt X0 V1 V0)
                 (SubstTT__subst_te X0 V1 e1) (SubstTT__subst_tt X0 V1 T1)).
        + exact HwsT.
        + intros x HxL.
          assert (HxL0 : x `notin` L) by (apply notin_union_1 in HxL; exact HxL).
          assert (HxRest : x `notin` ({{X0}} `union` (dom Env0 `union` dom A0)))
            by (apply notin_union_2 in HxL; exact HxL).
          assert (HxSing : x `notin` {{X0}})
            by (apply notin_union_1 in HxRest; exact HxRest).
          assert (HxX : x <> X0)
            by (apply notin_singleton_1' in HxSing; symmetry; exact HxSing).
          assert (HxRest2 : x `notin` (dom Env0 `union` dom A0))
            by (apply notin_union_2 in HxRest; exact HxRest).
          assert (HxEnv0 : x `notin` dom Env0)
            by (apply notin_union_1 in HxRest2; exact HxRest2).
          assert (HxDomA : x `notin` dom A0)
            by (apply notin_union_2 in HxRest2; exact HxRest2).
          assert (HnotA' : X0 `notin` dom (x ~ bind_typ V0 ++ A0)).
          { simpl. rewrite add_iff. intros [Heq | Hin].
            - apply HxX. exact Heq.
            - exact (HnotA0 Hin). }
          assert (Hwf' : wf_env ((x ~ bind_typ V0 ++ A0) ++ X0 ~ bind_sub U0 ++ E0)).
          { change (wf_env (x ~ bind_typ V0 ++ (A0 ++ X0 ~ bind_sub U0 ++ E0))).
            rewrite <- HE. apply wf_env_typ.
            - exact HweEnv0.
            - exact HwV0.
            - exact HxEnv0. }
          assert (HE' : x ~ bind_typ V0 ++ Env0
                        = (x ~ bind_typ V0 ++ A0) ++ X0 ~ bind_sub U0 ++ E0).
          { rewrite HE. reflexivity. }
          pose proof (IHbody x HxL0 (x ~ bind_typ V0 ++ A0) E0 X0 U0 V1
                        HnotA' HnotE0 Hwf' HV0 Hc0 Hsub0 Hfv0 HE') as Hbody0.
          rewrite (SubstTT__subst_te_open_ee e1 x X0 V1) in Hbody0.
          simpl in Hbody0.
          exact Hbody0.
      - (* typing_app *)
        intros T1 Env0 R0 e1 e2 T2 Hws Ht1 IH1 Ht2 IH2.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        assert (Hws0 : wf_sig (A0 ++ X0 ~ bind_sub U0 ++ E0) R0)
          by (rewrite <- HE; exact Hws).
        assert (HwsT : wf_sig (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0)
          by (apply (SubstTT__wf_sig_subst_gen A0 E0 R0 X0 U0 Hwf0 Hws0 Hfv0 V0 Hc0 HV0)).
        pose proof (IH1 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty1.
        pose proof (IH2 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty2.
        simpl in Hty1.
        apply (typing_app (SubstTT__subst_tt X0 V0 T1)
                 (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0
                 (SubstTT__subst_te X0 V0 e1) (SubstTT__subst_te X0 V0 e2) (SubstTT__subst_tt X0 V0 T2)).
        + exact HwsT.
        + exact Hty1.
        + exact Hty2.
      - (* typing_tabs *)
        intros L Env0 R0 V0 e1 T1 Hws Hbody IHbody.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V1 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        assert (Hws0 : wf_sig (A0 ++ X0 ~ bind_sub U0 ++ E0) R0)
          by (rewrite <- HE; exact Hws).
        assert (HweEnv0 : wf_env Env0) by (rewrite HE; exact Hwf0).
        assert (HwfAll : wf_typ Env0 (typ_all V0 T1))
          by (apply (SubstTT__typing_wf_typ Env0 R0 (exp_tabs V0 e1) (typ_all V0 T1));
              apply (typing_tabs L Env0 R0 V0 e1 T1 Hws Hbody)).
        destruct (Dev__wf_typ_inv_all Env0 V0 T1 HwfAll) as [L0 [HwV0 _]].
        assert (HwsT : wf_sig (SubstTT__subst_tt_env X0 V1 A0 ++ E0) R0)
          by (apply (SubstTT__wf_sig_subst_gen A0 E0 R0 X0 U0 Hwf0 Hws0 Hfv0 V1 Hc0 HV0)).
        apply (typing_tabs (L `union` ({{X0}} `union` (dom Env0 `union` dom A0)))
                 (SubstTT__subst_tt_env X0 V1 A0 ++ E0) R0 (SubstTT__subst_tt X0 V1 V0)
                 (SubstTT__subst_te X0 V1 e1) (SubstTT__subst_tt X0 V1 T1)).
        + exact HwsT.
        + intros Y HY.
          assert (HYL : Y `notin` L) by (apply notin_union_1 in HY; exact HY).
          assert (HYRest : Y `notin` ({{X0}} `union` (dom Env0 `union` dom A0)))
            by (apply notin_union_2 in HY; exact HY).
          assert (HYSing : Y `notin` {{X0}})
            by (apply notin_union_1 in HYRest; exact HYRest).
          assert (HYX : Y <> X0)
            by (apply notin_singleton_1' in HYSing; symmetry; exact HYSing).
          assert (HYRest2 : Y `notin` (dom Env0 `union` dom A0))
            by (apply notin_union_2 in HYRest; exact HYRest).
          assert (HYEnv0 : Y `notin` dom Env0)
            by (apply notin_union_1 in HYRest2; exact HYRest2).
          assert (HYDomA : Y `notin` dom A0)
            by (apply notin_union_2 in HYRest2; exact HYRest2).
          assert (HnotA' : X0 `notin` dom (Y ~ bind_sub V0 ++ A0)).
          { simpl. rewrite add_iff. intros [Heq | Hin].
            - apply HYX. exact Heq.
            - exact (HnotA0 Hin). }
          assert (Hwf' : wf_env ((Y ~ bind_sub V0 ++ A0) ++ X0 ~ bind_sub U0 ++ E0)).
          { change (wf_env (Y ~ bind_sub V0 ++ (A0 ++ X0 ~ bind_sub U0 ++ E0))).
            rewrite <- HE. apply wf_env_sub.
            - exact HweEnv0.
            - exact HwV0.
            - exact HYEnv0. }
          assert (HE' : Y ~ bind_sub V0 ++ Env0
                        = (Y ~ bind_sub V0 ++ A0) ++ X0 ~ bind_sub U0 ++ E0).
          { rewrite HE. reflexivity. }
          pose proof (IHbody Y HYL (Y ~ bind_sub V0 ++ A0) E0 X0 U0 V1
                        HnotA' HnotE0 Hwf' HV0 Hc0 Hsub0 Hfv0 HE') as Hbody0.
          unfold open_te in Hbody0.
          unfold open_tt in Hbody0.
          rewrite <- (SubstTT__open_te_rec_comm e1 0 X0 V1 Y Hc0 HYX) in Hbody0.
          rewrite <- (SubstTT__open_tt_rec_subst_comm 0 T1 X0 V1 Y Hc0 HYX) in Hbody0.
          simpl in Hbody0.
          exact Hbody0.
      - (* typing_tapp *)
        intros T1 Env0 R0 e1 Targ T2 Hws Ht1 IH1 HsubTy.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        assert (Hws0 : wf_sig (A0 ++ X0 ~ bind_sub U0 ++ E0) R0)
          by (rewrite <- HE; exact Hws).
        assert (HweEnv0 : wf_env Env0) by (rewrite HE; exact Hwf0).
        assert (HwsT : wf_sig (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0)
          by (apply (SubstTT__wf_sig_subst_gen A0 E0 R0 X0 U0 Hwf0 Hws0 Hfv0 V0 Hc0 HV0)).
        pose proof (SubstTT__typing_wf_typ Env0 R0 e1 (typ_all T1 T2) Ht1) as HwfAll.
        destruct (Dev__wf_typ_inv_all Env0 T1 T2 HwfAll) as [L0 [HwT1 _]].
        assert (HwTS : wf_typ Env0 Targ)
          by (apply (Dev__sub_wf_source Env0 Targ T1 HweEnv0 HwT1 HsubTy)).
        assert (HwTS' : wf_typ (A0 ++ X0 ~ bind_sub U0 ++ E0) Targ)
          by (rewrite <- HE; exact HwTS).
        assert (HsubTy' : sub (A0 ++ X0 ~ bind_sub U0 ++ E0) Targ T1)
          by (rewrite <- HE; exact HsubTy).
        assert (HwVt : wf_typ (SubstTT__subst_tt_env X0 V0 A0 ++ E0) V0)
          by (apply (Dev__wf_typ_weaken E0 V0 HV0 (SubstTT__subst_tt_env X0 V0 A0))).
        pose proof (SubstTT__sub_subst_gen A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0
                      HwVt Hsub0 Targ T1 HwTS' HsubTy') as HsubT.
        pose proof (IH1 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty1.
        simpl in Hty1.
        assert (Hop : SubstTT__subst_tt X0 V0 (open_tt T2 Targ)
                      = open_tt (SubstTT__subst_tt X0 V0 T2) (SubstTT__subst_tt X0 V0 Targ)).
        { unfold open_tt. apply (SubstTT__open_tt_rec_subst2 0 T2 X0 V0 Targ Hc0). }
        rewrite Hop.
        apply (typing_tapp (SubstTT__subst_tt X0 V0 T1)
                 (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0 (SubstTT__subst_te X0 V0 e1)
                 (SubstTT__subst_tt X0 V0 Targ) (SubstTT__subst_tt X0 V0 T2)).
        + exact HwsT.
        + exact Hty1.
        + exact HsubT.
      - (* typing_sub *)
        intros S Env0 R0 e0 Tsub Hws Ht1 IH1 HsubTy.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        assert (Hws0 : wf_sig (A0 ++ X0 ~ bind_sub U0 ++ E0) R0)
          by (rewrite <- HE; exact Hws).
        assert (HweEnv0 : wf_env Env0) by (rewrite HE; exact Hwf0).
        assert (HwsT : wf_sig (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0)
          by (apply (SubstTT__wf_sig_subst_gen A0 E0 R0 X0 U0 Hwf0 Hws0 Hfv0 V0 Hc0 HV0)).
        assert (HwS : wf_typ Env0 S)
          by (apply (SubstTT__typing_wf_typ Env0 R0 e0 S Ht1)).
        assert (HwT : wf_typ Env0 Tsub)
          by (apply (Dev__sub_wf_target Env0 S Tsub HweEnv0 HwS HsubTy)).
        assert (HwS' : wf_typ (A0 ++ X0 ~ bind_sub U0 ++ E0) S)
          by (rewrite <- HE; exact HwS).
        assert (HsubTy' : sub (A0 ++ X0 ~ bind_sub U0 ++ E0) S Tsub)
          by (rewrite <- HE; exact HsubTy).
        assert (HwVt : wf_typ (SubstTT__subst_tt_env X0 V0 A0 ++ E0) V0)
          by (apply (Dev__wf_typ_weaken E0 V0 HV0 (SubstTT__subst_tt_env X0 V0 A0))).
        pose proof (SubstTT__sub_subst_gen A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0
                      HwVt Hsub0 S Tsub HwS' HsubTy') as HsubT.
        pose proof (IH1 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty1.
        apply (typing_sub (SubstTT__subst_tt X0 V0 S)
                 (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0 (SubstTT__subst_te X0 V0 e0)
                 (SubstTT__subst_tt X0 V0 Tsub)).
        + exact HwsT.
        + exact Hty1.
        + exact HsubT.
      - (* typing_let *)
        intros L T1 T2 e1 e2 Env0 R0 Hws Ht1 IH1 Hbody IHbody.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        assert (Hws0 : wf_sig (A0 ++ X0 ~ bind_sub U0 ++ E0) R0)
          by (rewrite <- HE; exact Hws).
        assert (HweEnv0 : wf_env Env0) by (rewrite HE; exact Hwf0).
        assert (HwsT : wf_sig (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0)
          by (apply (SubstTT__wf_sig_subst_gen A0 E0 R0 X0 U0 Hwf0 Hws0 Hfv0 V0 Hc0 HV0)).
        pose proof (SubstTT__typing_wf_typ Env0 R0 e1 T1 Ht1) as HwT1.
        pose proof (IH1 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty1.
        apply (typing_let (L `union` ({{X0}} `union` (dom Env0 `union` dom A0)))
                 (SubstTT__subst_tt X0 V0 T1) (SubstTT__subst_tt X0 V0 T2)
                 (SubstTT__subst_te X0 V0 e1) (SubstTT__subst_te X0 V0 e2)
                 (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0).
        + exact HwsT.
        + exact Hty1.
        + intros x HxL.
          assert (HxL0 : x `notin` L) by (apply notin_union_1 in HxL; exact HxL).
          assert (HxRest : x `notin` ({{X0}} `union` (dom Env0 `union` dom A0)))
            by (apply notin_union_2 in HxL; exact HxL).
          assert (HxSing : x `notin` {{X0}})
            by (apply notin_union_1 in HxRest; exact HxRest).
          assert (HxX : x <> X0)
            by (apply notin_singleton_1' in HxSing; symmetry; exact HxSing).
          assert (HxRest2 : x `notin` (dom Env0 `union` dom A0))
            by (apply notin_union_2 in HxRest; exact HxRest).
          assert (HxEnv0 : x `notin` dom Env0)
            by (apply notin_union_1 in HxRest2; exact HxRest2).
          assert (HnotA' : X0 `notin` dom (x ~ bind_typ T1 ++ A0)).
          { simpl. rewrite add_iff. intros [Heq | Hin].
            - apply HxX. exact Heq.
            - exact (HnotA0 Hin). }
          assert (Hwf' : wf_env ((x ~ bind_typ T1 ++ A0) ++ X0 ~ bind_sub U0 ++ E0)).
          { change (wf_env (x ~ bind_typ T1 ++ (A0 ++ X0 ~ bind_sub U0 ++ E0))).
            rewrite <- HE. apply wf_env_typ.
            - exact HweEnv0.
            - exact HwT1.
            - exact HxEnv0. }
          assert (HE' : x ~ bind_typ T1 ++ Env0
                        = (x ~ bind_typ T1 ++ A0) ++ X0 ~ bind_sub U0 ++ E0).
          { rewrite HE. reflexivity. }
          pose proof (IHbody x HxL0 (x ~ bind_typ T1 ++ A0) E0 X0 U0 V0
                        HnotA' HnotE0 Hwf' HV0 Hc0 Hsub0 Hfv0 HE') as Hbody0.
          rewrite (SubstTT__subst_te_open_ee e2 x X0 V0) in Hbody0.
          simpl in Hbody0.
          exact Hbody0.
      - (* typing_box *)
        intros Env0 R0 e T Hws Ht1 IH1.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        assert (Hws0 : wf_sig (A0 ++ X0 ~ bind_sub U0 ++ E0) R0)
          by (rewrite <- HE; exact Hws).
        assert (HwsT : wf_sig (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0)
          by (apply (SubstTT__wf_sig_subst_gen A0 E0 R0 X0 U0 Hwf0 Hws0 Hfv0 V0 Hc0 HV0)).
        pose proof (IH1 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty1.
        apply (typing_box (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0
                 (SubstTT__subst_te X0 V0 e) (SubstTT__subst_tt X0 V0 T)).
        + exact HwsT.
        + exact Hty1.
      - (* typing_unbox *)
        intros Env0 R0 e T Hws Ht1 IH1.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        assert (Hws0 : wf_sig (A0 ++ X0 ~ bind_sub U0 ++ E0) R0)
          by (rewrite <- HE; exact Hws).
        assert (HwsT : wf_sig (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0)
          by (apply (SubstTT__wf_sig_subst_gen A0 E0 R0 X0 U0 Hwf0 Hws0 Hfv0 V0 Hc0 HV0)).
        pose proof (IH1 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty1.
        simpl in Hty1.
        apply (typing_unbox (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0
                 (SubstTT__subst_te X0 V0 e) (SubstTT__subst_tt X0 V0 T)).
        + exact HwsT.
        + exact Hty1.
      - (* typing_set_box *)
        intros Env0 R0 e1 e2 T Hws Ht1 IH1 Ht2 IH2.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        assert (Hws0 : wf_sig (A0 ++ X0 ~ bind_sub U0 ++ E0) R0)
          by (rewrite <- HE; exact Hws).
        assert (HwsT : wf_sig (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0)
          by (apply (SubstTT__wf_sig_subst_gen A0 E0 R0 X0 U0 Hwf0 Hws0 Hfv0 V0 Hc0 HV0)).
        pose proof (IH1 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty1.
        pose proof (IH2 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty2.
        simpl in Hty1.
        apply (typing_set_box (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0
                 (SubstTT__subst_te X0 V0 e1) (SubstTT__subst_te X0 V0 e2) (SubstTT__subst_tt X0 V0 T)).
        + exact HwsT.
        + exact Hty1.
        + exact Hty2.
      - (* typing_ref *)
        intros Env0 R0 l T Hwe Hws Hb.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        assert (Hws0 : wf_sig (A0 ++ X0 ~ bind_sub U0 ++ E0) R0)
          by (rewrite <- HE; exact Hws).
        assert (HweT : wf_env (SubstTT__subst_tt_env X0 V0 A0 ++ E0))
          by (apply (SubstTT__wf_env_subst_gen A0 E0 X0 U0 Hwf0 V0 Hc0 HV0)).
        assert (HwsT : wf_sig (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0)
          by (apply (SubstTT__wf_sig_subst_gen A0 E0 R0 X0 U0 Hwf0 Hws0 Hfv0 V0 Hc0 HV0)).
        assert (HnotX : X0 `notin` Dev__fv_typ T)
          by (apply (SubstTT__fv_sig_binds_typ R0 l T X0 Hb Hfv0)).
        assert (HeqT : SubstTT__subst_tt X0 V0 T = T) by (apply SubstTT__subst_tt_id; exact HnotX).
        apply (typing_ref (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0 l (SubstTT__subst_tt X0 V0 T)).
        + exact HweT.
        + exact HwsT.
        + rewrite HeqT. exact Hb.
      - (* typing_seal *)
        intros Env0 R0 e T Ht1 IH1.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        pose proof (IH1 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty1.
        apply (typing_seal (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0
                 (SubstTT__subst_te X0 V0 e) (SubstTT__subst_tt X0 V0 T)).
        exact Hty1.
      - (* typing_unbox_readonly *)
        intros Env0 R0 e T Ht1 IH1.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        pose proof (IH1 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty1.
        simpl in Hty1.
        apply (typing_unbox_readonly (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0
                 (SubstTT__subst_te X0 V0 e) (SubstTT__subst_tt X0 V0 T)).
        exact Hty1.
      - (* typing_record *)
        intros Env0 R0 r T Htr IHtr.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        assert (Hws0 : wf_sig (A0 ++ X0 ~ bind_sub U0 ++ E0) R0)
          by (rewrite <- HE;
              apply (SubstTT__typing_record_comp_wf_sig Env0 R0 r T Htr)).
        assert (Htr' : typing_record_comp (A0 ++ X0 ~ bind_sub U0 ++ E0) R0 r T)
          by (rewrite <- HE; exact Htr).
        apply (typing_record (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0
                 (SubstTT__subst_te_record X0 V0 r) (SubstTT__subst_tt X0 V0 T)).
        apply (SubstTT__typing_record_comp_subst_te_gen A0 E0 X0 U0 R0 r T V0
                 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 Htr').
      - (* typing_record_read *)
        intros Env0 R0 e a T Ht1 IH1.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        pose proof (IH1 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty1.
        simpl in Hty1.
        apply (typing_record_read (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0
                 (SubstTT__subst_te X0 V0 e) a (SubstTT__subst_tt X0 V0 T)).
        exact Hty1.
      - (* typing_record_read_readonly *)
        intros Env0 R0 e a T Ht1 IH1.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        pose proof (IH1 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty1.
        simpl in Hty1.
        apply (typing_record_read_readonly (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0
                 (SubstTT__subst_te X0 V0 e) a (SubstTT__subst_tt X0 V0 T)).
        exact Hty1.
      - (* typing_record_write *)
        intros Env0 R0 e1 a e2 T Ht1 IH1 Ht2 IH2.
        unfold SubstTT__typing_subst_P.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        pose proof (IH1 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty1.
        pose proof (IH2 A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hty2.
        simpl in Hty1.
        apply (typing_record_write (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0
                 (SubstTT__subst_te X0 V0 e1) a (SubstTT__subst_te X0 V0 e2) (SubstTT__subst_tt X0 V0 T)).
        + exact Hty1.
        + exact Hty2.
      - (* typing_record_empty, P0true *)
        intros Env0 R0 Hwe Hws. unfold SubstTT__typing_subst_P0_true. exact I.
      - (* typing_record_exp, P0true *)
        intros Env0 R0 a e r T Tr Hnotin Htr IHtr Ht IHt.
        unfold SubstTT__typing_subst_P0_true. exact I.
      - (* typing_record_ref, P0true *)
        intros Env0 R0 a l r T Tr Hnotin Htr IHtr Hb.
        unfold SubstTT__typing_subst_P0_true. exact I.
    }
    unfold SubstTT__typing_subst_P in Hgen.
    exact (Hgen A E X U V HnotA HnotE Hwf HV Hc Hsub Hfv eq_refl).
  - intros A E X U R r T V HnotA HnotE Hwf HV Hc Hsub Hfv Htr.
    assert (Hgen : SubstTT__typing_subst_P0 (A ++ X ~ bind_sub U ++ E) R r T Htr).
    { apply (SubstTT__typing_record_mut SubstTT__typing_subst_P_true SubstTT__typing_subst_P0).
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - intros. unfold SubstTT__typing_subst_P_true. exact I.
      - (* typing_record_empty *)
        intros Env0 R0 Hwe Hws.
        unfold SubstTT__typing_subst_P0.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        assert (Hws0 : wf_sig (A0 ++ X0 ~ bind_sub U0 ++ E0) R0)
          by (rewrite <- HE; exact Hws).
        simpl.
        apply typing_record_empty.
        + apply (SubstTT__wf_env_subst_gen A0 E0 X0 U0 Hwf0 V0 Hc0 HV0).
        + apply (SubstTT__wf_sig_subst_gen A0 E0 R0 X0 U0 Hwf0 Hws0 Hfv0 V0 Hc0 HV0).
      - (* typing_record_exp *)
        intros Env0 R0 a eF rTail TF Tr Hnotin Htail IHtail Ht IHfield.
        unfold SubstTT__typing_subst_P0.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        pose proof (IHtail A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hrec.
        assert (Ht' : typing (A0 ++ X0 ~ bind_sub U0 ++ E0) R0 eF TF)
          by (rewrite <- HE; exact Ht).
        pose proof (SubstTT__typing_subst_te_gen A0 E0 X0 U0 R0 eF TF V0
                      HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 Ht') as Hfield.
        simpl.
        apply (typing_record_exp (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0 a
                 (SubstTT__subst_te X0 V0 eF) (SubstTT__subst_te_record X0 V0 rTail)
                 (SubstTT__subst_tt X0 V0 TF) (SubstTT__subst_tt X0 V0 Tr)).
        + rewrite SubstTT__record_dom_subst_te_record. exact Hnotin.
        + exact Hrec.
        + exact Hfield.
      - (* typing_record_ref *)
        intros Env0 R0 a l rTail TF Tr Hnotin Htail IHtail Hb.
        unfold SubstTT__typing_subst_P0.
        intros A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE.
        pose proof (IHtail A0 E0 X0 U0 V0 HnotA0 HnotE0 Hwf0 HV0 Hc0 Hsub0 Hfv0 HE)
          as Hrec.
        assert (HnotX : X0 `notin` Dev__fv_typ TF)
          by (apply (SubstTT__fv_sig_binds_typ R0 l TF X0 Hb Hfv0)).
        assert (HeqT : SubstTT__subst_tt X0 V0 TF = TF)
          by (apply SubstTT__subst_tt_id; exact HnotX).
        simpl.
        apply (typing_record_ref (SubstTT__subst_tt_env X0 V0 A0 ++ E0) R0 a l
                 (SubstTT__subst_te_record X0 V0 rTail)
                 (SubstTT__subst_tt X0 V0 TF) (SubstTT__subst_tt X0 V0 Tr)).
        + rewrite SubstTT__record_dom_subst_te_record. exact Hnotin.
        + exact Hrec.
        + rewrite HeqT. exact Hb.
    }
    unfold SubstTT__typing_subst_P0 in Hgen.
    exact (Hgen A E X U V HnotA HnotE Hwf HV Hc Hsub Hfv eq_refl).
Qed.

(* ================================================================== *)
(* Corollaries at the empty prefix.                                   *)
(* ================================================================== *)

Corollary SubstTT__typing_subst_tt : forall (E : env) (R : sig) X U V e T,
  wf_typ E V ->
  sub E V U ->
  X `notin` SubstTT__fv_sig R ->
  typing (X ~ bind_sub U ++ E) R e T ->
  typing E R (SubstTT__subst_te X V e) (SubstTT__subst_tt X V T).
Proof.
  intros E R X U V e T HV Hsub Hfv Hty.
  assert (Hc : SubstTT__closed_typ V) by (apply (SubstTT__wf_typ_closed E V HV)).
  assert (Hws : wf_sig (X ~ bind_sub U ++ E) R)
    by (apply (SubstTT__typing_wf_sig (X ~ bind_sub U ++ E) R e T Hty)).
  assert (Hwe : wf_env (X ~ bind_sub U ++ E))
    by (apply (Dev__wf_sig_wf_env (X ~ bind_sub U ++ E) R Hws)).
  destruct (SubstTT__test_wf_env_cons_bind_sub_inv E X U Hwe) as [HweE [HwU HnotE]].
  apply (SubstTT__typing_subst_te_gen nil E X U R e T V (notin_empty X) HnotE Hwe HV Hc Hsub Hfv).
  exact Hty.
Qed.

Corollary SubstTT__typing_record_comp_subst_tt : forall (E : env) (R : sig) X U V r T,
  wf_typ E V ->
  sub E V U ->
  X `notin` SubstTT__fv_sig R ->
  typing_record_comp (X ~ bind_sub U ++ E) R r T ->
  typing_record_comp E R (SubstTT__subst_te_record X V r) (SubstTT__subst_tt X V T).
Proof.
  intros E R X U V r T HV Hsub Hfv Htr.
  assert (Hc : SubstTT__closed_typ V) by (apply (SubstTT__wf_typ_closed E V HV)).
  assert (Hws : wf_sig (X ~ bind_sub U ++ E) R)
    by (apply (SubstTT__typing_record_comp_wf_sig (X ~ bind_sub U ++ E) R r T Htr)).
  assert (Hwe : wf_env (X ~ bind_sub U ++ E))
    by (apply (Dev__wf_sig_wf_env (X ~ bind_sub U ++ E) R Hws)).
  destruct (SubstTT__test_wf_env_cons_bind_sub_inv E X U Hwe) as [HweE [HwU HnotE]].
  apply (SubstTT__typing_record_comp_subst_te_gen nil E X U R r T V
           (notin_empty X) HnotE Hwe HV Hc Hsub Hfv).
  exact Htr.
Qed.

Corollary SubstTT__typing_subst_tt0 : forall (E : env) X V (R : sig) e T,
  X `notin` dom E ->
  wf_typ E V ->
  X `notin` SubstTT__fv_sig R ->
  typing (X ~ bind_sub V ++ E) R e T ->
  typing E R (SubstTT__subst_te X V e) (SubstTT__subst_tt X V T).
Proof.
  intros E X V R e T HnotE HV Hfv Hty.
  assert (Hws : wf_sig (X ~ bind_sub V ++ E) R)
    by (apply (SubstTT__typing_wf_sig (X ~ bind_sub V ++ E) R e T Hty)).
  assert (Hwe : wf_env (X ~ bind_sub V ++ E))
    by (apply (Dev__wf_sig_wf_env (X ~ bind_sub V ++ E) R Hws)).
  destruct (SubstTT__test_wf_env_cons_bind_sub_inv E X V Hwe) as [HweE [_ _]].
  assert (Hc : SubstTT__closed_typ V) by (apply (SubstTT__wf_typ_closed E V HV)).
  assert (Hsub : sub E V V) by (apply (Dev__sub_refl E V HweE HV)).
  apply (SubstTT__typing_subst_tt E R X V V e T HV Hsub Hfv Hty).
Qed.

Corollary SubstTT__typing_record_comp_subst_tt0 : forall (E : env) X V (R : sig) r T,
  X `notin` dom E ->
  wf_typ E V ->
  X `notin` SubstTT__fv_sig R ->
  typing_record_comp (X ~ bind_sub V ++ E) R r T ->
  typing_record_comp E R (SubstTT__subst_te_record X V r) (SubstTT__subst_tt X V T).
Proof.
  intros E X V R r T HnotE HV Hfv Htr.
  assert (Hws : wf_sig (X ~ bind_sub V ++ E) R)
    by (apply (SubstTT__typing_record_comp_wf_sig (X ~ bind_sub V ++ E) R r T Htr)).
  assert (Hwe : wf_env (X ~ bind_sub V ++ E))
    by (apply (Dev__wf_sig_wf_env (X ~ bind_sub V ++ E) R Hws)).
  destruct (SubstTT__test_wf_env_cons_bind_sub_inv E X V Hwe) as [HweE [_ _]].
  assert (Hc : SubstTT__closed_typ V) by (apply (SubstTT__wf_typ_closed E V HV)).
  assert (Hsub : sub E V V) by (apply (Dev__sub_refl E V HweE HV)).
  apply (SubstTT__typing_record_comp_subst_tt E R X V V r T HV Hsub Hfv Htr).
Qed.

(* Raw/open form: the source derivation is the body opened at X.          *)
Corollary SubstTT__typing_subst_tt_open : forall (E : env) (R : sig) X U V e T,
  X `notin` SubstTT__fv_te e ->
  X `notin` Dev__fv_typ T ->
  X `notin` SubstTT__fv_sig R ->
  wf_typ E V ->
  sub E V U ->
  typing (X ~ bind_sub U ++ E) R (open_te e X) (open_tt T X) ->
  typing E R (open_te e V) (open_tt T V).
Proof.
  intros E R X U V e T Hfve HfvT HfvR HV Hsub Hty.
  pose proof (SubstTT__typing_subst_tt E R X U V (open_te e X) (open_tt T X)
                HV Hsub HfvR Hty) as H.
  rewrite <- (SubstTT__open_te_subst_te e X V Hfve) in H.
  rewrite <- (SubstTT__open_tt_subst_tt T X V HfvT) in H.
  exact H.
Qed.

Corollary SubstTT__typing_subst_tt0_open : forall (E : env) X V (R : sig) e T,
  X `notin` SubstTT__fv_te e ->
  X `notin` Dev__fv_typ T ->
  X `notin` SubstTT__fv_sig R ->
  wf_typ E V ->
  typing (X ~ bind_sub V ++ E) R (open_te e X) (open_tt T X) ->
  typing E R (open_te e V) (open_tt T V).
Proof.
  intros E X V R e T Hfve HfvT HfvR HV Hty.
  assert (Hws : wf_sig (X ~ bind_sub V ++ E) R)
    by (apply (SubstTT__typing_wf_sig (X ~ bind_sub V ++ E) R (open_te e X) (open_tt T X) Hty)).
  assert (Hwe : wf_env (X ~ bind_sub V ++ E))
    by (apply (Dev__wf_sig_wf_env (X ~ bind_sub V ++ E) R Hws)).
  destruct (SubstTT__test_wf_env_cons_bind_sub_inv E X V Hwe) as [HweE [_ _]].
  assert (Hc : SubstTT__closed_typ V) by (apply (SubstTT__wf_typ_closed E V HV)).
  assert (Hsub : sub E V V) by (apply (Dev__sub_refl E V HweE HV)).
  apply (SubstTT__typing_subst_tt_open E R X V V e T Hfve HfvT HfvR HV Hsub Hty).
Qed.

Corollary SubstTT__sub_subst_tt : forall (E : env) X U V S T,
  wf_typ E V ->
  wf_env (X ~ bind_sub U ++ E) ->
  sub E V U ->
  wf_typ (X ~ bind_sub U ++ E) S ->
  sub (X ~ bind_sub U ++ E) S T ->
  sub E (SubstTT__subst_tt X V S) (SubstTT__subst_tt X V T).
Proof.
  intros E X U V S T HV Hwf Hsub HwS HsubS.
  assert (Hc : SubstTT__closed_typ V) by (apply (SubstTT__wf_typ_closed E V HV)).
  destruct (SubstTT__test_wf_env_cons_bind_sub_inv E X U Hwf) as [HweE [HwU HnotE]].
  assert (HwVt : wf_typ (SubstTT__subst_tt_env X V nil ++ E) V).
  { apply (Dev__wf_typ_weaken E V HV (SubstTT__subst_tt_env X V nil)). }
  apply (SubstTT__sub_subst_gen nil E X U V (notin_empty X) HnotE Hwf HV Hc HwVt
           Hsub S T HwS HsubS).
Qed.




(* ================================================================ *)
(* Mutual induction principle for typing / typing_record_comp       *)
(* ================================================================ *)

Scheme SubstEE__typing_induction := Induction for typing Sort Prop
with SubstEE__typing_record_induction := Induction for typing_record_comp Sort Prop.

(* ================================================================ *)
(* 1. Term-variable substitution                                    *)
(* ================================================================ *)

Fixpoint SubstEE__subst_ee (x : atom) (v e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar y => if (x === y) then v else exp_fvar y
  | exp_abs V e1 => exp_abs V (SubstEE__subst_ee x v e1)
  | exp_app e1 e2 => exp_app (SubstEE__subst_ee x v e1) (SubstEE__subst_ee x v e2)
  | exp_tabs V e1 => exp_tabs V (SubstEE__subst_ee x v e1)
  | exp_tapp e1 V => exp_tapp (SubstEE__subst_ee x v e1) V
  | exp_let e1 e2 => exp_let (SubstEE__subst_ee x v e1) (SubstEE__subst_ee x v e2)
  | exp_box e1 => exp_box (SubstEE__subst_ee x v e1)
  | exp_unbox e1 => exp_unbox (SubstEE__subst_ee x v e1)
  | exp_set_box e1 e2 => exp_set_box (SubstEE__subst_ee x v e1) (SubstEE__subst_ee x v e2)
  | exp_ref l => exp_ref l
  | exp_seal e1 => exp_seal (SubstEE__subst_ee x v e1)
  | exp_record r => exp_record (SubstEE__subst_ee_rec_comp x v r)
  | exp_record_read e1 a => exp_record_read (SubstEE__subst_ee x v e1) a
  | exp_record_write e1 a e2 => exp_record_write (SubstEE__subst_ee x v e1) a (SubstEE__subst_ee x v e2)
  end
with SubstEE__subst_ee_rec_comp (x : atom) (v : exp) (r : rec_comp) {struct r} : rec_comp :=
  match r with
  | rec_empty => rec_empty
  | rec_exp a e r => rec_exp a (SubstEE__subst_ee x v e) (SubstEE__subst_ee_rec_comp x v r)
  | rec_ref a l r => rec_ref a l (SubstEE__subst_ee_rec_comp x v r)
  end.

Lemma SubstEE__subst_ee_eq_fvar : forall x v,
  SubstEE__subst_ee x v (exp_fvar x) = v.
Proof.
  intros. simpl.
  destruct (x === x) as [Heq|Hneq]; [reflexivity|].
  exfalso. apply Hneq. reflexivity.
Qed.

Lemma SubstEE__subst_ee_neq_fvar : forall x y v,
  y <> x -> SubstEE__subst_ee x v (exp_fvar y) = exp_fvar y.
Proof.
  intros. simpl.
  destruct (x === y) as [Heq|Hneq]; [|reflexivity].
  exfalso. apply H. symmetry. assumption.
Qed.

(* ================================================================ *)
(* 2. Free atoms of an expression                                   *)
(* ================================================================ *)

Fixpoint SubstEE__fv_exp (e : exp) : atoms :=
  match e with
  | exp_bvar _ => {}
  | exp_fvar x => {{ x }}
  | exp_abs V e1 => Dev__fv_typ V `union` SubstEE__fv_exp e1
  | exp_app e1 e2 => SubstEE__fv_exp e1 `union` SubstEE__fv_exp e2
  | exp_tabs V e1 => Dev__fv_typ V `union` SubstEE__fv_exp e1
  | exp_tapp e1 V => SubstEE__fv_exp e1 `union` Dev__fv_typ V
  | exp_let e1 e2 => SubstEE__fv_exp e1 `union` SubstEE__fv_exp e2
  | exp_box e1 => SubstEE__fv_exp e1
  | exp_unbox e1 => SubstEE__fv_exp e1
  | exp_set_box e1 e2 => SubstEE__fv_exp e1 `union` SubstEE__fv_exp e2
  | exp_ref _ => {}
  | exp_seal e1 => SubstEE__fv_exp e1
  | exp_record r => SubstEE__fv_rec_comp r
  | exp_record_read e1 a => SubstEE__fv_exp e1 `union` {{ a }}
  | exp_record_write e1 a e2 => (SubstEE__fv_exp e1 `union` {{ a }}) `union` SubstEE__fv_exp e2
  end
with SubstEE__fv_rec_comp (r : rec_comp) : atoms :=
  match r with
  | rec_empty => {}
  | rec_exp a e r => ({{ a }} `union` SubstEE__fv_exp e) `union` SubstEE__fv_rec_comp r
  | rec_ref a _ r => {{ a }} `union` SubstEE__fv_rec_comp r
  end.

Fixpoint SubstEE__subst_ee_fv (e : exp) {struct e} :
  forall x v, x `notin` SubstEE__fv_exp e -> SubstEE__subst_ee x v e = e :=
  match e with
  | exp_bvar i => fun x v _ => eq_refl
  | exp_fvar y =>
      fun x v H => SubstEE__subst_ee_neq_fvar x y v (notin_singleton_1' y x H)
  | exp_abs V e1 =>
      fun x v H =>
        f_equal (fun z => exp_abs V z)
          (SubstEE__subst_ee_fv e1 x v (notin_union_2 x (Dev__fv_typ V) (SubstEE__fv_exp e1) H))
  | exp_app e1 e2 =>
      fun x v H =>
        f_equal2 exp_app
          (SubstEE__subst_ee_fv e1 x v (notin_union_1 x (SubstEE__fv_exp e1) (SubstEE__fv_exp e2) H))
          (SubstEE__subst_ee_fv e2 x v (notin_union_2 x (SubstEE__fv_exp e1) (SubstEE__fv_exp e2) H))
  | exp_tabs V e1 =>
      fun x v H =>
        f_equal (fun z => exp_tabs V z)
          (SubstEE__subst_ee_fv e1 x v (notin_union_2 x (Dev__fv_typ V) (SubstEE__fv_exp e1) H))
  | exp_tapp e1 V =>
      fun x v H =>
        f_equal (fun z => exp_tapp z V)
          (SubstEE__subst_ee_fv e1 x v (notin_union_1 x (SubstEE__fv_exp e1) (Dev__fv_typ V) H))
  | exp_let e1 e2 =>
      fun x v H =>
        f_equal2 exp_let
          (SubstEE__subst_ee_fv e1 x v (notin_union_1 x (SubstEE__fv_exp e1) (SubstEE__fv_exp e2) H))
          (SubstEE__subst_ee_fv e2 x v (notin_union_2 x (SubstEE__fv_exp e1) (SubstEE__fv_exp e2) H))
  | exp_box e1 =>
      fun x v H => f_equal exp_box (SubstEE__subst_ee_fv e1 x v H)
  | exp_unbox e1 =>
      fun x v H => f_equal exp_unbox (SubstEE__subst_ee_fv e1 x v H)
  | exp_set_box e1 e2 =>
      fun x v H =>
        f_equal2 exp_set_box
          (SubstEE__subst_ee_fv e1 x v (notin_union_1 x (SubstEE__fv_exp e1) (SubstEE__fv_exp e2) H))
          (SubstEE__subst_ee_fv e2 x v (notin_union_2 x (SubstEE__fv_exp e1) (SubstEE__fv_exp e2) H))
  | exp_ref l => fun x v _ => eq_refl
  | exp_seal e1 =>
      fun x v H => f_equal exp_seal (SubstEE__subst_ee_fv e1 x v H)
  | exp_record r =>
      fun x v H => f_equal exp_record (SubstEE__subst_ee_rec_fv r x v H)
  | exp_record_read e1 a =>
      fun x v H =>
        f_equal (fun z => exp_record_read z a)
          (SubstEE__subst_ee_fv e1 x v (notin_union_1 x (SubstEE__fv_exp e1) {{ a }} H))
  | exp_record_write e1 a e2 =>
      fun x v H =>
        f_equal2 (fun z w => exp_record_write z a w)
          (SubstEE__subst_ee_fv e1 x v
             (notin_union_1 x (SubstEE__fv_exp e1) {{ a }}
                (notin_union_1 x (SubstEE__fv_exp e1 `union` {{ a }}) (SubstEE__fv_exp e2) H)))
          (SubstEE__subst_ee_fv e2 x v
             (notin_union_2 x (SubstEE__fv_exp e1 `union` {{ a }}) (SubstEE__fv_exp e2) H))
  end
with SubstEE__subst_ee_rec_fv (r : rec_comp) {struct r} :
  forall x v, x `notin` SubstEE__fv_rec_comp r -> SubstEE__subst_ee_rec_comp x v r = r :=
  match r with
  | rec_empty => fun x v _ => eq_refl
  | rec_exp a e r =>
      fun x v H =>
        f_equal2 (fun z w => rec_exp a z w)
          (SubstEE__subst_ee_fv e x v
             (notin_union_2 x ({{ a }}) (SubstEE__fv_exp e)
                (notin_union_1 x ({{ a }} `union` SubstEE__fv_exp e) (SubstEE__fv_rec_comp r) H)))
          (SubstEE__subst_ee_rec_fv r x v
             (notin_union_2 x ({{ a }} `union` SubstEE__fv_exp e) (SubstEE__fv_rec_comp r) H))
  | rec_ref a l r =>
      fun x v H =>
        f_equal (fun z => rec_ref a l z)
          (SubstEE__subst_ee_rec_fv r x v
             (notin_union_2 x ({{ a }}) (SubstEE__fv_rec_comp r) H))
  end.

Lemma SubstEE__subst_ee_fv_apply : forall e x v,
  x `notin` SubstEE__fv_exp e -> SubstEE__subst_ee x v e = e.
Proof. intros. apply (SubstEE__subst_ee_fv e). assumption. Qed.

Lemma SubstEE__subst_ee_rec_fv_apply : forall r x v,
  x `notin` SubstEE__fv_rec_comp r -> SubstEE__subst_ee_rec_comp x v r = r.
Proof. intros. apply (SubstEE__subst_ee_rec_fv r). assumption. Qed.

(* ================================================================ *)
(* 3. Local closure of terms (term variables)                      *)
(* ================================================================ *)

Fixpoint SubstEE__lc_exp (d : nat) (e : exp) {struct e} : Prop :=
  match e with
  | exp_bvar i => i < d
  | exp_fvar _ => True
  | exp_abs _ e1 => SubstEE__lc_exp (S d) e1
  | exp_app e1 e2 => SubstEE__lc_exp d e1 /\ SubstEE__lc_exp d e2
  | exp_tabs _ e1 => SubstEE__lc_exp d e1
  | exp_tapp e1 _ => SubstEE__lc_exp d e1
  | exp_let e1 e2 => SubstEE__lc_exp d e1 /\ SubstEE__lc_exp (S d) e2
  | exp_box e1 => SubstEE__lc_exp d e1
  | exp_unbox e1 => SubstEE__lc_exp d e1
  | exp_set_box e1 e2 => SubstEE__lc_exp d e1 /\ SubstEE__lc_exp d e2
  | exp_ref _ => True
  | exp_seal e1 => SubstEE__lc_exp d e1
  | exp_record r => SubstEE__lc_rec d r
  | exp_record_read e1 _ => SubstEE__lc_exp d e1
  | exp_record_write e1 _ e2 => SubstEE__lc_exp d e1 /\ SubstEE__lc_exp d e2
  end
with SubstEE__lc_rec (d : nat) (r : rec_comp) {struct r} : Prop :=
  match r with
  | rec_empty => True
  | rec_exp _ e r => SubstEE__lc_exp d e /\ SubstEE__lc_rec d r
  | rec_ref _ _ r => SubstEE__lc_rec d r
  end.

Lemma SubstEE__lc_exp_bound_eq : forall e d d', d = d' -> SubstEE__lc_exp d e -> SubstEE__lc_exp d' e.
Proof. intros e d d' Heq H. subst. exact H. Qed.

Lemma SubstEE__lc_rec_bound_eq : forall r d d', d = d' -> SubstEE__lc_rec d r -> SubstEE__lc_rec d' r.
Proof. intros r d d' Heq H. subst. exact H. Qed.

Lemma SubstEE__max_succ_succ_aux : forall d j,
  max (S d) (S (S j)) = S (max d (S j)).
Proof. intros. symmetry. apply Nat.succ_max_distr. Qed.

Lemma SubstEE__lc_exp_open_ee_bvar : forall d i, i < d -> forall k w,
  d <= k -> open_ee_rec k w (exp_bvar i) = exp_bvar i.
Proof.
  intros d i H k w Hk. simpl.
  destruct (k == i) as [Heq|Hneq]; [|reflexivity].
  exfalso. subst i.
  exact (Nat.lt_irrefl k (Nat.lt_le_trans k d k H Hk)).
Qed.

Fixpoint SubstEE__lc_exp_open_ee (e : exp) {struct e} :
  forall d, SubstEE__lc_exp d e ->
  forall k w, d <= k -> open_ee_rec k w e = e :=
  match e with
  | exp_bvar i => fun d H k w Hk => SubstEE__lc_exp_open_ee_bvar d i H k w Hk
  | exp_fvar _ => fun d _ k w _ => eq_refl
  | exp_abs V e1 =>
      fun d H k w Hk =>
        f_equal (fun z => exp_abs V z)
          (SubstEE__lc_exp_open_ee e1 (S d) H (S k) w (le_n_S d k Hk))
  | exp_app e1 e2 =>
      fun d H k w Hk =>
        f_equal2 exp_app
          (SubstEE__lc_exp_open_ee e1 d (proj1 H) k w Hk)
          (SubstEE__lc_exp_open_ee e2 d (proj2 H) k w Hk)
  | exp_tabs V e1 =>
      fun d H k w Hk =>
        f_equal (fun z => exp_tabs V z)
          (SubstEE__lc_exp_open_ee e1 d H k w Hk)
  | exp_tapp e1 V =>
      fun d H k w Hk =>
        f_equal (fun z => exp_tapp z V)
          (SubstEE__lc_exp_open_ee e1 d H k w Hk)
  | exp_let e1 e2 =>
      fun d H k w Hk =>
        f_equal2 exp_let
          (SubstEE__lc_exp_open_ee e1 d (proj1 H) k w Hk)
          (SubstEE__lc_exp_open_ee e2 (S d) (proj2 H) (S k) w (le_n_S d k Hk))
  | exp_box e1 =>
      fun d H k w Hk => f_equal exp_box (SubstEE__lc_exp_open_ee e1 d H k w Hk)
  | exp_unbox e1 =>
      fun d H k w Hk => f_equal exp_unbox (SubstEE__lc_exp_open_ee e1 d H k w Hk)
  | exp_set_box e1 e2 =>
      fun d H k w Hk =>
        f_equal2 exp_set_box
          (SubstEE__lc_exp_open_ee e1 d (proj1 H) k w Hk)
          (SubstEE__lc_exp_open_ee e2 d (proj2 H) k w Hk)
  | exp_ref l => fun d _ k w _ => eq_refl
  | exp_seal e1 =>
      fun d H k w Hk => f_equal exp_seal (SubstEE__lc_exp_open_ee e1 d H k w Hk)
  | exp_record r =>
      fun d H k w Hk => f_equal exp_record (SubstEE__lc_rec_open_ee r d H k w Hk)
  | exp_record_read e1 a =>
      fun d H k w Hk =>
        f_equal (fun z => exp_record_read z a)
          (SubstEE__lc_exp_open_ee e1 d H k w Hk)
  | exp_record_write e1 a e2 =>
      fun d H k w Hk =>
        f_equal2 (fun z z' => exp_record_write z a z')
          (SubstEE__lc_exp_open_ee e1 d (proj1 H) k w Hk)
          (SubstEE__lc_exp_open_ee e2 d (proj2 H) k w Hk)
  end
with SubstEE__lc_rec_open_ee (r : rec_comp) {struct r} :
  forall d, SubstEE__lc_rec d r ->
  forall k w, d <= k -> open_ee_record_rec k w r = r :=
  match r with
  | rec_empty => fun d _ k w _ => eq_refl
  | rec_exp a e r =>
      fun d H k w Hk =>
        f_equal2 (fun z z' => rec_exp a z z')
          (SubstEE__lc_exp_open_ee e d (proj1 H) k w Hk)
          (SubstEE__lc_rec_open_ee r d (proj2 H) k w Hk)
  | rec_ref a l r =>
      fun d H k w Hk =>
        f_equal (fun z => rec_ref a l z)
          (SubstEE__lc_rec_open_ee r d H k w Hk)
  end.

Lemma SubstEE__lc_exp_open_ee_apply : forall e,
  SubstEE__lc_exp 0 e -> forall k w, open_ee_rec k w e = e.
Proof. intros e H k w. apply (SubstEE__lc_exp_open_ee e 0 H k w). apply Nat.le_0_l. Qed.

Lemma SubstEE__lc_rec_open_ee_apply : forall r,
  SubstEE__lc_rec 0 r -> forall k w, open_ee_record_rec k w r = r.
Proof. intros r H k w. apply (SubstEE__lc_rec_open_ee r 0 H k w). apply Nat.le_0_l. Qed.

Fixpoint SubstEE__lc_exp_open_te_inv (e : exp) {struct e} :
  forall d K U, SubstEE__lc_exp d (open_te_rec K U e) -> SubstEE__lc_exp d e :=
  match e with
  | exp_bvar i => fun d K U H => H
  | exp_fvar x => fun d K U H => H
  | exp_abs V e1 =>
      fun d K U H => SubstEE__lc_exp_open_te_inv e1 (S d) K U H
  | exp_app e1 e2 =>
      fun d K U H =>
        conj (SubstEE__lc_exp_open_te_inv e1 d K U (proj1 H))
             (SubstEE__lc_exp_open_te_inv e2 d K U (proj2 H))
  | exp_tabs V e1 =>
      fun d K U H => SubstEE__lc_exp_open_te_inv e1 d (S K) U H
  | exp_tapp e1 V =>
      fun d K U H => SubstEE__lc_exp_open_te_inv e1 d K U H
  | exp_let e1 e2 =>
      fun d K U H =>
        conj (SubstEE__lc_exp_open_te_inv e1 d K U (proj1 H))
             (SubstEE__lc_exp_open_te_inv e2 (S d) K U (proj2 H))
  | exp_box e1 =>
      fun d K U H => SubstEE__lc_exp_open_te_inv e1 d K U H
  | exp_unbox e1 =>
      fun d K U H => SubstEE__lc_exp_open_te_inv e1 d K U H
  | exp_set_box e1 e2 =>
      fun d K U H =>
        conj (SubstEE__lc_exp_open_te_inv e1 d K U (proj1 H))
             (SubstEE__lc_exp_open_te_inv e2 d K U (proj2 H))
  | exp_ref l => fun d K U _ => I
  | exp_seal e1 =>
      fun d K U H => SubstEE__lc_exp_open_te_inv e1 d K U H
  | exp_record r =>
      fun d K U H => SubstEE__lc_rec_open_te_inv r d K U H
  | exp_record_read e1 a =>
      fun d K U H => SubstEE__lc_exp_open_te_inv e1 d K U H
  | exp_record_write e1 a e2 =>
      fun d K U H =>
        conj (SubstEE__lc_exp_open_te_inv e1 d K U (proj1 H))
             (SubstEE__lc_exp_open_te_inv e2 d K U (proj2 H))
  end
with SubstEE__lc_rec_open_te_inv (r : rec_comp) {struct r} :
  forall d K U, SubstEE__lc_rec d (open_te_record_rec K U r) -> SubstEE__lc_rec d r :=
  match r with
  | rec_empty => fun d K U _ => I
  | rec_exp a e r =>
      fun d K U H =>
        conj (SubstEE__lc_exp_open_te_inv e d K U (proj1 H))
             (SubstEE__lc_rec_open_te_inv r d K U (proj2 H))
  | rec_ref a l r =>
      fun d K U H => SubstEE__lc_rec_open_te_inv r d K U H
  end.

Lemma SubstEE__lc_exp_open_te_inv_apply : forall e d (x : atom),
  SubstEE__lc_exp d (open_te e (typ_fvar x)) -> SubstEE__lc_exp d e.
Proof. intros e d x H. unfold open_te in H. apply (SubstEE__lc_exp_open_te_inv e d 0 (typ_fvar x)). exact H. Qed.

Lemma SubstEE__lc_exp_open_inv_bvar : forall d j i x,
  SubstEE__lc_exp d (open_ee_rec j (exp_fvar x) (exp_bvar i)) ->
  i < max d (S j).
Proof.
  intros d j i x H. simpl in H.
  destruct (j == i) as [Heq|Hneq].
  - subst i. apply Nat.lt_le_trans with (S j).
    + apply Nat.lt_succ_diag_r.
    + apply Nat.le_max_r.
  - apply Nat.lt_le_trans with d.
    + simpl in H. exact H.
    + apply Nat.le_max_l.
Qed.

Fixpoint SubstEE__lc_exp_open_inv (e : exp) {struct e} :
  forall d j x,
    SubstEE__lc_exp d (open_ee_rec j (exp_fvar x) e) -> SubstEE__lc_exp (max d (S j)) e :=
  match e with
  | exp_bvar i =>
      fun d j x H => SubstEE__lc_exp_open_inv_bvar d j i x H
  | exp_fvar _ => fun d j x _ => I
  | exp_abs V e1 =>
      fun d j x H =>
        SubstEE__lc_exp_bound_eq e1 (max (S d) (S (S j))) (S (max d (S j)))
          (SubstEE__max_succ_succ_aux d j)
          (SubstEE__lc_exp_open_inv e1 (S d) (S j) x H)
  | exp_app e1 e2 =>
      fun d j x H =>
        conj (SubstEE__lc_exp_open_inv e1 d j x (proj1 H))
             (SubstEE__lc_exp_open_inv e2 d j x (proj2 H))
  | exp_tabs V e1 =>
      fun d j x H => SubstEE__lc_exp_open_inv e1 d j x H
  | exp_tapp e1 V =>
      fun d j x H => SubstEE__lc_exp_open_inv e1 d j x H
  | exp_let e1 e2 =>
      fun d j x H =>
        conj (SubstEE__lc_exp_open_inv e1 d j x (proj1 H))
             (SubstEE__lc_exp_bound_eq e2 (max (S d) (S (S j))) (S (max d (S j)))
                (SubstEE__max_succ_succ_aux d j)
                (SubstEE__lc_exp_open_inv e2 (S d) (S j) x (proj2 H)))
  | exp_box e1 =>
      fun d j x H => SubstEE__lc_exp_open_inv e1 d j x H
  | exp_unbox e1 =>
      fun d j x H => SubstEE__lc_exp_open_inv e1 d j x H
  | exp_set_box e1 e2 =>
      fun d j x H =>
        conj (SubstEE__lc_exp_open_inv e1 d j x (proj1 H))
             (SubstEE__lc_exp_open_inv e2 d j x (proj2 H))
  | exp_ref l => fun d j x _ => I
  | exp_seal e1 =>
      fun d j x H => SubstEE__lc_exp_open_inv e1 d j x H
  | exp_record r =>
      fun d j x H => SubstEE__lc_rec_open_inv r d j x H
  | exp_record_read e1 a =>
      fun d j x H => SubstEE__lc_exp_open_inv e1 d j x H
  | exp_record_write e1 a e2 =>
      fun d j x H =>
        conj (SubstEE__lc_exp_open_inv e1 d j x (proj1 H))
             (SubstEE__lc_exp_open_inv e2 d j x (proj2 H))
  end
with SubstEE__lc_rec_open_inv (r : rec_comp) {struct r} :
  forall d j x,
    SubstEE__lc_rec d (open_ee_record_rec j (exp_fvar x) r) -> SubstEE__lc_rec (max d (S j)) r :=
  match r with
  | rec_empty => fun d j x _ => I
  | rec_exp a e r =>
      fun d j x H =>
        conj (SubstEE__lc_exp_open_inv e d j x (proj1 H))
             (SubstEE__lc_rec_open_inv r d j x (proj2 H))
  | rec_ref a l r =>
      fun d j x H => SubstEE__lc_rec_open_inv r d j x H
  end.

Lemma SubstEE__lc_exp_open_inv_apply : forall e (x : atom),
  SubstEE__lc_exp 0 (open_ee e (exp_fvar x)) -> SubstEE__lc_exp 1 e.
Proof.
  intros e x H. unfold open_ee in H.
  exact (SubstEE__lc_exp_open_inv e 0 0 x H).
Qed.

(* ================================================================ *)
(* 4. Type-level closure under opening by a type variable           *)
(* ================================================================ *)

Lemma SubstEE__lc_at_bound_eq : forall (T : typ) d d',
  d = d' -> SubstTT__lc_at d T -> SubstTT__lc_at d' T.
Proof. intros T d d' Heq H. subst. exact H. Qed.

Lemma SubstEE__lc_at_open_fvar_inv : forall (T : typ) d j X,
  SubstTT__lc_at d (open_tt_rec j (typ_fvar X) T) -> SubstTT__lc_at (max d (S j)) T.
Proof.
  induction T; intros d j X H; simpl in *.
  - exact I.
  - destruct (j == n) as [Heq|Hneq].
    + subst n. apply Nat.lt_le_trans with (S j).
      * apply Nat.lt_succ_diag_r.
      * apply Nat.le_max_r.
    + apply Nat.lt_le_trans with d.
      * exact H.
      * apply Nat.le_max_l.
  - exact I.
  - destruct H as [H1 H2]. split.
    + apply (IHT1 d j X H1).
    + apply (IHT2 d j X H2).
  - destruct H as [H1 H2]. split.
    + apply (IHT1 d j X H1).
    + apply (SubstEE__lc_at_bound_eq T2 (max (S d) (S (S j))) (S (max d (S j)))
             (SubstEE__max_succ_succ_aux d j) (IHT2 (S d) (S j) X H2)).
  - apply (IHT d j X H).
  - apply (IHT d j X H).
  - destruct H as [H1 H2]. split.
    + apply (IHT1 d j X H1).
    + apply (IHT2 d j X H2).
  - apply (IHT d j X H).
Qed.

(* ================================================================ *)
(* 5. Closure of all type annotations in a term                     *)
(* ================================================================ *)

Fixpoint SubstEE__annot_lc (d : nat) (e : exp) {struct e} : Prop :=
  match e with
  | exp_bvar _ => True
  | exp_fvar _ => True
  | exp_abs V e1 => SubstTT__lc_at d V /\ SubstEE__annot_lc d e1
  | exp_app e1 e2 => SubstEE__annot_lc d e1 /\ SubstEE__annot_lc d e2
  | exp_tabs V e1 => SubstTT__lc_at d V /\ SubstEE__annot_lc (S d) e1
  | exp_tapp e1 V => SubstEE__annot_lc d e1 /\ SubstTT__lc_at d V
  | exp_let e1 e2 => SubstEE__annot_lc d e1 /\ SubstEE__annot_lc d e2
  | exp_box e1 => SubstEE__annot_lc d e1
  | exp_unbox e1 => SubstEE__annot_lc d e1
  | exp_set_box e1 e2 => SubstEE__annot_lc d e1 /\ SubstEE__annot_lc d e2
  | exp_ref _ => True
  | exp_seal e1 => SubstEE__annot_lc d e1
  | exp_record r => SubstEE__annot_rec d r
  | exp_record_read e1 _ => SubstEE__annot_lc d e1
  | exp_record_write e1 _ e2 => SubstEE__annot_lc d e1 /\ SubstEE__annot_lc d e2
  end
with SubstEE__annot_rec (d : nat) (r : rec_comp) {struct r} : Prop :=
  match r with
  | rec_empty => True
  | rec_exp _ e r => SubstEE__annot_lc d e /\ SubstEE__annot_rec d r
  | rec_ref _ _ r => SubstEE__annot_rec d r
  end.

Lemma SubstEE__annot_lc_bound_eq : forall e d d',
  d = d' -> SubstEE__annot_lc d e -> SubstEE__annot_lc d' e.
Proof. intros e d d' Heq H. subst. exact H. Qed.

Lemma SubstEE__annot_rec_bound_eq : forall r d d',
  d = d' -> SubstEE__annot_rec d r -> SubstEE__annot_rec d' r.
Proof. intros r d d' Heq H. subst. exact H. Qed.

Fixpoint SubstEE__annot_lc_open_te_inv (e : exp) {struct e} :
  forall d j X,
    SubstEE__annot_lc d (open_te_rec j (typ_fvar X) e) ->
    SubstEE__annot_lc (max d (S j)) e :=
  match e with
  | exp_bvar _ => fun d j X _ => I
  | exp_fvar _ => fun d j X _ => I
  | exp_abs V e1 =>
      fun d j X H =>
        conj (SubstEE__lc_at_open_fvar_inv V d j X (proj1 H))
             (SubstEE__annot_lc_open_te_inv e1 d j X (proj2 H))
  | exp_app e1 e2 =>
      fun d j X H =>
        conj (SubstEE__annot_lc_open_te_inv e1 d j X (proj1 H))
             (SubstEE__annot_lc_open_te_inv e2 d j X (proj2 H))
  | exp_tabs V e1 =>
      fun d j X H =>
        conj (SubstEE__lc_at_open_fvar_inv V d j X (proj1 H))
             (SubstEE__annot_lc_bound_eq e1 (max (S d) (S (S j))) (S (max d (S j)))
                (SubstEE__max_succ_succ_aux d j)
                (SubstEE__annot_lc_open_te_inv e1 (S d) (S j) X (proj2 H)))
  | exp_tapp e1 V =>
      fun d j X H =>
        conj (SubstEE__annot_lc_open_te_inv e1 d j X (proj1 H))
             (SubstEE__lc_at_open_fvar_inv V d j X (proj2 H))
  | exp_let e1 e2 =>
      fun d j X H =>
        conj (SubstEE__annot_lc_open_te_inv e1 d j X (proj1 H))
             (SubstEE__annot_lc_open_te_inv e2 d j X (proj2 H))
  | exp_box e1 =>
      fun d j X H => SubstEE__annot_lc_open_te_inv e1 d j X H
  | exp_unbox e1 =>
      fun d j X H => SubstEE__annot_lc_open_te_inv e1 d j X H
  | exp_set_box e1 e2 =>
      fun d j X H =>
        conj (SubstEE__annot_lc_open_te_inv e1 d j X (proj1 H))
             (SubstEE__annot_lc_open_te_inv e2 d j X (proj2 H))
  | exp_ref _ => fun d j X _ => I
  | exp_seal e1 =>
      fun d j X H => SubstEE__annot_lc_open_te_inv e1 d j X H
  | exp_record r =>
      fun d j X H => SubstEE__annot_rec_open_te_inv r d j X H
  | exp_record_read e1 a =>
      fun d j X H => SubstEE__annot_lc_open_te_inv e1 d j X H
  | exp_record_write e1 a e2 =>
      fun d j X H =>
        conj (SubstEE__annot_lc_open_te_inv e1 d j X (proj1 H))
             (SubstEE__annot_lc_open_te_inv e2 d j X (proj2 H))
  end
with SubstEE__annot_rec_open_te_inv (r : rec_comp) {struct r} :
  forall d j X,
    SubstEE__annot_rec d (open_te_record_rec j (typ_fvar X) r) ->
    SubstEE__annot_rec (max d (S j)) r :=
  match r with
  | rec_empty => fun d j X _ => I
  | rec_exp a e r =>
      fun d j X H =>
        conj (SubstEE__annot_lc_open_te_inv e d j X (proj1 H))
             (SubstEE__annot_rec_open_te_inv r d j X (proj2 H))
  | rec_ref a l r =>
      fun d j X H => SubstEE__annot_rec_open_te_inv r d j X H
  end.

Fixpoint SubstEE__annot_lc_open_te_id (e : exp) {struct e} :
  forall d K X,
    SubstEE__annot_lc d e -> d <= K -> open_te_rec K (typ_fvar X) e = e :=
  match e with
  | exp_bvar _ => fun d K X _ _ => eq_refl
  | exp_fvar _ => fun d K X _ _ => eq_refl
  | exp_abs V e1 =>
      fun d K X H HK =>
        f_equal2 exp_abs
          (SubstTT__lc_at_open_id V d (proj1 H) K (typ_fvar X) HK)
          (SubstEE__annot_lc_open_te_id e1 d K X (proj2 H) HK)
  | exp_app e1 e2 =>
      fun d K X H HK =>
        f_equal2 exp_app
          (SubstEE__annot_lc_open_te_id e1 d K X (proj1 H) HK)
          (SubstEE__annot_lc_open_te_id e2 d K X (proj2 H) HK)
  | exp_tabs V e1 =>
      fun d K X H HK =>
        f_equal2 exp_tabs
          (SubstTT__lc_at_open_id V d (proj1 H) K (typ_fvar X) HK)
          (SubstEE__annot_lc_open_te_id e1 (S d) (S K) X (proj2 H) (le_n_S d K HK))
  | exp_tapp e1 V =>
      fun d K X H HK =>
        f_equal2 exp_tapp
          (SubstEE__annot_lc_open_te_id e1 d K X (proj1 H) HK)
          (SubstTT__lc_at_open_id V d (proj2 H) K (typ_fvar X) HK)
  | exp_let e1 e2 =>
      fun d K X H HK =>
        f_equal2 exp_let
          (SubstEE__annot_lc_open_te_id e1 d K X (proj1 H) HK)
          (SubstEE__annot_lc_open_te_id e2 d K X (proj2 H) HK)
  | exp_box e1 =>
      fun d K X H HK => f_equal exp_box (SubstEE__annot_lc_open_te_id e1 d K X H HK)
  | exp_unbox e1 =>
      fun d K X H HK => f_equal exp_unbox (SubstEE__annot_lc_open_te_id e1 d K X H HK)
  | exp_set_box e1 e2 =>
      fun d K X H HK =>
        f_equal2 exp_set_box
          (SubstEE__annot_lc_open_te_id e1 d K X (proj1 H) HK)
          (SubstEE__annot_lc_open_te_id e2 d K X (proj2 H) HK)
  | exp_ref _ => fun d K X _ _ => eq_refl
  | exp_seal e1 =>
      fun d K X H HK => f_equal exp_seal (SubstEE__annot_lc_open_te_id e1 d K X H HK)
  | exp_record r =>
      fun d K X H HK => f_equal exp_record (SubstEE__annot_rec_open_te_id r d K X H HK)
  | exp_record_read e1 a =>
      fun d K X H HK =>
        f_equal (fun z => exp_record_read z a)
          (SubstEE__annot_lc_open_te_id e1 d K X H HK)
  | exp_record_write e1 a e2 =>
      fun d K X H HK =>
        f_equal2 (fun z z' => exp_record_write z a z')
          (SubstEE__annot_lc_open_te_id e1 d K X (proj1 H) HK)
          (SubstEE__annot_lc_open_te_id e2 d K X (proj2 H) HK)
  end
with SubstEE__annot_rec_open_te_id (r : rec_comp) {struct r} :
  forall d K X,
    SubstEE__annot_rec d r -> d <= K -> open_te_record_rec K (typ_fvar X) r = r :=
  match r with
  | rec_empty => fun d K X _ _ => eq_refl
  | rec_exp a e r =>
      fun d K X H HK =>
        f_equal2 (fun z z' => rec_exp a z z')
          (SubstEE__annot_lc_open_te_id e d K X (proj1 H) HK)
          (SubstEE__annot_rec_open_te_id r d K X (proj2 H) HK)
  | rec_ref a l r =>
      fun d K X H HK =>
        f_equal (fun z => rec_ref a l z)
          (SubstEE__annot_rec_open_te_id r d K X H HK)
  end.

Lemma SubstEE__annot_lc_closed_open_te : forall v,
  SubstEE__annot_lc 0 v -> forall K X, open_te_rec K (typ_fvar X) v = v.
Proof.
  intros v H K X. apply (SubstEE__annot_lc_open_te_id v 0 K X H). apply Nat.le_0_l.
Qed.

Lemma SubstEE__annot_rec_closed_open_te : forall r,
  SubstEE__annot_rec 0 r -> forall K X, open_te_record_rec K (typ_fvar X) r = r.
Proof.
  intros r H K X. apply (SubstEE__annot_rec_open_te_id r 0 K X H). apply Nat.le_0_l.
Qed.

Fixpoint SubstEE__annot_lc_open_ee_inv (e : exp) {struct e} :
  forall d j x,
    SubstEE__annot_lc d (open_ee_rec j (exp_fvar x) e) -> SubstEE__annot_lc d e :=
  match e with
  | exp_bvar _ => fun d j x _ => I
  | exp_fvar _ => fun d j x H => H
  | exp_abs V e1 =>
      fun d j x H =>
        conj (proj1 H) (SubstEE__annot_lc_open_ee_inv e1 d (S j) x (proj2 H))
  | exp_app e1 e2 =>
      fun d j x H =>
        conj (SubstEE__annot_lc_open_ee_inv e1 d j x (proj1 H))
             (SubstEE__annot_lc_open_ee_inv e2 d j x (proj2 H))
  | exp_tabs V e1 =>
      fun d j x H =>
        conj (proj1 H) (SubstEE__annot_lc_open_ee_inv e1 (S d) j x (proj2 H))
  | exp_tapp e1 V =>
      fun d j x H =>
        conj (SubstEE__annot_lc_open_ee_inv e1 d j x (proj1 H)) (proj2 H)
  | exp_let e1 e2 =>
      fun d j x H =>
        conj (SubstEE__annot_lc_open_ee_inv e1 d j x (proj1 H))
             (SubstEE__annot_lc_open_ee_inv e2 d (S j) x (proj2 H))
  | exp_box e1 =>
      fun d j x H => SubstEE__annot_lc_open_ee_inv e1 d j x H
  | exp_unbox e1 =>
      fun d j x H => SubstEE__annot_lc_open_ee_inv e1 d j x H
  | exp_set_box e1 e2 =>
      fun d j x H =>
        conj (SubstEE__annot_lc_open_ee_inv e1 d j x (proj1 H))
             (SubstEE__annot_lc_open_ee_inv e2 d j x (proj2 H))
  | exp_ref _ => fun d j x _ => I
  | exp_seal e1 =>
      fun d j x H => SubstEE__annot_lc_open_ee_inv e1 d j x H
  | exp_record r =>
      fun d j x H => SubstEE__annot_rec_open_ee_inv r d j x H
  | exp_record_read e1 a =>
      fun d j x H => SubstEE__annot_lc_open_ee_inv e1 d j x H
  | exp_record_write e1 a e2 =>
      fun d j x H =>
        conj (SubstEE__annot_lc_open_ee_inv e1 d j x (proj1 H))
             (SubstEE__annot_lc_open_ee_inv e2 d j x (proj2 H))
  end
with SubstEE__annot_rec_open_ee_inv (r : rec_comp) {struct r} :
  forall d j x,
    SubstEE__annot_rec d (open_ee_record_rec j (exp_fvar x) r) -> SubstEE__annot_rec d r :=
  match r with
  | rec_empty => fun d j x _ => I
  | rec_exp a e r =>
      fun d j x H =>
        conj (SubstEE__annot_lc_open_ee_inv e d j x (proj1 H))
             (SubstEE__annot_rec_open_ee_inv r d j x (proj2 H))
  | rec_ref a l r =>
      fun d j x H => SubstEE__annot_rec_open_ee_inv r d j x H
  end.

(* ================================================================ *)
(* 6. Typed terms are locally closed and their annotations are      *)
(*    locally closed as well.                                       *)
(* ================================================================ *)

Definition SubstEE__typing_lc_annot_P (E : env) (R : sig) (e : exp) (T : typ)
    (_ : typing E R e T) : Prop := SubstEE__lc_exp 0 e /\ SubstEE__annot_lc 0 e.

Definition SubstEE__typing_lc_annot_Q (E : env) (R : sig) (r : rec_comp) (T : typ)
    (_ : typing_record_comp E R r T) : Prop := SubstEE__lc_rec 0 r /\ SubstEE__annot_rec 0 r.

Lemma SubstEE__typing_lc_annot : forall (E : env) (R : sig) e T,
  typing E R e T -> SubstEE__lc_exp 0 e /\ SubstEE__annot_lc 0 e.
Proof.
  - intros E0 R0 e0 T0 H0. change (SubstEE__typing_lc_annot_P E0 R0 e0 T0 H0).
    apply (SubstEE__typing_induction SubstEE__typing_lc_annot_P SubstEE__typing_lc_annot_Q).
    + (* var *) intros E R x T w w0 b. simpl. split; exact I.
    + (* abs *) intros L E R V e1 T1 w Hbody IHbody.
      destruct (atom_fresh (L `union` dom E)) as [x Hx].
      apply notin_union_1 in Hx as HxL.
      apply notin_union_2 in Hx as HxE.
      pose proof (Hbody x HxL) as Hbodyx.
      pose proof (IHbody x HxL) as IHx.
      assert (Hws : wf_sig (x ~ bind_typ V ++ E) R)
        by (apply (SubstTT__typing_wf_sig (x ~ bind_typ V ++ E) R (open_ee e1 (exp_fvar x)) T1); exact Hbodyx).
      assert (Hwe : wf_env (x ~ bind_typ V ++ E)) by (apply (Dev__wf_sig_wf_env (x ~ bind_typ V ++ E) R); exact Hws).
      assert (HwV : wf_typ E V) by (apply (proj2 (Dev__wf_env_cons_bind_typ E x V Hwe))).
      assert (HlcV : SubstTT__lc_at 0 V) by (apply (SubstTT__wf_typ_lc E V); exact HwV).
      assert (Hlc1 : SubstEE__lc_exp 1 e1).
      { apply (SubstEE__lc_exp_open_inv_apply e1 x). exact (proj1 IHx). }
      assert (Hann1 : SubstEE__annot_lc 0 e1).
      { apply (SubstEE__annot_lc_open_ee_inv e1 0 0 x). exact (proj2 IHx). }
      simpl. split; [exact Hlc1 | split; [exact HlcV | exact Hann1]].
    + (* app *) intros T1 E R e1 e2 T2 w H1 IH1 H2 IH2.
      simpl. split; split.
      * exact (proj1 IH1).
      * exact (proj1 IH2).
      * exact (proj2 IH1).
      * exact (proj2 IH2).
    + (* tabs *) intros L E R V e1 T1 w Hbody IHbody.
      destruct (atom_fresh (L `union` dom E)) as [X HX].
      apply notin_union_1 in HX as HXL.
      apply notin_union_2 in HX as HXE.
      pose proof (Hbody X HXL) as HbodyX.
      pose proof (IHbody X HXL) as IHX.
      assert (Hws : wf_sig (X ~ bind_sub V ++ E) R)
        by (apply (SubstTT__typing_wf_sig (X ~ bind_sub V ++ E) R (open_te e1 (typ_fvar X)) (open_tt T1 (typ_fvar X))); exact HbodyX).
      assert (Hwe : wf_env (X ~ bind_sub V ++ E)) by (apply (Dev__wf_sig_wf_env (X ~ bind_sub V ++ E) R); exact Hws).
      assert (HwV : wf_typ E V) by (apply (proj2 (Dev__wf_env_cons_bind_sub E X V Hwe))).
      assert (HlcV : SubstTT__lc_at 0 V) by (apply (SubstTT__wf_typ_lc E V); exact HwV).
      assert (Hlc0 : SubstEE__lc_exp 0 e1).
      { apply (SubstEE__lc_exp_open_te_inv_apply e1 0 X). exact (proj1 IHX). }
      assert (Hann1 : SubstEE__annot_lc 1 e1).
      { change (SubstEE__annot_lc (max 0 (S 0)) e1).
        apply (SubstEE__annot_lc_open_te_inv e1 0 0 X). exact (proj2 IHX). }
      simpl. split; [exact Hlc0 | split; [exact HlcV | exact Hann1]].
    + (* tapp *) intros T1 E R e1 T T2 w H1 IH1 Hsub.
      assert (Hwe : wf_env E) by (apply Dev__wf_sig_wf_env with (R := R); exact w).
      assert (Hwf_all : wf_typ E (typ_all T1 T2))
        by (apply (SubstTT__typing_wf_typ E R e1 (typ_all T1 T2)); exact H1).
      destruct (Dev__wf_typ_inv_all E T1 T2 Hwf_all) as [L [HwT1 _]].
      assert (HwT : wf_typ E T) by (apply (Dev__sub_wf_source E T T1 Hwe HwT1 Hsub)).
      assert (HlcT : SubstTT__lc_at 0 T) by (apply (SubstTT__wf_typ_lc E T); exact HwT).
      simpl. split; [exact (proj1 IH1) | split; [exact (proj2 IH1)|exact HlcT]].
    + (* sub *) intros S E R e T w H1 IH1 Hsub. exact IH1.
    + (* let *) intros L T1 T2 e1 e2 E R w H1 IH1 Hbody IHbody.
      destruct (atom_fresh (L `union` dom E)) as [x Hx].
      apply notin_union_1 in Hx as HxL.
      pose proof (IHbody x HxL) as IHx.
      assert (Hlc2 : SubstEE__lc_exp 1 e2).
      { apply (SubstEE__lc_exp_open_inv_apply e2 x). exact (proj1 IHx). }
      assert (Hann2 : SubstEE__annot_lc 0 e2).
      { apply (SubstEE__annot_lc_open_ee_inv e2 0 0 x). exact (proj2 IHx). }
      simpl. split; [split; [exact (proj1 IH1)|exact Hlc2] |
                     split; [exact (proj2 IH1)|exact Hann2]].
    + (* box *) intros E R e T w H1 IH1. exact IH1.
    + (* unbox *) intros E R e T w H1 IH1. exact IH1.
    + (* set_box *) intros E R e1 e2 T w H1 IH1 H2 IH2.
      simpl. split; split.
      * exact (proj1 IH1).
      * exact (proj1 IH2).
      * exact (proj2 IH1).
      * exact (proj2 IH2).
    + (* ref *) intros E R l T w w0 b. simpl. split; exact I.
    + (* seal *) intros E R e T H1 IH1. exact IH1.
    + (* unbox_readonly *) intros E R e T H1 IH1. exact IH1.
    + (* record *) intros E R r T Hr IHr. simpl. exact IHr.
    + (* record_read *) intros E R e a T H1 IH1. exact IH1.
    + (* record_read_readonly *) intros E R e a T H1 IH1. exact IH1.
    + (* record_write *) intros E R e1 a e2 T H1 IH1 H2 IH2.
      simpl. split; split.
      * exact (proj1 IH1).
      * exact (proj1 IH2).
      * exact (proj2 IH1).
      * exact (proj2 IH2).
    + (* record_empty *) intros E R w w0. simpl. split; exact I.
    + (* record_exp *) intros E R a e r T Tr Hnd Hr IHr He IHe.
      simpl. split; split.
      * exact (proj1 IHe).
      * exact (proj1 IHr).
      * exact (proj2 IHe).
      * exact (proj2 IHr).
    + (* record_ref *) intros E R a l r T Tr Hnd Hr IHr b. exact IHr.
Qed.

Lemma SubstEE__typing_record_comp_lc_annot : forall (E : env) (R : sig) r T,
  typing_record_comp E R r T -> SubstEE__lc_rec 0 r /\ SubstEE__annot_rec 0 r.
Proof.
  intros E R r T Htr.
  induction Htr as
      [ E0 R0 w w0
      | E0 R0 a e r T Tr Hnd Hr IHr He
      | E0 R0 a l r T Tr Hnd Hr IHr b ].
  + simpl. split; exact I.
  + simpl. split; split.
    * exact (proj1 (SubstEE__typing_lc_annot E0 R0 e T He)).
    * exact (proj1 IHr).
    * exact (proj2 (SubstEE__typing_lc_annot E0 R0 e T He)).
    * exact (proj2 IHr).
  + exact IHr.
Qed.

(* ================= appended from ScratchEnv.v ================= *)
Lemma SubstEE__in_dom_app_iff : forall (E F : env) x,
  x `in` dom (E ++ F) <-> x `in` dom E \/ x `in` dom F.
Proof.
  induction E as [| [y b] E IH]; intros F x; simpl.
  - split; intros H; [right; assumption|].
    destruct H as [H0|H0]; [apply empty_iff in H0; destruct H0|assumption].
  - simpl. repeat rewrite add_iff. rewrite IH. tauto.
Qed.

Lemma SubstEE__notin_dom_app : forall (E F : env) x,
  x `notin` dom (E ++ F) -> x `notin` dom E /\ x `notin` dom F.
Proof.
  intros E F x H. split; intro Hx.
  - apply H. apply SubstEE__in_dom_app_iff. left. assumption.
  - apply H. apply SubstEE__in_dom_app_iff. right. assumption.
Qed.

Lemma SubstEE__in_dom_app_1 : forall (E F : env) x,
  x `in` dom E -> x `in` dom (E ++ F).
Proof. intros. apply SubstEE__in_dom_app_iff. left. assumption. Qed.
Lemma SubstEE__in_dom_app_2 : forall (E F : env) x,
  x `in` dom F -> x `in` dom (E ++ F).
Proof. intros. apply SubstEE__in_dom_app_iff. right. assumption. Qed.

Definition SubstEE__env_incl (E E' : env) : Prop :=
  forall x b, binds x b E -> binds x b E'.

Lemma SubstEE__env_incl_refl : forall E, SubstEE__env_incl E E.
Proof. intros E x b H. assumption. Qed.

Lemma SubstEE__env_incl_trans : forall E1 E2 E3,
  SubstEE__env_incl E1 E2 -> SubstEE__env_incl E2 E3 -> SubstEE__env_incl E1 E3.
Proof. intros E1 E2 E3 H12 H23 x b H. apply H23. apply H12. assumption. Qed.

Lemma SubstEE__env_incl_cons : forall (E E' : env) x b,
  SubstEE__env_incl E E' -> SubstEE__env_incl ((x,b)::E) ((x,b)::E').
Proof.
  intros E E' x b H y c Hy. simpl in Hy. destruct Hy as [Heq|Hin].
  - left. assumption.
  - right. apply H. assumption.
Qed.

Lemma SubstEE__env_incl_app_same : forall (P : env) E E',
  SubstEE__env_incl E E' -> SubstEE__env_incl (P ++ E) (P ++ E').
Proof.
  intros P. induction P as [| [y c] P IH]; intros E E' H.
  - simpl. assumption.
  - simpl. apply SubstEE__env_incl_cons. apply IH. assumption.
Qed.

Lemma SubstEE__env_incl_app_left : forall (P E : env),
  SubstEE__env_incl P (P ++ E).
Proof.
  intros P E x b H. exact (Dev__binds_app_1 P E x b H).
Qed.

Lemma SubstEE__binds_subst_mid_typ_neq : forall (P E : env) x V Y b,
  Y <> x -> binds Y b (P ++ (x, bind_typ V) :: E) -> binds Y b (P ++ E).
Proof.
  induction P as [| [z c] P IH]; intros E x V Y b Hneq Hb; simpl in *.
  - destruct Hb as [Heq|Hin].
    + inversion Heq. subst. exfalso. apply Hneq. reflexivity.
    + assumption.
  - destruct Hb as [Heq|Hin].
    + left. assumption.
    + right. eapply IH; eauto.
Qed.

Lemma SubstEE__binds_sub_remove_mid_typ : forall (P E : env) x V Y U,
  binds Y (bind_sub U) (P ++ (x, bind_typ V) :: E) ->
  binds Y (bind_sub U) (P ++ E).
Proof.
  induction P as [| [z c] P IH]; intros E x V Y U Hb; simpl in *.
  - destruct Hb as [Heq|Hin].
    + inversion Heq.
    + assumption.
  - destruct Hb as [Heq|Hin].
    + left. assumption.
    + right. eapply IH; eauto.
Qed.

Lemma SubstEE__in_dom_remove_mid_typ_mono : forall (P E : env) x V Y,
  Y `in` dom (P ++ E) -> Y `in` dom (P ++ (x, bind_typ V) :: E).
Proof.
  induction P as [| [z c] P IH]; intros E x V Y Hin; simpl in *.
  - apply add_iff. right. assumption.
  - apply add_iff in Hin. apply add_iff.
    destruct Hin as [Heq|Hin]; [left|right]; auto.
Qed.

Lemma SubstEE__notin_dom_remove_mid_typ_gen : forall (P E : env) x V Y,
  Y `notin` dom (P ++ (x, bind_typ V) :: E) -> Y `notin` dom (P ++ E).
Proof.
  intros. intro Hin. apply H. apply SubstEE__in_dom_remove_mid_typ_mono. assumption.
Qed.

Lemma SubstEE__wf_env_head_notin : forall (E : env) y b,
  wf_env ((y,b)::E) -> y `notin` dom E.
Proof. intros E y b H. inversion H; subst; assumption. Qed.

Lemma SubstEE__wf_env_remove_mid_typ_gen : forall (P E : env) x V,
  wf_env (P ++ (x, bind_typ V) :: E) -> wf_env (P ++ E).
Proof.
  induction P as [| [z c] P IH]; intros E x V H; simpl in *.
  - inversion H; subst. assumption.
  - destruct c as [T|T]; simpl in *.
    + inversion H as [| E0 X U Hwe Hwt Hnotin | E0 y U Hwe Hwt Hnotin]; subst.
      assert (Hwe' : wf_env (P ++ E)) by (apply (IH E x V); assumption).
      assert (Hwt' : wf_typ (P ++ E) T).
      { eapply SubstTT__wf_typ_incl; [exact Hwt|].
        intros Y U Hb. eapply SubstEE__binds_sub_remove_mid_typ. exact Hb. }
      assert (Hnotin' : z `notin` dom (P ++ E)).
      { eapply SubstEE__notin_dom_remove_mid_typ_gen. exact Hnotin. }
      apply (wf_env_sub (P ++ E) z T); assumption.
    + inversion H as [| E0 X U Hwe Hwt Hnotin | E0 y U Hwe Hwt Hnotin]; subst.
      assert (Hwe' : wf_env (P ++ E)) by (apply (IH E x V); assumption).
      assert (Hwt' : wf_typ (P ++ E) T).
      { eapply SubstTT__wf_typ_incl; [exact Hwt|].
        intros Y U Hb. eapply SubstEE__binds_sub_remove_mid_typ. exact Hb. }
      assert (Hnotin' : z `notin` dom (P ++ E)).
      { eapply SubstEE__notin_dom_remove_mid_typ_gen. exact Hnotin. }
      apply (wf_env_typ (P ++ E) z T); assumption.
Qed.

Lemma SubstEE__wf_env_binds_unique : forall (E : env), wf_env E ->
  forall x b1 b2, binds x b1 E -> binds x b2 E -> b1 = b2.
Proof.
  intros E H.
  induction H as [| E0 X T Hwe IHH Hwt Hnotin | E0 y T Hwe IHH Hwt Hnotin];
    intros z c1 c2 Hz1 Hz2.
  - inversion Hz1.
  - simpl in *. destruct Hz1 as [Heq1|Hin1]; destruct Hz2 as [Heq2|Hin2].
    + inversion Heq1. inversion Heq2. reflexivity.
    + inversion Heq1. subst. exfalso. apply Hnotin.
      apply (Dev__in_dom_binds E0 z c2). assumption.
    + inversion Heq2. subst. exfalso. apply Hnotin.
      apply (Dev__in_dom_binds E0 z c1). assumption.
    + apply (IHH z c1 c2); assumption.
  - simpl in *. destruct Hz1 as [Heq1|Hin1]; destruct Hz2 as [Heq2|Hin2].
    + inversion Heq1. inversion Heq2. reflexivity.
    + inversion Heq1. subst. exfalso. apply Hnotin.
      apply (Dev__in_dom_binds E0 z c2). assumption.
    + inversion Heq2. subst. exfalso. apply Hnotin.
      apply (Dev__in_dom_binds E0 z c1). assumption.
    + apply (IHH z c1 c2); assumption.
Qed.

(* ================= appended from ScratchSub.v ================= *)
Lemma SubstEE__wf_sig_incl : forall (E E' : env) (R : sig),
  wf_env E' ->
  (forall X U, binds X (bind_sub U) E -> binds X (bind_sub U) E') ->
  wf_sig E R -> wf_sig E' R.
Proof.
  intros E E' R Hwe Hincl Hs.
  induction Hs as [E0 Hwe0 | E0 R0 l T Hws IHH Hwt Hnotin].
  - apply wf_sig_empty. assumption.
  - apply (wf_sig_typ E' R0 l T); [apply (IHH Hincl) | | exact Hnotin].
    eapply SubstTT__wf_typ_incl; [exact Hwt | exact Hincl].
Qed.

Lemma SubstEE__sub_weaken_bindsub : forall (E1 : env) S T,
  wf_env E1 -> wf_typ E1 S -> sub E1 S T ->
  forall (E2 : env), wf_env E2 ->
  (forall X U, binds X (bind_sub U) E1 -> binds X (bind_sub U) E2) ->
  sub E2 S T.
Proof.
  intros E1 S T HE1 HS1 Hsub.
  revert HE1 HS1.
  induction Hsub as [ E1 S HE0 HS0
                 | E1 X HE0 HS0
                 | U E1 T0 X Hb Hsub IHsub
                 | E1 S1 S2 T1 T2 H1 IH1 H2 IH2
                 | L0 E1 S1 S2 T1 T2 H1 IH1 H0 IH0
                 | E1 T1 T2 H1 IH1 H2 IH2
                 | E1 T1 T2 H1 IH1
                 | E1 T1 T2 H1 IH1
                 | E1 T1 T2 T3 H1 IH1 H2 IH2
                 | E1 T1 T2 HEi1 HSi1 HSi2
                 | E1 T1 T2 HEi2 HSi2b HSi2c
                 | E1 T1 T2 T3 H1 IH1 H2 IH2
                 | E1 a T1 T2 H1 IH1 H2 IH2
                 | E1 a T1 T2 H1 IH1
                 | E1 T1 T2 HSd1 HSd2 Hsub IHsub ];
    intros HE1 HS1 E2 HE2 Hincl.
  - apply sub_top; [assumption |].
    apply (SubstTT__wf_typ_incl E1 S HS1 E2). assumption.
  - apply sub_refl_tvar; [assumption |].
    apply (SubstTT__wf_typ_incl E1 (typ_fvar X) HS1 E2). assumption.
  - apply (sub_trans_tvar U E2 T0 X).
    + apply Hincl. assumption.
    + apply (IHsub HE1 (Dev__wf_env_binds_sub _ HE1 X U Hb) E2 HE2 Hincl).
  - destruct (Dev__wf_typ_inv_arrow _ _ _ HS1) as [HSa HSb].
    assert (HT1 : wf_typ E1 T1) by (apply (Dev__sub_wf_source E1 T1 S1 HE1 HSa H1)).
    apply sub_arrow.
    + apply (IH1 HE1 HT1 E2 HE2 Hincl).
    + apply (IH2 HE1 HSb E2 HE2 Hincl).
  - destruct (Dev__wf_typ_inv_all _ _ _ HS1) as [L1 [HSa HSb]].
    apply (sub_all (L0 `union` L1 `union` dom E1 `union` dom E2) E2 S1 S2 T1 T2).
    + assert (HT1 : wf_typ E1 T1) by (apply (Dev__sub_wf_source E1 T1 S1 HE1 HSa H1)).
      apply (IH1 HE1 HT1 E2 HE2 Hincl).
    + intros Y HY.
      assert (HYL0 : Y `notin` L0) by (apply notin_union_1 in HY; assumption).
      assert (HYL1 : Y `notin` L1) by (apply notin_union_2 in HY; apply notin_union_1 in HY; assumption).
      assert (HYd1 : Y `notin` dom E1)
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; apply notin_union_1 in HY; assumption).
      assert (HYd : Y `notin` dom E2)
        by (apply notin_union_2 in HY; apply notin_union_2 in HY; apply notin_union_2 in HY; assumption).
      assert (HT1s : wf_typ E1 T1) by (apply (Dev__sub_wf_source E1 T1 S1 HE1 HSa H1)).
      assert (HT1 : wf_typ E2 T1).
      { apply (SubstTT__wf_typ_incl E1 T1 HT1s E2). assumption. }
      assert (Hwe1 : wf_env (Y ~ bind_sub T1 ++ E1)).
      { apply (wf_env_sub E1 Y T1); [exact HE1 | exact HT1s | exact HYd1]. }
      assert (Hwe2 : wf_env (Y ~ bind_sub T1 ++ E2)).
      { apply (wf_env_sub E2 Y T1); [exact HE2 | exact HT1 | exact HYd]. }
      assert (HSbT : wf_typ (Y ~ bind_sub T1 ++ E1) (open_tt S2 Y)).
      { eapply Dev__wf_typ_kind. exact (HSb Y HYL1).
        intros Z. apply Dev__same_kinds_cons_sub_any. apply Dev__same_kinds_refl. }
      apply (IH0 Y HYL0 Hwe1 HSbT (Y ~ bind_sub T1 ++ E2) Hwe2).
      intros x b Hb.
      destruct Hb as [Heq | Hin].
      * left; assumption.
      * right. apply Hincl. assumption.
  - assert (HwT1 : wf_typ E1 T1) by (apply (Dev__wf_typ_inv_box _ _ HS1)).
    assert (HwT2 : wf_typ E1 T2).
    { apply (Dev__sub_wf_target E1 T1 T2 HE1 HwT1 H1). }
    apply sub_box.
    + apply (IH1 HE1 HwT1 E2 HE2 Hincl).
    + apply (IH2 HE1 HwT2 E2 HE2 Hincl).
  - apply sub_readonly. apply (IH1 HE1 (Dev__wf_typ_inv_readonly _ _ _ HS1) E2 HE2 Hincl).
  - apply sub_readonly_mutable. apply (IH1 HE1 HS1 E2 HE2 Hincl).
  - assert (HT2 : wf_typ E1 T2) by (apply (Dev__sub_wf_target E1 T1 T2 HE1 HS1 H1)).
    apply sub_trans with (T2 := T2).
    + apply (IH1 HE1 HS1 E2 HE2 Hincl).
    + apply (IH2 HE1 HT2 E2 HE2 Hincl).
  - apply (sub_inter_left E2 T1 T2); [assumption | |].
    + apply (SubstTT__wf_typ_incl E1 T1 HSi1 E2); assumption.
    + apply (SubstTT__wf_typ_incl E1 T2 HSi2 E2); assumption.
  - apply (sub_inter_right E2 T1 T2); [assumption | |].
    + apply (SubstTT__wf_typ_incl E1 T1 HSi2b E2); assumption.
    + apply (SubstTT__wf_typ_incl E1 T2 HSi2c E2); assumption.
  - apply sub_inter.
    + apply (IH1 HE1 HS1 E2 HE2 Hincl).
    + apply (IH2 HE1 HS1 E2 HE2 Hincl).
  - assert (HwT1 : wf_typ E1 T1) by (apply (Dev__wf_typ_inv_record _ _ _ HS1)).
    assert (HwT2 : wf_typ E1 T2) by (apply (Dev__sub_wf_target E1 T1 T2 HE1 HwT1 H1)).
    apply sub_record.
    + apply (IH1 HE1 HwT1 E2 HE2 Hincl).
    + apply (IH2 HE1 HwT2 E2 HE2 Hincl).
  - apply sub_readonly_record.
    apply (IH1 HE1 (Dev__wf_typ_inv_record _ _ _ (Dev__wf_typ_inv_readonly _ _ _ HS1)) E2 HE2 Hincl).
  - apply (sub_denormalize E2 T1 T2).
    + apply (SubstTT__wf_typ_incl E1 T1 HSd1 E2); assumption.
    + apply (SubstTT__wf_typ_incl E1 T2 HSd2 E2); assumption.
    + apply (IHsub HE1 (Dev__wf_typ_nf _ _ HSd1) E2 HE2 Hincl).
Qed.

(* ================= appended from ScratchEE.v ================= *)
(* ================================================================ *)
(* Commutation of term substitution with term opening                *)
(* ================================================================ *)

(* ---------------- lc-conditioned commutation ---------------- *)

Fixpoint SubstEE__subst_ee_open_ee_lc (e : exp) {struct e} :
  forall x v (k : nat) f,
    SubstEE__lc_exp 0 v ->
    SubstEE__subst_ee x v (open_ee_rec k f e) =
    open_ee_rec k (SubstEE__subst_ee x v f) (SubstEE__subst_ee x v e)
with SubstEE__subst_ee_rec_open_ee_lc (r : rec_comp) {struct r} :
  forall x v (k : nat) f,
    SubstEE__lc_exp 0 v ->
    SubstEE__subst_ee_rec_comp x v (open_ee_record_rec k f r) =
    open_ee_record_rec k (SubstEE__subst_ee x v f) (SubstEE__subst_ee_rec_comp x v r).
Proof.
  - destruct e; intros x v k f Hlc; simpl; try reflexivity.
    + destruct (k == n); reflexivity.
    + destruct (x === a) as [Heq|Hneq].
      * symmetry. apply (SubstEE__lc_exp_open_ee_apply v Hlc k (SubstEE__subst_ee x v f)).
      * reflexivity.
    + f_equal. apply SubstEE__subst_ee_open_ee_lc. exact Hlc.
    + f_equal; [apply SubstEE__subst_ee_open_ee_lc | apply SubstEE__subst_ee_open_ee_lc]; exact Hlc.
    + f_equal. apply SubstEE__subst_ee_open_ee_lc. exact Hlc.
    + f_equal; try reflexivity; apply SubstEE__subst_ee_open_ee_lc; exact Hlc.
    + f_equal; [apply SubstEE__subst_ee_open_ee_lc | apply SubstEE__subst_ee_open_ee_lc]; exact Hlc.
    + f_equal. apply SubstEE__subst_ee_open_ee_lc. exact Hlc.
    + f_equal. apply SubstEE__subst_ee_open_ee_lc. exact Hlc.
    + f_equal; [apply SubstEE__subst_ee_open_ee_lc | apply SubstEE__subst_ee_open_ee_lc]; exact Hlc.
    + f_equal. apply SubstEE__subst_ee_open_ee_lc. exact Hlc.
    + f_equal. apply SubstEE__subst_ee_rec_open_ee_lc. exact Hlc.
    + f_equal; try reflexivity; apply SubstEE__subst_ee_open_ee_lc; exact Hlc.
    + f_equal; try reflexivity; apply SubstEE__subst_ee_open_ee_lc; exact Hlc.
  - destruct r; intros x v k f Hlc; simpl; try reflexivity.
    + f_equal; [apply SubstEE__subst_ee_open_ee_lc | apply SubstEE__subst_ee_rec_open_ee_lc]; exact Hlc.
    + f_equal. apply SubstEE__subst_ee_rec_open_ee_lc. exact Hlc.
Qed.

Lemma SubstEE__subst_ee_open_ee_lc_apply : forall x v e f,
  SubstEE__lc_exp 0 v ->
  SubstEE__subst_ee x v (open_ee e f) = open_ee (SubstEE__subst_ee x v e) (SubstEE__subst_ee x v f).
Proof. intros. apply (SubstEE__subst_ee_open_ee_lc e x v 0 f H). Qed.

Lemma SubstEE__subst_ee_open_ee_fvar_lc : forall x v e y,
  SubstEE__lc_exp 0 v -> y <> x ->
  SubstEE__subst_ee x v (open_ee e (exp_fvar y)) =
  open_ee (SubstEE__subst_ee x v e) (exp_fvar y).
Proof.
  intros x v e y Hlc Hneq. rewrite (SubstEE__subst_ee_open_ee_lc_apply x v e (exp_fvar y) Hlc).
  rewrite SubstEE__subst_ee_neq_fvar; [reflexivity|assumption].
Qed.

Lemma SubstEE__subst_ee_rec_open_ee_lc_apply : forall x v r f,
  SubstEE__lc_exp 0 v ->
  SubstEE__subst_ee_rec_comp x v (open_ee_record_rec 0 f r) =
  open_ee_record_rec 0 (SubstEE__subst_ee x v f) (SubstEE__subst_ee_rec_comp x v r).
Proof. intros. apply (SubstEE__subst_ee_rec_open_ee_lc r x v 0 f H). Qed.

Lemma SubstEE__subst_ee_rec_open_ee_fvar_lc : forall x v r y,
  SubstEE__lc_exp 0 v -> y <> x ->
  SubstEE__subst_ee_rec_comp x v (open_ee_record_rec 0 (exp_fvar y) r) =
  open_ee_record_rec 0 (exp_fvar y) (SubstEE__subst_ee_rec_comp x v r).
Proof.
  intros x v r y Hlc Hneq.
  rewrite (SubstEE__subst_ee_rec_open_ee_lc_apply x v r (exp_fvar y) Hlc).
  rewrite SubstEE__subst_ee_neq_fvar; [reflexivity|assumption].
Qed.

(* ---------------- free-variable commutation ---------------- *)

Fixpoint SubstEE__subst_ee_open_ee_fvar_fv (e : exp) {struct e} :
  forall x v (k : nat),
    x `notin` SubstEE__fv_exp e ->
    SubstEE__subst_ee x v (open_ee_rec k (exp_fvar x) e) = open_ee_rec k v e
with SubstEE__subst_ee_rec_open_ee_fvar_fv (r : rec_comp) {struct r} :
  forall x v (k : nat),
    x `notin` SubstEE__fv_rec_comp r ->
    SubstEE__subst_ee_rec_comp x v (open_ee_record_rec k (exp_fvar x) r) =
    open_ee_record_rec k v r.
Proof.
  - destruct e; intros x v k H; simpl in *.
    + destruct (k == n); [apply SubstEE__subst_ee_eq_fvar|reflexivity].
    + apply SubstEE__subst_ee_neq_fvar. apply (notin_singleton_1' a x H).
    + f_equal. apply SubstEE__subst_ee_open_ee_fvar_fv.
      apply notin_union_2 in H. exact H.
    + f_equal.
      * apply SubstEE__subst_ee_open_ee_fvar_fv. apply notin_union_1 in H. exact H.
      * apply SubstEE__subst_ee_open_ee_fvar_fv. apply notin_union_2 in H. exact H.
    + f_equal. apply SubstEE__subst_ee_open_ee_fvar_fv.
      apply notin_union_2 in H. exact H.
    + f_equal; try reflexivity; apply SubstEE__subst_ee_open_ee_fvar_fv.
      apply notin_union_1 in H. exact H.
    + f_equal.
      * apply SubstEE__subst_ee_open_ee_fvar_fv. apply notin_union_1 in H. exact H.
      * apply SubstEE__subst_ee_open_ee_fvar_fv. apply notin_union_2 in H. exact H.
    + f_equal. apply SubstEE__subst_ee_open_ee_fvar_fv. exact H.
    + f_equal. apply SubstEE__subst_ee_open_ee_fvar_fv. exact H.
    + f_equal.
      * apply SubstEE__subst_ee_open_ee_fvar_fv. apply notin_union_1 in H. exact H.
      * apply SubstEE__subst_ee_open_ee_fvar_fv. apply notin_union_2 in H. exact H.
    + reflexivity.
    + f_equal. apply SubstEE__subst_ee_open_ee_fvar_fv. exact H.
    + f_equal. apply SubstEE__subst_ee_rec_open_ee_fvar_fv. exact H.
    + f_equal; try reflexivity; apply SubstEE__subst_ee_open_ee_fvar_fv.
      apply notin_union_1 in H. exact H.
    + f_equal.
      * apply SubstEE__subst_ee_open_ee_fvar_fv. apply notin_union_1 in H.
        apply notin_union_1 in H. exact H.
      * apply SubstEE__subst_ee_open_ee_fvar_fv. apply notin_union_2 in H. exact H.
  - destruct r; intros x v k H; simpl in *.
    + reflexivity.
    + f_equal.
      * apply SubstEE__subst_ee_open_ee_fvar_fv.
        apply notin_union_1 in H. apply notin_union_2 in H. exact H.
      * apply SubstEE__subst_ee_rec_open_ee_fvar_fv. apply notin_union_2 in H. exact H.
    + f_equal. apply SubstEE__subst_ee_rec_open_ee_fvar_fv.
      apply notin_union_2 in H. exact H.
Qed.

Lemma SubstEE__open_ee_eq_subst : forall x v e,
  x `notin` SubstEE__fv_exp e ->
  open_ee e v = SubstEE__subst_ee x v (open_ee e (exp_fvar x)).
Proof.
  intros x v e H. symmetry. apply (SubstEE__subst_ee_open_ee_fvar_fv e x v 0 H).
Qed.

(* ---------------- commutation with type opening ---------------- *)

Fixpoint SubstEE__subst_ee_open_te_fvar (e : exp) {struct e} :
  forall x v (K : nat) X,
    SubstEE__annot_lc 0 v ->
    SubstEE__subst_ee x v (open_te_rec K (typ_fvar X) e) =
    open_te_rec K (typ_fvar X) (SubstEE__subst_ee x v e)
with SubstEE__subst_ee_rec_open_te_fvar (r : rec_comp) {struct r} :
  forall x v (K : nat) X,
    SubstEE__annot_lc 0 v ->
    SubstEE__subst_ee_rec_comp x v (open_te_record_rec K (typ_fvar X) r) =
    open_te_record_rec K (typ_fvar X) (SubstEE__subst_ee_rec_comp x v r).
Proof.
  - destruct e; intros x v K X Hann; simpl; try reflexivity.
    + destruct (x === a) as [Heq|Hneq].
      * symmetry. apply (SubstEE__annot_lc_closed_open_te v Hann K X).
      * reflexivity.
    + f_equal. apply SubstEE__subst_ee_open_te_fvar. exact Hann.
    + f_equal; [apply SubstEE__subst_ee_open_te_fvar | apply SubstEE__subst_ee_open_te_fvar]; exact Hann.
    + f_equal. apply SubstEE__subst_ee_open_te_fvar. exact Hann.
    + f_equal; try reflexivity; apply SubstEE__subst_ee_open_te_fvar; exact Hann.
    + f_equal; [apply SubstEE__subst_ee_open_te_fvar | apply SubstEE__subst_ee_open_te_fvar]; exact Hann.
    + f_equal. apply SubstEE__subst_ee_open_te_fvar. exact Hann.
    + f_equal. apply SubstEE__subst_ee_open_te_fvar. exact Hann.
    + f_equal; [apply SubstEE__subst_ee_open_te_fvar | apply SubstEE__subst_ee_open_te_fvar]; exact Hann.
    + f_equal. apply SubstEE__subst_ee_open_te_fvar. exact Hann.
    + f_equal. apply SubstEE__subst_ee_rec_open_te_fvar. exact Hann.
    + f_equal; try reflexivity; apply SubstEE__subst_ee_open_te_fvar; exact Hann.
    + f_equal; try reflexivity; apply SubstEE__subst_ee_open_te_fvar; exact Hann.
  - destruct r; intros x v K X Hann; simpl; try reflexivity.
    + f_equal; [apply SubstEE__subst_ee_open_te_fvar | apply SubstEE__subst_ee_rec_open_te_fvar]; exact Hann.
    + f_equal. apply SubstEE__subst_ee_rec_open_te_fvar. exact Hann.
Qed.

Lemma SubstEE__subst_ee_open_te_fvar_apply : forall x v e X,
  SubstEE__annot_lc 0 v ->
  SubstEE__subst_ee x v (open_te e (typ_fvar X)) =
  open_te (SubstEE__subst_ee x v e) (typ_fvar X).
Proof. intros. apply (SubstEE__subst_ee_open_te_fvar e x v 0 X H). Qed.

Lemma SubstEE__subst_ee_rec_open_te_fvar_apply : forall x v r X,
  SubstEE__annot_lc 0 v ->
  SubstEE__subst_ee_rec_comp x v (open_te_record_rec 0 (typ_fvar X) r) =
  open_te_record_rec 0 (typ_fvar X) (SubstEE__subst_ee_rec_comp x v r).
Proof. intros. apply (SubstEE__subst_ee_rec_open_te_fvar r x v 0 X H). Qed.

(* ================================================================ *)
(* Typing weakening under environment inclusion                      *)
(* ================================================================ *)

Definition SubstEE__typing_weaken_P (E : env) (R : sig) (e : exp) (T : typ)
    (_ : typing E R e T) : Prop :=
  forall E' : env, wf_env E' -> SubstEE__env_incl E E' -> typing E' R e T.

Definition SubstEE__typing_weaken_Q (E : env) (R : sig) (r : rec_comp) (T : typ)
    (_ : typing_record_comp E R r T) : Prop :=
  forall E' : env, wf_env E' -> SubstEE__env_incl E E' -> typing_record_comp E' R r T.

Lemma SubstEE__typing_weaken_incl : forall (E : env) (R : sig) e T,
  typing E R e T ->
  forall E' : env, wf_env E' -> SubstEE__env_incl E E' -> typing E' R e T.
Proof.
  intros E R ee Tres Hty. change (SubstEE__typing_weaken_P E R ee Tres Hty).
  apply (SubstEE__typing_induction SubstEE__typing_weaken_P SubstEE__typing_weaken_Q).
  + (* var *) intros E0 R0 x T0 Hwe Hws Hb E' Hwe' Hinc.
    apply (typing_var E' R0 x T0); [exact Hwe' | |].
    * apply (SubstEE__wf_sig_incl E0 E' R0 Hwe'); [|exact Hws].
      intros X U HX. apply Hinc. assumption.
    * apply Hinc. assumption.
  + (* abs *) intros L E0 R0 V e1 T1 Hws Hbody IHbody E' Hwe' Hinc.
    set (L' := L `union` dom E').
    apply (typing_abs L' E' R0 V e1 T1).
    * apply (SubstEE__wf_sig_incl E0 E' R0 Hwe'); [|exact Hws].
      intros X U HX. apply Hinc. assumption.
    * intros x Hx. unfold L' in Hx.
      apply notin_union_1 in Hx as HxL.
      apply notin_union_2 in Hx as Hxd.
      assert (Hbodyx : typing (x ~ bind_typ V ++ E0) R0 (open_ee e1 (exp_fvar x)) T1)
        by (apply Hbody; assumption).
      assert (Hwss : wf_sig (x ~ bind_typ V ++ E0) R0)
        by (apply (SubstTT__typing_wf_sig (x ~ bind_typ V ++ E0) R0 (open_ee e1 (exp_fvar x)) T1); exact Hbodyx).
      assert (Hwes : wf_env (x ~ bind_typ V ++ E0))
        by (apply (Dev__wf_sig_wf_env (x ~ bind_typ V ++ E0) R0); exact Hwss).
      destruct (Dev__wf_env_cons_bind_typ E0 x V Hwes) as [Hwe0 HwV].
      assert (HwV' : wf_typ E' V).
      { apply (SubstTT__wf_typ_incl E0 V HwV E'). intros X U HX. apply Hinc. assumption. }
      assert (HweB : wf_env (x ~ bind_typ V ++ E'))
        by (apply (wf_env_typ E' x V); assumption).
      assert (HincB : SubstEE__env_incl (x ~ bind_typ V ++ E0) (x ~ bind_typ V ++ E'))
        by (apply SubstEE__env_incl_cons; exact Hinc).
      exact (IHbody x HxL (x ~ bind_typ V ++ E') HweB HincB).
  + (* app *) intros T1 E0 R0 e1 e2 T2 Hws H1 IH1 H2 IH2 E' Hwe' Hinc.
    apply (typing_app T1 E' R0 e1 e2 T2).
    * apply (SubstEE__wf_sig_incl E0 E' R0 Hwe'); [|exact Hws].
      intros X U HX. apply Hinc. assumption.
    * exact (IH1 E' Hwe' Hinc).
    * exact (IH2 E' Hwe' Hinc).
  + (* tabs *) intros L E0 R0 V e1 T1 Hws Hbody IHbody E' Hwe' Hinc.
    set (L' := L `union` dom E').
    apply (typing_tabs L' E' R0 V e1 T1).
    * apply (SubstEE__wf_sig_incl E0 E' R0 Hwe'); [|exact Hws].
      intros X U HX. apply Hinc. assumption.
    * intros X HX. unfold L' in HX.
      apply notin_union_1 in HX as HXL.
      apply notin_union_2 in HX as HXd.
      assert (HbodyX : typing (X ~ bind_sub V ++ E0) R0 (open_te e1 (typ_fvar X)) (open_tt T1 (typ_fvar X)))
        by (apply Hbody; assumption).
      assert (Hwss : wf_sig (X ~ bind_sub V ++ E0) R0)
        by (apply (SubstTT__typing_wf_sig (X ~ bind_sub V ++ E0) R0 (open_te e1 (typ_fvar X)) (open_tt T1 (typ_fvar X))); exact HbodyX).
      assert (Hwes : wf_env (X ~ bind_sub V ++ E0))
        by (apply (Dev__wf_sig_wf_env (X ~ bind_sub V ++ E0) R0); exact Hwss).
      destruct (Dev__wf_env_cons_bind_sub E0 X V Hwes) as [Hwe0 HwV].
      assert (HwV' : wf_typ E' V).
      { apply (SubstTT__wf_typ_incl E0 V HwV E'). intros X0 U HX0. apply Hinc. assumption. }
      assert (HweB : wf_env (X ~ bind_sub V ++ E'))
        by (apply (wf_env_sub E' X V); assumption).
      assert (HincB : SubstEE__env_incl (X ~ bind_sub V ++ E0) (X ~ bind_sub V ++ E'))
        by (apply SubstEE__env_incl_cons; exact Hinc).
      exact (IHbody X HXL (X ~ bind_sub V ++ E') HweB HincB).
  + (* tapp *) intros T1 E0 R0 e1 T T2 Hws H1 IH1 Hsub E' Hwe' Hinc.
    assert (Hwe0 : wf_env E0) by (apply Dev__wf_sig_wf_env with (R := R0); exact Hws).
    assert (HwAll : wf_typ E0 (typ_all T1 T2))
      by (apply (SubstTT__typing_wf_typ E0 R0 e1 (typ_all T1 T2)); exact H1).
    destruct (Dev__wf_typ_inv_all E0 T1 T2 HwAll) as [L [HwT1 _]].
    assert (HwT : wf_typ E0 T) by (apply (Dev__sub_wf_source E0 T T1 Hwe0 HwT1 Hsub)).
    apply (typing_tapp T1 E' R0 e1 T T2).
    * apply (SubstEE__wf_sig_incl E0 E' R0 Hwe'); [|exact Hws].
      intros X U HX. apply Hinc. assumption.
    * exact (IH1 E' Hwe' Hinc).
    * apply (SubstEE__sub_weaken_bindsub E0 T T1 Hwe0 HwT Hsub E' Hwe').
      intros X U HX. apply Hinc. assumption.
  + (* sub *) intros S E0 R0 e T Hws H1 IH1 Hsub E' Hwe' Hinc.
    assert (Hwe0 : wf_env E0) by (apply Dev__wf_sig_wf_env with (R := R0); exact Hws).
    assert (HwS : wf_typ E0 S) by (apply (SubstTT__typing_wf_typ E0 R0 e S); exact H1).
    apply (typing_sub S E' R0 e T).
    * apply (SubstEE__wf_sig_incl E0 E' R0 Hwe'); [|exact Hws].
      intros X U HX. apply Hinc. assumption.
    * exact (IH1 E' Hwe' Hinc).
    * apply (SubstEE__sub_weaken_bindsub E0 S T Hwe0 HwS Hsub E' Hwe').
      intros X U HX. apply Hinc. assumption.
  + (* let *) intros L T1 T2 e1 e2 E0 R0 Hws H1 IH1 Hbody IHbody E' Hwe' Hinc.
    set (L' := L `union` dom E').
    apply (typing_let L' T1 T2 e1 e2 E' R0).
    * apply (SubstEE__wf_sig_incl E0 E' R0 Hwe'); [|exact Hws].
      intros X U HX. apply Hinc. assumption.
    * exact (IH1 E' Hwe' Hinc).
    * intros x Hx. unfold L' in Hx.
      apply notin_union_1 in Hx as HxL.
      apply notin_union_2 in Hx as Hxd.
      assert (Hbodyx : typing (x ~ bind_typ T1 ++ E0) R0 (open_ee e2 (exp_fvar x)) T2)
        by (apply Hbody; assumption).
      assert (Hwss : wf_sig (x ~ bind_typ T1 ++ E0) R0)
        by (apply (SubstTT__typing_wf_sig (x ~ bind_typ T1 ++ E0) R0 (open_ee e2 (exp_fvar x)) T2); exact Hbodyx).
      assert (Hwes : wf_env (x ~ bind_typ T1 ++ E0))
        by (apply (Dev__wf_sig_wf_env (x ~ bind_typ T1 ++ E0) R0); exact Hwss).
      destruct (Dev__wf_env_cons_bind_typ E0 x T1 Hwes) as [Hwe0 HwT1].
      assert (HwT1' : wf_typ E' T1).
      { apply (SubstTT__wf_typ_incl E0 T1 HwT1 E'). intros X U HX. apply Hinc. assumption. }
      assert (HweB : wf_env (x ~ bind_typ T1 ++ E'))
        by (apply (wf_env_typ E' x T1); assumption).
      assert (HincB : SubstEE__env_incl (x ~ bind_typ T1 ++ E0) (x ~ bind_typ T1 ++ E'))
        by (apply SubstEE__env_incl_cons; exact Hinc).
      exact (IHbody x HxL (x ~ bind_typ T1 ++ E') HweB HincB).
  + (* box *) intros E0 R0 e T Hws H1 IH1 E' Hwe' Hinc.
    apply typing_box.
    * apply (SubstEE__wf_sig_incl E0 E' R0 Hwe'); [|exact Hws].
      intros X U HX. apply Hinc. assumption.
    * exact (IH1 E' Hwe' Hinc).
  + (* unbox *) intros E0 R0 e T Hws H1 IH1 E' Hwe' Hinc.
    apply typing_unbox.
    * apply (SubstEE__wf_sig_incl E0 E' R0 Hwe'); [|exact Hws].
      intros X U HX. apply Hinc. assumption.
    * exact (IH1 E' Hwe' Hinc).
  + (* set_box *) intros E0 R0 e1 e2 T Hws H1 IH1 H2 IH2 E' Hwe' Hinc.
    apply typing_set_box.
    * apply (SubstEE__wf_sig_incl E0 E' R0 Hwe'); [|exact Hws].
      intros X U HX. apply Hinc. assumption.
    * exact (IH1 E' Hwe' Hinc).
    * exact (IH2 E' Hwe' Hinc).
  + (* ref *) intros E0 R0 l T Hwe Hws Hb E' Hwe' Hinc.
    apply (typing_ref E' R0 l T); [exact Hwe' | | exact Hb].
    apply (SubstEE__wf_sig_incl E0 E' R0 Hwe'); [|exact Hws].
    intros X U HX. apply Hinc. assumption.
  + (* seal *) intros E0 R0 e T H1 IH1 E' Hwe' Hinc.
    apply typing_seal. exact (IH1 E' Hwe' Hinc).
  + (* unbox_readonly *) intros E0 R0 e T H1 IH1 E' Hwe' Hinc.
    apply typing_unbox_readonly. exact (IH1 E' Hwe' Hinc).
  + (* record *) intros E0 R0 r T Hr IHr E' Hwe' Hinc.
    apply typing_record. exact (IHr E' Hwe' Hinc).
  + (* record_read *) intros E0 R0 e a T H1 IH1 E' Hwe' Hinc.
    apply typing_record_read. exact (IH1 E' Hwe' Hinc).
  + (* record_read_readonly *) intros E0 R0 e a T H1 IH1 E' Hwe' Hinc.
    apply typing_record_read_readonly. exact (IH1 E' Hwe' Hinc).
  + (* record_write *) intros E0 R0 e1 a e2 T H1 IH1 H2 IH2 E' Hwe' Hinc.
    apply typing_record_write.
    * exact (IH1 E' Hwe' Hinc).
    * exact (IH2 E' Hwe' Hinc).
  + (* record_empty *) intros E0 R0 Hwe Hws E' Hwe' Hinc.
    apply typing_record_empty; [exact Hwe'|].
    apply (SubstEE__wf_sig_incl E0 E' R0 Hwe'); [|exact Hws].
    intros X U HX. apply Hinc. assumption.
  + (* record_exp *) intros E0 R0 a e r T Tr Hnd Hr IHr He IHe E' Hwe' Hinc.
    apply typing_record_exp with (a := a).
    * exact Hnd.
    * exact (IHr E' Hwe' Hinc).
    * exact (IHe E' Hwe' Hinc).
  + (* record_ref *) intros E0 R0 a l r T Tr Hnd Hr IHr Hb E' Hwe' Hinc.
    apply typing_record_ref with (a := a).
    * exact Hnd.
    * exact (IHr E' Hwe' Hinc).
    * exact Hb.
Qed.

Lemma SubstEE__typing_record_comp_weaken_incl : forall (E : env) (R : sig) r T,
  typing_record_comp E R r T ->
  forall E' : env, wf_env E' -> SubstEE__env_incl E E' -> typing_record_comp E' R r T.
Proof.
  intros E R r T Htr.
  induction Htr as [ E0 R0 Hwe Hws
                  | E0 R0 a e r T Tr Hnd Hr IHr He
                  | E0 R0 a l r T Tr Hnd Hr IHr Hb ].
  - intros E' Hwe' Hinc. apply typing_record_empty; [exact Hwe'|].
    apply (SubstEE__wf_sig_incl E0 E' R0 Hwe'); [|exact Hws].
    intros X U HX. apply Hinc. assumption.
  - intros E' Hwe' Hinc. apply typing_record_exp with (a := a).
    + exact Hnd.
    + exact (IHr E' Hwe' Hinc).
    + apply (SubstEE__typing_weaken_incl E0 R0 e T He E' Hwe' Hinc).
  - intros E' Hwe' Hinc. apply typing_record_ref with (a := a).
    + exact Hnd.
    + exact (IHr E' Hwe' Hinc).
    + exact Hb.
Qed.

(* ================= appended from ScratchSubst.v ================= *)
Lemma SubstEE__record_dom_subst_ee_rec : forall x vsub (r : rec_comp),
  record_dom (SubstEE__subst_ee_rec_comp x vsub r) = record_dom r.
Proof.
  intros x vsub r. induction r; simpl; try reflexivity; rewrite IHr; reflexivity.
Qed.

Definition SubstEE__typing_subst_P (x : atom) (vsub : exp) (V : typ)
    (E : env) (R : sig) (e : exp) (T : typ)
    (_ : typing E R e T) : Prop :=
  forall (P E0 : env),
    E = P ++ (x, bind_typ V) :: E0 ->
    typing (P ++ E0) R vsub V ->
    typing (P ++ E0) R (SubstEE__subst_ee x vsub e) T.

Definition SubstEE__typing_subst_Q (x : atom) (vsub : exp) (V : typ)
    (E : env) (R : sig) (r : rec_comp) (T : typ)
    (_ : typing_record_comp E R r T) : Prop :=
  forall (P E0 : env),
    E = P ++ (x, bind_typ V) :: E0 ->
    typing (P ++ E0) R vsub V ->
    typing_record_comp (P ++ E0) R (SubstEE__subst_ee_rec_comp x vsub r) T.

Lemma SubstEE__typing_subst_ee_gen : forall (x : atom) (vsub : exp) (V : typ)
  (Esrc : env) (Rsrc : sig) (esrc : exp) (Tres : typ),
  typing Esrc Rsrc esrc Tres ->
  forall (P E0 : env),
    Esrc = P ++ (x, bind_typ V) :: E0 ->
    typing (P ++ E0) Rsrc vsub V ->
    typing (P ++ E0) Rsrc (SubstEE__subst_ee x vsub esrc) Tres.
Proof.
  intros xsub vsub Vsub Esrc Rsrc esrc Tres Hty.
  change (SubstEE__typing_subst_P xsub vsub Vsub Esrc Rsrc esrc Tres Hty).
  apply (SubstEE__typing_induction (SubstEE__typing_subst_P xsub vsub Vsub)
                          (SubstEE__typing_subst_Q xsub vsub Vsub)).
  + (* var *) intros E R x T Hwe Hws Hb P E0 Heq Hv. subst E.
    assert (Hwe' : wf_env (P ++ E0))
      by (apply (SubstEE__wf_env_remove_mid_typ_gen P E0 xsub Vsub); exact Hwe).
    assert (Hws' : wf_sig (P ++ E0) R)
      by (apply (SubstTT__typing_wf_sig (P ++ E0) R vsub Vsub); exact Hv).
    destruct (xsub === x) as [Heq_x|Hneq_x].
    * subst x.
      assert (Hbmid : binds xsub (bind_typ Vsub)
                       (P ++ (xsub, bind_typ Vsub) :: E0)).
      { exact (Dev__binds_app_2 P ((xsub, bind_typ Vsub) :: E0)
                 xsub (bind_typ Vsub)
                 (Dev__binds_cons_1 E0 xsub (bind_typ Vsub))). }
      pose proof (SubstEE__wf_env_binds_unique (P ++ (xsub, bind_typ Vsub) :: E0)
                    Hwe xsub (bind_typ T) (bind_typ Vsub) Hb Hbmid) as Hu.
      inversion Hu. subst T.
      rewrite SubstEE__subst_ee_eq_fvar. exact Hv.
    * rewrite (SubstEE__subst_ee_neq_fvar xsub x vsub).
      -- apply (typing_var (P ++ E0) R x T Hwe' Hws').
         exact (SubstEE__binds_subst_mid_typ_neq P E0 xsub Vsub x (bind_typ T)
                  (fun Hx => Hneq_x (eq_sym Hx)) Hb).
      -- intro Hx. apply Hneq_x. symmetry. assumption.
  + (* abs *) intros L E R Vb e1 T1 Hws Hbody IHbody P E0 Heq Hv. subst E.
    destruct (SubstEE__typing_lc_annot (P ++ E0) R vsub Vsub Hv) as [Hlv Hanv].
    assert (Hws_t : wf_sig (P ++ E0) R)
      by (apply (SubstTT__typing_wf_sig (P ++ E0) R vsub Vsub); exact Hv).
    set (L' := (L `union` {{ xsub }}) `union` dom (P ++ E0)).
    apply (typing_abs L' (P ++ E0) R Vb (SubstEE__subst_ee xsub vsub e1) T1).
    * exact Hws_t.
    * intros y Hy. unfold L' in Hy.
      apply notin_union_1 in Hy as HyLx.
      apply notin_union_1 in HyLx as HyL.
      apply notin_union_2 in HyLx as Hyx.
      apply notin_union_2 in Hy as Hyd.
      apply notin_singleton_1' in Hyx.
      assert (Hbodyy : typing (y ~ bind_typ Vb ++ P ++ (xsub, bind_typ Vsub) :: E0)
                              R (open_ee e1 (exp_fvar y)) T1)
        by (apply Hbody; assumption).
      assert (Hwss : wf_sig (y ~ bind_typ Vb ++ P ++ (xsub, bind_typ Vsub) :: E0) R)
        by (apply (SubstTT__typing_wf_sig (y ~ bind_typ Vb ++ P ++ (xsub, bind_typ Vsub) :: E0) R
                   (open_ee e1 (exp_fvar y)) T1); exact Hbodyy).
      assert (Hwes : wf_env (y ~ bind_typ Vb ++ P ++ (xsub, bind_typ Vsub) :: E0))
        by (apply (Dev__wf_sig_wf_env (y ~ bind_typ Vb ++ P ++ (xsub, bind_typ Vsub) :: E0) R); exact Hwss).
      destruct (Dev__wf_env_cons_bind_typ (P ++ (xsub, bind_typ Vsub) :: E0) y Vb Hwes)
        as [Hwe0 HwVb_s].
      assert (Hwe_t : wf_env (P ++ E0))
        by (apply (SubstTT__typing_wf_sig  (P ++ E0) R vsub Vsub) in Hv; apply (Dev__wf_sig_wf_env (P ++ E0) R); exact Hv).
      assert (HwVb_t : wf_typ (P ++ E0) Vb).
      { apply (SubstTT__wf_typ_incl (P ++ (xsub, bind_typ Vsub) :: E0) Vb HwVb_s (P ++ E0)).
        intros Y U HYU. apply (SubstEE__binds_sub_remove_mid_typ P E0 xsub Vsub Y U). exact HYU. }
      assert (HweB : wf_env (y ~ bind_typ Vb ++ P ++ E0))
        by (apply (wf_env_typ (P ++ E0) y Vb); assumption).
      assert (Hv' : typing (y ~ bind_typ Vb ++ P ++ E0) R vsub Vsub).
      { apply (SubstEE__typing_weaken_incl (P ++ E0) R vsub Vsub Hv (y ~ bind_typ Vb ++ P ++ E0) HweB).
        intros z c Hz. simpl. right. assumption. }
      pose proof (IHbody y HyL ((y, bind_typ Vb) :: P) E0 eq_refl Hv') as Hres.
      simpl in Hres.
      rewrite (SubstEE__subst_ee_open_ee_fvar_lc xsub vsub e1 y Hlv
                 (fun H => Hyx (eq_sym H))) in Hres.
      exact Hres.
  + (* app *) intros T1 E R e1 e2 T2 Hws H1 IH1 H2 IH2 P E0 Heq Hv. subst E.
    assert (Hws_t : wf_sig (P ++ E0) R)
      by (apply (SubstTT__typing_wf_sig (P ++ E0) R vsub Vsub); exact Hv).
    simpl. apply (typing_app T1 (P ++ E0) R (SubstEE__subst_ee xsub vsub e1) (SubstEE__subst_ee xsub vsub e2) T2).
    * exact Hws_t.
    * exact (IH1 P E0 eq_refl Hv).
    * exact (IH2 P E0 eq_refl Hv).
  + (* tabs *) intros L E R Vb e1 T1 Hws Hbody IHbody P E0 Heq Hv. subst E.
    destruct (SubstEE__typing_lc_annot (P ++ E0) R vsub Vsub Hv) as [Hlv Hanv].
    assert (Hws_t : wf_sig (P ++ E0) R)
      by (apply (SubstTT__typing_wf_sig (P ++ E0) R vsub Vsub); exact Hv).
    set (L' := L `union` dom (P ++ E0)).
    apply (typing_tabs L' (P ++ E0) R Vb (SubstEE__subst_ee xsub vsub e1) T1).
    * exact Hws_t.
    * intros X HX. unfold L' in HX.
      apply notin_union_1 in HX as HXL.
      apply notin_union_2 in HX as HXd.
      assert (HbodyX : typing (X ~ bind_sub Vb ++ P ++ (xsub, bind_typ Vsub) :: E0)
                              R (open_te e1 (typ_fvar X)) (open_tt T1 (typ_fvar X)))
        by (apply Hbody; assumption).
      assert (Hwss : wf_sig (X ~ bind_sub Vb ++ P ++ (xsub, bind_typ Vsub) :: E0) R)
        by (apply (SubstTT__typing_wf_sig (X ~ bind_sub Vb ++ P ++ (xsub, bind_typ Vsub) :: E0) R
                   (open_te e1 (typ_fvar X)) (open_tt T1 (typ_fvar X))); exact HbodyX).
      assert (Hwes : wf_env (X ~ bind_sub Vb ++ P ++ (xsub, bind_typ Vsub) :: E0))
        by (apply (Dev__wf_sig_wf_env (X ~ bind_sub Vb ++ P ++ (xsub, bind_typ Vsub) :: E0) R); exact Hwss).
      destruct (Dev__wf_env_cons_bind_sub (P ++ (xsub, bind_typ Vsub) :: E0) X Vb Hwes)
        as [Hwe0 HwVb_s].
      assert (Hwe_t : wf_env (P ++ E0))
        by (apply (SubstTT__typing_wf_sig (P ++ E0) R vsub Vsub) in Hv; apply (Dev__wf_sig_wf_env (P ++ E0) R); exact Hv).
      assert (HwVb_t : wf_typ (P ++ E0) Vb).
      { apply (SubstTT__wf_typ_incl (P ++ (xsub, bind_typ Vsub) :: E0) Vb HwVb_s (P ++ E0)).
        intros Y U HYU. apply (SubstEE__binds_sub_remove_mid_typ P E0 xsub Vsub Y U). exact HYU. }
      assert (HweB : wf_env (X ~ bind_sub Vb ++ P ++ E0))
        by (apply (wf_env_sub (P ++ E0) X Vb); assumption).
      assert (Hv' : typing (X ~ bind_sub Vb ++ P ++ E0) R vsub Vsub).
      { apply (SubstEE__typing_weaken_incl (P ++ E0) R vsub Vsub Hv (X ~ bind_sub Vb ++ P ++ E0) HweB).
        intros z c Hz. simpl. right. assumption. }
      pose proof (IHbody X HXL ((X, bind_sub Vb) :: P) E0 eq_refl Hv') as Hres.
      simpl in Hres.
      rewrite (SubstEE__subst_ee_open_te_fvar_apply xsub vsub e1 X Hanv) in Hres.
      exact Hres.
  + (* tapp *) intros T1 E R e1 T T2 Hws H1 IH1 Hsub P E0 Heq Hv. subst E.
    assert (Hws_t : wf_sig (P ++ E0) R)
      by (apply (SubstTT__typing_wf_sig (P ++ E0) R vsub Vsub); exact Hv).
    assert (Hwe_t : wf_env (P ++ E0))
      by (apply (Dev__wf_sig_wf_env (P ++ E0) R); exact Hws_t).
    assert (Hwe_s : wf_env (P ++ (xsub, bind_typ Vsub) :: E0))
      by (apply (Dev__wf_sig_wf_env (P ++ (xsub, bind_typ Vsub) :: E0) R); exact Hws).
    assert (HwAll : wf_typ (P ++ (xsub, bind_typ Vsub) :: E0) (typ_all T1 T2))
      by (apply (SubstTT__typing_wf_typ (P ++ (xsub, bind_typ Vsub) :: E0) R e1 (typ_all T1 T2)); exact H1).
    destruct (Dev__wf_typ_inv_all (P ++ (xsub, bind_typ Vsub) :: E0) T1 T2 HwAll) as [L [HwT1 _]].
    assert (HwT : wf_typ (P ++ (xsub, bind_typ Vsub) :: E0) T)
      by (apply (Dev__sub_wf_source (P ++ (xsub, bind_typ Vsub) :: E0) T T1 Hwe_s HwT1 Hsub)).
    apply (typing_tapp T1 (P ++ E0) R (SubstEE__subst_ee xsub vsub e1) T T2).
    * exact Hws_t.
    * exact (IH1 P E0 eq_refl Hv).
    * apply (SubstEE__sub_weaken_bindsub (P ++ (xsub, bind_typ Vsub) :: E0) T T1 Hwe_s HwT Hsub (P ++ E0) Hwe_t).
      intros Y U HYU. apply (SubstEE__binds_sub_remove_mid_typ P E0 xsub Vsub Y U). exact HYU.
  + (* sub *) intros S E R e T Hws H1 IH1 Hsub P E0 Heq Hv. subst E.
    assert (Hws_t : wf_sig (P ++ E0) R)
      by (apply (SubstTT__typing_wf_sig (P ++ E0) R vsub Vsub); exact Hv).
    assert (Hwe_t : wf_env (P ++ E0))
      by (apply (Dev__wf_sig_wf_env (P ++ E0) R); exact Hws_t).
    assert (Hwe_s : wf_env (P ++ (xsub, bind_typ Vsub) :: E0))
      by (apply (Dev__wf_sig_wf_env (P ++ (xsub, bind_typ Vsub) :: E0) R); exact Hws).
    assert (HwS : wf_typ (P ++ (xsub, bind_typ Vsub) :: E0) S)
      by (apply (SubstTT__typing_wf_typ (P ++ (xsub, bind_typ Vsub) :: E0) R e S); exact H1).
    apply (typing_sub S (P ++ E0) R (SubstEE__subst_ee xsub vsub e) T).
    * exact Hws_t.
    * exact (IH1 P E0 eq_refl Hv).
    * apply (SubstEE__sub_weaken_bindsub (P ++ (xsub, bind_typ Vsub) :: E0) S T Hwe_s HwS Hsub (P ++ E0) Hwe_t).
      intros Y U HYU. apply (SubstEE__binds_sub_remove_mid_typ P E0 xsub Vsub Y U). exact HYU.
  + (* let *) intros L T1 T2 e1 e2 E R Hws H1 IH1 Hbody IHbody P E0 Heq Hv. subst E.
    destruct (SubstEE__typing_lc_annot (P ++ E0) R vsub Vsub Hv) as [Hlv Hanv].
    assert (Hws_t : wf_sig (P ++ E0) R)
      by (apply (SubstTT__typing_wf_sig (P ++ E0) R vsub Vsub); exact Hv).
    set (L' := (L `union` {{ xsub }}) `union` dom (P ++ E0)).
    apply (typing_let L' T1 T2 (SubstEE__subst_ee xsub vsub e1) (SubstEE__subst_ee xsub vsub e2) (P ++ E0) R).
    * exact Hws_t.
    * exact (IH1 P E0 eq_refl Hv).
    * intros y Hy. unfold L' in Hy.
      apply notin_union_1 in Hy as HyLx.
      apply notin_union_1 in HyLx as HyL.
      apply notin_union_2 in HyLx as Hyx.
      apply notin_union_2 in Hy as Hyd.
      apply notin_singleton_1' in Hyx.
      assert (Hbodyy : typing (y ~ bind_typ T1 ++ P ++ (xsub, bind_typ Vsub) :: E0)
                              R (open_ee e2 (exp_fvar y)) T2)
        by (apply Hbody; assumption).
      assert (Hwss : wf_sig (y ~ bind_typ T1 ++ P ++ (xsub, bind_typ Vsub) :: E0) R)
        by (apply (SubstTT__typing_wf_sig (y ~ bind_typ T1 ++ P ++ (xsub, bind_typ Vsub) :: E0) R
                   (open_ee e2 (exp_fvar y)) T2); exact Hbodyy).
      assert (Hwes : wf_env (y ~ bind_typ T1 ++ P ++ (xsub, bind_typ Vsub) :: E0))
        by (apply (Dev__wf_sig_wf_env (y ~ bind_typ T1 ++ P ++ (xsub, bind_typ Vsub) :: E0) R); exact Hwss).
      destruct (Dev__wf_env_cons_bind_typ (P ++ (xsub, bind_typ Vsub) :: E0) y T1 Hwes)
        as [Hwe0 HwT1_s].
      assert (Hwe_t : wf_env (P ++ E0))
        by (apply (SubstTT__typing_wf_sig (P ++ E0) R vsub Vsub) in Hv; apply (Dev__wf_sig_wf_env (P ++ E0) R); exact Hv).
      assert (HwT1_t : wf_typ (P ++ E0) T1).
      { apply (SubstTT__wf_typ_incl (P ++ (xsub, bind_typ Vsub) :: E0) T1 HwT1_s (P ++ E0)).
        intros Y U HYU. apply (SubstEE__binds_sub_remove_mid_typ P E0 xsub Vsub Y U). exact HYU. }
      assert (HweB : wf_env (y ~ bind_typ T1 ++ P ++ E0))
        by (apply (wf_env_typ (P ++ E0) y T1); assumption).
      assert (Hv' : typing (y ~ bind_typ T1 ++ P ++ E0) R vsub Vsub).
      { apply (SubstEE__typing_weaken_incl (P ++ E0) R vsub Vsub Hv (y ~ bind_typ T1 ++ P ++ E0) HweB).
        intros z c Hz. simpl. right. assumption. }
      pose proof (IHbody y HyL ((y, bind_typ T1) :: P) E0 eq_refl Hv') as Hres.
      simpl in Hres.
      rewrite (SubstEE__subst_ee_open_ee_fvar_lc xsub vsub e2 y Hlv
                 (fun H => Hyx (eq_sym H))) in Hres.
      exact Hres.
  + (* box *) intros E R e T Hws H1 IH1 P E0 Heq Hv. subst E.
    assert (Hws_t : wf_sig (P ++ E0) R)
      by (apply (SubstTT__typing_wf_sig (P ++ E0) R vsub Vsub); exact Hv).
    simpl. apply (typing_box (P ++ E0) R (SubstEE__subst_ee xsub vsub e) T); [exact Hws_t|].
    exact (IH1 P E0 eq_refl Hv).
  + (* unbox *) intros E R e T Hws H1 IH1 P E0 Heq Hv. subst E.
    assert (Hws_t : wf_sig (P ++ E0) R)
      by (apply (SubstTT__typing_wf_sig (P ++ E0) R vsub Vsub); exact Hv).
    simpl. apply (typing_unbox (P ++ E0) R (SubstEE__subst_ee xsub vsub e) T); [exact Hws_t|].
    exact (IH1 P E0 eq_refl Hv).
  + (* set_box *) intros E R e1 e2 T Hws H1 IH1 H2 IH2 P E0 Heq Hv. subst E.
    assert (Hws_t : wf_sig (P ++ E0) R)
      by (apply (SubstTT__typing_wf_sig (P ++ E0) R vsub Vsub); exact Hv).
    simpl. apply (typing_set_box (P ++ E0) R (SubstEE__subst_ee xsub vsub e1) (SubstEE__subst_ee xsub vsub e2) T).
    * exact Hws_t.
    * exact (IH1 P E0 eq_refl Hv).
    * exact (IH2 P E0 eq_refl Hv).
  + (* ref *) intros E R l T Hwe Hws Hb P E0 Heq Hv. subst E.
    assert (Hwe' : wf_env (P ++ E0))
      by (apply (SubstEE__wf_env_remove_mid_typ_gen P E0 xsub Vsub); exact Hwe).
    assert (Hws' : wf_sig (P ++ E0) R).
    { apply (SubstEE__wf_sig_incl (P ++ (xsub, bind_typ Vsub) :: E0) (P ++ E0) R Hwe').
      - intros X U HX. apply (SubstEE__binds_sub_remove_mid_typ P E0 xsub Vsub X U). exact HX.
      - exact Hws. }
    simpl. apply (typing_ref (P ++ E0) R l T); assumption.
  + (* seal *) intros E R e T H1 IH1 P E0 Heq Hv. subst E.
    simpl. apply typing_seal. exact (IH1 P E0 eq_refl Hv).
  + (* unbox_readonly *) intros E R e T H1 IH1 P E0 Heq Hv. subst E.
    simpl. apply typing_unbox_readonly. exact (IH1 P E0 eq_refl Hv).
  + (* record *) intros E R r T Hr IHr P E0 Heq Hv. subst E.
    simpl. apply typing_record. exact (IHr P E0 eq_refl Hv).
  + (* record_read *) intros E R e a T H1 IH1 P E0 Heq Hv. subst E.
    simpl. apply typing_record_read. exact (IH1 P E0 eq_refl Hv).
  + (* record_read_readonly *) intros E R e a T H1 IH1 P E0 Heq Hv. subst E.
    simpl. apply typing_record_read_readonly. exact (IH1 P E0 eq_refl Hv).
  + (* record_write *) intros E R e1 a e2 T H1 IH1 H2 IH2 P E0 Heq Hv. subst E.
    simpl. apply typing_record_write.
    * exact (IH1 P E0 eq_refl Hv).
    * exact (IH2 P E0 eq_refl Hv).
  + (* record_empty *) intros E R Hwe Hws P E0 Heq Hv. subst E.
    assert (Hwe' : wf_env (P ++ E0))
      by (apply (SubstEE__wf_env_remove_mid_typ_gen P E0 xsub Vsub); exact Hwe).
    assert (Hws' : wf_sig (P ++ E0) R).
    { apply (SubstEE__wf_sig_incl (P ++ (xsub, bind_typ Vsub) :: E0) (P ++ E0) R Hwe').
      - intros X U HX. apply (SubstEE__binds_sub_remove_mid_typ P E0 xsub Vsub X U). exact HX.
      - exact Hws. }
    simpl. apply (typing_record_empty (P ++ E0) R); assumption.
  + (* record_exp *) intros E R a e r T Tr Hnd Hr IHr He IHe P E0 Heq Hv. subst E.
    simpl. apply (typing_record_exp (P ++ E0) R a (SubstEE__subst_ee xsub vsub e) (SubstEE__subst_ee_rec_comp xsub vsub r) T Tr).
    * rewrite SubstEE__record_dom_subst_ee_rec. exact Hnd.
    * exact (IHr P E0 eq_refl Hv).
    * exact (IHe P E0 eq_refl Hv).
  + (* record_ref *) intros E R a l r T Tr Hnd Hr IHr Hb P E0 Heq Hv. subst E.
    simpl. apply (typing_record_ref (P ++ E0) R a l (SubstEE__subst_ee_rec_comp xsub vsub r) T Tr).
    * rewrite SubstEE__record_dom_subst_ee_rec. exact Hnd.
    * exact (IHr P E0 eq_refl Hv).
    * exact Hb.
Qed.

Lemma SubstEE__typing_record_comp_subst_ee_gen : forall (x : atom) (vsub : exp) (V : typ)
  (Esrc : env) (Rsrc : sig) (r : rec_comp) (Tres : typ),
  typing_record_comp Esrc Rsrc r Tres ->
  forall (P E0 : env),
    Esrc = P ++ (x, bind_typ V) :: E0 ->
    typing (P ++ E0) Rsrc vsub V ->
    typing_record_comp (P ++ E0) Rsrc (SubstEE__subst_ee_rec_comp x vsub r) Tres.
Proof.
  intros xsub vsub Vsub Esrc Rsrc r Tres Htr.
  induction Htr as [ E R Hwe Hws
                  | E R a e r T Tr Hnd Hr IHr He
                  | E R a l r T Tr Hnd Hr IHr Hb ];
    intros P E0 Heq Hv; subst E.
  - assert (Hwe' : wf_env (P ++ E0))
      by (apply (SubstEE__wf_env_remove_mid_typ_gen P E0 xsub Vsub); exact Hwe).
    assert (Hws' : wf_sig (P ++ E0) R).
    { apply (SubstEE__wf_sig_incl (P ++ (xsub, bind_typ Vsub) :: E0) (P ++ E0) R Hwe').
      - intros X U HX. apply (SubstEE__binds_sub_remove_mid_typ P E0 xsub Vsub X U). exact HX.
      - exact Hws. }
    simpl. apply (typing_record_empty (P ++ E0) R); assumption.
  - simpl. apply (typing_record_exp (P ++ E0) R a (SubstEE__subst_ee xsub vsub e)
                 (SubstEE__subst_ee_rec_comp xsub vsub r) T Tr).
    + rewrite SubstEE__record_dom_subst_ee_rec. exact Hnd.
    + exact (IHr P E0 eq_refl Hv).
    + exact (SubstEE__typing_subst_ee_gen xsub vsub Vsub (P ++ (xsub, bind_typ Vsub) :: E0) R e T He P E0 eq_refl Hv).
  - simpl. apply (typing_record_ref (P ++ E0) R a l (SubstEE__subst_ee_rec_comp xsub vsub r) T Tr).
    + rewrite SubstEE__record_dom_subst_ee_rec. exact Hnd.
    + exact (IHr P E0 eq_refl Hv).
    + exact Hb.
Qed.

Lemma SubstEE__typing_subst_ee : forall (E : env) (R : sig) (x : atom) (V : typ) (vsub : exp) e T,
  typing (x ~ bind_typ V ++ E) R e T ->
  typing E R vsub V ->
  typing E R (SubstEE__subst_ee x vsub e) T.
Proof.
  intros E R x V vsub e T Hty Hv.
  exact (SubstEE__typing_subst_ee_gen x vsub V (x ~ bind_typ V ++ E) R e T Hty empty E eq_refl Hv).
Qed.

Lemma SubstEE__typing_record_comp_subst_ee : forall (E : env) (R : sig) (x : atom) (V : typ) (vsub : exp) r T,
  typing_record_comp (x ~ bind_typ V ++ E) R r T ->
  typing E R vsub V ->
  typing_record_comp E R (SubstEE__subst_ee_rec_comp x vsub r) T.
Proof.
  intros E R x V vsub r T Htr Hv.
  exact (SubstEE__typing_record_comp_subst_ee_gen x vsub V (x ~ bind_typ V ++ E) R r T Htr empty E eq_refl Hv).
Qed.

(* ================================================================ *)
(* Open-substitution forms used by preservation                     *)
(* ================================================================ *)

Lemma SubstEE__typing_subst_ee0 : forall (E : env) (x : atom) (U : typ) (R : sig)
  e T (vsub : exp),
  x `notin` dom E -> value vsub -> typing E R vsub U ->
  typing (x ~ bind_typ U ++ E) R e T ->
  typing E R (SubstEE__subst_ee x vsub e) T.
Proof.
  intros E x U R e T vsub Hx Hval Hv Hty.
  exact (SubstEE__typing_subst_ee E R x U vsub e T Hty Hv).
Qed.

Lemma SubstEE__typing_record_comp_subst_ee0 : forall (E : env) (x : atom) (U : typ)
  (R : sig) r T (vsub : exp),
  x `notin` dom E -> value vsub -> typing E R vsub U ->
  typing_record_comp (x ~ bind_typ U ++ E) R r T ->
  typing_record_comp E R (SubstEE__subst_ee_rec_comp x vsub r) T.
Proof.
  intros E x U R r T vsub Hx Hval Hv Htr.
  exact (SubstEE__typing_record_comp_subst_ee E R x U vsub r T Htr Hv).
Qed.

Lemma SubstEE__typing_subst_ee0_open : forall (E : env) (x : atom) (U : typ) (R : sig)
  e T (vsub : exp),
  x `notin` dom E -> x `notin` SubstEE__fv_exp e -> value vsub -> typing E R vsub U ->
  typing (x ~ bind_typ U ++ E) R (open_ee e (exp_fvar x)) T ->
  typing E R (open_ee e vsub) T.
Proof.
  intros E x U R e T vsub Hx Hxfv Hval Hv Hty.
  pose proof (SubstEE__typing_subst_ee E R x U vsub (open_ee e (exp_fvar x)) T Hty Hv) as Hsub.
  change (typing E R (open_ee_rec 0 vsub e) T).
  rewrite <- (SubstEE__subst_ee_open_ee_fvar_fv e x vsub 0 Hxfv).
  exact Hsub.
Qed.

Lemma SubstEE__typing_record_comp_subst_ee0_open : forall (E : env) (x : atom)
  (U : typ) (R : sig) r T (vsub : exp),
  x `notin` dom E -> x `notin` SubstEE__fv_rec_comp r -> value vsub ->
  typing E R vsub U ->
  typing_record_comp (x ~ bind_typ U ++ E) R
    (open_ee_record_rec 0 (exp_fvar x) r) T ->
  typing_record_comp E R (open_ee_record_rec 0 vsub r) T.
Proof.
  intros E x U R r T vsub Hx Hxfv Hval Hv Htr.
  pose proof (SubstEE__typing_record_comp_subst_ee E R x U vsub
                (open_ee_record_rec 0 (exp_fvar x) r) T Htr Hv) as Hsub.
  rewrite <- (SubstEE__subst_ee_rec_open_ee_fvar_fv r x vsub 0 Hxfv).
  exact Hsub.
Qed.




(* Beta for term abstraction: type the opened body at a type below the
   arrow's codomain. *)
Lemma PresHelpers__typing_abs_beta : forall E R V e1 T1 T2 v2,
  typing E R (exp_abs V e1) (typ_arrow T1 T2) ->
  typing E R v2 T1 ->
  value v2 ->
  exists Tbody,
    typing E R (open_ee e1 v2) Tbody /\ sub E Tbody T2.
Proof.
  intros E R V e1 T1 T2 v2 Hty Hv2ty Hval2.
  assert (Hws : wf_sig E R) by (apply (Store__typing_wf_sig_mut E R (exp_abs V e1) (typ_arrow T1 T2)); assumption).
  assert (HE : wf_env E) by (apply (Dev__wf_sig_wf_env E R); assumption).
  assert (HWf : wf_typ E (typ_arrow T1 T2))
    by (apply (SubstTT__typing_wf_typ E R (exp_abs V e1) (typ_arrow T1 T2)); assumption).
  destruct (TypingInv__typing_abs_inv E R V e1 (typ_arrow T1 T2) Hty HE HWf)
    as [Tbody [L [Hs Hbody]]].
  assert (HWS : wf_typ E (typ_arrow V Tbody))
    by (apply (Dev__sub_wf_source E (typ_arrow V Tbody) (typ_arrow T1 T2)); assumption).
  destruct (MyWork__sub_arrow_arrow E V Tbody T1 T2 HE HWS HWf Hs)
    as [Hcontra Hco].
  destruct (atom_fresh (L `union` dom E `union` SubstEE__fv_exp e1)) as [x Hx].
  assert (HxL : x `notin` L).
  { apply notin_union_1 in Hx. assumption. }
  assert (HxE : x `notin` dom E).
  { apply notin_union_2 in Hx. apply notin_union_1 in Hx. assumption. }
  assert (Hxfv : x `notin` SubstEE__fv_exp e1).
  { apply notin_union_2 in Hx. apply notin_union_2 in Hx. assumption. }
  assert (HvV : typing E R v2 V)
    by (apply (typing_sub T1 E R v2 V Hws Hv2ty Hcontra)).
  assert (Hbodyx : typing (x ~ bind_typ V ++ E) R (open_ee e1 x) Tbody)
    by (apply Hbody; assumption).
  exists Tbody. split.
  - exact (SubstEE__typing_subst_ee0_open E x V R e1 Tbody v2 HxE Hxfv Hval2 HvV Hbodyx).
  - exact Hco.
Qed.

(* Beta for type abstraction. *)
Lemma PresHelpers__typing_tabs_beta : forall E R V e1 T1 T2 Varg,
  typing E R (exp_tabs V e1) (typ_all T1 T2) ->
  wf_typ E Varg ->
  sub E Varg T1 ->
  exists Tbody,
    typing E R (open_te e1 Varg) Tbody /\
    sub E Tbody (open_tt T2 Varg).
Proof.
  intros E R V e1 T1 T2 Varg Hty HwVarg HsubArg.
  assert (HWf : wf_typ E (typ_all T1 T2))
    by (apply (SubstTT__typing_wf_typ E R (exp_tabs V e1) (typ_all T1 T2)); assumption).
  assert (HE : wf_env E) by (apply (Dev__wf_sig_wf_env E R);
    apply (Store__typing_wf_sig_mut E R (exp_tabs V e1) (typ_all T1 T2)); assumption).
  destruct (TypingInv__typing_tabs_inv E R V e1 (typ_all T1 T2) Hty HE HWf)
    as [Tbody [L [Hs Hbody]]].
  assert (HWS : wf_typ E (typ_all V Tbody))
    by (apply (Dev__sub_wf_source E (typ_all V Tbody) (typ_all T1 T2)); assumption).
  destruct (AllComp__sub_all_all E V Tbody T1 T2 HE HWS HWf Hs)
    as [HwT1 [HsubT1V [La Hbodyrel]]].
  destruct (Dev__wf_typ_inv_all E T1 T2 HWf) as [Lw [HwT1' HwT2body]].
  assert (HsubArgV : sub E Varg V)
    by (eapply sub_trans; [exact HsubArg | exact HsubT1V]).
  destruct (atom_fresh
    (La `union` (L `union` (Lw `union` (dom E `union` (SubstTT__fv_te e1 `union`
      (Dev__fv_typ Tbody `union` (Dev__fv_typ T2 `union` SubstTT__fv_sig R))))))))
    as [X HX].
  assert (HX1 : X `notin` (L `union` (Lw `union` (dom E `union` (SubstTT__fv_te e1 `union`
      (Dev__fv_typ Tbody `union` (Dev__fv_typ T2 `union` SubstTT__fv_sig R)))))))
    by (apply notin_union_2 in HX; exact HX).
  assert (HX2 : X `notin` (Lw `union` (dom E `union` (SubstTT__fv_te e1 `union`
      (Dev__fv_typ Tbody `union` (Dev__fv_typ T2 `union` SubstTT__fv_sig R))))))
    by (apply notin_union_2 in HX1; exact HX1).
  assert (HX3 : X `notin` (dom E `union` (SubstTT__fv_te e1 `union`
      (Dev__fv_typ Tbody `union` (Dev__fv_typ T2 `union` SubstTT__fv_sig R)))))
    by (apply notin_union_2 in HX2; exact HX2).
  assert (HX4 : X `notin` (SubstTT__fv_te e1 `union`
      (Dev__fv_typ Tbody `union` (Dev__fv_typ T2 `union` SubstTT__fv_sig R))))
    by (apply notin_union_2 in HX3; exact HX3).
  assert (HX5 : X `notin` (Dev__fv_typ Tbody `union` (Dev__fv_typ T2 `union` SubstTT__fv_sig R)))
    by (apply notin_union_2 in HX4; exact HX4).
  assert (HX6 : X `notin` (Dev__fv_typ T2 `union` SubstTT__fv_sig R))
    by (apply notin_union_2 in HX5; exact HX5).
  assert (HXsig : X `notin` SubstTT__fv_sig R)
    by (apply notin_union_2 in HX6; exact HX6).
  assert (HXt2 : X `notin` Dev__fv_typ T2)
    by (apply notin_union_1 in HX6; exact HX6).
  assert (HXtb : X `notin` Dev__fv_typ Tbody)
    by (apply notin_union_1 in HX5; exact HX5).
  assert (HXte : X `notin` SubstTT__fv_te e1)
    by (apply notin_union_1 in HX4; exact HX4).
  assert (HXE : X `notin` dom E)
    by (apply notin_union_1 in HX3; exact HX3).
  assert (HXw : X `notin` Lw)
    by (apply notin_union_1 in HX2; exact HX2).
  assert (HXL : X `notin` L)
    by (apply notin_union_1 in HX1; exact HX1).
  assert (HXLa : X `notin` La)
    by (apply notin_union_1 in HX; exact HX).
  assert (HbodyX : typing (X ~ bind_sub V ++ E) R (open_te e1 X)
                    (open_tt Tbody X))
    by (apply Hbody; assumption).
  assert (HbodyrelX : sub (X ~ bind_sub T1 ++ E) (open_tt Tbody X)
                        (open_tt T2 X))
    by (apply Hbodyrel; assumption).
  assert (HwT2X : wf_typ (X ~ bind_sub T1 ++ E) (open_tt T2 X))
    by (apply HwT2body; assumption).
  assert (HwEnvT1 : wf_env (X ~ bind_sub T1 ++ E)).
  { apply (wf_env_sub E X T1); assumption. }
  assert (HwSrcT1 : wf_typ (X ~ bind_sub T1 ++ E) (open_tt Tbody X))
    by (apply (Dev__sub_wf_source (X ~ bind_sub T1 ++ E)
               (open_tt Tbody X) (open_tt T2 X)); assumption).
  assert (HrelSubst :
    sub E (SubstTT__subst_tt X Varg (open_tt Tbody X))
          (SubstTT__subst_tt X Varg (open_tt T2 X))).
  { apply (SubstTT__sub_subst_tt E X T1 Varg (open_tt Tbody X) (open_tt T2 X)).
    - exact HwVarg.
    - exact HwEnvT1.
    - exact HsubArg.
    - exact HwSrcT1.
    - exact HbodyrelX. }
  rewrite <- (SubstTT__open_tt_subst_tt Tbody X Varg HXtb) in HrelSubst.
  rewrite <- (SubstTT__open_tt_subst_tt T2 X Varg HXt2) in HrelSubst.
  assert (HbodySubst : typing E R (open_te e1 Varg) (open_tt Tbody Varg)).
  { apply (SubstTT__typing_subst_tt_open E R X V Varg e1 Tbody).
    - exact HXte.
    - exact HXtb.
    - exact HXsig.
    - exact HwVarg.
    - exact HsubArgV.
    - exact HbodyX. }
  exists (open_tt Tbody Varg). split; assumption.
Qed.

(* If [e] is typed at [S] and [readonly S <: T], then [e] is typed at [T]. *)
Lemma PresHelpers__typing_seal_inner_result : forall E R e S T,
  typing E R e S ->
  sub E (typ_mut mut_readonly S) T ->
  typing E R e T.
Proof.
  intros E R e S T Hty Hsub.
  assert (Hws : wf_sig E R) by (apply (Store__typing_wf_sig_mut E R e S); assumption).
  apply (typing_sub (typ_mut mut_readonly S) E R e T Hws).
  - apply (Helpers__typing_readonly_wrap E R e S); assumption.
  - exact Hsub.
Qed.

(* If [v : T0] and [T0 <: S], then [v : readonly S]. *)
Lemma PresHelpers__typing_value_at_readonly : forall E R v T0 S,
  typing E R v T0 ->
  sub E T0 S ->
  typing E R v (typ_mut mut_readonly S).
Proof.
  intros E R v T0 S Hty Hsub.
  assert (Hws : wf_sig E R) by (apply (Store__typing_wf_sig_mut E R v T0); assumption).
  apply (typing_sub T0 E R v (typ_mut mut_readonly S) Hws Hty).
  apply sub_readonly_mutable. exact Hsub.
Qed.

(* The final result for unboxing a plain reference at a readonly box type. *)
Lemma PresHelpers__typing_value_readonly_result : forall E R v T0 S T,
  typing E R v T0 ->
  sub E T0 S ->
  sub E (typ_mut mut_readonly S) T ->
  typing E R v T.
Proof.
  intros E R v T0 S T Hty Hsub0 HsubRO.
  assert (Hws : wf_sig E R) by (apply (Store__typing_wf_sig_mut E R v T0); assumption).
  apply (typing_sub (typ_mut mut_readonly S) E R v T Hws).
  - apply (PresHelpers__typing_value_at_readonly E R v T0 S); assumption.
  - exact HsubRO.
Qed.

(* Sealing a value of type T0, when T0 <: S, produces a value of readonly S. *)
Lemma PresHelpers__typing_seal_value_at_readonly : forall E R v T0 S,
  typing E R v T0 ->
  sub E T0 S ->
  typing E R (exp_seal v) (typ_mut mut_readonly S).
Proof.
  intros E R v T0 S Hty Hsub.
  assert (Hws : wf_sig E R) by (apply (Store__typing_wf_sig_mut E R v T0); assumption).
  apply (typing_sub (typ_mut mut_readonly T0) E R (exp_seal v)
           (typ_mut mut_readonly S) Hws).
  - apply typing_seal. exact Hty.
  - apply sub_readonly. exact Hsub.
Qed.




(* ================================================================== *)
(* Auxiliary inversion lemmas not provided by the imported modules.   *)
(* ================================================================== *)

(* Shape-directed inversion for [exp_tapp], analogous to
   TypingInv__typing_app_inv. *)
Lemma typing_tapp_inv_local : forall E R e Targ T,
  typing E R (exp_tapp e Targ) T ->
  wf_env E -> wf_typ E T ->
  exists A B, typing E R e (typ_all A B) /\
    sub E Targ A /\ sub E (open_tt B Targ) T.
Proof.
  intros E R e Targ T H. remember (exp_tapp e Targ) as e0 eqn:He.
  revert He.
  induction H as [ E0 R0 x T0 Hwe Hws Hb
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targb T2 Hws H1 IH1 Hsub
                 | S E0 R0 e0 T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e0 T0 Hws H1 IH1
                 | E0 R0 e0 T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 l T0 Hwe Hws Hb
                 | E0 R0 e0 T0 H1 IH1
                 | E0 R0 e0 T0 H1 IH1
                 | E0 R0 r T0 Hr IHr
                 | E0 R0 e0 a T0 H1 IH1
                 | E0 R0 e0 a T0 H1 IH1
                 | E0 R0 e1b a e2b T0 H1 IH1 H2 IH2 ];
  intros He HE Ht; try discriminate.
  - (* typing_tapp *)
    injection He as Hx Hy. subst e1b Targb.
    exists T1, T2. split; [assumption|split; [assumption|]].
    apply (Dev__sub_refl E0 (open_tt T2 Targ) HE Ht).
  - (* typing_sub *)
    destruct (IH1 He HE (WfTyping__typing_wf_typ E0 R0 e0 S H1))
      as [A [B [HA [Hsub1 Hsub2]]]].
    exists A, B. split; [assumption|split; [assumption|]].
    eapply sub_trans; eauto.
Qed.

(* Inversion for [exp_unbox (exp_seal (exp_ref l))]: the only usable
   typing is the readonly-box one, and the store binding type is
   related to the result through a readonly type. *)
Lemma typing_unbox_sealed_ref_inv_local : forall E R l T,
  typing E R (exp_unbox (exp_seal (exp_ref l))) T ->
  exists T0, Signatures.binds l (bind_sig T0) R /\
    sub E (typ_mut mut_readonly T0) T.
Proof.
  intros E R l T H. remember (exp_unbox (exp_seal (exp_ref l))) as e0 eqn:He.
  revert l He.
  induction H as [ E0 R0 x T0 Hwe Hws Hb
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b e2b T2 Hws H1 IH1 H2 IH2
                 | L E0 R0 V e1b T1 Hws Hbody IHbody
                 | T1 E0 R0 e1b Targb T2 Hws H1 IH1 Hsub
                 | S E0 R0 e0 T0 Hws H1 IH1 Hsub
                 | L T1 T2 e1b e2b E0 R0 Hws H1 IH1 Hbody IHbody2
                 | E0 R0 e0 T0 Hws H1 IH1
                 | E0 R0 e0 T0 Hws H1 IH1
                 | E0 R0 e1b e2b T0 Hws H1 IH1 H2 IH2
                 | E0 R0 lb T0 Hwe Hws Hb
                 | E0 R0 e0 T0 H1 IH1
                 | E0 R0 e0 T0 H1 IH1
                 | E0 R0 r T0 Hr IHr
                 | E0 R0 e0 a T0 H1 IH1
                 | E0 R0 e0 a T0 H1 IH1
                 | E0 R0 e1b a e2b T0 H1 IH1 H2 IH2 ];
  intros l0 He; try discriminate.
  - (* typing_sub *)
    destruct (IH1 l0 He) as [Tb [Hb Hsubb]].
    exists Tb. split; [assumption|]. eapply sub_trans; eauto.
  - (* typing_unbox: impossible *)
    injection He as He1. subst e0.
    assert (Hws0 : wf_sig E0 R0) by (eapply Store__typing_wf_sig_mut; eauto).
    assert (HE : wf_env E0) by (apply (Dev__wf_sig_wf_env E0 R0 Hws0)).
    assert (HWT : wf_typ E0 (typ_box T0))
      by (apply (WfTyping__typing_wf_typ E0 R0 (exp_seal (exp_ref l0)) (typ_box T0) H1)).
    destruct (TypingInv__typing_seal_inv E0 R0 (exp_ref l0) (typ_box T0) H1 HE HWT)
      as [S0 [_ Hss]].
    exfalso. exact (Readonly__sub_readonly_box_false E0 S0 T0 Hss).
  - (* typing_unbox_readonly *)
    injection He as He1. subst e0.
    assert (Hws0 : wf_sig E0 R0) by (eapply Store__typing_wf_sig_mut; eauto).
    assert (HE : wf_env E0) by (apply (Dev__wf_sig_wf_env E0 R0 Hws0)).
    assert (HWT : wf_typ E0 (typ_mut mut_readonly (typ_box T0)))
      by (apply (WfTyping__typing_wf_typ E0 R0 (exp_seal (exp_ref l0))
                   (typ_mut mut_readonly (typ_box T0)) H1)).
    assert (HWTb : wf_typ E0 (typ_box T0))
      by (apply (Dev__wf_typ_inv_readonly E0 mut_readonly (typ_box T0) HWT)).
    assert (HWT0 : wf_typ E0 T0) by (apply (Dev__wf_typ_inv_box E0 T0 HWTb)).
    destruct (TypingInv__typing_seal_inv E0 R0 (exp_ref l0)
                (typ_mut mut_readonly (typ_box T0)) H1 HE HWT)
      as [S0 [Htyref Hsubseal]].
    destruct (MyWork__typing_ref_inv E0 R0 l0 S0 Htyref)
      as [Tb [Hb Hsubbox]].
    assert (Hsubr : sub E0 (typ_mut mut_readonly (typ_box Tb))
                            (typ_mut mut_readonly (typ_box T0)))
      by (eapply sub_trans; [apply sub_readonly; exact Hsubbox | exact Hsubseal]).
    assert (Hwsrc : wf_typ E0 (typ_mut mut_readonly (typ_box Tb)))
      by (apply (Dev__sub_wf_source E0 _ _ HE HWT Hsubr)).
    destruct (MyWork__sub_boxcomp E0
                (typ_mut mut_readonly (typ_box Tb))
                (typ_mut mut_readonly (typ_box T0)) HE Hwsrc Hsubr T0 HWT0
                (MyWork__box_comp_mut mut_readonly (typ_box T0) T0
                   (MyWork__box_comp_box T0)))
      as [A' [HA' [Hac' [Hlt Hgt]]]].
    assert (Hac'' : MyWork__BoxComp (typ_box Tb) A')
      by (exact (MyWork__BoxComp_mut_inv mut_readonly (typ_box Tb) A' Hac')).
    assert (Heq : A' = Tb)
      by (exact (MyWork__BoxComp_box_inv Tb A' Hac'')).
    subst A'.
    exists Tb. split; [exact Hb |].
    (* goal: sub E0 (readonly Tb) (readonly T0), obtained by sub_readonly
       from Hlt : sub E0 Tb T0 *)
    apply sub_readonly. exact Hgt.
Qed.

(* A stored value can be retyped at its signature binding type. *)
Lemma typing_store_value : forall E R s l v T,
  wf_sig E R ->
  typing_store E R s ->
  Signatures.binds l (bind_sig T) R ->
  LabelMapImpl.MapsTo l v s ->
  typing E R v T.
Proof.
  intros E R s l v T Hws Hst Hb HM.
  destruct (Hst l) as [Hf Hg].
  destruct (Hg v HM) as [T0 [Hval [Hty0 Hb0]]].
  assert (Heq : T0 = T)
    by (eapply Store__wf_sig_binds_uniq; eauto).
  subst T0. exact Hty0.
Qed.

(* Inversions of record-component typings. *)
Lemma typing_record_comp_exp_inv : forall E R a e r T,
  typing_record_comp E R (rec_exp a e r) T ->
  exists T1 Tr, a `notin` record_dom r /\ typing_record_comp E R r Tr /\
    typing E R e T1 /\ T = typ_int (typ_record a T1) Tr.
Proof.
  intros E R a e r T H. inversion H; subst.
  eexists; eexists; repeat split; eauto.
Qed.

Lemma typing_record_comp_ref_inv : forall E R a l r T,
  typing_record_comp E R (rec_ref a l r) T ->
  exists T1 Tr, a `notin` record_dom r /\ typing_record_comp E R r Tr /\
    Signatures.binds l (bind_sig T1) R /\ T = typ_int (typ_record a T1) Tr.
Proof.
  intros E R a l r T H. inversion H; subst.
  eexists; eexists; repeat split; eauto.
Qed.

(* Bundled well-formedness facts for expression and record typings. *)
Lemma typing_ctx_facts : forall E R e T,
  typing E R e T -> wf_env E /\ wf_sig E R /\ wf_typ E T.
Proof.
  intros E R e T H.
  assert (Hws : wf_sig E R) by (eapply Store__typing_wf_sig_mut; exact H).
  split.
  - apply (Dev__wf_sig_wf_env E R Hws).
  - split; [exact Hws | exact (WfTyping__typing_wf_typ E R e T H)].
Qed.

Lemma record_ctx_facts : forall E R r T,
  typing_record_comp E R r T -> wf_env E /\ wf_sig E R /\ wf_typ E T.
Proof.
  intros E R r T H.
  assert (Hws : wf_sig E R) by (apply (MyWork__typing_record_comp_wf_sig E R r T); exact H).
  split.
  - apply (Dev__wf_sig_wf_env E R Hws).
  - split; [exact Hws | apply (WfTyping__typing_record_comp_wf_typ E R r T); exact H].
Qed.

(* Signature bindings survive extension of the signature by a prefix. *)
Lemma binds_sig_weaken_prefix : forall (R R' : sig) (l : label) (T : typ),
  Signatures.binds l (bind_sig T) R ->
  Signatures.binds l (bind_sig T) (R' ++ R).
Proof.
  intros R R' l T H.
  exact (Signatures.binds_weaken signature l (bind_sig T) sempty R' R H).
Qed.

(* The head binding of [l ~ bind_sig T ++ R] is [l]. *)
Lemma binds_sig_head : forall (R : sig) (l : label) (T : typ),
  Signatures.binds l (bind_sig T) (l ~ bind_sig T ++ R).
Proof.
  intros R l T.
  apply (Signatures.binds_cons_iff signature l l (bind_sig T) (bind_sig T) R).
  left. split; reflexivity.
Qed.

(* Reduction of a record component preserves its exported domain. *)
Lemma record_dom_red_comp : forall r s r' s',
  red_record_comp r s r' s' -> record_dom r = record_dom r'.
Proof.
  intros r s r' s' H. induction H.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHred_record_comp. reflexivity.
Qed.

(* ================================================================== *)
(* Preservation.                                                      *)
(* ================================================================== *)

Theorem preservation : forall E R e s e' s' T,
  typing E R e T ->
  typing_store E R s ->
  red e s e' s' ->
  exists R', wf_sig E (R' ++ R) /\
    typing E (R' ++ R) e' T /\
    typing_store E (R' ++ R) s'
with preservation_record : forall E R r s r' s' T,
  typing_record_comp E R r T ->
  typing_store E R s ->
  red_record_comp r s r' s' ->
  exists R', wf_sig E (R' ++ R) /\
    typing_record_comp E (R' ++ R) r' T /\
    typing_store E (R' ++ R) s'.
Proof.
  - (* preservation *)
    intros E R e s e' s' T Hty Hst Hred.
    revert E R T Hty Hst.
    induction Hred as
      [ e1 e1' s1 s1' e2 Hexpr Hred1 IH1
      | e1 e2 s2 e2' s2' Hval1 Hred2 IH2
      | e1 e1' s1 s1' V Htype Hred1 IH1
      | Vabs e1 s1 v2 Hwf Hexpr Hval2
      | Vtabs e1 s1 Targ Hwf Hexpr Htype
      | e1 e1' s1 s1' e2 Hred1 IH1 Hbody
      | v1 e2 s2 Hwf Hval1 Hbody
      | e1 e1' s1 s1' Hred1 IH1
      | v1 l s1 Hwf Hval1 Hfresh
      | e1 e1' s1 s1' Hred1 IH1
      | l v1 s1 Hwf Hval1 Hmaps
      | l v1 s1 Hwf Hval1 Hmaps
      | e1 s1 e1' s1' e2 Hexpr Hred1 IH1
      | v1 e2 s2 e2' s2' Hval1 Hred2 IH2
      | l v1 v2 s1 Hwf Hval1 Hval2 Hmaps
      | e1 s1 e1' s1' Hred1 IH1
      | Vabs e1 s1 Hwf Hexpr
      | Vtabs e1 s1 Hwf Hexpr
      | l s1 Hwf
      | r s1 Hwf Hvalrec
      | r1 s1 r1' s1' Hredrc
      | a e1 e1' s1 s1' Hred1 IH1
      | r a l v1 s1 Hwf Hvalrec Hlook Hval1 Hmaps
      | r a l v1 s1 Hwf Hvalrec Hlook Hval1 Hmaps
      | a e1 s1 e1' s1' e2 Hexpr Hred1 IH1
      | a v1 e2 s2 e2' s2' Hval1 Hred2 IH2
      | a l r v1 v2 s1 Hwf Hvalrec Hlook Hval1 Hval2 Hmaps ] using red_ind;
      intros E R Tgoal Hty Hst.

    + (* red_app_1 *)
      destruct (typing_ctx_facts E R (exp_app e1 e2) Tgoal Hty) as [HE [Hws HWT]].
      destruct (TypingInv__typing_app_inv E R e1 e2 Tgoal Hty HE HWT)
        as [A [B [Hty1 [Hty2 Hsub]]]].
      destruct (IH1 E R (typ_arrow A B) Hty1 Hst) as [R' [Hws' [Hty1' Hst']]].
      exists R'. split; [exact Hws' | split].
      * eapply typing_sub.
        -- exact Hws'.
        -- eapply typing_app.
           ++ exact Hws'.
           ++ exact Hty1'.
           ++ exact (Store__typing_sig_weaken E R e2 A Hty2 R' Hws').
        -- exact Hsub.
      * exact Hst'.

    + (* red_app_2 *)
      destruct (typing_ctx_facts E R (exp_app e1 e2) Tgoal Hty) as [HE [Hws HWT]].
      destruct (TypingInv__typing_app_inv E R e1 e2 Tgoal Hty HE HWT)
        as [A [B [Hty1 [Hty2 Hsub]]]].
      destruct (IH2 E R A Hty2 Hst) as [R' [Hws' [Hty2' Hst']]].
      exists R'. split; [exact Hws' | split].
      * eapply typing_sub.
        -- exact Hws'.
        -- eapply typing_app.
           ++ exact Hws'.
           ++ exact (Store__typing_sig_weaken E R e1 (typ_arrow A B) Hty1 R' Hws').
           ++ exact Hty2'.
        -- exact Hsub.
      * exact Hst'.

    + (* red_tapp *)
      destruct (typing_ctx_facts E R (exp_tapp e1 V) Tgoal Hty) as [HE [Hws HWT]].
      destruct (typing_tapp_inv_local E R e1 V Tgoal Hty HE HWT)
        as [A [B [HtyAll [HsubArg HsubRes]]]].
      destruct (IH1 E R (typ_all A B) HtyAll Hst) as [R' [Hws' [HtyAll' Hst']]].
      exists R'. split; [exact Hws' | split].
      * eapply typing_sub.
        -- exact Hws'.
        -- eapply typing_tapp.
           ++ exact Hws'.
           ++ exact HtyAll'.
           ++ exact HsubArg.
        -- exact HsubRes.
      * exact Hst'.

    + (* red_abs *)
      destruct (typing_ctx_facts E R (exp_app (exp_abs Vabs e1) v2) Tgoal Hty)
        as [HE [Hws HWT]].
      destruct (TypingInv__typing_app_inv E R (exp_abs Vabs e1) v2 Tgoal Hty HE HWT)
        as [A [B [HtyAbs [Htyv2 Hsub]]]].
      destruct (PresHelpers__typing_abs_beta E R Vabs e1 A B v2 HtyAbs Htyv2 Hval2)
        as [Tbody [Htybody Hsubbody]].
      exists sempty. simpl. split; [exact Hws | split].
      * eapply typing_sub.
        -- exact Hws.
        -- exact Htybody.
        -- eapply sub_trans; [exact Hsubbody | exact Hsub].
      * exact Hst.

    + (* red_tabs *)
      destruct (typing_ctx_facts E R (exp_tapp (exp_tabs Vtabs e1) Targ) Tgoal Hty)
        as [HE [Hws HWT]].
      destruct (typing_tapp_inv_local E R (exp_tabs Vtabs e1) Targ Tgoal Hty HE HWT)
        as [A [B [HtyTabs [HsubArg HsubRes]]]].
      assert (HWA : wf_typ E A).
      { destruct (Dev__wf_typ_inv_all E A B
                    (WfTyping__typing_wf_typ E R (exp_tabs Vtabs e1) (typ_all A B) HtyTabs))
          as [L0 [HWA _]]. exact HWA. }
      assert (HWTarg : wf_typ E Targ)
        by (apply (Dev__sub_wf_source E Targ A HE HWA HsubArg)).
      destruct (PresHelpers__typing_tabs_beta E R Vtabs e1 A B Targ HtyTabs HWTarg HsubArg)
        as [Tbody [Htybody Hsubbody]].
      exists sempty. simpl. split; [exact Hws | split].
      * eapply typing_sub.
        -- exact Hws.
        -- exact Htybody.
        -- eapply sub_trans; [exact Hsubbody | exact HsubRes].
      * exact Hst.

    + (* red_let_1 *)
      destruct (typing_ctx_facts E R (exp_let e1 e2) Tgoal Hty) as [HE [Hws HWT]].
      destruct (TypingInv__typing_let_inv E R e1 e2 Tgoal Hty HE HWT)
        as [T1 [T2 [L [Hty1 [Hbodyty Hsub]]]]].
      destruct (IH1 E R T1 Hty1 Hst) as [R' [Hws' [Hty1' Hst']]].
      assert (HWT1 : wf_typ E T1)
        by (apply (WfTyping__typing_wf_typ E R e1 T1); exact Hty1).
      exists R'. split; [exact Hws' | split].
      * eapply typing_sub.
        -- exact Hws'.
        -- eapply (typing_let (L `union` dom E) T1 T2 e1' e2 E (R'++R) Hws' Hty1').
           intros x Hx.
           assert (HxL : x `notin` L)
             by (exact (notin_union_1 x L (dom E) Hx)).
           assert (Hxdom : x `notin` dom E)
             by (exact (notin_union_2 x L (dom E) Hx)).
           assert (Hwe : wf_env (x ~ bind_typ T1 ++ E))
             by (apply (wf_env_typ E x T1 HE HWT1 Hxdom)).
           assert (Hwsx : wf_sig (x ~ bind_typ T1 ++ E) (R'++R))
             by (apply (Store__wf_sig_env_weaken_cons E (R'++R) x (bind_typ T1) Hws' Hwe)).
           exact (Store__typing_sig_weaken (x ~ bind_typ T1 ++ E) R (open_ee e2 x) T2
                    (Hbodyty x HxL) R' Hwsx).
        -- exact Hsub.
      * exact Hst'.

    + (* red_let *)
      destruct (typing_ctx_facts E R (exp_let v1 e2) Tgoal Hty) as [HE [Hws HWT]].
      destruct (TypingInv__typing_let_inv E R v1 e2 Tgoal Hty HE HWT)
        as [T1 [T2 [L [Htyv1 [Hbodyty Hsub]]]]].
      destruct (atom_fresh ((L `union` dom E) `union` SubstEE__fv_exp e2)) as [x Hx].
      assert (HxLdom : x `notin` (L `union` dom E))
        by (exact (notin_union_1 x (L `union` dom E) (SubstEE__fv_exp e2) Hx)).
      assert (Hxfv : x `notin` SubstEE__fv_exp e2)
        by (exact (notin_union_2 x (L `union` dom E) (SubstEE__fv_exp e2) Hx)).
      assert (HxL : x `notin` L)
        by (exact (notin_union_1 x L (dom E) HxLdom)).
      assert (Hxdom : x `notin` dom E)
        by (exact (notin_union_2 x L (dom E) HxLdom)).
      assert (Hbodyx : typing (x ~ bind_typ T1 ++ E) R (open_ee e2 x) T2)
        by (apply Hbodyty; exact HxL).
      assert (Htyopen : typing E R (open_ee e2 v1) T2)
        by (exact (SubstEE__typing_subst_ee0_open E x T1 R e2 T2 v1 Hxdom Hxfv Hval1 Htyv1 Hbodyx)).
      exists sempty. simpl. split; [exact Hws | split].
      * eapply typing_sub.
        -- exact Hws.
        -- exact Htyopen.
        -- exact Hsub.
      * exact Hst.

    + (* red_box_1 *)
      destruct (typing_ctx_facts E R (exp_box e1) Tgoal Hty) as [HE [Hws HWT]].
      destruct (TypingInv__typing_box_inv E R e1 Tgoal Hty HE HWT) as [S [Hty1 Hsub]].
      destruct (IH1 E R S Hty1 Hst) as [R' [Hws' [Hty1' Hst']]].
      exists R'. split; [exact Hws' | split].
      * eapply typing_sub.
        -- exact Hws'.
        -- eapply typing_box; [exact Hws' | exact Hty1'].
        -- exact Hsub.
      * exact Hst'.

    + (* red_box_ref *)
      destruct (typing_ctx_facts E R (exp_box v1) Tgoal Hty) as [HE [Hws HWT]].
      destruct (TypingInv__typing_box_inv E R v1 Tgoal Hty HE HWT) as [S [Hty1 Hsub]].
      assert (HWS : wf_typ E S)
        by (apply (WfTyping__typing_wf_typ E R v1 S); exact Hty1).
      assert (Hnotmaps : forall v0 : exp, ~ LabelMapImpl.MapsTo l v0 s1).
      { intros v0 HM. exact (Store__fresh_label_not_maps s1 l v0 (eq_sym Hfresh) HM). }
      assert (Hnotdom : LabelSetImpl.notin l (Signatures.dom R)).
      { apply (Store__fresh_label_notin_sig_dom E R s1 l Hst Hfresh). }
      assert (Hws' : wf_sig E (l ~ bind_sig S ++ R))
        by (apply (wf_sig_typ E R l S Hws HWS Hnotdom)).
      exists (l ~ bind_sig S). split; [exact Hws' | split].
      * eapply typing_sub.
        -- exact Hws'.
        -- apply (typing_ref E (l ~ bind_sig S ++ R) l S HE Hws').
           exact (binds_sig_head R l S).
        -- exact Hsub.
      * exact (Store__typing_store_add E R s1 l v1 S HWS Hst Hnotmaps Hty1 Hval1).

    + (* red_unbox_1 *)
      destruct (typing_ctx_facts E R (exp_unbox e1) Tgoal Hty) as [HE [Hws HWT]].
      destruct (TypingInv__typing_unbox_inv E R e1 Tgoal Hty HE HWT)
        as [[S [Hty1 Hsub]] | [S [Hty1 Hsub]]].
      * destruct (IH1 E R (typ_box S) Hty1 Hst) as [R' [Hws' [Hty1' Hst']]].
        exists R'. split; [exact Hws' | split].
        -- eapply typing_sub.
           ++ exact Hws'.
           ++ eapply typing_unbox; [exact Hws' | exact Hty1'].
           ++ exact Hsub.
        -- exact Hst'.
      * destruct (IH1 E R (typ_mut mut_readonly (typ_box S)) Hty1 Hst)
          as [R' [Hws' [Hty1' Hst']]].
        exists R'. split; [exact Hws' | split].
        -- eapply typing_sub.
           ++ exact Hws'.
           ++ eapply typing_unbox_readonly; [exact Hty1'].
           ++ exact Hsub.
        -- exact Hst'.

    + (* red_unbox_ref *)
      destruct (typing_ctx_facts E R (exp_unbox (exp_ref l)) Tgoal Hty) as [HE [Hws HWT]].
      destruct (TypingInv__typing_unbox_inv E R (exp_ref l) Tgoal Hty HE HWT)
        as [[S [HtyRef Hsub]] | [S [HtyRef Hsub]]].
      * destruct (MyWork__typing_ref_inv E R l (typ_box S) HtyRef) as [T0 [Hb HsubBox]].
        assert (HWT0 : wf_typ E T0) by (apply (Store__wf_sig_binds E R l T0 Hws Hb)).
        assert (HWTbox0 : wf_typ E (typ_box T0)) by (apply (wf_typ_box E T0 HWT0)).
        assert (HWTboxS : wf_typ E (typ_box S))
          by (apply (WfTyping__typing_wf_typ E R (exp_ref l) (typ_box S)); exact HtyRef).
        destruct (MyWork__sub_box_box E T0 S HE HWTbox0 HWTboxS HsubBox) as [HsubT0S _].
        assert (Htyv1 : typing E R v1 T0)
          by (exact (typing_store_value E R s1 l v1 T0 Hws Hst Hb Hmaps)).
        assert (Htyv1S : typing E R v1 S)
          by (exact (typing_sub T0 E R v1 S Hws Htyv1 HsubT0S)).
        exists sempty. simpl. split; [exact Hws | split].
        -- eapply typing_sub.
           ++ exact Hws.
           ++ exact Htyv1S.
           ++ exact Hsub.
        -- exact Hst.
      * destruct (MyWork__typing_ref_inv E R l (typ_mut mut_readonly (typ_box S)) HtyRef) as [T0 [Hb HsubBoxRO]].
        assert (HWT0 : wf_typ E T0) by (apply (Store__wf_sig_binds E R l T0 Hws Hb)).
        assert (HWTbox0 : wf_typ E (typ_box T0)) by (apply (wf_typ_box E T0 HWT0)).
        assert (HWTRO : wf_typ E (typ_mut mut_readonly (typ_box S)))
          by (apply (WfTyping__typing_wf_typ E R (exp_ref l)
                       (typ_mut mut_readonly (typ_box S))); exact HtyRef).
        assert (HWSbox : wf_typ E (typ_box S))
          by (apply (Dev__wf_typ_inv_readonly E mut_readonly (typ_box S) HWTRO)).
        assert (HWS : wf_typ E S) by (apply (Dev__wf_typ_inv_box E S HWSbox)).
        destruct (MyWork__sub_boxcomp E (typ_box T0) (typ_mut mut_readonly (typ_box S))
                    HE HWTbox0 HsubBoxRO S HWS
                    (MyWork__box_comp_mut mut_readonly (typ_box S) S (MyWork__box_comp_box S)))
          as [A' [HA' [Hac [Hlt Hgt]]]].
        assert (Heq : A' = T0) by (exact (MyWork__BoxComp_box_inv T0 A' Hac)).
        subst A'.
        assert (HsubT0S : sub E T0 S) by exact Hgt.
        assert (Htyv1 : typing E R v1 T0)
          by (exact (typing_store_value E R s1 l v1 T0 Hws Hst Hb Hmaps)).
        exists sempty. simpl. split; [exact Hws | split].
        -- exact (PresHelpers__typing_value_readonly_result E R v1 T0 S Tgoal
                    Htyv1 HsubT0S Hsub).
        -- exact Hst.

    + (* red_unbox_sealed_ref *)
      destruct (typing_ctx_facts E R (exp_unbox (exp_seal (exp_ref l))) Tgoal Hty)
        as [HE [Hws HWT]].
      destruct (typing_unbox_sealed_ref_inv_local E R l Tgoal Hty) as [T0 [Hb Hsub]].
      assert (HWT0 : wf_typ E T0) by (apply (Store__wf_sig_binds E R l T0 Hws Hb)).
      assert (Htyv1 : typing E R v1 T0)
        by (exact (typing_store_value E R s1 l v1 T0 Hws Hst Hb Hmaps)).
      assert (Htyseal : typing E R (exp_seal v1) (typ_mut mut_readonly T0))
        by (exact (PresHelpers__typing_seal_value_at_readonly E R v1 T0 T0
                     Htyv1 (Dev__sub_refl E T0 HE HWT0))).
      exists sempty. simpl. split; [exact Hws | split].
      * eapply typing_sub.
        -- exact Hws.
        -- exact Htyseal.
        -- exact Hsub.
      * exact Hst.

    + (* red_set_box_1 *)
      destruct (typing_ctx_facts E R (exp_set_box e1 e2) Tgoal Hty) as [HE [Hws HWT]].
      destruct (TypingInv__typing_set_box_inv E R e1 e2 Tgoal Hty HE HWT)
        as [S [Hty1 [Hty2 Hsub]]].
      destruct (IH1 E R (typ_box S) Hty1 Hst) as [R' [Hws' [Hty1' Hst']]].
      exists R'. split; [exact Hws' | split].
      * eapply typing_sub.
        -- exact Hws'.
        -- eapply typing_set_box.
           ++ exact Hws'.
           ++ exact Hty1'.
           ++ exact (Store__typing_sig_weaken E R e2 S Hty2 R' Hws').
        -- exact Hsub.
      * exact Hst'.

    + (* red_set_box_2 *)
      destruct (typing_ctx_facts E R (exp_set_box v1 e2) Tgoal Hty) as [HE [Hws HWT]].
      destruct (TypingInv__typing_set_box_inv E R v1 e2 Tgoal Hty HE HWT)
        as [S [Hty1 [Hty2 Hsub]]].
      destruct (IH2 E R S Hty2 Hst) as [R' [Hws' [Hty2' Hst']]].
      exists R'. split; [exact Hws' | split].
      * eapply typing_sub.
        -- exact Hws'.
        -- eapply typing_set_box.
           ++ exact Hws'.
           ++ exact (Store__typing_sig_weaken E R v1 (typ_box S) Hty1 R' Hws').
           ++ exact Hty2'.
        -- exact Hsub.
      * exact Hst'.

    + (* red_set_box_ref *)
      destruct (typing_ctx_facts E R (exp_set_box (exp_ref l) v2) Tgoal Hty)
        as [HE [Hws HWT]].
      destruct (TypingInv__typing_set_box_inv E R (exp_ref l) v2 Tgoal Hty HE HWT)
        as [S [HtyRef [Hty2 Hsub]]].
      destruct (MyWork__typing_ref_inv E R l (typ_box S) HtyRef) as [T0 [Hb HsubBox]].
      assert (HWT0 : wf_typ E T0) by (apply (Store__wf_sig_binds E R l T0 Hws Hb)).
      assert (HWTbox0 : wf_typ E (typ_box T0)) by (apply (wf_typ_box E T0 HWT0)).
      assert (HWTboxS : wf_typ E (typ_box S))
        by (apply (WfTyping__typing_wf_typ E R (exp_ref l) (typ_box S)); exact HtyRef).
      destruct (MyWork__sub_box_box E T0 S HE HWTbox0 HWTboxS HsubBox) as [HsubT0S HsubST0].
      assert (Htyv2T0 : typing E R v2 T0)
        by (exact (typing_sub S E R v2 T0 Hws Hty2 HsubST0)).
      assert (HtyStore : typing_store E R (LabelMapImpl.add l v2 s1))
        by (exact (Store__typing_store_update E R s1 l v2 T0 Hst Hb Htyv2T0 Hval2)).
      assert (Htyv1 : typing E R v1 T0)
        by (exact (typing_store_value E R s1 l v1 T0 Hws Hst Hb Hmaps)).
      assert (Htyv1S : typing E R v1 S)
        by (exact (typing_sub T0 E R v1 S Hws Htyv1 HsubT0S)).
      exists sempty. simpl. split; [exact Hws | split].
      * eapply typing_sub.
        -- exact Hws.
        -- exact Htyv1S.
        -- exact Hsub.
      * exact HtyStore.

    + (* red_seal_1 *)
      destruct (typing_ctx_facts E R (exp_seal e1) Tgoal Hty) as [HE [Hws HWT]].
      destruct (TypingInv__typing_seal_inv E R e1 Tgoal Hty HE HWT) as [S [Hty1 Hsub]].
      destruct (IH1 E R S Hty1 Hst) as [R' [Hws' [Hty1' Hst']]].
      exists R'. split; [exact Hws' | split].
      * eapply typing_sub.
        -- exact Hws'.
        -- eapply typing_seal; [exact Hty1'].
        -- exact Hsub.
      * exact Hst'.

    + (* red_seal_abs *)
      destruct (typing_ctx_facts E R (exp_seal (exp_abs Vabs e1)) Tgoal Hty)
        as [HE [Hws HWT]].
      destruct (TypingInv__typing_seal_inv E R (exp_abs Vabs e1) Tgoal Hty HE HWT)
        as [S [Hinner Hsub]].
      exists sempty. simpl. split; [exact Hws | split].
      * exact (PresHelpers__typing_seal_inner_result E R (exp_abs Vabs e1) S Tgoal
                 Hinner Hsub).
      * exact Hst.

    + (* red_seal_tabs *)
      destruct (typing_ctx_facts E R (exp_seal (exp_tabs Vtabs e1)) Tgoal Hty)
        as [HE [Hws HWT]].
      destruct (TypingInv__typing_seal_inv E R (exp_tabs Vtabs e1) Tgoal Hty HE HWT)
        as [S [Hinner Hsub]].
      exists sempty. simpl. split; [exact Hws | split].
      * exact (PresHelpers__typing_seal_inner_result E R (exp_tabs Vtabs e1) S Tgoal
                 Hinner Hsub).
      * exact Hst.

    + (* red_seal_sealed_ref *)
      destruct (typing_ctx_facts E R (exp_seal (exp_seal (exp_ref l))) Tgoal Hty)
        as [HE [Hws HWT]].
      destruct (TypingInv__typing_seal_inv E R (exp_seal (exp_ref l)) Tgoal Hty HE HWT)
        as [S [Hinner Hsub]].
      exists sempty. simpl. split; [exact Hws | split].
      * exact (PresHelpers__typing_seal_inner_result E R (exp_seal (exp_ref l)) S Tgoal
                 Hinner Hsub).
      * exact Hst.

    + (* red_seal_sealed_record *)
      destruct (typing_ctx_facts E R (exp_seal (exp_seal (exp_record r))) Tgoal Hty)
        as [HE [Hws HWT]].
      destruct (TypingInv__typing_seal_inv E R (exp_seal (exp_record r)) Tgoal Hty HE HWT)
        as [S [Hinner Hsub]].
      exists sempty. simpl. split; [exact Hws | split].
      * exact (PresHelpers__typing_seal_inner_result E R (exp_seal (exp_record r)) S Tgoal
                 Hinner Hsub).
      * exact Hst.

    + (* red_record *)
      destruct (typing_ctx_facts E R (exp_record r1) Tgoal Hty) as [HE [Hws HWT]].
      destruct (TypingInv__typing_record_inv E R r1 Tgoal Hty HE HWT) as [Tr [Hrc Hsub]].
      assert (Hex : exists R', wf_sig E (R' ++ R) /\
          typing_record_comp E (R' ++ R) r1' Tr /\
          typing_store E (R' ++ R) s1').
      { exact (preservation_record E R r1 s1 r1' s1' Tr Hrc Hst Hredrc). }
      destruct Hex as [Radd [Hwsadd [Hrcadd Hstadd]]].
      exists Radd. split; [exact Hwsadd | split].
      * eapply typing_sub.
        -- exact Hwsadd.
        -- eapply typing_record; [exact Hrcadd].
        -- exact Hsub.
      * exact Hstadd.

    + (* red_record_read_1 *)
      destruct (typing_ctx_facts E R (exp_record_read e1 a) Tgoal Hty) as [HE [Hws HWT]].
      destruct (TypingInv__typing_record_read_inv E R e1 a Tgoal Hty HE HWT)
        as [[S [Hty1 Hsub]] | [S [Hty1 Hsub]]].
      * destruct (IH1 E R (typ_record a S) Hty1 Hst) as [R' [Hws' [Hty1' Hst']]].
        exists R'. split; [exact Hws' | split].
        -- eapply typing_sub.
           ++ exact Hws'.
           ++ eapply typing_record_read; [exact Hty1'].
           ++ exact Hsub.
        -- exact Hst'.
      * destruct (IH1 E R (typ_mut mut_readonly (typ_record a S)) Hty1 Hst)
          as [R' [Hws' [Hty1' Hst']]].
        exists R'. split; [exact Hws' | split].
        -- eapply typing_sub.
           ++ exact Hws'.
           ++ eapply typing_record_read_readonly; [exact Hty1'].
           ++ exact Hsub.
        -- exact Hst'.

    + (* red_record_read_ref *)
      destruct (typing_ctx_facts E R (exp_record_read (exp_record r) a) Tgoal Hty)
        as [HE [Hws HWT]].
      destruct (TypingInv__typing_record_read_inv E R (exp_record r) a Tgoal Hty HE HWT)
        as [[S [HtyRec Hsub]] | [S [HtyRec Hsub]]].
      * destruct (RecordInv__record_field_nonro_strong E R r a S Hvalrec HtyRec)
          as [l0 [Tf [Hlook0 [Hb [HsubTfS [HsubSTf HsubRec]]]]]].
        assert (Heql : l0 = l)
          by (rewrite Hlook0 in Hlook; injection Hlook as Hl; exact Hl).
        subst l0.
        assert (Htyv1 : typing E R v1 Tf)
          by (exact (typing_store_value E R s1 l v1 Tf Hws Hst Hb Hmaps)).
        assert (Htyv1S : typing E R v1 S)
          by (exact (typing_sub Tf E R v1 S Hws Htyv1 HsubTfS)).
        exists sempty. simpl. split; [exact Hws | split].
        -- eapply typing_sub.
           ++ exact Hws.
           ++ exact Htyv1S.
           ++ exact Hsub.
        -- exact Hst.
      * destruct (RecordInv__record_field_readonly E R r a S Hvalrec HtyRec)
          as [l0 [Tf [Hlook0 [Hb HsubTfS]]]].
        assert (Heql : l0 = l)
          by (rewrite Hlook0 in Hlook; injection Hlook as Hl; exact Hl).
        subst l0.
        assert (Htyv1 : typing E R v1 Tf)
          by (exact (typing_store_value E R s1 l v1 Tf Hws Hst Hb Hmaps)).
        exists sempty. simpl. split; [exact Hws | split].
        -- exact (PresHelpers__typing_value_readonly_result E R v1 Tf S Tgoal
                    Htyv1 HsubTfS Hsub).
        -- exact Hst.

    + (* red_sealed_record_read_ref *)
      destruct (typing_ctx_facts E R (exp_record_read (exp_seal (exp_record r)) a) Tgoal Hty)
        as [HE [Hws HWT]].
      destruct (TypingInv__typing_record_read_inv E R (exp_seal (exp_record r)) a Tgoal Hty HE HWT)
        as [[S [HtySeal Hsub]] | [S [HtySeal Hsub]]].
      * (* a sealed record cannot be typed at a plain record type *)
        destruct (TypingInv__typing_seal_inv E R (exp_record r) (typ_record a S) HtySeal HE
                    (WfTyping__typing_wf_typ E R (exp_seal (exp_record r)) (typ_record a S) HtySeal))
          as [St [Hrec Hsubseal]].
        exfalso. exact (Readonly__sub_readonly_record_false E St a S Hsubseal).
      * destruct (TypingInv__typing_seal_inv E R (exp_record r)
                    (typ_mut mut_readonly (typ_record a S)) HtySeal HE
                    (WfTyping__typing_wf_typ E R (exp_seal (exp_record r))
                       (typ_mut mut_readonly (typ_record a S)) HtySeal))
          as [St [Hrec Hsubseal]].
        assert (HWTtarget : wf_typ E (typ_mut mut_readonly (typ_record a S)))
          by (apply (WfTyping__typing_wf_typ E R (exp_seal (exp_record r))
                       (typ_mut mut_readonly (typ_record a S))); exact HtySeal).
        assert (HWTrec : wf_typ E (typ_record a S))
          by (apply (Dev__wf_typ_inv_readonly E mut_readonly (typ_record a S) HWTtarget)).
        assert (HWS : wf_typ E S) by (apply (Dev__wf_typ_inv_record E a S HWTrec)).
        destruct (RecordInv__typing_exp_record_inv E R r St Hrec) as [Tr [Hrc HsubTrSt]].
        assert (HWTroTr : wf_typ E (typ_mut mut_readonly Tr)).
        { apply (wf_typ_readonly E Tr).
          apply (WfTyping__typing_record_comp_wf_typ E R r Tr). exact Hrc. }
        assert (HsubRO : sub E (typ_mut mut_readonly Tr)
                              (typ_mut mut_readonly (typ_record a S))).
        { eapply sub_trans.
          - apply sub_readonly. exact HsubTrSt.
          - exact Hsubseal. }
        destruct (MyWork__sub_rcomp a E (typ_mut mut_readonly Tr)
                    (typ_mut mut_readonly (typ_record a S)) HE HWTroTr HsubRO
                    S HWS (MyWork__rc_mut a mut_readonly (typ_record a S) S (MyWork__rc_here a S)))
          as [A' [HA' [Hac' HsubA'S]]].
        assert (HacTr : MyWork__RComp a Tr A')
          by (exact (MyWork__RComp_mut_inv a mut_readonly Tr A' Hac')).
        destruct (RecordInv__typing_record_comp_ref_field E R r Tr a A' Hrc Hvalrec HacTr)
          as [l0 [Tf [Hlook0 [Hb HsubTfA']]]].
        assert (Heql : l0 = l)
          by (rewrite Hlook0 in Hlook; injection Hlook as Hl; exact Hl).
        subst l0.
        assert (HsubTfS : sub E Tf S)
          by (eapply sub_trans; [exact HsubTfA' | exact HsubA'S]).
        assert (Htyv1 : typing E R v1 Tf)
          by (exact (typing_store_value E R s1 l v1 Tf Hws Hst Hb Hmaps)).
        assert (Htyseal : typing E R (exp_seal v1) (typ_mut mut_readonly S))
          by (exact (PresHelpers__typing_seal_value_at_readonly E R v1 Tf S
                       Htyv1 HsubTfS)).
        exists sempty. simpl. split; [exact Hws | split].
        -- eapply typing_sub.
           ++ exact Hws.
           ++ exact Htyseal.
           ++ exact Hsub.
        -- exact Hst.

    + (* red_record_write_1 *)
      destruct (typing_ctx_facts E R (exp_record_write e1 a e2) Tgoal Hty)
        as [HE [Hws HWT]].
      destruct (TypingInv__typing_record_write_inv E R e1 a e2 Tgoal Hty HE HWT)
        as [S [Hty1 [Hty2 Hsub]]].
      destruct (IH1 E R (typ_record a S) Hty1 Hst) as [R' [Hws' [Hty1' Hst']]].
      exists R'. split; [exact Hws' | split].
      * eapply typing_sub.
        -- exact Hws'.
        -- eapply typing_record_write.
           ++ exact Hty1'.
           ++ exact (Store__typing_sig_weaken E R e2 S Hty2 R' Hws').
        -- exact Hsub.
      * exact Hst'.

    + (* red_record_write_2 *)
      destruct (typing_ctx_facts E R (exp_record_write v1 a e2) Tgoal Hty)
        as [HE [Hws HWT]].
      destruct (TypingInv__typing_record_write_inv E R v1 a e2 Tgoal Hty HE HWT)
        as [S [Hty1 [Hty2 Hsub]]].
      destruct (IH2 E R S Hty2 Hst) as [R' [Hws' [Hty2' Hst']]].
      exists R'. split; [exact Hws' | split].
      * eapply typing_sub.
        -- exact Hws'.
        -- eapply typing_record_write.
           ++ exact (Store__typing_sig_weaken E R v1 (typ_record a S) Hty1 R' Hws').
           ++ exact Hty2'.
        -- exact Hsub.
      * exact Hst'.

    + (* red_record_write_ref *)
      destruct (typing_ctx_facts E R (exp_record_write (exp_record r) a v2) Tgoal Hty)
        as [HE [Hws HWT]].
      destruct (TypingInv__typing_record_write_inv E R (exp_record r) a v2 Tgoal Hty HE HWT)
        as [S [HtyRec [Htyv2 Hsub]]].
      destruct (RecordInv__record_field_nonro_strong E R r a S Hvalrec HtyRec)
        as [l0 [Tf [Hlook0 [Hb [HsubTfS [HsubSTf HsubRec]]]]]].
      assert (Heql : l0 = l)
        by (rewrite Hlook0 in Hlook; injection Hlook as Hl; exact Hl).
      subst l0.
      assert (Htyv2Tf : typing E R v2 Tf)
        by (exact (typing_sub S E R v2 Tf Hws Htyv2 HsubSTf)).
      assert (HtyStore : typing_store E R (LabelMapImpl.add l v2 s1))
        by (exact (Store__typing_store_update E R s1 l v2 Tf Hst Hb Htyv2Tf Hval2)).
      assert (Htyv1 : typing E R v1 Tf)
        by (exact (typing_store_value E R s1 l v1 Tf Hws Hst Hb Hmaps)).
      assert (Htyv1S : typing E R v1 S)
        by (exact (typing_sub Tf E R v1 S Hws Htyv1 HsubTfS)).
      exists sempty. simpl. split; [exact Hws | split].
      * eapply typing_sub.
        -- exact Hws.
        -- exact Htyv1S.
        -- exact Hsub.
      * exact HtyStore.

  - (* preservation_record *)
    intros E R r s r' s' T Hrc Hst Hred.
    revert E R T Hrc Hst.
    induction Hred as
      [ a e1 s1 e1' s1' r1 Hrec Hred1
      | a v r1 s1 l Hwf Hrec Hval Hfresh
      | a l r1 s1 r1' s1' Hred1 IH1 ] using red_record_comp_ind;
      intros E R Tgoal Hrc Hst.

    + (* red_record_exp_1 *)
      destruct (record_ctx_facts E R (rec_exp a e1 r1) Tgoal Hrc) as [HE [Hws HWT]].
      destruct (typing_record_comp_exp_inv E R a e1 r1 Tgoal Hrc)
        as [T1 [Tr [Hnotin [Hrcr [Hty1 HeqT]]]]].
      subst Tgoal.
      destruct (preservation E R e1 s1 e1' s1' T1 Hty1 Hst Hred1)
        as [R' [Hws' [Hty1' Hst']]].
      exists R'. split; [exact Hws' | split].
      * eapply typing_record_exp.
        -- exact Hnotin.
        -- exact (Helpers__typing_record_comp_sig_weaken E R r1 Tr Hrcr R' Hws').
        -- exact Hty1'.
      * exact Hst'.

    + (* red_record_exp_2 *)
      destruct (record_ctx_facts E R (rec_exp a v r1) Tgoal Hrc) as [HE [Hws HWT]].
      destruct (typing_record_comp_exp_inv E R a v r1 Tgoal Hrc)
        as [T1 [Tr [Hnotin [Hrcr [Htyv HeqT]]]]].
      subst Tgoal.
      assert (HWT1 : wf_typ E T1)
        by (apply (WfTyping__typing_wf_typ E R v T1); exact Htyv).
      assert (Hnotmaps : forall v0 : exp, ~ LabelMapImpl.MapsTo l v0 s1).
      { intros v0 HM. exact (Store__fresh_label_not_maps s1 l v0 (eq_sym Hfresh) HM). }
      assert (Hnotdom : LabelSetImpl.notin l (Signatures.dom R)).
      { apply (Store__fresh_label_notin_sig_dom E R s1 l Hst Hfresh). }
      assert (Hws' : wf_sig E (l ~ bind_sig T1 ++ R))
        by (apply (wf_sig_typ E R l T1 Hws HWT1 Hnotdom)).
      assert (Hrcr' : typing_record_comp E (l ~ bind_sig T1 ++ R) r1 Tr)
        by (exact (Helpers__typing_record_comp_sig_weaken E R r1 Tr Hrcr
                     (l ~ bind_sig T1) Hws')).
      exists (l ~ bind_sig T1). split; [exact Hws' | split].
      * eapply typing_record_ref.
        -- exact Hnotin.
        -- exact Hrcr'.
        -- exact (binds_sig_head R l T1).
      * exact (Store__typing_store_add E R s1 l v T1 HWT1 Hst Hnotmaps Htyv Hval).

    + (* red_record_ref *)
      destruct (record_ctx_facts E R (rec_ref a l r1) Tgoal Hrc) as [HE [Hws HWT]].
      destruct (typing_record_comp_ref_inv E R a l r1 Tgoal Hrc)
        as [T1 [Tr [Hnotin [Hrcr [Hb HeqT]]]]].
      subst Tgoal.
      destruct (IH1 E R Tr Hrcr Hst) as [R' [Hws' [Hrcr' Hst']]].
      exists R'. split; [exact Hws' | split].
      * eapply typing_record_ref.
        -- rewrite <- (record_dom_red_comp r1 s1 r1' s1' Hred1). exact Hnotin.
        -- exact Hrcr'.
        -- exact (binds_sig_weaken_prefix R R' l T1 Hb).
      * exact Hst'.
Qed.




(* ================================================================ *)
(* Progress                                                         *)
(*                                                                  *)
(* We prove a version generalised over an environment [E] together  *)
(* with a proof [E = empty]; this keeps the environment an abstract *)
(* variable during dependent elimination while still letting the    *)
(* variable case be discharged.                                     *)
(* ================================================================ *)

Fixpoint all_steps (E : env) (R : sig) (e : exp) (T : typ)
    (Hty : typing E R e T) (HE : E = empty) {struct Hty} :
    forall s, typing_store E R s ->
      value e \/ exists e' s', red e s e' s'
with all_steps_record (E : env) (R : sig) (r : rec_comp) (T : typ)
    (Hr : typing_record_comp E R r T) (HE : E = empty) {struct Hr} :
    forall s, typing_store E R s ->
      value_record_comp r \/ exists r' s', red_record_comp r s r' s'.
Proof.
  - intros s Hstore.
    destruct Hty as
      [ E R0 x T0 Hwe Hws Hb
      | L E R0 V e1b T1 Hws Hbody
      | T1 E R0 e1b e2b T2 Hws H1 H2
      | L E R0 V e1b T1 Hws Hbody
      | T1 E R0 e1b Targ T2 Hws H1 Hsub
      | S E R0 e0 T0 Hws H1 Hsub
      | L T1 T2 e1b e2b E R0 Hws H1 Hbody
      | E R0 e0 T0 Hws H1
      | E R0 e0 T0 Hws H1
      | E R0 e1b e2b T0 Hws H1 H2
      | E R0 l T0 Hwe Hws Hb
      | E R0 e0 T0 H1
      | E R0 e0 T0 H1
      | E R0 rb T0 Hr
      | E R0 e0 a T0 H1
      | E R0 e0 a T0 H1
      | E R0 e1b a e2b T0 H1 H2 ].
    + (* var *) exfalso.
      apply (Helpers__no_binds_empty x (bind_typ T0)). rewrite HE in Hb. exact Hb.
    + (* abs *)
      left. apply value_abs.
      apply (TypingExpr__typing_expr E R0 (exp_abs V e1b) (typ_arrow V T1)).
      apply (typing_abs L E R0 V e1b T1 Hws Hbody).
    + (* app *)
      assert (Hwfe : wf_env E) by (apply (Dev__wf_sig_wf_env E R0); exact Hws).
      destruct (all_steps E R0 e1b (typ_arrow T1 T2) H1 HE s Hstore)
        as [Hv1 | [e1' [s1' Hred1]]].
      * destruct (all_steps E R0 e2b T1 H2 HE s Hstore)
          as [Hv2 | [e2' [s2' Hred2]]].
        -- destruct (Canonical__value_arrow_abs E R0 e1b T1 T2 Hv1 H1 Hwfe)
             as [V [body Heq]].
           subst e1b.
           right. exists (open_ee body e2b), s.
           apply (red_abs V body s e2b
                    (Helpers__well_formed_store_of_typing_store E R0 s Hstore)).
           ++ apply (TypingExpr__typing_expr E R0 (exp_abs V body) (typ_arrow T1 T2) H1).
           ++ exact Hv2.
        -- right. exists (exp_app e1b e2'), s2'.
           apply (red_app_2 e1b e2b s e2' s2' Hv1 Hred2).
      * right. exists (exp_app e1' e2b), s1'.
        apply (red_app_1 e1b e1' s s1' e2b).
        -- apply (TypingExpr__typing_expr E R0 e2b T1 H2).
        -- exact Hred1.
    + (* tabs *)
      left. apply value_tabs.
      apply (TypingExpr__typing_expr E R0 (exp_tabs V e1b) (typ_all V T1)).
      apply (typing_tabs L E R0 V e1b T1 Hws Hbody).
    + (* tapp *)
      assert (Hwfe : wf_env E) by (apply (Dev__wf_sig_wf_env E R0); exact Hws).
      assert (Hwf : wf_typ E (typ_all T1 T2))
        by (apply (SubstTT__typing_wf_typ E R0 e1b (typ_all T1 T2)); exact H1).
      destruct (Dev__wf_typ_inv_all E T1 T2 Hwf) as [La [HwT1 _]].
      assert (HTarg : wf_typ E Targ)
        by (apply (Dev__sub_wf_source E Targ T1 Hwfe HwT1 Hsub)).
      assert (HtypeArg : type Targ) by (exact (SubstTT__wf_typ_type E Targ HTarg)).
      destruct (all_steps E R0 e1b (typ_all T1 T2) H1 HE s Hstore)
        as [Hv1 | [e1' [s1' Hred1]]].
      * destruct (CanonicalAll__value_all_tabs E R0 e1b T1 T2 Hv1 H1 Hwfe)
          as [V [body Heq]].
        subst e1b.
        right. exists (open_te body Targ), s.
        apply (red_tabs V body s Targ
                 (Helpers__well_formed_store_of_typing_store E R0 s Hstore)).
        -- apply (TypingExpr__typing_expr E R0 (exp_tabs V body) (typ_all T1 T2) H1).
        -- exact HtypeArg.
      * right. exists (exp_tapp e1' Targ), s1'.
        apply (red_tapp e1b e1' s s1' Targ HtypeArg Hred1).
    + (* typing_sub *)
      destruct (all_steps E R0 e0 S H1 HE s Hstore) as [Hv | [e' [s' Hred]]].
      * left. exact Hv.
      * right. exists e', s'. exact Hred.
    + (* let *)
      assert (Hbody_e : body_e e2b).
      { exists L. intros x Hx.
        apply (TypingExpr__typing_expr (x ~ bind_typ T1 ++ E) R0 (open_ee e2b x) T2).
        apply Hbody. exact Hx. }
      destruct (all_steps E R0 e1b T1 H1 HE s Hstore)
        as [Hv1 | [e1' [s1' Hred1]]].
      * right. exists (open_ee e2b e1b), s.
        apply (red_let e1b e2b s
                 (Helpers__well_formed_store_of_typing_store E R0 s Hstore) Hv1 Hbody_e).
      * right. exists (exp_let e1' e2b), s1'.
        apply (red_let_1 e1b e1' s s1' e2b Hred1 Hbody_e).
    + (* box *)
      assert (Hwfe : wf_env E) by (apply (Dev__wf_sig_wf_env E R0); exact Hws).
      destruct (all_steps E R0 e0 T0 H1 HE s Hstore) as [Hv | [e' [s' Hred]]].
      * right. exists (exp_ref (fresh_label_for_store s)),
                       (LabelMapImpl.add (fresh_label_for_store s) e0 s).
        apply (red_box_ref e0 (fresh_label_for_store s) s
                 (Helpers__well_formed_store_of_typing_store E R0 s Hstore) Hv eq_refl).
      * right. exists (exp_box e'), s'.
        apply (red_box_1 e0 e' s s' Hred).
    + (* unbox *)
      assert (Hwfe : wf_env E) by (apply (Dev__wf_sig_wf_env E R0); exact Hws).
      destruct (all_steps E R0 e0 (typ_box T0) H1 HE s Hstore)
        as [Hv | [e' [s' Hred]]].
      * destruct (Canonical__value_box_ref E R0 e0 T0 Hv H1 Hwfe) as [l Heq].
        subst e0.
        destruct (MyWork__typing_ref_inv E R0 l (typ_box T0) H1) as [S [Hb _]].
        destruct (proj1 (Hstore l) S Hb) as [v [HMaps [Htyv Hvalv]]].
        right. exists v, s.
        apply (red_unbox_ref l v s
                 (Helpers__well_formed_store_of_typing_store E R0 s Hstore) Hvalv HMaps).
      * right. exists (exp_unbox e'), s'.
        apply (red_unbox_1 e0 e' s s' Hred).
    + (* set_box *)
      assert (Hwfe : wf_env E) by (apply (Dev__wf_sig_wf_env E R0); exact Hws).
      destruct (all_steps E R0 e1b (typ_box T0) H1 HE s Hstore)
        as [Hv1 | [e1' [s1' Hred1]]].
      * destruct (Canonical__value_box_ref E R0 e1b T0 Hv1 H1 Hwfe) as [l Heq].
        subst e1b.
        destruct (MyWork__typing_ref_inv E R0 l (typ_box T0) H1) as [S [Hb _]].
        destruct (proj1 (Hstore l) S Hb) as [v1 [HMaps [Htyv1 Hval1]]].
        destruct (all_steps E R0 e2b T0 H2 HE s Hstore)
          as [Hv2 | [e2' [s2' Hred2]]].
        -- right. exists v1, (LabelMapImpl.add l e2b s).
           apply (red_set_box_ref l v1 e2b s
                    (Helpers__well_formed_store_of_typing_store E R0 s Hstore)
                    Hval1 Hv2 HMaps).
        -- right. exists (exp_set_box (exp_ref l) e2'), s2'.
           apply (red_set_box_2 (exp_ref l) e2b s e2' s2' Hv1 Hred2).
      * right. exists (exp_set_box e1' e2b), s1'.
        apply (red_set_box_1 e1b s e1' s1' e2b).
        -- apply (TypingExpr__typing_expr E R0 e2b T0 H2).
        -- exact Hred1.
    + (* ref *)
      left. apply value_ref.
    + (* seal *)
      destruct (all_steps E R0 e0 T0 H1 HE s Hstore)
        as [Hv | [e' [s' Hred]]].
      * clear H1.
        destruct Hv as [V body Hexpr | V body Hexpr | l | l | rb Hvr | rb Hvr].
        -- right. exists (exp_abs V body), s.
           apply (red_seal_abs V body s
                    (Helpers__well_formed_store_of_typing_store E R0 s Hstore) Hexpr).
        -- right. exists (exp_tabs V body), s.
           apply (red_seal_tabs V body s
                    (Helpers__well_formed_store_of_typing_store E R0 s Hstore) Hexpr).
        -- left. apply value_sealed_ref.
        -- right. exists (exp_seal (exp_ref l)), s.
           apply (red_seal_sealed_ref l s
                    (Helpers__well_formed_store_of_typing_store E R0 s Hstore)).
        -- left. apply (value_sealed_record rb Hvr).
        -- right. exists (exp_seal (exp_record rb)), s.
           apply (red_seal_sealed_record rb s
                    (Helpers__well_formed_store_of_typing_store E R0 s Hstore) Hvr).
      * right. exists (exp_seal e'), s'.
        apply (red_seal_1 e0 s e' s' Hred).
    + (* unbox_readonly *)
      assert (Hwfe : wf_env E) by (rewrite HE; apply wf_env_empty).
      destruct (all_steps E R0 e0 (typ_mut mut_readonly (typ_box T0)) H1 HE s Hstore)
        as [Hv | [e' [s' Hred]]].
      * destruct (Canonical__value_readonly_box E R0 e0 T0 Hv H1 Hwfe)
          as [[l Heq] | [l Heq]].
        -- subst e0.
           destruct (MyWork__typing_ref_inv E R0 l
                       (typ_mut mut_readonly (typ_box T0)) H1) as [S [Hb _]].
           destruct (proj1 (Hstore l) S Hb) as [v [HMaps [Htyv Hvalv]]].
           right. exists v, s.
           apply (red_unbox_ref l v s
                    (Helpers__well_formed_store_of_typing_store E R0 s Hstore) Hvalv HMaps).
        -- subst e0.
           assert (HWf : wf_typ E (typ_mut mut_readonly (typ_box T0)))
             by (apply (SubstTT__typing_wf_typ E R0 (exp_seal (exp_ref l))
                          (typ_mut mut_readonly (typ_box T0))); exact H1).
           destruct (TypingInv__typing_seal_inv E R0 (exp_ref l)
                       (typ_mut mut_readonly (typ_box T0)) H1 Hwfe HWf)
             as [S [Href Hsub]].
           destruct (MyWork__typing_ref_inv E R0 l S Href) as [S0 [Hb _]].
           destruct (proj1 (Hstore l) S0 Hb) as [v [HMaps [Htyv Hvalv]]].
           right. exists (exp_seal v), s.
           apply (red_unbox_sealed_ref l v s
                    (Helpers__well_formed_store_of_typing_store E R0 s Hstore) Hvalv HMaps).
      * right. exists (exp_unbox e'), s'.
        apply (red_unbox_1 e0 e' s s' Hred).
    + (* record *)
      destruct (all_steps_record E R0 rb T0 Hr HE s Hstore)
        as [Hv | [r' [s' Hred]]].
      * left. apply value_record. exact Hv.
      * right. exists (exp_record r'), s'.
        apply (red_record rb s r' s' Hred).
    + (* record_read *)
      assert (Hwfe : wf_env E) by (rewrite HE; apply wf_env_empty).
      destruct (all_steps E R0 e0 (typ_record a T0) H1 HE s Hstore)
        as [Hv | [e' [s' Hred]]].
      * destruct (Canonical__value_record_lit E R0 e0 a T0 Hv H1 Hwfe) as [rb Heq].
        subst e0.
        assert (Hvr : value_record_comp rb) by (inversion Hv; subst; assumption).
        destruct (RecordInv__record_field_nonro E R0 rb a T0 Hvr H1)
          as [l [Tf [Hlook [Hb HsubT]]]].
        destruct (proj1 (Hstore l) Tf Hb) as [v1 [HMaps [Htyv Hval1]]].
        right. exists v1, s.
        apply (red_record_read_ref rb a l v1 s
                 (Helpers__well_formed_store_of_typing_store E R0 s Hstore)
                 Hvr Hlook Hval1 HMaps).
      * right. exists (exp_record_read e' a), s'.
        apply (red_record_read_1 a e0 e' s s' Hred).
    + (* record_read_readonly *)
      assert (Hwfe : wf_env E) by (rewrite HE; apply wf_env_empty).
      destruct (all_steps E R0 e0 (typ_mut mut_readonly (typ_record a T0)) H1 HE s Hstore)
        as [Hv | [e' [s' Hred]]].
      * destruct (Canonical__value_record_readonly_lit E R0 e0 a T0 Hv H1 Hwfe)
          as [[rb Heq] | [rb Heq]].
        -- subst e0.
           assert (Hvr : value_record_comp rb) by (inversion Hv; subst; assumption).
           destruct (RecordInv__record_field_readonly E R0 rb a T0 Hvr H1)
             as [l [Tf [Hlook [Hb HsubT]]]].
           destruct (proj1 (Hstore l) Tf Hb) as [v1 [HMaps [Htyv Hval1]]].
           right. exists v1, s.
           apply (red_record_read_ref rb a l v1 s
                    (Helpers__well_formed_store_of_typing_store E R0 s Hstore)
                    Hvr Hlook Hval1 HMaps).
        -- subst e0.
           assert (Hvr : value_record_comp rb) by (inversion Hv; subst; assumption).
           assert (HWf : wf_typ E (typ_mut mut_readonly (typ_record a T0)))
             by (apply (SubstTT__typing_wf_typ E R0 (exp_seal (exp_record rb))
                          (typ_mut mut_readonly (typ_record a T0))); exact H1).
           destruct (TypingInv__typing_seal_inv E R0 (exp_record rb)
                       (typ_mut mut_readonly (typ_record a T0)) H1 Hwfe HWf)
             as [S [Hrec Hsub]].
           assert (HT : wf_typ E T0).
           { apply (Dev__wf_typ_inv_record E a T0).
             apply (Dev__wf_typ_inv_readonly E mut_readonly (typ_record a T0)).
             exact HWf. }
           assert (HWfS : wf_typ E (typ_mut mut_readonly S))
             by (apply (Dev__sub_wf_source E (typ_mut mut_readonly S)
                          (typ_mut mut_readonly (typ_record a T0))
                          Hwfe HWf Hsub)).
           destruct (MyWork__sub_rcomp a E (typ_mut mut_readonly S)
                       (typ_mut mut_readonly (typ_record a T0))
                       Hwfe HWfS Hsub T0 HT
                       (MyWork__rc_mut a mut_readonly (typ_record a T0) T0 (MyWork__rc_here a T0)))
             as [A' [HA' [HacA' HsubA'T]]].
           assert (HacS : MyWork__RComp a S A')
             by (apply (MyWork__RComp_mut_inv a mut_readonly S A' HacA')).
           destruct (TypingInv__typing_record_inv E R0 rb S Hrec Hwfe
                       (SubstTT__typing_wf_typ E R0 (exp_record rb) S Hrec))
             as [Tr [Hrc HsubTr]].
           assert (HTr : wf_typ E Tr)
             by (apply (Dev__sub_wf_source E Tr S Hwfe
                          (SubstTT__typing_wf_typ E R0 (exp_record rb) S Hrec) HsubTr)).
           destruct (MyWork__sub_rcomp a E Tr S Hwfe HTr HsubTr A' HA' HacS)
             as [A'' [HA'' [HacTr HsubA''A']]].
           destruct (RecordInv__typing_record_comp_ref_field E R0 rb Tr a A'' Hrc Hvr HacTr)
             as [l [Tf [Hlook [Hb HsubTf]]]].
           destruct (proj1 (Hstore l) Tf Hb) as [v1 [HMaps [Htyv Hval1]]].
           right. exists (exp_seal v1), s.
           apply (red_sealed_record_read_ref rb a l v1 s
                    (Helpers__well_formed_store_of_typing_store E R0 s Hstore)
                    Hvr Hlook Hval1 HMaps).
      * right. exists (exp_record_read e' a), s'.
        apply (red_record_read_1 a e0 e' s s' Hred).
    + (* record_write *)
      assert (Hwfe : wf_env E) by (rewrite HE; apply wf_env_empty).
      destruct (all_steps E R0 e1b (typ_record a T0) H1 HE s Hstore)
        as [Hv1 | [e1' [s1' Hred1]]].
      * destruct (Canonical__value_record_lit E R0 e1b a T0 Hv1 H1 Hwfe) as [rb Heq].
        subst e1b.
        assert (Hvr : value_record_comp rb) by (inversion Hv1; subst; assumption).
        destruct (all_steps E R0 e2b T0 H2 HE s Hstore)
          as [Hv2 | [e2' [s2' Hred2]]].
        -- destruct (RecordInv__record_field_nonro E R0 rb a T0 Hvr H1)
             as [l [Tf [Hlook [Hb HsubT]]]].
           destruct (proj1 (Hstore l) Tf Hb) as [v1 [HMaps [Htyv Hval1]]].
           right. exists v1, (LabelMapImpl.add l e2b s).
           apply (red_record_write_ref a l rb v1 e2b s
                    (Helpers__well_formed_store_of_typing_store E R0 s Hstore)
                    Hvr Hlook Hval1 Hv2 HMaps).
        -- right. exists (exp_record_write (exp_record rb) a e2'), s2'.
           apply (red_record_write_2 a (exp_record rb) e2b s e2' s2' Hv1 Hred2).
      * right. exists (exp_record_write e1' a e2b), s1'.
        apply (red_record_write_1 a e1b s e1' s1' e2b).
        -- apply (TypingExpr__typing_expr E R0 e2b T0 H2).
        -- exact Hred1.
  - intros s Hstore.
    destruct Hr as
      [ E R0 Hwe Hws
      | E R0 a eb rb T0 Tr Hnot Hr Hty
      | E R0 a l rb T0 Tr Hnot Hr Hb ].
    + left. apply value_rec_empty.
    + destruct (all_steps E R0 eb T0 Hty HE s Hstore)
        as [Hv | [e' [s' Hred]]].
      * right. exists (rec_ref a (fresh_label_for_store s) rb),
                       (LabelMapImpl.add (fresh_label_for_store s) eb s).
        apply (red_record_exp_2 a eb rb s (fresh_label_for_store s)
                 (Helpers__well_formed_store_of_typing_store E R0 s Hstore)
                 (Helpers__typing_record_comp_record E R0 rb Tr Hr) Hv eq_refl).
      * right. exists (rec_exp a e' rb), s'.
        apply (red_record_exp_1 a eb s e' s' rb
                 (Helpers__typing_record_comp_record E R0 rb Tr Hr) Hred).
    + destruct (all_steps_record E R0 rb Tr Hr HE s Hstore)
        as [Hv | [r' [s' Hred]]].
      * left. apply value_rec_ref. exact Hv.
      * right. exists (rec_ref a l r'), s'.
        apply (red_record_ref a l rb s r' s' Hred).
Defined.

(* ================================================================ *)
(* The requested theorems                                          *)
(* ================================================================ *)

(* The requested mutual progress group.  The structural induction is
   performed by the generalized mutual fixpoint all_steps /
   all_steps_record above; these declarations expose it at the
   required empty-environment target types. *)

Theorem progress : forall e s R T,
  typing empty R e T ->
  typing_store empty R s ->
  value e \/ exists e' s', red e s e' s'
with progress_record_comp : forall r s R T,
  typing_record_comp empty R r T ->
  typing_store empty R s ->
  value_record_comp r \/ exists r' s', red_record_comp r s r' s'.
Proof.
  - intros e s R T Hty Hst.
    revert Hty Hst.
    destruct T; intros Hty Hst;
      exact (all_steps empty R e _ Hty eq_refl s Hst).
  - intros r s R T Htr Hst.
    revert Htr Hst.
    destruct T; intros Htr Hst;
      exact (all_steps_record empty R r _ Htr eq_refl s Hst).
Qed.
