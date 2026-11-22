From Stdlib Require Import List.
Require Import Metalib.Metatheory.
Require Import Definitions.

Notation "G '⊢' t ':' T" := (typing G t T) (at level 40, t at level 59).

Notation "##" := mod_non_nullable.

Notation "??" := mod_safe.

Notation "!!" := mod_unsafe.

Notation "G '⊢e' t ':' T" := (typingE G t T) (at level 40, t at level 59).

Notation "G '⊢i' t ':' T" := (typingI G t T) (at level 40, t at level 59).

Notation "### T '→' U" := (typE_nonnull_arrow T U) (at level 40).

Notation "??? T '→' U" := (typE_safe_arrow T U) (at level 40).

Notation "!!! T '→' U" := (typI_unsafe_arrow T U) (at level 40).

Fixpoint desugarTe (Te : typE) : typ :=
  match Te with
  | typE_null => typ_null
  | typE_nonnull_arrow Se Ue => typ_mod_arrow ## (desugarTe Se) (desugarTe Ue)
  | typE_safe_arrow Se Ue => typ_mod_arrow ?? (desugarTe Se) (desugarTe Ue)
  end.

Fixpoint desugarTi (Ti : typI) : typ :=
  match Ti with
  | typI_null => typ_null
  | typI_unsafe_arrow Si Ui => typ_mod_arrow !! (desugarTi Si) (desugarTi Ui)
  end.

Definition fresh_label (existing : list blame_label) : blame_label := MetatheoryAtom.Atom.fresh existing.

Definition E_l := fresh_label nil.

Definition I_l := fresh_label (E_l :: nil).

Definition E_intl := fresh_label (E_l :: I_l :: nil).

Definition I_intl := fresh_label (E_l :: I_l :: E_intl :: nil).

Definition E_lab := label_name E_l.

Definition I_lab := label_name I_l.

Definition E_int := label_name E_intl.

Definition I_int := label_name I_intl.

Fixpoint desugar t :=
  match t with
  | tei_var_b n =>
    t_var_b n
  | tei_var_f x =>
    t_var_f x
  | tei_null _ =>
    t_null
  | tei_abs_exp T t =>
    t_abs (desugarTe T) (desugar t)
  | tei_abs_imp Ti t Ui =>
    t_cast (t_abs (desugarTi Ti) (desugar t))
           (typ_mod_arrow ## (desugarTi Ti) (desugarTi Ui))
           I_int
           (typ_mod_arrow !! (desugarTi Ti) (desugarTi Ui))
  | tei_app t u _ =>
    t_app (desugar t) (desugar u)
  | tei_app_safe s t u m =>
    t_app_safe (desugar s) (desugar t) (desugar u)
  | tei_cast_exp t Te Ue =>
    t_cast (desugar t) (desugarTe Te) E_int (desugarTe Ue)
  | tei_cast_imp t Ti p Ui =>
    t_cast (desugar t) (desugarTi Ti) p (desugarTi Ui)
  | tei_import_exp Te t Ti u =>
    t_app (t_abs (desugarTe Te) (desugar u))
          (t_cast (desugar t) (desugarTi Ti) I_lab (desugarTe Te))
  | tei_import_imp Ti t Te u =>
    t_app (t_abs (desugarTi Ti) (desugar u))
          (t_cast (desugar t) (desugarTe Te) E_lab (desugarTi Ti))
  end.

Notation dGe Ge :=
  (map desugarTe Ge).

Notation dGi Gi :=
  (map desugarTi Gi).


(* ---------- Auxiliary lemmas ---------- *)

Lemma compat_refl : forall T, compat T T.
Proof.
  induction T; simpl.
  - constructor.
  - constructor; assumption.
Qed.

Lemma ssub_compat : forall Ve Te, ssub Ve Te -> compat (desugarTe Ve) (desugarTe Te).
Proof.
  intros Ve Te H. induction H; simpl.
  - constructor.
  - constructor; discriminate.
  - apply compat_arrow; assumption.
  - apply compat_arrow; assumption.
  - apply compat_arrow; assumption.
Qed.

Lemma nullify_compat_both : forall Ti Te, nullify Ti Te ->
  compat (desugarTi Ti) (desugarTe Te) /\ compat (desugarTe Te) (desugarTi Ti).
Proof.
  intros Ti Te H. induction H; simpl.
  - split; constructor.
  - destruct IHnullify1 as [IH1a IH1b]. destruct IHnullify2 as [IH2a IH2b].
    split; apply compat_arrow; assumption.
Qed.

Lemma nullify_compat : forall Ti Te, nullify Ti Te -> compat (desugarTi Ti) (desugarTe Te).
Proof. intros. apply nullify_compat_both. assumption. Qed.

Lemma erase_compat_both : forall Te Ti, erase Te Ti ->
  compat (desugarTe Te) (desugarTi Ti) /\ compat (desugarTi Ti) (desugarTe Te).
Proof.
  intros Te Ti H. induction H; simpl.
  - split; constructor.
  - destruct IHerase1 as [IH1a IH1b]. destruct IHerase2 as [IH2a IH2b].
    split; apply compat_arrow; assumption.
  - destruct IHerase1 as [IH1a IH1b]. destruct IHerase2 as [IH2a IH2b].
    split; apply compat_arrow; assumption.
Qed.

Lemma erase_compat : forall Te Ti, erase Te Ti -> compat (desugarTe Te) (desugarTi Ti).
Proof. intros. apply erase_compat_both. assumption. Qed.

Lemma compatI_compat : forall Vi Ti, compatI Vi Ti -> compat (desugarTi Vi) (desugarTi Ti).
Proof.
  intros Vi Ti H. induction H; simpl.
  - constructor.
  - constructor; discriminate.
  - apply compat_arrow; assumption.
Qed.

Lemma desugar_open_rec : forall (u : trmEI) (k : nat) (t : trmEI),
  desugar (open_trmEI_wrt_trmEI_rec k t u) =
  open_trm_wrt_trm_rec k (desugar t) (desugar u).
Proof.
  induction u; intros k t; simpl.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHu. reflexivity.
  - rewrite IHu. reflexivity.
  - rewrite IHu1, IHu2. reflexivity.
  - rewrite IHu1, IHu2, IHu3. reflexivity.
  - rewrite IHu. reflexivity.
  - rewrite IHu. reflexivity.
  - rewrite IHu1, IHu2. reflexivity.
  - rewrite IHu1, IHu2. reflexivity.
Qed.

Lemma desugar_open_var : forall (u : trmEI) (x : varEI),
  desugar (open_trmEI_wrt_trmEI u (tei_var_f x)) =
  open_trm_wrt_trm (desugar u) (t_var_f x).
Proof.
  intros. unfold open_trmEI_wrt_trmEI, open_trm_wrt_trm.
  rewrite desugar_open_rec. reflexivity.
Qed.

(* Contexts of well-typed terms are unique, and typing is stable under
   appending a (uniquely bound) suffix to the context. *)

Lemma notin_dom_app : forall (A:Type) (x:atom) (E F:list (atom*A)),
  x `notin` dom E -> x `notin` dom F -> x `notin` dom (E++F).
Proof.
  intros. rewrite dom_app. apply notin_union; assumption.
Qed.

Lemma typingE_uniq : forall G t T, typingE G t T -> uniq G.
Proof.
  intros G t T H. induction H using typingE_ind.
  - assumption.
  - assumption.
  - destruct (atom_fresh L) as [x Hx].
    match goal with
    | IH : forall y, y `notin` L -> uniq _ |- _ =>
        pose proof (IH x Hx) as Hz; apply uniq_app_2 in Hz
    end.
    assumption.
  - assumption.
  - assumption.
  - assumption.
  - destruct (atom_fresh L) as [x Hx].
    match goal with
    | IH : forall y, y `notin` L -> uniq _ |- _ =>
        pose proof (IH x Hx) as Hz; apply uniq_app_2 in Hz
    end.
    assumption.
Qed.

Lemma typingI_uniq : forall G t T, typingI G t T -> uniq G.
Proof.
  intros G t T H. induction H using typingI_ind.
  - assumption.
  - assumption.
  - destruct (atom_fresh L) as [x Hx].
    match goal with
    | IH : forall y, y `notin` L -> uniq _ |- _ =>
        pose proof (IH x Hx) as Hz; apply uniq_app_2 in Hz
    end.
    assumption.
  - assumption.
  - assumption.
  - assumption.
  - destruct (atom_fresh L) as [x Hx].
    match goal with
    | IH : forall y, y `notin` L -> uniq _ |- _ =>
        pose proof (IH x Hx) as Hz; apply uniq_app_2 in Hz
    end.
    assumption.
Qed.

Lemma typing_uniq : forall G t T, typing G t T -> uniq G.
Proof.
  intros G t T H. induction H using typing_ind.
  - assumption.
  - assumption.
  - destruct (atom_fresh L) as [x Hx].
    match goal with
    | IH : forall y, y `notin` L -> uniq _ |- _ =>
        pose proof (IH x Hx) as Hz; apply uniq_app_2 in Hz
    end.
    assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma typing_weaken : forall G0 t T, typing G0 t T ->
  forall G, uniq (G0 ++ G) -> typing (G0 ++ G) t T.
Proof.
  intros G0 t T H. induction H using typing_ind.
  - intros G0 Hu. apply typing_var.
    + assumption.
    + apply in_or_app. left. assumption.
  - intros G0 Hu. apply typing_null. assumption.
  - intros G0 Hu. apply typing_abs with (L := union L (union (dom G) (dom G0))).
    intros x Hx.
    assert (HxL : x `notin` L) by (exact (notin_union_1 x L (union (dom G) (dom G0)) Hx)).
    assert (Hx2 : x `notin` union (dom G) (dom G0)) by (exact (notin_union_2 x L (union (dom G) (dom G0)) Hx)).
    assert (HxG : x `notin` dom G) by (exact (notin_union_1 x (dom G) (dom G0) Hx2)).
    assert (HxG0 : x `notin` dom G0) by (exact (notin_union_2 x (dom G) (dom G0) Hx2)).
    assert (Hnot : x `notin` dom (G ++ G0)) by (apply notin_dom_app; assumption).
    assert (Hu' : uniq (x ~ V ++ (G ++ G0))).
    { apply uniq_push. - exact Hu. - exact Hnot. }
    apply (H0 x HxL G0 Hu').
  - intros G0 Hu. apply typing_app with (M := M) (V := V).
    + apply IHtyping1. assumption.
    + assumption.
    + apply IHtyping2. assumption.
  - intros G0 Hu. apply typing_safe_app with (M := M) (V := V).
    + apply IHtyping1. assumption.
    + assumption.
    + apply IHtyping2. assumption.
    + apply IHtyping3. assumption.
  - intros G0 Hu. apply typing_cast with (V := V).
    + apply IHtyping. assumption.
    + assumption.
Qed.

Scheme typingEI_mut := Induction for typingE Sort Prop
  with typingII_mut := Induction for typingI Sort Prop.

Lemma desugar_typingE : forall Ge tei Te,
  Ge ⊢e tei : Te -> dGe Ge ⊢ desugar tei : desugarTe Te.
Proof.
  intros Ge tei Te H.
  induction H using typingEI_mut
    with (P0 := fun Gi tei Ti _ => dGi Gi ⊢ desugar tei : desugarTi Ti).
  - (* typingE_var *)
    simpl. apply typing_var.
    + apply uniq_map_iff. assumption.
    + apply binds_map_2. assumption.
  - (* typingE_null *)
    simpl. apply typing_null. apply uniq_map_iff. assumption.
  - (* typingE_abs *)
    simpl. eapply typing_abs with (L := L).
    intros xei Hx. rewrite <- (desugar_open_var sei xei). apply H. assumption.
  - (* typingE_app *)
    simpl. eapply typing_app with (M := mod_non_nullable) (V := desugarTe Ve).
    + apply IHtypingE1.
    + discriminate.
    + apply IHtypingE2.
  - (* typingE_safe_app *)
    simpl. eapply typing_safe_app with (M := mod_safe) (V := desugarTe Ve).
    + apply IHtypingE1.
    + discriminate.
    + apply IHtypingE2.
    + apply IHtypingE3.
  - (* typingE_cast *)
    simpl. eapply typing_cast.
    + apply IHtypingE.
    + apply ssub_compat. assumption.
  - (* typingE_import *)
    simpl. eapply typing_app with (M := mod_non_nullable) (V := desugarTe Te).
    + eapply typing_abs with (L := L).
      intros xei Hx. rewrite <- (desugar_open_var uei xei). apply H. assumption.
    + discriminate.
    + eapply typing_cast.
      * apply (typing_weaken nil (desugar tei) (desugarTi Ti) IHtypingE (dGe Ge)).
        simpl. apply uniq_map_iff.
        exact (typingE_uniq Ge (tei_import_exp Te tei Ti uei) Ve
                 (typingE_import L Ge Te tei Ti uei Ve i i0 t t0 n)).
      * apply nullify_compat. assumption.
  - (* typingI_var *)
    simpl. apply typing_var.
    + apply uniq_map_iff. assumption.
    + apply binds_map_2. assumption.
  - (* typingI_null *)
    simpl. apply typing_null. apply uniq_map_iff. assumption.
  - (* typingI_abs *)
    simpl. eapply typing_cast.
    + eapply typing_abs with (L := L).
      intros xei Hx. rewrite <- (desugar_open_var sei xei). apply H. assumption.
    + apply compat_arrow; apply compat_refl.
  - (* typingI_app *)
    simpl. eapply typing_app with (M := mod_unsafe) (V := desugarTi Vi).
    + apply IHtypingE.
    + discriminate.
    + apply IHtypingE0.
  - (* typingI_safi_app *)
    simpl. eapply typing_safe_app with (M := mod_unsafe) (V := desugarTi Vi).
    + apply IHtypingE.
    + discriminate.
    + apply IHtypingE0.
    + apply IHtypingE1.
  - (* typingI_cast *)
    simpl. eapply typing_cast.
    + apply IHtypingE.
    + apply compatI_compat. assumption.
  - (* typingI_import *)
    simpl. eapply typing_app with (M := mod_non_nullable) (V := desugarTi Ti).
    + eapply typing_abs with (L := L).
      intros xei Hx. rewrite <- (desugar_open_var uei xei). apply H. assumption.
    + discriminate.
    + eapply typing_cast.
      * apply (typing_weaken nil (desugar tei) (desugarTe Te) IHtypingE (dGi Gi)).
        simpl. apply uniq_map_iff.
        exact (typingI_uniq Gi (tei_import_imp Ti tei Te uei) Vi
                 (typingI_import L Gi Ti tei Te uei Vi i i0 t H0 e)).
      * apply erase_compat. assumption.
Qed.

Lemma desugar_typingI : forall Gi tei Ti,
  Gi ⊢i tei : Ti -> dGi Gi ⊢ desugar tei : desugarTi Ti.
Proof.
  intros Gi tei Ti H.
  induction H using typingII_mut
    with (P := fun Ge tei Te _ => dGe Ge ⊢ desugar tei : desugarTe Te).
  - (* typingE_var *)
    simpl. apply typing_var.
    + apply uniq_map_iff. assumption.
    + apply binds_map_2. assumption.
  - (* typingE_null *)
    simpl. apply typing_null. apply uniq_map_iff. assumption.
  - (* typingE_abs *)
    simpl. eapply typing_abs with (L := L).
    intros xei Hx. rewrite <- (desugar_open_var sei xei). apply H. assumption.
  - (* typingE_app *)
    simpl. eapply typing_app with (M := mod_non_nullable) (V := desugarTe Ve).
    + apply IHtypingI.
    + discriminate.
    + apply IHtypingI0.
  - (* typingE_safe_app *)
    simpl. eapply typing_safe_app with (M := mod_safe) (V := desugarTe Ve).
    + apply IHtypingI.
    + discriminate.
    + apply IHtypingI0.
    + apply IHtypingI1.
  - (* typingE_cast *)
    simpl. eapply typing_cast.
    + apply IHtypingI.
    + apply ssub_compat. assumption.
  - (* typingE_import *)
    simpl. eapply typing_app with (M := mod_non_nullable) (V := desugarTe Te).
    + eapply typing_abs with (L := L).
      intros xei Hx. rewrite <- (desugar_open_var uei xei). apply H. assumption.
    + discriminate.
    + eapply typing_cast.
      * apply (typing_weaken nil (desugar tei) (desugarTi Ti) IHtypingI (dGe Ge)).
        simpl. apply uniq_map_iff.
        exact (typingE_uniq Ge (tei_import_exp Te tei Ti uei) Ve
                 (typingE_import L Ge Te tei Ti uei Ve i i0 t H0 n)).
      * apply nullify_compat. assumption.
  - (* typingI_var *)
    simpl. apply typing_var.
    + apply uniq_map_iff. assumption.
    + apply binds_map_2. assumption.
  - (* typingI_null *)
    simpl. apply typing_null. apply uniq_map_iff. assumption.
  - (* typingI_abs *)
    simpl. eapply typing_cast.
    + eapply typing_abs with (L := L).
      intros xei Hx. rewrite <- (desugar_open_var sei xei). apply H. assumption.
    + apply compat_arrow; apply compat_refl.
  - (* typingI_app *)
    simpl. eapply typing_app with (M := mod_unsafe) (V := desugarTi Vi).
    + apply IHtypingI1.
    + discriminate.
    + apply IHtypingI2.
  - (* typingI_safi_app *)
    simpl. eapply typing_safe_app with (M := mod_unsafe) (V := desugarTi Vi).
    + apply IHtypingI1.
    + discriminate.
    + apply IHtypingI2.
    + apply IHtypingI3.
  - (* typingI_cast *)
    simpl. eapply typing_cast.
    + apply IHtypingI.
    + apply compatI_compat. assumption.
  - (* typingI_import *)
    simpl. eapply typing_app with (M := mod_non_nullable) (V := desugarTi Ti).
    + eapply typing_abs with (L := L).
      intros xei Hx. rewrite <- (desugar_open_var uei xei). apply H. assumption.
    + discriminate.
    + eapply typing_cast.
      * apply (typing_weaken nil (desugar tei) (desugarTe Te) IHtypingI (dGi Gi)).
        simpl. apply uniq_map_iff.
        exact (typingI_uniq Gi (tei_import_imp Ti tei Te uei) Vi
                 (typingI_import L Gi Ti tei Te uei Vi i i0 t t0 e)).
      * apply erase_compat. assumption.
Qed.

Theorem desugar_typing:
  (forall Ge tei Te,
      Ge ⊢e tei : Te ->
      dGe Ge ⊢ desugar tei : desugarTe Te) /\
  (forall Gi tei Ti,
      Gi ⊢i tei : Ti ->
      dGi Gi ⊢ desugar tei : desugarTi Ti).
Proof.
  split.
  - apply desugar_typingE.
  - apply desugar_typingI.
Qed.
