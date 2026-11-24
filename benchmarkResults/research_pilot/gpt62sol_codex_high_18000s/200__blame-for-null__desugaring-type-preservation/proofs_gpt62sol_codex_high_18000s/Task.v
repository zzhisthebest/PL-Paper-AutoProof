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

Lemma desugar_open_rec : forall t k u,
    desugar (open_trmEI_wrt_trmEI_rec k u t) =
    open_trm_wrt_trm_rec k (desugar u) (desugar t).
Proof.
  induction t; intros k u; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; reflexivity.
  - now rewrite IHt.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2, IHt3.
  - now rewrite IHt.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
Qed.

Lemma desugar_open : forall t x,
    desugar (open_trmEI_wrt_trmEI t (tei_var_f x)) =
    open_trm_wrt_trm (desugar t) (t_var_f x).
Proof.
  intros t x. exact (desugar_open_rec t 0 (tei_var_f x)).
Qed.

Lemma desugar_compat_refl : forall T, compat T T.
Proof.
  induction T; constructor; assumption.
Qed.

Lemma desugar_compat_ssub : forall V T,
    ssub V T -> compat (desugarTe V) (desugarTe T).
Proof.
  intros V T H. induction H; simpl; constructor; try assumption; discriminate.
Qed.

Lemma desugar_compat_implicit : forall V T,
    compatI V T -> compat (desugarTi V) (desugarTi T).
Proof.
  intros V T H. induction H; simpl; constructor; try assumption; discriminate.
Qed.

Lemma desugar_compat_nullify : forall Ti Te,
    nullify Ti Te ->
    compat (desugarTi Ti) (desugarTe Te) /\
    compat (desugarTe Te) (desugarTi Ti).
Proof.
  intros Ti Te H. induction H; simpl; split; constructor; tauto.
Qed.

Lemma desugar_compat_erase : forall Te Ti,
    erase Te Ti ->
    compat (desugarTe Te) (desugarTi Ti) /\
    compat (desugarTi Ti) (desugarTe Te).
Proof.
  intros Te Ti H. induction H; simpl; split; constructor; tauto.
Qed.

Lemma desugar_target_uniq : forall G t T, G ⊢ t : T -> uniq G.
Proof.
  intros G t T H.
  induction H as [ | | L G V s T Hbody IH | | | ]; try assumption.
  pick fresh x.
  eapply uniq_app_2.
  apply (IH x). solve_notin.
Qed.

Lemma desugar_target_weaken : forall G t T,
    G ⊢ t : T ->
    forall G', uniq G' ->
    (forall x V, binds x V G -> binds x V G') ->
    G' ⊢ t : T.
Proof.
  intros G t T Htyping.
  induction Htyping as
      [G x T Huniq Hbind
      |G Huniq
      |L G V s T Hbody IH
      |G s t T M V Hfun IHfun Hmod Harg IHarg
      |G f s t T M V Hfun IHfun Hmod Harg IHarg Hfallback IHfallback
      |G s V p T Hterm IH Hcompat];
    intros G' Huniq' Hbinds.
  - apply typing_var; auto.
  - apply typing_null. exact Huniq'.
  - apply typing_abs with (L := L `union` dom G').
    intros x Hfresh.
    apply IH.
    + solve_notin.
    + apply uniq_push; [exact Huniq' | solve_notin].
    + intros y U Hbind.
      apply binds_cons_1 in Hbind.
      destruct Hbind as [[Hy HU] | Hbind].
      * apply binds_cons_2; assumption.
      * apply binds_cons. now apply Hbinds.
  - eapply typing_app; eauto.
  - eapply typing_safe_app; eauto.
  - apply typing_cast; auto.
Qed.

Lemma desugar_target_import : forall G f t V U T p,
    G ⊢ f : (typ_mod_arrow ## U T) ->
    nil ⊢ t : V ->
    compat V U ->
    G ⊢ t_app f (t_cast t V p U) : T.
Proof.
  intros G f t V U T p Hfun Hterm Hcompat.
  eapply typing_app with (M := ##) (V := U).
  - exact Hfun.
  - discriminate.
  - apply typing_cast; [| exact Hcompat].
    eapply desugar_target_weaken.
    + exact Hterm.
    + eapply desugar_target_uniq. exact Hfun.
    + intros x W Hbind. inversion Hbind.
Qed.

Scheme desugar_typingE_ind := Induction for typingE Sort Prop
with desugar_typingI_ind := Induction for typingI Sort Prop.
Combined Scheme desugar_typing_mutind
  from desugar_typingE_ind, desugar_typingI_ind.

Theorem desugar_typing:
  (forall Ge tei Te,
      Ge ⊢e tei : Te ->
      dGe Ge ⊢ desugar tei : desugarTe Te) /\
  (forall Gi tei Ti,
      Gi ⊢i tei : Ti ->
      dGi Gi ⊢ desugar tei : desugarTi Ti).
Proof.
  apply desugar_typing_mutind.
  - intros Ge x Te Huniq Hbind. simpl.
    apply typing_var; [now apply uniq_map | now apply binds_map].
  - intros Ge Huniq. simpl.
    apply typing_null. now apply uniq_map.
  - intros L Ge Ve s Te _ _ IH. simpl.
    apply typing_abs with (L := L).
    intros x Hfresh. rewrite <- desugar_open.
    exact (IH x Hfresh).
  - intros Ge s t Te Ve _ _ _ IHfun _ IHarg. simpl.
    eapply typing_app with (M := ##).
    + exact IHfun.
    + discriminate.
    + exact IHarg.
  - intros Ge f s t Te Ve _ IHfun _ IHarg _ IHfallback. simpl.
    eapply typing_safe_app with (M := ??).
    + exact IHfun.
    + discriminate.
    + exact IHarg.
    + exact IHfallback.
  - intros Ge s Ve Te _ _ IH Hsub. simpl.
    apply typing_cast; [exact IH | now apply desugar_compat_ssub].
  - intros L Ge Te t Ti u Ve _ _ _ IHbody _ IHterm Hnullify. simpl.
    eapply desugar_target_import.
    + apply typing_abs with (L := L).
      intros x Hfresh. rewrite <- desugar_open.
      exact (IHbody x Hfresh).
    + exact IHterm.
    + exact (proj1 (desugar_compat_nullify _ _ Hnullify)).
  - intros Gi x Ti Huniq Hbind. simpl.
    apply typing_var; [now apply uniq_map | now apply binds_map].
  - intros Gi Huniq. simpl.
    apply typing_null. now apply uniq_map.
  - intros L Gi Vi s Ti _ _ IH. simpl.
    apply typing_cast.
    + apply typing_abs with (L := L).
      intros x Hfresh. rewrite <- desugar_open.
      exact (IH x Hfresh).
    + apply compat_arrow; apply desugar_compat_refl.
  - intros Gi s t Ti Vi _ _ _ IHfun _ IHarg. simpl.
    eapply typing_app with (M := !!).
    + exact IHfun.
    + discriminate.
    + exact IHarg.
  - intros Gi f s t Ti Vi _ _ _ _ IHfun _ IHarg _ IHfallback. simpl.
    eapply typing_safe_app with (M := !!).
    + exact IHfun.
    + discriminate.
    + exact IHarg.
    + exact IHfallback.
  - intros Gi s Vi p Ti _ _ IH Hcompat. simpl.
    apply typing_cast; [exact IH | now apply desugar_compat_implicit].
  - intros L Gi Ti t Te u Vi _ _ _ IHbody _ IHterm Herase. simpl.
    eapply desugar_target_import.
    + apply typing_abs with (L := L).
      intros x Hfresh. rewrite <- desugar_open.
      exact (IHbody x Hfresh).
    + exact IHterm.
    + exact (proj1 (desugar_compat_erase _ _ Herase)).
Qed.
