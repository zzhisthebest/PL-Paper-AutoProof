From Stdlib Require Import List.
Require Import Metalib.Metatheory.
Require Import Blame.

Notation "G '⊢e' t ':' T" := (typingE G t T) (at level 40, t at level 59).

Notation "G '⊢i' t ':' T" := (typingI G t T) (at level 40, t at level 59).

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

Notation dTe Te := (desugarTe Te).

Notation dTi Ti := (desugarTi Ti).

Definition fresh_label (existing : list blame_label) : blame_label := MetatheoryAtom.Atom.fresh existing.

Definition E_l := fresh_label nil.

Definition I_l := fresh_label (E_l :: nil).

Definition E_intl := fresh_label (E_l :: I_l :: nil).

Definition I_intl := fresh_label (E_l :: I_l :: E_intl :: nil).

Definition E_lab := label_name E_l.

Definition I_lab := label_name I_l.

Definition E_int := label_name E_intl.

Definition I_int := label_name I_intl.

Definition EIlabels := E_lab ::
                       I_lab ::
                       ~~E_lab ::
                       ~~I_lab ::
                       E_int ::
                       I_int ::
                       ~~E_int ::
                       ~~I_int ::
                       nil.

Notation SafeLabels :=
  (~~I_lab :: E_lab :: I_int :: ~~I_int :: E_int :: ~~E_int :: nil).

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

Fixpoint labels t :=
  match t with
  | tei_var_b _ => nil
  | tei_var_f _ => nil
  | tei_null _ => nil
  | tei_abs_exp _ t => labels t
  | tei_abs_imp _ t _ => labels t
  | tei_app t u _ => labels t ++ labels u
  | tei_app_safe s t u _ => labels s ++ labels t ++ labels u
  | tei_cast_exp t Te Ue => labels t
  | tei_cast_imp t Ti p Ui => p :: labels t
  | tei_import_exp Te t Ti u => labels t ++ labels u
  | tei_import_imp Ti t Te u => labels t ++ labels u
  end.

Definition disjoint {A} (l1 l2 : list A) :=
  forall x, In x l1 -> ~(In x l2).

Notation sfors t ls := (forall l, In l ls -> sfor t l).

Lemma desugar_ssub : forall S T,
  ssub S T -> psub (dTe S) (dTe T) /\ nsub (dTe S) (dTe T).
Proof.
  intros S T H.
  induction H; cbn; intuition eauto using
    psub_null_refl, psub_null, psub_arrow_nn, psub_arrow_nullable,
    nsub_null_refl, nsub_null, nsub_arrow_nn, nsub_arrow_nullable_safe,
    null_mod_safe.
Qed.

Lemma desugar_implicit_refl : forall T,
  psub (dTi T) (dTi T) /\ nsub (dTi T) (dTi T).
Proof.
  induction T; cbn; intuition eauto using
    psub_null_refl, psub_arrow_nullable, null_mod_unsafe,
    nsub_null_refl, nsub_arrow_nullable.
Qed.

Lemma desugar_nullify : forall Ti Te,
  nullify Ti Te -> nsub (dTi Ti) (dTe Te) /\ psub (dTe Te) (dTi Ti).
Proof.
  intros Ti Te H.
  induction H; cbn; intuition eauto using
    nsub_null_refl, nsub_arrow_nullable, psub_null_refl,
    psub_arrow_nullable, null_mod_safe, null_mod_unsafe.
Qed.

Lemma desugar_erase : forall Te Ti,
  erase Te Ti -> psub (dTe Te) (dTi Ti) /\ nsub (dTi Ti) (dTe Te).
Proof.
  intros Te Ti H.
  induction H; cbn; intuition eauto using
    psub_null_refl, psub_arrow_nn, psub_arrow_nullable,
    null_mod_safe, null_mod_unsafe, nsub_null_refl, nsub_arrow_nullable.
Qed.

Lemma reserved_label_atoms_distinct :
  E_l <> I_l /\ E_l <> E_intl /\ E_l <> I_intl /\
  I_l <> E_intl /\ I_l <> I_intl /\ E_intl <> I_intl.
Proof.
  pose proof (Atom.fresh_not_in (E_l :: nil)) as HI.
  pose proof (Atom.fresh_not_in (E_l :: I_l :: nil)) as HEint.
  pose proof (Atom.fresh_not_in (E_l :: I_l :: E_intl :: nil)) as HIint.
  change (~ In I_l (E_l :: nil)) in HI.
  change (~ In E_intl (E_l :: I_l :: nil)) in HEint.
  change (~ In I_intl (E_l :: I_l :: E_intl :: nil)) in HIint.
  cbn [In] in *.
  tauto.
Qed.

Lemma import_labels_outside_safe :
  ~ In I_lab SafeLabels /\ ~ In (~~E_lab) SafeLabels.
Proof.
  pose proof reserved_label_atoms_distinct.
  unfold E_lab, I_lab, E_int, I_int.
  cbn [In neglabel_fun].
  intuition congruence.
Qed.

Lemma safe_labels_reserved : forall p,
  In p SafeLabels -> In p EIlabels /\ In (~~p) EIlabels.
Proof.
  intros p Hp.
  cbn [In] in Hp.
  unfold EIlabels.
  destruct Hp as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
    cbn [In neglabel_fun]; tauto.
Qed.

Lemma neglabel_involutive : forall p, ~~(~~p) = p.
Proof.
  destruct p; reflexivity.
Qed.

Lemma sfor_cast_by_label : forall s S T p q,
  sfor s p ->
  (p = q -> psub S T) ->
  (p = (~~q) -> nsub S T) ->
  sfor (t_cast s S q T) p.
Proof.
  intros s S T p q Hs Hpos Hneg.
  assert (label_eq_dec : forall a b : label, {a = b} + {a <> b}).
  { decide equality; apply Atom.eq_dec. }
  destruct (label_eq_dec p q) as [-> | Hpq].
  - apply sfor_cast_pos; auto.
  - destruct (label_eq_dec p (~~q)) as [-> | Hpnq].
    + rewrite <- (neglabel_involutive q) at 1.
      apply sfor_cast_neg; auto.
    + now apply sfor_cast_diff.
Qed.

Lemma labels_open_free : forall t x k,
  labels (open_trmEI_wrt_trmEI_rec k (tei_var_f x) t) = labels t.
Proof.
  induction t; intros x k; cbn;
    try solve [rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity].
  destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; reflexivity.
Qed.

Lemma sfor_desugar_open_free : forall t x k p,
  sfor (desugar (open_trmEI_wrt_trmEI_rec k (tei_var_f x) t)) p ->
  sfor (desugar t) p.
Proof.
  induction t; intros x k q Hsafe; cbn in *.
  - constructor.
  - constructor.
  - constructor.
  - inversion Hsafe; subst. econstructor; eauto.
  - inversion Hsafe; subst;
      match goal with
      | H : sfor (t_abs _ _) _ |- _ => inversion H; subst
      end;
      eauto 8 using sfor_abs, sfor_cast_pos, sfor_cast_neg, sfor_cast_diff.
  - inversion Hsafe; subst. econstructor; eauto.
  - inversion Hsafe; subst. econstructor; eauto.
  - inversion Hsafe; subst;
      eauto using sfor_cast_pos, sfor_cast_neg, sfor_cast_diff.
  - inversion Hsafe; subst;
      eauto using sfor_cast_pos, sfor_cast_neg, sfor_cast_diff.
  - inversion Hsafe; subst;
      match goal with
      | H : sfor (t_abs _ _) _ |- _ => inversion H; subst
      end;
      match goal with
      | H : sfor (t_cast _ _ _ _) _ |- _ => inversion H; subst
      end;
      eauto 8 using sfor_app, sfor_abs, sfor_cast_pos, sfor_cast_neg, sfor_cast_diff.
  - inversion Hsafe; subst;
      match goal with
      | H : sfor (t_abs _ _) _ |- _ => inversion H; subst
      end;
      match goal with
      | H : sfor (t_cast _ _ _ _) _ |- _ => inversion H; subst
      end;
      eauto 8 using sfor_app, sfor_abs, sfor_cast_pos, sfor_cast_neg, sfor_cast_diff.
Qed.

Lemma sfor_desugar_body : forall L t,
  (forall x, x \notin L ->
    disjoint EIlabels (labels (open_trmEI_wrt_trmEI t (tei_var_f x))) ->
    sfors (desugar (open_trmEI_wrt_trmEI t (tei_var_f x))) SafeLabels) ->
  disjoint EIlabels (labels t) ->
  sfors (desugar t) SafeLabels.
Proof.
  intros L t IH Hdisjoint p Hp.
  destruct (atom_fresh L) as [x Hx].
  eapply sfor_desugar_open_free with (x := x) (k := 0).
  apply (IH x Hx); [| exact Hp].
  unfold open_trmEI_wrt_trmEI.
  now rewrite labels_open_free.
Qed.

Lemma disjoint_app_parts {A} : forall (reserved left right : list A),
  disjoint reserved (left ++ right) ->
  disjoint reserved left /\ disjoint reserved right.
Proof.
  unfold disjoint.
  setoid_rewrite in_app_iff.
  firstorder.
Qed.

Scheme typingE_desugar_ind := Induction for typingE Sort Prop
with typingI_desugar_ind := Induction for typingI Sort Prop.
Combined Scheme typingEI_desugar_ind from typingE_desugar_ind, typingI_desugar_ind.

Theorem explicit_cant_be_blamed :
  (forall Ge t Te,
      Ge ⊢e t : Te ->
      disjoint EIlabels (labels t) ->
      sfors (desugar t) SafeLabels) /\
  (forall Gi t Ti,
      Gi ⊢i t : Ti ->
      disjoint EIlabels (labels t) ->
      sfors (desugar t) SafeLabels).
Proof.
  apply typingEI_desugar_ind.
  - intros. constructor.
  - intros. constructor.
  - intros L Ge Ve s Te Hexp Htyping IH Hdisjoint p Hp.
    apply sfor_abs.
    exact (sfor_desugar_body L s IH Hdisjoint p Hp).
  - intros Ge s t Te Ve Hs Ht Htyping_s IHs Htyping_t IHt Hdisjoint p Hp.
    apply disjoint_app_parts in Hdisjoint as [Hleft Hright].
    apply sfor_app; auto.
  - intros Ge f s t Te Ve Htyping_f IHf Htyping_s IHs Htyping_t IHt Hdisjoint p Hp.
    apply disjoint_app_parts in Hdisjoint as [Hleft Hrest].
    apply disjoint_app_parts in Hrest as [Hmid Hright].
    apply sfor_safe_app; auto.
  - intros Ge s Ve Te Hexp Htyping IH Hsub Hdisjoint p Hp.
    destruct (desugar_ssub _ _ Hsub) as [Hpos Hneg].
    apply sfor_cast_by_label; auto.
  - intros L Ge Te t Ti u Ve Himp Hexp Htyping_u IHu Htyping_t IHt Hnull Hdisjoint p Hp.
    apply disjoint_app_parts in Hdisjoint as [Hleft Hright].
    apply sfor_app.
    + apply sfor_abs.
      exact (sfor_desugar_body L u IHu Hright p Hp).
    + apply sfor_cast_by_label.
      * exact (IHt Hleft p Hp).
      * intros ->. exfalso. exact (proj1 import_labels_outside_safe Hp).
      * intros _. exact (proj1 (desugar_nullify _ _ Hnull)).
  - intros. constructor.
  - intros. constructor.
  - intros L Gi Vi s Ti Himp Htyping IH Hdisjoint p Hp.
    destruct (desugar_implicit_refl Vi) as [HVpos HVneg].
    destruct (desugar_implicit_refl Ti) as [HTpos HTneg].
    apply sfor_cast_by_label.
    + apply sfor_abs.
      exact (sfor_desugar_body L s IH Hdisjoint p Hp).
    + intros _. now apply psub_arrow_nn.
    + intros _. now apply nsub_arrow_nn.
  - intros Gi s t Ti Vi Hs Ht Htyping_s IHs Htyping_t IHt Hdisjoint p Hp.
    apply disjoint_app_parts in Hdisjoint as [Hleft Hright].
    apply sfor_app; auto.
  - intros Gi f s t Ti Vi Hf Hs Ht Htyping_f IHf Htyping_s IHs Htyping_t IHt Hdisjoint p Hp.
    apply disjoint_app_parts in Hdisjoint as [Hleft Hrest].
    apply disjoint_app_parts in Hrest as [Hmid Hright].
    apply sfor_safe_app; auto.
  - intros Gi s Vi q Ti Himp Htyping IH Hcompat Hdisjoint p Hp.
    destruct (safe_labels_reserved p Hp) as [Hreserved Hneg_reserved].
    apply sfor_cast_diff.
    + apply IH; [| exact Hp].
      intros l Hl Hin. apply (Hdisjoint l Hl). now right.
    + intros <-. apply (Hdisjoint p Hreserved). now left.
    + intros ->.
      rewrite neglabel_involutive in Hneg_reserved.
      apply (Hdisjoint q Hneg_reserved). now left.
  - intros L Gi Ti t Te u Vi Hexp Himp Htyping_u IHu Htyping_t IHt Herase Hdisjoint p Hp.
    apply disjoint_app_parts in Hdisjoint as [Hleft Hright].
    apply sfor_app.
    + apply sfor_abs.
      exact (sfor_desugar_body L u IHu Hright p Hp).
    + apply sfor_cast_by_label.
      * exact (IHt Hleft p Hp).
      * intros _. exact (proj1 (desugar_erase _ _ Herase)).
      * intros ->. exfalso. exact (proj2 import_labels_outside_safe Hp).
Qed.
