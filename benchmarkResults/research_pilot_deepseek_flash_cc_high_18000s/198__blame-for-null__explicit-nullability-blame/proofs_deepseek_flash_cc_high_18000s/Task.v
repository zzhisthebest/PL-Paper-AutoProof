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

(** * Basic label facts *)

Lemma neglabel_invol : forall p, neglabel_fun (neglabel_fun p) = p.
Proof. destruct p; reflexivity. Qed.

Lemma neq_E_l_I_l : E_l <> I_l.
Proof. unfold I_l, fresh_label. intro H; symmetry in H.
  apply (Atom.fresh_not_in (E_l :: nil)). simpl. auto. Qed.
Lemma neq_E_l_E_intl : E_l <> E_intl.
Proof. unfold E_intl, fresh_label. intro H; symmetry in H.
  apply (Atom.fresh_not_in (E_l :: I_l :: nil)). simpl. auto. Qed.
Lemma neq_E_l_I_intl : E_l <> I_intl.
Proof. unfold I_intl, fresh_label. intro H; symmetry in H.
  apply (Atom.fresh_not_in (E_l :: I_l :: E_intl :: nil)). simpl. auto. Qed.
Lemma neq_I_l_E_intl : I_l <> E_intl.
Proof. unfold E_intl, fresh_label. intro H; symmetry in H.
  apply (Atom.fresh_not_in (E_l :: I_l :: nil)). simpl; auto. Qed.
Lemma neq_I_l_I_intl : I_l <> I_intl.
Proof. unfold I_intl, fresh_label. intro H; symmetry in H.
  apply (Atom.fresh_not_in (E_l :: I_l :: E_intl :: nil)). simpl; auto. Qed.
Lemma neq_E_intl_I_intl : E_intl <> I_intl.
Proof. unfold I_intl, fresh_label. intro H; symmetry in H.
  apply (Atom.fresh_not_in (E_l :: I_l :: E_intl :: nil)). simpl; auto. Qed.

Lemma atom_dists :
  E_l <> I_l /\ E_l <> E_intl /\ E_l <> I_intl /\
  I_l <> E_intl /\ I_l <> I_intl /\ E_intl <> I_intl.
Proof.
  repeat split; auto using neq_E_l_I_l, neq_E_l_E_intl, neq_E_l_I_intl,
    neq_I_l_E_intl, neq_I_l_I_intl, neq_E_intl_I_intl.
Qed.

Definition label_eq_dec : forall (p q : label), {p = q} + {p <> q}.
Proof. decide equality. Defined.

Lemma In_safe_EIlabels : forall l, In l SafeLabels -> In l EIlabels.
Proof.
  intros l H. unfold EIlabels, E_lab, I_lab, E_int, I_int in *.
  simpl in *. tauto.
Qed.

Lemma In_neg_safe_EIlabels : forall l, In l SafeLabels -> In (neglabel_fun l) EIlabels.
Proof.
  intros l Hl. unfold EIlabels, E_lab, I_lab, E_int, I_int in *.
  simpl in Hl |- *.
  destruct Hl as [H|[H|[H|[H|[H|[H|F]]]]]]; try contradiction; subst l;
    simpl in *; tauto.
Qed.

Lemma notin_I_lab_SafeLabels : ~ In I_lab SafeLabels.
Proof.
  pose proof atom_dists as AD. destruct AD as [d1 [d2 [d3 [d4 [d5 d6]]]]].
  unfold E_lab, I_lab, E_int, I_int, neglabel_fun.
  simpl. intros [H|[H|[H|[H|[H|[H|H]]]]]]; try discriminate; try contradiction;
    try (injection H; subst; congruence).
Qed.

Lemma notin_negE_lab_SafeLabels : ~ In (neglabel_fun E_lab) SafeLabels.
Proof.
  pose proof atom_dists as AD. destruct AD as [d1 [d2 [d3 [d4 [d5 d6]]]]].
  unfold E_lab, I_lab, E_int, I_int, neglabel_fun.
  simpl. intros [H|[H|[H|[H|[H|[H|H]]]]]]; try discriminate; try contradiction;
    try (injection H; subst; congruence).
Qed.

(** * Decomposing [sfor] proofs *)

Lemma sfor_abs_inv : forall T s l, sfor (t_abs T s) l -> sfor s l.
Proof. intros T s l H; inversion H; subst; assumption. Qed.

Lemma sfor_app_inv : forall t1 t2 l, sfor (t_app t1 t2) l -> sfor t1 l /\ sfor t2 l.
Proof. intros t1 t2 l H; inversion H; subst; auto. Qed.

Lemma sfor_app_safe_inv : forall t1 t2 t3 l,
  sfor (t_app_safe t1 t2 t3) l -> sfor t1 l /\ sfor t2 l /\ sfor t3 l.
Proof. intros t1 t2 t3 l H; inversion H; subst; auto. Qed.

Lemma sfor_cast_inv : forall s S p T l, sfor (t_cast s S p T) l -> sfor s l.
Proof. intros s S p T l H; inversion H; subst; assumption. Qed.

Lemma sfor_abs_replace : forall T r r' l,
  sfor (t_abs T r) l -> sfor r' l -> sfor (t_abs T r') l.
Proof. intros T r r' l H H'; apply sfor_abs; exact H'. Qed.

Lemma sfor_app_replace : forall r1 r2 r1' r2' l,
  sfor (t_app r1 r2) l -> sfor r1' l -> sfor r2' l -> sfor (t_app r1' r2') l.
Proof. intros r1 r2 r1' r2' l H H1 H2; apply sfor_app; assumption. Qed.

Lemma sfor_app_safe_replace : forall r1 r2 r3 r1' r2' r3' l,
  sfor (t_app_safe r1 r2 r3) l -> sfor r1' l -> sfor r2' l -> sfor r3' l ->
  sfor (t_app_safe r1' r2' r3') l.
Proof. intros r1 r2 r3 r1' r2' r3' l H H1 H2 H3; apply sfor_safe_app; assumption. Qed.

Lemma sfor_cast_replace : forall inner inner' S q T l,
  sfor (t_cast inner S q T) l -> sfor inner' l -> sfor (t_cast inner' S q T) l.
Proof.
  intros inner inner' S q T l H H'.
  inversion H; subst; [eapply sfor_cast_pos | eapply sfor_cast_neg | eapply sfor_cast_diff];
    eauto.
Qed.

Lemma sfors_cast_inv : forall s S p T ls,
  sfors (t_cast s S p T) ls -> sfors s ls.
Proof. intros s S p T ls H l Hl; apply (sfor_cast_inv _ _ _ _ _ (H l Hl)). Qed.

Lemma sfors_abs_inv : forall T s ls, sfors (t_abs T s) ls -> sfors s ls.
Proof. intros T s ls H l Hl; apply (sfor_abs_inv _ _ _ (H l Hl)). Qed.

Lemma sfors_app_inv : forall t1 t2 ls,
  sfors (t_app t1 t2) ls -> sfors t1 ls /\ sfors t2 ls.
Proof.
  intros t1 t2 ls H; split; intros l Hl;
    [apply (sfor_app_inv _ _ _ (H l Hl)) | apply (sfor_app_inv _ _ _ (H l Hl))].
Qed.

Lemma sfors_app_safe_inv : forall t1 t2 t3 ls,
  sfors (t_app_safe t1 t2 t3) ls -> sfors t1 ls /\ sfors t2 ls /\ sfors t3 ls.
Proof.
  intros t1 t2 t3 ls H. split.
  - intros l Hl. apply (sfor_app_safe_inv t1 t2 t3 l (H l Hl)).
  - split.
    + intros l Hl. apply (sfor_app_safe_inv t1 t2 t3 l (H l Hl)).
    + intros l Hl. apply (sfor_app_safe_inv t1 t2 t3 l (H l Hl)).
Qed.

(** * Subtyping relations transported through desugaring *)

(** * Reflexivity of the subtyping relations *)

Lemma sub_refl : forall T, psub T T /\ nsub T T.
Proof.
  induction T as [| M S IHS U IHU].
  - split; [apply psub_null_refl | apply nsub_null_refl].
  - destruct IHS as [HSps HSns]. destruct IHU as [HUps HUns].
    destruct M.
    + split.
      * apply psub_arrow_nullable; [apply null_mod_unsafe | apply null_mod_unsafe | assumption | assumption].
      * apply nsub_arrow_nullable; assumption.
    + split.
      * apply psub_arrow_nullable; [apply null_mod_safe | apply null_mod_safe | assumption | assumption].
      * apply nsub_arrow_nullable_safe; [right; reflexivity | assumption | assumption].
    + split.
      * apply psub_arrow_nn; assumption.
      * apply nsub_arrow_nn; assumption.
Qed.

Lemma psub_refl : forall T, psub T T.
Proof. intro T; apply (proj1 (sub_refl T)). Qed.

Lemma nsub_refl : forall T, nsub T T.
Proof. intro T; apply (proj2 (sub_refl T)). Qed.

Lemma ssub_pn : forall Ve Ve', ssub Ve Ve' ->
  psub (desugarTe Ve) (desugarTe Ve') /\ nsub (desugarTe Ve) (desugarTe Ve').
Proof.
  intros Ve Ve' H. induction H; cbn [desugarTe].
  - split; [apply psub_null_refl | apply nsub_null_refl].
  - split; [apply psub_null; apply null_mod_safe | apply nsub_null].
  - destruct IHssub1 as [H1p H1n]. destruct IHssub2 as [H2p H2n].
    split; [apply psub_arrow_nn | apply nsub_arrow_nn]; assumption.
  - destruct IHssub1 as [H1p H1n]. destruct IHssub2 as [H2p H2n].
    split; [apply psub_arrow_nn | apply nsub_arrow_nn]; assumption.
  - destruct IHssub1 as [H1p H1n]. destruct IHssub2 as [H2p H2n].
    split.
    + apply psub_arrow_nullable; [apply null_mod_safe | apply null_mod_safe | assumption | assumption].
    + apply nsub_arrow_nullable_safe; [right; reflexivity | assumption | assumption].
Qed.

Lemma ssub_psub : forall Ve Ve', ssub Ve Ve' -> psub (desugarTe Ve) (desugarTe Ve').
Proof. intros Ve Ve' H; exact (proj1 (ssub_pn Ve Ve' H)). Qed.

Lemma ssub_nsub : forall Ve Ve', ssub Ve Ve' -> nsub (desugarTe Ve) (desugarTe Ve').
Proof. intros Ve Ve' H; exact (proj2 (ssub_pn Ve Ve' H)). Qed.

Lemma nullify_pn : forall Ti Te, nullify Ti Te ->
  psub (desugarTe Te) (desugarTi Ti) /\ nsub (desugarTi Ti) (desugarTe Te).
Proof.
  intros Ti Te H. induction H; cbn [desugarTe desugarTi].
  - split; [apply psub_null_refl | apply nsub_null_refl].
  - destruct IHnullify1 as [H1p H1n]. destruct IHnullify2 as [H2p H2n].
    split.
    + apply psub_arrow_nullable; [apply null_mod_safe | apply null_mod_unsafe | assumption | assumption].
    + apply nsub_arrow_nullable; assumption.
Qed.

Lemma nullify_psub : forall Ti Te, nullify Ti Te -> psub (desugarTe Te) (desugarTi Ti).
Proof. intros Ti Te H; exact (proj1 (nullify_pn Ti Te H)). Qed.

Lemma nullify_nsub : forall Ti Te, nullify Ti Te -> nsub (desugarTi Ti) (desugarTe Te).
Proof. intros Ti Te H; exact (proj2 (nullify_pn Ti Te H)). Qed.

Lemma erase_pn : forall Te Ti, erase Te Ti ->
  psub (desugarTe Te) (desugarTi Ti) /\ nsub (desugarTi Ti) (desugarTe Te).
Proof.
  intros Te Ti H. induction H; cbn [desugarTe desugarTi].
  - split; [apply psub_null_refl | apply nsub_null_refl].
  - destruct IHerase1 as [H1p H1n]. destruct IHerase2 as [H2p H2n].
    split.
    + apply psub_arrow_nullable; [apply null_mod_safe | apply null_mod_unsafe | assumption | assumption].
    + apply nsub_arrow_nullable; assumption.
  - destruct IHerase1 as [H1p H1n]. destruct IHerase2 as [H2p H2n].
    split.
    + apply psub_arrow_nn; assumption.
    + apply nsub_arrow_nullable; assumption.
Qed.

Lemma erase_psub : forall Te Ti, erase Te Ti -> psub (desugarTe Te) (desugarTi Ti).
Proof. intros Te Ti H; exact (proj1 (erase_pn Te Ti H)). Qed.

Lemma erase_nsub : forall Te Ti, erase Te Ti -> nsub (desugarTi Ti) (desugarTe Te).
Proof. intros Te Ti H; exact (proj2 (erase_pn Te Ti H)). Qed.

(** * Generic insertion of casts *)

Lemma psub_NN_U : forall A B,
  psub (typ_mod_arrow mod_non_nullable A B) (typ_mod_arrow mod_unsafe A B).
Proof. intros; apply psub_arrow_nn; [apply nsub_refl | apply psub_refl]. Qed.

Lemma nsub_NN_U : forall A B,
  nsub (typ_mod_arrow mod_non_nullable A B) (typ_mod_arrow mod_unsafe A B).
Proof. intros; apply nsub_arrow_nn; [apply psub_refl | apply nsub_refl]. Qed.

Lemma sfor_cast_both : forall inner S q T l,
  psub S T -> nsub S T -> sfor inner l -> sfor (t_cast inner S q T) l.
Proof.
  intros inner S q T l Hp Hn Hi.
  destruct (label_eq_dec l q) as [-> | Hne1].
  - apply sfor_cast_pos; assumption.
  - destruct (label_eq_dec l (neglabel_fun q)) as [H | Hne2].
    + assert (Hq : q = neglabel_fun l) by (rewrite H; symmetry; apply neglabel_invol).
      rewrite Hq. apply sfor_cast_neg; assumption.
    + apply sfor_cast_diff; assumption.
Qed.

Lemma sfor_cast_psub_only : forall inner S q T l,
  psub S T -> l <> neglabel_fun q -> sfor inner l -> sfor (t_cast inner S q T) l.
Proof.
  intros inner S q T l Hp Hne Hi.
  destruct (label_eq_dec l q) as [-> | Hne1].
  - apply sfor_cast_pos; assumption.
  - apply sfor_cast_diff; assumption.
Qed.

Lemma sfor_cast_nsub_only : forall inner S q T l,
  nsub S T -> l <> q -> sfor inner l -> sfor (t_cast inner S q T) l.
Proof.
  intros inner S q T l Hn Hne Hi.
  destruct (label_eq_dec l (neglabel_fun q)) as [H | Hne2].
  - assert (Hq : q = neglabel_fun l) by (rewrite H; symmetry; apply neglabel_invol).
    rewrite Hq. apply sfor_cast_neg; assumption.
  - apply sfor_cast_diff; assumption.
Qed.

Lemma sfor_cast_user : forall inner S p T l,
  In l SafeLabels -> ~ In p EIlabels -> sfor inner l -> sfor (t_cast inner S p T) l.
Proof.
  intros inner S p T l Hl Hp Hi.
  apply sfor_cast_diff.
  - exact Hi.
  - intro H. apply Hp. rewrite <- H. apply In_safe_EIlabels. exact Hl.
  - intro H. apply Hp.
    replace p with (neglabel_fun l) by (rewrite H; apply neglabel_invol).
    apply In_neg_safe_EIlabels. exact Hl.
Qed.

(** * Base terms are safe *)

Lemma sfors_var_b : forall n, sfors (t_var_b n) SafeLabels.
Proof. intros n l Hl; apply sfor_varb. Qed.

Lemma sfors_var_f : forall x, sfors (t_var_f x) SafeLabels.
Proof. intros x l Hl; apply sfor_var. Qed.

Lemma sfors_null : sfors t_null SafeLabels.
Proof. intros l Hl; apply sfor_null. Qed.

(** * Psafe *)

Definition Psafe (t : trmEI) : Prop :=
  disjoint EIlabels (labels t) -> sfors (desugar t) SafeLabels.

(** * Opening inversion for desugared terms *)

Lemma sfors_desugar_open_inv :
  forall t k x,
    sfors (desugar (open_trmEI_wrt_trmEI_rec k (tei_var_f x) t)) SafeLabels ->
    sfors (desugar t) SafeLabels.
Proof.
  induction t as
    [ n | x0 | m
    | T s IHs
    | Ti s IHs Ui
    | s IHs t IHt m
    | s IHs t IHt u IHu m
    | s IHs Ve Te
    | s IHs Vi p Ti
    | Te s IHs Ti u IHu
    | Ti s IHs Te u IHu ];
    intros k x H.
  - apply sfors_var_b.
  - apply sfors_var_f.
  - apply sfors_null.
  - intros l Hl. cbn [desugar open_trmEI_wrt_trmEI_rec] in H |- *.
    apply sfor_abs.
    exact (IHs (S k) x (sfors_abs_inv _ _ _ H) l Hl).
  - intros l Hl. cbn [desugar open_trmEI_wrt_trmEI_rec] in H |- *.
    apply sfor_cast_both.
    + apply psub_NN_U.
    + apply nsub_NN_U.
    + apply sfor_abs.
      exact (IHs (S k) x (sfors_abs_inv _ _ _
               (sfors_cast_inv _ _ _ _ _ H)) l Hl).
  - intros l Hl. cbn [desugar open_trmEI_wrt_trmEI_rec] in H |- *.
    destruct (sfors_app_inv _ _ _ H) as [H1 H2].
    apply sfor_app.
    + exact (IHs k x H1 l Hl).
    + exact (IHt k x H2 l Hl).
  - intros l Hl. cbn [desugar open_trmEI_wrt_trmEI_rec] in H |- *.
    destruct (sfors_app_safe_inv _ _ _ _ H) as [H1 [H2 H3]].
    apply sfor_safe_app.
    + exact (IHs k x H1 l Hl).
    + exact (IHt k x H2 l Hl).
    + exact (IHu k x H3 l Hl).
  - intros l Hl. cbn [desugar open_trmEI_wrt_trmEI_rec] in H |- *.
    apply sfor_cast_replace with (inner := desugar (open_trmEI_wrt_trmEI_rec k (tei_var_f x) s)).
    + exact (H l Hl).
    + exact (IHs k x (sfors_cast_inv _ _ _ _ _ H) l Hl).
  - intros l Hl. cbn [desugar open_trmEI_wrt_trmEI_rec] in H |- *.
    apply sfor_cast_replace with (inner := desugar (open_trmEI_wrt_trmEI_rec k (tei_var_f x) s)).
    + exact (H l Hl).
    + exact (IHs k x (sfors_cast_inv _ _ _ _ _ H) l Hl).
  - intros l Hl. cbn [desugar open_trmEI_wrt_trmEI_rec] in H |- *.
    destruct (sfors_app_inv _ _ _ H) as [H1 H2].
    apply sfor_app.
    + apply sfor_abs.
      exact (IHu (S k) x (sfors_abs_inv _ _ _ H1) l Hl).
    + apply sfor_cast_replace with (inner := desugar (open_trmEI_wrt_trmEI_rec k (tei_var_f x) s)).
      * exact (H2 l Hl).
      * exact (IHs k x (sfors_cast_inv _ _ _ _ _ H2) l Hl).
  - intros l Hl. cbn [desugar open_trmEI_wrt_trmEI_rec] in H |- *.
    destruct (sfors_app_inv _ _ _ H) as [H1 H2].
    apply sfor_app.
    + apply sfor_abs.
      exact (IHu (S k) x (sfors_abs_inv _ _ _ H1) l Hl).
    + apply sfor_cast_replace with (inner := desugar (open_trmEI_wrt_trmEI_rec k (tei_var_f x) s)).
      * exact (H2 l Hl).
      * exact (IHs k x (sfors_cast_inv _ _ _ _ _ H2) l Hl).
Qed.

(** * Labels are invariant under opening with a variable *)

Lemma labels_open_var_rec : forall t k x,
  labels (open_trmEI_wrt_trmEI_rec k (tei_var_f x) t) = labels t.
Proof.
  induction t as
    [ n | x0 | m
    | T s IHs
    | Ti s IHs Ui
    | s IHs t IHt m
    | s IHs t IHt u IHu m
    | s IHs Ve Te
    | s IHs Vi p Ti
    | Te s IHs Ti u IHu
    | Ti s IHs Te u IHu ];
    intros k xx.
  - cbn [open_trmEI_wrt_trmEI_rec labels].
    destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [open_trmEI_wrt_trmEI_rec labels]. rewrite IHs. reflexivity.
  - cbn [open_trmEI_wrt_trmEI_rec labels]. rewrite IHs. reflexivity.
  - cbn [open_trmEI_wrt_trmEI_rec labels]. rewrite IHs, IHt. reflexivity.
  - cbn [open_trmEI_wrt_trmEI_rec labels]. rewrite IHs, IHt, IHu. reflexivity.
  - cbn [open_trmEI_wrt_trmEI_rec labels]. rewrite IHs. reflexivity.
  - cbn [open_trmEI_wrt_trmEI_rec labels]. rewrite IHs. reflexivity.
  - cbn [open_trmEI_wrt_trmEI_rec labels]. rewrite IHs, IHu. reflexivity.
  - cbn [open_trmEI_wrt_trmEI_rec labels]. rewrite IHs, IHu. reflexivity.
Qed.

Lemma labels_open_var : forall t x,
  labels (open_trmEI_wrt_trmEI t (tei_var_f x)) = labels t.
Proof. intros t x. apply labels_open_var_rec. Qed.

(** * Rule lemmas for [Psafe] *)

Lemma Psafe_var_f : forall x, Psafe (tei_var_f x).
Proof. intros x. unfold Psafe, disjoint. intros _ l Hl. cbn [desugar]. apply sfor_var. Qed.

Lemma Psafe_null_e : Psafe (tei_null mode_explicit).
Proof. unfold Psafe, disjoint. intros _ l Hl. cbn [desugar]. apply sfor_null. Qed.

Lemma Psafe_null_i : Psafe (tei_null mode_implicit).
Proof. unfold Psafe, disjoint. intros _ l Hl. cbn [desugar]. apply sfor_null. Qed.

Lemma Psafe_app : forall s t m, Psafe s -> Psafe t -> Psafe (tei_app s t m).
Proof.
  intros s t m Hs Ht. unfold Psafe, disjoint in *. cbn [labels] in *. intros Hdis l Hl.
  assert (H1 : forall y, In y EIlabels -> ~ In y (labels s)).
  { intros y Hy Hy2. apply (Hdis y Hy). rewrite in_app_iff. auto. }
  assert (H2 : forall y, In y EIlabels -> ~ In y (labels t)).
  { intros y Hy Hy2. apply (Hdis y Hy). rewrite in_app_iff. auto. }
  apply sfor_app.
  - exact (Hs H1 l Hl).
  - exact (Ht H2 l Hl).
Qed.

Lemma Psafe_app_safe : forall f s t m,
  Psafe f -> Psafe s -> Psafe t -> Psafe (tei_app_safe f s t m).
Proof.
  intros f s t m Hf Hs Ht. unfold Psafe, disjoint in *. cbn [labels] in *. intros Hdis l Hl.
  assert (H1 : forall y, In y EIlabels -> ~ In y (labels f)).
  { intros y Hy Hy2. apply (Hdis y Hy). rewrite in_app_iff. rewrite in_app_iff. auto. }
  assert (H2 : forall y, In y EIlabels -> ~ In y (labels s)).
  { intros y Hy Hy2. apply (Hdis y Hy). rewrite in_app_iff. rewrite in_app_iff. auto. }
  assert (H3 : forall y, In y EIlabels -> ~ In y (labels t)).
  { intros y Hy Hy2. apply (Hdis y Hy). rewrite in_app_iff. rewrite in_app_iff. auto. }
  apply sfor_safe_app.
  - exact (Hf H1 l Hl).
  - exact (Hs H2 l Hl).
  - exact (Ht H3 l Hl).
Qed.

Lemma Psafe_cast_exp : forall s Ve Te, Psafe s -> ssub Ve Te -> Psafe (tei_cast_exp s Ve Te).
Proof.
  intros s Ve Te Hs Hsub. unfold Psafe, disjoint in *. cbn [labels] in *. intros Hdis l Hl.
  apply sfor_cast_both.
  - apply ssub_psub. exact Hsub.
  - apply ssub_nsub. exact Hsub.
  - exact (Hs Hdis l Hl).
Qed.

Lemma Psafe_cast_imp : forall s Vi p Ti, Psafe s -> Psafe (tei_cast_imp s Vi p Ti).
Proof.
  intros s Vi p Ti Hs. unfold Psafe, disjoint in *. cbn [labels] in *. intros Hdis l Hl.
  assert (H1 : forall y, In y EIlabels -> ~ In y (labels s)).
  { intros y Hy Hy2. apply (Hdis y Hy). right. exact Hy2. }
  apply sfor_cast_user.
  - exact Hl.
  - intro Hp. exact (Hdis p Hp (or_introl eq_refl)).
  - exact (Hs H1 l Hl).
Qed.

Lemma Psafe_abs_exp : forall L Ve s,
  (forall x, x \notin L -> Psafe (open_trmEI_wrt_trmEI s (tei_var_f x))) ->
  Psafe (tei_abs_exp Ve s).
Proof.
  intros L Ve s IH. unfold Psafe, disjoint in *. cbn [labels] in *. intros Hdis.
  destruct (atom_fresh L) as [x Hx].
  assert (Hds : sfors (desugar s) SafeLabels).
  { apply (sfors_desugar_open_inv s 0 x).
    apply (IH x Hx). intros y Hy Hy2. rewrite labels_open_var in Hy2. exact (Hdis y Hy Hy2). }
  intros l Hl. apply sfor_abs. exact (Hds l Hl).
Qed.

Lemma Psafe_abs_imp : forall L Vi s Ti,
  (forall x, x \notin L -> Psafe (open_trmEI_wrt_trmEI s (tei_var_f x))) ->
  Psafe (tei_abs_imp Vi s Ti).
Proof.
  intros L Vi s Ti IH. unfold Psafe, disjoint in *. cbn [labels] in *. intros Hdis.
  destruct (atom_fresh L) as [x Hx].
  assert (Hds : sfors (desugar s) SafeLabels).
  { apply (sfors_desugar_open_inv s 0 x).
    apply (IH x Hx). intros y Hy Hy2. rewrite labels_open_var in Hy2. exact (Hdis y Hy Hy2). }
  intros l Hl. apply sfor_cast_both.
  - apply psub_NN_U.
  - apply nsub_NN_U.
  - apply sfor_abs. exact (Hds l Hl).
Qed.

Lemma Psafe_import_exp : forall L Te s Ti u,
  Psafe s ->
  (forall x, x \notin L -> Psafe (open_trmEI_wrt_trmEI u (tei_var_f x))) ->
  nullify Ti Te ->
  Psafe (tei_import_exp Te s Ti u).
Proof.
  intros L Te s Ti u Hs Hu Hnull. unfold Psafe, disjoint in *. cbn [labels] in *. intros Hdis.
  assert (Hds : forall y, In y EIlabels -> ~ In y (labels s)).
  { intros y Hy Hy2. apply (Hdis y Hy). rewrite in_app_iff. auto. }
  assert (Hdu : forall y, In y EIlabels -> ~ In y (labels u)).
  { intros y Hy Hy2. apply (Hdis y Hy). rewrite in_app_iff. auto. }
  destruct (atom_fresh L) as [x Hx].
  assert (Hdus : sfors (desugar u) SafeLabels).
  { apply (sfors_desugar_open_inv u 0 x).
    apply (Hu x Hx). intros y Hy Hy2. rewrite labels_open_var in Hy2. exact (Hdu y Hy Hy2). }
  intros l Hl. apply sfor_app.
  - apply sfor_abs. exact (Hdus l Hl).
  - apply sfor_cast_nsub_only.
    + apply nullify_nsub. exact Hnull.
    + intro H; rewrite H in Hl; exact (notin_I_lab_SafeLabels Hl).
    + exact (Hs Hds l Hl).
Qed.

Lemma Psafe_import_imp : forall L Ti s Te u,
  Psafe s ->
  (forall x, x \notin L -> Psafe (open_trmEI_wrt_trmEI u (tei_var_f x))) ->
  erase Te Ti ->
  Psafe (tei_import_imp Ti s Te u).
Proof.
  intros L Ti s Te u Hs Hu Her. unfold Psafe, disjoint in *. cbn [labels] in *. intros Hdis.
  assert (Hds : forall y, In y EIlabels -> ~ In y (labels s)).
  { intros y Hy Hy2. apply (Hdis y Hy). rewrite in_app_iff. auto. }
  assert (Hdu : forall y, In y EIlabels -> ~ In y (labels u)).
  { intros y Hy Hy2. apply (Hdis y Hy). rewrite in_app_iff. auto. }
  destruct (atom_fresh L) as [x Hx].
  assert (Hdus : sfors (desugar u) SafeLabels).
  { apply (sfors_desugar_open_inv u 0 x).
    apply (Hu x Hx). intros y Hy Hy2. rewrite labels_open_var in Hy2. exact (Hdu y Hy Hy2). }
  intros l Hl. apply sfor_app.
  - apply sfor_abs. exact (Hdus l Hl).
  - apply sfor_cast_psub_only.
    + apply erase_psub. exact Her.
    + intro H; rewrite H in Hl; exact (notin_negE_lab_SafeLabels Hl).
    + exact (Hs Hds l Hl).
Qed.

Scheme typingE_mut := Induction for typingE Sort Prop
  with typingI_mut := Induction for typingI Sort Prop.
Combined Scheme typing_mutind from typingE_mut, typingI_mut.

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
  change ((forall Ge t Te, typingE Ge t Te -> Psafe t) /\
          (forall Gi t Ti, typingI Gi t Ti -> Psafe t)).
  apply typing_mutind
    with (P := fun (Ge:ctxE) (t:trmEI) (Te:typE) (_:typingE Ge t Te) => Psafe t)
         (P0 := fun (Gi:ctxI) (t:trmEI) (Ti:typI) (_:typingI Gi t Ti) => Psafe t).
  - (* typingE_var *) intros Ge xei Te u b. apply Psafe_var_f.
  - (* typingE_null *) intros Ge u. apply Psafe_null_e.
  - (* typingE_abs *) intros L Ge Ve sei Te iHexp iHtyp iH.
    apply Psafe_abs_exp with L. intros x Hx. apply (iH x Hx).
  - (* typingE_app *) intros Ge sei tei Te Ve i i0 t IH1 t0 IH2.
    exact (Psafe_app sei tei mode_explicit IH1 IH2).
  - (* typingE_safe_app *) intros Ge fei sei tei Te Ve t IH1 t0 IH2 t1 IH3.
    exact (Psafe_app_safe fei sei tei mode_explicit IH1 IH2 IH3).
  - (* typingE_cast *) intros Ge sei Ve Te i t IH1 s.
    exact (Psafe_cast_exp sei Ve Te IH1 s).
  - (* typingE_import *) intros L Ge Te tei Ti uei Ve i i0 ityp IH t0 IH0 n.
    apply (Psafe_import_exp L Te tei Ti uei).
    + exact IH0.
    + intros x Hx. apply (IH x Hx).
    + exact n.
  - (* typingI_var *) intros Gi xei Ti u b. apply Psafe_var_f.
  - (* typingI_null *) intros Gi u. apply Psafe_null_i.
  - (* typingI_abs *) intros L Gi Vi sei Ti iHimp ityp IH.
    apply Psafe_abs_imp with L. intros x Hx. apply (IH x Hx).
  - (* typingI_app *) intros Gi sei tei Ti Vi i i0 t IH1 t0 IH2.
    exact (Psafe_app sei tei mode_implicit IH1 IH2).
  - (* typingI_safi_app *) intros Gi fei sei tei Ti Vi i i0 i1 t IH1 t0 IH2 t1 IH3.
    exact (Psafe_app_safe fei sei tei mode_implicit IH1 IH2 IH3).
  - (* typingI_cast *) intros Gi sei Vi p Ti i t IH c.
    exact (Psafe_cast_imp sei Vi p Ti IH).
  - (* typingI_import *) intros L Gi Ti tei Te uei Vi i i0 ityp IH t0 IH0 n.
    apply (Psafe_import_imp L Ti tei Te uei).
    + exact IH0.
    + intros x Hx. apply (IH x Hx).
    + exact n.
Qed.
