From Fsub Require Import Fm_Definitions.

Scheme typing_mut_ind := Induction for typing Sort Prop
with typing_comp_mut_ind := Induction for typing_record_comp Sort Prop.
Combined Scheme typing_mutual from typing_mut_ind, typing_comp_mut_ind.
Scheme expr_mut_ind := Induction for expr Sort Prop
with comp_mut_ind := Induction for record_comp Sort Prop.
Combined Scheme expr_mutual from expr_mut_ind, comp_mut_ind.
Scheme syntax_exp_ind := Induction for exp Sort Prop
with syntax_comp_ind := Induction for rec_comp Sort Prop.
Combined Scheme syntax_mutual from syntax_exp_ind, syntax_comp_ind.
Scheme red_mut_ind := Induction for red Sort Prop
with red_comp_mut_ind := Induction for red_record_comp Sort Prop.
Combined Scheme red_mutual from red_mut_ind, red_comp_mut_ind.

Local Ltac fresh_part :=
  repeat match goal with
  | H : _ `notin` (_ `union` _) |- _ => let H1 := fresh H in pose proof (notin_union_1 _ _ _ H) as H1; apply notin_union_2 in H
  end.
Local Ltac fresh_atom x H L :=
  destruct (atom_fresh L) as [x H]; fresh_part.

Local Hint Constructors wf_typ wf_env wf_sig type expr record_comp : core.
Local Hint Resolve binds_cons_2 binds_cons_3 : core.

Lemma wf_sig_env E R : wf_sig E R -> wf_env E.
Proof. induction 1; auto. Qed.

Definition type_scope (E F : env) :=
  forall X U, binds X (bind_sub U) E -> exists V, binds X (bind_sub V) F.

Lemma type_scope_cons E F x b c :
  type_scope E F ->
  (forall U, b = bind_sub U -> exists V, c = bind_sub V) ->
  type_scope (x ~ b ++ E) (x ~ c ++ F).
Proof.
  intros Hscope Hkind X U H.
  apply binds_cons_1 in H as [[-> Heq]|H].
  - destruct (Hkind U (eq_sym Heq)) as [V ->]. eauto.
  - destruct (Hscope _ _ H) as [V HV]. eauto.
Qed.

Lemma wf_typ_scope E T : wf_typ E T -> forall F, type_scope E F -> wf_typ F T.
Proof.
  induction 1; intros F HF; eauto.
  - destruct (HF _ _ H) as [V HV]. eauto.
  - eapply wf_typ_all with (L:=L); eauto.
    intros X HX. apply H1; auto. apply type_scope_cons; eauto.
Qed.

Lemma wf_typ_bound E X U :
  wf_env E -> binds X (bind_sub U) E -> wf_typ E U.
Proof.
  intros HE. induction HE; intros Hbind.
  - inversion Hbind.
  - apply binds_cons_1 in Hbind as [[_ Heq]|Hbind].
    + inversion Heq; subst. eapply wf_typ_scope; eauto.
      unfold type_scope; eauto.
    + eapply wf_typ_scope; [eauto|]. unfold type_scope; eauto.
  - apply binds_cons_1 in Hbind as [[_ Heq]|Hbind]; try discriminate.
    eapply wf_typ_scope; [eauto|]. unfold type_scope; eauto.
Qed.

Lemma wf_sig_scope E R : wf_sig E R ->
  forall F, wf_env F -> type_scope E F -> wf_sig F R.
Proof. induction 1; intros; eauto using wf_typ_scope. Qed.

Lemma wf_sig_bound E R l U :
  wf_sig E R -> Signatures.binds l (bind_sig U) R -> wf_typ E U.
Proof.
  induction 1; intros Hb.
  - apply Signatures.binds_nil_iff in Hb. contradiction.
  - apply Signatures.binds_cons_1 in Hb as [[_ Heq]|Hb].
    + inversion Heq; auto.
    + auto.
Qed.

Lemma wf_typ_type E T : wf_typ E T -> type T.
Proof.
  induction 1; eauto.
Qed.

Lemma normal_open_var T : forall k X,
  normal_form_typing (open_tt_rec k (typ_fvar X) T) =
  open_tt_rec k (typ_fvar X) (normal_form_typing T).
Proof.
  assert (Hmerge : forall T k X m,
    open_tt_rec k (typ_fvar X) (merge_mutability T m) =
    merge_mutability (open_tt_rec k (typ_fvar X) T) m).
  { intro U. induction U; intros; cbn [open_tt_rec merge_mutability]; try reflexivity.
    - destruct (k == n); reflexivity.
    - now rewrite IHU1, IHU2. }
  induction T; intros; cbn [open_tt_rec normal_form_typing]; try reflexivity.
  - destruct (k == n); reflexivity.
  - now rewrite IHT1, IHT2.
  - now rewrite IHT1, IHT2.
  - now rewrite IHT.
  - now rewrite Hmerge, IHT.
  - now rewrite IHT1, IHT2.
  - now rewrite IHT.
Qed.

Lemma wf_typ_merge E T m :
  wf_typ E T -> wf_typ E (merge_mutability T m).
Proof.
  destruct m. induction 1; cbn; eauto using wf_typ.
Qed.

Lemma wf_typ_normal E T : wf_typ E T -> wf_typ E (normal_form_typing T).
Proof.
  induction 1; cbn; eauto using wf_typ_merge.
  eapply wf_typ_all with (L:=L); eauto.
  intros X HX. unfold open_tt in *. rewrite <- normal_open_var.
  eapply wf_typ_scope; [eauto|].
  apply type_scope_cons; eauto. unfold type_scope; eauto.
Qed.

Lemma merge_idem T m :
  merge_mutability (merge_mutability T m) m = merge_mutability T m.
Proof. induction T; try reflexivity. exact (f_equal2 typ_int IHT1 IHT2). Qed.

Lemma normal_merge T m :
  normal_form_typing (merge_mutability T m) = merge_mutability (normal_form_typing T) m.
Proof.
  induction T; cbn [normal_form_typing merge_mutability]; try congruence.
  destruct m, m0. now rewrite merge_idem.
  exact (f_equal2 typ_int IHT1 IHT2).
Qed.

Lemma normal_idem T :
  normal_form_typing (normal_form_typing T) = normal_form_typing T.
Proof.
  induction T; try reflexivity.
  - exact (f_equal2 typ_arrow IHT1 IHT2).
  - exact (f_equal2 typ_all IHT1 IHT2).
  - exact (f_equal typ_box IHT).
  - change (normal_form_typing (merge_mutability (normal_form_typing T) m) = merge_mutability (normal_form_typing T) m).
    now rewrite normal_merge, IHT.
  - exact (f_equal2 typ_int IHT1 IHT2).
  - exact (f_equal (typ_record a) IHT).
Qed.

Lemma sub_regular E S T :
  sub E S T -> wf_env E /\ wf_typ E S /\ wf_typ E T.
Proof.
  induction 1; intuition eauto using wf_typ_bound.
  - eapply wf_typ_all with (L:=L); eauto.
    intros X HX. eapply wf_typ_scope.
    + exact (proj1 (proj2 (H1 X HX))).
    + apply type_scope_cons; eauto. unfold type_scope; eauto.
  - eapply wf_typ_all with (L:=L); eauto.
    intros X HX. exact (proj2 (proj2 (H1 X HX))).
Qed.

Lemma wf_typ_sub_refl E T :
  wf_typ E T -> wf_env E -> sub E T T.
Proof.
  induction 1; intros HE; eauto using sub.
  - eapply sub_all with (L:=L `union` dom E); eauto using sub.
Qed.

Lemma sub_normal_eq E S T :
  wf_env E -> wf_typ E S -> wf_typ E T ->
  normal_form_typing S = normal_form_typing T -> sub E S T.
Proof.
  intros HE HS HT H.
  apply sub_denormalize; auto. rewrite H.
  eauto using wf_typ_sub_refl, wf_typ_normal.
Qed.

Lemma sub_to_normal E T :
  wf_env E -> wf_typ E T -> sub E T (normal_form_typing T).
Proof. eauto using sub_normal_eq, wf_typ_normal, eq_sym, normal_idem. Qed.

Lemma sub_from_normal E T :
  wf_env E -> wf_typ E T -> sub E (normal_form_typing T) T.
Proof. eauto using sub_normal_eq, wf_typ_normal, normal_idem. Qed.

Lemma sub_weaken E S T :
  sub E S T -> forall F, wf_env F ->
  (forall X U, binds X (bind_sub U) E -> binds X (bind_sub U) F) ->
  sub F S T.
Proof.
  induction 1; intros F HF Hkeep;
    assert (Hscope : type_scope E F) by (unfold type_scope; eauto);
    eauto using sub, wf_typ_scope.
  eapply sub_all with (L:=L `union` dom F).
  - eauto.
  - intros X HX. fresh_part. apply H1; auto.
    + destruct (sub_regular _ _ _ H) as [_ [HT _]].
      constructor; eauto using wf_typ_scope.
    + intros Y U Hb. apply binds_cons_1 in Hb as [[-> ->]|Hb]; eauto.
Qed.

Lemma sub_weaken_cons E b x S T :
  sub E S T -> wf_env (x ~ b ++ E) -> sub (x ~ b ++ E) S T.
Proof. intros; eapply sub_weaken; eauto. Qed.

Lemma typing_sig_mutual :
  (forall E R e T, typing E R e T -> wf_sig E R) /\
  (forall E R r T, typing_record_comp E R r T -> wf_sig E R).
Proof. apply typing_mutual; auto. Qed.

Lemma typing_sig E R e T : typing E R e T -> wf_sig E R.
Proof. exact (proj1 typing_sig_mutual E R e T). Qed.

Lemma typing_comp_sig E R r T : typing_record_comp E R r T -> wf_sig E R.
Proof. exact (proj2 typing_sig_mutual E R r T). Qed.

Lemma wf_env_head E x b :
  wf_env (x ~ b ++ E) ->
  wf_typ E (match b with bind_sub T | bind_typ T => T end).
Proof. intro H; inversion H; subst; auto. Qed.

Lemma typing_term_binder_annotation L E R V e T :
  (forall x : atom, x `notin` L ->
    typing (x ~ bind_typ V ++ E) R (open_ee e x) T) -> wf_typ E V.
Proof.
  intros H. fresh_atom x Hx L.
  exact (wf_env_head _ _ _ (wf_sig_env _ _ (typing_sig _ _ _ _ (H x Hx)))).
Qed.

Lemma typing_type_binder_annotation L E R V e T :
  (forall X : atom, X `notin` L ->
    typing (X ~ bind_sub V ++ E) R (open_te e X) (open_tt T X)) -> wf_typ E V.
Proof.
  intros H. fresh_atom X HX L.
  exact (wf_env_head _ _ _ (wf_sig_env _ _ (typing_sig _ _ _ _ (H X HX)))).
Qed.

Definition env_incl (E F : env) :=
  forall x b, binds x b E -> binds x b F.
Definition sig_incl (R S : sig) :=
  forall l b, Signatures.binds l b R -> Signatures.binds l b S.

Lemma env_incl_scope E F : env_incl E F -> type_scope E F.
Proof. unfold env_incl, type_scope; eauto. Qed.

Lemma env_incl_cons E F x b :
  env_incl E F -> env_incl (x ~ b ++ E) (x ~ b ++ F).
Proof.
  intros H y c Hb. apply binds_cons_1 in Hb as [[-> ->]|Hb]; eauto.
Qed.

Lemma env_incl_push E x b : env_incl E (x ~ b ++ E).
Proof. unfold env_incl; auto. Qed.

Lemma wf_sig_incl E F R :
  wf_sig E R -> wf_env F -> env_incl E F -> wf_sig F R.
Proof. eauto using wf_sig_scope, env_incl_scope. Qed.

Lemma wf_sig_push E R x b :
  wf_sig E R -> wf_env (x ~ b ++ E) -> wf_sig (x ~ b ++ E) R.
Proof. eauto using wf_sig_incl, env_incl_push. Qed.

Local Hint Resolve typing_sig typing_comp_sig wf_sig_env : core.
Local Hint Constructors typing typing_record_comp : typing_rules.

Lemma typing_weaken_mutual :
  (forall E R e T, typing E R e T -> forall F S,
    env_incl E F -> sig_incl R S -> wf_sig F S -> typing F S e T) /\
  (forall E R r T, typing_record_comp E R r T -> forall F S,
    env_incl E F -> sig_incl R S -> wf_sig F S -> typing_record_comp F S r T).
Proof.
  apply typing_mutual; intros;
    try solve [unfold env_incl, sig_incl in *; eauto with typing_rules].

  - eapply typing_abs with (L:=L `union` dom F); auto.
    intros x Hx. fresh_part.
    apply H; auto using env_incl_cons.
    apply wf_sig_push; auto. constructor; eauto.
    eapply wf_typ_scope; [eapply typing_term_binder_annotation; eassumption|eauto using env_incl_scope].
  - eapply typing_tabs with (L:=L `union` dom F); auto.
    intros X HX. fresh_part.
    apply H; auto using env_incl_cons.
    apply wf_sig_push; auto. constructor; eauto.
    eapply wf_typ_scope; [eapply typing_type_binder_annotation; eassumption|eauto using env_incl_scope].
  - eapply typing_tapp; eauto. eapply sub_weaken; eauto.
  - eapply typing_sub; eauto. eapply sub_weaken; eauto.
  - eapply typing_let with (L:=L `union` dom F); eauto.
    intros x Hx. fresh_part.
    apply H0; auto using env_incl_cons.
    apply wf_sig_push; auto. constructor; eauto.
    eapply wf_typ_scope; [eapply typing_term_binder_annotation; eassumption|eauto using env_incl_scope].
Qed.

Lemma typing_weaken E R F S e T :
  typing E R e T -> env_incl E F -> sig_incl R S -> wf_sig F S ->
  typing F S e T.
Proof. exact (fun H => proj1 typing_weaken_mutual E R e T H F S). Qed.

Lemma typing_weaken_comp E R F S r T :
  typing_record_comp E R r T -> env_incl E F -> sig_incl R S -> wf_sig F S ->
  typing_record_comp F S r T.
Proof. exact (fun H => proj2 typing_weaken_mutual E R r T H F S). Qed.

Lemma typing_push E R x b e T :
  typing E R e T -> wf_env (x ~ b ++ E) -> typing (x ~ b ++ E) R e T.
Proof.
  intros H HF. eapply typing_weaken; eauto using env_incl_push, wf_sig_push.
  unfold sig_incl; auto.
Qed.

Lemma typing_expr_mutual :
  (forall E R e T, typing E R e T -> expr e) /\
  (forall E R r T, typing_record_comp E R r T -> record_comp r).
Proof.
  apply typing_mutual; eauto using wf_typ_type, typing_term_binder_annotation,
    typing_type_binder_annotation.
  intros. apply expr_tapp; auto.
  destruct (sub_regular _ _ _ s) as [_ [HW _]]. eauto using wf_typ_type.
Qed.

Lemma typing_expr E R e T : typing E R e T -> expr e.
Proof. exact (proj1 typing_expr_mutual E R e T). Qed.

Lemma typing_comp_expr E R r T : typing_record_comp E R r T -> record_comp r.
Proof. exact (proj2 typing_expr_mutual E R r T). Qed.

(* Opening a locally closed type at any index leaves it unchanged. *)
Lemma open_tt_rec_cancel T : forall i j X U,
  i <> j ->
  open_tt_rec i X T = open_tt_rec j U (open_tt_rec i X T) ->
  T = open_tt_rec j U T.
Proof.
  induction T; intros i j X U Hneq H; cbn [open_tt_rec] in *; try reflexivity.
  - destruct (i == n), (j == n); subst; try contradiction; auto.
    cbn [open_tt_rec] in H. destruct (n == n); congruence.
  - inversion H. f_equal; eauto.
  - inversion H. f_equal; eauto.
  - inversion H. f_equal; eauto.
  - inversion H. f_equal; eauto.
  - inversion H. f_equal; eauto.
  - inversion H. f_equal; eauto.
Qed.

Lemma type_open_closed T : type T -> forall k U, open_tt_rec k U T = T.
Proof.
  induction 1; intros k U; cbn [open_tt_rec]; try solve [f_equal; auto].
  f_equal; auto.
  fresh_atom X HX L. symmetry. eapply open_tt_rec_cancel with (i:=0) (X:=X).
  - discriminate.
  - symmetry. apply H1; auto.
Qed.

Fixpoint subst_ty (X : atom) (P T : typ) : typ :=
  match T with
  | typ_fvar Y => if Y === X then P else T
  | typ_arrow A B => typ_arrow (subst_ty X P A) (subst_ty X P B)
  | typ_all A B => typ_all (subst_ty X P A) (subst_ty X P B)
  | typ_box A => typ_box (subst_ty X P A)
  | typ_mut m A => typ_mut m (subst_ty X P A)
  | typ_int A B => typ_int (subst_ty X P A) (subst_ty X P B)
  | typ_record a A => typ_record a (subst_ty X P A)
  | _ => T
  end.

Fixpoint fv_ty (T : typ) : atoms :=
  match T with
  | typ_fvar X => {{ X }}
  | typ_arrow A B | typ_all A B | typ_int A B => fv_ty A `union` fv_ty B
  | typ_mut _ A | typ_box A | typ_record _ A => fv_ty A
  | _ => {}
  end.

Lemma subst_ty_fresh X P T : X `notin` fv_ty T -> subst_ty X P T = T.
Proof.
  induction T; cbn; intros H; fresh_part; try solve [f_equal; auto].
  destruct (a === X); subst; try reflexivity. exfalso; fsetdec.
Qed.

Lemma subst_ty_scope E T : wf_typ E T -> forall X P,
  X `notin` dom E -> subst_ty X P T = T.
Proof.
  assert (Hcancel : forall T i Y X P,
    X <> Y ->
    subst_ty X P (open_tt_rec i Y T) = open_tt_rec i Y T ->
    subst_ty X P T = T).
  { intro U. induction U; intros i Y X P Hneq H; cbn in *; try reflexivity;
      try solve [inversion H; f_equal; eauto].
    - exact H. }
  induction 1; intros Z P HX; cbn; try solve [f_equal; eauto].
  - destruct (X === Z) as [->|]; auto.
    exfalso. eapply binds_dom_contradiction; eauto.
  - f_equal; eauto.
    fresh_atom Y HY (L `union` {{ Z }}).
    eapply Hcancel with (i:=0) (Y:=Y); [fsetdec|].
    apply H1; [auto|]. simpl_env. fsetdec.
Qed.

Lemma subst_open_ty_rec X P T : type P -> forall k U,
  subst_ty X P (open_tt_rec k U T) =
  open_tt_rec k (subst_ty X P U) (subst_ty X P T).
Proof.
  intros HP. induction T; intros; cbn; try solve [f_equal; auto].
  - destruct (k == n); reflexivity.
  - destruct (a === X); eauto using eq_sym, type_open_closed.
Qed.

Lemma subst_open_ty X P T U :
  type P -> subst_ty X P (open_tt T U) = open_tt (subst_ty X P T) (subst_ty X P U).
Proof. intros HP. exact (subst_open_ty_rec X P T HP 0 U). Qed.

Lemma subst_open_ty_var X Y P T :
  type P -> Y <> X ->
  subst_ty X P (open_tt T Y) = open_tt (subst_ty X P T) Y.
Proof.
  intros. rewrite subst_open_ty by auto. cbn. destruct (Y === X); congruence.
Qed.

Lemma open_ty_intro X P T : X `notin` fv_ty T -> type P ->
  subst_ty X P (open_tt T X) = open_tt T P.
Proof.
  intros. rewrite subst_open_ty, subst_ty_fresh by auto.
  cbn. destruct (X === X); congruence.
Qed.

Lemma wf_typ_subst E T : wf_typ E T -> forall F X P,
  type P ->
  (forall Y U, binds Y (bind_sub U) E -> wf_typ F (subst_ty X P Y)) ->
  wf_typ F (subst_ty X P T).
Proof.
  induction 1; intros F Z P HP Hkeep; cbn; eauto.
  eapply wf_typ_all with (L:=L `union` {{ Z }}); eauto.
  intros X HX. fresh_part.
  assert (Hneq : X <> Z) by fsetdec.
  rewrite <- subst_open_ty_var by auto. apply H1; auto.
  intros Y U Hb. apply binds_cons_1 in Hb as [[-> Heq]|Hb].
  - cbn. destruct (X === Z); try contradiction. eauto.
  - eapply wf_typ_scope; [eauto|]. unfold type_scope; eauto.
Qed.

Lemma wf_typ_open E L V T U :
  wf_typ E U ->
  (forall X : atom, X `notin` L -> wf_typ (X ~ bind_sub V ++ E) (open_tt T X)) ->
  wf_typ E (open_tt T U).
Proof.
  intros HU HT. fresh_atom X HX (L `union` fv_ty T).
  assert (Htype : type U) by eauto using wf_typ_type.
  rewrite <- (open_ty_intro X U T) by auto.
  eapply wf_typ_subst; [apply HT; auto|exact Htype|].
  intros Y W Hb. cbn. destruct (Y === X) as [->|Hneq]; auto.
  apply binds_cons_1 in Hb as [[Heq _]|Hb]; [congruence|eauto].
Qed.

Lemma wf_typ_term_bound E x T :
  wf_env E -> binds x (bind_typ T) E -> wf_typ E T.
Proof.
  intros HE. induction HE; intros Hb; [inversion Hb| |].
  - apply binds_cons_1 in Hb as [[_ Heq]|Hb]; try discriminate.
    eapply wf_typ_scope; [eauto|]. unfold type_scope; eauto.
  - apply binds_cons_1 in Hb as [[_ Heq]|Hb].
    + inversion Heq; subst. eapply wf_typ_scope; [eauto|]. unfold type_scope; eauto.
    + eapply wf_typ_scope; [eauto|]. unfold type_scope; eauto.
Qed.

Lemma typing_wf_mutual :
  (forall E R e T, typing E R e T -> wf_typ E T) /\
  (forall E R r T, typing_record_comp E R r T -> wf_typ E T).
Proof.
  apply typing_mutual; intros; eauto using wf_sig_bound, wf_typ_term_bound, typing_term_binder_annotation,
    typing_type_binder_annotation.
  - assert (Hv : wf_typ E V) by eauto using typing_term_binder_annotation.
    constructor; auto. fresh_atom x HX L.
    eapply wf_typ_scope; [apply (H x HX)|].
    intros Y U Hb. apply binds_cons_1 in Hb as [[_ Heq]|Hb]; [discriminate|eauto].
  - inversion H; auto.
  - destruct (sub_regular _ _ _ s) as [_ [HW _]].
    inversion H; subst. eauto using wf_typ_open.
  - exact (proj2 (proj2 (sub_regular _ _ _ s))).
  - fresh_atom x HX L.
    eapply wf_typ_scope; [apply (H0 x HX)|].
    intros Y U Hb. apply binds_cons_1 in Hb as [[_ Heq]|Hb]; [discriminate|eauto].
  - inversion H; auto.
  - inversion H; subst. match goal with H' : wf_typ _ (typ_box _) |- _ => inversion H'; auto end.
  - inversion H; auto.
  - inversion H; subst. match goal with H' : wf_typ _ (typ_record _ _) |- _ => inversion H'; auto end.
Qed.

Lemma typing_wf E R e T : typing E R e T -> wf_typ E T.
Proof. exact (proj1 typing_wf_mutual E R e T). Qed.

(* Normalization is stable under substitution up to re-normalization.
   This is used for the denormalization rule in the substitution proof. *)
Lemma normal_subst_merge X P T m :
  normal_form_typing (subst_ty X P (merge_mutability T m)) =
  merge_mutability (normal_form_typing (subst_ty X P T)) m.
Proof.
  induction T; try reflexivity.
  - destruct m, m0. symmetry. apply merge_idem.
  - exact (f_equal2 typ_int IHT1 IHT2).
Qed.

Lemma normal_subst_normal X P T :
  normal_form_typing (subst_ty X P (normal_form_typing T)) =
  normal_form_typing (subst_ty X P T).
Proof.
  induction T; try reflexivity.
  - exact (f_equal2 typ_arrow IHT1 IHT2).
  - exact (f_equal2 typ_all IHT1 IHT2).
  - exact (f_equal typ_box IHT).
  - change (normal_form_typing (subst_ty X P (merge_mutability (normal_form_typing T) m)) =
      merge_mutability (normal_form_typing (subst_ty X P T)) m).
    now rewrite normal_subst_merge, IHT.
  - exact (f_equal2 typ_int IHT1 IHT2).
  - exact (f_equal (typ_record a) IHT).
Qed.

Definition subst_bounds (E F : env) X P :=
  forall Y U, binds Y (bind_sub U) E -> sub F (subst_ty X P Y) (subst_ty X P U).

Lemma subst_bounds_wf E F X P : subst_bounds E F X P ->
  forall Y U, binds Y (bind_sub U) E -> wf_typ F (subst_ty X P Y).
Proof. intros H Y U Hb. exact (proj1 (proj2 (sub_regular _ _ _ (H Y U Hb)))). Qed.

Lemma subst_bounds_push_sub E F X P Y T :
  subst_bounds E F X P -> Y <> X -> wf_env (Y ~ bind_sub (subst_ty X P T) ++ F) ->
  subst_bounds (Y ~ bind_sub T ++ E) (Y ~ bind_sub (subst_ty X P T) ++ F) X P.
Proof.
  intros H Hneq HF Z U Hb. apply binds_cons_1 in Hb as [[-> Heq]|Hb].
  - inversion Heq; subst. cbn. destruct (Y === X); try contradiction.
    eapply sub_trans_tvar; [apply binds_cons_2; reflexivity|].
    eauto using wf_typ_sub_refl, wf_typ_bound.
  - eauto using sub_weaken_cons.
Qed.

Lemma subst_bounds_push_typ E F X P y T :
  subst_bounds E F X P -> wf_env (y ~ bind_typ (subst_ty X P T) ++ F) ->
  subst_bounds (y ~ bind_typ T ++ E) (y ~ bind_typ (subst_ty X P T) ++ F) X P.
Proof.
  intros H HF Y U Hb. apply binds_cons_1 in Hb as [[_ Heq]|Hb]; try discriminate.
  eauto using sub_weaken_cons.
Qed.

Lemma sub_subst E S T : sub E S T -> forall F X P,
  wf_env F -> type P -> subst_bounds E F X P ->
  sub F (subst_ty X P S) (subst_ty X P T).
Proof.
  induction 1; intros F Z P HF HP Hkeep; cbn [subst_ty];
    try solve [eauto using sub, wf_typ_subst, subst_bounds_wf].
  - change (sub F (subst_ty Z P (typ_fvar X)) (subst_ty Z P (typ_fvar X))).
    eauto using wf_typ_sub_refl, wf_typ_subst, subst_bounds_wf.
  - eapply sub_all with (L:=L `union` (dom F `union` {{ Z }})); eauto.
    intros X HX. fresh_part. assert (Hneq : X <> Z) by fsetdec.
    assert (HF' : wf_env (X ~ bind_sub (subst_ty Z P T1) ++ F)).
    { destruct (sub_regular _ _ _ H) as [_ [HT _]].
      constructor; eauto using wf_typ_subst, subst_bounds_wf. }
    rewrite <- !subst_open_ty_var by auto.
    apply H1; eauto using subst_bounds_push_sub.
  - apply sub_inter_left; eauto using wf_typ_subst, subst_bounds_wf.
  - apply sub_inter_right; eauto using wf_typ_subst, subst_bounds_wf.
  - eapply sub_trans with (T2:=subst_ty Z P (normal_form_typing T1)).
    + eapply sub_normal_eq; eauto using wf_typ_subst, subst_bounds_wf, wf_typ_normal,
        eq_sym, normal_subst_normal.
    + eapply sub_trans with (T2:=subst_ty Z P (normal_form_typing T2)).
      * eauto.
      * eapply sub_normal_eq; eauto using wf_typ_subst, subst_bounds_wf, wf_typ_normal,
          normal_subst_normal.
Qed.

Lemma subst_bounds_head E X V P :
  sub E P V -> X `notin` dom E -> subst_bounds (X ~ bind_sub V ++ E) E X P.
Proof.
  intros Hsub HX Y U Hb.
  destruct (sub_regular _ _ _ Hsub) as [HE [HP HV]].
  cbn. destruct (Y === X) as [->|Hneq].
  - apply binds_cons_1 in Hb as [[_ Heq]|Hb].
    + inversion Heq; subst. rewrite (subst_ty_scope E) by auto. exact Hsub.
    + exfalso. eapply binds_dom_contradiction; eauto.
  - apply binds_cons_1 in Hb as [[Heq _]|Hb]; [congruence|].
    assert (HU : wf_typ E U) by eauto using wf_typ_bound.
    rewrite (subst_ty_scope E) by auto.
    eapply sub_trans_tvar; eauto using wf_typ_sub_refl.
Qed.

Lemma sub_open E L V S T P :
  sub E P V ->
  (forall X : atom, X `notin` L ->
    sub (X ~ bind_sub V ++ E) (open_tt S X) (open_tt T X)) ->
  sub E (open_tt S P) (open_tt T P).
Proof.
  intros Hsub Hbody.
  destruct (sub_regular _ _ _ Hsub) as [HE [HP HV]].
  assert (Htype : type P) by eauto using wf_typ_type.
  fresh_atom X HX (L `union` (dom E `union` (fv_ty S `union` fv_ty T))).
  rewrite <- (open_ty_intro X P S), <- (open_ty_intro X P T) by auto.
  eapply sub_subst; eauto using subst_bounds_head.
Qed.

Lemma open_ee_cancel :
  (forall e i j (x : atom) v, i <> j ->
    open_ee_rec i x e = open_ee_rec j v (open_ee_rec i x e) ->
    e = open_ee_rec j v e) /\
  (forall r i j (x : atom) v, i <> j ->
    open_ee_record_rec i x r = open_ee_record_rec j v (open_ee_record_rec i x r) ->
    r = open_ee_record_rec j v r).
Proof.
  apply syntax_mutual; intros; cbn [open_ee_rec open_ee_record_rec] in *;
    try reflexivity.
  1: { destruct (i == n), (j == n); subst; try contradiction; auto.
    cbn [open_ee_rec] in H0. destruct (n == n); congruence. }
  all: match goal with
  | H : context[open_ee_rec _ _ (open_ee_rec _ _ _)] |- _ =>
      injection H; intros; f_equal; eauto
  | H : context[open_ee_record_rec _ _ (open_ee_record_rec _ _ _)] |- _ =>
      injection H; intros; f_equal; eauto
  end.
Qed.

Lemma open_te_cancel :
  (forall e i j X U, i <> j ->
    open_te_rec i X e = open_te_rec j U (open_te_rec i X e) ->
    e = open_te_rec j U e) /\
  (forall r i j X U, i <> j ->
    open_te_record_rec i X r = open_te_record_rec j U (open_te_record_rec i X r) ->
    r = open_te_record_rec j U r).
Proof.
  apply syntax_mutual; intros; cbn [open_te_rec open_te_record_rec] in *;
    try reflexivity;
    match goal with
    | H : context[open_te_rec _ _ (open_te_rec _ _ _)] |- _ =>
        injection H; intros; f_equal; eauto using open_tt_rec_cancel
    | H : context[open_te_record_rec _ _ (open_te_record_rec _ _ _)] |- _ =>
        injection H; intros; f_equal; eauto using open_tt_rec_cancel
    end.
Qed.

Lemma open_ee_te_cancel :
  (forall e i j (x : atom) U,
    open_ee_rec i x e = open_te_rec j U (open_ee_rec i x e) ->
    e = open_te_rec j U e) /\
  (forall r i j (x : atom) U,
    open_ee_record_rec i x r = open_te_record_rec j U (open_ee_record_rec i x r) ->
    r = open_te_record_rec j U r).
Proof.
  apply syntax_mutual; intros; cbn [open_ee_rec open_ee_record_rec open_te_rec open_te_record_rec] in *;
    try reflexivity; try solve [destruct (i == n); reflexivity];
    match goal with
    | H : context[open_te_rec _ _ (open_ee_rec _ _ _)] |- _ =>
        injection H; intros; f_equal; eauto
    | H : context[open_te_record_rec _ _ (open_ee_record_rec _ _ _)] |- _ =>
        injection H; intros; f_equal; eauto
    end.
Qed.

Lemma open_te_ee_cancel :
  (forall e i j X v,
    open_te_rec i X e = open_ee_rec j v (open_te_rec i X e) ->
    e = open_ee_rec j v e) /\
  (forall r i j X v,
    open_te_record_rec i X r = open_ee_record_rec j v (open_te_record_rec i X r) ->
    r = open_ee_record_rec j v r).
Proof.
  apply syntax_mutual; intros; cbn [open_ee_rec open_ee_record_rec open_te_rec open_te_record_rec] in *;
    try assumption; try reflexivity;
    match goal with
    | H : context[open_ee_rec _ _ (open_te_rec _ _ _)] |- _ =>
        injection H; intros; f_equal; eauto
    | H : context[open_ee_record_rec _ _ (open_te_record_rec _ _ _)] |- _ =>
        injection H; intros; f_equal; eauto
    end.
Qed.

Lemma expr_open_ee_closed_mutual :
  (forall e, expr e -> forall k v, open_ee_rec k v e = e) /\
  (forall r, record_comp r -> forall k v, open_ee_record_rec k v r = r).
Proof.
  apply expr_mutual; intros; cbn [open_ee_rec open_ee_record_rec];
    try solve [f_equal; eauto].
  - f_equal. fresh_atom x HX L.
    symmetry. eapply (proj1 open_ee_cancel) with (i:=0) (x:=x); [discriminate|].
    symmetry. eauto.
  - f_equal. fresh_atom X HX L.
    symmetry. eapply (proj1 open_te_ee_cancel) with (i:=0) (X:=X).
    symmetry. eauto.
  - f_equal; auto. fresh_atom x HX L.
    symmetry. eapply (proj1 open_ee_cancel) with (i:=0) (x:=x); [discriminate|].
    symmetry. eauto.
Qed.

Lemma expr_open_te_closed_mutual :
  (forall e, expr e -> forall k U, open_te_rec k U e = e) /\
  (forall r, record_comp r -> forall k U, open_te_record_rec k U r = r).
Proof.
  apply expr_mutual; intros; cbn [open_te_rec open_te_record_rec];
    try solve [f_equal; eauto using type_open_closed].
  - f_equal; eauto using type_open_closed. fresh_atom x HX L.
    symmetry. eapply (proj1 open_ee_te_cancel) with (i:=0) (x:=x).
    symmetry. eauto.
  - f_equal; eauto using type_open_closed. fresh_atom X HX L.
    symmetry. eapply (proj1 open_te_cancel) with (i:=0) (X:=X); [discriminate|].
    symmetry. eauto.
  - f_equal; auto. fresh_atom x HX L.
    symmetry. eapply (proj1 open_ee_te_cancel) with (i:=0) (x:=x).
    symmetry. eauto.
Qed.

Lemma expr_open_ee_closed : forall e, expr e -> forall k v, open_ee_rec k v e = e.
Proof. exact (proj1 expr_open_ee_closed_mutual). Qed.

Lemma expr_open_te_closed : forall e, expr e -> forall k U, open_te_rec k U e = e.
Proof. exact (proj1 expr_open_te_closed_mutual). Qed.

Fixpoint map_exp (var : atom -> exp) (ann : typ -> typ) (e : exp) : exp :=
  match e with
  | exp_fvar x => var x
  | exp_abs T b => exp_abs (ann T) (map_exp var ann b)
  | exp_app f a => exp_app (map_exp var ann f) (map_exp var ann a)
  | exp_tabs T b => exp_tabs (ann T) (map_exp var ann b)
  | exp_tapp f T => exp_tapp (map_exp var ann f) (ann T)
  | exp_let a b => exp_let (map_exp var ann a) (map_exp var ann b)
  | exp_box a => exp_box (map_exp var ann a)
  | exp_unbox a => exp_unbox (map_exp var ann a)
  | exp_set_box a b => exp_set_box (map_exp var ann a) (map_exp var ann b)
  | exp_seal a => exp_seal (map_exp var ann a)
  | exp_record r => exp_record (map_comp var ann r)
  | exp_record_read a l => exp_record_read (map_exp var ann a) l
  | exp_record_write a l b => exp_record_write (map_exp var ann a) l (map_exp var ann b)
  | _ => e
  end
with map_comp (var : atom -> exp) (ann : typ -> typ) (r : rec_comp) : rec_comp :=
  match r with
  | rec_empty => rec_empty
  | rec_exp a e r => rec_exp a (map_exp var ann e) (map_comp var ann r)
  | rec_ref a l r => rec_ref a l (map_comp var ann r)
  end.

Definition replace_var (x : atom) (v : exp) (y : atom) :=
  if y === x then v else exp_fvar y.
Notation subst_e x v := (map_exp (replace_var x v) (fun T => T)).
Notation subst_r x v := (map_comp (replace_var x v) (fun T => T)).
Notation subst_te X P := (map_exp exp_fvar (subst_ty X P)).
Notation subst_tr X P := (map_comp exp_fvar (subst_ty X P)).

Lemma record_dom_map var ann r : record_dom (map_comp var ann r) = record_dom r.
Proof. induction r; cbn; congruence. Qed.

Fixpoint fv_exp (term : bool) (e : exp) : atoms :=
  match e with
  | exp_fvar x => if term then {{ x }} else {}
  | exp_abs T b | exp_tabs T b | exp_tapp b T =>
      (if term then {} else fv_ty T) `union` fv_exp term b
  | exp_app a b | exp_let a b | exp_set_box a b | exp_record_write a _ b =>
      fv_exp term a `union` fv_exp term b
  | exp_box a | exp_unbox a | exp_seal a | exp_record_read a _ => fv_exp term a
  | exp_record r => fv_comp term r
  | _ => {}
  end
with fv_comp (term : bool) (r : rec_comp) : atoms :=
  match r with
  | rec_empty => {}
  | rec_exp _ e r => fv_exp term e `union` fv_comp term r
  | rec_ref _ _ r => fv_comp term r
  end.

Lemma subst_e_fresh :
  (forall e x v, x `notin` fv_exp true e -> subst_e x v e = e) /\
  (forall r x v, x `notin` fv_comp true r -> subst_r x v r = r).
Proof.
  apply syntax_mutual; intros; cbn [fv_exp fv_comp map_exp map_comp] in *;
    fresh_part; try solve [f_equal; auto].
  unfold replace_var. destruct (a === x); subst; try reflexivity. exfalso; fsetdec.
Qed.

Lemma subst_te_fresh :
  (forall e X P, X `notin` fv_exp false e -> subst_te X P e = e) /\
  (forall r X P, X `notin` fv_comp false r -> subst_tr X P r = r).
Proof.
  apply syntax_mutual; intros; cbn [fv_exp fv_comp map_exp map_comp] in *;
    fresh_part; f_equal; auto using subst_ty_fresh.
Qed.

Lemma subst_e_open_ee :
  (forall e x v, expr v -> forall k u,
    subst_e x v (open_ee_rec k u e) = open_ee_rec k (subst_e x v u) (subst_e x v e)) /\
  (forall r x v, expr v -> forall k u,
    subst_r x v (open_ee_record_rec k u r) = open_ee_record_rec k (subst_e x v u) (subst_r x v r)).
Proof.
  apply syntax_mutual; intros;
    cbn [map_exp map_comp open_ee_rec open_ee_record_rec]; try solve [f_equal; auto].
  - destruct (k == n); reflexivity.
  - unfold replace_var. destruct (a === x); eauto using eq_sym, expr_open_ee_closed.
Qed.

Lemma subst_e_open_te :
  (forall e x v, expr v -> forall k U,
    subst_e x v (open_te_rec k U e) = open_te_rec k U (subst_e x v e)) /\
  (forall r x v, expr v -> forall k U,
    subst_r x v (open_te_record_rec k U r) = open_te_record_rec k U (subst_r x v r)).
Proof.
  apply syntax_mutual; intros;
    cbn [map_exp map_comp open_te_rec open_te_record_rec]; try solve [f_equal; auto].
  unfold replace_var. destruct (a === x); eauto using eq_sym, expr_open_te_closed.
Qed.

Lemma subst_te_open_ee :
  (forall e X P k u,
    subst_te X P (open_ee_rec k u e) = open_ee_rec k (subst_te X P u) (subst_te X P e)) /\
  (forall r X P k u,
    subst_tr X P (open_ee_record_rec k u r) = open_ee_record_rec k (subst_te X P u) (subst_tr X P r)).
Proof.
  apply syntax_mutual; intros;
    cbn [map_exp map_comp open_ee_rec open_ee_record_rec]; try solve [f_equal; auto].
  destruct (k == n); reflexivity.
Qed.

Lemma subst_te_open_te :
  (forall e X P, type P -> forall k U,
    subst_te X P (open_te_rec k U e) = open_te_rec k (subst_ty X P U) (subst_te X P e)) /\
  (forall r X P, type P -> forall k U,
    subst_tr X P (open_te_record_rec k U r) = open_te_record_rec k (subst_ty X P U) (subst_tr X P r)).
Proof.
  apply syntax_mutual; intros;
    cbn [map_exp map_comp open_te_rec open_te_record_rec];
    f_equal; auto using subst_open_ty_rec.
Qed.

Lemma open_ee_intro x v e : x `notin` fv_exp true e -> expr v ->
  subst_e x v (open_ee e x) = open_ee e v.
Proof.
  intros Hfresh Hv. unfold open_ee.
  rewrite (proj1 subst_e_open_ee) by exact Hv.
  rewrite (proj1 subst_e_fresh e x v Hfresh).
  cbn [map_exp]. unfold replace_var. destruct (x === x); congruence.
Qed.

Lemma open_te_intro X P e : X `notin` fv_exp false e -> type P ->
  subst_te X P (open_te e X) = open_te e P.
Proof.
  intros. unfold open_te. rewrite (proj1 subst_te_open_te), (proj1 subst_te_fresh) by auto.
  cbn. destruct (X === X); congruence.
Qed.

Definition map_binding (ann : typ -> typ) (b : binding) :=
  match b with bind_sub T => bind_sub (ann T) | bind_typ T => bind_typ (ann T) end.

Definition term_binds_map ann (E F : env) :=
  forall y U, binds y (bind_typ U) E -> binds y (bind_typ (ann U)) F.

Lemma term_binds_map_push ann E F y b :
  term_binds_map ann E F ->
  term_binds_map ann (y ~ b ++ E) (y ~ map_binding ann b ++ F).
Proof.
  intros H z U Hb. apply binds_cons_1 in Hb as [[-> Heq]|Hb].
  - destruct b; inversion Heq; subst; cbn; eauto.
  - eauto.
Qed.

Definition sig_binds_map ann (R S : sig) :=
  forall l U, Signatures.binds l (bind_sig U) R -> Signatures.binds l (bind_sig (ann U)) S.

Lemma subst_te_open_ee_var X P e (y : atom) :
  subst_te X P (open_ee e y) = open_ee (subst_te X P e) y.
Proof. unfold open_ee. rewrite (proj1 subst_te_open_ee). reflexivity. Qed.

Lemma subst_te_open_te_var X P e (Y : atom) :
  type P -> Y <> X ->
  subst_te X P (open_te e Y) = open_te (subst_te X P e) Y.
Proof.
  intros. unfold open_te. rewrite (proj1 subst_te_open_te) by auto.
  cbn. destruct (Y === X); congruence.
Qed.

Lemma typing_subst_type_mutual :
  (forall E R e T, typing E R e T -> forall F S X P,
    wf_sig F S -> type P -> subst_bounds E F X P ->
    term_binds_map (subst_ty X P) E F -> sig_binds_map (subst_ty X P) R S ->
    typing F S (subst_te X P e) (subst_ty X P T)) /\
  (forall E R r T, typing_record_comp E R r T -> forall F S X P,
    wf_sig F S -> type P -> subst_bounds E F X P ->
    term_binds_map (subst_ty X P) E F -> sig_binds_map (subst_ty X P) R S ->
    typing_record_comp F S (subst_tr X P r) (subst_ty X P T)).
Proof.
  apply typing_mutual; intros; cbn [map_exp map_comp subst_ty];
    try solve [eauto using sub_subst with typing_rules].
  - eapply typing_abs with (L:=L `union` dom F); auto.
    intros y Hy. fresh_part. rewrite <- subst_te_open_ee_var.
    assert (HF' : wf_env (y ~ bind_typ (subst_ty X P V) ++ F)).
    { constructor; eauto using wf_typ_subst, subst_bounds_wf, typing_term_binder_annotation. }
    eapply H; eauto using wf_sig_push, subst_bounds_push_typ.
    exact (term_binds_map_push (subst_ty X P) E F y (bind_typ V) ltac:(assumption)).
  - eapply typing_tabs with (L:=L `union` (dom F `union` {{ X }})); auto.
    intros Y HY. fresh_part. assert (Hneq : Y <> X) by fsetdec.
    rewrite <- subst_te_open_te_var, <- subst_open_ty_var by auto.
    assert (HF' : wf_env (Y ~ bind_sub (subst_ty X P V) ++ F)).
    { constructor; eauto using wf_typ_subst, subst_bounds_wf, typing_type_binder_annotation. }
    eapply H; eauto using wf_sig_push, subst_bounds_push_sub.
    exact (term_binds_map_push (subst_ty X P) E F Y (bind_sub V) ltac:(assumption)).
  - rewrite subst_open_ty by auto. eauto using sub_subst with typing_rules.
  - eapply typing_let with (L:=L `union` dom F); eauto.
    intros y Hy. fresh_part. rewrite <- subst_te_open_ee_var.
    assert (HF' : wf_env (y ~ bind_typ (subst_ty X P T1) ++ F)).
    { constructor; eauto using wf_typ_subst, subst_bounds_wf, typing_wf. }
    eapply H0; eauto using wf_sig_push, subst_bounds_push_typ.
    exact (term_binds_map_push (subst_ty X P) E F y (bind_typ T1) ltac:(assumption)).
  - apply typing_record_exp; rewrite ?record_dom_map; eauto.
  - apply typing_record_ref; rewrite ?record_dom_map; eauto.
Qed.

Lemma typing_open_type E R L V e T P :
  wf_sig E R -> sub E P V ->
  (forall X : atom, X `notin` L ->
    typing (X ~ bind_sub V ++ E) R (open_te e X) (open_tt T X)) ->
  typing E R (open_te e P) (open_tt T P).
Proof.
  intros HR Hsub Hbody.
  destruct (sub_regular _ _ _ Hsub) as [HE [HP HV]].
  assert (Htype : type P) by eauto using wf_typ_type.
  fresh_atom X HX (L `union` (dom E `union` (fv_exp false e `union` fv_ty T))).
  rewrite <- (open_te_intro X P e), <- (open_ty_intro X P T) by auto.
  eapply (proj1 typing_subst_type_mutual); eauto using subst_bounds_head.
  - intros y U Hb. apply binds_cons_1 in Hb as [[_ Heq]|Hb]; try discriminate.
    rewrite (subst_ty_scope E) by eauto using wf_typ_term_bound. exact Hb.
  - intros l U Hb. rewrite (subst_ty_scope E) by eauto using wf_sig_bound. exact Hb.
Qed.

Definition sub_incl (E F : env) :=
  forall Y U, binds Y (bind_sub U) E -> binds Y (bind_sub U) F.

Lemma sub_incl_scope E F : sub_incl E F -> type_scope E F.
Proof. unfold sub_incl, type_scope; eauto. Qed.

Lemma sub_incl_push E F y b :
  sub_incl E F -> sub_incl (y ~ b ++ E) (y ~ b ++ F).
Proof.
  intros H Y U Hb. apply binds_cons_1 in Hb as [[-> ->]|Hb]; eauto.
Qed.

Definition term_transport R E F x v :=
  forall y U, binds y (bind_typ U) E -> typing F R (replace_var x v y) U.

Lemma term_transport_push R E F x v y b :
  term_transport R E F x v -> y <> x -> wf_sig (y ~ b ++ F) R ->
  term_transport R (y ~ b ++ E) (y ~ b ++ F) x v.
Proof.
  intros H Hneq HF z U Hb. apply binds_cons_1 in Hb as [[-> Heq]|Hb].
  - unfold replace_var. destruct (y === x); try contradiction.
    subst. eauto with typing_rules.
  - eauto using typing_push.
Qed.

Lemma subst_e_open_ee_var x v e (y : atom) :
  expr v -> y <> x -> subst_e x v (open_ee e y) = open_ee (subst_e x v e) y.
Proof.
  intros. unfold open_ee. rewrite (proj1 subst_e_open_ee) by auto.
  cbn [map_exp]. unfold replace_var at 1. destruct (y === x); congruence.
Qed.

Lemma subst_e_open_te_var x v e (Y : atom) :
  expr v -> subst_e x v (open_te e Y) = open_te (subst_e x v e) Y.
Proof. intros. apply (proj1 subst_e_open_te); auto. Qed.

Lemma typing_subst_term_mutual :
  (forall E R e T, typing E R e T -> forall F x v,
    wf_sig F R -> expr v -> sub_incl E F -> term_transport R E F x v ->
    typing F R (subst_e x v e) T) /\
  (forall E R r T, typing_record_comp E R r T -> forall F x v,
    wf_sig F R -> expr v -> sub_incl E F -> term_transport R E F x v ->
    typing_record_comp F R (subst_r x v r) T).
Proof.
  apply typing_mutual; intros; cbn [map_exp map_comp];
    try solve [eauto using sub_weaken with typing_rules].
  - eapply typing_abs with (L:=L `union` (dom F `union` {{ x }})); auto.
    intros y Hy. fresh_part. assert (Hneq : y <> x) by fsetdec.
    rewrite <- subst_e_open_ee_var by auto.
    assert (HF' : wf_sig (y ~ bind_typ V ++ F) R).
    { apply wf_sig_push; auto. constructor; eauto using
        wf_typ_scope, sub_incl_scope, typing_term_binder_annotation. }
    apply H; eauto using sub_incl_push, term_transport_push.
  - eapply typing_tabs with (L:=L `union` (dom F `union` {{ x }})); auto.
    intros Y HY. fresh_part. assert (Hneq : Y <> x) by fsetdec.
    rewrite <- subst_e_open_te_var by auto.
    assert (HF' : wf_sig (Y ~ bind_sub V ++ F) R).
    { apply wf_sig_push; auto. constructor; eauto using
        wf_typ_scope, sub_incl_scope, typing_type_binder_annotation. }
    apply H; eauto using sub_incl_push, term_transport_push.
  - eapply typing_let with (L:=L `union` (dom F `union` {{ x }})); eauto.
    intros y Hy. fresh_part. assert (Hneq : y <> x) by fsetdec.
    rewrite <- subst_e_open_ee_var by auto.
    assert (HF' : wf_sig (y ~ bind_typ T1 ++ F) R).
    { apply wf_sig_push; auto. constructor; eauto using
        wf_typ_scope, sub_incl_scope, typing_term_binder_annotation. }
    apply H0; eauto using sub_incl_push, term_transport_push.
  - apply typing_record_exp; rewrite ?record_dom_map; eauto.
  - apply typing_record_ref; rewrite ?record_dom_map; eauto.
Qed.

Lemma typing_open_term E R L V e T v :
  typing E R v V ->
  (forall x : atom, x `notin` L ->
    typing (x ~ bind_typ V ++ E) R (open_ee e x) T) ->
  typing E R (open_ee e v) T.
Proof.
  intros Hv Hbody.
  assert (Hexpr : expr v) by eauto using typing_expr.
  fresh_atom x HX (L `union` (dom E `union` fv_exp true e)).
  rewrite <- (open_ee_intro x v e) by auto.
  eapply (proj1 typing_subst_term_mutual); eauto.
  - intros Y U Hb. apply binds_cons_1 in Hb as [[_ Heq]|Hb]; [discriminate|auto].
  - intros y U Hb. unfold replace_var. destruct (y === x) as [->|Hneq].
    + apply binds_cons_1 in Hb as [[_ Heq]|Hb].
      * inversion Heq; subst; auto.
      * exfalso. eapply binds_dom_contradiction; eauto.
    + apply binds_cons_1 in Hb as [[Heq _]|Hb]; [congruence|].
      eauto with typing_rules.
Qed.

Lemma normal_open_merge T m : forall k P,
  normal_form_typing (open_tt_rec k P (merge_mutability T m)) =
  merge_mutability (normal_form_typing (open_tt_rec k P T)) m.
Proof.
  induction T; intros; try reflexivity.
  - destruct m, m0. symmetry. apply merge_idem.
  - exact (f_equal2 typ_int (IHT1 k P) (IHT2 k P)).
Qed.

Lemma normal_open_normal T : forall k P,
  normal_form_typing (open_tt_rec k P (normal_form_typing T)) =
  normal_form_typing (open_tt_rec k P T).
Proof.
  induction T; intros; try reflexivity.
  - exact (f_equal2 typ_arrow (IHT1 k P) (IHT2 k P)).
  - exact (f_equal2 typ_all (IHT1 k P) (IHT2 (S k) P)).
  - exact (f_equal typ_box (IHT k P)).
  - change (normal_form_typing (open_tt_rec k P (merge_mutability (normal_form_typing T) m)) =
      merge_mutability (normal_form_typing (open_tt_rec k P T)) m).
    now rewrite normal_open_merge, IHT.
  - exact (f_equal2 typ_int (IHT1 k P) (IHT2 k P)).
  - exact (f_equal (typ_record a) (IHT k P)).
Qed.

(* The data of a runtime form, independently of any uses of subsumption. *)
Inductive runtime_shape :=
  | shape_abs (arg result : typ)
  | shape_tabs (bound body : typ)
  | shape_ref (sealed : bool) (contents : typ)
  | shape_record (sealed : bool) (field : atom -> typ -> Prop).

Definition permits_access E (sealed readonly : bool) U T :=
  sub E U T /\ (if readonly then True else sealed = false /\ sub E T U).

(* Readonly distributes through intersections. It restricts access to boxes
   and record fields, while leaving applications and instantiations available. *)
Fixpoint accepts E (shape : runtime_shape) (readonly : bool) (T : typ) : Prop :=
  match T with
  | typ_top => True
  | typ_fvar _ | typ_bvar _ => False
  | typ_arrow A B =>
      match shape with
      | shape_abs V U => sub E A V /\ sub E U B
      | _ => False
      end
  | typ_all A B =>
      match shape with
      | shape_tabs V U =>
          sub E A V /\ (forall P, sub E P A -> sub E (open_tt U P) (open_tt B P))
      | _ => False
      end
  | typ_box A =>
      match shape with
      | shape_ref sealed U => permits_access E sealed readonly U A
      | _ => False
      end
  | typ_record a A =>
      match shape with
      | shape_record sealed field => exists U, field a U /\ permits_access E sealed readonly U A
      | _ => False
      end
  | typ_int A B => accepts E shape readonly A /\ accepts E shape readonly B
  | typ_mut _ A => accepts E shape true A
  end.

Lemma accepts_readonly E shape T :
  accepts E shape false T -> accepts E shape true T.
Proof.
  induction T; cbn [accepts]; try tauto.
  - destruct shape; cbn; unfold permits_access; tauto.
  - destruct shape; cbn; unfold permits_access; firstorder.
Qed.

Lemma accepts_merge E shape T m ro :
  accepts E shape ro (merge_mutability T m) <-> accepts E shape true T.
Proof.
  induction T; try reflexivity.
  change ((accepts E shape ro (merge_mutability T1 m) /\
           accepts E shape ro (merge_mutability T2 m)) <->
          (accepts E shape true T1 /\ accepts E shape true T2)).
  now rewrite IHT1, IHT2.
Qed.

Lemma access_change E sealed ro U A B :
  sub E A B -> sub E B A ->
  permits_access E sealed ro U A -> permits_access E sealed ro U B.
Proof. unfold permits_access. destruct ro; intuition eauto using sub_trans. Qed.

Lemma accepts_normal E T : wf_typ E T -> wf_env E ->
  forall shape ro, accepts E shape ro (normal_form_typing T) <-> accepts E shape ro T.
Proof.
  induction 1; intros HE shape ro; try reflexivity.
  - destruct shape; try reflexivity. cbn [accepts normal_form_typing].
    pose proof (sub_to_normal E T1 HE H).
    pose proof (sub_from_normal E T1 HE H).
    pose proof (sub_to_normal E T2 HE H0).
    pose proof (sub_from_normal E T2 HE H0).
    intuition eauto using sub_trans.
  - destruct shape; try reflexivity.
    change ((sub E (normal_form_typing T1) bound /\
       (forall P, sub E P (normal_form_typing T1) ->
          sub E (open_tt body P) (open_tt (normal_form_typing T2) P))) <->
      (sub E T1 bound /\
       (forall P, sub E P T1 -> sub E (open_tt body P) (open_tt T2 P)))).
    pose proof (sub_to_normal E T1 HE H) as Hto.
    pose proof (sub_from_normal E T1 HE H) as Hfrom.
    assert (Hb : forall P, wf_typ E P ->
      sub E (open_tt (normal_form_typing T2) P) (open_tt T2 P) /\
      sub E (open_tt T2 P) (open_tt (normal_form_typing T2) P)).
    { intros P HP.
      assert (Hraw : wf_typ E (open_tt T2 P)) by eauto using wf_typ_open.
      assert (Hnorm : wf_typ E (open_tt (normal_form_typing T2) P)).
      { assert (Hall : wf_typ E (typ_all T1 T2)) by eauto.
        apply wf_typ_normal in Hall. inversion Hall; subst.
        eauto using wf_typ_open. }
      assert (Heq : normal_form_typing (open_tt (normal_form_typing T2) P) =
                    normal_form_typing (open_tt T2 P)) by apply normal_open_normal.
      split; eauto using sub_normal_eq. }
    split; intros [Ha Hr]; split; eauto using sub_trans.
    + intros P HP. destruct (sub_regular _ _ _ HP) as [_ [HPwf _]].
      destruct (Hb P HPwf) as [Hback _].
      eauto using sub_trans.
    + intros P HP. destruct (sub_regular _ _ _ HP) as [_ [HPwf _]].
      destruct (Hb P HPwf) as [_ Hforward].
      eauto using sub_trans.
  - destruct shape; try reflexivity.
    cbn [accepts normal_form_typing]. split; eapply access_change;
      eauto using sub_to_normal, sub_from_normal.
  - change (accepts E shape ro (merge_mutability (normal_form_typing T) mut_readonly) <->
            accepts E shape true T).
    rewrite accepts_merge. auto.
  - change ((accepts E shape ro (normal_form_typing T1) /\
             accepts E shape ro (normal_form_typing T2)) <->
            (accepts E shape ro T1 /\ accepts E shape ro T2)).
    now rewrite IHwf_typ1, IHwf_typ2.
  - destruct shape; try reflexivity. cbn [accepts normal_form_typing].
    split; intros [U [Hfield Haccess]]; exists U; split; auto;
      eapply access_change; eauto using sub_to_normal, sub_from_normal.
Qed.

Lemma accepts_sub E S T :
  sub E S T -> forall shape ro, accepts E shape ro S -> accepts E shape ro T.
Proof.
  induction 1; intros shape ro Hshape; cbn [accepts] in *;
    try solve [intuition eauto using accepts_readonly].
  - destruct shape; intuition eauto using sub_trans.
  - destruct shape; try contradiction.
    destruct Hshape as [Ha Hb]. split; eauto using sub_trans.
    intros P HP.
    eapply sub_trans; [apply Hb; eauto using sub_trans|].
    eapply sub_open; eauto.
  - destruct shape; try contradiction. eauto using access_change.
  - apply IHsub. destruct ro; auto using accepts_readonly.
  - destruct shape; [contradiction|contradiction|contradiction|].
    destruct Hshape as [U [Hfield Haccess]].
    exists U. eauto using access_change.
  - destruct shape; [contradiction|contradiction|contradiction|].
    destruct Hshape as [U [Hfield [Hup _]]].
    exists U. unfold permits_access. eauto using sub_trans.
  - destruct (sub_regular _ _ _ H1) as [HE _].
    apply (proj1 (accepts_normal _ _ H0 HE shape ro)).
    apply IHsub. apply (proj2 (accepts_normal _ _ H HE shape ro)); auto.
Qed.

Definition record_field R r a U :=
  exists l, record_lookup_ref a r = Some l /\ Signatures.binds l (bind_sig U) R.

Lemma record_lookup_fresh r a : a `notin` record_dom r -> record_lookup_ref a r = None.
Proof.
  induction r; cbn; auto. intros H. fresh_part.
  destruct (a === a0) as [->|]; [exfalso; fsetdec|auto].
Qed.

Lemma record_field_tail R a l r :
  a `notin` record_dom r ->
  forall b U, record_field R r b U -> record_field R (rec_ref a l r) b U.
Proof.
  intros Hfresh b U [q [Hlook Hbind]]. exists q. split; auto.
  cbn. destruct (b === a) as [->|]; auto.
  rewrite record_lookup_fresh in Hlook by auto. discriminate.
Qed.

Lemma accepts_fields E (fields fields' : atom -> typ -> Prop) sealed ro T :
  (forall a U, fields a U -> fields' a U) ->
  accepts E (shape_record sealed fields) ro T ->
  accepts E (shape_record sealed fields') ro T.
Proof.
  induction T in ro |- *; cbn [accepts]; intros; try tauto.
  - eauto.
  - intuition.
  - destruct H0 as [U [HF HU]]. eauto.
Qed.

Lemma record_value_accepts E R r T :
  typing_record_comp E R r T -> value_record_comp r ->
  accepts E (shape_record false (record_field R r)) false T.
Proof.
  induction 1; intros Hv; inversion Hv; subst; cbn [accepts]; auto.
  split.
  - exists T. split.
    + exists l. split; [cbn; destruct (a === a); congruence|assumption].
    + unfold permits_access.
      assert (HR : wf_sig E R) by eauto.
      assert (HT : wf_typ E T) by eauto using wf_sig_bound.
      assert (Hrefl : sub E T T) by eauto using wf_typ_sub_refl.
      auto.
  - eapply accepts_fields; [apply record_field_tail; auto|eauto].
Qed.

Definition seal_shape (shape : runtime_shape) :=
  match shape with
  | shape_ref _ U => shape_ref true U
  | shape_record _ fields => shape_record true fields
  | _ => shape
  end.

Lemma accepts_seal E shape T :
  accepts E shape true T -> accepts E (seal_shape shape) true T.
Proof.
  induction T; destruct shape; cbn [accepts seal_shape]; try tauto.
Qed.

Inductive runtime_form E R : exp -> runtime_shape -> Prop :=
  | form_abs L V e T :
      (forall x : atom, x `notin` L -> typing (x ~ bind_typ V ++ E) R (open_ee e x) T) ->
      runtime_form E R (exp_abs V e) (shape_abs V T)
  | form_tabs L V e T :
      (forall X : atom, X `notin` L ->
        typing (X ~ bind_sub V ++ E) R (open_te e X) (open_tt T X)) ->
      runtime_form E R (exp_tabs V e) (shape_tabs V T)
  | form_ref l T :
      Signatures.binds l (bind_sig T) R ->
      runtime_form E R (exp_ref l) (shape_ref false T)
  | form_record r :
      value_record_comp r ->
      runtime_form E R (exp_record r) (shape_record false (record_field R r))
  | form_sealed_ref l T :
      Signatures.binds l (bind_sig T) R ->
      runtime_form E R (exp_seal (exp_ref l)) (shape_ref true T)
  | form_sealed_record r :
      value_record_comp r ->
      runtime_form E R (exp_seal (exp_record r)) (shape_record true (record_field R r)).

Local Hint Constructors runtime_form value value_record_comp : core.

Lemma seal_value_inner e : value (exp_seal e) -> value e.
Proof. inversion 1; eauto. Qed.

Lemma seal_runtime_form E R e shape :
  value (exp_seal e) -> runtime_form E R e shape ->
  runtime_form E R (exp_seal e) (seal_shape shape).
Proof. intros Hv H; inversion Hv; subst; inversion H; subst; cbn [seal_shape]; eauto. Qed.

Lemma value_runtime E R e T :
  typing E R e T -> value e ->
  exists shape, runtime_form E R e shape /\ accepts E shape false T.
Proof.
  induction 1; intro Hv; try solve [inversion Hv].
  - exists (shape_abs V T1). split; eauto. cbn [accepts].
    assert (Hwf : wf_typ E (typ_arrow V T1)) by eauto using typing_wf, typing_abs.
    inversion Hwf; subst; split; eauto using wf_typ_sub_refl.
  - exists (shape_tabs V T1). split; eauto. cbn [accepts].
    assert (Hwf : wf_typ E (typ_all V T1)) by eauto using typing_wf, typing_tabs.
    inversion Hwf; subst. split; eauto using wf_typ_sub_refl.
    intros P HP. apply wf_typ_sub_refl; eauto.
    destruct (sub_regular _ _ _ HP) as [_ [HPwf _]]. eauto using wf_typ_open.
  - destruct (IHtyping Hv) as [shape [Hform Haccept]].
    exists shape. eauto using accepts_sub.
  - exists (shape_ref false T). split; eauto.
    cbn [accepts]. unfold permits_access.
    assert (Hrefl : sub E T T) by eauto using wf_typ_sub_refl, wf_sig_bound. auto.
  - destruct (IHtyping (seal_value_inner _ Hv)) as [shape [Hform Haccept]].
    exists (seal_shape shape). split; eauto using seal_runtime_form.
    cbn [accepts]. auto using accepts_readonly, accepts_seal.
  - inversion Hv; subst.
    exists (shape_record false (record_field R r)). eauto using record_value_accepts.
Qed.

(* Store typing connects every signature binding to a stored value and
   every stored value to its signature. Allocation and update preserve both. *)
Lemma typing_extend_sig E R R' e T :
  typing E R e T -> wf_sig E (R' ++ R) -> typing E (R' ++ R) e T.
Proof.
  intros H HR. eapply typing_weaken; eauto.
  - unfold env_incl; auto.
  - unfold sig_incl; eauto using Signatures.binds_app_3.
Qed.

Lemma typing_comp_extend_sig E R R' r T :
  typing_record_comp E R r T -> wf_sig E (R' ++ R) ->
  typing_record_comp E (R' ++ R) r T.
Proof.
  intros H HR. eapply typing_weaken_comp; eauto.
  - unfold env_incl; auto.
  - unfold sig_incl; eauto using Signatures.binds_app_3.
Qed.

Lemma wf_sig_uniq E R : wf_sig E R -> Signatures.uniq R.
Proof. induction 1; auto using Signatures.uniq_nil, Signatures.uniq_push. Qed.

Lemma sig_type_unique E R l T U :
  wf_sig E R -> Signatures.binds l (bind_sig T) R ->
  Signatures.binds l (bind_sig U) R -> T = U.
Proof.
  intros HR HT HU.
  pose proof (Signatures.binds_unique _ _ _ _ _ HT HU (wf_sig_uniq _ _ HR)).
  congruence.
Qed.

Lemma store_well_formed E R s : typing_store E R s -> well_formed_store s.
Proof.
  intros H l v Hv. destruct (proj2 (H l) _ Hv) as [T [Hval _]]. exact Hval.
Qed.

Lemma store_lookup E R s l T :
  typing_store E R s -> Signatures.binds l (bind_sig T) R ->
  exists v, LabelMapImpl.MapsTo l v s /\ typing E R v T /\ value v.
Proof. intros H. apply (proj1 (H l)). Qed.

Lemma store_read E R s l T v :
  typing_store E R s -> Signatures.binds l (bind_sig T) R ->
  LabelMapImpl.MapsTo l v s -> typing E R v T.
Proof.
  intros H Hb Hv. destruct (store_lookup _ _ _ _ _ H Hb) as [w [Hw [Ht _]]].
  assert (w = v) by eauto using LabelMapFacts.MapsTo_fun. subst. auto.
Qed.

Lemma store_fresh_label s v : ~ LabelMapImpl.MapsTo (fresh_label_for_store s) v s.
Proof.
  intros H. apply LabelMapImpl.elements_1 in H. apply InA_alt in H.
  destruct H as [[l w] [[Hl _] Hin]]. cbn in Hl.
  unfold fresh_label_for_store in Hl. subst l.
  apply (Label.fresh_not_in (List.map fst (LabelMapImpl.elements s))).
  exact (List.in_map fst _ _ Hin).
Qed.

Lemma store_fresh_sig E R s :
  typing_store E R s -> LabelSetImpl.notin (fresh_label_for_store s) (Signatures.dom R).
Proof.
  intros H Hin. apply Signatures.binds_In_inv in Hin as [[T] Hb].
  destruct (store_lookup _ _ _ _ _ H Hb) as [v [Hv _]].
  exact (store_fresh_label s v Hv).
Qed.

Lemma store_allocate E R s v T :
  typing_store E R s -> typing E R v T -> value v ->
  let l := fresh_label_for_store s in
  let S := l ~ bind_sig T ++ R in
  wf_sig E S /\ typing_store E S (LabelMapImpl.add l v s).
Proof.
  intros Hst Htyp Hval l S.
  assert (Hfresh : LabelSetImpl.notin l (Signatures.dom R)) by eauto using store_fresh_sig.
  assert (HS : wf_sig E S) by (unfold S; eauto using typing_wf).
  assert (Hkeep : sig_incl R S) by (unfold S, sig_incl; eauto using Signatures.binds_cons_3).
  assert (Hnew : Signatures.binds l (bind_sig T) S) by (apply Signatures.binds_cons_2; reflexivity).
  assert (Hweaken : forall w U, typing E R w U -> typing E S w U).
  { intros. eapply typing_weaken; eauto. unfold env_incl; auto. }
  split; auto. intros q. split.
  - intros U Hb. apply Signatures.binds_cons_1 in Hb as [[-> Heq]|Hb].
    + inversion Heq; subst. exists v. eauto using LabelMapImpl.add_1.
    + assert (l <> q).
      { intros ->. exact (Signatures.binds_dom_contradiction _ _ _ _ Hb Hfresh). }
      destruct (store_lookup _ _ _ _ _ Hst Hb) as [w [Hw [Ht Hwv]]].
      exists w. eauto using LabelMapImpl.add_2.
  - intros w Hw. apply LabelMapFacts.add_mapsto_iff in Hw as [[<- <-]|[_ Hw]].
    + exists T. eauto.
    + destruct (proj2 (Hst q) _ Hw) as [U [Hwv [Ht Hb]]].
      exists U. eauto.
Qed.

Lemma store_write E R s l v T :
  wf_sig E R -> typing_store E R s -> Signatures.binds l (bind_sig T) R ->
  value v -> typing E R v T -> typing_store E R (LabelMapImpl.add l v s).
Proof.
  intros HR Hst Hb Hv Ht q. split.
  - intros U Hu. destruct (Label.eq_dec l q) as [<-|Hneq].
    + assert (T = U) by eauto using sig_type_unique. subst.
      exists v. eauto using LabelMapImpl.add_1.
    + destruct (store_lookup _ _ _ _ _ Hst Hu) as [w [Hw [Hwt Hwv]]].
      exists w. eauto using LabelMapImpl.add_2.
  - intros w Hw. apply LabelMapFacts.add_mapsto_iff in Hw as [[<- <-]|[_ Hw]].
    + exists T. auto.
    + exact (proj2 (Hst q) w Hw).
Qed.

Lemma red_record_dom_mutual :
  (forall e s e' s', red e s e' s' -> True) /\
  (forall r s r' s', red_record_comp r s r' s' -> record_dom r = record_dom r').
Proof. apply red_mutual; cbn; congruence || auto. Qed.

Lemma red_record_dom r s r' s' :
  red_record_comp r s r' s' -> record_dom r = record_dom r'.
Proof. exact (proj2 red_record_dom_mutual r s r' s'). Qed.

Lemma arrow_runtime E R e A B :
  typing E R e (typ_arrow A B) -> value e ->
  exists L V b U, e = exp_abs V b /\
    (forall x : atom, x `notin` L -> typing (x ~ bind_typ V ++ E) R (open_ee b x) U) /\
    sub E A V /\ sub E U B.
Proof.
  intros H Hv. destruct (value_runtime _ _ _ _ H Hv) as [sh [Hform Haccept]].
  inversion Hform; subst; cbn [accepts] in Haccept; try contradiction.
  destruct Haccept. eauto 8.
Qed.

Lemma all_runtime E R e A B :
  typing E R e (typ_all A B) -> value e ->
  exists L V b U, e = exp_tabs V b /\
    (forall X : atom, X `notin` L ->
      typing (X ~ bind_sub V ++ E) R (open_te b X) (open_tt U X)) /\
    sub E A V /\
    (forall P, sub E P A -> sub E (open_tt U P) (open_tt B P)).
Proof.
  intros H Hv. destruct (value_runtime _ _ _ _ H Hv) as [sh [Hform Haccept]].
  inversion Hform; subst; cbn [accepts] in Haccept; try contradiction.
  destruct Haccept. eauto 8.
Qed.

Definition readonly_if (ro : bool) T := if ro then typ_mut mut_readonly T else T.
Definition seal_if (sealed : bool) e := if sealed then exp_seal e else e.

Lemma box_runtime E R e ro T :
  typing E R e (readonly_if ro (typ_box T)) -> value e ->
  exists l U sealed, e = seal_if sealed (exp_ref l) /\
    Signatures.binds l (bind_sig U) R /\ permits_access E sealed ro U T.
Proof.
  intros H Hv. destruct (value_runtime _ _ _ _ H Hv) as [sh [Hform Haccept]].
  destruct ro; inversion Hform; subst; cbn [accepts readonly_if] in Haccept;
    try contradiction.
  all: match goal with
  | Haccess : permits_access _ ?sealed _ ?U _,
    Hb : Signatures.binds ?l (bind_sig ?U) _ |- _ =>
      exists l, U, sealed; auto
  end.
Qed.

Lemma record_runtime E R e ro a T :
  typing E R e (readonly_if ro (typ_record a T)) -> value e ->
  exists r l U sealed, e = seal_if sealed (exp_record r) /\
    value_record_comp r /\ record_lookup_ref a r = Some l /\
    Signatures.binds l (bind_sig U) R /\ permits_access E sealed ro U T.
Proof.
  intros H Hv. destruct (value_runtime _ _ _ _ H Hv) as [sh [Hform Haccept]].
  destruct ro; inversion Hform; subst; cbn [accepts readonly_if] in Haccept; try contradiction.
  all: destruct Haccept as [U [[l [Hlook Hbind]] Haccess]];
    match type of Haccess with
    | permits_access _ ?sealed _ _ _ =>
        match goal with Hr : value_record_comp ?r |- _ => exists r, l, U, sealed end
    end; auto 8.
Qed.

Lemma sub_left_type E S T : sub E S T -> type S.
Proof. intro H. apply (wf_typ_type E). exact (proj1 (proj2 (sub_regular _ _ _ H))). Qed.

Lemma typed_body_e E R L V e T :
  (forall x : atom, x `notin` L -> typing (x ~ bind_typ V ++ E) R (open_ee e x) T) ->
  body_e e.
Proof. intros H. exists L. eauto using typing_expr. Qed.

Lemma unbox_value_steps E R v s ro T :
  typing E R v (readonly_if ro (typ_box T)) -> value v -> typing_store E R s ->
  exists e' s', red (exp_unbox v) s e' s'.
Proof.
  intros H Hv Hst.
  destruct (box_runtime _ _ _ _ _ H Hv) as [l [U [sealed [-> [Hb _]]]]].
  destruct (store_lookup _ _ _ _ _ Hst Hb) as [old [Hw [_ Hwv]]].
  destruct sealed; cbn [seal_if]; eexists; eexists.
  - eapply red_unbox_sealed_ref; eauto using store_well_formed.
  - eapply red_unbox_ref; eauto using store_well_formed.
Qed.

Lemma record_read_value_steps E R v s ro a T :
  typing E R v (readonly_if ro (typ_record a T)) -> value v -> typing_store E R s ->
  exists e' s', red (exp_record_read v a) s e' s'.
Proof.
  intros H Hv Hst.
  destruct (record_runtime _ _ _ _ _ _ H Hv) as [r [l [U [sealed [-> [Hrv [Hlook [Hb _]]]]]]]].
  destruct (store_lookup _ _ _ _ _ Hst Hb) as [old [Hw [_ Hwv]]].
  destruct sealed; cbn [seal_if]; eexists; eexists.
  - eapply red_sealed_record_read_ref; eauto using store_well_formed.
  - eapply red_record_read_ref; eauto using store_well_formed.
Qed.

Local Ltac take_step rule :=
  right; eexists; eexists; eapply rule;
  eauto using typing_expr, typing_comp_expr, store_well_formed, sub_left_type.

Lemma progress_mutual :
  (forall E R e T, typing E R e T -> E = empty ->
    forall s, typing_store E R s -> value e \/ exists e' s', red e s e' s') /\
  (forall E R r T, typing_record_comp E R r T -> E = empty ->
    forall s, typing_store E R s -> value_record_comp r \/ exists r' s', red_record_comp r s r' s').
Proof.
  apply typing_mutual; intros; subst E.
  - inversion b.
  - left. apply value_abs. eapply typing_expr. eapply typing_abs; eauto.
  - destruct (H eq_refl _ H2) as [Hv1|[e1' [s' Hstep]]].
    + destruct (H0 eq_refl _ H2) as [Hv2|[e2' [s' Hstep]]].
      * destruct (arrow_runtime _ _ _ _ _ t Hv1) as [L [V [b [U [-> _]]]]].
        inversion Hv1; subst. take_step red_abs.
      * take_step red_app_2.
    + take_step red_app_1.
  - left. apply value_tabs. eapply typing_expr. eapply typing_tabs; eauto.
  - destruct (H eq_refl _ H1) as [Hv|[e' [s' Hstep]]].
    + destruct (all_runtime _ _ _ _ _ t Hv) as [L [V [b [U [-> _]]]]].
      inversion Hv; subst. take_step red_tabs.
    + take_step red_tapp.
  - eauto.
  - assert (Hb : body_e e2) by eauto using typed_body_e.
    destruct (H eq_refl _ H2) as [Hv|[e' [s' Hstep]]].
    + take_step red_let.
    + take_step red_let_1.
  - destruct (H eq_refl _ H1) as [Hv|[e' [s' Hstep]]].
    + take_step red_box_ref.
    + take_step red_box_1.
  - destruct (H eq_refl _ H1) as [Hv|[e' [s' Hstep]]].
    + right. eapply unbox_value_steps with (ro:=false); eauto.
    + take_step red_unbox_1.
  - destruct (H eq_refl _ H2) as [Hv1|[e1' [s' Hstep]]].
    + destruct (H0 eq_refl _ H2) as [Hv2|[e2' [s' Hstep]]].
      * destruct (box_runtime _ _ _ false _ t Hv1)
          as [l [U [sealed [-> [Hb [_ [Hseal _]]]]]]]. subst sealed.
        destruct (store_lookup _ _ _ _ _ H2 Hb) as [old [Hw [_ Hwv]]].
        take_step red_set_box_ref.
      * take_step red_set_box_2.
    + take_step red_set_box_1.
  - eauto.
  - destruct (H eq_refl _ H1) as [Hv|[e' [s' Hstep]]].
    + inversion Hv; subst; eauto.
      * take_step red_seal_abs.
      * take_step red_seal_tabs.
      * take_step red_seal_sealed_ref.
      * take_step red_seal_sealed_record.
    + take_step red_seal_1.
  - destruct (H eq_refl _ H1) as [Hv|[e' [s' Hstep]]].
    + right. eapply unbox_value_steps with (ro:=true); eauto.
    + take_step red_unbox_1.
  - destruct (H eq_refl _ H1) as [Hv|[r' [s' Hstep]]]; [eauto|].
    take_step red_record.
  - destruct (H eq_refl _ H1) as [Hv|[e' [s' Hstep]]].
    + right. eapply record_read_value_steps with (ro:=false); eauto.
    + take_step red_record_read_1.
  - destruct (H eq_refl _ H1) as [Hv|[e' [s' Hstep]]].
    + right. eapply record_read_value_steps with (ro:=true); eauto.
    + take_step red_record_read_1.
  - destruct (H eq_refl _ H2) as [Hv1|[e1' [s' Hstep]]].
    + destruct (H0 eq_refl _ H2) as [Hv2|[e2' [s' Hstep]]].
      * destruct (record_runtime _ _ _ false _ _ t Hv1)
          as [r [l [U [sealed [-> [Hrv [Hlook [Hb [_ [Hseal _]]]]]]]]]]. subst sealed.
        destruct (store_lookup _ _ _ _ _ H2 Hb) as [old [Hw [_ Hwv]]].
        take_step red_record_write_ref.
      * take_step red_record_write_2.
    + take_step red_record_write_1.
  - eauto.
  - destruct (H0 eq_refl _ H2) as [Hv|[e' [s' Hstep]]].
    + take_step red_record_exp_2.
    + take_step red_record_exp_1.
  - destruct (H eq_refl _ H1) as [Hv|[r' [s' Hstep]]]; [eauto|].
    take_step red_record_ref.
Qed.

Lemma typing_by_sub E R e S T :
  typing E R e S -> sub E S T -> typing E R e T.
Proof. intros; eapply typing_sub; eauto. Qed.

Lemma typing_as_readonly E R e T :
  typing E R e T -> typing E R e (typ_mut mut_readonly T).
Proof.
  intros H. eapply typing_by_sub; [exact H|].
  apply sub_readonly_mutable. eauto using wf_typ_sub_refl, typing_wf.
Qed.

Lemma typing_beta E R V b arg A B :
  typing E R (exp_abs V b) (typ_arrow A B) -> expr (exp_abs V b) ->
  typing E R arg A -> typing E R (open_ee b arg) B.
Proof.
  intros H Hexpr Harg.
  destruct (arrow_runtime _ _ _ _ _ H (value_abs _ _ Hexpr))
    as [L [W [c [U [Heq [Hbody [Harg_sub Hres_sub]]]]]]].
  inversion Heq; subst.
  eapply typing_by_sub; [|exact Hres_sub].
  eapply typing_open_term; [eapply typing_by_sub; eauto|exact Hbody].
Qed.

Lemma typing_type_beta E R V b P A B :
  typing E R (exp_tabs V b) (typ_all A B) -> expr (exp_tabs V b) ->
  sub E P A -> typing E R (open_te b P) (open_tt B P).
Proof.
  intros H Hexpr Harg.
  destruct (all_runtime _ _ _ _ _ H (value_tabs _ _ Hexpr))
    as [L [W [c [U [Heq [Hbody [Hbound Hres_sub]]]]]]].
  inversion Heq; subst.
  eapply typing_by_sub; [|apply Hres_sub; exact Harg].
  eapply typing_open_type with (V:=W) (L:=L); [eauto| |exact Hbody].
  eapply sub_trans; eassumption.
Qed.

Lemma box_access E R l ro sealed T :
  typing E R (seal_if sealed (exp_ref l)) (readonly_if ro (typ_box T)) ->
  exists U, Signatures.binds l (bind_sig U) R /\ permits_access E sealed ro U T.
Proof.
  intros H. assert (Hv : value (seal_if sealed (exp_ref l))) by (destruct sealed; constructor).
  destruct (box_runtime _ _ _ _ _ H Hv) as [q [U [sealed' [Heq [Hb Haccess]]]]].
  destruct sealed, sealed'; cbn [seal_if] in Heq; inversion Heq; subst; eauto.
Qed.

Lemma record_access E R r a l ro sealed T :
  typing E R (seal_if sealed (exp_record r)) (readonly_if ro (typ_record a T)) ->
  value_record_comp r -> record_lookup_ref a r = Some l ->
  exists U, Signatures.binds l (bind_sig U) R /\ permits_access E sealed ro U T.
Proof.
  intros H Hr Hlook.
  assert (Hv : value (seal_if sealed (exp_record r))) by (destruct sealed; constructor; auto).
  destruct (record_runtime _ _ _ _ _ _ H Hv)
    as [r' [q [U [sealed' [Heq [_ [Hlook' [Hb Haccess]]]]]]]].
  destruct sealed, sealed'; cbn [seal_if] in Heq; inversion Heq; subst;
    assert (q = l) by congruence; subst; eauto.
Qed.

Lemma access_load E R s l v ro sealed U T :
  typing_store E R s -> LabelMapImpl.MapsTo l v s ->
  Signatures.binds l (bind_sig U) R -> permits_access E sealed ro U T ->
  typing E R (seal_if sealed v) (readonly_if ro T).
Proof.
  intros Hst Hmap Hb [Hup Hmode].
  assert (Ht : typing E R v T) by eauto using store_read, typing_by_sub.
  destruct ro, sealed; cbn [seal_if readonly_if] in *.
  - apply typing_seal; auto.
  - apply typing_as_readonly; auto.
  - destruct Hmode as [Hfalse _]. discriminate.
  - auto.
Qed.

Lemma access_swap E R s l old new U T :
  typing_store E R s -> LabelMapImpl.MapsTo l old s ->
  Signatures.binds l (bind_sig U) R -> permits_access E false false U T ->
  value new -> typing E R new T ->
  typing E R old T /\ typing_store E R (LabelMapImpl.add l new s).
Proof.
  intros Hst Hmap Hb [Hup [_ Hdown]] Hv Ht.
  split.
  - eauto using store_read, typing_by_sub.
  - eapply store_write; eauto using typing_by_sub.
Qed.

Local Ltac preservation_context :=
  match goal with
  | IH : forall s e' s', typing_store ?E ?R s -> red ?e s e' s' -> _,
    Hred : red ?e ?s ?e' ?s', Hstore : typing_store ?E ?R ?s |- _ =>
      let D := fresh "D" in let Hsig := fresh "Hsig" in
      let Htyped := fresh "Htyped" in let Hstore' := fresh "Hstore'" in
      destruct (IH s e' s' Hstore Hred) as [D [Hsig [Htyped Hstore']]];
      exists D; split; [exact Hsig|split; [|exact Hstore']]
  | IH : forall s r' s', typing_store ?E ?R s -> red_record_comp ?r s r' s' -> _,
    Hred : red_record_comp ?r ?s ?r' ?s', Hstore : typing_store ?E ?R ?s |- _ =>
      let D := fresh "D" in let Hsig := fresh "Hsig" in
      let Htyped := fresh "Htyped" in let Hstore' := fresh "Hstore'" in
      destruct (IH s r' s' Hstore Hred) as [D [Hsig [Htyped Hstore']]];
      exists D; split; [exact Hsig|split; [|exact Hstore']]
  end.

Local Ltac same_store :=
  exists sempty; cbn; split; [eauto|split; [|assumption]].

Lemma preservation_mutual :
  (forall E R e T, typing E R e T -> forall s e' s',
    typing_store E R s -> red e s e' s' ->
    exists R', wf_sig E (R' ++ R) /\ typing E (R' ++ R) e' T /\ typing_store E (R' ++ R) s') /\
  (forall E R r T, typing_record_comp E R r T -> forall s r' s',
    typing_store E R s -> red_record_comp r s r' s' ->
    exists R', wf_sig E (R' ++ R) /\ typing_record_comp E (R' ++ R) r' T /\ typing_store E (R' ++ R) s').
Proof.
  apply typing_mutual; intros; try solve [match goal with
    | Hred : red _ _ _ _ |- _ => inversion Hred
    | Hred : red_record_comp _ _ _ _ |- _ => inversion Hred
    end].
  - inversion H2; subst.
    + preservation_context. eapply typing_app; eauto using typing_extend_sig.
    + preservation_context. eapply typing_app; eauto using typing_extend_sig.
    + same_store. eauto using typing_beta.
  - inversion H1; subst.
    + preservation_context. eauto using typing_tapp.
    + same_store. eauto using typing_type_beta.
  - preservation_context. eauto using typing_by_sub.
  - inversion H2; subst.
    + preservation_context. eapply typing_let with (L:=L); eauto.
      intros x Hx. apply typing_extend_sig; auto. apply wf_sig_push; eauto.
    + same_store. eauto using typing_open_term.
  - inversion H1; subst.
    + preservation_context. eauto using typing_box.
    + destruct (store_allocate _ _ _ _ _ H0 t ltac:(assumption)) as [Hsig Hst].
      exists (fresh_label_for_store s ~ bind_sig T). split; auto.
      split; auto. eapply typing_ref; eauto.
  - inversion H1; subst.
    + preservation_context. eauto using typing_unbox.
    + same_store.
      destruct (box_access E R l false false T t) as [U [Hb Hacc]].
      eapply (access_load E R s' l _ false false); eauto.
    + same_store.
      destruct (box_access E R l false true T t) as [U [Hb [_ [Hbad _]]]].
      discriminate.
  - inversion H2; subst.
    + preservation_context. eapply typing_set_box; eauto using typing_extend_sig.
    + preservation_context. eapply typing_set_box; eauto using typing_extend_sig.
    + destruct (box_access E R l false false T t) as [U [Hb Hacc]].
      destruct (access_swap E R s l e' e2 U T H1 ltac:(assumption) Hb Hacc
        ltac:(assumption) t0) as [Hv Hst].
      exists sempty; cbn; auto.
  - inversion H1; subst.
    + preservation_context. eauto using typing_seal.
    + same_store. eauto using typing_as_readonly.
    + same_store. eauto using typing_as_readonly.
    + same_store. eauto using typing_as_readonly.
    + same_store. eauto using typing_as_readonly.
  - inversion H1; subst.
    + preservation_context. eauto using typing_unbox_readonly.
    + same_store.
      destruct (box_access E R l true false T t) as [U [Hb Hacc]].
      eapply (access_load E R s' l _ true false); eauto.
    + same_store.
      destruct (box_access E R l true true T t) as [U [Hb Hacc]].
      eapply (access_load E R s' l _ true true); eauto.
  - inversion H1; subst. preservation_context. eauto using typing_record.
  - inversion H1; subst.
    + preservation_context. eauto using typing_record_read.
    + same_store.
      destruct (record_access E R r a l false false T t ltac:(assumption) ltac:(assumption))
        as [U [Hb Hacc]].
      eapply (access_load E R s' l _ false false); eauto.
    + same_store.
      destruct (record_access E R r a l false true T t ltac:(assumption) ltac:(assumption))
        as [U [Hb [_ [Hbad _]]]]. discriminate.
  - inversion H1; subst.
    + preservation_context. eauto using typing_record_read_readonly.
    + same_store.
      destruct (record_access E R r a l true false T t ltac:(assumption) ltac:(assumption))
        as [U [Hb Hacc]].
      eapply (access_load E R s' l _ true false); eauto.
    + same_store.
      destruct (record_access E R r a l true true T t ltac:(assumption) ltac:(assumption))
        as [U [Hb Hacc]].
      eapply (access_load E R s' l _ true true); eauto.
  - inversion H2; subst.
    + preservation_context. eapply typing_record_write; eauto using typing_extend_sig.
    + preservation_context. eapply typing_record_write; eauto using typing_extend_sig.
    + destruct (record_access E R r a l false false T t ltac:(assumption) ltac:(assumption))
        as [U [Hb Hacc]].
      destruct (access_swap E R s l e' e2 U T H1 ltac:(assumption) Hb Hacc
        ltac:(assumption) t0) as [Hv Hst].
      exists sempty; cbn; eauto.
  - inversion H2; subst.
    + preservation_context. eauto using typing_record_exp, typing_comp_extend_sig.
    + destruct (store_allocate _ _ _ _ _ H1 t0 ltac:(assumption)) as [Hsig Hst].
      exists (fresh_label_for_store s ~ bind_sig T). split; auto.
      split; auto. eapply typing_record_ref; eauto using typing_comp_extend_sig.
  - inversion H1; subst. preservation_context.
    eapply typing_record_ref; eauto using Signatures.binds_app_3.
    erewrite <- red_record_dom by eassumption. assumption.
Qed.

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
  - intros E R e s e' s' T Htyping Hstore Hred.
    exact (proj1 preservation_mutual E R e T Htyping s e' s' Hstore Hred).
  - intros E R r s r' s' T Htyping Hstore Hred.
    exact (proj2 preservation_mutual E R r T Htyping s r' s' Hstore Hred).
Qed.

Theorem progress : forall e s R T,
  typing empty R e T ->
  typing_store empty R s ->
  value e \/ exists e' s', red e s e' s'
with progress_record_comp : forall r s R T,
  typing_record_comp empty R r T ->
  typing_store empty R s ->
  value_record_comp r \/ exists r' s', red_record_comp r s r' s'.
Proof.
  - intros e s R T Htyping Hstore.
    exact (proj1 progress_mutual empty R e T Htyping eq_refl s Hstore).
  - intros r s R T Htyping Hstore.
    exact (proj2 progress_mutual empty R r T Htyping eq_refl s Hstore).
Qed.
