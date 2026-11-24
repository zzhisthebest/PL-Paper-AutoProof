Set Implicit Arguments.

Require Import LibExtra AbstractSyntax GeneralTyping.
Require Import Transformation TransformationTerm TransformationLifting.
Require Import TransformationConfig TransformationSwapCalls TransformationIterateSim.
Require Import ConfigTyping OperationalSemantics TypedOperationalSemantics.
Require Import TFree ConfigNotations InertContext HeapCorrespondence.
Require Import EnvCorrespondence ConfigTypingAccessories.
Require Import TransformationSimilarity Similarity SyntaxSimilarity ConfigSimilarity.
From Stdlib Require Import Lia Logic.Classical_Prop Arith.Wf_nat.
Require Import ReadableSyntax Equivalence Indep HeapUpdate ConfigVarkinds.

Local Lemma swap_calls_typed_step_erases mode G1 G2 C1 C2 T :
  typed_red mode G1 C1 T G2 C2 ->
  C1 ↦ C2.
Proof.
  intro Hstep. destruct Hstep; subst;
    eauto using red_read, red_write, red_call, red_apply, red_let_fun,
      red_let_var, red_let_push.
  apply red_let_obj; [assumption |].
  simpl in Hfr.
  destruct Hfr as [Hy [Hw _]].
  intro Heq. subst w.
  apply Hw. rewrite in_union, in_singleton. now right.
Qed.

Local Lemma swap_calls_typed_run_erases mode G1 G2 C1 C2 T n :
  typed_red_closure mode G1 C1 T n G2 C2 ->
  C1 ⊣n↦* C2.
Proof.
  intro Hrun. induction Hrun.
  - apply red_refl.
  - eapply red_trans; [exact IHHrun | eapply swap_calls_typed_step_erases; eassumption].
Qed.

Local Lemma swap_calls_free_open :
  (forall x t, tfree_trm x t -> forall k y, tfree_trm x (open_rec k y t)) /\
  (forall x l, tfree_lit x l -> forall k y, tfree_lit x (open_rec k y l)) /\
  (forall x d, tfree_def x d -> forall k y, tfree_def x (open_rec k y d)) /\
  (forall x ds, tfree_defs x ds -> forall k y, tfree_defs x (open_rec k y ds)).
Proof.
  apply (tfree_mutind
    (fun x t _ => forall k y, tfree_trm x (open_rec k y t))
    (fun x l _ => forall k y, tfree_lit x (open_rec k y l))
    (fun x d _ => forall k y, tfree_def x (open_rec k y d))
    (fun x ds _ => forall k y, tfree_defs x (open_rec k y ds))).
  all: intros; cbn;
    eauto using tfree_trm, tfree_lit, tfree_def, tfree_defs.
Qed.

Local Lemma swap_calls_binding_in_context x T G :
  ctx_binds x T G -> x \in ctx_dom G.
Proof.
  intro H. induction H; cbn; rewrite ?in_union, ?in_singleton; auto.
Qed.

Local Lemma swap_calls_var_in_context mode G e x T :
  ty_var mode G objctx_empty e x T -> x \in ctx_dom G.
Proof.
  intro H. induction H; eauto using swap_calls_binding_in_context.
Qed.

Local Definition rename_avar (f : var -> var) (a : avar) :=
  match a with avar_b n => avar_b n | avar_f x => avar_f (f x) end.

Local Lemma rename_open_avar f x k a :
  rename_avar f (open_rec k x a) = open_rec k (f x) (rename_avar f a).
Proof.
  destruct a; cbn; try reflexivity.
  unfold AvarOpenable. case_if; reflexivity.
Qed.

Local Definition avar_map (f : var -> var) (a : avar) (_ : nat) := rename_avar f a.

Local Lemma rename_open_types f :
  (forall T d k x,
      transform_typ (avar_map f) (open_rec_typ k x T) d =
      open_rec_typ k (f x) (transform_typ (avar_map f) T d)) /\
  (forall D d k x,
      transform_dec (avar_map f) (open_rec_dec k x D) d =
      open_rec_dec k (f x) (transform_dec (avar_map f) D d)).
Proof.
  apply typ_mutind; intros; cbn [open_rec_typ open_rec_dec transform_typ transform_dec]; 
    try reflexivity;
    f_equal; unfold avar_map; auto using rename_open_avar.
Qed.

Local Lemma rename_open_terms f :
  (forall t d k x,
      transform_trm (avar_map f) (open_rec_trm k x t) d =
      open_rec_trm k (f x) (transform_trm (avar_map f) t d)) /\
  (forall l d k x,
      transform_lit (avar_map f) (open_rec_lit k x l) d =
      open_rec_lit k (f x) (transform_lit (avar_map f) l d)) /\
  (forall v d k x,
      transform_def (avar_map f) (open_rec_def k x v) d =
      open_rec_def k (f x) (transform_def (avar_map f) v d)) /\
  (forall ds d k x,
      transform_defs (avar_map f) (open_rec_defs k x ds) d =
      open_rec_defs k (f x) (transform_defs (avar_map f) ds d)).
Proof.
  destruct (rename_open_types f) as [Htyp Hdec].
  apply trm_mutind; intros;
    cbn [open_rec_trm open_rec_lit open_rec_def open_rec_defs
         transform_trm transform_lit transform_def transform_defs];
    try reflexivity;
    f_equal; unfold avar_map; auto using rename_open_avar.
Qed.

Local Lemma rename_depth_types f :
  (forall T d d', transform_typ (avar_map f) T d = transform_typ (avar_map f) T d') /\
  (forall D d d', transform_dec (avar_map f) D d = transform_dec (avar_map f) D d').
Proof.
  apply typ_mutind; intros; cbn [transform_typ transform_dec avar_map];
    try reflexivity; f_equal; auto.
Qed.

Local Lemma rename_depth_terms f :
  (forall t d d', transform_trm (avar_map f) t d = transform_trm (avar_map f) t d') /\
  (forall l d d', transform_lit (avar_map f) l d = transform_lit (avar_map f) l d') /\
  (forall v d d', transform_def (avar_map f) v d = transform_def (avar_map f) v d') /\
  (forall ds d d', transform_defs (avar_map f) ds d = transform_defs (avar_map f) ds d').
Proof.
  destruct (rename_depth_types f) as [Htyp Hdec].
  apply trm_mutind; intros;
    cbn [transform_trm transform_lit transform_def transform_defs avar_map];
    try reflexivity; f_equal; auto.
Qed.

Local Definition preserves_fv {A : Set} {AF : FreeVar A} (f : var -> var) (a : A) :=
  forall x, x \in fv a -> f x = x.

Local Lemma rename_avar_fixed f a :
  preserves_fv f a -> rename_avar f a = a.
Proof.
  destruct a as [i | x]; cbn; auto.
  intro H. f_equal. apply H.
  change (x \in \{x}). rewrite in_singleton. reflexivity.
Qed.

Local Ltac fixed_fv :=
  unfold preserves_fv in *;
  cbn [fv TypFreeVar DecFreeVar TrmFreeVar LitFreeVar DefFreeVar DefsFreeVar
       fv_typ fv_dec fv_trm fv_lit fv_def fv_defs] in *;
  let x := fresh "x" in
  let H := fresh "Hmem" in
  intros x H;
  match goal with
  | Hfixed : forall y, y \in _ -> _ |- _ =>
      apply Hfixed; repeat rewrite in_union in *; solve [auto 8]
  end.

Local Lemma rename_fixed_types f :
  (forall T d, preserves_fv f T -> transform_typ (avar_map f) T d = T) /\
  (forall D d, preserves_fv f D -> transform_dec (avar_map f) D d = D).
Proof.
  apply typ_mutind; intros; cbn [transform_typ transform_dec];
    try reflexivity; f_equal;
    try (unfold avar_map; apply rename_avar_fixed; fixed_fv);
    match goal with
    | IH : forall d, preserves_fv _ _ -> _ |- _ =>
        apply IH; fixed_fv
    end.
Qed.

Local Lemma rename_fixed_terms f :
  (forall t d, preserves_fv f t -> transform_trm (avar_map f) t d = t) /\
  (forall l d, preserves_fv f l -> transform_lit (avar_map f) l d = l) /\
  (forall v d, preserves_fv f v -> transform_def (avar_map f) v d = v) /\
  (forall ds d, preserves_fv f ds -> transform_defs (avar_map f) ds d = ds).
Proof.
  destruct (rename_fixed_types f) as [Htyp Hdec].
  apply trm_mutind; intros;
    cbn [transform_trm transform_lit transform_def transform_defs];
    try reflexivity; f_equal;
    try solve [unfold avar_map; apply rename_avar_fixed; fixed_fv];
    try solve [apply Htyp; fixed_fv];
    first [match goal with
    | IH : forall d, preserves_fv _ _ -> _ |- _ =>
        apply IH; fixed_fv
    end | idtac].
Qed.

Local Definition rename (f : var -> var) {A : Set}
    {Ao : Openable A} {Af : FreeVar A} {As : SubstVar A}
    {Aa : AbstractSyntax Ao Af As}
    {Ar : TransformCollect.Transform AvarAbstractSyntax Aa} (a : A) :=
  TransformCollect.transform (avar_map f) a 0.

Local Fixpoint rename_ctx f G :=
  match G with
  | ctx_empty => ctx_empty
  | ctx_push G x vk T => ctx_push (rename_ctx f G) (f x) vk (rename f T)
  | ctx_hide G => ctx_hide (rename_ctx f G)
  | ctx_stop G => ctx_stop (rename_ctx f G)
  end.

Local Definition rename_objctx f Go :=
  match Go with
  | objctx_empty => objctx_empty
  | objctx_lit x T => objctx_lit (f x) (rename f T)
  | objctx_heap x T => objctx_heap (f x) (rename f T)
  end.

Local Lemma rename_ctx_fixed f G :
  (forall x, x \in ctx_dom G -> f x = x) ->
  preserves_fv f G -> rename_ctx f G = G.
Proof.
  induction G; intros Hdom Hfv; cbn [rename_ctx]; try reflexivity.
  - cbn [ctx_dom] in Hdom.
    unfold preserves_fv in Hfv. change (forall x, x \in fv t \u ctx_fv G -> f x = x) in Hfv.
    f_equal.
    + apply IHG.
      * intros x Hx. apply Hdom. rewrite in_union. auto.
      * intros x Hx. apply Hfv. rewrite in_union. auto.
    + apply Hdom. rewrite in_union, in_singleton. auto.
    + apply (proj1 (rename_fixed_types f)); fixed_fv.
  - f_equal. auto.
  - f_equal. auto.
Qed.

Local Ltac prove_rename_open H :=
  unfold rename;
  apply H.

Local Lemma rename_open_typ f k x (T : typ) :
  rename f (open_rec k x T) = open_rec k (f x) (rename f T).
Proof. prove_rename_open (proj1 (rename_open_types f)). Qed.

Local Lemma rename_open_trm f k x (t : trm) :
  rename f (open_rec k x t) = open_rec k (f x) (rename f t).
Proof. prove_rename_open (proj1 (rename_open_terms f)). Qed.

Local Lemma rename_open_defs f k x (ds : defs) :
  rename f (open_rec k x ds) = open_rec k (f x) (rename f ds).
Proof. prove_rename_open (proj2 (proj2 (proj2 (rename_open_terms f)))). Qed.

Local Lemma rename_objctx_concat f G Go :
  rename_ctx f (G §§& Go) = rename_ctx f G §§& rename_objctx f Go.
Proof. destruct Go; cbn [rename_ctx ctx_obj rename_objctx]; rewrite ?rename_open_typ; reflexivity. Qed.

Local Lemma rename_and f S T :
  rename f (typ_and S T) = typ_and (rename f S) (rename f T).
Proof. reflexivity. Qed.

Local Lemma rename_objctx_method f m G Go arg TZ recv TC :
  rename_ctx f (ctx_obj_met m G Go arg TZ recv TC) =
  ctx_obj_met m (rename_ctx f G) (rename_objctx f Go)
    (f arg) (rename f TZ) (f recv) (rename f TC).
Proof.
  destruct Go; cbn [ctx_obj_met rename_objctx];
    destruct (mode_visibility' m); cbn [rename_ctx]; repeat rewrite rename_and; rewrite ?rename_open_typ;
    reflexivity.
Qed.

Local Lemma rename_binds f G x T :
  (forall x y, f x = f y -> x = y) ->
  ctx_binds x T G -> ctx_binds (f x) (rename f T) (rename_ctx f G).
Proof.
  intros Hinj Hbind. induction Hbind; cbn [rename_ctx];
    eauto using ctx_binds.
Qed.

Local Lemma rename_vis f G x :
  (forall x y, f x = f y -> x = y) ->
  ctx_vis G x -> ctx_vis (rename_ctx f G) (f x).
Proof.
  intros Hinj Hvis. induction Hvis; cbn [rename_ctx];
    eauto using ctx_vis.
Qed.

Local Lemma rename_avar_inj f :
  (forall x y, f x = f y -> x = y) ->
  forall x y, rename_avar f x = rename_avar f y -> x = y.
Proof.
  intros Hinj [i | x] [j | y] H; inversion H; auto.
  f_equal. auto.
Qed.

Local Lemma rename_typ_indep f a T :
  (forall x y, f x = f y -> x = y) ->
  typ_indep a T -> typ_indep (rename_avar f a) (rename f T).
Proof.
  intros Hinj H. induction H.
  all: cbn [rename_avar].
  all: unfold rename, TransformCollect.transform, TypTransform in *.
  all: cbn [transform_typ transform_dec avar_map] in *.
  all: rewrite ?(proj1 (rename_depth_types f) _ 1 0),
               ?(proj1 (rename_depth_types f) _ 2 0).
  all: try solve [eauto using typ_indep, rename_avar_inj].
  all: try solve [inversion H; subst; constructor; constructor].
  apply typ_indep_sel; unfold avar_map; eauto using rename_avar_inj.
Qed.

Local Ltac reduce_rename_types f :=
  unfold rename, TransformCollect.transform, TypTransform;
  cbn [transform_typ transform_dec avar_map];
  rewrite ?(proj1 (rename_depth_types f) _ 1 0),
          ?(proj1 (rename_depth_types f) _ 2 0).

Local Ltac reduce_rename_types_in f H :=
  unfold rename, TransformCollect.transform, TypTransform in H;
  cbn [transform_typ transform_dec avar_map] in H;
  rewrite ?(proj1 (rename_depth_types f) _ 1 0),
          ?(proj1 (rename_depth_types f) _ 2 0) in H.

Local Lemma tyq_var_empty v w :
  tyq_var empty v w -> v = w.
Proof.
  intro H. remember (@empty var) as e eqn:He in H.
  induction H; subst; unfold typing_equiv in *; auto; try congruence.
  - exfalso. eapply binds_empty_inv; eassumption.
  - symmetry. auto.
  - repeat match goal with IH : @empty var = empty -> _ |- _ => specialize (IH eq_refl) end.
    congruence.
Qed.

Local Ltac rename_equiv_body f Hinv :=
  let z := fresh "z" in
  intro z;
  match goal with
  | IH : forall z : var, @empty var = empty -> tyq_typ _ (rename f (open_rec _ z _)) _ |- _ =>
      let Hr := fresh "Hrename" in
      pose proof (IH (f z) eq_refl) as Hr;
      rewrite !rename_open_typ, !Hinv in Hr; exact Hr
  end.

Local Lemma rename_tyq_typ f :
  (forall x, f (f x) = x) ->
  forall e S T, tyq_typ e S T -> e = empty ->
  tyq_typ empty (rename f S) (rename f T).
Proof.
  intros Hinv e S T H. induction H; intro He; subst.
  - inversion H; subst; constructor; constructor.
  - inversion H; subst; reduce_rename_types f;
      eapply tyq_typ_andor; unfold typing_equiv in *; eauto.
  - reduce_rename_types f.
    eapply tyq_typ_fun; unfold typing_equiv in *; [eauto |].
    rename_equiv_body f Hinv.
  - reduce_rename_types f.
    eapply tyq_typ_fld; unfold typing_equiv in *; eauto.
  - reduce_rename_types f.
    eapply tyq_typ_typ; unfold typing_equiv in *; rename_equiv_body f Hinv.
  - reduce_rename_types f. apply tyq_typ_sel_normal.
    apply tyq_var_empty in H. subst. apply tyq_var_refl.
  - reduce_rename_types f. apply tyq_typ_sel.
  - reduce_rename_types f.
    eapply tyq_typ_bnd; unfold typing_equiv in *.
    rename_equiv_body f Hinv.
  - reduce_rename_types f.
    eapply tyq_typ_met; unfold typing_equiv in *.
    + rename_equiv_body f Hinv.
    + eauto.
    + intros z w.
      pose proof (H3 (f z) (f w) eq_refl) as Hr.
      rewrite !rename_open_typ, !Hinv in Hr. exact Hr.
Qed.

Local Lemma rename_bnd f T :
  rename f (typ_bnd T) = typ_bnd (rename f T).
Proof.
  unfold rename, TransformCollect.transform, TypTransform.
  cbn [transform_typ]. f_equal. apply (proj1 (rename_depth_types f)).
Qed.

Local Lemma rename_involution_types f :
  (forall x, f (f x) = x) ->
  (forall T d n, transform_typ (avar_map f) (transform_typ (avar_map f) T d) n = T) /\
  (forall D d n, transform_dec (avar_map f) (transform_dec (avar_map f) D d) n = D).
Proof.
  intro Hinv. apply typ_mutind;
    intros; cbn [transform_typ transform_dec];
    try reflexivity; f_equal; auto.
  all: unfold avar_map; match goal with
  | |- context [rename_avar _ (rename_avar _ ?a)] => destruct a; cbn; now rewrite ?Hinv
  end.
Qed.

Local Lemma rename_involution_typ f (T : typ) :
  (forall x, f (f x) = x) -> rename f (rename f T) = T.
Proof. intro Hinv. apply (proj1 (rename_involution_types f Hinv)). Qed.

Local Lemma get_def_rename f l ds :
  get_def l (rename f ds) = option_map (rename f) (get_def l ds).
Proof.
  induction ds; [reflexivity |].
  change (get_def l (defs_cons (rename f ds) (rename f d)) = option_map (rename f) (get_def l (defs_cons ds d))).
  assert (Hlabel : label_of (rename f d) = label_of d) by (destruct d; reflexivity).
  cbn [get_def]. rewrite Hlabel. case_if; auto.
Qed.

Local Lemma rename_defs_hasnt f ds l :
  defs_hasnt ds l -> defs_hasnt (rename f ds) l.
Proof. unfold defs_hasnt. intro H. rewrite get_def_rename, H. reflexivity. Qed.

Local Lemma rename_lit_fun f T t :
  rename f (lit_fun T t) = lit_fun (rename f T) (rename f t).
Proof.
  change (lit_fun (rename f T) (transform_trm (avar_map f) t 1) =
          lit_fun (rename f T) (transform_trm (avar_map f) t 0)).
  f_equal. apply (proj1 (rename_depth_terms f)).
Qed.

Local Lemma rename_lit_obj f T ds :
  rename f (lit_obj T ds) = lit_obj (rename f T) (rename f ds).
Proof.
  change (lit_obj (transform_typ (avar_map f) T 1) (transform_defs (avar_map f) ds 1) =
          lit_obj (transform_typ (avar_map f) T 0) (transform_defs (avar_map f) ds 0)).
  f_equal; [apply (proj1 (rename_depth_types f)) |
    apply (proj2 (proj2 (proj2 (rename_depth_terms f))))].
Qed.

Local Lemma rename_def_met f m t :
  rename f (def_met m t) = def_met m (rename f t).
Proof.
  change (def_met m (transform_trm (avar_map f) t 2) =
          def_met m (transform_trm (avar_map f) t 0)).
  f_equal. apply (proj1 (rename_depth_terms f)).
Qed.

Local Lemma rename_def_typ f l T :
  rename f (def_typ l T) = def_typ l (rename f T).
Proof.
  change (def_typ l (transform_typ (avar_map f) T 1) =
          def_typ l (transform_typ (avar_map f) T 0)).
  f_equal. apply (proj1 (rename_depth_types f)).
Qed.

Local Lemma rename_dec_typ f L T U :
  rename f (dec_typ L T U) = dec_typ L (rename f T) (rename f U).
Proof.
  change (dec_typ L (transform_typ (avar_map f) T 1) (transform_typ (avar_map f) U 1) =
          dec_typ L (transform_typ (avar_map f) T 0) (transform_typ (avar_map f) U 0)).
  f_equal; apply (proj1 (rename_depth_types f)).
Qed.

Local Lemma rename_dec_met f l TC TZ TR :
  rename f (dec_met l TC TZ TR) = dec_met l (rename f TC) (rename f TZ) (rename f TR).
Proof.
  change (dec_met l (transform_typ (avar_map f) TC 1)
            (transform_typ (avar_map f) TZ 0) (transform_typ (avar_map f) TR 2) =
          dec_met l (transform_typ (avar_map f) TC 0)
            (transform_typ (avar_map f) TZ 0) (transform_typ (avar_map f) TR 0)).
  f_equal; apply (proj1 (rename_depth_types f)).
Qed.

Local Ltac reduce_rename_terms f :=
  unfold rename, TransformCollect.transform, TrmTransform, LitTransform,
    Terms.DefTransform, Terms.DefsTransform, TypTransform;
  cbn [transform_trm transform_lit transform_def transform_defs
       transform_typ transform_dec avar_map rename_avar];
  rewrite ?(proj1 (rename_depth_types f) _ 1 0),
          ?(proj1 (rename_depth_types f) _ 2 0),
          ?(proj1 (rename_depth_terms f) _ 1 0),
          ?(proj1 (rename_depth_terms f) _ 2 0),
          ?(proj2 (proj2 (proj2 (rename_depth_terms f))) _ 1 0).

Section RenameTyping.

Context (m : Mode) (f : var -> var) (support : vars).
Context (Hinv : forall x, f (f x) = x).
Context (Hfix : forall x, x \notin support -> f x = x).

Local Lemma rename_injective x y : f x = f y -> x = y.
Proof. intro H. rewrite <- (Hinv x), <- (Hinv y), H. reflexivity. Qed.

Local Ltac renamed_type_judgments :=
  unfold obj_typing, subtyping, obj_ref_incap, obj_cap_bnd in *;
  try rewrite !rename_open_typ;
  eauto using rename_binds, rename_injective, rename_typ_indep, rename_tyq_typ.

Local Lemma rename_types :
  (forall G Go e x T, ty_var m G Go e x T -> e = empty ->
    ty_var m (rename_ctx f G) (rename_objctx f Go) empty (f x) (rename f T)) /\
  (forall G Go e S T, subtyp m G Go e S T -> e = empty ->
    subtyp m (rename_ctx f G) (rename_objctx f Go) empty (rename f S) (rename f T)) /\
  (forall G Go e S T, ty_incap m G Go e S T -> e = empty ->
    ty_incap m (rename_ctx f G) (rename_objctx f Go) empty (rename f S) (rename f T)).
Proof.
  apply (@ts_mutind m
    (fun G Go e x T _ => e = empty ->
      ty_var m (rename_ctx f G) (rename_objctx f Go) empty (f x) (rename f T))
    (fun G Go e S T _ => e = empty ->
      subtyp m (rename_ctx f G) (rename_objctx f Go) empty (rename f S) (rename f T))
    (fun G Go e S T _ => e = empty ->
      ty_incap m (rename_ctx f G) (rename_objctx f Go) empty (rename f S) (rename f T))).
  all: intros; subst; cbn [rename_objctx]; rewrite ?rename_open_typ; reduce_rename_types f.
  - apply ty_var_var. eauto using rename_binds, rename_injective.
  - apply ty_rec_intro.
    + match goal with
      | IH : @empty var = empty -> ty_var _ _ _ _ _ (rename f (open_rec _ _ _)) |- _ =>
          specialize (IH eq_refl); rewrite rename_open_typ in IH; exact IH
      end.
    + apply (@rename_typ_indep f (avar_b 0)); auto using rename_injective.
    + intro Hmode.
      match goal with
      | IH : _ -> @empty var = empty -> ty_incap _ _ _ _ _ _ |- _ =>
          specialize (IH Hmode eq_refl); rewrite !rename_open_typ in IH; exact IH
      end.
  - eapply ty_rec_elim with (T := rename f T).
    + unfold obj_typing in *; rewrite rename_bnd in H. auto.
    + apply (@rename_typ_indep f (avar_b 0)); auto using rename_injective.
  - apply ty_var_and; renamed_type_judgments.
  - eapply ty_var_sub; renamed_type_judgments.
  - eapply ty_var_mut_top with (T := rename f T); renamed_type_judgments.
  - apply subtyp_top.
  - apply subtyp_bot.
  - apply subtyp_refl.
  - eapply subtyp_trans; renamed_type_judgments.
  - apply subtyp_and11.
  - apply subtyp_and12.
  - apply subtyp_and2; renamed_type_judgments.
  - apply subtyp_or11.
  - apply subtyp_or12.
  - apply subtyp_or2; renamed_type_judgments.
  - apply subtyp_fld; renamed_type_judgments.
  - apply subtyp_typ; unfold subtyping in *; intro z.
    + specialize (H (f z) eq_refl). rewrite !rename_open_typ, !Hinv in H. exact H.
    + specialize (H0 (f z) eq_refl). rewrite !rename_open_typ, !Hinv in H0. exact H0.
  - eapply subtyp_sel2 with (T := rename f T).
    unfold obj_typing in *. specialize (H eq_refl). reduce_rename_types_in f H. exact H.
  - eapply subtyp_sel1 with (S := rename f S).
    unfold obj_typing in *. specialize (H eq_refl). reduce_rename_types_in f H. exact H.
  - eapply subtyp_fun with (L := L \u support); renamed_type_judgments.
    intros z Hz. apply notin_union in Hz as [HzL HzS].
    specialize (H0 z HzL eq_refl).
    cbn [rename_ctx rename_objctx] in H0.
    rewrite !rename_open_typ, (Hfix HzS) in H0. exact H0.
  - eapply subtyp_met with (L := L \u support); renamed_type_judgments.
    + intros z Hz. apply notin_union in Hz as [HzL HzS].
      specialize (H0 z HzL eq_refl).
      cbn [rename_ctx rename_objctx] in H0.
      rewrite !rename_open_typ, (Hfix HzS) in H0. exact H0.
    + intros Hmode Hind.
      apply (@rename_typ_indep f (avar_b 0)); auto using rename_injective.
      apply t; [assumption |].
      apply (@rename_typ_indep f (avar_b 0)) in Hind; auto using rename_injective.
      change (typ_indep_b 0 (rename f (rename f TC2))) in Hind.
      rewrite rename_involution_typ in Hind; assumption.
    + intros z Hz w Hneq Hw.
      apply notin_union in Hz as [HzL HzS].
      apply notin_union in Hw as [HwL HwS].
      specialize (H1 z HzL w Hneq HwL eq_refl).
      cbn [rename_ctx rename_objctx] in H1.
      rewrite !rename_open_typ, (Hfix HzS), (Hfix HwS) in H1. exact H1.
  - apply subtyp_tyq. unfold typing_equiv in *. eapply rename_tyq_typ; eauto.
  - apply subtyp_typ_and.
  - apply subtyp_dist.
  - apply subtyp_nocap_bnd.
  - apply subtyp_nocap_typ.
  - apply subtyp_nocap_fld.
  - apply subtyp_nocap_met.
  - apply subtyp_nocap_fun. assumption.
  - apply subtyp_nocap_mut_top_boundless. assumption.
  - apply subtyp_nocap_mut_top_complement. assumption.
  - apply subtyp_nocap_mut_bot. assumption.
  - apply subtyp_mut_top. assumption.
  - apply ty_incap_top.
  - apply ty_incap_bot.
  - apply ty_incap_typ.
  - apply ty_incap_cap.
  - apply ty_incap_met.
  - apply ty_incap_fld.
  - eapply ty_incap_sel with (S := rename f S) (T := rename f T).
    + unfold obj_typing in *. specialize (H eq_refl). reduce_rename_types_in f H. exact H.
    + unfold obj_ref_incap in *. specialize (H0 eq_refl); rewrite rename_open_typ in H0; exact H0.
  - apply ty_incap_rec.
  - apply ty_incap_and; renamed_type_judgments.
  - apply ty_incap_or; renamed_type_judgments.
  - apply ty_incap_fun. assumption.
  - apply ty_incap_nocap; renamed_type_judgments.
Qed.

Local Lemma rename_capbnd C G Go e S T :
  ty_capbnd m C G Go e S T -> e = empty ->
  ty_capbnd m C (rename_ctx f G) (rename_objctx f Go) empty (rename f S) (rename f T).
Proof.
  destruct rename_types as [Rvar _].
  intro H. induction H; intros He; subst; cbn [rename_objctx]; reduce_rename_types f.
  - apply ty_capbnd_top.
  - apply ty_capbnd_bot.
  - apply ty_capbnd_typ.
  - apply ty_capbnd_cap_sel.
  - apply ty_capbnd_cap_ignore. assumption.
  - apply ty_capbnd_met.
  - apply ty_capbnd_fld.
  - eapply ty_capbnd_sel with (S := rename f S) (T := rename f T).
    + unfold obj_typing in *. specialize (Rvar _ _ _ _ _ H eq_refl).
      reduce_rename_types_in f Rvar. exact Rvar.
    + unfold obj_cap_bnd in *. specialize (IHty_capbnd eq_refl).
      rewrite rename_open_typ in IHty_capbnd. exact IHty_capbnd.
  - apply ty_capbnd_rec.
  - apply ty_capbnd_and; renamed_type_judgments.
  - apply ty_capbnd_or; renamed_type_judgments.
  - apply ty_capbnd_all.
Qed.

Local Lemma rename_viewpoint x G Go e S T :
  viewpoint_adapt m x G Go e S T -> e = empty ->
  viewpoint_adapt m (f x) (rename_ctx f G) (rename_objctx f Go) empty (rename f S) (rename f T).
Proof.
  destruct rename_types as [_ [_ Rincap]].
  unfold viewpoint_adapt. destruct (mode_viewpoint_adaptation' m).
  - congruence.
  - intros H He. destruct H; subst. reduce_rename_types f.
    constructor; unfold obj_ref_incap, obj_cap_bnd in *; eauto using rename_capbnd.
Qed.

Local Ltac finish_rename_var f Rvar :=
  match goal with
  | H : ty_var _ _ _ _ _ _ |- _ =>
      let Hr := fresh "Hrenamed" in
      pose proof (Rvar _ _ _ _ _ H eq_refl) as Hr;
      first [exact Hr |
        rewrite rename_open_typ in Hr; exact Hr |
        reduce_rename_types_in f Hr; exact Hr]
  end.

Local Lemma rename_terms :
  (forall G Go e t T, ty_trm m G Go e t T -> e = empty ->
    ty_trm m (rename_ctx f G) (rename_objctx f Go) empty (rename f t) (rename f T)) /\
  (forall G Go e l T, ty_lit m G Go e l T -> e = empty ->
    ty_lit m (rename_ctx f G) (rename_objctx f Go) empty (rename f l) (rename f T)) /\
  (forall G Go e d D, ty_def m G Go e d D -> e = empty ->
    ty_def m (rename_ctx f G) (rename_objctx f Go) empty (rename f d) (rename f D)) /\
  (forall G Go e ds T, ty_defs m G Go e ds T -> e = empty ->
    ty_defs m (rename_ctx f G) (rename_objctx f Go) empty (rename f ds) (rename f T)).
Proof.
  destruct rename_types as [Rvar [Rsub Rincap]].
  apply (@rules_mutind m
    (fun G Go e t T _ => e = empty ->
      ty_trm m (rename_ctx f G) (rename_objctx f Go) empty (rename f t) (rename f T))
    (fun G Go e l T _ => e = empty ->
      ty_lit m (rename_ctx f G) (rename_objctx f Go) empty (rename f l) (rename f T))
    (fun G Go e d D _ => e = empty ->
      ty_def m (rename_ctx f G) (rename_objctx f Go) empty (rename f d) (rename f D))
    (fun G Go e ds T _ => e = empty ->
      ty_defs m (rename_ctx f G) (rename_objctx f Go) empty (rename f ds) (rename f T))).
  all: intros; subst; cbn [rename_objctx]; rewrite ?rename_open_typ;
    rewrite ?rename_lit_fun, ?rename_lit_obj, ?rename_def_met, ?rename_def_typ,
            ?rename_dec_typ, ?rename_dec_met;
    reduce_rename_terms f; unfold obj_typing, subtyping, obj_dec_typing in *.
  - apply ty_trm_var; unfold obj_typing.
    + intros Hv. apply rename_vis; auto using rename_injective.
    + exact (Rvar _ _ _ _ _ o eq_refl).
  - eapply ty_trm_apply with (S := rename f S) (T := rename f T);
    unfold obj_typing; intros; eauto using rename_vis, rename_injective.
    all: finish_rename_var f Rvar.
  - eapply ty_trm_read with (S := rename f S) (T := rename f T);
    unfold obj_typing; intros; eauto using rename_vis, rename_injective, rename_viewpoint.
    all: try solve [finish_rename_var f Rvar].
    exact (@rename_viewpoint x G objctx_empty empty T U v eq_refl).
  - eapply ty_trm_write with (S := rename f S);
    unfold obj_typing; intros; eauto using rename_vis, rename_injective.
    all: try solve [finish_rename_var f Rvar].
    unfold obj_typing in o. exact (Rvar _ _ _ _ _ (o H) eq_refl).
  - eapply ty_trm_call with (TC := rename f TC) (TZ := rename f TZ) (TR := rename f TR);
    unfold obj_typing; intros; eauto using rename_vis, rename_injective.
    all: try solve [finish_rename_var f Rvar].
    apply (@rename_typ_indep f (avar_b 0)); eauto using rename_injective.
  - eapply ty_trm_let with (L := L \u support) (T := rename f T); unfold obj_typing; eauto.
    intros z Hz. apply notin_union in Hz as [HzL HzS].
    specialize (H0 z HzL eq_refl).
    cbn [rename_ctx rename_objctx] in H0.
    rewrite rename_open_trm, (Hfix HzS) in H0. exact H0.
  - eapply ty_trm_lit with (L := L \u support) (T := rename f T); unfold obj_typing; eauto.
    intros z Hz. apply notin_union in Hz as [HzL HzS].
    specialize (H0 z HzL eq_refl).
    cbn [rename_ctx rename_objctx] in H0.
    rewrite rename_open_trm, (Hfix HzS) in H0. exact H0.
  - eapply ty_trm_sub; unfold obj_typing, subtyping; eauto.
    exact (Rsub _ _ _ _ _ s eq_refl).
  - eapply ty_lit_fun with (L := L \u support); unfold obj_typing; eauto.
    intros z Hz. apply notin_union in Hz as [HzL HzS].
    specialize (H z HzL eq_refl).
    cbn [rename_ctx rename_objctx] in H.
    rewrite rename_open_trm, rename_open_typ, (Hfix HzS) in H. exact H.
  - assert (Hren : ty_lit m (rename_ctx f G) objctx_empty empty
        (lit_obj (rename f T) (rename f ds)) (typ_objlit m (rename f T))).
    {
      eapply ty_lit_obj with (L := L \u support); unfold obj_typing.
      - intros z Hz. apply notin_union in Hz as [HzL HzS].
        specialize (H z HzL eq_refl).
        cbn [rename_objctx] in H.
        rewrite rename_open_defs, rename_open_typ, (Hfix HzS) in H. exact H.
      - apply (@rename_typ_indep f (avar_b 0)); auto using rename_injective.
    }
    destruct (mode_objlit_refcaps' m); reduce_rename_terms f; exact Hren.
  - eapply ty_def_typ with (L := L \u support); unfold typing_equiv in *.
    intros z Hz. apply notin_union in Hz as [HzL HzS].
    pose proof (rename_tyq_typ f Hinv (t z HzL) eq_refl) as Hren.
    rewrite !rename_open_typ, (Hfix HzS) in Hren. exact Hren.
  - apply ty_def_fld; unfold obj_typing.
    + intros Hv. rewrite <- rename_objctx_concat. apply rename_vis; eauto using rename_injective.
    + rewrite <- rename_objctx_concat. exact (Rvar _ _ _ _ _ o eq_refl).
  - eapply ty_def_met with (L := L \u support); unfold obj_typing.
    intros z Hz w Hneq Hw.
    apply notin_union in Hz as [HzL HzS].
    apply notin_union in Hw as [HwL HwS].
    specialize (H z HzL w Hneq HwL eq_refl).
    rewrite rename_objctx_method, !rename_open_trm, !rename_open_typ,
      (Hfix HzS), (Hfix HwS) in H. exact H.
  - apply ty_defs_one; unfold obj_dec_typing; eauto.
  - apply ty_defs_cons; unfold obj_typing, obj_dec_typing; eauto.
    assert (Hlabel : label_of (rename f d) = label_of d) by (destruct d; reflexivity).
    change (defs_hasnt (rename f ds) (label_of (rename f d))).
    rewrite Hlabel. apply rename_defs_hasnt. assumption.
Qed.

End RenameTyping.

Local Lemma open_transform_types k x f g :
  (forall a d, open_rec (k + d) x (f a d) =
     g (open_rec (k + d) x a) d) ->
  (forall T d, open_rec_typ (k + d) x (transform_typ f T d) =
     transform_typ g (open_rec_typ (k + d) x T) d) /\
  (forall D d, open_rec_dec (k + d) x (transform_dec f D d) =
     transform_dec g (open_rec_dec (k + d) x D) d).
Proof.
  intro H. apply typ_mutind; intros;
    cbn [open_rec_typ open_rec_dec transform_typ transform_dec];
    try reflexivity; f_equal; try rewrite <- !Nat.add_succ_r; auto.
Qed.

Local Lemma open_transform_terms k x f g :
  (forall a d, open_rec (k + d) x (f a d) =
     g (open_rec (k + d) x a) d) ->
  (forall t d, open_rec_trm (k + d) x (transform_trm f t d) =
     transform_trm g (open_rec_trm (k + d) x t) d) /\
  (forall l d, open_rec_lit (k + d) x (transform_lit f l d) =
     transform_lit g (open_rec_lit (k + d) x l) d) /\
  (forall v d, open_rec_def (k + d) x (transform_def f v d) =
     transform_def g (open_rec_def (k + d) x v) d) /\
  (forall ds d, open_rec_defs (k + d) x (transform_defs f ds d) =
     transform_defs g (open_rec_defs (k + d) x ds) d).
Proof.
  intro H. destruct (@open_transform_types k x f g H) as [HT HD].
  apply trm_mutind; intros;
    cbn [open_rec_trm open_rec_lit open_rec_def open_rec_defs
         transform_trm transform_lit transform_def transform_defs];
    try reflexivity; f_equal; try rewrite <- !Nat.add_succ_r; auto.
Qed.

Local Lemma close_and_open_trm k x (t : trm) :
  open_rec k x (close_rec k x t) = open_rec k x t.
Proof.
  assert (H : forall a d, open_rec (k + d) x (close_depth_rec k x a d) =
      avar_map id (open_rec (k + d) x a) d).
  {
    intros [i | y] d;
      unfold close_depth_rec, avar_map, rename_avar, close_rec, open_rec,
        AvarOpenable, AvarClosing, id; cbn; repeat case_if; congruence.
  }
  pose proof (proj1 (@open_transform_terms k x _ _ H) t 0) as Heq.
  rewrite Nat.add_0_r in Heq.
  change (open_rec k x (close_rec k x t) =
    transform_trm (avar_map id) (open_rec k x t) 0) in Heq.
  rewrite Heq. apply (proj1 (rename_fixed_terms id)).
  intros y Hy. reflexivity.
Qed.

Local Lemma close_open_other_trm k m x y (t : trm) :
  k <> m -> x <> y ->
  open_rec k x (close_rec m y t) = close_rec m y (open_rec k x t).
Proof.
  intros Hkm Hxy.
  assert (H : forall (a : avar) d, open_rec (k + d) x (close_depth_rec m y a d) =
      close_depth_rec m y (open_rec (k + d) x a) d).
  {
    intros [i | z] d;
      unfold close_depth_rec, close_rec, open_rec, AvarOpenable, AvarClosing;
      cbn; repeat case_if; try congruence.
    all: exfalso; apply Hkm; lia.
  }
  pose proof (proj1 (@open_transform_terms k x _ _ H) t 0) as Heq.
  rewrite Nat.add_0_r in Heq. exact Heq.
Qed.

Local Definition close_fv_property {A : Set} {AF : FreeVar A}
    (x : var) (a : A) (atdepth : A -> nat -> A) :=
  forall d v, v \in fv (atdepth a d) -> v \in fv a /\ v <> x.

Local Ltac prove_close_fv :=
  unfold close_fv_property in *;
  cbn [fv TypFreeVar DecFreeVar TrmFreeVar LitFreeVar DefFreeVar DefsFreeVar
       fv_typ fv_dec fv_trm fv_lit fv_def fv_defs
       transform_typ transform_dec transform_trm transform_lit transform_def transform_defs] in *;
  let d := fresh "depth" in let v := fresh "name" in let H := fresh "Hmem" in
  intros d v H;
  repeat rewrite in_union in *;
  try solve [rewrite in_empty in H; contradiction];
  repeat match goal with H : _ \/ _ |- _ => destruct H end;
  match goal with
  | H : ?v \in _,
    IH : forall (d : nat) (v : var), v \in _ -> v \in _ /\ v <> _ |- _ =>
      let Hmem := fresh in
      assert (Hmem := IH _ v H);
      destruct Hmem; auto 8
  | H : ?v \in _, IH : forall (a : _) (d : nat) (v : var), v \in _ -> v \in _ /\ v <> _ |- _ =>
      let Hmem := fresh in
      assert (Hmem := IH _ _ v H);
      destruct Hmem; auto 8
  end.

Local Lemma close_fv_types f x :
  (forall a d v, v \in fv (f a d) -> v \in fv a /\ v <> x) ->
  (forall T, close_fv_property x T (transform_typ f)) /\
  (forall D, close_fv_property x D (transform_dec f)).
Proof.
  intro Hf. apply typ_mutind; intros; prove_close_fv.
Qed.

Local Lemma close_fv_terms f x :
  (forall a d v, v \in fv (f a d) -> v \in fv a /\ v <> x) ->
  (forall t, close_fv_property x t (transform_trm f)) /\
  (forall l, close_fv_property x l (transform_lit f)) /\
  (forall d, close_fv_property x d (transform_def f)) /\
  (forall ds, close_fv_property x ds (transform_defs f)).
Proof.
  intro Hf. destruct (@close_fv_types f x Hf) as [HT HD].
  apply trm_mutind; intros; prove_close_fv.
Qed.

Local Lemma close_trm_fv k x (t : trm) v :
  v \in fv (close_rec k x t) -> v \in fv t /\ v <> x.
Proof.
  assert (Hf : forall (a : avar) d v, v \in fv (close_depth_rec k x a d) ->
                    v \in fv a /\ v <> x).
  {
    intros [i|y] d z;
      unfold close_depth_rec, close_rec, AvarClosing; cbn; try case_if;
      unfold fv, AvarFreeVar; cbn;
      rewrite ?in_empty, ?in_singleton; intuition congruence.
  }
  apply (proj1 (@close_fv_terms _ x Hf) t 0).
Qed.

Local Definition ctx_extends G G' :=
  (forall x T, ctx_binds x T G -> ctx_binds x T G') /\
  (forall x, ctx_vis G x -> ctx_vis G' x).

Local Lemma ctx_extends_push G G' x vk T :
  ctx_extends G G' ->
  ctx_extends (G § x / vk ~ T) (G' § x / vk ~ T).
Proof.
  intros [Hbind Hvis]. split.
  - intros w S H. inversion H; subst; eauto using ctx_binds.
  - intros w H. inversion H; subst; eauto using ctx_vis.
Qed.

Local Lemma ctx_extends_hide G G' :
  ctx_extends G G' -> ctx_extends (ctx_hide G) (ctx_hide G').
Proof.
  intros [Hbind Hvis]. split.
  - intros w S H. inversion H; subst. constructor. now apply Hbind.
  - intros w H. inversion H.
Qed.

Local Lemma ctx_extends_object G G' Go :
  ctx_extends G G' -> ctx_extends (G §§& Go) (G' §§& Go).
Proof.
  destruct Go; cbn; auto using ctx_extends_push.
Qed.

Local Lemma ctx_extends_method m G G' Go z TZ c TC :
  ctx_extends G G' ->
  ctx_extends (ctx_obj_met m G Go z TZ c TC) (ctx_obj_met m G' Go z TZ c TC).
Proof.
  destruct Go; cbn [ctx_obj_met]; destruct (mode_visibility' m);
    auto 6 using ctx_extends_push, ctx_extends_hide.
Qed.

Local Ltac extend_typing_context :=
  match goal with
  | H : ctx_extends _ _ |- _ =>
      let Hb := fresh "Hbind" in
      let Hv := fresh "Hvis" in
      pose proof (proj1 H) as Hb; pose proof (proj2 H) as Hv
  end.

Section Extending.
Context (m : Mode).

Local Lemma ctx_extends_types :
  (forall G Go e x T, ty_var m G Go e x T ->
   forall G', ctx_extends G G' -> ty_var m G' Go e x T) /\
  (forall G Go e S T, subtyp m G Go e S T ->
   forall G', ctx_extends G G' -> subtyp m G' Go e S T) /\
  (forall G Go e S T, ty_incap m G Go e S T ->
   forall G', ctx_extends G G' -> ty_incap m G' Go e S T).
Proof.
  apply (@ts_mutind m
    (fun G Go e x T _ => forall G', ctx_extends G G' -> ty_var m G' Go e x T)
    (fun G Go e S T _ => forall G', ctx_extends G G' -> subtyp m G' Go e S T)
    (fun G Go e S T _ => forall G', ctx_extends G G' -> ty_incap m G' Go e S T)).
  all: intros; extend_typing_context.
  all: solve [econstructor; unfold obj_typing, subtyping, obj_ref_incap in *;
    intros; solve [eauto 7 using ctx_extends_push]].
Qed.

Local Lemma ctx_extends_capbnd C G Go e S T :
  ty_capbnd m C G Go e S T ->
  forall G', ctx_extends G G' -> ty_capbnd m C G' Go e S T.
Proof.
  destruct ctx_extends_types as [Hvar _].
  intro H. induction H; intros G' Hext.
  all: solve [econstructor; unfold obj_typing, obj_cap_bnd in *; solve [eauto]].
Qed.

Local Lemma ctx_extends_viewpoint x G Go e S T :
  viewpoint_adapt m x G Go e S T ->
  forall G', ctx_extends G G' -> viewpoint_adapt m x G' Go e S T.
Proof.
  destruct ctx_extends_types as [_ [_ Hincap]].
  unfold viewpoint_adapt.
  destruct (mode_viewpoint_adaptation' m); auto.
  intros H G' Hext. destruct H.
  constructor; unfold obj_ref_incap, obj_cap_bnd in *; eauto using ctx_extends_capbnd.
Qed.

Local Lemma ctx_extends_terms :
  (forall G Go e t T, ty_trm m G Go e t T ->
   forall G', ctx_extends G G' -> ty_trm m G' Go e t T) /\
  (forall G Go e l T, ty_lit m G Go e l T ->
   forall G', ctx_extends G G' -> ty_lit m G' Go e l T) /\
  (forall G Go e d D, ty_def m G Go e d D ->
   forall G', ctx_extends G G' -> ty_def m G' Go e d D) /\
  (forall G Go e ds T, ty_defs m G Go e ds T ->
   forall G', ctx_extends G G' -> ty_defs m G' Go e ds T).
Proof.
  destruct ctx_extends_types as [Hvar [Hsub Hincap]].
  apply (@rules_mutind m
    (fun G Go e t T _ => forall G', ctx_extends G G' -> ty_trm m G' Go e t T)
    (fun G Go e l T _ => forall G', ctx_extends G G' -> ty_lit m G' Go e l T)
    (fun G Go e d D _ => forall G', ctx_extends G G' -> ty_def m G' Go e d D)
    (fun G Go e ds T _ => forall G', ctx_extends G G' -> ty_defs m G' Go e ds T)).
  all: intros; extend_typing_context.
  all: solve [econstructor; unfold obj_typing, obj_dec_typing, subtyping, obj_ref_incap in *;
    intros; solve [eauto 7 using ctx_extends_push, ctx_extends_object,
      ctx_extends_method, ctx_extends_viewpoint |
      match goal with Hext : ctx_extends _ _ |- _ =>
        eapply (proj2 (ctx_extends_object _ Hext)); eauto
      end]].
Qed.

End Extending.

Local Definition swap_names (x y z : var) :=
  If z = x then y else (If z = y then x else z).

Local Lemma swap_names_involutive x y z : swap_names x y (swap_names x y z) = z.
Proof. unfold swap_names. repeat case_if; congruence. Qed.

Local Lemma swap_names_fixes x y z :
  z \notin \{x} \u \{y} -> swap_names x y z = z.
Proof.
  intro H. apply notin_union in H as [Hx Hy].
  apply notin_singleton in Hx, Hy.
  unfold swap_names. repeat case_if; congruence.
Qed.

Local Lemma swap_names_left x y : swap_names x y x = y.
Proof. unfold swap_names. case_if; congruence. Qed.

Local Definition let_freshness G (S T : typ) := ctx_dom G \u ctx_fv G \u fv S \u fv T.

Local Lemma type_let_from_one_open mode G x S T (a u : trm) :
  x \notin let_freshness G S T ->
  x \notin fv u ->
  ty_trm mode G objctx_empty empty a S ->
  ty_trm mode (G §ˣ x ~ S) objctx_empty empty (open x u) T ->
  ty_trm mode G objctx_empty empty (trm_let a u) T.
Proof.
  intros Hx Hxu Ha Hu.
  eapply ty_trm_let with (L := let_freshness G S T \u fv u); [exact Ha |].
  intros z Hz. apply notin_union in Hz as [Hz Hzu].
  set (f := swap_names x z).
  assert (Hfixed : forall v,
    (v \in let_freshness G S T \/ v \in fv u) -> f v = v).
  {
    intros v Hv. apply swap_names_fixes.
    apply notin_union. split; apply notin_singleton; intro Heq; subst v;
      destruct Hv; contradiction.
  }
  assert (Hctx : rename_ctx f G = G).
  {
    apply rename_ctx_fixed; intros v Hv; apply Hfixed; left;
      unfold let_freshness; repeat rewrite in_union; auto.
  }
  assert (HS : rename f S = S).
  {
    apply (proj1 (rename_fixed_types f)).
    intros v Hv. apply Hfixed; left; unfold let_freshness; repeat rewrite in_union; auto.
  }
  assert (HT : rename f T = T).
  {
    apply (proj1 (rename_fixed_types f)).
    intros v Hv. apply Hfixed; left; unfold let_freshness; repeat rewrite in_union; auto.
  }
  assert (Hbody : rename f u = u).
  {
    apply (proj1 (rename_fixed_terms f)).
    intros v Hv. apply Hfixed; auto.
  }
  pose proof (proj1 (@rename_terms mode f (\{x} \u \{z})
    (swap_names_involutive x z) (@swap_names_fixes x z))
    _ _ _ _ _ Hu eq_refl) as Hren.
  cbn [rename_ctx rename_objctx] in Hren.
  rewrite rename_open_trm, Hctx, HS, HT, Hbody in Hren.
  unfold f in Hren. rewrite swap_names_left in Hren. exact Hren.
Qed.

Local Lemma vis_in_dom x G :
  ctx_vis G x -> x \in ctx_dom G.
Proof. intro H. induction H; cbn; rewrite ?in_union, ?in_singleton; auto. Qed.

Local Lemma ctx_extends_with_fresh G x vk T :
  x \notin ctx_dom G -> ctx_extends G (G § x / vk ~ T).
Proof.
  intro Hfresh. split.
  - intros w S H. apply ctx_binds_n; auto.
    intro Heq. subst w. apply Hfresh. eapply swap_calls_binding_in_context; eassumption.
  - intros w H. apply ctx_vis_n; auto.
    intro Heq. subst w. apply Hfresh. now apply vis_in_dom.
Qed.

Local Lemma ctx_extends_exchange G x y vk1 vk2 T1 T2 :
  x <> y ->
  ctx_extends (G § x / vk1 ~ T1 § y / vk2 ~ T2)
              (G § y / vk2 ~ T2 § x / vk1 ~ T1).
Proof.
  intro Hxy. split.
  - intros w T H. inversion H; subst.
    + apply ctx_binds_n; [congruence | constructor].
    + match goal with H' : ctx_binds _ _ (G § x / vk1 ~ T1) |- _ =>
        inversion H'; subst; eauto 5 using ctx_binds
      end.
  - intros w H. inversion H; subst.
    + apply ctx_vis_n; [congruence | constructor].
    + match goal with H' : ctx_vis (G § x / vk1 ~ T1) _ |- _ =>
        inversion H'; subst; eauto 5 using ctx_vis
      end.
Qed.

Local Definition call_swap_scope G (T T1 T2 : typ) :=
  ctx_dom G \u ctx_fv G \u fv T \u fv T1 \u fv T2.

Local Ltac solve_call_freshness :=
  unfold let_freshness, call_swap_scope in *;
  cbn [ctx_dom ctx_collect_values] in *;
  repeat rewrite notin_union in *;
  repeat rewrite notin_singleton in *;
  (repeat split; (tauto || congruence)).

Local Lemma type_two_calls mode G x1 m1 p1 x2 m2 p2 y1 y2 t T T1 T2 :
  y1 <> y2 ->
  y1 \notin call_swap_scope G T T1 T2 ->
  y2 \notin call_swap_scope G T T1 T2 ->
  closed t ->
  ty_trm mode G objctx_empty empty (trm_call (avar_f x1) m1 (avar_f p1)) T1 ->
  ty_trm mode G objctx_empty empty (trm_call (avar_f x2) m2 (avar_f p2)) T2 ->
  ty_trm mode (G §ˣ y1 ~ T1 §ˣ y2 ~ T2) objctx_empty empty t T ->
  ty_trm mode G objctx_empty empty
    ❪Let y1=Call $x1․m1 $p1 In Let y2=Call $x2․m2 $p2 In t❫ T.
Proof.
  intros Hdistinct Hfresh1 Hfresh2 Hclosed Hcall1 Hcall2 Htail.
  eapply type_let_from_one_open with (x := y1) (S := T1).
  - solve_call_freshness.
  - intro H. apply close_trm_fv in H. tauto.
  - exact Hcall1.
  - rewrite close_and_open_trm. cbn [open_rec_trm].
    change (ty_trm mode (G §ˣ y1 ~ T1) objctx_empty empty
      (trm_let (trm_call (avar_f x2) m2 (avar_f p2))
                (open_rec 1 y1 (close y2 t))) T).
    rewrite close_open_other_trm by (congruence || lia).
    rewrite Hclosed.
    eapply type_let_from_one_open with (x := y2) (S := T2).
    + solve_call_freshness.
    + intro H. apply close_trm_fv in H. tauto.
    + eapply (proj1 (ctx_extends_terms mode)); [exact Hcall2 |].
      apply ctx_extends_with_fresh. solve_call_freshness.
    + rewrite close_and_open_trm, Hclosed. exact Htail.
Qed.

Local Lemma swap_calls_local_typed_empty mode f g :
  f ∼(trf_swap_calls_local mode)∼> g ->
  match f, g with
  | 〈 G1⁏e1 ⊢ t1 ∶ T1 〉, 〈 G2⁏e2 ⊢ t2 ∶ T2 〉 =>
      e1 = empty -> e2 = empty ->
      ty_trm mode G1 objctx_empty empty t1 T1 /\ ty_trm mode G2 objctx_empty empty t2 T2
  end.
Proof.
  intro H. destruct H. intros He _. subst e.
  match goal with Hfresh : fresh _ _ _ |- _ =>
    cbn in Hfresh; destruct Hfresh as [Hy1 [Hy2 _]]
  end.
  apply notin_union in Hy2 as [Hy2 Hneq].
  apply notin_singleton in Hneq.
  assert (Hy1' : y1 \notin call_swap_scope G T T1 T2) by solve_call_freshness.
  assert (Hy2' : y2 \notin call_swap_scope G T T1 T2) by solve_call_freshness.
  split.
  - eapply type_two_calls; eauto.
    eapply (proj1 (ctx_extends_terms mode)); [eassumption |].
    apply ctx_extends_exchange. exact Hneq.
  - eapply (@type_two_calls mode G x2 m2 xp2 x1 m1 xp1 y2 y1 t T T2 T1);
      try eassumption; try congruence;
      solve_call_freshness.
Qed.

Local Definition typed_pair {A B : Set} (typing : ctx -> objctx -> renv -> A -> B -> Prop)
    (a b : TypedElement TrfContextTy B A) :=
  match a, b with
  | 〈 G⁏e ⊢ t ∶ T 〉, 〈 G'⁏e' ⊢ t' ∶ T' 〉 =>
      e = empty -> e' = empty ->
      typing G objctx_empty empty t T /\ typing G' objctx_empty empty t' T'
  end.

Local Definition typed_obj_pair {A B : Set} (typing : ctx -> objctx -> renv -> A -> B -> Prop)
    (a b : TypedElement TrfContextObjTy B A) :=
  match a, b with
  | 〈 G §§ Go⁏e ⊢ t ∶ T 〉, 〈 G' §§ Go'⁏e' ⊢ t' ∶ T' 〉 =>
      e = empty -> e' = empty ->
      typing G Go empty t T /\ typing G' Go' empty t' T'
  end.

Local Ltac finish_pair_typing :=
  unfold obj_typing, obj_dec_typing, subtyping in *;
  intros;
  repeat match goal with
  | IH : @empty var = empty -> empty = empty -> _ /\ _ |- _ =>
      destruct (IH eq_refl eq_refl); clear IH
  | IH : forall x : var, x \notin ?L -> @empty var = empty -> empty = empty -> _ /\ _,
    Hx : ?x \notin ?L |- _ =>
      destruct (IH x Hx eq_refl eq_refl); clear IH
  | IH : forall x : var, x \notin ?L -> forall y : var, y <> x -> y \notin ?L ->
      @empty var = empty -> empty = empty -> _ /\ _,
    Hx : ?x \notin ?L, Hy : ?y \notin ?L, Hxy : ?y <> ?x |- _ =>
      destruct (IH x Hx y Hxy Hy eq_refl eq_refl); clear IH
  end;
  eauto.

Local Lemma swap_calls_lifted_typed_empty mode :
  (forall a b, a ∼(trf_local_idtyp_trm mode (trf_swap_calls_local mode))∼> b ->
    typed_pair (ty_trm mode) a b) /\
  (forall a b, a ∼(trf_local_idtyp_lit mode (trf_swap_calls_local mode))∼> b ->
    typed_pair (ty_lit mode) a b) /\
  (forall a b, a ∼(trf_local_idtyp_def mode (trf_swap_calls_local mode))∼> b ->
    typed_obj_pair (ty_def mode) a b) /\
  (forall a b, a ∼(trf_local_idtyp_defs mode (trf_swap_calls_local mode))∼> b ->
    typed_obj_pair (ty_defs mode) a b).
Proof.
  apply (@trf_local_idtyp_mutind mode (trf_swap_calls_local mode)
    (fun a b _ => typed_pair (ty_trm mode) a b)
    (fun a b _ => typed_pair (ty_lit mode) a b)
    (fun a b _ => typed_obj_pair (ty_def mode) a b)
    (fun a b _ => typed_obj_pair (ty_defs mode) a b));
    cbn [typed_pair typed_obj_pair] in *; intros; subst.
  - match goal with H : transform (trf_swap_calls_local _) _ _ |- _ =>
      let Htyped := fresh in
      pose proof (swap_calls_local_typed_empty H) as Htyped;
      cbn in Htyped; destruct (Htyped eq_refl eq_refl)
    end.
    split; eapply ty_trm_sub; finish_pair_typing.
  - split; eapply ty_trm_sub; [eapply ty_trm_let with (L := L) (T := Tl) | idtac
                            | eapply ty_trm_let with (L := L) (T := Tl) | idtac];
      finish_pair_typing.
  - split; eapply ty_trm_sub; [eapply ty_trm_let with (L := L) (T := Tl) | idtac
                            | eapply ty_trm_let with (L := L) (T := Tl) | idtac];
      finish_pair_typing.
  - split; eapply ty_trm_sub; [eapply ty_trm_lit with (L := L) (T := Tl) | idtac
                            | eapply ty_trm_lit with (L := L) (T := Tl) | idtac];
      finish_pair_typing.
  - split; eapply ty_trm_sub; [eapply ty_trm_lit with (L := L) (T := Tl) | idtac
                            | eapply ty_trm_lit with (L := L) (T := Tl) | idtac];
      finish_pair_typing.
  - split; eapply ty_lit_fun with (L := L); finish_pair_typing.
  - split; eapply ty_lit_obj with (L := L); finish_pair_typing.
  - split; eapply ty_def_met with (L := L); finish_pair_typing.
  - split; apply ty_defs_one; finish_pair_typing.
  - split; apply ty_defs_cons; finish_pair_typing.
  - split; apply ty_defs_cons; finish_pair_typing.
Qed.

Local Lemma no_function_literal_typing mode G e (T : typ) u U :
  mode_has_mutability mode ->
  ~ ty_trm mode G objctx_empty e (trm_lit (lit_fun T u) U) typ_top.
Proof.
  intros Hmut H. remember (trm_lit (lit_fun T u) U) as t eqn:Ht in H.
  induction H; try discriminate; eauto.
  inversion Ht; subst.
  inversion H; subst. destruct mode; discriminate.
Qed.

Section InitialConfigurations.
Context (mode : Mode).

Local Definition vars_in_context {A : Set} {AT : TFree A} G (a : A) :=
  forall x, tfree x a -> x \in ctx_dom G.

Local Ltac strip_fresh_binding H :=
  rewrite in_union, in_singleton in H;
  destruct H as [Heq | H]; [congruence |].

Local Lemma swap_calls_typed_vars :
  (forall G Go e t T, ty_trm mode G Go e t T -> vars_in_context (G §§& Go) t) /\
  (forall G Go e l T, ty_lit mode G Go e l T -> vars_in_context (G §§& Go) l) /\
  (forall G Go e d D, ty_def mode G Go e d D -> vars_in_context (G §§& Go) d) /\
  (forall G Go e ds T, ty_defs mode G Go e ds T -> vars_in_context (G §§& Go) ds).
Proof.
  destruct swap_calls_free_open as [Htrm [_ [_ Hdefs]]].
  apply (@rules_mutind mode
    (fun G Go _ t _ _ => vars_in_context (G §§& Go) t)
    (fun G Go _ l _ _ => vars_in_context (G §§& Go) l)
    (fun G Go _ d _ _ => vars_in_context (G §§& Go) d)
    (fun G Go _ ds _ _ => vars_in_context (G §§& Go) ds)).
  all: unfold vars_in_context in *; cbn [ctx_obj] in *.
  all: intros; unfold vars_in_context in *.
  all: try solve [match goal with
    | H : tfree _ _ |- _ => inversion H; subst; eauto using swap_calls_var_in_context
    end].
  all: match goal with H : tfree _ _ |- _ => inversion H; subst end.
  all: try solve [eauto].
  all: try solve [match goal with H : tfree_defs _ defs_nil |- _ => inversion H end].
  all: try solve [
    match goal with
    | IH : forall z, z \notin ?L -> forall x, tfree x (open_rec 0 z ?t) -> _,
      HF : tfree_trm ?x ?t |- _ =>
        let z := fresh "z" in let Hfresh := fresh "Hfresh" in
        let Hz := fresh "Hz" in let Hzx := fresh "Hzx" in
        destruct (var_fresh (L \u \{x})) as [z Hfresh];
        apply notin_union in Hfresh as [Hz Hzx];
        apply notin_singleton in Hzx;
        specialize (IH z Hz x (Htrm _ _ HF 0 z));
        cbn [ctx_dom] in IH;
        strip_fresh_binding IH; assumption
    | IH : forall z, z \notin ?L -> forall x, tfree x (open_rec 0 z ?ds) -> _,
      HF : tfree_defs ?x ?ds |- _ =>
        let z := fresh "z" in let Hfresh := fresh "Hfresh" in
        let Hz := fresh "Hz" in let Hzx := fresh "Hzx" in
        destruct (var_fresh (L \u \{x})) as [z Hfresh];
        apply notin_union in Hfresh as [Hz Hzx];
        apply notin_singleton in Hzx;
        specialize (IH z Hz x (Hdefs _ _ HF 0 z));
        cbn [ctx_dom] in IH;
        strip_fresh_binding IH; assumption
    end].
  destruct (var_fresh (L \u \{x})) as [arg Harg].
  apply notin_union in Harg as [Harg Hargx].
  apply notin_singleton in Hargx.
  destruct (var_fresh ((L \u \{x}) \u \{arg})) as [recv Hrecv].
  apply notin_union in Hrecv as [Hrecv Hrecvarg].
  apply notin_union in Hrecv as [Hrecv Hrecvx].
  apply notin_singleton in Hrecvarg, Hrecvx.
  specialize (H arg Harg recv Hrecvarg Hrecv x
    (Htrm _ _ (Htrm _ _ H3 1 recv) 0 arg)).
  destruct Go; cbn [ctx_obj_met] in H; destruct (mode_visibility' mode);
    cbn [ctx_obj_met ctx_obj ctx_dom] in *;
    strip_fresh_binding H; strip_fresh_binding H; exact H.
Qed.

Local Lemma swap_calls_empty_heap_correspond :
  @heap_correspond mode ctx_empty empty empty.
Proof.
  unfold heap_correspond. cbn [ctx_kdom].
  repeat split; try constructor; try rewrite dom_empty; try reflexivity.
  intros x H. rewrite in_empty in H. contradiction.
Qed.

Local Lemma swap_calls_initial_typed t T Lv :
  ty_trm mode ctx_empty objctx_empty empty t T ->
  closed t ->
  closed T ->
  (exists null, null \in Lv) ->
  fv T \c Lv ->
  @ty_config mode ctx_empty (config_mk t stack_nil empty empty Lv) T.
Proof.
  intros Hty Ht HT Hnull Hfv.
  eapply ty_config_c with (T := T).
  - constructor.
  - exact swap_calls_empty_heap_correspond.
  - constructor. apply subtyp_refl.
  - intros x H. inversion H.
  - exact Hty.
  - intros x Hx.
    destruct swap_calls_typed_vars as [Hfree _].
    specialize (Hfree _ _ _ _ _ Hty x Hx).
    cbn in Hfree. rewrite in_empty in Hfree. contradiction.
  - repeat split.
    + simpl. intros x H. rewrite in_empty in H. contradiction.
    + unfold nothing_fresh_in_config. simpl.
      intros x H. rewrite in_empty in H. contradiction.
    + unfold nothing_fresh_in_config. simpl.
      intros x H. repeat rewrite in_union. right; right; right; right.
      apply Hfv, H.
  - exact Hnull.
  - intros x. reflexivity.
  - constructor; try assumption; constructor.
  - exact HT.
Qed.

Local Lemma swap_calls_config_accessories G e fs heap t T Lv :
  @ty_config mode G (config_mk t fs heap e Lv) T ->
  @ty_config_accessories mode G e fs heap t T Lv.
Proof.
  intro H. inversion H; subst. unfold ty_config_accessories. tauto.
Qed.

Local Lemma swap_calls_initial_related ta tb Ta Tb :
  〈ctx_empty⁏empty ⊢ ta ∶ Ta〉 ∼(trf_local_idtyp_trm mode (trf_swap_calls_local mode))∼> 〈ctx_empty⁏empty ⊢ tb ∶ Tb〉 ->
  closed ta ->
  closed tb ->
  closed Ta ->
  exists Ca Cb,
    config_initial ta Ca /\ config_initial tb Cb /\
    @ty_config mode ctx_empty Ca Ta /\
    @ty_config mode ctx_empty Cb Tb /\
    〈ctx_empty ⊢ Ca ∶ Ta〉
      ∼(trf_lift_sim_conf mode (trf_swap_calls_local mode))∼>
    〈ctx_empty ⊢ Cb ∶ Tb〉.
Proof.
  intros Hswap Hca Hcb HT.
  pose proof (proj1 (swap_calls_lifted_typed_empty mode) _ _ Hswap) as Htypes.
  cbn [typed_pair] in Htypes.
  destruct (Htypes eq_refl eq_refl) as [Hta Htb].
  assert (Ta = Tb) by (inversion Hswap; reflexivity).
  subst Tb.
  destruct (var_fresh (fv Ta)) as [null _].
  set (Lv := \{null} \u fv Ta).
  assert (Hnull : exists n, n \in Lv).
  { exists null. unfold Lv. rewrite in_union, in_singleton. auto. }
  assert (Hfv : fv Ta \c Lv).
  { unfold Lv. apply subset_union_weak_r. }
  pose proof (swap_calls_initial_typed Hta Hca HT Hnull Hfv) as HinitA.
  pose proof (swap_calls_initial_typed Htb Hcb HT Hnull Hfv) as HinitB.
  eexists _, _. split; [constructor |]. split; [constructor |].
  split; [exact HinitA |]. split; [exact HinitB |].
  eapply trf_iterate_S.
  - apply trf_iterate_0. exact HinitA.
  - right. apply trf_lift_idtyp_conf_focus.
    eapply trf_focus_idtyp_conf_focus with (Ts := Ta) (Tt := Ta).
    + eapply swap_calls_config_accessories; exact HinitA.
    + eapply swap_calls_config_accessories; exact HinitB.
    + exact swap_calls_empty_heap_correspond.
    + constructor. apply subtyp_refl.
    + exact Hswap.
    + apply subtyp_refl.
Qed.

End InitialConfigurations.

Section Answers.
Context (mode : Mode).

Local Definition answer_element (e : TypedElement ctx typ config) :=
  match e with
  | typed_elem _ _ c => answer c
  end.

Local Definition focus_is_variable (t : trm) :=
  exists x, t = trm_var (avar_f x).

Local Lemma swap_calls_answer_characterization t fs h e fv :
  answer (config_mk t fs h e fv) <-> focus_is_variable t /\ fs = stack_nil.
Proof.
  split.
  - intro H. inversion H; subst. split; [now eexists | reflexivity].
  - intros [[x ->] ->]. constructor.
Qed.

Local Lemma swap_calls_swap_focus_not_variable G e ta tb Ta Tb :
  〈G⁏e ⊢ ta ∶ Ta〉 ∼(trf_local_idtyp_trm mode (trf_swap_calls_local mode))∼> 〈G⁏e ⊢ tb ∶ Tb〉 ->
  ~ focus_is_variable ta /\ ~ focus_is_variable tb.
Proof.
  intro H. inversion H; subst;
    try solve [split; intros [? Hcontra]; discriminate].
  match goal with
  | Hlocal : transform (trf_swap_calls_local _) _ _ |- _ =>
      inversion Hlocal; subst
  end.
  split; intros [? Hcontra]; discriminate.
Qed.

Local Lemma swap_calls_lift_swap_preserves_answer a b :
  a ∼(trf_lift_idtyp_conf mode (trf_swap_calls_local mode))∼> b ->
  (answer_element a <-> answer_element b).
Proof.
  intro H. destruct H.
  - inversion H; subst. cbn [answer_element].
    repeat rewrite swap_calls_answer_characterization.
    match goal with
    | Hswap : transform (trf_local_idtyp_trm _ _) _ _ |- _ =>
        destruct (swap_calls_swap_focus_not_variable Hswap) as [Ha Hb]
    end.
    tauto.
  - cbn [answer_element]. now repeat rewrite swap_calls_answer_characterization.
  - cbn [answer_element]. repeat rewrite swap_calls_answer_characterization.
    match goal with
    | Hstack : transform (trf_lift_idtyp_stack _ _) _ _ |- _ =>
        inversion Hstack; subst
    end;
    split; intros [_ Hnil]; discriminate.
Qed.

Local Lemma swap_calls_subst_preserves_focus x y t :
  focus_is_variable (subst_var x y t) <-> focus_is_variable t.
Proof.
  destruct t; cbn; try solve [split; intros [? H]; discriminate].
  destruct a; cbn.
  - split; intros [? H]; discriminate.
  - split; intro; eexists; reflexivity.
Qed.

Local Lemma swap_calls_subst_vars_preserves_focus xs ys t :
  focus_is_variable (subst_vars xs ys t) <-> focus_is_variable t.
Proof.
  revert ys t.
  induction xs as [|x xs IH]; intros [|y ys] t;
    cbn [vars_zip_map]; try reflexivity.
  rewrite swap_calls_subst_preserves_focus. apply IH.
Qed.

Local Lemma swap_calls_subst_vars_preserves_empty_stack xs ys fs :
  subst_vars xs ys fs = stack_nil <-> fs = stack_nil.
Proof.
  revert ys fs.
  induction xs as [|x xs IH]; intros [|y ys] fs;
    cbn [vars_zip_map]; try reflexivity.
  transitivity (subst_vars xs ys fs = stack_nil); [|apply IH].
  destruct (subst_vars xs ys fs); cbn;
    split; intros H; try discriminate; reflexivity.
Qed.

Local Lemma swap_calls_similarity_preserves_answer a b :
  a ∼(trf_similarity mode)∼> b ->
  (answer_element a <-> answer_element b).
Proof.
  intro H. destruct H as [Ga [ta sa ha ea La] T Gb [tb sb hb eb Lb] Ha Hb Hsim].
  destruct Hsim as [xs [ys [_ [_ [_ [Ht [Hs _]]]]]]].
  change (similar_by_subst xs ys ta tb) in Ht.
  change (similar_by_subst xs ys sa sb) in Hs.
  destruct Ht as [t [zs [_ [_ [_ [_ [<- <-]]]]]]].
  destruct Hs as [s [ws [_ [_ [_ [_ [<- <-]]]]]]].
  cbn [answer_element]. repeat rewrite swap_calls_answer_characterization.
  repeat rewrite swap_calls_subst_vars_preserves_focus.
  repeat rewrite swap_calls_subst_vars_preserves_empty_stack.
  reflexivity.
Qed.

Local Lemma swap_calls_preserves_answer a b :
  a ∼(trf_lift_sim_conf mode (trf_swap_calls_local mode))∼> b ->
  (answer_element a <-> answer_element b).
Proof.
  intro H. induction H as [a Htyped | a b c Hab IH Hbc].
  - reflexivity.
  - transitivity (answer_element b); [exact IH |].
    destruct Hbc as [Hsimilar | Hlift].
    + exact (swap_calls_similarity_preserves_answer Hsimilar).
    + exact (swap_calls_lift_swap_preserves_answer Hlift).
Qed.

End Answers.

Local Lemma swap_calls_local_symmetric mode a b :
  a ∼(trf_swap_calls_local mode)∼> b ->
  b ∼(trf_swap_calls_local mode)∼> a.
Proof.
  intro H. destruct H.
  match goal with Hfresh : fresh _ _ _ |- _ =>
    cbn in Hfresh; destruct Hfresh as [Hy1 [Hy2 _]]
  end.
  apply notin_union in Hy2 as [Hy2 Hneq].
  apply notin_singleton in Hneq.
  eapply (@trf_swap_calls_local_at mode x2 x1 m2 m1 xp2 xp1 y2 y1 t G e T2 T1 T TZ2 TZ1);
    try assumption.
  - cbn [fresh].
    solve_call_freshness.
  - eapply (proj1 (ctx_extends_terms mode)); [eassumption |].
    apply ctx_extends_exchange. exact Hneq.
Qed.

Local Lemma swap_calls_local_lift_symmetric mode :
  (forall a b, a ∼(trf_local_idtyp_trm mode (trf_swap_calls_local mode))∼> b ->
    b ∼(trf_local_idtyp_trm mode (trf_swap_calls_local mode))∼> a) /\
  (forall a b, a ∼(trf_local_idtyp_lit mode (trf_swap_calls_local mode))∼> b ->
    b ∼(trf_local_idtyp_lit mode (trf_swap_calls_local mode))∼> a) /\
  (forall a b, a ∼(trf_local_idtyp_def mode (trf_swap_calls_local mode))∼> b ->
    b ∼(trf_local_idtyp_def mode (trf_swap_calls_local mode))∼> a) /\
  (forall a b, a ∼(trf_local_idtyp_defs mode (trf_swap_calls_local mode))∼> b ->
    b ∼(trf_local_idtyp_defs mode (trf_swap_calls_local mode))∼> a).
Proof.
  apply (@trf_local_idtyp_mutind mode (trf_swap_calls_local mode)
    (fun a b _ => b ∼(trf_local_idtyp_trm mode (trf_swap_calls_local mode))∼> a)
    (fun a b _ => b ∼(trf_local_idtyp_lit mode (trf_swap_calls_local mode))∼> a)
    (fun a b _ => b ∼(trf_local_idtyp_def mode (trf_swap_calls_local mode))∼> a)
    (fun a b _ => b ∼(trf_local_idtyp_defs mode (trf_swap_calls_local mode))∼> a));
    intros; unfold Transformation.transform in *.
  - eapply trf_local_idtyp_trm_local; eauto using swap_calls_local_symmetric.
  - eapply trf_local_idtyp_trm_letl with (L := L); eauto.
  - eapply trf_local_idtyp_trm_letr with (L := L); eauto.
  - eapply trf_local_idtyp_trm_litl with (L := L); eauto.
  - eapply trf_local_idtyp_trm_litr with (L := L); eauto.
  - eapply trf_local_idtyp_lit_fun with (L := L); eauto.
  - eapply trf_local_idtyp_lit_obj with (L := L); eauto.
  - eapply trf_local_idtyp_def_met with (L := L); eauto 6.
  - eapply trf_local_idtyp_defs_one; eauto.
  - eapply trf_local_idtyp_defs_consl; eauto.
  - eapply trf_local_idtyp_defs_consr; eauto.
Qed.

Section Reverse.
Context (mode : Mode).
Local Notation swap := (trf_swap_calls_local mode).

Local Lemma swap_calls_stack_symmetric a b :
  a ∼(trf_lift_idtyp_stack mode swap)∼> b ->
  b ∼(trf_lift_idtyp_stack mode swap)∼> a.
Proof.
  destruct (swap_calls_local_lift_symmetric mode) as [Hterm _].
  intro H. induction H.
  - eapply trf_lift_idtyp_stack_e with (L := L); eauto.
  - eapply trf_lift_idtyp_stack_n with (L := L); eauto.
Qed.

Local Lemma swap_calls_item_symmetric a b :
  a ∼(trf_lift_idtyp_item mode swap)∼> b ->
  b ∼(trf_lift_idtyp_item mode swap)∼> a.
Proof.
  destruct (swap_calls_local_lift_symmetric mode) as [Hterm [_ [_ Hdefs]]].
  intro H. destruct H.
  - eapply trf_lift_idtyp_item_fun with (L := L); eauto.
  - eapply trf_lift_idtyp_item_obj; eauto.
Qed.

Local Lemma swap_calls_heap_symmetric a b :
  a ∼(trf_lift_idtyp_heap mode swap)∼> b ->
  b ∼(trf_lift_idtyp_heap mode swap)∼> a.
Proof.
  intro H. induction H; eauto using trf_lift_idtyp_heap_e,
    trf_lift_idtyp_heap_n, swap_calls_item_symmetric.
Qed.

Local Lemma swap_calls_conf_symmetric a b :
  a ∼(trf_lift_idtyp_conf mode swap)∼> b ->
  b ∼(trf_lift_idtyp_conf mode swap)∼> a.
Proof.
  destruct (swap_calls_local_lift_symmetric mode) as [Hterm _].
  intro H. destruct H.
  - inversion H; subst. apply trf_lift_idtyp_conf_focus.
    eapply trf_focus_idtyp_conf_focus; eauto.
  - eapply trf_lift_idtyp_conf_heap; eauto using swap_calls_heap_symmetric.
  - eapply trf_lift_idtyp_conf_stack; eauto using swap_calls_stack_symmetric.
Qed.

End Reverse.

Local Lemma rename_similarity_symmetric {A : Set} {AF : FreeVar A} {AS : SubstVar A}
    xs ys (a b : A) :
  similar_by_subst xs ys a b -> similar_by_subst ys xs b a.
Proof.
  intros [c [zs [Hx [Hy [Hfresh [Hfv [Ha Hb]]]]]]].
  exists c, zs. repeat split; try assumption.
  replace (fv b \u fv a \u from_list ys \u from_list xs)
    with (fv a \u fv b \u from_list xs \u from_list ys) by
      (apply fset_extens; intros v H; repeat rewrite in_union in *; tauto).
  exact Hfresh.
Qed.

Local Lemma swap_calls_env_similarity_symmetric {A : Set} (AS : Similar A) :
  (forall xs ys a b, similar xs ys a b -> similar ys xs b a) ->
  forall xs ys ks ls a b,
  similar_env_with AS xs ys ks ls a b ->
  similar_env_with AS ys xs ls ks b a.
Proof.
  intros Hvalues xs ys ks ls a b H. induction H.
  - apply similar_env_empty. symmetry. assumption.
  - eapply similar_env_dom; eauto.
  - apply similar_env_notin; auto.
Qed.

Local Lemma swap_calls_config_similarity_symmetric a b :
  similar_conf_1to1 a b -> similar_conf_1to1 b a.
Proof.
  intros [xs [ys [Hx [Hy [Hlen Hsim]]]]].
  exists ys, xs. split; [exact Hy |]. split; [exact Hx |].
  split; [symmetry; exact Hlen |].
  destruct a, b. destruct Hsim as [Hterm [Hstack [Hheap Henv]]].
  repeat split.
  - eapply rename_similarity_symmetric; exact Hterm.
  - eapply rename_similarity_symmetric; exact Hstack.
  - eapply swap_calls_env_similarity_symmetric; [|exact Hheap].
    intros. eapply rename_similarity_symmetric; eassumption.
  - eapply swap_calls_env_similarity_symmetric; [|exact Henv].
    intros. eapply rename_similarity_symmetric; eassumption.
Qed.

Local Lemma swap_calls_similarity_symmetric mode a b :
  a ∼(trf_similarity mode)∼> b ->
  b ∼(trf_similarity mode)∼> a.
Proof.
  intro H. destruct H.
  constructor; eauto using swap_calls_config_similarity_symmetric.
Qed.

Local Lemma swap_calls_reverse_append mode a b :
  a ∼(trf_lift_sim_conf mode (trf_swap_calls_local mode))∼> b ->
  forall c, c ∼(trf_lift_sim_conf mode (trf_swap_calls_local mode))∼> b ->
  c ∼(trf_lift_sim_conf mode (trf_swap_calls_local mode))∼> a.
Proof.
  intro H. induction H as [a Ha | a b d Hab IH Hbd].
  - auto.
  - intros c Hcd. apply IH.
    eapply trf_iterate_S; [exact Hcd |].
    destruct Hbd as [Hsimilar | Hswap].
    + left. apply swap_calls_similarity_symmetric. assumption.
    + right. apply swap_calls_conf_symmetric. assumption.
Qed.

Local Lemma swap_calls_reverse mode a b :
  a ∼(trf_lift_sim_conf mode (trf_swap_calls_local mode))∼> b ->
  TransformCondConfTyped mode b ->
  b ∼(trf_lift_sim_conf mode (trf_swap_calls_local mode))∼> a.
Proof.
  intros Hab Hb. eapply swap_calls_reverse_append; [exact Hab |].
  apply trf_iterate_0. exact Hb.
Qed.

Local Lemma swap_calls_append_typed_steps mode G0 G1 G2 C0 C1 C2 T n k :
  typed_red_closure mode G0 C0 T n G1 C1 ->
  typed_red_closure mode G1 C1 T k G2 C2 ->
  typed_red_closure mode G0 C0 T (n + k) G2 C2.
Proof.
  intros Hprefix Hsuffix. induction Hsuffix.
  - now rewrite Nat.add_0_r.
  - rewrite Nat.add_succ_r. eapply typed_red_step; eauto.
Qed.

Local Lemma swap_calls_answer_no_step C C' : answer C -> C ↦ C' -> False.
Proof. intros Hanswer Hstep. destruct Hanswer. inversion Hstep. Qed.

Local Lemma swap_calls_answer_typed_trace mode G C T n G' C' :
  answer C ->
  typed_red_closure mode G C T n G' C' ->
  n = 0 /\ G' = G /\ C' = C.
Proof.
  intros Hanswer Hsteps. induction Hsteps.
  - auto.
  - destruct IHHsteps as [-> [-> ->]]; [exact Hanswer |].
    exfalso. eapply swap_calls_answer_no_step; [exact Hanswer |].
    eapply swap_calls_typed_step_erases; eassumption.
Qed.

Local Definition call_swap_relation mode :=
  trf_lift_sim_conf mode (trf_swap_calls_local mode).

Local Definition call_swap_prefix_matching mode :=
  forall Ga Gb Ca Cb T n Gfinal Cfinal,
    〈Ga ⊢ Ca ∶ T〉 ∼(call_swap_relation mode)∼> 〈Gb ⊢ Cb ∶ T〉 ->
    typed_red_closure mode Ga Ca T n Gfinal Cfinal ->
    answer Cfinal ->
    ~ answer Ca ->
    exists k l rest Ga' Gb' Ca' Cb',
      0 < k /\ l <= k /\ n = k + rest /\
      typed_red_closure mode Ga Ca T k Ga' Ca' /\
      typed_red_closure mode Gb Cb T l Gb' Cb' /\
      typed_red_closure mode Ga' Ca' T rest Gfinal Cfinal /\
      〈Ga' ⊢ Ca' ∶ T〉 ∼(call_swap_relation mode)∼> 〈Gb' ⊢ Cb' ∶ T〉.

Local Lemma swap_calls_match_terminating_trace mode :
  call_swap_prefix_matching mode ->
  forall n Ga Gb Ca Cb T Gfinal Cfinal,
    〈Ga ⊢ Ca ∶ T〉 ∼(call_swap_relation mode)∼> 〈Gb ⊢ Cb ∶ T〉 ->
    typed_red_closure mode Ga Ca T n Gfinal Cfinal ->
    answer Cfinal ->
    exists m Gb' Cb',
      m <= n /\
      typed_red_closure mode Gb Cb T m Gb' Cb' /\
      answer Cb' /\
      〈Gfinal ⊢ Cfinal ∶ T〉 ∼(call_swap_relation mode)∼> 〈Gb' ⊢ Cb' ∶ T〉.
Proof.
  intros Hmatch n. induction n using lt_wf_ind.
  intros Ga Gb Ca Cb T Gfinal Cfinal Hswap Hrun Hfinal.
  destruct (classic (answer Ca)) as [Ha | Ha].
  - destruct (swap_calls_answer_typed_trace Ha Hrun) as [-> [-> ->]].
    exists 0, Gb, Cb. repeat split; try constructor; try assumption.
    exact (proj1 (swap_calls_preserves_answer Hswap) Ha).
  - destruct (Hmatch _ _ _ _ _ _ _ _ Hswap Hrun Hfinal Ha)
      as [k [l [rest [Ga' [Gb' [Ca' [Cb' [Hk [Hle [Hsum [_ [Hb [Hrest Hswap']]]]]]]]]]]]].
    assert (Hrest_lt : rest < n) by lia.
    destruct (H rest Hrest_lt _ _ _ _ _ _ _ Hswap' Hrest Hfinal)
      as [m [Gb'' [Cb'' [Hmle [Htail [Hbfinal Hrelfinal]]]]]].
    exists (l + m), Gb'', Cb''. repeat split; try assumption.
    + lia.
    + eapply swap_calls_append_typed_steps; eassumption.
Qed.

Local Definition typed_has_answer mode G C T :=
  exists n G' C', typed_red_closure mode G C T n G' C' /\ answer C'.

Local Lemma swap_calls_guarantee_for_related_typable_configurations mode :
  call_swap_prefix_matching mode ->
  forall Ga Gb Ca Cb T,
    〈Ga ⊢ Ca ∶ T〉 ∼(call_swap_relation mode)∼> 〈Gb ⊢ Cb ∶ T〉 ->
    @ty_config mode Gb Cb T ->
    (~ typed_has_answer mode Ga Ca T -> forall n, exists Ca', Ca ⊣n↦* Ca') ->
    (~ typed_has_answer mode Gb Cb T -> forall n, exists Cb', Cb ⊣n↦* Cb') ->
    (exists na nb Ga' Gb' Ca' Cb',
      nb <= na /\
      typed_red_closure mode Ga Ca T na Ga' Ca' /\
      typed_red_closure mode Gb Cb T nb Gb' Cb' /\
      answer Ca' /\ answer Cb' /\
      〈Ga' ⊢ Ca' ∶ T〉 ∼(call_swap_relation mode)∼> 〈Gb' ⊢ Cb' ∶ T〉) \/
    (forall n, exists Ca' Cb', Ca ⊣n↦* Ca' /\ Cb ⊣n↦* Cb').
Proof.
  intros Hmatching Ga Gb Ca Cb T Hswap Htyb HprogressA HprogressB.
  destruct (classic (typed_has_answer mode Ga Ca T)) as [HtermA | HdivA].
  - destruct HtermA as [na [Ga' [Ca' [HrunA HanswerA]]]].
    destruct (swap_calls_match_terminating_trace Hmatching Hswap HrunA HanswerA)
      as [nb [Gb' [Cb' [Hle [HrunB [HanswerB Hrelated]]]]]].
    left. exists na, nb, Ga', Gb', Ca', Cb'. repeat split; assumption.
  - assert (HdivB : ~ typed_has_answer mode Gb Cb T).
    {
      intros [nb [Gb' [Cb' [HrunB HanswerB]]]].
      assert (Hreverse : 〈Gb ⊢ Cb ∶ T〉 ∼(call_swap_relation mode)∼> 〈Ga ⊢ Ca ∶ T〉).
      { eapply swap_calls_reverse; eassumption. }
      destruct (swap_calls_match_terminating_trace Hmatching Hreverse HrunB HanswerB)
        as [na [Ga' [Ca' [_ [HrunA [HanswerA _]]]]]].
      apply HdivA. exists na, Ga', Ca'. auto.
    }
    right. intro n.
    destruct (HprogressA HdivA n) as [Ca' HrunA].
    destruct (HprogressB HdivB n) as [Cb' HrunB].
    exists Ca', Cb'. auto.
Qed.

Local Lemma invert_typed_let mode G e s u T :
  ty_trm mode G objctx_empty e (trm_let s u) T ->
  exists L S,
    ty_trm mode G objctx_empty e s S /\
    (forall x, x \notin L ->
      ty_trm mode (G §ˣ x ~ S) objctx_empty e (open x u) T).
Proof.
  intro Hty. remember (trm_let s u) as t eqn:Heq in Hty.
  induction Hty; inversion Heq; subst.
  - exists L, T. split; assumption.
  - destruct (IHHty eq_refl) as [L [S [Hs Hu]]].
    exists (L \u ctx_dom G), S. split; [exact Hs |].
    intros x Hx. apply notin_union in Hx as [HxL HxG].
    eapply ty_trm_sub; [apply Hu; exact HxL |].
    destruct (ctx_extends_types mode) as [_ [Hsub _]].
    unfold subtyping in *. eapply Hsub; [eassumption |].
    apply ctx_extends_with_fresh. exact HxG.
Qed.

Local Lemma let_push_closed s u fs h e Lv :
  config_closed (config_mk (trm_let s u) fs h e Lv) ->
  config_closed
    (config_mk s (stack_cons (frame_let u) fs) h e
      (fv_config (config_mk (trm_let s u) fs h e Lv))).
Proof.
  intro H. inversion H; subst.
  match goal with Hc : closed (trm_let s u) |- _ => rename Hc into Hlet end.
  match goal with Hc : closed fs |- _ => rename Hc into Hstack end.
  constructor; try assumption; intros n x.
  - specialize (Hlet n x). cbn [open_rec_trm] in Hlet.
    change (trm_let (open_rec n x s) (open_rec (S n) x u) = trm_let s u) in Hlet.
    now injection Hlet.
  - specialize (Hlet n x). cbn [open_rec_trm] in Hlet.
    change (trm_let (open_rec n x s) (open_rec (S n) x u) = trm_let s u) in Hlet.
    injection Hlet as Hu Hs.
    change (stack_cons (frame_let (open_rec (S n) x u)) (open_rec n x fs) =
            stack_cons (frame_let u) fs).
    rewrite ?Hu, ?Hs, Hstack. reflexivity.
Qed.

Local Lemma let_push_preservation mode G s u fs h e Lv T :
  @ty_config mode G (config_mk (trm_let s u) fs h e Lv) T ->
  @ty_config mode G
    (config_mk s (stack_cons (frame_let u) fs) h e
      (fv_config (config_mk (trm_let s u) fs h e Lv))) T.
Proof.
  intro Hty. inversion Hty; subst. unfold obj_typing in *.
  match goal with H : ty_trm _ _ _ _ (trm_let _ _) _ |- _ =>
    destruct (invert_typed_let H) as [L [S [Hs Hu]]]
  end.
  eapply ty_config_c with (T := S); try assumption.
  - eapply ty_stack_let; eassumption.
  - intros x Hx. inversion Hx; subst.
    + apply H9. apply tfree_trm_let_r. assumption.
    + apply H7. assumption.
  - intros x Hx. apply H9. apply tfree_trm_let_l. exact Hx.
  - destruct H11 as [[Hd Hfv] HT].
    split; [split |]; unfold nothing_fresh_in_config in *;
      intros v Hv; do 4 (rewrite in_union; right); eauto.
  - match goal with H : has_null Lv |- _ => destruct H as [null Hnull] end.
    exists null. repeat rewrite in_union. auto 7.
  - eapply let_push_closed; eassumption.
Qed.

Local Lemma kinded_binding_in_context x k T G G' :
  ctx_binds_k_after x k T G G' -> x \in ctx_kdom k G.
Proof.
  intro H. induction H; cbn [ctx_kdom]; case_if; try congruence;
    rewrite ?in_union, ?in_singleton; auto.
Qed.

Local Lemma kinded_binding_in_suffix x k T G G' :
  ctx_binds_k_after x k T G G' -> forall k', ctx_kdom k' G' \c ctx_kdom k' G.
Proof.
  intro H. induction H; intros k' z0 Hv; cbn [ctx_kdom];
    case_if; rewrite ?in_union; auto;
    try right; eapply IHctx_binds_k_after; eassumption.
Qed.

Local Lemma reference_target_in_context mode G e w y :
  @renv_corr mode G e -> binds w y e -> y \in ctx_kdom v_loc G.
Proof.
  intros Hcorr. induction Hcorr; intro Hbind.
  - exfalso. eapply binds_empty_inv; eassumption.
  - apply binds_push_inv in Hbind.
    destruct Hbind as [[-> ->] | [_ Hbind]].
    + eapply kinded_binding_in_suffix.
      * eassumption.
      * eapply kinded_binding_in_context; eassumption.
    + auto.
Qed.

Local Lemma no_functions_in_mutability_mode mode :
  mode_has_mutability mode -> mode_has_fun' mode = false.
Proof. destruct mode; simpl; congruence. Qed.

Local Lemma reference_lookup mode G e h w :
  mode_has_mutability mode ->
  @heap_correspond mode G e h ->
  ctx_k G w v_ref ->
  exists y ds, binds w y e /\ binds y (item_obj ds) h /\ defs_varkinds G ds.
Proof.
  intros Hmut [_ [_ [_ [_ [Hloc [Href [Henv Hitems]]]]]]]
    [T [G' Hbind]].
  assert (Hdom : w \in dom e).
  { rewrite <- Href. eapply kinded_binding_in_context; eassumption. }
  destruct (get_some Hdom) as [y Hy].
  assert (HdomY : y \in dom h).
  { rewrite <- Hloc. eapply reference_target_in_context; eassumption. }
  specialize (Hitems _ HdomY). destruct Hitems.
  - destruct mode; simpl in *; discriminate.
  - eexists _, _. repeat split; eassumption.
Qed.

Local Lemma def_lookup_kinded G ds d :
  defs_varkinds G ds -> defs_has ds d -> def_varkinds G d.
Proof.
  intro H. induction H; unfold defs_has in *; cbn [get_def]; intro Hget.
  - discriminate.
  - case_if. 
    + inversion Hget; subst. assumption.
    + auto.
Qed.

Local Lemma lookup_field_location G ds a v :
  defs_varkinds G ds -> defs_has ds (def_fld a v) ->
  exists y, v = avar_f y /\ ctx_k G y v_loc.
Proof.
  intros Hdefs Hhas.
  pose proof (def_lookup_kinded Hdefs Hhas) as Hkind. inversion Hkind; subst.
  eexists. split; [reflexivity | eassumption].
Qed.

Local Lemma heap_lookup_transport mode G t fs h e Lv T w :
  mode_has_mutability mode ->
  @ty_config mode G (config_mk t fs h e Lv) T ->
  tfree_trm w t ->
  exists y ds, binds w y e /\ binds y (item_obj ds) h /\ defs_varkinds G ds.
Proof.
  intros Hmut Hty Hfree. inversion Hty; subst.
  eapply reference_lookup; [exact Hmut | eassumption |].
  match goal with H : all_tfree_k _ t v_ref |- _ =>
    apply H; exact Hfree
  end.
Qed.

Local Lemma defs_update_has_field ds a v y :
  defs_has ds (def_fld a v) -> exists ds', defs_update ds a y ds'.
Proof.
  unfold defs_has; cbn [label_of DefLabelOf].
  induction ds as [|ds IH d]; cbn [get_def]; intro H.
  - discriminate.
  - case_if.
    + inversion H; subst. eexists. constructor.
    + destruct (IH H) as [ds' Hds']. exists (defs_cons ds' d).
      apply defs_update_push; assumption.
Qed.

Local Lemma replace_heap_item (h : heap) x i i' :
  ok h ->
  binds x i h ->
  exists h',
    ok h' /\ dom h' = dom h /\ binds x i' h' /\
    (forall z v, z <> x -> binds z v h -> binds z v h').
Proof.
  intros Hok. induction Hok as [|h z v Hok IH Hfresh]; intro Hbind.
  - exfalso. eapply binds_empty_inv; eassumption.
  - apply binds_push_inv in Hbind. destruct Hbind as [[-> ->] | [Hneq Hbind]].
    + exists (h & z ~ i'). repeat split.
      * apply ok_push; assumption.
      * now rewrite !dom_push.
      * apply binds_push_eq.
      * intros z' v' Hneq' Hbind. apply binds_push_inv in Hbind.
        destruct Hbind as [[Heq _] | [_ Hbind]]; [congruence |].
        apply binds_push_neq; assumption.
    + destruct (IH Hbind) as [h' [Hok' [Hdom [Hbind' Hothers]]]].
      exists (h' & z ~ v). repeat split.
      * apply ok_push; [exact Hok' |]. unfold notin in *. rewrite Hdom. exact Hfresh.
      * now rewrite !dom_push, Hdom.
      * apply binds_push_neq; assumption.
      * intros z' v' Hneq' Hbind''. apply binds_push_inv in Hbind''.
        destruct Hbind'' as [[-> ->] | [Hneq'' Hb]].
        -- apply binds_push_eq.
        -- apply binds_push_neq; auto.
Qed.

Local Lemma update_existing_field h x ds a v y :
  ok h ->
  binds x (item_obj ds) h ->
  defs_has ds (def_fld a v) ->
  exists h', heap_update h x a y h'.
Proof.
  intros Hok Hbind Hfield.
  destruct (defs_update_has_field y Hfield) as [ds' Hds'].
  destruct (replace_heap_item (item_obj ds') Hok Hbind)
    as [h' [Hok' [Hdom [Hbind' Hothers]]]].
  exists h'. repeat split; try assumption.
  - symmetry. assumption.
  - exists ds, ds'. auto.
Qed.

Local Lemma typed_call_with_member mode G w p a fs h e Lv T :
  mode_has_mutability mode ->
  @ty_config mode G (config_mk (trm_call (avar_f w) a (avar_f p)) fs h e Lv) T ->
  (forall y ds, binds w y e -> binds y (item_obj ds) h ->
    exists body, defs_has ds (def_met a body)) ->
  exists G' C', typed_red mode G (config_mk (trm_call (avar_f w) a (avar_f p)) fs h e Lv) T G' C'.
Proof.
  intros Hmut Htype Hmember.
  destruct (heap_lookup_transport Hmut Htype (tfree_trm_call_l w (avar_f p) a))
    as [y [ds [Href [Hloc Hkind]]]].
  destruct (Hmember y ds Href Hloc) as [body Hbody].
  assert (Hin : inert (typing_mode := mode) G) by (inversion Htype; assumption).
  eexists _, _. eapply (@tred_call mode G w w p y p); eauto.
Qed.

Local Lemma typed_write_with_member mode G w p a fs h e Lv T :
  mode_has_mutability mode ->
  @ty_config mode G (config_mk (trm_write (avar_f w) a (avar_f p)) fs h e Lv) T ->
  (forall y ds, binds w y e -> binds y (item_obj ds) h ->
    exists v, defs_has ds (def_fld a v)) ->
  exists G' C', typed_red mode G (config_mk (trm_write (avar_f w) a (avar_f p)) fs h e Lv) T G' C'.
Proof.
  intros Hmut Htype Hmember.
  destruct (heap_lookup_transport Hmut Htype (tfree_trm_write_l w (avar_f p) a))
    as [y [ds [Href [Hloc Hkind]]]].
  destruct (heap_lookup_transport Hmut Htype (tfree_trm_write_r (avar_f w) p a))
    as [z [dz [Harg [_ _]]]].
  destruct (Hmember y ds Href Hloc) as [v Hfield].
  assert (Hin : inert (typing_mode := mode) G) by (inversion Htype; assumption).
  assert (Hok : ok h).
  { inversion Htype; subst.
    match goal with Hcorr : heap_correspond _ _ _ |- _ =>
      destruct Hcorr as [_ [_ [Hok _]]]; exact Hok
    end. }
  destruct (update_existing_field z Hok Hloc Hfield) as [h' Hupdate].
  eexists _, _. eapply tred_write; eauto.
Qed.

Local Definition free_control_head (t : trm) :=
  match t with
  | trm_var v => exists w, v = avar_f w
  | trm_read v _ => exists w, v = avar_f w
  | trm_write v _ p | trm_call v _ p | trm_apply v p =>
      exists w u, v = avar_f w /\ p = avar_f u
  | trm_let _ _ | trm_lit _ _ => True
  end.

Local Lemma typing_has_free_head mode G e t T :
  ty_trm mode G objctx_empty e t T ->
  free_control_head t.
Proof. intro H. induction H; cbn; eauto. Qed.

Local Definition needs_heap_step (t : trm) :=
  match t with
  | trm_call _ _ _ | trm_apply _ _ | trm_read _ _ | trm_write _ _ _ => True
  | _ => False
  end.

Local Lemma local_swap_widen mode G e ta tb T T' :
  〈G⁏e ⊢ ta ∶ T〉 ∼(trf_local_idtyp_trm mode (trf_swap_calls_local mode))∼> 〈G⁏e ⊢ tb ∶ T〉 ->
  subtyp mode G objctx_empty e T T' ->
  〈G⁏e ⊢ ta ∶ T'〉 ∼(trf_local_idtyp_trm mode (trf_swap_calls_local mode))∼> 〈G⁏e ⊢ tb ∶ T'〉.
Proof.
  intros H Hsub. inversion H; subst; unfold subtyping in *.
  all: try solve [eapply trf_local_idtyp_trm_local; unfold subtyping; try eassumption; eapply subtyp_trans; [eassumption | exact Hsub]].
  all: try solve [eapply trf_local_idtyp_trm_letl with (L := L); unfold subtyping; try eassumption; eapply subtyp_trans; [eassumption | exact Hsub]].
  all: try solve [eapply trf_local_idtyp_trm_letr with (L := L); unfold subtyping; try eassumption; eapply subtyp_trans; [eassumption | exact Hsub]].
  all: try solve [eapply trf_local_idtyp_trm_litl with (L := L); unfold subtyping; try eassumption; eapply subtyp_trans; [eassumption | exact Hsub]].
  all: try solve [eapply trf_local_idtyp_trm_litr with (L := L); unfold subtyping; try eassumption; eapply subtyp_trans; [eassumption | exact Hsub]].
Qed.

Local Definition let_pushed s u fs h e Lv :=
  config_mk s (stack_cons (frame_let u) fs) h e
    (fv_config (config_mk (trm_let s u) fs h e Lv)).

Local Lemma one_typed_let_push mode G s u fs h e Lv T :
  @ty_config mode G (config_mk (trm_let s u) fs h e Lv) T ->
  typed_red_closure mode G (config_mk (trm_let s u) fs h e Lv) T 1 G
    (let_pushed s u fs h e Lv).
Proof.
  intro H.
  eapply typed_red_step; [apply typed_red_refl |].
  unfold let_pushed. eapply tred_let_push; eauto. inversion H; assumption.
Qed.

Local Lemma weaken_under_fresh_binder mode G e x V T T' :
  x \notin ctx_dom G ->
  subtyp mode G objctx_empty e T T' ->
  subtyp mode (G §ˣ x ~ V) objctx_empty e T T'.
Proof.
  intros Hx Hsub.
  eapply (proj1 (proj2 (ctx_extends_types mode))); [exact Hsub |].
  now apply ctx_extends_with_fresh.
Qed.

Local Lemma original_let_stack_for_swapped_focus mode G e fs u L S T Ts T0 :
  @ty_stack mode G e Ts fs T0 ->
  (forall x, x \notin L -> ty_trm mode (G §ˣ x ~ S) objctx_empty e (open x u) T) ->
  subtyp mode G objctx_empty e T Ts ->
  @ty_stack mode G e S (stack_cons (frame_let u) fs) T0.
Proof.
  intros Hstack Hu Hsub.
  eapply ty_stack_let with (L := L \u ctx_dom G); [exact Hstack |].
  intros x Hx. apply notin_union in Hx as [HxL HxG].
  eapply ty_trm_sub; [apply Hu; exact HxL |].
  now apply weaken_under_fresh_binder.
Qed.

Local Lemma swap_calls_step_let_left mode G e fs h sa sb u S T Ts T0 La Lb L :
  @ty_config mode G (config_mk (trm_let sa u) fs h e La) T0 ->
  @ty_config mode G (config_mk (trm_let sb u) fs h e Lb) T0 ->
  〈G⁏e ⊢ sa ∶ S〉 ∼(trf_local_idtyp_trm mode (trf_swap_calls_local mode))∼> 〈G⁏e ⊢ sb ∶ S〉 ->
  @ty_stack mode G e Ts fs T0 ->
  (forall x, x \notin L -> ty_trm mode (G §ˣ x ~ S) objctx_empty e (open x u) T) ->
  subtyp mode G objctx_empty e T Ts ->
  typed_red_closure mode G (config_mk (trm_let sa u) fs h e La) T0 1 G (let_pushed sa u fs h e La) /\
  typed_red_closure mode G (config_mk (trm_let sb u) fs h e Lb) T0 1 G (let_pushed sb u fs h e Lb) /\
  〈G ⊢ (let_pushed sa u fs h e La) ∶ T0〉
    ∼(call_swap_relation mode)∼>
  〈G ⊢ (let_pushed sb u fs h e Lb) ∶ T0〉.
Proof.
  intros Htya Htyb Hswap Hstack Hu Hsub.
  repeat split; try (apply one_typed_let_push; assumption).
  pose proof (let_push_preservation Htya) as Htya'.
  pose proof (let_push_preservation Htyb) as Htyb'.
  unfold let_pushed. eapply trf_iterate_S.
  - apply trf_iterate_0. exact Htya'.
  - right. apply trf_lift_idtyp_conf_focus.
    eapply trf_focus_idtyp_conf_focus with (Tt := S) (Ts := S).
    + eapply swap_calls_config_accessories. exact Htya'.
    + eapply swap_calls_config_accessories. exact Htyb'.
    + inversion Htya'; assumption.
    + eapply original_let_stack_for_swapped_focus; eassumption.
    + exact Hswap.
    + apply subtyp_refl.
Qed.

Local Lemma swap_calls_step_let_right mode G e fs h s ua ub S T Ts T0 La Lb L :
  @ty_config mode G (config_mk (trm_let s ua) fs h e La) T0 ->
  @ty_config mode G (config_mk (trm_let s ub) fs h e Lb) T0 ->
  (forall x, x \notin L ->
    〈G §ˣ x ~ S⁏e ⊢ open x ua ∶ T〉
      ∼(trf_local_idtyp_trm mode (trf_swap_calls_local mode))∼>
    〈G §ˣ x ~ S⁏e ⊢ open x ub ∶ T〉) ->
  ty_trm mode G objctx_empty e s S ->
  @ty_stack mode G e Ts fs T0 ->
  subtyp mode G objctx_empty e T Ts ->
  typed_red_closure mode G (config_mk (trm_let s ua) fs h e La) T0 1 G (let_pushed s ua fs h e La) /\
  typed_red_closure mode G (config_mk (trm_let s ub) fs h e Lb) T0 1 G (let_pushed s ub fs h e Lb) /\
  〈G ⊢ (let_pushed s ua fs h e La) ∶ T0〉
    ∼(call_swap_relation mode)∼>
  〈G ⊢ (let_pushed s ub fs h e Lb) ∶ T0〉.
Proof.
  intros Htya Htyb Hswap Hs Hstack Hsub.
  repeat split; try (apply one_typed_let_push; assumption).
  pose proof (let_push_preservation Htya) as Htya'.
  pose proof (let_push_preservation Htyb) as Htyb'.
  unfold let_pushed. eapply trf_iterate_S.
  - apply trf_iterate_0. exact Htya'.
  - right. eapply trf_lift_idtyp_conf_stack with (Tt := S).
    + eapply swap_calls_config_accessories. exact Htya'.
    + eapply swap_calls_config_accessories. exact Htyb'.
    + inversion Htya'; assumption.
    + eapply trf_lift_idtyp_stack_e with (L := L \u ctx_dom G); [|exact Hstack].
      intros x Hx. apply notin_union in Hx as [HxL HxG].
      eapply local_swap_widen; [apply Hswap; exact HxL |].
      now apply weaken_under_fresh_binder.
    + exact Hs.
Qed.

Local Lemma typed_steps_first_step mode G C T n G' C' :
  typed_red_closure mode G C T n G' C' ->
  match n with
  | 0 => G' = G /\ C' = C
  | S k => exists G1 C1, typed_red mode G C T G1 C1 /\
                        typed_red_closure mode G1 C1 T k G' C'
  end.
Proof.
  intro H. induction H.
  - auto.
  - destruct n as [|k].
    + destruct IHtyped_red_closure as [-> ->].
      eexists _, _. split; [eassumption | constructor].
    + destruct IHtyped_red_closure as [Gx [Cx [Hfirst Hsuffix]]].
      exists Gx, Cx. split; [exact Hfirst |].
      eapply typed_red_step; eassumption.
Qed.

Local Lemma typed_let_push_only_step mode G s u fs h e Lv T G' C' :
  typed_red mode G (config_mk (trm_let s u) fs h e Lv) T G' C' ->
  G' = G /\ C' = let_pushed s u fs h e Lv.
Proof. intro H. unfold let_pushed. inversion H; subst; try discriminate. split; congruence. Qed.

Local Lemma typed_let_trace_suffix mode G s u fs h e Lv T n G' C' :
  typed_red_closure mode G (config_mk (trm_let s u) fs h e Lv) T (S n) G' C' ->
  typed_red_closure mode G (let_pushed s u fs h e Lv) T n G' C'.
Proof.
  intro H.
  destruct (typed_steps_first_step H) as [G1 [C1 [Hfirst Hrest]]].
  destruct (typed_let_push_only_step Hfirst) as [-> ->]. exact Hrest.
Qed.

Local Lemma swap_calls_match_focused_let_left mode G e fs h sa sb u Tl T Ts T0 La Lb L
    n Gfinal Cfinal :
  @ty_config mode G (config_mk (trm_let sa u) fs h e La) T0 ->
  @ty_config mode G (config_mk (trm_let sb u) fs h e Lb) T0 ->
  〈G⁏e ⊢ sa ∶ Tl〉 ∼(trf_local_idtyp_trm mode (trf_swap_calls_local mode))∼> 〈G⁏e ⊢ sb ∶ Tl〉 ->
  @ty_stack mode G e Ts fs T0 ->
  (forall x, x \notin L -> ty_trm mode (G §ˣ x ~ Tl) objctx_empty e (open x u) T) ->
  subtyp mode G objctx_empty e T Ts ->
  typed_red_closure mode G (config_mk (trm_let sa u) fs h e La) T0 (S n) Gfinal Cfinal ->
  exists k l rest Ga' Gb' Ca' Cb',
    0 < k /\ l <= k /\ S n = k + rest /\
    typed_red_closure mode G (config_mk (trm_let sa u) fs h e La) T0 k Ga' Ca' /\
    typed_red_closure mode G (config_mk (trm_let sb u) fs h e Lb) T0 l Gb' Cb' /\
    typed_red_closure mode Ga' Ca' T0 rest Gfinal Cfinal /\
    〈Ga' ⊢ Ca' ∶ T0〉 ∼(call_swap_relation mode)∼> 〈Gb' ⊢ Cb' ∶ T0〉.
Proof.
  intros Hta Htb Hrel Hstack Hbody Hsub Hrun.
  destruct (swap_calls_step_let_left Hta Htb Hrel Hstack Hbody Hsub) as [Ha [Hb Hr]].
  exists 1, 1, n, G, G. exists (let_pushed sa u fs h e La).
  exists (let_pushed sb u fs h e Lb).
  repeat split; try assumption; try lia.
  now apply typed_let_trace_suffix in Hrun.
Qed.

(* Reductions with a saved caller stack. *)

Local Definition attach_stack (suffix : stack) (c : config) :=
  match c with
  | config_mk t fs h e L => config_mk t (stack_append fs suffix) h e L
  end.

Local Lemma stack_append_free_variables fs suffix :
  fv (stack_append fs suffix) = fv fs \u fv suffix.
Proof.
  induction fs as [|f fs IH]; simpl.
  - symmetry. apply union_empty_l.
  - change ((fv f \u fv (stack_append fs suffix)) = (fv f \u fv fs) \u fv suffix).
    rewrite IH. apply union_assoc.
Qed.

Local Lemma attach_stack_free_variables suffix C :
  fv_config (attach_stack suffix C) = fv_config C \u fv suffix.
Proof.
  destruct C as [t fs h e L]. cbn [attach_stack].
  rewrite stack_append_free_variables.
  apply fset_extens; intros x H; repeat rewrite in_union in *; tauto.
Qed.

Local Lemma attach_stack_same_free_variables suffix C :
  fv suffix \c fv_config C ->
  fv_config (attach_stack suffix C) = fv_config C.
Proof.
  intro H. rewrite attach_stack_free_variables.
  apply fset_extens.
  - intros x Hx. rewrite in_union in Hx. destruct Hx; auto.
  - apply subset_union_weak_l.
Qed.

Local Lemma raw_step_keeps_free_variables C D :
  C ↦ D -> fv_config C \c fv_config D.
Proof.
  intro H. destruct H; intros a0 Ha0;
    do 4 (rewrite in_union; right); exact Ha0.
Qed.

Local Lemma replay_step_under_stack suffix C D :
  fv suffix \c fv_config C ->
  C ↦ D ->
  attach_stack suffix C ↦ attach_stack suffix D.
Proof.
  intros Hsuffix Hstep.
  pose proof (@attach_stack_same_free_variables suffix C Hsuffix) as Hfv.
  destruct Hstep; cbn [attach_stack stack_append] in Hfv |- *;
    try (rewrite <- Hfv);
    try (rewrite <- Hfv in H).
  all: eauto using red, red_read, red_let_fun, red_let_obj.
Qed.

Local Lemma raw_steps_keep_free_variables C D n :
  C ⊣n↦* D -> fv_config C \c fv_config D.
Proof.
  intro H. induction H.
  - intros x Hx. exact Hx.
  - intros x Hx. eapply raw_step_keeps_free_variables; eauto.
Qed.

Local Lemma replay_run_under_stack suffix C D n :
  fv suffix \c fv_config C ->
  C ⊣n↦* D ->
  attach_stack suffix C ⊣n↦* attach_stack suffix D.
Proof.
  intros Hsuffix Hrun. induction Hrun.
  - apply red_refl.
  - eapply red_trans; [exact (IHHrun Hsuffix) |].
    apply replay_step_under_stack; [|eassumption].
    intros x Hx.
    eapply raw_steps_keep_free_variables; [eassumption |].
    now apply Hsuffix.
Qed.

Local Lemma answer_without_suffix C suffix :
  answer (attach_stack suffix C) -> answer C.
Proof.
  destruct C; destruct s; cbn [attach_stack stack_append].
  - intro H. inversion H; subst. constructor.
  - intro H. inversion H.
Qed.

Local Lemma project_step_under_stack suffix C E :
  fv suffix \c fv_config C ->
  ~ answer C ->
  attach_stack suffix C ↦ E ->
  exists D, C ↦ D /\ E = attach_stack suffix D.
Proof.
  intros Hsuffix Hanswer Hstep.
  pose proof (@attach_stack_same_free_variables suffix C Hsuffix) as Hfv.
  destruct C as [t fs h e L].
  cbn [attach_stack] in Hfv, Hstep.
  inversion Hstep; subst; clear Hstep.
  all: try solve [
    eexists; split; [econstructor; eauto | cbn [attach_stack]; reflexivity]].
  all: try solve [
    eexists; split; [econstructor; eauto | cbn [attach_stack]; now rewrite Hfv]].
  - rewrite Hfv in *. eexists; split; [eapply red_read; eassumption | reflexivity].
  - rewrite Hfv in *. eexists; split; [eapply red_let_fun; eassumption | reflexivity].
  - rewrite Hfv in *. eexists; split; [eapply red_let_obj; eassumption | reflexivity].
  - destruct fs as [|[u] fs].
    + exfalso. apply Hanswer. constructor.
    + cbn [stack_append] in *.
      match goal with Hfs : stack_cons _ _ = stack_cons _ _ |- _ =>
        inversion Hfs; subst
      end.
      rewrite Hfv in *. eexists; split; [apply red_let_var | reflexivity].
Qed.

Local Lemma raw_cons_step C D E n :
  C ↦ D -> D ⊣n↦* E -> C ⊣(S n)↦* E.
Proof.
  intros Hstep Hrun. induction Hrun.
  - eapply red_trans; [apply red_refl | exact Hstep].
  - eapply red_trans; eauto.
Qed.

Local Lemma first_raw_step C E n :
  C ⊣n↦* E ->
  match n with
  | 0 => E = C
  | S k => exists D, C ↦ D /\ D ⊣k↦* E
  end.
Proof.
  intro H. induction H.
  - reflexivity.
  - destruct n.
    + subst C2. exists C3. split; [assumption | constructor].
    + destruct IHred_closure as [D [Hfirst Hrest]].
      exists D. split; [exact Hfirst |]. eapply red_trans; eassumption.
Qed.

Local Lemma terminating_run_splits_at_frame suffix n C E :
  fv suffix \c fv_config C ->
  attach_stack suffix C ⊣n↦* E ->
  answer E ->
  exists k rest A,
    n = k + rest /\ C ⊣k↦* A /\ answer A /\
    attach_stack suffix A ⊣rest↦* E.
Proof.
  revert C E. induction n as [|n IH]; intros C E Hsuffix Hrun Hend.
  - apply first_raw_step in Hrun. subst E.
    exists 0, 0, C. repeat split; try constructor.
    eapply answer_without_suffix; eassumption.
  - destruct (classic (answer C)) as [Hanswer | Hanswer].
    + exists 0, (S n), C. repeat split; try constructor; assumption.
    + destruct (first_raw_step Hrun) as [E1 [Hfirst Hrest]].
      destruct (@project_step_under_stack suffix C E1 Hsuffix Hanswer Hfirst)
        as [D [Hstep ->]].
      assert (HsuffixD : fv suffix \c fv_config D).
      { intros x Hx. eapply raw_step_keeps_free_variables; [exact Hstep |].
        now apply Hsuffix. }
      destruct (IH D E HsuffixD Hrest Hend) as [k [rest [A [Hlen [Hbody [Hdone Htail]]]]]].
      exists (S k), rest, A. repeat split; try assumption; try lia.
      now eapply raw_cons_step; eassumption.
Qed.

Require Import Deref.

Local Lemma replay_fv_env_push {A : Type} (fv_value : A -> vars) E x a :
  fv_in_values fv_value (E & x ~ a) = fv_value a \u fv_in_values fv_value E.
Proof.
  unfold fv_in_values. rewrite values_def, concat_def, single_def. reflexivity.
Qed.

Local Lemma replay_fv_env_concat {A : Type} (fv_value : A -> vars) E F :
  fv_in_values fv_value (E & F) = fv_in_values fv_value E \u fv_in_values fv_value F.
Proof.
  induction F using env_ind.
  - rewrite concat_empty_r. symmetry.
    unfold fv_in_values. rewrite !values_def, empty_def, LibList.map_nil.
    apply union_empty_r.
  - rewrite concat_assoc, !replay_fv_env_push, IHF.
    apply fset_extens; intros z Hz; repeat rewrite in_union in *; tauto.
Qed.

Local Lemma replay_deref_base_push {A : Set} (Su : SubstVar A) E x v a :
  deref_base Su (E & x ~ v) a = deref_base Su E (subst_var x v a).
Proof. rewrite concat_def, single_def. reflexivity. Qed.

Local Lemma deref_base_concat {A : Set} (S : SubstVar A) E F (a : A) :
  deref_base S (E & F) a = deref_base S E (deref_base S F a).
Proof.
  revert a. induction F using env_ind; intro a.
  - rewrite concat_empty_r, empty_def. reflexivity.
  - rewrite concat_assoc, !replay_deref_base_push. apply IHF.
Qed.

Local Lemma replay_deref_defs_concat E F ds :
  deref (E & F) ds = deref E (deref F ds).
Proof.
  induction ds; [reflexivity |].
  change (defs_cons (deref (E & F) ds) (deref (E & F) d) =
    defs_cons (deref E (deref F ds)) (deref E (deref F d))).
  rewrite IHds. f_equal.
  destruct d; try reflexivity.
  change (def_fld f (deref_base AvarSubstVar (E & F) a) =
    def_fld f (deref_base AvarSubstVar E (deref_base AvarSubstVar F a))).
  now rewrite deref_base_concat.
Qed.

Local Lemma replay_deref_avar_fresh E (a : avar) :
  (forall v, v \in fv a -> v # E) ->
  deref E a = a.
Proof.
  induction E using env_ind; intros Hfresh.
  - unfold deref, deref_avar. rewrite empty_def. reflexivity.
  - unfold deref, deref_avar. rewrite replay_deref_base_push.
    change (deref E (subst_var x v a) = a).
    assert (Heq : subst_var x v a = a).
    {
      destruct a as [i | y]; [reflexivity |].
      assert (Hxy : y <> x).
      { intro Heq. subst y.
        assert (Hx : x \in fv (avar_f x)).
        { change (x \in \{x}). now rewrite in_singleton. }
        specialize (Hfresh x Hx).
        apply Hfresh. rewrite dom_push, in_union, in_singleton. auto. }
      cbn. case_if; congruence.
    }
    rewrite Heq. apply IHE. intros z Hz HzE.
    eapply Hfresh; [exact Hz |].
    rewrite dom_push, in_union. auto.
Qed.

Local Lemma replay_deref_defs_fresh E ds :
  (forall v, v \in fv ds -> v # E) ->
  deref E ds = ds.
Proof.
  induction ds as [|ds IH d]; intro Hfresh; [reflexivity |].
  change (defs_cons (deref E ds) (deref E d) = defs_cons ds d).
  f_equal.
  - apply IH. intros x Hx. apply Hfresh.
    change (x \in fv ds \u fv d). rewrite in_union. auto.
  - destruct d; try reflexivity.
    change (def_fld f (deref E a) = def_fld f a).
    f_equal. apply replay_deref_avar_fresh. intros x Hx. apply Hfresh.
    change (x \in fv ds \u fv a). rewrite in_union. auto.
Qed.

Local Lemma replay_ok_concat {A : Type} (E F : env A) :
  ok E -> ok F -> (forall x, x \in dom F -> x # E) -> ok (E & F).
Proof.
  intros HE HF. induction HF; intros Hsep.
  - now rewrite concat_empty_r.
  - rewrite concat_assoc.
    apply ok_push.
    + apply IHHF. intros z Hz. apply Hsep.
      rewrite dom_push, in_union. auto.
    + intro Hx. rewrite dom_concat, in_union in Hx.
      destruct Hx as [HxE | HxF].
      * eapply Hsep; [|exact HxE]. rewrite dom_push, in_union, in_singleton. auto.
      * contradiction.
Qed.

Local Lemma replay_heap_update_before H S x a y S' :
  ok H ->
  (forall z, z \in dom S -> z # H) ->
  heap_update S x a y S' ->
  heap_update (H & S) x a y (H & S').
Proof.
  intros Hextra Hsep [Hok [Hok' [Hdom [Hrest [ds [ds' [Hitem [Hupdate Hitem']]]]]]]].
  unfold heap_update. repeat split.
  - apply replay_ok_concat; assumption.
  - apply replay_ok_concat; try assumption. now rewrite <- Hdom.
  - rewrite !dom_concat. now rewrite Hdom.
  - intros z v Hneq Hz.
    apply binds_concat_inv in Hz. destruct Hz as [Hb | [Hout Hb]].
    + apply binds_concat_right. now apply Hrest.
    + apply binds_concat_left; [exact Hb |]. now rewrite <- Hdom.
  - exists ds, ds'. repeat split; auto using binds_concat_right.
Qed.

Local Definition extension_variables (H : heap) (E : renv) :=
  fv_heap H \u fv_renv E.

Local Definition extend_machine (H : heap) (E : renv) (L : vars) (C : config) :=
  match C with
  | config_mk t fs h e _ => config_mk t fs (H & h) (E & e) L
  end.

Local Lemma extend_machine_variable_bound H E L C :
  L \c fv_config C \u extension_variables H E ->
  fv_config (extend_machine H E L C) \c fv_config C \u extension_variables H E.
Proof.
  intros Hmask x Hx. destruct C.
  cbn [extend_machine] in Hx.
  rewrite !dom_concat, !replay_fv_env_concat in Hx.
  unfold extension_variables in *.
  cbn in Hmask.
  specialize (Hmask x).
  repeat rewrite in_union in *.
  repeat destruct Hx as [Hx | Hx]; (auto 12 || apply Hmask; exact Hx).
Qed.

Local Lemma fresh_vars_notin L xs n :
  fresh L n xs ->
  forall x, x \in from_list xs -> x \notin L.
Proof.
  revert n L. induction xs as [|y ys IH]; intros [|n] L H x Hx; cbn [fresh] in H;
    try contradiction.
  - rewrite from_list_nil, in_empty in Hx. contradiction.
  - rewrite from_list_cons, in_union, in_singleton in Hx.
    destruct H as [Hy Hrest]. destruct Hx as [-> | Hx]; [exact Hy |].
    pose proof (IH _ _ Hrest _ Hx) as Hnot.
    apply notin_union in Hnot. tauto.
Qed.

Local Lemma fresh_decrease_set L L' xs n :
  L' \c L -> fresh L n xs -> fresh L' n xs.
Proof.
  revert n L L'. induction xs as [|y ys IH]; intros [|n] L L' Hsub H;
    cbn [fresh] in *; try contradiction; auto.
  destruct H as [Hy Hrest]. split.
  - intro H. apply Hy. now apply Hsub.
  - eapply IH; [|exact Hrest].
    intros z Hz. rewrite in_union in *. destruct Hz; auto.
Qed.

Local Lemma fresh_add_avoided_set L X xs n :
  fresh L n xs ->
  (forall x, x \in from_list xs -> x \notin X) ->
  fresh (L \u X) n xs.
Proof.
  revert n L X. induction xs as [|y ys IH]; intros [|n] L X H Havoid;
    cbn [fresh] in *; try contradiction; auto.
  destruct H as [Hy Hrest]. split.
  - apply notin_union. split; [exact Hy |].
    apply Havoid. rewrite from_list_cons, in_union, in_singleton. auto.
  - assert (Htail : forall x, x \in from_list ys -> x \notin X).
    { intros x Hx. apply Havoid. rewrite from_list_cons, in_union. auto. }
    eapply fresh_decrease_set; [|exact (IH n (L \u \{y}) X Hrest Htail)].
    intros z Hz. repeat rewrite in_union in *. tauto.
Qed.

Local Lemma replay_fresh H E L C D xs n :
  L \c fv_config C \u extension_variables H E ->
  (forall v, v \in fv_config D -> v \notin fv_config C ->
     v \notin extension_variables H E) ->
  from_list xs \c fv_config D ->
  fresh (fv_config C) n xs ->
  fresh (fv_config (extend_machine H E L C)) n xs.
Proof.
  intros Hmask Hnew Hnames Hfresh.
  eapply fresh_decrease_set; [apply extend_machine_variable_bound; exact Hmask |].
  eapply fresh_add_avoided_set; [exact Hfresh |].
  intros x Hx. apply Hnew.
  - now apply Hnames.
  - eapply fresh_vars_notin; eassumption.
Qed.

Local Lemma dom_heap_in_machine_fv t fs h e L :
  dom h \c fv_config (config_mk t fs h e L).
Proof. intros x Hx. repeat rewrite in_union. tauto. Qed.

Local Lemma dom_env_in_machine_fv t fs h e L :
  dom e \c fv_config (config_mk t fs h e L).
Proof. intros x Hx. repeat rewrite in_union. tauto. Qed.

Local Lemma replay_resolve_fields E e ds y h t fs L :
  (forall x, x \in fv_config (config_mk t fs (h & y ~ item_obj (deref e ds)) e L) -> x # E) ->
  deref (E & e) ds = deref e ds.
Proof.
  intro Hkeys. rewrite replay_deref_defs_concat.
  apply replay_deref_defs_fresh. intros x Hx. apply Hkeys.
  rewrite replay_fv_env_push. cbn [ItemFreeVar fv_item].
  repeat rewrite in_union. auto 8.
Qed.

Local Lemma replay_step_with_extensions H E L C D :
  ok H ->
  (forall x, x \in fv_config D -> x # H) ->
  (forall x, x \in fv_config D -> x # E) ->
  (forall x, x \in fv_config D -> x \notin fv_config C ->
    x \notin extension_variables H E) ->
  L \c fv_config C \u extension_variables H E ->
  C ↦ D ->
  extend_machine H E L C ↦
    extend_machine H E (fv_config (extend_machine H E L C)) D.
Proof.
  intros Hok Hheap Henv Hnew Hmask Hstep.
  pose proof (raw_step_keeps_free_variables Hstep) as Hkeep.
  destruct Hstep; cbn [extend_machine].
  - rewrite concat_assoc.
    eapply red_read; [|apply binds_concat_right; eassumption |
       apply binds_concat_right; eassumption | eassumption].
    eapply (@replay_fresh H E L
      (config_mk (trm_read (avar_f wObj) m) fs Sigma e Lv)
      (config_mk (trm_var (avar_f wVal)) fs Sigma (e & wVal ~ yVal)
         (fv_config (config_mk (trm_read (avar_f wObj) m) fs Sigma e Lv))));
      [exact Hmask | exact Hnew | | eassumption].
    intros x Hx. rewrite from_list_cons, from_list_nil, union_empty_r, in_singleton in Hx.
    subst x. apply dom_env_in_machine_fv.
    rewrite dom_push, in_union, in_singleton. auto.
  - eapply red_write; [|apply binds_concat_right; eassumption |
                        apply binds_concat_right; eassumption].
    apply replay_heap_update_before; try eassumption.
    intros x Hx. apply Hheap, Hkeep.
    now apply dom_heap_in_machine_fv.
  - eapply red_call; [apply binds_concat_right; eassumption | eassumption |
                      apply binds_concat_right; eassumption].
  - eapply red_apply; apply binds_concat_right; eassumption.
  - rewrite !concat_assoc.
    apply red_let_fun; [|assumption].
    eapply (@replay_fresh H E L
      (config_mk (trm_lit (lit_fun T t1) t2) fs Sigma e Lv)
      (config_mk (open w t2) fs (Sigma & y ~ item_fun t1) (e & w ~ y)
         (fv_config (config_mk (trm_lit (lit_fun T t1) t2) fs Sigma e Lv))));
      [exact Hmask | exact Hnew | | eassumption].
    intros x Hx. rewrite !from_list_cons, from_list_nil, union_empty_r, in_union,
      !in_singleton in Hx. destruct Hx as [-> | ->].
    + apply dom_heap_in_machine_fv. rewrite dom_push, in_union, in_singleton. auto.
    + apply dom_env_in_machine_fv. rewrite dom_push, in_union, in_singleton. auto.
  - assert (Hdefs : deref (E & (e & w ~ y)) (open w ds) = deref (e & w ~ y) (open w ds)).
    { eapply replay_resolve_fields with (y := y) (h := Sigma)
          (t := open w t) (fs := fs) (L := fv_config (config_mk (trm_lit (lit_obj T ds) t) fs Sigma e Lv)).
      exact Henv. }
    unfold deref in Hdefs. rewrite <- Hdefs.
    rewrite !concat_assoc.
    apply red_let_obj; [|assumption].
    eapply (@replay_fresh H E L
      (config_mk (trm_lit (lit_obj T ds) t) fs Sigma e Lv)
      (config_mk (open w t) fs (Sigma & y ~ item_obj (deref (e & w ~ y) (open w ds)))
         (e & w ~ y)
         (fv_config (config_mk (trm_lit (lit_obj T ds) t) fs Sigma e Lv))));
      [exact Hmask | exact Hnew | | eassumption].
    intros x Hx. rewrite !from_list_cons, from_list_nil, union_empty_r, in_union,
      !in_singleton in Hx. destruct Hx as [-> | ->].
    + apply dom_heap_in_machine_fv. rewrite dom_push, in_union, in_singleton. auto.
    + apply dom_env_in_machine_fv. rewrite dom_push, in_union, in_singleton. auto.
  - apply red_let_var.
  - apply red_let_push.
Qed.

Local Lemma replay_run_with_extensions H E L C D n :
  ok H ->
  C ⊣n↦* D ->
  (forall x, x \in fv_config D -> x # H) ->
  (forall x, x \in fv_config D -> x # E) ->
  (forall x, x \in fv_config D -> x \notin fv_config C ->
    x \notin extension_variables H E) ->
  L \c fv_config C \u extension_variables H E ->
  exists L',
    extend_machine H E L C ⊣n↦* extend_machine H E L' D /\
    L' \c fv_config D \u extension_variables H E.
Proof.
  intros Hok Hrun.
  induction Hrun as [C | C1 C2 C3 n Hrun IH Hstep]; intros Hheap Henv Hnew Hmask.
  - exists L. split; [apply red_refl | exact Hmask].
  - assert (Hkeep : fv_config C2 \c fv_config C3) by (apply raw_step_keeps_free_variables; assumption).
    destruct IH as [L2 [Hrun2 Hmask2]].
    + intros x Hx. apply Hheap, Hkeep, Hx.
    + intros x Hx. apply Henv, Hkeep, Hx.
    + intros x Hx Hx1. apply Hnew; [now apply Hkeep | exact Hx1].
    + exact Hmask.
    + exists (fv_config (extend_machine H E L2 C2)). split.
      * eapply red_trans; [exact Hrun2 |].
        eapply replay_step_with_extensions; try eassumption.
        intros x Hx Hx2. apply Hnew; [exact Hx |].
        intro Hx1. apply Hx2. eapply raw_steps_keep_free_variables; eassumption.
      * intros x Hx.
        pose proof (@extend_machine_variable_bound H E L2 C2 Hmask2 x Hx) as Hbounds.
        rewrite in_union in Hbounds |- *. destruct Hbounds; auto.
Qed.

(* Replay across stores with the same lookups. *)

Local Definition same_bindings {A : Type} (e f : env A) :=
  forall x v, binds x v e <-> binds x v f.

Local Lemma same_bindings_same_domain {A : Type} (e f : env A) :
  same_bindings e f -> dom e = dom f.
Proof.
  intro H. apply fset_extens; intros x Hx;
    destruct (get_some Hx) as [v Hv].
  - apply get_some_inv with (v := v). now apply H.
  - apply get_some_inv with (v := v). now apply H.
Qed.

Local Lemma same_bindings_push {A : Type} (e f : env A) x v :
  same_bindings e f -> same_bindings (e & x ~ v) (f & x ~ v).
Proof.
  intros H y w. split; intro Hb; apply binds_push_inv in Hb;
    destruct Hb as [[-> ->] | [Hneq Hb]];
    auto using binds_push_eq, binds_push_neq.
  all: apply binds_push_neq; [now apply H | exact Hneq].
Qed.

Local Lemma fv_env_value_member {A : Type} (fv_value : A -> vars) e x :
  ok e ->
  x \in fv_in_values fv_value e <-> exists w v, binds w v e /\ x \in fv_value v.
Proof.
  intro Hok. induction Hok as [|e w v Hok IH Hfresh].
  - assert (Hem : fv_in_values fv_value (@empty A) = \{}).
    { unfold fv_in_values. rewrite values_def, empty_def, LibList.map_nil. reflexivity. }
    rewrite Hem, in_empty. split; [tauto |].
    intros [y [u [Hy _]]]. eapply binds_empty_inv; eassumption.
  - rewrite replay_fv_env_push, in_union, IH.
    split.
    + intros [Hnew | [y [u [Hy Hu]]]].
      * exists w, v. split; auto using binds_push_eq.
      * exists y, u. split; [|exact Hu].
        apply binds_push_neq; [exact Hy |].
        intro Heq. subst y. eapply binds_fresh_inv; eassumption.
    + intros [y [u [Hy Hu]]]. apply binds_push_inv in Hy.
      destruct Hy as [[_ ->] | [_ Hy]]; [now left |].
      right; eauto.
Qed.

Local Lemma fv_env_same_bindings {A : Type} (fv_value : A -> vars) e f :
  ok e -> ok f -> same_bindings e f ->
  fv_in_values fv_value e = fv_in_values fv_value f.
Proof.
  intros He Hf Hbind. apply fset_extens; intros x Hx.
  - apply (proj2 (@fv_env_value_member A fv_value f x Hf)).
    destruct (proj1 (@fv_env_value_member A fv_value e x He) Hx)
      as [w [v [Hb Hv]]].
    exists w, v. split; [now apply Hbind | exact Hv].
  - apply (proj2 (@fv_env_value_member A fv_value e x He)).
    destruct (proj1 (@fv_env_value_member A fv_value f x Hf) Hx)
      as [w [v [Hb Hv]]].
    exists w, v. split; [now apply Hbind | exact Hv].
Qed.

Local Lemma same_bindings_concat_commute {A : Type} (E F : env A) :
  disjoint (dom E) (dom F) ->
  same_bindings (E & F) (F & E).
Proof.
  intros Hseparate x v. split; intro Hbind;
    apply binds_concat_inv in Hbind;
    destruct Hbind as [Hbind | [Hout Hbind]];
    try solve [apply binds_concat_right; exact Hbind].
  - apply binds_concat_left; [exact Hbind |].
    eapply disjoint_in_notin; [exact (disjoint_comm Hseparate) |].
    eapply get_some_inv; eassumption.
  - apply binds_concat_left; [exact Hbind |].
    eapply disjoint_in_notin; [exact Hseparate |].
    eapply get_some_inv; eassumption.
Qed.

Local Lemma deref_bound_value e w y :
  renv_idempotent e ->
  binds w y e ->
  deref e (avar_f w) = avar_f y.
Proof.
  induction e using env_ind; intros Hidem Hb.
  - exfalso. eapply binds_empty_inv; eassumption.
  - unfold deref, deref_avar. rewrite replay_deref_base_push.
    change (deref e (subst_var x v (avar_f w)) = avar_f y).
    apply binds_push_inv in Hb.
    destruct Hb as [[-> ->] | [Hneq Hb]].
    + assert (Hsub : subst_var x v (avar_f x) = avar_f v).
      { cbn. case_if; congruence. }
      rewrite Hsub. apply replay_deref_avar_fresh.
      intros z Hz. change (z \in \{v}) in Hz.
      rewrite in_singleton in Hz. subst z.
      intro Hbad. apply (Hidem v).
      * rewrite dom_push, in_union. auto.
      * rewrite replay_fv_env_push, in_union. left.
        change (v \in \{v}). now rewrite in_singleton.
    + assert (Hsub : subst_var x v (avar_f w) = avar_f w).
      { cbn. case_if; congruence. }
      rewrite Hsub. apply IHe; [|exact Hb].
      intros z Hz Hbad. apply (Hidem z).
      * rewrite dom_push, in_union. auto.
      * rewrite replay_fv_env_push, in_union. auto.
Qed.

Local Lemma deref_same_binding e f (ds : defs) :
  renv_idempotent e -> renv_idempotent f -> same_bindings e f ->
  deref e ds = deref f ds.
Proof.
  intros He Hf Hsame. induction ds as [|ds IH d]; [reflexivity |].
  change (defs_cons (deref e ds) (deref e d) = defs_cons (deref f ds) (deref f d)).
  rewrite IH. f_equal. destruct d; try reflexivity.
  change (def_fld f0 (deref e a) = def_fld f0 (deref f a)). f_equal.
  destruct a as [k | w].
  - transitivity (avar_b k); [|symmetry]; apply replay_deref_avar_fresh.
    all: intros z Hz; change (z \in \{}) in Hz; rewrite in_empty in Hz; contradiction.
  - destruct (classic (w \in dom e)) as [Hin | Hout].
    + destruct (get_some Hin) as [v Hb].
      transitivity (avar_f v); [|symmetry]; apply deref_bound_value; auto.
      now apply Hsame.
    + assert (Hout' : w # f).
      { rewrite <- (same_bindings_same_domain Hsame). exact Hout. }
      transitivity (avar_f w); [|symmetry]; apply replay_deref_avar_fresh;
        intros z Hz; change (z \in \{w}) in Hz; rewrite in_singleton in Hz;
        subst z; assumption.
Qed.

Local Definition same_valid_bindings {A : Type} (e f : env A) :=
  ok e /\ ok f /\ same_bindings e f.

Local Lemma same_valid_bindings_push {A : Type} (e f : env A) x v :
  same_valid_bindings e f ->
  x # e ->
  same_valid_bindings (e & x ~ v) (f & x ~ v).
Proof.
  intros [He [Hf Hbind]] Hfresh. split; [|split].
  - apply ok_push; assumption.
  - apply ok_push; [exact Hf |]. now rewrite <- (same_bindings_same_domain Hbind).
  - now apply same_bindings_push.
Qed.

Local Lemma same_valid_bindings_refl {A : Type} (e : env A) :
  ok e -> same_valid_bindings e e.
Proof. intro H. split; [exact H |]. split; [exact H |]. firstorder. Qed.

Local Lemma deref_agreement_push e f w y :
  (forall ds : defs, deref e ds = deref f ds) ->
  forall ds : defs, deref (e & w ~ y) ds = deref (f & w ~ y) ds.
Proof. intros He ds. rewrite !replay_deref_defs_concat. apply He. Qed.

Local Lemma heap_update_equivalent_source h1 h2 x a y h' :
  same_valid_bindings h1 h2 ->
  heap_update h1 x a y h' ->
  heap_update h2 x a y h'.
Proof.
  intros [H1 [H2 Hbind]] [_ [Hok' [Hdom [Hother [ds [ds' [H1x [Hupd Hdst]]]]]]]].
  unfold heap_update. repeat split; try assumption.
  - rewrite <- (same_bindings_same_domain Hbind). exact Hdom.
  - intros z v Hneq Hb. apply Hother; [exact Hneq | now apply Hbind].
  - exists ds, ds'. split; [now apply Hbind | auto].
Qed.

Local Definition raw_store_agreement (C D : config) :=
  match C,D with
  | config_mk t fs h e L, config_mk t' fs' h' e' L' =>
    t = t' /\ fs = fs' /\ L = L' /\
    same_valid_bindings h h' /\ same_valid_bindings e e' /\
    (forall ds : defs, deref e ds = deref e' ds)
  end.

Local Lemma raw_store_agreement_free_variables C D :
  raw_store_agreement C D -> fv_config C = fv_config D.
Proof.
  destruct C, D.
  intros [-> [-> [-> [[Hs [Hs0 Hheap]] [[He [He0 Henv]] _]]]]].
  rewrite (same_bindings_same_domain Hheap), (same_bindings_same_domain Henv).
  rewrite (fv_env_same_bindings fv Hs Hs0 Hheap).
  rewrite (fv_env_same_bindings fv He He0 Henv). reflexivity.
Qed.

Local Lemma fresh_from_machine_for_heap t fs h e L x :
  x \notin fv_config (config_mk t fs h e L) -> x # h.
Proof. intros H Hx. apply H. now apply dom_heap_in_machine_fv. Qed.

Local Lemma fresh_from_machine_for_env t fs h e L x :
  x \notin fv_config (config_mk t fs h e L) -> x # e.
Proof. intros H Hx. apply H. now apply dom_env_in_machine_fv. Qed.

Local Ltac agreement_split :=
  cbn [raw_store_agreement];
  split; [reflexivity |
  split; [reflexivity |
  split; [reflexivity |
  split; [try assumption | split; try assumption]]]].

Local Lemma replay_step_same_store C1 D1 C2 :
  C1 ↦ D1 ->
  raw_store_agreement C1 C2 ->
  exists D2, C2 ↦ D2 /\ raw_store_agreement D1 D2.
Proof.
  intros Hstep. revert C2.
  destruct Hstep; intros [tA fsA hA eA LA] Hagree;
    pose proof (@raw_store_agreement_free_variables _ _ Hagree) as Hfv;
    cbn [raw_store_agreement] in Hagree;
    destruct Hagree as [<- [<- [<- [Hheap [Henv Hderef]]]]];
    pose proof (proj2 (proj2 Hheap)) as HbindH;
    pose proof (proj2 (proj2 Henv)) as HbindE.
  - eexists. split.
    + eapply (@red_read yObj wObj m hA eA Lv yVal wVal ds fs);
        [rewrite <- Hfv; eassumption | apply HbindE; eassumption | apply HbindH; eassumption | eassumption].
    + change (fv_config (config_mk (trm_read (avar_f wObj) m) fs Sigma e Lv) =
        fv_config (config_mk (trm_read (avar_f wObj) m) fs hA eA Lv)) in Hfv.
      rewrite <- Hfv. agreement_split.
      * apply same_valid_bindings_push; [exact Henv |].
        eapply fresh_from_machine_for_env. exact (proj1 H).
      * now apply deref_agreement_push.
  - assert (Hupd : heap_update hA yObj m yArg Sigma')
      by (eapply heap_update_equivalent_source; eassumption).
    eexists. split.
    + eapply red_write; [exact Hupd | apply HbindE; eassumption | apply HbindE; eassumption].
    + rewrite <- Hfv. agreement_split.
      apply same_valid_bindings_refl. destruct Hupd as [_ [Hok _]]. exact Hok.
  - eexists. split.
    + eapply red_call; [apply HbindH; eassumption | eassumption | apply HbindE; eassumption].
    + rewrite <- Hfv. agreement_split.
  - eexists. split.
    + eapply red_apply; [apply HbindH; eassumption | apply HbindE; eassumption].
    + rewrite <- Hfv. agreement_split.
  - eexists. split.
    + eapply red_let_fun with (y := y) (w := w); [rewrite <- Hfv; eassumption | assumption].
    + rewrite <- Hfv. agreement_split.
      * apply same_valid_bindings_push; [exact Hheap |].
        eapply fresh_from_machine_for_heap. exact (proj1 H).
      * apply same_valid_bindings_push; [exact Henv |].
        eapply fresh_from_machine_for_env.
        pose proof (proj1 (proj2 H)) as Hw. apply notin_union in Hw as [Hw _]. exact Hw.
      * now apply deref_agreement_push.
  - eexists. split.
    + eapply red_let_obj with (y := y) (w := w); [rewrite <- Hfv; eassumption | assumption].
    + assert (Hdefs : deref (e & w ~ y) (open w ds) = deref (eA & w ~ y) (open w ds))
        by (apply deref_agreement_push; exact Hderef).
      unfold deref in Hdefs. rewrite <- Hdefs, <- Hfv. agreement_split.
      * apply same_valid_bindings_push; [exact Hheap |].
        eapply fresh_from_machine_for_heap. exact (proj1 H).
      * apply same_valid_bindings_push; [exact Henv |].
        eapply fresh_from_machine_for_env.
        pose proof (proj1 (proj2 H)) as Hw. apply notin_union in Hw as [Hw _]. exact Hw.
      * now apply deref_agreement_push.
  - eexists. split; [apply red_let_var |]. rewrite <- Hfv. agreement_split.
  - eexists. split; [apply red_let_push |]. rewrite <- Hfv. agreement_split.
Qed.

Local Lemma replay_run_same_store C1 D1 C2 n :
  C1 ⊣n↦* D1 ->
  raw_store_agreement C1 C2 ->
  exists D2, C2 ⊣n↦* D2 /\ raw_store_agreement D1 D2.
Proof.
  intro Hrun. induction Hrun; intro Hsame.
  - exists C2. split; [constructor | exact Hsame].
  - destruct (IHHrun Hsame) as [D [Hprefix HsameD]].
    destruct (@replay_step_same_store _ _ _ H HsameD) as [E [Hstep Hresult]].
    exists E. split; [eapply red_trans; eassumption | exact Hresult].
Qed.

Local Lemma same_valid_bindings_commute {A : Type} (e f : env A) :
  ok e -> ok f -> (forall x, x \in dom f -> x # e) ->
  same_valid_bindings (e & f) (f & e).
Proof.
  intros He Hf Hsep. split.
  - apply replay_ok_concat; assumption.
  - split.
    + apply replay_ok_concat; try assumption.
      intros x Hx Hxf. exact (Hsep x Hxf Hx).
    + apply same_bindings_concat_commute.
      unfold disjoint. apply fset_extens; intros x Hx.
      * rewrite in_inter in Hx. destruct Hx as [Hex Hfx].
        exfalso. exact (Hsep x Hfx Hex).
      * rewrite in_empty in Hx. contradiction.
Qed.

Local Lemma replay_after_independent_allocation t fs h e Lv H E L D n :
  ok h -> ok e -> ok H -> ok E ->
  renv_idempotent (E & e) ->
  (config_mk t fs h e Lv) ⊣n↦* D ->
  (forall x, x \in fv_config D -> x # H) ->
  (forall x, x \in fv_config D -> x # E) ->
  (forall x, x \in fv_config D -> x \notin fv_config (config_mk t fs h e Lv) ->
    x \notin extension_variables H E) ->
  L \c fv_config (config_mk t fs h e Lv) \u extension_variables H E ->
  exists L' D',
    (config_mk t fs (h & H) (e & E) L) ⊣n↦* D' /\
    raw_store_agreement (extend_machine H E L' D) D'.
Proof.
  intros Hokh Hoke HokH HokE Hidem Htrace Hheap Henv Hnew Hmask.
  destruct (@replay_run_with_extensions H E L (config_mk t fs h e Lv)
    D n HokH Htrace Hheap Henv Hnew Hmask)
    as [L' [Htrace' Hmask']].
  assert (Hh : same_valid_bindings (H & h) (h & H)).
  {
    apply same_valid_bindings_commute; try assumption.
    intros x Hx. apply Hheap. eapply raw_steps_keep_free_variables; [exact Htrace |].
    now apply dom_heap_in_machine_fv.
  }
  assert (He : same_valid_bindings (E & e) (e & E)).
  {
    apply same_valid_bindings_commute; try assumption.
    intros x Hx. apply Henv. eapply raw_steps_keep_free_variables; [exact Htrace |].
    now apply dom_env_in_machine_fv.
  }
  assert (Hderef : forall ds : defs, deref (E & e) ds = deref (e & E) ds).
  {
    destruct He as [He1 [He2 Hsame]]. intro ds.
    apply deref_same_binding; try assumption.
    unfold renv_idempotent in *. rewrite <- (same_bindings_same_domain Hsame).
    now rewrite <- (fv_env_same_bindings fv He1 He2 Hsame).
  }
  destruct (@replay_run_same_store _ _ (config_mk t fs (h & H) (e & E) L) n Htrace')
    as [D' [Hrun Hresult]].
  - change (raw_store_agreement (config_mk t fs (H & h) (E & e) L)
      (config_mk t fs (h & H) (e & E) L)). agreement_split.
  - exists L', D'. auto.
Qed.

Local Definition let_focus (s u : trm) (fs : stack) (h : heap) (e : renv) (L : vars) :=
  config_mk s stack_nil h e (fv_config (config_mk (trm_let s u) fs h e L)).

Local Lemma let_focus_covers_saved_frame s u fs h e L :
  fv (stack_cons (frame_let u) fs) \c fv_config (let_focus s u fs h e L).
Proof.
  intros x Hx.
  change (x \in fv u \u fv fs) in Hx. rewrite in_union in Hx.
  unfold let_focus.
  change (x \in fv s \u fv stack_nil \u fv_heap h \u fv_renv e \u
    ((fv s \u fv u) \u fv fs \u fv_heap h \u fv_renv e \u L)).
  repeat rewrite in_union. destruct Hx; auto 12.
Qed.

Local Lemma raw_let_from_focus_run s u fs h e L n w h' e' L' :
  let_focus s u fs h e L ⊣n↦* config_mk (trm_var (avar_f w)) stack_nil h' e' L' ->
  exists L'',
    config_mk (trm_let s u) fs h e L ⊣(S (S n))↦*
    config_mk (open w u) fs h' e' L''.
Proof.
  intro Hbody.
  pose proof (@replay_run_under_stack (stack_cons (frame_let u) fs)
    (let_focus s u fs h e L) (config_mk (trm_var (avar_f w)) stack_nil h' e' L') n
    (@let_focus_covers_saved_frame s u fs h e L) Hbody) as Hframed.
  eexists. eapply raw_cons_step.
  - apply red_let_push.
  - eapply red_trans; [exact Hframed | apply red_let_var].
Qed.

Local Lemma terminating_let_splits s u fs h e L n E :
  config_mk (trm_let s u) fs h e L ⊣n↦* E ->
  answer E ->
  exists k rest w h' e' L' L'',
    n = S (S (k + rest)) /\
    let_focus s u fs h e L ⊣k↦* config_mk (trm_var (avar_f w)) stack_nil h' e' L' /\
    config_mk (open w u) fs h' e' L'' ⊣rest↦* E.
Proof.
  intros Hrun Hanswer. destruct n as [|n].
  - apply first_raw_step in Hrun. subst E. inversion Hanswer.
  - destruct (first_raw_step Hrun) as [first [Hstep Hrest]].
    assert (Hfirst : first = attach_stack (stack_cons (frame_let u) fs) (let_focus s u fs h e L))
      by (inversion Hstep; subst; reflexivity).
    subst first.
    destruct (@terminating_run_splits_at_frame (stack_cons (frame_let u) fs)
      n (let_focus s u fs h e L) E
      (@let_focus_covers_saved_frame s u fs h e L) Hrest Hanswer)
      as [k [m [A [Hbudget [Hbody [Hdone Hback]]]]]].
    destruct Hdone as [w h' e' L']. destruct m as [|m].
    + apply first_raw_step in Hback. subst E.
      cbn [attach_stack stack_append] in Hanswer. inversion Hanswer.
    + destruct (first_raw_step Hback) as [next [Hpop Htail]].
      cbn [attach_stack stack_append] in Hpop.
      inversion Hpop; subst.
      exists k, m, w, h', e', L'. eexists.
      split; [lia |]. split; eassumption.
Qed.

Local Lemma same_bindings_compose {A : Type} (e f g : env A) :
  same_bindings e f -> same_bindings f g -> same_bindings e g.
Proof. intros Hef Hfg x v. transitivity (binds x v f); auto. Qed.

Local Lemma same_bindings_concat {A : Type} (e1 e2 f1 f2 : env A) :
  same_bindings e1 e2 -> same_bindings f1 f2 ->
  same_bindings (e1 & f1) (e2 & f2).
Proof.
  intros He Hf x v. split; intro H; apply binds_concat_inv in H;
    destruct H as [Hb | [Hfresh Hb]].
  - apply binds_concat_right. now apply Hf.
  - apply binds_concat_left; [now apply He |].
    now rewrite <- (same_bindings_same_domain Hf).
  - apply binds_concat_right. now apply Hf.
  - apply binds_concat_left; [now apply He |].
    now rewrite (same_bindings_same_domain Hf).
Qed.

Local Lemma bindings_exchange_independent_fragments {A : Type} (base f1 f2 : env A) :
  (forall x, x \in dom f1 -> x # base) ->
  (forall x, x \in dom f2 -> x # base) ->
  (forall x, x \in dom f2 -> x # f1) ->
  same_bindings (f1 & (base & f2)) (f2 & (base & f1)).
Proof.
  intros H1 H2 H12.
  assert (Hdisj : forall (e f : env A),
      (forall x, x \in dom f -> x # e) -> disjoint (dom e) (dom f)).
  {
    intros e f Hsep. unfold disjoint. apply fset_extens; intros x Hx.
    - rewrite in_inter in Hx. destruct Hx as [Hex Hfx].
      exfalso. exact (Hsep x Hfx Hex).
    - rewrite in_empty in Hx. contradiction.
  }
  assert (Hleft : same_bindings (f1 & (base & f2)) (base & (f1 & f2))).
  {
    rewrite !concat_assoc. apply same_bindings_concat; [|firstorder].
    apply same_bindings_concat_commute, disjoint_comm. now apply Hdisj.
  }
  assert (Hright : same_bindings (base & (f2 & f1)) (f2 & (base & f1))).
  {
    rewrite !concat_assoc. apply same_bindings_concat; [|firstorder].
    apply same_bindings_concat_commute. now apply Hdisj.
  }
  eapply same_bindings_compose; [exact Hleft |].
  eapply same_bindings_compose; [|exact Hright].
  apply same_bindings_concat; [firstorder |].
  apply same_bindings_concat_commute. now apply Hdisj.
Qed.

Local Definition independent_extension_for H E L C D :=
  (forall x, x \in fv_config D -> x # H) /\
  (forall x, x \in fv_config D -> x # E) /\
  (forall x, x \in fv_config D -> x \notin fv_config C ->
    x \notin extension_variables H E) /\
  L \c fv_config C \u extension_variables H E.

Local Lemma independent_returning_runs_commute ta tb h e La Lb La' Lb'
    Ha Hb Ea Eb wa wb na nb Lab Lba :
  ok h -> ok e -> ok Ha -> ok Hb -> ok Ea -> ok Eb ->
  renv_idempotent (Ea & e) -> renv_idempotent (Eb & e) ->
  let A := config_mk ta stack_nil h e La in
  let B := config_mk tb stack_nil h e Lb in
  let A' := config_mk (trm_var (avar_f wa)) stack_nil (h & Ha) (e & Ea) La' in
  let B' := config_mk (trm_var (avar_f wb)) stack_nil (h & Hb) (e & Eb) Lb' in
  A ⊣na↦* A' ->
  B ⊣nb↦* B' ->
  independent_extension_for Ha Ea Lab B B' ->
  independent_extension_for Hb Eb Lba A A' ->
  exists h_ab h_ba e_ab e_ba L_ab L_ba,
    (config_mk tb stack_nil (h & Ha) (e & Ea) Lab) ⊣nb↦*
      config_mk (trm_var (avar_f wb)) stack_nil h_ab e_ab L_ab /\
    (config_mk ta stack_nil (h & Hb) (e & Eb) Lba) ⊣na↦*
      config_mk (trm_var (avar_f wa)) stack_nil h_ba e_ba L_ba /\
    same_bindings h_ab h_ba /\ same_bindings e_ab e_ba.
Proof.
  intros Hokh Hoke HokHa HokHb HokEa HokEb HidemA HidemB.
  cbv zeta. intros HrunA HrunB [Hhab [Heab [Hnewab HLab]]]
    [Hhba [Heba [Hnewba HLba]]].
  destruct (@replay_after_independent_allocation tb stack_nil h e Lb Ha Ea Lab _ nb
     Hokh Hoke HokHa HokEa HidemA HrunB Hhab Heab Hnewab HLab)
    as [Lblend [Cab [HrunAB HstoreAB]]].
  destruct (@replay_after_independent_allocation ta stack_nil h e La Hb Eb Lba _ na
     Hokh Hoke HokHb HokEb HidemB HrunA Hhba Heba Hnewba HLba)
    as [Lalen [Cba [HrunBA HstoreBA]]].
  destruct Cab as [tab sab hab eab Lab'].
  destruct Cba as [tba sba hba eba Lba'].
  cbn [extend_machine raw_store_agreement] in HstoreAB, HstoreBA.
  destruct HstoreAB as [<- [<- [<- [[_ [_ HHab]] [[_ [_ HEab]] _]]]]].
  destruct HstoreBA as [<- [<- [<- [[_ [_ HHba]] [[_ [_ HEba]] _]]]]].
  exists hab, hba, eab, eba, Lblend, Lalen.
  split; [exact HrunAB |]. split; [exact HrunBA |]. split.
  - eapply same_bindings_compose; [intros x v; symmetry; exact (HHab x v) |].
    eapply same_bindings_compose; [|exact HHba].
    apply bindings_exchange_independent_fragments; intros x Hx.
    + intro Hxbase. eapply Hhab; [|exact Hx].
      apply dom_heap_in_machine_fv. rewrite dom_concat, in_union. now left.
    + intro Hxbase. eapply Hhba; [|exact Hx].
      apply dom_heap_in_machine_fv. rewrite dom_concat, in_union. now left.
    + apply Hhab. apply dom_heap_in_machine_fv.
      rewrite dom_concat, in_union. now right.
  - eapply same_bindings_compose; [intros x v; symmetry; exact (HEab x v) |].
    eapply same_bindings_compose; [|exact HEba].
    apply bindings_exchange_independent_fragments; intros x Hx.
    + intro Hxbase. eapply Heab; [|exact Hx].
      apply dom_env_in_machine_fv. rewrite dom_concat, in_union. now left.
    + intro Hxbase. eapply Heba; [|exact Hx].
      apply dom_env_in_machine_fv. rewrite dom_concat, in_union. now left.
    + apply Heab. apply dom_env_in_machine_fv.
      rewrite dom_concat, in_union. now right.
Qed.

Local Lemma close_open_to_return_name k y w (t : trm) :
  open_rec k w (close_rec k y t) =
  rename (subst_fvar y w) (open_rec k w t).
Proof.
  assert (H : forall (a : avar) d,
    open_rec (k + d) w (close_depth_rec k y a d) =
    avar_map (subst_fvar y w) (open_rec (k + d) w a) d).
  {
    intros [i | x] d;
      unfold close_depth_rec, avar_map, rename_avar, subst_fvar,
        close_rec, open_rec, AvarOpenable, AvarClosing;
      cbn; repeat case_if; congruence.
  }
  pose proof (proj1 (@open_transform_terms k w _ _ H) t 0) as Heq.
  rewrite Nat.add_0_r in Heq. exact Heq.
Qed.

Local Lemma name_maps_commute_on_types f g :
  (forall x, f (g x) = g (f x)) ->
  (forall T d, transform_typ (avar_map f) (transform_typ (avar_map g) T d) d =
               transform_typ (avar_map g) (transform_typ (avar_map f) T d) d) /\
  (forall D d, transform_dec (avar_map f) (transform_dec (avar_map g) D d) d =
               transform_dec (avar_map g) (transform_dec (avar_map f) D d) d).
Proof.
  intro Hcomm. apply typ_mutind; intros; cbn [transform_typ transform_dec];
    try reflexivity; f_equal; auto.
  all: unfold avar_map; match goal with
    | |- context [rename_avar _ (rename_avar _ ?v)] => destruct v; cbn; now rewrite ?Hcomm
    end.
Qed.

Local Lemma name_maps_commute_on_terms f g :
  (forall x, f (g x) = g (f x)) ->
  (forall t d, transform_trm (avar_map f) (transform_trm (avar_map g) t d) d =
               transform_trm (avar_map g) (transform_trm (avar_map f) t d) d) /\
  (forall l d, transform_lit (avar_map f) (transform_lit (avar_map g) l d) d =
               transform_lit (avar_map g) (transform_lit (avar_map f) l d) d) /\
  (forall a d, transform_def (avar_map f) (transform_def (avar_map g) a d) d =
               transform_def (avar_map g) (transform_def (avar_map f) a d) d) /\
  (forall ds d, transform_defs (avar_map f) (transform_defs (avar_map g) ds d) d =
                transform_defs (avar_map g) (transform_defs (avar_map f) ds d) d).
Proof.
  intro Hcomm. destruct (name_maps_commute_on_types f g Hcomm) as [HT HD].
  apply trm_mutind; intros;
    cbn [transform_trm transform_lit transform_def transform_defs];
    try reflexivity; f_equal; auto.
  all: unfold avar_map; match goal with
    | |- context [rename_avar _ (rename_avar _ ?v)] => destruct v; cbn; now rewrite ?Hcomm
    end.
Qed.

Local Lemma distinct_substitutions_commute y1 y2 w1 w2 :
  y1 <> y2 -> w1 <> y2 -> w2 <> y1 ->
  forall x,
    subst_fvar y1 w1 (subst_fvar y2 w2 x) =
    subst_fvar y2 w2 (subst_fvar y1 w1 x).
Proof. intros. unfold subst_fvar. repeat case_if; congruence. Qed.

Local Lemma swapped_result_continuations_match (t : trm) y1 y2 w1 w2 :
  closed t ->
  y1 <> y2 -> w1 <> y2 -> w2 <> y1 ->
  open w2 (open_rec 1 w1 (close_rec 1 y1 (close y2 t))) =
  open w1 (open_rec 1 w2 (close_rec 1 y2 (close y1 t))).
Proof.
  intros Hclosed Hdistinct Hw1 Hw2.
  rewrite (@close_open_to_return_name 1 y1 w1 (close y2 t)).
  rewrite (@close_open_to_return_name 1 y2 w2 (close y1 t)).
  rewrite !close_open_other_trm by (congruence || lia).
  rewrite !Hclosed.
  assert (H1 : subst_fvar y1 w1 w2 = w2)
    by (unfold subst_fvar; case_if; congruence).
  assert (H2 : subst_fvar y2 w2 w1 = w1)
    by (unfold subst_fvar; case_if; congruence).
  replace (open w2 (rename (subst_fvar y1 w1) (close y2 t)))
    with (rename (subst_fvar y1 w1) (open w2 (close y2 t)))
    by (rewrite rename_open_trm, H1; reflexivity).
  replace (open w1 (rename (subst_fvar y2 w2) (close y1 t)))
    with (rename (subst_fvar y2 w2) (open w1 (close y1 t)))
    by (rewrite rename_open_trm, H2; reflexivity).
  rewrite !close_open_to_return_name, !Hclosed.
  apply (proj1 (name_maps_commute_on_terms _ _ (@distinct_substitutions_commute y1 y2 w1 w2 Hdistinct Hw1 Hw2))).
Qed.

(* A call that writes only to fresh locations preserves every original heap binding. *)

Local Definition preserves_bindings {A : Type} (e f : env A) :=
  forall x v, binds x v e -> binds x v f.

Local Lemma binding_fragment {A : Type} (e : env A) (excluded : vars) :
  ok e -> exists fragment : env A,
    ok fragment /\
    (forall x v, binds x v fragment <-> binds x v e /\ x \notin excluded).
Proof.
  intro Hok. induction Hok as [|e x v Hok IH Hfresh].
  - exists (@empty A). split; [constructor |].
    intros y w. split; [intro Hb | intros [Hb _]];
      exfalso; eapply binds_empty_inv; eassumption.
  - destruct IH as [f [Hokf Hf]].
    destruct (classic (x \in excluded)) as [Hex | Hex].
    + exists f. split; [exact Hokf |].
      intros y w. rewrite Hf. split.
      * intros [Hb Hout]. split; [apply binds_push_neq; [exact Hb | congruence] | exact Hout].
      * intros [Hb Hout]. split; [|exact Hout].
        apply binds_push_inv in Hb as [[-> _] | [_ Hb]]; [contradiction | exact Hb].
    + exists (f & x ~ v). split.
      * apply ok_push; [exact Hokf |].
        intro Hx. destruct (get_some Hx) as [z Hz].
        apply Hf in Hz as [Hb _]. eapply binds_fresh_inv; eassumption.
      * intros y w. split.
        -- intro Hb. apply binds_push_inv in Hb as [[-> ->] | [Hneq Hb]].
           ++ split; [apply binds_push_eq | exact Hex].
           ++ apply Hf in Hb as [Hb Hout]. split; [now apply binds_push_neq | exact Hout].
        -- intros [Hb Hout]. apply binds_push_inv in Hb as [[-> ->] | [Hneq Hb]].
           ++ apply binds_push_eq.
           ++ apply binds_push_neq; [apply Hf; auto | exact Hneq].
Qed.

Local Lemma preserved_bindings_split {A : Type} (e f : env A) :
  ok e -> ok f -> preserves_bindings e f ->
  exists fragment : env A,
    ok fragment /\ same_valid_bindings (e & fragment) f /\
    (forall x, x \in dom fragment -> x # e).
Proof.
  intros Hoke Hokf Hpres.
  destruct (binding_fragment (dom e) Hokf) as [fragment [Hfragment Hfilter]].
  assert (Hsep : forall x, x \in dom fragment -> x # e).
  {
    intros x Hx. destruct (get_some Hx) as [v Hv].
    exact (proj2 (proj1 (Hfilter x v) Hv)).
  }
  exists fragment. split; [exact Hfragment |]. split; [|exact Hsep].
  split; [now apply replay_ok_concat |]. split; [exact Hokf |].
  intros x v. split.
  - intro Hb. apply binds_concat_inv in Hb as [Hb | [_ Hb]].
    + exact (proj1 (proj1 (Hfilter x v) Hb)).
    + now apply Hpres.
  - intro Hb. destruct (classic (x \in dom e)) as [Hx | Hx].
    + destruct (get_some Hx) as [v' Hv'].
      assert (v = v') by (eapply binds_functional; [exact Hb | now apply Hpres]).
      subst v'. apply binds_concat_left; [exact Hv' |].
      intro Hx'. exact (Hsep x Hx' Hx).
    + apply binds_concat_right. apply Hfilter. auto.
Qed.

Local Definition permits_writes_only_outside (base : heap) (C : config) : Prop :=
  match C with
  | config_mk (trm_write (avar_f w) _ _) _ _ e _ =>
      forall y, binds w y e -> y # base
  | _ => True
  end.

Local Lemma raw_step_preserves_base_heap base C D :
  red C D -> permits_writes_only_outside base C ->
  ok (config_heap C) -> preserves_bindings base (config_heap C) ->
  ok (config_heap D) /\ preserves_bindings base (config_heap D).
Proof.
  intros Hstep Hwrites Hok Hbase. destruct Hstep;
    cbn [config_heap permits_writes_only_outside] in *; try solve [auto].
  - match goal with H : heap_update _ _ _ _ _ |- _ =>
      destruct H as [_ [Hok' [_ [Hkeep _]]]]
    end.
    split; [exact Hok' |]. intros x v Hv.
    eapply Hkeep; [|now apply Hbase].
    intro Heq; subst x. eapply binds_fresh_inv; [exact Hv | now apply Hwrites].
  - assert (Hfresh : y # Sigma).
    { intro Hy. eapply fresh_vars_notin; [exact H | |].
      - rewrite !from_list_cons, from_list_nil, union_empty_r, in_union, in_singleton.
        now left.
      - now apply dom_heap_in_machine_fv. }
    split; [now apply ok_push |].
    intros x v Hv. apply binds_push_neq; [now apply Hbase |].
    intro Heq; subst x. eapply binds_fresh_inv; [exact (Hbase _ _ Hv) | exact Hfresh].
  - assert (Hfresh : y # Sigma).
    { intro Hy. eapply fresh_vars_notin; [exact H | |].
      - rewrite !from_list_cons, from_list_nil, union_empty_r, in_union, in_singleton.
        now left.
      - now apply dom_heap_in_machine_fv. }
    split; [now apply ok_push |].
    intros x v Hv. apply binds_push_neq; [now apply Hbase |].
    intro Heq; subst x. eapply binds_fresh_inv; [exact (Hbase _ _ Hv) | exact Hfresh].
Qed.

Inductive raw_steps_outside_heap (base : heap) : config -> nat -> config -> Prop :=
| raw_steps_outside_heap_refl C :
    raw_steps_outside_heap base C 0 C
| raw_steps_outside_heap_step C D E n :
    raw_steps_outside_heap base C n D ->
    permits_writes_only_outside base D ->
    red D E ->
    raw_steps_outside_heap base C (S n) E.

Local Lemma raw_steps_preserve_base_heap base C D n :
  raw_steps_outside_heap base C n D ->
  ok (config_heap C) -> preserves_bindings base (config_heap C) ->
  ok (config_heap D) /\ preserves_bindings base (config_heap D).
Proof.
  intros Hrun Hok Hbase. induction Hrun as [C | C D E n Hrun IH Houtside Hstep].
  - auto.
  - destruct (IH Hok Hbase) as [HokD HD].
    eapply raw_step_preserves_base_heap; eassumption.
Qed.

Local Lemma raw_steps_outside_heap_extend C D n :
  ok (config_heap C) ->
  raw_steps_outside_heap (config_heap C) C n D ->
  exists fragment : heap,
    ok fragment /\ same_valid_bindings (config_heap C & fragment) (config_heap D) /\
    (forall x, x \in dom fragment -> x # config_heap C).
Proof.
  intros Hok Hrun.
  pose proof (raw_steps_preserve_base_heap Hrun Hok (fun _ _ H => H)) as [HokD Hkeep].
  eapply preserved_bindings_split; eassumption.
Qed.

Local Lemma raw_step_renv_extends C D :
  red C D -> exists E, config_env D = config_env C & E.
Proof.
  intros Hstep. destruct Hstep; cbn [config_env].
  all: try solve [eexists; reflexivity].
  all: exists (@empty var); rewrite concat_empty_r; reflexivity.
Qed.

Local Lemma raw_steps_renv_extends C D n :
  C ⊣n↦* D -> exists E, config_env D = config_env C & E.
Proof.
  intro Hrun. induction Hrun as [C | C D E n Hrun [F HF] Hstep].
  - exists (@empty var). now rewrite concat_empty_r.
  - destruct (raw_step_renv_extends Hstep) as [F' HF'].
    exists (F & F'). rewrite HF', HF, concat_assoc. reflexivity.
Qed.


(* Typing transport when a binding is specialized to a subtype. *)

Local Definition ctx_typing_morphism mode e G G' :=
  ctx_dom G = ctx_dom G' /\
  (forall x T, ctx_binds x T G -> ty_var mode G' objctx_empty e x T) /\
  (forall x, ctx_vis G x -> ctx_vis G' x).

Local Definition bindings_extend G G' :=
  (forall x T, ctx_binds x T G -> ctx_binds x T G') /\ True.

Local Lemma bindings_extend_push G G' x vk T :
  bindings_extend G G' -> bindings_extend (G § x / vk ~ T) (G' § x / vk ~ T).
Proof.
  intros [HG _]. split; [|trivial].
  intros u U Hb. inversion Hb; subst; eauto using ctx_binds.
Qed.

Local Lemma types_under_binding_extension mode :
  (forall G Go e x T, ty_var mode G Go e x T ->
    forall G', bindings_extend G G' -> ty_var mode G' Go e x T) /\
  (forall G Go e S T, subtyp mode G Go e S T ->
    forall G', bindings_extend G G' -> subtyp mode G' Go e S T) /\
  (forall G Go e S T, ty_incap mode G Go e S T ->
    forall G', bindings_extend G G' -> ty_incap mode G' Go e S T).
Proof.
  apply (@ts_mutind mode
    (fun G Go e x T _ => forall G', bindings_extend G G' -> ty_var mode G' Go e x T)
    (fun G Go e S T _ => forall G', bindings_extend G G' -> subtyp mode G' Go e S T)
    (fun G Go e S T _ => forall G', bindings_extend G G' -> ty_incap mode G' Go e S T)).
  all: intros; match goal with H : bindings_extend _ _ |- _ =>
    let Hb := fresh "Hbindings" in pose proof (proj1 H) as Hb
    end.
  all: solve [econstructor; unfold obj_typing, subtyping, obj_ref_incap in *;
    intros; solve [eauto 7 using bindings_extend_push]].
Qed.

Local Lemma ctx_typing_morphism_hide mode e G G' :
  ctx_typing_morphism mode e G G' ->
  ctx_typing_morphism mode e (ctx_hide G) (ctx_hide G').
Proof.
  intros [HD [HB HV]]. split; [exact HD |]. split.
  - intros x T Hb. inversion Hb; subst.
    eapply (proj1 (types_under_binding_extension mode)).
    + apply HB; eassumption.
    + split; [|trivial]. intros y U H. now apply ctx_binds_hide.
  - intros x H. inversion H.
Qed.

Local Lemma ctx_typing_morphism_push mode e G G' x vk T :
  ctx_typing_morphism mode e G G' ->
  x \notin ctx_dom G ->
  ctx_typing_morphism mode e (G § x / vk ~ T) (G' § x / vk ~ T).
Proof.
  intros [Hd [Hb Hv]] Hx.
  rewrite Hd in Hx.
  split; [cbn; now rewrite Hd |]. split.
  - intros u U Hu. inversion Hu; subst.
    + apply ty_var_var, ctx_binds_e.
    + eapply (proj1 (types_under_binding_extension mode)).
      * apply Hb; eassumption.
      * split; [exact (proj1 (@ctx_extends_with_fresh G' x vk T Hx)) | trivial].
  - intros u Hu. inversion Hu; subst; eauto using ctx_vis.
Qed.

Local Lemma ctx_types_under_morphism mode :
  (forall G Go e x T, ty_var mode G Go e x T ->
    forall G', ctx_typing_morphism mode e G G' -> ty_var mode G' Go e x T) /\
  (forall G Go e S T, subtyp mode G Go e S T ->
    forall G', ctx_typing_morphism mode e G G' -> subtyp mode G' Go e S T) /\
  (forall G Go e S T, ty_incap mode G Go e S T ->
    forall G', ctx_typing_morphism mode e G G' -> ty_incap mode G' Go e S T).
Proof.
  apply (@ts_mutind mode
    (fun G Go e x T _ => forall G', ctx_typing_morphism mode e G G' -> ty_var mode G' Go e x T)
    (fun G Go e S T _ => forall G', ctx_typing_morphism mode e G G' -> subtyp mode G' Go e S T)
    (fun G Go e S T _ => forall G', ctx_typing_morphism mode e G G' -> ty_incap mode G' Go e S T)).
  all: intros.
  1: match goal with HM : ctx_typing_morphism _ _ _ _ |- _ => apply (proj1 (proj2 HM)); assumption end.
  all: try solve [econstructor; unfold obj_typing, subtyping, obj_ref_incap in *; eauto 3].
  all: match goal with HM : ctx_typing_morphism _ _ ?G ?G' |- _ =>
    match goal with
    | |- subtyp _ _ _ _ (typ_fun _ _) (typ_fun _ _) =>
        eapply subtyp_fun with (L := L \u ctx_dom G)
    | |- subtyp _ _ _ _ (typ_rcd (dec_met _ _ _ _)) (typ_rcd (dec_met _ _ _ _)) =>
        eapply subtyp_met with (L := L \u ctx_dom G)
    end
    end.
  all: unfold subtyping in *; try solve [eauto 3].
  all: intros; repeat match goal with H : _ \notin ?Ls \u ctx_dom _ |- _ =>
    apply notin_union in H as [? ?] end.
  all: try solve [eauto using ctx_typing_morphism_push].
  match goal with
  | HM : ctx_typing_morphism _ _ ?G _,
    H1 : ?x \notin ctx_dom ?G, H2 : ?y \notin ctx_dom ?G, Hneq : ?y <> ?x |- _ =>
    assert (Hy : y \notin ctx_dom (G § x / v_par ~ TZ2)) by
      (change (y \notin \{ x } \u ctx_dom G); rewrite notin_union, notin_singleton; auto)
  end.
  eauto 10 using ctx_typing_morphism_push.
Qed.

Local Lemma ctx_cap_bound_under_morphism mode C G Go e S T :
  ty_capbnd mode C G Go e S T ->
  forall G', ctx_typing_morphism mode e G G' -> ty_capbnd mode C G' Go e S T.
Proof.
  destruct (ctx_types_under_morphism mode) as [Hvar _].
  intro H. induction H; intros G' HM;
    solve [econstructor; unfold obj_typing, obj_cap_bnd in *; eauto].
Qed.

Local Lemma ctx_viewpoint_under_morphism mode x G Go e S T :
  viewpoint_adapt mode x G Go e S T ->
  forall G', ctx_typing_morphism mode e G G' -> viewpoint_adapt mode x G' Go e S T.
Proof.
  destruct (ctx_types_under_morphism mode) as [_ [_ Hincap]].
  unfold viewpoint_adapt. destruct (mode_viewpoint_adaptation' mode); auto.
  intros H G' HM. destruct H.
  constructor; unfold obj_ref_incap, obj_cap_bnd in *.
  - eauto.
  - eapply ctx_cap_bound_under_morphism; eassumption.
Qed.

Local Definition objctx_self_fresh G Go :=
  forall x, x \in objctx_dom Go -> x \notin ctx_dom G.

Local Lemma objctx_self_fresh_empty G : objctx_self_fresh G objctx_empty.
Proof. intros x Hx. cbn [objctx_dom] in Hx. rewrite in_empty in Hx. contradiction. Qed.

Local Lemma objctx_self_fresh_lit G x T :
  x \notin ctx_dom G -> objctx_self_fresh G (objctx_lit x T).
Proof.
  intros Hx y Hy. cbn [objctx_dom] in Hy. rewrite in_singleton in Hy. now subst y.
Qed.

Local Lemma ctx_typing_morphism_object mode e G G' Go :
  ctx_typing_morphism mode e G G' ->
  objctx_self_fresh G Go ->
  ctx_typing_morphism mode e (G §§& Go) (G' §§& Go).
Proof.
  destruct Go; cbn [ctx_obj]; auto.
  intros H HM. apply ctx_typing_morphism_push; [exact H |].
  apply HM. cbn [objctx_dom]. now rewrite in_singleton.
Qed.

Local Lemma ctx_typing_morphism_for_method mode e G G' Go z TZ c TC :
  ctx_typing_morphism mode e G G' ->
  objctx_self_fresh G Go ->
  z \notin (objctx_dom Go \u ctx_dom G) ->
  c \notin (objctx_dom Go \u ctx_dom G) ->
  c <> z ->
  ctx_typing_morphism mode e
    (ctx_obj_met mode G Go z TZ c TC) (ctx_obj_met mode G' Go z TZ c TC).
Proof.
  intros HM Hself Hz Hc Hneq.
  pose proof (ctx_typing_morphism_object HM Hself) as HMself.
  destruct Go; destruct (mode_visibility' mode) eqn:Hvis;
    cbn [ctx_obj_met] in *; rewrite Hvis.
  all: apply ctx_typing_morphism_push; [| idtac].
  all: try solve [cbn [ctx_dom objctx_dom] in *;
    rewrite ?union_empty_l, ?notin_union, ?notin_singleton in *; tauto].
  all: apply ctx_typing_morphism_push; [try apply ctx_typing_morphism_hide; exact HMself |].
  all: cbn [ctx_dom objctx_dom] in *;
    rewrite ?union_empty_l, ?notin_union, ?notin_singleton in *; tauto.
Qed.

Local Lemma ctx_terms_under_morphism mode :
  (forall G Go e t T, ty_trm mode G Go e t T ->
    forall G', ctx_typing_morphism mode e G G' ->
      objctx_self_fresh G Go -> ty_trm mode G' Go e t T) /\
  (forall G Go e l T, ty_lit mode G Go e l T ->
    forall G', ctx_typing_morphism mode e G G' ->
      objctx_self_fresh G Go -> ty_lit mode G' Go e l T) /\
  (forall G Go e d D, ty_def mode G Go e d D ->
    forall G', ctx_typing_morphism mode e G G' ->
      objctx_self_fresh G Go -> ty_def mode G' Go e d D) /\
  (forall G Go e ds T, ty_defs mode G Go e ds T ->
    forall G', ctx_typing_morphism mode e G G' ->
      objctx_self_fresh G Go -> ty_defs mode G' Go e ds T).
Proof.
  destruct (ctx_types_under_morphism mode) as [Hvar [Hsub Hincap]].
  apply (@rules_mutind mode
    (fun G Go e t T _ => forall G', ctx_typing_morphism mode e G G' ->
      objctx_self_fresh G Go -> ty_trm mode G' Go e t T)
    (fun G Go e l T _ => forall G', ctx_typing_morphism mode e G G' ->
      objctx_self_fresh G Go -> ty_lit mode G' Go e l T)
    (fun G Go e d D _ => forall G', ctx_typing_morphism mode e G G' ->
      objctx_self_fresh G Go -> ty_def mode G' Go e d D)
    (fun G Go e ds T _ => forall G', ctx_typing_morphism mode e G G' ->
      objctx_self_fresh G Go -> ty_defs mode G' Go e ds T)).
  all: intros; unfold obj_typing, obj_dec_typing, subtyping, obj_ref_incap in *.
  all: match goal with HM : ctx_typing_morphism _ _ _ _ |- _ =>
    let Hv := fresh "Hvisible" in pose proof (proj2 (proj2 HM)) as Hv
    end.
  all: try solve [econstructor; unfold obj_typing, obj_dec_typing, subtyping, obj_ref_incap in *;
    intros; eauto 5 using ctx_viewpoint_under_morphism].
  all: match goal with HM : ctx_typing_morphism _ _ ?G _ |- _ =>
    match goal with
    | |- ty_trm _ _ _ _ (trm_let _ _) _ =>
      eapply ty_trm_let with (L := L \u ctx_dom G)
    | |- ty_trm _ _ _ _ (trm_lit _ _) _ =>
      eapply ty_trm_lit with (L := L \u ctx_dom G)
    | |- ty_lit _ _ _ _ (lit_fun _ _) _ =>
      eapply ty_lit_fun with (L := L \u ctx_dom G)
    | |- ty_lit _ _ _ _ (lit_obj _ _) _ =>
      eapply ty_lit_obj with (L := L \u ctx_dom G)
    | |- ty_def _ _ ?Go _ (def_met _ _) _ =>
      eapply ty_def_met with (L := L \u (objctx_dom Go \u ctx_dom G))
    | |- ty_def _ _ ?Go _ (def_fld _ _) _ =>
      let Hm := fresh "Hobject" in
      assert (Hm : ctx_typing_morphism mode e (G §§& Go) (G' §§& Go))
        by (apply ctx_typing_morphism_object; assumption);
      apply ty_def_fld; unfold obj_typing; [intros; apply (proj2 (proj2 Hm)) | eapply Hvar]; eauto
    end end.
  all: unfold obj_typing, obj_dec_typing in *; try solve [eauto].
  all: intros; repeat match goal with H : _ \notin ?Ls \u ctx_dom _ |- _ =>
    apply notin_union in H as [? ?] end.
  all: try solve [eauto 6 using ctx_typing_morphism_push,
    objctx_self_fresh_empty, objctx_self_fresh_lit].
  eauto 7 using ctx_typing_morphism_for_method, objctx_self_fresh_empty, notin_union.
Qed.

Local Lemma specialize_last_binding mode G e x vk S U :
  x \notin ctx_dom G ->
  subtyp mode G objctx_empty e S U ->
  ctx_typing_morphism mode e (G § x / vk ~ U) (G § x / vk ~ S).
Proof.
  intros Hx Hsub. split; [reflexivity |]. split.
  - intros y T Hb. inversion Hb; subst.
    + eapply ty_var_sub with (T := S).
      * apply ty_var_var, ctx_binds_e.
      * unfold subtyping.
        eapply (proj1 (proj2 (ctx_extends_types mode))); [exact Hsub |].
        now apply ctx_extends_with_fresh.
    + apply ty_var_var. apply ctx_binds_n; assumption.
  - intros y Hy. inversion Hy; subst; eauto using ctx_vis.
Qed.

Local Lemma stack_narrow_input mode G e fs S U T :
  @ty_stack mode G e U fs T ->
  subtyp mode G objctx_empty e S U ->
  @ty_stack mode G e S fs T.
Proof.
  intros Hstack Hsub. destruct Hstack as [G e U T Hout | L G e fs u U V T Htail Hbody].
  - apply ty_stack_nil. unfold subtyping in *.
    eapply subtyp_trans; eassumption.
  - apply ty_stack_let with (L := L \u ctx_dom G) (T := V); [exact Htail |].
    intros x Hx. apply notin_union in Hx as [HxL HxG].
    eapply (proj1 (ctx_terms_under_morphism mode)).
    + exact (Hbody x HxL).
    + now apply specialize_last_binding.
    + apply objctx_self_fresh_empty.
Qed.

Local Lemma invert_read_type mode G e w a U :
  ty_trm mode G objctx_empty e (trm_read (avar_f w) a) U ->
  exists W R V,
    ty_var mode G objctx_empty e w (typ_rcd (dec_fld a W R)) /\
    viewpoint_adapt mode w G objctx_empty e R V /\
    subtyp mode G objctx_empty e V U.
Proof.
  intro H. remember (trm_read (avar_f w) a) as t eqn:Ht.
  induction H; try discriminate; unfold obj_typing, subtyping in *.
  - inversion Ht; subst. exists S, T, U. split; [assumption |]. split; [assumption | apply subtyp_refl].
  - destruct (IHty_trm Ht) as [W [R [V [Hfield [Hview Hsub]]]]].
    exists W, R, V. repeat split; try assumption. eapply subtyp_trans; eassumption.
Qed.

Local Lemma read_continuation_type mode G e w a U T fs :
  ty_trm mode G objctx_empty e (trm_read (avar_f w) a) U ->
  @ty_stack mode G e U fs T ->
  mode_has_mutability mode ->
  exists W R TS TC,
    ty_var mode G objctx_empty e w (typ_rcd (dec_fld a W R)) /\
    ty_incap mode G objctx_empty e R TS /\
    ty_capbnd mode typ_refcap_mutability G objctx_empty e R TC /\
    @ty_stack mode G e (rodot_read_term_type TS w TC) fs T.
Proof.
  intros Hread Hstack Hmut.
  destruct (invert_read_type Hread) as [W [R [V [Hfield [Hview Hsub]]]]].
  unfold viewpoint_adapt in Hview.
  assert (Hmode : mode_viewpoint_adaptation' mode = mode_viewpoint_adapt_mutability)
    by (destruct mode; simpl in *; congruence).
  rewrite Hmode in Hview. inversion Hview as [C1 x G1 Go e1 R' TS TC Hic Hcap]; subst.
  exists W, R, TS, TC. unfold obj_ref_incap, obj_cap_bnd in *. repeat split; try assumption.
  eapply stack_narrow_input; eassumption.
Qed.

Require Import RecordTypes.

Local Lemma definition_label_matches_typing mode G Go e d D :
  ty_def mode G Go e d D -> label_of d = label_of D.
Proof. intro H. destruct H; reflexivity. Qed.

Local Lemma typed_record_member_exists mode G Go e ds T D :
  ty_defs mode G Go e ds T -> record_has T D ->
  exists d, label_of d = label_of D /\ defs_has ds d.
Proof.
  intros Hdefs Hrec. induction Hdefs as [G Go e d D0 Hdec | G Go e ds d T D0 Hdefs IH Hdec Habsent].
  - inversion Hrec; subst. exists d.
    pose proof (definition_label_matches_typing Hdec).
    split; [assumption |].
    unfold defs_has. cbn [get_def]. case_if; congruence.
  - inversion Hrec; subst.
    + destruct IH as [d' [Hb Hget]]; [assumption |].
      exists d'. split; [exact Hb |].
      unfold defs_has, defs_hasnt in *. cbn [get_def].
      case_if; congruence.
    + match goal with H : record_has (typ_rcd _) _ |- _ => inversion H; subst end. exists d.
      pose proof (definition_label_matches_typing Hdec).
      split; [assumption |].
      unfold defs_has. cbn [get_def]. case_if; congruence.
Qed.

Local Lemma ctx_binds_unique G x T U :
  ctx_binds x T G -> ctx_binds x U G -> T = U.
Proof.
  intros H. revert U. induction H; intros U HU; inversion HU; subst;
    try congruence; auto.
Qed.

Local Lemma forget_kind_of_binding x vk T G P :
  ctx_binds_k_after x vk T G P -> ctx_binds x T G.
Proof. intros H. induction H; auto using ctx_binds. Qed.

Local Lemma typed_location_record_member mode G e h y U S ds D :
  heap_correspond (typing_mode := mode) G e h ->
  binds y (item_obj ds) h ->
  ctx_binds y (typ_objref U S) G ->
  record_has (open y U) D ->
  exists d, label_of d = label_of D /\ defs_has ds d.
Proof.
  intros Hcorr Hb Htype Hrecord.
  destruct Hcorr as [_ [_ [_ [_ [_ [_ [_ Hitems]]]]]]].
  assert (Hy : y \in dom h) by (apply get_some_inv with (v := item_obj ds); exact Hb).
  specialize (Hitems y Hy).
  destruct Hitems as [G e h y S' body L T Hfun Hbind Hof Hbody Hkind |
    G e h y U' S' ds' T Hbind Hof Htype' Hdefs Hkind]; subst.
  - pose proof (binds_functional Hb Hof). discriminate.
  - pose proof (binds_functional Hb Hof) as Hds. inversion Hds; subst.
    pose proof (ctx_binds_unique Htype Hbind) as Htypes. inversion Htypes; subst.
    unfold obj_typing in Hdefs. eapply typed_record_member_exists; eassumption.
Qed.

Local Lemma typed_location_object_type mode G e h y :
  mode_has_mutability mode ->
  heap_correspond (typing_mode := mode) G e h ->
  ctx_k G y v_loc ->
  exists R1 R2 P, ctx_binds_k_after y v_loc (typ_objref R1 R2) G P.
Proof.
  intros Hmut [_ [_ [_ [_ [Hloc [_ [_ Hitems]]]]]]]
    [S [P Hbind]].
  assert (Hy : y \in dom h).
  { rewrite <- Hloc. eapply kinded_binding_in_context; exact Hbind. }
  specialize (Hitems y Hy).
  destruct Hitems.
  - exfalso. pose proof (no_functions_in_mutability_mode mode Hmut). congruence.
  - assert (S = typ_objref U S0)
      by (eapply ctx_binds_unique; eauto using forget_kind_of_binding; congruence).
    subst. eauto.
Qed.

Local Lemma typed_read_with_member mode G w a fs h e Lv T :
  let C := config_mk (trm_read (avar_f w) a) fs h e Lv in
  mode_has_mutability mode ->
  @ty_config mode G C T ->
  (forall y ds, binds w y e -> binds y (item_obj ds) h ->
    exists v, defs_has ds (def_fld a v)) ->
  (forall y R1 R2 P W R TS TC,
    ctx_binds_k_after y v_loc (typ_objref R1 R2) G P ->
    ty_var mode G objctx_empty e w (typ_rcd (dec_fld a W R)) ->
    ty_incap mode G objctx_empty e R TS ->
    ty_capbnd mode typ_refcap_mutability G objctx_empty e R TC ->
    @ty_stack mode G e (rodot_read_term_type TS w TC) fs T ->
    closed (rodot_read_ref_type R1 TS w TC) /\
    nothing_fresh_in_config (rodot_read_ref_type R1 TS w TC) C) ->
  exists G' C', typed_red mode G C T G' C'.
Proof.
  cbv zeta.
  intros Hmut Htyping Hmember Hscoped.
  destruct (heap_lookup_transport Hmut Htyping (tfree_trm_read w a))
    as [yobj [ds [Href [Hobj Hkinds]]]].
  destruct (Hmember _ _ Href Hobj) as [v Hfield].
  destruct (lookup_field_location Hkinds Hfield) as [y [-> Hy]].
  inversion Htyping as [G0 e0 fs0 h0 L0 t0 U T0 Hin Hheap Hstack Htf Hread]; subst.
  unfold obj_typing in Hread.
  destruct (read_continuation_type Hread Hstack Hmut)
    as [W [R [TS [TC [Hproj [Hstrip [Hcap Hcont]]]]]]].
  destruct (typed_location_object_type Hmut Hheap Hy) as [R1 [R2 [P Hbind]]].
  destruct (Hscoped _ _ _ _ _ _ _ _ Hbind Hproj Hstrip Hcap Hcont)
    as [Hclosed Hnfr].
  set (Rref := rodot_read_ref_type R1 TS w TC) in *.
  set (C := config_mk (trm_read (avar_f w) a) fs h e Lv) in *.
  destruct (var_fresh (fv_config C \u (ctx_fv G \u fv Rref))) as [w' Hw].
  apply notin_union in Hw as [HwC HwT].
  apply notin_union in HwT as [HwG HwT].
  assert (Hmode : mode_viewpoint_adaptation' mode = mode_viewpoint_adapt_mutability)
    by (destruct mode; simpl in *; congruence).
  exists (G § w' / v_ref ~ Rref).
  exists (config_mk (trm_var (avar_f w')) fs h (e & w' ~ y) (fv_config C)).
  eapply (@tred_read_obj mode G P w w' yobj y a T Rref R W R1 R2 ds
    (trm_read (avar_f w) a) fs e h Lv); try assumption; try reflexivity.
  - cbn [fresh length]. auto.
  - auto.
  - rewrite Hmode. exists TS, TC. repeat split; assumption || reflexivity.
Qed.

(* A fresh reference binding leaves all previous renaming facts available. *)

Local Lemma var_equiv_under_renv_extension e w v :
  tyq_var e w v -> forall e', preserves_bindings e e' -> tyq_var e' w v.
Proof.
  intro H. induction H as [e w | e w v Hb | e w v H IH | e a b c H1 IH1 H2 IH2];
    intros e' Hext.
  - apply tyq_var_refl.
  - apply tyq_var_binds. exact (Hext w v Hb).
  - apply tyq_var_sym. exact (IH e' Hext).
  - eapply tyq_var_trans; [exact (IH1 e' Hext) | exact (IH2 e' Hext)].
Qed.

Local Lemma type_equiv_under_renv_extension e S T :
  tyq_typ e S T -> forall e', preserves_bindings e e' -> tyq_typ e' S T.
Proof.
  intro H. induction H; intros e' Hext;
    solve [econstructor; unfold typing_equiv in *; intros;
      eauto using var_equiv_under_renv_extension].
Qed.

Local Lemma types_under_renv_extension mode :
  (forall G Go e w T, ty_var mode G Go e w T ->
    forall e', preserves_bindings e e' -> ty_var mode G Go e' w T) /\
  (forall G Go e S T, subtyp mode G Go e S T ->
    forall e', preserves_bindings e e' -> subtyp mode G Go e' S T) /\
  (forall G Go e S T, ty_incap mode G Go e S T ->
    forall e', preserves_bindings e e' -> ty_incap mode G Go e' S T).
Proof.
  apply (@ts_mutind mode
    (fun G Go e w T _ => forall e', preserves_bindings e e' -> ty_var mode G Go e' w T)
    (fun G Go e S T _ => forall e', preserves_bindings e e' -> subtyp mode G Go e' S T)
    (fun G Go e S T _ => forall e', preserves_bindings e e' -> ty_incap mode G Go e' S T)).
  all: intros; solve [econstructor; unfold obj_typing, obj_ref_incap, subtyping, typing_equiv in *;
    intros; eauto 4 using type_equiv_under_renv_extension].
Qed.

Local Lemma cap_bound_under_renv_extension mode C G Go e S T :
  ty_capbnd mode C G Go e S T ->
  forall e', preserves_bindings e e' -> ty_capbnd mode C G Go e' S T.
Proof.
  destruct (types_under_renv_extension mode) as [Hvar _].
  intro H. induction H; intros e' Hext;
    solve [econstructor; unfold obj_typing, obj_cap_bnd in *; eauto].
Qed.

Local Lemma viewpoint_under_renv_extension mode w G Go e S T :
  viewpoint_adapt mode w G Go e S T ->
  forall e', preserves_bindings e e' -> viewpoint_adapt mode w G Go e' S T.
Proof.
  destruct (types_under_renv_extension mode) as [_ [_ Hincap]].
  unfold viewpoint_adapt. destruct (mode_viewpoint_adaptation' mode); auto.
  intros H e' Hext. destruct H.
  constructor; unfold obj_ref_incap, obj_cap_bnd in *;
    eauto using cap_bound_under_renv_extension.
Qed.

Local Lemma terms_under_renv_extension mode :
  (forall G Go e t T, ty_trm mode G Go e t T ->
    forall e', preserves_bindings e e' -> ty_trm mode G Go e' t T) /\
  (forall G Go e l T, ty_lit mode G Go e l T ->
    forall e', preserves_bindings e e' -> ty_lit mode G Go e' l T) /\
  (forall G Go e d D, ty_def mode G Go e d D ->
    forall e', preserves_bindings e e' -> ty_def mode G Go e' d D) /\
  (forall G Go e ds T, ty_defs mode G Go e ds T ->
    forall e', preserves_bindings e e' -> ty_defs mode G Go e' ds T).
Proof.
  destruct (types_under_renv_extension mode) as [Hvar [Hsub Hincap]].
  apply (@rules_mutind mode
    (fun G Go e t T _ => forall e', preserves_bindings e e' -> ty_trm mode G Go e' t T)
    (fun G Go e l T _ => forall e', preserves_bindings e e' -> ty_lit mode G Go e' l T)
    (fun G Go e d D _ => forall e', preserves_bindings e e' -> ty_def mode G Go e' d D)
    (fun G Go e ds T _ => forall e', preserves_bindings e e' -> ty_defs mode G Go e' ds T)).
  all: intros; solve [econstructor; unfold obj_typing, obj_dec_typing, subtyping,
    obj_ref_incap, typing_equiv in *; intros;
    eauto 6 using viewpoint_under_renv_extension, type_equiv_under_renv_extension].
Qed.

Local Lemma stack_typing_under_renv_extension mode G e S fs T :
  @ty_stack mode G e S fs T ->
  forall e', preserves_bindings e e' -> @ty_stack mode G e' S fs T.
Proof.
  destruct (types_under_renv_extension mode) as [_ [Hsub _]].
  destruct (terms_under_renv_extension mode) as [Hterm _].
  intro H. induction H; intros e' Hext;
    solve [econstructor; unfold subtyping, obj_typing in *; eauto].
Qed.

Local Lemma stack_typing_under_ctx_extension mode G e S fs T :
  @ty_stack mode G e S fs T ->
  forall G', ctx_extends G G' -> @ty_stack mode G' e S fs T.
Proof.
  destruct (ctx_extends_types mode) as [_ [Hsub _]].
  destruct (ctx_extends_terms mode) as [Hterm _].
  intro H. induction H; intros G' Hext;
    solve [econstructor; unfold subtyping, obj_typing in *; intros;
      eauto using ctx_extends_push].
Qed.

Local Lemma fresh_ref_extension_keeps_bindings (e : renv) w y :
  w # e -> preserves_bindings e (e & w ~ y).
Proof.
  intros Hfresh x v Hb. apply binds_push_neq; [exact Hb |].
  intro Heq. subst x. eapply binds_fresh_inv; eassumption.
Qed.

Local Lemma invert_object_let_type mode G e R ds u U :
  ty_trm mode G objctx_empty e (trm_lit (lit_obj R ds) u) U ->
  exists L V,
    (forall w, w \notin L ->
      ty_trm mode (G §ˣ w ~ typ_objref_loc mode R) objctx_empty e (open w u) V) /\
    subtyp mode G objctx_empty e V U.
Proof.
  intro H. remember (trm_lit (lit_obj R ds) u) as t eqn:Ht.
  induction H; try discriminate; unfold obj_typing, subtyping in *.
  - inversion Ht; subst. inversion H; subst. exists L, U.
    split.
    + destruct mode; simpl in *; assumption.
    + apply subtyp_refl.
  - destruct (IHty_trm Ht) as [L [V [Hbody Hsub]]].
    exists L, V. split; [exact Hbody |]. eapply subtyp_trans; eassumption.
Qed.

Local Lemma allocated_control_typing_avoiding mode G e R ds u fs h Lv T (avoid : vars) :
  @ty_config mode G (config_mk (trm_lit (lit_obj R ds) u) fs h e Lv) T ->
  exists y w V,
    let G' := inert_G_for_obj_loc mode G w y R in
    let e' := e & w ~ y in
    let C := config_mk (trm_lit (lit_obj R ds) u) fs h e Lv in
    let allocated := config_mk (open w u) fs
      (heap_with_obj_dereffed h e w y ds) e' (fv_config C) in
    y \notin avoid /\ w \notin avoid /\
    fresh_in_config (y :: w :: nil)%list C /\
    y \notin (ctx_fv G \u fv R) /\ w \notin (ctx_fv G \u fv R) /\
    typed_red mode G C T G' allocated /\
    ty_trm mode G' objctx_empty e' (open w u) V /\
    @ty_stack mode G' e' V fs T.
Proof.
  intro Hty.
  inversion Hty as [G0 e0 fs0 h0 Lv0 t0 U T0 Hin Hheap Hstack Htfs Hterm Htft Hfv]; subst.
  unfold obj_typing in Hterm.
  destruct (invert_object_let_type Hterm) as [L [V [Hbody Hsub]]].
  set (C := config_mk (trm_lit (lit_obj R ds) u) fs h e Lv) in *.
  set (A := typ_objref_loc mode R) in *.
  set (D := (fv_config C \u (ctx_fv G \u fv R)) \u avoid).
  destruct (var_fresh D) as [y Hy].
  destruct (var_fresh (D \u (L \u \{y}))) as [w Hw].
  unfold D in Hy, Hw.
  apply notin_union in Hy as [Hy Hyavoid].
  apply notin_union in Hy as [HyC Hyfv].
  apply notin_union in Hw as [Hw HwL].
  apply notin_union in Hw as [Hw Hwavoid].
  apply notin_union in Hw as [HwC Hwfv].
  apply notin_union in HwL as [HwL Hneq].
  assert (HyG : y \notin ctx_dom G)
    by (intro Hdom; apply HyC; exact (proj1 (proj1 Hfv) _ Hdom)).
  assert (HwG : w \notin ctx_dom G)
    by (intro Hdom; apply HwC; exact (proj1 (proj1 Hfv) _ Hdom)).
  assert (HwG' : w \notin ctx_dom (G § y / v_loc ~ A)).
  {
    cbn [ctx_dom]. apply notin_union. auto.
  }
  assert (Hext : ctx_extends G (G § y / v_loc ~ A § w / v_ref ~ A)).
  {
    destruct (@ctx_extends_with_fresh G y v_loc A HyG) as [Hb1 Hv1].
    destruct (@ctx_extends_with_fresh (G § y / v_loc ~ A) w v_ref A HwG') as [Hb2 Hv2].
    split.
    - intros v S Hb. exact (Hb2 v S (Hb1 v S Hb)).
    - intros v Hv. exact (Hv2 v (Hv1 v Hv)).
  }
  assert (Hbody_ext : ctx_extends (G §ˣ w ~ A) (G § y / v_loc ~ A § w / v_ref ~ A)).
  {
    destruct (@ctx_extends_push G (G § y / v_loc ~ A) w v_let A (@ctx_extends_with_fresh G y v_loc A HyG))
      as [Hb Hv].
    split.
    - intros x S Hx. specialize (Hb x S Hx). inversion Hb; subst; eauto using ctx_binds.
    - intros x Hx. specialize (Hv x Hx). inversion Hv; subst; eauto using ctx_vis.
  }
  assert (Hrenv_ext : preserves_bindings e (e & w ~ y))
    by (apply fresh_ref_extension_keeps_bindings; now apply fresh_from_machine_for_env in HwC).
  assert (Hfresh : fresh_in_config (y :: w :: nil)%list C).
  {
    cbn [fresh length]. split; [exact HyC |]. split; [|trivial].
    apply notin_union. auto.
  }
  exists y, w, V. cbv zeta.
  split; [exact Hyavoid |]. split; [exact Hwavoid |].
  split; [exact Hfresh |]. split; [exact Hyfv |]. split; [exact Hwfv |]. split.
  - eapply tred_let_obj; try reflexivity; assumption.
  - split.
    + eapply (proj1 (terms_under_renv_extension mode)); [| exact Hrenv_ext].
      eapply (proj1 (ctx_extends_terms mode)); [|exact Hbody_ext].
      exact (Hbody w HwL).
    + eapply stack_typing_under_renv_extension; [|exact Hrenv_ext].
      eapply stack_typing_under_ctx_extension; [|exact Hext].
      eapply stack_narrow_input; eassumption.
Qed.



Local Lemma allocated_control_typing mode G e R ds u fs h Lv T :
  @ty_config mode G (config_mk (trm_lit (lit_obj R ds) u) fs h e Lv) T ->
  exists y w V,
    let G' := inert_G_for_obj_loc mode G w y R in
    let e' := e & w ~ y in
    let C := config_mk (trm_lit (lit_obj R ds) u) fs h e Lv in
    let allocated := config_mk (open w u) fs
      (heap_with_obj_dereffed h e w y ds) e' (fv_config C) in
    typed_red mode G C T G' allocated /\
    ty_trm mode G' objctx_empty e' (open w u) V /\
    @ty_stack mode G' e' V fs T.
Proof.
  intro H.
  destruct (@allocated_control_typing_avoiding mode G e R ds u fs h Lv T \{} H)
    as [y [w [V [_ [_ [_ [_ [_ Hstep]]]]]]]].
  exists y, w, V. exact Hstep.
Qed.

Require Import TypeInduction.

(* Changing a self alias affects only the receivers of normal type selections. *)

Inductive type_alias_congr (e : renv) : typ -> typ -> Prop :=
| type_alias_congr_id T : type_alias_congr e T T
| type_alias_congr_sel x y A p :
    tyq_var e x y ->
    type_alias_congr e
      (typ_sel (avar_f x) (typ_label_normal A) p)
      (typ_sel (avar_f y) (typ_label_normal A) p)
| type_alias_congr_and T1 T2 U1 U2 :
    type_alias_congr e T1 U1 -> type_alias_congr e T2 U2 ->
    type_alias_congr e (typ_and T1 T2) (typ_and U1 U2)
| type_alias_congr_or T1 T2 U1 U2 :
    type_alias_congr e T1 U1 -> type_alias_congr e T2 U2 ->
    type_alias_congr e (typ_or T1 T2) (typ_or U1 U2)
| type_alias_congr_bnd T U :
    type_alias_congr e T U -> type_alias_congr e (typ_bnd T) (typ_bnd U)
| type_alias_congr_fun S T U V :
    type_alias_congr e S U -> type_alias_congr e T V ->
    type_alias_congr e (typ_fun S T) (typ_fun U V)
| type_alias_congr_fld a S T U V :
    type_alias_congr e S U -> type_alias_congr e T V ->
    type_alias_congr e (typ_rcd (dec_fld a S T)) (typ_rcd (dec_fld a U V))
| type_alias_congr_typ A S T U V :
    type_alias_congr e S U -> type_alias_congr e T V ->
    type_alias_congr e (typ_rcd (dec_typ A S T)) (typ_rcd (dec_typ A U V))
| type_alias_congr_met m TC TZ TR UC UZ UR :
    type_alias_congr e TC UC -> type_alias_congr e TZ UZ -> type_alias_congr e TR UR ->
    type_alias_congr e (typ_rcd (dec_met m TC TZ TR)) (typ_rcd (dec_met m UC UZ UR)).

Local Lemma type_alias_congr_open e S T :
  type_alias_congr e S T ->
  forall k x, type_alias_congr e (open_rec k x S) (open_rec k x T).
Proof.
  induction 1; intros;
    cbn [open_rec TypOpenable open_rec_typ open_rec_dec AvarOpenable];
    eauto using type_alias_congr.
Qed.

Local Lemma opening_height_preserved :
  (forall T k x,
    typ_opening_ind_height (open_rec k x T) = typ_opening_ind_height T) /\
  (forall D k x,
    typ_opening_ind_height (typ_rcd (open_rec k x D)) = typ_opening_ind_height (typ_rcd D)).
Proof.
  apply typ_mutind; intros; unfold open_rec, TypOpenable, DecOpenable in *;
    cbn [open_rec_typ open_rec_dec typ_opening_ind_height];
    rewrite ?H, ?H0, ?H1; try reflexivity; auto.
  exact (H k x).
Qed.

Local Lemma tyq_type_reflexive e T : tyq_typ e T T.
Proof.
  remember (typ_opening_ind_height T) as h eqn:Hh.
  revert T Hh. induction h using lt_wf_ind.
  intros T Hh. destruct (opening_height_preserved) as [Hopen Hdec].
  assert (Hlt : forall U, typ_opening_ind_height U < h -> tyq_typ e U U)
    by (intros U Hu; eapply H; [exact Hu | reflexivity]).
  assert (Hlt_open : forall U, typ_opening_ind_height U < h ->
    forall k x, tyq_typ e (open_rec k x U) (open_rec k x U)).
  { intros U HU k x. apply Hlt. now rewrite Hopen. }
  clear H. destruct T as [| |D|S T|S T|x A y|T|S T|];
    try solve [apply tyq_typ_nulary; constructor].
  - destruct D as [A S T | a S T | m C Z R].
    + apply tyq_typ_typ; unfold typing_equiv. all: intros; apply Hlt_open;
        cbn in Hh; lia.
    + apply tyq_typ_fld; unfold typing_equiv. all: apply Hlt;
        cbn in Hh; lia.
    + apply tyq_typ_met; unfold typing_equiv.
      * intros. apply Hlt_open. cbn in Hh. lia.
      * apply Hlt. cbn in Hh. lia.
      * intros. apply Hlt_open. rewrite Hopen. cbn in Hh. lia.
  - apply tyq_typ_andor with (T := typ_and); unfold typing_equiv;
      [constructor | apply Hlt | apply Hlt]; cbn in Hh; lia.
  - apply tyq_typ_andor with (T := typ_or); unfold typing_equiv;
      [constructor | apply Hlt | apply Hlt]; cbn in Hh; lia.
  - apply tyq_typ_sel.
  - apply tyq_typ_bnd. unfold typing_equiv. intro. apply Hlt_open. cbn in Hh. lia.
  - apply tyq_typ_fun; unfold typing_equiv.
    + apply Hlt. cbn in Hh. lia.
    + intro. apply Hlt_open. cbn in Hh. lia.
Qed.

Local Lemma type_alias_congr_is_equiv e S T :
  type_alias_congr e S T -> tyq_typ e S T.
Proof.
  remember (typ_opening_ind_height S) as h eqn:Hh.
  revert S T Hh. induction h using lt_wf_ind.
  intros S T Hh Hcongr.
  assert (Hlt : forall A B, typ_opening_ind_height A < h ->
    type_alias_congr e A B -> tyq_typ e A B)
    by (intros A B HA HAB; eapply H; [exact HA | reflexivity | exact HAB]).
  destruct (opening_height_preserved) as [Hopen _].
  assert (Hlt_open : forall A B, typ_opening_ind_height A < h ->
    type_alias_congr e A B -> forall k x, tyq_typ e (open_rec k x A) (open_rec k x B)).
  {
    intros A B HA HAB k x. apply Hlt; [now rewrite Hopen |].
    now apply type_alias_congr_open.
  }
  clear H. destruct Hcongr; cbn in Hh.
  - apply tyq_type_reflexive.
  - apply tyq_typ_sel_normal. assumption.
  - apply tyq_typ_andor with (T := typ_and); unfold typing_equiv;
      [constructor | apply Hlt | apply Hlt]; try lia; assumption.
  - apply tyq_typ_andor with (T := typ_or); unfold typing_equiv;
      [constructor | apply Hlt | apply Hlt]; try lia; assumption.
  - apply tyq_typ_bnd. unfold typing_equiv. intro. apply Hlt_open; [lia | assumption].
  - apply tyq_typ_fun; unfold typing_equiv.
    + apply Hlt; [lia | assumption].
    + intro. apply Hlt_open; [lia | assumption].
  - apply tyq_typ_fld; unfold typing_equiv; apply Hlt; try lia; assumption.
  - apply tyq_typ_typ; unfold typing_equiv; intros; apply Hlt_open; try lia; assumption.
  - apply tyq_typ_met; unfold typing_equiv.
    + intros. apply Hlt_open; [lia | assumption].
    + apply Hlt; [lia | assumption].
    + intros. apply Hlt_open; [rewrite Hopen; lia | now apply type_alias_congr_open].
Qed.

Local Lemma open_avar_unchanged k x a :
  avar_b k <> a -> open_rec k x a = a.
Proof. destruct a; cbn [open_rec AvarOpenable]; try case_if; congruence. Qed.

Local Lemma open_avar_equal k x : open_rec k x (avar_b k) = avar_f x.
Proof. cbn [open_rec AvarOpenable]. case_if; congruence. Qed.

Local Lemma independent_type_opens_with_alias e x y v T :
  tyq_var e x y ->
  typ_indep v T ->
  forall k, v = avar_b k -> type_alias_congr e (open_rec k x T) (open_rec k y T).
Proof.
  intros Hxy Hi. induction Hi; intros k Hk; try (injection Hk as <-); subst; try discriminate.
  all: cbn [open_rec TypOpenable open_rec_typ open_rec_dec].
  all: fold open_rec_typ open_rec_dec.
  all: try solve [econstructor;
    match goal with
    | IH : forall k : nat, avar_b _ = avar_b k -> _ |- _ => apply IH; reflexivity
    end].
  - destruct H; apply type_alias_congr_id.
  - change (type_alias_congr e (typ_sel (open_rec k x v1) l (open_rec k x v2))
      (typ_sel (open_rec k y v1) l (open_rec k y v2))).
    rewrite !open_avar_unchanged by assumption. apply type_alias_congr_id.
  - change (type_alias_congr e
      (typ_sel (open_rec k x v1) (typ_label_normal l) (open_rec k x v2))
      (typ_sel (open_rec k y v1) (typ_label_normal l) (open_rec k y v2))).
    rewrite (open_avar_unchanged x H), (open_avar_unchanged y H).
    destruct (classic (v1 = avar_b k)) as [-> | Hneq].
    + rewrite !open_avar_equal. apply type_alias_congr_sel. exact Hxy.
    + rewrite !open_avar_unchanged by congruence. apply type_alias_congr_id.
Qed.

Local Lemma opening_independent_type_with_alias e x y k T :
  tyq_var e x y -> typ_indep_b k T ->
  tyq_typ e (open_rec k x T) (open_rec k y T).
Proof.
  intros Hxy Htype. apply type_alias_congr_is_equiv.
  eapply independent_type_opens_with_alias; eassumption || reflexivity.
Qed.

Local Lemma type_equivalence_transitive e T U V :
  tyq_typ e T U -> tyq_typ e U V -> tyq_typ e T V.
Proof.
  intros Htu. revert V. induction Htu; intros V Huv; try exact Huv.
  all: repeat match goal with H : typ_andor _ |- _ => destruct H end.
  all: inversion Huv; subst; clear Huv.
  all: repeat match goal with H : typ_andor _ |- _ => destruct H end.
  all: repeat match goal with H : typ_nulary _ |- _ => inversion H; subst; clear H end.
  all: repeat match goal with H : _ = _ |- _ => inversion H; subst; clear H end.
  all: try solve [econstructor; unfold typing_equiv in *; intros; eauto 5 using tyq_var_trans].
  all: try (eapply tyq_typ_andor; [constructor | |]; unfold typing_equiv in *; eauto 4).
  apply tyq_typ_sel_normal. eapply tyq_var_trans; eassumption.
Qed.

Local Lemma nocap_subtypes_incapacitated_type mode G Go e S T :
  ty_incap mode G Go e S T -> subtyp mode G Go e typ_nocap T.
Proof.
  intro H. induction H; unfold subtyping in *.
  all: try solve [assumption | apply subtyp_top | apply subtyp_refl |
    apply subtyp_nocap_typ | apply subtyp_nocap_met | apply subtyp_nocap_fld |
    apply subtyp_nocap_bnd | apply subtyp_nocap_fun; assumption].
  - apply subtyp_and2; assumption.
  - eapply subtyp_trans with (T := S2); [assumption | apply subtyp_or11].
Qed.

Local Lemma equivalent_type_subtypes mode G e S T :
  tyq_typ e S T -> subtyp mode G objctx_empty e S T.
Proof. intro H. apply subtyp_tyq. exact H. Qed.

Local Lemma transport_variable_to_alias mode G e w y T :
  mode_incap' mode = mode_incap_nocap ->
  tyq_var e w y ->
  (forall S, ctx_binds w S G -> ty_var mode G objctx_empty e y S) ->
  ty_var mode G objctx_empty e w T ->
  ty_var mode G objctx_empty e y T.
Proof.
  intros Hmode Heq Hbind Htype.
  remember w as z eqn:Hz in Htype.
  induction Htype; subst; unfold obj_typing, subtyping, obj_ref_incap in *.
  - now apply Hbind.
  - assert (Halias : subtyp mode G objctx_empty e (open w T) (open y T))
      by (apply equivalent_type_subtypes; now apply opening_independent_type_with_alias).
    eapply ty_rec_intro; unfold obj_typing, obj_ref_incap.
    + eapply ty_var_sub; [apply IHHtype; auto | exact Halias].
    + assumption.
    + intro Hcap. apply ty_incap_nocap; [exact Hmode |].
      unfold subtyping. eapply subtyp_trans; [|exact Halias].
      eapply nocap_subtypes_incapacitated_type. exact (H1 Hcap).
  - assert (Halias : subtyp mode G objctx_empty e (open y T) (open w T))
      by (apply equivalent_type_subtypes, opening_independent_type_with_alias;
          [now apply tyq_var_sym | assumption]).
    eapply ty_var_sub; unfold obj_typing, subtyping.
    + eapply ty_rec_elim; unfold obj_typing; [apply IHHtype; auto | assumption].
    + exact Halias.
  - eapply ty_var_and; unfold obj_typing; auto.
  - eapply ty_var_sub; unfold obj_typing; eauto.
  - eapply ty_var_mut_top; unfold obj_typing; eauto.
Qed.

Local Lemma ctx_kind_domain_is_in_domain G k : ctx_kdom k G \c ctx_dom G.
Proof.
  induction G; intros x Hx; cbn [ctx_kdom ctx_dom] in *; auto.
  case_if; rewrite ?in_union in *; intuition.
Qed.

Local Lemma ctx_kind_domains_disjoint G k k' :
  ctx_ok G -> k <> k' -> disjoint (ctx_kdom k G) (ctx_kdom k' G).
Proof.
  intros Hok Hneq.
  assert (Hsep : forall x, x \in ctx_kdom k G -> x \in ctx_kdom k' G -> False).
  {
    induction Hok; intros x Hx Hy; cbn [ctx_kdom] in *; rewrite ?in_empty in *; try contradiction; auto.
    repeat case_if; try congruence; rewrite ?in_union, ?in_singleton in *;
      repeat match goal with HD : _ \/ _ |- _ => destruct HD end;
      subst; try congruence; eauto.
    all: try solve [eapply IHHok; eassumption].
    all: match goal with Hout : ?v \notin ctx_dom ?G,
      Hin : ?v \in ctx_kdom ?k ?G |- _ =>
      exact (Hout (@ctx_kind_domain_is_in_domain G k v Hin))
    end.
  }
  unfold disjoint. apply fset_extens; intros x Hx.
  - rewrite in_inter in Hx. destruct Hx as [Hx Hy]. now exfalso; apply (Hsep x).
  - rewrite in_empty in Hx. contradiction.
Qed.

Local Lemma ctx_kind_domain_is_bound G k x :
  ctx_ok G -> ctx_weakens G -> x \in ctx_kdom k G -> ctx_k G x k.
Proof.
  intro Hok. induction Hok; intros Hw Hx; cbn [ctx_kdom] in Hx; try inversion Hw.
  - rewrite in_empty in Hx. contradiction.
  - assert (Hlater : x \in ctx_kdom k G -> x <> v -> ctx_k (G § v / vk ~ t) x k).
    {
      intros Hdom Hd. destruct (IHHok ltac:(assumption) Hdom) as [T [P Hb]].
      exists T, P. now apply ctx_binds_k_n.
    }
    case_if.
    + rewrite in_union in Hx. destruct Hx as [Heq | Hx].
      * rewrite in_singleton in Heq. subst. exists t, G. constructor.
      * apply Hlater; [exact Hx |]. intro Heq. subst.
        eapply H. now apply ctx_kind_domain_is_in_domain with (k := vk).
    + apply Hlater; [exact Hx |]. intro Heq. subst.
      eapply H. now apply ctx_kind_domain_is_in_domain with (k := k).
Qed.

Local Lemma context_extends_kinded_suffix x k S G G' :
  ctx_binds_k_after x k S G G' -> ctx_ok G -> ctx_extends G' G.
Proof.
  intro H. induction H; intro Hok; inversion Hok; subst.
  - now apply ctx_extends_with_fresh.
  - destruct (IHctx_binds_k_after ltac:(assumption)) as [H1bind H1vis].
    match goal with Hx : v2 \notin ctx_dom G1 |- _ =>
      destruct (@ctx_extends_with_fresh G1 v2 vk2 t2 Hx) as [H2bind H2vis]
    end.
    split.
    + intros y U Hy. exact (H2bind _ _ (H1bind _ _ Hy)).
    + intros y Hy. exact (H2vis _ (H1vis _ Hy)).
Qed.

Local Lemma renv_corresponding_bindings mode G e w y :
  @renv_corr mode G e -> ctx_ok G -> binds w y e ->
  exists Tw Ty, ctx_binds w Tw G /\ ctx_binds y Ty G /\ typ_corr (typing_mode := mode) Tw Ty.
Proof.
  intro H. induction H; intros Hok Hb; [exfalso; eapply binds_empty_inv; exact Hb |].
  apply binds_push_inv in Hb as [[-> ->] | [_ Hb]].
  - exists Tw, Ty. split; [eapply forget_kind_of_binding; eassumption |]. split; [|assumption].
    destruct (context_extends_kinded_suffix H Hok) as [Hprefix _].
    apply Hprefix. eapply forget_kind_of_binding; eassumption.
  - auto.
Qed.

Local Lemma corresponding_location_type_subtype mode G e Tw Ty :
  typ_corr (typing_mode := mode) Tw Ty ->
  subtyp mode G objctx_empty e Ty Tw.
Proof.
  intro H. destruct H as [R W Y HC | S T HF].
  - destruct mode; cbn in HC;
      try solve [subst; apply subtyp_refl].
    all: destruct HC as [B [-> ->]].
    all: apply subtyp_and2; unfold subtyping.
    all: try solve [apply subtyp_and11].
    all: eapply subtyp_trans; [apply subtyp_and12 |].
    all: apply subtyp_typ; unfold subtyping; intros; cbn; first [apply subtyp_refl | apply subtyp_bot].
  - apply subtyp_refl.
Qed.

Local Lemma location_preserves_reference_typing mode G e w y T :
  mode_incap' mode = mode_incap_nocap ->
  ctx_ok G -> @renv_corr mode G e ->
  binds w y e ->
  ty_var mode G objctx_empty e w T ->
  ty_var mode G objctx_empty e y T.
Proof.
  intros Hmode Hok Hcorr Hb Hty.
  destruct (renv_corresponding_bindings Hcorr Hok Hb) as [Tw [Ty [Hw [Hy HC]]]].
  eapply (@transport_variable_to_alias mode G e w y T); [exact Hmode | | | exact Hty].
  - apply tyq_var_binds. exact Hb.
  - intros U Hu. pose proof (ctx_binds_unique Hw Hu) as <-.
    eapply ty_var_sub with (T := Ty); unfold obj_typing, subtyping.
    + apply ty_var_var. exact Hy.
    + now apply corresponding_location_type_subtype.
Qed.

Local Lemma corresponding_renv_idempotent mode G e :
  ctx_ok G -> ok e -> ctx_kdom v_ref G = dom e ->
  @renv_corr mode G e -> renv_idempotent e.
Proof.
  intros Hok Hoe Hdom Hcorr w Hw Hfv.
  destruct (proj1 (@fv_env_value_member var fv e w Hoe) Hfv) as [x [y [Hb Hy]]].
  change (w \in \{y}) in Hy. rewrite in_singleton in Hy. subst y.
  eapply (@disjoint_in_notin var (ctx_kdom v_ref G) (ctx_kdom v_loc G) w).
  - apply ctx_kind_domains_disjoint; [exact Hok | discriminate].
  - rewrite Hdom. exact Hw.
  - eapply reference_target_in_context; eassumption.
Qed.

Local Lemma deref_keeps_unbound_name e w :
  w # e -> deref e (avar_f w) = avar_f w.
Proof.
  intro Hw. apply replay_deref_avar_fresh.
  intros y Hy. change (y \in \{w}) in Hy. rewrite in_singleton in Hy. now subst y.
Qed.

Local Lemma deref_label e d : label_of (deref e d) = label_of d.
Proof. destruct d; reflexivity. Qed.

Local Lemma get_def_after_deref e l ds :
  get_def l (deref e ds) = option_map (deref e) (get_def l ds).
Proof.
  induction ds as [|ds IH d]; [reflexivity |].
  change (get_def l (defs_cons (deref e ds) (deref e d)) =
    option_map (deref e) (get_def l (defs_cons ds d))).
  cbn [get_def]. rewrite deref_label, IH.
  case_if; reflexivity.
Qed.

Local Lemma ctx_binds_visible G x T :
  ctx_weakens G -> ctx_binds x T G -> ctx_vis G x.
Proof.
  intros Hw Hb. induction Hb; inversion Hw; subst; auto using ctx_vis.
Qed.

Local Lemma typed_heap_def_after_deref mode G e y R d D :
  mode_incap' mode = mode_incap_nocap ->
  ctx_ok G -> ctx_weakens G -> renv_idempotent e -> @renv_corr mode G e ->
  ty_def mode G (objctx_heap y R) e d D ->
  ty_def mode G (objctx_heap y R) e (deref e d) D.
Proof.
  intros Hmode Hok Hw Hi Hcorr Htd.
  remember (objctx_heap y R) as Go eqn:HGo in Htd.
  destruct Htd; subst Go; try assumption.
  - change (ty_def mode G (objctx_heap y R) e (def_typ (typ_label_normal A) T)
      (dec_typ (typ_label_normal A) U U)).
    eapply ty_def_typ; eassumption.
  - change (ty_def mode G (objctx_heap y R) e (def_fld a (deref e (avar_f t)))
      (dec_fld a T T)).
    destruct (classic (t \in dom e)) as [Ht | Ht].
    + destruct (get_some Ht) as [p Hb].
      rewrite (deref_bound_value Hi Hb).
      apply ty_def_fld; cbn [ctx_obj]; unfold obj_typing in *.
      * intros _. 
        destruct (renv_corresponding_bindings Hcorr Hok Hb) as [Tw [Ty [_ [Hloc _]]]].
        apply ctx_binds_visible with (T := Ty); [|exact Hloc].
        exact ltac:(assumption).
      * eapply location_preserves_reference_typing; eassumption.
    + rewrite deref_keeps_unbound_name by assumption.
      now apply ty_def_fld.
  - eapply ty_def_met; eassumption.
Qed.

Local Lemma typed_heap_defs_after_deref mode G e y R ds T :
  mode_incap' mode = mode_incap_nocap ->
  ctx_ok G -> ctx_weakens G -> renv_idempotent e -> @renv_corr mode G e ->
  ty_defs mode G (objctx_heap y R) e ds T ->
  ty_defs mode G (objctx_heap y R) e (deref e ds) T.
Proof.
  intros Hmode Hok Hw Hi Hcorr Hty.
  remember (objctx_heap y R) as Go eqn:HGo in Hty.
  induction Hty; subst Go; unfold obj_typing, obj_dec_typing in *.
  - apply ty_defs_one. unfold obj_dec_typing.
    eapply typed_heap_def_after_deref; eassumption.
  - apply ty_defs_cons; unfold obj_typing, obj_dec_typing.
    + apply IHHty; auto.
    + eapply typed_heap_def_after_deref; eassumption.
    + unfold defs_hasnt in *. rewrite deref_label, get_def_after_deref.
      match goal with Habs : get_def _ _ = None |- _ => now rewrite Habs end.
Qed.

Local Lemma kind_after_fresh_push G x k y vk T :
  y \notin ctx_dom G -> ctx_k G x k -> ctx_k (G § y / vk ~ T) x k.
Proof.
  intros Hy [U [P Hbind]]. exists U, P. apply ctx_binds_k_n; [|exact Hbind].
  intro Heq. subst y. apply Hy.
  eapply swap_calls_binding_in_context, forget_kind_of_binding; eassumption.
Qed.

Local Lemma defs_varkinds_under_context_change G G' ds :
  (forall x k, ctx_k G x k -> ctx_k G' x k) ->
  defs_varkinds G ds -> defs_varkinds G' ds.
Proof.
  intros Hkind Hd. induction Hd; [constructor |].
  constructor; [now apply IHHd |]. destruct H.
  - constructor. now apply Hkind.
  - constructor.
  - constructor. intros x Hx. auto.
Qed.

Local Lemma renv_corr_under_fresh_binding mode G e x vk T :
  @renv_corr mode G e ->
  x \notin ctx_dom G ->
  @renv_corr mode (G § x / vk ~ T) e.
Proof.
  intro H. induction H; intro Hfresh.
  - apply renv_corr_empty.
  - eapply renv_corr_ref; [|exact H0|exact H1|now apply IHrenv_corr].
    apply ctx_binds_k_n; [|exact H].
    intro E. subst x. apply Hfresh.
    eapply swap_calls_binding_in_context, forget_kind_of_binding; eassumption.
Qed.

Local Lemma allocated_heap_correspondence mode G e h w y R ds :
  let A := typ_objref_loc mode R in
  let G' := G § y / v_loc ~ A § w / v_ref ~ A in
  let e' := e & w ~ y in
  mode_has_mutability mode ->
  heap_correspond (typing_mode := mode) G e h ->
  y \notin ctx_dom G -> w \notin ctx_dom G -> w <> y ->
  ty_defs mode G' (objctx_heap y R) e' ds (open y R) ->
  defs_varkinds G' ds ->
  heap_correspond (typing_mode := mode) G' e' (h & y ~ item_obj ds).
Proof.
  cbv zeta. intros Hmut Hheap HyG HwG Hneq Hdefs Hd.
  set (A := typ_objref_loc mode R) in *.
  destruct Hheap as [Hok [Hctx [Hh [He [Hdom1 [Hdom2 [Hcorr Hitems]]]]]]].
  assert (HwG' : w \notin ctx_dom (G § y / v_loc ~ A)).
  { cbn [ctx_dom]. rewrite notin_union, notin_singleton. auto. }
  assert (Hyh : y # h).
  { rewrite <- Hdom1. intro Hy. apply HyG. eapply ctx_kind_domain_is_in_domain; exact Hy. }
  assert (Hwe : w # e).
  { rewrite <- Hdom2. intro Hw. apply HwG. eapply ctx_kind_domain_is_in_domain; exact Hw. }
  assert (Hext : ctx_extends G (G § y / v_loc ~ A § w / v_ref ~ A)).
  {
    destruct (@ctx_extends_with_fresh G y v_loc A HyG) as [Hb1 Hv1].
    destruct (@ctx_extends_with_fresh (G § y / v_loc ~ A) w v_ref A HwG') as [Hb2 Hv2].
    split.
    - intros p S Hb. exact (Hb2 p S (Hb1 p S Hb)).
    - intros p Hv. exact (Hv2 p (Hv1 p Hv)).
  }
  split; [apply ctx_ok_push; [now apply ctx_ok_push | exact HwG'] |].
  split; [now do 2 constructor |].
  split; [now apply ok_push |]. split; [now apply ok_push |].
  split; [cbn [ctx_kdom]; repeat case_if; try congruence;
    rewrite Hdom1, dom_push, union_comm; reflexivity |].
  split; [cbn [ctx_kdom]; repeat case_if; try congruence;
    rewrite Hdom2, dom_push, union_comm; reflexivity |].
  split.
  - assert (Htyp : typ_corr (typing_mode := mode) A A).
    { subst A. destruct mode; cbn in *; try discriminate.
      all: apply typ_corr_obj; exists typ_bot; auto. }
    eapply renv_corr_ref; [apply ctx_binds_k_e | apply ctx_binds_k_e | exact Htyp |].
    apply renv_corr_under_fresh_binding; [|exact HwG'].
    now apply renv_corr_under_fresh_binding.
  - intros p Hp. rewrite dom_push, in_union, in_singleton in Hp.
    destruct Hp as [-> | Hp].
    + assert (HA : A = typ_objref R (typ_mut_marker typ_bot))
        by (subst A; destruct mode; cbn in *; try discriminate; reflexivity).
      eapply ty_item_obj_s with (U := R) (S := typ_mut_marker typ_bot) (T := A);
        [apply ctx_binds_n; [congruence | apply ctx_binds_e] |
         apply binds_push_eq | exact HA | exact Hdefs | exact Hd].
    + specialize (Hitems p Hp).
      assert (Hneqp : p <> y) by (intro E; subst p; contradiction).
      destruct Hitems as [G e h p U body L V Hfun Hbound Hit Hbody Hvk |
        G e h p U W defs T Hbound Hit Heq Hds Hvk].
      * pose proof (@no_functions_in_mutability_mode mode Hmut). congruence.
      * eapply ty_item_obj_s with (ds := defs) (U := U) (S := W) (T := T);
          [exact (proj1 Hext _ _ Hbound) | apply binds_push_neq; assumption |
           exact Heq | |].
        -- unfold obj_typing in *.
           eapply (proj2 (proj2 (proj2 (terms_under_renv_extension mode))));
             [|now apply fresh_ref_extension_keeps_bindings].
           eapply (proj2 (proj2 (proj2 (ctx_extends_terms mode)))); eassumption.
        -- eapply defs_varkinds_under_context_change; [|exact Hvk].
           intros x k Hkind. apply kind_after_fresh_push; [exact HwG' |].
           now apply kind_after_fresh_push.
Qed.

Local Lemma dereferenced_definition_varkinds mode G Go e d D :
  ctx_ok G -> ctx_weakens G -> ctx_kdom v_ref G = dom e ->
  renv_idempotent e -> @renv_corr mode G e ->
  ty_def mode G Go e d D ->
  all_tfree_k_def G d v_ref ->
  def_varkinds G (deref e d).
Proof.
  intros Hok Hw Hdom Hid Henv Hty Hv.
  destruct Hty.
  - constructor.
  - assert (Ht : t \in dom e).
    {
      rewrite <- Hdom. destruct (Hv t (tfree_def_trm t a)) as [S [P Hb]].
      eapply kinded_binding_in_context; exact Hb.
    }
    destruct (get_some Ht) as [y Hy].
    change (def_varkinds G (def_fld a (deref e (avar_f t)))).
    rewrite (deref_bound_value Hid Hy). apply def_varkinds_fld.
    apply ctx_kind_domain_is_bound; try assumption.
    eapply reference_target_in_context; eassumption.
  - constructor. intros x Hfree.
    apply Hv. now apply tfree_def_met.
Qed.

Local Lemma dereferenced_definitions_varkinds mode G Go e ds T :
  ctx_ok G -> ctx_weakens G -> ctx_kdom v_ref G = dom e ->
  renv_idempotent e -> @renv_corr mode G e ->
  ty_defs mode G Go e ds T ->
  all_tfree_k_defs G ds v_ref ->
  defs_varkinds G (deref e ds).
Proof.
  intros Hok Hw Hdom Hid Henv Hty. induction Hty; intro Hv;
    unfold obj_dec_typing in *.
  - change (defs_varkinds G (defs_cons defs_nil (deref e d))).
    constructor; [constructor |].
    eapply dereferenced_definition_varkinds; try eassumption.
    intros x Hx. apply Hv. now apply tfree_defs_cons_r.
  - change (defs_varkinds G (defs_cons (deref e ds) (deref e d))).
    constructor.
    + apply IHHty; try assumption.
      intros x Hx. apply Hv. now apply tfree_defs_cons_l.
    + eapply dereferenced_definition_varkinds; try eassumption.
      intros x Hx. apply Hv. now apply tfree_defs_cons_r.
Qed.

Local Lemma typed_definition_makes_record_declaration mode G Go e d D :
  ty_def mode G Go e d D -> record_dec D.
Proof. intro H. destruct H; constructor. Qed.

Local Lemma record_type_labels_have_declarations T L l :
  record_typ T L -> l \in L -> exists D, label_of D = l /\ record_has T D.
Proof.
  intros H. induction H; intro Hin.
  - rewrite in_singleton in Hin. subst. exists D. split; [reflexivity | constructor].
  - rewrite in_union, in_singleton in Hin. destruct Hin as [Hin | ->].
    + destruct (IHrecord_typ Hin) as [E [Heq HE]].
      exists E. split; [exact Heq | now apply rh_andl].
    + exists D. split; [congruence | apply rh_andr, rh_one].
Qed.

Local Lemma defs_typing_makes_record_type mode G Go e ds T :
  ty_defs mode G Go e ds T -> record_type T.
Proof.
  intro H. induction H as [G Go e d D Hdec | G Go e ds d T D Hdefs IH Hdec Hnot];
    unfold obj_dec_typing in *.
  - exists \{label_of D}. apply rt_one; [eapply typed_definition_makes_record_declaration; eassumption | reflexivity].
  - destruct IH as [L Hrecord].
    exists (L \u \{label_of D}).
    apply rt_cons; [exact Hrecord | eapply typed_definition_makes_record_declaration; eassumption | reflexivity |].
    intro Hin.
    destruct (record_type_labels_have_declarations Hrecord Hin) as [E [Heq HE]].
    destruct (typed_record_member_exists Hdefs HE) as [d' [Hd' Hhas]].
    pose proof (definition_label_matches_typing Hdec) as Hd.
    unfold defs_has, defs_hasnt in *. rewrite Hd', Heq in Hhas. rewrite Hd, Hhas in Hnot.
    discriminate.
Qed.

Local Lemma ctx_typing_morphism_narrowed_push mode e G G' x vk S U :
  ctx_typing_morphism mode e G G' ->
  x \notin ctx_dom G ->
  subtyp mode G' objctx_empty e S U ->
  ctx_typing_morphism mode e (G § x / vk ~ U) (G' § x / vk ~ S).
Proof.
  intros [Hdom [Hbind Hvis]] Hfresh Hsub.
  assert (Hfresh' : x \notin ctx_dom G') by now rewrite <- Hdom.
  pose proof (@ctx_extends_with_fresh G' x vk S Hfresh') as [HW _].
  split; [cbn [ctx_dom]; now rewrite Hdom |]. split.
  - intros y T Hb. inversion Hb; subst.
    + eapply ty_var_sub with (T := S); unfold obj_typing, subtyping.
      * apply ty_var_var, ctx_binds_e.
      * eapply (proj1 (proj2 (types_under_binding_extension mode))).
        -- exact Hsub.
        -- split; auto.
    + eapply (proj1 (types_under_binding_extension mode)).
      * apply Hbind. eassumption.
      * split; auto.
  - intros y Hv. inversion Hv; subst; eauto using ctx_vis.
Qed.

Local Lemma remove_literal_self_override mode G e w S :
  ctx_vis G w ->
  ty_var mode G objctx_empty e w S ->
  ctx_typing_morphism mode e (G § w / v_self ~ S) G.
Proof.
  intros Hvis Hty. split.
  - apply fset_extens; intros x Hx.
    + cbn [ctx_dom] in Hx. rewrite in_union, in_singleton in Hx.
      destruct Hx as [-> | Hx]; [now apply vis_in_dom | exact Hx].
    + cbn [ctx_dom]. rewrite in_union. now right.
  - split.
    + intros x T Hb. inversion Hb; subst; [exact Hty |].
      apply ty_var_var. assumption.
    + intros x Hv. inversion Hv; subst; assumption.
Qed.

Local Lemma object_reference_open_type mode G e w R S :
  ctx_binds w (typ_objref R S) G ->
  typ_indep_b 0 R ->
  ty_var mode G objctx_empty e w (open w R).
Proof.
  intros Hbind Hind.
  apply ty_rec_elim; [|exact Hind]. unfold obj_typing.
  eapply ty_var_sub with (T := typ_objref R S); unfold obj_typing, subtyping.
  - now apply ty_var_var.
  - apply subtyp_and11.
Qed.

Local Lemma method_literal_body_to_heap mode G e w y R m body TC TZ TR :
  mode_has_mutability mode -> ctx_weakens G ->
  ctx_binds w (typ_objref R (typ_mut_marker typ_bot)) G ->
  typ_indep_b 0 R ->
  tyq_var e w y ->
  typ_indep_b 1 TC -> typ_indep_b 0 TZ -> typ_indep_b 2 TR ->
  ty_def mode G (objctx_lit w R) e body
    (dec_met m (open_rec 1 w TC) (open w TZ) (open_rec 2 w TR)) ->
  ty_def mode G (objctx_heap y R) e body
    (dec_met m (open_rec 1 y TC) (open y TZ) (open_rec 2 y TR)).
Proof.
  intros Hmut Hw Hbind HR Heq HC HZ HT Hder.
  inversion Hder; subst.
  match goal with H : forall z, z \notin _ -> forall c, c <> z -> _ |- _ =>
    rename H into Hbody end.
  assert (Hvis : mode_visibility' mode = mode_visibility_hide_method)
    by (destruct mode; cbn in *; congruence).
  assert (Hlit : ctx_typing_morphism mode e (G § w / v_self ~ open w R) G).
  {
    apply remove_literal_self_override.
    - eapply ctx_binds_visible; eassumption.
    - eapply object_reference_open_type; eassumption.
  }
  apply ctx_typing_morphism_hide in Hlit.
  eapply ty_def_met with (L := L \u ctx_dom G).
  intros z Hz c Hneq Hc.
  apply notin_union in Hz as [HzL HzG].
  apply notin_union in Hc as [HcL HcG].
  specialize (Hbody z HzL c Hneq HcL).
  unfold obj_typing in *.
  unfold ctx_obj_met in *. rewrite Hvis in *.
  assert (Hzy : ctx_typing_morphism mode e
    (ctx_hide (G § w / v_self ~ open w R) § z / v_par ~ open w TZ)
    (ctx_hide G § z / v_par ~ open y TZ)).
  {
    apply ctx_typing_morphism_narrowed_push; [exact Hlit | |].
    - cbn [ctx_dom]. rewrite notin_union, notin_singleton.
      split; [|exact HzG].
      intro E. subst z. apply HzG. eapply swap_calls_binding_in_context; eassumption.
    - apply equivalent_type_subtypes, opening_independent_type_with_alias;
        [now apply tyq_var_sym | exact HZ].
  }
  eapply ty_trm_sub; unfold obj_typing, subtyping.
  - eapply (proj1 (ctx_terms_under_morphism mode)); [exact Hbody | |apply objctx_self_fresh_empty].
    apply ctx_typing_morphism_narrowed_push; [exact Hzy | |].
    + cbn [ctx_dom]. rewrite !notin_union, !notin_singleton.
      split; [exact Hneq |]. split; [|exact HcG].
      intro E. subst c. apply HcG. eapply swap_calls_binding_in_context; eassumption.
    + apply equivalent_type_subtypes, type_alias_congr_is_equiv.
      apply type_alias_congr_and.
      * apply type_alias_congr_open.
        eapply independent_type_opens_with_alias; [now apply tyq_var_sym | exact HC | reflexivity].
      * apply type_alias_congr_and; [|apply type_alias_congr_id].
        eapply independent_type_opens_with_alias; [now apply tyq_var_sym | exact HR | reflexivity].
  - apply equivalent_type_subtypes, type_alias_congr_is_equiv, type_alias_congr_open, type_alias_congr_open.
    eapply independent_type_opens_with_alias; [exact Heq | exact HT | reflexivity].
Qed.

Local Lemma rename_freshly_opened_type (T : typ) k w y :
  w \notin fv T ->
  rename (subst_fvar w y) (open_rec k w T) = open_rec k y T.
Proof.
  intro Hfresh. rewrite rename_open_typ.
  assert (Hname : subst_fvar w y w = y) by (unfold subst_fvar; case_if; congruence).
  rewrite Hname. f_equal.
  apply (proj1 (rename_fixed_types (subst_fvar w y))).
  intros x Hx. unfold subst_fvar. case_if; congruence.
Qed.

Local Lemma equal_openings_change_fresh_name (S T : typ) k w y :
  w \notin fv S -> w \notin fv T ->
  open_rec k w S = open_rec k w T ->
  open_rec k y S = open_rec k y T.
Proof.
  intros Hs Ht Hopen.
  rewrite <- (@rename_freshly_opened_type S k w y Hs).
  rewrite <- (@rename_freshly_opened_type T k w y Ht).
  now rewrite Hopen.
Qed.

Local Lemma literal_definition_to_heap mode G e w y R d D :
  mode_has_mutability mode -> ctx_weakens G ->
  ctx_binds w (typ_objref R (typ_mut_marker typ_bot)) G ->
  typ_indep_b 0 R ->
  tyq_var e w y ->
  typ_indep_b 0 (typ_rcd D) ->
  w \notin fv D ->
  ty_def mode G (objctx_lit w R) e d (open w D) ->
  ty_def mode G (objctx_heap y R) e d (open y D).
Proof.
  intros Hmut Hw Hbind HR Heq Hind Hfresh Hty.
  destruct D as [A S T | a S T | m TC TZ TR].
  - change (ty_def mode G (objctx_lit w R) e d
      (dec_typ A (open_rec 1 w S) (open_rec 1 w T))) in Hty.
    change (ty_def mode G (objctx_heap y R) e d
      (dec_typ A (open_rec 1 y S) (open_rec 1 y T))).
    inversion Hind; subst; try discriminate;
      try solve [match goal with H : typ_nulary _ |- _ => inversion H end].
    inversion Hty; subst.
    assert (Hbounds : open_rec 1 y S = open_rec 1 y T).
    {
      eapply equal_openings_change_fresh_name with (w := w);
        try solve [change (w \notin fv S \u fv T) in Hfresh;
          rewrite notin_union in Hfresh; tauto | congruence].
    }
    rewrite <- Hbounds.
    eapply ty_def_typ with (L := L). intros x Hx. unfold typing_equiv in *.
    eapply type_equivalence_transitive.
    + match goal with H : forall z, z \notin L -> tyq_typ _ _ _ |- _ =>
        pose proof (H x Hx) as Hopen; exact Hopen
      end.
    + apply type_alias_congr_is_equiv, type_alias_congr_open.
      eapply independent_type_opens_with_alias; eassumption || reflexivity.
  - change (ty_def mode G (objctx_lit w R) e d
      (dec_fld a (open w S) (open w T))) in Hty.
    change (ty_def mode G (objctx_heap y R) e d
      (dec_fld a (open y S) (open y T))).
    inversion Hind; subst; try discriminate;
      try solve [match goal with H : typ_nulary _ |- _ => inversion H end].
    inversion Hty; subst.
    assert (Hbounds : open_rec 0 y S = open_rec 0 y T).
    {
      eapply equal_openings_change_fresh_name with (w := w);
        try solve [change (w \notin fv S \u fv T) in Hfresh;
          rewrite notin_union in Hfresh; tauto | congruence].
    }
    rewrite <- Hbounds.
    assert (Hlit : ctx_typing_morphism mode e (G § w / v_self ~ open w R) G).
    {
      apply remove_literal_self_override.
      - eapply ctx_binds_visible; eassumption.
      - eapply object_reference_open_type; eassumption.
    }
    apply ty_def_fld; cbn [ctx_obj] in *; unfold obj_typing.
    + intros Hmode. apply (proj2 (proj2 Hlit)); auto.
    + eapply ty_var_sub with (T := open w S); unfold obj_typing, subtyping.
      * eapply (proj1 (ctx_types_under_morphism mode)); eassumption.
      * apply equivalent_type_subtypes, opening_independent_type_with_alias; assumption.
  - inversion Hind; subst; try discriminate;
      try solve [match goal with H : typ_nulary _ |- _ => inversion H end].
    eapply method_literal_body_to_heap; eassumption.
Qed.

Local Lemma literal_definitions_to_heap mode G e w y R ds U :
  mode_has_mutability mode -> ctx_weakens G ->
  ctx_binds w (typ_objref R (typ_mut_marker typ_bot)) G ->
  typ_indep_b 0 R ->
  tyq_var e w y ->
  typ_indep_b 0 U ->
  w \notin fv U ->
  ty_defs mode G (objctx_lit w R) e ds (open w U) ->
  ty_defs mode G (objctx_heap y R) e ds (open y U).
Proof.
  intros Hmut Hw Hbind HR Heq Hind Hfresh Hty.
  remember (objctx_lit w R) as Go eqn:HGo in Hty.
  remember (open w U) as V eqn:HV in Hty.
  revert U Hind Hfresh HV.
  induction Hty as [G Go e d D Hdec | G Go e ds d T D Hdefs IH Hdec Habs];
    intros U Hind Hfresh HV; subst Go; unfold obj_dec_typing in *.
  - destruct U; try discriminate.
    change (typ_rcd D = typ_rcd (open w d0)) in HV. inversion HV; subst.
    apply ty_defs_one. unfold obj_dec_typing.
    eapply literal_definition_to_heap; eassumption.
  - destruct U as [| |D'|U1 U2| | | | |]; try discriminate.
    change (typ_and T (typ_rcd D) = typ_and (open w U1) (open w U2)) in HV.
    inversion HV; subst T.
    destruct U2 as [| |D'| | | | | |]; try discriminate.
    match goal with H : typ_rcd D = _ |- _ =>
      change (typ_rcd D = typ_rcd (open w D')) in H; inversion H; subst D
    end.
    inversion Hind; subst; try solve [match goal with H : typ_nulary _ |- _ => inversion H end].
    change (w \notin fv U1 \u fv D') in Hfresh.
    apply notin_union in Hfresh as [Hfresh1 Hfresh2].
    change (ty_defs mode G (objctx_heap y R) e (defs_cons ds d)
      (typ_and (open y U1) (typ_rcd (open y D')))).
    apply ty_defs_cons; unfold obj_typing, obj_dec_typing.
    + eapply IH; eassumption || reflexivity.
    + eapply literal_definition_to_heap; eassumption.
    + assumption.
Qed.

Local Lemma close_fresh_open_type_def :
  (forall T k d w, w \notin fv T ->
    transform_typ (close_depth_rec k w) (open_rec_typ (k + d) w T) d = T) /\
  (forall D k d w, w \notin fv D ->
    transform_dec (close_depth_rec k w) (open_rec_dec (k + d) w D) d = D).
Proof.
  assert (Hname : forall (a : avar) k d w, w \notin fv a ->
    close_depth_rec k w (open_rec (k+d) w a) d = a).
  {
    intros [n | x] k d w Hfresh.
    - destruct (classic (n = k+d)) as [-> | Hneq].
      + rewrite open_avar_equal.
        unfold close_depth_rec, close_rec, AvarClosing. case_if; congruence.
      + rewrite open_avar_unchanged by congruence. reflexivity.
    - change (w \notin \{x}) in Hfresh. rewrite notin_singleton in Hfresh.
      unfold close_depth_rec, close_rec, open_rec, AvarClosing, AvarOpenable.
      case_if; congruence.
  }
  apply typ_mutind; intros;
    cbn [open_rec_typ open_rec_dec transform_typ transform_dec fv TypFreeVar DecFreeVar fv_typ fv_dec] in *;
    fold open_rec_typ open_rec_dec transform_typ transform_dec;
    try reflexivity;
    repeat rewrite notin_union in *; f_equal;
    try rewrite <- !Nat.add_succ_r;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; eauto using Hname.
Qed.

Local Lemma fresh_open_type_injective k x (S T : typ) :
  x \notin fv S -> x \notin fv T ->
  open_rec k x S = open_rec k x T -> S = T.
Proof.
  intros HS HT Hopen.
  destruct close_fresh_open_type_def as [HC _].
  specialize (HC S k 0 x HS) as HCS.
  specialize (proj1 close_fresh_open_type_def T k 0 x HT) as HCT.
  rewrite !Nat.add_0_r in HCS, HCT.
  change (open_rec_typ k x S = open_rec_typ k x T) in Hopen.
  rewrite Hopen, HCT in HCS. symmetry. exact HCS.
Qed.

Local Lemma opening_reflects_record_dec w D :
  w \notin fv D -> record_dec (open w D) -> record_dec D.
Proof.
  intros Hfresh Hrec. destruct D as [A S T | a S T | m C Z R].
  - change (record_dec (dec_typ A (open_rec 1 w S) (open_rec 1 w T))) in Hrec.
    change (w \notin fv S \u fv T) in Hfresh.
    apply notin_union in Hfresh as [HS HT].
    inversion Hrec; subst.
    + assert (S = T) by (eapply fresh_open_type_injective with (k := 1) (x := w);
        try assumption; congruence).
      subst. constructor.
    + assert (S = typ_bot).
      {
        eapply fresh_open_type_injective with (k := 1) (x := w); try assumption;
          [change (w \notin \{}); apply notin_empty | change (open_rec 1 w S = typ_bot); congruence].
      }
      subst. apply rd_typb.
  - change (record_dec (dec_fld a (open w S) (open w T))) in Hrec.
    change (w \notin fv S \u fv T) in Hfresh.
    apply notin_union in Hfresh as [HS HT].
    inversion Hrec; subst.
    assert (S = T) by (eapply fresh_open_type_injective with (k := 0) (x := w);
      try assumption; congruence).
    subst. constructor.
  - constructor.
Qed.

Local Lemma opening_keeps_record_label w (D : dec) : label_of (open w D) = label_of D.
Proof. destruct D; reflexivity. Qed.

Local Lemma opening_reflects_record_type w T L :
  w \notin fv T -> record_typ (open w T) L -> record_typ T L.
Proof.
  intros Hfresh Hrec.
  remember (open w T) as U eqn:HU in Hrec.
  revert T Hfresh HU.
  induction Hrec as [D l Hdec Hl | U ls D l Hrecord IH Hdec Hl Hunique];
    intros T Hfresh HU.
  - destruct T; try discriminate.
    change (typ_rcd D = typ_rcd (open w d)) in HU.
    inversion HU; subst. rewrite ?opening_keeps_record_label in *.
    apply rt_one; [eapply opening_reflects_record_dec; eassumption | reflexivity].
  - destruct T as [| |D'|T1 T2| | | | |]; try discriminate.
    change (typ_and U (typ_rcd D) = typ_and (open w T1) (open w T2)) in HU.
    inversion HU; subst.
    destruct T2 as [| |D'| | | | | |]; try discriminate.
    match goal with H : typ_rcd D = _ |- _ =>
      change (typ_rcd D = typ_rcd (open w D')) in H; inversion H; subst D
    end.
    change (w \notin fv T1 \u fv D') in Hfresh.
    apply notin_union in Hfresh as [HfreshLeft HfreshRight].
    rewrite ?opening_keeps_record_label in *.
    eapply rt_cons; [apply IH; [assumption | reflexivity] | eapply opening_reflects_record_dec; eassumption |
      reflexivity | exact Hunique].
Qed.
Local Lemma open_avar_free_origin k w a x :
  open_rec k w a = avar_f x -> a = avar_f x \/ x = w.
Proof.
  destruct a; cbn [open_rec AvarOpenable].
  - case_if; intuition congruence.
  - intuition.
Qed.

Local Lemma opened_term_free_variable_origin :
  (forall t k w x, tfree_trm x (open_rec k w t) -> tfree_trm x t \/ x = w) /\
  (forall l k w x, tfree_lit x (open_rec k w l) -> tfree_lit x l \/ x = w) /\
  (forall d k w x, tfree_def x (open_rec k w d) -> tfree_def x d \/ x = w) /\
  (forall ds k w x, tfree_defs x (open_rec k w ds) -> tfree_defs x ds \/ x = w).
Proof.
  apply trm_mutind; intros.
  all: match goal with H : tfree_trm _ _ |- _ => inversion H; subst
     | H : tfree_lit _ _ |- _ => inversion H; subst
     | H : tfree_def _ _ |- _ => inversion H; subst
     | H : tfree_defs _ _ |- _ => inversion H; subst end.
  all: repeat match goal with HE : avar_f ?x = open_rec ?k ?w ?a |- _ =>
    destruct (@open_avar_free_origin k w a x (eq_sym HE)) as [-> | ->]; clear HE
    end.
  all: try solve [right; reflexivity | left; constructor].
  all: match goal with
  | IH : forall k w x, tfree_trm x (open_rec k w ?t) -> _,
    HF : tfree_trm ?x (open_rec_trm ?k ?w ?t) |- _ => specialize (IH k w x HF)
  | IH : forall k w x, tfree_lit x (open_rec k w ?t) -> _,
    HF : tfree_lit ?x (open_rec_lit ?k ?w ?t) |- _ => specialize (IH k w x HF)
  | IH : forall k w x, tfree_def x (open_rec k w ?t) -> _,
    HF : tfree_def ?x (open_rec_def ?k ?w ?t) |- _ => specialize (IH k w x HF)
  | IH : forall k w x, tfree_defs x (open_rec k w ?t) -> _,
    HF : tfree_defs ?x (open_rec_defs ?k ?w ?t) |- _ => specialize (IH k w x HF)
  end.
  all: intuition eauto using tfree_trm, tfree_lit, tfree_def, tfree_defs.
Qed.

Local Lemma term_openings_commute :
  (forall (t : trm) k l x y, k <> l -> open_rec k x (open_rec l y t) = open_rec l y (open_rec k x t)) /\
  (forall v : lit, forall k l x y, k <> l -> open_rec k x (open_rec l y v) = open_rec l y (open_rec k x v)) /\
  (forall d : def, forall k l x y, k <> l -> open_rec k x (open_rec l y d) = open_rec l y (open_rec k x d)) /\
  (forall ds : defs, forall k l x y, k <> l -> open_rec k x (open_rec l y ds) = open_rec l y (open_rec k x ds)).
Proof.
  assert (Havar : forall (a : avar) k l x y,
    k <> l -> open_rec k x (open_rec l y a) = open_rec l y (open_rec k x a)).
  { intros [n | v] k l x y Hkl; repeat (cbn [open_rec AvarOpenable]; case_if); cbn [open_rec AvarOpenable]; congruence. }
  assert (Hty :
    (forall T : typ, forall k l x y,
      k <> l -> open_rec k x (open_rec l y T) = open_rec l y (open_rec k x T)) /\
    (forall D : dec, forall k l x y,
      k <> l -> open_rec k x (open_rec l y D) = open_rec l y (open_rec k x D))).
  {
    apply typ_mutind; intros;
      unfold open_rec, TypOpenable, DecOpenable in *;
      cbn [open_rec_typ open_rec_dec]; fold open_rec_typ open_rec_dec;
      f_equal; eauto using Nat.succ_inj_wd.
  }
  destruct Hty as [HT HD]. apply trm_mutind; intros.
  all: unfold open_rec, TrmOpenable, LitOpenable, DefOpenable, DefsOpenable,
    TypOpenable, DecOpenable in *.
  all: cbn [open_rec_trm open_rec_lit open_rec_def open_rec_defs];
    fold open_rec_trm open_rec_lit open_rec_def open_rec_defs open_rec_typ open_rec_dec;
    f_equal; eauto using Nat.succ_inj_wd.
Qed.

Local Lemma term_opening_idempotent :
  (forall (t : trm) k x y, open_rec k x (open_rec k y t) = open_rec k y t) /\
  (forall v : lit, forall k x y, open_rec k x (open_rec k y v) = open_rec k y v) /\
  (forall d : def, forall k x y, open_rec k x (open_rec k y d) = open_rec k y d) /\
  (forall ds : defs, forall k x y, open_rec k x (open_rec k y ds) = open_rec k y ds).
Proof.
  assert (Havar : forall (a : avar) k x y,
    open_rec k x (open_rec k y a) = open_rec k y a).
  { intros [n | v] k x y; repeat (cbn [open_rec AvarOpenable]; case_if); cbn [open_rec AvarOpenable]; congruence. }
  assert (Hty :
    (forall T : typ, forall k x y,
      open_rec k x (open_rec k y T) = open_rec k y T) /\
    (forall D : dec, forall k x y,
      open_rec k x (open_rec k y D) = open_rec k y D)).
  {
    apply typ_mutind; intros;
      unfold open_rec, TypOpenable, DecOpenable in *;
      cbn [open_rec_typ open_rec_dec]; fold open_rec_typ open_rec_dec;
      f_equal; eauto.
  }
  destruct Hty as [HT HD]. apply trm_mutind; intros.
  all: unfold open_rec, TrmOpenable, LitOpenable, DefOpenable, DefsOpenable,
    TypOpenable, DecOpenable in *.
  all: cbn [open_rec_trm open_rec_lit open_rec_def open_rec_defs];
    fold open_rec_trm open_rec_lit open_rec_def open_rec_defs open_rec_typ open_rec_dec;
    f_equal; eauto.
Qed.

Local Lemma opening_closed_let_body u w :
  (forall k x, open_rec (S k) x u = u) ->
  closed (open w u : trm).
Proof.
  intros Hu [|k] x.
  - apply (proj1 term_opening_idempotent).
  - rewrite (proj1 term_openings_commute) by discriminate.
    now rewrite Hu.
Qed.

Local Lemma opening_closed_object_definitions ds w :
  (forall k x, open_rec (S k) x ds = ds) ->
  closed (open w ds : defs).
Proof.
  intros Hds [|k] x.
  - apply (proj2 (proj2 (proj2 term_opening_idempotent))).
  - rewrite (proj2 (proj2 (proj2 term_openings_commute))) by discriminate.
    now rewrite Hds.
Qed.

Local Lemma allocated_object_body_closed R ds u w :
  closed (trm_lit (lit_obj R ds) u) ->
  closed (open w ds) /\ closed (open w u).
Proof.
  intro Hcl. split.
  - apply opening_closed_object_definitions. intros k x.
    specialize (Hcl k x).
    change (trm_lit (lit_obj (open_rec (S k) x R) (open_rec (S k) x ds))
      (open_rec (S k) x u) = trm_lit (lit_obj R ds) u) in Hcl.
    congruence.
  - apply opening_closed_let_body. intros k x.
    specialize (Hcl k x).
    change (trm_lit (open_rec k x (lit_obj R ds)) (open_rec (S k) x u) =
      trm_lit (lit_obj R ds) u) in Hcl.
    congruence.
Qed.

Local Lemma deref_free_avar_is_free e w :
  exists y, deref e (avar_f w) = avar_f y.
Proof.
  revert w. induction e using env_ind; intro w.
  - exists w. unfold deref, deref_avar. rewrite empty_def. reflexivity.
  - unfold deref, deref_avar. rewrite replay_deref_base_push.
    change (exists y, deref e (subst_var x v (avar_f w)) = avar_f y).
    cbn [subst_var AvarSubstVar]. apply IHe.
Qed.

Local Lemma dereferenced_definition_closed e (d : def) :
  closed d -> closed (deref e d).
Proof.
  intro H. destruct d as [l T | l a | l t]; [exact H | |exact H].
  destruct a as [n | w].
  - assert (Hvar : forall x, avar_f x = avar_b n).
    {
      intro x. specialize (H n x).
      change (def_fld l (open_rec n x (avar_b n)) = def_fld l (avar_b n)) in H.
      injection H as H. unfold open_rec, AvarOpenable in H. case_if; congruence.
    }
    destruct (var_fresh \{}) as [x Hx]. specialize (Hvar x). discriminate.
  - destruct (deref_free_avar_is_free e w) as [y Hy].
    change (closed (def_fld l (deref e (avar_f w)))). rewrite Hy.
    intros k x. reflexivity.
Qed.

Local Lemma dereferenced_definitions_closed e (ds : defs) : closed ds -> closed (deref e ds).
Proof.
  induction ds as [| ds IH d]; intro H; [intros k x; reflexivity |].
  assert (Hds : closed ds).
  {
    intros k x. specialize (H k x).
    change (defs_cons (open_rec k x ds) (open_rec k x d) = defs_cons ds d) in H.
    congruence.
  }
  assert (Hd : closed d).
  {
    intros k x. specialize (H k x).
    change (defs_cons (open_rec k x ds) (open_rec k x d) = defs_cons ds d) in H.
    congruence.
  }
  assert (Hds' := IH Hds).
  assert (Hd' := dereferenced_definition_closed e Hd).
  intros k x.
  change (defs_cons (open_rec k x (deref e ds)) (open_rec k x (deref e d)) =
    defs_cons (deref e ds) (deref e d)).
  now rewrite Hds', Hd'.
Qed.

Local Lemma seal_if_all_higher_openings_are_fixed :
  (forall (T : typ) d, (forall k a, open_rec (d + k) a T = T) ->
    forall y, seal_rec d y T = T) /\
  (forall (D : dec) d, (forall k a, open_rec (d + k) a D = D) ->
    forall y, seal_rec d y D = D).
Proof.
  assert (Ha : forall (v : avar) d, (forall k a, open_rec (d+k) a v = v) ->
    forall y, seal_rec d y v = v).
  {
    intros [n | x] d H y; [|reflexivity].
    unfold seal_rec, AvarSealable. case_if; [|reflexivity].
    specialize (H (n-d) y). replace (d + (n-d)) with n in H by lia.
    unfold open_rec, AvarOpenable in H. case_if; congruence.
  }
  apply typ_mutind; intros;
    match goal with H : forall k a, open_rec (_ + k) a _ = _ |- _ => rename H into Hfixed end.
  all: unfold seal_rec, TypSealable, DecSealable.
  all: cbn [seal_rec_typ seal_rec_dec]; fold seal_rec_typ seal_rec_dec.
  all: try reflexivity; f_equal.
  all: match goal with
    | IH : forall d, (forall k a, open_rec (d + k) a ?T = ?T) ->
        forall y, seal_rec d y ?T = ?T
       |- seal_rec_typ ?d ?y ?T = ?T => apply (IH d)
    | IH : forall d, (forall k a, open_rec (d + k) a ?D = ?D) ->
        forall y, seal_rec d y ?D = ?D
       |- seal_rec_dec ?d ?y ?D = ?D => apply (IH d)
    | |- seal_rec ?d ?y ?a = ?a => apply Ha
    end.
  all: intros k z; pose proof (Hfixed k z) as Hs;
    unfold open_rec, TypOpenable, DecOpenable in Hs;
    cbn [open_rec_typ open_rec_dec] in Hs;
    fold open_rec_typ open_rec_dec in Hs;
    rewrite ?Nat.add_succ_l; injection Hs; auto.
Qed.

Local Lemma closed_type_is_sealed (T : typ) : closed T -> sealed T.
Proof.
  intros H y. exact ((proj1 seal_if_all_higher_openings_are_fixed) T 0 H y).
Qed.

Local Lemma closed_object_type_binder R ds u :
  closed (trm_lit (lit_obj R ds) u) -> closed (typ_bnd R).
Proof.
  intros H k x. specialize (H k x).
  change (trm_lit (lit_obj (open_rec (S k) x R) (open_rec (S k) x ds)) (open_rec (S k) x u) =
    trm_lit (lit_obj R ds) u) in H.
  change (typ_bnd (open_rec (S k) x R) = typ_bnd R).
  congruence.
Qed.

Local Lemma allocated_object_heap_is_typed mode G e h y w R ds :
  let A := typ_objref_loc mode R in
  let G' := inert_G_for_item G w y A in
  let e' := e & w ~ y in
  mode_has_mutability mode -> mode_has_sef mode ->
  heap_correspond (typing_mode := mode) G e h ->
  y \notin ctx_dom G -> w \notin ctx_dom G -> w <> y ->
  typ_indep_b 0 R -> w \notin fv R ->
  ty_defs mode G (objctx_lit w R) e (open w ds) (open w R) ->
  all_tfree_k_defs G ds v_ref ->
  heap_correspond (typing_mode := mode) G' e'
    (heap_with_obj_dereffed h e w y ds).
Proof.
  cbv zeta.
  intros Hmut Hsef Hh Hy Hw Hneq HR HwR Hliteral Hfv.
  pose proof Hh as [Hok [Hweak [Hokh [Hoke [Hloc [Href [Hcorr Hitems]]]]]]].
  set (A := typ_objref_loc mode R) in *.
  set (G' := inert_G_for_item G w y A).
  set (e' := e & w ~ y).
  assert (HA : A = typ_objref R (typ_mut_marker typ_bot))
    by (subst A; destruct mode; cbn in *; try discriminate; reflexivity).
  assert (Hmode : mode_incap' mode = mode_incap_nocap)
    by (destruct mode; cbn in *; congruence).
  assert (Hw' : w \notin ctx_dom (G § y / v_loc ~ A)).
  { cbn [ctx_dom]. rewrite notin_union, notin_singleton. auto. }
  assert (Hwenv : w # e).
  { rewrite <- Href. intro Hdom. apply Hw.
    eapply ctx_kind_domain_is_in_domain; exact Hdom. }
  assert (Hok' : ctx_ok G') by (apply ctx_ok_push; [now apply ctx_ok_push | exact Hw']).
  assert (Hweak' : ctx_weakens G') by now do 2 constructor.
  assert (Hoke' : ok e') by now apply ok_push.
  assert (Href' : ctx_kdom v_ref G' = dom e').
  {
    unfold G', e'. cbn [ctx_kdom]. repeat case_if; try congruence.
    now rewrite Href, dom_push, union_comm.
  }
  assert (Hcorr' : @renv_corr mode G' e').
  {
    eapply renv_corr_ref; [apply ctx_binds_k_e | apply ctx_binds_k_e | |].
    - rewrite HA. apply typ_corr_obj. destruct mode; cbn in *; try discriminate.
      all: exists typ_bot; auto.
    - apply renv_corr_under_fresh_binding; [|exact Hw'].
      exact (@renv_corr_under_fresh_binding mode G e y v_loc A Hcorr Hy).
  }
  assert (Hidem' : renv_idempotent e') by (eapply corresponding_renv_idempotent; eassumption).
  assert (Hext : ctx_extends G G').
  {
    destruct (@ctx_extends_with_fresh G y v_loc A Hy) as [Hb1 Hv1].
    destruct (@ctx_extends_with_fresh (G § y / v_loc ~ A) w v_ref A Hw') as [Hb2 Hv2].
    split; [intros x P Hx; exact (Hb2 _ _ (Hb1 _ _ Hx)) |
      intros x Hx; exact (Hv2 _ (Hv1 _ Hx))].
  }
  assert (Hdefs : ty_defs mode G' (objctx_heap y R) e' (open w ds) (open y R)).
  {
    eapply (@literal_definitions_to_heap mode G' e' w y R (open w ds) R); try assumption.
    - rewrite <- HA. apply ctx_binds_e.
    - apply tyq_var_binds, binds_push_eq.
    - eapply (proj2 (proj2 (proj2 (terms_under_renv_extension mode))));
        [|now apply fresh_ref_extension_keeps_bindings].
      eapply (proj2 (proj2 (proj2 (ctx_extends_terms mode)))); eassumption.
  }
  eapply (@allocated_heap_correspondence mode G e h w y R (deref e' (open w ds)));
    try eassumption.
  - eapply typed_heap_defs_after_deref; eassumption.
  - eapply dereferenced_definitions_varkinds; try eassumption.
    intros x Hx.
    destruct ((proj2 (proj2 (proj2 opened_term_free_variable_origin))) _ _ _ _ Hx)
      as [Horiginal | ->].
    + apply kind_after_fresh_push; [exact Hw' |].
      apply kind_after_fresh_push; [exact Hy | exact (Hfv _ Horiginal)].
    + exists A, (G § y / v_loc ~ A). apply ctx_binds_k_e.
Qed.

Local Lemma object_let_annotation mode G e R ds u U :
  ty_trm mode G objctx_empty e (trm_lit (lit_obj R ds) u) U ->
  typ_indep_b 0 R /\ exists L,
  forall w, w \notin L ->
    ty_defs mode G (objctx_lit w R) e (open w ds) (open w R).
Proof.
  intro H. remember (trm_lit (lit_obj R ds) u) as t eqn:Ht.
  induction H; try discriminate; unfold obj_typing in *.
  - inversion Ht; subst. inversion H; subst. split; [assumption | eauto].
  - auto.
Qed.

Local Lemma fresh_added_object_fv mode G w y R :
  ctx_fv (inert_G_for_obj_loc mode G w y R) \c fv R \u ctx_fv G.
Proof.
  intros x Hx. destruct mode; cbn [mode_refcaps' ctx_collect_values fv
    TypFreeVar fv_typ fv_dec] in Hx;
    repeat rewrite in_union in *; rewrite ?in_empty in *; tauto.
Qed.

Local Lemma object_allocation_has_typed_successor mode G e R ds u fs h Lv T :
  mode_has_mutability mode -> mode_has_sef mode ->
  @ty_config mode G (config_mk (trm_lit (lit_obj R ds) u) fs h e Lv) T ->
  exists G' C', typed_red mode G (config_mk (trm_lit (lit_obj R ds) u) fs h e Lv) T G' C' /\
    @ty_config mode G' C' T.
Proof.
  intros Hmut Hsef Htype.
  set (C := config_mk (trm_lit (lit_obj R ds) u) fs h e Lv) in *.
  inversion Htype as [G0 e0 s0 h0 Lv0 t0 U T0 Hin Hheap Hstack Hstk Hterm Hfree Hscoped Hnull Hseal Hclosed HT]; subst.
  unfold obj_typing in Hterm.
  destruct (object_let_annotation Hterm) as [HR [L Hdef]].
  destruct (@allocated_control_typing_avoiding mode G e R ds u fs h Lv T L Htype)
    as [y [w [V [_ [HwL [Hfresh [Hyfv [Hwfv [Hstep [Hterm' Hstack']]]]]]]]]].
  cbv zeta in Hstep, Hterm', Hstack'.
  set (A := typ_objref_loc mode R) in *.
  set (G' := inert_G_for_item G w y A) in *.
  set (e' := e & w ~ y) in *.
  set (o := deref (e & w ~ y) (open w ds) : defs).
  set (C' := config_mk (open w u) fs (h & y ~ item_obj o) e' (fv_config C)).
  exists G', C'. split; [exact Hstep |].
  cbn [fresh length] in Hfresh. destruct Hfresh as [HyC [HwC _]].
  apply notin_union in HwC as [HwC Hneq].
  apply notin_singleton in Hneq.
  assert (HyG : y \notin ctx_dom G)
    by (intro Hd; apply HyC; exact (proj1 (proj1 Hscoped) _ Hd)).
  assert (HwG : w \notin ctx_dom G)
    by (intro Hd; apply HwC; exact (proj1 (proj1 Hscoped) _ Hd)).
  assert (HyR : y \notin fv R) by
    (match goal with H : y \notin ctx_fv G \u fv R |- _ => now apply notin_union in H as [_ H] end).
  assert (HwR : w \notin fv R) by
    (match goal with H : w \notin ctx_fv G \u fv R |- _ => now apply notin_union in H as [_ H] end).
  assert (Hyctx : y \notin ctx_fv G) by
    (match goal with H : y \notin ctx_fv G \u fv R |- _ => now apply notin_union in H as [H _] end).
  assert (Hwctx : w \notin ctx_fv G) by
    (match goal with H : w \notin ctx_fv G \u fv R |- _ => now apply notin_union in H as [H _] end).
  assert (HwG' : w \notin ctx_dom (G § y / v_loc ~ A)).
  { cbn [ctx_dom]. rewrite notin_union, notin_singleton. auto. }
  assert (HAfv : fv A = fv R).
  { subst A. destruct mode; cbn [mode_refcaps' fv TypFreeVar fv_typ fv_dec];
      rewrite ?union_empty_r, ?union_empty_l; reflexivity. }
  assert (HFV : ctx_fv (G § y / v_loc ~ A) = fv R \u ctx_fv G) by (cbn [ctx_collect_values]; now rewrite HAfv).
  assert (Hrecord : record_type R).
  {
    destruct (defs_typing_makes_record_type (Hdef w HwL)) as [Ls Hrec].
    exists Ls. eapply opening_reflects_record_type; eassumption.
  }
  assert (Hkind : forall x k, ctx_k G x k -> ctx_k G' x k).
  { intros x k Hx. apply kind_after_fresh_push; [exact HwG' |].
    now apply kind_after_fresh_push. }
  assert (HfvR : fv R \c fv_config C).
  {
    intros x Hx. unfold C. cbn [fv TrmFreeVar LitFreeVar fv_trm fv_lit].
    repeat rewrite in_union. tauto.
  }
  assert (HoldVars : fv_config C \c fv_config C').
  { intros x Hx. unfold C'. repeat rewrite in_union. auto 9. }
  assert (Hneww : w \in fv_config C').
  { unfold C', e'. apply dom_env_in_machine_fv. rewrite dom_push, in_union, in_singleton. auto. }
  assert (Hnewy : y \in fv_config C').
  { unfold C'. apply dom_heap_in_machine_fv. rewrite dom_push, in_union, in_singleton. auto. }
  eapply ty_config_c with (T := V); try assumption.
  - unfold G'. apply inert_push.
    + apply inert_push; try assumption; [constructor | | now rewrite HAfv].
      unfold A. destruct mode; cbn in *; try discriminate;
        apply inert_typ_obj; try assumption; constructor.
    + constructor.
    + unfold A. destruct mode; cbn in *; try discriminate;
        apply inert_typ_obj; try assumption; constructor.
    + exact HwG'.
    + rewrite HFV, notin_union. auto.
    + now rewrite HAfv.
  - eapply (@allocated_object_heap_is_typed mode G e h y w R ds); try eassumption.
    1: exact (Hdef w HwL).
    intros x Hx. apply Hfree, tfree_trm_lit_l, tfree_lit_obj. exact Hx.
  - intros x Hx. apply Hkind. now apply Hstk.
  - intros x Hx.
    destruct ((proj1 opened_term_free_variable_origin) u 0 w x Hx) as [Horig | ->].
    + apply Hkind, Hfree. now apply tfree_trm_lit_r.
    + exists A, (G § y / v_loc ~ A). constructor.
  - destruct Hscoped as [[Hdom Hfv] HTfv]. split; [split |].
    + intros x Hx. unfold G' in Hx. cbn [ctx_dom] in Hx.
      rewrite !in_union, !in_singleton in Hx.
      destruct Hx as [-> | [-> | Hx]]; auto.
    + intros x Hx.
      pose proof (@fresh_added_object_fv mode G w y R x Hx) as Hmember.
      rewrite in_union in Hmember.
      apply HoldVars. destruct Hmember as [HRx | HGx]; [exact (HfvR x HRx) | exact (Hfv x HGx)].
    + intros x Hx. apply HoldVars. now apply HTfv.
  - destruct Hnull as [x Hx]. exists x. unfold C. repeat rewrite in_union. auto 12.
  - inversion Hclosed; subst.
    assert (HA : sealed A).
    {
      apply closed_type_is_sealed.
      match goal with Hcl : closed (trm_lit (lit_obj _ _) _) |- _ =>
        pose proof (closed_object_type_binder Hcl) as HB end.
      intros k x. unfold A. destruct (mode_refcaps' mode).
      - change (typ_and (open_rec k x (typ_bnd R)) typ_top = typ_and (typ_bnd R) typ_top).
        now rewrite HB.
      - change (typ_and (open_rec k x (typ_bnd R)) (typ_mut_marker typ_bot) =
          typ_objref R (typ_mut_marker typ_bot)).
        now rewrite HB.
    }
    intros x. unfold G'.
    change (seal x G § y / v_loc ~ seal x A § w / v_ref ~ seal x A =
      G § y / v_loc ~ A § w / v_ref ~ A).
    now rewrite (Hseal x), (HA x).
  - inversion Hclosed; subst.
    match goal with Hcl : closed (trm_lit (lit_obj _ _) _) |- _ =>
      destruct (allocated_object_body_closed w Hcl) as [Hd Hu] end.
    constructor; try assumption.
    apply heap_closed_push; [assumption |].
    intros k x. change (item_obj (open_rec k x o) = item_obj o).
    f_equal. unfold o. now apply dereferenced_definitions_closed.
Qed.


(* The target of a substitution may already be in scope. *)

Local Definition names_agree_on (f g : var -> var) (S : vars) :=
  forall x, x \in S -> f x = g x.

Local Lemma names_agree_types f g :
  (forall T d, names_agree_on f g (fv T) ->
   transform_typ (avar_map f) T d = transform_typ (avar_map g) T d) /\
  (forall D d, names_agree_on f g (fv D) ->
   transform_dec (avar_map f) D d = transform_dec (avar_map g) D d).
Proof.
  assert (Hname : forall (a : avar) d, names_agree_on f g (fv a) ->
    avar_map f a d = avar_map g a d).
  {
    intros [i | x] d H; [reflexivity |]. cbn [avar_map rename_avar]. f_equal.
    apply H. change (x \in \{x}). now rewrite in_singleton.
  }
  apply typ_mutind; intros; cbn [transform_typ transform_dec]; try reflexivity;
    f_equal.
  all: match goal with
  | HA : names_agree_on _ _ _ |- _ =>
    first [apply Hname | solve [eauto] |
      match goal with IH : forall d, names_agree_on _ _ _ -> _ |- _ => apply IH end];
    intros x Hx; apply HA; cbn [fv TypFreeVar DecFreeVar fv_typ fv_dec];
    repeat rewrite in_union; auto 10
  end.
Qed.

Local Lemma names_agree_terms f g :
  (forall t d, names_agree_on f g (fv t) ->
    transform_trm (avar_map f) t d = transform_trm (avar_map g) t d) /\
  (forall l d, names_agree_on f g (fv l) ->
    transform_lit (avar_map f) l d = transform_lit (avar_map g) l d) /\
  (forall d k, names_agree_on f g (fv d) ->
    transform_def (avar_map f) d k = transform_def (avar_map g) d k) /\
  (forall ds d, names_agree_on f g (fv ds) ->
    transform_defs (avar_map f) ds d = transform_defs (avar_map g) ds d).
Proof.
  destruct (names_agree_types f g) as [HT HD].
  assert (Hname : forall (a : avar) d, names_agree_on f g (fv a) ->
    avar_map f a d = avar_map g a d).
  {
    intros [i | x] d H; [reflexivity |]. cbn [avar_map rename_avar]. f_equal.
    apply H. change (x \in \{x}). now rewrite in_singleton.
  }
  apply trm_mutind; intros; cbn [transform_trm transform_lit transform_def transform_defs];
    try reflexivity; f_equal.
  all: match goal with
  | HA : names_agree_on _ _ _ |- _ =>
    first [apply Hname | apply HT | apply HD |
      match goal with IH : forall d, names_agree_on _ _ _ -> _ |- _ => apply IH end];
    intros x Hx; apply HA; cbn [fv TrmFreeVar LitFreeVar DefFreeVar DefsFreeVar
      fv_trm fv_lit fv_def fv_defs];
    repeat rewrite in_union; auto 10
  end.
Qed.

Local Definition map_name_as (f : var -> var) (z x : var) :=
  fun v => If v = z then x else f v.

Local Lemma map_name_as_here f z x : map_name_as f z x z = x.
Proof. unfold map_name_as. case_if; congruence. Qed.

Local Lemma map_name_as_agrees f z x S :
  z \notin S -> names_agree_on (map_name_as f z x) f S.
Proof.
  intros Hz v Hv. unfold map_name_as. case_if; congruence.
Qed.

Local Lemma opened_type_mapping_at_fresh_name f x z k (T : typ) :
  z \notin fv T ->
  rename (map_name_as f z x) (open_rec k z T) =
  open_rec k x (rename f T).
Proof.
  intro Hz. rewrite rename_open_typ, map_name_as_here. f_equal.
  apply (proj1 (names_agree_types _ _)), map_name_as_agrees. exact Hz.
Qed.

Local Lemma opened_term_mapping_at_fresh_name f x z k (t : trm) :
  z \notin fv t ->
  rename (map_name_as f z x) (open_rec k z t) =
  open_rec k x (rename f t).
Proof.
  intro Hz. rewrite rename_open_trm, map_name_as_here. f_equal.
  apply (proj1 (names_agree_terms _ _)), map_name_as_agrees. exact Hz.
Qed.

Local Lemma opened_defs_mapping_at_fresh_name f x z k (ds : defs) :
  z \notin fv ds ->
  rename (map_name_as f z x) (open_rec k z ds) =
  open_rec k x (rename f ds).
Proof.
  intro Hz. rewrite rename_open_defs, map_name_as_here. f_equal.
  apply (proj2 (proj2 (proj2 (names_agree_terms _ _)))), map_name_as_agrees. exact Hz.
Qed.

Local Lemma rename_bound_independent f v T :
  typ_indep v T -> forall k d, v = avar_b k ->
  typ_indep_b k (transform_typ (avar_map f) T d).
Proof.
  induction 1; intros k d Hk; try (injection Hk as <-); subst; try discriminate;
    cbn [transform_typ transform_dec]; try solve [econstructor; eauto 5].
  - destruct H. all: constructor; constructor.
  - apply typ_indep_sel; unfold avar_map; intros HH;
      destruct v1; destruct v2; cbn in *; congruence.
  - apply typ_indep_sel_normal. unfold avar_map. destruct v2; cbn; congruence.
Qed.

Local Lemma rename_preserves_bound_indep f k (T : typ) :
  typ_indep_b k T -> typ_indep_b k (rename f T).
Proof. intros H. eapply rename_bound_independent; [exact H | reflexivity]. Qed.

Local Lemma map_name_as_other f z x v : v <> z -> map_name_as f z x v = f v.
Proof. unfold map_name_as. case_if; congruence. Qed.

Local Lemma maps_agree_twice f z c x y S :
  z \notin S -> c \notin S ->
  names_agree_on (map_name_as (map_name_as f z x) c y) f S.
Proof.
  intros Hz Hc v Hv.
  now rewrite (@map_name_as_agrees (map_name_as f z x) c y S Hc v Hv),
    (@map_name_as_agrees f z x S Hz v Hv).
Qed.

Local Lemma method_type_mapping_at_fresh_names f z c x y (T : typ) :
  z <> c -> z \notin fv T -> c \notin fv T ->
  rename (map_name_as (map_name_as f z x) c y) (open_met z c T) =
    open_met x y (rename f T).
Proof.
  intros Hneq Hz Hc.
  rewrite !rename_open_typ, (@map_name_as_other (map_name_as f z x) c y z Hneq), !map_name_as_here.
  f_equal. f_equal. apply (proj1 (names_agree_types _ _)).
  now apply maps_agree_twice.
Qed.

Local Lemma method_term_mapping_at_fresh_names f z c x y (t : trm) :
  z <> c -> z \notin fv t -> c \notin fv t ->
  rename (map_name_as (map_name_as f z x) c y) (open_met z c t) =
    open_met x y (rename f t).
Proof.
  intros Hneq Hz Hc.
  rewrite !rename_open_trm, (@map_name_as_other (map_name_as f z x) c y z Hneq), !map_name_as_here.
  f_equal. f_equal. apply (proj1 (names_agree_terms _ _)).
  now apply maps_agree_twice.
Qed.

Local Definition maps_reference_names e e' (f : var -> var) :=
  ok e /\ forall a b, binds a b e -> tyq_var e' (f a) (f b).

Local Lemma reference_names_agree_after_override e e' f z x :
  maps_reference_names e e' f ->
  z \notin fv_renv e ->
  maps_reference_names e e' (map_name_as f z x).
Proof.
  intros [Hok Hmap] Hz. split; [exact Hok |].
  intros a b Hbind. apply notin_union in Hz as [HzDom HzFv].
  assert (Ha : a <> z).
  { intro E. subst a. apply HzDom. eapply get_some_inv; exact Hbind. }
  assert (Hb : b <> z).
  {
    intro E. subst b. apply HzFv.
    apply (proj2 (@fv_env_value_member var fv e z Hok)).
    exists a, z. split; [exact Hbind |].
    change (z \in \{z}). now rewrite in_singleton.
  }
  rewrite !map_name_as_other by assumption. now apply Hmap.
Qed.

Local Lemma map_var_equiv e a b :
  tyq_var e a b -> forall e' f, maps_reference_names e e' f ->
    tyq_var e' (f a) (f b).
Proof.
  intro H. induction H as [e a | e a b Hb | e a b H IH | e a b c H1 IH1 H2 IH2];
    intros e' f Hmap.
  - apply tyq_var_refl.
  - exact (proj2 Hmap _ _ Hb).
  - apply tyq_var_sym. now apply IH.
  - eapply tyq_var_trans; [now apply IH1 | now apply IH2].
Qed.

Local Ltac split_fresh_name_hypotheses :=
  repeat match goal with H : ?x \notin ?S \u ?T |- _ =>
    apply notin_union in H as [? ?] end;
  repeat rewrite ?notin_singleton in *.

Local Ltac map_type_equiv_binder :=
  lazymatch goal with
  | |- tyq_typ ?e' (open_rec ?k ?x (rename ?f ?S))
         (open_rec ?k ?x (rename ?f ?T)) =>
    match goal with
    | Hmap : maps_reference_names ?e ?e' ?f,
      IH : forall z : var, forall e' f, maps_reference_names ?e e' f ->
          tyq_typ e' (rename f (open_rec ?k z ?S)) (rename f (open_rec ?k z ?T)) |- _ =>
       let z := fresh "z" in
       let Hz := fresh "Hz" in
       let Hresult := fresh "Hmapped" in
       destruct (var_fresh (fv S \u fv T \u fv_renv e)) as [z Hz];
       split_fresh_name_hypotheses;
       pose proof (IH z e' (map_name_as f z x)
         ltac:(apply reference_names_agree_after_override; [exact Hmap | now apply notin_union])) as Hresult;
       rewrite !opened_type_mapping_at_fresh_name in Hresult by assumption;
       exact Hresult
    end
  end.

Local Lemma map_type_equiv e T U :
  tyq_typ e T U -> forall e' f, maps_reference_names e e' f ->
    tyq_typ e' (rename f T) (rename f U).
Proof.
  intro H. induction H; intros e' f Hmap.
  - destruct H; apply tyq_typ_nulary; constructor.
  - destruct H; reduce_rename_types f.
    + apply tyq_typ_andor with (T := typ_and); unfold typing_equiv in *; eauto using typ_andor_and.
    + apply tyq_typ_andor with (T := typ_or); unfold typing_equiv in *; eauto using typ_andor_or.
  - reduce_rename_types f. change (tyq_typ e' (typ_fun (rename f t11) (rename f t12)) (typ_fun (rename f t21) (rename f t22))).
    apply tyq_typ_fun; unfold typing_equiv in *; [auto |].
    intro. map_type_equiv_binder.
  - reduce_rename_types f. apply tyq_typ_fld; unfold typing_equiv in *; eauto.
  - reduce_rename_types f.
    change (tyq_typ e'
      (typ_rcd (dec_typ B (rename f t11) (rename f t12)))
      (typ_rcd (dec_typ B (rename f t21) (rename f t22)))).
    apply tyq_typ_typ; unfold typing_equiv in *; intros;
      map_type_equiv_binder.
  - reduce_rename_types f. apply tyq_typ_sel_normal.
    unfold typing_equiv in H. eapply map_var_equiv; eassumption.
  - reduce_rename_types f. apply tyq_typ_sel.
  - rewrite !rename_bnd. apply tyq_typ_bnd. unfold typing_equiv in *.
    intros. map_type_equiv_binder.
  - reduce_rename_types f.
    change (tyq_typ e'
      (typ_rcd (dec_met m (rename f t11) (rename f t12) (rename f t13)))
      (typ_rcd (dec_met m (rename f t21) (rename f t22) (rename f t23)))).
    apply tyq_typ_met. unfold typing_equiv in *.
    + intro. map_type_equiv_binder.
    + match goal with IH : forall e' f, maps_reference_names _ _ _ ->
          tyq_typ _ (rename f t12) (rename f t22) |- _ => exact (IH e' f Hmap) end.
    + intros x y.
      destruct (var_fresh (fv t13 \u fv t23 \u fv_renv e)) as [z Hz].
      destruct (var_fresh (fv t13 \u fv t23 \u fv_renv e \u \{z})) as [c Hc].
      split_fresh_name_hypotheses.
      assert (Hmap' : maps_reference_names e e' (map_name_as (map_name_as f z x) c y)).
      { apply reference_names_agree_after_override;
          [apply reference_names_agree_after_override; [exact Hmap |] |];
          apply notin_union; assumption || auto. }
      pose proof (H3 z c e' (map_name_as (map_name_as f z x) c y) Hmap') as Hmapped.
      rewrite !method_type_mapping_at_fresh_names in Hmapped by (assumption || congruence).
      exact Hmapped.
Qed.

Local Lemma rename_reflects_bound_independence f :
  (forall T d k, typ_indep_b k (transform_typ (avar_map f) T d) -> typ_indep_b k T) /\
  (forall D d k, typ_indep_b k (typ_rcd (transform_dec (avar_map f) D d)) ->
    typ_indep_b k (typ_rcd D)).
Proof.
  apply typ_mutind; intros;
    cbn [transform_typ transform_dec] in *;
    try solve [match goal with IH : forall d k, _ -> _ |- _ => eapply IH; eassumption end];
    match goal with HI : typ_indep _ _ |- _ =>
      inversion HI; subst; try solve [match goal with X : typ_nulary _ |- _ => inversion X; subst; constructor; constructor end]
    end;
    try solve [econstructor; eauto].
  all: match goal with
  | |- typ_indep _ (typ_sel _ _ _) =>
    solve [
      apply typ_indep_sel; intro E; subst; cbn [avar_map rename_avar] in *; congruence |
      apply typ_indep_sel_normal; intro E; subst; cbn [avar_map rename_avar] in *; congruence ]
  end.
Qed.

Local Lemma rename_reflects_bound_indep f k (T : typ) :
  typ_indep_b k (rename f T) -> typ_indep_b k T.
Proof. apply (proj1 (rename_reflects_bound_independence f) T 0 k). Qed.

Local Definition maps_context mode e' f G G' :=
  (forall w T, ctx_binds w T G ->
    ty_var mode G' objctx_empty e' (f w) (rename f T)) /\
  (forall w, ctx_vis G w -> ctx_vis G' (f w)).

Local Lemma bound_type_free_vars_in_context G w (T : typ) :
  ctx_binds w T G -> fv T \c ctx_fv G.
Proof.
  induction 1; intros x Hx; cbn [ctx_collect_values]; rewrite ?in_union; auto.
Qed.

Local Lemma context_names_agree_after_override mode e' f G G' z x :
  maps_context mode e' f G G' ->
  z \notin ctx_dom G -> z \notin ctx_fv G ->
  maps_context mode e' (map_name_as f z x) G G'.
Proof.
  intros [Hbind Hvis] HzD HzF. split.
  - intros w T Hb.
    rewrite map_name_as_other by
      (intro H; subst w; apply HzD; eapply swap_calls_binding_in_context; exact Hb).
    assert (Hname : rename (map_name_as f z x) T = rename f T).
    {
      apply (proj1 (names_agree_types _ _)), map_name_as_agrees.
      intro H; apply HzF; exact (@bound_type_free_vars_in_context G w T Hb z H).
    }
    rewrite Hname. now apply Hbind.
  - intros w Hv. rewrite map_name_as_other by
      (intro H; subst w; apply HzD; exact (vis_in_dom Hv)).
    now apply Hvis.
Qed.

Local Lemma mapped_context_push mode e' f G G' z k (T : typ) :
  maps_context mode e' f G G' ->
  f z \notin ctx_dom G' ->
  maps_context mode e' f (G § z / k ~ T) (G' § f z / k ~ rename f T).
Proof.
  intros [HB HV] Hz.
  assert (HW := @ctx_extends_with_fresh G' (f z) k (rename f T) Hz).
  split.
  - intros x U Hx. inversion Hx; subst.
    + apply ty_var_var, ctx_binds_e.
    + eapply (proj1 (ctx_extends_types mode)).
      * apply HB. eassumption.
      * exact HW.
  - intros x Hx. inversion Hx; subst.
    + constructor.
    + apply (proj2 HW), HV. assumption.
Qed.

Local Lemma mapped_context_hide mode e' f G G' :
  maps_context mode e' f G G' ->
  maps_context mode e' f (ctx_hide G) (ctx_hide G').
Proof.
  intros [Hb Hv]. split.
  - intros x T Hx. inversion Hx; subst.
    eapply (proj1 (types_under_binding_extension mode)).
    + apply Hb. assumption.
    + split; [|trivial]. intros y U Hy. now apply ctx_binds_hide.
  - intros x Hx. inversion Hx.
Qed.

Local Definition mapped_objctx_fresh f G' Go :=
  forall w, w \in objctx_dom (rename_objctx f Go) -> w \notin ctx_dom G'.

Local Lemma mapped_empty_objctx f G' :
  mapped_objctx_fresh f G' objctx_empty.
Proof. intros w H; cbn [rename_objctx objctx_dom] in H; rewrite in_empty in H; contradiction. Qed.

Local Lemma mapped_context_object mode e' f G G' Go :
  maps_context mode e' f G G' ->
  mapped_objctx_fresh f G' Go ->
  maps_context mode e' f (G §§& Go) (G' §§& rename_objctx f Go).
Proof.
  destruct Go; cbn [ctx_obj rename_objctx]; auto.
  intros H HM. rewrite <- rename_open_typ.
  apply mapped_context_push; [exact H |].
  apply HM. cbn [rename_objctx objctx_dom]. now rewrite in_singleton.
Qed.

Local Definition context_and_env_names G e :=
  ctx_dom G \u ctx_fv G \u fv_renv e.

Local Lemma maps_context_env_after_override mode e e' f G G' z x :
  maps_context mode e' f G G' ->
  maps_reference_names e e' f ->
  z \notin context_and_env_names G e ->
  maps_context mode e' (map_name_as f z x) G G' /\
  maps_reference_names e e' (map_name_as f z x).
Proof.
  intros HG He Hz. unfold context_and_env_names in Hz.
  apply notin_union in Hz as [Hd Hz]. apply notin_union in Hz as [Hf Hr].
  split.
  - apply context_names_agree_after_override; assumption.
  - apply reference_names_agree_after_override; assumption.
Qed.

Local Lemma mapped_context_fresh_binder mode e' f G G' z x k (S : typ) :
  maps_context mode e' f G G' ->
  z \notin ctx_dom G -> z \notin ctx_fv G -> z \notin fv S ->
  x \notin ctx_dom G' ->
  maps_context mode e' (map_name_as f z x) (G § z / k ~ S) (G' § x / k ~ rename f S).
Proof.
  intros HG HzD HzF HzS Hx.
  assert (HS : rename (map_name_as f z x) S = rename f S)
    by (apply (proj1 (names_agree_types _ _)), map_name_as_agrees; exact HzS).
  replace (G' § x / k ~ rename f S)
    with (G' § map_name_as f z x z / k ~ rename (map_name_as f z x) S)
    by (now rewrite HS, map_name_as_here).
  apply mapped_context_push.
  - apply context_names_agree_after_override; assumption.
  - now rewrite map_name_as_here.
Qed.

Local Lemma mapped_context_method_parameters mode e e' f G G' z c x y S C :
  maps_context mode e' f G G' ->
  maps_reference_names e e' f ->
  z \notin context_and_env_names G e ->
  c \notin context_and_env_names G e ->
  z \notin fv S \u fv C ->
  c \notin fv S \u fv C ->
  z <> c -> x <> y ->
  x \notin ctx_dom G' -> y \notin ctx_dom G' ->
  let g := map_name_as (map_name_as f z x) c y in
  maps_context mode e' g (ctx_met G z S c C)
    (ctx_met G' x (rename f S) y (rename f C)) /\
  maps_reference_names e e' g.
Proof.
  intros HG He Hz Hc HzS HcS Hzc Hxy Hx Hy. cbv zeta.
  destruct (@maps_context_env_after_override mode e e' f G G' z x HG He Hz) as [HG1 He1].
  destruct (@maps_context_env_after_override mode e e' (map_name_as f z x) G G' c y HG1 He1 Hc) as [HG2 He2].
  split; [|exact He2].
  set (g := map_name_as (map_name_as f z x) c y) in *.
  assert (HS : rename g S = rename f S).
  { apply (proj1 (names_agree_types _ _)), maps_agree_twice;
      apply notin_union in HzS as [? ?]; apply notin_union in HcS as [? ?]; assumption. }
  assert (HC : rename g C = rename f C).
  { apply (proj1 (names_agree_types _ _)), maps_agree_twice;
      apply notin_union in HzS as [? ?]; apply notin_union in HcS as [? ?]; assumption. }
  assert (Hzx : g z = x).
  { unfold g. rewrite map_name_as_other by assumption. apply map_name_as_here. }
  assert (Hcy : g c = y) by apply map_name_as_here.
  replace (open x (rename f C)) with (rename g (open z C)).
  - rewrite <- HS at 1. rewrite <- Hzx at 1. rewrite <- Hcy.
    apply mapped_context_push.
    + apply mapped_context_push; [exact HG2 | now rewrite Hzx].
    + rewrite Hcy. cbn [ctx_dom]. rewrite notin_union, notin_singleton, Hzx. auto.
  - now rewrite rename_open_typ, HC, Hzx.
Qed.

Local Ltac fresh_fv :=
  repeat match goal with H : _ \notin _ \u _ |- _ => apply notin_union in H as [? ?] end.

Local Ltac map_decl_subtyping_binder m f G G' e e' S T x HG HE IH :=
  let z := fresh "z" in let Hz := fresh "Hz" in
  let HG' := fresh "HGmapped" in let He' := fresh "Hemapped" in
  let Hfresh := fresh "Hfresh" in let Hresult := fresh "Hmapped" in
  destruct (var_fresh (context_and_env_names G e \u (fv S \u fv T))) as [z Hz];
  apply notin_union in Hz as [Hfresh Hz];
  apply notin_union in Hz as [? ?];
  destruct (@maps_context_env_after_override m e e' f G G' z x HG HE Hfresh)
    as [HG' He'];
  pose proof (IH z (map_name_as f z x) G' e' HG' He') as Hresult;
  rewrite !opened_type_mapping_at_fresh_name in Hresult by assumption;
  exact Hresult.

Local Ltac map_cofinite_subtyping_binder m f G G' e e' L S x Hx Hgal Heb IH U V :=
  let z := fresh "z" in let Hfresh := fresh "Hfresh" in
  let HzL := fresh "HzL" in let HzE := fresh "HzE" in
  let HGnew := fresh "HGnew" in let Henew := fresh "Henew" in
  let Hresult := fresh "Hmapped" in
  destruct (var_fresh (context_and_env_names G e \u L \u fv S \u fv U \u fv V)) as [z Hfresh];
  apply notin_union in Hfresh as [HzE Hfresh]; fresh_fv;
  destruct (@maps_context_env_after_override m e e' f G G' z x Hgal Heb HzE)
    as [_ Henew];
  assert (HGnew : maps_context m e' (map_name_as f z x) (G § z / v_par ~ S) (G' § x / v_par ~ rename f S)) by
    (eapply mapped_context_fresh_binder; try eassumption;
      unfold context_and_env_names in HzE; fresh_fv; assumption);
  pose proof (IH z ltac:(assumption) (map_name_as f z x) (G' § x / v_par ~ rename f S) e' HGnew Henew)
    as Hresult;
  rewrite !opened_type_mapping_at_fresh_name in Hresult by assumption;
  exact Hresult.

Local Lemma map_type_judgments mode :
  (forall G Go e w T, ty_var mode G Go e w T ->
    forall f G' e', maps_context mode e' f G G' -> maps_reference_names e e' f ->
      ty_var mode G' objctx_empty e' (f w) (rename f T)) /\
  (forall G Go e S T, subtyp mode G Go e S T ->
    forall f G' e', maps_context mode e' f G G' -> maps_reference_names e e' f ->
      subtyp mode G' objctx_empty e' (rename f S) (rename f T)) /\
  (forall G Go e S T, ty_incap mode G Go e S T ->
    forall f G' e', maps_context mode e' f G G' -> maps_reference_names e e' f ->
      ty_incap mode G' objctx_empty e' (rename f S) (rename f T)).
Proof.
  apply (@ts_mutind mode
    (fun G Go e w T _ => forall f G' e', maps_context mode e' f G G' -> maps_reference_names e e' f ->
      ty_var mode G' objctx_empty e' (f w) (rename f T))
    (fun G Go e S T _ => forall f G' e', maps_context mode e' f G G' -> maps_reference_names e e' f ->
      subtyp mode G' objctx_empty e' (rename f S) (rename f T))
    (fun G Go e S T _ => forall f G' e', maps_context mode e' f G G' -> maps_reference_names e e' f ->
      ty_incap mode G' objctx_empty e' (rename f S) (rename f T))).
  all: intros; try rewrite !rename_open_typ; reduce_rename_types f;
    unfold obj_typing, subtyping, obj_ref_incap, typing_equiv in *.
  all: match goal with HC : maps_context _ _ _ _ _ |- _ => rename HC into Hctx end.
  all: match goal with HR : maps_reference_names _ _ _ |- _ => rename HR into Hrenv end.
  - eapply (proj1 Hctx); eassumption.
  - apply ty_rec_intro; unfold obj_typing, obj_ref_incap.
    + match goal with IH : forall f G' e', maps_context _ _ _ _ _ -> _ -> ty_var _ _ _ _ _ _ |- _ =>
        pose proof (IH f G' e' Hctx Hrenv) as Hmapped end.
      now rewrite rename_open_typ in Hmapped.
    + now apply rename_preserves_bound_indep.
    + intro Hinc. match goal with IH : _ -> forall f G' e', maps_context _ _ _ _ _ -> _ -> ty_incap _ _ _ _ _ _ |- _ =>
        pose proof (IH Hinc f G' e' Hctx Hrenv) as Hmapped end.
      now rewrite !rename_open_typ in Hmapped.
  - eapply ty_rec_elim with (T := rename f T); unfold obj_typing.
    + match goal with IH : forall f G' e', maps_context _ _ _ _ _ -> _ -> ty_var _ _ _ _ _ _ |- _ =>
        pose proof (IH f G' e' Hctx Hrenv) as Hmapped end.
      now rewrite rename_bnd in Hmapped.
    + now apply rename_preserves_bound_indep.
  - apply ty_var_and; unfold obj_typing; eauto.
  - eapply ty_var_sub; unfold obj_typing, subtyping; eauto.
  - eapply ty_var_mut_top with (T := rename f T); unfold obj_typing; eauto.
  - apply subtyp_top.
  - apply subtyp_bot.
  - apply subtyp_refl.
  - eapply subtyp_trans; unfold subtyping; eauto.
  - apply subtyp_and11.
  - apply subtyp_and12.
  - apply subtyp_and2; unfold subtyping; eauto.
  - apply subtyp_or11.
  - apply subtyp_or12.
  - apply subtyp_or2; unfold subtyping; eauto.
  - apply subtyp_fld; unfold subtyping; eauto.
  - apply subtyp_typ; unfold subtyping; intro x.
    + map_decl_subtyping_binder mode f G G' e e' S2 S1 x Hctx Hrenv H.
    + map_decl_subtyping_binder mode f G G' e e' T1 T2 x Hctx Hrenv H0.
  - eapply subtyp_sel2 with (T := rename f T). unfold obj_typing.
    pose proof (H f G' e' Hctx Hrenv) as Hr. reduce_rename_types_in f Hr. exact Hr.
  - eapply subtyp_sel1 with (S := rename f S). unfold obj_typing.
    pose proof (H f G' e' Hctx Hrenv) as Hr. reduce_rename_types_in f Hr. exact Hr.
  - eapply subtyp_fun with (L := ctx_dom G'); unfold subtyping; eauto.
    intros x Hx. map_cofinite_subtyping_binder mode f G G' e e' L S2 x Hx Hctx Hrenv H0 T1 T2.
  - eapply subtyp_met with (L := ctx_dom G'); unfold subtyping; eauto.
    + intros x Hx. map_cofinite_subtyping_binder mode f G G' e e' L TZ2 x Hx Hctx Hrenv H0 TC2 TC1.
    + intros Hmode Hind. apply rename_preserves_bound_indep, t; [exact Hmode |].
      eapply rename_reflects_bound_indep; exact Hind.
    + intros x Hx y Hyx Hy.
      set (W := context_and_env_names G e \u L \u fv TZ2 \u fv TC2 \u fv TR1 \u fv TR2).
      destruct (var_fresh W) as [z Hz].
      destruct (var_fresh (W \u \{z})) as [c Hc].
      apply notin_union in Hc as [Hc Hcz].
      rewrite notin_singleton in Hcz.
      unfold W in Hz, Hc.
      apply notin_union in Hz as [HzE Hz].
      apply notin_union in Hc as [HcE Hc].
      fresh_fv.
      destruct (@mapped_context_method_parameters mode e e' f G G' z c x y TZ2 TC2 Hctx Hrenv HzE HcE
        ltac:(apply notin_union; tauto) ltac:(apply notin_union; tauto)
        ltac:(congruence) ltac:(congruence) Hx Hy) as [HGnew Henew].
      pose proof (H1 z ltac:(assumption) c Hcz ltac:(assumption)
        (map_name_as (map_name_as f z x) c y) _ e' HGnew Henew) as Hmapped.
      rewrite !method_type_mapping_at_fresh_names in Hmapped by (assumption || congruence).
      exact Hmapped.
  - apply subtyp_tyq. unfold typing_equiv. eapply map_type_equiv; eassumption.
  - apply subtyp_typ_and.
  - apply subtyp_dist.
  - apply subtyp_nocap_bnd.
  - apply subtyp_nocap_typ.
  - apply subtyp_nocap_fld.
  - apply subtyp_nocap_met.
  - now apply subtyp_nocap_fun.
  - now apply subtyp_nocap_mut_top_boundless.
  - now apply subtyp_nocap_mut_top_complement.
  - now apply subtyp_nocap_mut_bot.
  - now apply subtyp_mut_top.
  - apply ty_incap_top.
  - apply ty_incap_bot.
  - apply ty_incap_typ.
  - apply ty_incap_cap.
  - apply ty_incap_met.
  - apply ty_incap_fld.
  - eapply ty_incap_sel with (S := rename f S) (T := rename f T).
    + unfold obj_typing. pose proof (H f G' e' Hctx Hrenv) as Hr.
      reduce_rename_types_in f Hr. exact Hr.
    + unfold obj_ref_incap. pose proof (H0 f G' e' Hctx Hrenv) as Hr.
      now rewrite rename_open_typ in Hr.
  - apply ty_incap_rec.
  - apply ty_incap_and; unfold obj_ref_incap; eauto.
  - apply ty_incap_or; unfold obj_ref_incap; eauto.
  - now apply ty_incap_fun.
  - apply ty_incap_nocap; unfold subtyping; eauto.
Qed.

Local Lemma map_cap_bound mode C G Go e S T :
  ty_capbnd mode C G Go e S T ->
  forall f G' e', maps_context mode e' f G G' -> maps_reference_names e e' f ->
    ty_capbnd mode C G' objctx_empty e' (rename f S) (rename f T).
Proof.
  destruct (map_type_judgments mode) as [Rvar _].
  intro H. induction H; intros f G' e' HG HE; reduce_rename_types f;
    try solve [econstructor; unfold obj_cap_bnd in *; eauto].
  eapply ty_capbnd_sel with (S := rename f S) (T := rename f T).
  - unfold obj_typing in *. pose proof (Rvar _ _ _ _ _ H f G' e' HG HE) as Hv.
    reduce_rename_types_in f Hv. exact Hv.
  - unfold obj_cap_bnd in *. pose proof (IHty_capbnd f G' e' HG HE) as Hb.
    now rewrite rename_open_typ in Hb.
Qed.

Local Lemma map_viewpoint mode x G e S T :
  viewpoint_adapt mode x G objctx_empty e S T ->
  forall f G' e', maps_context mode e' f G G' -> maps_reference_names e e' f ->
    viewpoint_adapt mode (f x) G' objctx_empty e' (rename f S) (rename f T).
Proof.
  destruct (map_type_judgments mode) as [_ [_ Rincap]].
  unfold viewpoint_adapt. destruct (mode_viewpoint_adaptation' mode); [congruence |].
  intros H f G' e' HG HE. inversion H; subst; reduce_rename_types f.
  constructor; unfold obj_ref_incap, obj_cap_bnd in *; eauto using map_cap_bound.
Qed.

Local Lemma object_names_agree_after_override f z x Go :
  z \notin objctx_dom Go \u objctx_fv Go ->
  rename_objctx (map_name_as f z x) Go = rename_objctx f Go.
Proof.
  destruct Go as [| w R | w R]; intro Hz; [reflexivity | |].
  all: cbn [objctx_dom objctx_fv rename_objctx] in *;
    try rewrite union_empty_l in Hz; fresh_fv;
    rewrite notin_singleton in *; f_equal;
    [apply map_name_as_other; congruence |
     apply (proj1 (names_agree_types _ _)), map_name_as_agrees; assumption].
Qed.

Local Lemma mapped_method_context mode e' f G G' Go z c TZ TC :
  maps_context mode e' f G G' ->
  mapped_objctx_fresh f G' Go ->
  f z \notin objctx_dom (rename_objctx f Go) \u ctx_dom G' ->
  f c \notin objctx_dom (rename_objctx f Go) \u ctx_dom G' ->
  f c <> f z ->
  maps_context mode e' f (ctx_obj_met mode G Go z TZ c TC)
    (ctx_obj_met mode G' (rename_objctx f Go) (f z) (rename f TZ) (f c) (rename f TC)).
Proof.
  intros HG Hself Hz Hc Hneq.
  pose proof (mapped_context_object HG Hself) as Hobj.
  destruct Go; destruct (mode_visibility' mode) eqn:Hvis;
    cbn [ctx_obj_met rename_objctx]; rewrite Hvis.
  all: rewrite <- !rename_open_typ; repeat rewrite <- rename_and.
  all: cbn [ctx_obj rename_objctx] in Hobj; try rewrite <- rename_open_typ in Hobj.
  all: apply mapped_context_push.
  all: try solve [cbn [ctx_dom objctx_dom rename_objctx] in *;
    rewrite ?union_empty_l, ?notin_union, ?notin_singleton in *; tauto].
  all: apply mapped_context_push; [try apply mapped_context_hide; exact Hobj |].
  all: cbn [ctx_dom objctx_dom rename_objctx] in *;
    rewrite ?union_empty_l, ?notin_union, ?notin_singleton in *; tauto.
Qed.

Local Ltac mapped_term_binder m f G G' e e' L k S u R x Hx Hctx Hrenv IH :=
  let z := fresh "z" in let Hz := fresh "Hz" in let Havoid := fresh "Havoid" in
  let HG := fresh "HG" in let HE := fresh "HE" in
  let Hmapped := fresh "Hmapped" in
  destruct (var_fresh (context_and_env_names G e \u L \u fv S \u fv u \u fv R)) as [z Hz];
  apply notin_union in Hz as [Havoid Hz]; fresh_fv;
  destruct (@maps_context_env_after_override m e e' f G G' z x Hctx Hrenv Havoid) as [_ HE];
  assert (HG : maps_context m e' (map_name_as f z x) (G § z / k ~ S) (G' § x / k ~ rename f S))
    by (apply mapped_context_fresh_binder; try eassumption;
        unfold context_and_env_names in Havoid; fresh_fv; assumption);
  pose proof (IH z ltac:(assumption) (map_name_as f z x) _ e' HG HE
    (@mapped_empty_objctx (map_name_as f z x) (G' § x / k ~ rename f S))) as Hmapped;
  rewrite opened_term_mapping_at_fresh_name in Hmapped by assumption;
  try rewrite opened_type_mapping_at_fresh_name in Hmapped by assumption;
  first [exact Hmapped |
    replace (rename (map_name_as f z x) R) with (rename f R) in Hmapped
      by (symmetry; apply (proj1 (names_agree_types _ _)), map_name_as_agrees; assumption);
    exact Hmapped].

Local Ltac map_typed_variable f G' e' HG He Rvar :=
  match goal with H : ty_var _ _ _ _ _ _ |- _ =>
    let Hr := fresh "Hmapped" in
    pose proof (Rvar _ _ _ _ _ H f G' e' HG He) as Hr;
    first [exact Hr | rewrite rename_open_typ in Hr; exact Hr | reduce_rename_types_in f Hr; exact Hr]
  end.

Local Lemma map_term_judgments mode :
  (forall G Go e t T, ty_trm mode G Go e t T ->
    forall f G' e', maps_context mode e' f G G' -> maps_reference_names e e' f ->
      mapped_objctx_fresh f G' Go ->
      ty_trm mode G' (rename_objctx f Go) e' (rename f t) (rename f T)) /\
  (forall G Go e l T, ty_lit mode G Go e l T ->
    forall f G' e', maps_context mode e' f G G' -> maps_reference_names e e' f ->
      mapped_objctx_fresh f G' Go ->
      ty_lit mode G' (rename_objctx f Go) e' (rename f l) (rename f T)) /\
  (forall G Go e d D, ty_def mode G Go e d D ->
    forall f G' e', maps_context mode e' f G G' -> maps_reference_names e e' f ->
      mapped_objctx_fresh f G' Go ->
      ty_def mode G' (rename_objctx f Go) e' (rename f d) (rename f D)) /\
  (forall G Go e ds T, ty_defs mode G Go e ds T ->
    forall f G' e', maps_context mode e' f G G' -> maps_reference_names e e' f ->
      mapped_objctx_fresh f G' Go ->
      ty_defs mode G' (rename_objctx f Go) e' (rename f ds) (rename f T)).
Proof.
  destruct (map_type_judgments mode) as [Rvar [Rsub Rincap]].
  apply (@rules_mutind mode
    (fun G Go e t T _ => forall f G' e', maps_context mode e' f G G' ->
      maps_reference_names e e' f -> mapped_objctx_fresh f G' Go ->
      ty_trm mode G' (rename_objctx f Go) e' (rename f t) (rename f T))
    (fun G Go e l T _ => forall f G' e', maps_context mode e' f G G' ->
      maps_reference_names e e' f -> mapped_objctx_fresh f G' Go ->
      ty_lit mode G' (rename_objctx f Go) e' (rename f l) (rename f T))
    (fun G Go e d D _ => forall f G' e', maps_context mode e' f G G' ->
      maps_reference_names e e' f -> mapped_objctx_fresh f G' Go ->
      ty_def mode G' (rename_objctx f Go) e' (rename f d) (rename f D))
    (fun G Go e ds T _ => forall f G' e', maps_context mode e' f G G' ->
      maps_reference_names e e' f -> mapped_objctx_fresh f G' Go ->
      ty_defs mode G' (rename_objctx f Go) e' (rename f ds) (rename f T))).
  all: intros; cbn [rename_objctx] in *; rewrite ?rename_open_typ;
    rewrite ?rename_lit_fun, ?rename_lit_obj, ?rename_def_met, ?rename_def_typ,
      ?rename_dec_typ, ?rename_dec_met;
    reduce_rename_terms f; unfold obj_typing, subtyping, obj_dec_typing in *.
  all: match goal with HC : maps_context _ _ _ _ _ |- _ =>
    rename HC into Hctx; pose proof (proj2 Hctx) as Hvis end.
  all: match goal with HR : maps_reference_names _ _ _ |- _ => rename HR into Hrenv end.
  all: match goal with HF : mapped_objctx_fresh _ _ _ |- _ => rename HF into Hself end.
  - apply ty_trm_var; unfold obj_typing; auto. map_typed_variable f G' e' Hctx Hrenv Rvar.
  - eapply ty_trm_apply with (S := rename f S) (T := rename f T);
      unfold obj_typing; intros; auto. all: map_typed_variable f G' e' Hctx Hrenv Rvar.
  - eapply ty_trm_read with (S := rename f S) (T := rename f T);
      unfold obj_typing; intros; auto.
    + map_typed_variable f G' e' Hctx Hrenv Rvar.
    + eapply map_viewpoint; eassumption.
  - eapply ty_trm_write with (S := rename f S);
      unfold obj_typing; intros; auto.
    all: try solve [map_typed_variable f G' e' Hctx Hrenv Rvar].
    unfold obj_typing in o. exact (Rvar _ _ _ _ _ (o H) f G' e' Hctx Hrenv).
  - eapply ty_trm_call with (TC := rename f TC) (TZ := rename f TZ) (TR := rename f TR);
      unfold obj_typing; intros; auto.
    all: try solve [map_typed_variable f G' e' Hctx Hrenv Rvar].
    apply rename_preserves_bound_indep; auto.
  - eapply ty_trm_let with (L := ctx_dom G') (T := rename f T); unfold obj_typing; eauto.
    intros x Hx. mapped_term_binder mode f G G' e e' L v_let T u U x Hx Hctx Hrenv H0.
  - eapply ty_trm_lit with (L := ctx_dom G') (T := rename f T); unfold obj_typing; eauto.
    intros x Hx. mapped_term_binder mode f G G' e e' L v_let T u U x Hx Hctx Hrenv H0.
  - eapply ty_trm_sub; unfold obj_typing, subtyping; eauto.
  - eapply ty_lit_fun with (L := ctx_dom G'); unfold obj_typing; eauto.
    intros x Hx. mapped_term_binder mode f G G' e e' L v_par T t U x Hx Hctx Hrenv H.
  - assert (Hnew : ty_lit mode G' objctx_empty e'
      (lit_obj (rename f T) (rename f ds)) (typ_objlit mode (rename f T))).
    {
      apply ty_lit_obj with (L := ctx_dom G'); unfold obj_typing.
      - intros x Hx.
        destruct (var_fresh (context_and_env_names G e \u L \u fv T \u fv ds)) as [z Hz].
        apply notin_union in Hz as [HzE Hz]. fresh_fv.
        destruct (@maps_context_env_after_override mode e e' f G G' z x Hctx Hrenv HzE) as [HG HE].
        set (g := map_name_as f z x) in *.
        assert (Hself' : mapped_objctx_fresh g G' (objctx_lit z T)).
        {
          intros w Hw. cbn [rename_objctx objctx_dom] in Hw.
          rewrite in_singleton in Hw. rewrite Hw. unfold g. now rewrite map_name_as_here.
        }
        pose proof (H z ltac:(assumption) g G' e' HG HE Hself') as Hmapped.
        unfold g in Hmapped. rewrite opened_defs_mapping_at_fresh_name,
          opened_type_mapping_at_fresh_name in Hmapped by assumption.
        cbn [rename_objctx] in Hmapped. rewrite map_name_as_here in Hmapped.
        replace (rename (map_name_as f z x) T) with (rename f T) in Hmapped
          by (symmetry; apply (proj1 (names_agree_types _ _)), map_name_as_agrees; assumption).
        exact Hmapped.
      - now apply rename_preserves_bound_indep.
    }
    destruct (mode_objlit_refcaps' mode); reduce_rename_terms f; exact Hnew.
  - eapply ty_def_typ with (L := \{}); unfold typing_equiv.
    intros x _.
    destruct (var_fresh (fv T \u fv U \u fv_renv e \u L)) as [z Hz].
    fresh_fv.
    pose proof (@map_type_equiv e _ _ (t z ltac:(assumption))
      e' (map_name_as f z x) ltac:(apply reference_names_agree_after_override; [
        exact Hrenv | now apply notin_union])) as Hmapped.
    rewrite !opened_type_mapping_at_fresh_name in Hmapped by assumption. exact Hmapped.
  - pose proof (mapped_context_object Hctx Hself) as Hobj.
    apply ty_def_fld; unfold obj_typing.
    + intros Hmode. apply (proj2 Hobj). auto.
    + eapply Rvar; eassumption.
  - eapply ty_def_met with (L := objctx_dom (rename_objctx f Go) \u ctx_dom G'); unfold obj_typing.
    intros x Hx y Hyx Hy.
    set (W := context_and_env_names G e \u (objctx_dom Go \u objctx_fv Go) \u L
      \u fv t \u fv TC \u fv TZ \u fv TR).
    destruct (var_fresh W) as [z Hz].
    destruct (var_fresh (W \u \{z})) as [c Hc].
    apply notin_union in Hc as [Hc Hcz]. rewrite notin_singleton in Hcz.
    unfold W in Hz, Hc.
    apply notin_union in Hz as [HzE Hz].
    apply notin_union in Hc as [HcE Hc].
    apply notin_union in Hz as [HzO Hz].
    apply notin_union in Hc as [HcO Hc].
    repeat (apply notin_union in Hz as [? Hz]).
    repeat (apply notin_union in Hc as [? Hc]).
    destruct (@maps_context_env_after_override mode e e' f G G' z x Hctx Hrenv HzE) as [HG1 HE1].
    destruct (@maps_context_env_after_override mode e e' (map_name_as f z x) G G' c y HG1 HE1 HcE) as [HG2 HE2].
    set (g := map_name_as (map_name_as f z x) c y) in *.
    assert (HGo : rename_objctx g Go = rename_objctx f Go).
    { unfold g. rewrite !object_names_agree_after_override by assumption. reflexivity. }
    assert (HgZ : g z = x) by (unfold g; rewrite map_name_as_other by congruence; apply map_name_as_here).
    assert (HgC : g c = y) by apply map_name_as_here.
    assert (HgTZ : rename g TZ = rename f TZ)
      by (apply (proj1 (names_agree_types _ _)), maps_agree_twice; assumption).
    assert (HgTC : rename g TC = rename f TC)
      by (apply (proj1 (names_agree_types _ _)), maps_agree_twice; assumption).
    pose proof (@mapped_method_context mode e' g G G' Go z c TZ TC HG2
      ltac:(unfold mapped_objctx_fresh; rewrite HGo; exact Hself)
      ltac:(rewrite HGo, HgZ; exact Hx)
      ltac:(rewrite HGo, HgC; exact Hy)
      ltac:(rewrite HgZ, HgC; exact Hyx)) as HGmethod.
    rewrite HGo, HgZ, HgC, HgTZ, HgTC in HGmethod.
    pose proof (H z ltac:(assumption) c Hcz ltac:(assumption)
      g _ e' HGmethod HE2 (@mapped_empty_objctx _ _)) as Hmapped.
    unfold g in Hmapped.
    rewrite method_term_mapping_at_fresh_names, method_type_mapping_at_fresh_names in Hmapped
      by (assumption || congruence).
    exact Hmapped.
  - apply ty_defs_one. unfold obj_dec_typing. eauto.
  - apply ty_defs_cons; unfold obj_typing, obj_dec_typing; eauto.
    assert (Hlabel : label_of (rename f d) = label_of d) by (destruct d; reflexivity).
    change (defs_hasnt (rename f ds) (label_of (rename f d))).
    rewrite Hlabel. now apply rename_defs_hasnt.
Qed.

Local Lemma identity_mapped_type (T : typ) : rename id T = T.
Proof. apply (proj1 (rename_fixed_types id)); intros x _; reflexivity. Qed.

Local Lemma identity_mapped_term (t : trm) : rename id t = t.
Proof. apply (proj1 (rename_fixed_terms id)); intros x _; reflexivity. Qed.

Local Lemma replacement_name_mapping_type z w (T : typ) :
  z \notin fv T -> rename (map_name_as id z w) T = T.
Proof.
  intro Hz. rewrite <- (identity_mapped_type T) at 2.
  apply (proj1 (names_agree_types _ _)), map_name_as_agrees. exact Hz.
Qed.

Local Lemma map_abstract_binding_to_reference mode G e z w k S :
  ctx_vis G w -> ty_var mode G objctx_empty e w S ->
  z \notin ctx_dom G -> z \notin ctx_fv G -> z \notin fv S ->
  maps_context mode e (map_name_as id z w) (G § z / k ~ S) G.
Proof.
  intros Hvis Hty HzD HzF HzS. split.
  - intros a T Ha. inversion Ha; subst.
    + rewrite map_name_as_here, replacement_name_mapping_type by assumption. exact Hty.
    + rewrite map_name_as_other by assumption.
      rewrite replacement_name_mapping_type;
        [apply ty_var_var; assumption |].
      intro Hf. apply HzF. eapply bound_type_free_vars_in_context; eassumption.
  - intros a Ha. inversion Ha; subst.
    + now rewrite map_name_as_here.
    + now rewrite map_name_as_other by assumption.
Qed.

Local Lemma typed_free_term_variable mode G e w T :
  ty_trm mode G objctx_empty e (trm_var (avar_f w)) T -> ty_var mode G objctx_empty e w T.
Proof.
  intro H. remember (trm_var (avar_f w)) as t eqn:Ht.
  induction H; try discriminate; unfold obj_typing, subtyping in *.
  - inversion Ht; subst; assumption.
  - eapply ty_var_sub; unfold obj_typing, subtyping; eauto.
Qed.

Local Lemma typed_frame_instantiation mode G e L w S u U :
  ok e ->
  ctx_vis G w ->
  ty_var mode G objctx_empty e w S ->
  (forall z, z \notin L -> ty_trm mode (G §ˣ z ~ S) objctx_empty e (open z u) U) ->
  ty_trm mode G objctx_empty e (open w u) U.
Proof.
  intros Hok Hvis Hvar Hbody.
  destruct (var_fresh (context_and_env_names G e \u L \u fv S \u fv u \u fv U)) as [z Hz].
  unfold context_and_env_names in Hz. fresh_fv.
  set (g := map_name_as id z w).
  assert (HG : maps_context mode e g (G §ˣ z ~ S) G)
    by (apply map_abstract_binding_to_reference; assumption).
  assert (HE : maps_reference_names e e g).
  {
    unfold g. apply reference_names_agree_after_override.
    - split; [exact Hok |]. intros a b Hab. now apply tyq_var_binds.
    - now apply notin_union.
  }
  pose proof ((proj1 (map_term_judgments mode)) _ _ _ _ _
    (Hbody z ltac:(assumption)) g G e HG HE (@mapped_empty_objctx g G)) as Hmapped.
  unfold g in Hmapped.
  rewrite opened_term_mapping_at_fresh_name in Hmapped by assumption.
  rewrite identity_mapped_term, replacement_name_mapping_type in Hmapped by assumption.
  exact Hmapped.
Qed.

Local Lemma let_return_preserves_configuration mode G e h Lv u fs w T :
  @ty_config mode G (config_mk (trm_var (avar_f w)) (stack_cons (frame_let u) fs) h e Lv) T ->
  @ty_config mode G (config_mk (open w u) fs h e
    (fv_config (config_mk (trm_var (avar_f w)) (stack_cons (frame_let u) fs) h e Lv))) T.
Proof.
  intro H.
  inversion H as [G0 e0 st0 h0 Lv0 t0 U V Hin Hheap Hstack Htfs Hvar Htfv Hfv Hnull Hseal Hclosed HT]; subst.
  inversion Hstack as [|L G0 e0 fs0 u0 S U' T0 Htail Hbody]; subst.
  assert (Hbound : ctx_k G w v_ref).
  { apply Htfv. constructor. }
  assert (Hvis : ctx_vis G w).
  {
    destruct Hheap as [_ [Hweak _]].
    destruct Hbound as [S0 [P Hbind]].
    eapply ctx_binds_visible; [exact Hweak |].
    eapply forget_kind_of_binding; eassumption.
  }
  assert (Hoke : ok e) by (destruct Hheap as [_ [_ [_ [Hok _]]]]; exact Hok).
  assert (Hopen : ty_trm mode G objctx_empty e (open w u) U').
  {
    eapply typed_frame_instantiation; [exact Hoke | exact Hvis | |exact Hbody].
    apply typed_free_term_variable. exact Hvar.
  }
  eapply ty_config_c with (T := U'); try assumption.
  - intros z Hz. apply Htfs. now apply tfree_stack_cons_r.
  - intros z Hz. destruct ((proj1 opened_term_free_variable_origin) u 0 w z Hz) as [Ho | ->].
    + apply Htfs. now apply tfree_stack_cons_l.
    + exact Hbound.
  - destruct Hfv as [[Hd Hctx] HTfv]. split; [split |];
      intros z Hz; do 4 (rewrite in_union; right); auto.
  - destruct Hnull as [z Hz]. exists z. repeat rewrite in_union. auto 12.
  - inversion Hclosed; subst. constructor; try assumption.
    + apply opening_closed_let_body. intros k z.
      match goal with Hst : closed (stack_cons (frame_let _) _) |- _ =>
        pose proof (Hst k z) as Hshape end.
      change (stack_cons (frame_let (open_rec (S k) z u)) (open_rec k z fs) =
        stack_cons (frame_let u) fs) in Hshape.
      congruence.
    + intros k z.
      match goal with Hst : closed (stack_cons (frame_let _) _) |- _ =>
        pose proof (Hst k z) as Hshape end.
      change (stack_cons (frame_let (open_rec (S k) z u)) (open_rec k z fs) =
        stack_cons (frame_let u) fs) in Hshape.
      congruence.
Qed.

Local Lemma let_return_has_typed_successor mode G e h Lv u fs w T :
  @ty_config mode G (config_mk (trm_var (avar_f w)) (stack_cons (frame_let u) fs) h e Lv) T ->
  exists C',
    typed_red mode G (config_mk (trm_var (avar_f w)) (stack_cons (frame_let u) fs) h e Lv) T G C' /\
    @ty_config mode G C' T.
Proof.
  intro H.
  eexists. split.
  - apply tred_let_var; [inversion H; assumption | exact H | reflexivity].
  - now apply let_return_preserves_configuration.
Qed.

Local Lemma source_binding_maps_to_existing_value mode e f G G' z k S :
  maps_context mode e f G G' ->
  ctx_vis G' (f z) ->
  ty_var mode G' objctx_empty e (f z) (rename f S) ->
  maps_context mode e f (G § z / k ~ S) G'.
Proof.
  intros [HB HV] Hz Htype. split.
  - intros x T Hx. inversion Hx; subst; auto.
  - intros x Hx. inversion Hx; subst; auto.
Qed.

Local Lemma identity_context_mapping mode G e : maps_context mode e id G G.
Proof.
  split; [|intros x Hx; exact Hx].
  intros x T Hx. rewrite identity_mapped_type. now apply ty_var_var.
Qed.

Local Lemma binding_under_hidden_context G x T :
  ctx_binds x T (ctx_hide G) -> ctx_binds x T G.
Proof. intro H. inversion H; subst; assumption. Qed.

Local Lemma heap_method_body_instantiation mode G e loc R m body TC TZ TR x y :
  mode_has_mutability mode ->
  ok e -> ctx_vis G x -> ctx_vis G y ->
  ty_var mode G objctx_empty e x TZ ->
  ty_var mode G objctx_empty e y
    (typ_and (open x TC) (typ_and (open loc R) (open y R))) ->
  ty_def mode G (objctx_heap loc R) e (def_met m body) (dec_met m TC TZ TR) ->
  ty_trm mode G objctx_empty e (open_met x y body) (open_met x y TR).
Proof.
  intros Hmut Hok Hvisx Hvisy Hx Hy Hmethod.
  inversion Hmethod; subst.
  match goal with H : forall z, z \notin _ -> forall c, c <> z -> _ |- _ => rename H into Hbody end.
  set (W := context_and_env_names G e \u L \u fv body \u fv TC \u fv TZ \u fv TR \u fv R \u \{loc}).
  destruct (var_fresh W) as [z Hz].
  destruct (var_fresh (W \u \{z})) as [c Hc].
  apply notin_union in Hc as [Hc Hcz]. rewrite notin_singleton in Hcz.
  unfold W in Hz, Hc.
  apply notin_union in Hz as [Hze Hz].
  apply notin_union in Hc as [Hce Hc].
  fresh_fv. repeat rewrite ?notin_singleton in *.
  assert (Hid : maps_reference_names e e id).
  { split; [exact Hok |]. intros a b Hab. now apply tyq_var_binds. }
  pose proof (identity_context_mapping mode G e) as HG0.
  destruct (@maps_context_env_after_override mode e e id G G z x HG0 Hid Hze) as [HG1 HE1].
  destruct (@maps_context_env_after_override mode e e (map_name_as id z x) G G c y HG1 HE1 Hce) as [HG2 HE2].
  set (g := map_name_as (map_name_as id z x) c y) in *.
  assert (Hzx : g z = x) by (unfold g; rewrite map_name_as_other by congruence; apply map_name_as_here).
  assert (Hcy : g c = y) by apply map_name_as_here.
  assert (Hloc : g loc = loc).
  { unfold g. rewrite !map_name_as_other by congruence. reflexivity. }
  assert (HTZ : rename g TZ = TZ).
  { rewrite <- (identity_mapped_type TZ) at 2.
    apply (proj1 (names_agree_types _ _)), maps_agree_twice; assumption. }
  assert (HTC : rename g TC = TC).
  { rewrite <- (identity_mapped_type TC) at 2.
    apply (proj1 (names_agree_types _ _)), maps_agree_twice; assumption. }
  assert (HR : rename g R = R).
  { rewrite <- (identity_mapped_type R) at 2.
    apply (proj1 (names_agree_types _ _)), maps_agree_twice; assumption. }
  assert (Hctx : maps_context mode e g (ctx_obj_met mode G (objctx_heap loc R) z TZ c TC) G).
  {
    cbn [ctx_obj_met].
    assert (Hvis : mode_visibility' mode = mode_visibility_hide_method) by (destruct mode; cbn in *; congruence).
    rewrite Hvis.
    apply source_binding_maps_to_existing_value.
    - apply source_binding_maps_to_existing_value.
      + destruct HG2 as [HB HVis]. split; [|intros a Ha; inversion Ha].
        intros a S Ha. now apply HB, binding_under_hidden_context.
      + now rewrite Hzx.
      + now rewrite Hzx, HTZ.
    - now rewrite Hcy.
    - rewrite Hcy. rewrite !rename_and, !rename_open_typ, Hzx, Hcy, Hloc, HTC, HR.
      exact Hy.
  }
  unfold obj_typing in *.
  pose proof ((proj1 (map_term_judgments mode)) _ _ _ _ _
    (Hbody z ltac:(assumption) c Hcz ltac:(assumption)) g G e Hctx HE2 (@mapped_empty_objctx g G)) as Hmapped.
  unfold g in Hmapped. rewrite method_term_mapping_at_fresh_names,
    method_type_mapping_at_fresh_names, identity_mapped_term, identity_mapped_type in Hmapped
    by (assumption || congruence).
  exact Hmapped.
Qed.

Local Lemma typed_record_member_has_declared_type mode G Go e ds T D :
  ty_defs mode G Go e ds T -> record_has T D ->
  exists d, defs_has ds d /\ ty_def mode G Go e d D.
Proof.
  intros Hdefs Hrec. induction Hdefs as [G Go e d D0 Hdec | G Go e ds d T D0 Hdefs IH Hdec Habs].
  - inversion Hrec; subst. exists d. split; [|exact Hdec].
    unfold defs_has. cbn [get_def]. case_if; congruence.
  - inversion Hrec; subst.
    + destruct IH as [d' [Hget Hd]]; [assumption |].
      exists d'. split; [|exact Hd].
      unfold defs_has, defs_hasnt in *. cbn [get_def].
      case_if; congruence.
    + match goal with H : record_has (typ_rcd _) _ |- _ => inversion H; subst end.
      exists d. split; [|exact Hdec].
      unfold defs_has. cbn [get_def]. case_if; congruence.
Qed.

Local Lemma control_step_has_typed_successor mode G t fs h e Lv T :
  mode_has_mutability mode -> mode_has_sef mode ->
  @ty_config mode G (config_mk t fs h e Lv) T ->
  ~ needs_heap_step t ->
  answer (config_mk t fs h e Lv) \/
  exists G' C', typed_red mode G (config_mk t fs h e Lv) T G' C' /\
    @ty_config mode G' C' T.
Proof.
  intros Hmut Hsef Htype Hcontrol.
  destruct t; cbn [needs_heap_step] in Hcontrol; try contradiction.
  - assert (Hfree : free_control_head (trm_var a)).
    { inversion Htype; subst. eapply typing_has_free_head; eassumption. }
    destruct Hfree as [w ->].
    destruct fs as [|[u] fs].
    + left. constructor.
    + right. destruct (let_return_has_typed_successor Htype) as [C' [Hstep Htype']].
      exists G, C'. auto.
  - right. exists G, (let_pushed t1 t2 fs h e Lv). split.
    + inversion Htype; subst. apply tred_let_push; eauto.
    + now apply let_push_preservation.
  - destruct l as [A body | A ds].
    + exfalso. eapply no_function_literal_typing; [exact Hmut |].
      inversion Htype; subst.
      eapply ty_trm_sub; unfold obj_typing, subtyping; [eassumption | apply subtyp_top].
    + right. eapply object_allocation_has_typed_successor; eassumption.
Qed.

Local Definition typed_heap_successors mode :=
  forall G t fs h e Lv T,
    @ty_config mode G (config_mk t fs h e Lv) T ->
    needs_heap_step t ->
    exists G' C', typed_red mode G (config_mk t fs h e Lv) T G' C' /\
      @ty_config mode G' C' T.

Local Lemma typed_progress_from_heap_successors mode :
  mode_has_mutability mode -> mode_has_sef mode ->
  typed_heap_successors mode ->
  forall G C T,
    @ty_config mode G C T ->
    answer C \/ exists G' C', typed_red mode G C T G' C' /\ @ty_config mode G' C' T.
Proof.
  intros Hmut Hsef Hheap G [t fs h e Lv] T Htype.
  destruct (classic (needs_heap_step t)) as [Hneeds | Hcontrol].
  - right. eapply Hheap; eassumption.
  - eapply control_step_has_typed_successor; eassumption.
Qed.

Local Lemma raw_prefixes_from_typed_successors mode G C T :
  mode_has_mutability mode -> mode_has_sef mode ->
  typed_heap_successors mode -> @ty_config mode G C T ->
  ~ typed_has_answer mode G C T ->
  forall n, exists C', C ⊣n↦* C'.
Proof.
  intros Hmut Hsef Hheap Hty Hnoanswer n.
  assert (Hprefix : exists G' C', typed_red_closure mode G C T n G' C' /\ @ty_config mode G' C' T).
  {
    induction n as [| n [G' [C' [Hrun Htype]]]].
    - exists G, C. split; [constructor | exact Hty].
    - destruct (typed_progress_from_heap_successors Hmut Hsef Hheap Htype)
        as [Hdone | [G'' [C'' [Hstep Hnext]]]].
      + exfalso. apply Hnoanswer. now exists n, G', C'.
      + exists G'', C''. split; [eapply typed_red_step; eassumption | exact Hnext].
  }
  destruct Hprefix as [G' [C' [Hrun _]]].
  exists C'. eapply swap_calls_typed_run_erases; eassumption.
Qed.

Local Lemma member_of_closed_definitions_is_closed ds d : closed ds -> defs_has ds d -> closed d.
Proof.
  unfold defs_has. induction ds as [|ds IH q]; cbn [get_def]; intros Hclosed Hget.
  - discriminate.
  - case_if.
    + inversion Hget; subst q.
      intros k x. specialize (Hclosed k x).
      change (defs_cons (open_rec k x ds) (open_rec k x d) = defs_cons ds d) in Hclosed.
      congruence.
    + apply IH; [|exact Hget].
      intros k x. specialize (Hclosed k x).
      change (defs_cons (open_rec k x ds) (open_rec k x q) = defs_cons ds q) in Hclosed.
      congruence.
Qed.

Local Lemma heap_binding_item_is_closed h y i :
  heap_closed h -> binds y i h -> closed i.
Proof.
  intros H. induction H; intro Hb.
  - exfalso. eapply binds_empty_inv; exact Hb.
  - apply binds_push_inv in Hb as [[_ ->] | [_ Hb]]; auto.
Qed.

Local Lemma opened_method_is_closed m t x y :
  closed (def_met m t) -> closed (open_met x y t).
Proof.
  intro Hcl.
  assert (Hbound : forall k z, open_rec (S (S k)) z t = t).
  {
    intros k z. specialize (Hcl k z).
    change (def_met m (open_rec (S (S k)) z t) = def_met m t) in Hcl. congruence.
  }
  intros [|[|k]] z.
  - apply (proj1 term_opening_idempotent).
  - rewrite (proj1 term_openings_commute) by discriminate.
    rewrite (proj1 term_opening_idempotent). reflexivity.
  - rewrite ((proj1 term_openings_commute) (open_rec 1 y t) (S (S k)) 0 z x) by discriminate.
    rewrite ((proj1 term_openings_commute) t (S (S k)) 1 z y) by discriminate.
    now rewrite Hbound.
Qed.

Local Lemma call_step_for_typed_body mode G e h Lv fs w p m y ds t S T :
  mode_has_mutability mode ->
  @ty_config mode G (config_mk (trm_call (avar_f w) m (avar_f p)) fs h e Lv) T ->
  binds w y e -> binds y (item_obj ds) h -> defs_has ds (def_met m t) ->
  ty_trm mode G objctx_empty e (open_met p w t) S ->
  @ty_stack mode G e S fs T ->
  let C := config_mk (trm_call (avar_f w) m (avar_f p)) fs h e Lv in
  let C' := config_mk (open_met p w t) fs h e (fv_config C) in
  typed_red mode G C T G C' /\ @ty_config mode G C' T.
Proof.
  cbv zeta. intros Hmut Htype Hrecv Hobj Hmet Hbody Hstack.
  destruct (heap_lookup_transport Hmut Htype (tfree_trm_call_l w (avar_f p) m))
    as [y' [ds' [Hrecv' [Hobj' Hkd]]]].
  pose proof (binds_functional Hrecv Hrecv') as E. subst y'.
  pose proof (binds_functional Hobj Hobj') as E. inversion E; subst ds'.
  pose proof (def_lookup_kinded Hkd Hmet) as Hm.
  inversion Hm; subst.
  inversion Htype as [G0 e0 fs0 h0 Lv0 t0 U T0 Hin Hheap HuStack Htk Hcontrol Hfree Hscope Hnull Hsealed Hclosed HT]; subst.
  split.
  - eapply (@tred_call mode G w w p y p m T ds t
      (trm_call (avar_f w) m (avar_f p)) fs e h Lv); try assumption; reflexivity.
  - eapply ty_config_c with (T := S); try assumption.
    + intros x Hx.
      destruct ((proj1 opened_term_free_variable_origin) _ 0 p x Hx) as [Hx' | ->].
      * destruct ((proj1 opened_term_free_variable_origin) _ 1 w x Hx') as [Horig | ->].
        -- match goal with H : all_tfree_k _ t v_ref |- _ => exact (H x Horig) end.
        -- apply Hfree, tfree_trm_call_l.
      * apply Hfree, tfree_trm_call_r.
    + destruct Hscope as [[HD HF] Hout]. split; [split |];
        intros x Hx; do 4 (rewrite in_union; right); eauto.
    + destruct Hnull as [x Hx]. exists x. repeat rewrite in_union. auto 12.
    + inversion Hclosed; subst.
      constructor; try assumption.
      apply opened_method_is_closed with (m := m).
      apply (@member_of_closed_definitions_is_closed ds (def_met m t)); [|exact Hmet].
      assert (Hitem : closed (item_obj ds)) by (eapply heap_binding_item_is_closed; eassumption).
      intros k x. specialize (Hitem k x).
      change (item_obj (open_rec k x ds) = item_obj ds) in Hitem.
      now injection Hitem.
Qed.

(* A field update retains the record declaration and the other heap entries. *)

Local Lemma update_retains_other_definitions ds a x ds' :
  defs_update ds a x ds' ->
  forall label, label <> label_fld a -> get_def label ds' = get_def label ds.
Proof.
  intro H. induction H; intros l Hl; cbn [get_def];
    cbn [label_of DefLabelOf] in *.
  - case_if; congruence.
  - case_if; auto.
Qed.

Local Lemma field_update_preserves_record_typing mode G y R e ds a loc ds' V S :
  defs_update ds a loc ds' ->
  ty_defs mode G (objctx_heap y R) e ds V ->
  record_has V (dec_fld a S S) ->
  ctx_vis G loc ->
  ty_var mode G objctx_empty e loc S ->
  ty_defs mode G (objctx_heap y R) e ds' V.
Proof.
  intros Hupdate Hdefs Hmember Hvis Hvar.
  revert V Hdefs Hmember.
  induction Hupdate as [ds a v loc | ds d a loc ds' Hupd IH Hneq];
    intros V Hdefs Hmember.
  - inversion Hdefs; subst; unfold obj_dec_typing, obj_typing in *.
    + inversion Hmember; subst.
      apply ty_defs_one. unfold obj_dec_typing. apply ty_def_fld; cbn [ctx_obj]; auto.
    + assert (Hright : D = dec_fld a S S).
      {
        inversion Hmember; subst.
        - destruct (typed_record_member_exists H1 H3) as [q [Hq Hget]].
          unfold defs_has in Hget. rewrite Hq in Hget.
          change (get_def (label_fld a) ds = None) in H7.
          change (get_def (label_fld a) ds = Some q) in Hget.
          congruence.
        - match goal with H : record_has (typ_rcd _) _ |- _ => inversion H; subst; reflexivity end.
      }
      subst D.
      apply ty_defs_cons; unfold obj_dec_typing, obj_typing; try assumption.
      * apply ty_def_fld; cbn [ctx_obj]; auto.
  - inversion Hdefs; subst; unfold obj_dec_typing, obj_typing in *.
    + inversion Hupd.
    + assert (Hleft : record_has T (dec_fld a S S)).
      {
        inversion Hmember; subst; [assumption |].
        match goal with H : record_has (typ_rcd _) _ |- _ => inversion H; subst end.
        match goal with HD : ty_def _ _ _ _ d (dec_fld a S S) |- _ =>
          pose proof (definition_label_matches_typing HD) as Hlabel
        end.
        cbn [label_of DecLabelOf] in Hlabel. contradiction.
      }
      apply ty_defs_cons; unfold obj_dec_typing, obj_typing; try assumption.
      * eapply IH; eassumption.
      * unfold defs_hasnt in *. rewrite (@update_retains_other_definitions ds a loc ds' Hupd (label_of d) Hneq).
        assumption.
Qed.

Local Lemma field_update_preserves_varkinds G ds a loc ds' :
  defs_update ds a loc ds' ->
  defs_varkinds G ds -> ctx_k G loc v_loc ->
  defs_varkinds G ds'.
Proof.
  intro H. induction H; intros Hds Hloc; inversion Hds; subst.
  - constructor; [assumption | now apply def_varkinds_fld].
  - constructor; auto.
Qed.

Local Lemma field_update_preserves_closed ds a loc ds' :
  defs_update ds a loc ds' -> closed ds -> closed ds'.
Proof.
  intro H. induction H as [ds a v loc |ds d a loc ds' Hupd IH Hneq]; intro Hcl.
  - intros k x.
    specialize (Hcl k x).
    change (defs_cons (open_rec k x ds) (open_rec k x (def_fld a v)) =
      defs_cons ds (def_fld a v)) in Hcl.
    change (defs_cons (open_rec k x ds) (def_fld a (avar_f loc)) =
      defs_cons ds (def_fld a (avar_f loc))).
    congruence.
  - assert (Hds : closed ds).
    {
      intros k x. specialize (Hcl k x).
      change (defs_cons (open_rec k x ds) (open_rec k x d) = defs_cons ds d) in Hcl.
      congruence.
    }
    pose proof (IH Hds) as Hds'.
    intros k x. specialize (Hcl k x).
    change (defs_cons (open_rec k x ds) (open_rec k x d) = defs_cons ds d) in Hcl.
    change (defs_cons (open_rec k x ds') (open_rec k x d) = defs_cons ds' d).
    rewrite Hds'. congruence.
Qed.

Local Lemma heap_closed_when_items_closed h :
  ok h -> (forall x i, binds x i h -> closed i) -> heap_closed h.
Proof.
  intro H. induction H as [|h x i Hok IH Hfresh]; intro Hvalue.
  - constructor.
  - apply heap_closed_push.
    + apply IH. intros y item Hy. apply (Hvalue y item).
      apply binds_push_neq; [exact Hy |].
      intro Eq. subst y. eapply binds_fresh_inv; eassumption.
    + eapply Hvalue. apply binds_push_eq.
Qed.

Local Lemma typed_heap_object_declarations mode G e h y R B ds :
  heap_correspond (typing_mode := mode) G e h ->
  ctx_binds y (typ_objref R B) G -> binds y (item_obj ds) h ->
  ty_defs mode G (objctx_heap y R) e ds (open y R) /\ defs_varkinds G ds.
Proof.
  intros Hheap Htype Hb.
  destruct Hheap as [_ [_ [_ [_ [_ [_ [_ Hitems]]]]]]].
  assert (Hy : y \in dom h) by (eapply get_some_inv; exact Hb).
  destruct (Hitems y Hy) as [G e h y A t L T Hfun Hbind Hof Hbody Hkind |
                            G e h y U S ds' T Hbind Hof Heq Hdefs Hkind]; subst.
  - pose proof (binds_functional Hb Hof). discriminate.
  - pose proof (binds_functional Hb Hof) as Hds. inversion Hds; subst.
    pose proof (ctx_binds_unique Htype Hbind) as Htypes. inversion Htypes; subst.
    split; assumption.
Qed.

Local Lemma closed_heap_object_definitions h y ds :
  heap_closed h -> binds y (item_obj ds) h -> closed ds.
Proof.
  intros H Hb. pose proof (heap_binding_item_is_closed H Hb) as Hitem.
  intros k x. specialize (Hitem k x).
  change (item_obj (open_rec k x ds) = item_obj ds) in Hitem.
  now injection Hitem.
Qed.

Local Lemma typed_field_update_of_nominal_object mode G e h y R B ds a S loc :
  heap_correspond (typing_mode := mode) G e h ->
  heap_closed h ->
  ctx_binds y (typ_objref R B) G -> binds y (item_obj ds) h ->
  record_has (open y R) (dec_fld a S S) ->
  ty_var mode G objctx_empty e loc S ->
  ctx_k G loc v_loc ->
  exists h', heap_update h y a loc h' /\
    heap_correspond (typing_mode := mode) G e h' /\ heap_closed h'.
Proof.
  intros Hheap Hclosed Htype Hb Hmember Hvar Hloc.
  destruct (typed_heap_object_declarations Hheap Htype Hb) as [Hdefs Hkinds].
  destruct (typed_record_member_has_declared_type Hdefs Hmember) as [d [Hget Hd]].
  inversion Hd; subst.
  destruct Hheap as [Hok [Hw [Hokh [Hoke [Hdom1 [Hdom2 [Hcorr Hitems]]]]]]].
  assert (Hvis : ctx_vis G loc).
  {
    destruct Hloc as [P [GbeforeLoc HL]].
    eapply ctx_binds_visible; [exact Hw |].
    eapply forget_kind_of_binding; exact HL.
  }
  destruct (update_existing_field loc Hokh Hb Hget) as [h' Hupd].
  exists h'. split; [exact Hupd |].
  destruct Hupd as [_ [Hokh' [Hdom [Hother [ds0 [ds' [Hsrc [Hdupd Htarget]]]]]]]].
  pose proof (binds_functional Hb Hsrc) as Eds. inversion Eds; subst ds0.
  split.
  - unfold heap_correspond. repeat split; try assumption.
    + now rewrite <- Hdom.
    + intros x Hx. destruct (classic (x = y)) as [-> | Hneq].
      * eapply ty_item_obj_s with (T := typ_objref R B) (ds := ds') (U := R) (S := B);
          [exact Htype | exact Htarget | reflexivity | |].
        -- unfold obj_typing. eapply field_update_preserves_record_typing; eassumption.
        -- eapply field_update_preserves_varkinds; eassumption.
      * rewrite <- Hdom in Hx. destruct (Hitems _ Hx).
        -- eapply ty_item_fun_s; try eassumption.
           eapply Hother; eassumption.
        -- eapply ty_item_obj_s; try eassumption.
           eapply Hother; eassumption.
  - apply heap_closed_when_items_closed; [exact Hokh' |].
    intros x i Hi. destruct (classic (x = y)) as [-> | Hneq].
    + pose proof (binds_functional Hi Htarget) as ->.
      intros k v. change (item_obj (open_rec k v ds') = item_obj ds').
      f_equal. eapply field_update_preserves_closed; [exact Hdupd |].
      eapply closed_heap_object_definitions; eassumption.
    + assert (Hx : x \in dom h).
      { rewrite Hdom. eapply get_some_inv; exact Hi. }
      destruct (get_some Hx) as [old Hold].
      pose proof (binds_functional Hi (Hother x old Hneq Hold)) as ->.
      eapply heap_binding_item_is_closed; eassumption.
Qed.

Local Lemma write_step_for_nominal_field mode G e h Lv fs w p a y loc ds R B S V T :
  mode_incap' mode = mode_incap_nocap ->
  @ty_config mode G (config_mk (trm_write (avar_f w) a (avar_f p)) fs h e Lv) T ->
  binds w y e -> binds y (item_obj ds) h -> ctx_binds y (typ_objref R B) G ->
  binds p loc e -> record_has (open y R) (dec_fld a S S) ->
  ty_var mode G objctx_empty e p S -> ty_var mode G objctx_empty e p V ->
  @ty_stack mode G e V fs T ->
  let C := config_mk (trm_write (avar_f w) a (avar_f p)) fs h e Lv in
  exists C', typed_red mode G C T G C' /\ @ty_config mode G C' T.
Proof.
  cbv zeta.
  intros Hmode Hty Hw Hy Hbind Hp Hm Harg Hresult Hstack.
  inversion Hty as [G0 e0 fs0 h0 Lv0 t0 U T0 Hin Hheap Hu Htk Hterm Hfree Hscope Hnull Hsealed Hclosed HT]; subst.
  inversion Hclosed as [t0 s0 h0 e0 Lv0 HcT HcS HcH]; subst.
  assert (Hloc : ctx_k G loc v_loc).
  {
    destruct Hheap as [Hok [Hweak [_ [_ [_ [_ [Hcorr _]]]]]]].
    apply ctx_kind_domain_is_bound; try assumption.
    eapply reference_target_in_context; eassumption.
  }
  assert (Hlocal : ty_var mode G objctx_empty e loc S).
  {
    destruct Hheap as [Hok [_ [_ [_ [_ [_ [Hcorr _]]]]]]].
    eapply location_preserves_reference_typing; eassumption.
  }
  destruct (typed_field_update_of_nominal_object Hheap HcH Hbind Hy Hm Hlocal Hloc)
    as [h' [Hupd [Hheap' Hclosed']]].
  eexists. split.
  - eapply (@tred_write mode G w p y loc a T (trm_write (avar_f w) a (avar_f p)) fs e h h' Lv);
      try assumption; reflexivity.
  - eapply ty_config_c with (T := V); try assumption.
    + apply ty_trm_var; unfold obj_typing; [|exact Hresult].
      intro Hmodevis.
      destruct Hheap as [_ [Hweak _]].
      assert (Hbound : ctx_k G p v_ref) by (apply Hfree; apply tfree_trm_write_r).
      destruct Hbound as [P [GbeforeArg HB]]. eapply ctx_binds_visible; [exact Hweak |].
      eapply forget_kind_of_binding; eassumption.
    + intros x Hx. inversion Hx; subst. apply Hfree, tfree_trm_write_r.
    + destruct Hscope as [[HD HF] Hout]. split; [split |];
        intros x Hx; do 4 (rewrite in_union; right); eauto.
    + destruct Hnull as [x Hx]. exists x. repeat rewrite in_union. auto 12.
    + constructor; try assumption. intros k x. reflexivity.
Qed.

(* Configuration similarity after replay of independent calls. *)

Local Lemma rename_compose_types f g :
  (forall A d, transform_typ (avar_map f) (transform_typ (avar_map g) A d) d =
    transform_typ (avar_map (fun x => f (g x))) A d) /\
  (forall D d, transform_dec (avar_map f) (transform_dec (avar_map g) D d) d =
    transform_dec (avar_map (fun x => f (g x))) D d).
Proof.
  apply typ_mutind; intros; cbn [transform_typ transform_dec]; try reflexivity;
    f_equal; auto.
  all: unfold avar_map; match goal with
  | |- context [rename_avar _ (rename_avar _ ?v)] => destruct v; reflexivity
  end.
Qed.

Local Lemma rename_compose_terms f g :
  (forall t d, transform_trm (avar_map f) (transform_trm (avar_map g) t d) d =
    transform_trm (avar_map (fun x => f (g x))) t d) /\
  (forall l d, transform_lit (avar_map f) (transform_lit (avar_map g) l d) d =
    transform_lit (avar_map (fun x => f (g x))) l d) /\
  (forall v d, transform_def (avar_map f) (transform_def (avar_map g) v d) d =
    transform_def (avar_map (fun x => f (g x))) v d) /\
  (forall ds d, transform_defs (avar_map f) (transform_defs (avar_map g) ds d) d =
    transform_defs (avar_map (fun x => f (g x))) ds d).
Proof.
  destruct (rename_compose_types f g) as [HT HD].
  apply trm_mutind; intros;
    cbn [transform_trm transform_lit transform_def transform_defs];
    try reflexivity; f_equal; auto.
  all: unfold avar_map; match goal with
  | |- context [rename_avar _ (rename_avar _ ?v)] => destruct v; reflexivity
  end.
Qed.

Local Lemma substitution_is_rename_types x y :
  (forall A d, subst_typ x y A = transform_typ (avar_map (subst_fvar x y)) A d) /\
  (forall D d, subst_dec x y D = transform_dec (avar_map (subst_fvar x y)) D d).
Proof.
  apply typ_mutind; intros; cbn [subst_typ subst_dec transform_typ transform_dec];
    try reflexivity; f_equal; auto.
  all: unfold avar_map; match goal with
  | |- context [rename_avar _ ?v] => destruct v; reflexivity
  end.
Qed.

Local Lemma substitution_is_rename_terms x y :
  (forall t d, subst_trm x y t = transform_trm (avar_map (subst_fvar x y)) t d) /\
  (forall l d, subst_lit x y l = transform_lit (avar_map (subst_fvar x y)) l d) /\
  (forall v d, subst_def x y v = transform_def (avar_map (subst_fvar x y)) v d) /\
  (forall ds d, subst_defs x y ds = transform_defs (avar_map (subst_fvar x y)) ds d).
Proof.
  destruct (substitution_is_rename_types x y) as [HT HD].
  apply trm_mutind; intros;
    cbn [subst_trm subst_lit subst_def subst_defs
         transform_trm transform_lit transform_def transform_defs];
    try reflexivity; f_equal; auto.
  all: unfold avar_map; match goal with
  | |- context [rename_avar _ ?v] => destruct v; reflexivity
  end.
Qed.

Local Definition image_names (f : var -> var) (X Y : vars) :=
  forall x, x \in X -> f x \in Y.

Local Lemma rename_avar_image f a X :
  image_names f (fv a) X -> fv (rename_avar f a) \c X.
Proof.
  destruct a; unfold rename_avar, image_names, fv, AvarFreeVar; intros H x.
  - rewrite in_empty. tauto.
  - rewrite in_singleton. intros ->. apply H. now rewrite in_singleton.
Qed.

Local Ltac take_image_names :=
  unfold image_names in *;
  cbn [fv TypFreeVar DecFreeVar TrmFreeVar LitFreeVar DefFreeVar DefsFreeVar
       StackFreeVar FrameFreeVar ItemFreeVar
       fv_typ fv_dec fv_trm fv_lit fv_def fv_defs stack_fv frame_fv fv_item] in *;
  intros w Hw;
  match goal with
  | Himage : forall v, v \in _ -> _ |- _ => apply Himage; repeat rewrite in_union in *; auto 8
  end.

Local Lemma subset_from_union (X Y Z : vars) :
  X \c Z -> Y \c Z -> (X \u Y) \c Z.
Proof. intros HX HY u Hu. rewrite in_union in Hu. intuition. Qed.

Local Ltac prove_image_names :=
  first [
    solve [apply subset_empty_l]
  | solve [unfold avar_map; apply rename_avar_image; take_image_names]
  | solve [
      match goal with
      | IH : forall d X, image_names _ _ X -> _ |- _ =>
          apply IH; take_image_names
      end]
  | apply subset_from_union; [prove_image_names | prove_image_names]
  ].

Local Lemma rename_image_types f :
  (forall A d X, image_names f (fv A) X -> fv (transform_typ (avar_map f) A d) \c X) /\
  (forall D d X, image_names f (fv D) X -> fv (transform_dec (avar_map f) D d) \c X).
Proof.
  apply typ_mutind; intros; cbn [transform_typ transform_dec fv TypFreeVar DecFreeVar fv_typ fv_dec];
    prove_image_names.
Qed.

Local Lemma rename_image_terms f :
  (forall t d X, image_names f (fv t) X -> fv (transform_trm (avar_map f) t d) \c X) /\
  (forall l d X, image_names f (fv l) X -> fv (transform_lit (avar_map f) l d) \c X) /\
  (forall v d X, image_names f (fv v) X -> fv (transform_def (avar_map f) v d) \c X) /\
  (forall ds d X, image_names f (fv ds) X -> fv (transform_defs (avar_map f) ds d) \c X).
Proof.
  destruct (rename_image_types f) as [HT HD].
  apply trm_mutind; intros;
    cbn [transform_trm transform_lit transform_def transform_defs TypTransform TransformCollect.transform
      fv TrmFreeVar LitFreeVar DefFreeVar DefsFreeVar fv_trm fv_lit fv_def fv_defs];
    try prove_image_names.
  - apply subset_from_union.
    + apply HT. take_image_names.
    + prove_image_names.
  - apply subset_from_union.
    + apply HT. take_image_names.
    + prove_image_names.
  - apply HT. take_image_names.
Qed.

Local Definition name_action_laws {A : Set} {AF : FreeVar A} {AS : SubstVar A}
    (r : (var -> var) -> A -> A) : Prop :=
  (forall x y a, subst_var x y a = r (subst_fvar x y) a) /\
  (forall f g a, r f (r g a) = r (fun x => f (g x)) a) /\
  (forall f a, preserves_fv f a -> r f a = a) /\
  (forall f a X, image_names f (fv a) X -> fv (r f a) \c X).

Local Lemma name_action_var : name_action_laws (fun f (x : var) => f x).
Proof.
  repeat split; try reflexivity.
  - intros f x H. apply H. apply in_singleton_self.
  - intros f x X H u Hu.
    change (u \in \{f x}) in Hu. rewrite in_singleton in Hu. subst u.
    apply H. apply in_singleton_self.
Qed.

Local Lemma name_action_trm : name_action_laws (fun f (t : trm) => rename f t).
Proof.
  repeat split; unfold rename; cbn [TransformCollect.transform TrmTransform].
  - intros. apply (proj1 (substitution_is_rename_terms _ _)).
  - intros. apply (proj1 (rename_compose_terms _ _)).
  - intros. now apply (proj1 (rename_fixed_terms _)).
  - intros. now apply (proj1 (rename_image_terms _)).
Qed.

Local Lemma name_action_item : name_action_laws (fun f (p : item) => rename f p).
Proof.
  repeat split; unfold rename; cbn [TransformCollect.transform ItemTransform].
  - intros x y [ds | t]; cbn [TransformCollect.transform ItemTransform transform_item subst_var ItemSubstVar subst_item];
    f_equal.
    + apply (proj2 (proj2 (proj2 (substitution_is_rename_terms x y)))).
    + apply (proj1 (substitution_is_rename_terms x y)).
  - intros f g [ds | t]; cbn [transform_item TransformCollect.transform ItemTransform DefsTransform TrmTransform];
    f_equal.
    + apply (proj2 (proj2 (proj2 (rename_compose_terms f g)))).
    + apply (proj1 (rename_compose_terms f g)).
  - intros f [ds | t] H; cbn [TransformCollect.transform ItemTransform transform_item]; f_equal.
    + apply (proj2 (proj2 (proj2 (rename_fixed_terms f)))); exact H.
    + apply (proj1 (rename_fixed_terms f)); exact H.
  - intros f [ds | t] X H; cbn [TransformCollect.transform ItemTransform transform_item fv ItemFreeVar fv_item].
    + apply (proj2 (proj2 (proj2 (rename_image_terms f)))); exact H.
    + apply (proj1 (rename_image_terms f)); exact H.
Qed.

Local Lemma name_action_stack : name_action_laws (fun f (st : stack) => rename f st).
Proof.
  repeat split; unfold rename; cbn [TransformCollect.transform StackTransform].
  - intros x y st. induction st as [|[t] s IH]; [reflexivity |].
    cbn [subst_var StackSubstVar stack_subst_var FrameSubstVar frame_subst_var
         transform_stack TransformCollect.transform StackTransform FrameTransform transform_frame TrmTransform].
    f_equal; [f_equal; apply (proj1 (substitution_is_rename_terms x y)) | exact IH].
  - intros f g st. induction st as [|[t] s IH]; [reflexivity |].
    cbn [transform_stack TransformCollect.transform StackTransform FrameTransform transform_frame TrmTransform].
    f_equal.
    + f_equal. apply (proj1 (rename_compose_terms f g)).
    + exact IH.
  - intros f st. induction st as [|[t] s IH]; intro H; [reflexivity |].
    cbn [transform_stack TransformCollect.transform StackTransform FrameTransform transform_frame TrmTransform].
    f_equal.
    + f_equal. apply (proj1 (rename_fixed_terms f)).
      intros w Hw. apply H. change (w \in fv t \u fv s). rewrite in_union. now left.
    + apply IH.
      intros w Hw. apply H. change (w \in fv t \u fv s). rewrite in_union. now right.
  - intros f st. induction st as [|[t] s IH]; intros X H.
    + apply subset_empty_l.
    + cbn [transform_stack TransformCollect.transform StackTransform FrameTransform transform_frame TrmTransform
           fv StackFreeVar stack_fv FrameFreeVar frame_fv].
      apply subset_from_union.
      * apply (proj1 (rename_image_terms f) t 1 X). take_image_names.
      * apply IH. take_image_names.
Qed.

Local Fixpoint paired_names (xs ys : list var) (u : var) :=
  match xs, ys with
  | (x :: xs)%list, (y :: ys)%list => subst_fvar x y (paired_names xs ys u)
  | _, _ => u
  end.

Local Lemma paired_names_outside xs ys u :
  u \notin from_list xs -> paired_names xs ys u = u.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hu; cbn [paired_names];
    try reflexivity.
  rewrite from_list_cons, notin_union, notin_singleton in Hu.
  destruct Hu as [Hhead Htail].
  rewrite IH by exact Htail.
  unfold subst_fvar. case_if; congruence.
Qed.

Local Lemma paired_names_round_trip xs ys :
  length xs = length ys ->
  fresh \{} (length xs) xs ->
  fresh \{} (length ys) ys ->
  disjoint (from_list xs) (from_list ys) ->
  forall u, u \in from_list xs ->
    paired_names xs ys u \in from_list ys /\
    paired_names ys xs (paired_names xs ys u) = u.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hlen Hxs Hys Hdisj u Hu;
    try discriminate.
  - rewrite from_list_nil, in_empty in Hu. contradiction.
  - injection Hlen as Hlen.
    cbn [fresh length] in Hxs, Hys.
    destruct Hxs as [_ Hxs]. destruct Hys as [_ Hys].
    assert (Hx : x \notin from_list xs).
    { apply fresh_single_notin with (n := length xs).
      eapply fresh_union_r2. exact Hxs. }
    assert (Hy : y \notin from_list ys).
    { apply fresh_single_notin with (n := length ys).
      eapply fresh_union_r2. exact Hys. }
    rewrite from_list_cons, in_union, in_singleton in Hu.
    destruct Hu as [-> | Hu].
    + cbn [paired_names].
      rewrite paired_names_outside by exact Hx.
      assert (Hsubst : subst_fvar x y x = y)
        by (unfold subst_fvar; case_if; congruence).
      rewrite Hsubst. split.
      * rewrite from_list_cons, in_union. left. apply in_singleton_self.
      * rewrite paired_names_outside by exact Hy.
        unfold subst_fvar. case_if; congruence.
    + assert (Htails : disjoint (from_list xs) (from_list ys)).
      {
        unfold disjoint. apply fset_extens; intros w Hw.
        - rewrite in_inter in Hw. destruct Hw as [Hw1 Hw2].
          exfalso. eapply (@disjoint_in_notin var _ _ w Hdisj).
          + rewrite from_list_cons, in_union. now right.
          + rewrite from_list_cons, in_union. now right.
        - rewrite in_empty in Hw. contradiction.
      }
      destruct (IH ys Hlen (fresh_empty Hxs) (fresh_empty Hys) Htails u Hu)
        as [Hw Hback].
      assert (Hnot_x : paired_names xs ys u <> x).
      {
        intro Heq. rewrite Heq in Hw.
        eapply (@disjoint_in_notin var _ _ x Hdisj).
        - rewrite from_list_cons, in_union. left. apply in_singleton_self.
        - rewrite from_list_cons, in_union. now right.
      }
      assert (Hnot_y : u <> y).
      {
        intro Heq. subst u.
        eapply (@disjoint_in_notin var _ _ y Hdisj); rewrite from_list_cons, in_union; auto using in_singleton_self.
      }
      cbn [paired_names].
      assert (Hforward : subst_fvar x y (paired_names xs ys u) = paired_names xs ys u).
      { unfold subst_fvar. case_if; congruence. }
      rewrite Hforward, Hback. split.
      * rewrite from_list_cons, in_union. now right.
      * unfold subst_fvar. case_if; congruence.
Qed.

Local Lemma paired_names_acts {A : Set} {AF : FreeVar A} {AS : SubstVar A}
    (r : (var -> var) -> A -> A) :
  name_action_laws r ->
  forall xs ys a, subst_vars xs ys a = r (paired_names xs ys) a.
Proof.
  intros [Hsubst [Hcompose [Hid _]]].
  induction xs as [|x xs IH]; intros [|y ys] a;
    cbn [vars_zip_map paired_names]; try solve [symmetry; apply Hid; intros z _; reflexivity].
  rewrite IH, Hsubst. apply Hcompose.
Qed.

Local Lemma fresh_count_agrees L xs n :
  fresh L n xs -> n = length xs.
Proof.
  revert L n. induction xs as [|x xs IH]; intros L [|n] Hfresh;
    cbn [fresh length] in *; try contradiction; try reflexivity.
  destruct Hfresh as [_ Htail]. f_equal. eapply IH; exact Htail.
Qed.

Local Lemma identity_similarity_with_support {A : Set} {AF : FreeVar A} {AS : SubstVar A}
    (r : (var -> var) -> A -> A) :
  name_action_laws r ->
  forall xs a, fresh \{} (length xs) xs -> fv a \c from_list xs ->
    similar_by_subst xs xs a a.
Proof.
  intros Hlaws xs a Hfresh Hsub.
  destruct (var_freshes (fv a \u fv a \u from_list xs \u from_list xs) (length xs))
    as [zs Hnew].
  pose proof (@fresh_count_agrees _ zs _ Hnew) as Hlen.
  assert (Hseparate : disjoint (from_list xs) (from_list zs)).
  {
    unfold disjoint. apply fset_extens; intros w Hw.
    - rewrite in_inter in Hw. destruct Hw as [Hw Hz].
      exfalso. eapply (@fresh_vars_notin _ zs _ Hnew w Hz).
      repeat rewrite in_union. auto.
    - rewrite in_empty in Hw. contradiction.
  }
  assert (Hzs : fresh \{} (length zs) zs) by (rewrite <- Hlen; now apply (fresh_empty Hnew)).
  pose proof (@paired_names_round_trip xs zs Hlen Hfresh Hzs Hseparate) as Hround.
  pose proof (@paired_names_acts A AF AS r Hlaws) as Hacts.
  destruct Hlaws as [_ [Hcompose [Hid Himage]]].
  assert (Hback : subst_vars zs xs (r (paired_names xs zs) a) = a).
  {
    rewrite Hacts, Hcompose.
    apply Hid. intros u Hu. apply Hsub in Hu. apply Hround in Hu. tauto.
  }
  exists (r (paired_names xs zs) a), zs.
  repeat split; try assumption.
  - now rewrite <- Hlen.
  - apply Himage. intros u Hu. apply Hsub in Hu. apply Hround in Hu. tauto.
Qed.

Local Lemma enumerate_names X :
  exists xs : list var, X = from_list xs /\ fresh \{} (length xs) xs.
Proof.
  destruct (FsetImpl.fset_finite X) as [ls ->].
  induction ls as [|x ls IH].
  - exists (nil : list var). split; [reflexivity | exact I].
  - destruct IH as [xs [Hset Hfresh]]. rewrite from_list_cons, Hset.
    destruct (classic (x \in from_list xs)) as [Hin | Hout].
    + exists xs. split; [|exact Hfresh].
      apply fset_extens; intros w Hw; rewrite in_union, in_singleton in *; firstorder congruence.
    + exists (x :: xs)%list. split; [symmetry; apply from_list_cons |].
      cbn [length fresh]. split; [apply notin_empty |].
      apply fresh_add_avoided_set; [exact Hfresh |].
      intros w Hw. rewrite notin_singleton. intro Heq. subst w. contradiction.
Qed.

Local Lemma same_bindings_similar_with {A : Set} (AS : Similar A) xs
    (e f : env A) :
  same_bindings e f ->
  (forall x v, binds x v e -> @similar A AS xs xs v v) ->
  forall ks, similar_env_with AS xs xs ks ks e f.
Proof.
  intros Hbind Hvalue ks. induction ks as [|x ks IH].
  - apply similar_env_empty. reflexivity.
  - destruct (classic (x \in dom e)) as [Hin | Hout].
    + destruct (get_some Hin) as [v Hv].
      eapply similar_env_dom; [exact IH | exact Hv | exact (proj1 (Hbind x v) Hv) |].
      eapply Hvalue; exact Hv.
    + apply similar_env_notin; [exact IH | exact Hout |].
      now rewrite <- (same_bindings_same_domain Hbind).
Qed.

Local Lemma same_control_and_store_similar t fs ha hb ea eb La Lb :
  same_valid_bindings ha hb ->
  same_valid_bindings ea eb ->
  similar_conf_1to1
    (config_mk t fs ha ea La)
    (config_mk t fs hb eb Lb).
Proof.
  intros [Hha [Hhb Hh]] [Hea [Heb He]].
  pose proof (same_bindings_same_domain Hh) as HDh.
  pose proof (same_bindings_same_domain He) as HDe.
  pose proof (fv_env_same_bindings fv Hha Hhb Hh) as HFh.
  pose proof (fv_env_same_bindings fv Hea Heb He) as HFe.
  destruct (enumerate_names (fv t \u fv fs \u fv_heap ha \u fv_renv ea))
    as [xs [Hnames Hfresh]].
  exists xs, xs. unfold vars_conf_unique. repeat split; try assumption.
  - rewrite <- Hnames. intros x Hx. repeat rewrite in_union in *. tauto.
  - rewrite <- HDh, <- HDe, <- HFh, <- HFe, <- Hnames.
    intros x Hx. repeat rewrite in_union in *. tauto.
  - change (similar_by_subst xs xs t t).
    eapply identity_similarity_with_support; [exact name_action_trm | exact Hfresh |].
    rewrite <- Hnames. intros x Hx. repeat rewrite in_union. auto.
  - change (similar_by_subst xs xs fs fs).
    eapply identity_similarity_with_support; [exact name_action_stack | exact Hfresh |].
    rewrite <- Hnames. intros x Hx. repeat rewrite in_union. auto.
  - change (similar_env_with similar_item xs xs xs xs ha hb).
    apply same_bindings_similar_with; [exact Hh |].
    intros x v Hv. change (similar_by_subst xs xs v v).
    eapply identity_similarity_with_support; [exact name_action_item | exact Hfresh |].
    rewrite <- Hnames. intros y Hy.
    assert (Hfv : y \in fv_env ha).
    { eapply fv_env_value_member; [exact Hha |]. exists x, v. auto. }
    repeat rewrite in_union. tauto.
  - change (similar_env_with similar_var xs xs xs xs ea eb).
    apply same_bindings_similar_with; [exact He |].
    intros x v Hv. change (similar_by_subst xs xs v v).
    eapply identity_similarity_with_support; [exact name_action_var | exact Hfresh |].
    rewrite <- Hnames. intros y Hy.
    assert (Hfv : y \in fv_env ea).
    { eapply fv_env_value_member; [exact Hea |]. exists x, v. auto. }
    repeat rewrite in_union. tauto.
Qed.

Local Lemma matching_replayed_configurations mode Ga Gb t fs ha hb ea eb La Lb T :
  @ty_config mode Ga (config_mk t fs ha ea La) T ->
  @ty_config mode Gb (config_mk t fs hb eb Lb) T ->
  same_bindings ha hb ->
  same_bindings ea eb ->
  〈Ga ⊢ (t ; fs ; ha ; ea ; La) ∶ T〉 ∼(call_swap_relation mode)∼>
  〈Gb ⊢ (t ; fs ; hb ; eb ; Lb) ∶ T〉.
Proof.
  intros HtyA HtyB Hh He.
  inversion HtyA as [? ? ? ? ? ? ? ? _ HheapA]; subst.
  inversion HtyB as [? ? ? ? ? ? ? ? _ HheapB]; subst.
  destruct HheapA as [_ [_ [Hha [Hea _]]]].
  destruct HheapB as [_ [_ [Hhb [Heb _]]]].
  unfold call_swap_relation, trf_lift_sim_conf.
  eapply trf_iterate_S.
  - apply trf_iterate_0. exact HtyA.
  - left. apply trf_similarity_c; try assumption.
    apply same_control_and_store_similar.
    + split; [exact Hha | split; assumption].
    + split; [exact Hea | split; assumption].
Qed.

Local Lemma related_swapped_resumptions mode G1 G2 t y1 y2 w1 w2
    fs h1 h2 e1 e2 L1 L2 T :
  closed t -> y1 <> y2 -> w1 <> y2 -> w2 <> y1 ->
  let A := config_mk
    (open w2 (open_rec 1 w1 (close_rec 1 y1 (close y2 t)))) fs h1 e1 L1 in
  let B := config_mk
    (open w1 (open_rec 1 w2 (close_rec 1 y2 (close y1 t)))) fs h2 e2 L2 in
  @ty_config mode G1 A T ->
  @ty_config mode G2 B T ->
  same_bindings h1 h2 ->
  same_bindings e1 e2 ->
  〈G1 ⊢ A ∶ T〉 ∼(call_swap_relation mode)∼> 〈G2 ⊢ B ∶ T〉.
Proof.
  cbv zeta. intros Hclosed Hdistinct H1 H2 Htype1 Htype2 Hheap Henv.
  rewrite (@swapped_result_continuations_match t y1 y2 w1 w2 Hclosed Hdistinct H1 H2)
    in Htype1 |- *.
  now apply matching_replayed_configurations.
Qed.

Local Lemma typing_an_application_requires_functions mode G e t T :
  ty_trm mode G objctx_empty e t T ->
  forall f a, t = trm_apply f a -> mode_has_fun mode.
Proof.
  intro Hty. induction Hty; intros fn arg Heq; try discriminate; eauto.
Qed.

Local Lemma mutable_heap_successors_from_members mode :
  mode_has_mutability mode ->
  (forall G h e fs Lv w a T,
    @ty_config mode G (config_mk (trm_read (avar_f w) a) fs h e Lv) T ->
    exists G' C', typed_red mode G
      (config_mk (trm_read (avar_f w) a) fs h e Lv) T G' C' /\
      @ty_config mode G' C' T) ->
  (forall G h e fs Lv w p a T,
    @ty_config mode G (config_mk (trm_write (avar_f w) a (avar_f p)) fs h e Lv) T ->
    exists G' C', typed_red mode G
      (config_mk (trm_write (avar_f w) a (avar_f p)) fs h e Lv) T G' C' /\
      @ty_config mode G' C' T) ->
  (forall G h e fs Lv w p m T,
    @ty_config mode G (config_mk (trm_call (avar_f w) m (avar_f p)) fs h e Lv) T ->
    exists G' C', typed_red mode G
      (config_mk (trm_call (avar_f w) m (avar_f p)) fs h e Lv) T G' C' /\
      @ty_config mode G' C' T) ->
  typed_heap_successors mode.
Proof.
  intros Hmut Hread Hwrite Hcall G t fs h e Lv T Hty Hheap.
  assert (Hex : exists U, ty_trm mode G objctx_empty e t U).
  { inversion Hty; subst. eexists. eassumption. }
  destruct Hex as [U Hfocus].
  pose proof (typing_has_free_head Hfocus) as Hfree.
  destruct t; cbn [needs_heap_step free_control_head] in *; try contradiction.
  - destruct Hfree as [w ->]. now apply Hread.
  - exfalso. pose proof (typing_an_application_requires_functions Hfocus eq_refl) as Hfun.
    rewrite (no_functions_in_mutability_mode mode Hmut) in Hfun. discriminate.
  - destruct Hfree as [w [p [-> ->]]]. now apply Hwrite.
  - destruct Hfree as [w [p [-> ->]]]. now apply Hcall.
Qed.

Local Lemma inert_binding_annotation mode G P y vk T :
  @inert mode G -> ctx_binds_k_after y vk T G P ->
  inert_typ (typing_mode := mode) T vk.
Proof.
  intros Hty Hbind. induction Hbind; inversion Hty; subst; auto.
Qed.

Local Lemma heap_correspond_for_existing_alias mode G e h y w P R B :
  mode_has_mutability mode ->
  heap_correspond (typing_mode := mode) G e h ->
  ctx_binds_k_after y v_loc (typ_objref R (typ_mut_marker typ_bot)) G P ->
  w \notin ctx_dom G ->
  heap_correspond (typing_mode := mode)
    (G § w / v_ref ~ typ_objref R (typ_mut_marker B)) (e & w ~ y) h.
Proof.
  intros Hmut [Hok [Hw [Hh [He [Hdloc [Hdref [Hcorr Hitems]]]]]]] Hloc Hfresh.
  set (A := typ_objref R (typ_mut_marker B)).
  assert (Henv : w # e).
  { rewrite <- Hdref. intro H. apply Hfresh. eapply ctx_kind_domain_is_in_domain; exact H. }
  pose proof (@ctx_extends_with_fresh G w v_ref A Hfresh) as Hext.
  split; [now apply ctx_ok_push |].
  split; [now constructor |].
  split; [exact Hh |].
  split; [now apply ok_push |].
  split.
  { cbn [ctx_kdom]. repeat case_if; try congruence; exact Hdloc. }
  split.
  { cbn [ctx_kdom]. repeat case_if; try congruence. now rewrite dom_push, Hdref, union_comm. }
  split.
  - eapply renv_corr_ref; [apply ctx_binds_k_e | exact Hloc | |].
    2: now apply renv_corr_under_fresh_binding.
    unfold A. apply typ_corr_obj. destruct mode; cbn in *; try discriminate.
    all: exists B; auto.
  - intros z Hz. destruct (Hitems z Hz) as
      [G e h z S t L T Hmode Hbind Hitem Hbody Hfv
      |G e h z S B' ds T Hbind Hitem Heq Hdefs Hfv].
    + pose proof (no_functions_in_mutability_mode mode Hmut). congruence.
    + eapply ty_item_obj_s.
      * exact (proj1 Hext _ _ Hbind).
      * exact Hitem.
      * exact Heq.
      * unfold obj_typing in *.
        eapply (proj2 (proj2 (proj2 (terms_under_renv_extension mode))));
          [|now apply fresh_ref_extension_keeps_bindings].
        eapply (proj2 (proj2 (proj2 (ctx_extends_terms mode)))); eassumption.
      * eapply defs_varkinds_under_context_change; [|exact Hfv].
        intros x k Hx. eapply kind_after_fresh_push; eassumption.
Qed.

Local Lemma read_alias_preserves_config_with_stack_fit mode G t fs h e Lv T y w P R B :
  let A := typ_objref R (typ_mut_marker B) in
  let C := config_mk t fs h e Lv in
  mode_has_mutability mode ->
  @ty_config mode G C T ->
  ctx_binds_k_after y v_loc (typ_objref R (typ_mut_marker typ_bot)) G P ->
  @ty_stack mode G e A fs T ->
  w \notin fv_config C ->
  w \notin ctx_fv G ->
  w \notin fv A ->
  closed A ->
  nothing_fresh_in_config A C ->
  @ty_config mode (G § w / v_ref ~ A)
    (config_mk (trm_var (avar_f w)) fs h (e & w ~ y) (fv_config C)) T.
Proof.
  cbv zeta. intros Hmut Hty Hloc Hfit HwC HwG HwA HclA HscopeA.
  set (A := typ_objref R (typ_mut_marker B)) in *.
  set (C := config_mk t fs h e Lv) in *.
  set (C' := config_mk (trm_var (avar_f w)) fs h (e & w ~ y) (fv_config C)).
  inversion Hty as [? ? ? ? ? ? U ? Hin Hheap Hstack HfreeFs Hterm Hfree Hscope Hnull Hseal Hclosed HT]; subst.
  assert (Hw : w \notin ctx_dom G).
  { intro Hdom. apply HwC. exact (proj1 (proj1 Hscope) _ Hdom). }
  assert (Hwe : w # e) by (apply fresh_from_machine_for_env with (t := t) (fs := fs) (h := h) (L := Lv); exact HwC).
  assert (Hkind : forall x k, ctx_k G x k -> ctx_k (G § w / v_ref ~ A) x k).
  { intros x k Hx. eapply kind_after_fresh_push; eassumption. }
  assert (Hbound : ctx_k (G § w / v_ref ~ A) w v_ref).
  { exists A, G. apply ctx_binds_k_e. }
  assert (Hkeep : fv_config C \c fv_config C').
  { intros x Hx. unfold C'. do 4 (rewrite in_union; right). exact Hx. }
  assert (Hw' : w \in fv_config C').
  { unfold C'. apply dom_env_in_machine_fv. rewrite dom_push, in_union, in_singleton. auto. }
  eapply ty_config_c with (T := A); try assumption.
  - apply inert_push; try assumption; [constructor |].
    pose proof (inert_binding_annotation Hin Hloc) as Hanno.
    inversion Hanno; subst.
    apply inert_typ_obj; try assumption.
    unfold refcap_inert_type. destruct mode; cbn in *; try discriminate; constructor.
  - unfold A. eapply heap_correspond_for_existing_alias; eassumption.
  - apply stack_typing_under_renv_extension with (e := e).
    + apply stack_typing_under_ctx_extension with (G := G); [exact Hfit |].
      now apply ctx_extends_with_fresh.
    + now apply fresh_ref_extension_keeps_bindings.
  - intros x Hx. apply Hkind. now apply HfreeFs.
  - apply ty_trm_var; [intros _; apply ctx_vis_e | apply ty_var_var, ctx_binds_e].
  - intros x Hx. inversion Hx; subst. exact Hbound.
  - destruct Hscope as [[HD HF] HTF]. split; [split |].
    + intros x Hx. cbn [ctx_dom] in Hx. rewrite in_union, in_singleton in Hx.
      destruct Hx as [-> | Hx]; [exact Hw' | now apply Hkeep, HD].
    + intros x Hx. cbn [fv CtxFreeVar ctx_collect_values] in Hx. rewrite in_union in Hx.
      apply Hkeep. destruct Hx as [Hx | Hx]; [now apply HscopeA | now apply HF].
    + intros x Hx. now apply Hkeep, HTF.
  - destruct Hnull as [x Hx]. exists x. unfold C.
    do 4 (rewrite in_union; right). exact Hx.
  - intro x. specialize (Hseal x). pose proof (closed_type_is_sealed HclA x) as HseA.
    change (seal x G § w / v_ref ~ seal x A = G § w / v_ref ~ A).
    now rewrite Hseal, HseA.
  - inversion Hclosed; subst. constructor; try assumption. intros k x. reflexivity.
Qed.

Local Lemma read_step_with_nominal_view mode G e h fs Lv w a y z ds R P W U TS TC T :
  let C := config_mk (trm_read (avar_f w) a) fs h e Lv in
  let A := rodot_read_ref_type R TS w TC in
  mode_has_mutability mode ->
  @ty_config mode G C T ->
  binds w y e ->
  binds y (item_obj ds) h ->
  defs_has ds (def_fld a (avar_f z)) ->
  ctx_binds_k_after z v_loc (typ_objref R (typ_mut_marker typ_bot)) G P ->
  ty_var mode G objctx_empty e w (typ_rcd (dec_fld a W U)) ->
  ty_incap mode G objctx_empty e U TS ->
  ty_capbnd mode typ_refcap_mutability G objctx_empty e U TC ->
  @ty_stack mode G e (rodot_read_term_type TS w TC) fs T ->
  @ty_stack mode G e A fs T ->
  closed A ->
  nothing_fresh_in_config A C ->
  exists G' C', typed_red mode G C T G' C' /\ @ty_config mode G' C' T.
Proof.
  cbv zeta.
  intros Hmut Hty Href Hobj Hfield Hloc Hproj Hstrip Hcap Hview Hfit Hclosed Hscope.
  set (C := config_mk (trm_read (avar_f w) a) fs h e Lv) in *.
  set (A := rodot_read_ref_type R TS w TC) in *.
  destruct (var_fresh (fv_config C \u ctx_fv G \u fv A)) as [p Hp].
  rewrite !notin_union in Hp. destruct Hp as [HpC [HpG HpA]].
  exists (G § p / v_ref ~ A).
  exists (config_mk (trm_var (avar_f p)) fs h (e & p ~ z) (fv_config C)).
  split.
  - assert (Hin : @inert mode G) by (inversion Hty; assumption).
    assert (Hmode : mode_viewpoint_adaptation' mode = mode_viewpoint_adapt_mutability)
      by (destruct mode; simpl in *; congruence).
    eapply (@tred_read_obj mode G P w p y z a T A U W R (typ_mut_marker typ_bot)
      ds (trm_read (avar_f w) a) fs e h Lv); try assumption; try reflexivity.
    + cbn [fresh length]. auto.
    + auto.
    + rewrite Hmode. exists TS, TC. repeat split; assumption || reflexivity.
  - apply read_alias_preserves_config_with_stack_fit with (P := P); assumption.
Qed.

Local Lemma object_location_has_nominal_record mode G e h y ds :
  mode_has_mutability mode ->
  @inert mode G ->
  heap_correspond (typing_mode := mode) G e h ->
  binds y (item_obj ds) h ->
  exists R P,
    ctx_binds_k_after y v_loc (typ_objref R (typ_mut_marker typ_bot)) G P /\
    ty_defs mode G (objctx_heap y R) e ds (open y R).
Proof.
  intros Hmut Hin Hheap Hb.
  assert (Hloc : ctx_k G y v_loc).
  {
    destruct Hheap as [Hok [Hw [_ [_ [Hdom _]]]]].
    apply ctx_kind_domain_is_bound; try assumption.
    rewrite Hdom. eapply get_some_inv; exact Hb.
  }
  destruct (typed_location_object_type Hmut Hheap Hloc) as [R [B [P Hkind]]].
  pose proof (inert_binding_annotation Hin Hkind) as Hanno.
  assert (Hcap : refcap_inert_type (typing_mode := mode) B v_loc)
    by (inversion Hanno; assumption).
  assert (HB : B = typ_mut_marker typ_bot).
  {
    destruct mode; cbn in *; try discriminate.
    all: now inversion Hcap.
  }
  subst B.
  exists R, P. split; [exact Hkind |].
  eapply typed_heap_object_declarations; [exact Hheap | | exact Hb].
  eapply forget_kind_of_binding. exact Hkind.
Qed.

Local Lemma call_step_for_nominal_record mode G e h Lv fs w p m y ds R TC TZ TR T :
  mode_has_mutability mode ->
  @ty_config mode G (config_mk (trm_call (avar_f w) m (avar_f p)) fs h e Lv) T ->
  binds w y e ->
  binds y (item_obj ds) h ->
  ty_defs mode G (objctx_heap y R) e ds (open y R) ->
  record_has (open y R) (dec_met m TC TZ TR) ->
  ty_var mode G objctx_empty e p TZ ->
  ty_var mode G objctx_empty e w
    (typ_and (open p TC) (typ_and (open y R) (open w R))) ->
  @ty_stack mode G e (open_met p w TR) fs T ->
  exists C', typed_red mode G (config_mk (trm_call (avar_f w) m (avar_f p)) fs h e Lv)
    T G C' /\ @ty_config mode G C' T.
Proof.
  intros Hmut Hty Href Hobj Hdefs Hmember Hparam Hrecv Hfit.
  set (C := config_mk (trm_call (avar_f w) m (avar_f p)) fs h e Lv) in *.
  inversion Hty as [? ? ? ? ? ? U ? Hin Hheap Hstack Htf Hcontrol Hfree]; subst.
  assert (Hvars : forall x, tfree_trm x (trm_call (avar_f w) m (avar_f p)) -> ctx_vis G x).
  {
    intros x Hx. apply Hfree in Hx. destruct Hx as [V [Q Hx]].
    destruct Hheap as [_ [Hw _]].
    eapply ctx_binds_visible; [exact Hw | eapply forget_kind_of_binding; exact Hx].
  }
  assert (Hok : ok e) by (destruct Hheap as [_ [_ [_ [Hok _]]]]; exact Hok).
  destruct (typed_record_member_has_declared_type Hdefs Hmember) as [d [Hget Hd]].
  inversion Hd; subst.
  eexists. eapply call_step_for_typed_body; [exact Hmut | exact Hty | exact Href |
    exact Hobj | exact Hget | | exact Hfit].
  eapply heap_method_body_instantiation; try eassumption.
  - apply Hvars, tfree_trm_call_r.
  - apply Hvars, tfree_trm_call_l.
Qed.

Local Lemma open_types_of_nominal_receiver mode G e h w y R P :
  @inert mode G ->
  heap_correspond (typing_mode := mode) G e h ->
  binds w y e ->
  ctx_binds_k_after y v_loc (typ_objref R (typ_mut_marker typ_bot)) G P ->
  ty_var mode G objctx_empty e w (typ_and (open y R) (open w R)).
Proof.
  intros Hin Hheap Href Hnom.
  pose proof (inert_binding_annotation Hin Hnom) as Hanno.
  assert (Hind : typ_indep_b 0 R) by (inversion Hanno; assumption).
  destruct Hheap as [Hok [_ [_ [_ [_ [_ [Hcorr _]]]]]]].
  destruct (renv_corresponding_bindings Hcorr Hok Href) as [Tw [Ty [HbW [HbY Htypes]]]].
  pose proof (ctx_binds_unique HbY (forget_kind_of_binding Hnom)) as Heq.
  destruct Htypes as [R' W Y HcorrT | S U Hfun]; inversion Heq; subst.
  pose proof (@object_reference_open_type mode G e w R W HbW Hind) as Hw.
  apply ty_var_and; unfold obj_typing; [|exact Hw].
  eapply ty_var_sub; unfold obj_typing, subtyping; [exact Hw |].
  apply equivalent_type_subtypes.
  apply opening_independent_type_with_alias; [|exact Hind].
  now apply tyq_var_binds.
Qed.

Local Lemma invert_typed_write mode G e w p a U :
  ty_trm mode G objctx_empty e (trm_write (avar_f w) a (avar_f p)) U ->
  exists W R,
    ty_var mode G objctx_empty e w (typ_rcd (dec_fld a W R)) /\
    ty_var mode G objctx_empty e p W /\
    subtyp mode G objctx_empty e R U.
Proof.
  intro H. remember (trm_write (avar_f w) a (avar_f p)) as t eqn:Ht.
  induction H; try discriminate; unfold obj_typing, subtyping in *.
  - inversion Ht; subst. exists S, T. repeat split; try assumption; apply subtyp_refl.
  - destruct (IHty_trm Ht) as [W [R [Hfield [Hp Hresult]]]].
    exists W, R. repeat split; try assumption. eapply subtyp_trans; eassumption.
Qed.

Local Lemma invert_typed_call mode G e w p m U :
  ty_trm mode G objctx_empty e (trm_call (avar_f w) m (avar_f p)) U ->
  exists TC TZ TR,
    ty_var mode G objctx_empty e w (typ_rcd (dec_met m TC TZ TR)) /\
    ty_var mode G objctx_empty e p TZ /\
    (mode_has_sef mode -> typ_indep_b 0 TC) /\
    ty_var mode G objctx_empty e w (open p TC) /\
    subtyp mode G objctx_empty e (open_met p w TR) U.
Proof.
  intro H. remember (trm_call (avar_f w) m (avar_f p)) as t eqn:Ht.
  induction H; try discriminate; unfold obj_typing, subtyping in *.
  - inversion Ht; subst. exists TC, TZ, TR. repeat split; try assumption; apply subtyp_refl.
  - destruct (IHty_trm Ht) as [TC [TZ [TR [Hrecv [Hp [Hind [Hself Hresult]]]]]]].
    exists TC, TZ, TR. repeat split; try assumption. eapply subtyp_trans; eassumption.
Qed.

Local Lemma instantiate_call_receiver_subtyping mode G e L p S A B :
  ok e -> ctx_vis G p ->
  ty_var mode G objctx_empty e p S ->
  (forall z, z \notin L -> subtyp mode (G § z / v_par ~ S) objctx_empty e
       (open z A) (open z B)) ->
  subtyp mode G objctx_empty e (open p A) (open p B).
Proof.
  intros Hok Hvis Hp Hbound.
  destruct (var_fresh (context_and_env_names G e \u L \u fv S \u fv A \u fv B)) as [z Hz].
  unfold context_and_env_names in Hz. fresh_fv.
  assert (Hctx : maps_context mode e (map_name_as id z p) (G § z / v_par ~ S) G)
    by (apply map_abstract_binding_to_reference; assumption).
  assert (He : maps_reference_names e e (map_name_as id z p)).
  {
    apply reference_names_agree_after_override.
    - split; [exact Hok |]. intros x y Hxy. now apply tyq_var_binds.
    - now apply notin_union.
  }
  pose proof ((proj1 (proj2 (map_type_judgments mode))) _ _ _ _ _
    (Hbound z ltac:(assumption)) (map_name_as id z p) G e Hctx He) as Hmapped.
  cbn [rename_objctx] in Hmapped.
  rewrite !opened_type_mapping_at_fresh_name, !identity_mapped_type in Hmapped by assumption.
  exact Hmapped.
Qed.

Local Lemma instantiate_call_receiver_constraint mode G e L w p S A B :
  ok e -> ctx_vis G p ->
  ty_var mode G objctx_empty e p S ->
  (forall z, z \notin L -> subtyp mode (G § z / v_par ~ S) objctx_empty e
       (open z A) (open z B)) ->
  ty_var mode G objctx_empty e w (open p A) ->
  ty_var mode G objctx_empty e w (open p B).
Proof.
  intros Hok Hvis Hp Hbound Hw.
  eapply ty_var_sub; unfold obj_typing, subtyping; [exact Hw |].
  exact (@instantiate_call_receiver_subtyping mode G e L p S A B Hok Hvis Hp Hbound).
Qed.

Local Lemma instantiate_call_result_subtyping mode G e L w p S C A B :
  ok e -> ctx_vis G p -> ctx_vis G w ->
  ty_var mode G objctx_empty e p S ->
  ty_var mode G objctx_empty e w (open p C) ->
  (forall z, z \notin L -> forall c, c <> z -> c \notin L ->
    subtyp mode (ctx_met G z S c C) objctx_empty e (open_met z c A) (open_met z c B)) ->
  subtyp mode G objctx_empty e (open_met p w A) (open_met p w B).
Proof.
  intros Hok HvisP HvisW Hp Hw Hresults.
  set (F := context_and_env_names G e \u L \u fv S \u fv C \u fv A \u fv B).
  destruct (var_fresh F) as [z Hz].
  destruct (var_fresh (F \u \{z})) as [c Hc].
  apply notin_union in Hc as [Hc Hcz]. rewrite notin_singleton in Hcz.
  unfold F in Hz, Hc.
  apply notin_union in Hz as [HzBase Hz].
  apply notin_union in Hc as [HcBase Hc].
  fresh_fv.
  assert (HE : maps_reference_names e e id).
  { split; [exact Hok |]. intros x y Hb. now apply tyq_var_binds. }
  destruct (@maps_context_env_after_override mode e e id G G z p
    (identity_context_mapping mode G e) HE HzBase) as [HG1 HE1].
  destruct (@maps_context_env_after_override mode e e (map_name_as id z p) G G c w
    HG1 HE1 HcBase) as [HG2 HE2].
  set (f := map_name_as (map_name_as id z p) c w) in *.
  assert (Hzp : f z = p)
    by (unfold f; rewrite map_name_as_other by congruence; apply map_name_as_here).
  assert (Hcw : f c = w) by apply map_name_as_here.
  assert (HS : rename f S = S)
    by (rewrite <- (identity_mapped_type S) at 2;
        apply (proj1 (names_agree_types _ _)), maps_agree_twice; assumption).
  assert (HC : rename f C = C)
    by (rewrite <- (identity_mapped_type C) at 2;
        apply (proj1 (names_agree_types _ _)), maps_agree_twice; assumption).
  assert (Hctx : maps_context mode e f (ctx_met G z S c C) G).
  {
    apply source_binding_maps_to_existing_value.
    - apply source_binding_maps_to_existing_value; [exact HG2 | now rewrite Hzp |].
      now rewrite Hzp, HS.
    - now rewrite Hcw.
    - now rewrite Hcw, rename_open_typ, Hzp, HC.
  }
  pose proof ((proj1 (proj2 (map_type_judgments mode))) _ _ _ _ _
    (Hresults z ltac:(assumption) c Hcz ltac:(assumption)) f G e Hctx HE2) as Hmapped.
  unfold f in Hmapped. rewrite !method_type_mapping_at_fresh_names, !identity_mapped_type
    in Hmapped by (assumption || congruence).
  exact Hmapped.
Qed.

Local Lemma active_operand_visible mode G t fs h e L T x :
  @ty_config mode G (config_mk t fs h e L) T ->
  tfree_trm x t -> ctx_vis G x.
Proof.
  intros Hty Hfree.
  inversion Hty as [? ? ? ? ? ? ? ? _ Hheap _ _ _ Hvars]; subst.
  destruct (Hvars _ Hfree) as [S [P Hkind]].
  destruct Hheap as [_ [Hw _]].
  apply ctx_binds_visible with (T := S); [exact Hw |].
  eapply forget_kind_of_binding. exact Hkind.
Qed.

(* A reduction introduces only names allocated by that reduction. *)

Local Definition opening_stays_in {A : Set} {AF : FreeVar A} {AO : Openable A}
    (a : A) :=
  forall k w, fv (open_rec k w a) \c fv a \u \{w}.

Local Lemma opening_avar_stays_in (v : avar) : opening_stays_in v.
Proof.
  intros k w x Hx. rewrite in_union.
  destruct v; cbn [open_rec AvarOpenable] in *.
  - unfold AvarOpenable in Hx. case_if; [now right |].
    change (x \in \{}) in Hx. rewrite in_empty in Hx. contradiction.
  - now left.
Qed.

Local Ltac opening_stays_in_components :=
  unfold opening_stays_in in *;
  intros k w x Hx;
  cbn [open_rec TypOpenable DecOpenable TrmOpenable LitOpenable DefOpenable DefsOpenable
       open_rec_typ open_rec_dec open_rec_trm open_rec_lit open_rec_def open_rec_defs
       fv TypFreeVar DecFreeVar TrmFreeVar LitFreeVar DefFreeVar DefsFreeVar
       fv_typ fv_dec fv_trm fv_lit fv_def fv_defs] in *;
  repeat rewrite in_union in *;
  try solve [rewrite in_empty in Hx; contradiction];
  repeat match goal with H : _ \/ _ |- _ => destruct H end;
  try solve [auto 10];
  let Hnames := fresh "Hnames" in
  first [
    match goal with
    | IH : forall (_ : nat) (_ : var), _,
      H : ?v \in _ |- _ =>
        first [pose proof (IH k w v H) as Hnames
              |pose proof (IH (S k) w v H) as Hnames
              |pose proof (IH (S (S k)) w v H) as Hnames]
    end
  | match goal with
    | IH : forall (_ : typ) (_ : nat) (_ : var), _,
      H : ?v \in _ |- _ =>
        first [pose proof (IH _ k w v H) as Hnames
              |pose proof (IH _ (S k) w v H) as Hnames]
    end
  | match goal with
    | a : avar, H : ?v \in _ |- _ =>
        pose proof (@opening_avar_stays_in a k w v H) as Hnames
    end
  ];
  rewrite ?in_union in Hnames; intuition.

Local Lemma opening_types_stay_in :
  (forall T : typ, opening_stays_in T) /\ (forall D : dec, opening_stays_in D).
Proof. apply typ_mutind; intros; opening_stays_in_components. Qed.

Local Lemma opening_terms_stay_in :
  (forall t : trm, opening_stays_in t) /\
  (forall l : lit, opening_stays_in l) /\
  (forall d : def, opening_stays_in d) /\
  (forall ds : defs, opening_stays_in ds).
Proof.
  destruct opening_types_stay_in as [Htyp Hdec].
  apply trm_mutind; intros; opening_stays_in_components.
Qed.

Local Lemma definition_lookup_fv ds d :
  defs_has ds d -> fv d \c fv ds.
Proof.
  unfold defs_has. induction ds as [|ds IH v]; cbn [get_def]; intros H x Hx.
  - discriminate.
  - change (x \in fv ds \u fv v). rewrite in_union. case_if.
    + injection H as ->. auto.
    + left. eapply IH; eassumption.
Qed.

Local Lemma updated_defs_fv ds a w ds' :
  defs_update ds a w ds' -> fv ds' \c fv ds \u \{w}.
Proof.
  intro H. induction H; intros q Hx;
    cbn [fv DefsFreeVar DefFreeVar fv_defs fv_def] in *;
    repeat rewrite in_union in *; [tauto |].
  destruct Hx as [Hx | Hx]; [apply IHdefs_update in Hx |];
    rewrite ?in_union in Hx; tauto.
Qed.

Local Lemma updated_heap_fv h x a y h' :
  heap_update h x a y h' -> fv_heap h' \c fv_heap h \u \{y}.
Proof.
  intros [Hok [Hok' [Hdom [Hrest [ds [ds' [Hb [Hupdate Hb']]]]]]]] v Hv.
  rewrite in_union in Hv. destruct Hv as [Hv | Hv].
  - rewrite <- Hdom in Hv. repeat rewrite in_union. auto.
  - apply fv_env_value_member in Hv; [|exact Hok'].
    destruct Hv as [p [it [Hp Hv]]].
    destruct (classic (p = x)) as [-> | Hneq].
    + pose proof (binds_functional Hp Hb') as ->.
      change (v \in fv ds') in Hv.
      pose proof (updated_defs_fv Hupdate Hv) as Horig.
      rewrite in_union in Horig. destruct Horig as [Horig | Hnew].
      * repeat rewrite in_union. left; right.
        eapply fv_env_value_member; [exact Hok |].
        exists x, (item_obj ds). auto.
      * rewrite in_union. now right.
    + repeat rewrite in_union. left; right.
      eapply fv_env_value_member; [exact Hok |].
      assert (Hdomp : p \in dom h).
      { rewrite Hdom. eapply get_some_inv; eassumption. }
      destruct (get_some Hdomp) as [it0 Hp0].
      pose proof (binds_functional Hp (Hrest p it0 Hneq Hp0)) as ->.
      exists p, it0. auto.
Qed.

Local Lemma dereferenced_avar_fv e (v : avar) :
  fv (deref e v) \c fv v \u fv_env e.
Proof.
  revert v. induction e as [|e y z IH] using env_ind; intros v x Hx.
  - change (x \in fv (deref_base AvarSubstVar empty v)) in Hx.
    unfold deref_base in Hx. rewrite empty_def in Hx. rewrite in_union. auto.
  - change (x \in fv (deref_base AvarSubstVar (e & y ~ z) v)) in Hx.
    rewrite replay_deref_base_push in Hx.
    apply IH in Hx. rewrite replay_fv_env_push, !in_union in *.
    destruct Hx as [Hx | Hx]; [|tauto].
    destruct v as [n | p]; cbn [subst_var AvarSubstVar] in Hx; [tauto |].
    case_if; auto.
Qed.

Local Lemma dereferenced_object_fv e ds :
  fv (deref e ds) \c fv ds \u fv_env e.
Proof.
  induction ds as [|ds IH v]; intros x Hx.
  - change (x \in \{}) in Hx. rewrite in_empty in Hx. contradiction.
  - change (x \in fv (deref e ds) \u fv (deref e v)) in Hx.
    change (x \in (fv ds \u fv v) \u fv_env e).
    rewrite in_union in Hx. repeat rewrite in_union.
    destruct Hx as [Hx | Hx].
    + apply IH in Hx. rewrite in_union in Hx. tauto.
    + destruct v; try tauto.
      change (x \in fv (deref e a)) in Hx.
      apply dereferenced_avar_fv in Hx.
      change (x \in fv a \u fv_env e) in Hx.
      rewrite in_union in Hx. tauto.
Qed.

Local Lemma heap_definition_fv h loc ds d x :
  ok h -> binds loc (item_obj ds) h ->
  defs_has ds d -> x \in fv d -> x \in fv_env h.
Proof.
  intros Hok Hb Hget Hx.
  eapply fv_env_value_member; [exact Hok |].
  exists loc, (item_obj ds). split; [exact Hb |].
  change (x \in fv ds). eapply definition_lookup_fv; eassumption.
Qed.

Local Ltac reduction_name_sets :=
  cbn [fv TrmFreeVar LitFreeVar StackFreeVar FrameFreeVar ItemFreeVar VarFreeVar AvarFreeVar
       fv_trm fv_lit stack_fv frame_fv fv_item] in *;
  repeat rewrite dom_push in *; repeat rewrite replay_fv_env_push in *;
  repeat rewrite from_list_cons in *; rewrite ?from_list_nil in *;
  cbv [fv VarFreeVar ItemFreeVar fv_item] in *;
  repeat rewrite in_union in *;
  rewrite ?in_empty, ?in_singleton in *.

Local Lemma raw_step_support C D :
  C ↦ D -> ok (config_heap C) -> ok (config_env C) ->
  exists names : list var,
    fresh (fv_config C) (length names) names /\
    from_list names \c dom (config_heap D) \u dom (config_env D) /\
    fv_config D \c fv_config C \u from_list names.
Proof.
  intros Hred Hheap Henv.
  destruct Hred;
    cbn [config_heap config_env] in Hheap, Henv.
  - exists (wVal :: nil)%list. split; [exact H |].
    split.
    { intros x Hx. cbn [config_heap config_env]. reduction_name_sets. tauto. }
    assert (Hv : yVal \in fv_env Sigma).
    {
      eapply heap_definition_fv; [exact Hheap | eassumption | eassumption |].
      change (yVal \in \{yVal}). apply in_singleton_self.
    }
    intros x Hx. rewrite replay_fv_env_push in Hx.
    reduction_name_sets. intuition congruence.
  - exists (nil : list var). split; [exact I |].
    split; [rewrite from_list_nil; apply subset_empty_l |].
    assert (Hy : yArg \in fv_env e).
    {
      eapply fv_env_value_member; [exact Henv |].
      exists wArg, yArg. split; [assumption | apply in_singleton_self].
    }
    intros x Hx.
    assert (Hstore : x \in fv_heap Sigma' -> x \in fv_heap Sigma \u \{yArg})
      by (eapply updated_heap_fv; eassumption).
    reduction_name_sets. intuition congruence.
  - exists (nil : list var). split; [exact I |].
    split; [rewrite from_list_nil; apply subset_empty_l |].
    intros x Hx.
    assert (Hbody : x \in fv t -> x \in fv_env Sigma).
    { intro Ht. eapply heap_definition_fv with (d := def_met m t); eassumption. }
    assert (Hopen1 := (proj1 opening_terms_stay_in) (open_rec 1 wObj t) 0 wArg x).
    assert (Hopen2 := (proj1 opening_terms_stay_in) t 1 wObj x).
    reduction_name_sets. intuition congruence.
  - exists (nil : list var). split; [exact I |].
    split; [rewrite from_list_nil; apply subset_empty_l |].
    intros x Hx.
    assert (Hbody : x \in fv t -> x \in fv_env Sigma).
    { intro Ht. eapply fv_env_value_member; [exact Hheap |]. exists yFun, (item_fun t). auto. }
    assert (Hopen := (proj1 opening_terms_stay_in) t 0 wArg x).
    reduction_name_sets. intuition congruence.
  - exists (y :: w :: nil)%list. split; [exact H |].
    split.
    { intros x Hx. cbn [config_heap config_env]. reduction_name_sets. tauto. }
    intros x Hx.
    assert (Hopen := (proj1 opening_terms_stay_in) t2 0 w x).
    rewrite !replay_fv_env_push in Hx.
    reduction_name_sets. intuition congruence.
  - exists (y :: w :: nil)%list. split; [exact H |].
    split.
    { intros x Hx. cbn [config_heap config_env]. reduction_name_sets. tauto. }
    intros x Hx.
    assert (Hopen := (proj1 opening_terms_stay_in) t 0 w x).
    assert (HopenDefs := (proj2 (proj2 (proj2 opening_terms_stay_in))) ds 0 w x).
    assert (Hresolved := @dereferenced_object_fv (e & w ~ y) (open w ds) x).
    reduction_name_sets. intuition congruence.
  - exists (nil : list var). split; [exact I |].
    split; [rewrite from_list_nil; apply subset_empty_l |].
    intros q Hq.
    assert (Hopen := (proj1 opening_terms_stay_in) t 0 x q).
    reduction_name_sets. intuition congruence.
  - exists (nil : list var). split; [exact I |].
    split; [rewrite from_list_nil; apply subset_empty_l |].
    intros x Hx. reduction_name_sets. tauto.
Qed.

Local Lemma field_update_deterministic ds a y ds1 ds2 :
  defs_update ds a y ds1 -> defs_update ds a y ds2 -> ds1 = ds2.
Proof.
  intros H. revert ds2. induction H; intros res Hres;
    inversion Hres; subst; try reflexivity;
    try solve [match goal with Hbad : label_of (def_fld ?a _) <> label_fld ?a |- _ => exfalso; apply Hbad; reflexivity end];
    f_equal; auto.
Qed.

Local Lemma heap_updates_agree h a b x l y :
  heap_update h x l y a -> heap_update h x l y b -> same_valid_bindings a b.
Proof.
  intros [_ [Hoka [HdomA [HotherA [dA [dA' [HA [HuA HA']]]]]]]]
    [_ [Hokb [HdomB [HotherB [dB [dB' [HB [HuB HB']]]]]]]].
  pose proof (binds_functional HA HB) as Heq. injection Heq as <-.
  pose proof (field_update_deterministic HuA HuB) as <-.
  split; [exact Hoka |]. split; [exact Hokb |].
  intros z v. destruct (classic (z = x)) as [-> | Hneq].
  - split; intro Hbind.
    + pose proof (binds_functional Hbind HA') as ->. exact HB'.
    + pose proof (binds_functional Hbind HB') as ->. exact HA'.
  - assert (Hcopy : forall k (h' : heap),
      dom h = dom h' ->
      (forall j i, j <> x -> binds j i h -> binds j i h') ->
      binds z k h' -> binds z k h).
    {
      intros k h' HD Hothers Hbind.
      assert (Hz : z \in dom h) by (rewrite HD; eapply get_some_inv; eassumption).
      destruct (get_some Hz) as [j Hj].
      pose proof (binds_functional Hbind (Hothers z j Hneq Hj)) as ->.
      exact Hj.
    }
    split; intro Hbind.
    + apply HotherB; [exact Hneq |]. exact (Hcopy v a HdomA HotherA Hbind).
    + apply HotherA; [exact Hneq |]. exact (Hcopy v b HdomB HotherB Hbind).
Qed.

Local Lemma binds_remove_prefix {A : Type} (f e : env A) x v :
  x # f -> binds x v (f & e) -> binds x v e.
Proof.
  intros Hfresh Hb. apply binds_concat_inv in Hb as [Hb | [_ Hb]].
  - exact Hb.
  - exfalso. eapply binds_fresh_inv; eassumption.
Qed.

Local Lemma heap_update_projects_away_prefix H h big big' loc a y :
  ok H -> ok h ->
  (forall x, x \in dom h -> x # H) ->
  loc # H ->
  same_valid_bindings (H & h) big ->
  heap_update big loc a y big' ->
  exists h', heap_update h loc a y h' /\ same_valid_bindings (H & h') big'.
Proof.
  intros Hprefix Hsmall Havoid Hloc Hagree Hupdate.
  pose proof Hupdate as [_ [_ [_ [_ [ds [ds' [Hbind [Hchange _]]]]]]]].
  assert (HbindSmall : binds loc (item_obj ds) h).
  { eapply binds_remove_prefix; [exact Hloc |]. apply Hagree. exact Hbind. }
  destruct (replace_heap_item (item_obj ds') Hsmall HbindSmall)
    as [h' [Hok [Hdom [Hdst Hother]]]].
  assert (Hupd : heap_update h loc a y h').
  {
    unfold heap_update. split; [exact Hsmall |]. split; [exact Hok |].
    split; [symmetry; exact Hdom |]. split; [exact Hother |].
    eauto 8.
  }
  exists h'. split; [exact Hupd |].
  apply heap_updates_agree with (h := big) (x := loc) (l := a) (y := y);
    [|exact Hupdate].
  eapply heap_update_equivalent_source; [exact Hagree |].
  eapply replay_heap_update_before; eassumption.
Qed.

Local Definition avoids_store_names (H : heap) (E : renv) (C : config) :=
  forall x, x \in fv_config C -> x # H /\ x # E.

Local Lemma reduction_avoids_store_names H E C D :
  C ↦ D -> ok (config_heap C) -> ok (config_env C) ->
  avoids_store_names H E C ->
  (forall x, x \in dom (config_heap D) -> x # H /\ x # E) ->
  (forall x, x \in dom (config_env D) -> x # H /\ x # E) ->
  avoids_store_names H E D.
Proof.
  intros Hstep Hheap Henv Hsource Hloc Href x Hx.
  destruct (raw_step_support Hstep Hheap Henv) as [ns [_ [Hkeys Hnames]]].
  apply Hnames in Hx. rewrite in_union in Hx.
  destruct Hx as [Hx | Hx]; [now apply Hsource |].
  apply Hkeys in Hx. rewrite in_union in Hx. destruct Hx; auto.
Qed.

Local Definition projects_off_stores (H : heap) (E : renv) (C D : config) :=
  match C, D with
  | config_mk tb sb hb eb Lb, config_mk t fs h e L =>
    tb = t /\ sb = fs /\ same_valid_bindings (H & h) hb /\ eb = E & e /\
    L \c Lb /\ ok h /\ ok e /\ avoids_store_names H E D
  end.

Local Lemma projected_free_variables H E C D :
  projects_off_stores H E C D -> fv_config D \c fv_config C.
Proof.
  destruct C as [tb sb hb eb Lb], D as [t fs h e L].
  intros [-> [-> [[Hok [Hokb Hsame]] [-> [Hmask _]]]]] x Hx.
  rewrite <- (same_bindings_same_domain Hsame),
    <- (fv_env_same_bindings fv Hok Hokb Hsame), !dom_concat, !replay_fv_env_concat.
  pose proof (Hmask x).
  repeat rewrite in_union in *. tauto.
Qed.

Local Lemma selected_reference_value_fv e x y :
  ok e -> binds x y e -> y \in fv_env e.
Proof.
  intros Hok Hb. eapply fv_env_value_member; [exact Hok |].
  exists x, y. split; [exact Hb | apply in_singleton_self].
Qed.

Local Lemma projection_env_lookup H E t fs h e L w y :
  avoids_store_names H E (config_mk t fs h e L) ->
  w \in fv_config (config_mk t fs h e L) ->
  binds w y (E & e) -> binds w y e.
Proof. intros Havoid Hfree. apply binds_remove_prefix. exact (proj2 (Havoid _ Hfree)). Qed.

Local Lemma projection_heap_lookup H E t fs h e L hb w y : forall it,
  avoids_store_names H E (config_mk t fs h e L) ->
  same_valid_bindings (H & h) hb ->
  ok e -> binds w y e -> binds y it hb -> binds y it h.
Proof.
  intros it Havoid [Hlarge [Hokb Hsame]] Hok Hb Hitem.
  eapply binds_remove_prefix.
  - assert (Hy : y \in fv_config (config_mk t fs h e L)).
    { pose proof (selected_reference_value_fv Hok Hb). repeat rewrite in_union. tauto. }
    exact (proj1 (Havoid y Hy)).
  - now apply Hsame.
Qed.

Local Ltac project_intro :=
  cbn [projects_off_stores];
  split; [reflexivity | split; [reflexivity |]];
  split; [idtac | split; [try reflexivity |]];
  try (split; [assumption | split; [assumption | split; [assumption |]]]).

Local Ltac projection_old_keys :=
  intros z Hz;
  match goal with Havo : avoids_store_names _ _ (config_mk ?t ?fs ?h ?e ?Ls) |- _ =>
    apply Havo;
    first [exact (@dom_heap_in_machine_fv t fs h e Ls z Hz)
          |exact (@dom_env_in_machine_fv t fs h e Ls z Hz)]
  end.

Local Lemma avoided_names_in_large_store H E C D x :
  projects_off_stores H E C D ->
  x \notin fv_config C ->
  x # H /\ x # E.
Proof.
  destruct C as [tb sb hb eb Lb], D as [t fs h e L].
  intros [-> [-> [[_ [_ Hsame]] [-> _]]]] Hx.
  rewrite <- (same_bindings_same_domain Hsame), !dom_concat in Hx.
  split; intro Hin; apply Hx; repeat rewrite in_union; tauto.
Qed.

Local Lemma prefix_preserves_binding_agreement {A : Type}
    (H e f : env A) x v :
  same_valid_bindings (H & e) f -> x # f ->
  same_valid_bindings (H & (e & x ~ v)) (f & x ~ v).
Proof.
  intros Hagree Hx. rewrite concat_assoc.
  apply same_valid_bindings_push; [exact Hagree |].
  rewrite (same_bindings_same_domain (proj2 (proj2 Hagree))). exact Hx.
Qed.

Local Lemma projected_new_keys H E C D names n :
  projects_off_stores H E C D ->
  fresh (fv_config C) n names ->
  forall x, x \in from_list names -> x # H /\ x # E.
Proof.
  intros Hproj Hfresh x Hx. eapply avoided_names_in_large_store; [exact Hproj |].
  eapply fresh_vars_notin; eassumption.
Qed.

Local Lemma pushed_keys_avoid {A : Type} (H : heap) (E : renv) (f : env A) y v :
  (forall x, x \in dom f -> x # H /\ x # E) ->
  y # H /\ y # E ->
  forall x, x \in dom (f & y ~ v) -> x # H /\ x # E.
Proof.
  intros Hprevious Hnew x. rewrite dom_push, in_union, in_singleton.
  intros [-> | Hx]; auto.
Qed.

Local Ltac active_reference_name :=
  cbn [fv TrmFreeVar AvarFreeVar fv_trm]; repeat rewrite in_union;
  rewrite ?in_singleton; tauto.

Local Ltac projected_step_safety Hsmall :=
  eapply reduction_avoids_store_names; [exact Hsmall | assumption | assumption | assumption | |];
  cbn [config_heap config_env].

Local Lemma project_independent_raw_step H E C D :
  C ↦ D -> ok H ->
  forall C0, projects_off_stores H E C C0 ->
    exists D0, C0 ↦ D0 /\ projects_off_stores H E D D0.
Proof.
  intros Hstep HokH.
  destruct Hstep as
    [yObj wObj m Sigma e Lv yVal wVal ds fs Hfresh Href Hobj Hget
    |yObj wObj m Sigma e Lv yArg wArg Sigma' fs Hupd Href Harg
    |yObj wObj m Sigma e Lv wArg t ds fs Hobj Hget Href
    |yFun wFun wArg Sigma e Lv t fs Hfun Href
    |T t1 t2 Sigma e Lv y w fs Hfresh Hdistinct
    |T ds t Sigma e Lv y w fs Hfresh Hdistinct
    |t Sigma e Lv x fs
    |s t fs Sigma e Lv];
    intros [tm st hSmall eSmall Lsmall] Hproj;
    pose proof (@projected_free_variables H E _ _ Hproj) as Hscope;
    pose proof Hproj as Hpr;
    cbn [projects_off_stores] in Hpr;
    destruct Hpr as [Ht [Hs [Hheap [He [Hmask [Hokh [Hoke Havoid]]]]]]];
    subst tm st e.
  - assert (HrefSmall : binds wObj yObj eSmall).
    { eapply projection_env_lookup; [exact Havoid | active_reference_name | exact Href]. }
    assert (HobjSmall : binds yObj (item_obj ds) hSmall).
    { eapply projection_heap_lookup; eassumption. }
    assert (Hsmall := @red_read yObj wObj m hSmall eSmall Lsmall yVal wVal ds fs
      ltac:(eapply fresh_decrease_set; eassumption) HrefSmall HobjSmall Hget).
    exists (config_mk (trm_var (avar_f wVal)) fs hSmall (eSmall & wVal ~ yVal)
      (fv_config (config_mk (trm_read (avar_f wObj) m) fs hSmall eSmall Lsmall))).
    split; [exact Hsmall |].
    assert (Hnew : wVal # H /\ wVal # E).
    { eapply projected_new_keys; [exact Hproj | exact Hfresh |].
      rewrite from_list_cons, in_union, in_singleton. now left. }
    assert (HenvNew : ok (eSmall & wVal ~ yVal)).
    {
      apply ok_push; [exact Hoke |].
      apply (@fresh_from_machine_for_env (trm_read (avar_f wObj) m) fs hSmall eSmall Lsmall wVal).
      intro Hw. apply (proj1 Hfresh). now apply Hscope.
    }
    cbn [projects_off_stores]. rewrite (concat_assoc E eSmall (wVal ~ yVal)).
    project_intro; try assumption.
    projected_step_safety Hsmall.
    + projection_old_keys.
    + apply pushed_keys_avoid; [projection_old_keys | exact Hnew].
  - assert (HrefSmall : binds wObj yObj eSmall).
    { eapply projection_env_lookup; [exact Havoid | active_reference_name | exact Href]. }
    assert (HargSmall : binds wArg yArg eSmall).
    { eapply projection_env_lookup; [exact Havoid | active_reference_name | exact Harg]. }
    assert (Hloc : yObj # H).
    {
      assert (Hy : yObj \in fv_config (config_mk
        (trm_write (avar_f wObj) m (avar_f wArg)) fs hSmall eSmall Lsmall)).
      { pose proof (selected_reference_value_fv Hoke HrefSmall).
        repeat rewrite in_union. tauto. }
      exact (proj1 (Havoid yObj Hy)).
    }
    destruct (@heap_update_projects_away_prefix H hSmall Sigma Sigma' yObj m yArg
      HokH Hokh ltac:(intros x Hx; apply (proj1 (Havoid x (@dom_heap_in_machine_fv _ _ _ _ _ x Hx))))
      Hloc Hheap Hupd) as [hNew [Hupdate HheapNew]].
    pose proof (@red_write yObj wObj m hSmall eSmall Lsmall yArg wArg hNew fs
      Hupdate HrefSmall HargSmall) as Hsmall.
    eexists. split; [exact Hsmall |].
    pose proof Hupdate as [_ [HokNew [HD _]]].
    project_intro; try assumption.
    projected_step_safety Hsmall.
    + intros x Hx. rewrite <- HD in Hx.
      apply Havoid. eapply dom_heap_in_machine_fv; eassumption.
    + projection_old_keys.
  - assert (HrefSmall : binds wObj yObj eSmall).
    { eapply projection_env_lookup; [exact Havoid | active_reference_name | exact Href]. }
    assert (HobjSmall : binds yObj (item_obj ds) hSmall).
    { eapply projection_heap_lookup; eassumption. }
    pose proof (@red_call yObj wObj m hSmall eSmall Lsmall wArg t ds fs
      HobjSmall Hget HrefSmall) as Hsmall.
    eexists. split; [exact Hsmall |].
    project_intro; try assumption.
    projected_step_safety Hsmall; projection_old_keys.
  - assert (HrefSmall : binds wFun yFun eSmall).
    { eapply projection_env_lookup; [exact Havoid | active_reference_name | exact Href]. }
    assert (HfunSmall : binds yFun (item_fun t) hSmall).
    { eapply projection_heap_lookup; eassumption. }
    pose proof (@red_apply yFun wFun wArg hSmall eSmall Lsmall t fs HfunSmall HrefSmall) as Hsmall.
    eexists. split; [exact Hsmall |].
    project_intro; try assumption.
    projected_step_safety Hsmall; projection_old_keys.
  - assert (Hy : y # H /\ y # E).
    { eapply projected_new_keys; [exact Hproj | exact Hfresh |].
      rewrite from_list_cons, in_union, in_singleton. now left. }
    assert (Hw : w # H /\ w # E).
    { eapply projected_new_keys; [exact Hproj | exact Hfresh |].
      rewrite !from_list_cons, !in_union, !in_singleton. auto. }
    assert (HfreshSmall : fresh
      (fv_config (config_mk (trm_lit (lit_fun T t1) t2) fs hSmall eSmall Lsmall))
      2 (y :: w :: nil)%list) by (eapply fresh_decrease_set; eassumption).
    assert (HfreshY : y # hSmall)
      by (eapply fresh_from_machine_for_heap; exact (proj1 HfreshSmall)).
    assert (HfreshW : w # eSmall).
    {
      eapply fresh_from_machine_for_env.
      pose proof (proj1 (proj2 HfreshSmall)) as HF.
      apply notin_union in HF as [HF _]. exact HF.
    }
    pose proof (@red_let_fun T t1 t2 hSmall eSmall Lsmall y w fs HfreshSmall Hdistinct) as Hsmall.
    eexists. split; [exact Hsmall |].
    assert (HheapNew : same_valid_bindings (H & (hSmall & y ~ item_fun t1)) (Sigma & y ~ item_fun t1)).
    { apply prefix_preserves_binding_agreement; [exact Hheap |].
      eapply fresh_from_machine_for_heap. exact (proj1 Hfresh). }
    assert (HhNew : ok (hSmall & y ~ item_fun t1)) by (now apply ok_push).
    assert (HeNew : ok (eSmall & w ~ y)) by (now apply ok_push).
    cbn [projects_off_stores]. rewrite (concat_assoc E eSmall (w ~ y)).
    project_intro; try assumption.
    projected_step_safety Hsmall.
    + apply pushed_keys_avoid; [projection_old_keys | exact Hy].
    + apply pushed_keys_avoid; [projection_old_keys | exact Hw].
  - assert (Hy : y # H /\ y # E).
    { eapply projected_new_keys; [exact Hproj | exact Hfresh |].
      rewrite from_list_cons, in_union, in_singleton. now left. }
    assert (Hw : w # H /\ w # E).
    { eapply projected_new_keys; [exact Hproj | exact Hfresh |].
      rewrite !from_list_cons, !in_union, !in_singleton. auto. }
    assert (HfreshSmall : fresh
      (fv_config (config_mk (trm_lit (lit_obj T ds) t) fs hSmall eSmall Lsmall))
      2 (y :: w :: nil)%list) by (eapply fresh_decrease_set; eassumption).
    assert (HfreshY : y # hSmall)
      by (eapply fresh_from_machine_for_heap; exact (proj1 HfreshSmall)).
    assert (HfreshW : w # eSmall).
    {
      eapply fresh_from_machine_for_env.
      pose proof (proj1 (proj2 HfreshSmall)) as HF.
      apply notin_union in HF as [HF _]. exact HF.
    }
    pose proof (@red_let_obj T ds t hSmall eSmall Lsmall y w fs HfreshSmall Hdistinct) as Hsmall.
    set (dsNew := deref (eSmall & w ~ y) (open w ds) : defs) in *.
    set (Lnew := fv_config (config_mk (trm_lit (lit_obj T ds) t) fs hSmall eSmall Lsmall)) in *.
    set (Dsmall := config_mk (open w t) fs (hSmall & y ~ item_obj dsNew) (eSmall & w ~ y) Lnew).
    change (config_mk (trm_lit (lit_obj T ds) t) fs hSmall eSmall Lsmall ↦ Dsmall) in Hsmall.
    assert (Have : avoids_store_names H E Dsmall).
    {
      unfold Dsmall. projected_step_safety Hsmall.
      - apply pushed_keys_avoid; [projection_old_keys | exact Hy].
      - apply pushed_keys_avoid; [projection_old_keys | exact Hw].
    }
    assert (Hdefs : deref ((E & eSmall) & w ~ y) (open w ds) = dsNew).
    {
      subst dsNew. rewrite <- concat_assoc.
      eapply replay_resolve_fields with (y := y) (h := hSmall) (t := open w t)
        (fs := fs) (L := Lnew).
      intros q Hq. exact (proj2 (Have q Hq)).
    }
    exists Dsmall. split; [exact Hsmall |].
    unfold Dsmall. cbn [projects_off_stores].
    unfold deref in Hdefs. rewrite Hdefs, (concat_assoc E eSmall (w ~ y)).
    assert (HheapNew : same_valid_bindings
      (H & (hSmall & y ~ item_obj dsNew)) (Sigma & y ~ item_obj dsNew)).
    { apply prefix_preserves_binding_agreement; [exact Hheap |].
      eapply fresh_from_machine_for_heap. exact (proj1 Hfresh). }
    assert (HhNew : ok (hSmall & y ~ item_obj dsNew)) by (now apply ok_push).
    assert (HeNew : ok (eSmall & w ~ y)) by (now apply ok_push).
    project_intro; assumption.
  - pose proof (@red_let_var t hSmall eSmall Lsmall x fs) as Hsmall.
    eexists. split; [exact Hsmall |].
    project_intro; try assumption.
    projected_step_safety Hsmall; projection_old_keys.
  - pose proof (@red_let_push s t fs hSmall eSmall Lsmall) as Hsmall.
    eexists. split; [exact Hsmall |].
    project_intro; try assumption.
    projected_step_safety Hsmall; projection_old_keys.
Qed.

Local Definition machine_store_keys C :=
  dom (config_heap C) \u dom (config_env C).

Local Lemma new_reduction_key_is_fresh C D x :
  C ↦ D ->
  x \notin machine_store_keys C ->
  x \in machine_store_keys D ->
  x \notin fv_config C.
Proof.
  intro Hstep. destruct Hstep;
    intros Hnot Hkeys; unfold machine_store_keys in Hnot, Hkeys;
    cbn [config_heap config_env] in Hnot, Hkeys;
    try solve [exfalso; apply Hnot; exact Hkeys].
  - rewrite dom_push in Hkeys. repeat rewrite in_union in Hkeys.
    rewrite in_singleton in Hkeys.
    destruct Hkeys as [Hh | [-> | He]].
    + exfalso. apply Hnot. rewrite in_union. auto.
    + exact (proj1 H).
    + exfalso. apply Hnot. rewrite in_union. auto.
  - pose proof H as [_ [_ [Hdom _]]]. rewrite <- Hdom in Hkeys. contradiction.
  - repeat rewrite dom_push in Hkeys. repeat rewrite in_union in Hkeys.
    repeat rewrite in_singleton in Hkeys.
    destruct Hkeys as [[-> | Hh] | [-> | He]].
    + exact (proj1 H).
    + exfalso. apply Hnot. rewrite in_union. auto.
    + pose proof (proj1 (proj2 H)) as HF.
      now apply notin_union in HF as [HF _].
    + exfalso. apply Hnot. rewrite in_union. auto.
  - repeat rewrite dom_push in Hkeys. repeat rewrite in_union in Hkeys.
    repeat rewrite in_singleton in Hkeys.
    destruct Hkeys as [[-> | Hh] | [-> | He]].
    + exact (proj1 H).
    + exfalso. apply Hnot. rewrite in_union. auto.
    + pose proof (proj1 (proj2 H)) as HF.
      now apply notin_union in HF as [HF _].
    + exfalso. apply Hnot. rewrite in_union. auto.
Qed.

Local Lemma projected_store_key H E C D :
  projects_off_stores H E C D ->
  forall x, x \in machine_store_keys C <->
    x \in dom H \/ x \in dom E \/ x \in machine_store_keys D.
Proof.
  destruct C as [t fs h e L], D as [t0 fs0 h0 e0 L0].
  intros [_ [_ [[_ [_ Hsame]] [-> _]]]] x.
  unfold machine_store_keys. cbn [config_heap config_env].
  rewrite <- (same_bindings_same_domain Hsame), !dom_concat.
  repeat rewrite in_union. tauto.
Qed.

Local Lemma projected_reduction_preserves_earlier_names H E C D C0 D0 x :
  C ↦ D -> C0 ↦ D0 ->
  projects_off_stores H E C C0 ->
  projects_off_stores H E D D0 ->
  x \in fv_config D0 -> x \notin fv_config C0 ->
  x \notin fv_config C.
Proof.
  intros Hbig Hsmall Hbefore Hafter Hx Hnew.
  assert (Hpresent : x \in machine_store_keys D0).
  {
    pose proof Hbefore as Hpr. destruct C, C0; cbn [projects_off_stores] in Hpr.
    destruct Hpr as [_ [_ [_ [_ [_ [Hh [He _]]]]]]].
    destruct (raw_step_support Hsmall Hh He) as [names [_ [Hallocated Hsupport]]].
    apply Hsupport in Hx. rewrite in_union in Hx. destruct Hx; [contradiction |].
    now apply Hallocated.
  }
  eapply new_reduction_key_is_fresh; [exact Hbig | |].
  - intro Hin. apply (proj1 (@projected_store_key H E C C0 Hbefore x)) in Hin.
    destruct Hin as [Hhere | [Hhere | Hhere]].
    + destruct D, D0; simpl in Hafter.
      destruct Hafter as [_ [_ [_ [_ [_ [_ [_ Havoid]]]]]]].
      exact (proj1 (Havoid _ Hx) Hhere).
    + destruct D, D0; simpl in Hafter.
      destruct Hafter as [_ [_ [_ [_ [_ [_ [_ Havoid]]]]]]].
      exact (proj2 (Havoid _ Hx) Hhere).
    + apply Hnew. destruct C0; unfold machine_store_keys in Hhere; cbn [config_heap config_env] in Hhere.
      rewrite in_union in Hhere. destruct Hhere.
      * now apply dom_heap_in_machine_fv.
      * now apply dom_env_in_machine_fv.
  - apply (proj2 (@projected_store_key H E D D0 Hafter x)). auto.
Qed.

Local Lemma project_independent_raw_run H E C D n :
  C ⊣n↦* D -> ok H ->
  forall C0, projects_off_stores H E C C0 ->
    exists D0, C0 ⊣n↦* D0 /\ projects_off_stores H E D D0 /\
      (forall x, x \in fv_config D0 -> x \notin fv_config C0 -> x \notin fv_config C).
Proof.
  intros Hrun Hok. induction Hrun as [C | C1 C2 C3 n Hrun IH Hstep].
  - intros C0 Hproj. exists C0. split; [constructor |]. split; [exact Hproj |].
    intros x Hin Hout. contradiction.
  - intros C0 Hproj.
    destruct (IH _ Hproj) as [C2' [Hsteps [Hpr Hnames]]].
    destruct (@project_independent_raw_step H E _ _ Hstep Hok _ Hpr) as [C3' [Hlast Hresult]].
    exists C3'. split; [eapply red_trans; eassumption |]. split; [exact Hresult |].
    intros x Hx Hnew.
    destruct (classic (x \in fv_config C2')) as [Hpresent | Habsent].
    + now apply Hnames.
    + intro Hbig. eapply (@projected_reduction_preserves_earlier_names H E C2 C3 C2' C3' x);
        try eassumption.
      eapply raw_steps_keep_free_variables; eassumption.
Qed.

Local Lemma project_run_after_independent_allocation t fs h e L H E Lbig D n :
  ok h -> ok e -> ok H -> ok E ->
  renv_idempotent (E & e) ->
  L \c Lbig ->
  avoids_store_names H E (config_mk t fs h e L) ->
  (config_mk t fs (h & H) (e & E) Lbig) ⊣n↦* D ->
  exists D0 D1,
    (config_mk t fs h e L) ⊣n↦* D0 /\
    raw_store_agreement D D1 /\
    projects_off_stores H E D1 D0 /\
    (forall x, x \in fv_config D0 ->
      x \notin fv_config (config_mk t fs h e L) ->
      x \notin fv_config (config_mk t fs (h & H) (e & E) Lbig)).
Proof.
  intros Hokh Hoke HokH HokE Henv Hmask Havoid Hrun.
  assert (Hh : same_valid_bindings (h & H) (H & h)).
  {
    apply same_valid_bindings_commute; try assumption. intros x Hx Hxb.
    exact (proj1 (Havoid x (@dom_heap_in_machine_fv t fs h e L x Hxb)) Hx).
  }
  assert (He : same_valid_bindings (e & E) (E & e)).
  {
    apply same_valid_bindings_commute; try assumption. intros x Hx Hxb.
    exact (proj2 (Havoid x (@dom_env_in_machine_fv t fs h e L x Hxb)) Hx).
  }
  assert (Hderef : forall ds : defs, deref (e & E) ds = deref (E & e) ds).
  {
    destruct He as [H1 [H2 Hsame]]. intro ds. symmetry.
    apply deref_same_binding; try assumption.
    - unfold renv_idempotent in *.
      rewrite (same_bindings_same_domain Hsame), (fv_env_same_bindings fv H1 H2 Hsame).
      exact Henv.
    - intros x v. symmetry. apply Hsame.
  }
  assert (Hinitial : raw_store_agreement
    (config_mk t fs (h & H) (e & E) Lbig) (config_mk t fs (H & h) (E & e) Lbig)).
  { agreement_split. }
  destruct (@replay_run_same_store _ _ _ n Hrun Hinitial) as [D1 [Hrun1 Hagree]].
  assert (Hproj : projects_off_stores H E
    (config_mk t fs (H & h) (E & e) Lbig) (config_mk t fs h e L)).
  {
    project_intro; try assumption. apply same_valid_bindings_refl.
    exact (proj1 (proj2 Hh)).
  }
  destruct (@project_independent_raw_run H E _ _ n Hrun1 HokH _ Hproj) as [D0 [Hrun0 [Hresult Hnames]]].
  exists D0, D1. split; [exact Hrun0 |]. split; [exact Hagree |]. split; [exact Hresult |].
  intros x Hx Hout.
  rewrite (@raw_store_agreement_free_variables _ _ Hinitial). now apply Hnames.
Qed.

Require Import PreciseTyping TightTyping.

(* Precise projections of an inert object stay within its declared members. *)

Local Lemma bound_inert_type mode G x T :
  @inert mode G -> ctx_binds x T G -> @inert_type mode T.
Proof.
  unfold inert_type. intros Hin. induction Hin; intro Hb; inversion Hb; subst; eauto.
Qed.

Local Lemma inert_object_binding mode G x T :
  mode_has_mutability mode ->
  @inert mode G -> ctx_binds x T G ->
  exists R B, T = typ_objref R (typ_mut_marker B) /\
    record_type R /\ typ_indep_b 0 R.
Proof.
  intros Hmut Hctx Hbind. destruct (bound_inert_type Hctx Hbind) as [k Htype].
  destruct Htype as [S T k Hfun | R C k Hrecord Hcap Hind].
  - pose proof (no_functions_in_mutability_mode mode Hmut). congruence.
  - assert (HC : exists B, C = typ_mut_marker B).
    { destruct mode; cbn in *; try discriminate; inversion Hcap; eauto. }
    destruct HC as [B ->]. eauto 7.
Qed.

Local Lemma record_open_declaration x D :
  record_dec D -> record_dec (open x D).
Proof. intro H. destruct H; constructor. Qed.

Local Lemma record_open_label_set R L x :
  record_typ R L -> record_typ (open x R) L.
Proof.
  intro H. induction H; subst.
  - change (record_typ (typ_rcd (open x D)) \{label_of D}).
    apply rt_one; [now apply record_open_declaration | symmetry; apply opening_keeps_record_label].
  - change (record_typ (typ_and (open x T) (typ_rcd (open x D))) (ls \u \{label_of D})).
    apply rt_cons; try assumption.
    + now apply record_open_declaration.
    + symmetry. apply opening_keeps_record_label.
Qed.

Local Lemma record_open_type R x :
  record_type R -> record_type (open x R).
Proof.
  intros [L HL]. exists L. now apply record_open_label_set.
Qed.

Local Lemma record_type_and_components A B :
  record_type (typ_and A B) -> record_type A /\ record_type B.
Proof.
  intros [L HL]. inversion HL; subst.
  split; [eexists; eassumption |].
  eexists. apply rt_one; [eassumption | reflexivity].
Qed.

Local Lemma record_type_not_binder R :
  record_type (typ_bnd R) -> False.
Proof. intros [L H]. inversion H. Qed.

Local Lemma record_has_is_declared R L D :
  record_typ R L -> record_has R D ->
  record_dec D /\ label_of D \in L.
Proof.
  intros H. induction H; intros HD; inversion HD; subst.
  - split; [assumption | apply in_singleton_self].
  - destruct (IHrecord_typ ltac:(assumption)) as [Hd Hl].
    split; [exact Hd | rewrite in_union; auto].
  - match goal with H : record_has (typ_rcd _) _ |- _ => inversion H; subst end.
    split; [assumption | rewrite in_union; right; apply in_singleton_self].
Qed.

Local Lemma record_has_same_label_unique R L D1 D2 :
  record_typ R L -> record_has R D1 -> record_has R D2 ->
  label_of D1 = label_of D2 -> D1 = D2.
Proof.
  intros H. revert D1 D2. induction H; intros D1 D2 HD1 HD2 Heq;
    inversion HD1; inversion HD2; subst; eauto.
  all: repeat match goal with H : record_has (typ_rcd _) _ |- _ =>
    inversion H; subst; clear H
  end.
  all: try reflexivity.
  all: exfalso; match goal with
    | Hout : label_of ?D \notin ?ls, Hr : record_typ ?T ?ls,
      Hd : record_has ?T ?D' |- _ =>
        apply Hout; rewrite Heq || rewrite <- Heq;
        exact (proj2 (@record_has_is_declared T ls D' Hr Hd))
    end.
Qed.

Local Lemma projected_record_members x R S :
  open_proj x R S ->
  record_type R ->
  record_type S /\ (forall D, record_has S D -> record_has R D).
Proof.
  intro H. induction H; intro HR.
  - auto.
  - destruct (IHopen_proj HR) as [Hfalse _]. exact (False_rect _ (record_type_not_binder Hfalse)).
  - destruct (IHopen_proj HR) as [Hboth Hmembers].
    destruct (record_type_and_components Hboth) as [Hleft _].
    split; [exact Hleft | intros D HD; now apply Hmembers, rh_andl].
  - destruct (IHopen_proj HR) as [Hboth Hmembers].
    destruct (record_type_and_components Hboth) as [_ Hright].
    split; [exact Hright | intros D HD; eapply Hmembers, rh_andr; eassumption].
Qed.

Local Lemma project_nominal_object x R B U :
  open_proj x (typ_objref R (typ_mut_marker B)) U ->
  record_type R ->
  U = typ_objref R (typ_mut_marker B) \/
  U = typ_bnd R \/ U = typ_mut_marker B \/
  (record_type U /\ forall D, record_has U D -> record_has (open x R) D).
Proof.
  intros H. remember (typ_objref R (typ_mut_marker B)) as V eqn:HV in H.
  induction H; intros HR.
  - auto.
  - subst. specialize (IHopen_proj HR).
    destruct IHopen_proj as [E | [E | [E | [Hfalse _]]]]; try discriminate.
    + injection E as ->. do 3 right. split; auto using record_open_type.
    + exfalso. exact (record_type_not_binder Hfalse).
  - subst. specialize (IHopen_proj HR).
    destruct IHopen_proj as [E | [E | [E | [Hrecord Hmember]]]]; try discriminate.
    + injection E as -> ->. auto.
    + destruct (record_type_and_components Hrecord) as [Hleft _].
      do 3 right. split; [exact Hleft | intros D HD; now apply Hmember, rh_andl].
  - subst. specialize (IHopen_proj HR).
    destruct IHopen_proj as [E | [E | [E | [Hrecord Hmember]]]]; try discriminate.
    + injection E as -> ->. auto.
    + destruct (record_type_and_components Hrecord) as [_ Hright].
      do 3 right. split; [exact Hright | intros D HD; eapply Hmember, rh_andr; eassumption].
Qed.

Local Lemma precise_flow_projects x G T U :
  precise_flow x G T U -> ctx_binds x T G /\ open_proj x T U.
Proof. intro H. induction H; intuition eauto using open_proj. Qed.

Local Lemma precise_flow_member x G T R D :
  precise_flow x G T R -> record_has R D ->
  precise_flow x G T (typ_rcd D).
Proof.
  intros HF HD. induction HD; eauto using precise_flow.
Qed.

Local Definition precise_member G x D :=
  exists T, precise_flow x G T (typ_rcd D).

Local Lemma precise_object_member x G R B D :
  ctx_binds x (typ_objref R (typ_mut_marker B)) G ->
  record_type R ->
  precise_member G x D ->
  D = dec_typ (typ_label_refcap typ_refcap_mutability) typ_bot B \/
  record_has (open x R) D.
Proof.
  intros Hb HR [T HF].
  destruct (precise_flow_projects HF) as [HT Hproj].
  pose proof (ctx_binds_unique HT Hb) as ->.
  destruct (project_nominal_object Hproj HR) as [E | [E | [E | [_ HM]]]];
    try discriminate.
  - now left; injection E as ->.
  - right. apply HM. constructor.
Qed.

Local Lemma precise_member_declared x G R B D :
  ctx_binds x (typ_objref R (typ_mut_marker B)) G ->
  record_has (open x R) D ->
  precise_member G x D.
Proof.
  intros Hb Hd. eexists.
  eapply precise_flow_member; [|exact Hd].
  apply pf_open, pf_and1 with (U2 := typ_mut_marker B), pf_bind. exact Hb.
Qed.

Local Lemma precise_member_inert_type_bounds mode G x A S T :
  mode_has_mutability mode -> @inert mode G ->
  precise_member G x (dec_typ A S T) ->
  S = typ_bot \/ S = T.
Proof.
  intros Hmut Hin Hm.
  destruct Hm as [U HU].
  pose proof (proj1 (precise_flow_projects HU)) as HB.
  destruct (inert_object_binding Hmut Hin HB) as [R [B [-> [HR _]]]].
  assert (HM : precise_member G x (dec_typ A S T)) by (unfold precise_member; eauto).
  destruct (precise_object_member HB HR HM) as [Heq | Hdeclared].
  - inversion Heq; auto.
  - destruct (record_open_type x HR) as [L HL].
    destruct (record_has_is_declared HL Hdeclared) as [HD _].
    inversion HD; auto.
Qed.

Local Lemma precise_type_member_unique mode G x A S1 T1 S2 T2 :
  mode_has_mutability mode -> @inert mode G ->
  precise_member G x (dec_typ A S1 T1) ->
  precise_member G x (dec_typ A S2 T2) ->
  S1 = S2 /\ T1 = T2.
Proof.
  intros Hmut Hin H1 H2.
  destruct H1 as [U HU].
  pose proof (proj1 (precise_flow_projects HU)) as Hb.
  destruct (inert_object_binding Hmut Hin Hb) as [R [B [-> [HR _]]]].
  assert (H1 : precise_member G x (dec_typ A S1 T1)) by (eexists; exact HU).
  destruct (precise_object_member Hb HR H1) as [Heq1 | Hr1];
  destruct (precise_object_member Hb HR H2) as [Heq2 | Hr2].
  - split; congruence.
  - inversion Heq1; subst. destruct (record_open_type x HR) as [L HL].
    destruct (record_has_is_declared HL Hr2) as [HD _]. inversion HD.
  - inversion Heq2; subst. destruct (record_open_type x HR) as [L HL].
    destruct (record_has_is_declared HL Hr1) as [HD _]. inversion HD.
  - destruct (record_open_type x HR) as [L HL].
    assert (Heq : dec_typ A S1 T1 = dec_typ A S2 T2)
      by (eapply record_has_same_label_unique; eassumption || reflexivity).
    inversion Heq; auto.
Qed.

Local Definition nominal_record_binding G x R :=
  exists B, ctx_binds x (typ_objref R B) G.

Local Lemma alias_nominal_record_binding mode G e x y :
  ctx_ok G -> @renv_corr mode G e ->
  tyq_var e x y -> forall R,
    nominal_record_binding G x R <-> nominal_record_binding G y R.
Proof.
  intros Hok Hcorr H. induction H; intro R; try reflexivity.
  - destruct (renv_corresponding_bindings Hcorr Hok H) as [X [Y [Hx [Hy HC]]]].
    destruct HC as [R' B C Hcap | S T Hfun].
    + unfold nominal_record_binding. split; intros [A HA].
      * pose proof (ctx_binds_unique Hx HA) as Heq. injection Heq as -> _. eauto.
      * pose proof (ctx_binds_unique Hy HA) as Heq. injection Heq as -> _. eauto.
    + split; intros [A HA].
      * pose proof (ctx_binds_unique Hx HA). discriminate.
      * pose proof (ctx_binds_unique Hy HA). discriminate.
  - symmetry. now apply IHtyq_var.
  - transitivity (nominal_record_binding G v2 R); eauto.
Qed.

Local Lemma equivalent_records_transfer_members e R Q D :
  record_has R D -> tyq_typ e R Q ->
  exists D', record_has Q D' /\ tyq_typ e (typ_rcd D) (typ_rcd D').
Proof.
  intros H. revert Q. induction H; intros Q Heq.
  - inversion Heq; subst;
      repeat match goal with H : typ_andor _ |- _ => destruct H end; try discriminate;
      solve [eexists; split; [apply rh_one | exact Heq]].
  - inversion Heq; subst; try discriminate.
    + match goal with Hn : typ_nulary (typ_and _ _) |- _ => inversion Hn end.
    + match goal with Ho : typ_andor _ |- _ => destruct Ho end; try discriminate.
      match goal with Hshape : typ_and _ _ = typ_and _ _ |- _ =>
        inversion Hshape; subst end.
      match goal with Hlt : e ⊢ T ≈ _ |- _ =>
        destruct (IHrecord_has _ Hlt) as [D' [HD' HE']]
      end.
      exists D'. split; [now apply rh_andl | exact HE'].
  - inversion Heq; subst; try discriminate.
    + match goal with Hn : typ_nulary (typ_and _ _) |- _ => inversion Hn end.
    + match goal with Ho : typ_andor _ |- _ => destruct Ho end; try discriminate.
      match goal with Hshape : typ_and _ _ = typ_and _ _ |- _ =>
        inversion Hshape; subst end.
      match goal with Hlt : e ⊢ U ≈ _ |- _ =>
        destruct (IHrecord_has _ Hlt) as [D' [HD' HE']]
      end.
      exists D'. split; [now apply rh_andr | exact HE'].
Qed.

Local Lemma aliased_nominal_normal_type_member mode G e x y A S T :
  mode_has_mutability mode -> @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  tyq_var e x y ->
  precise_member G x (dec_typ (typ_label_normal A) S T) ->
  exists S' T', precise_member G y (dec_typ (typ_label_normal A) S' T') /\
    (forall u, tyq_typ e (open u S) (open u S')) /\
    (forall u, tyq_typ e (open u T) (open u T')).
Proof.
  intros Hmut Hin Hok Hcorr Hxy Hm. destruct Hm as [U HU].
  pose proof (proj1 (precise_flow_projects HU)) as Hb.
  destruct (inert_object_binding Hmut Hin Hb) as [R [B [-> [HR Hind]]]].
  assert (Hmember : precise_member G x (dec_typ (typ_label_normal A) S T))
    by (eexists; exact HU).
  destruct (precise_object_member Hb HR Hmember) as [Hbad | Hdecl]; [discriminate |].
  assert (Hnom : nominal_record_binding G x R) by (eexists; exact Hb).
  apply (alias_nominal_record_binding Hok Hcorr Hxy R) in Hnom.
  destruct Hnom as [B' Hbound].
  pose proof (opening_independent_type_with_alias Hxy Hind) as Heq.
  destruct (equivalent_records_transfer_members Hdecl Heq) as [D' [HD' Hsame]].
  inversion Hsame; subst; try discriminate.
  all: repeat match goal with H : typ_andor _ |- _ => destruct H end; try discriminate.
  all: try solve [match goal with Hn : typ_nulary (typ_rcd _) |- _ => inversion Hn end].
  exists t21, t22. split; [|auto].
  exists (typ_objref R B'). eapply precise_flow_member; [|exact HD'].
  apply pf_open, pf_and1 with (U2 := B'), pf_bind. exact Hbound.
Qed.

Local Lemma precise_flow_inert_has_type mode G e x T U :
  mode_has_mutability mode -> @inert mode G ->
  precise_flow x G T U -> ty_var mode G objctx_empty e x U.
Proof.
  intros Hmut Hin Hflow. induction Hflow.
  - now apply ty_var_var.
  - destruct (precise_flow_projects Hflow) as [Hb Hp].
    destruct (inert_object_binding Hmut Hin Hb) as [R [B [-> [HR Hind]]]].
    assert (Hind' : typ_indep_b 0 U).
    {
      destruct (project_nominal_object Hp HR) as [Heq | [Heq | [Heq | [Hbad _]]]]; try discriminate.
      - inversion Heq; subst. exact Hind.
      - exfalso. exact (record_type_not_binder Hbad).
    }
    apply ty_rec_elim; [exact (IHHflow Hin) | exact Hind'].
  - eapply ty_var_sub. unfold obj_typing, subtyping.
    + exact (IHHflow Hin).
    + apply subtyp_and11.
  - eapply ty_var_sub. unfold obj_typing, subtyping.
    + exact (IHHflow Hin).
    + apply subtyp_and12.
Qed.

Local Lemma tight_subtyping_in_inert_context mode G e S T :
  subtyp_t mode G e S T ->
  mode_has_mutability mode -> @inert mode G ->
  subtyp mode G objctx_empty e S T.
Proof.
  intro H. induction H; intros Hmut Hin;
    unfold subtyping in *.
  - apply subtyp_top.
  - apply subtyp_bot.
  - apply subtyp_refl.
  - eapply subtyp_trans; unfold subtyping; eauto.
  - apply subtyp_and11.
  - apply subtyp_and12.
  - apply subtyp_and2; unfold subtyping; eauto.
  - apply subtyp_or11.
  - apply subtyp_or12.
  - apply subtyp_or2; unfold subtyping; eauto.
  - apply subtyp_fld; unfold subtyping; eauto.
  - apply subtyp_typ; unfold subtyping; eauto.
  - eapply subtyp_sel2; unfold obj_typing.
    eapply precise_flow_inert_has_type; eassumption.
  - eapply subtyp_sel1; unfold obj_typing.
    eapply precise_flow_inert_has_type; eassumption.
  - eapply subtyp_fun; unfold subtyping; eauto.
  - eapply subtyp_met; unfold subtyping; eauto.
  - apply subtyp_tyq. assumption.
  - apply subtyp_typ_and.
  - apply subtyp_dist.
  - apply subtyp_nocap_bnd.
  - apply subtyp_nocap_typ.
  - apply subtyp_nocap_fld.
  - apply subtyp_nocap_met.
  - apply subtyp_nocap_fun. assumption.
  - apply subtyp_nocap_mut_top_boundless. assumption.
  - apply subtyp_nocap_mut_top_complement. assumption.
  - apply subtyp_nocap_mut_bot. assumption.
  - apply subtyp_mut_top. assumption.
Qed.

(* A shape can retain the variance information of its declared member. *)

Inductive accepted_shape (G : ctx) (x : var) (decl : dec -> Prop) (K : typ -> Prop) : typ -> Prop :=
| accepted_top : accepted_shape G x decl K typ_top
| accepted_and S T :
    accepted_shape G x decl K S -> accepted_shape G x decl K T ->
    accepted_shape G x decl K (typ_and S T)
| accepted_or_left S T : accepted_shape G x decl K S ->
    accepted_shape G x decl K (typ_or S T)
| accepted_or_right S T : accepted_shape G x decl K T ->
    accepted_shape G x decl K (typ_or S T)
| accepted_record D : decl D -> accepted_shape G x decl K (typ_rcd D)
| accepted_fun S T : accepted_shape G x decl K (typ_fun S T)
| accepted_binder T : accepted_shape G x decl K (open x T) -> K (open x T) ->
    accepted_shape G x decl K (typ_bnd T)
| accepted_selection v A w S T :
    precise_member G v (dec_typ A S T) ->
    accepted_shape G x decl K (open w T) ->
    accepted_shape G x decl K (typ_sel (avar_f v) A (avar_f w)).

Inductive atomic_declaration_widens mode G e : dec -> dec -> Prop :=
| widen_decl_equiv D D' :
    tyq_typ e (typ_rcd D) (typ_rcd D') -> atomic_declaration_widens mode G e D D'
| widen_decl_fld a W S V T :
    subtyp mode G objctx_empty e W S ->
    subtyp mode G objctx_empty e T V ->
    atomic_declaration_widens mode G e (dec_fld a S T) (dec_fld a W V)
| widen_decl_typ A W S V T :
    (forall x, subtyp_t mode G e (open x W) (open x S)) ->
    (forall x, subtyp_t mode G e (open x T) (open x V)) ->
    atomic_declaration_widens mode G e (dec_typ A S T) (dec_typ A W V)
| widen_decl_met m C Z V C' Z' V' L :
    subtyp mode G objctx_empty e Z' Z ->
    (forall z, z \notin L ->
      subtyp mode (G § z / v_par ~ Z') objctx_empty e (open z C') (open z C)) ->
    (mode_has_sef mode -> typ_indep_b 0 C' -> typ_indep_b 0 C) ->
    (forall z, z \notin L -> forall c, c <> z -> c \notin L ->
      subtyp mode (ctx_met G z Z' c C') objctx_empty e
        (open_met z c V) (open_met z c V')) ->
    atomic_declaration_widens mode G e (dec_met m C Z V) (dec_met m C' Z' V').

Local Definition accepted_declarations mode G e (decl : dec -> Prop) :=
  (forall A S T, decl (dec_typ (typ_label_refcap A) S T)) /\
  (forall D D', atomic_declaration_widens mode G e D D' -> decl D -> decl D') /\
  (forall A S1 T1 S2 T2, decl (dec_typ A S1 T1) -> decl (dec_typ A S2 T2) ->
    decl (dec_typ A (typ_or S1 S2) (typ_and T1 T2))).

Local Lemma accepted_shape_follows_type_equivalence mode G e x P K :
  mode_has_mutability mode -> @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  accepted_declarations mode G e P ->
  (forall S T, tyq_typ e S T -> K S -> K T) ->
  forall S T, accepted_shape G x P K S -> tyq_typ e S T -> accepted_shape G x P K T.
Proof.
  intros Hmut Hin Hok Hcorr [Htypes [Hdec _]] HK S T Hshape.
  revert T. induction Hshape; intros U HE;
    inversion HE; subst; try discriminate.
  all: repeat match goal with Hn : typ_nulary _ |- _ => inversion Hn; subst; clear Hn end.
  all: repeat match goal with Ho : typ_andor _ |- _ => destruct Ho end;
    try discriminate.
  all: repeat match goal with H : typ_and _ _ = typ_and _ _ |- _ => inversion H; clear H; subst end.
  all: repeat match goal with H : typ_or _ _ = typ_or _ _ |- _ => inversion H; clear H; subst end.
  all: unfold typing_equiv in *.
  all: try solve [eauto 7 using accepted_shape, atomic_declaration_widens].
  match goal with Hm : precise_member G ?r (dec_typ (typ_label_normal ?A) ?S ?T),
    Hr : tyq_var e ?r ?r' |- _ =>
      destruct (aliased_nominal_normal_type_member Hmut Hin Hok Hcorr Hr Hm)
        as [S' [T' [Hmem [Hlo Hhi]]]]
  end.
  eapply accepted_selection; [exact Hmem |]. eapply IHHshape; apply Hhi.
Qed.

Local Lemma tight_subtyping_preserves_shape mode G e S T :
  subtyp_t mode G e S T ->
  mode_has_mutability mode -> @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  forall x P K, accepted_declarations mode G e P ->
    (forall S T, tyq_typ e S T -> K S -> K T) ->
    accepted_shape G x P K S -> accepted_shape G x P K T.
Proof.
  intro H. induction H; intros Hmut Hin Hok Hcorr r P K Hdecl HK Hshape.
  all: pose proof (proj1 Hdecl) as Htypes; pose proof (proj2 Hdecl) as [Hmembers Hmerge].
  - apply accepted_top.
  - inversion Hshape.
  - exact Hshape.
  - eapply IHsubtyp_t2; try assumption. eapply IHsubtyp_t1; eassumption.
  - inversion Hshape; assumption.
  - inversion Hshape; assumption.
  - apply accepted_and; eauto.
  - now apply accepted_or_left.
  - now apply accepted_or_right.
  - inversion Hshape; subst; eauto.
  - inversion Hshape; subst.
    apply accepted_record. eapply Hmembers; [|eassumption].
    apply widen_decl_fld; eapply tight_subtyping_in_inert_context; eassumption.
  - inversion Hshape; subst.
    apply accepted_record. eapply Hmembers; [|eassumption].
    apply widen_decl_typ; eauto.
  - assert (Hmember : precise_member G x (dec_typ A TL TU))
      by (eexists; eassumption).
    destruct (precise_member_inert_type_bounds Hmut Hin Hmember) as [E | E]; subst TL.
    + inversion Hshape.
    + eapply accepted_selection; eassumption.
  - assert (Hmember : precise_member G x (dec_typ A TL TU))
      by (eexists; eassumption).
    inversion Hshape; subst.
    match goal with
    | Hm : precise_member G x (dec_typ A ?SL ?SU) |- _ =>
        assert (E : SU = TU) by
          (exact (proj2 (@precise_type_member_unique mode G x A SL SU TL TU Hmut Hin Hm Hmember)));
        now subst SU
    end.
  - apply accepted_fun.
  - inversion Hshape; subst.
    apply accepted_record. eapply Hmembers; [|eassumption].
    eapply widen_decl_met; unfold subtyping in *; try eassumption.
    eapply tight_subtyping_in_inert_context; eassumption.
  - eapply accepted_shape_follows_type_equivalence; eassumption.
  - inversion Hshape; subst.
    apply accepted_record. apply Hmerge;
      match goal with H : accepted_shape _ _ _ _ (typ_rcd _) |- _ => inversion H; subst; assumption end.
  - inversion Hshape; subst.
    match goal with
    | Hor : accepted_shape _ _ _ _ (typ_or _ _) |- _ =>
        inversion Hor; subst; eauto using accepted_shape
    end.
  - inversion Hshape.
  - inversion Hshape.
  - inversion Hshape.
  - inversion Hshape.
  - inversion Hshape.
  - apply accepted_or_right, accepted_record, Htypes.
  - apply accepted_or_right, accepted_record, Htypes.
  - inversion Hshape; subst.
    match goal with Hn : accepted_shape _ _ _ _ typ_nocap |- _ => inversion Hn end.
  - apply accepted_record, Htypes.
Qed.

Local Definition shape_gate_is_closed mode G e (K : typ -> Prop) :=
  (forall S U, tyq_typ e S U -> K S -> K U) /\
  (forall S U, subtyp_t mode G e S U -> K S -> K U) /\
  (forall S U, K S -> K U -> K (typ_and S U)) /\
  (forall T, K (typ_bnd T)) /\
  K (typ_mut_marker typ_top).

Local Lemma tight_typing_preserves_shape_and_gate mode G e x T :
  ty_trm_t mode G e x T ->
  mode_has_mutability mode -> @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  forall P K, accepted_declarations mode G e P ->
    shape_gate_is_closed mode G e K ->
    (forall U, ctx_binds x U G -> accepted_shape G x P K U /\ K U) ->
    accepted_shape G x P K T /\ K T.
Proof.
  intro H. induction H; intros Hmut Hin Hok Hcorr P K HP HK Hb.
  all: pose proof HK as [Heq [Hsub [Hand [Hbnd Htop]]]].
  - auto.
  - match goal with IH : forall (_ : mode_has_mutability mode), _ |- _ =>
      destruct (IH Hmut Hin Hok Hcorr P K HP HK Hb) as [HS HG]
    end.
    split; [now apply accepted_binder | apply Hbnd].
  - match goal with IH : forall (_ : mode_has_mutability mode), _ |- _ =>
      destruct (IH Hmut Hin Hok Hcorr P K HP HK Hb) as [HS _]
    end.
    now inversion HS.
  - destruct (IHty_trm_t Hmut Hin Hok Hcorr P K HP HK Hb) as [Hleft Kleft].
    destruct (IHty_trm_t0 Hmut Hin Hok Hcorr P K HP HK Hb) as [Hright Kright].
    split; [now apply accepted_and | auto].
  - match goal with IH : forall (_ : mode_has_mutability mode), _ |- _ =>
      destruct (IH Hmut Hin Hok Hcorr P K HP HK Hb) as [HS HG]
    end.
    split; [eapply tight_subtyping_preserves_shape; eassumption | eapply Hsub; eassumption].
  - split; [apply accepted_record, (proj1 HP) | exact Htop].
Qed.

Local Lemma tight_typing_preserves_shape mode G e x T :
  ty_trm_t mode G e x T ->
  mode_has_mutability mode -> @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  forall P, accepted_declarations mode G e P ->
    (forall U, ctx_binds x U G -> accepted_shape G x P (fun _ => True) U) ->
    accepted_shape G x P (fun _ => True) T.
Proof.
  intros Hty Hmut Hin Hok Hcorr P HP Hb.
  assert (HG : shape_gate_is_closed mode G e (fun _ => True)).
  { repeat split; intros; exact I. }
  assert (HB : forall U, ctx_binds x U G ->
    accepted_shape G x P (fun _ => True) U /\ True).
  { intros U HU. split; [now apply Hb | exact I]. }
  exact (proj1 (@tight_typing_preserves_shape_and_gate mode G e x T Hty
    Hmut Hin Hok Hcorr P (fun _ => True) HP HG HB)).
Qed.

Local Lemma declared_record_accepted G x P K R :
  record_type R ->
  (forall D, record_has R D -> P D) ->
  accepted_shape G x P K R.
Proof.
  intros [L HR]. induction HR; intro Haccept.
  - apply accepted_record, Haccept, rh_one.
  - apply accepted_and.
    + apply IHHR. intros E HE. apply Haccept. now apply rh_andl.
    + apply accepted_record, Haccept, rh_andr, rh_one.
Qed.

Local Lemma equiv_type_is_symmetric e T U :
  tyq_typ e T U -> tyq_typ e U T.
Proof.
  intro H. induction H; unfold typing_equiv in *.
  - now apply tyq_typ_nulary.
  - eapply tyq_typ_andor; eassumption.
  - apply tyq_typ_fun; unfold typing_equiv; assumption.
  - apply tyq_typ_fld; unfold typing_equiv; assumption.
  - apply tyq_typ_typ; unfold typing_equiv; assumption.
  - apply tyq_typ_sel_normal, tyq_var_sym. assumption.
  - apply tyq_typ_sel.
  - apply tyq_typ_bnd. assumption.
  - apply tyq_typ_met; unfold typing_equiv; assumption.
Qed.

Local Definition nominal_field_consequence mode G e R a (d : dec) :=
  match d with
  | dec_fld l W V => l = a -> exists S,
      record_has R (dec_fld a S S) /\
      subtyp mode G objctx_empty e W S /\ subtyp mode G objctx_empty e S V
  | _ => True
  end.

Local Lemma nominal_field_accepted mode G e R a :
  accepted_declarations mode G e (nominal_field_consequence mode G e R a).
Proof.
  split; [intros; exact I |].
  split; [|intros; exact I].
  intros D D' H. destruct H.
  - destruct D'; try (intros; exact I).
    intro Hfield. inversion H; subst; try discriminate.
    all: try solve [match goal with Hn : typ_nulary (typ_rcd _) |- _ => inversion Hn end].
    all: repeat match goal with Ho : typ_andor _ |- _ => destruct Ho end; try discriminate.
    unfold nominal_field_consequence, typing_equiv in *.
    intros [S [HS [HW HV]]]%Hfield.
    exists S. split; [exact HS |]. split.
    + eapply subtyp_trans; unfold subtyping; [|exact HW].
      apply equivalent_type_subtypes, equiv_type_is_symmetric. assumption.
    + eapply subtyp_trans; unfold subtyping; [exact HV |].
      apply equivalent_type_subtypes. assumption.
  - intros Hsource Ha. destruct (Hsource Ha) as [U [HU [HS HT]]].
    exists U. split; [exact HU |].
    split; eapply subtyp_trans; unfold subtyping; eassumption.
  - intros; exact I.
  - intros; exact I.
Qed.

Local Lemma tight_field_projection_uses_nominal_type mode G e x R B a W V :
  mode_has_mutability mode -> @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  record_type R ->
  ctx_binds x (typ_objref R (typ_mut_marker B)) G ->
  ty_trm_t mode G e x (typ_rcd (dec_fld a W V)) ->
  exists S,
    record_has (open x R) (dec_fld a S S) /\
    subtyp mode G objctx_empty e W S /\ subtyp mode G objctx_empty e S V.
Proof.
  intros Hmut Hin Hok Hcorr HR Hbind Htight.
  set (P := nominal_field_consequence mode G e (open x R) a).
  assert (Hb : forall U, ctx_binds x U G -> accepted_shape G x P (fun _ => True) U).
  {
    intros U Hu. pose proof (ctx_binds_unique Hu Hbind) as ->.
    apply accepted_and.
    - apply accepted_binder; [|exact I].
      apply declared_record_accepted; [now apply record_open_type |].
      intros [A W' V' | l W' V' | m C Z T] Hmem; try exact I.
      unfold P, nominal_field_consequence.
      intro Ha. subst l.
      destruct (record_open_type x HR) as [L HL].
      destruct (record_has_is_declared HL Hmem) as [HD _]. inversion HD; subst.
      eexists. split; [exact Hmem |]. split; apply subtyp_refl.
    - apply accepted_record. exact I.
  }
  pose proof (@tight_typing_preserves_shape mode G e x _ Htight Hmut Hin Hok Hcorr P
    (nominal_field_accepted mode G e (open x R) a) Hb) as Hshape.
  inversion Hshape; subst.
  match goal with HP : P (dec_fld a W V) |- _ => exact (HP eq_refl) end.
Qed.

Local Fixpoint independent_bound_type k (T : typ) : Prop :=
  match T with
  | typ_rcd D => independent_bound_dec k D
  | typ_and U V | typ_or U V => independent_bound_type k U /\ independent_bound_type k V
  | typ_bnd U => independent_bound_type (S k) U
  | typ_fun U V => independent_bound_type k U /\ independent_bound_type (S k) V
  | typ_sel x A y => y <> avar_b k /\
      match A with typ_label_normal _ => True | typ_label_refcap _ => x <> avar_b k end
  | _ => True
  end
with independent_bound_dec k (D : dec) : Prop :=
  match D with
  | dec_typ _ U V => independent_bound_type (S k) U /\ independent_bound_type (S k) V
  | dec_fld _ U V => independent_bound_type k U /\ independent_bound_type k V
  | dec_met _ C Z R => independent_bound_type (S k) C /\ independent_bound_type k Z /\
      independent_bound_type (S (S k)) R
  end.

Local Lemma independent_bound_characterization :
  (forall T k, independent_bound_type k T <-> typ_indep_b k T) /\
  (forall D k, independent_bound_dec k D <-> typ_indep_b k (typ_rcd D)).
Proof.
  apply typ_mutind; intros; cbn [independent_bound_type independent_bound_dec].
  all: try solve [split; [intros _; apply typ_indep_nulary; constructor | intros; exact I]].
  all: try solve [apply H].
  all: rewrite ?H, ?H0, ?H1.
  all: try solve [
    split; intro Ht;
    [ first [apply typ_indep_and | apply typ_indep_or | apply typ_indep_bnd_b
            | apply typ_indep_fun_b | apply typ_indep_typ_b | apply typ_indep_fld
            | apply typ_indep_met_b]; tauto
    | inversion Ht; subst;
      try solve [match goal with Hn : typ_nulary _ |- _ => inversion Hn end];
      tauto ]].
  destruct t.
  - split.
    + intros [Hy _]. apply typ_indep_sel_normal. congruence.
    + inversion 1; subst;
        try solve [match goal with Hn : typ_nulary _ |- _ => inversion Hn end].
      all: split; [congruence | exact I].
  - split.
    + intros [Hy Hx]. apply typ_indep_sel; congruence.
    + inversion 1; subst;
      try solve [match goal with Hn : typ_nulary _ |- _ => inversion Hn end].
      split; congruence.
Qed.

Local Fixpoint independent_free_type x (T : typ) : Prop :=
  match T with
  | typ_rcd D => independent_free_dec x D
  | typ_and U V | typ_or U V | typ_fun U V =>
      independent_free_type x U /\ independent_free_type x V
  | typ_bnd U => independent_free_type x U
  | typ_sel a A b => b <> avar_f x /\
      match A with typ_label_normal _ => True | typ_label_refcap _ => a <> avar_f x end
  | _ => True
  end
with independent_free_dec x (D : dec) : Prop :=
  match D with
  | dec_typ _ U V | dec_fld _ U V => independent_free_type x U /\ independent_free_type x V
  | dec_met _ C Z R =>
      independent_free_type x C /\ independent_free_type x Z /\ independent_free_type x R
  end.

Local Lemma opening_fresh_name_preserves_independence :
  (forall (T : typ) n x, x \notin fv T ->
    independent_free_type x (open_rec n x T) <-> independent_bound_type n T) /\
  (forall (D : dec) n x, x \notin fv D ->
    independent_free_dec x (open_rec n x D) <-> independent_bound_dec n D).
Proof.
  assert (HA : forall (a : avar) n x, x \notin fv a ->
    (open_rec n x a <> avar_f x <-> a <> avar_b n)).
  {
    intros [k | y] n x Hfresh.
    - unfold open_rec, AvarOpenable. case_if; split; congruence.
    - change (x \notin \{y}) in Hfresh. rewrite notin_singleton in Hfresh.
      change (avar_f y <> avar_f x <-> avar_f y <> avar_b n). split; congruence.
  }
  apply typ_mutind; intros;
    cbn [open_rec TypOpenable DecOpenable open_rec_typ open_rec_dec
         independent_free_type independent_free_dec independent_bound_type independent_bound_dec];
    repeat rewrite ?H, ?H0, ?H1 by
      (cbn [fv TypFreeVar DecFreeVar fv_typ fv_dec] in *; fresh_fv; assumption);
    try reflexivity.
  destruct t; cbn; repeat rewrite HA by
    (cbn [fv TypFreeVar fv_typ] in *; fresh_fv; assumption); reflexivity.
Qed.

Local Lemma free_independence_survives_other_openings :
  (forall (T : typ) d x y, x <> y ->
    independent_free_type x (open_rec d y T) <-> independent_free_type x T) /\
  (forall (D : dec) d x y, x <> y ->
    independent_free_dec x (open_rec d y D) <-> independent_free_dec x D).
Proof.
  assert (Ha : forall (a : avar) d x y, x <> y ->
    (open_rec d y a <> avar_f x <-> a <> avar_f x)).
  {
    intros [n | z] d x y Hneq.
    - unfold open_rec, AvarOpenable. case_if; split; congruence.
    - reflexivity.
  }
  apply typ_mutind; intros;
    cbn [open_rec TypOpenable DecOpenable open_rec_typ open_rec_dec
         independent_free_type independent_free_dec];
    repeat rewrite ?H, ?H0, ?H1 by assumption; try reflexivity.
  destruct t; cbn; repeat rewrite Ha by assumption; reflexivity.
Qed.

Local Lemma type_equiv_preserves_free_independence e S T :
  tyq_typ e S T -> forall x, independent_free_type x S <-> independent_free_type x T.
Proof.
  intro H. induction H as
    [e T Hnull
    | constr e A B U V Hconstr Hleft IHleft Hright IHright
    | e A B U V Harg IHarg Hbody IHbody
    | e a A B U V Hread IHread Hwrite IHwrite
    | e a A B U V Hlow IHlow Hhigh IHhigh
    | e x y z A Hxy
    | e x y A
    | e A B Hbody IHbody
    | m e C Z R C' Z' R' Hrecv IHrecv Harg IHarg Hresult IHresult];
    intro w; cbn [independent_free_type independent_free_dec]; try reflexivity.
  - destruct Hconstr; cbn [independent_free_type independent_free_dec];
      now rewrite IHleft, IHright.
  - destruct (var_fresh \{w}) as [x Hx]. rewrite notin_singleton in Hx.
    pose proof (IHbody x w) as HB.
    repeat rewrite (proj1 free_independence_survives_other_openings) in HB by congruence.
    now rewrite IHarg, HB.
  - now rewrite IHread, IHwrite.
  - destruct (var_fresh \{w}) as [x Hx]. rewrite notin_singleton in Hx.
    pose proof (IHlow x w) as HL. pose proof (IHhigh x w) as HU.
    repeat rewrite (proj1 free_independence_survives_other_openings) in HL by congruence.
    repeat rewrite (proj1 free_independence_survives_other_openings) in HU by congruence.
    now rewrite HL, HU.
  - destruct (var_fresh \{w}) as [x Hx]. rewrite notin_singleton in Hx.
    pose proof (IHbody x w) as HB.
    repeat rewrite (proj1 free_independence_survives_other_openings) in HB by congruence.
    exact HB.
  - destruct (var_fresh \{w}) as [x Hx]. rewrite notin_singleton in Hx.
    pose proof (IHrecv x w) as HC.
    pose proof (IHresult x x w) as HR.
    repeat rewrite (proj1 free_independence_survives_other_openings) in HC by congruence.
    repeat rewrite (proj1 free_independence_survives_other_openings) in HR by congruence.
    now rewrite HC, IHarg, HR.
Qed.

Local Lemma equivalent_open_receivers_have_same_independence e (C C' : typ) :
  (forall x, tyq_typ e (open x C) (open x C')) ->
  typ_indep_b 0 C <-> typ_indep_b 0 C'.
Proof.
  intro H.
  destruct (var_fresh (fv C \u fv C')) as [x Hx].
  apply notin_union in Hx as [H1 H2].
  pose proof (type_equiv_preserves_free_independence (H x) x) as Heq.
  change (independent_free_type x (open_rec 0 x C) <->
    independent_free_type x (open_rec 0 x C')) in Heq.
  rewrite (proj1 opening_fresh_name_preserves_independence C 0 x H1),
    (proj1 opening_fresh_name_preserves_independence C' 0 x H2) in Heq.
  now rewrite <- !(proj1 independent_bound_characterization).
Qed.

Local Definition method_variance mode G e C1 Z1 V1 C2 Z2 V2 :=
  subtyp mode G objctx_empty e Z2 Z1 /\
  (mode_has_sef mode -> typ_indep_b 0 C2 -> typ_indep_b 0 C1) /\
  exists L,
    (forall z, z \notin L ->
      subtyp mode (G § z / v_par ~ Z2) objctx_empty e (open z C2) (open z C1)) /\
    (forall z, z \notin L -> forall c, c <> z -> c \notin L ->
      subtyp mode (ctx_met G z Z2 c C2) objctx_empty e
        (open_met z c V1) (open_met z c V2)).

Local Lemma method_variance_reflexive mode G e C Z V :
  method_variance mode G e C Z V C Z V.
Proof.
  split; [apply subtyp_refl |]. split; [auto |].
  exists (\{} : vars). split; intros; apply subtyp_refl.
Qed.

Local Lemma method_variance_under_equivalence mode G e C1 Z1 V1 C2 Z2 V2 :
  (forall z, tyq_typ e (open z C1) (open z C2)) ->
  tyq_typ e Z1 Z2 ->
  (forall z c, tyq_typ e (open_met z c V1) (open_met z c V2)) ->
  method_variance mode G e C1 Z1 V1 C2 Z2 V2.
Proof.
  intros HC HZ HV. split.
  - apply equivalent_type_subtypes, equiv_type_is_symmetric. exact HZ.
  - split.
    + intros _ Hind. apply (proj2 (@equivalent_open_receivers_have_same_independence e C1 C2 HC)). exact Hind.
    + exists (\{} : vars). split; intros.
      * apply equivalent_type_subtypes, equiv_type_is_symmetric, HC.
      * apply equivalent_type_subtypes, HV.
Qed.

Local Lemma method_variance_compose mode G e C1 Z1 V1 C2 Z2 V2 C3 Z3 V3 :
  method_variance mode G e C1 Z1 V1 C2 Z2 V2 ->
  method_variance mode G e C2 Z2 V2 C3 Z3 V3 ->
  method_variance mode G e C1 Z1 V1 C3 Z3 V3.
Proof.
  intros [HZ21 [Hind21 [L2 [HC21 HV12]]]] [HZ32 [Hind32 [L3 [HC32 HV23]]]].
  split.
  { eapply subtyp_trans; unfold subtyping; eassumption. }
  split.
  { intros Hsef Hind. apply Hind21; [exact Hsef | now apply Hind32]. }
  exists (ctx_dom G \u L2 \u L3).
  assert (HQ : forall z, z \notin ctx_dom G ->
    ctx_typing_morphism mode e (G § z / v_par ~ Z2) (G § z / v_par ~ Z3)).
  { intros z Hz. now apply specialize_last_binding. }
  split.
  - intros z Hz. fresh_fv.
    eapply subtyp_trans; unfold subtyping; [apply HC32; assumption |].
    eapply (proj1 (proj2 (ctx_types_under_morphism mode)));
      [apply HC21; assumption | apply HQ; assumption].
  - intros z Hz c Hcz Hc. fresh_fv.
    eapply subtyp_trans; unfold subtyping; [|apply (HV23 z); assumption].
    eapply (proj1 (proj2 (ctx_types_under_morphism mode))).
    + apply (HV12 z); assumption.
    + apply ctx_typing_morphism_narrowed_push.
      * apply HQ; assumption.
      * cbn [ctx_dom]. rewrite notin_union, notin_singleton. auto.
      * apply HC32; assumption.
Qed.

Local Definition nominal_method_consequence mode G e R m (D : dec) :=
  match D with
  | dec_met l C' Z' V' => l = m ->
      exists C Z V, record_has R (dec_met m C Z V) /\
        method_variance mode G e C Z V C' Z' V'
  | _ => True
  end.

Local Lemma nominal_method_accepted mode G e R m :
  accepted_declarations mode G e (nominal_method_consequence mode G e R m).
Proof.
  split; [intros; exact I |].
  split; [|intros; exact I].
  intros D D' Hw. destruct Hw.
  - destruct D'; try (intros; exact I).
    intro Hmethod. inversion H; subst; try discriminate.
    all: try solve [match goal with Hn : typ_nulary (typ_rcd _) |- _ => inversion Hn end].
    all: repeat match goal with Ho : typ_andor _ |- _ => destruct Ho end; try discriminate.
    unfold nominal_method_consequence, typing_equiv in *.
    intros [C [Z [V [Hmember Hbase]]]]%Hmethod.
    exists C, Z, V. split; [exact Hmember |].
    eapply method_variance_compose; [exact Hbase |].
    apply method_variance_under_equivalence; assumption.
  - intros; exact I.
  - intros; exact I.
  - intros Hsource Hm. destruct (Hsource Hm) as [C0 [Z0 [V0 [Hmember Hbase]]]].
    exists C0, Z0, V0. split; [exact Hmember |].
    eapply method_variance_compose; [exact Hbase |].
    split; [assumption |]. split; [assumption |]. exists L. split; assumption.
Qed.

Local Lemma tight_method_projection_uses_nominal_type mode G e x R B m C' Z' V' :
  mode_has_mutability mode -> @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  record_type R ->
  ctx_binds x (typ_objref R (typ_mut_marker B)) G ->
  ty_trm_t mode G e x (typ_rcd (dec_met m C' Z' V')) ->
  exists C Z V, record_has (open x R) (dec_met m C Z V) /\
    method_variance mode G e C Z V C' Z' V'.
Proof.
  intros Hmut Hin Hok Hcorr HR Hbind Htight.
  set (P := nominal_method_consequence mode G e (open x R) m).
  assert (Hb : forall U, ctx_binds x U G -> accepted_shape G x P (fun _ => True) U).
  {
    intros U Hu. pose proof (ctx_binds_unique Hu Hbind) as ->.
    apply accepted_and.
    - apply accepted_binder; [|exact I].
      apply declared_record_accepted; [now apply record_open_type |].
      intros [A W V | a W V | l C Z V] Hmem; try exact I.
      unfold P, nominal_method_consequence. intro Hlabel. subst l.
      exists C, Z, V. split; [exact Hmem | apply method_variance_reflexive].
    - apply accepted_record. exact I.
  }
  pose proof (@tight_typing_preserves_shape mode G e x _ Htight Hmut Hin Hok Hcorr P
    (nominal_method_accepted mode G e (open x R) m) Hb) as Hshape.
  inversion Hshape; subst.
  match goal with HP : P (dec_met m C' Z' V') |- _ => exact (HP eq_refl) end.
Qed.

Local Definition nominal_type_consequence mode G e R A (d : dec) :=
  match d with
  | dec_typ (typ_label_normal B) W V => B = A -> exists S T,
      record_has R (dec_typ (typ_label_normal A) S T) /\
      (forall x, subtyp_t mode G e (open x W) (open x S)) /\
      (forall x, subtyp_t mode G e (open x T) (open x V))
  | _ => True
  end.

Local Lemma nominal_type_accepted mode G e R A :
  record_type R ->
  accepted_declarations mode G e (nominal_type_consequence mode G e R A).
Proof.
  intros [L HL]. split; [intros; exact I |]. split.
  - intros D D' Hw. destruct Hw.
    + destruct D' as [[B | B] W V | a W V | m C Z V]; try (intros; exact I).
      intro Hsource. inversion H; subst; try discriminate.
      all: try solve [match goal with Hn : typ_nulary (typ_rcd _) |- _ => inversion Hn end].
      all: repeat match goal with Ho : typ_andor _ |- _ => destruct Ho end; try discriminate.
      unfold nominal_type_consequence, typing_equiv in *.
      intros [S [T [Hmem [Hlo Hhi]]]]%Hsource.
      exists S, T. split; [exact Hmem |]. split; intro w.
      * eapply subtyp_trans_t; [|apply Hlo].
        apply subtyp_tyq_t, equiv_type_is_symmetric. auto.
      * eapply subtyp_trans_t; [apply Hhi |]. apply subtyp_tyq_t. unfold typing_equiv. auto.
    + intros; exact I.
    + destruct A0 as [B | B]; [|intros; exact I].
      intros Hsource HB. destruct (Hsource HB) as [S0 [T0 [Hmem [Hlo Hhi]]]].
      exists S0, T0. split; [exact Hmem |].
      split; intro x; eapply subtyp_trans_t; eauto.
    + intros; exact I.
  - intros [B | B] W1 V1 W2 V2 H1 H2; [|exact I].
    intro HB. destruct (H1 HB) as [S1 [T1 [HM1 [Hno1 Hhi1]]]].
    destruct (H2 HB) as [S2 [T2 [HM2 [Hno2 Hhi2]]]].
    assert (Heq : dec_typ (typ_label_normal A) S1 T1 = dec_typ (typ_label_normal A) S2 T2)
      by (eapply record_has_same_label_unique; eassumption || reflexivity).
    inversion Heq; subst.
    exists S2, T2. split; [exact HM1 |].
    split; intro x.
    + apply subtyp_or2_t; auto.
    + apply subtyp_and2_t; auto.
Qed.

Local Lemma tight_normal_type_uses_precise_bounds mode G e x A W V :
  mode_has_mutability mode -> @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  ty_trm_t mode G e x (typ_rcd (dec_typ (typ_label_normal A) W V)) ->
  exists S T, precise_member G x (dec_typ (typ_label_normal A) S T) /\
    (forall a, subtyp_t mode G e (open a W) (open a S)) /\
    (forall a, subtyp_t mode G e (open a T) (open a V)).
Proof.
  intros Hmut Hin Hok Hcorr Hty.
  assert (Hex : exists U, ctx_binds x U G).
  { induction Hty; eauto. }
  destruct Hex as [U Hbind].
  destruct (inert_object_binding Hmut Hin Hbind) as [R [B [-> [HR _]]]].
  pose proof (record_open_type x HR) as Hrecord.
  set (P := nominal_type_consequence mode G e (open x R) A).
  assert (Hb : forall U, ctx_binds x U G -> accepted_shape G x P (fun _ => True) U).
  {
    intros U Hu. pose proof (ctx_binds_unique Hu Hbind) as ->.
    apply accepted_and.
    - apply accepted_binder; [|exact I].
      apply declared_record_accepted; [exact Hrecord |].
      intros [[B' | B'] S T | a W' V' | m C Z V'] Hmem; try exact I.
      unfold P, nominal_type_consequence. intro HLabel. subst B'.
      exists S, T. split; [exact Hmem |]. split; intro a; apply subtyp_refl_t.
    - apply accepted_record. exact I.
  }
  pose proof (@tight_typing_preserves_shape mode G e x _ Hty Hmut Hin Hok Hcorr P
    (@nominal_type_accepted mode G e (open x R) A Hrecord) Hb) as Hshape.
  inversion Hshape; subst.
  match goal with HP : P (dec_typ _ W V) |- _ =>
    destruct (HP eq_refl) as [S [T [Hmem [Hlo Hhi]]]]
  end.
  exists S, T. split; [eapply precise_member_declared; eassumption | auto].
Qed.

Local Definition precise_capability_variance mode G e B S T :=
  (forall a, subtyp_t mode G e (open a S) typ_bot) /\
  (forall a, subtyp_t mode G e (open a B) (open a T)).

Local Definition capability_nocap_case mode G e B :=
  mode_has_top_nm_complement mode ->
  ~ precise_capability_variance mode G e B typ_bot typ_bot.

Local Definition capability_declaration mode G e B (D : dec) :=
  match D with
  | dec_typ (typ_label_refcap _) W V => precise_capability_variance mode G e B W V
  | _ => True
  end.

Inductive capability_shape mode G e B : typ -> Prop :=
| capability_shape_top : capability_shape mode G e B typ_top
| capability_shape_nocap : capability_nocap_case mode G e B ->
    capability_shape mode G e B typ_nocap
| capability_shape_and S T :
    capability_shape mode G e B S -> capability_shape mode G e B T ->
    capability_shape mode G e B (typ_and S T)
| capability_shape_or_left S T : capability_shape mode G e B S ->
    capability_shape mode G e B (typ_or S T)
| capability_shape_or_right S T : capability_shape mode G e B T ->
    capability_shape mode G e B (typ_or S T)
| capability_shape_record D : capability_declaration mode G e B D ->
    capability_shape mode G e B (typ_rcd D)
| capability_shape_fun S T : capability_shape mode G e B (typ_fun S T)
| capability_shape_binder T : capability_shape mode G e B (typ_bnd T)
| capability_shape_selection v A w S T :
    precise_member G v (dec_typ A S T) ->
    capability_shape mode G e B (open w T) ->
    capability_shape mode G e B (typ_sel (avar_f v) A (avar_f w)).

Local Lemma capability_shape_follows_type_equivalence mode G e B :
  mode_has_mutability mode -> @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  forall S T, capability_shape mode G e B S -> tyq_typ e S T -> capability_shape mode G e B T.
Proof.
  intros Hmut Hin Hok Hcorr S T Hshape.
  revert T. induction Hshape; intros U HE;
    inversion HE; subst; try discriminate.
  all: repeat match goal with Hn : typ_nulary _ |- _ => inversion Hn; subst; clear Hn end.
  all: repeat match goal with Ho : typ_andor _ |- _ => destruct Ho end; try discriminate.
  all: repeat match goal with H : typ_and _ _ = typ_and _ _ |- _ => inversion H; clear H; subst end.
  all: repeat match goal with H : typ_or _ _ = typ_or _ _ |- _ => inversion H; clear H; subst end.
  all: unfold typing_equiv in *.
  all: try solve [apply capability_shape_record; exact I].
  all: try solve [eauto 6 using capability_shape].
  - apply capability_shape_record.
    destruct B0; [exact I |].
    unfold capability_declaration, precise_capability_variance in *.
    destruct H as [Hlo Hhi]. split; intro x.
    + eapply subtyp_trans_t; [|apply Hlo].
      apply subtyp_tyq_t, equiv_type_is_symmetric. auto.
    + eapply subtyp_trans_t; [apply Hhi |]. apply subtyp_tyq_t. unfold typing_equiv. auto.
  - match goal with Hm : precise_member G ?r (dec_typ (typ_label_normal ?A) ?S ?T),
      Hr : tyq_var e ?r ?r' |- _ =>
        destruct (aliased_nominal_normal_type_member Hmut Hin Hok Hcorr Hr Hm)
          as [S' [T' [Hmem [Hlo Hhi]]]]
    end.
    eapply capability_shape_selection; [exact Hmem |]. eapply IHHshape; apply Hhi.
Qed.

Local Lemma capability_shape_preserved_by_tight_subtyping mode G e S T :
  subtyp_t mode G e S T ->
  mode_has_mutability mode -> @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  forall B, capability_shape mode G e B S -> capability_shape mode G e B T.
Proof.
  intro H. induction H; intros Hmut Hin Hok Hcorr B Hshape.
  - apply capability_shape_top.
  - inversion Hshape.
  - exact Hshape.
  - eapply IHsubtyp_t2; try assumption. eapply IHsubtyp_t1; eassumption.
  - inversion Hshape; assumption.
  - inversion Hshape; assumption.
  - apply capability_shape_and; eauto.
  - now apply capability_shape_or_left.
  - now apply capability_shape_or_right.
  - inversion Hshape; subst; eauto.
  - apply capability_shape_record. exact I.
  - inversion Hshape; subst. apply capability_shape_record.
    destruct A; [exact I |].
    match goal with Hcap : capability_declaration _ _ _ _ _ |- _ =>
      destruct Hcap as [Hlo Hhi] end.
    split; intro x; eapply subtyp_trans_t; eauto.
  - assert (Hmember : precise_member G x (dec_typ A TL TU))
      by (eexists; eassumption).
    destruct (precise_member_inert_type_bounds Hmut Hin Hmember) as [E | E]; subst TL.
    + inversion Hshape.
    + eapply capability_shape_selection; eassumption.
  - assert (Hmember : precise_member G x (dec_typ A TL TU))
      by (eexists; eassumption).
    inversion Hshape; subst.
    match goal with
    | Hm : precise_member G x (dec_typ A ?SL ?SU) |- _ =>
        assert (E : SU = TU) by
          (exact (proj2 (@precise_type_member_unique mode G x A SL SU TL TU Hmut Hin Hm Hmember)));
        now subst SU
    end.
  - apply capability_shape_fun.
  - apply capability_shape_record. exact I.
  - eapply capability_shape_follows_type_equivalence; eassumption.
  - apply capability_shape_record. destruct A; [exact I |].
    inversion Hshape; subst.
    repeat match goal with HR : capability_shape _ _ _ _ (typ_rcd _) |- _ =>
      inversion HR; subst; clear HR
    end.
    match goal with HL : capability_declaration _ _ _ _ (dec_typ _ S1 T1),
                    HU : capability_declaration _ _ _ _ (dec_typ _ S2 T2) |- _ =>
      destruct HL as [Hlo1 Hhi1]; destruct HU as [Hlo2 Hhi2]
    end.
    split; intro x; [apply subtyp_or2_t | apply subtyp_and2_t]; auto.
  - inversion Hshape; subst.
    match goal with Hor : capability_shape _ _ _ _ (typ_or _ _) |- _ =>
      inversion Hor; subst; eauto using capability_shape end.
  - apply capability_shape_binder.
  - apply capability_shape_record. exact I.
  - apply capability_shape_record. exact I.
  - apply capability_shape_record. exact I.
  - apply capability_shape_fun.
  - apply capability_shape_or_left, capability_shape_nocap.
    intros Hcontra. destruct mode; cbn in *; congruence.
  - destruct (classic (@precise_capability_variance mode G e B typ_bot typ_bot))
      as [HP | Hnot].
    + apply capability_shape_or_right, capability_shape_record. exact HP.
    + apply capability_shape_or_left, capability_shape_nocap. intros _. exact Hnot.
  - inversion Hshape; subst.
    match goal with Hn : capability_shape _ _ _ _ typ_nocap,
                    Hm : capability_shape _ _ _ _ (typ_mut_marker typ_bot) |- _ =>
      inversion Hn; subst; inversion Hm; subst
    end.
    exfalso. exact (H0 H H4).
  - apply capability_shape_record. split; intros; [apply subtyp_bot_t | apply subtyp_top_t].
Qed.

Local Lemma record_type_accepts_capability_shape mode G e B R :
  record_type R -> capability_shape mode G e B R.
Proof.
  intros [L HL]. induction HL.
  - apply capability_shape_record. inversion H; exact I.
  - apply capability_shape_and; [exact IHHL | apply capability_shape_record].
    inversion H; exact I.
Qed.

Local Lemma tight_typing_tracks_binding_capability mode G e x R B T :
  mode_has_mutability mode -> @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  ctx_binds x (typ_objref R (typ_mut_marker B)) G ->
  ty_trm_t mode G e x T ->
  capability_shape mode G e B T.
Proof.
  intros Hmut Hin Hok Hcorr Hbind Hty.
  pose proof (inert_object_binding Hmut Hin Hbind) as [R' [B' [Heq [HR _]]]].
  inversion Heq; subst R' B'.
  set (K := capability_shape mode G e B).
  assert (HK : shape_gate_is_closed mode G e K).
  {
    unfold shape_gate_is_closed. repeat split.
    - intros S U Hq HS. unfold K in *. eapply capability_shape_follows_type_equivalence; eassumption.
    - intros S U Hsub HS. unfold K in *. eapply capability_shape_preserved_by_tight_subtyping; eassumption.
    - intros S U Hs Ht. apply capability_shape_and; assumption.
    - apply capability_shape_binder.
    - apply capability_shape_record. split; intros.
      + apply subtyp_bot_t.
      + apply subtyp_top_t.
  }
  assert (HP : accepted_declarations mode G e (fun _ => True))
    by (repeat split; intros; exact I).
  assert (Hb : forall U, ctx_binds x U G -> accepted_shape G x (fun _ => True) K U /\ K U).
  {
    intros U Hu. pose proof (ctx_binds_unique Hu Hbind) as ->.
    split.
    - apply accepted_and; [|apply accepted_record; exact I].
      apply accepted_binder.
      + apply declared_record_accepted; [now apply record_open_type | intros; exact I].
      + apply record_type_accepts_capability_shape. now apply record_open_type.
    - apply capability_shape_and; [apply capability_shape_binder |].
      apply capability_shape_record. split; intros; apply subtyp_refl_t.
  }
  pose proof (proj2 (@tight_typing_preserves_shape_and_gate mode G e x _ Hty
    Hmut Hin Hok Hcorr (fun _ => True) K HP HK Hb)) as Hshape.
  exact Hshape.
Qed.

Local Lemma tight_capability_uses_precise_bounds mode G e x M W V :
  mode_has_mutability mode -> @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  ty_trm_t mode G e x (typ_rcd (dec_typ (typ_label_refcap M) W V)) ->
  exists B, precise_member G x (dec_typ (typ_label_refcap M) typ_bot B) /\
    precise_capability_variance mode G e B W V.
Proof.
  destruct M. intros Hmut Hin Hok Hcorr Hty.
  assert (Hex : exists U, ctx_binds x U G) by (induction Hty; eauto).
  destruct Hex as [U Hbind].
  destruct (inert_object_binding Hmut Hin Hbind) as [R [B [-> [HR _]]]].
  pose proof (tight_typing_tracks_binding_capability Hmut Hin Hok Hcorr Hbind Hty) as Hshape.
  exists B. split.
  - exists (typ_objref R (typ_mut_marker B)).
    eapply pf_and2, pf_bind. exact Hbind.
  - inversion Hshape; assumption.
Qed.

Local Lemma narrow_type_member_bounds mode G e x A W V :
  mode_has_mutability mode -> @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  ty_trm_t mode G e x (typ_rcd (dec_typ A W V)) ->
  exists S T, precise_member G x (dec_typ A S T) /\
    (forall a, subtyp_t mode G e (open a W) (open a S)) /\
    (forall a, subtyp_t mode G e (open a T) (open a V)).
Proof.
  destruct A as [A | A]; intros.
  - now apply tight_normal_type_uses_precise_bounds.
  - destruct (tight_capability_uses_precise_bounds H H0 H1 H2 H3)
      as [B [Hmem [Hlo Hhi]]].
    exists typ_bot, B. auto.
Qed.

Local Lemma inert_judgments_admit_precise_selections mode :
  mode_has_mutability mode ->
  mode_incap' mode = mode_incap_nocap ->
  (forall G Go e x T, ty_var mode G Go e x T ->
    @inert mode G -> ctx_ok G -> @renv_corr mode G e -> ty_trm_t mode G e x T) /\
  (forall G Go e S T, subtyp mode G Go e S T ->
    @inert mode G -> ctx_ok G -> @renv_corr mode G e -> subtyp_t mode G e S T) /\
  (forall G Go e S T, ty_incap mode G Go e S T ->
    @inert mode G -> ctx_ok G -> @renv_corr mode G e -> subtyp_t mode G e typ_nocap T).
Proof.
  intros Hmut Hinc.
  apply (@ts_mutind mode
    (fun G Go e x T _ => @inert mode G -> ctx_ok G -> @renv_corr mode G e -> ty_trm_t mode G e x T)
    (fun G Go e S T _ => @inert mode G -> ctx_ok G -> @renv_corr mode G e -> subtyp_t mode G e S T)
    (fun G Go e S T _ => @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
      subtyp_t mode G e typ_nocap T)).
  all: intros;
    match goal with Hin : @inert ?m ?G, Hok : ctx_ok ?G,
                    Hcorr : @renv_corr ?m ?G ?e |- _ =>
      repeat match goal with
      | HH : @inert m G -> ctx_ok G -> @renv_corr m G e -> _ |- _ =>
          specialize (HH Hin Hok Hcorr)
      end
    end.
  - now apply ty_var_t.
  - apply ty_rec_intro_t; try assumption.
    + rewrite Hinc. discriminate.
    + intros _. match goal with
      | IH : forall h : mode_has_incap mode, _ |- _ =>
        apply IH; try assumption; unfold mode_has_incap'; rewrite Hinc; reflexivity
      end.
  - apply ty_rec_elim_t; assumption.
  - apply ty_and_intro_t; assumption.
  - eapply ty_sub_t; eassumption.
  - eapply ty_var_mut_top_t; eassumption.
  - apply subtyp_top_t.
  - apply subtyp_bot_t.
  - apply subtyp_refl_t.
  - eapply subtyp_trans_t; eassumption.
  - apply subtyp_and11_t.
  - apply subtyp_and12_t.
  - apply subtyp_and2_t; assumption.
  - apply subtyp_or11_t.
  - apply subtyp_or12_t.
  - apply subtyp_or2_t; assumption.
  - apply subtyp_fld_t; assumption.
  - apply subtyp_typ_t; eauto.
  - match goal with Ht : ty_trm_t mode ?G ?e ?x (typ_rcd (dec_typ ?A ?S ?T)) |- _ =>
      destruct (@narrow_type_member_bounds mode G e x A S T Hmut
        ltac:(assumption) ltac:(assumption) ltac:(assumption) Ht)
        as [S0 [T0 [[U Hmem] [Hlo Hhi]]]]
    end.
    eapply subtyp_trans_t; [apply Hlo | eapply subtyp_sel2_t; exact Hmem].
  - match goal with Ht : ty_trm_t mode ?G ?e ?x (typ_rcd (dec_typ ?A ?S ?T)) |- _ =>
      destruct (@narrow_type_member_bounds mode G e x A S T Hmut
        ltac:(assumption) ltac:(assumption) ltac:(assumption) Ht)
        as [S0 [T0 [[U Hmem] [Hlo Hhi]]]]
    end.
    eapply subtyp_trans_t; [eapply subtyp_sel1_t; exact Hmem | apply Hhi].
  - eapply subtyp_fun_t; eassumption.
  - eapply subtyp_met_t; eassumption.
  - now apply subtyp_tyq_t.
  - apply subtyp_typ_and_t.
  - apply subtyp_dist_t.
  - apply subtyp_nocap_bnd_t.
  - apply subtyp_nocap_typ_t.
  - apply subtyp_nocap_fld_t.
  - apply subtyp_nocap_met_t.
  - now apply subtyp_nocap_fun_t.
  - now apply subtyp_nocap_mut_top_boundless_t.
  - now apply subtyp_nocap_mut_top_complement_t.
  - now apply subtyp_nocap_mut_bot_t.
  - now apply subtyp_mut_top_t.
  - apply subtyp_top_t.
  - apply subtyp_refl_t.
  - apply subtyp_nocap_typ_t.
  - apply subtyp_top_t.
  - apply subtyp_nocap_met_t.
  - apply subtyp_nocap_fld_t.
  - assumption.
  - apply subtyp_nocap_bnd_t.
  - apply subtyp_and2_t; assumption.
  - eapply subtyp_trans_t with (T := S2); [eassumption | apply subtyp_or11_t].
  - now apply subtyp_nocap_fun_t.
  - assumption.
Qed.

Local Lemma record_from_inert_object_binding mode G y R B :
  mode_has_mutability mode -> @inert mode G ->
  ctx_binds y (typ_objref R (typ_mut_marker B)) G ->
  record_type R.
Proof.
  intros Hmut Hin Hb.
  destruct (inert_object_binding Hmut Hin Hb) as [R' [B' [Htype [HR _]]]].
  inversion Htype; subst. exact HR.
Qed.

Local Lemma precise_typing_at_reference_location mode G e h w y T :
  mode_has_mutability mode -> mode_incap' mode = mode_incap_nocap ->
  @inert mode G -> heap_correspond (typing_mode := mode) G e h ->
  binds w y e ->
  ty_var mode G objctx_empty e w T ->
  ty_trm_t mode G e y T.
Proof.
  intros Hmut Hinc Hin Hheap Href Hty.
  destruct Hheap as [Hok [_ [_ [_ [_ [_ [Hcorr _]]]]]]].
  apply (proj1 (inert_judgments_admit_precise_selections mode Hmut Hinc) G objctx_empty e y T).
  - eapply location_preserves_reference_typing; eassumption.
  - exact Hin.
  - exact Hok.
  - exact Hcorr.
Qed.

Local Lemma field_view_of_heap_location mode G e h w y R B a W V :
  mode_has_mutability mode -> mode_incap' mode = mode_incap_nocap ->
  @inert mode G -> heap_correspond (typing_mode := mode) G e h ->
  binds w y e -> ctx_binds y (typ_objref R (typ_mut_marker B)) G ->
  ty_var mode G objctx_empty e w (typ_rcd (dec_fld a W V)) ->
  exists S,
    record_has (open y R) (dec_fld a S S) /\
    subtyp mode G objctx_empty e W S /\ subtyp mode G objctx_empty e S V.
Proof.
  intros Hmut Hinc Hin Hheap Href Hbind Hty.
  pose proof (precise_typing_at_reference_location Hmut Hinc Hin Hheap Href Hty) as Htight.
  destruct Hheap as [Hok [_ [_ [_ [_ [_ [Hcorr _]]]]]]].
  eapply tight_field_projection_uses_nominal_type; try eassumption.
  eapply record_from_inert_object_binding; eassumption.
Qed.

Local Lemma method_view_of_heap_location mode G e h w y R B m C Z V :
  mode_has_mutability mode -> mode_incap' mode = mode_incap_nocap ->
  @inert mode G -> heap_correspond (typing_mode := mode) G e h ->
  binds w y e -> ctx_binds y (typ_objref R (typ_mut_marker B)) G ->
  ty_var mode G objctx_empty e w (typ_rcd (dec_met m C Z V)) ->
  exists C0 Z0 V0, record_has (open y R) (dec_met m C0 Z0 V0) /\
    method_variance mode G e C0 Z0 V0 C Z V.
Proof.
  intros Hmut Hinc Hin Hheap Href Hbind Hty.
  pose proof (precise_typing_at_reference_location Hmut Hinc Hin Hheap Href Hty) as Htight.
  destruct Hheap as [Hok [_ [_ [_ [_ [_ [Hcorr _]]]]]]].
  eapply tight_method_projection_uses_nominal_type; try eassumption.
  eapply record_from_inert_object_binding; eassumption.
Qed.

(* Reading an object can weaken its capability without discarding its record. *)

Local Lemma subtyping_widens_union_right mode G e N S T :
  subtyp mode G objctx_empty e S T ->
  subtyp mode G objctx_empty e (typ_or N S) (typ_or N T).
Proof.
  intro HS. apply subtyp_or2; unfold subtyping; [apply subtyp_or11 |].
  eapply subtyp_trans; [exact HS | apply subtyp_or12].
Qed.

Local Lemma subtyping_merges_union_cases mode G e N S T :
  subtyp mode G objctx_empty e
    (typ_and (typ_or N S) (typ_or N T)) (typ_or N (typ_and S T)).
Proof.
  eapply subtyp_trans; unfold subtyping; [apply subtyp_dist |].
  apply subtyp_or2; unfold subtyping.
  - eapply subtyp_trans; [apply subtyp_and12 | apply subtyp_or11].
  - eapply subtyp_trans with (T := typ_and T (typ_or N S)); unfold subtyping.
    + apply subtyp_and2; unfold subtyping; [apply subtyp_and12 | apply subtyp_and11].
    + eapply subtyp_trans; [apply subtyp_dist |].
      apply subtyp_or2; unfold subtyping.
      * eapply subtyp_trans; [apply subtyp_and12 | apply subtyp_or11].
      * eapply subtyp_trans; [|apply subtyp_or12].
        apply subtyp_and2; unfold subtyping; [apply subtyp_and12 | apply subtyp_and11].
Qed.

Local Lemma variable_uses_nocap_alternative mode G e x S :
  ty_var mode G objctx_empty e x (typ_or typ_nocap S) ->
  subtyp mode G objctx_empty e typ_nocap S ->
  ty_var mode G objctx_empty e x S.
Proof.
  intros HT HS. eapply ty_var_sub; unfold obj_typing, subtyping; [exact HT |].
  apply subtyp_or2; unfold subtyping; [exact HS | apply subtyp_refl].
Qed.

Local Lemma variable_adds_nocap_alternative mode G e x S :
  ty_var mode G objctx_empty e x S ->
  ty_var mode G objctx_empty e x (typ_or typ_nocap S).
Proof.
  intro HT. eapply ty_var_sub; unfold obj_typing, subtyping;
    [exact HT | apply subtyp_or12].
Qed.

Local Lemma transport_alias_through_nocap mode G e w y T :
  mode_incap' mode = mode_incap_nocap ->
  tyq_var e w y ->
  (forall S, ctx_binds w S G -> ty_var mode G objctx_empty e y (typ_or typ_nocap S)) ->
  ty_var mode G objctx_empty e w T ->
  ty_var mode G objctx_empty e y (typ_or typ_nocap T).
Proof.
  intros Hmode Heq Hbind Htype.
  remember w as z eqn:Hz in Htype.
  induction Htype; subst; unfold obj_typing, subtyping, obj_ref_incap in *.
  - now apply Hbind.
  - assert (Halias : subtyp mode G objctx_empty e (open w T) (open y T))
      by (apply equivalent_type_subtypes; now apply opening_independent_type_with_alias).
    assert (Hcap : mode_has_incap mode) by (unfold mode_has_incap'; rewrite Hmode; reflexivity).
    assert (Hsafe : subtyp mode G objctx_empty e typ_nocap (open y T)).
    { eapply subtyp_trans; [|exact Halias].
      eapply nocap_subtypes_incapacitated_type. exact (H1 Hcap). }
    apply variable_adds_nocap_alternative, ty_rec_intro; unfold obj_typing, obj_ref_incap.
    + eapply variable_uses_nocap_alternative; [|exact Hsafe].
      eapply ty_var_sub; unfold obj_typing, subtyping; [apply IHHtype; auto |].
      now apply subtyping_widens_union_right.
    + assumption.
    + intros _. apply ty_incap_nocap; assumption.
  - assert (Halias : subtyp mode G objctx_empty e (open y T) (open w T))
      by (apply equivalent_type_subtypes, opening_independent_type_with_alias;
          [now apply tyq_var_sym | assumption]).
    eapply ty_var_sub with (T := typ_or typ_nocap (open y T));
      unfold obj_typing, subtyping; [|now apply subtyping_widens_union_right].
    apply variable_adds_nocap_alternative, ty_rec_elim; unfold obj_typing; try assumption.
    eapply variable_uses_nocap_alternative; [apply IHHtype; auto | apply subtyp_nocap_bnd].
  - eapply ty_var_sub with (T := typ_and (typ_or typ_nocap T) (typ_or typ_nocap U));
      unfold obj_typing, subtyping.
    + apply ty_var_and; unfold obj_typing; auto.
    + apply subtyping_merges_union_cases.
  - eapply ty_var_sub; unfold obj_typing, subtyping; [apply IHHtype; auto |].
    now apply subtyping_widens_union_right.
  - apply variable_adds_nocap_alternative.
    eapply ty_var_mut_top; unfold obj_typing; [exact H |].
    apply IHHtype; auto.
Qed.

Local Lemma incapacitation_widens_type mode G Go e S T :
  ty_incap mode G Go e S T ->
  subtyp mode G Go e S T.
Proof.
  intro H. induction H; unfold subtyping in *;
    try solve [apply subtyp_top | apply subtyp_bot | apply subtyp_refl].
  - eapply subtyp_trans; [eapply subtyp_sel1; eassumption | eassumption].
  - apply subtyp_and2; unfold subtyping.
    + eapply subtyp_trans; [apply subtyp_and11 | eassumption].
    + eapply subtyp_trans; [apply subtyp_and12 | eassumption].
  - apply subtyp_or2; unfold subtyping.
    + eapply subtyp_trans; [eassumption | apply subtyp_or11].
    + eapply subtyp_trans; [eassumption | apply subtyp_or12].
Qed.

Local Lemma nocap_or_mutable_view mode G e :
  mode_has_top_nm_subtype mode ->
  subtyp mode G objctx_empty e typ_top (typ_or typ_nocap (typ_mut_marker typ_bot)).
Proof.
  intro Hmode.
  destruct mode; cbn in Hmode; try discriminate.
  all: first [apply subtyp_nocap_mut_top_boundless; reflexivity | apply subtyp_nocap_mut_top_complement];
    reflexivity.
Qed.

Local Lemma nonmutable_alias_has_stripped_view mode G e loc p R B S TS :
  mode_incap' mode = mode_incap_nocap -> mode_has_top_nm_subtype mode ->
  ctx_binds loc (typ_objref R (typ_mut_marker typ_bot)) G ->
  ctx_binds p (typ_objref R (typ_mut_marker B)) G ->
  tyq_var e loc p ->
  ty_var mode G objctx_empty e loc S ->
  ty_incap mode G objctx_empty e S TS ->
  ty_var mode G objctx_empty e p TS.
Proof.
  intros Hmode HNM Hloc Hp Heq Hty Hstrip.
  eapply variable_uses_nocap_alternative; [|eapply nocap_subtypes_incapacitated_type; exact Hstrip].
  eapply transport_alias_through_nocap; [exact Hmode | exact Heq | |].
  - intros U HU. pose proof (ctx_binds_unique HU Hloc) as ->.
    eapply ty_var_sub with
      (T := typ_and (typ_bnd R) (typ_or typ_nocap (typ_mut_marker typ_bot)));
      unfold obj_typing, subtyping.
    + apply ty_var_and; unfold obj_typing.
      * eapply ty_var_sub; unfold obj_typing, subtyping.
        -- apply ty_var_var. exact Hp.
        -- apply subtyp_and11.
      * eapply ty_var_sub; unfold obj_typing, subtyping.
        -- apply ty_var_var. exact Hp.
        -- eapply subtyp_trans; [apply subtyp_top | now apply nocap_or_mutable_view].
    + eapply subtyp_trans; [apply subtyp_dist |].
      apply subtyp_or2; unfold subtyping.
      * eapply subtyp_trans; [apply subtyp_and12 | apply subtyp_or11].
      * apply subtyp_or12.
  - eapply ty_var_sub; unfold obj_typing, subtyping; [exact Hty |].
    eapply incapacitation_widens_type. exact Hstrip.
Qed.

Local Lemma seal_fixed_openings_are_fixed :
  (forall (T : typ) d, (forall a, seal_rec d a T = T) ->
    forall k y, open_rec (d + k) y T = T) /\
  (forall (D : dec) d, (forall a, seal_rec d a D = D) ->
    forall k y, open_rec (d + k) y D = D).
Proof.
  assert (Ha : forall (a : avar) d, (forall x, seal_rec d x a = a) ->
    forall k y, open_rec (d + k) y a = a).
  {
    intros [n | x] d HH k y; [|reflexivity].
    unfold open_rec, AvarOpenable. case_if; [|reflexivity].
    specialize (HH y). unfold seal_rec, AvarSealable in HH.
    rewrite If_l in HH by lia. discriminate.
  }
  apply typ_mutind; intros;
    match goal with H : forall a, seal_rec _ a _ = _ |- _ => rename H into Hfixed end.
  all: unfold open_rec, TypOpenable, DecOpenable;
    cbn [open_rec_typ open_rec_dec]; fold open_rec_typ open_rec_dec.
  all: try reflexivity; f_equal; repeat rewrite <- Nat.add_succ_l.
  all: match goal with
    | IH : forall d, (forall a, seal_rec d a ?T = ?T) -> forall k y, open_rec (d + k) y ?T = ?T
        |- open_rec_typ (?d + ?k) ?y ?T = ?T => apply (IH d)
    | IH : forall d, (forall a, seal_rec d a ?D = ?D) -> forall k y, open_rec (d + k) y ?D = ?D
        |- open_rec_dec (?d + ?k) ?y ?D = ?D => apply (IH d)
    | |- open_rec (?d + ?k) ?y ?a = ?a => apply Ha
    end.
  all: intro z; pose proof (Hfixed z) as Hs;
    unfold seal_rec, TypSealable, DecSealable in Hs;
    cbn [seal_rec_typ seal_rec_dec] in Hs;
    fold seal_rec_typ seal_rec_dec in Hs;
    injection Hs; auto.
Qed.

Local Lemma sealed_type_is_closed (T : typ) :
  sealed T -> closed T.
Proof.
  intros H k y. exact ((proj1 seal_fixed_openings_are_fixed) T 0 H k y).
Qed.

Local Lemma bindings_of_sealed_context_are_sealed G y T :
  ctx_binds y T G -> sealed G -> sealed T.
Proof.
  intro H. induction H; intros Hc x.
  - specialize (Hc x). cbn [seal_rec CtxSealable ctx_seal_rec] in Hc. congruence.
  - apply IHctx_binds. intro p. specialize (Hc p).
    cbn [seal_rec CtxSealable ctx_seal_rec] in Hc. congruence.
  - apply IHctx_binds. intro p. specialize (Hc p).
    cbn [seal_rec CtxSealable ctx_seal_rec] in Hc. congruence.
Qed.

Local Lemma read_alias_preserves_continuation_type mode G t fs h e Lv T y w P R B V :
  let A := typ_objref R (typ_mut_marker B) in
  let C := config_mk t fs h e Lv in
  mode_has_mutability mode ->
  @ty_config mode G C T ->
  ctx_binds_k_after y v_loc (typ_objref R (typ_mut_marker typ_bot)) G P ->
  @ty_stack mode G e V fs T ->
  ty_var mode (G § w / v_ref ~ A) objctx_empty (e & w ~ y) w V ->
  w \notin fv_config C ->
  w \notin ctx_fv G ->
  w \notin fv A ->
  closed A ->
  nothing_fresh_in_config A C ->
  @ty_config mode (G § w / v_ref ~ A)
    (config_mk (trm_var (avar_f w)) fs h (e & w ~ y) (fv_config C)) T.
Proof.
  cbv zeta. intros Hmut Hty Hloc Hfit Hvalue HwC HwG HwA HclA HscopeA.
  set (A := typ_objref R (typ_mut_marker B)) in *.
  set (C := config_mk t fs h e Lv) in *.
  set (C' := config_mk (trm_var (avar_f w)) fs h (e & w ~ y) (fv_config C)).
  inversion Hty as [? ? ? ? ? ? U ? Hin Hheap Hstack HfreeFs Hterm Hfree Hscope Hnull Hseal Hclosed HT]; subst.
  assert (Hw : w \notin ctx_dom G).
  { intro Hdom. apply HwC. exact (proj1 (proj1 Hscope) _ Hdom). }
  assert (Hwe : w # e) by (apply fresh_from_machine_for_env with (t := t) (fs := fs) (h := h) (L := Lv); exact HwC).
  assert (Hkind : forall x k, ctx_k G x k -> ctx_k (G § w / v_ref ~ A) x k).
  { intros x k Hx. eapply kind_after_fresh_push; eassumption. }
  assert (Hbound : ctx_k (G § w / v_ref ~ A) w v_ref).
  { exists A, G. apply ctx_binds_k_e. }
  assert (Hkeep : fv_config C \c fv_config C').
  { intros x Hx. unfold C'. do 4 (rewrite in_union; right). exact Hx. }
  assert (Hw' : w \in fv_config C').
  { unfold C'. apply dom_env_in_machine_fv. rewrite dom_push, in_union, in_singleton. auto. }
  eapply ty_config_c with (T := V); try assumption.
  - apply inert_push; try assumption; [constructor |].
    pose proof (inert_binding_annotation Hin Hloc) as Hanno.
    inversion Hanno; subst.
    apply inert_typ_obj; try assumption.
    unfold refcap_inert_type. destruct mode; cbn in *; try discriminate; constructor.
  - unfold A. eapply heap_correspond_for_existing_alias; eassumption.
  - apply stack_typing_under_renv_extension with (e := e).
    + apply stack_typing_under_ctx_extension with (G := G); [exact Hfit |].
      now apply ctx_extends_with_fresh.
    + now apply fresh_ref_extension_keeps_bindings.
  - intros x Hx. apply Hkind. now apply HfreeFs.
  - apply ty_trm_var; [intros _; apply ctx_vis_e | exact Hvalue].
  - intros x Hx. inversion Hx; subst. exact Hbound.
  - destruct Hscope as [[HD HF] HTF]. split; [split |].
    + intros x Hx. cbn [ctx_dom] in Hx. rewrite in_union, in_singleton in Hx.
      destruct Hx as [-> | Hx]; [exact Hw' | now apply Hkeep, HD].
    + intros x Hx. cbn [fv CtxFreeVar ctx_collect_values] in Hx. rewrite in_union in Hx.
      apply Hkeep. destruct Hx as [Hx | Hx]; [now apply HscopeA | now apply HF].
    + intros x Hx. now apply Hkeep, HTF.
  - destruct Hnull as [x Hx]. exists x. unfold C.
    do 4 (rewrite in_union; right). exact Hx.
  - intro x. specialize (Hseal x). pose proof (closed_type_is_sealed HclA x) as HseA.
    change (seal x G § w / v_ref ~ seal x A = G § w / v_ref ~ A).
    now rewrite Hseal, HseA.
  - inversion Hclosed; subst. constructor; try assumption. intros k x. reflexivity.
Qed.


Local Lemma location_kind_has_mutable_binding mode G e h z :
  mode_has_mutability mode -> @inert mode G ->
  heap_correspond (typing_mode := mode) G e h ->
  ctx_k G z v_loc ->
  exists R P, ctx_binds_k_after z v_loc (typ_objref R (typ_mut_marker typ_bot)) G P.
Proof.
  intros Hmut Hin Hheap Hloc.
  destruct (typed_location_object_type Hmut Hheap Hloc) as [R [B [P Hbinding]]].
  pose proof (inert_binding_annotation Hin Hbinding) as Hannotation.
  assert (HB : refcap_inert_type (typing_mode := mode) B v_loc)
    by (inversion Hannotation; assumption).
  assert (HE : B = typ_mut_marker typ_bot).
  { destruct mode; cbn in *; try discriminate; now inversion HB. }
  subst B. eauto.
Qed.

Local Lemma scoped_read_reference_type R TC w :
  closed (typ_objref R (typ_mut_marker typ_bot)) ->
  closed (typ_mut_marker TC) ->
  closed (rodot_read_ref_type R typ_top w TC).
Proof.
  intros Hrecord Hcap k x.
  specialize (Hrecord k x). specialize (Hcap k x).
  assert (HR : open_rec (S k) x R = R)
    by (change (typ_objref (open_rec (S k) x R) (typ_mut_marker typ_bot) =
      typ_objref R (typ_mut_marker typ_bot)) in Hrecord; congruence).
  assert (HC : open_rec (S k) x TC = TC)
    by (change (typ_mut_marker (open_rec (S k) x TC) = typ_mut_marker TC)
      in Hcap; congruence).
  assert (HB : open_rec (S k) x (avar_b 0) = avar_b 0).
  { apply open_avar_unchanged. intro E. discriminate. }
  change (typ_objref (open_rec (S k) x R)
    (typ_mut_marker (typ_or (open_rec (S k) x TC)
      (typ_sel (avar_f w) (typ_label_refcap typ_refcap_mutability)
        (open_rec (S k) x (avar_b 0))))) = rodot_read_ref_type R typ_top w TC).
  now rewrite HR, HC, HB.
Qed.

Local Lemma read_step_from_scoped_view mode G e h fs Lv w a T W U TS TC :
  let C := config_mk (trm_read (avar_f w) a) fs h e Lv in
  mode_has_mutability mode -> mode_incap' mode = mode_incap_nocap ->
  mode_has_top_nm_subtype mode ->
  @ty_config mode G C T ->
  ty_var mode G objctx_empty e w (typ_rcd (dec_fld a W U)) ->
  ty_incap mode G objctx_empty e U TS ->
  ty_capbnd mode typ_refcap_mutability G objctx_empty e U TC ->
  @ty_stack mode G e (rodot_read_term_type TS w TC) fs T ->
  closed (typ_mut_marker TC) -> fv TC \c fv_config C ->
  exists G' C', typed_red mode G C T G' C' /\ @ty_config mode G' C' T.
Proof.
  cbv zeta. intros Hmut Hinc HNM Hty Hproject Hstrip Hcap Hstack HclTC HfvTC.
  set (C := config_mk (trm_read (avar_f w) a) fs h e Lv) in *.
  inversion Hty as [? ? ? ? ? ? ? ? Hin Hheap _ _ _ _ Hscopes _ Hseal]; subst.
  destruct (heap_lookup_transport Hmut Hty (tfree_trm_read w a))
    as [y [ds [Hrecv [Hobj Hkinds]]]].
  destruct (object_location_has_nominal_record Hmut Hin Hheap Hobj)
    as [Ry [Py [HlocY Hdefs]]].
  destruct (@field_view_of_heap_location mode G e h w y Ry typ_bot a W U
    Hmut Hinc Hin Hheap Hrecv (forget_kind_of_binding HlocY) Hproject)
    as [S [Hmember [_ Hread]]].
  destruct (typed_record_member_has_declared_type Hdefs Hmember) as [d [Hget Htype]].
  inversion Htype; subst.
  rename t into z. rename Hget into Hfield.
  assert (Hk : ctx_k G z v_loc).
  {
    destruct (lookup_field_location Hkinds Hfield) as [z0 [HE HK]].
    inversion HE; subst. exact HK.
  }
  destruct (location_kind_has_mutable_binding Hmut Hin Hheap Hk) as [R [P Hloc]].
  assert (Hz : ty_var mode G objctx_empty e z U).
  { eapply ty_var_sub; unfold obj_typing, subtyping in *; [|exact Hread].
    cbn [ctx_obj] in *. eassumption. }
  pose proof (forget_kind_of_binding Hloc) as Hb.
  set (A := rodot_read_ref_type R TS w TC).
  assert (HclA : closed A).
  {
    unfold A. apply scoped_read_reference_type; [|exact HclTC].
    apply sealed_type_is_closed. eapply bindings_of_sealed_context_are_sealed; eassumption.
  }
  assert (HscopeA : nothing_fresh_in_config A C).
  {
    unfold nothing_fresh_in_config, A. intros q Hq.
    cbn [fv TypFreeVar fv_typ fv_dec AvarFreeVar] in Hq.
    repeat rewrite in_union in Hq.
    rewrite ?in_empty, ?in_singleton in Hq.
    repeat match goal with Hq : _ \/ _ |- _ => destruct Hq as [Hq | Hq] end;
      try contradiction.
    - apply (proj2 (proj1 Hscopes)).
      eapply bound_type_free_vars_in_context; [exact Hb |].
      change (q \in fv R \u (\{} \u \{})). rewrite in_union. now left.
    - now apply HfvTC.
    - subst q. unfold C. cbn [fv TrmFreeVar fv_trm AvarFreeVar].
      rewrite in_union, in_singleton. auto.
  }
  destruct (var_fresh (fv_config C \u ctx_fv G \u fv A)) as [p Hp].
  rewrite !notin_union in Hp. destruct Hp as [HpC [HpG HpA]].
  set (G' := G § p / v_ref ~ A).
  set (e' := e & p ~ z).
  exists G', (config_mk (trm_var (avar_f p)) fs h e' (fv_config C)).
  split.
  - assert (Hmode : mode_viewpoint_adaptation' mode = mode_viewpoint_adapt_mutability)
      by (destruct mode; simpl in *; congruence).
    eapply (@tred_read_obj mode G P w p y z a T A U W R (typ_mut_marker typ_bot)
      ds (trm_read (avar_f w) a) fs e h Lv); try assumption; try reflexivity.
    + cbn [fresh length]. auto.
    + auto.
    + rewrite Hmode. exists TS, TC. repeat split; assumption || reflexivity.
  - assert (HpD : p \notin ctx_dom G)
      by (intro Hnew; apply HpC; exact (proj1 (proj1 Hscopes) _ Hnew)).
    assert (HpE : p # e) by (eapply fresh_from_machine_for_env; exact HpC).
    assert (HG : ctx_extends G G') by (apply ctx_extends_with_fresh; exact HpD).
    assert (HE : preserves_bindings e e') by (now apply fresh_ref_extension_keeps_bindings).
    apply (@read_alias_preserves_continuation_type mode G (trm_read (avar_f w) a)
      fs h e Lv T z p P R (typ_or TC (typ_sel (avar_f w) (typ_label_refcap typ_refcap_mutability) (avar_b 0)))
      (rodot_read_term_type TS w TC)); try assumption.
    apply ty_var_and; unfold obj_typing.
    + eapply nonmutable_alias_has_stripped_view with (loc := z) (R := R) (S := U);
        try assumption.
      * exact (proj1 HG _ _ Hb).
      * apply ctx_binds_e.
      * apply tyq_var_sym, tyq_var_binds, binds_push_eq.
      * eapply (proj1 (types_under_renv_extension mode)); [|exact HE].
        eapply (proj1 (ctx_extends_types mode)); eassumption.
      * eapply (proj2 (proj2 (types_under_renv_extension mode))); [|exact HE].
        eapply (proj2 (proj2 (ctx_extends_types mode))); eassumption.
    + eapply ty_var_sub with (T := A); unfold obj_typing, subtyping.
      * apply ty_var_var, ctx_binds_e.
      * apply subtyp_and12.
Qed.

(* Bound indices outside the binder depth may be replaced by a fixed name. *)

Local Lemma seal_open_avar_at_depth d z x (a : avar) :
  seal_rec d z (open_rec d x a) = open_rec d x (seal_rec (S d) z a).
Proof.
  destruct a; unfold open_rec, AvarOpenable, seal_rec, AvarSealable;
    repeat case_if; try reflexivity; try congruence; lia.
Qed.

Local Lemma seal_open_types_at_depth :
  (forall T d z x,
    seal_rec_typ d z (open_rec_typ d x T) =
    open_rec_typ d x (seal_rec_typ (S d) z T)) /\
  (forall D d z x,
    seal_rec_dec d z (open_rec_dec d x D) =
    open_rec_dec d x (seal_rec_dec (S d) z D)).
Proof.
  apply typ_mutind; intros;
    cbn [seal_rec_typ seal_rec_dec open_rec_typ open_rec_dec];
    try reflexivity; f_equal; auto using seal_open_avar_at_depth.
Qed.

Local Lemma seal_open_terms_at_depth :
  (forall t d z x,
    seal_rec_trm d z (open_rec_trm d x t) =
    open_rec_trm d x (seal_rec_trm (S d) z t)) /\
  (forall l d z x,
    seal_rec_lit d z (open_rec_lit d x l) =
    open_rec_lit d x (seal_rec_lit (S d) z l)) /\
  (forall v d z x,
    seal_rec_def d z (open_rec_def d x v) =
    open_rec_def d x (seal_rec_def (S d) z v)) /\
  (forall ds d z x,
    seal_rec_defs d z (open_rec_defs d x ds) =
    open_rec_defs d x (seal_rec_defs (S d) z ds)).
Proof.
  destruct seal_open_types_at_depth as [HT HD].
  apply trm_mutind; intros;
    cbn [seal_rec_trm seal_rec_lit seal_rec_def seal_rec_defs
         open_rec_trm open_rec_lit open_rec_def open_rec_defs];
    try reflexivity; f_equal; auto using seal_open_avar_at_depth.
Qed.

Local Lemma seal_open_typ d z x (T : typ) :
  seal_rec d z (open_rec d x T) = open_rec d x (seal_rec (S d) z T).
Proof. apply (proj1 seal_open_types_at_depth). Qed.

Local Lemma seal_open_trm d z x (t : trm) :
  seal_rec d z (open_rec d x t) = open_rec d x (seal_rec (S d) z t).
Proof. apply (proj1 seal_open_terms_at_depth). Qed.

Local Lemma seal_open_defs d z x (ds : defs) :
  seal_rec d z (open_rec d x ds) = open_rec d x (seal_rec (S d) z ds).
Proof. apply (proj2 (proj2 (proj2 seal_open_terms_at_depth))). Qed.

Local Lemma seal_preserves_avar_bound_at_lower_depth d k z (a : avar) :
  k < d -> (seal_rec d z a = avar_b k <-> a = avar_b k).
Proof.
  intros Hd. destruct a; unfold seal_rec, AvarSealable;
    repeat case_if; split; intro E; try assumption; inversion E; lia.
Qed.

Local Lemma independent_bound_seal :
  (forall T d k z, k < d ->
     independent_bound_type k (seal_rec_typ d z T) <-> independent_bound_type k T) /\
  (forall D d k z, k < d ->
     independent_bound_dec k (seal_rec_dec d z D) <-> independent_bound_dec k D).
Proof.
  apply typ_mutind; intros;
    cbn [independent_bound_type independent_bound_dec seal_rec_typ seal_rec_dec];
    try (rewrite ?H by lia); try (rewrite ?H0 by lia); try (rewrite ?H1 by lia);
    try reflexivity.
  destruct t; cbn.
  all: repeat match goal with |- context [seal_rec ?d ?z ?a = avar_b ?k] =>
    rewrite (@seal_preserves_avar_bound_at_lower_depth d k z a) by assumption
  end; reflexivity.
Qed.

Local Lemma seal_binder_independence d k z (T : typ) :
  k < d ->
  (typ_indep_b k (seal_rec d z T) <-> typ_indep_b k T).
Proof.
  intro Hlt. rewrite <- !(proj1 independent_bound_characterization).
  apply (proj1 independent_bound_seal). exact Hlt.
Qed.

Local Lemma seal_open_avar_inside k d z x (a : avar) :
  k < d -> seal_rec d z (open_rec k x a) = open_rec k x (seal_rec d z a).
Proof.
  intros Hlt. destruct a; unfold seal_rec, AvarSealable, open_rec, AvarOpenable;
    repeat case_if; try reflexivity; try congruence; lia.
Qed.

Local Lemma seal_open_type_components_inside :
  (forall T k d z x, k < d ->
    seal_rec_typ d z (open_rec_typ k x T) =
    open_rec_typ k x (seal_rec_typ d z T)) /\
  (forall D k d z x, k < d ->
    seal_rec_dec d z (open_rec_dec k x D) =
    open_rec_dec k x (seal_rec_dec d z D)).
Proof.
  apply typ_mutind; intros;
    cbn [seal_rec_typ seal_rec_dec open_rec_typ open_rec_dec];
    try reflexivity; f_equal;
    eauto using seal_open_avar_inside.
  all: match goal with IH : forall k d z x, k < d -> _ |- _ => apply IH; lia end.
Qed.

Local Lemma seal_open_typ_inside k d z x (T : typ) :
  k < d -> seal_rec d z (open_rec k x T) = open_rec k x (seal_rec d z T).
Proof. apply (proj1 seal_open_type_components_inside). Qed.

Local Lemma seal_type_equivalence e T U :
  tyq_typ e T U ->
  forall d z, tyq_typ e (seal_rec d z T) (seal_rec d z U).
Proof.
  intro Hq. induction Hq; intros d z;
    cbn [seal_rec TypSealable seal_rec_typ seal_rec_dec AvarSealable];
    unfold typing_equiv in *.
  - destruct H; apply tyq_typ_nulary; constructor.
  - destruct H; cbn [seal_rec TypSealable seal_rec_typ];
    [apply tyq_typ_andor with (T := typ_and) | apply tyq_typ_andor with (T := typ_or)];
    unfold typing_equiv; try constructor; auto.
  - apply tyq_typ_fun; unfold typing_equiv; [auto |].
    intros x. repeat rewrite <- seal_open_typ_inside by lia. auto.
  - apply tyq_typ_fld; unfold typing_equiv; auto.
  - apply tyq_typ_typ; unfold typing_equiv;
      intros x; repeat rewrite <- seal_open_typ_inside by lia; auto.
  - now apply tyq_typ_sel_normal.
  - apply tyq_typ_sel.
  - apply tyq_typ_bnd. unfold typing_equiv. intros x. repeat rewrite <- seal_open_typ_inside by lia. auto.
  - apply tyq_typ_met; unfold typing_equiv.
    + intros x. repeat rewrite <- seal_open_typ_inside by lia. auto.
    + auto.
    + intros x y. repeat rewrite <- seal_open_typ_inside by lia. auto.
Qed.

Local Lemma seal_context_binding G x T :
  ctx_binds x T G -> forall d z, ctx_binds x (seal_rec d z T) (seal_rec d z G).
Proof.
  intro H. induction H; intros;
    cbn [seal_rec CtxSealable ctx_seal_rec]; eauto using ctx_binds.
Qed.

Local Lemma seal_typed_types mode z :
  (forall G Go e x T, ty_var mode G Go e x T ->
    ty_var mode (seal z G) Go e x (seal z T)) /\
  (forall G Go e T U, subtyp mode G Go e T U ->
    subtyp mode (seal z G) Go e (seal z T) (seal z U)) /\
  (forall G Go e T U, ty_incap mode G Go e T U ->
    ty_incap mode (seal z G) Go e (seal z T) (seal z U)).
Proof.
  apply (@ts_mutind mode
    (fun G Go e x T _ => ty_var mode (seal z G) Go e x (seal z T))
    (fun G Go e T U _ => subtyp mode (seal z G) Go e (seal z T) (seal z U))
    (fun G Go e T U _ => ty_incap mode (seal z G) Go e (seal z T) (seal z U))).
  all: intros; unfold obj_typing, subtyping, obj_ref_incap in *.
  all: cbn [seal_rec TypSealable seal_rec_typ seal_rec_dec AvarSealable] in *.
  - apply ty_var_var, seal_context_binding; assumption.
  - apply ty_rec_intro; unfold obj_typing, obj_ref_incap.
    + rewrite <- seal_open_typ. assumption.
    + apply seal_binder_independence; [lia | assumption].
    + intros Hcap. rewrite <- seal_open_typ. auto.
  - rewrite seal_open_typ. apply ty_rec_elim; unfold obj_typing;
      [eassumption | apply seal_binder_independence; [lia | assumption]].
  - apply ty_var_and; unfold obj_typing; assumption.
  - eapply ty_var_sub; unfold obj_typing, subtyping; eassumption.
  - eapply ty_var_mut_top; unfold obj_typing; eassumption.
  - apply subtyp_top.
  - apply subtyp_bot.
  - apply subtyp_refl.
  - eapply subtyp_trans; unfold subtyping; eassumption.
  - apply subtyp_and11.
  - apply subtyp_and12.
  - apply subtyp_and2; unfold subtyping; eassumption.
  - apply subtyp_or11.
  - apply subtyp_or12.
  - apply subtyp_or2; unfold subtyping; eassumption.
  - apply subtyp_fld; unfold subtyping; eassumption.
  - apply subtyp_typ; unfold subtyping; intro x; rewrite <- !seal_open_typ; auto.
  - rewrite seal_open_typ. eapply subtyp_sel2; unfold obj_typing; eassumption.
  - rewrite seal_open_typ. eapply subtyp_sel1; unfold obj_typing; eassumption.
  - eapply subtyp_fun with (L := L); unfold subtyping; try eassumption.
    intros x Hx. rewrite <- !seal_open_typ.
    change (subtyp mode (seal z (G § x / v_par ~ S2)) objctx_empty e
      (seal z (open x T1)) (seal z (open x T2))). auto.
  - eapply subtyp_met with (L := L); unfold subtyping; try eassumption.
    + intros x Hx. rewrite <- !seal_open_typ.
      change (subtyp mode (seal z (G § x / v_par ~ TZ2)) objctx_empty e
        (seal z (open x TC2)) (seal z (open x TC1))). auto.
    + intros Hsef HInd.
      apply seal_binder_independence; [lia |].
      match goal with HF : mode_has_sef mode -> typ_indep_b 0 TC2 -> typ_indep_b 0 TC1 |- _ =>
        apply HF; [exact Hsef |]
      end.
      apply seal_binder_independence with (d := 1) (z := z); [lia | exact HInd].
    + intros x Hx y Hneq Hy. repeat rewrite <- seal_open_typ.
      change (subtyp mode
        (seal z (ctx_met G x TZ2 y TC2)) objctx_empty e
        (seal z (open_met x y TR1)) (seal z (open_met x y TR2))).
      auto.
  - apply subtyp_tyq. apply seal_type_equivalence. assumption.
  - apply subtyp_typ_and.
  - apply subtyp_dist.
  - apply subtyp_nocap_bnd.
  - apply subtyp_nocap_typ.
  - apply subtyp_nocap_fld.
  - apply subtyp_nocap_met.
  - apply subtyp_nocap_fun. assumption.
  - apply subtyp_nocap_mut_top_boundless. assumption.
  - apply subtyp_nocap_mut_top_complement. assumption.
  - apply subtyp_nocap_mut_bot. assumption.
  - apply subtyp_mut_top. assumption.
  - apply ty_incap_top.
  - apply ty_incap_bot.
  - apply ty_incap_typ.
  - apply ty_incap_cap.
  - apply ty_incap_met.
  - apply ty_incap_fld.
  - eapply ty_incap_sel; unfold obj_typing, obj_ref_incap; [eassumption |].
    rewrite <- seal_open_typ. assumption.
  - apply ty_incap_rec.
  - apply ty_incap_and; unfold obj_ref_incap; assumption.
  - apply ty_incap_or; unfold obj_ref_incap; assumption.
  - apply ty_incap_fun. assumption.
  - apply ty_incap_nocap; unfold subtyping; assumption.
Qed.

Local Lemma seal_capability_bound mode C z G e S B :
  ty_capbnd mode C G objctx_empty e S B ->
  ty_capbnd mode C (seal z G) objctx_empty e (seal z S) (seal_rec 1 z B).
Proof.
  intro H. induction H;
    cbn [seal_rec TypSealable seal_rec_typ seal_rec_dec AvarSealable];
    unfold obj_cap_bnd.
  - apply ty_capbnd_top.
  - apply ty_capbnd_bot.
  - apply ty_capbnd_typ.
  - apply ty_capbnd_cap_sel.
  - apply ty_capbnd_cap_ignore. assumption.
  - apply ty_capbnd_met.
  - apply ty_capbnd_fld.
  - eapply ty_capbnd_sel; unfold obj_typing, obj_cap_bnd.
    + pose proof ((proj1 (seal_typed_types mode z)) _ _ _ _ _ H) as Hmapped.
      exact Hmapped.
    + rewrite <- seal_open_typ. exact IHty_capbnd.
  - apply ty_capbnd_rec.
  - apply ty_capbnd_and; unfold obj_cap_bnd; assumption.
  - apply ty_capbnd_or; unfold obj_cap_bnd; assumption.
  - apply ty_capbnd_all.
Qed.

Local Lemma seal_read_term_type z w TS TC :
  seal z (rodot_read_term_type TS w TC) =
  rodot_read_term_type (seal z TS) w (seal_rec 1 z TC).
Proof.
  cbn [seal_rec TypSealable seal_rec_typ seal_rec_dec AvarSealable].
  rewrite If_r by lia. reflexivity.
Qed.

Local Lemma seal_viewpoint_type mode z G e w S U :
  viewpoint_adapt mode w G objctx_empty e S U ->
  viewpoint_adapt mode w (seal z G) objctx_empty e (seal z S) (seal z U).
Proof.
  unfold viewpoint_adapt. destruct (mode_viewpoint_adaptation' mode).
  - now intros ->.
  - inversion 1; subst.
    rewrite seal_read_term_type.
    apply viewpoint_adapt_cap_strip_combine; unfold obj_ref_incap, obj_cap_bnd.
    + eapply (proj2 (proj2 (seal_typed_types mode z))); eassumption.
    + eapply seal_capability_bound; eassumption.
Qed.

Local Lemma seal_context_visibility G x :
  ctx_vis G x -> forall d z, ctx_vis (seal_rec d z G) x.
Proof.
  intro H. induction H; intros; cbn [seal_rec CtxSealable ctx_seal_rec]; eauto using ctx_vis.
Qed.

Local Definition seal_objctx z Go :=
  match Go with
  | objctx_empty => objctx_empty
  | objctx_lit x T => objctx_lit x (seal_rec 1 z T)
  | objctx_heap x T => objctx_heap x (seal_rec 1 z T)
  end.

Local Lemma seal_context_object z G Go :
  seal z (G §§& Go) = (seal z G) §§& (seal_objctx z Go).
Proof.
  destruct Go; cbn [ctx_obj seal_objctx seal_rec CtxSealable ctx_seal_rec];
    rewrite ?seal_open_typ; reflexivity.
Qed.

Local Lemma seal_context_method mode z G Go p S w C :
  seal z (ctx_obj_met mode G Go p S w C) =
    ctx_obj_met mode (seal z G) (seal_objctx z Go) p (seal z S) w (seal_rec 1 z C).
Proof.
  unfold ctx_obj_met. destruct Go; destruct (mode_visibility' mode); cbn [seal_objctx
    seal_rec CtxSealable ctx_seal_rec TypSealable seal_rec_typ];
    repeat rewrite seal_open_typ; reflexivity.
Qed.

Local Lemma seal_open_method_type z p w (T : typ) :
  seal z (open_met p w T) = open_met p w (seal_rec 2 z T).
Proof. now rewrite !seal_open_typ. Qed.

Local Lemma seal_open_method_term z p w (t : trm) :
  seal z (open_met p w t) = open_met p w (seal_rec 2 z t).
Proof. now rewrite !seal_open_trm. Qed.

Local Lemma seal_definition_label z n (d : def) :
  label_of (seal_rec n z d) = label_of d.
Proof. destruct d; reflexivity. Qed.

Local Lemma seal_preserves_absent_definition z n l ds :
  defs_hasnt ds l -> defs_hasnt (seal_rec n z ds) l.
Proof.
  unfold defs_hasnt.
  induction ds as [|ds IH d]; intros H; [reflexivity |].
  change (get_def l (defs_cons (seal_rec n z ds) (seal_rec n z d)) = None).
  cbn [get_def] in H |- *. rewrite seal_definition_label. case_if; try discriminate; auto.
Qed.

Local Lemma seal_literal_object_type mode z T :
  seal z (typ_objlit mode T) = typ_objlit mode (seal_rec 1 z T).
Proof. destruct mode; reflexivity. Qed.

Local Ltac seal_from_variable_derivation Hvar :=
  match goal with H : ty_var _ _ _ _ _ _ |- _ => exact (Hvar _ _ _ _ _ H) end.

Local Lemma seal_term_judgments mode z :
  (forall G Go e t T, ty_trm mode G Go e t T ->
    ty_trm mode (seal z G) (seal_objctx z Go) e (seal z t) (seal z T)) /\
  (forall G Go e l T, ty_lit mode G Go e l T ->
    ty_lit mode (seal z G) (seal_objctx z Go) e (seal z l) (seal z T)) /\
  (forall G Go e d D, ty_def mode G Go e d D ->
    ty_def mode (seal z G) (seal_objctx z Go) e (seal z d) (seal z D)) /\
  (forall G Go e ds T, ty_defs mode G Go e ds T ->
    ty_defs mode (seal z G) (seal_objctx z Go) e (seal z ds) (seal z T)).
Proof.
  destruct (seal_typed_types mode z) as [Hvar [Hsub Hstrip]].
  apply (@rules_mutind mode
    (fun G Go e t T _ =>
      ty_trm mode (seal z G) (seal_objctx z Go) e (seal z t) (seal z T))
    (fun G Go e l T _ =>
      ty_lit mode (seal z G) (seal_objctx z Go) e (seal z l) (seal z T))
    (fun G Go e d D _ =>
      ty_def mode (seal z G) (seal_objctx z Go) e (seal z d) (seal z D))
    (fun G Go e ds T _ =>
      ty_defs mode (seal z G) (seal_objctx z Go) e (seal z ds) (seal z T))).
  all: intros; unfold obj_typing, obj_dec_typing, subtyping in *.
  all: cbn [seal_objctx seal_rec TrmSealable LitSealable DefSealable DefsSealable
        seal_rec_trm seal_rec_lit seal_rec_def seal_rec_defs
        TypSealable DecSealable seal_rec_typ seal_rec_dec AvarSealable].
  - apply ty_trm_var; unfold obj_typing; [|auto].
    intros Hmode. apply seal_context_visibility. auto.
  - rewrite seal_open_typ. eapply ty_trm_apply; unfold obj_typing;
      try solve [eauto 5 | intro Hmode; apply seal_context_visibility; auto].
    seal_from_variable_derivation Hvar.
  - eapply ty_trm_read; unfold obj_typing.
    + intros Hmode. apply seal_context_visibility. auto.
    + seal_from_variable_derivation Hvar.
    + eapply seal_viewpoint_type. eassumption.
  - eapply ty_trm_write; unfold obj_typing;
      try solve [intro Hmode; apply seal_context_visibility; auto].
    + intro Hmode.
      match goal with HP : mode_has_mutability _ -> ty_var _ _ _ _ _ _ |- _ =>
        exact (Hvar _ _ _ _ _ (HP Hmode))
      end.
    + seal_from_variable_derivation Hvar.
    + seal_from_variable_derivation Hvar.
  - rewrite seal_open_method_type. eapply ty_trm_call; unfold obj_typing;
      try solve [intro Hmode; apply seal_context_visibility; auto].
    + seal_from_variable_derivation Hvar.
    + seal_from_variable_derivation Hvar.
    + intros Hmode. apply seal_binder_independence; [lia | auto].
    + rewrite <- seal_open_typ. seal_from_variable_derivation Hvar.
  - eapply ty_trm_let with (L := L); unfold obj_typing; try eassumption.
    intros x Hx. rewrite <- seal_open_trm.
    change (ty_trm mode (seal z (G §ˣ x ~ T)) objctx_empty e
      (seal z (open x u)) (seal z U)). auto.
  - eapply ty_trm_lit with (L := L); unfold obj_typing; try eassumption.
    intros x Hx. rewrite <- seal_open_trm.
    change (ty_trm mode (seal z (G §ˣ x ~ T)) objctx_empty e
      (seal z (open x u)) (seal z U)). auto.
  - eapply ty_trm_sub; unfold obj_typing, subtyping; eauto.
  - eapply ty_lit_fun with (L := L); unfold obj_typing; try assumption.
    intros x Hx. rewrite <- seal_open_trm, <- seal_open_typ.
    change (ty_trm mode (seal z (G § x / v_par ~ T)) objctx_empty e
      (seal z (open x t)) (seal z (open x U))). auto.
  - rewrite seal_literal_object_type.
    eapply ty_lit_obj with (L := L); unfold obj_typing.
    + intros x Hx. rewrite <- seal_open_defs, <- seal_open_typ.
      change (ty_defs mode (seal z G) (seal_objctx z (objctx_lit x T)) e
        (seal z (open x ds)) (seal z (open x T))). auto.
    + apply seal_binder_independence; [lia | assumption].
  - eapply ty_def_typ with (L := L); unfold typing_equiv.
    intros x Hx. rewrite <- !seal_open_typ.
    apply seal_type_equivalence. exact (t x Hx).
  - apply ty_def_fld; unfold obj_typing; rewrite <- seal_context_object.
    + intros Hmode. apply seal_context_visibility. auto.
    + apply Hvar. assumption.
  - eapply ty_def_met with (L := L); unfold obj_typing.
    intros x Hx y Hneq Hy.
    rewrite <- seal_context_method, <- seal_open_method_term, <- seal_open_method_type.
    auto.
  - apply ty_defs_one; unfold obj_dec_typing; assumption.
  - eapply ty_defs_cons; unfold obj_typing, obj_dec_typing; try eassumption.
    rewrite seal_definition_label. now apply seal_preserves_absent_definition.
Qed.

Local Lemma seal_removes_external_type_indices :
  (forall (T : typ) d k z y, open_rec (d + k) y (seal_rec d z T) = seal_rec d z T) /\
  (forall (D : dec) d k z y, open_rec (d + k) y (seal_rec d z D) = seal_rec d z D).
Proof.
  assert (HA : forall (a : avar) d k z y,
      open_rec (d + k) y (seal_rec d z a) = seal_rec d z a).
  {
    destruct a; intros; unfold open_rec, AvarOpenable, seal_rec, AvarSealable;
      repeat case_if; try reflexivity; try lia.
  }
  apply typ_mutind; intros;
    cbn [open_rec TypOpenable DecOpenable open_rec_typ open_rec_dec
      seal_rec TypSealable DecSealable seal_rec_typ seal_rec_dec];
    try reflexivity; f_equal; repeat rewrite <- Nat.add_succ_l;
    auto.
Qed.

Local Lemma sealing_closed_terms_is_identity :
  (forall (t : trm) d, (forall k y, open_rec (d + k) y t = t) ->
    forall z, seal_rec d z t = t) /\
  (forall (l : lit) d, (forall k y, open_rec (d + k) y l = l) ->
    forall z, seal_rec d z l = l) /\
  (forall (v : def) d, (forall k y, open_rec (d + k) y v = v) ->
    forall z, seal_rec d z v = v) /\
  (forall (ds : defs) d, (forall k y, open_rec (d + k) y ds = ds) ->
    forall z, seal_rec d z ds = ds).
Proof.
  assert (HA : forall (a : avar) d, (forall k y, open_rec (d+k) y a = a) ->
    forall z, seal_rec d z a = a).
  {
    intros [n | x] d H z; [|reflexivity].
    unfold seal_rec, AvarSealable. case_if; [|reflexivity].
    specialize (H (n-d) z). replace (d + (n-d)) with n in H by lia.
    unfold open_rec, AvarOpenable in H. rewrite If_l in H by reflexivity. discriminate.
  }
  destruct seal_if_all_higher_openings_are_fixed as [HT HD].
  apply trm_mutind; intros;
    match goal with H : forall (k : nat) (a : var), _ |- _ => rename H into Hfixed end.
  all: unfold seal_rec, TrmSealable, LitSealable, DefSealable, DefsSealable.
  all: cbn [seal_rec_trm seal_rec_lit seal_rec_def seal_rec_defs];
    fold seal_rec_trm seal_rec_lit seal_rec_def seal_rec_defs.
  all: try reflexivity; f_equal.
  all: first [apply HA | apply HT | apply HD |
    match goal with
    | IH : forall (d : nat), _ -> forall (z : var), _ |- _ => apply IH
    end].
  all: intros k y; pose proof (Hfixed k y) as Hs;
    cbn [open_rec TrmOpenable LitOpenable DefOpenable DefsOpenable
         open_rec_trm open_rec_lit open_rec_def open_rec_defs] in Hs;
    fold open_rec_trm open_rec_lit open_rec_def open_rec_defs in Hs;
    rewrite ?Nat.add_succ_l; injection Hs; auto.
Qed.

Local Fixpoint seal_typing_stack z fs : stack :=
  match fs with
  | stack_nil => stack_nil
  | stack_cons (frame_let t) fs' => stack_cons (frame_let (seal_rec 1 z t)) (seal_typing_stack z fs')
  end.

Local Lemma sealing_closed_stack_is_identity z fs :
  closed fs -> seal_typing_stack z fs = fs.
Proof.
  induction fs as [|[t] fs IH]; intros Hc; [reflexivity |].
  cbn [seal_typing_stack]. f_equal.
  - f_equal. apply (proj1 sealing_closed_terms_is_identity).
    intros k x. pose proof (Hc k x) as Hr.
    change (stack_cons (frame_let (open_rec (S k) x t)) (open_rec k x fs) =
      stack_cons (frame_let t) fs) in Hr.
    change (open_rec (S k) x t = t); now injection Hr.
  - apply IH. intros k x. pose proof (Hc k x) as Hr.
    change (stack_cons (frame_let (open_rec (S k) x t)) (open_rec k x fs) =
      stack_cons (frame_let t) fs) in Hr.
    now injection Hr.
Qed.

Local Lemma seal_stack_judgment mode G e S fs T :
  @ty_stack mode G e S fs T -> forall z,
  @ty_stack mode (seal z G) e (seal z S) (seal_typing_stack z fs) (seal z T).
Proof.
  intro H. induction H as [G e S T HS | L G e fs t S U T Hstack IH Hbody].
  - intro z. apply ty_stack_nil. unfold subtyping in *.
    eapply (proj1 (proj2 (seal_typed_types mode z))); eassumption.
  - intro z. cbn [seal_typing_stack]. apply ty_stack_let with (L := L) (T := seal z U).
    + apply IH.
    + intros x Hx. unfold obj_typing. rewrite <- seal_open_trm.
      change (ty_trm mode (seal z (G §ˣ x ~ S)) objctx_empty e (seal z (open x t)) (seal z U)).
      exact ((proj1 (seal_term_judgments mode z)) _ objctx_empty _ _ _ (Hbody x Hx)).
Qed.

Local Lemma rename_stack_cons f t fs :
  rename f (stack_cons (frame_let t) fs) =
  stack_cons (frame_let (rename f t)) (rename f fs).
Proof.
  change (stack_cons (frame_let (transform_trm (avar_map f) t 1)) (rename f fs) =
    stack_cons (frame_let (rename f t)) (rename f fs)).
  f_equal. f_equal. apply (proj1 (rename_depth_terms f)).
Qed.

Local Lemma rename_fixed_stack f (fs : stack) :
  preserves_fv f fs -> rename f fs = fs.
Proof.
  induction fs as [|[t] fs IH]; intro Hfixed; [reflexivity |].
  rewrite rename_stack_cons. f_equal.
  - f_equal. apply (proj1 (rename_fixed_terms f)).
    intros x Hx. apply Hfixed. change (x \in fv t \u fv fs). rewrite in_union. auto.
  - apply IH. intros x Hx. apply Hfixed.
    change (x \in fv t \u fv fs). rewrite in_union. auto.
Qed.

Local Lemma map_stack_judgment mode G e S fs T :
  @ty_stack mode G e S fs T ->
  forall f G' e', maps_context mode e' f G G' -> maps_reference_names e e' f ->
    @ty_stack mode G' e' (rename f S) (rename f fs) (rename f T).
Proof.
  intro H. induction H as [G e S T HS | L G e fs t S U T Hstack IH Hbody].
  - intros f G' e' HG HE. apply ty_stack_nil. unfold subtyping in *.
    eapply (proj1 (proj2 (map_type_judgments mode))); eassumption.
  - intros f G' e' HG HE. rewrite rename_stack_cons.
    apply ty_stack_let with (L := ctx_dom G') (T := rename f U).
    + now apply IH.
    + intros x Hx. unfold obj_typing.
      assert (Hmap : forall z, z \notin L ->
        forall g J e'', maps_context mode e'' g (G §ˣ z ~ S) J ->
          maps_reference_names e e'' g -> mapped_objctx_fresh g J objctx_empty ->
          ty_trm mode J objctx_empty e'' (rename g (open z t)) (rename g U)).
      {
        intros z Hz g J e'' Hctx Hrenv Hfresh.
        exact ((proj1 (map_term_judgments mode)) _ _ _ _ _ (Hbody z Hz)
          g J e'' Hctx Hrenv Hfresh).
      }
      mapped_term_binder mode f G G' e e' L v_let S t U x Hx HG HE Hmap.
Qed.

Local Lemma rename_read_term_type f w TS TC :
  rename f (rodot_read_term_type TS w TC) =
  rodot_read_term_type (rename f TS) (f w) (rename f TC).
Proof.
  change (rodot_read_term_type (rename f TS) (f w)
    (transform_typ (avar_map f) TC 1) = rodot_read_term_type (rename f TS) (f w) (rename f TC)).
  rewrite (proj1 (rename_depth_types f) TC 1 0). reflexivity.
Qed.

Local Lemma rename_seal_typing_types f :
  (forall T d z k, transform_typ (avar_map f) (seal_rec d z T) k =
    seal_rec d (f z) (transform_typ (avar_map f) T k)) /\
  (forall D d z k, transform_dec (avar_map f) (seal_rec d z D) k =
    seal_rec d (f z) (transform_dec (avar_map f) D k)).
Proof.
  assert (HA : forall (a : avar) d z k, avar_map f (seal_rec d z a) k =
      seal_rec d (f z) (avar_map f a k)).
  {
    destruct a; unfold avar_map, rename_avar, seal_rec, AvarSealable; intros;
      repeat case_if; reflexivity.
  }
  apply typ_mutind; intros;
    cbn [seal_rec TypSealable DecSealable seal_rec_typ seal_rec_dec transform_typ transform_dec];
    try reflexivity; f_equal; auto.
Qed.

Local Lemma read_continuation_has_scoped_view mode G e h fs Lv w a T :
  mode_has_mutability mode ->
  @ty_config mode G (config_mk (trm_read (avar_f w) a) fs h e Lv) T ->
  exists W U TS TC,
    ty_var mode G objctx_empty e w (typ_rcd (dec_fld a W U)) /\
    ty_incap mode G objctx_empty e U TS /\
    ty_capbnd mode typ_refcap_mutability G objctx_empty e U TC /\
    @ty_stack mode G e (rodot_read_term_type TS w TC) fs T /\
    closed (typ_mut_marker TC) /\
    fv TC \c fv_config (config_mk (trm_read (avar_f w) a) fs h e Lv).
Proof.
  intros Hmut Htype.
  inversion Htype as [? ? ? ? ? ? V ? Hin Hheap Hstack Hframes Hcontrol Hterm
    Hscope HhasNull Hseal Hclosed HtypeClosed]; subst.
  destruct Hscope as [[Hdom Hctx] HtypeFV].
  destruct HhasNull as [null Hnull].
  destruct (read_continuation_type Hcontrol Hstack Hmut)
    as [W [U [TS [TC [Hproject [Hstrip [Hcap Hcontinue]]]]]]].
  inversion Hclosed as [? ? ? ? ? HclosedTerm HclosedStack HclosedHeap]; subst.
  set (W0 := seal null W).
  set (U0 := seal null U).
  set (TS0 := seal null TS).
  set (TC0 := seal_rec 1 null TC).
  pose proof ((proj1 (seal_typed_types mode null)) _ _ _ _ _ Hproject) as HP.
  pose proof ((proj2 (proj2 (seal_typed_types mode null))) _ _ _ _ _ Hstrip) as HS.
  pose proof (seal_capability_bound null Hcap) as HC.
  pose proof (seal_stack_judgment Hcontinue null) as HK.
  specialize (Hseal null).
  simpl seal_objctx in HP, HS.
  rewrite Hseal in HP, HS, HC, HK.
  rewrite (sealing_closed_stack_is_identity null HclosedStack),
    (closed_type_is_sealed HtypeClosed null), seal_read_term_type in HK.
  change (ty_var mode G objctx_empty e w (typ_rcd (dec_fld a W0 U0))) in HP.
  change (ty_incap mode G objctx_empty e U0 TS0) in HS.
  change (ty_capbnd mode typ_refcap_mutability G objctx_empty e U0 TC0) in HC.
  change (@ty_stack mode G e (rodot_read_term_type TS0 w TC0) fs T) in HK.
  set (C := config_mk (trm_read (avar_f w) a) fs h e Lv) in *.
  set (f := fun x : var => If x \in fv_config C then x else null).
  assert (Hfix : forall x, x \in fv_config C -> f x = x).
  { intros x Hx. unfold f. now rewrite If_l. }
  assert (Himage : forall x, f x \in fv_config C).
  {
    intro x. unfold f. case_if; [assumption |].
    unfold C. repeat rewrite in_union. tauto.
  }
  assert (HmapG : maps_context mode e f G G).
  {
    split.
    - intros x P Hb.
      rewrite Hfix by (apply Hdom; eapply swap_calls_binding_in_context; exact Hb).
      replace (rename f P) with P.
      + now apply ty_var_var.
      + symmetry. apply (proj1 (rename_fixed_types f)).
        intros y Hy. apply Hfix, Hctx. eapply bound_type_free_vars_in_context; eassumption.
    - intros x Hvis. rewrite Hfix by (apply Hdom; now apply vis_in_dom). exact Hvis.
  }
  assert (HmapE : maps_reference_names e e f).
  {
    assert (Hok : ok e) by (destruct Hheap as [_ [_ [_ [Ha _]]]]; exact Ha).
    split; [exact Hok |].
    intros x y Hb.
    rewrite (Hfix x) by (unfold C; apply dom_env_in_machine_fv; eapply get_some_inv; exact Hb).
    rewrite (Hfix y).
    - now apply tyq_var_binds.
    - pose proof (selected_reference_value_fv Hok Hb).
      unfold C. repeat rewrite in_union. tauto.
  }
  assert (Hw : f w = w).
  {
    apply Hfix. unfold C. change (w \in \{w} \u fv fs \u fv_heap h \u fv_renv e \u Lv).
    repeat rewrite in_union. rewrite in_singleton. auto.
  }
  exists (rename f W0), (rename f U0), (rename f TS0), (rename f TC0).
  repeat split.
  - pose proof ((proj1 (map_type_judgments mode)) _ _ _ _ _ HP f G e HmapG HmapE) as HH.
    now rewrite Hw in HH.
  - exact ((proj2 (proj2 (map_type_judgments mode))) _ _ _ _ _ HS f G e HmapG HmapE).
  - exact (map_cap_bound HC HmapG HmapE).
  - pose proof (map_stack_judgment HK HmapG HmapE) as HH.
    rewrite rename_read_term_type, Hw in HH.
    rewrite (rename_fixed_stack (f := f)) in HH by
      (intros x Hx; apply Hfix; unfold C; repeat rewrite in_union; auto).
    replace (rename f T) with T in HH by
      (symmetry; apply (proj1 (rename_fixed_types f)); intros x Hx; apply Hfix, HtypeFV, Hx).
    exact HH.
  - intro k. intro y. unfold TC0.
    change (open_rec k y (typ_mut_marker (transform_typ (avar_map f) (seal_rec 1 null TC) 0)) =
      typ_mut_marker (transform_typ (avar_map f) (seal_rec 1 null TC) 0)).
    rewrite (proj1 (rename_seal_typing_types f)).
    change (open_rec (0+k) y (seal_rec 0 (f null) (typ_mut_marker (rename f TC))) =
      seal_rec 0 (f null) (typ_mut_marker (rename f TC))).
    apply (proj1 seal_removes_external_type_indices).
  - apply (proj1 (rename_image_types f)). intros x Hx. apply Himage.
Qed.

Local Definition all_term_names_visible {A : Set} {AT : TFree A} G (a : A) :=
  forall x, tfree x a -> ctx_vis G x.

Local Lemma visibility_before_distinct_binding G k T x y :
  x <> y -> ctx_vis (G § y / k ~ T) x -> ctx_vis G x.
Proof. intros Hneq H; inversion H; subst; congruence || assumption. Qed.

Local Lemma typing_confines_term_names_to_visible_bindings mode :
  mode_has_visibility mode ->
  (forall G Go e t T, ty_trm mode G Go e t T ->
    all_term_names_visible (G §§& Go) t) /\
  (forall G Go e l T, ty_lit mode G Go e l T ->
    all_term_names_visible (G §§& Go) l) /\
  (forall G Go e d D, ty_def mode G Go e d D ->
    all_term_names_visible (G §§& Go) d) /\
  (forall G Go e ds T, ty_defs mode G Go e ds T ->
    all_term_names_visible (G §§& Go) ds).
Proof.
  intro Hmode.
  destruct swap_calls_free_open as [Htrm [_ [_ Hdefs]]].
  apply (@rules_mutind mode
    (fun G Go _ t _ _ => all_term_names_visible (G §§& Go) t)
    (fun G Go _ l _ _ => all_term_names_visible (G §§& Go) l)
    (fun G Go _ d _ _ => all_term_names_visible (G §§& Go) d)
    (fun G Go _ ds _ _ => all_term_names_visible (G §§& Go) ds)).
  all: unfold all_term_names_visible in *; cbn [ctx_obj] in *.
  all: intros.
  all: match goal with H : tfree _ _ |- _ => inversion H; subst end.
  all: try solve [eauto].
  all: try solve [match goal with H : tfree_defs _ defs_nil |- _ => inversion H end].
  all: try solve [
    match goal with
    | IH : forall z, z \notin ?L -> forall x : var, _ -> _,
      HF : tfree_trm ?x ?t |- _ =>
        let z := fresh "z" in let Hz := fresh "Hz" in let Hzx := fresh "Hzx" in
        destruct (var_fresh (L \u \{x})) as [z Hz];
        apply notin_union in Hz as [Hz Hzx]; rewrite notin_singleton in Hzx;
        specialize (IH z Hz x (Htrm _ _ HF 0 z));
        eapply visibility_before_distinct_binding; [|exact IH]; congruence
    | IH : forall z, z \notin ?L -> forall x : var, _ -> _,
      HF : tfree_defs ?x ?ds |- _ =>
        let z := fresh "z" in let Hz := fresh "Hz" in let Hzx := fresh "Hzx" in
        destruct (var_fresh (L \u \{x})) as [z Hz];
        apply notin_union in Hz as [Hz Hzx]; rewrite notin_singleton in Hzx;
        specialize (IH z Hz x (Hdefs _ _ HF 0 z));
        eapply visibility_before_distinct_binding; [|exact IH]; congruence
    end].
  destruct (var_fresh (L \u \{x})) as [arg Harg].
  apply notin_union in Harg as [Harg Hargx]. rewrite notin_singleton in Hargx.
  destruct (var_fresh ((L \u \{x}) \u \{arg})) as [self Hself].
  rewrite !notin_union, !notin_singleton in Hself.
  destruct Hself as [[Hself Hselfx] Hselfarg].
  pose proof (H arg Harg self Hselfarg Hself x
    (Htrm _ _ (Htrm _ _ H3 1 self) 0 arg)) as HV.
  unfold ctx_obj_met in HV. rewrite Hmode in HV.
  destruct Go.
  all: eapply visibility_before_distinct_binding in HV; [|congruence].
  all: eapply visibility_before_distinct_binding in HV; [|congruence].
  all: inversion HV.
Qed.

Local Lemma typed_methods_have_no_free_term_names mode G Go e m body C Z R :
  mode_has_mutability mode ->
  ty_def mode G Go e (def_met m body) (dec_met m C Z R) ->
  forall x, ~ tfree x body.
Proof.
  intros Hmut Hmeth x Hfree.
  inversion Hmeth; subst.
  assert (Hvis : mode_has_visibility mode) by (destruct mode; cbn in *; congruence).
  destruct swap_calls_free_open as [Htrm _].
  destruct (var_fresh (L \u \{x})) as [p Hp].
  rewrite notin_union, notin_singleton in Hp. destruct Hp as [Hp Hpx].
  destruct (var_fresh ((L \u \{x}) \u \{p})) as [w Hw].
  rewrite !notin_union, !notin_singleton in Hw. destruct Hw as [[Hw Hwx] Hwp].
  pose proof ((proj1 (typing_confines_term_names_to_visible_bindings mode Hvis)) _ _ _ _ _
    (H3 p Hp w Hwp Hw) x (Htrm _ _ (Htrm _ _ Hfree 1 w) 0 p)) as HF.
  cbn [ctx_obj] in HF. unfold ctx_obj_met in HF. rewrite Hvis in HF.
  destruct Go.
  all: eapply visibility_before_distinct_binding in HF; [|congruence].
  all: eapply visibility_before_distinct_binding in HF; [|congruence].
  all: inversion HF.
Qed.

Local Lemma call_with_nocap_constraints_uses_nocap_signature
    mode G h e Lv fs w p m T Z :
  mode_has_mutability mode ->
  mode_has_sef mode ->
  @ty_config mode G (config_mk (trm_call (avar_f w) m (avar_f p)) fs h e Lv) T ->
  ty_var mode G objctx_empty e w (typ_rcd (dec_met m typ_nocap Z typ_top)) ->
  ty_var mode G objctx_empty e p Z ->
  subtyp mode G objctx_empty e typ_nocap Z ->
  exists y ds R body TC TZ TR,
    binds w y e /\ binds y (item_obj ds) h /\ defs_has ds (def_met m body) /\
    ty_def mode G (objctx_heap y R) e (def_met m body) (dec_met m TC TZ TR) /\
    subtyp mode G objctx_empty e typ_nocap (open p TC) /\
    subtyp mode G objctx_empty e typ_nocap TZ /\
    typ_indep_b 0 TC /\
    (forall q, ~ tfree q body).
Proof.
  intros Hmut Hsef Hty Hreceiver Harg Hnocap.
  destruct (heap_lookup_transport Hmut Hty (tfree_trm_call_l w (avar_f p) m))
    as [y [ds [Href [Hobj _]]]].
  inversion Hty as [? ? ? ? ? ? U ? Hin Hheap Hstack Hframes Hcontrol]; subst.
  destruct (object_location_has_nominal_record Hmut Hin Hheap Hobj)
    as [R [P [Hloc Hdefs]]].
  assert (Hinc : mode_incap' mode = mode_incap_nocap)
    by (destruct mode; cbn in *; congruence).
  destruct (@method_view_of_heap_location mode G e h w y R typ_bot m typ_nocap Z typ_top
    Hmut Hinc Hin Hheap Href (forget_kind_of_binding Hloc) Hreceiver)
    as [TC [TZ [TR [Hmember [HZ [Hind [L [Hrecv Hresult]]]]]]]].
  destruct (typed_record_member_has_declared_type Hdefs Hmember) as [d [Hget Hdef]].
  assert (Hshape : exists body, d = def_met m body) by (inversion Hdef; subst; eauto).
  destruct Hshape as [body ->].
  assert (Hok : ok e) by (destruct Hheap as [_ [_ [_ [Hok _]]]]; exact Hok).
  assert (Hvis : ctx_vis G p) by
    (eapply active_operand_visible; [exact Hty | apply tfree_trm_call_r]).
  exists y, ds, R, body, TC, TZ. exists TR. repeat split; try assumption.
  - exact (@instantiate_call_receiver_subtyping mode G e L p Z typ_nocap TC
      Hok Hvis Harg Hrecv).
  - eapply subtyp_trans; unfold subtyping; eassumption.
  - apply Hind; [exact Hsef | apply typ_indep_nulary; constructor].
  - eapply typed_methods_have_no_free_term_names; eassumption.
Qed.

Local Lemma inert_top_is_not_below_bottom mode G e :
  mode_has_mutability mode -> mode_incap' mode = mode_incap_nocap ->
  @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  ~ subtyp mode G objctx_empty e typ_top typ_bot.
Proof.
  intros Hmut Hinc Hin Hok Hcorr Hsub.
  pose proof ((proj1 (proj2 (inert_judgments_admit_precise_selections mode Hmut Hinc)))
    _ _ _ _ _ Hsub Hin Hok Hcorr) as Htight.
  pose proof (capability_shape_preserved_by_tight_subtyping Htight
    Hmut Hin Hok Hcorr (capability_shape_top mode G e typ_top)) as Hfalse.
  inversion Hfalse.
Qed.

Local Lemma reference_with_readonly_bound_cannot_write mode G e w R B :
  mode_has_mutability mode -> mode_incap' mode = mode_incap_nocap ->
  @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  ctx_binds w (typ_objref R (typ_mut_marker B)) G ->
  (exists q, capability_shape mode G e typ_top (open q B)) ->
  ~ ty_var mode G objctx_empty e w (typ_mut_marker typ_bot).
Proof.
  intros Hmut Hinc Hin Hok Hcorr Hb [q Hbound] Hwrite.
  pose proof ((proj1 (inert_judgments_admit_precise_selections mode Hmut Hinc))
    _ _ _ _ _ Hwrite Hin Hok Hcorr) as Htight.
  destruct (tight_capability_uses_precise_bounds Hmut Hin Hok Hcorr Htight)
    as [U [Hmem [_ Hupper]]].
  assert (Hnominal : precise_member G w
      (dec_typ (typ_label_refcap typ_refcap_mutability) typ_bot B)).
  {
    exists (typ_objref R (typ_mut_marker B)).
    eapply pf_and2, pf_bind. exact Hb.
  }
  pose proof (@precise_type_member_unique mode G w (typ_label_refcap typ_refcap_mutability)
    typ_bot U typ_bot B Hmut Hin Hmem Hnominal) as [_ ->].
  pose proof (capability_shape_preserved_by_tight_subtyping (Hupper q)
    Hmut Hin Hok Hcorr Hbound) as Hfalse.
  inversion Hfalse.
Qed.

Local Lemma readonly_base_aliases_rule_out_base_writes mode G base t fs h e L T :
  mode_has_sef mode -> mode_has_mutability mode ->
  @ty_config mode G (config_mk t fs h e L) T ->
  (forall w y, tfree w t -> binds w y e -> y \in dom base ->
    exists R B q,
      ctx_binds w (typ_objref R (typ_mut_marker B)) G /\
      capability_shape mode G e typ_top (open q B)) ->
  permits_writes_only_outside base (config_mk t fs h e L).
Proof.
  intros Hsef Hmut Hcfg Hreadonly.
  destruct t as [| | | | | a f a0 | ]; try exact I.
  destruct a as [k | w]; [exact I |].
  cbn [permits_writes_only_outside]. intros y Hb Hy.
  destruct (Hreadonly w y (tfree_trm_write_l w a0 f) Hb Hy) as [R [B [q [Href Hbound]]]].
  inversion Hcfg as [? ? ? ? ? ? U ? Hin Hheap Hstack Hframes Hcontrol]; subst.
  assert (Hwrite : ty_var mode G objctx_empty e w (typ_mut_marker typ_bot)).
  {
    unfold obj_typing in Hcontrol.
    clear -Hcontrol Hmut.
    remember (trm_write (avar_f w) f a0) as t eqn:Ht in Hcontrol.
    induction Hcontrol; try discriminate; auto.
    inversion Ht; subst. exact (H1 Hmut).
  }
  destruct Hheap as [Hok [_ [_ [_ [_ [_ [Hcorr _]]]]]]].
  assert (Hinc : mode_incap' mode = mode_incap_nocap)
    by (destruct mode; cbn in *; congruence).
  exact (@reference_with_readonly_bound_cannot_write mode G e w R B
    Hmut Hinc Hin Hok Hcorr Href (ex_intro _ q Hbound) Hwrite).
Qed.

Local Lemma readonly_receiver_preserves_readonly_bound mode G e w R B TC q :
  ctx_binds w (typ_objref R (typ_mut_marker B)) G ->
  capability_shape mode G e typ_top (open q B) ->
  capability_shape mode G e typ_top
    (open q (typ_or TC (typ_sel (avar_f w) (typ_label_refcap typ_refcap_mutability) (avar_b 0)))).
Proof.
  intros Hb Hcap.
  change (capability_shape mode G e typ_top
    (typ_or (open q TC) (typ_sel (avar_f w) (typ_label_refcap typ_refcap_mutability) (open q (avar_b 0))))).
  rewrite (open_avar_equal 0 q).
  apply capability_shape_or_right.
  eapply capability_shape_selection; [|exact Hcap].
  exists (typ_objref R (typ_mut_marker B)).
  eapply pf_and2, pf_bind. exact Hb.
Qed.

Local Lemma readonly_field_capability_bound mode G e S TC :
  mode_has_mutability mode -> mode_incap' mode = mode_incap_nocap ->
  @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  ty_capbnd mode typ_refcap_mutability G objctx_empty e S TC ->
  forall B, (forall q, capability_shape mode G e typ_top (open q B)) ->
  capability_shape mode G e B S ->
  forall q, capability_shape mode G e typ_top (open q TC).
Proof.
  intros Hmut Hinc Hin Hok Hcorr Hcap.
  induction Hcap; intros Anchor Hreadonly Hshape q; try solve [apply capability_shape_top].
  - inversion Hshape.
  - inversion Hshape; subst.
    match goal with HD : capability_declaration _ _ _ _ _ |- _ =>
      exact (capability_shape_preserved_by_tight_subtyping (proj2 HD q)
        Hmut Hin Hok Hcorr (Hreadonly q))
    end.
  - inversion Hshape; subst.
    match goal with
    | Hm : precise_member G x (dec_typ _ ?low ?high),
      Hhi : capability_shape mode G e Anchor (open y ?high) |- _ =>
      assert (Hlookup : ty_trm_t mode G e x (typ_rcd (dec_typ B S T)))
        by (eapply (proj1 (inert_judgments_admit_precise_selections mode Hmut Hinc));
            unfold obj_typing in *; eassumption);
      destruct (narrow_type_member_bounds Hmut Hin Hok Hcorr Hlookup)
        as [U1 [U2 [HU [_ Hsub]]]];
      pose proof (proj2 (@precise_type_member_unique mode G x _ _ _ _ _
                     Hmut Hin HU Hm)) as Heq; subst U2;
      apply (IHHcap Anchor Hreadonly);
      exact (capability_shape_preserved_by_tight_subtyping (Hsub y)
        Hmut Hin Hok Hcorr Hhi)
    end.
  - inversion Hshape; subst.
    cbn [open_rec TypOpenable open_rec_typ]. apply capability_shape_and; eauto.
  - inversion Hshape; subst;
      cbn [open_rec TypOpenable open_rec_typ];
      eauto using capability_shape_or_left, capability_shape_or_right.
Qed.

Local Lemma readonly_field_of_stored_reference mode G e w R B S U TC :
  mode_has_mutability mode -> mode_incap' mode = mode_incap_nocap ->
  @inert mode G -> ctx_ok G -> @renv_corr mode G e ->
  ctx_binds w (typ_objref R (typ_mut_marker B)) G ->
  (forall q, capability_shape mode G e typ_top (open q B)) ->
  ty_var mode G objctx_empty e w S ->
  subtyp mode G objctx_empty e S U ->
  ty_capbnd mode typ_refcap_mutability G objctx_empty e U TC ->
  forall q, capability_shape mode G e typ_top (open q TC).
Proof.
  intros Hmut Hinc Hin Hok Hcorr Hb Hreadonly Hstored Hsub Hcap.
  assert (Hvisible : ty_var mode G objctx_empty e w U).
  { eapply ty_var_sub; unfold obj_typing, subtyping; eassumption. }
  pose proof ((proj1 (inert_judgments_admit_precise_selections mode Hmut Hinc))
    _ _ _ _ _ Hvisible Hin Hok Hcorr) as Htight.
  pose proof (tight_typing_tracks_binding_capability Hmut Hin Hok Hcorr Hb Htight) as Hshape.
  eapply readonly_field_capability_bound; eassumption.
Qed.

Local Lemma precise_members_extend_context G G' x D :
  ctx_extends G G' -> precise_member G x D -> precise_member G' x D.
Proof.
  intros [Hb Hv] [T Hflow]. exists T.
  induction Hflow; eauto using precise_flow.
Qed.

Local Lemma readonly_capability_shapes_survive_extension mode G G' e e' T :
  mode_has_mutability mode -> mode_incap' mode = mode_incap_nocap ->
  @inert mode G -> @inert mode G' -> ctx_ok G' -> @renv_corr mode G' e' ->
  ctx_extends G G' -> preserves_bindings e e' ->
  capability_shape mode G e typ_top T ->
  capability_shape mode G' e' typ_top T.
Proof.
  intros Hmut Hinc Hin Hin' Hok Hcorr Hctx Henv Hshape.
  assert (Hsub : forall S U, subtyp_t mode G e S U -> subtyp_t mode G' e' S U).
  {
    intros S U HS.
    eapply (proj1 (proj2 (inert_judgments_admit_precise_selections mode Hmut Hinc)));
      [|eassumption..].
    eapply (proj1 (proj2 (types_under_renv_extension mode))); [|exact Henv].
    eapply (proj1 (proj2 (ctx_extends_types mode))); [|exact Hctx].
    eapply tight_subtyping_in_inert_context; eassumption.
  }
  induction Hshape.
  - apply capability_shape_top.
  - apply capability_shape_nocap. intros _ [_ Hcontra].
    destruct (var_fresh (\{} : vars)) as [q _].
    apply (@inert_top_is_not_below_bottom mode G' e' Hmut Hinc Hin' Hok Hcorr).
    eapply tight_subtyping_in_inert_context; [exact (Hcontra q) | assumption..].
  - now apply capability_shape_and.
  - now apply capability_shape_or_left.
  - now apply capability_shape_or_right.
  - apply capability_shape_record.
    destruct D as [[a | m] S U | | ]; try exact I.
    destruct H as [Hlo Hhi]. split; intro w; apply Hsub; auto.
  - apply capability_shape_fun.
  - apply capability_shape_binder.
  - eapply capability_shape_selection; [|eassumption].
    eapply precise_members_extend_context; eassumption.
Qed.

Local Lemma mutable_mode_has_heap_successors typing_mode :
  mode_has_sef typing_mode ->
  mode_has_mutability typing_mode ->
  typed_heap_successors typing_mode.
Proof.
  intros Hms Hmm.
  apply (mutable_heap_successors_from_members Hmm).
  1: {
    intros G h e fs Lv w a T Htype.
    assert (Hcapmode : mode_incap' typing_mode = mode_incap_nocap)
      by (destruct typing_mode; cbn in *; congruence).
    assert (HNM : mode_has_top_nm_subtype typing_mode)
      by (destruct typing_mode; cbn in *; congruence).
    destruct (read_continuation_has_scoped_view Hmm Htype)
      as [W [U [TS [TC [Hproject [Hstrip [Hcap [Hstack [Hcl Hfv]]]]]]]]].
    exact (@read_step_from_scoped_view typing_mode G e h fs Lv w a T W U TS TC
      Hmm Hcapmode HNM Htype Hproject Hstrip Hcap Hstack Hcl Hfv).
  }
  1: {
    intros G h e fs Lv w p a T Htype.
    destruct (heap_lookup_transport Hmm Htype (tfree_trm_write_l w (avar_f p) a))
      as [y [ds [Href [Hobj _]]]].
    destruct (heap_lookup_transport Hmm Htype (tfree_trm_write_r (avar_f w) p a))
      as [loc [obj [Hparam _]]].
    inversion Htype as [? ? ? ? ? ? U ? Hin Hheap Hinput _ Hcontrol]; subst.
    destruct (object_location_has_nominal_record Hmm Hin Hheap Hobj)
      as [R [P [Hloc _]]].
    unfold obj_typing in Hcontrol.
    destruct (invert_typed_write Hcontrol)
      as [W [V [Hprojection [Hargument Houtput]]]].
    assert (Hcapmode : mode_incap' typing_mode = mode_incap_nocap)
      by (destruct typing_mode; cbn in *; congruence).
    destruct (@field_view_of_heap_location typing_mode G e h w y R typ_bot a W V
      Hmm Hcapmode Hin Hheap Href (forget_kind_of_binding Hloc) Hprojection)
      as [S [Hmember [Hwrite Hread]]].
    assert (Hvalue : ty_var typing_mode G objctx_empty e p S).
    { eapply ty_var_sub; unfold obj_typing, subtyping; eassumption. }
    assert (Hstack : @ty_stack typing_mode G e S fs T).
    {
      eapply stack_narrow_input; [exact Hinput |].
      eapply subtyp_trans; unfold subtyping; eassumption.
    }
    destruct (@write_step_for_nominal_field typing_mode G e h Lv fs w p a y loc ds
      R (typ_mut_marker typ_bot) S S T Hcapmode Htype Href Hobj
      (forget_kind_of_binding Hloc) Hparam Hmember Hvalue Hvalue Hstack)
      as [C' [Hstep Hnext]].
    exists G, C'. auto.
  }
  1: {
    intros G h e fs Lv w p m T Htype.
    destruct (heap_lookup_transport Hmm Htype (tfree_trm_call_l w (avar_f p) m))
      as [y [ds [Href [Hobj _]]]].
    inversion Htype as [? ? ? ? ? ? U ? Hin Hheap Hinput _ Hcontrol]; subst.
    destruct (object_location_has_nominal_record Hmm Hin Hheap Hobj)
      as [R [P [Hloc Hdefs]]].
    unfold obj_typing in Hcontrol.
    destruct (invert_typed_call Hcontrol)
      as [C [Z [V [Hprojection [Hargument [Hind [Hrecv Houtput]]]]]]].
    assert (Hcapmode : mode_incap' typing_mode = mode_incap_nocap)
      by (destruct typing_mode; cbn in *; congruence).
    destruct (@method_view_of_heap_location typing_mode G e h w y R typ_bot m C Z V
      Hmm Hcapmode Hin Hheap Href (forget_kind_of_binding Hloc) Hprojection)
      as [TC [TZ [TR [Hmember [Hparameter [HindReceiv [L [Hreceiver Hresult]]]]]]]].
    assert (Hok : ok e) by (destruct Hheap as [_ [_ [_ [Hok _]]]]; exact Hok).
    assert (HvisW : ctx_vis G w) by
      (eapply active_operand_visible; [exact Htype | apply tfree_trm_call_l]).
    assert (HvisP : ctx_vis G p) by
      (eapply active_operand_visible; [exact Htype | apply tfree_trm_call_r]).
    assert (Hp : ty_var typing_mode G objctx_empty e p TZ).
    { eapply ty_var_sub; unfold obj_typing, subtyping; eassumption. }
    assert (Hw : ty_var typing_mode G objctx_empty e w (open p TC)).
    {
      exact (@instantiate_call_receiver_constraint typing_mode G e L w p Z C TC
        Hok HvisP Hargument Hreceiver Hrecv).
    }
    assert (Hstack : @ty_stack typing_mode G e (open_met p w TR) fs T).
    {
      eapply stack_narrow_input; [exact Hinput |].
      eapply subtyp_trans; unfold subtyping; [|exact Houtput].
      exact (@instantiate_call_result_subtyping typing_mode G e L w p Z C TR V
        Hok HvisP HvisW Hargument Hrecv Hresult).
    }
    assert (Hself : ty_var typing_mode G objctx_empty e w
      (typ_and (open p TC) (typ_and (open y R) (open w R)))).
    {
      apply ty_var_and; unfold obj_typing; [exact Hw |].
      exact (@open_types_of_nominal_receiver typing_mode G e h w y R P Hin Hheap Href Hloc).
    }
    destruct (@call_step_for_nominal_record typing_mode G e h Lv fs w p m y ds
      R TC TZ TR T Hmm Htype Href Hobj Hdefs Hmember Hp Hself Hstack)
      as [C' [Hstep Hnext]].
    exists G, C'. auto.
  }
Qed.

Section WithTypingMode.

Context (typing_mode: Mode).

Context (Hms : mode_has_sef typing_mode).

Context (Hmm : mode_has_mutability typing_mode).

Theorem swap_calls_transformation_guarantee ta tb Ta Tb:
  〈ctx_empty⁏empty ⊢ ta ∶ Ta〉 ∼(trf_local_idtyp_trm typing_mode (trf_swap_calls_local typing_mode))∼> 〈ctx_empty⁏empty ⊢ tb ∶ Tb〉 ->
  closed ta ->
  closed tb ->
  closed Ta ->
  closed Tb ->

  exists Ca Cb,
    config_initial ta Ca /\
    config_initial tb Cb /\
    (
      ( exists  na nb Ga2 Gb2 Ca2 Cb2,

        nb <= na /\

        ctx_empty ⊢ Ca ∶ Ta ⊣na↦* Ga2 ⊢ Ca2 /\
        ctx_empty ⊢ Cb ∶ Tb ⊣nb↦* Gb2 ⊢ Cb2 /\
        answer Ca2 /\
        answer Cb2 /\

        〈Ga2 ⊢ Ca2 ∶ Ta〉 ∼(trf_lift_sim_conf typing_mode (trf_swap_calls_local typing_mode))∼> 〈Gb2 ⊢ Cb2 ∶ Tb〉
      ) \/ (
         forall (n : nat),
         exists (Ca2 Cb2 : config),
           Ca ⊣n↦* Ca2 /\
           Cb ⊣n↦* Cb2
      )
    ).

Proof.
  intros Hswap HclosedA HclosedB HtypeA HtypeB.
  assert (Ta = Tb) by (inversion Hswap; reflexivity).
  subst Tb.
  destruct (swap_calls_initial_related Hswap HclosedA HclosedB HtypeA)
    as [Ca [Cb [HinitialA [HinitialB [HtypingA [HtypingB Hrelated]]]]]].
  exists Ca, Cb. split; [exact HinitialA |]. split; [exact HinitialB |].
  eapply swap_calls_guarantee_for_related_typable_configurations;
    [|exact Hrelated|exact HtypingB| |].
  2,3: eapply raw_prefixes_from_typed_successors;
    eauto using mutable_mode_has_heap_successors.

End WithTypingMode.
