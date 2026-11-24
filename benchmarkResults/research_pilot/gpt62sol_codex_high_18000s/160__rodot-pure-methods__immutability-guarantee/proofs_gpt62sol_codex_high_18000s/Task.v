Set Implicit Arguments.

Require Import LibExtra AbstractSyntax GeneralTyping ConfigTyping.
Require Import OperationalSemantics MutableReachability.
Require Import HeapUpdate HeapCorrespondence InertContext TFree ConfigNotations.
Require Import ConfigVarkinds EnvCorrespondence RecordTypes.
Require Import Equivalence Indep Deref.
From Stdlib Require Import Lia Program.Equality.

Section WithRodotMode.
Context (typing_mode: Mode).
Context (Hmm: mode_has_mutability typing_mode).

(* Execution only needs the context annotations to have fresh free names.
   Capability bounds may retain bound indices in intermediate annotations. *)
Inductive execution_config : ctx -> config -> typ -> Prop :=
| execution_config_intro : forall G e s Sigma Lv t T U,
    inert G ->
    heap_correspond G e Sigma ->
    ty_stack G e T s U ->
    all_tfree_k_stack G s v_ref ->
    G ⁏ e ⊢ t ∶ T ->
    all_tfree_k G t v_ref ->
    ty_nothing_fresh_in_config G U (t ; s ; Sigma ; e ; Lv) ->
    has_null Lv ->
    config_closed (t ; s ; Sigma ; e ; Lv) ->
    closed U ->
    execution_config G (t ; s ; Sigma ; e ; Lv) U.

Local Lemma typed_config_supports_execution F C T :
    ty_config F C T -> execution_config F C T.
Proof. intros H. inversion H; subst. econstructor; eassumption. Qed.

Local Lemma reachability_move_roots F t s t' s' S e Lv Lv' y :
    (forall w, tfree w t' \/ tfree w s' -> tfree w t \/ tfree w s) ->
    F ⊢ (t' ; s' ; S ; e ; Lv') mreach y ->
    F ⊢ (t ; s ; S ; e ; Lv) mreach y.
Proof.
  intros Hroots Hr.
  change (mut_reach typing_mode F
            (t' ; s' ; S ; e ; Lv') y) in Hr.
  remember (t' ; s' ; S ; e ; Lv') as C' eqn:Heq.
  induction Hr; inversion Heq; subst.
  - eapply mreach_fld; eauto.
  - eapply mreach_trm; eauto.
Qed.

Local Lemma reachability_let_push F t u s S e Lv Lv' y :
    F ⊢ (t ; stack_cons (frame_let u) s ; S ; e ; Lv') mreach y ->
    F ⊢ (trm_let t u ; s ; S ; e ; Lv) mreach y.
Proof.
  apply reachability_move_roots.
  intros w [Ht | Hs].
  - left. apply tfree_trm_let_l. exact Ht.
  - change (tfree_stack w (stack_cons (frame_let u) s)) in Hs.
    inversion Hs; subst.
    + left. apply tfree_trm_let_r. assumption.
    + right. assumption.
Qed.

Local Lemma open_avar_free a k x w :
    open_rec k x a = avar_f w -> a = avar_f w \/ w = x.
Proof.
  destruct a as [i | z].
  - change ((If k = i then avar_f x else avar_b i) = avar_f w ->
            avar_b i = avar_f w \/ w = x).
    destruct (Nat.eq_dec k i) as [Heq | Hneq].
    + rewrite If_l by exact Heq. intros H. injection H as ->. now right.
    + rewrite If_r by exact Hneq. discriminate.
  - intros H. now left.
Qed.

Local Lemma tfree_opened_mutual :
    (forall t : trm, forall k x w,
      tfree w (open_rec k x t) -> tfree w t \/ w = x) /\
    (forall l : lit, forall k x w,
      tfree w (open_rec k x l) -> tfree w l \/ w = x) /\
    (forall d : def, forall k x w,
      tfree w (open_rec k x d) -> tfree w d \/ w = x) /\
    (forall ds : defs, forall k x w,
      tfree w (open_rec k x ds) -> tfree w ds \/ w = x).
Proof.
  apply trm_mutind; intros;
    match goal with
    | H : tfree _ (open_rec _ _ _) |- _ => inversion H; subst; clear H
    end.
  all: try match goal with
    | H : avar_f _ = open_rec _ _ _ |- _ =>
        symmetry in H; apply open_avar_free in H as [-> | ->];
        [left; constructor | now right]
    end.
  all: match goal with
    | IH : forall k x w, tfree w (open_rec k x ?a) -> _,
      H : _ ?w (?op ?k ?x ?a) |- _ =>
        destruct (IH k x w H) as [Hfree | ->];
        [left; solve [constructor; exact Hfree] | now right]
    end.
Qed.

Local Lemma reachability_let_pop F x t s S e Lv Lv' y :
    F ⊢ (open x t ; s ; S ; e ; Lv') mreach y ->
    F ⊢ (trm_var (avar_f x) ; stack_cons (frame_let t) s ; S ; e ; Lv) mreach y.
Proof.
  apply reachability_move_roots.
  intros w [Ht | Hs].
  - destruct (proj1 tfree_opened_mutual t 0 x w Ht) as [Ht' | ->].
    + right. apply tfree_stack_cons_l. exact Ht'.
    + left. apply tfree_trm_var.
  - right. apply tfree_stack_cons_r. exact Hs.
Qed.

Local Hint Constructors tfree_trm tfree_lit tfree_def tfree_defs : term_free.

Local Lemma tfree_stays_open :
    (forall w t, tfree_trm w t -> forall k x, tfree w (open_rec k x t)) /\
    (forall w l, tfree_lit w l -> forall k x, tfree w (open_rec k x l)) /\
    (forall w d, tfree_def w d -> forall k x, tfree w (open_rec k x d)) /\
    (forall w ds, tfree_defs w ds -> forall k x, tfree w (open_rec k x ds)).
Proof.
  apply tfree_mutind; intros;
    cbn [open_rec TrmOpenable LitOpenable DefOpenable DefsOpenable
      open_rec_trm open_rec_lit open_rec_def open_rec_defs AvarOpenable];
    unfold tfree in *; eauto with term_free.
Qed.

Local Lemma term_free_stays_open w (t : trm) k x :
    tfree w t -> tfree w (open_rec k x t).
Proof. intros H. exact (proj1 tfree_stays_open w t H k x). Qed.

Local Lemma visibility_of_mutable_mode :
    mode_has_visibility typing_mode.
Proof. destruct typing_mode; simpl in *; discriminate || reflexivity. Qed.

Local Lemma ctx_vis_pop G x k T w :
    x <> w -> ctx_vis (G § x / k ~ T) w -> ctx_vis G w.
Proof. intros Hneq Hvis. inversion Hvis; subst; congruence. Qed.

Local Lemma fresh_except (L : vars) (w : var) :
    exists x, x \notin L /\ x <> w.
Proof.
  destruct (var_fresh (L \u \{w})) as [x Hx].
  rewrite notin_union in Hx.
  destruct Hx as [HL Hw].
  exists x. split; [exact HL |].
  intros ->. apply Hw. rewrite in_singleton. reflexivity.
Qed.

Local Lemma typed_free_visible :
    (forall G Go e t T, ty_trm typing_mode G Go e t T ->
      forall w, tfree w t -> ctx_vis G w) /\
    (forall G Go e l T, ty_lit typing_mode G Go e l T ->
      forall w, tfree w l -> ctx_vis G w) /\
    (forall G Go e d D, ty_def typing_mode G Go e d D ->
      forall w, tfree w d -> ctx_vis (G §§& Go) w) /\
    (forall G Go e ds T, ty_defs typing_mode G Go e ds T ->
      forall w, tfree w ds -> ctx_vis (G §§& Go) w).
Proof.
  apply rules_mutind; intros.
  all: try match goal with
    | H : tfree _ ?a |- _ => is_var a; solve [eauto]
    | H : tfree _ _ |- _ =>
        solve [inversion H; subst; eauto using visibility_of_mutable_mode]
    end.
  all: try match goal with
    | H : tfree _ _ |- _ => inversion H; subst; clear H
    end.
  all: try solve [eauto using visibility_of_mutable_mode].
  all: try solve [match goal with
    | IH : forall x, x \notin ?L -> forall w, tfree w (open_rec 0 x ?b) -> _,
      H : tfree_trm ?w ?b |- ctx_vis ?G ?w =>
        let x := fresh "x" in let Hx := fresh "Hx" in let Hneq := fresh "Hneq" in
        destruct (fresh_except L w) as [x [Hx Hneq]];
        eapply ctx_vis_pop; [exact Hneq |];
        exact (IH x Hx w (@term_free_stays_open w b 0 x H))
    end].
  - match goal with
    | IH : forall x, x \notin ?L -> forall w, tfree w (open_rec 0 x ?b) -> _,
      H : _ ?w ?b |- ctx_vis ?G ?w =>
        destruct (fresh_except L w) as [x [Hx Hneq]];
        exact (ctx_vis_pop Hneq
          (IH x Hx w (proj2 (proj2 (proj2 tfree_stays_open)) w b H 0 x)))
    end.
  - match goal with
    | IH : forall xz, xz \notin ?L -> forall xc, xc <> xz ->
           xc \notin ?L -> forall w, tfree w _ -> _,
      H : tfree_trm ?w ?b |- _ =>
        destruct (fresh_except L w) as [xz [Hz Hzw]];
        destruct (fresh_except (L \u \{xz}) w) as [xc [Hc Hcw]];
        rewrite notin_union in Hc;
        destruct Hc as [Hc Hcz];
        rewrite notin_singleton in Hcz;
        pose proof (IH xz Hz xc Hcz Hc w
          (@term_free_stays_open w _ 0 xz
            (@term_free_stays_open w _ 1 xc H))) as Hvis;
        unfold ctx_obj_met in Hvis;
        rewrite visibility_of_mutable_mode in Hvis;
        destruct Go; simpl in Hvis;
        apply (ctx_vis_pop Hcw) in Hvis;
        apply (ctx_vis_pop Hzw) in Hvis;
        inversion Hvis
    end.
  - match goal with H : tfree_defs _ defs_nil |- _ => inversion H end.
Qed.

Local Lemma typed_method_free G Go e m t D w :
    G §§ Go ⁏ e ⊢ def_met m t ∶d D ->
    ~ tfree w t.
Proof.
  intros Hty Hfree.
  inversion Hty; subst.
  match goal with
  | Hbody : forall z, z \notin ?L -> forall c, c <> z ->
        c \notin ?L -> _ |- _ =>
      destruct (fresh_except L w) as [z [Hz Hzw]];
      destruct (fresh_except (L \u \{z}) w) as [c [Hc Hcw]];
      rewrite notin_union in Hc;
      destruct Hc as [Hc Hcz];
      rewrite notin_singleton in Hcz;
      pose proof (proj1 typed_free_visible _ _ _ _ _ (Hbody z Hz c Hcz Hc) w
        (@term_free_stays_open w _ 0 z
          (@term_free_stays_open w t 1 c Hfree))) as Hvis
  end.
  unfold ctx_obj_met in Hvis.
  rewrite visibility_of_mutable_mode in Hvis.
  destruct Go; simpl in Hvis;
    apply (ctx_vis_pop Hcw) in Hvis;
    apply (ctx_vis_pop Hzw) in Hvis;
    inversion Hvis.
Qed.

Local Lemma typed_defs_member_record G Go e ds T :
    G §§ Go ⁏ e ⊢ ds ∶ T ->
    forall d, defs_has ds d ->
    exists D, record_has T D /\ G §§ Go ⁏ e ⊢ d ∶d D.
Proof.
  intros Hty. induction Hty; intros member Hhas.
  - unfold defs_has in Hhas. simpl get_def in Hhas.
    destruct (classic (label_of d = label_of member)) as [Heq | Hneq].
    + rewrite If_l in Hhas by exact Heq. inversion Hhas; subst.
      eexists. split; [apply rh_one | eassumption].
    + rewrite If_r in Hhas by exact Hneq. discriminate.
  - unfold defs_has in Hhas. simpl get_def in Hhas.
    destruct (classic (label_of d = label_of member)) as [Heq | Hneq].
    + rewrite If_l in Hhas by exact Heq. inversion Hhas; subst.
      eexists. split; [apply rh_andr, rh_one | eassumption].
    + rewrite If_r in Hhas by exact Hneq.
      destruct (IHHty member Hhas) as [D' [Hmember Hty']].
      exists D'. split; [now apply rh_andl | exact Hty'].
Qed.

Local Lemma typed_defs_member G Go e ds T :
    G §§ Go ⁏ e ⊢ ds ∶ T ->
    forall d, defs_has ds d -> exists D, G §§ Go ⁏ e ⊢ d ∶d D.
Proof.
  intros Hty d Hhas.
  destruct (typed_defs_member_record Hty Hhas) as [D [_ HD]].
  now exists D.
Qed.

Local Lemma heap_method_free F C T y ds m t w :
    execution_config F C T ->
    binds y (item_obj ds) (config_heap C) ->
    defs_has ds (def_met m t) ->
    ~ tfree w t.
Proof.
  intros Hcfg Hbind Hhas.
  inversion Hcfg; subst; simpl in Hbind.
  match goal with H : heap_correspond _ _ _ |- _ =>
    destruct H as (_ & _ & _ & _ & _ & _ & _ & Hitems)
  end.
  assert (Hin : y \in dom Sigma).
  { destruct (classic (y \in dom Sigma)) as [Hmem | Hmem]; [exact Hmem |].
    exfalso. exact (binds_fresh_inv Hbind Hmem). }
  specialize (Hitems y Hin). inversion Hitems; subst.
  - match goal with H : binds y (item_fun _) Sigma |- _ =>
      discriminate (binds_functional Hbind H)
    end.
  - match goal with H : binds y (item_obj _) Sigma |- _ =>
      let Heq := fresh "Heq" in
      pose proof (binds_functional Hbind H) as Heq; inversion Heq; subst
    end.
    destruct (typed_defs_member ltac:(eassumption) Hhas) as [D Hdef].
    eapply typed_method_free; exact Hdef.
Qed.

Local Lemma reachability_call F s S e Lv Lv' wObj wArg m t T yObj ds y :
    execution_config F (trm_call (avar_f wObj) m (avar_f wArg) ; s ; S ; e ; Lv) T ->
    binds yObj (item_obj ds) S ->
    defs_has ds (def_met m t) ->
    F ⊢ (open wArg (open_rec 1 wObj t) ; s ; S ; e ; Lv') mreach y ->
    F ⊢ (trm_call (avar_f wObj) m (avar_f wArg) ; s ; S ; e ; Lv) mreach y.
Proof.
  intros Hcfg Hbind Hhas. apply reachability_move_roots.
  intros w [Ht | Hs]; [left | now right].
  destruct (proj1 tfree_opened_mutual (open_rec 1 wObj t) 0 wArg w Ht)
    as [Ht' | ->]; [| apply tfree_trm_call_r].
  destruct (proj1 tfree_opened_mutual t 1 wObj w Ht')
    as [Hfree | ->]; [| apply tfree_trm_call_l].
  exfalso. eapply heap_method_free; eassumption.
Qed.

Local Lemma write_receiver_mutable F e t T w a u :
    F ⁏ e ⊢ t ∶ T ->
    t = trm_write (avar_f w) a (avar_f u) ->
    F ⁏ e ⊢ trm_var (avar_f w) ∶ typ_mut_marker typ_bot.
Proof.
  intros Hty.
  induction Hty; intros Heq; try discriminate.
  - inversion Heq; subst. apply ty_trm_var; auto.
  - auto.
Qed.

Local Lemma write_typing_operands F e t T :
    F ⁏ e ⊢ t ∶ T ->
    forall w a u, t = trm_write (avar_f w) a (avar_f u) ->
    exists A B,
      vis_var typing_mode F u /\
      F ⁏ e ⊢ w ∶ typ_rcd (dec_fld a A B) /\
      F ⁏ e ⊢ u ∶ A /\
      F ⁏ e ⊢ B <: T.
Proof.
  intros Hty. induction Hty; intros w' a' u' Heq; try discriminate.
  - inversion Heq; subst. do 2 eexists. repeat split; eauto using subtyp_refl.
  - destruct (IHHty w' a' u' Heq) as [A [B [Hvis [Hobj [Harg Hsub]]]]].
    exists A, B. repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

Local Lemma variable_term_typing F e t T :
    F ⁏ e ⊢ t ∶ T ->
    forall w, t = trm_var (avar_f w) -> F ⁏ e ⊢ w ∶ T.
Proof.
  intros Hty. induction Hty; intros w Heq; try discriminate.
  - inversion Heq; subst; assumption.
  - eapply ty_var_sub; eauto.
Qed.

Local Lemma fresh_config_keys t s S e Lv x xs :
    fresh_in_config (x :: xs) (t ; s ; S ; e ; Lv) -> x # S /\ x # e.
Proof.
  intros [Hfresh _].
  change (x \notin (fv t \u fv s \u (dom S \u fv_env S)
                    \u fv_renv e \u Lv)) in Hfresh.
  repeat rewrite notin_union in Hfresh.
  tauto.
Qed.

Local Lemma fresh_heap_binding t s S e Lv x xs y i :
    fresh_in_config (x :: xs) (t ; s ; S ; e ; Lv) ->
    binds y i S ->
    y <> x.
Proof.
  intros Hfresh Hbind ->.
  exact (binds_fresh_inv Hbind (proj1 (fresh_config_keys Hfresh))).
Qed.

Local Lemma mode_disallows_functions :
    mode_has_fun' typing_mode = false.
Proof. destruct typing_mode; simpl in *; discriminate || reflexivity. Qed.

Local Lemma heap_function_impossible F C T y t :
    execution_config F C T -> binds y (item_fun t) (config_heap C) -> False.
Proof.
  intros Hcfg Hbind.
  inversion Hcfg; subst; simpl in Hbind.
  match goal with H : heap_correspond _ _ _ |- _ =>
    destruct H as (_ & _ & _ & _ & _ & _ & _ & Hitems)
  end.
  assert (Hin : y \in dom Sigma).
  { destruct (classic (y \in dom Sigma)) as [Hmem | Hmem]; [exact Hmem |].
    exfalso. exact (binds_fresh_inv Hbind Hmem). }
  specialize (Hitems y Hin). inversion Hitems; subst.
  - pose proof mode_disallows_functions. congruence.
  - match goal with H : binds y (item_obj _) Sigma |- _ =>
      discriminate (binds_functional Hbind H)
    end.
Qed.

Local Definition includes_bindings (G G' : ctx) :=
  forall x T, ctx_binds x T G -> ctx_binds x T G'.

Local Lemma includes_bindings_push G G' x k T :
    includes_bindings G G' ->
    includes_bindings (G § x / k ~ T) (G' § x / k ~ T).
Proof.
  intros Hinc y U Hbind. inversion Hbind; subst.
  - apply ctx_binds_e.
  - apply ctx_binds_n; auto.
Qed.

Local Hint Constructors ty_var subtyp ty_incap : core_typing.
Local Hint Resolve includes_bindings_push : core_typing.

Local Lemma weaken_core_typing :
    (forall G Go e x T, ty_var typing_mode G Go e x T ->
      forall G', includes_bindings G G' -> ty_var typing_mode G' Go e x T) /\
    (forall G Go e S T, subtyp typing_mode G Go e S T ->
      forall G', includes_bindings G G' -> subtyp typing_mode G' Go e S T) /\
    (forall G Go e S T, ty_incap typing_mode G Go e S T ->
      forall G', includes_bindings G G' -> ty_incap typing_mode G' Go e S T).
Proof.
  apply ts_mutind; intros.
  all: fold (@obj_typing var (ty_var typing_mode)) in *;
       fold (@subtyping (subtyp typing_mode)) in *;
       fold (@obj_ref_incap (ty_incap typing_mode)) in *.
  all: try solve [eauto 4 with core_typing].
  - eapply subtyp_fun; [assumption | eauto | intros].
    eauto using includes_bindings_push.
  - eapply subtyp_met; [eauto | intros | assumption | intros];
      eauto using includes_bindings_push.
Qed.

Local Lemma context_binding_in_domain G x T :
    ctx_binds x T G -> x \in ctx_dom G.
Proof.
  intros Hbind. induction Hbind; simpl ctx_dom.
  - rewrite in_union, in_singleton. now left.
  - rewrite in_union. now right.
  - assumption.
Qed.

Local Lemma kind_binding_gives_binding G G' x k T :
    ctx_binds_k_after x k T G G' -> ctx_binds x T G.
Proof.
  intros H. induction H.
  - apply ctx_binds_e.
  - now apply ctx_binds_n.
Qed.

Local Lemma earlier_kind_binding G G' G'' x k T y l U :
    ctx_binds_k_after x k T G G' ->
    ctx_ok G ->
    ctx_binds_k_after y l U G' G'' ->
    ctx_binds_k_after y l U G G''.
Proof.
  intros Hafter. induction Hafter; intros Hok Hbind; inversion Hok; subst.
  - apply ctx_binds_k_n; [| exact Hbind].
    intros ->. eapply H4.
    eapply context_binding_in_domain, kind_binding_gives_binding; exact Hbind.
  - specialize (IHHafter ltac:(assumption) Hbind).
    apply ctx_binds_k_n; [| exact IHHafter].
    intros ->. eapply H5.
    eapply context_binding_in_domain, kind_binding_gives_binding; exact IHHafter.
Qed.

Local Lemma reference_binding_types G e w y :
    ctx_ok G ->
    renv_corr G e ->
    binds w y e ->
    exists Tw Ty Gw Gy,
      ctx_binds_k_after w v_ref Tw G Gw /\
      ctx_binds_k_after y v_loc Ty G Gy /\
      typ_corr Tw Ty.
Proof.
  intros Hok Henv. induction Henv; intros Hbind.
  - exfalso. eapply binds_empty_inv; eassumption.
  - apply binds_push_inv in Hbind as [[-> ->] | [Hneq Hbind]].
    + do 4 eexists. split; [eassumption |]. split; [|eassumption].
      eapply earlier_kind_binding; eassumption.
    + now apply IHHenv.
Qed.

Local Lemma reference_location_annotations G e w y :
    ctx_ok G ->
    renv_corr G e ->
    binds w y e ->
    exists U B Gw Gy,
      ctx_binds_k_after w v_ref (typ_objref U (typ_mut_marker B)) G Gw /\
      ctx_binds_k_after y v_loc (typ_objref U (typ_mut_marker typ_bot)) G Gy.
Proof.
  intros Hok Henv Hbind.
  destruct (reference_binding_types Hok Henv Hbind)
    as [Tw [Ty [Gw [Gy [Hw [Hy Hcorr]]]]]].
  inversion Hcorr; subst.
  - assert (Hmode : mode_refcap_corr' typing_mode = mode_refcap_corr_ref_mutability).
    { destruct typing_mode; simpl in *; discriminate || reflexivity. }
    match goal with H : (match mode_refcap_corr' typing_mode with _ => _ end) |- _ =>
      rewrite Hmode in H; destruct H as [B [-> ->]]
    end.
    do 4 eexists. split; eassumption.
  - pose proof mode_disallows_functions. congruence.
Qed.

Local Lemma fresh_context_extension G x k T :
    x §# G -> includes_bindings G (G § x / k ~ T).
Proof.
  intros Hfresh y U Hbind. apply ctx_binds_n; [| exact Hbind].
  intros ->. apply Hfresh. eapply context_binding_in_domain; eassumption.
Qed.

Local Definition typing_respects_bindings G G' e :=
  forall x T, ctx_binds x T G -> G' ⁏ e ⊢ x ∶ T.

Local Lemma typing_respects_bindings_push G G' e x k T :
    x §# G' ->
    typing_respects_bindings G G' e ->
    typing_respects_bindings (G § x / k ~ T) (G' § x / k ~ T) e.
Proof.
  intros Hfresh Hres y U Hbind. inversion Hbind; subst.
  - apply ty_var_var. apply ctx_binds_e.
  - apply (proj1 weaken_core_typing G' objctx_empty e y U).
    + eapply Hres; eassumption.
    + now apply fresh_context_extension.
Qed.

Local Hint Resolve typing_respects_bindings_push : core_typing.

Local Lemma replace_core_bindings :
    (forall G Go e x T, ty_var typing_mode G Go e x T ->
      forall G', typing_respects_bindings G G' e -> ty_var typing_mode G' Go e x T) /\
    (forall G Go e S T, subtyp typing_mode G Go e S T ->
      forall G', typing_respects_bindings G G' e -> subtyp typing_mode G' Go e S T) /\
    (forall G Go e S T, ty_incap typing_mode G Go e S T ->
      forall G', typing_respects_bindings G G' e -> ty_incap typing_mode G' Go e S T).
Proof.
  apply ts_mutind; intros.
  all: fold (@obj_typing var (ty_var typing_mode)) in *;
       fold (@subtyping (subtyp typing_mode)) in *;
       fold (@obj_ref_incap (ty_incap typing_mode)) in *.
  all: try solve [eauto 4 with core_typing].
  - eapply subtyp_fun with (L := L \u ctx_dom G'); [assumption | eauto |].
    intros x Hx. apply notin_union in Hx as [HxL HxG].
    eauto with core_typing.
  - eapply subtyp_met with (L := L \u ctx_dom G'); [eauto | | assumption |].
    + intros x Hx. apply notin_union in Hx as [HxL HxG].
      eauto with core_typing.
    + intros x Hx y Hneq Hy.
      apply notin_union in Hx as [HxL HxG].
      apply notin_union in Hy as [HyL HyG].
      assert (HyG' : y §# (G' § x / v_par ~ TZ2)).
      { simpl ctx_dom. rewrite notin_union, notin_singleton. auto. }
      eauto with core_typing.
Qed.

Local Lemma replace_var_typing G G' e (x : var) T :
    typing_respects_bindings G G' e ->
    G ⁏ e ⊢ x ∶ T ->
    G' ⁏ e ⊢ x ∶ T.
Proof.
  intros Hres Hty. exact (proj1 replace_core_bindings _ _ _ _ _ Hty _ Hres).
Qed.

Local Lemma replace_subtyping G G' e S T :
    typing_respects_bindings G G' e ->
    G ⁏ e ⊢ S <: T ->
    G' ⁏ e ⊢ S <: T.
Proof.
  intros Hres Hty.
  exact (proj1 (proj2 replace_core_bindings) _ _ _ _ _ Hty _ Hres).
Qed.

Local Lemma replace_incap G G' e S T :
    typing_respects_bindings G G' e ->
    G ⁏ e ⊢ S ∶icp T ->
    G' ⁏ e ⊢ S ∶icp T.
Proof.
  intros Hres Hty.
  exact (proj2 (proj2 replace_core_bindings) _ _ _ _ _ Hty _ Hres).
Qed.

Local Hint Resolve replace_var_typing replace_subtyping replace_incap : binding_transport.
Local Hint Constructors ty_capbnd : binding_transport.

Local Lemma replace_capability_bound C G G' e S T :
    typing_respects_bindings G G' e ->
    G ⁏ e ⊢ S ∶cpb⟦C⟧ T ->
    G' ⁏ e ⊢ S ∶cpb⟦C⟧ T.
Proof.
  intros Hres Hty. induction Hty;
    try solve [constructor; eauto].
  eapply ty_capbnd_sel; eauto using replace_var_typing.
Qed.

Local Lemma replace_viewpoint G G' e x S T :
    typing_respects_bindings G G' e ->
    G ⁏ e ⊢ x ▷ S ⟶ T ->
    G' ⁏ e ⊢ x ▷ S ⟶ T.
Proof.
  intros Hres Hty.
  unfold viewpoint_adapt in *.
  destruct (mode_viewpoint_adaptation' typing_mode); [exact Hty |].
  inversion Hty; subst.
  apply viewpoint_adapt_cap_strip_combine;
    eauto using replace_incap, replace_capability_bound.
Qed.

Local Definition typing_context_extends G G' e :=
  typing_respects_bindings G G' e /\
  (forall x, ctx_vis G x -> ctx_vis G' x).

Local Lemma typing_context_extends_push G G' e x k T :
    x §# G' ->
    typing_context_extends G G' e ->
    typing_context_extends (G § x / k ~ T) (G' § x / k ~ T) e.
Proof.
  intros Hfresh [Hbind Hvis]. split.
  - now apply typing_respects_bindings_push.
  - intros y Hlocal. inversion Hlocal; subst.
    + apply ctx_vis_e.
    + apply ctx_vis_n; auto.
Qed.

Local Lemma typing_context_extends_hide G G' e :
    typing_context_extends G G' e ->
    typing_context_extends (ctx_hide G) (ctx_hide G') e.
Proof.
  intros [Hbind Hvis]. split.
  - intros x T Hhidden. inversion Hhidden; subst.
    assert (Hty : G' ⁏ e ⊢ x ∶ T) by (eapply Hbind; eassumption).
    exact (proj1 weaken_core_typing G' objctx_empty e x T Hty (ctx_hide G')
             ltac:(intros y U H; now apply ctx_binds_hide)).
  - intros x H. inversion H.
Qed.

Local Lemma fresh_pushed_context G x k T y :
    y <> x -> y §# G -> y §# (G § x / k ~ T).
Proof.
  intros Hneq Hfresh. simpl ctx_dom.
  rewrite notin_union, notin_singleton. auto.
Qed.

Local Lemma typing_context_extends_method G G' Go e z c TZ TC :
    typing_context_extends (G §§& Go) (G' §§& Go) e ->
    z §# (G' §§& Go) ->
    c §# (G' §§& Go) ->
    c <> z ->
    typing_context_extends (ctx_obj_met typing_mode G Go z TZ c TC)
      (ctx_obj_met typing_mode G' Go z TZ c TC) e.
Proof.
  intros Hres Hz Hc Hneq.
  unfold ctx_obj_met. rewrite visibility_of_mutable_mode.
  destruct Go; simpl in *.
  all: apply typing_context_extends_push;
         [apply fresh_pushed_context; assumption |].
  all: apply typing_context_extends_push;
         [assumption | now apply typing_context_extends_hide].
Qed.

Local Lemma transport_vis G G' e x :
    typing_context_extends G G' e ->
    ctx_vis G x -> ctx_vis G' x.
Proof. intros [_ H]. exact (H x). Qed.

Local Lemma transport_binding_typing G G' e :
    typing_context_extends G G' e ->
    typing_respects_bindings G G' e.
Proof. intros [H _]. exact H. Qed.

Local Hint Resolve transport_vis transport_binding_typing replace_viewpoint
  typing_context_extends_push typing_context_extends_method : binding_transport.
Local Hint Constructors ty_trm ty_lit ty_def ty_defs : binding_transport.

Local Lemma replace_term_bindings :
    (forall G Go e t T, ty_trm typing_mode G Go e t T ->
      forall G', typing_context_extends G G' e ->
        typing_context_extends (G §§& Go) (G' §§& Go) e ->
        ty_trm typing_mode G' Go e t T) /\
    (forall G Go e l T, ty_lit typing_mode G Go e l T ->
      forall G', typing_context_extends G G' e ->
        typing_context_extends (G §§& Go) (G' §§& Go) e ->
        ty_lit typing_mode G' Go e l T) /\
    (forall G Go e d D, ty_def typing_mode G Go e d D ->
      forall G', typing_context_extends G G' e ->
        typing_context_extends (G §§& Go) (G' §§& Go) e ->
        ty_def typing_mode G' Go e d D) /\
    (forall G Go e ds T, ty_defs typing_mode G Go e ds T ->
      forall G', typing_context_extends G G' e ->
        typing_context_extends (G §§& Go) (G' §§& Go) e ->
        ty_defs typing_mode G' Go e ds T).
Proof.
  apply rules_mutind; intros.
  all: fold (@obj_typing trm (ty_trm typing_mode)) in *;
       fold (@obj_typing lit (ty_lit typing_mode)) in *;
       fold (@obj_typing defs (ty_defs typing_mode)) in *;
       fold (@obj_dec_typing def (ty_def typing_mode)) in *.
  all: try solve [eauto 5 with binding_transport].
  - eapply ty_trm_var; [intro |]; eauto with binding_transport.
  - pose proof mode_disallows_functions. congruence.
  - eapply ty_trm_read with (S := S) (T := T); [intro | |];
      eauto with binding_transport.
  - eapply ty_trm_write with (S := S); [intro | intro | intro | |];
      eauto with binding_transport.
  - eapply ty_trm_call with (TC := TC) (TZ := TZ) (TR := TR);
      [intro | intro | | | assumption |]; eauto with binding_transport.
  - eapply ty_trm_let with (L := L \u ctx_dom G'); [eauto |].
    intros x Hx; apply notin_union in Hx as [HxL HxG].
    pose proof (typing_context_extends_push v_let T HxG H1) as Hext.
    exact (H0 x HxL _ Hext Hext).
  - eapply ty_trm_lit with (L := L \u ctx_dom G'); [eauto |].
    intros x Hx; apply notin_union in Hx as [HxL HxG].
    pose proof (typing_context_extends_push v_let T HxG H1) as Hext.
    exact (H0 x HxL _ Hext Hext).
  - pose proof mode_disallows_functions. congruence.
  - eapply ty_lit_obj with (L := L \u ctx_dom G'); [| assumption].
    intros x Hx; apply notin_union in Hx as [HxL HxG].
    exact (H x HxL G' H0
             (typing_context_extends_push v_self (open x T) HxG H0)).
  - eapply ty_def_fld; [intro |]; eauto with binding_transport.
  - eapply ty_def_met with (L := L \u ctx_dom (G' §§& Go)).
    intros z Hz c Hcz Hc.
    apply notin_union in Hz as [HzL HzG].
    apply notin_union in Hc as [HcL HcG].
    pose proof (@typing_context_extends_method G G' Go e z c TZ TC
                 H1 HzG HcG Hcz) as Hext.
    exact (H z HzL c Hcz HcL _ Hext Hext).
Qed.

Local Lemma narrow_last_binding G e x k S T :
    x §# G ->
    G ⁏ e ⊢ S <: T ->
    typing_context_extends (G § x / k ~ T) (G § x / k ~ S) e.
Proof.
  intros Hx Hsub. split.
  - intros y U Hbind. inversion Hbind; subst.
    + eapply ty_var_sub.
      * apply ty_var_var. apply ctx_binds_e.
      * exact (proj1 (proj2 weaken_core_typing) _ _ _ _ _ Hsub _
                 (fresh_context_extension k S Hx)).
    + apply ty_var_var. now apply ctx_binds_n.
  - intros y Hvis. inversion Hvis; subst.
    + apply ctx_vis_e.
    + now apply ctx_vis_n.
Qed.

Local Lemma stack_accepts_subtype G e S T U s :
    G ⁏ e ⊢ S <: T ->
    ty_stack G e T s U ->
    ty_stack G e S s U.
Proof.
  intros Hsub Hstack. destruct Hstack.
  - apply ty_stack_nil. eapply subtyp_trans; eassumption.
  - eapply ty_stack_let with (L := L \u ctx_dom G); [eassumption |].
    intros x Hx. apply notin_union in Hx as [HxL HxG].
    pose proof (@narrow_last_binding G e x v_let S S0 HxG Hsub) as Hext.
    exact (proj1 replace_term_bindings _ _ _ _ _ (H x HxL) _ Hext Hext).
Qed.

Local Lemma avar_open_commute (a : avar) k l x y :
    k <> l ->
    open_rec k x (open_rec l y a) = open_rec l y (open_rec k x a).
Proof.
  intros Hkl. destruct a as [i | z]; [| reflexivity].
  cbn [open_rec AvarOpenable].
  destruct (Nat.eq_dec k i) as [Hki | Hki];
    destruct (Nat.eq_dec l i) as [Hli | Hli]; try congruence.
  all: repeat first [rewrite (@If_l _ (k = i)) by assumption
                   | rewrite (@If_l _ (l = i)) by assumption
                   | rewrite (@If_r _ (k = i)) by assumption
                   | rewrite (@If_r _ (l = i)) by assumption
                   | progress cbn [open_rec AvarOpenable]];
       reflexivity.
Qed.

Local Lemma type_dec_open_commute :
    (forall T : typ, forall k l x y, k <> l ->
      open_rec k x (open_rec l y T) = open_rec l y (open_rec k x T)) /\
    (forall D : dec, forall k l x y, k <> l ->
      open_rec k x (open_rec l y D) = open_rec l y (open_rec k x D)).
Proof.
  apply typ_mutind; intros;
    cbn [open_rec TypOpenable DecOpenable open_rec_typ open_rec_dec];
    try reflexivity;
    f_equal; eauto using avar_open_commute; try congruence.
Qed.

Local Lemma type_open_commute (T : typ) k l x y :
    k <> l ->
    open_rec k x (open_rec l y T) = open_rec l y (open_rec k x T).
Proof. exact (proj1 type_dec_open_commute T k l x y). Qed.

Local Lemma type_equiv_stays_open e (T U : typ) :
    e ⊢ T ≈ U ->
    forall k x, e ⊢ open_rec k x T ≈ open_rec k x U.
Proof.
  intros Hty. induction Hty; intros k u.
  - inversion H; subst; apply tyq_typ_nulary; constructor.
  - inversion H; subst; cbn [open_rec TypOpenable open_rec_typ];
      eapply tyq_typ_andor; [constructor | ..]; auto.
  - change (e ⊢ typ_fun (open_rec k u t11) (open_rec (S k) u t12)
              ≈ typ_fun (open_rec k u t21) (open_rec (S k) u t22)).
    apply tyq_typ_fun; [auto |].
    intros x. rewrite !(@type_open_commute _ 0 (S k) x u) by discriminate.
    auto.
  - apply tyq_typ_fld; auto.
  - change (e ⊢ typ_rcd (dec_typ B (open_rec (S k) u t11) (open_rec (S k) u t12))
              ≈ typ_rcd (dec_typ B (open_rec (S k) u t21) (open_rec (S k) u t22))).
    apply tyq_typ_typ; intros x;
      rewrite !(@type_open_commute _ 0 (S k) x u) by discriminate; auto.
  - apply tyq_typ_sel_normal; assumption.
  - apply tyq_typ_sel.
  - change (e ⊢ typ_bnd (open_rec (S k) u t1) ≈ typ_bnd (open_rec (S k) u t2)).
    apply tyq_typ_bnd. intros x.
    rewrite !(@type_open_commute _ 0 (S k) x u) by discriminate. auto.
  - change (e ⊢ typ_rcd (dec_met m (open_rec (S k) u t11) (open_rec k u t12)
                                       (open_rec (S (S k)) u t13))
              ≈ typ_rcd (dec_met m (open_rec (S k) u t21) (open_rec k u t22)
                                       (open_rec (S (S k)) u t23))).
    apply tyq_typ_met.
    + intros x. rewrite !(@type_open_commute _ 0 (S k) x u) by discriminate.
      auto.
    + auto.
    + intros x y. rewrite !(@type_open_commute _ 1 (S (S k)) y u) by congruence.
      rewrite !(@type_open_commute _ 0 (S (S k)) x u) by discriminate. auto.
Qed.

Local Lemma avar_open_away a k x :
    a <> avar_b k -> open_rec k x a = a.
Proof.
  intros Hneq. destruct a as [i | z]; [| reflexivity].
  cbn [open_rec AvarOpenable]. rewrite If_r by congruence. reflexivity.
Qed.

Local Lemma avar_open_here k x :
    open_rec k x (avar_b k) = avar_f x.
Proof.
  cbn [open_rec AvarOpenable]. rewrite If_l by reflexivity. reflexivity.
Qed.

Local Lemma independent_type_open_alias e x y v T :
    e ⊢ x ≈ y ->
    typ_indep v T ->
    forall k, v = avar_b k -> e ⊢ open_rec k x T ≈ open_rec k y T.
Proof.
  intros Halias Hind. induction Hind; intros k Heq; inversion Heq; subst.
  - inversion H; subst; apply tyq_typ_nulary; constructor.
  - eapply tyq_typ_andor; [apply typ_andor_and | eauto | eauto].
  - eapply tyq_typ_andor; [apply typ_andor_or | eauto | eauto].
  - apply tyq_typ_fld; eauto.
  - apply tyq_typ_typ; intros z; apply type_equiv_stays_open; eauto.
  - apply tyq_typ_fun; [eauto |].
    intros z. apply type_equiv_stays_open; eauto.
  - change (e ⊢ typ_sel (open_rec k x v1) l (open_rec k x v2)
              ≈ typ_sel (open_rec k y v1) l (open_rec k y v2)).
    rewrite !avar_open_away by congruence. apply tyq_typ_sel.
  - change (e ⊢ typ_sel (open_rec k x v1) (typ_label_normal l) (open_rec k x v2)
              ≈ typ_sel (open_rec k y v1) (typ_label_normal l) (open_rec k y v2)).
    rewrite !(@avar_open_away v2 k) by congruence.
    destruct (classic (v1 = avar_b k)) as [-> | Hneq].
    + rewrite !avar_open_here. now apply tyq_typ_sel_normal.
    + rewrite !avar_open_away by exact Hneq. apply tyq_typ_sel.
  - apply tyq_typ_bnd. intros z. apply type_equiv_stays_open; eauto.
  - apply tyq_typ_met.
    + intros z. apply type_equiv_stays_open; eauto.
    + eauto.
    + intros z c. do 2 apply type_equiv_stays_open. eauto.
Qed.

Local Lemma incap_result_accepts_nocap G e T U :
    G ⁏ e ⊢ T ∶icp U -> G ⁏ e ⊢ typ_nocap <: U.
Proof.
  intros Hty. induction Hty;
    try solve [first [apply subtyp_top | apply subtyp_refl | apply subtyp_nocap_typ
                  | apply subtyp_nocap_met | apply subtyp_nocap_fld
                  | apply subtyp_nocap_bnd | now apply subtyp_nocap_fun]];
    try assumption.
  - now apply subtyp_and2.
  - eapply subtyp_trans with (T := S2); [assumption | apply subtyp_or11].
Qed.

Local Fixpoint neutral_outer_shape (N : Prop) (T : typ) : Prop :=
  match T with
  | typ_top | typ_bnd _ => True
  | typ_nocap => N
  | typ_fun _ _ => mode_has_fun typing_mode
  | typ_and a b | typ_or a b =>
      neutral_outer_shape N a /\ neutral_outer_shape N b
  | typ_rcd (dec_fld _ _ _) | typ_rcd (dec_met _ _ _ _)
  | typ_rcd (dec_typ (typ_label_normal _) _ _) => True
  | _ => False
  end.

Local Lemma structural_incap_result G e T U :
    mode_incap' typing_mode = mode_incap_structural ->
    G ⁏ e ⊢ T ∶icp U ->
    neutral_outer_shape True U.
Proof.
  intros Hmode Hty. induction Hty; simpl; try tauto; congruence.
Qed.

Local Lemma structural_incap_identity_shape G e T U :
    mode_incap' typing_mode = mode_incap_structural ->
    G ⁏ e ⊢ T ∶icp U ->
    T = U ->
    neutral_outer_shape False T.
Proof.
  intros Hmode Hty. induction Hty; intros Heq;
    try discriminate; inversion Heq; subst; simpl; try tauto.
  - eapply structural_incap_result in H0; [exact H0 | exact Hmode].
  - congruence.
Qed.

Local Lemma neutral_shape_incap G e T :
    neutral_outer_shape False T -> G ⁏ e ⊢ T ∶icp T.
Proof.
  induction T; simpl; intros H; try contradiction.
  - apply ty_incap_top.
  - destruct d as [A S U | a S U | m TC TZ TR].
    + destruct A; [apply ty_incap_typ | contradiction].
    + apply ty_incap_fld.
    + apply ty_incap_met.
  - destruct H as [H1 H2]. apply ty_incap_and; [apply IHT1 | apply IHT2]; assumption.
  - destruct H as [H1 H2]. apply ty_incap_or; [apply IHT1 | apply IHT2]; assumption.
  - apply ty_incap_rec.
  - now apply ty_incap_fun.
Qed.

Local Lemma type_equiv_keeps_neutral_shape e (T U : typ) :
    e ⊢ T ≈ U ->
    neutral_outer_shape False T ->
    neutral_outer_shape False U.
Proof.
  intros Hty. induction Hty; simpl; try tauto.
  inversion H; subst; simpl; tauto.
Qed.

Local Lemma incap_identity_respects_equiv G e T U :
    G ⁏ e ⊢ T ∶icp T ->
    e ⊢ T ≈ U ->
    G ⁏ e ⊢ U ∶icp U.
Proof.
  intros Hty Heq.
  assert (Hm : mode_incap' typing_mode = mode_incap_structural \/
               mode_incap' typing_mode = mode_incap_nocap).
  { destruct typing_mode; simpl in *; discriminate || auto. }
  destruct Hm as [Hm | Hm].
  - apply neutral_shape_incap.
    eapply type_equiv_keeps_neutral_shape; [exact Heq |].
    eapply structural_incap_identity_shape; eauto.
  - apply ty_incap_nocap; [exact Hm |].
    eapply subtyp_trans.
    + eapply incap_result_accepts_nocap; exact Hty.
    + now apply subtyp_tyq.
Qed.

Local Lemma alias_inherits_typing G e (x : var) T :
    G ⁏ e ⊢ x ∶ T ->
    forall y,
      e ⊢ x ≈ y ->
      (forall U, ctx_binds x U G -> G ⁏ e ⊢ y ∶ U) ->
      G ⁏ e ⊢ y ∶ T.
Proof.
  intros Hty. induction Hty; intros y Halias Hbind.
  - now apply Hbind.
  - assert (Heq : e ⊢ open x T ≈ open y T).
    { eapply independent_type_open_alias; eauto. }
    apply ty_rec_intro; [| assumption |].
    + eapply ty_var_sub with (T := open x T).
      * now apply IHHty.
      * now apply subtyp_tyq.
    + intros Hmode. eapply incap_identity_respects_equiv; eauto.
  - eapply ty_var_sub with (T := open y T).
    + apply ty_rec_elim; auto.
    + apply subtyp_tyq. eapply independent_type_open_alias; eauto using tyq_var_sym.
  - apply ty_var_and; auto.
  - eapply ty_var_sub; eauto.
  - eapply ty_var_mut_top; eauto.
Qed.

Local Lemma context_binding_unique G x T U :
    ctx_binds x T G -> ctx_binds x U G -> T = U.
Proof.
  intros H1. revert U. induction H1; intros U H2;
    inversion H2; subst; try congruence; auto.
Qed.

Local Lemma reference_typing_at_location G e w y T :
    ctx_ok G ->
    renv_corr G e ->
    binds w y e ->
    G ⁏ e ⊢ w ∶ T ->
    G ⁏ e ⊢ y ∶ T.
Proof.
  intros Hok Hcorr Hbind Hty.
  destruct (reference_location_annotations Hok Hcorr Hbind)
    as [U [B [Gw [Gy [Hw Hy]]]]].
  pose proof (kind_binding_gives_binding Hw) as Hw'.
  pose proof (ty_var_var typing_mode e (kind_binding_gives_binding Hy)) as Hy'.
  eapply alias_inherits_typing; [exact Hty | now apply tyq_var_binds |].
  intros A Hdecl.
  rewrite (context_binding_unique Hdecl Hw').
  apply ty_var_and.
  - eapply ty_var_sub; [exact Hy' | apply subtyp_and11].
  - eapply ty_var_sub with (T := typ_mut_marker typ_bot).
    + eapply ty_var_sub; [exact Hy' | apply subtyp_and12].
    + apply subtyp_typ; intros; first [apply subtyp_refl | apply subtyp_bot].
Qed.

Local Lemma inert_binding_class F x T :
    inert F -> ctx_binds x T F ->
    exists k G, inert_vk k /\ inert_typ T k /\ ctx_binds_k_after x k T F G.
Proof.
  intros Hctx. induction Hctx; intros Hbind; inversion Hbind; subst.
  - exists vk, G. repeat split; try assumption. apply ctx_binds_k_e.
  - match goal with H : ctx_binds x T G |- _ =>
      destruct (IHHctx H) as [k [G0 [Hk [Htype Hafter]]]]
    end.
    exists k, G0. repeat split; try assumption. now apply ctx_binds_k_n.
Qed.

Local Lemma kind_binding_in_kind_domain F G x k T :
    ctx_binds_k_after x k T F G -> x \in ctx_kdom k F.
Proof.
  intros H. induction H; simpl ctx_kdom.
  - rewrite If_l by reflexivity. rewrite in_union, in_singleton. now left.
  - destruct (classic (vk1 = vk2)) as [Heq | Hneq].
    + rewrite If_l by exact Heq. rewrite in_union. now right.
    + now rewrite If_r by exact Hneq.
Qed.

Local Lemma kind_domain_in_context_domain F k x :
    x \in ctx_kdom k F -> x \in ctx_dom F.
Proof.
  induction F as [| G IH y l T | G IH | G IH]; simpl.
  - auto.
  - destruct (classic (k = l)) as [Heq | Hneq].
    + rewrite If_l by exact Heq. repeat rewrite in_union. tauto.
    + rewrite If_r by exact Hneq. rewrite in_union. auto.
  - exact IH.
  - exact IH.
Qed.

Local Lemma kind_domain_has_binding F k x :
    ctx_weakens F -> ctx_ok F ->
    x \in ctx_kdom k F ->
    ctx_k F x k.
Proof.
  intros Hweak. induction Hweak; intros Hok Hin; simpl ctx_kdom in Hin.
  - rewrite in_empty in Hin. contradiction.
  - assert (Hold : ctx_ok G) by (inversion Hok; assumption).
    assert (Hfresh : v §# G) by (inversion Hok; assumption).
    destruct (classic (k = vk)) as [Heq | Hneq].
    + subst k. rewrite If_l in Hin by reflexivity.
      rewrite in_union, in_singleton in Hin. destruct Hin as [-> | Hin].
      * exists t, G. apply ctx_binds_k_e.
      * destruct (IHHweak Hold Hin) as [A [F0 Hbind]].
        exists A, F0. apply ctx_binds_k_n; [| exact Hbind].
        intros ->. apply Hfresh. eapply kind_domain_in_context_domain; exact Hin.
    + rewrite If_r in Hin by exact Hneq.
      destruct (IHHweak Hold Hin) as [A [F0 Hbind]].
      exists A, F0. apply ctx_binds_k_n; [| exact Hbind].
      intros ->. apply Hfresh. eapply kind_domain_in_context_domain; exact Hin.
Qed.

Local Lemma kind_binding_unique F G G' x k l T U :
    ctx_binds_k_after x k T F G -> ctx_binds_k_after x l U F G' -> k = l.
Proof.
  intros H1. revert G' l U. induction H1; intros G' l U H2;
    inversion H2; subst; try congruence; eauto.
Qed.

Local Lemma location_not_environment_key F e S y A G :
    heap_correspond F e S ->
    ctx_binds_k_after y v_loc A F G ->
    y # e.
Proof.
  intros (Hok & Hweak & _ & _ & _ & Hdom & _ & _) Hloc Hin.
  rewrite <- Hdom in Hin.
  destruct (@kind_domain_has_binding F v_ref y Hweak Hok Hin) as [B [G' Href]].
  discriminate (kind_binding_unique Hloc Href).
Qed.

Local Definition canonical_location (e : renv) (x : var) : var :=
  match get x e with Some y => y | None => x end.

Local Lemma environment_binding_canonical_locations F e S x y :
    heap_correspond F e S -> binds x y e ->
    canonical_location e x = y /\ canonical_location e y = y.
Proof.
  intros Hheap Hb.
  assert (Hok : ctx_ok F) by (exact (proj1 Hheap)).
  assert (Henv : renv_corr F e) by
    (destruct Hheap as (_ & _ & _ & _ & _ & _ & Henv & _); exact Henv).
  destruct (reference_binding_types Hok Henv Hb)
    as [Tw [Ty [Gw [Gy [Hw [Hy Hcorr]]]]]].
  split; unfold canonical_location.
  - now rewrite (binds_get Hb).
  - rewrite (get_none (location_not_environment_key Hheap Hy)). reflexivity.
Qed.

Local Lemma equivalent_variables_share_location F e S (x y : var) :
    heap_correspond F e S -> e ⊢ x ≈ y ->
    canonical_location e x = canonical_location e y.
Proof.
  intros Hheap Heq.
  induction Heq as [e v | e w z Hb | e v1 v2 H IH | e v1 v2 v3 H1 IH1 H2 IH2].
  - reflexivity.
  - destruct (environment_binding_canonical_locations Hheap Hb) as [-> ->].
    reflexivity.
  - symmetry; auto.
  - transitivity (canonical_location e v2); auto.
Qed.

Local Lemma variable_equiv_to_location e x :
    e ⊢ x ≈ canonical_location e x.
Proof.
  unfold canonical_location. destruct (get x e) as [y |] eqn:Hget.
  - now apply tyq_var_binds.
  - apply tyq_var_refl.
Qed.

Local Lemma location_has_typed_defs F e S y G R B :
    heap_correspond F e S ->
    ctx_binds_k_after y v_loc (typ_objref R B) F G ->
    exists ds,
      binds y (item_obj ds) S /\
      F §§ (objctx_heap y R) ⁏ e ⊢ ds ∶ open y R.
Proof.
  intros (_ & _ & _ & _ & Hdom & _ & _ & Hitems) Hkind.
  pose proof (kind_binding_in_kind_domain Hkind) as Hin.
  rewrite Hdom in Hin. specialize (Hitems y Hin).
  inversion Hitems; subst.
  - pose proof mode_disallows_functions. congruence.
  - match goal with Hb : ctx_binds y _ F |- _ =>
      pose proof (context_binding_unique Hb (kind_binding_gives_binding Hkind)) as Heq;
      inversion Heq; subst; eauto
    end.
Qed.

Local Lemma precise_config_annotation F e S x T :
    inert F -> heap_correspond F e S -> ctx_binds x T F ->
    exists R B ds,
      T = typ_objref R (typ_mut_marker B) /\
      record_type R /\
      typ_indep_b 0 R /\
      ctx_binds (canonical_location e x) (typ_objref R (typ_mut_marker typ_bot)) F /\
      binds (canonical_location e x) (item_obj ds) S /\
      F §§ (objctx_heap (canonical_location e x) R) ⁏ e
        ⊢ ds ∶ open (canonical_location e x) R.
Proof.
  intros Hinert Hheap Hbind.
  destruct (inert_binding_class Hinert Hbind)
    as [k [G [Hkind [Htype Hentry]]]].
  inversion Htype; subst.
  - pose proof mode_disallows_functions. congruence.
  - assert (Hmode : mode_refcaps' typing_mode = mode_refcaps_mutability).
    { destruct typing_mode; simpl in *; discriminate || reflexivity. }
    match goal with Hcap : refcap_inert_type ?A ?k |- _ =>
      unfold refcap_inert_type in Hcap;
      rewrite Hmode in Hcap;
      inversion Hcap; subst
    end.
    + destruct (location_has_typed_defs Hheap Hentry) as [ds [Hb Hds]].
      assert (Hcanonical : canonical_location e x = x).
      { unfold canonical_location.
        rewrite (get_none (location_not_environment_key Hheap Hentry)).
        reflexivity. }
      rewrite Hcanonical. do 3 eexists. repeat split;
        first [eassumption | eapply kind_binding_gives_binding; eassumption].
    + assert (Henv : renv_corr F e).
      { destruct Hheap as (_ & _ & _ & _ & _ & _ & Henv & _); exact Henv. }
      assert (Hok : ctx_ok F) by (exact (proj1 Hheap)).
      assert (Hdom : ctx_kdom v_ref F = dom e).
      { destruct Hheap as (_ & _ & _ & _ & _ & Hdom & _); exact Hdom. }
      pose proof (kind_binding_in_kind_domain Hentry) as Hin.
      rewrite Hdom in Hin. destruct (get_some Hin) as [y Hb].
      change (binds x y e) in Hb.
      destruct (reference_location_annotations Hok Henv Hb)
        as [R [B [Gw [Gy [Hw Hy]]]]].
      pose proof (context_binding_unique (kind_binding_gives_binding Hentry)
                   (kind_binding_gives_binding Hw)) as Heq.
      inversion Heq; subst.
      destruct (location_has_typed_defs Hheap Hy) as [ds [Hitem Hds]].
      rewrite (proj1 (environment_binding_canonical_locations Hheap Hb)).
      do 3 eexists. repeat split;
        first [eassumption | eapply kind_binding_gives_binding; eassumption].
Qed.

Local Lemma typed_record_contains_declaration F Go e (ds : defs) T D :
    F §§ Go ⁏ e ⊢ ds ∶ T ->
    record_has T D ->
    exists d, F §§ Go ⁏ e ⊢ d ∶d D.
Proof.
  intros Hty. induction Hty; intros Hdecl; inversion Hdecl; subst.
  - eexists; eassumption.
  - apply IHHty; assumption.
  - match goal with Hr : record_has (typ_rcd _) _ |- _ =>
      inversion Hr; subst; eexists; eassumption
    end.
Qed.

Local Lemma precise_normal_member_bounds F Go e (ds : defs) T a S U :
    F §§ Go ⁏ e ⊢ ds ∶ T ->
    record_has T (dec_typ (typ_label_normal a) S U) ->
    S = U.
Proof.
  intros Hty Hdecl.
  destruct (typed_record_contains_declaration Hty Hdecl) as [d Hd].
  now inversion Hd.
Qed.

Local Lemma record_projects_declaration F e R D :
    record_has R D -> F ⁏ e ⊢ R <: typ_rcd D.
Proof.
  intros Hhas. induction Hhas.
  - apply subtyp_refl.
  - eapply subtyp_trans; [apply subtyp_and11 | exact IHHhas].
  - eapply subtyp_trans; [apply subtyp_and12 | exact IHHhas].
Qed.

Local Lemma precise_declaration_is_accessible F e x R B D :
    ctx_binds x (typ_objref R B) F ->
    typ_indep_b 0 R ->
    record_has (open (canonical_location e x) R) D ->
    F ⁏ e ⊢ x ∶ typ_rcd D.
Proof.
  intros Hb Hind Hdecl.
  eapply ty_var_sub with (T := open (canonical_location e x) R).
  - eapply ty_var_sub with (T := open x R).
    + apply ty_rec_elim; [| exact Hind].
      eapply ty_var_sub with (T := typ_objref R B);
        [apply ty_var_var; exact Hb | apply subtyp_and11].
    + apply subtyp_tyq.
      eapply independent_type_open_alias;
        [apply variable_equiv_to_location | exact Hind | reflexivity].
  - now apply record_projects_declaration.
Qed.

Local Lemma open_preserves_declaration_label (D : dec) n x :
    label_of (open_rec n x D) = label_of D.
Proof. destruct D; reflexivity. Qed.

Local Lemma opened_record_declaration D n x :
    record_dec D -> record_dec (open_rec n x D).
Proof. intros H. inversion H; subst; constructor. Qed.

Local Lemma opened_record_typ R ls n x :
    record_typ R ls -> record_typ (open_rec n x R) ls.
Proof.
  intros H. induction H.
  - change (record_typ (typ_rcd (open_rec n x D)) \{l}).
    apply rt_one; [now apply opened_record_declaration |].
    now rewrite open_preserves_declaration_label.
  - change (record_typ (typ_and (open_rec n x T) (typ_rcd (open_rec n x D)))
                 (ls \u \{l})).
    apply rt_cons; [assumption | now apply opened_record_declaration | | assumption].
    now rewrite open_preserves_declaration_label.
Qed.

Local Lemma single_record_has_only D E :
    record_has (typ_rcd D) E -> E = D.
Proof. intros H. now inversion H. Qed.

Local Lemma record_intersection_member R T D :
    record_has (typ_and R T) D -> record_has R D \/ record_has T D.
Proof. intros H. inversion H; subst; auto. Qed.

Local Lemma record_member_label_in_labels R ls D :
    record_typ R ls -> record_has R D -> label_of D \in ls.
Proof.
  intros H. induction H; intros Hmember.
  - apply single_record_has_only in Hmember as ->.
    now rewrite in_singleton.
  - apply record_intersection_member in Hmember as [Hleft | Hright].
    + rewrite in_union. left. now apply IHrecord_typ.
    + apply single_record_has_only in Hright as ->.
      rewrite in_union, in_singleton. now right.
Qed.

Local Lemma record_label_unique R ls D E :
    record_typ R ls ->
    record_has R D ->
    record_has R E ->
    label_of D = label_of E ->
    D = E.
Proof.
  intros H. induction H as [d l Hdec -> | R ls d l Hrt IH Hdec -> Hfresh];
    intros Hd He Hlabel.
  - apply single_record_has_only in Hd as ->.
    symmetry. now apply single_record_has_only.
  - apply record_intersection_member in Hd as [Hd | Hd];
    apply record_intersection_member in He as [He | He].
    + now apply IH.
    + apply single_record_has_only in He as ->.
      exfalso. apply Hfresh. rewrite <- Hlabel.
      eapply record_member_label_in_labels; eassumption.
    + apply single_record_has_only in Hd as ->.
      exfalso. apply Hfresh. rewrite Hlabel.
      eapply record_member_label_in_labels; eassumption.
    + apply single_record_has_only in Hd as ->.
      symmetry. now apply single_record_has_only.
Qed.

Inductive exact_type_declaration F e (x : var) : typ_label -> typ -> typ -> Prop :=
| exact_normal_declaration R B a L U :
    ctx_binds x (typ_objref R (typ_mut_marker B)) F ->
    record_has (open (canonical_location e x) R) (dec_typ (typ_label_normal a) L U) ->
    exact_type_declaration F e x (typ_label_normal a) L U
| exact_capability_declaration R B :
    ctx_binds x (typ_objref R (typ_mut_marker B)) F ->
    exact_type_declaration F e x typ_label_mutability typ_bot B.

Local Lemma exact_type_declaration_gives_typing F e S x a L U :
    inert F -> heap_correspond F e S ->
    exact_type_declaration F e x a L U ->
    F ⁏ e ⊢ x ∶ typ_rcd (dec_typ a L U).
Proof.
  intros Hinert Hheap Hdecl. destruct Hdecl as [R B a L U Hb Hrecord | R B Hb].
  - destruct (precise_config_annotation Hinert Hheap Hb)
      as [R' [B' [ds [Heq [_ [Hind _]]]]]].
    inversion Heq; subst.
    eapply precise_declaration_is_accessible; eassumption.
  - eapply ty_var_sub with (T := typ_objref R (typ_mut_marker B));
      [apply ty_var_var; exact Hb | apply subtyp_and12].
Qed.

Local Lemma exact_normal_type_declaration_has_equal_bounds F e S x a L U :
    inert F -> heap_correspond F e S ->
    exact_type_declaration F e x (typ_label_normal a) L U ->
    L = U.
Proof.
  intros Hinert Hheap Hdecl. inversion Hdecl; subst.
  match goal with Hb : ctx_binds x _ F |- _ =>
    destruct (precise_config_annotation Hinert Hheap Hb)
      as [R' [B' [ds [Heq [_ [_ [_ [_ Hds]]]]]]]]
  end.
  inversion Heq; subst.
  eapply precise_normal_member_bounds; eassumption.
Qed.

Local Lemma exact_type_declaration_unique F e S x a L U L' U' :
    inert F -> heap_correspond F e S ->
    exact_type_declaration F e x a L U ->
    exact_type_declaration F e x a L' U' ->
    L = L' /\ U = U'.
Proof.
  intros Hinert Hheap H1 H2.
  destruct H1 as [R B a L U Hb Hrecord | R B Hb].
  - inversion H2 as [R2 B2 a2 L2 U2 Hb2 Hrecord2 | R2 B2 Hb2]; subst.
    pose proof (context_binding_unique Hb Hb2) as Hbindings.
    inversion Hbindings; subst R2 B2.
    destruct (precise_config_annotation Hinert Hheap Hb)
      as [R' [B' [ds [Heq [[ls Hrd] _]]]]].
    inversion Heq; subst.
    pose proof (opened_record_typ 0 (canonical_location e x) Hrd) as Hopened.
    pose proof (record_label_unique Hopened Hrecord Hrecord2 eq_refl) as Hmembers.
    inversion Hmembers; auto.
  - inversion H2 as [R2 B2 a2 L2 U2 Hb2 Hrecord2 | R2 B2 Hb2]; subst.
    pose proof (context_binding_unique Hb Hb2) as Hbindings.
    inversion Hbindings; auto.
Qed.

Local Lemma reference_of_declared_location F e S x R :
    heap_correspond F e S ->
    ctx_binds (canonical_location e x) (typ_objref R (typ_mut_marker typ_bot)) F ->
    exists B, ctx_binds x (typ_objref R (typ_mut_marker B)) F.
Proof.
  intros (Hok & _ & _ & _ & _ & _ & Henv & _) Hloc.
  unfold canonical_location in Hloc. destruct (get x e) as [y |] eqn:Hget.
  - change (binds x y e) in Hget.
    destruct (reference_location_annotations Hok Henv Hget)
      as [R' [B [Gw [Gy [Hw Hy]]]]].
    pose proof (context_binding_unique Hloc (kind_binding_gives_binding Hy)) as Heq.
    inversion Heq; subst.
    exists B. eapply kind_binding_gives_binding; eassumption.
  - now exists typ_bot.
Qed.

Local Lemma exact_normal_type_declaration_on_alias F e S (x y : var) a L U :
    inert F -> heap_correspond F e S ->
    e ⊢ x ≈ y ->
    exact_type_declaration F e x (typ_label_normal a) L U ->
    exact_type_declaration F e y (typ_label_normal a) L U.
Proof.
  intros Hinert Hheap Hequiv Hdecl.
  pose proof (equivalent_variables_share_location Hheap Hequiv) as Hsame.
  inversion Hdecl; subst.
  match goal with Hb : ctx_binds x _ F |- _ =>
    destruct (precise_config_annotation Hinert Hheap Hb)
      as [R' [B' [ds [Heq [_ [_ [Hloc _]]]]]]]
  end.
  inversion Heq; subst.
  rewrite Hsame in Hloc.
  destruct (@reference_of_declared_location F e S y R' Hheap Hloc) as [B0 Hy].
  eapply exact_normal_declaration; [exact Hy |].
  rewrite <- Hsame. assumption.
Qed.

(* Type selections here use the declarations of the inert context. Method
   subtyping can still check its binders in an extended abstract context. *)
Local Definition method_type_bounds F e C Z R C' Z' R' : Prop :=
  F ⁏ e ⊢ Z' <: Z /\
  exists L,
    (forall x, x \notin L -> F § x / v_par ~ Z' ⁏ e ⊢ open x C' <: open x C) /\
    (forall x, x \notin L -> forall y, y <> x -> y \notin L ->
      ctx_met F x Z' y C' ⁏ e ⊢ open_met x y R <: open_met x y R').

Local Lemma method_type_bounds_refl F e C Z R :
    method_type_bounds F e C Z R C Z R.
Proof.
  split; [apply subtyp_refl |].
  exists (\{} : vars). split; intros; apply subtyp_refl.
Qed.

Local Lemma method_type_bounds_trans F e C0 Z0 R0 C1 Z1 R1 C2 Z2 R2 :
    method_type_bounds F e C0 Z0 R0 C1 Z1 R1 ->
    method_type_bounds F e C1 Z1 R1 C2 Z2 R2 ->
    method_type_bounds F e C0 Z0 R0 C2 Z2 R2.
Proof.
  intros (HZ01 & L1 & HC01 & HR01) (HZ12 & L2 & HC12 & HR12).
  split; [eapply subtyp_trans; eassumption |].
  exists (L1 \u (L2 \u ctx_dom F)). split.
  - intros x Hx. rewrite !notin_union in Hx.
    destruct Hx as [Hx1 [Hx2 HxF]].
    eapply subtyp_trans; [exact (HC12 x Hx2) |].
    eapply replace_subtyping; [| exact (HC01 x Hx1)].
    exact (proj1 (@narrow_last_binding F e x v_par Z2 Z1 HxF HZ12)).
  - intros x Hx y Hneq Hy.
    rewrite !notin_union in Hx, Hy.
    destruct Hx as [Hx1 [Hx2 HxF]], Hy as [Hy1 [Hy2 HyF]].
    assert (Hfresh2 : y §# (F § x / v_par ~ Z2)) by now apply fresh_pushed_context.
    pose proof (@narrow_last_binding F e x v_par Z2 Z1 HxF HZ12) as Hpar.
    pose proof (@typing_context_extends_push _ _ e y v_recv (open x C1)
                 Hfresh2 Hpar) as Hmethod.
    pose proof (@narrow_last_binding (F § x / v_par ~ Z2) e y v_recv
                  (open x C2) (open x C1) Hfresh2 (HC12 x Hx2)) as Hrecv.
    eapply subtyp_trans; [| exact (HR12 x Hx2 y Hneq Hy2)].
    eapply replace_subtyping; [exact (proj1 Hrecv) |].
    eapply replace_subtyping; [exact (proj1 Hmethod) | exact (HR01 x Hx1 y Hneq Hy1)].
Qed.

Inductive exact_subtype (F : ctx) (e : renv) : typ -> typ -> Prop :=
| exact_subtype_top T : exact_subtype F e T typ_top
| exact_subtype_bot T : exact_subtype F e typ_bot T
| exact_subtype_refl T : exact_subtype F e T T
| exact_subtype_trans S T U :
    exact_subtype F e S T -> exact_subtype F e T U -> exact_subtype F e S U
| exact_subtype_and_left T U : exact_subtype F e (typ_and T U) T
| exact_subtype_and_right T U : exact_subtype F e (typ_and T U) U
| exact_subtype_and S T U :
    exact_subtype F e S T -> exact_subtype F e S U ->
    exact_subtype F e S (typ_and T U)
| exact_subtype_or_left T U : exact_subtype F e T (typ_or T U)
| exact_subtype_or_right T U : exact_subtype F e U (typ_or T U)
| exact_subtype_or S T U :
    exact_subtype F e S T -> exact_subtype F e U T ->
    exact_subtype F e (typ_or S U) T
| exact_subtype_field a A B C D :
    exact_subtype F e C A -> exact_subtype F e B D ->
    exact_subtype F e (typ_rcd (dec_fld a A B)) (typ_rcd (dec_fld a C D))
| exact_subtype_member a A B C D :
    (forall x, exact_subtype F e (open x C) (open x A)) ->
    (forall x, exact_subtype F e (open x B) (open x D)) ->
    exact_subtype F e (typ_rcd (dec_typ a A B)) (typ_rcd (dec_typ a C D))
| exact_subtype_select_upper x a y L U :
    exact_type_declaration F e x a L U ->
    exact_subtype F e (typ_sel (avar_f x) a (avar_f y)) (open y U)
| exact_subtype_select_lower x a y L U :
    exact_type_declaration F e x a L U ->
    exact_subtype F e (open y L) (typ_sel (avar_f x) a (avar_f y))
| exact_subtype_method m C Z R C' Z' R' :
    F ⁏ e ⊢ typ_rcd (dec_met m C Z R) <: typ_rcd (dec_met m C' Z' R') ->
    method_type_bounds F e C Z R C' Z' R' ->
    exact_subtype F e (typ_rcd (dec_met m C Z R)) (typ_rcd (dec_met m C' Z' R'))
| exact_subtype_equiv T U :
    e ⊢ T ≈ U -> exact_subtype F e T U
| exact_subtype_member_and a L U L' U' :
    exact_subtype F e
      (typ_and (typ_rcd (dec_typ a L U)) (typ_rcd (dec_typ a L' U')))
      (typ_rcd (dec_typ a (typ_or L L') (typ_and U U')))
| exact_subtype_dist A B C :
    exact_subtype F e (typ_and A (typ_or B C))
      (typ_or (typ_and A B) (typ_and A C))
| exact_subtype_nocap_rec T : exact_subtype F e typ_nocap (typ_bnd T)
| exact_subtype_nocap_member a T U :
    exact_subtype F e typ_nocap (typ_rcd (dec_typ (typ_label_normal a) T U))
| exact_subtype_nocap_field a T U :
    exact_subtype F e typ_nocap (typ_rcd (dec_fld a T U))
| exact_subtype_nocap_method m C Z R :
    exact_subtype F e typ_nocap (typ_rcd (dec_met m C Z R))
| exact_subtype_nocap_boundless T U :
    mode_has_top_nm_subtype_boundless typing_mode ->
    exact_subtype F e typ_top
      (typ_or typ_nocap (typ_rcd (dec_typ typ_label_mutability T U)))
| exact_subtype_nocap_complement :
    mode_has_top_nm_complement typing_mode ->
    exact_subtype F e typ_top (typ_or typ_nocap (typ_mut_marker typ_bot))
| exact_subtype_nocap_complement_bot :
    mode_has_top_nm_complement typing_mode ->
    exact_subtype F e (typ_and typ_nocap (typ_mut_marker typ_bot)) typ_bot
| exact_subtype_mut_top :
    mode_has_mut_top typing_mode ->
    exact_subtype F e typ_top (typ_mut_marker typ_top).

Local Lemma exact_subtype_general F e H S T :
    inert F -> heap_correspond F e H ->
    exact_subtype F e S T -> F ⁏ e ⊢ S <: T.
Proof.
  intros Hinert Hheap Hsub. induction Hsub; try solve [eauto 4 with core_typing].
  - eapply subtyp_sel1.
    eapply exact_type_declaration_gives_typing; eassumption.
  - eapply subtyp_sel2.
    eapply exact_type_declaration_gives_typing; eassumption.
Qed.

Local Definition interface_bounds F e (actual requested : dec) : Prop :=
  match actual, requested with
  | dec_fld a L U, dec_fld b L' U' =>
      a = b /\ exact_subtype F e L' L /\ exact_subtype F e U U'
  | dec_typ (typ_label_normal a) L U, dec_typ (typ_label_normal b) L' U' =>
      a = b /\
      (forall x, exact_subtype F e (open x L') (open x L)) /\
      (forall x, exact_subtype F e (open x U) (open x U'))
  | dec_met a C Z R, dec_met b C' Z' R' =>
      a = b /\ method_type_bounds F e C Z R C' Z' R'
  | _, _ => False
  end.

Local Lemma interface_bounds_refl F e D :
    record_dec D -> interface_bounds F e D D.
Proof.
  intros H; destruct H; simpl; split; try reflexivity.
  - split; intros; apply exact_subtype_refl.
  - split; intros; apply exact_subtype_refl.
  - split; apply exact_subtype_refl.
  - apply method_type_bounds_refl.
Qed.

Inductive object_view := declaration_view | capability_view.

(* The declaration view tracks the shape of an actual object. The capability
   view tracks the upper bound of its mutable capability independently. *)
Inductive object_has_view (F : ctx) (e : renv) (x : var) (R B : typ)
    : object_view -> typ -> Prop :=
| view_top v : object_has_view F e x R B v typ_top
| view_and v A C :
    object_has_view F e x R B v A ->
    object_has_view F e x R B v C ->
    object_has_view F e x R B v (typ_and A C)
| view_or_left v A C :
    object_has_view F e x R B v A ->
    object_has_view F e x R B v (typ_or A C)
| view_or_right v A C :
    object_has_view F e x R B v C ->
    object_has_view F e x R B v (typ_or A C)
| view_normal_selection v w a z L U :
    exact_type_declaration F e w (typ_label_normal a) L U ->
    object_has_view F e x R B v (open z U) ->
    object_has_view F e x R B v (typ_sel (avar_f w) (typ_label_normal a) (avar_f z))
| view_record_declaration actual requested :
    record_has (open (canonical_location e x) R) actual ->
    interface_bounds F e actual requested ->
    object_has_view F e x R B declaration_view (typ_rcd requested)
| view_declaration_capability a L U :
    object_has_view F e x R B declaration_view
      (typ_rcd (dec_typ (typ_label_refcap a) L U))
| view_capability_member a L U :
    object_has_view F e x R B capability_view
      (typ_rcd (dec_typ (typ_label_normal a) L U))
| view_capability_field a L U :
    object_has_view F e x R B capability_view (typ_rcd (dec_fld a L U))
| view_capability_method a C Z T :
    object_has_view F e x R B capability_view (typ_rcd (dec_met a C Z T))
| view_capability_bounds L U :
    (forall z, exact_subtype F e (open z L) typ_bot) ->
    (forall z, exact_subtype F e (open z B) (open z U)) ->
    object_has_view F e x R B capability_view (typ_rcd (dec_typ typ_label_mutability L U))
| view_nocap :
    (mode_has_top_nm_complement typing_mode ->
      ~ (forall z, exact_subtype F e (open z B) typ_bot)) ->
    object_has_view F e x R B capability_view typ_nocap
| view_declaration_rec T Witness :
    e ⊢ typ_bnd Witness ≈ typ_bnd T ->
    typ_indep_b 0 Witness ->
    F ⁏ e ⊢ open (canonical_location e x) Witness ∶icp open (canonical_location e x) Witness ->
    object_has_view F e x R B declaration_view (open (canonical_location e x) Witness) ->
    object_has_view F e x R B declaration_view (open (canonical_location e x) T) ->
    object_has_view F e x R B capability_view (open (canonical_location e x) T) ->
    object_has_view F e x R B declaration_view (typ_bnd T)
| view_capability_rec T :
    object_has_view F e x R B capability_view (typ_bnd T).

Local Lemma declaration_view_field_bounds F e x R B a A L U ls :
    record_typ (open (canonical_location e x) R) ls ->
    record_has (open (canonical_location e x) R) (dec_fld a A A) ->
    object_has_view F e x R B declaration_view (typ_rcd (dec_fld a L U)) ->
    exact_subtype F e L A /\ exact_subtype F e A U.
Proof.
  intros Hrec Hfield Hview. inversion Hview; subst.
  destruct actual as [al TL TU | fl TL TU | ml TC TZ TR].
  - destruct al; contradiction.
  - simpl in H1. destruct H1 as [Hlabel [Hlower Hupper]]. subst fl.
    pose proof (record_label_unique Hrec Hfield H0 eq_refl) as Heq.
    inversion Heq; subst TL TU. exact (conj Hlower Hupper).
  - contradiction.
Qed.

Local Lemma view_of_record_declarations F e (x : var) R B T ls :
    record_typ T ls ->
    (forall D, record_has T D -> record_has (open (canonical_location e x) R) D) ->
    object_has_view F e x R B declaration_view T /\
    object_has_view F e x R B capability_view T.
Proof.
  intros Hrec. induction Hrec; intros Hinclude;
    assert (Hmember : record_has (open (canonical_location e x) R) D)
      by (apply Hinclude; eauto using rh_one, rh_andr);
    assert (Hbounds : interface_bounds F e D D) by now apply interface_bounds_refl.
  - destruct H.
    all: split;
      [eapply view_record_declaration; [exact Hmember | exact Hbounds]
      | first [apply view_capability_member | apply view_capability_field
             | apply view_capability_method]].
  - destruct (IHHrec ltac:(intros d Hd; apply Hinclude; now apply rh_andl))
      as [Hdata Hcap].
    destruct H.
    all: split; apply view_and; try assumption.
    all: first [eapply view_record_declaration; [exact Hmember | exact Hbounds]
              | apply view_capability_member | apply view_capability_field
              | apply view_capability_method].
Qed.

Local Lemma type_equiv_symmetric e (T U : typ) :
    e ⊢ T ≈ U -> e ⊢ U ≈ T.
Proof.
  intros H. induction H.
  - now apply tyq_typ_nulary.
  - now apply tyq_typ_andor.
  - now apply tyq_typ_fun.
  - now apply tyq_typ_fld.
  - now apply tyq_typ_typ.
  - apply tyq_typ_sel_normal. now apply tyq_var_sym.
  - apply tyq_typ_sel.
  - now apply tyq_typ_bnd.
  - now apply tyq_typ_met.
Qed.

Local Definition equivalent_declaration_parts e (d d' : dec) : Prop :=
  match d, d' with
  | dec_fld a L U, dec_fld a' L' U' =>
      a = a' /\ e ⊢ L ≈ L' /\ e ⊢ U ≈ U'
  | dec_typ a L U, dec_typ a' L' U' =>
      a = a' /\ (forall z, e ⊢ open z L ≈ open z L') /\
                (forall z, e ⊢ open z U ≈ open z U')
  | dec_met a C Z R, dec_met a' C' Z' R' =>
      a = a' /\ (forall x, e ⊢ open x C ≈ open x C') /\
      e ⊢ Z ≈ Z' /\ (forall x y, e ⊢ open_met x y R ≈ open_met x y R')
  | _, _ => False
  end.

Local Definition equivalent_type_parts e (T U : typ) : Prop :=
  match T, U with
  | typ_top, typ_top | typ_bot, typ_bot | typ_nocap, typ_nocap => True
  | typ_and a b, typ_and c d | typ_or a b, typ_or c d =>
      e ⊢ a ≈ c /\ e ⊢ b ≈ d
  | typ_bnd a, typ_bnd b => forall z, e ⊢ open z a ≈ open z b
  | typ_rcd a, typ_rcd b => equivalent_declaration_parts e a b
  | typ_fun a b, typ_fun c d =>
      e ⊢ a ≈ c /\ (forall z, e ⊢ open z b ≈ open z d)
  | typ_sel a l b, typ_sel c l' d =>
      l = l' /\ b = d /\
      (a = c \/ exists x y k,
        a = avar_f x /\ c = avar_f y /\ l = typ_label_normal k /\ e ⊢ x ≈ y)
  | _, _ => False
  end.

Local Lemma type_equiv_has_parts e (T U : typ) :
    e ⊢ T ≈ U -> equivalent_type_parts e T U.
Proof.
  intros H. induction H; simpl;
    try solve [repeat split; assumption || reflexivity].
  - inversion H; subst; exact I.
  - inversion H; subst; simpl; auto.
  - repeat split; auto. right. do 3 eexists. repeat split; auto.
  - repeat split; auto.
Qed.

Local Lemma type_equiv_transitive e (T U V : typ) :
    e ⊢ T ≈ U -> e ⊢ U ≈ V -> e ⊢ T ≈ V.
Proof.
  intros H. revert V. induction H; intros V HV.
  - exact HV.
  - inversion H; subst; apply type_equiv_has_parts in HV;
      destruct V; simpl in HV; try contradiction;
      destruct HV; apply tyq_typ_andor; eauto using typ_andor_and, typ_andor_or.
  - apply type_equiv_has_parts in HV. destruct V; simpl in HV; try contradiction.
    destruct HV. apply tyq_typ_fun; eauto.
  - apply type_equiv_has_parts in HV. destruct V; simpl in HV; try contradiction.
    destruct d; simpl in HV; try contradiction.
    destruct HV as [<- [? ?]]. apply tyq_typ_fld; eauto.
  - apply type_equiv_has_parts in HV. destruct V; simpl in HV; try contradiction.
    destruct d; simpl in HV; try contradiction.
    destruct HV as [<- [? ?]]. apply tyq_typ_typ; eauto.
  - apply type_equiv_has_parts in HV. destruct V; simpl in HV; try contradiction.
    destruct HV as (Hlab & Harg & [Hsame | (p & q & k & Hp & Hq & Hk & Heq)]).
    + rewrite <- Hlab, <- Harg, <- Hsame. now apply tyq_typ_sel_normal.
    + rewrite <- Hlab, <- Harg, Hq. inversion Hp; subst.
      apply tyq_typ_sel_normal. eapply tyq_var_trans; eassumption.
  - exact HV.
  - apply type_equiv_has_parts in HV. destruct V; simpl in HV; try contradiction.
    apply tyq_typ_bnd; eauto.
  - apply type_equiv_has_parts in HV. destruct V; simpl in HV; try contradiction.
    destruct d; simpl in HV; try contradiction.
    destruct HV as [<- (? & ? & ?)]. apply tyq_typ_met; eauto.
Qed.

Local Lemma type_equiv_reflexive e (T : typ) : e ⊢ T ≈ T.
Proof.
  assert (H : (forall U : typ, e ⊢ U ≈ U) /\
             (forall D : dec, e ⊢ typ_rcd D ≈ typ_rcd D)).
  { apply typ_mutind; intros; try assumption;
      try solve [apply tyq_typ_nulary; constructor | apply tyq_typ_sel].
    - apply tyq_typ_andor; [apply typ_andor_and | assumption | assumption].
    - apply tyq_typ_andor; [apply typ_andor_or | assumption | assumption].
    - apply tyq_typ_bnd. intro z. now apply type_equiv_stays_open.
    - apply tyq_typ_fun; [assumption |]. intro z. now apply type_equiv_stays_open.
    - apply tyq_typ_typ; intros; now apply type_equiv_stays_open.
    - now apply tyq_typ_fld.
    - apply tyq_typ_met.
      + intros; now apply type_equiv_stays_open.
      + assumption.
      + intros; do 2 apply type_equiv_stays_open; assumption. }
  exact (proj1 H T).
Qed.

Local Lemma method_type_bounds_equiv F e C Z R C' Z' R' :
    (forall x, e ⊢ open x C ≈ open x C') ->
    e ⊢ Z ≈ Z' ->
    (forall x y, e ⊢ open_met x y R ≈ open_met x y R') ->
    method_type_bounds F e C Z R C' Z' R'.
Proof.
  intros HC HZ HR.
  split; [apply subtyp_tyq, type_equiv_symmetric; exact HZ |].
  exists (\{} : vars). split.
  - intros x _. apply subtyp_tyq, type_equiv_symmetric, HC.
  - intros x _ y _ _. apply subtyp_tyq, HR.
Qed.

Local Lemma interface_bounds_equiv F e d d' d'' :
    interface_bounds F e d d' ->
    equivalent_declaration_parts e d' d'' ->
    interface_bounds F e d d''.
Proof.
  destruct d; destruct d'; destruct d''.
  all: repeat match goal with a : typ_label |- _ => destruct a end;
    simpl; try tauto.
  all: try solve
    [intros (Hlabel & Hlower & Hupper) (Hlabel' & Hlower' & Hupper');
     try (injection Hlabel' as Heq; subst);
     subst; split; [reflexivity | split];
     intros;
     [eapply exact_subtype_trans;
      [apply exact_subtype_equiv, type_equiv_symmetric; apply Hlower' | apply Hlower]
     | eapply exact_subtype_trans; [apply Hupper | apply exact_subtype_equiv; apply Hupper']]].
  all: try solve
    [intros (Hlabel & Hbounds) (Hlabel' & HC & HZ & HR);
     subst; split; [reflexivity |];
     eapply method_type_bounds_trans; [exact Hbounds |
       apply method_type_bounds_equiv; assumption]].
  all: intros; repeat match goal with H : _ /\ _ |- _ => destruct H end;
       congruence.
Qed.

Local Lemma object_view_respects_equivalence F e S x R B v T U :
    inert F -> heap_correspond F e S ->
    object_has_view F e x R B v T ->
    e ⊢ T ≈ U ->
    object_has_view F e x R B v U.
Proof.
  intros Hinert Hheap Hview. revert U.
  induction Hview as
    [v | v A C HA IHA HC IHC | v A C HA IHA | v A C HC IHC
    | v w a z L U Hdecl Hinner IH
    | actual requested Hactual Hbounds | a L U
    | a L U | a L U | a C Z T | L U Hlower Hupper
    | Hnocap | T W HBnd Hind Hinc HW IHW Hdecl IHdecl Hcap IHcap | T];
    intros V Heq; pose proof (type_equiv_has_parts Heq) as Hparts;
    destruct V; simpl in Hparts; try contradiction.
  - apply view_top.
  - destruct Hparts as [Hp Hq]. apply view_and; auto.
  - destruct Hparts as [Hp Hq]. apply view_or_left; auto.
  - destruct Hparts as [Hp Hq]. apply view_or_right; auto.
  - destruct Hparts as [Hlabel [Harg [Howner | Halias]]]; subst.
    + eapply view_normal_selection; eassumption.
    + destruct Halias as [w1 [w2 [a' [Heq1 [Heq2 [Hlabel Halias]]]]]].
      inversion Heq1; subst.
      eapply view_normal_selection; [| exact Hinner].
      eapply exact_normal_type_declaration_on_alias; eassumption.
  - eapply view_record_declaration; [exact Hactual |].
    eapply interface_bounds_equiv; eassumption.
  - destruct d; simpl in Hparts; try contradiction.
    destruct Hparts as [Hlabel _]. subst.
    apply view_declaration_capability.
  - destruct d; simpl in Hparts; try contradiction.
    destruct Hparts as [Hlabel _]. subst.
    apply view_capability_member.
  - destruct d; simpl in Hparts; try contradiction. apply view_capability_field.
  - destruct d; simpl in Hparts; try contradiction. apply view_capability_method.
  - destruct d; simpl in Hparts; try contradiction.
    destruct Hparts as [Hlabel [Hp Hq]]. subst.
    apply view_capability_bounds; intros z.
    + eapply exact_subtype_trans; [| apply Hlower].
      apply exact_subtype_equiv, type_equiv_symmetric, Hp.
    + eapply exact_subtype_trans; [apply Hupper |].
      apply exact_subtype_equiv, Hq.
  - apply view_nocap; exact Hnocap.
  - eapply view_declaration_rec with (Witness := W); try eassumption; auto.
    eapply type_equiv_transitive; eassumption.
  - apply view_capability_rec.
Qed.

Local Lemma record_has_identity_incap F e R ls :
    record_typ R ls -> F ⁏ e ⊢ R ∶icp R.
Proof.
  assert (Hd : forall D, record_dec D -> F ⁏ e ⊢ typ_rcd D ∶icp typ_rcd D).
  { intros D H. destruct H; constructor. }
  intros H. induction H.
  - now apply Hd.
  - apply ty_incap_and; auto.
Qed.

Local Lemma views_of_annotation F e (x : var) R B :
    record_type R ->
    typ_indep_b 0 R ->
    object_has_view F e x R B declaration_view (typ_objref R (typ_mut_marker B)) /\
    object_has_view F e x R B capability_view (typ_objref R (typ_mut_marker B)).
Proof.
  intros [ls Hrec] Hind.
  pose proof (opened_record_typ 0 (canonical_location e x) Hrec) as Hopened.
  destruct (@view_of_record_declarations F e x R B
    (open (canonical_location e x) R) ls Hopened (fun _ H => H))
    as [Hdecl Hcap].
  split; apply view_and.
  - eapply view_declaration_rec with (Witness := R); try eassumption.
    + apply type_equiv_reflexive.
    + eapply record_has_identity_incap; exact Hopened.
  - apply view_declaration_capability.
  - apply view_capability_rec.
  - apply view_capability_bounds; intros z; apply exact_subtype_refl.
Qed.

Local Lemma interface_bounds_field_weaken F e d a L U L' U' :
    interface_bounds F e d (dec_fld a L U) ->
    exact_subtype F e L' L -> exact_subtype F e U U' ->
    interface_bounds F e d (dec_fld a L' U').
Proof.
  destruct d as [al A B | fl A B | ml C Z T].
  - destruct al; contradiction.
  - simpl. intros (Hlabel & Hlower & Hupper) Hlow Hup.
    split; [exact Hlabel | split]; eapply exact_subtype_trans; eassumption.
  - contradiction.
Qed.

Local Lemma interface_bounds_member_weaken F e d a L U L' U' :
    interface_bounds F e d (dec_typ (typ_label_normal a) L U) ->
    (forall z, exact_subtype F e (open z L') (open z L)) ->
    (forall z, exact_subtype F e (open z U) (open z U')) ->
    interface_bounds F e d (dec_typ (typ_label_normal a) L' U').
Proof.
  destruct d as [al A B | fl A B | ml C Z T].
  - destruct al; [| contradiction]. simpl.
    intros (Hlabel & Hlower & Hupper) Hlow Hup.
    split; [exact Hlabel | split]; intros z.
    + eapply exact_subtype_trans; [apply Hlow | apply Hlower].
    + eapply exact_subtype_trans; [apply Hupper | apply Hup].
  - contradiction.
  - contradiction.
Qed.

Local Lemma interface_bounds_method_weaken F e d m C Z R C' Z' R' :
    interface_bounds F e d (dec_met m C Z R) ->
    method_type_bounds F e C Z R C' Z' R' ->
    interface_bounds F e d (dec_met m C' Z' R').
Proof.
  destruct d as [a ? ? | ? ? ? | ? ? ? ?]; try destruct a; try contradiction.
  intros [Hlabel Hbounds] Hweaken. split; [exact Hlabel |].
  eapply method_type_bounds_trans; eassumption.
Qed.

Local Lemma view_of_intersection F e x R B v A C :
    object_has_view F e x R B v (typ_and A C) ->
    object_has_view F e x R B v A /\ object_has_view F e x R B v C.
Proof. intros H. inversion H; subst; auto. Qed.

Local Lemma view_of_union F e x R B v A C :
    object_has_view F e x R B v (typ_or A C) ->
    object_has_view F e x R B v A \/ object_has_view F e x R B v C.
Proof. intros H. inversion H; subst; auto. Qed.

Local Lemma view_of_capability F e x R B L U :
    object_has_view F e x R B capability_view (typ_rcd (dec_typ typ_label_mutability L U)) ->
    (forall z, exact_subtype F e (open z L) typ_bot) /\
    (forall z, exact_subtype F e (open z B) (open z U)).
Proof. intros H. inversion H; subst; auto. Qed.

Local Lemma view_of_normal_declaration F e x R B a L U :
    object_has_view F e x R B declaration_view (typ_rcd (dec_typ (typ_label_normal a) L U)) ->
    exists C D,
      record_has (open (canonical_location e x) R) (dec_typ (typ_label_normal a) C D) /\
      (forall z, exact_subtype F e (open z L) (open z C)) /\
      (forall z, exact_subtype F e (open z D) (open z U)).
Proof.
  intros H. inversion H; subst.
  destruct actual as [lbl C D | fl C D | ml TC TZ TR].
  - destruct lbl; [| contradiction].
    match goal with Hbounds : interface_bounds _ _ _ _ |- _ =>
      destruct Hbounds as [Heq [HL HU]]; subst
    end.
    exists C, D. repeat split; assumption.
  - contradiction.
  - contradiction.
Qed.

Local Lemma view_field_weaken F e x R B v a L U L' U' :
    exact_subtype F e L' L ->
    exact_subtype F e U U' ->
    object_has_view F e x R B v (typ_rcd (dec_fld a L U)) ->
    object_has_view F e x R B v (typ_rcd (dec_fld a L' U')).
Proof.
  intros Hlow Hup Hview. inversion Hview; subst.
  - eapply view_record_declaration; [eassumption |].
    eapply interface_bounds_field_weaken; eassumption.
  - apply view_capability_field.
Qed.

Local Lemma view_member_weaken F e x R B v a L U L' U' :
    (forall z, exact_subtype F e (open z L') (open z L)) ->
    (forall z, exact_subtype F e (open z U) (open z U')) ->
    object_has_view F e x R B v (typ_rcd (dec_typ a L U)) ->
    object_has_view F e x R B v (typ_rcd (dec_typ a L' U')).
Proof.
  intros Hlow Hup Hview. destruct a as [a | []]; destruct v.
  - inversion Hview; subst.
    eapply view_record_declaration; [eassumption |].
    eapply interface_bounds_member_weaken; eassumption.
  - apply view_capability_member.
  - apply view_declaration_capability.
  - destruct (view_of_capability Hview) as [HL HU].
    apply view_capability_bounds; intros z.
    + eapply exact_subtype_trans; [apply Hlow | apply HL].
    + eapply exact_subtype_trans; [apply HU | apply Hup].
Qed.

Local Lemma view_method_weaken F e x R B v m C Z T C' Z' T' :
    method_type_bounds F e C Z T C' Z' T' ->
    object_has_view F e x R B v (typ_rcd (dec_met m C Z T)) ->
    object_has_view F e x R B v (typ_rcd (dec_met m C' Z' T')).
Proof.
  intros Hbounds Hview. inversion Hview; subst.
  - eapply view_record_declaration; [eassumption |].
    eapply interface_bounds_method_weaken; eassumption.
  - apply view_capability_method.
Qed.

Local Lemma view_member_merge F e x R B v a L U L' U' ls :
    record_typ (open (canonical_location e x) R) ls ->
    object_has_view F e x R B v (typ_rcd (dec_typ a L U)) ->
    object_has_view F e x R B v (typ_rcd (dec_typ a L' U')) ->
    object_has_view F e x R B v
      (typ_rcd (dec_typ a (typ_or L L') (typ_and U U'))).
Proof.
  intros Hrecord H1 H2. destruct a as [a | []]; destruct v.
  - destruct (view_of_normal_declaration H1) as [P [Q [Hmem [HL HU]]]].
    destruct (view_of_normal_declaration H2) as [P' [Q' [Hmem' [HL' HU']]]].
    pose proof (record_label_unique Hrecord Hmem Hmem' eq_refl) as Heq.
    inversion Heq; subst P' Q'.
    eapply view_record_declaration; [exact Hmem |].
    simpl. split; [reflexivity | split]; intros z.
    + apply exact_subtype_or; auto.
    + apply exact_subtype_and; auto.
  - apply view_capability_member.
  - apply view_declaration_capability.
  - destruct (view_of_capability H1) as [HL HU].
    destruct (view_of_capability H2) as [HL' HU'].
    apply view_capability_bounds; intros z.
    + apply exact_subtype_or; auto.
    + apply exact_subtype_and; auto.
Qed.

Local Lemma view_select_upper F e H x R B v w a z L U :
    inert F -> heap_correspond F e H ->
    exact_type_declaration F e w a L U ->
    object_has_view F e x R B v (typ_sel (avar_f w) a (avar_f z)) ->
    object_has_view F e x R B v (open z U).
Proof.
  intros Hinert Hheap Hd Hview. inversion Hview; subst.
  match goal with Hactual : exact_type_declaration F e w _ ?low ?high |- _ =>
    let Hbounds := fresh "Hbounds" in
    pose proof (exact_type_declaration_unique Hinert Hheap Hd Hactual) as Hbounds;
    destruct Hbounds as [_ Hu]; rewrite Hu; assumption
  end.
Qed.

Local Lemma view_select_lower F e H x R B v w a z L U :
    inert F -> heap_correspond F e H ->
    exact_type_declaration F e w a L U ->
    object_has_view F e x R B v (open z L) ->
    object_has_view F e x R B v (typ_sel (avar_f w) a (avar_f z)).
Proof.
  intros Hinert Hheap Hd Hview. destruct a as [a | []].
  - pose proof (exact_normal_type_declaration_has_equal_bounds Hinert Hheap Hd) as ->.
    eapply view_normal_selection; eassumption.
  - inversion Hd; subst. inversion Hview.
Qed.

Local Lemma exact_subtype_preserves_view F e H x R B S T :
    inert F -> heap_correspond F e H -> record_type R ->
    exact_subtype F e S T ->
    forall v, object_has_view F e x R B v S -> object_has_view F e x R B v T.
Proof.
  intros Hinert Hheap [ls Hrec] Hsub.
  pose proof (opened_record_typ 0 (canonical_location e x) Hrec) as Hopened.
  induction Hsub; intros v Hview.
  - apply view_top.
  - inversion Hview.
  - exact Hview.
  - auto.
  - exact (proj1 (view_of_intersection Hview)).
  - exact (proj2 (view_of_intersection Hview)).
  - apply view_and; auto.
  - now apply view_or_left.
  - now apply view_or_right.
  - destruct (view_of_union Hview); auto.
  - eapply view_field_weaken; eassumption.
  - eapply view_member_weaken; eassumption.
  - eapply view_select_upper; eassumption.
  - eapply view_select_lower; eassumption.
  - eapply view_method_weaken; eassumption.
  - eapply object_view_respects_equivalence; eassumption.
  - destruct (view_of_intersection Hview) as [Hleft Hright].
    eapply view_member_merge; eassumption.
  - destruct (view_of_intersection Hview) as [HA HBC].
    destruct (view_of_union HBC) as [HB | HC].
    + apply view_or_left, view_and; assumption.
    + apply view_or_right, view_and; assumption.
  - inversion Hview; subst. apply view_capability_rec.
  - inversion Hview; subst. apply view_capability_member.
  - inversion Hview; subst. apply view_capability_field.
  - inversion Hview; subst. apply view_capability_method.
  - destruct v.
    + apply view_or_right, view_declaration_capability.
    + apply view_or_left, view_nocap. intros Hbad.
      destruct typing_mode; simpl in *; discriminate.
  - destruct v.
    + apply view_or_right, view_declaration_capability.
    + destruct (classic (forall z, exact_subtype F e (open z B) typ_bot)) as [HC | HC].
      * apply view_or_right, view_capability_bounds; [intros; apply exact_subtype_refl | exact HC].
      * apply view_or_left, view_nocap. intros _. exact HC.
  - destruct (view_of_intersection Hview) as [Hnocap Hcap].
    inversion Hnocap; subst.
    exfalso.
    match goal with Hfail : mode_has_top_nm_complement typing_mode -> _ |- _ =>
      apply Hfail; [assumption | exact (proj2 (view_of_capability Hcap))]
    end.
  - destruct v.
    + apply view_declaration_capability.
    + apply view_capability_bounds; intros; [apply exact_subtype_refl | apply exact_subtype_top].
Qed.

Local Lemma bound_variable_from_typing F e (x : var) T :
    F ⁏ e ⊢ x ∶ T -> exists A, ctx_binds x A F.
Proof.
  intros H. induction H; eauto.
Qed.

Local Lemma declaration_from_views F e x R B a L U :
    ctx_binds x (typ_objref R (typ_mut_marker B)) F ->
    object_has_view F e x R B declaration_view (typ_rcd (dec_typ a L U)) ->
    object_has_view F e x R B capability_view (typ_rcd (dec_typ a L U)) ->
    exists C D,
      exact_type_declaration F e x a C D /\
      (forall z, exact_subtype F e (open z L) (open z C)) /\
      (forall z, exact_subtype F e (open z D) (open z U)).
Proof.
  intros Hbind Hdecl Hcap. destruct a as [a | []].
  - destruct (view_of_normal_declaration Hdecl) as [C [D [Hmem [HL HU]]]].
    exists C, D. split; [eapply exact_normal_declaration; eassumption | auto].
  - destruct (view_of_capability Hcap) as [HL HU].
    exists typ_bot, B. split; [eapply exact_capability_declaration; eassumption | auto].
Qed.

Local Hint Constructors exact_subtype : exact_subtyping.

Local Lemma variable_views_and_exact_subtypes :
    (forall F Go e x T, ty_var typing_mode F Go e x T ->
      forall H R B, inert F -> heap_correspond F e H ->
        ctx_binds x (typ_objref R (typ_mut_marker B)) F ->
        record_type R ->
        object_has_view F e x R B declaration_view T /\
        object_has_view F e x R B capability_view T) /\
    (forall F Go e S T, subtyp typing_mode F Go e S T ->
      forall H, inert F -> heap_correspond F e H -> exact_subtype F e S T) /\
    (forall F Go e S T, ty_incap typing_mode F Go e S T -> True).
Proof.
  apply ts_mutind; intros.
  all: try solve [exact I | eauto 4 with exact_subtyping
                | pose proof mode_disallows_functions; congruence
                | apply exact_subtype_member; intros; eauto].
  - match goal with
    | Hb : ctx_binds _ T _, Hprecise : ctx_binds _ (typ_objref _ _) _ |- _ =>
        rewrite (context_binding_unique Hb Hprecise)
    end.
    apply views_of_annotation; [assumption |].
    match goal with Hentry : ctx_binds _ (typ_objref R _) _ |- _ =>
      destruct (precise_config_annotation ltac:(eassumption) ltac:(eassumption) Hentry)
        as [R' [B' [ds [Heq [_ [Hind _]]]]]];
      inversion Heq; subst; assumption
    end.
  - match goal with
    | IH : forall H R B, inert _ -> heap_correspond _ _ H -> _,
      Hheap : heap_correspond _ _ ?heap |- _ =>
        destruct (IH heap R B ltac:(eassumption) Hheap ltac:(eassumption) ltac:(eassumption))
          as [Hdecl Hcap]
    end.
    assert (Heq : e ⊢ open x T ≈ open (canonical_location e x) T).
    { eapply independent_type_open_alias;
        [apply variable_equiv_to_location | eassumption | reflexivity]. }
    split; [| apply view_capability_rec].
    eapply view_declaration_rec with (Witness := T).
    + apply type_equiv_reflexive.
    + assumption.
    + eapply incap_identity_respects_equiv; [| exact Heq].
      match goal with Hinc : mode_has_incap typing_mode -> _ |- _ => apply Hinc end.
      destruct typing_mode; simpl in *; discriminate || reflexivity.
    + eapply object_view_respects_equivalence; eassumption.
    + eapply object_view_respects_equivalence; eassumption.
    + eapply object_view_respects_equivalence; eassumption.
  - match goal with
    | IH : forall H R B, inert _ -> heap_correspond _ _ H -> _,
      Hheap : heap_correspond _ _ ?heap |- _ =>
        destruct (IH heap R B ltac:(eassumption) Hheap ltac:(eassumption) ltac:(eassumption))
          as [Hdecl Hcap]
    end.
    assert (Heq : e ⊢ open (canonical_location e x) T ≈ open x T).
    { eapply independent_type_open_alias;
        [apply tyq_var_sym, variable_equiv_to_location | eassumption | reflexivity]. }
    inversion Hdecl; subst.
    split; eapply object_view_respects_equivalence; eassumption.
  - match goal with Hheap : heap_correspond _ _ ?heap |- _ =>
      destruct (H heap R B ltac:(eassumption) Hheap ltac:(eassumption) ltac:(eassumption))
        as [Hshape1 Hcap1];
      destruct (H0 heap R B ltac:(eassumption) Hheap ltac:(eassumption) ltac:(eassumption))
        as [Hshape2 Hcap2]
    end.
    split; apply view_and; assumption.
  - match goal with
    | IH : forall H R B, inert _ -> heap_correspond _ _ H -> _,
      Hheap : heap_correspond _ _ ?heap |- _ =>
        destruct (IH heap R B ltac:(eassumption) Hheap ltac:(eassumption) ltac:(eassumption))
          as [Hdecl Hcap]
    end.
    split; eapply exact_subtype_preserves_view; eauto.
  - split; [apply view_declaration_capability |].
    apply view_capability_bounds; intros; [apply exact_subtype_refl | apply exact_subtype_top].
  - destruct (bound_variable_from_typing o) as [Bound HA].
    destruct (precise_config_annotation ltac:(eassumption) ltac:(eassumption) HA)
      as [R [B [ds [-> [Hrecord _]]]]].
    match goal with
    | IH : forall H R B, inert _ -> heap_correspond _ _ H -> _,
      Hheap : heap_correspond _ _ ?heap |- _ =>
        destruct (IH heap R B ltac:(eassumption) Hheap HA Hrecord) as [Hdecl Hcap]
    end.
    destruct (declaration_from_views HA Hdecl Hcap) as [C [D [Hexact [HL HU]]]].
    eapply exact_subtype_trans; [apply HL | eapply exact_subtype_select_lower; eassumption].
  - destruct (bound_variable_from_typing o) as [Bound HA].
    destruct (precise_config_annotation ltac:(eassumption) ltac:(eassumption) HA)
      as [R [B [ds [-> [Hrecord _]]]]].
    match goal with
    | IH : forall H R B, inert _ -> heap_correspond _ _ H -> _,
      Hheap : heap_correspond _ _ ?heap |- _ =>
        destruct (IH heap R B ltac:(eassumption) Hheap HA Hrecord) as [Hdecl Hcap]
    end.
    destruct (declaration_from_views HA Hdecl Hcap) as [C [D [Hexact [HL HU]]]].
    eapply exact_subtype_trans; [eapply exact_subtype_select_upper; eassumption | apply HU].
  - apply exact_subtype_method.
    + eapply subtyp_met with (L := L); eassumption.
    + split; [assumption | exists L; split; assumption].
  Unshelve. all: eassumption.
Qed.

Local Lemma let_term_typing G e t U :
    G ⁏ e ⊢ t ∶ U ->
    forall p q, t = trm_let p q ->
    exists L A B,
      G ⁏ e ⊢ p ∶ A /\
      (forall x, x \notin L -> G § x / v_let ~ A ⁏ e ⊢ open x q ∶ B) /\
      G ⁏ e ⊢ B <: U.
Proof.
  intros Hty. induction Hty; intros p q Heq; try discriminate.
  - inversion Heq; subst. repeat eexists; eauto using subtyp_refl.
  - destruct (IHHty p q Heq) as [L [A [B [Hp [Hq HB]]]]].
    exists L, A, B. split; [exact Hp |]. split; [exact Hq |].
    eapply subtyp_trans; eassumption.
Qed.

Local Lemma history_in_config C w :
    w \in config_fv C -> w \in fv_config C.
Proof.
  destruct C. cbn.
  do 4 (rewrite in_union; right).
  trivial.
Qed.

Local Lemma carry_config_names F (U : typ) C C' :
    config_fv C' = fv_config C ->
    ty_nothing_fresh_in_config F U C ->
    ty_nothing_fresh_in_config F U C'.
Proof.
  intros Heq [[Hdom Hctx] Htype].
  repeat split; intros w Hw; apply (@history_in_config C' w);
    rewrite Heq; [apply Hdom | apply Hctx | apply Htype]; exact Hw.
Qed.

Local Lemma carry_config_null C C' :
    config_fv C' = fv_config C ->
    has_null (config_fv C) ->
    has_null (config_fv C').
Proof.
  intros Heq [null Hnull].
  exists null. rewrite Heq. now apply (@history_in_config C null).
Qed.

Local Lemma let_push_preservation F t u s S e Lv U :
    execution_config F (trm_let t u ; s ; S ; e ; Lv) U ->
    execution_config F (t ; stack_cons (frame_let u) s ; S ; e ;
                   fv_config (trm_let t u ; s ; S ; e ; Lv)) U.
Proof.
  intros Hcfg. inversion Hcfg; subst.
  match goal with Hty : _ ⁏ _ ⊢ trm_let t u ∶ _ |- _ =>
    destruct (let_term_typing Hty (eq_refl (trm_let t u)))
      as [L [A [B [Ht [Hu HB]]]]]
  end.
  eapply execution_config_intro with (T := A); try eassumption.
  - eapply ty_stack_let with (L := L); [| exact Hu].
    eapply stack_accepts_subtype; eassumption.
  - intros w Hw. change (tfree_stack w (stack_cons (frame_let u) s)) in Hw.
    inversion Hw; subst.
    + match goal with Hk : all_tfree_k_trm F (trm_let t u) v_ref |- _ =>
        apply Hk; now apply tfree_trm_let_r end.
    + match goal with Hk : all_tfree_k_stack F s v_ref |- _ =>
        now apply Hk end.
  - intros w Hw.
    match goal with Hk : all_tfree_k_trm F (trm_let t u) v_ref |- _ =>
      apply Hk; now apply tfree_trm_let_l end.
  - exact (@carry_config_names F U (trm_let t u ; s ; S ; e ; Lv)
             (t ; stack_cons (frame_let u) s ; S ; e ;
               fv_config (trm_let t u ; s ; S ; e ; Lv)) eq_refl ltac:(assumption)).
  - exact (@carry_config_null (trm_let t u ; s ; S ; e ; Lv)
             (t ; stack_cons (frame_let u) s ; S ; e ;
               fv_config (trm_let t u ; s ; S ; e ; Lv)) eq_refl ltac:(assumption)).
  - match goal with Hclosed : config_closed _ |- _ => inversion Hclosed; subst end.
    constructor; [| | assumption].
    + intros n x.
      match goal with Hterm : closed (trm_let t u) |- _ =>
        pose proof (Hterm n x) as Hopen;
        change (trm_let (open_rec n x t) (open_rec (Datatypes.S n) x u)
                  = trm_let t u) in Hopen;
        injection Hopen; intros; assumption
      end.
    + intros n x.
      change (stack_cons (frame_let (open_rec (Datatypes.S n) x u))
                (open_rec n x s) = stack_cons (frame_let u) s).
      match goal with
      | Hterm : closed (trm_let t u), Hstack : closed s |- _ =>
          rewrite (Hstack n x);
          pose proof (Hterm n x) as Hopen;
          change (trm_let (open_rec n x t) (open_rec (Datatypes.S n) x u)
                    = trm_let t u) in Hopen;
          injection Hopen; intros; congruence
      end.
Qed.

Local Lemma binding_in_domain A (S : env A) y i :
    binds y i S -> y \in dom S.
Proof.
  intros Hbind. destruct (classic (y \in dom S)) as [Hdom | Hdom].
  - exact Hdom.
  - exfalso. exact (binds_fresh_inv Hbind Hdom).
Qed.

Local Lemma update_lookup ds ds' a x :
    defs_update ds a x ds' ->
    forall l, get_def l ds' =
      (If label_fld a = l then Some (def_fld a (avar_f x)) else get_def l ds).
Proof.
  intros Hupdate. induction Hupdate; intros l; simpl get_def.
  - change ((If label_fld a = l then Some (def_fld a (avar_f x))
             else get_def l ds) =
            (If label_fld a = l then Some (def_fld a (avar_f x))
             else (If label_fld a = l then Some (def_fld a t)
                   else get_def l ds))).
    destruct (classic (label_fld a = l)) as [Heq | Hneq].
    + repeat rewrite If_l by exact Heq. reflexivity.
    + repeat rewrite If_r by exact Hneq. reflexivity.
  - destruct (classic (label_of d = l)) as [Heq | Hneq].
    + assert (Ha : label_fld a <> l) by congruence.
      rewrite (@If_r _ (label_fld a = l)) by exact Ha.
      now rewrite !(@If_l _ (label_of d = l)) by exact Heq.
    + rewrite !(@If_r _ (label_of d = l)) by exact Hneq. apply IHHupdate.
Qed.

Local Lemma type_updated_field G Go e a u v D :
    G §§ Go ⁏ e ⊢ def_fld a u ∶d D ->
    vis_var typing_mode (G §§& Go) v ->
    (forall T, D = dec_fld a T T -> G §§& Go ⁏ e ⊢ v ∶ T) ->
    G §§ Go ⁏ e ⊢ def_fld a (avar_f v) ∶d D.
Proof.
  intros Hfield Hvis Hval. inversion Hfield; subst.
  apply ty_def_fld; [exact Hvis | now apply Hval].
Qed.

Local Lemma type_updated_defs G Go e ds U :
    G §§ Go ⁏ e ⊢ ds ∶ U ->
    forall ds' a v, defs_update ds a v ds' ->
    vis_var typing_mode (G §§& Go) v ->
    (forall T, record_has U (dec_fld a T T) -> G §§& Go ⁏ e ⊢ v ∶ T) ->
    G §§ Go ⁏ e ⊢ ds' ∶ U.
Proof.
  intros Hty. induction Hty; intros ds' a v Hupdate Hvis Hvalue;
    inversion Hupdate; subst.
  - apply ty_defs_one. eapply type_updated_field; [eassumption | exact Hvis |].
    intros T ->. apply Hvalue. apply rh_one.
  - match goal with H : defs_update defs_nil _ _ _ |- _ => inversion H end.
  - eapply ty_defs_cons; [eassumption | | eassumption].
    eapply type_updated_field; [eassumption | exact Hvis |].
    intros R ->. apply Hvalue. apply rh_andr. apply rh_one.
  - eapply ty_defs_cons; [| eassumption |].
    + eapply IHHty; [eassumption | exact Hvis |].
      intros R Hmember. apply Hvalue. now apply rh_andl.
    + unfold defs_hasnt in *.
      match goal with
      | Hup : defs_update _ a v _, Hneq : label_of _ <> label_fld a |- _ =>
          rewrite (update_lookup Hup); rewrite If_r by congruence; assumption
      end.
Qed.

Local Lemma kind_bound_visible G v k :
    ctx_k G v k -> ctx_vis G v.
Proof.
  intros [T [G0 Hk]]. induction Hk.
  - apply ctx_vis_e.
  - now apply ctx_vis_n.
Qed.

Local Lemma updated_defs_keep_kinds G ds ds' a v :
    defs_update ds a v ds' ->
    defs_varkinds G ds ->
    ctx_k G v v_loc ->
    defs_varkinds G ds'.
Proof.
  intros Hup. induction Hup; intros Hk Hv; inversion Hk; subst.
  - apply defs_varkinds_cons; [assumption | now apply def_varkinds_fld].
  - apply defs_varkinds_cons; [now apply IHHup | assumption].
Qed.

Local Lemma updated_defs_keep_closed ds ds' a v :
    defs_update ds a v ds' ->
    closed ds ->
    closed ds'.
Proof.
  intros Hup. induction Hup as [ds a t v | ds d a v ds' Hup IH Hneq];
    intros Hclosed n x.
  - change (defs_cons (open_rec n x ds) (def_fld a (avar_f v)) =
            defs_cons ds (def_fld a (avar_f v))).
    pose proof (Hclosed n x) as Hopen.
    change (defs_cons (open_rec n x ds) (open_rec n x (def_fld a t)) =
            defs_cons ds (def_fld a t)) in Hopen.
    injection Hopen; intros; congruence.
  - assert (Hds : closed ds).
    { intros k z. pose proof (Hclosed k z) as Hopen.
      change (defs_cons (open_rec k z ds) (open_rec k z d) = defs_cons ds d)
        in Hopen.
      injection Hopen; intros; assumption. }
    change (defs_cons (open_rec n x ds') (open_rec n x d) = defs_cons ds' d).
    rewrite (IH Hds n x).
    pose proof (Hclosed n x) as Hopen.
    change (defs_cons (open_rec n x ds) (open_rec n x d) = defs_cons ds d)
      in Hopen.
    injection Hopen; intros; congruence.
Qed.

Local Lemma bound_heap_item_closed S y i :
    heap_closed S -> binds y i S -> closed i.
Proof.
  intros Hclosed. induction Hclosed; intros Hbind.
  - exfalso. eapply binds_empty_inv; exact Hbind.
  - apply binds_push_inv in Hbind as [[_ ->] | [_ Hbind]]; auto.
Qed.

Local Lemma heap_closed_by_bindings S :
    ok S ->
    (forall y i, binds y i S -> closed i) ->
    heap_closed S.
Proof.
  induction S as [| E x v IH] using env_ind; intros Hok Hclosed.
  - apply heap_closed_empty.
  - destruct (ok_push_inv Hok) as [Hok' Hfresh].
    apply heap_closed_push.
    + apply IH; [exact Hok' |].
      intros y i Hbind. eapply Hclosed. apply binds_push_neq; [exact Hbind |].
      intros ->. exact (binds_fresh_inv Hbind Hfresh).
    + eapply Hclosed. apply binds_push_eq.
Qed.

Local Lemma updated_heap_stays_closed S S' yObj a yArg :
    heap_closed S ->
    heap_update S yObj a yArg S' ->
    heap_closed S'.
Proof.
  intros Hclosed (_ & Hok' & Hdom & Hsame & ds & ds' & Hbind0 & Hupd & Hbind1).
  apply heap_closed_by_bindings; [exact Hok' |].
  intros y i Hbind.
  destruct (classic (y = yObj)) as [-> | Hneq].
  - pose proof (binds_functional Hbind Hbind1) as ->.
    assert (Hds : closed ds).
    { intros n x. pose proof (bound_heap_item_closed Hclosed Hbind0 n x) as Hopen.
      change (item_obj (open_rec n x ds) = item_obj ds) in Hopen.
      now injection Hopen. }
    intros n x. change (item_obj (open_rec n x ds') = item_obj ds').
    now rewrite (updated_defs_keep_closed Hupd Hds n x).
  - pose proof (binding_in_domain Hbind) as Hin.
    rewrite <- Hdom in Hin. destruct (get_some Hin) as [i0 Hi0].
    change (binds y i0 S) in Hi0.
    pose proof (binds_functional (Hsame _ _ Hneq Hi0) Hbind) as <-.
    eapply bound_heap_item_closed; eassumption.
Qed.

Local Lemma heap_correspondence_after_update G e S S' yObj a yArg :
    heap_correspond G e S ->
    heap_update S yObj a yArg S' ->
    ctx_k G yArg v_loc ->
    (forall U M T,
      ctx_binds yObj (typ_objref U M) G ->
      record_has (open yObj U) (dec_fld a T T) ->
      G ⁏ e ⊢ yArg ∶ T) ->
    heap_correspond G e S'.
Proof.
  intros (Hctx & Hweak & Hok & Heok & Hloc & Href & Henv & Hitems)
    (_ & Hok' & Hdom & Hsame & ds0 & ds1 & Hbind0 & Hupdate & Hbind1)
    Hkind Harg.
  split; [exact Hctx |]. split; [exact Hweak |].
  split; [exact Hok' |]. split; [exact Heok |].
  split; [congruence |]. split; [exact Href |].
  split; [exact Henv |].
  intros y Hy. rewrite <- Hdom in Hy.
  specialize (Hitems y Hy).
  inversion Hitems; subst.
  - pose proof mode_disallows_functions. congruence.
  - destruct (classic (y = yObj)) as [-> | Hneq].
    + match goal with Hbind : binds yObj (item_obj _) S |- _ =>
        let Heq := fresh "Heq" in
        pose proof (binds_functional Hbind0 Hbind) as Heq;
        inversion Heq; subst
      end.
      eapply ty_item_obj_s; [eassumption | exact Hbind1 | reflexivity | |].
      * eapply type_updated_defs; [eassumption | exact Hupdate | |].
        -- intro. now apply (kind_bound_visible Hkind).
        -- intros R HR. eapply Harg; eassumption.
      * eapply updated_defs_keep_kinds; eassumption.
    + eapply ty_item_obj_s; [eassumption | apply Hsame; eassumption |
        reflexivity | eassumption | eassumption].
Qed.

Local Lemma write_preservation_with_field_typing F s S S' e Lv wObj wArg a yObj yArg U :
    execution_config F (trm_write (avar_f wObj) a (avar_f wArg) ; s ; S ; e ; Lv) U ->
    heap_update S yObj a yArg S' ->
    binds wArg yArg e ->
    (forall T,
      F ⁏ e ⊢ trm_write (avar_f wObj) a (avar_f wArg) ∶ T ->
      F ⁏ e ⊢ trm_var (avar_f wArg) ∶ T) ->
    (forall A M T,
      ctx_binds yObj (typ_objref A M) F ->
      record_has (open yObj A) (dec_fld a T T) ->
      F ⁏ e ⊢ yArg ∶ T) ->
    execution_config F (trm_var (avar_f wArg) ; s ; S' ; e ;
                   fv_config (trm_write (avar_f wObj) a (avar_f wArg) ; s ; S ; e ; Lv)) U.
Proof.
  intros Hcfg Hup Hbind Hret Hfld.
  inversion Hcfg; subst.
  assert (Hkind : ctx_k F yArg v_loc).
  { match goal with Hcorr : heap_correspond F e S |- _ =>
      destruct Hcorr as (Hok & _ & _ & _ & _ & _ & Henv & _);
      destruct (reference_location_annotations Hok Henv Hbind)
        as [A [B [Gw [Gy [_ Hy]]]]];
      exists (typ_objref A (typ_mut_marker typ_bot)), Gy; exact Hy
    end. }
  eapply execution_config_intro with (T := T); try eassumption.
  - eapply heap_correspondence_after_update; eassumption.
  - apply Hret; assumption.
  - intros w Hw. change (tfree_trm w (trm_var (avar_f wArg))) in Hw.
    inversion Hw; subst.
    match goal with Hfree : all_tfree_k_trm F (trm_write _ _ _) v_ref |- _ =>
      apply Hfree; apply tfree_trm_write_r
    end.
  - exact (@carry_config_names F U
             (trm_write (avar_f wObj) a (avar_f wArg) ; s ; S ; e ; Lv)
             (trm_var (avar_f wArg) ; s ; S' ; e ;
               fv_config (trm_write (avar_f wObj) a (avar_f wArg) ; s ; S ; e ; Lv))
             eq_refl ltac:(assumption)).
  - exact (@carry_config_null
             (trm_write (avar_f wObj) a (avar_f wArg) ; s ; S ; e ; Lv)
             (trm_var (avar_f wArg) ; s ; S' ; e ;
               fv_config (trm_write (avar_f wObj) a (avar_f wArg) ; s ; S ; e ; Lv))
             eq_refl ltac:(assumption)).
  - match goal with Hclosed : config_closed _ |- _ => inversion Hclosed; subst end.
    constructor; [intros n x; reflexivity | assumption |].
    eapply updated_heap_stays_closed; eassumption.
Qed.

Local Lemma write_field_origin S S' yObj a yArg y ds l z :
    heap_update S yObj a yArg S' ->
    binds y (item_obj ds) S' ->
    defs_has ds (def_fld l (avar_f z)) ->
    (y = yObj /\ l = a /\ z = yArg) \/
    exists ds0, binds y (item_obj ds0) S /\
      defs_has ds0 (def_fld l (avar_f z)).
Proof.
  intros (_ & _ & Hdom & Hsame & ds0 & ds1 & Hbind0 & Hdefs & Hbind1)
    Hbind Hfield.
  destruct (classic (y = yObj)) as [-> | Hneq].
  - pose proof (binds_functional Hbind Hbind1) as Heq.
    inversion Heq; subst ds1.
    unfold defs_has in Hfield.
    rewrite (update_lookup Hdefs) in Hfield.
    change ((If label_fld a = label_fld l then Some (def_fld a (avar_f yArg))
              else get_def (label_fld l) ds0) = Some (def_fld l (avar_f z))) in Hfield.
    destruct (classic (label_fld a = label_fld l)) as [Heq' | Hneq].
    + rewrite If_l in Hfield by exact Heq'. inversion Hfield; subst. auto.
    + rewrite If_r in Hfield by exact Hneq. right. now exists ds0.
  - right. pose proof (binding_in_domain Hbind) as Hin.
    rewrite <- Hdom in Hin.
    destruct (get_some Hin) as [i Hi].
    change (binds y i S) in Hi.
    pose proof (binds_functional (Hsame _ _ Hneq Hi) Hbind) as ->.
    now exists ds.
Qed.

Local Lemma reachability_write F s S S' e Lv Lv' wObj wArg a yObj yArg y :
    heap_update S yObj a yArg S' ->
    binds wArg yArg e ->
    (F ⁏ e ⊢ trm_var (avar_f yObj) ∶ typ_rcd (dec_fld a typ_bot (typ_mut_marker typ_bot)) ->
      F ⁏ e ⊢ trm_var (avar_f wArg) ∶ typ_mut_marker typ_bot) ->
    F ⊢ (trm_var (avar_f wArg) ; s ; S' ; e ; Lv') mreach y ->
    F ⊢ (trm_write (avar_f wObj) a (avar_f wArg) ; s ; S ; e ; Lv) mreach y.
Proof.
  intros Hupdate Harg Hmutable Hr.
  change (mut_reach typing_mode F (trm_var (avar_f wArg) ; s ; S' ; e ; Lv') y) in Hr.
  remember (trm_var (avar_f wArg) ; s ; S' ; e ; Lv') as C' eqn:Heq.
  induction Hr; inversion Heq; subst.
  - match goal with
    | Hbind : binds ?z (item_obj _) S', Hhas : defs_has _ _ |- _ =>
        destruct (write_field_origin Hupdate Hbind Hhas)
          as [(-> & -> & ->) | [ds0 [Hbind0 Hhas0]]]
    end.
    + eapply mreach_trm with (w := wArg); eauto.
      left. apply tfree_trm_write_r.
    + eapply mreach_fld; eauto.
  - eapply mreach_trm; try eassumption.
    match goal with Hfree : tfree _ _ \/ tfree _ _ |- _ =>
      destruct Hfree as [Hfree | Hfree]; [left | now right];
      inversion Hfree; subst; apply tfree_trm_write_r
    end.
Qed.

Local Lemma original_update_field ds ds' a v :
    defs_update ds a v ds' ->
    exists u, defs_has ds (def_fld a u).
Proof.
  intros Hup. induction Hup.
  - exists t. unfold defs_has. simpl get_def.
    rewrite If_l by reflexivity. reflexivity.
  - destruct IHHup as [u Hu]. exists u.
    unfold defs_has in *. simpl get_def.
    rewrite If_r by exact H. exact Hu.
Qed.

Local Lemma heap_field_annotation F e S y ds a v :
    heap_correspond F e S ->
    binds y (item_obj ds) S ->
    defs_has ds (def_fld a v) ->
    exists R M A,
      ctx_binds y (typ_objref R M) F /\
      record_has (open y R) (dec_fld a A A).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hitems) Hbind Hhas.
  specialize (Hitems y (binding_in_domain Hbind)).
  inversion Hitems; subst.
  - pose proof mode_disallows_functions. congruence.
  - match goal with
    | Hobj : binds y (item_obj ?os) S,
      Hty : F §§ _ ⁏ e ⊢ ?os ∶ _ |- _ =>
        pose proof (binds_functional Hobj Hbind) as Heq;
        inversion Heq; subst;
        destruct (typed_defs_member_record Hty Hhas) as [D [Hmember HD]]
    end.
    inversion HD; subst.
    do 3 eexists. split; eassumption.
Qed.

Local Definition field_bounds_agree_with_declaration F e y a :=
  forall R M A S T,
    ctx_binds y (typ_objref R M) F ->
    record_has (open y R) (dec_fld a A A) ->
    F ⁏ e ⊢ y ∶ typ_rcd (dec_fld a S T) ->
    F ⁏ e ⊢ S <: A /\ F ⁏ e ⊢ A <: T.

Local Lemma field_declaration_gives_bounds F e H y a :
    inert F ->
    heap_correspond F e H ->
    canonical_location e y = y ->
    field_bounds_agree_with_declaration F e y a.
Proof.
  intros Hinert Hheap Hcanonical R M A L U Hbound Hfield Hty.
  destruct (precise_config_annotation Hinert Hheap Hbound)
    as [R' [B [ds [Heq [Hrecord _]]]]].
  inversion Heq; subst R' M.
  destruct (proj1 variable_views_and_exact_subtypes F objctx_empty e y _ Hty H R B
    Hinert Hheap Hbound Hrecord) as [Hview _].
  destruct Hrecord as [ls Hrec].
  pose proof (opened_record_typ 0 (canonical_location e y) Hrec) as Hopened.
  rewrite <- Hcanonical in Hfield at 1.
  destruct (declaration_view_field_bounds Hopened Hfield Hview) as [Hlower Hupper].
  split; eapply exact_subtype_general; eassumption.
Qed.

Local Lemma write_step_with_field_bounds F s S S' e Lv wObj wArg a yObj yArg U :
    execution_config F (trm_write (avar_f wObj) a (avar_f wArg) ; s ; S ; e ; Lv) U ->
    heap_update S yObj a yArg S' ->
    binds wObj yObj e ->
    binds wArg yArg e ->
    field_bounds_agree_with_declaration F e yObj a ->
    let C' := (trm_var (avar_f wArg) ; s ; S' ; e ;
                 fv_config (trm_write (avar_f wObj) a (avar_f wArg) ; s ; S ; e ; Lv)) in
    execution_config F C' U /\
    (forall y, F ⊢ C' mreach y ->
      F ⊢ (trm_write (avar_f wObj) a (avar_f wArg) ; s ; S ; e ; Lv) mreach y).
Proof.
  intros Hcfg Hupdate Hobj Harg Hbounds. cbn zeta.
  assert (Hheap : heap_correspond F e S) by (inversion Hcfg; assumption).
  assert (Hwrite : exists T, F ⁏ e ⊢ trm_write (avar_f wObj) a (avar_f wArg) ∶ T)
    by (inversion Hcfg; eauto).
  pose proof Hheap as (Hok & _ & _ & _ & _ & _ & Henv & _).
  assert (Hdecl : exists R M A, ctx_binds yObj (typ_objref R M) F /\
                            record_has (open yObj R) (dec_fld a A A)).
  { destruct Hupdate as (_ & _ & _ & _ & ds & ds' & Hbind & Hup & _).
    destruct (original_update_field Hup) as [v Hv].
    eapply heap_field_annotation; eassumption. }
  destruct Hdecl as [R [M [A [Hdecl Hfield]]]].
  split.
  - eapply write_preservation_with_field_typing; try eassumption.
    + intros T Hty.
      destruct (write_typing_operands Hty (eq_refl (trm_write (avar_f wObj) a (avar_f wArg))))
        as [L [B [Hvis [Hleft [Hright Hres]]]]].
      pose proof (reference_typing_at_location Hok Henv Hobj Hleft) as Hleft'.
      destruct (Hbounds _ _ _ _ _ Hdecl Hfield Hleft') as [HL HB].
      apply ty_trm_var; [exact Hvis |].
      eapply ty_var_sub; [exact Hright |].
      eapply subtyp_trans; [exact HL |].
      eapply subtyp_trans; eassumption.
    + intros R' M' A' Hdecl' Hfield'.
      destruct Hwrite as [T Hty].
      destruct (write_typing_operands Hty (eq_refl (trm_write (avar_f wObj) a (avar_f wArg))))
        as [L [B [_ [Hleft [Hright _]]]]].
      pose proof (reference_typing_at_location Hok Henv Hobj Hleft) as Hleft'.
      destruct (Hbounds _ _ _ _ _ Hdecl' Hfield' Hleft') as [HL _].
      eapply ty_var_sub; [| exact HL].
      eapply reference_typing_at_location; eassumption.
  - intros y Hr. eapply reachability_write; [exact Hupdate | exact Harg | | exact Hr].
    intros Hcap.
    destruct Hwrite as [T Hty].
    destruct (write_typing_operands Hty (eq_refl (trm_write (avar_f wObj) a (avar_f wArg))))
      as [L [B [Hvis [Hleft [Hright _]]]]].
    pose proof (reference_typing_at_location Hok Henv Hobj Hleft) as Hleft'.
    pose proof (variable_term_typing Hcap (eq_refl (trm_var (avar_f yObj)))) as Hcap'.
    destruct (Hbounds _ _ _ _ _ Hdecl Hfield Hleft') as [HL _].
    destruct (Hbounds _ _ _ _ _ Hdecl Hfield Hcap') as [_ HR].
    apply ty_trm_var; [exact Hvis |].
    eapply ty_var_sub; [exact Hright |].
    eapply subtyp_trans; eassumption.
Qed.

Local Lemma write_step_typing_and_reachability F s S S' e Lv wObj wArg a yObj yArg U :
    execution_config F (trm_write (avar_f wObj) a (avar_f wArg) ; s ; S ; e ; Lv) U ->
    heap_update S yObj a yArg S' ->
    binds wObj yObj e ->
    binds wArg yArg e ->
    let C' := (trm_var (avar_f wArg) ; s ; S' ; e ;
                 fv_config (trm_write (avar_f wObj) a (avar_f wArg) ; s ; S ; e ; Lv)) in
    execution_config F C' U /\
    (forall y, F ⊢ C' mreach y ->
      F ⊢ (trm_write (avar_f wObj) a (avar_f wArg) ; s ; S ; e ; Lv) mreach y).
Proof.
  intros Hcfg Hupdate Hobj Harg.
  eapply write_step_with_field_bounds; try eassumption.
  assert (Hinert : inert F) by (inversion Hcfg; assumption).
  assert (Hheap : heap_correspond F e S) by (inversion Hcfg; assumption).
  eapply field_declaration_gives_bounds; [exact Hinert | exact Hheap |].
  exact (proj2 (environment_binding_canonical_locations Hheap Hobj)).
Qed.

Local Lemma reachability_read F F' s S e Lv Lv' wObj wVal a yObj yVal ds y :
    inert F ->
    binds wObj yObj e ->
    binds yObj (item_obj ds) S ->
    defs_has ds (def_fld a (avar_f yVal)) ->
    (forall w, w <> wVal ->
      F' ⁏ (e & wVal ~ yVal) ⊢ trm_var (avar_f w) ∶ typ_mut_marker typ_bot ->
      F ⁏ e ⊢ trm_var (avar_f w) ∶ typ_mut_marker typ_bot) ->
    (forall x l contents, binds x (item_obj contents) S ->
      F' ⁏ (e & wVal ~ yVal) ⊢ trm_var (avar_f x)
        ∶ typ_rcd (dec_fld l typ_bot (typ_mut_marker typ_bot)) ->
      F ⁏ e ⊢ trm_var (avar_f x)
        ∶ typ_rcd (dec_fld l typ_bot (typ_mut_marker typ_bot))) ->
    (F' ⁏ (e & wVal ~ yVal) ⊢ trm_var (avar_f wVal) ∶ typ_mut_marker typ_bot ->
      F ⁏ e ⊢ trm_var (avar_f wObj) ∶ typ_mut_marker typ_bot /\
      F ⁏ e ⊢ trm_var (avar_f yObj) ∶ typ_rcd (dec_fld a typ_bot (typ_mut_marker typ_bot))) ->
    F' ⊢ (trm_var (avar_f wVal) ; s ; S ; e & wVal ~ yVal ; Lv') mreach y ->
    F ⊢ (trm_read (avar_f wObj) a ; s ; S ; e ; Lv) mreach y.
Proof.
  intros Hinert Hobj Hheap Hhas Hrefs Hfields Hnew Hr.
  change (mut_reach typing_mode F'
    (trm_var (avar_f wVal) ; s ; S ; e & wVal ~ yVal ; Lv') y) in Hr.
  remember (trm_var (avar_f wVal) ; s ; S ; e & wVal ~ yVal ; Lv') as C' eqn:Heq.
  remember F' as post eqn:Hctx in Hr.
  induction Hr; inversion Heq; inversion Hctx; subst.
  - eapply mreach_fld; eauto.
  - match goal with Hbind : binds _ _ (e & wVal ~ yVal) |- _ =>
      apply binds_push_inv in Hbind as [[-> ->] | [Hneq Hbind]]
    end.
    + eapply mreach_fld; try eassumption.
      * eapply mreach_trm with (w := wObj); try eassumption.
        -- left. apply tfree_trm_read.
        -- apply (proj1 (Hnew ltac:(eassumption))).
      * apply (proj2 (Hnew ltac:(eassumption))).
    + eapply mreach_trm; try eassumption.
      * match goal with Hfree : tfree _ _ \/ tfree _ _ |- _ =>
          destruct Hfree as [Hfree | Hfree]; [| now right];
          inversion Hfree; subst; contradiction
        end.
      * eapply Hrefs; eassumption.
Qed.

Local Lemma immutability_step C C' F T y ds :
    binds y (item_obj ds) (config_heap C) ->
    execution_config F C T ->
    C ↦ C' ->
    binds y (item_obj ds) (config_heap C') \/ F ⊢ C mreach y.
Proof.
  intros Hbind Hty Hred.
  destruct Hred; simpl in Hbind |- *; try (left; exact Hbind).
  - destruct H as (_ & _ & _ & Hother & _).
    destruct (classic (y = yObj)) as [-> | Hneq].
    + right. inversion Hty; subst.
      eapply mreach_trm with (w := wObj).
      * eassumption.
      * left. apply tfree_trm_write_l.
      * eassumption.
      * eapply write_receiver_mutable; [eassumption | reflexivity].
    + left. now apply Hother.
  - left. eapply binds_push_neq; [exact Hbind |].
    eapply fresh_heap_binding; eassumption.
  - left. eapply binds_push_neq; [exact Hbind |].
    eapply fresh_heap_binding; eassumption.
Qed.

Local Definition rename_avar (f : var -> var) (a : avar) :=
  match a with
  | avar_b n => avar_b n
  | avar_f x => avar_f (f x)
  end.

Local Notation renaming f := (fun a _ => rename_avar f a).
Local Notation "'rename_typ' f T" := (transform_typ (renaming f) T 0)
  (at level 10, f at level 9, T at level 9, only parsing).
Local Notation "'rename_dec' f D" := (transform_dec (renaming f) D 0)
  (at level 10, f at level 9, D at level 9, only parsing).
Local Notation "'rename_trm' f t" := (transform_trm (renaming f) t 0)
  (at level 10, f at level 9, t at level 9, only parsing).
Local Notation "'rename_lit' f l" := (transform_lit (renaming f) l 0)
  (at level 10, f at level 9, l at level 9, only parsing).
Local Notation "'rename_def' f d" := (transform_def (renaming f) d 0)
  (at level 10, f at level 9, d at level 9, only parsing).
Local Notation "'rename_defs' f ds" := (transform_defs (renaming f) ds 0)
  (at level 10, f at level 9, ds at level 9, only parsing).

Local Lemma rename_type_depth :
    (forall T f n p, transform_typ (renaming f) T n = transform_typ (renaming f) T p) /\
    (forall D f n p, transform_dec (renaming f) D n = transform_dec (renaming f) D p).
Proof.
  apply typ_mutind; intros; simpl; try reflexivity; f_equal; eauto.
Qed.

Local Lemma rename_term_depth :
    (forall t f n p, transform_trm (renaming f) t n = transform_trm (renaming f) t p) /\
    (forall l f n p, transform_lit (renaming f) l n = transform_lit (renaming f) l p) /\
    (forall d f n p, transform_def (renaming f) d n = transform_def (renaming f) d p) /\
    (forall ds f n p, transform_defs (renaming f) ds n = transform_defs (renaming f) ds p).
Proof.
  apply trm_mutind; intros; simpl; try reflexivity; f_equal; eauto using (proj1 rename_type_depth).
Qed.

Local Lemma rename_avar_open (f : var -> var) a n x :
    rename_avar f (open_rec n x a) = open_rec n (f x) (rename_avar f a).
Proof.
  destruct a as [k | x']; [| reflexivity].
  cbn [open_rec AvarOpenable rename_avar].
  destruct (Nat.eq_dec n k).
  - now rewrite !If_l by assumption.
  - now rewrite !If_r by assumption.
Qed.

Local Lemma rename_type_open :
    (forall T f k n x,
      transform_typ (renaming f) (open_rec n x T) k =
      open_rec n (f x) (transform_typ (renaming f) T k)) /\
    (forall D f k n x,
      transform_dec (renaming f) (open_rec n x D) k =
      open_rec n (f x) (transform_dec (renaming f) D k)).
Proof.
  apply typ_mutind; intros;
    cbn [open_rec TypOpenable DecOpenable open_rec_typ open_rec_dec transform_typ transform_dec];
    try reflexivity; f_equal; eauto using rename_avar_open.
Qed.

Local Lemma rename_term_open :
    (forall t f k n x,
      transform_trm (renaming f) (open_rec n x t) k =
      open_rec n (f x) (transform_trm (renaming f) t k)) /\
    (forall l f k n x,
      transform_lit (renaming f) (open_rec n x l) k =
      open_rec n (f x) (transform_lit (renaming f) l k)) /\
    (forall d f k n x,
      transform_def (renaming f) (open_rec n x d) k =
      open_rec n (f x) (transform_def (renaming f) d k)) /\
    (forall ds f k n x,
      transform_defs (renaming f) (open_rec n x ds) k =
      open_rec n (f x) (transform_defs (renaming f) ds k)).
Proof.
  apply trm_mutind; intros;
    cbn [open_rec TrmOpenable LitOpenable DefOpenable DefsOpenable
      open_rec_trm open_rec_lit open_rec_def open_rec_defs
      transform_trm transform_lit transform_def transform_defs transform TypTransform];
    try reflexivity; f_equal; eauto using rename_avar_open, (proj1 rename_type_open).
Qed.

Local Definition names_agree_on (L : vars) (f g : var -> var) :=
  forall x, x \in L -> f x = g x.

Local Lemma names_agree_left F E f g :
    names_agree_on (F \u E) f g -> names_agree_on F f g.
Proof. intros H x Hx. apply H. rewrite in_union. now left. Qed.

Local Lemma names_agree_right F E f g :
    names_agree_on (F \u E) f g -> names_agree_on E f g.
Proof. intros H x Hx. apply H. rewrite in_union. now right. Qed.

Local Lemma rename_avar_congruent f g a :
    names_agree_on (fv a) f g -> rename_avar f a = rename_avar g a.
Proof.
  destruct a as [i | x]; [reflexivity |].
  intros H. change (avar_f (f x) = avar_f (g x)).
  f_equal. apply H. change (x \in \{x}). now rewrite in_singleton.
Qed.

Local Hint Resolve names_agree_left names_agree_right rename_avar_congruent : names.

Local Lemma rename_types_congruent :
    (forall T f g n, names_agree_on (fv T) f g ->
      transform_typ (renaming f) T n = transform_typ (renaming g) T n) /\
    (forall D f g n, names_agree_on (fv D) f g ->
      transform_dec (renaming f) D n = transform_dec (renaming g) D n).
Proof.
  apply typ_mutind; intros;
    cbn [fv TypFreeVar DecFreeVar fv_typ fv_dec transform_typ transform_dec] in *;
    try reflexivity; f_equal; eauto 8 with names.
Qed.

Local Lemma rename_terms_congruent :
    (forall t f g n, names_agree_on (fv t) f g ->
      transform_trm (renaming f) t n = transform_trm (renaming g) t n) /\
    (forall l f g n, names_agree_on (fv l) f g ->
      transform_lit (renaming f) l n = transform_lit (renaming g) l n) /\
    (forall d f g n, names_agree_on (fv d) f g ->
      transform_def (renaming f) d n = transform_def (renaming g) d n) /\
    (forall ds f g n, names_agree_on (fv ds) f g ->
      transform_defs (renaming f) ds n = transform_defs (renaming g) ds n).
Proof.
  apply trm_mutind; intros;
    cbn [fv TrmFreeVar LitFreeVar DefFreeVar DefsFreeVar
      fv_trm fv_lit fv_def fv_defs transform_trm transform_lit transform_def
      transform_defs transform TypTransform] in *;
    try reflexivity; f_equal; eauto 8 using (proj1 rename_types_congruent) with names.
Qed.

Local Lemma rename_avar_identity a :
    rename_avar (fun x => x) a = a.
Proof. now destruct a. Qed.

Local Lemma rename_types_identity :
    (forall T n, transform_typ (renaming (fun x => x)) T n = T) /\
    (forall D n, transform_dec (renaming (fun x => x)) D n = D).
Proof.
  apply typ_mutind; intros; cbn [transform_typ transform_dec];
    try reflexivity; f_equal; eauto using rename_avar_identity.
Qed.

Local Lemma rename_terms_identity :
    (forall t n, transform_trm (renaming (fun x => x)) t n = t) /\
    (forall l n, transform_lit (renaming (fun x => x)) l n = l) /\
    (forall d n, transform_def (renaming (fun x => x)) d n = d) /\
    (forall ds n, transform_defs (renaming (fun x => x)) ds n = ds).
Proof.
  apply trm_mutind; intros;
    cbn [transform_trm transform_lit transform_def transform_defs transform TypTransform];
    try reflexivity; f_equal; eauto using rename_avar_identity, (proj1 rename_types_identity).
Qed.

Local Lemma rename_typ_inactive f T :
    names_agree_on (fv T) f (fun x => x) ->
    rename_typ f T = T.
Proof.
  intros H.
  exact (@Logic.eq_trans _ _ _ _ (proj1 rename_types_congruent T f (fun x => x) 0 H)
                              (proj1 rename_types_identity T 0)).
Qed.

Local Lemma rename_trm_inactive f t :
    names_agree_on (fv t) f (fun x => x) ->
    rename_trm f t = t.
Proof.
  intros H.
  exact (@Logic.eq_trans _ _ _ _ (proj1 rename_terms_congruent t f (fun x => x) 0 H)
                              (proj1 rename_terms_identity t 0)).
Qed.

Local Lemma names_agree_trans L f g h :
    names_agree_on L f g -> names_agree_on L g h -> names_agree_on L f h.
Proof.
  intros Hfg Hgh x Hx. rewrite (Hfg x Hx). now apply Hgh.
Qed.

Local Definition replace_name (f : var -> var) a b x :=
  If x = a then b else f x.

Local Lemma replace_name_at f a b : replace_name f a b a = b.
Proof. unfold replace_name. now rewrite If_l. Qed.

Local Lemma replace_name_away f a b x :
    x <> a -> replace_name f a b x = f x.
Proof. intros H. unfold replace_name. now rewrite If_r. Qed.

Local Lemma replace_name_fresh L f a b :
    a \notin L -> names_agree_on L (replace_name f a b) f.
Proof.
  intros Hfresh x Hx. apply replace_name_away.
  intros ->. contradiction.
Qed.

Local Definition renaming_respects_aliases (f : var -> var) (e e' : renv) :=
  forall x y, binds x y e -> e' ⊢ f x ≈ f y.

Local Lemma rename_variable_equivalence f e e' (x y : var) :
    renaming_respects_aliases f e e' ->
    e ⊢ x ≈ y ->
    e' ⊢ f x ≈ f y.
Proof.
  intros Henv Heq. induction Heq.
  - apply tyq_var_refl.
  - now apply Henv.
  - apply tyq_var_sym; auto.
  - apply tyq_var_trans with (v2 := f v2); auto.
Qed.

Local Lemma renaming_can_open_at f e e' L x :
    renaming_respects_aliases f e e' ->
    exists z g,
      g z = x /\ names_agree_on L g f /\ renaming_respects_aliases g e e'.
Proof.
  intros Hrename.
  destruct (var_fresh (L \u fv_renv e)) as [z Hz].
  rewrite !notin_union in Hz.
  destruct Hz as [HzL [HzDom HzRange]].
  exists z, (replace_name f z x).
  split; [apply replace_name_at |].
  split; [now apply replace_name_fresh |].
  intros u v Hbind.
  rewrite !replace_name_away.
  - now apply Hrename.
  - intros ->.
    pose proof (@fv_in_values_binds var z (@fv var _) u z e Hbind HzRange) as H.
    apply H. change (z \in \{z}); now rewrite in_singleton.
  - intros ->. exact (binds_fresh_inv Hbind HzDom).
Qed.

Local Lemma rename_equivalence_under_open e (T U : typ) n :
    (forall z f e', renaming_respects_aliases f e e' ->
        e' ⊢ rename_typ f (open_rec n z T) ≈ rename_typ f (open_rec n z U)) ->
    forall x f e', renaming_respects_aliases f e e' ->
        e' ⊢ open_rec n x (rename_typ f T) ≈ open_rec n x (rename_typ f U).
Proof.
  intros H x f e' Henv.
  destruct (renaming_can_open_at (fv T \u fv U) x Henv)
    as [z [g [Hmap [Hagree Henv']]]].
  pose proof (H z g e' Henv') as Heq.
  rewrite !(proj1 rename_type_open) in Heq.
  rewrite Hmap in Heq.
  rewrite (proj1 rename_types_congruent T g f 0 (names_agree_left Hagree)) in Heq.
  rewrite (proj1 rename_types_congruent U g f 0 (names_agree_right Hagree)) in Heq.
  exact Heq.
Qed.

Local Lemma rename_equivalence_under_two_opens e (T U : typ) :
    (forall z w f e', renaming_respects_aliases f e e' ->
        e' ⊢ rename_typ f (open_met z w T) ≈ rename_typ f (open_met z w U)) ->
    forall x y f e', renaming_respects_aliases f e e' ->
        e' ⊢ open_met x y (rename_typ f T) ≈ open_met x y (rename_typ f U).
Proof.
  intros H x y f e' Henv.
  destruct (renaming_can_open_at (fv T \u fv U) y Henv)
    as [w [g [Hy [Hagree Henv']]]].
  destruct (renaming_can_open_at ((fv T \u fv U) \u \{w}) x Henv')
    as [z [h [Hx [Hagree' Henv'']]]].
  assert (Hw : h w = y).
  { rewrite <- Hy. apply (names_agree_right Hagree').
    now rewrite in_singleton. }
  pose proof (H z w h e' Henv'') as Heq.
  rewrite !(proj1 rename_type_open), Hx, Hw in Heq.
  pose proof (names_agree_trans (names_agree_left Hagree') Hagree) as Hsame.
  rewrite (proj1 rename_types_congruent T h f 0 (names_agree_left Hsame)) in Heq.
  rewrite (proj1 rename_types_congruent U h f 0 (names_agree_right Hsame)) in Heq.
  exact Heq.
Qed.

Local Lemma rename_equivalence e (T U : typ) :
    e ⊢ T ≈ U ->
    forall f e', renaming_respects_aliases f e e' ->
    e' ⊢ rename_typ f T ≈ rename_typ f U.
Proof.
  intros H. induction H; intros f e' Henv.
  - inversion H; subst; apply tyq_typ_nulary; constructor.
  - inversion H; subst; apply tyq_typ_andor; try constructor; auto.
  - cbn [transform_typ].
    repeat rewrite ((proj1 rename_type_depth) _ f 1 0).
    apply tyq_typ_fun; [auto |].
    intros x. eapply rename_equivalence_under_open; eauto.
  - apply tyq_typ_fld; auto.
  - cbn [transform_typ transform_dec].
    repeat rewrite ((proj1 rename_type_depth) _ f 1 0).
    apply tyq_typ_typ; intros x; eapply rename_equivalence_under_open; eauto.
  - apply tyq_typ_sel_normal. eapply rename_variable_equivalence; eassumption.
  - apply tyq_typ_sel.
  - cbn [transform_typ].
    repeat rewrite ((proj1 rename_type_depth) _ f 1 0).
    apply tyq_typ_bnd. intros x. eapply rename_equivalence_under_open; eauto.
  - cbn [transform_typ transform_dec].
    repeat rewrite ((proj1 rename_type_depth) _ f 1 0).
    repeat rewrite ((proj1 rename_type_depth) _ f 2 0).
    apply tyq_typ_met.
    + intros x. eapply rename_equivalence_under_open; eauto.
    + auto.
    + intros x y. eapply rename_equivalence_under_two_opens; eauto.
Qed.

Local Lemma rename_avar_differs_from_bound f a n :
    avar_b n <> a -> avar_b n <> rename_avar f a.
Proof. destruct a; simpl; congruence. Qed.

Local Hint Constructors typ_indep : renaming_independence.
Local Hint Resolve rename_avar_differs_from_bound : renaming_independence.

Local Lemma renaming_preserves_independence T v :
    typ_indep v T ->
    forall f n k, v = avar_b n ->
      typ_indep_b n (transform_typ (renaming f) T k).
Proof.
  intros H. induction H; intros f n' k Heq; inversion Heq; subst;
    cbn [transform_typ transform_dec];
    try solve [eauto 6 with renaming_independence].
  inversion H; subst; apply typ_indep_nulary; constructor.
Qed.

Local Lemma rename_bound_difference f a n :
    avar_b n <> rename_avar f a -> avar_b n <> a.
Proof. intros H Heq. subst a. apply H; reflexivity. Qed.

Local Hint Resolve rename_bound_difference : renaming_independence.

Local Lemma renaming_reflects_independence :
    (forall T f n k, typ_indep_b n (transform_typ (renaming f) T k) -> typ_indep_b n T) /\
    (forall D f n k, typ_indep_b n (typ_rcd (transform_dec (renaming f) D k)) ->
                     typ_indep_b n (typ_rcd D)).
Proof.
  apply typ_mutind; intros;
    match goal with H : typ_indep _ _ |- _ =>
      cbn [transform_typ transform_dec] in H;
      first [solve [eauto using typ_indep_nulary, typ_nulary_top, typ_nulary_bot,
                      typ_nulary_nocap]
           | solve [eauto]
           | inversion H; subst; try solve [eauto 6 with renaming_independence]]
    end.
  all: match goal with H : typ_nulary _ |- _ => inversion H end.
Qed.

Local Definition renaming_fixes_outside (L : vars) (f : var -> var) :=
  forall x, x \notin L -> f x = x.

Local Lemma replace_name_fixes_outside L f a b :
    renaming_fixes_outside L f ->
    renaming_fixes_outside (L \u \{a}) (replace_name f a b).
Proof.
  intros H x Hx. rewrite notin_union, notin_singleton in Hx.
  destruct Hx as [HL Hxa]. rewrite replace_name_away by exact Hxa.
  now apply H.
Qed.

Local Definition renamed_bindings (f : var -> var) G G' e :=
  forall x T, ctx_binds x T G -> G' ⁏ e ⊢ f x ∶ rename_typ f T.

Local Lemma renamed_bindings_push f G G' e x k T :
    f x §# G' ->
    renamed_bindings f G G' e ->
    renamed_bindings f (G § x / k ~ T) (G' § f x / k ~ rename_typ f T) e.
Proof.
  intros Hfresh Hbind y U Hlookup. inversion Hlookup; subst.
  - apply ty_var_var. apply ctx_binds_e.
  - apply (proj1 weaken_core_typing G' objctx_empty e (f y) (rename_typ f U)).
    + eapply Hbind; eassumption.
    + now apply fresh_context_extension.
Qed.

Local Lemma renamed_bindings_hide f G G' e :
    renamed_bindings f G G' e ->
    renamed_bindings f (ctx_hide G) (ctx_hide G') e.
Proof.
  intros Hbind x T Hlookup. inversion Hlookup; subst.
  assert (Hx : G' ⁏ e ⊢ f x ∶ rename_typ f T) by (eapply Hbind; eassumption).
  exact (proj1 weaken_core_typing _ _ _ _ _ Hx (ctx_hide G')
           ltac:(intros y U H; now apply ctx_binds_hide)).
Qed.

Local Lemma renamed_bindings_push_fixed f G G' e x k T :
    f x = x ->
    x §# G' ->
    renamed_bindings f G G' e ->
    renamed_bindings f (G § x / k ~ T) (G' § x / k ~ rename_typ f T) e.
Proof.
  intros Hx Hfresh Hctx.
  assert (Hfx : f x §# G') by now rewrite Hx.
  pose proof (@renamed_bindings_push f G G' e x k T Hfx Hctx) as Hnew.
  now rewrite Hx in Hnew.
Qed.

Local Lemma renaming_fresh_binder f L K G x :
    renaming_fixes_outside K f ->
    x \notin L \u (K \u ctx_dom G) ->
    x \notin L /\ f x = x /\ x §# G.
Proof.
  intros Hfix Hx. rewrite !notin_union in Hx.
  destruct Hx as [H1 [H2 H3]]. auto.
Qed.

Local Lemma bound_type_free_in_context G x T :
    ctx_binds x T G ->
    forall y, y \in fv T -> y \in ctx_fv G.
Proof.
  intros H. induction H; intros y Hy; cbn [ctx_collect_values].
  - rewrite in_union. now left.
  - rewrite in_union. auto.
  - auto.
Qed.

Local Lemma renamed_bindings_agree f g G G' e :
    names_agree_on (ctx_dom G \u ctx_fv G) g f ->
    renamed_bindings f G G' e ->
    renamed_bindings g G G' e.
Proof.
  intros Hagree Hbind x T Hlookup.
  assert (Hx : g x = f x).
  { apply (names_agree_left Hagree). eapply context_binding_in_domain; eassumption. }
  assert (HT : rename_typ g T = rename_typ f T).
  { apply (proj1 rename_types_congruent).
    intros y Hy. apply (names_agree_right Hagree).
    eapply bound_type_free_in_context; eassumption. }
  rewrite Hx, HT. now apply Hbind.
Qed.

Local Lemma replace_name_respects_aliases f e e' z x :
    z \notin fv_renv e ->
    renaming_respects_aliases f e e' ->
    renaming_respects_aliases (replace_name f z x) e e'.
Proof.
  intros Hz Henv u v Hbind.
  rewrite notin_union in Hz. destruct Hz as [HzDom HzRange].
  rewrite !replace_name_away.
  - now apply Henv.
  - intros ->.
    pose proof (@fv_in_values_binds var z (@fv var _) u z e Hbind HzRange) as H.
    apply H. change (z \in \{z}); now rewrite in_singleton.
  - intros ->. exact (binds_fresh_inv Hbind HzDom).
Qed.

Local Lemma renamed_subtyping_under_open G e (T U : typ) :
    (forall x f L G' e',
        renaming_fixes_outside L f ->
        renaming_respects_aliases f e e' ->
        renamed_bindings f G G' e' ->
        G' ⁏ e' ⊢ rename_typ f (open x T) <: rename_typ f (open x U)) ->
    forall x f L G' e',
      renaming_fixes_outside L f ->
      renaming_respects_aliases f e e' ->
      renamed_bindings f G G' e' ->
      G' ⁏ e' ⊢ open x (rename_typ f T) <: open x (rename_typ f U).
Proof.
  intros H x f L G' e' Hfix Henv Hbind.
  destruct (var_fresh ((fv T \u fv U) \u ((ctx_dom G \u ctx_fv G) \u fv_renv e)))
    as [z Hz].
  apply notin_union in Hz as [HzTypes Hz].
  apply notin_union in Hz as [HzCtx HzEnv].
  set (g := replace_name f z x).
  assert (Hsame : names_agree_on (fv T \u fv U) g f) by now apply replace_name_fresh.
  pose proof (H z g (L \u \{z}) G' e'
    (@replace_name_fixes_outside L f z x Hfix)
    (@replace_name_respects_aliases f e e' z x HzEnv Henv)
    (@renamed_bindings_agree f g G G' e'
      (@replace_name_fresh (ctx_dom G \u ctx_fv G) f z x HzCtx) Hbind)) as Hsub.
  rewrite !(proj1 rename_type_open) in Hsub.
  assert (Hzmap : g z = x) by apply replace_name_at.
  rewrite Hzmap in Hsub.
  rewrite (proj1 rename_types_congruent T g f 0 (names_agree_left Hsame)) in Hsub.
  rewrite (proj1 rename_types_congruent U g f 0 (names_agree_right Hsame)) in Hsub.
  exact Hsub.
Qed.

Local Lemma rename_typ_at_zero f T n :
    transform_typ (renaming f) T (S n) = rename_typ f T.
Proof. apply (proj1 rename_type_depth). Qed.

Local Lemma rename_trm_at_zero f t n :
    transform_trm (renaming f) t (S n) = rename_trm f t.
Proof. apply (proj1 rename_term_depth). Qed.

Local Lemma rename_lit_at_zero f l n :
    transform_lit (renaming f) l (S n) = rename_lit f l.
Proof. apply (proj1 (proj2 rename_term_depth)). Qed.

Local Lemma rename_defs_at_zero f ds n :
    transform_defs (renaming f) ds (S n) = rename_defs f ds.
Proof. apply (proj2 (proj2 (proj2 rename_term_depth))). Qed.

Local Lemma rename_typ_opens f T n x :
    rename_typ f (open_rec n x T) = open_rec n (f x) (rename_typ f T).
Proof. apply (proj1 rename_type_open). Qed.

Local Lemma rename_trm_opens f t n x :
    rename_trm f (open_rec n x t) = open_rec n (f x) (rename_trm f t).
Proof. apply (proj1 rename_term_open). Qed.

Local Lemma rename_defs_open f ds n x :
    rename_defs f (open_rec n x ds) = open_rec n (f x) (rename_defs f ds).
Proof. apply (proj2 (proj2 (proj2 rename_term_open))). Qed.

Local Hint Rewrite rename_typ_at_zero rename_trm_at_zero rename_lit_at_zero rename_defs_at_zero
  rename_typ_opens rename_trm_opens rename_defs_open : rename_syntax.

Local Ltac normalize_renamed_syntax :=
  cbn [transform_typ transform_dec transform_trm transform_lit transform_def transform_defs
       transform TypTransform rename_avar];
  autorewrite with rename_syntax.

Local Ltac normalize_renamed_in H :=
  cbn [transform_typ transform_dec transform_trm transform_lit transform_def transform_defs
       transform TypTransform rename_avar] in H;
  autorewrite with rename_syntax in H.

Local Hint Resolve renamed_bindings_push rename_equivalence renaming_preserves_independence
  renamed_subtyping_under_open : renamed_core.
Local Hint Constructors ty_var subtyp ty_incap : renamed_core.

Local Lemma core_typing_renaming :
    (forall G Go e x T, ty_var typing_mode G Go e x T ->
      forall f L G' e', renaming_fixes_outside L f ->
        renaming_respects_aliases f e e' -> renamed_bindings f G G' e' ->
        G' ⁏ e' ⊢ f x ∶ rename_typ f T) /\
    (forall G Go e T U, subtyp typing_mode G Go e T U ->
      forall f L G' e', renaming_fixes_outside L f ->
        renaming_respects_aliases f e e' -> renamed_bindings f G G' e' ->
        G' ⁏ e' ⊢ rename_typ f T <: rename_typ f U) /\
    (forall G Go e T U, ty_incap typing_mode G Go e T U ->
      forall f L G' e', renaming_fixes_outside L f ->
        renaming_respects_aliases f e e' -> renamed_bindings f G G' e' ->
        G' ⁏ e' ⊢ rename_typ f T ∶icp rename_typ f U).
Proof.
  apply ts_mutind; intros.
  all: normalize_renamed_syntax.
  all: try solve [eauto 4 with renamed_core |
                  pose proof mode_disallows_functions; congruence].
  - apply ty_rec_intro.
    + rewrite <- rename_typ_opens. eauto.
    + eapply renaming_preserves_independence; [eassumption | reflexivity].
    + intros Hmode. rewrite <- rename_typ_opens. eauto.
  - apply ty_rec_elim.
    + pose proof (H f L G' e' H0 H1 H2) as Hrec.
      normalize_renamed_in Hrec. exact Hrec.
    + eapply renaming_preserves_independence; [eassumption | reflexivity].
  - eapply subtyp_sel2 with (S := rename_typ f S) (T := rename_typ f T).
    pose proof (H f L G' e' ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hsel.
    normalize_renamed_in Hsel. exact Hsel.
  - eapply subtyp_sel1 with (S := rename_typ f S) (T := rename_typ f T).
    pose proof (H f L G' e' ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hsel.
    normalize_renamed_in Hsel. exact Hsel.
  - eapply subtyp_met with (L := L \u (L0 \u ctx_dom G')); [eauto | | |].
    + intros z Hz.
      destruct (@renaming_fresh_binder f L L0 G' z ltac:(assumption) Hz)
        as [HzL [Hfz HzG]].
      assert (HZ : renamed_bindings f (G § z / v_par ~ TZ2)
        (G' § z / v_par ~ rename_typ f TZ2) e').
      { now apply renamed_bindings_push_fixed. }
      match goal with
      | IH : forall x, x \notin L -> forall f L G' e', _ |- _ =>
          pose proof (IH z HzL f L0 _ e' ltac:(assumption) ltac:(assumption) HZ) as Hsub
      end.
      rewrite !rename_typ_opens, Hfz in Hsub. exact Hsub.
    + intros Hmode HT. eapply renaming_preserves_independence; [| reflexivity].
      match goal with Hind : _ -> typ_indep_b 0 TC2 -> typ_indep_b 0 TC1 |- _ =>
        apply Hind; [exact Hmode |]
      end.
      eapply (proj1 renaming_reflects_independence); exact HT.
    + intros z Hz c Hneq Hc.
      destruct (@renaming_fresh_binder f L L0 G' z ltac:(assumption) Hz)
        as [HzL [Hfz HzG]].
      destruct (@renaming_fresh_binder f L L0 G' c ltac:(assumption) Hc)
        as [HcL [Hfc HcG]].
      assert (HZ : renamed_bindings f (G § z / v_par ~ TZ2)
        (G' § z / v_par ~ rename_typ f TZ2) e').
      { now apply renamed_bindings_push_fixed. }
      assert (HC : renamed_bindings f (ctx_met G z TZ2 c TC2)
        (ctx_met G' z (rename_typ f TZ2) c (rename_typ f TC2)) e').
      { replace (open z (rename_typ f TC2)) with (rename_typ f (open z TC2))
          by now rewrite rename_typ_opens, Hfz.
        apply renamed_bindings_push_fixed;
          [exact Hfc | now apply fresh_pushed_context | exact HZ]. }
      match goal with
      | IH : forall x, x \notin L -> forall y, y <> x -> y \notin L ->
          forall f L G' e', _ |- _ =>
          pose proof (IH z HzL c Hneq HcL f L0 _ e' ltac:(assumption)
            ltac:(assumption) HC) as Hsub
      end.
      rewrite !rename_typ_opens, Hfz, Hfc in Hsub. exact Hsub.
  - eapply ty_incap_sel with (S := rename_typ f S) (T := rename_typ f T).
    + pose proof (H f L G' e' ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hsel.
      normalize_renamed_in Hsel. exact Hsel.
    + rewrite <- rename_typ_opens. eauto.
Qed.

Local Definition renamed_context f G G' e :=
  renamed_bindings f G G' e /\
  (forall x, ctx_vis G x -> ctx_vis G' (f x)).

Local Lemma renamed_context_push f G G' e x k T :
    f x §# G' ->
    renamed_context f G G' e ->
    renamed_context f (G § x / k ~ T) (G' § f x / k ~ rename_typ f T) e.
Proof.
  intros Hfresh [Hbind Hvis]. split.
  - now apply renamed_bindings_push.
  - intros y Hlookup. inversion Hlookup; subst.
    + apply ctx_vis_e.
    + destruct (classic (f y = f x)) as [Heq | Hneq].
      * rewrite Heq. apply ctx_vis_e.
      * apply ctx_vis_n; auto.
Qed.

Local Lemma renamed_context_hide f G G' e :
    renamed_context f G G' e ->
    renamed_context f (ctx_hide G) (ctx_hide G') e.
Proof.
  intros [Hbind _]. split; [now apply renamed_bindings_hide |].
  intros x H. inversion H.
Qed.

Local Lemma renamed_context_push_fixed f G G' e x k T :
    f x = x ->
    x §# G' ->
    renamed_context f G G' e ->
    renamed_context f (G § x / k ~ T) (G' § x / k ~ rename_typ f T) e.
Proof.
  intros Heq Hfresh Hctx.
  assert (Hfresh' : f x §# G') by now rewrite Heq.
  pose proof (@renamed_context_push f G G' e x k T Hfresh' Hctx) as Hext.
  now rewrite Heq in Hext.
Qed.

Local Lemma renamed_context_push_two f G G' e z c P Q :
    f z §# G' ->
    f c §# G' ->
    f c <> f z ->
    renamed_context f G G' e ->
    renamed_context f (G § z / v_par ~ P § c / v_recv ~ Q)
      (G' § f z / v_par ~ rename_typ f P § f c / v_recv ~ rename_typ f Q) e.
Proof.
  intros Hz Hc Hneq Hctx.
  apply renamed_context_push; [now apply fresh_pushed_context |].
  now apply renamed_context_push.
Qed.

Local Definition rename_objctx f Go :=
  match Go with
  | objctx_empty => objctx_empty
  | objctx_lit x R => objctx_lit (f x) (rename_typ f R)
  | objctx_heap y R => objctx_heap (f y) (rename_typ f R)
  end.

Local Lemma renamed_method_scope f G G' Go e z c TZ TC :
    renamed_context f (G §§& Go) (G' §§& rename_objctx f Go) e ->
    f z §# (G' §§& rename_objctx f Go) ->
    f c §# (G' §§& rename_objctx f Go) ->
    f c <> f z ->
    renamed_context f (ctx_obj_met typing_mode G Go z TZ c TC)
      (ctx_obj_met typing_mode G' (rename_objctx f Go) (f z) (rename_typ f TZ)
        (f c) (rename_typ f TC)) e.
Proof.
  intros Hctx Hz Hc Hneq.
  unfold ctx_obj_met. rewrite visibility_of_mutable_mode.
  pose proof (renamed_context_hide Hctx) as Hhidden.
  destruct Go as [| self R | loc R].
  - pose proof (@renamed_context_push_two f (ctx_hide G) (ctx_hide G') e z c TZ
                 (open z TC) Hz Hc Hneq Hhidden) as Hr.
    normalize_renamed_in Hr. exact Hr.
  - pose proof (@renamed_context_push_two f
                 (ctx_hide (G §§& objctx_lit self R))
                 (ctx_hide (G' §§& rename_objctx f (objctx_lit self R))) e z c TZ
                 (typ_and (open z TC) (typ_and (open self R) (open c R)))
                 Hz Hc Hneq Hhidden) as Hr.
    normalize_renamed_in Hr. exact Hr.
  - pose proof (@renamed_context_push_two f (ctx_hide G) (ctx_hide G') e z c TZ
                 (typ_and (open z TC) (typ_and (open loc R) (open c R)))
                 Hz Hc Hneq Hhidden) as Hr.
    normalize_renamed_in Hr. exact Hr.
Qed.

Local Lemma renamed_method_scope_fixed f G G' Go e z c TZ TC :
    renamed_context f (G §§& Go) (G' §§& rename_objctx f Go) e ->
    f z = z -> f c = c ->
    z §# (G' §§& rename_objctx f Go) ->
    c §# (G' §§& rename_objctx f Go) ->
    c <> z ->
    renamed_context f (ctx_obj_met typing_mode G Go z TZ c TC)
      (ctx_obj_met typing_mode G' (rename_objctx f Go) z (rename_typ f TZ)
        c (rename_typ f TC)) e.
Proof.
  intros Hctx Hz Hc HzG HcG Hneq.
  assert (Hfz : f z §# (G' §§& rename_objctx f Go)) by now rewrite Hz.
  assert (Hfc : f c §# (G' §§& rename_objctx f Go)) by now rewrite Hc.
  assert (Hdiff : f c <> f z) by now rewrite Hz, Hc.
  pose proof (@renamed_method_scope f G G' Go e z c TZ TC Hctx Hfz Hfc Hdiff) as Hr.
  now rewrite Hz, Hc in Hr.
Qed.

Local Lemma renamed_def_label f d n :
    label_of (transform_def (renaming f) d n) = label_of d.
Proof. destruct d; reflexivity. Qed.

Local Lemma renamed_defs_lookup f ds n l :
    get_def l (transform_defs (renaming f) ds n) =
    option_map (fun d => transform_def (renaming f) d n) (get_def l ds).
Proof.
  induction ds as [| ds IH d]; simpl get_def; [reflexivity |].
  cbn [transform_defs get_def].
  rewrite renamed_def_label.
  destruct (classic (label_of d = l)) as [H | H].
  - rewrite !If_l by exact H. reflexivity.
  - rewrite !If_r by exact H. exact IH.
Qed.

Local Lemma renamed_defs_hasnt f ds d :
    defs_hasnt ds (label_of d) ->
    defs_hasnt (rename_defs f ds) (label_of (rename_def f d)).
Proof.
  unfold defs_hasnt. rewrite renamed_def_label, renamed_defs_lookup.
  intros ->. reflexivity.
Qed.

Local Lemma renamed_variable_typing G G' e e' f L (x : var) T :
    renaming_fixes_outside L f ->
    renaming_respects_aliases f e e' ->
    renamed_bindings f G G' e' ->
    G ⁏ e ⊢ x ∶ T ->
    G' ⁏ e' ⊢ f x ∶ rename_typ f T.
Proof.
  intros Hfix Henv Hbind Hty.
  exact (proj1 core_typing_renaming _ _ _ _ _ Hty _ _ _ _ Hfix Henv Hbind).
Qed.

Local Lemma renamed_subtyping G G' e e' f L T U :
    renaming_fixes_outside L f ->
    renaming_respects_aliases f e e' ->
    renamed_bindings f G G' e' ->
    G ⁏ e ⊢ T <: U ->
    G' ⁏ e' ⊢ rename_typ f T <: rename_typ f U.
Proof.
  intros Hfix Henv Hbind Hty.
  exact (proj1 (proj2 core_typing_renaming) _ _ _ _ _ Hty _ _ _ _ Hfix Henv Hbind).
Qed.

Local Lemma renamed_incap G G' e e' f L T U :
    renaming_fixes_outside L f ->
    renaming_respects_aliases f e e' ->
    renamed_bindings f G G' e' ->
    G ⁏ e ⊢ T ∶icp U ->
    G' ⁏ e' ⊢ rename_typ f T ∶icp rename_typ f U.
Proof.
  intros Hfix Henv Hbind Hty.
  exact (proj2 (proj2 core_typing_renaming) _ _ _ _ _ Hty _ _ _ _ Hfix Henv Hbind).
Qed.

Local Hint Resolve renamed_variable_typing renamed_subtyping renamed_incap : renamed_rules.

Local Lemma renamed_capability_bound C G G' e e' f L T U :
    renaming_fixes_outside L f ->
    renaming_respects_aliases f e e' ->
    renamed_bindings f G G' e' ->
    G ⁏ e ⊢ T ∶cpb⟦C⟧ U ->
    G' ⁏ e' ⊢ rename_typ f T ∶cpb⟦C⟧ rename_typ f U.
Proof.
  intros Hfix Henv Hbind Hty.
  induction Hty; normalize_renamed_syntax;
    try solve [constructor; eauto].
  eapply ty_capbnd_sel with (S := rename_typ f S) (T := rename_typ f T).
  - pose proof (@renamed_variable_typing G G' e e' f L x
       (typ_rcd (dec_typ B S T)) Hfix Henv Hbind ltac:(assumption)) as Hsel.
    normalize_renamed_in Hsel. exact Hsel.
  - rewrite <- rename_typ_opens. eauto.
Qed.

Local Lemma renamed_viewpoint G G' e e' f L x T U :
    renaming_fixes_outside L f ->
    renaming_respects_aliases f e e' ->
    renamed_bindings f G G' e' ->
    G ⁏ e ⊢ x ▷ T ⟶ U ->
    G' ⁏ e' ⊢ (f x) ▷ rename_typ f T ⟶ rename_typ f U.
Proof.
  intros Hfix Henv Hbind Hty. unfold viewpoint_adapt in *.
  destruct (mode_viewpoint_adaptation' typing_mode); [now subst |].
  inversion Hty; subst. normalize_renamed_syntax.
  apply viewpoint_adapt_cap_strip_combine.
  - eapply renamed_incap; eassumption.
  - eapply renamed_capability_bound; eassumption.
Qed.

Local Lemma renamed_context_gives_bindings f G G' e :
    renamed_context f G G' e -> renamed_bindings f G G' e.
Proof. apply proj1. Qed.

Local Lemma renamed_context_gives_visibility f G G' e x :
    renamed_context f G G' e -> ctx_vis G x -> ctx_vis G' (f x).
Proof. intros [_ H]. exact (H x). Qed.

Local Hint Resolve renamed_context_gives_bindings renamed_context_gives_visibility
  renamed_viewpoint renamed_defs_hasnt : renamed_rules.
Local Hint Constructors ty_trm ty_lit ty_def ty_defs : renamed_rules.

Local Ltac solve_renamed_variable :=
  match goal with
  | Hfix : renaming_fixes_outside ?K ?f,
    Henv : renaming_respects_aliases ?f ?e ?e',
    Hscope : renamed_context ?f ?G ?G' ?e',
    Hty : ?G ⁏ ?e ⊢ ?x ∶ ?T |- ?G' ⁏ ?e' ⊢ ?f ?x ∶ _ =>
      let Hout := fresh "Hrenamed" in
      pose proof (@renamed_variable_typing G G' e e' f K x T
        Hfix Henv (renamed_context_gives_bindings Hscope) Hty) as Hout;
      normalize_renamed_in Hout;
      exact Hout
  end.

Local Ltac renamed_let_body f L K G G' A e' IH :=
  let z := fresh "z" in let Hz := fresh "Hz" in
  let HzL := fresh "HzL" in let Hfz := fresh "Hfz" in let HzG := fresh "HzG" in
  let Hscope := fresh "Hscope" in let Hbody := fresh "Hbody" in
  intros z Hz;
  destruct (@renaming_fresh_binder f L K G' z ltac:(assumption) Hz)
    as [HzL [Hfz HzG]];
  assert (Hscope : renamed_context f (G § z / v_let ~ A)
             (G' § z / v_let ~ rename_typ f A) e')
    by (now apply renamed_context_push_fixed);
  pose proof (IH z HzL f K _ e' ltac:(assumption) ltac:(assumption) Hscope Hscope)
    as Hbody;
  rewrite !rename_trm_opens, Hfz in Hbody;
  exact Hbody.

Local Lemma term_typing_renaming :
    (forall G Go e t T, ty_trm typing_mode G Go e t T ->
      forall f L G' e',
      renaming_fixes_outside L f -> renaming_respects_aliases f e e' ->
      renamed_context f G G' e' ->
      renamed_context f (G §§& Go) (G' §§& rename_objctx f Go) e' ->
      G' §§ rename_objctx f Go ⁏ e' ⊢ rename_trm f t ∶ rename_typ f T) /\
    (forall G Go e l T, ty_lit typing_mode G Go e l T ->
      forall f L G' e',
      renaming_fixes_outside L f -> renaming_respects_aliases f e e' ->
      renamed_context f G G' e' ->
      renamed_context f (G §§& Go) (G' §§& rename_objctx f Go) e' ->
      G' §§ rename_objctx f Go ⁏ e' ⊢ rename_lit f l ∶ rename_typ f T) /\
    (forall G Go e d D, ty_def typing_mode G Go e d D ->
      forall f L G' e',
      renaming_fixes_outside L f -> renaming_respects_aliases f e e' ->
      renamed_context f G G' e' ->
      renamed_context f (G §§& Go) (G' §§& rename_objctx f Go) e' ->
      G' §§ rename_objctx f Go ⁏ e' ⊢ rename_def f d ∶d rename_dec f D) /\
    (forall G Go e ds T, ty_defs typing_mode G Go e ds T ->
      forall f L G' e',
      renaming_fixes_outside L f -> renaming_respects_aliases f e e' ->
      renamed_context f G G' e' ->
      renamed_context f (G §§& Go) (G' §§& rename_objctx f Go) e' ->
      G' §§ rename_objctx f Go ⁏ e' ⊢ rename_defs f ds ∶ rename_typ f T).
Proof.
  apply rules_mutind; intros.
  all: unfold rename_objctx at 1; normalize_renamed_syntax.
  all: try solve [eauto 4 with renamed_rules |
                  pose proof mode_disallows_functions; congruence].
  - eapply ty_trm_var; [intro |]; eauto with renamed_rules.
  - eapply ty_trm_read with (S := rename_typ f S) (T := rename_typ f T).
    + intro; eauto with renamed_rules.
    + solve_renamed_variable.
    + eapply renamed_viewpoint; try eassumption.
      eapply renamed_context_gives_bindings; eassumption.
  - eapply ty_trm_write with (S := rename_typ f S);
      [intro | intro | intros Hmode; specialize (o Hmode) | |];
      first [solve_renamed_variable | eauto with renamed_rules].
  - eapply ty_trm_call with
      (TC := rename_typ f TC) (TZ := rename_typ f TZ) (TR := rename_typ f TR).
    + intros; eauto with renamed_rules.
    + intros; eauto with renamed_rules.
    + solve_renamed_variable.
    + solve_renamed_variable.
    + intros Hmode. eapply renaming_preserves_independence; [eauto | reflexivity].
    + solve_renamed_variable.
  - eapply ty_trm_let with (L := L \u (L0 \u ctx_dom G')) (T := rename_typ f T);
      [eauto | renamed_let_body f L L0 G G' T e' H0].
  - eapply ty_trm_lit with (L := L \u (L0 \u ctx_dom G')) (T := rename_typ f T);
      [eauto | renamed_let_body f L L0 G G' T e' H0].
  - eapply ty_trm_sub with (T := rename_typ f T); eauto with renamed_rules.
  - replace (rename_typ f (typ_objlit typing_mode T))
        with (typ_objlit typing_mode (rename_typ f T)) by
        (destruct (mode_objlit_refcaps' typing_mode); normalize_renamed_syntax; reflexivity).
    eapply ty_lit_obj with (L := L \u (L0 \u ctx_dom G')); [|].
    + intros z Hz.
      destruct (@renaming_fresh_binder f L L0 G' z ltac:(assumption) Hz)
        as [HzL [Hfz HzG]].
      assert (Hscope : renamed_context f (G § z / v_self ~ open z T)
        (G' § z / v_self ~ open z (rename_typ f T)) e').
      { replace (open z (rename_typ f T)) with (rename_typ f (open z T))
          by now rewrite rename_typ_opens, Hfz.
        now apply renamed_context_push_fixed. }
      assert (Hobject : renamed_context f (G §§& objctx_lit z T)
        (G' §§& rename_objctx f (objctx_lit z T)) e').
      { cbn [ctx_obj rename_objctx]. rewrite Hfz. exact Hscope. }
      pose proof (H z HzL f L0 G' e' ltac:(assumption) ltac:(assumption)
        ltac:(assumption) Hobject) as Hbody.
      cbn [rename_objctx] in Hbody. rewrite !rename_typ_opens, !rename_defs_open, Hfz in Hbody.
      exact Hbody.
    + eapply renaming_preserves_independence; [eassumption | reflexivity].
  - eapply ty_def_typ with (L := L \u L0).
    intros z Hz. apply notin_union in Hz as [HzL HzRename].
    assert (Hfz : f z = z) by (eapply H; eassumption).
    pose proof (@rename_equivalence e _ _ (t z HzL) f e' ltac:(assumption)) as Hdecl.
    rewrite !rename_typ_opens, Hfz in Hdecl. exact Hdecl.
  - eapply ty_def_fld; [intro; eauto with renamed_rules | solve_renamed_variable].
  - eapply ty_def_met with (L := L \u (L0 \u ctx_dom (G' §§& rename_objctx f Go))).
    intros z Hz c Hneq Hc.
    destruct (@renaming_fresh_binder f L L0 (G' §§& rename_objctx f Go)
      z ltac:(assumption) Hz) as [HzL [Hfz HzG]].
    destruct (@renaming_fresh_binder f L L0 (G' §§& rename_objctx f Go)
      c ltac:(assumption) Hc) as [HcL [Hfc HcG]].
    pose proof (@renamed_method_scope_fixed f G G' Go e' z c TZ TC
      ltac:(assumption) Hfz Hfc HzG HcG Hneq) as Hscope.
    pose proof (H z HzL c Hneq HcL f L0 _ e' ltac:(assumption) ltac:(assumption)
      Hscope Hscope) as Hbody.
    rewrite !rename_typ_opens, !rename_trm_opens, Hfz, Hfc in Hbody.
    exact Hbody.
  - change (G' §§ rename_objctx f Go ⁏ e'
      ⊢ defs_cons (rename_defs f ds) (rename_def f d)
      ∶ typ_and (rename_typ f T) (typ_rcd (rename_dec f D))).
    apply ty_defs_cons; eauto with renamed_rules.
Qed.

Local Lemma term_open_commutes_mutual :
    (forall t : trm, forall k l x y, k <> l ->
       open_rec k x (open_rec l y t) = open_rec l y (open_rec k x t)) /\
    (forall a : lit, forall k l x y, k <> l ->
       open_rec k x (open_rec l y a) = open_rec l y (open_rec k x a)) /\
    (forall d : def, forall k l x y, k <> l ->
       open_rec k x (open_rec l y d) = open_rec l y (open_rec k x d)) /\
    (forall ds : defs, forall k l x y, k <> l ->
       open_rec k x (open_rec l y ds) = open_rec l y (open_rec k x ds)).
Proof.
  apply trm_mutind; intros;
    cbn [open_rec TrmOpenable LitOpenable DefOpenable DefsOpenable
      open_rec_trm open_rec_lit open_rec_def open_rec_defs];
    f_equal; eauto using avar_open_commute, type_open_commute; congruence.
Qed.

Local Lemma avar_open_absorbs (a : avar) n x y :
    open_rec n x (open_rec n y a) = open_rec n y a.
Proof.
  destruct a as [k | z]; [| reflexivity].
  cbn [open_rec AvarOpenable].
  destruct (Nat.eq_dec n k).
  - now rewrite !If_l by assumption.
  - rewrite (@If_r _ (n = k)) by assumption.
    cbn [open_rec AvarOpenable].
    now rewrite (@If_r _ (n = k)) by assumption.
Qed.

Local Lemma type_dec_open_absorbs :
    (forall T : typ, forall n x y,
       open_rec n x (open_rec n y T) = open_rec n y T) /\
    (forall D : dec, forall n x y,
       open_rec n x (open_rec n y D) = open_rec n y D).
Proof.
  apply typ_mutind; intros;
    cbn [open_rec TypOpenable DecOpenable open_rec_typ open_rec_dec];
    try reflexivity; f_equal; eauto using avar_open_absorbs.
Qed.

Local Lemma type_open_absorbs (T : typ) n x y :
    open_rec n x (open_rec n y T) = open_rec n y T.
Proof. exact (proj1 type_dec_open_absorbs T n x y). Qed.

Local Lemma term_open_absorbs_mutual :
    (forall t : trm, forall n x y, open_rec n x (open_rec n y t) = open_rec n y t) /\
    (forall a : lit, forall n x y, open_rec n x (open_rec n y a) = open_rec n y a) /\
    (forall d : def, forall n x y, open_rec n x (open_rec n y d) = open_rec n y d) /\
    (forall ds : defs, forall n x y, open_rec n x (open_rec n y ds) = open_rec n y ds).
Proof.
  apply trm_mutind; intros;
    cbn [open_rec TrmOpenable LitOpenable DefOpenable DefsOpenable
      open_rec_trm open_rec_lit open_rec_def open_rec_defs];
    f_equal; eauto using avar_open_absorbs, type_open_absorbs.
Qed.

Local Lemma closed_frame_body t s x :
    closed (stack_cons (frame_let t) s) ->
    closed (open x t) /\ closed s.
Proof.
  intros Hclosed.
  assert (Hparts : forall n z, open_rec (S n) z t = t /\ open_rec n z s = s).
  { intros n z. pose proof (Hclosed n z) as Hopen.
    change (stack_cons (frame_let (open_rec (S n) z t)) (open_rec n z s) =
            stack_cons (frame_let t) s) in Hopen.
    injection Hopen; auto. }
  split; intros n z.
  - destruct n as [| n].
    + apply (proj1 term_open_absorbs_mutual).
    + rewrite (proj1 term_open_commutes_mutual t (S n) 0 z x) by discriminate.
      now rewrite (proj1 (Hparts n z)).
  - exact (proj2 (Hparts n z)).
Qed.

Local Lemma substitution_context G e z x A :
    z §# G ->
    z \notin ctx_fv G ->
    z \notin fv A ->
    G ⁏ e ⊢ x ∶ A ->
    ctx_vis G x ->
    renamed_context (replace_name (fun p => p) z x) (G § z / v_let ~ A) G e.
Proof.
  intros Hz Hctx HA Hx Hvis. split.
  - intros y B Hb. inversion Hb; subst.
    + rewrite replace_name_at.
      rewrite rename_typ_inactive by now apply replace_name_fresh.
      exact Hx.
    + rewrite replace_name_away by assumption.
      rewrite rename_typ_inactive.
      * apply ty_var_var; assumption.
      * apply replace_name_fresh. intros Hbad. apply Hctx.
        eapply bound_type_free_in_context; eassumption.
  - intros y Hy. inversion Hy; subst.
    + now rewrite replace_name_at.
    + now rewrite replace_name_away by assumption.
Qed.

Local Lemma instantiate_let_body G e L (t : trm) A B x :
    (forall z, z \notin L -> G § z / v_let ~ A ⁏ e ⊢ open z t ∶ B) ->
    G ⁏ e ⊢ x ∶ A ->
    ctx_vis G x ->
    G ⁏ e ⊢ open x t ∶ B.
Proof.
  intros Hbody Hx Hvis.
  destruct (var_fresh
    (L \u ctx_dom G \u ctx_fv G \u fv_renv e \u fv t \u fv A \u fv B)) as [z Hz].
  rewrite !notin_union in Hz.
  destruct Hz as (HzL & HzDom & HzCtx & [HzED HzER] & Hzt & HzA & HzB).
  set (f := replace_name (fun p => p) z x).
  assert (Hfix : renaming_fixes_outside \{z} f).
  { intros y Hy. rewrite notin_singleton in Hy. now apply replace_name_away. }
  assert (Haliases : renaming_respects_aliases f e e).
  { unfold f. apply replace_name_respects_aliases.
    - apply notin_union; auto.
    - intros a b Hb. now apply tyq_var_binds. }
  assert (Hscope : renamed_context f (G § z / v_let ~ A) G e)
    by (unfold f; now apply substitution_context).
  pose proof (proj1 term_typing_renaming _ _ _ _ _ (Hbody z HzL)
    f \{z} G e Hfix Haliases Hscope Hscope) as Hopened.
  cbn [rename_objctx] in Hopened.
  rewrite rename_trm_opens in Hopened.
  assert (Hfz : f z = x) by apply replace_name_at.
  rewrite Hfz in Hopened.
  rewrite rename_trm_inactive in Hopened by (unfold f; now apply replace_name_fresh).
  rewrite rename_typ_inactive in Hopened by (unfold f; now apply replace_name_fresh).
  exact Hopened.
Qed.

Local Lemma let_pop_preservation F x t s S e Lv U :
    execution_config F (trm_var (avar_f x) ; stack_cons (frame_let t) s ; S ; e ; Lv) U ->
    execution_config F (open x t ; s ; S ; e ;
      fv_config (trm_var (avar_f x) ; stack_cons (frame_let t) s ; S ; e ; Lv)) U.
Proof.
  intros Hcfg. inversion Hcfg; subst.
  match goal with Hs : ty_stack F e _ (stack_cons (frame_let t) s) U |- _ =>
    inversion Hs; subst
  end.
  assert (Hvisible : ctx_vis F x).
  { eapply kind_bound_visible.
    match goal with Hfree : all_tfree_k_trm F (trm_var (avar_f x)) v_ref |- _ =>
      apply Hfree; apply tfree_trm_var
    end. }
  match goal with Htail : ty_stack F e ?B s U |- _ =>
    eapply execution_config_intro with (T := B)
  end; try eassumption.
  - intros w Hfree.
    match goal with Hframe : all_tfree_k_stack F (stack_cons (frame_let t) s) v_ref |- _ =>
      apply Hframe; now apply tfree_stack_cons_r
    end.
  - eapply instantiate_let_body; [eassumption | | exact Hvisible].
    eapply variable_term_typing; [eassumption | reflexivity].
  - intros w Hfree. apply (proj1 tfree_opened_mutual) in Hfree as [Hbodyfree | ->].
    + match goal with Hframe : all_tfree_k_stack F (stack_cons (frame_let t) s) v_ref |- _ =>
        apply Hframe; now apply tfree_stack_cons_l
      end.
    + match goal with Hvar : all_tfree_k_trm F (trm_var (avar_f x)) v_ref |- _ =>
        apply Hvar; apply tfree_trm_var
      end.
  - exact (@carry_config_names F U
       (trm_var (avar_f x) ; stack_cons (frame_let t) s ; S ; e ; Lv)
       (open x t ; s ; S ; e ;
        fv_config (trm_var (avar_f x) ; stack_cons (frame_let t) s ; S ; e ; Lv))
       eq_refl ltac:(assumption)).
  - exact (@carry_config_null
       (trm_var (avar_f x) ; stack_cons (frame_let t) s ; S ; e ; Lv)
       (open x t ; s ; S ; e ;
        fv_config (trm_var (avar_f x) ; stack_cons (frame_let t) s ; S ; e ; Lv))
       eq_refl ltac:(assumption)).
  - match goal with Hclosed : config_closed _ |- _ => inversion Hclosed; subst end.
    destruct (@closed_frame_body t s x ltac:(assumption)) as [Hterm Hstack].
    constructor; assumption.
Qed.

Local Lemma closed_definitions_member ds d :
    closed ds -> defs_has ds d -> closed d.
Proof.
  induction ds as [| ds IH last]; intros Hclosed Hmember.
  - discriminate.
  - unfold defs_has in Hmember. simpl get_def in Hmember.
    assert (Hparts : forall n z,
      open_rec n z ds = ds /\ open_rec n z last = last).
    { intros n z. pose proof (Hclosed n z) as Hopen.
      change (defs_cons (open_rec n z ds) (open_rec n z last) =
              defs_cons ds last) in Hopen.
      injection Hopen; auto. }
    destruct (classic (label_of last = label_of d)) as [Heq | Hneq].
    + rewrite If_l in Hmember by exact Heq. inversion Hmember; subst.
      intros n z. exact (proj2 (Hparts n z)).
    + rewrite If_r in Hmember by exact Hneq.
      apply IH; [| exact Hmember].
      intros n z. exact (proj1 (Hparts n z)).
Qed.

Local Lemma method_body_closed_after_opening m t x y :
    closed (def_met m t) ->
    closed (open_met x y t).
Proof.
  intros Hclosed n z. destruct n as [| n].
  - apply (proj1 term_open_absorbs_mutual).
  - rewrite (proj1 term_open_commutes_mutual (open_rec 1 y t) (S n) 0 z x)
      by discriminate.
    destruct n as [| n].
    + rewrite (proj1 term_open_absorbs_mutual t 1 z y). reflexivity.
    + rewrite (proj1 term_open_commutes_mutual t (S (S n)) 1 z y)
        by congruence.
      pose proof (Hclosed n z) as Hopen.
      change (def_met m (open_rec (S (S n)) z t) = def_met m t) in Hopen.
      injection Hopen. intros ->. reflexivity.
Qed.

Local Lemma call_preservation_with_body_typing F s S e Lv wObj wArg m t U yObj ds :
    execution_config F (trm_call (avar_f wObj) m (avar_f wArg) ; s ; S ; e ; Lv) U ->
    binds yObj (item_obj ds) S ->
    defs_has ds (def_met m t) ->
    (forall T, F ⁏ e ⊢ trm_call (avar_f wObj) m (avar_f wArg) ∶ T ->
               F ⁏ e ⊢ open_met wArg wObj t ∶ T) ->
    execution_config F (open_met wArg wObj t ; s ; S ; e ;
      fv_config (trm_call (avar_f wObj) m (avar_f wArg) ; s ; S ; e ; Lv)) U.
Proof.
  intros Hcfg Hbind Hmethod Hbody.
  inversion Hcfg; subst.
  eapply execution_config_intro with (T := T); try eassumption.
  - now apply Hbody.
  - intros w Hfree.
    match goal with Hk : all_tfree_k_trm F (trm_call _ _ _) v_ref |- _ => apply Hk end.
    destruct (proj1 tfree_opened_mutual (open_rec 1 wObj t) 0 wArg w Hfree)
      as [Hw | ->]; [| apply tfree_trm_call_r].
    destruct (proj1 tfree_opened_mutual t 1 wObj w Hw)
      as [Hw' | ->]; [| apply tfree_trm_call_l].
    exfalso. eapply heap_method_free; eassumption.
  - exact (@carry_config_names F U
       (trm_call (avar_f wObj) m (avar_f wArg) ; s ; S ; e ; Lv)
       (open_met wArg wObj t ; s ; S ; e ;
        fv_config (trm_call (avar_f wObj) m (avar_f wArg) ; s ; S ; e ; Lv))
       eq_refl ltac:(assumption)).
  - exact (@carry_config_null
       (trm_call (avar_f wObj) m (avar_f wArg) ; s ; S ; e ; Lv)
       (open_met wArg wObj t ; s ; S ; e ;
        fv_config (trm_call (avar_f wObj) m (avar_f wArg) ; s ; S ; e ; Lv))
       eq_refl ltac:(assumption)).
  - match goal with Hclosed : config_closed _ |- _ => inversion Hclosed; subst end.
    constructor; [|assumption|assumption].
    eapply method_body_closed_after_opening.
    eapply closed_definitions_member; [| exact Hmethod].
    intros n z.
    pose proof (@bound_heap_item_closed S yObj (item_obj ds)
      ltac:(assumption) Hbind n z) as Hopen.
    change (item_obj (open_rec n z ds) = item_obj ds) in Hopen.
    now injection Hopen.
Qed.

Local Lemma visibility_in_context_domain G x :
    ctx_vis G x -> x \in ctx_dom G.
Proof.
  intros H. induction H; simpl ctx_dom; rewrite in_union.
  - left. now rewrite in_singleton.
  - now right.
Qed.

Local Lemma rename_context_identity_on_scope f G e :
    names_agree_on (ctx_dom G \u ctx_fv G) f (fun p => p) ->
    renamed_context f G G e.
Proof.
  intros Hagree. split.
  - intros x T Hb.
    assert (Hx : f x = x).
    { apply (names_agree_left Hagree). eapply context_binding_in_domain; eassumption. }
    rewrite Hx, rename_typ_inactive.
    + now apply ty_var_var.
    + intros y Hy. apply (names_agree_right Hagree).
      eapply bound_type_free_in_context; eassumption.
  - intros x Hvis.
    assert (Hx : f x = x).
    { apply (names_agree_left Hagree). now apply visibility_in_context_domain. }
    now rewrite Hx.
Qed.

Local Lemma renamed_context_hide_source f G G' e :
    renamed_context f G G' e ->
    renamed_context f (ctx_hide G) G' e.
Proof.
  intros [Hbind Hvis]. split.
  - intros x T Hb. inversion Hb; subst. now apply Hbind.
  - intros x Hv. inversion Hv.
Qed.

Local Lemma renamed_context_discharge f G G' e z k T :
    renamed_context f G G' e ->
    G' ⁏ e ⊢ f z ∶ rename_typ f T ->
    ctx_vis G' (f z) ->
    renamed_context f (G § z / k ~ T) G' e.
Proof.
  intros [Hbind Hvis] Hty Hvisible. split.
  - intros x U Hb. inversion Hb; subst; auto.
  - intros x Hv. inversion Hv; subst; auto.
Qed.

Local Lemma fresh_two_name_substitution e L x y :
    exists z c (f : var -> var),
      z \notin L /\ c \notin L /\ c <> z /\
      f z = x /\ f c = y /\
      renaming_fixes_outside (\{z} \u \{c}) f /\
      names_agree_on L f (fun p => p) /\
      renaming_respects_aliases f e e.
Proof.
  destruct (var_fresh (L \u fv_renv e)) as [z Hz].
  apply notin_union in Hz as [HzL HzEnv].
  destruct (var_fresh (L \u (fv_renv e \u \{z}))) as [c Hc].
  apply notin_union in Hc as [HcL Hc].
  apply notin_union in Hc as [HcEnv Hc].
  rewrite notin_singleton in Hc.
  set (g := replace_name (fun p => p) z x).
  exists z, c, (replace_name g c y).
  repeat split; try assumption.
  - rewrite replace_name_away by congruence. apply replace_name_at.
  - apply replace_name_at.
  - intros p Hp. rewrite notin_union, !notin_singleton in Hp. destruct Hp as [Hpz Hpc].
    unfold g. now rewrite !replace_name_away by assumption.
  - eapply names_agree_trans with (g := g).
    + now apply replace_name_fresh.
    + now apply replace_name_fresh.
  - apply replace_name_respects_aliases; [exact HcEnv |].
    apply replace_name_respects_aliases; [exact HzEnv |].
    intros a b Hb. now apply tyq_var_binds.
Qed.

Local Lemma call_typing_operands F e t T :
    F ⁏ e ⊢ t ∶ T ->
    forall w m a, t = trm_call (avar_f w) m (avar_f a) ->
    exists C Z R,
      ctx_vis F w /\ ctx_vis F a /\
      F ⁏ e ⊢ w ∶ typ_rcd (dec_met m C Z R) /\
      F ⁏ e ⊢ a ∶ Z /\
      F ⁏ e ⊢ w ∶ open a C /\
      F ⁏ e ⊢ open_met a w R <: T.
Proof.
  intros Hty. induction Hty; intros w0 m0 a0 Heq; try discriminate.
  - inversion Heq; subst. do 3 eexists.
    repeat split; eauto using visibility_of_mutable_mode, subtyp_refl.
  - destruct (IHHty w0 m0 a0 Heq) as (C & Z & R & Hw & Ha & Hm & Hz & Hc & Hr).
    exists C, Z, R. repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

Local Lemma declaration_view_method_bounds F e x R B m C0 Z0 T0 C Z T ls :
    record_typ (open (canonical_location e x) R) ls ->
    record_has (open (canonical_location e x) R) (dec_met m C0 Z0 T0) ->
    object_has_view F e x R B declaration_view (typ_rcd (dec_met m C Z T)) ->
    method_type_bounds F e C0 Z0 T0 C Z T.
Proof.
  intros Hrec Hmethod Hview. inversion Hview; subst.
  destruct actual as [al TL TU | fl TL TU | ml TC TZ TR].
  - destruct al; contradiction.
  - contradiction.
  - simpl in H1. destruct H1 as [Hlabel Hbounds]. subst ml.
    pose proof (record_label_unique Hrec Hmethod H0 eq_refl) as Heq.
    now inversion Heq.
Qed.

Local Lemma method_declaration_gives_bounds F e H y m R B C0 Z0 T0 C Z T :
    inert F ->
    heap_correspond F e H ->
    canonical_location e y = y ->
    ctx_binds y (typ_objref R (typ_mut_marker B)) F ->
    record_has (open y R) (dec_met m C0 Z0 T0) ->
    F ⁏ e ⊢ y ∶ typ_rcd (dec_met m C Z T) ->
    method_type_bounds F e C0 Z0 T0 C Z T.
Proof.
  intros Hinert Hheap Hcanonical Hbound Hmethod Hty.
  destruct (precise_config_annotation Hinert Hheap Hbound)
    as [R' [B' [ds [Heq [Hrecord _]]]]].
  inversion Heq; subst R' B'.
  destruct (proj1 variable_views_and_exact_subtypes F objctx_empty e y _ Hty H R B
    Hinert Hheap Hbound Hrecord) as [Hview _].
  destruct Hrecord as [ls Hrec].
  pose proof (opened_record_typ 0 (canonical_location e y) Hrec) as Hopened.
  rewrite <- Hcanonical in Hmethod at 1.
  eapply declaration_view_method_bounds; eassumption.
Qed.

Local Ltac close_renamed_types HK Hzmap Hcmap Hymap :=
  repeat first
    [ rewrite rename_typ_opens
    | rewrite rename_trm_opens
    | progress rewrite ?Hzmap, ?Hcmap, ?Hymap
    | rewrite rename_typ_inactive by (intros v Hv; apply HK; rewrite !in_union; tauto)
    | rewrite rename_trm_inactive by (intros v Hv; apply HK; rewrite !in_union; tauto) ].

Local Lemma instantiate_method_body F e y R m t C0 Z0 T0 C Z T w a :
    F §§ objctx_heap y R ⁏ e ⊢ def_met m t ∶d dec_met m C0 Z0 T0 ->
    method_type_bounds F e C0 Z0 T0 C Z T ->
    F ⁏ e ⊢ a ∶ Z ->
    F ⁏ e ⊢ w ∶ open a C ->
    F ⁏ e ⊢ w ∶ open y R ->
    F ⁏ e ⊢ w ∶ open w R ->
    ctx_vis F a ->
    ctx_vis F w ->
    F ⁏ e ⊢ open_met a w t ∶ open_met a w T.
Proof.
  intros Hmethod (HargSub & Lsub & HrecvSub & HresSub)
    Harg Hrecv Hloc Hself Havis Hwvis.
  inversion Hmethod as [| | L G Go E m' t' C' Z' T' Hbody]; subst.
  set (K := (ctx_dom F \u ctx_fv F) \u
    \{y} \u fv t \u fv R \u fv C0 \u fv Z0 \u fv T0 \u fv C \u fv Z \u fv T).
  destruct (@fresh_two_name_substitution e (L \u (Lsub \u K)) a w)
    as (z & c & f & Hz & Hc & Hneq & Hzmap & Hcmap & Hfix & Hagree & Henv).
  rewrite !notin_union in Hz, Hc.
  destruct Hz as (HzL & HzSub & _), Hc as (HcL & HcSub & _).
  pose proof (names_agree_right (names_agree_right Hagree)) as HK.
  unfold K in HK.
  assert (Hymap : f y = y).
  { apply (names_agree_left (names_agree_right HK)). now rewrite in_singleton. }
  assert (HF : renamed_context f F F e).
  { apply rename_context_identity_on_scope. exact (names_agree_left HK). }
  assert (Hpar : renamed_context f (F § z / v_par ~ Z) F e).
  { apply renamed_context_discharge; [exact HF | | now rewrite Hzmap].
    close_renamed_types HK Hzmap Hcmap Hymap. exact Harg. }
  pose proof (@renamed_subtyping _ F e e f _ _ _ Hfix Henv
    (proj1 Hpar) (HrecvSub z HzSub)) as HrecvSub'.
  assert (Hrecv' : F ⁏ e ⊢ w ∶ open a C0).
  { eapply ty_var_sub; [exact Hrecv |].
    revert HrecvSub'. close_renamed_types HK Hzmap Hcmap Hymap. auto. }
  assert (Hscope : renamed_context f (ctx_met F z Z c C) F e).
  { apply renamed_context_discharge; [exact Hpar | | now rewrite Hcmap].
    close_renamed_types HK Hzmap Hcmap Hymap. exact Hrecv. }
  pose proof (@renamed_subtyping _ F e e f _ _ _ Hfix Henv
    (proj1 Hscope) (HresSub z HzSub c Hneq HcSub)) as HresSub'.
  assert (Hpar' : renamed_context f (ctx_hide F § z / v_par ~ Z0) F e).
  { apply renamed_context_discharge; [now apply renamed_context_hide_source | | now rewrite Hzmap].
    close_renamed_types HK Hzmap Hcmap Hymap. eapply ty_var_sub; eassumption. }
  assert (Hscope' : renamed_context f (ctx_obj_met typing_mode F (objctx_heap y R)
    z Z0 c C0) F e).
  { unfold ctx_obj_met. rewrite visibility_of_mutable_mode.
    apply renamed_context_discharge; [exact Hpar' | | now rewrite Hcmap].
    normalize_renamed_syntax. close_renamed_types HK Hzmap Hcmap Hymap.
    apply ty_var_and; [exact Hrecv' | now apply ty_var_and]. }
  pose proof (proj1 term_typing_renaming _ _ _ _ _ (Hbody z HzL c Hneq HcL)
    f _ F e Hfix Henv Hscope' Hscope') as Hopened.
  cbn [rename_objctx] in Hopened.
  revert Hopened HresSub'. close_renamed_types HK Hzmap Hcmap Hymap.
  eauto using ty_trm_sub.
Qed.

Local Lemma object_reference_record_views F e w y R B :
    binds w y e ->
    ctx_binds w (typ_objref R (typ_mut_marker B)) F ->
    typ_indep_b 0 R ->
    F ⁏ e ⊢ w ∶ open y R /\ F ⁏ e ⊢ w ∶ open w R.
Proof.
  intros Hbind Hty Hindep.
  assert (Hself : F ⁏ e ⊢ w ∶ open w R).
  { apply ty_rec_elim; [| exact Hindep].
    eapply ty_var_sub; [exact (ty_var_var typing_mode e Hty) | apply subtyp_and11]. }
  split; [| exact Hself].
  eapply ty_var_sub; [exact Hself |].
  apply subtyp_tyq.
  eapply independent_type_open_alias; [now apply tyq_var_binds | exact Hindep | reflexivity].
Qed.

Local Lemma call_step_typing_and_reachability F s S e Lv wObj wArg m t U yObj ds :
    execution_config F (trm_call (avar_f wObj) m (avar_f wArg) ; s ; S ; e ; Lv) U ->
    binds yObj (item_obj ds) S ->
    defs_has ds (def_met m t) ->
    binds wObj yObj e ->
    let C' := (open_met wArg wObj t ; s ; S ; e ;
      fv_config (trm_call (avar_f wObj) m (avar_f wArg) ; s ; S ; e ; Lv)) in
    execution_config F C' U /\
    (forall y, F ⊢ C' mreach y ->
      F ⊢ (trm_call (avar_f wObj) m (avar_f wArg) ; s ; S ; e ; Lv) mreach y).
Proof.
  intros Hcfg Hbind Hmethod Hobj.
  assert (Hinert : inert F) by (inversion Hcfg; assumption).
  assert (Hheap : heap_correspond F e S) by (inversion Hcfg; assumption).
  pose proof Hheap as (Hok & _ & _ & _ & _ & _ & Henv & _).
  destruct (reference_location_annotations Hok Henv Hobj)
    as (R & B & Gw & Gy & Hw & Hy).
  pose proof (kind_binding_gives_binding Hw) as Hw'.
  pose proof (kind_binding_gives_binding Hy) as Hy'.
  destruct (precise_config_annotation Hinert Hheap Hw')
    as (R' & B' & ds' & Heq & Hrecord & Hindep & _).
  inversion Heq; subst R' B'.
  destruct (location_has_typed_defs Hheap Hy) as (ds0 & Hbind0 & Hdefs).
  pose proof (binds_functional Hbind Hbind0) as Heqds.
  inversion Heqds; subst ds0.
  destruct (typed_defs_member_record Hdefs Hmethod) as (D & Hmember & HD).
  inversion HD; subst.
  assert (Hcanonical : canonical_location e yObj = yObj)
    by exact (proj2 (environment_binding_canonical_locations Hheap Hobj)).
  destruct (object_reference_record_views Hobj Hw' Hindep) as [Hloc Hself].
  split.
  - eapply call_preservation_with_body_typing; try eassumption.
    intros T Hcall.
    destruct (call_typing_operands Hcall eq_refl)
      as (C & Z & R0 & Hvis & Havis & Hty & Harg & Hrecv & Hsub).
    pose proof (reference_typing_at_location Hok Henv Hobj Hty) as Hty'.
    pose proof (method_declaration_gives_bounds Hinert Hheap Hcanonical Hy' Hmember Hty') as Hbounds.
    eapply ty_trm_sub; [| exact Hsub].
    eapply instantiate_method_body; eassumption.
  - intros y HyReach. eapply reachability_call; eassumption.
Qed.

Local Lemma capability_widen F e B B' :
    (forall x, F ⁏ e ⊢ open x B <: open x B') ->
    F ⁏ e ⊢ typ_mut_marker B <: typ_mut_marker B'.
Proof.
  intros H. apply subtyp_typ; [intros; apply subtyp_refl | exact H].
Qed.

Local Lemma capability_intersection F e A B :
    F ⁏ e ⊢ typ_and (typ_mut_marker A) (typ_mut_marker B) <:
      typ_mut_marker (typ_and A B).
Proof.
  eapply subtyp_trans.
  - apply subtyp_typ_and.
  - apply subtyp_typ; intros; [apply subtyp_bot | apply subtyp_refl].
Qed.

Local Lemma capability_bound_projection F e T B :
    F ⁏ e ⊢ T ∶cpb⟦typ_refcap_mutability⟧ B ->
    (forall z, F ⁏ e ⊢ typ_top <: open z B) \/
    F ⁏ e ⊢ T <: typ_mut_marker B.
Proof.
  intros H. induction H; try solve [left; intro; apply subtyp_refl
    | right; apply subtyp_bot].
  - right. apply subtyp_typ; intros; [apply subtyp_bot | apply subtyp_refl].
  - match goal with IH : _ \/ _ |- _ => destruct IH as [Htop | Hcap] end;
      [now left | right].
    eapply subtyp_trans; [eapply subtyp_sel1; eassumption | exact Hcap].
  - match goal with
    | IL : (forall z, ?F ⁏ ?e ⊢ typ_top <: open z ?A) \/ _,
      IR : (forall z, ?F ⁏ ?e ⊢ typ_top <: open z ?B) \/ _
      |- _ \/ ?F ⁏ ?e ⊢ _ <: typ_mut_marker (typ_and ?A ?B) =>
        destruct IL as [HL | HL], IR as [HR | HR]
    end.
    + left. intro z. apply subtyp_and2; auto.
    + right. eapply subtyp_trans; [apply subtyp_and12 |].
      eapply subtyp_trans; [exact HR |].
      apply capability_widen. intro z. apply subtyp_and2; [|apply subtyp_refl].
      eapply subtyp_trans; [apply subtyp_top | apply HL].
    + right. eapply subtyp_trans; [apply subtyp_and11 |].
      eapply subtyp_trans; [exact HL |].
      apply capability_widen. intro z. apply subtyp_and2; [apply subtyp_refl |].
      eapply subtyp_trans; [apply subtyp_top | apply HR].
    + right. eapply subtyp_trans; [|apply capability_intersection].
      apply subtyp_and2.
      * eapply subtyp_trans; [apply subtyp_and11 | exact HL].
      * eapply subtyp_trans; [apply subtyp_and12 | exact HR].
  - match goal with
    | IL : (forall z, ?F ⁏ ?e ⊢ typ_top <: open z ?A) \/ _,
      IR : (forall z, ?F ⁏ ?e ⊢ typ_top <: open z ?B) \/ _
      |- _ \/ ?F ⁏ ?e ⊢ _ <: typ_mut_marker (typ_or ?A ?B) =>
        destruct IL as [HL | HL], IR as [HR | HR]
    end; try solve
      [left; intro z; eapply subtyp_trans; [apply HL | apply subtyp_or11]
      |left; intro z; eapply subtyp_trans; [apply HR | apply subtyp_or12]].
    right. apply subtyp_or2.
    + eapply subtyp_trans; [exact HL |]. apply capability_widen; intros; apply subtyp_or11.
    + eapply subtyp_trans; [exact HR |]. apply capability_widen; intros; apply subtyp_or12.
Qed.

Local Lemma no_top_below_bottom F e S y R B :
    inert F ->
    heap_correspond F e S ->
    ctx_binds y (typ_objref R (typ_mut_marker B)) F ->
    F ⁏ e ⊢ typ_top <: typ_bot ->
    False.
Proof.
  intros Hinert Hheap Hbound Hsub.
  destruct (precise_config_annotation Hinert Hheap Hbound)
    as (R' & B' & ds & Heq & Hrecord & _).
  inversion Heq; subst R' B'.
  pose proof (proj1 (proj2 variable_views_and_exact_subtypes)
    F objctx_empty e _ _ Hsub S Hinert Hheap) as Hexact.
  pose proof (@exact_subtype_preserves_view F e S y R B _ _
    Hinert Hheap Hrecord Hexact declaration_view (@view_top F e y R B declaration_view)) as Hview.
  inversion Hview.
Qed.

Local Lemma mutable_adapted_field_bound F e S w R M T B :
    inert F ->
    heap_correspond F e S ->
    ctx_binds w (typ_objref R (typ_mut_marker M)) F ->
    F ⁏ e ⊢ T ∶cpb⟦typ_refcap_mutability⟧ B ->
    (forall z, F ⁏ e ⊢ open z
      (typ_or B (typ_sel (avar_f w) typ_label_mutability (avar_b 0))) <: typ_bot) ->
    F ⁏ e ⊢ T <: typ_mut_marker typ_bot.
Proof.
  intros Hinert Hheap Hbound Hcap Hbot.
  assert (HB : forall z, F ⁏ e ⊢ open z B <: typ_bot).
  { intro z. eapply subtyp_trans; [apply subtyp_or11 | apply Hbot]. }
  destruct (capability_bound_projection Hcap) as [Htop | Hproject].
  - exfalso. eapply no_top_below_bottom; [exact Hinert | exact Hheap | exact Hbound |].
    eapply subtyp_trans; [apply (Htop w) | apply HB].
  - eapply subtyp_trans; [exact Hproject |].
    exact (@capability_widen F e B typ_bot HB).
Qed.

Local Lemma alias_extension_collapse F e w y R B :
    w \notin ctx_dom F ->
    w \notin ctx_fv F ->
    w \notin fv_renv e ->
    w <> y ->
    ctx_vis F y ->
    ctx_binds y (typ_objref R (typ_mut_marker typ_bot)) F ->
    let f := replace_name (fun v => v) w y in
    renaming_respects_aliases f (e & w ~ y) e /\
    renamed_context f (F § w / v_ref ~ typ_objref R (typ_mut_marker B)) F e.
Proof.
  intros Hdom Hfv Henv Hneq Hvis Hbind f.
  pose proof (ty_var_var typing_mode e Hbind) as Hloc.
  assert (HK : names_agree_on (ctx_dom F \u ctx_fv F) f (fun v => v)).
  { apply replace_name_fresh, notin_union. auto. }
  assert (HR : rename_typ f R = R).
  { apply rename_typ_inactive, replace_name_fresh.
    intro Hbad. apply Hfv.
    eapply bound_type_free_in_context; [exact Hbind |].
    cbn [fv TypFreeVar fv_typ fv_dec]. rewrite in_union; auto. }
  split.
  - intros a b Hb. apply binds_push_inv in Hb as [[-> ->] | [Haw Hb]].
    + unfold f. rewrite replace_name_at, replace_name_away by congruence.
      apply tyq_var_refl.
    + unfold f.
      apply replace_name_respects_aliases with (e := e); [exact Henv | | exact Hb].
      intros u v Huv. now apply tyq_var_binds.
  - apply renamed_context_discharge.
    + now apply rename_context_identity_on_scope.
    + unfold f at 1. rewrite replace_name_at.
      normalize_renamed_syntax. rewrite HR.
      apply ty_var_and.
      * eapply ty_var_sub; [exact Hloc | apply subtyp_and11].
      * eapply ty_var_sub with (T := typ_mut_marker typ_bot);
          [| apply capability_widen; intros; apply subtyp_bot].
        eapply ty_var_sub; [exact Hloc | apply subtyp_and12].
    + unfold f. now rewrite replace_name_at.
Qed.

Local Lemma alias_extension_reflects_variable F e w y R B x T :
    w \notin ctx_dom F ->
    w \notin ctx_fv F ->
    w \notin fv_renv e ->
    w <> y ->
    w <> x ->
    w \notin fv T ->
    ctx_vis F y ->
    ctx_binds y (typ_objref R (typ_mut_marker typ_bot)) F ->
    (F § w / v_ref ~ typ_objref R (typ_mut_marker B))
      ⁏ (e & w ~ y) ⊢ trm_var (avar_f x) ∶ T ->
    F ⁏ e ⊢ trm_var (avar_f x) ∶ T.
Proof.
  intros Hdom Hfv Hfresh Hwy Hwx HT Hy Hloc Hty.
  destruct (@alias_extension_collapse F e w y R B Hdom Hfv Hfresh Hwy Hy Hloc)
    as [He Hctx].
  set (f := replace_name (fun v => v) w y) in *.
  assert (Hfix : renaming_fixes_outside \{w} f).
  { intros p Hp. rewrite notin_singleton in Hp. now apply replace_name_away. }
  pose proof (proj1 term_typing_renaming _ _ _ _ _ Hty f _ F e Hfix He Hctx Hctx) as Hty'.
  cbn [rename_objctx] in Hty'.
  normalize_renamed_in Hty'.
  rewrite rename_typ_inactive in Hty' by (now apply replace_name_fresh).
  unfold f in Hty'. now rewrite replace_name_away in Hty' by congruence.
Qed.

Local Lemma extends_reference_environment e e' :
    env_binds_more e e' ->
    renaming_respects_aliases (fun x => x) e e'.
Proof. intros H w y Hb. apply tyq_var_binds. now apply H. Qed.

Local Lemma identity_renaming_of_contexts F F' e' :
    typing_context_extends F F' e' ->
    renamed_context (fun x => x) F F' e'.
Proof.
  intros [Hbind Hvis]. split; [| exact Hvis].
  intros x T Hb. rewrite (proj1 rename_types_identity).
  now apply Hbind.
Qed.

Local Lemma weaken_stack_env F F' e e' T s U :
    ty_stack F e T s U ->
    env_binds_more e e' ->
    typing_context_extends F F' e' ->
    ty_stack F' e' T s U.
Proof.
  intros Hstack. induction Hstack; intros He HF.
  - apply ty_stack_nil.
    pose proof (@renamed_subtyping G F' e e' (fun v => v) \{} _ _
      (fun _ _ => eq_refl) (extends_reference_environment He)
      (proj1 (identity_renaming_of_contexts HF)) H) as Hsub.
    now rewrite !(proj1 rename_types_identity) in Hsub.
  - eapply ty_stack_let with (L := L \u ctx_dom F').
    + auto.
    + intros x Hx. apply notin_union in Hx as [HxL HxF].
      pose proof (typing_context_extends_push v_let S HxF HF) as Hext.
      pose proof (identity_renaming_of_contexts Hext) as Hrename.
      pose proof (proj1 term_typing_renaming _ _ _ _ _ (H x HxL)
        (fun v => v) \{} _ e' (fun _ _ => eq_refl)
        (extends_reference_environment He) Hrename Hrename) as Hbody.
      cbn [rename_objctx] in Hbody.
      now rewrite (proj1 rename_terms_identity), (proj1 rename_types_identity) in Hbody.
Qed.

Local Lemma extend_context_typing F e' w k A :
    w §# F -> typing_context_extends F (F § w / k ~ A) e'.
Proof.
  intros Hfresh. split.
  - intros x T Hb. apply ty_var_var.
    now apply fresh_context_extension.
  - intros x Hv. apply ctx_vis_n; [| exact Hv].
    intros ->. apply Hfresh. now apply visibility_in_context_domain.
Qed.

Local Lemma renv_correspondence_extend_scope F e w k A :
    renv_corr F e ->
    w §# F ->
    renv_corr (F § w / k ~ A) e.
Proof.
  intros H. induction H; intros Hfresh.
  - apply renv_corr_empty.
  - eapply renv_corr_ref; [| eassumption | eassumption | auto].
    apply ctx_binds_k_n; [| exact H].
    intros ->. apply Hfresh.
    eapply kind_domain_in_context_domain, kind_binding_in_kind_domain; exact H.
Qed.

Local Lemma kind_keep_under_binding F w k A x l :
    w §# F -> ctx_k F x l -> ctx_k (F § w / k ~ A) x l.
Proof.
  intros Hfresh (B & G & Hb). exists B, G.
  apply ctx_binds_k_n; [| exact Hb].
  intros ->. apply Hfresh.
  eapply kind_domain_in_context_domain, kind_binding_in_kind_domain; exact Hb.
Qed.

Local Lemma definitions_keep_kinds F w k A ds :
    w §# F ->
    defs_varkinds F ds ->
    defs_varkinds (F § w / k ~ A) ds.
Proof.
  intros Hfresh Hk. induction Hk.
  - constructor.
  - apply defs_varkinds_cons; [now apply IHHk |].
    inversion H; subst; constructor.
    + now apply kind_keep_under_binding.
    + intros p Hp. apply kind_keep_under_binding; auto.
Qed.

Local Lemma heap_reference_extension F e S w y R B G :
    heap_correspond F e S ->
    ctx_binds_k_after y v_loc (typ_objref R (typ_mut_marker typ_bot)) F G ->
    w §# F ->
    w # e ->
    heap_correspond (F § w / v_ref ~ typ_objref R (typ_mut_marker B)) (e & w ~ y) S.
Proof.
  intros (Hok & Hscope & Hheap & Henv & Hloc & Href & Hcorr & Hitem)
    Hbound Hfresh HfreshEnv.
  set (A := typ_objref R (typ_mut_marker B)).
  set (F' := F § w / v_ref ~ A).
  assert (He : env_binds_more e (e & w ~ y)).
  { intros b a Hb. apply binds_push_neq; [exact Hb |].
    intros ->. exact (binds_fresh_inv Hb HfreshEnv). }
  assert (HF : typing_context_extends F F' (e & w ~ y)).
  { unfold F'. now apply extend_context_typing. }
  split; [constructor; assumption |].
  split; [constructor; assumption |].
  split; [exact Hheap |].
  split; [now apply ok_push |].
  split.
  { simpl ctx_kdom. rewrite If_r by discriminate. exact Hloc. }
  split.
  { simpl ctx_kdom. rewrite If_l by reflexivity. now rewrite Href, dom_push. }
  split.
  { eapply renv_corr_ref with (G2 := F) (G3 := G)
      (Tw := A) (Ty := typ_objref R (typ_mut_marker typ_bot)).
    - apply ctx_binds_k_e.
    - exact Hbound.
    - constructor. destruct typing_mode; simpl in *; try discriminate;
        exists B; auto.
    - now apply renv_correspondence_extend_scope. }
  intros x Hx. specialize (Hitem x Hx). inversion Hitem; subst.
  - pose proof mode_disallows_functions. congruence.
  - eapply ty_item_obj_s; [| eassumption | reflexivity | |].
    + unfold F'. eapply fresh_context_extension; eassumption.
    + pose proof (identity_renaming_of_contexts HF) as Hrename.
      match goal with Hd : F §§ objctx_heap x ?U ⁏ e ⊢ ?ds ∶ open x ?U |- _ =>
        pose proof (proj2 (proj2 (proj2 term_typing_renaming))
          F (objctx_heap x U) e ds _ Hd (fun v => v) \{} F' (e & w ~ y)
          (fun _ _ => eq_refl) (extends_reference_environment He) Hrename Hrename)
          as Hdefs
      end.
      cbn [rename_objctx] in Hdefs.
      now rewrite (proj2 (proj2 (proj2 rename_terms_identity))),
        !(proj1 rename_types_identity) in Hdefs.
    + unfold F'. now apply definitions_keep_kinds.
Qed.

Local Lemma union_with_nocap_subtyping G e A B :
    G ⁏ e ⊢ A <: B ->
    G ⁏ e ⊢ typ_or A typ_nocap <: typ_or B typ_nocap.
Proof.
  intros H. apply subtyp_or2; [| apply subtyp_or12].
  eapply subtyp_trans; [exact H | apply subtyp_or11].
Qed.

Local Lemma merge_nocap_unions G e A B :
    G ⁏ e ⊢ typ_and (typ_or A typ_nocap) (typ_or B typ_nocap)
      <: typ_or (typ_and A B) typ_nocap.
Proof.
  eapply subtyp_trans; [apply subtyp_dist |].
  apply subtyp_or2.
  - eapply subtyp_trans; [| eapply subtyp_trans; [apply subtyp_dist |]].
    + apply subtyp_and2; [apply subtyp_and12 | apply subtyp_and11].
    + apply subtyp_or2.
      * eapply subtyp_trans; [| apply subtyp_or11].
        apply subtyp_and2; [apply subtyp_and12 | apply subtyp_and11].
      * eapply subtyp_trans; [apply subtyp_and12 | apply subtyp_or12].
  - eapply subtyp_trans; [apply subtyp_and12 | apply subtyp_or12].
Qed.

Local Lemma alias_inherits_nocap_disjunction G e (y : var) T :
    G ⁏ e ⊢ y ∶ T ->
    forall w,
      e ⊢ y ≈ w ->
      (forall A, ctx_binds y A G -> G ⁏ e ⊢ w ∶ typ_or A typ_nocap) ->
      G ⁏ e ⊢ w ∶ typ_or T typ_nocap.
Proof.
  intros Hty. induction Hty; intros w Halias Hbind.
  - now apply Hbind.
  - assert (Hmode : mode_has_incap typing_mode)
      by (destruct typing_mode; simpl in *; discriminate || reflexivity).
    assert (Hopen : G ⁏ e ⊢ w ∶ open x T).
    { eapply ty_var_sub; [now apply IHHty |].
      apply subtyp_or2; [apply subtyp_refl |].
      eapply incap_result_accepts_nocap; eauto. }
    assert (Heq : e ⊢ open x T ≈ open w T).
    { eapply independent_type_open_alias; eauto. }
    eapply ty_var_sub; [| apply subtyp_or11].
    apply ty_rec_intro; [| assumption |].
    + eapply ty_var_sub; [exact Hopen | now apply subtyp_tyq].
    + intros. eapply incap_identity_respects_equiv; eauto.
  - eapply ty_var_sub; [| apply subtyp_or11].
    eapply ty_var_sub with (T := open w T).
    + apply ty_rec_elim; [| assumption].
      eapply ty_var_sub; [now apply IHHty |].
      apply subtyp_or2; [apply subtyp_refl | apply subtyp_nocap_bnd].
    + apply subtyp_tyq. eapply independent_type_open_alias; eauto using tyq_var_sym.
  - eapply ty_var_sub; [| apply merge_nocap_unions].
    apply ty_var_and; auto.
  - eapply ty_var_sub; [now apply IHHty | now apply union_with_nocap_subtyping].
  - eapply ty_var_sub; [| apply subtyp_or11].
    eapply ty_var_mut_top; [exact Hmm | now apply IHHty].
Qed.

Local Lemma top_admits_nocap_or_mutable G e :
    mode_has_top_nm_subtype typing_mode ->
    G ⁏ e ⊢ typ_top <: typ_or (typ_mut_marker typ_bot) typ_nocap.
Proof.
  intros Hmode. assert (H : G ⁏ e ⊢ typ_top <:
    typ_or typ_nocap (typ_mut_marker typ_bot)).
  { destruct typing_mode; simpl in *; try discriminate;
      first [apply subtyp_nocap_mut_top_boundless; reflexivity
            | apply subtyp_nocap_mut_top_complement; reflexivity]. }
  eapply subtyp_trans; [exact H |].
  apply subtyp_or2; [apply subtyp_or12 | apply subtyp_or11].
Qed.

Local Lemma alias_inherits_type_admitting_nocap F e y w R B T :
    mode_has_top_nm_subtype typing_mode ->
    binds w y e ->
    ctx_binds y (typ_objref R (typ_mut_marker typ_bot)) F ->
    ctx_binds w (typ_objref R (typ_mut_marker B)) F ->
    F ⁏ e ⊢ y ∶ T ->
    F ⁏ e ⊢ typ_nocap <: T ->
    F ⁏ e ⊢ w ∶ T.
Proof.
  intros Hmode Halias Hy Hw Hty Hsub.
  eapply ty_var_sub; [| apply subtyp_or2; [apply subtyp_refl | exact Hsub]].
  eapply alias_inherits_nocap_disjunction; [exact Hty | |].
  - apply tyq_var_sym. now apply tyq_var_binds.
  - intros U Hb. rewrite (context_binding_unique Hb Hy).
    eapply ty_var_sub.
    + apply ty_var_and.
      * eapply ty_var_sub; [exact (ty_var_var typing_mode e Hw) | apply subtyp_and11].
      * eapply ty_var_sub; [exact (ty_var_var typing_mode e Hw) |].
        eapply subtyp_trans; [apply subtyp_top | now apply top_admits_nocap_or_mutable].
    + eapply subtyp_trans; [apply subtyp_dist |].
      apply subtyp_or2; [apply subtyp_or11 |].
      eapply subtyp_trans; [apply subtyp_and12 | apply subtyp_or12].
Qed.

Local Lemma incap_type_weakens F e A B :
    F ⁏ e ⊢ A ∶icp B -> F ⁏ e ⊢ A <: B.
Proof.
  intros H. induction H; try solve [apply subtyp_refl | apply subtyp_top | apply subtyp_bot].
  - eapply subtyp_trans; [eapply subtyp_sel1; eassumption | assumption].
  - apply subtyp_and2;
      eapply subtyp_trans; [apply subtyp_and11 | eassumption | apply subtyp_and12 | eassumption].
  - apply subtyp_or2;
      eapply subtyp_trans; [eassumption | apply subtyp_or11 | eassumption | apply subtyp_or12].
Qed.

Local Lemma viewpoint_for_mutability :
    mode_viewpoint_adaptation' typing_mode = mode_viewpoint_adapt_mutability.
Proof. destruct typing_mode; simpl in *; discriminate || reflexivity. Qed.

Local Lemma read_typing_operands F e t T :
    F ⁏ e ⊢ t ∶ T ->
    forall w a, t = trm_read (avar_f w) a ->
    exists L U V,
      F ⁏ e ⊢ w ∶ typ_rcd (dec_fld a L U) /\
      F ⁏ e ⊢ w ▷ U ⟶ V /\
      F ⁏ e ⊢ V <: T.
Proof.
  intros Hty. induction Hty; intros w0 a0 Heq; try discriminate.
  - inversion Heq; subst. do 3 eexists. repeat split; eauto using subtyp_refl.
  - destruct (IHHty w0 a0 Heq) as (L & U0 & V & Hfield & Hadapt & Hsub).
    exists L, U0, V. repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

Local Lemma heap_field_value_typing F e S y ds a z :
    heap_correspond F e S ->
    binds y (item_obj ds) S ->
    defs_has ds (def_fld a (avar_f z)) ->
    exists R M A,
      ctx_binds y (typ_objref R M) F /\
      record_has (open y R) (dec_fld a A A) /\
      F ⁏ e ⊢ z ∶ A /\ ctx_k F z v_loc.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hitem) Hbind Hfield.
  specialize (Hitem y (binding_in_domain Hbind)). inversion Hitem; subst.
  - pose proof mode_disallows_functions. congruence.
  - match goal with
    | Hobj : binds y (item_obj ?os) S,
      Hty : F §§ _ ⁏ e ⊢ ?os ∶ _ |- _ =>
        pose proof (binds_functional Hobj Hbind) as Heq;
        inversion Heq; subst;
        destruct (typed_defs_member_record Hty Hfield) as [D [Hmember HD]]
    end.
    inversion HD; subst. do 3 eexists. repeat split; try eassumption.
    match goal with HK : defs_varkinds F ds |- _ =>
      clear -HK Hfield; induction HK as [| G ds d HK IH HKd]
    end.
    + discriminate.
    + unfold defs_has in Hfield. simpl get_def in Hfield.
      destruct (classic (label_of d = label_of (def_fld a (avar_f z)))) as [Heq | Hneq].
      * rewrite If_l in Hfield by exact Heq. inversion Hfield; subst.
        now inversion HKd.
      * rewrite If_r in Hfield by exact Hneq. now apply IH.
Qed.

Local Lemma typing_context_extends_trans F G H e :
    typing_context_extends F G e ->
    typing_context_extends G H e ->
    typing_context_extends F H e.
Proof.
  intros [HFG VFG] [HGH VGH]. split.
  - intros x A Hb. eapply replace_var_typing; [exact HGH | now apply HFG].
  - intros x Hv. apply VGH, VFG, Hv.
Qed.

Local Lemma typed_literal_operands F e t T :
    F ⁏ e ⊢ t ∶ T ->
    forall R ds u, t = trm_lit (lit_obj R ds) u ->
    exists L L' A,
      (forall x, x \notin L -> F §§ objctx_lit x R ⁏ e ⊢ open x ds ∶ open x R) /\
      typ_indep_b 0 R /\
      (forall x, x \notin L' ->
        F § x / v_let ~ typ_objref R (typ_mut_marker typ_bot) ⁏ e ⊢ open x u ∶ A) /\
      F ⁏ e ⊢ A <: T.
Proof.
  assert (Hmode : mode_objlit_refcaps' typing_mode = mode_objlit_refcaps_mutable)
    by (destruct typing_mode; simpl in *; discriminate || reflexivity).
  intros Hty. induction Hty; intros R ds u0 Heq; try discriminate.
  - inversion Heq; subst.
    match goal with HL : _ ⁏ _ ⊢ lit_obj _ _ ∶ _ |- _ => inversion HL; subst end.
    rewrite Hmode in *.
    do 3 eexists. repeat split; eauto using subtyp_refl.
  - destruct (IHHty R ds u0 Heq) as (L & L' & A & Hds & Hind & Hu & Hsub).
    exists L, L', A. repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

Local Lemma typed_def_is_record_declaration G Go e d D :
    G §§ Go ⁏ e ⊢ d ∶d D -> record_dec D.
Proof. intros H; destruct H; constructor. Qed.

Local Lemma typed_defs_are_record G Go e ds R :
    G §§ Go ⁏ e ⊢ ds ∶ R ->
    exists ls, record_typ R ls /\
      forall l, l \in ls -> exists d, label_of d = l /\ defs_has ds d.
Proof.
  intros Hty. induction Hty as [G Go e d D Hd | G Go e ds d T D Hds IH Hd Hno].
  - exists \{label_of D}. split.
    + apply rt_one; [eapply typed_def_is_record_declaration; eassumption | reflexivity].
    + intros l Hin. rewrite in_singleton in Hin. subst l.
      assert (Hl : label_of d = label_of D) by (inversion Hd; reflexivity).
      exists d. split; [exact Hl |].
      unfold defs_has. simpl get_def. now rewrite If_l by reflexivity.
  - destruct IH as (ls & Hrecord & Hlookup).
    assert (Hl : label_of d = label_of D) by (inversion Hd; reflexivity).
    exists (ls \u \{label_of D}). split.
    + apply rt_cons; [exact Hrecord | eapply typed_def_is_record_declaration; eassumption |
                        reflexivity |].
      intro Hin. destruct (Hlookup _ Hin) as (d' & Hl' & Hmember).
      unfold defs_hasnt, defs_has in *. rewrite Hl in *.
      rewrite Hl' in Hmember. congruence.
    + intros l Hin. rewrite in_union, in_singleton in Hin.
      destruct (classic (l = label_of d)) as [-> | Hneq].
      * exists d. split; [reflexivity |].
        unfold defs_has. simpl get_def. now rewrite If_l by reflexivity.
      * destruct Hin as [Hin | Hin]; [| congruence].
        destruct (Hlookup _ Hin) as (d' & Hl' & Hmember).
        exists d'. split; [exact Hl' |].
        unfold defs_has in *. simpl get_def.
        now rewrite If_r by congruence.
Qed.

Local Definition close_fresh_avar x a k :=
  match a with
  | avar_f y => If x = y then avar_b k else avar_f y
  | avar_b n => avar_b n
  end.

Local Lemma close_fresh_after_open_avar x a k :
    x \notin fv a ->
    close_fresh_avar x (open_rec k x a) k = a.
Proof.
  destruct a as [n | y]; intros Hz.
  - cbn [open_rec AvarOpenable].
    destruct (Nat.eq_dec k n) as [-> | Hneq].
    + rewrite If_l by reflexivity. unfold close_fresh_avar.
      now rewrite If_l by reflexivity.
    + rewrite If_r by assumption. reflexivity.
  - change (x \notin \{y}) in Hz.
    rewrite notin_singleton in Hz.
    unfold close_fresh_avar; cbn [open_rec AvarOpenable].
    now rewrite If_r by assumption.
Qed.

Local Lemma close_fresh_after_open_types :
    (forall T n x, x \notin fv T ->
       transform_typ (close_fresh_avar x) (open_rec n x T) n = T) /\
    (forall D n x, x \notin fv D ->
       transform_dec (close_fresh_avar x) (open_rec n x D) n = D).
Proof.
  apply typ_mutind; intros; cbn [open_rec TypOpenable DecOpenable open_rec_typ open_rec_dec
    transform_typ transform_dec] in *; try reflexivity.
  all: cbn [fv TypFreeVar DecFreeVar fv_typ fv_dec] in *;
    repeat rewrite notin_union in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    f_equal; eauto using close_fresh_after_open_avar.
Qed.

Local Lemma open_fresh_type_injective (B C : typ) n x :
    x \notin fv B -> x \notin fv C ->
    open_rec n x B = open_rec n x C -> B = C.
Proof.
  intros HB HC Heq.
  rewrite <- (proj1 close_fresh_after_open_types B n x HB),
          <- (proj1 close_fresh_after_open_types C n x HC).
  now rewrite Heq.
Qed.

Local Lemma unopened_record_declaration D k x :
    x \notin fv D ->
    record_dec (open_rec k x D) ->
    record_dec D.
Proof.
  intros Hfresh Hdec. destruct D as [a B C | a B C | m B C R].
  all: cbn [fv DecFreeVar fv_dec] in Hfresh; repeat rewrite notin_union in Hfresh.
  - destruct a; cbn [open_rec DecOpenable open_rec_dec] in Hdec; inversion Hdec; subst.
    + destruct Hfresh. assert (B = C) by (eapply open_fresh_type_injective; eassumption).
      subst. constructor.
    + assert (B = typ_bot).
      { destruct B; cbn [open_rec TypOpenable open_rec_typ] in *; congruence. }
      subst. constructor.
  - cbn [open_rec DecOpenable open_rec_dec] in Hdec. inversion Hdec.
    destruct Hfresh. assert (B = C) by (eapply open_fresh_type_injective; eassumption).
    subst. constructor.
  - constructor.
Qed.

Local Lemma unopened_record_typ R ls k x :
    x \notin fv R -> record_typ (open_rec k x R) ls -> record_typ R ls.
Proof.
  revert ls k x. induction R; intros ls k x HF HR;
    cbn [open_rec TypOpenable open_rec_typ] in HR;
    inversion HR; subst.
  - apply rt_one.
    + eapply unopened_record_declaration; eassumption.
    + apply open_preserves_declaration_label.
  - destruct R2; cbn [open_rec_typ] in *; try discriminate.
    cbn [fv TypFreeVar fv_typ] in HF. rewrite notin_union in HF.
    destruct HF as [Hleft Hright].
    match goal with
    | Heq : typ_rcd ?D = open_rec k x (typ_rcd ?d) |- _ =>
        change (typ_rcd D = typ_rcd (open_rec k x d)) in Heq;
        inversion Heq; subst D
    end.
    try rewrite open_preserves_declaration_label in *.
    eapply rt_cons; [eapply IHR1; eassumption | | reflexivity | eassumption].
    eapply unopened_record_declaration; eassumption.
Qed.

(* The ideals of the original subtyping order provide joins for assigning
   meanings to recursive selection bounds. A principal ideal remembers its
   original subtyping judgment. *)
Section WithIdealOrder.
Context (F : ctx) (e : renv).

Record subtype_ideal := {
  ideal_has : typ -> Prop;
  ideal_has_bot : ideal_has typ_bot;
  ideal_lower : forall A B, F ⁏ e ⊢ A <: B -> ideal_has B -> ideal_has A;
  ideal_closed_join : forall A B, ideal_has A -> ideal_has B -> ideal_has (typ_or A B)
}.

Local Definition ideal_below (I J : subtype_ideal) :=
  forall A, ideal_has I A -> ideal_has J A.

Local Lemma ideal_below_trans I J K :
    ideal_below I J -> ideal_below J K -> ideal_below I K.
Proof. unfold ideal_below. auto. Qed.

Local Definition ideal_principal (T : typ) : subtype_ideal.
Proof.
  refine {| ideal_has A := F ⁏ e ⊢ A <: T |}.
  - apply subtyp_bot.
  - intros; eapply subtyp_trans; eassumption.
  - intros; now apply subtyp_or2.
Defined.

Local Lemma ideal_principal_below A B :
    F ⁏ e ⊢ A <: B -> ideal_below (ideal_principal A) (ideal_principal B).
Proof. intros H T HT. cbn in *. eapply subtyp_trans; eassumption. Qed.

Local Lemma ideal_principal_intro A I :
    ideal_has I A -> ideal_below (ideal_principal A) I.
Proof. intros H T HT. eapply ideal_lower; [exact HT | exact H]. Qed.

Local Lemma ideal_principal_elim A B :
    ideal_below (ideal_principal A) (ideal_principal B) -> F ⁏ e ⊢ A <: B.
Proof. intros H. apply (H A). apply subtyp_refl. Qed.

Local Lemma ideal_bot_least I : ideal_below (ideal_principal typ_bot) I.
Proof. apply ideal_principal_intro, ideal_has_bot. Qed.

Local Lemma ideal_top_greatest I : ideal_below I (ideal_principal typ_top).
Proof. intros A _. apply subtyp_top. Qed.

Local Definition ideal_meet (I J : subtype_ideal) : subtype_ideal.
Proof.
  refine {| ideal_has A := ideal_has I A /\ ideal_has J A |}.
  - split; apply ideal_has_bot.
  - intros A B H [HI HJ]. split; eapply ideal_lower; eassumption.
  - intros A B [HIA HJA] [HIB HJB]. split; apply ideal_closed_join; assumption.
Defined.

Local Definition ideal_join (I J : subtype_ideal) : subtype_ideal.
Proof.
  refine {| ideal_has A :=
    exists B C, ideal_has I B /\ ideal_has J C /\ F ⁏ e ⊢ A <: typ_or B C |}.
  - exists typ_bot, typ_bot. repeat split; first [apply ideal_has_bot | apply subtyp_bot].
  - intros A B H (P & Q & HP & HQ & HB). exists P, Q.
    repeat split; try assumption. eapply subtyp_trans; eassumption.
  - intros A B (P & Q & HP & HQ & HA) (R & S & HR & HS & HB).
    exists (typ_or P R), (typ_or Q S).
    split; [now apply ideal_closed_join |].
    split; [now apply ideal_closed_join |].
    apply subtyp_or2.
    + eapply subtyp_trans; [exact HA |].
      apply subtyp_or2; eapply subtyp_trans;
        [apply subtyp_or11 | apply subtyp_or11 | apply subtyp_or11 | apply subtyp_or12].
    + eapply subtyp_trans; [exact HB |].
      apply subtyp_or2; eapply subtyp_trans;
        [apply subtyp_or12 | apply subtyp_or11 | apply subtyp_or12 | apply subtyp_or12].
Defined.

Local Lemma ideal_join_left I J : ideal_below I (ideal_join I J).
Proof.
  intros A HA. exists A, typ_bot. repeat split; auto using ideal_has_bot, subtyp_or11.
Qed.

Local Lemma ideal_join_right I J : ideal_below J (ideal_join I J).
Proof.
  intros A HA. exists typ_bot, A. repeat split; auto using ideal_has_bot, subtyp_or12.
Qed.

Local Lemma ideal_join_lub I J K :
    ideal_below I K -> ideal_below J K -> ideal_below (ideal_join I J) K.
Proof.
  intros HI HJ A (B & C & HB & HC & Hsub).
  eapply ideal_lower; [exact Hsub |]. apply ideal_closed_join; auto.
Qed.

Local Lemma ideal_meet_mono I J I' J' :
    ideal_below I I' -> ideal_below J J' -> ideal_below (ideal_meet I J) (ideal_meet I' J').
Proof. intros HI HJ A [HA HB]. split; auto. Qed.

Local Lemma ideal_join_mono I J I' J' :
    ideal_below I I' -> ideal_below J J' -> ideal_below (ideal_join I J) (ideal_join I' J').
Proof.
  intros HI HJ. apply ideal_join_lub;
    eapply ideal_below_trans; eauto using ideal_join_left, ideal_join_right.
Qed.

Local Lemma ideal_distributes I J K :
    ideal_below (ideal_meet I (ideal_join J K))
      (ideal_join (ideal_meet I J) (ideal_meet I K)).
Proof.
  intros A (HA & B & C & HB & HC & Hsub).
  exists (typ_and A B), (typ_and A C).
  split; [split | split; [split |]].
  - eapply ideal_lower; [apply subtyp_and11 | exact HA].
  - eapply ideal_lower; [apply subtyp_and12 | exact HB].
  - eapply ideal_lower; [apply subtyp_and11 | exact HA].
  - eapply ideal_lower; [apply subtyp_and12 | exact HC].
  - eapply subtyp_trans; [| apply subtyp_dist].
    apply subtyp_and2; [apply subtyp_refl | exact Hsub].
Qed.

Local Definition ideal_sup (P : subtype_ideal -> Prop) : subtype_ideal.
Proof.
  refine {| ideal_has A := forall J, (forall I, P I -> ideal_below I J) -> ideal_has J A |}.
  - intros; apply ideal_has_bot.
  - intros A B Hab HB J HJ. eapply ideal_lower; [exact Hab | auto].
  - intros A B HA HB J HJ. apply ideal_closed_join; auto.
Defined.

Local Lemma ideal_sup_lower P I : P I -> ideal_below I (ideal_sup P).
Proof. intros HI A HA J HJ. now apply (HJ I). Qed.

Local Lemma ideal_sup_least P I :
    (forall J, P J -> ideal_below J I) -> ideal_below (ideal_sup P) I.
Proof. intros HI A HA. exact (HA I HI). Qed.

Local Lemma cofinite_opened_subtyping (L : vars) (A B : typ) :
    (forall x, x \notin L -> F ⁏ e ⊢ open x A <: open x B) ->
    forall x, F ⁏ e ⊢ open x A <: open x B.
Proof.
  intros H x.
  destruct (var_fresh (L \u ((fv A \u fv B) \u ((ctx_dom F \u ctx_fv F) \u fv_renv e))))
    as [z Hz].
  apply notin_union in Hz as [HzL Hz].
  apply notin_union in Hz as [HzTypes Hz].
  apply notin_union in Hz as [HzCtx HzEnv].
  set (f := replace_name (fun v => v) z x).
  assert (Hfix : renaming_fixes_outside \{z} f).
  { intros u Hu. rewrite notin_singleton in Hu. now apply replace_name_away. }
  assert (Henv : renaming_respects_aliases f e e).
  { apply replace_name_respects_aliases; [exact HzEnv |].
    intros a b Hab. now apply tyq_var_binds. }
  assert (HF : renamed_context f F F e).
  { apply rename_context_identity_on_scope. now apply replace_name_fresh. }
  pose proof (@renamed_subtyping F F e e f \{z} _ _ Hfix Henv (proj1 HF) (H z HzL)) as Hsub.
  rewrite !rename_typ_opens in Hsub.
  assert (Hmap : f z = x) by apply replace_name_at. rewrite Hmap in Hsub.
  apply notin_union in HzTypes as [HzA HzB].
  rewrite !rename_typ_inactive in Hsub by (unfold f; apply replace_name_fresh; assumption).
  exact Hsub.
Qed.

Context (avoid : vars).

Definition ideal_capability (I : var -> subtype_ideal) : subtype_ideal.
Proof.
  refine {| ideal_has A := exists B,
    (forall z, z \notin avoid -> ideal_has (I z) (open z B)) /\
    F ⁏ e ⊢ A <: typ_mut_marker B |}.
  - exists typ_bot. split; [intros; apply ideal_has_bot | apply subtyp_bot].
  - intros A B HAB (C & HC & HBC). exists C. split; [exact HC |].
    eapply subtyp_trans; eassumption.
  - intros A B (C & HC & HAC) (D & HD & HBD). exists (typ_or C D).
    split; [intros; apply ideal_closed_join; auto |].
    apply subtyp_or2.
    + eapply subtyp_trans; [exact HAC |].
      apply capability_widen; intros; apply subtyp_or11.
    + eapply subtyp_trans; [exact HBD |].
      apply capability_widen; intros; apply subtyp_or12.
Defined.

Local Lemma ideal_capability_mono I J :
    (forall z, z \notin avoid -> ideal_below (I z) (J z)) ->
    ideal_below (ideal_capability I) (ideal_capability J).
Proof.
  intros H A (B & HB & HAB). exists B. split; [| exact HAB].
  intros z Hz. apply H; auto.
Qed.

Local Lemma ideal_capability_meet I J :
    ideal_below (ideal_meet (ideal_capability I) (ideal_capability J))
      (ideal_capability (fun z => ideal_meet (I z) (J z))).
Proof.
  intros A ((B & HB & HAB) & (C & HC & HAC)).
  exists (typ_and B C). split.
  - intros z Hz. split.
    + eapply ideal_lower; [apply subtyp_and11 | auto].
    + eapply ideal_lower; [apply subtyp_and12 | auto].
  - eapply subtyp_trans; [| apply capability_intersection].
    now apply subtyp_and2.
Qed.

Local Lemma ideal_capability_principal_l B I :
    (forall z, z \notin avoid -> ideal_has (I z) (open z B)) ->
    ideal_below (ideal_principal (typ_mut_marker B)) (ideal_capability I).
Proof. intros HB A HA. exists B. auto. Qed.

Local Lemma ideal_capability_principal_r B :
    ideal_below (ideal_capability (fun z => ideal_principal (open z B)))
      (ideal_principal (typ_mut_marker B)).
Proof.
  intros A (C & HC & HA). eapply subtyp_trans; [exact HA |].
  apply capability_widen. exact (@cofinite_opened_subtyping avoid C B HC).
Qed.

End WithIdealOrder.

Local Definition names_outside (L V : vars) := forall x, x \in V -> x \notin L.

Local Lemma names_outside_union L A B :
    names_outside L (A \u B) <-> names_outside L A /\ names_outside L B.
Proof.
  unfold names_outside. split.
  - intros H. split; intros x Hx; apply H; rewrite in_union; auto.
  - intros [HA HB] x Hx. rewrite in_union in Hx. destruct Hx; auto.
Qed.

Local Lemma names_outside_open_avar L (a : avar) n z :
    z \notin L -> names_outside L (fv a) -> names_outside L (fv (open_rec n z a)).
Proof.
  intros Hfresh Ha. destruct a as [k | x]; [| exact Ha].
  cbn [open_rec AvarOpenable]. destruct (Nat.eq_dec n k).
  - rewrite If_l by assumption. intros v Hv. change (v \in \{z}) in Hv.
    rewrite in_singleton in Hv. now subst.
  - rewrite If_r by assumption. exact Ha.
Qed.

Local Lemma names_outside_open_mutual L :
    (forall (T : typ) n z, z \notin L -> names_outside L (fv T) ->
      names_outside L (fv (open_rec n z T))) /\
    (forall (D : dec) n z, z \notin L -> names_outside L (fv D) ->
      names_outside L (fv (open_rec n z D))).
Proof.
  apply typ_mutind; intros;
    cbn [fv TypFreeVar DecFreeVar fv_typ fv_dec open_rec TypOpenable
      DecOpenable open_rec_typ open_rec_dec] in *;
    repeat rewrite names_outside_union in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto using names_outside_open_avar.
Qed.

Local Fixpoint type_size T : nat :=
  match T with
  | typ_and A B | typ_or A B | typ_fun A B => S (type_size A + type_size B)
  | typ_rcd D => S (declaration_size D)
  | typ_bnd A => S (type_size A)
  | _ => 1
  end
with declaration_size D : nat :=
  match D with
  | dec_typ _ A B | dec_fld _ A B => S (type_size A + type_size B)
  | dec_met _ A B C => S (type_size A + type_size B + type_size C)
  end.

Local Lemma opened_type_size_mutual :
    (forall T n z, type_size (open_rec n z T) = type_size T) /\
    (forall D n z, declaration_size (open_rec n z D) = declaration_size D).
Proof.
  apply typ_mutind; intros;
    cbn [type_size declaration_size open_rec TypOpenable DecOpenable open_rec_typ open_rec_dec];
    try reflexivity;
    repeat match goal with H : forall _ _, _ = _ |- _ => rewrite H end;
    reflexivity.
Qed.

Section WithSelectionEvaluation.
Context (F G : ctx) (e p : renv) (avoid : vars).

Local Notation ideal := (subtype_ideal F e).
Local Notation "I ⪯ J" := (ideal_below I J) (at level 70).
Local Notation principal T := (ideal_principal F e T).
Local Notation iBot := (ideal_principal F e typ_bot).
Local Notation iTop := (ideal_principal F e typ_top).
Local Notation iNoCap := (ideal_principal F e typ_nocap).
Local Notation iCap I := (@ideal_capability F e avoid I).

Local Definition evaluates_equally (I J : ideal) := I ⪯ J /\ J ⪯ I.

Local Lemma evaluates_equally_refl I : evaluates_equally I I.
Proof. split; intros A HA; exact HA. Qed.

Local Lemma evaluates_equally_trans I J K :
    evaluates_equally I J -> evaluates_equally J K -> evaluates_equally I K.
Proof. intros [H H'] [K1 K2]; split; eapply ideal_below_trans; eassumption. Qed.

Local Lemma evaluates_equally_sym I J : evaluates_equally I J -> evaluates_equally J I.
Proof. intros [H H']; split; assumption. Qed.

Local Lemma evaluates_equally_meet I I' J J' :
    evaluates_equally I I' -> evaluates_equally J J' ->
    evaluates_equally (ideal_meet I J) (ideal_meet I' J').
Proof. intros [] []; split; now apply ideal_meet_mono. Qed.

Local Lemma evaluates_equally_join I I' J J' :
    evaluates_equally I I' -> evaluates_equally J J' ->
    evaluates_equally (ideal_join I J) (ideal_join I' J').
Proof. intros [] []; split; now apply ideal_join_mono. Qed.

Local Lemma evaluates_equally_capability I J :
    (forall x, x \notin avoid -> evaluates_equally (I x) (J x)) ->
    evaluates_equally (iCap I) (iCap J).
Proof.
  intros H. split; apply ideal_capability_mono; intros x Hx;
    destruct (H x Hx); assumption.
Qed.

Local Definition selection_valuation := var -> typ_label -> var -> ideal.

Local Definition selection_receiver x a :=
  match a with
  | typ_label_normal _ => canonical_location p x
  | typ_label_refcap _ => x
  end.

Local Definition resolve_avar (scope : nat -> option var) a :=
  match a with avar_f x => Some x | avar_b n => scope n end.

Local Definition push_resolved_name (scope : nat -> option var) x n :=
  match n with 0 => Some x | S k => scope k end.

Local Fixpoint evaluate_type (v : selection_valuation) T (scope : nat -> option var) : ideal :=
  match T with
  | typ_bot => iBot
  | typ_nocap => iNoCap
  | typ_and A B => ideal_meet (evaluate_type v A scope) (evaluate_type v B scope)
  | typ_or A B => ideal_join (evaluate_type v A scope) (evaluate_type v B scope)
  | typ_sel a l b =>
    match resolve_avar scope a, resolve_avar scope b with
    | Some x, Some z => v (selection_receiver x l) l z
    | _, _ => iTop
    end
  | typ_rcd D => evaluate_decl v D scope
  | _ => iTop
  end
with evaluate_decl (v : selection_valuation) D (scope : nat -> option var) : ideal :=
  match D with
  | dec_typ (typ_label_refcap _) _ B =>
    iCap (fun x => evaluate_type v B (push_resolved_name scope x))
  | _ => iTop
  end.

Local Definition empty_resolution (_ : nat) : option var := None.
Local Definition evaluate v T := evaluate_type v T empty_resolution.

Local Definition opened_resolution (scope : nat -> option var) n x k :=
  If k = n then Some x else scope k.

Local Lemma resolve_avar_opened a scope n x scope' :
    (forall k, scope' k = opened_resolution scope n x k) ->
    resolve_avar scope (open_rec n x a) = resolve_avar scope' a.
Proof.
  intros H. destruct a as [k | y]; [| reflexivity].
  unfold opened_resolution in H. cbn [resolve_avar open_rec AvarOpenable].
  rewrite H. destruct (Nat.eq_dec n k); subst.
  - now rewrite !If_l by reflexivity.
  - rewrite If_r by assumption. rewrite If_r by congruence. reflexivity.
Qed.

Local Lemma pushed_opened_resolution scope scope' n x a :
    (forall k, scope' k = opened_resolution scope n x k) ->
    forall k, push_resolved_name scope' a k =
      opened_resolution (push_resolved_name scope a) (S n) x k.
Proof.
  intros H [|k]; unfold opened_resolution, push_resolved_name.
  - now rewrite If_r by discriminate.
  - rewrite H. unfold opened_resolution.
    destruct (Nat.eq_dec k n); subst.
    + now rewrite !If_l by reflexivity.
    + now rewrite !If_r by congruence.
Qed.

Local Lemma evaluate_opened_mutual :
    (forall T v scope n x scope',
      (forall k, scope' k = opened_resolution scope n x k) ->
      evaluates_equally (evaluate_type v (open_rec n x T) scope)
        (evaluate_type v T scope')) /\
    (forall D v scope n x scope',
      (forall k, scope' k = opened_resolution scope n x k) ->
      evaluates_equally (evaluate_decl v (open_rec n x D) scope)
        (evaluate_decl v D scope')).
Proof.
  apply typ_mutind; intros;
    cbn [open_rec TypOpenable DecOpenable open_rec_typ open_rec_dec
      evaluate_type evaluate_decl] in *;
    try solve [apply evaluates_equally_refl | eauto using
      evaluates_equally_meet, evaluates_equally_join].
  - rewrite !resolve_avar_opened with (scope' := scope') by assumption.
    apply evaluates_equally_refl.
  - destruct t; [apply evaluates_equally_refl |].
    apply evaluates_equally_capability. intros z Hz.
    eauto using pushed_opened_resolution.
Qed.

Local Lemma evaluate_member_capability v a A B :
    evaluates_equally (evaluate v (typ_rcd (dec_typ (typ_label_refcap a) A B)))
      (iCap (fun z => evaluate v (open z B))).
Proof.
  unfold evaluate. cbn [evaluate_type evaluate_decl]. apply evaluates_equally_capability.
  intros z Hz. apply evaluates_equally_sym.
  apply (proj1 evaluate_opened_mutual). intros [|k].
  - unfold push_resolved_name, opened_resolution. now rewrite If_l by reflexivity.
  - unfold push_resolved_name, opened_resolution. now rewrite If_r by discriminate.
Qed.

Local Definition valuations_below (v w : selection_valuation) :=
  forall x a z, v x a z ⪯ w x a z.

Local Lemma evaluate_monotone_mutual :
    (forall T v w scope, valuations_below v w ->
      evaluate_type v T scope ⪯ evaluate_type w T scope) /\
    (forall D v w scope, valuations_below v w ->
      evaluate_decl v D scope ⪯ evaluate_decl w D scope).
Proof.
  apply typ_mutind; intros;
    cbn [evaluate_type evaluate_decl] in *;
    try solve [intros A HA; exact HA | eauto using ideal_meet_mono, ideal_join_mono].
  - destruct (resolve_avar scope a), (resolve_avar scope a0);
      first [apply H | intros A HA; exact HA].
  - destruct t; [intros A HA; exact HA |].
    apply ideal_capability_mono. eauto.
Qed.

Local Definition selection_upper_step (v : selection_valuation)
    (x : var) (a : typ_label) (z : var) : ideal.
Proof.
  refine {| ideal_has B := forall L U, exact_type_declaration G p x a L U ->
    ideal_has (evaluate v (open z U)) B |}.
  - intros. apply ideal_has_bot.
  - intros B C H HC L U Hdecl.
    eapply ideal_lower; [exact H | exact (HC L U Hdecl)].
  - intros B C HB HC L U Hdecl.
    apply ideal_closed_join; [exact (HB L U Hdecl) | exact (HC L U Hdecl)].
Defined.

Local Lemma selection_upper_step_monotone v w :
    valuations_below v w -> valuations_below (selection_upper_step v) (selection_upper_step w).
Proof.
  intros H x a z B HB L U Hdecl.
  exact (proj1 evaluate_monotone_mutual (open z U) v w empty_resolution H B
    (HB L U Hdecl)).
Qed.

Local Definition bounded_by_upper_step (v : selection_valuation) :=
  valuations_below v (selection_upper_step v).

Local Definition recursive_selection_valuation : selection_valuation :=
  fun x a z => @ideal_sup F e
    (fun I => exists v, bounded_by_upper_step v /\ I = v x a z).

Local Lemma recursive_selection_dominates v :
    bounded_by_upper_step v -> valuations_below v recursive_selection_valuation.
Proof. intros H x a z. apply ideal_sup_lower. exists v. auto. Qed.

Local Lemma recursive_selection_bounded :
    bounded_by_upper_step recursive_selection_valuation.
Proof.
  intros x a z. apply ideal_sup_least.
  intros I (v & Hv & ->). eapply ideal_below_trans; [apply Hv |].
  eapply selection_upper_step_monotone. now apply recursive_selection_dominates.
Qed.

Local Lemma recursive_selection_unfold x a z :
    evaluates_equally (recursive_selection_valuation x a z)
      (selection_upper_step recursive_selection_valuation x a z).
Proof.
  split; [apply recursive_selection_bounded |].
  apply recursive_selection_dominates.
  apply selection_upper_step_monotone, recursive_selection_bounded.
Qed.

Local Lemma evaluate_selection_bound S x a z L U :
    inert G -> heap_correspond G p S ->
    exact_type_declaration G p x a L U ->
    evaluates_equally (evaluate recursive_selection_valuation
      (typ_sel (avar_f x) a (avar_f z)))
      (evaluate recursive_selection_valuation (open z U)).
Proof.
  intros Hinert Hheap Hdecl.
  assert (Hcanon : exact_type_declaration G p (selection_receiver x a) a L U).
  { destruct a; cbn [selection_receiver]; [| exact Hdecl].
    eapply exact_normal_type_declaration_on_alias; [exact Hinert | exact Hheap | | exact Hdecl].
    apply variable_equiv_to_location. }
  change (evaluates_equally
    (recursive_selection_valuation (selection_receiver x a) a z)
    (evaluate recursive_selection_valuation (open z U))).
  eapply evaluates_equally_trans; [apply recursive_selection_unfold |].
  split.
  - intros B HB. exact (HB L U Hcanon).
  - intros B HB L' U' Hdecl'.
    destruct (exact_type_declaration_unique Hinert Hheap Hcanon Hdecl') as [_ <-].
    exact HB.
Qed.

Local Lemma evaluation_respects_equivalence q v T U :
    q ⊢ T ≈ U ->
    (forall x y : var, q ⊢ x ≈ y -> canonical_location p x = canonical_location p y) ->
    evaluates_equally (evaluate v T) (evaluate v U).
Proof.
  intros Hty. induction Hty; intros Hlocations.
  - apply evaluates_equally_refl.
  - inversion H; subst; [apply evaluates_equally_meet | apply evaluates_equally_join]; auto.
  - apply evaluates_equally_refl.
  - apply evaluates_equally_refl.
  - destruct B; [apply evaluates_equally_refl |].
    eapply evaluates_equally_trans; [apply evaluate_member_capability |].
    eapply evaluates_equally_trans; [| apply evaluates_equally_sym, evaluate_member_capability].
    apply evaluates_equally_capability. auto.
  - destruct v3 as [n | z]; [apply evaluates_equally_refl |].
    change (evaluates_equally (v (canonical_location p v1) (typ_label_normal l) z)
      (v (canonical_location p v2) (typ_label_normal l) z)).
    rewrite (Hlocations _ _ H). apply evaluates_equally_refl.
  - apply evaluates_equally_refl.
  - apply evaluates_equally_refl.
  - apply evaluates_equally_refl.
Qed.

Local Lemma evaluate_equivalence S v T U :
    heap_correspond G p S ->
    p ⊢ T ≈ U ->
    evaluates_equally (evaluate v T) (evaluate v U).
Proof.
  intros Hheap Hty. eapply evaluation_respects_equivalence; [exact Hty |].
  intros x y Hxy. eapply equivalent_variables_share_location; eassumption.
Qed.

Local Lemma evaluate_mutable_literal v :
    evaluates_equally (evaluate v (typ_mut_marker typ_bot))
      (principal (typ_mut_marker typ_bot)).
Proof.
  change (evaluates_equally (iCap (fun _ => iBot)) (principal (typ_mut_marker typ_bot))).
  split.
  - exact (@ideal_capability_principal_r F e avoid typ_bot).
  - apply ideal_capability_principal_l. intros; apply subtyp_refl.
Qed.

Local Lemma nocap_mutable_cases_in_ideals :
    mode_has_top_nm_subtype typing_mode ->
    iTop ⪯ ideal_join iNoCap (principal (typ_mut_marker typ_bot)).
Proof.
  intros Hmode A HA. exists typ_nocap, (typ_mut_marker typ_bot).
  split; [apply subtyp_refl |]. split; [apply subtyp_refl |].
  eapply subtyp_trans; [exact HA |].
  destruct typing_mode; simpl in *; try discriminate;
    first [apply subtyp_nocap_mut_top_boundless; reflexivity
          | apply subtyp_nocap_mut_top_complement; reflexivity].
Qed.

Local Lemma evaluate_exact_subtype S T U :
    inert G -> heap_correspond G p S ->
    exact_subtype G p T U ->
    evaluate recursive_selection_valuation T ⪯ evaluate recursive_selection_valuation U.
Proof.
  intros Hinert Hheap Hsub. induction Hsub.
  - apply ideal_top_greatest.
  - apply ideal_bot_least.
  - intros A HA. exact HA.
  - eapply ideal_below_trans; eassumption.
  - intros A [HA _]. exact HA.
  - intros A [_ HA]. exact HA.
  - intros A HA. split; auto.
  - apply ideal_join_left.
  - apply ideal_join_right.
  - now apply ideal_join_lub.
  - apply ideal_top_greatest.
  - destruct a; [apply ideal_top_greatest |].
    eapply ideal_below_trans; [apply (proj1 (evaluate_member_capability _ _ _ _)) |].
    eapply ideal_below_trans; [| apply (proj2 (evaluate_member_capability _ _ _ _))].
    apply ideal_capability_mono. auto.
  - apply (proj1 (@evaluate_selection_bound S x a y L U Hinert Hheap H)).
  - destruct a as [a | []].
    + rewrite (exact_normal_type_declaration_has_equal_bounds Hinert Hheap H).
      apply (proj2 (@evaluate_selection_bound S x (typ_label_normal a) y L U Hinert Hheap H)).
    + inversion H; subst. apply ideal_bot_least.
  - apply ideal_top_greatest.
  - apply (proj1 (evaluate_equivalence _ Hheap H)).
  - destruct a; [apply ideal_top_greatest |].
    change (ideal_meet (evaluate recursive_selection_valuation (typ_rcd (dec_typ
        (typ_label_refcap t) L U)))
      (evaluate recursive_selection_valuation (typ_rcd (dec_typ
        (typ_label_refcap t) L' U'))) ⪯
      evaluate recursive_selection_valuation (typ_rcd (dec_typ
        (typ_label_refcap t) (typ_or L L') (typ_and U U')))).
    eapply ideal_below_trans.
    { apply ideal_meet_mono; apply (proj1 (evaluate_member_capability _ _ _ _)). }
    eapply ideal_below_trans; [apply ideal_capability_meet |].
    exact (proj2 (@evaluate_member_capability recursive_selection_valuation t
      (typ_or L L') (typ_and U U'))).
  - apply ideal_distributes.
  - apply ideal_top_greatest.
  - apply ideal_top_greatest.
  - apply ideal_top_greatest.
  - apply ideal_top_greatest.
  - eapply ideal_below_trans.
    { apply nocap_mutable_cases_in_ideals.
      destruct typing_mode; simpl in *; discriminate || reflexivity. }
    change (ideal_join iNoCap (principal (typ_mut_marker typ_bot)) ⪯
      ideal_join iNoCap
      (evaluate recursive_selection_valuation (typ_rcd (dec_typ typ_label_mutability T U)))).
    apply ideal_join_mono; [intros A HA; exact HA |].
    eapply ideal_below_trans; [| apply (proj2 (evaluate_member_capability _ _ _ _))].
    apply ideal_capability_principal_l. intros; apply ideal_has_bot.
  - eapply ideal_below_trans.
    { apply nocap_mutable_cases_in_ideals.
      destruct typing_mode; simpl in *; discriminate || reflexivity. }
    change (ideal_join iNoCap (principal (typ_mut_marker typ_bot)) ⪯
      ideal_join iNoCap (evaluate recursive_selection_valuation (typ_mut_marker typ_bot))).
    apply ideal_join_mono; [intros A HA; exact HA |].
    apply (proj2 (evaluate_mutable_literal _)).
  - intros A [Hnocap Hmut].
    eapply subtyp_trans; [| apply subtyp_nocap_mut_bot; assumption].
    apply subtyp_and2; [exact Hnocap |].
    apply (proj1 (evaluate_mutable_literal recursive_selection_valuation)). exact Hmut.
  - eapply ideal_below_trans; [apply ideal_principal_below; now apply subtyp_mut_top |].
    apply ideal_capability_principal_l. intros; apply subtyp_refl.
Qed.

Local Definition old_selection_seed : selection_valuation :=
  fun x a z =>
    If (x \notin avoid /\ z \notin avoid)
      then principal (typ_sel (avar_f x) a (avar_f z)) else iBot.

Local Definition preserves_old_canonical_locations :=
  forall x, x \notin avoid ->
    canonical_location p x = canonical_location e x /\ canonical_location p x \notin avoid.

Local Definition preserves_old_selection_bounds :=
  forall x a L U, x \notin avoid -> exact_type_declaration G p x a L U ->
    exact_type_declaration F e x a L U /\ names_outside avoid (fv U).

Local Lemma seed_covers_old_type :
    preserves_old_canonical_locations ->
    forall T, names_outside avoid (fv T) ->
    principal T ⪯ evaluate old_selection_seed T.
Proof.
  intros Hcanon.
  assert (H : forall n T, type_size T < n -> names_outside avoid (fv T) ->
      principal T ⪯ evaluate old_selection_seed T).
  { induction n as [|n IH]; intros T Hsize Hnames; [lia |].
    destruct T as [| | D | A B | A B | a l b | A | A B |].
    - apply ideal_top_greatest.
    - apply ideal_bot_least.
    - destruct D as [l L U | | ]; try apply ideal_top_greatest.
      destruct l as [l | c]; [apply ideal_top_greatest |].
      destruct c.
      eapply ideal_below_trans with (J := principal (typ_mut_marker U)).
      { apply ideal_principal_below. apply subtyp_typ; intros;
          [apply subtyp_bot | apply subtyp_refl]. }
      eapply ideal_below_trans; [| apply (proj2 (evaluate_member_capability _ _ _ _))].
      apply ideal_capability_principal_l. intros z Hz.
      apply (IH (open z U)).
      + rewrite (proj1 opened_type_size_mutual). simpl in Hsize. lia.
      + eapply (proj1 (names_outside_open_mutual avoid)); [exact Hz |].
        change (names_outside avoid (fv L \u fv U)) in Hnames.
        now apply names_outside_union in Hnames as [_ Hnames].
      + apply subtyp_refl.
    - change (names_outside avoid (fv A \u fv B)) in Hnames.
      apply names_outside_union in Hnames as [HA HB].
      intros X HX. split.
      + apply (IH A); [simpl in Hsize; lia | exact HA |].
        eapply subtyp_trans; [exact HX | apply subtyp_and11].
      + apply (IH B); [simpl in Hsize; lia | exact HB |].
        eapply subtyp_trans; [exact HX | apply subtyp_and12].
    - change (names_outside avoid (fv A \u fv B)) in Hnames.
      apply names_outside_union in Hnames as [HA HB].
      apply ideal_principal_intro. apply ideal_closed_join.
      + apply ideal_join_left, (IH A); [simpl in Hsize; lia | exact HA | apply subtyp_refl].
      + apply ideal_join_right, (IH B); [simpl in Hsize; lia | exact HB | apply subtyp_refl].
    - destruct a as [|x], b as [|z]; try apply ideal_top_greatest.
      change (names_outside avoid (\{x} \u \{z})) in Hnames.
      apply names_outside_union in Hnames as [Hx Hz].
      specialize (Hx x ltac:(now rewrite in_singleton)).
      specialize (Hz z ltac:(now rewrite in_singleton)).
      destruct l as [l | c].
      + change (principal (typ_sel (avar_f x) (typ_label_normal l) (avar_f z)) ⪯
          old_selection_seed (canonical_location p x) (typ_label_normal l) z).
        unfold old_selection_seed. destruct (Hcanon x Hx) as [Heq Hnew].
        rewrite If_l by auto. rewrite Heq.
        apply ideal_principal_below, subtyp_tyq, tyq_typ_sel_normal.
        apply variable_equiv_to_location.
      + change (principal (typ_sel (avar_f x) (typ_label_refcap c) (avar_f z)) ⪯
          old_selection_seed x (typ_label_refcap c) z).
        unfold old_selection_seed. rewrite If_l by auto. intros X HX. exact HX.
    - apply ideal_top_greatest.
    - apply ideal_top_greatest.
    - intros X HX. exact HX. }
  intros T HT. apply (H (S (type_size T)) T); auto.
Qed.

Local Lemma recursive_evaluation_covers_old_type S :
    inert F -> heap_correspond F e S ->
    preserves_old_canonical_locations -> preserves_old_selection_bounds ->
    forall T, names_outside avoid (fv T) ->
    principal T ⪯ evaluate recursive_selection_valuation T.
Proof.
  intros Hinert Hheap Hcanon Hbounds T HT.
  eapply ideal_below_trans; [exact (@seed_covers_old_type Hcanon T HT) |].
  apply (proj1 evaluate_monotone_mutual), recursive_selection_dominates.
  intros x a z. unfold old_selection_seed.
  destruct (classic (x \notin avoid /\ z \notin avoid)) as [[Hx Hz] | Hfresh].
  - rewrite If_l by auto. intros A HA L U Hdecl.
    destruct (Hbounds x a L U Hx Hdecl) as [Hold Hscope].
    apply (@seed_covers_old_type Hcanon (open z U)).
    + eapply (proj1 (names_outside_open_mutual avoid)); eassumption.
    + eapply subtyp_trans; [exact HA |].
      apply subtyp_sel1 with (S := L).
      eapply exact_type_declaration_gives_typing; eassumption.
  - rewrite If_r by exact Hfresh. apply ideal_bot_least.
Qed.

Local Lemma bottom_subtype_reflect_across_extension S S' T :
    inert F -> heap_correspond F e S ->
    inert G -> heap_correspond G p S' ->
    preserves_old_canonical_locations -> preserves_old_selection_bounds ->
    names_outside avoid (fv T) ->
    exact_subtype G p T typ_bot ->
    F ⁏ e ⊢ T <: typ_bot.
Proof.
  intros HF HS HG HS' Hcanon Hbounds HT Hsub.
  apply ideal_principal_elim.
  eapply ideal_below_trans.
  - eapply recursive_evaluation_covers_old_type; eassumption.
  - exact (evaluate_exact_subtype HG HS' Hsub).
Qed.

Local Lemma mutable_subtype_reflect_across_extension S S' T :
    inert F -> heap_correspond F e S ->
    inert G -> heap_correspond G p S' ->
    preserves_old_canonical_locations -> preserves_old_selection_bounds ->
    names_outside avoid (fv T) ->
    exact_subtype G p T (typ_mut_marker typ_bot) ->
    F ⁏ e ⊢ T <: typ_mut_marker typ_bot.
Proof.
  intros HF HS HG HS' Hcanon Hbounds HT Hsub.
  apply ideal_principal_elim.
  eapply ideal_below_trans.
  - eapply recursive_evaluation_covers_old_type; eassumption.
  - eapply ideal_below_trans; [exact (evaluate_exact_subtype HG HS' Hsub) |].
    apply (proj1 (evaluate_mutable_literal _)).
Qed.

End WithSelectionEvaluation.

Local Lemma record_member_names_outside T D L :
    record_has T D -> names_outside L (fv T) -> names_outside L (fv D).
Proof.
  intros H. induction H; intros HF.
  - exact HF.
  - apply IHrecord_has. now apply names_outside_union in HF as [HF _].
  - apply IHrecord_has. now apply names_outside_union in HF as [_ HF].
Qed.

Local Lemma canonical_location_names_outside e L :
    names_outside L (fv_renv e) ->
    forall x, x \notin L -> canonical_location e x \notin L.
Proof.
  intros He x Hx. unfold canonical_location.
  destruct (get x e) as [y |] eqn:Hb; [| exact Hx].
  apply He. rewrite in_union. right.
  destruct (classic (y \in fv_env e)); [assumption |].
  exfalso. pose proof (@fv_in_values_binds var y (@fv var _) x y e Hb H) as Hbad.
  apply Hbad. change (y \in \{y}). now rewrite in_singleton.
Qed.

Local Lemma stable_selection_bounds_from_context F G e p L :
    (forall x T, x \notin L -> ctx_binds x T G -> ctx_binds x T F) ->
    names_outside L (ctx_fv F) ->
    preserves_old_canonical_locations e p L ->
    preserves_old_selection_bounds F G e p L.
Proof.
  intros Hb Hnames Hcanon x a B C Hx Hdecl.
  destruct Hdecl as [R M a B C Hbind Hrecord | R M Hbind].
  - pose proof (Hb _ _ Hx Hbind) as Hold.
    destruct (Hcanon x Hx) as [Hlocation Houtside].
    split.
    + eapply exact_normal_declaration; [exact Hold | now rewrite <- Hlocation].
    + assert (HR : names_outside L (fv R)).
      { intros z Hz. apply Hnames. eapply bound_type_free_in_context; [exact Hold |].
        cbn [fv TypFreeVar fv_typ fv_dec]. rewrite in_union. now left. }
      assert (Hrecord' : names_outside L
        (fv (dec_typ (typ_label_normal a) B C))).
      { eapply record_member_names_outside; [exact Hrecord |].
        eapply (proj1 (names_outside_open_mutual L)); eassumption. }
      now apply names_outside_union in Hrecord' as [_ Hscope].
  - pose proof (Hb _ _ Hx Hbind) as Hold.
    split; [eapply exact_capability_declaration; exact Hold |].
    intros z Hz. apply Hnames. eapply bound_type_free_in_context; [exact Hold |].
    cbn [fv TypFreeVar fv_typ fv_dec]. rewrite !in_union. tauto.
Qed.

Local Lemma push_same_existing_canonical_locations e w y L :
    w \in L ->
    names_outside L (fv_renv e) ->
    preserves_old_canonical_locations e (e & w ~ y) L.
Proof.
  intros Hw Hscope x Hx.
  assert (Hneq : x <> w) by (intros ->; contradiction).
  assert (Heq : canonical_location (e & w ~ y) x = canonical_location e x).
  { unfold canonical_location. rewrite get_push. now rewrite If_r by assumption. }
  split; [exact Heq |]. rewrite Heq.
  now apply canonical_location_names_outside.
Qed.

Local Lemma selection_capability_exposes_its_upper F e S w T B z :
    inert F -> heap_correspond F e S ->
    ctx_binds w (typ_objref T (typ_mut_marker B)) F ->
    F ⁏ e ⊢ typ_sel (avar_f w) typ_label_mutability (avar_f z) <: typ_bot ->
    F ⁏ e ⊢ open z B <: typ_bot.
Proof.
  intros HF HS Hw Hsub.
  assert (Hnothing : forall x : var, x \notin \{}) by (intros; apply notin_empty).
  assert (Hcanon : preserves_old_canonical_locations e e \{})
    by (intros x _; split; auto).
  assert (Hbounds : preserves_old_selection_bounds F F e e \{})
    by (intros x a A C _ Hdecl; split; auto; intros v _; apply Hnothing).
  pose proof (proj1 (proj2 variable_views_and_exact_subtypes)
    F objctx_empty e _ _ Hsub S HF HS) as Hnormalized.
  pose proof (@recursive_evaluation_covers_old_type F F e e \{} S HF HS Hcanon Hbounds
    (open z B) ltac:(intros v _; apply Hnothing)) as Hprincipal.
  pose proof (@evaluate_selection_bound F F e e \{} S w typ_label_mutability z typ_bot B
    HF HS (@exact_capability_declaration F e w T B Hw)) as [_ Hopt].
  apply ideal_principal_elim.
  eapply ideal_below_trans; [exact Hprincipal |].
  eapply ideal_below_trans; [exact Hopt |].
  exact (@evaluate_exact_subtype F F e e \{} S _ typ_bot HF HS Hnormalized).
Qed.

Local Lemma existing_reference_mutability_reflects F G e p S S' L w R B :
    inert F -> heap_correspond F e S ->
    inert G -> heap_correspond G p S' ->
    preserves_old_canonical_locations e p L ->
    preserves_old_selection_bounds F G e p L ->
    ctx_binds w (typ_objref R (typ_mut_marker B)) F ->
    ctx_binds w (typ_objref R (typ_mut_marker B)) G ->
    names_outside L (fv B) ->
    G ⁏ p ⊢ w ∶ typ_mut_marker typ_bot ->
    F ⁏ e ⊢ w ∶ typ_mut_marker typ_bot.
Proof.
  intros HF HS HG HS' Hcanon Hbounds Hw Hw' HB Hpost.
  destruct (precise_config_annotation HG HS' Hw') as (R' & B' & ds & Heq & Hrecord & _).
  inversion Heq; subst R' B'.
  destruct (proj1 variable_views_and_exact_subtypes G objctx_empty p w _ Hpost S' R B
    HG HS' Hw' Hrecord) as [_ Hview].
  destruct (view_of_capability Hview) as [_ Hbot].
  eapply ty_var_sub with (T := typ_mut_marker B).
  - eapply ty_var_sub; [exact (ty_var_var typing_mode e Hw) | apply subtyp_and12].
  - apply capability_widen.
    apply (@cofinite_opened_subtyping F e L B typ_bot).
    intros z Hz.
    eapply bottom_subtype_reflect_across_extension;
      [exact HF | exact HS | exact HG | exact HS' | exact Hcanon | exact Hbounds | | apply Hbot].
    eapply (proj1 (names_outside_open_mutual L)); eassumption.
Qed.

Local Lemma heap_location_info F e S y d :
    heap_correspond F e S -> binds y d S ->
    canonical_location e y = y /\ ctx_vis F y.
Proof.
  intros Hheap Hbind.
  pose proof Hheap as (Hok & Hwk & _ & _ & Hd & _).
  pose proof (binding_in_domain Hbind) as Hin.
  rewrite <- Hd in Hin.
  destruct (@kind_domain_has_binding F v_loc y Hwk Hok Hin) as (T & Q & Hk).
  split.
  - unfold canonical_location.
    now rewrite (get_none (location_not_environment_key Hheap Hk)).
  - apply kind_bound_visible with (k := v_loc). now exists T, Q.
Qed.

Local Lemma existing_field_mutability_reflects F G e p S S' L y R M A l :
    inert F -> heap_correspond F e S ->
    inert G -> heap_correspond G p S' ->
    preserves_old_canonical_locations e p L ->
    preserves_old_selection_bounds F G e p L ->
    names_outside L (ctx_fv F) ->
    y \notin L -> canonical_location e y = y ->
    ctx_binds y (typ_objref R M) F ->
    ctx_binds y (typ_objref R M) G ->
    record_has (open y R) (dec_fld l A A) ->
    G ⁏ p ⊢ y ∶ typ_rcd (dec_fld l typ_bot (typ_mut_marker typ_bot)) ->
    F ⁏ e ⊢ y ∶ typ_rcd (dec_fld l typ_bot (typ_mut_marker typ_bot)).
Proof.
  intros HF HS HG HS' Hcanon Hbounds Hscope Hy Hloc Hb Hb' Hmem Hpost.
  assert (Hcanon' : canonical_location p y = y).
  { rewrite (proj1 (Hcanon y Hy)). exact Hloc. }
  destruct (field_declaration_gives_bounds HG HS' Hcanon' Hb' Hmem Hpost) as [_ Hsub].
  assert (HA : names_outside L (fv A)).
  { assert (HR : names_outside L (fv R)).
    { intros z Hz. apply Hscope. eapply bound_type_free_in_context; [exact Hb |].
      cbn [fv TypFreeVar fv_typ]. rewrite in_union. now left. }
    pose proof (@record_member_names_outside _ _ L Hmem
      (proj1 (names_outside_open_mutual L) R 0 y Hy HR)) as Hoccurs.
    now apply names_outside_union in Hoccurs as [Hoccurs _]. }
  assert (Hsub' : F ⁏ e ⊢ A <: typ_mut_marker typ_bot).
  { eapply mutable_subtype_reflect_across_extension;
      [exact HF | exact HS | exact HG | exact HS' | exact Hcanon | exact Hbounds | exact HA |].
    exact (proj1 (proj2 variable_views_and_exact_subtypes)
      G objctx_empty p _ _ Hsub S' HG HS'). }
  destruct (precise_config_annotation HF HS Hb) as (R' & M' & ds & Heq & _ & Hind & _).
  inversion Heq; subst R'.
  eapply ty_var_sub with (T := typ_rcd (dec_fld l A A)).
  - eapply precise_declaration_is_accessible; [exact Hb | exact Hind |].
    now rewrite Hloc.
  - apply subtyp_fld; [apply subtyp_bot | exact Hsub'].
Qed.

Local Lemma structural_interface_subtype F e S D D' :
    inert F -> heap_correspond F e S ->
    mode_incap' typing_mode = mode_incap_structural ->
    interface_bounds F e D D' ->
    F ⁏ e ⊢ typ_rcd D <: typ_rcd D'.
Proof.
  intros HF HS Hmode.
  destruct D as [a L U | a L U | m C Z T],
    D' as [a' L' U' | a' L' U' | m' C' Z' T']; simpl; try contradiction;
    try (destruct a; contradiction);
    try (destruct a'; contradiction).
  - destruct a, a'; simpl; try contradiction.
    intros (-> & HL & HU). apply subtyp_typ; intros;
      eapply exact_subtype_general; eauto.
  - intros (-> & HL & HU). apply subtyp_fld;
      eapply exact_subtype_general; eauto.
  - intros (-> & Hpar & K & Hrecv & Hres).
    eapply subtyp_met with (L := K); try eassumption.
    intros Hsef _. destruct typing_mode; simpl in *; discriminate.
Qed.

Local Lemma reconstruct_neutral_declaration_view F e S (x w : var) R B v T :
    inert F -> heap_correspond F e S ->
    mode_incap' typing_mode = mode_incap_structural ->
    F ⁏ e ⊢ w ∶ open (canonical_location e x) R ->
    canonical_location e w = canonical_location e x ->
    object_has_view F e x R B v T ->
    v = declaration_view -> neutral_outer_shape True T ->
    F ⁏ e ⊢ w ∶ T.
Proof.
  intros HF HS Hmode Hw Hsame Hview.
  induction Hview; simpl; intros Hkind Hneutral; try discriminate; try contradiction.
  - eapply ty_var_sub; [exact Hw | apply subtyp_top].
  - destruct Hneutral. apply ty_var_and; auto.
  - destruct Hneutral. eapply ty_var_sub with (T := A); [eauto | apply subtyp_or11].
  - destruct Hneutral. eapply ty_var_sub with (T := C); [eauto | apply subtyp_or12].
  - eapply ty_var_sub.
    + eapply ty_var_sub; [exact Hw | apply record_projects_declaration; eassumption].
    + eapply structural_interface_subtype; eassumption.
  - assert (Hopen : e ⊢ open (canonical_location e x) Witness ≈ open w Witness).
    { eapply independent_type_open_alias; [| eassumption | reflexivity].
      rewrite <- Hsame. apply tyq_var_sym, variable_equiv_to_location. }
    eapply ty_var_sub with (T := typ_bnd Witness); [| now apply subtyp_tyq].
    apply ty_rec_intro; try eassumption.
    + eapply ty_var_sub with (T := open (canonical_location e x) Witness).
      2: exact (subtyp_tyq _ _ Hopen).
      apply IHHview1; [reflexivity |].
      eapply structural_incap_result; eassumption.
    + intros. eapply incap_identity_respects_equiv; eassumption.
Qed.

Local Lemma aliases_inherit_incap_result F e S y w R B T Tstrip :
    inert F -> heap_correspond F e S ->
    binds w y e ->
    ctx_binds y (typ_objref R (typ_mut_marker typ_bot)) F ->
    ctx_binds w (typ_objref R (typ_mut_marker B)) F ->
    F ⁏ e ⊢ y ∶ Tstrip ->
    F ⁏ e ⊢ T ∶icp Tstrip ->
    F ⁏ e ⊢ w ∶ Tstrip.
Proof.
  intros HF HS Hbind Hy Hw Hty Hstrip.
  assert (Hmode : mode_has_top_nm_subtype typing_mode \/
      mode_incap' typing_mode = mode_incap_structural).
  { destruct typing_mode; simpl in *; try discriminate; auto. }
  destruct Hmode as [Hmode | Hmode].
  - eapply alias_inherits_type_admitting_nocap; try eassumption.
    eapply incap_result_accepts_nocap; eassumption.
  - destruct (precise_config_annotation HF HS Hy)
      as (R' & B' & ds & Heq & Hrec & Hind & _).
    inversion Heq; subst R' B'.
    destruct (proj1 variable_views_and_exact_subtypes F objctx_empty e y _ Hty
      S R typ_bot HF HS Hy Hrec) as [Hdecl _].
    destruct (object_reference_record_views Hbind Hw Hind) as [Hloc _].
    destruct (environment_binding_canonical_locations HS Hbind) as [Hx HyCanon].
    eapply reconstruct_neutral_declaration_view; try eassumption.
    + now rewrite HyCanon.
    + now rewrite Hx, HyCanon.
    + reflexivity.
    + eapply structural_incap_result; eassumption.
Qed.

Local Lemma rename_stack_while_fixing_terms F e f K s T U :
    ty_stack F e T s U ->
    renaming_fixes_outside K f ->
    renaming_respects_aliases f e e ->
    renamed_context f F F e ->
    names_agree_on (fv s) f (fun x => x) ->
    ty_stack F e (rename_typ f T) s (rename_typ f U).
Proof.
  intros Hty. induction Hty; intros Hfix Henv Hsc Hnames.
  - apply ty_stack_nil.
    eapply renamed_subtyping; try eassumption. exact (proj1 Hsc).
  - change (names_agree_on (fv t \u fv s) f (fun x => x)) in Hnames.
    eapply ty_stack_let with (L := L \u (K \u ctx_dom G)).
    + apply IHHty; eauto using names_agree_right.
    + intros x Hx.
      destruct (@renaming_fresh_binder f L K G x Hfix Hx) as [HxL [Hmap HxG]].
      pose proof (@renamed_context_push_fixed f G G e x v_let S Hmap HxG Hsc) as Hpush.
      pose proof (proj1 term_typing_renaming _ _ _ _ _ (H x HxL)
        f K _ e Hfix Henv Hpush Hpush) as Hbody.
      cbn [rename_objctx] in Hbody.
      now rewrite rename_trm_opens, Hmap,
        (@rename_trm_inactive f t (names_agree_left Hnames)) in Hbody.
Qed.

Local Lemma renaming_preserves_scope_avar (f : var -> var) (a : avar) K :
    (forall x, x \in fv a -> f x \in K) -> fv (rename_avar f a) \c K.
Proof.
  destruct a as [n | x]; intros H v Hv.
  - change (v \in (\{} : vars)) in Hv. now rewrite in_empty in Hv.
  - change (v \in \{f x}) in Hv. rewrite in_singleton in Hv. subst v.
    apply H. change (x \in \{x}). now rewrite in_singleton.
Qed.

Local Lemma renaming_preserves_scope_types :
    (forall T f n K, (forall x, x \in fv T -> f x \in K) ->
      fv (transform_typ (renaming f) T n) \c K) /\
    (forall D f n K, (forall x, x \in fv D -> f x \in K) ->
      fv (transform_dec (renaming f) D n) \c K).
Proof.
  apply typ_mutind; intros;
    cbn [transform_typ transform_dec fv TypFreeVar DecFreeVar fv_typ fv_dec] in *;
    intros x Hx;
    try solve [rewrite in_empty in Hx; contradiction | eauto].
  all: repeat rewrite in_union in Hx;
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
    first [eapply renaming_preserves_scope_avar; [| eassumption] | eapply H; [|eassumption] |
      eapply H0; [|eassumption] | eapply H1; [|eassumption]];
    intros z Hz;
    match goal with Hs : forall v, v \in _ -> ?f v \in ?K |- _ => apply Hs end;
    repeat rewrite in_union; tauto.
Qed.

Local Definition place_cap_names_in_history (C : config) (B : typ) null x :=
  If (x \in fv B /\ x \notin fv_config C) then null else x.

Local Lemma cap_history_map_stays_in_domain C B null :
    null \in fv_config C ->
    fv (rename_typ (place_cap_names_in_history C B null) B) \c fv_config C.
Proof.
  intros Hnull. apply (proj1 renaming_preserves_scope_types).
  intros z Hz. unfold place_cap_names_in_history.
  destruct (classic (z \in fv_config C)) as [Hin | Hout].
  - rewrite If_r by (intros [_ Hbad]; exact (Hbad Hin)). exact Hin.
  - rewrite If_l by (split; assumption). exact Hnull.
Qed.

Local Lemma cap_history_map_fixes_configuration C B null :
    names_agree_on (fv_config C) (place_cap_names_in_history C B null) (fun x => x).
Proof.
  intros x H. unfold place_cap_names_in_history.
  rewrite If_r by (intros [_ Hbad]; exact (Hbad H)). reflexivity.
Qed.

Local Lemma read_configuration_with_cap F s S e Lv w w' y a R B U T G0 :
    let C := (trm_read (avar_f w) a ; s ; S ; e ; Lv) in
    let G := F § w' / v_ref ~ typ_objref R (typ_mut_marker B) in
    let p := e & w' ~ y in
    execution_config F C U ->
    fresh_in_config (w' :: nil) C ->
    ctx_binds_k_after y v_loc (typ_objref R (typ_mut_marker typ_bot)) F G0 ->
    record_type R -> typ_indep_b 0 R ->
    fv B \c fv_config C ->
    ty_stack F e T s U ->
    G ⁏ p ⊢ trm_var (avar_f w') ∶ T ->
    execution_config G (trm_var (avar_f w') ; s ; S ; p ; fv_config C) U.
Proof.
  intros C G p Hcfg Hfresh Hloc Hrecord Hind HB Hstack Hty.
  assert (Hw : w' \notin fv_config C) by (inversion Hfresh; assumption).
  destruct (fresh_config_keys Hfresh) as [_ HwEnv].
  pose proof (kind_binding_gives_binding Hloc) as Hbind.
  assert (Hnames : ty_nothing_fresh_in_config F U C) by (inversion Hcfg; assumption).
  destruct Hnames as ((Hdom & Hfv) & Hu).
  assert (HwDom : w' §# F) by (intro Hbad; apply Hw, Hdom; exact Hbad).
  assert (HwFv : w' \notin ctx_fv F) by (intro Hbad; apply Hw, Hfv; exact Hbad).
  set (A := typ_objref R (typ_mut_marker B)).
  assert (HA : fv A \c fv_config C).
  { intros v Hv. change (v \in fv R \u (\{} \u fv B)) in Hv.
    rewrite !in_union, in_empty in Hv.
    destruct Hv as [Hv | [Hfalse | Hv]]; try contradiction; [| now apply HB].
    apply Hfv. eapply bound_type_free_in_context; [exact Hbind |].
    cbn [fv TypFreeVar fv_typ]. rewrite in_union. now left. }
  assert (HwA : w' \notin fv A) by (intro Hbad; apply Hw, HA; exact Hbad).
  assert (Hext : typing_context_extends F G p) by (unfold G; now apply extend_context_typing).
  assert (He : env_binds_more e p).
  { intros b x Hb. unfold p. apply binds_push_neq; [exact Hb |].
    intros ->. exact (binds_fresh_inv Hb HwEnv). }
  pose proof (history_in_config (trm_var (avar_f w') ; s ; S ; p ; fv_config C)) as Hcarry.
  inversion Hcfg; subst. eapply execution_config_intro with (T := T); try eassumption.
  - unfold G. apply inert_push; try assumption; [constructor |].
    apply inert_typ_obj; try assumption.
    unfold refcap_inert_type.
    destruct typing_mode; simpl in *; try discriminate; constructor.
  - unfold G, p. eapply heap_reference_extension; eassumption.
  - eapply weaken_stack_env; eassumption.
  - intros x Hx. unfold G. apply kind_keep_under_binding; auto.
  - intros x Hx. inversion Hx; subst. unfold G. eexists; eexists; apply ctx_binds_k_e.
  - split; [split |]; intros x Hx.
    + unfold G in Hx. simpl ctx_dom in Hx. rewrite in_union, in_singleton in Hx.
      destruct Hx as [-> | Hx].
      * change (w' \in (fv (trm_var (avar_f w')) \u fv s \u fv_heap S \u
          fv_renv p \u fv_config C)).
        rewrite in_union. left. change (w' \in \{w'}). now rewrite in_singleton.
      * apply Hcarry. now apply Hdom.
    + change (x \in (fv A \u ctx_fv F)) in Hx. rewrite in_union in Hx.
      apply Hcarry. destruct Hx as [Hx | Hx]; [now apply HA | now apply Hfv].
    + apply Hcarry. now apply Hu.
  - match goal with Hnull : has_null Lv |- _ =>
      destruct Hnull as [z Hz]; exists z; exact (@history_in_config C z Hz)
    end.
  - match goal with Hclosed : config_closed _ |- _ => inversion Hclosed; subst end.
    constructor; try assumption. intros n x; reflexivity.
Qed.

Local Lemma location_binding_has_mutable_record F y :
    inert F -> ctx_k F y v_loc ->
    exists R G, ctx_binds_k_after y v_loc (typ_objref R (typ_mut_marker typ_bot)) F G /\
                record_type R /\ typ_indep_b 0 R.
Proof.
  intros Hinert (A & G & Hloc).
  destruct (inert_binding_class Hinert (kind_binding_gives_binding Hloc))
    as (k & G0 & _ & Hty & Hkind).
  pose proof (kind_binding_unique Hkind Hloc) as ->.
  inversion Hty; subst.
  - pose proof mode_disallows_functions. congruence.
  - match goal with HC : refcap_inert_type ?M v_loc |- _ =>
      assert (Hmode : mode_refcaps' typing_mode = mode_refcaps_mutability)
        by (destruct typing_mode; simpl in *; try discriminate; reflexivity);
      unfold refcap_inert_type in HC; rewrite Hmode in HC; inversion HC; subst M
    end.
    eauto.
Qed.

Local Lemma environment_entry_names e x y :
    binds x y e -> x \in fv_renv e /\ y \in fv_renv e.
Proof.
  intros H. rewrite !in_union. split.
  - left. now apply (binding_in_domain H).
  - right. destruct (classic (y \in fv_env e)); [assumption |].
    exfalso. pose proof (@fv_in_values_binds var y (@fv var _) x y e H H0) as Hbad.
    apply Hbad. change (y \in \{y}). now rewrite in_singleton.
Qed.

Local Lemma alias_added_capability_requirement F e S w y R B :
    w \notin ctx_dom F -> w \notin ctx_fv F -> w \notin fv_renv e ->
    w \notin fv B -> w <> y -> ctx_vis F y ->
    ctx_binds y (typ_objref R (typ_mut_marker typ_bot)) F ->
    let G := F § w / v_ref ~ typ_objref R (typ_mut_marker B) in
    let p := e & w ~ y in
    inert G -> heap_correspond G p S ->
    G ⁏ p ⊢ w ∶ typ_mut_marker typ_bot ->
    forall z, F ⁏ e ⊢ open z B <: typ_bot.
Proof.
  intros Hdom Hfv Henv HB Hneq HyVis Hy G p HG HS Hmutable.
  assert (Hw : ctx_binds w (typ_objref R (typ_mut_marker B)) G)
    by (unfold G; apply ctx_binds_e).
  destruct (precise_config_annotation HG HS Hw)
    as (R' & B' & ds & Heq & Hrec & _). inversion Heq; subst R' B'.
  destruct (proj1 variable_views_and_exact_subtypes G objctx_empty p w _ Hmutable
    S R B HG HS Hw Hrec) as [_ Hcap].
  destruct (view_of_capability Hcap) as [_ Hbot].
  destruct (@alias_extension_collapse F e w y R B Hdom Hfv Henv Hneq HyVis Hy)
    as [Hal Hscope].
  set (f := replace_name (fun v => v) w y) in *.
  assert (Hfix : renaming_fixes_outside \{w} f).
  { intros x Hx. rewrite notin_singleton in Hx. now apply replace_name_away. }
  apply (@cofinite_opened_subtyping F e \{w} B typ_bot).
  intros z Hz.
  pose proof (exact_subtype_general HG HS (Hbot z)) as Hsub.
  pose proof (@renamed_subtyping G F p e f _ _ _ Hfix Hal (proj1 Hscope) Hsub) as Hout.
  rewrite rename_typ_opens in Hout.
  assert (Hfz : f z = z) by (now apply Hfix).
  rewrite Hfz, (@rename_typ_inactive f B ltac:(now apply replace_name_fresh)) in Hout.
  exact Hout.
Qed.

Local Lemma read_step_preserves_execution F s S e Lv w w' y z a ds U :
    let C := (trm_read (avar_f w) a ; s ; S ; e ; Lv) in
    let D := (trm_var (avar_f w') ; s ; S ; e & w' ~ z ; fv_config C) in
    execution_config F C U ->
    fresh_in_config (w' :: nil) C ->
    binds w y e -> binds y (item_obj ds) S -> defs_has ds (def_fld a (avar_f z)) ->
    exists G, execution_config G D U /\ (forall target, G ⊢ D mreach target -> F ⊢ C mreach target).
Proof.
  intros C D Hcfg Hfresh Hobj Hbind Hmember.
  inversion Hcfg as [F0 e0 s0 S0 Lv0 t0 T U0 HF HS Hstack Hsk Hty Htk Hnames Hnull Hclosed HU]; subst.
  pose proof HS as (Hok & _ & _ & _ & _ & _ & Henv & _).
  destruct (heap_field_value_typing HS Hbind Hmember)
    as (RO & BO & A & Howner & Hfield & Hvalue & Hkind).
  destruct (location_binding_has_mutable_record HF Hkind)
    as (R & GF & Hloc & Hrec & Hind).
  pose proof (kind_binding_gives_binding Hloc) as HzBind.
  assert (HzVis : ctx_vis F z) by (now apply (kind_bound_visible Hkind)).
  destruct (read_typing_operands Hty eq_refl) as (L & V & Ret & Hread & Hadapt & Hsub).
  unfold viewpoint_adapt in Hadapt. rewrite viewpoint_for_mutability in Hadapt.
  inversion Hadapt; subst.
  destruct Hnull as [null Hnull].
  set (f := place_cap_names_in_history C Tcap null).
  assert (Hfix : renaming_fixes_outside (fv Tcap) f).
  { intros x Hx. unfold f, place_cap_names_in_history.
    rewrite If_r by (intros [Hbad _]; exact (Hx Hbad)). reflexivity. }
  assert (HnamesC : names_agree_on (fv_config C) f (fun x => x))
    by apply cap_history_map_fixes_configuration.
  pose proof Hnames as ((Hdom & Hfv) & Hres).
  assert (Hscope : renamed_context f F F e).
  { apply rename_context_identity_on_scope. intros x Hx. apply HnamesC.
    rewrite in_union in Hx. destruct Hx; [now apply Hdom | now apply Hfv]. }
  assert (Henvf : renaming_respects_aliases f e e).
  { intros v q Hb. destruct (environment_entry_names Hb) as [Hv Hq].
    assert (Hstay : forall x, x \in fv_renv e -> f x = x).
    { intros x Hx. apply HnamesC. unfold C; cbn. do 3 (rewrite in_union; right).
      rewrite in_union. now left. }
    rewrite !Hstay by assumption. now apply tyq_var_binds. }
  assert (Hfw : f w = w).
  { apply HnamesC. unfold C; cbn. rewrite in_union. left.
    change (w \in \{w}). now rewrite in_singleton. }
  pose proof (@renamed_variable_typing F F e e f _ _ _ Hfix Henvf (proj1 Hscope) Hread) as Hread'.
  normalize_renamed_in Hread'. rewrite Hfw in Hread'.
  pose proof (@renamed_capability_bound typ_refcap_mutability F F e e f _ _ _
    Hfix Henvf (proj1 Hscope) ltac:(eassumption)) as Hcap'.
  pose proof (@renamed_incap F F e e f _ _ _ Hfix Henvf (proj1 Hscope) ltac:(eassumption)) as Hstrip'.
  pose proof (@renamed_subtyping F F e e f _ _ _ Hfix Henvf (proj1 Hscope) Hsub) as Hout'.
  normalize_renamed_in Hout'. rewrite Hfw in Hout'.
  set (B := typ_or (rename_typ f Tcap)
    (typ_sel (avar_f w) typ_label_mutability (avar_b 0))) in *.
  assert (HB : fv B \c fv_config C).
  { intros v Hv. change (v \in (fv (rename_typ f Tcap) \u (\{w} \u \{}))) in Hv.
    rewrite !in_union, in_empty, in_singleton in Hv.
    destruct Hv as [Hv | [-> | Hbad]]; [| | contradiction].
    - eapply cap_history_map_stays_in_domain; [apply (@history_in_config C); exact Hnull | exact Hv].
    - unfold C; cbn. rewrite in_union. left. change (w \in \{w}). now rewrite in_singleton. }
  assert (Hw : w' \notin fv_config C) by (inversion Hfresh; assumption).
  destruct (fresh_config_keys Hfresh) as [_ HwEnv].
  assert (HwDom : w' §# F) by (intro Hbad; apply Hw, Hdom; exact Hbad).
  assert (HwFv : w' \notin ctx_fv F) by (intro Hbad; apply Hw, Hfv; exact Hbad).
  assert (HwEnvNames : w' \notin fv_renv e).
  { intros Hbad. apply Hw. unfold C; cbn. do 3 (rewrite in_union; right).
    rewrite in_union. now left. }
  assert (HwB : w' \notin fv B) by (intro Hbad; apply Hw, HB; exact Hbad).
  assert (Hneq : w' <> z).
  { intros ->. apply HwDom. eapply context_binding_in_domain; exact HzBind. }
  set (G := F § w' / v_ref ~ typ_objref R (typ_mut_marker B)).
  set (p := e & w' ~ z).
  assert (HG : inert G).
  { unfold G. apply inert_push; try assumption.
    - constructor.
    - apply inert_typ_obj; try assumption. unfold refcap_inert_type.
      destruct typing_mode; simpl in *; try discriminate; constructor.
    - intro Hbad. apply Hw. cbn [fv TypFreeVar fv_typ fv_dec] in Hbad.
      rewrite !in_union, in_empty in Hbad. destruct Hbad as [Hr | [Hfalse | Hb]].
      + apply Hfv. eapply bound_type_free_in_context; [exact HzBind |].
        cbn [fv TypFreeVar fv_typ fv_dec]. rewrite in_union. now left.
      + contradiction.
      + now apply HB. }
  assert (HS' : heap_correspond G p S) by
    (unfold G, p; eapply heap_reference_extension; eassumption).
  assert (Hp : env_binds_more e p).
  { intros q x Hb. unfold p. apply binds_push_neq; [exact Hb |].
    intros ->. exact (binds_fresh_inv Hb HwEnv). }
  assert (Hext : typing_context_extends F G p) by (unfold G; now apply extend_context_typing).
  pose proof (extends_reference_environment Hp) as HidEnv.
  pose proof (proj1 (identity_renaming_of_contexts Hext)) as HidCtx.
  assert (Hid : renaming_fixes_outside \{} (fun x => x)) by (intros x _; reflexivity).
  assert (HreadLoc : F ⁏ e ⊢ y ∶ typ_rcd (dec_fld a (rename_typ f L) (rename_typ f V)))
    by (eapply reference_typing_at_location; eassumption).
  pose proof (proj2 (environment_binding_canonical_locations HS Hobj)) as Hcanon.
  destruct (field_declaration_gives_bounds HF HS Hcanon Howner Hfield HreadLoc) as [_ HV].
  assert (HvalueStrip : F ⁏ e ⊢ z ∶ rename_typ f Tstrip).
  { eapply ty_var_sub; [exact Hvalue |].
    eapply subtyp_trans; [exact HV | eapply incap_type_weakens; eassumption]. }
  pose proof (@renamed_variable_typing F G e p (fun x => x) \{} _ _
    Hid HidEnv HidCtx HvalueStrip) as HvalueStrip'.
  rewrite (proj1 rename_types_identity) in HvalueStrip'.
  pose proof (@renamed_incap F G e p (fun x => x) \{} _ _
    Hid HidEnv HidCtx Hstrip') as HstripPost.
  rewrite !(proj1 rename_types_identity) in HstripPost.
  pose proof (@renamed_subtyping F G e p (fun x => x) \{} _ _
    Hid HidEnv HidCtx Hout') as Hout.
  rewrite !(proj1 rename_types_identity) in Hout.
  assert (HzG : ctx_binds z (typ_objref R (typ_mut_marker typ_bot)) G)
    by (unfold G; now apply fresh_context_extension).
  assert (HwG : ctx_binds w' (typ_objref R (typ_mut_marker B)) G)
    by (unfold G; apply ctx_binds_e).
  assert (HstripW : G ⁏ p ⊢ w' ∶ rename_typ f Tstrip).
  { eapply aliases_inherit_incap_result; try eassumption. unfold p. apply binds_push_eq. }
  assert (HcapW : G ⁏ p ⊢ w' ∶ typ_mut_marker B).
  { eapply ty_var_sub; [exact (ty_var_var typing_mode p HwG) | apply subtyp_and12]. }
  assert (HnewTerm : G ⁏ p ⊢ trm_var (avar_f w') ∶ rename_typ f T).
  { apply ty_trm_var; [intro; unfold G; apply ctx_vis_e |].
    eapply ty_var_sub; [| exact Hout].
    apply ty_var_and; [exact HstripW | exact HcapW]. }
  assert (Hstack' : ty_stack F e (rename_typ f T) s U).
  { pose proof (@rename_stack_while_fixing_terms F e f _ s T U Hstack
      Hfix Henvf Hscope) as Hsc.
    rewrite (@rename_typ_inactive f U ltac:(intros x Hx; apply HnamesC, Hres, Hx)) in Hsc.
    apply Hsc. intros x Hx. apply HnamesC. unfold C; cbn. rewrite in_union. right.
    rewrite in_union. now left. }
  exists G. split.
  { unfold D, G, p.
    eapply read_configuration_with_cap; eassumption. }
  intros target Hreach. unfold D, G, p in Hreach.
  eapply reachability_read; [exact HF | exact Hobj | exact Hbind | exact Hmember | | | | exact Hreach].
  - intros x Hx HtyX. eapply alias_extension_reflects_variable; try eassumption; try congruence.
    cbn [fv TypFreeVar fv_typ fv_dec]. rewrite !notin_union. repeat split; apply notin_empty.
  - intros x l items Hb HtyX. eapply alias_extension_reflects_variable; try eassumption.
    + pose proof (fresh_heap_binding Hfresh Hb). congruence.
    + cbn [fv TypFreeVar fv_typ fv_dec]. rewrite !notin_union. repeat split; apply notin_empty.
  - intros Hr. pose proof (variable_term_typing Hr eq_refl) as Hvar.
    pose proof (@alias_added_capability_requirement F e S w' z R B
      HwDom HwFv HwEnvNames HwB Hneq HzVis HzBind HG HS' Hvar) as Hbounded.
    destruct (reference_location_annotations Hok Henv Hobj)
      as (RObj & MObj & GW & GY & HwK & HyK).
    pose proof (kind_binding_gives_binding HwK) as HwBind.
    split.
    + apply ty_trm_var.
      { intro. apply kind_bound_visible with (k := v_ref).
        exists (typ_objref RObj (typ_mut_marker MObj)), GW. exact HwK. }
      eapply ty_var_sub with (T := typ_mut_marker MObj).
      * eapply ty_var_sub; [exact (ty_var_var typing_mode e HwBind) | apply subtyp_and12].
      * apply capability_widen. intro v.
        apply (@selection_capability_exposes_its_upper F e S w RObj MObj v HF HS HwBind).
        eapply subtyp_trans; [| exact (Hbounded v)].
        change (F ⁏ e ⊢ typ_sel (avar_f w) typ_label_mutability (avar_f v) <:
          typ_or (open v (rename_typ f Tcap))
            (typ_sel (avar_f w) typ_label_mutability (open v (avar_b 0)))).
        rewrite avar_open_here. apply subtyp_or12.
    + apply ty_trm_var.
      { intro. apply kind_bound_visible with (k := v_loc).
        exists (typ_objref RObj (typ_mut_marker typ_bot)), GY. exact HyK. }
      eapply ty_var_sub; [exact HreadLoc | apply subtyp_fld; [apply subtyp_bot |]].
      eapply mutable_adapted_field_bound; eassumption.
Qed.

Local Lemma rename_defs_inactive f ds :
    names_agree_on (fv ds) f (fun x => x) ->
    rename_defs f ds = ds.
Proof.
  intros H.
  exact (@Logic.eq_trans _ _ _ _
    (proj2 (proj2 (proj2 rename_terms_congruent)) ds f (fun x => x) 0 H)
    (proj2 (proj2 (proj2 rename_terms_identity)) ds 0)).
Qed.

Local Lemma renamed_context_binding_embedding f F G e :
    names_agree_on (ctx_dom F \u ctx_fv F) f (fun x => x) ->
    includes_bindings F G ->
    (forall x, ctx_vis F x -> ctx_vis G x) ->
    renamed_context f F G e.
Proof.
  intros Hnames Hb Hva. split.
  - intros x T HT. assert (Hx : f x = x).
    { apply (names_agree_left Hnames). eapply context_binding_in_domain; eassumption. }
    rewrite Hx, rename_typ_inactive.
    + apply ty_var_var. now apply Hb.
    + intros a Ha. apply (names_agree_right Hnames).
      eapply bound_type_free_in_context; eassumption.
  - intros x Hx. assert (Heq : f x = x).
    { apply (names_agree_left Hnames), visibility_in_context_domain, Hx. }
    rewrite Heq. now apply Hva.
Qed.

Local Lemma open_literal_in_extended_context F G e p (R : typ) (ds : defs) L w :
    (forall z, z \notin L -> F §§ objctx_lit z R ⁏ e ⊢ open z ds ∶ open z R) ->
    env_binds_more e p ->
    includes_bindings F G ->
    (forall z, ctx_vis F z -> ctx_vis G z) ->
    w §# F ->
    G §§ objctx_lit w R ⁏ p ⊢ open w ds ∶ open w R.
Proof.
  intros Hbody Hp Hbind Hvis Hw.
  destruct (var_fresh (L \u ((ctx_dom F \u ctx_fv F) \u (fv_renv e \u fv R \u fv ds))))
    as [z Hz].
  rewrite !notin_union in Hz.
  destruct Hz as (HzL & [Hzdom Hzfv] & [Hzed Hzef] & HzR & HzDs).
  set (f := replace_name (fun v => v) z w).
  assert (Hmap : f z = w) by apply replace_name_at.
  assert (HR : rename_typ f R = R) by (apply rename_typ_inactive; now apply replace_name_fresh).
  assert (Hds : rename_defs f ds = ds) by (apply rename_defs_inactive; now apply replace_name_fresh).
  assert (Hfix : renaming_fixes_outside \{z} f).
  { intros x Hx. rewrite notin_singleton in Hx. now apply replace_name_away. }
  assert (Henv : renaming_respects_aliases f e p).
  { unfold f. apply replace_name_respects_aliases; [apply notin_union; auto |].
    now apply extends_reference_environment. }
  assert (Hnames : names_agree_on (ctx_dom F \u ctx_fv F) f (fun x => x)).
  { apply replace_name_fresh, notin_union. auto. }
  pose proof (@renamed_context_binding_embedding f F G p Hnames Hbind Hvis) as Hbase.
  assert (Hoverlay : renamed_context f (F §§& objctx_lit z R)
    (G §§& rename_objctx f (objctx_lit z R)) p).
  { cbn [ctx_obj rename_objctx]. rewrite Hmap, HR.
    apply renamed_context_discharge.
    - apply renamed_context_binding_embedding; [exact Hnames | |].
      + intros x T Hb. apply ctx_binds_n; [| now apply Hbind].
        intros ->. apply Hw. eapply context_binding_in_domain; exact Hb.
      + intros x Hx. apply ctx_vis_n; [| now apply Hvis].
        intros ->. apply Hw. now apply visibility_in_context_domain.
    - rewrite Hmap, rename_typ_opens, Hmap, HR.
      apply ty_var_var, ctx_binds_e.
    - rewrite Hmap. apply ctx_vis_e. }
  pose proof (proj2 (proj2 (proj2 term_typing_renaming))
    F (objctx_lit z R) e _ _ (Hbody z HzL) f _ G p Hfix Henv Hbase Hoverlay) as Hfresh.
  cbn [rename_objctx] in Hfresh.
  now rewrite rename_defs_open, rename_typ_opens, Hmap, HR, Hds in Hfresh.
Qed.

Local Lemma object_self_scope_discharge G e w R :
    G ⁏ e ⊢ w ∶ open w R ->
    ctx_vis G w ->
    typing_context_extends (G § w / v_self ~ open w R) G e.
Proof.
  intros Hw Hv. split.
  - intros x T Hx. inversion Hx; subst; [exact Hw | now apply ty_var_var].
  - intros x Hx. inversion Hx; subst; assumption.
Qed.

Local Lemma literal_definition_change_owner G e w y R d D :
    G §§ objctx_lit w R ⁏ e ⊢ d ∶d D ->
    G ⁏ e ⊢ w ∶ open w R ->
    ctx_vis G w ->
    e ⊢ open y R ≈ open w R ->
    G §§ objctx_heap y R ⁏ e ⊢ d ∶d D.
Proof.
  intros Hd Hw Hvis Hself.
  pose proof (@object_self_scope_discharge G e w R Hw Hvis) as Hscope.
  clear Hw Hvis.
  inversion Hd; subst.
  - eapply ty_def_typ; eassumption.
  - apply ty_def_fld.
    + intros Hv. eapply transport_vis; eauto.
    + eapply replace_var_typing; [exact (proj1 Hscope) | eassumption].
  - eapply ty_def_met with (L := L \u ctx_dom G).
    intros z Hz c Hneq Hc. rewrite !notin_union in Hz, Hc.
    destruct Hz as [HzL HzG], Hc as [HcL HcG].
    unfold ctx_obj_met in *. rewrite visibility_of_mutable_mode in *.
    pose proof (@typing_context_extends_hide _ _ e Hscope) as Hhide.
    pose proof (@typing_context_extends_push _ (ctx_hide G) e z v_par TZ HzG Hhide) as Hpar.
    assert (HcFresh : c §# (ctx_hide G § z / v_par ~ TZ))
      by now apply fresh_pushed_context.
    set (T1 := typ_and (open z TC) (typ_and (open w R) (open c R))).
    set (T2 := typ_and (open z TC) (typ_and (open y R) (open c R))).
    assert (Hsub : (ctx_hide G § z / v_par ~ TZ) ⁏ e ⊢ T2 <: T1).
    { unfold T1, T2. apply subtyp_and2; [apply subtyp_and11 |].
      eapply subtyp_trans; [apply subtyp_and12 |].
      apply subtyp_and2; [| apply subtyp_and12].
      eapply subtyp_trans; [apply subtyp_and11 | now apply subtyp_tyq]. }
    pose proof (typing_context_extends_push v_recv T1 HcFresh Hpar) as Hrecv.
    pose proof (@narrow_last_binding _ e c v_recv T2 T1 HcFresh Hsub) as Hnarrow.
    pose proof (typing_context_extends_trans Hrecv Hnarrow) as Hext.
    exact (proj1 replace_term_bindings _ _ _ _ _ (H z HzL c Hneq HcL) _ Hext Hext).
Qed.

Local Lemma literal_defs_change_owner G e w y R (ds : defs) T :
    G §§ objctx_lit w R ⁏ e ⊢ ds ∶ T ->
    G ⁏ e ⊢ w ∶ open w R ->
    ctx_vis G w ->
    e ⊢ open y R ≈ open w R ->
    G §§ objctx_heap y R ⁏ e ⊢ ds ∶ T.
Proof.
  intros Hty Hw Hvis Hself.
  change (ty_defs typing_mode G (objctx_lit w R) e ds T) in Hty.
  dependent induction Hty;
    eauto using ty_defs_one, ty_defs_cons, literal_definition_change_owner.
Qed.

Local Lemma open_record_member R D n x :
    record_has R D -> record_has (open_rec n x R) (open_rec n x D).
Proof.
  intros H; induction H; cbn [open_rec TypOpenable open_rec_typ].
  - apply rh_one.
  - now apply rh_andl.
  - now apply rh_andr.
Qed.

Local Lemma invert_open_record_member R D n x :
    record_has (open_rec n x R) D ->
    exists D0, record_has R D0 /\ D = open_rec n x D0.
Proof.
  revert D n x. induction R; intros D n x H;
    cbn [open_rec TypOpenable open_rec_typ] in H; inversion H; subst.
  - eexists. split; [constructor | reflexivity].
  - destruct (IHR1 _ _ _ ltac:(eassumption)) as [D0 [HD Heq]].
    exists D0. split; [now apply rh_andl | exact Heq].
  - destruct (IHR2 _ _ _ ltac:(eassumption)) as [D0 [HD Heq]].
    exists D0. split; [now apply rh_andr | exact Heq].
Qed.

Local Definition diagonal_declaration D :=
  match D with
  | dec_typ _ L U | dec_fld _ L U => L = U
  | dec_met _ _ _ _ => True
  end.

Local Lemma typed_def_diagonal G Go e d D :
    G §§ Go ⁏ e ⊢ d ∶d D -> diagonal_declaration D.
Proof. intros H; destruct H; simpl; auto. Qed.

Local Lemma opened_literal_record_diagonal F Go e R (ds : defs) w y :
    w \notin fv R ->
    F §§ Go ⁏ e ⊢ ds ∶ open w R ->
    forall D, record_has (open y R) D -> diagonal_declaration D.
Proof.
  intros Hfresh Hty D Hmember.
  destruct (invert_open_record_member R 0 y Hmember) as (D0 & Hmem & ->).
  pose proof (open_record_member 0 w Hmem) as Hmem'.
  destruct (typed_record_contains_declaration Hty Hmem') as [d Hd].
  pose proof (typed_def_diagonal Hd) as Hdiag.
  assert (HfreshD : w \notin fv D0).
  { intros Hbad.
    assert (Hscope : names_outside \{w} (fv R)).
    { intros z Hz. rewrite notin_singleton. intros ->. exact (Hfresh Hz). }
    pose proof (@record_member_names_outside R D0 \{w} Hmem Hscope) as Houtside.
    exact (Houtside w Hbad ltac:(now rewrite in_singleton)). }
  destruct D0 as [a L U | a L U | m C Z T]; cbn [diagonal_declaration open_rec
    DecOpenable open_rec_dec] in *; try exact I;
    change (w \notin fv L \u fv U) in HfreshD;
    apply notin_union in HfreshD as [HL HU];
    assert (L = U) by (eapply open_fresh_type_injective; eassumption);
    subst; reflexivity.
Qed.

Local Lemma heap_definition_substitute_equivalent_type G e y R d D D' :
    G §§ objctx_heap y R ⁏ e ⊢ d ∶d D ->
    equivalent_declaration_parts e D D' ->
    diagonal_declaration D' ->
    G §§ objctx_heap y R ⁏ e ⊢ d ∶d D'.
Proof.
  intros Hty Hparts Hdiagonal. inversion Hty; subst;
    destruct D' as [a' L' U' | a' L' U' | m' C' Z' T']; simpl in *; try contradiction.
  - destruct Hparts as [<- [HLo HUp]]. subst U'.
    eapply ty_def_typ with (L := L). intros x Hx.
    eapply type_equiv_transitive; eauto.
  - destruct Hparts as [<- [HLo HUp]]. subst U'.
    apply ty_def_fld; [assumption |].
    eapply ty_var_sub; [eassumption | now apply subtyp_tyq].
  - destruct Hparts as [<- [HC [HZ HT]]].
    eapply ty_def_met with (L := L \u ctx_dom G).
    intros z Hz c Hneq Hc.
    apply notin_union in Hz as [HzL HzG]. apply notin_union in Hc as [HcL HcG].
    unfold ctx_obj_met in *. rewrite visibility_of_mutable_mode in *.
    assert (HsubZ : ctx_hide G ⁏ e ⊢ Z' <: TZ).
    { apply subtyp_tyq, type_equiv_symmetric, HZ. }
    pose proof (@narrow_last_binding (ctx_hide G) e z v_par Z' TZ HzG HsubZ) as Hpar.
    assert (HcFresh : c §# (ctx_hide G § z / v_par ~ Z'))
      by now apply fresh_pushed_context.
    set (Csrc := typ_and (open z TC) (typ_and (open y R) (open c R))).
    set (Cdst := typ_and (open z C') (typ_and (open y R) (open c R))).
    assert (HsubC : (ctx_hide G § z / v_par ~ Z') ⁏ e ⊢ Cdst <: Csrc).
    { unfold Csrc, Cdst. apply subtyp_and2; [| apply subtyp_and12].
      eapply subtyp_trans; [apply subtyp_and11 |].
      apply subtyp_tyq, type_equiv_symmetric, HC. }
    pose proof (typing_context_extends_push v_recv Csrc HcFresh Hpar) as Hrecv.
    pose proof (@narrow_last_binding _ e c v_recv Cdst Csrc HcFresh HsubC) as Hnarrow.
    pose proof (typing_context_extends_trans Hrecv Hnarrow) as Hext.
    eapply ty_trm_sub with (T := open_met z c TR); [| apply subtyp_tyq; exact (HT z c)].
    exact (proj1 replace_term_bindings _ _ _ _ _ (H z HzL c Hneq HcL) _ Hext Hext).
Qed.

Local Lemma heap_defs_substitute_equivalent_type G e y R (ds : defs) T U :
    G §§ objctx_heap y R ⁏ e ⊢ ds ∶ T ->
    e ⊢ T ≈ U ->
    (forall D, record_has U D -> diagonal_declaration D) ->
    G §§ objctx_heap y R ⁏ e ⊢ ds ∶ U.
Proof.
  intros Hty. change (ty_defs typing_mode G (objctx_heap y R) e ds T) in Hty.
  revert U. dependent induction Hty; intros U HU HD;
    apply type_equiv_has_parts in HU; destruct U; simpl in HU; try contradiction.
  - apply ty_defs_one. eapply heap_definition_substitute_equivalent_type; try eassumption.
    now apply HD, rh_one.
  - destruct HU as [HL HR]. destruct U2; simpl in *;
      apply type_equiv_has_parts in HR; simpl in HR; try contradiction.
    apply ty_defs_cons; try assumption.
    + eapply IHHty; try reflexivity; try (apply type_equiv_symmetric; eassumption);
        try eassumption. intros D0 HD0. now apply HD, rh_andl.
    + eapply heap_definition_substitute_equivalent_type; try eassumption.
      now apply HD, rh_andr, rh_one.
Qed.

Local Lemma deref_fresh_reference e x :
    x # e -> deref e (avar_f x) = avar_f x.
Proof.
  induction e as [| E y z IH] using env_ind; intros Hfresh.
  - rewrite empty_def. reflexivity.
  - rewrite dom_push, notin_union, notin_singleton in Hfresh.
    destruct Hfresh as [Hneq Hdom].
    rewrite <- cons_to_push.
    change (deref E (avar_f (If x = y then z else x)) = avar_f x).
    rewrite If_r by assumption. now apply IH.
Qed.

Local Lemma deref_reference_binding e x y :
    binds x y e -> y # e -> deref e (avar_f x) = avar_f y.
Proof.
  induction e as [| E w z IH] using env_ind; intros Hb Hfresh.
  - exfalso. eapply binds_empty_inv; eassumption.
  - apply binds_push_inv in Hb as [[-> ->] | [Hneq Hb]];
      rewrite dom_push, notin_union in Hfresh;
      destruct Hfresh as [_ Hfresh];
      rewrite <- cons_to_push;
      cbn [deref deref_avar deref_base subst_var AvarSubstVar].
    + rewrite If_l by reflexivity. now apply deref_fresh_reference.
    + rewrite If_r by assumption. now apply IH.
Qed.

Local Lemma renv_referent_not_key G e w y :
    ctx_ok G ->
    ctx_weakens G ->
    ctx_kdom v_ref G = dom e ->
    renv_corr G e ->
    binds w y e ->
    y # e.
Proof.
  intros Hok Hweak Hdom Henv Hbind Hy.
  destruct (reference_location_annotations Hok Henv Hbind)
    as (R & B & Gw & Gy & HwKind & HyKind).
  rewrite <- Hdom in Hy.
  destruct (@kind_domain_has_binding G v_ref y Hweak Hok Hy) as (U & J & HyRef).
  discriminate (kind_binding_unique HyKind HyRef).
Qed.

Local Lemma deref_keeps_label e d : label_of (deref e d) = label_of d.
Proof. destruct d; reflexivity. Qed.

Local Lemma deref_defs_lookup e ds l :
    get_def l (deref e ds) = option_map (deref e) (get_def l ds).
Proof.
  induction ds as [| ds IH d]; [reflexivity |].
  change ((If label_of (deref e d) = l then Some (deref e d)
       else get_def l (deref e ds)) =
    option_map (deref e) (If label_of d = l then Some d else get_def l ds)).
  rewrite deref_keeps_label. destruct (classic (label_of d = l)).
  - now rewrite !If_l by assumption.
  - now rewrite !If_r by assumption.
Qed.

Local Lemma deref_typed_heap_defs G e y R ds T :
    ctx_ok G -> ctx_weakens G ->
    ctx_kdom v_ref G = dom e ->
    renv_corr G e ->
    G §§ objctx_heap y R ⁏ e ⊢ ds ∶ T ->
    all_tfree_k_defs G ds v_ref ->
    G §§ objctx_heap y R ⁏ e ⊢ deref e ds ∶ T /\ defs_varkinds G (deref e ds).
Proof.
  intros Hok Hweak Hdom Henv Hty.
  assert (Hdef : forall d D, G §§ objctx_heap y R ⁏ e ⊢ d ∶d D ->
    all_tfree_k_def G d v_ref ->
    G §§ objctx_heap y R ⁏ e ⊢ deref e d ∶d D /\ def_varkinds G (deref e d)).
  { intros d D Hd Hk. inversion Hd; subst.
    - split; [eapply ty_def_typ; eassumption | constructor].
    - match goal with Hty : _ ⁏ _ ⊢ ?x ∶ _ |- _ =>
        let Href := fresh "Href" in
        pose proof (Hk x (tfree_def_trm x a)) as Href;
        destruct Href as (A & J & Href);
        pose proof (kind_binding_in_kind_domain Href) as Hin;
        rewrite Hdom in Hin;
        destruct (get_some Hin) as [b Hb];
        change (binds x b e) in Hb;
        pose proof (renv_referent_not_key Hok Hweak Hdom Henv Hb) as Hfresh;
        pose proof (deref_reference_binding Hb Hfresh) as Hderef;
        cbn [deref deref_def]
      end.
      rewrite Hderef.
      destruct (reference_location_annotations Hok Henv Hb)
        as (U & M & Gx & Gy & _ & Hy).
      assert (HyKind : ctx_k G b v_loc) by (eexists; eexists; exact Hy).
      split; [apply ty_def_fld | constructor]; try exact HyKind.
      + intros _. now apply (kind_bound_visible HyKind).
      + eapply reference_typing_at_location; eassumption.
    - split.
      + eapply ty_def_met; eassumption.
      + constructor. intros z Hz. apply Hk. now apply tfree_def_met. }
  change (ty_defs typing_mode G (objctx_heap y R) e ds T) in Hty.
  dependent induction Hty; intros Hk.
  - destruct (Hdef _ _ H ltac:(intros z Hz; apply Hk; now apply tfree_defs_cons_r))
      as [Hd HK].
    split; [now apply ty_defs_one | constructor; [constructor | exact HK]].
  - destruct (IHHty Hmm y R Hok Hweak Hdom Henv eq_refl Hdef
      ltac:(intros z Hz; apply Hk; now apply tfree_defs_cons_l))
      as [Hds HK].
    destruct (Hdef _ _ H0 ltac:(intros z Hz; apply Hk; now apply tfree_defs_cons_r))
      as [Hd HKd].
    split; [| now constructor].
    apply ty_defs_cons; try assumption.
    unfold defs_hasnt in *. rewrite deref_keeps_label, deref_defs_lookup.
    now rewrite H1.
Qed.

Local Lemma allocated_heap_correspondence F e S y w R ds :
    let A := typ_objref R (typ_mut_marker typ_bot) in
    let G := F § y / v_loc ~ A § w / v_ref ~ A in
    let p := e & w ~ y in
    let item' := item_obj (deref p ds) in
    heap_correspond F e S ->
    y §# F -> w §# F -> w <> y -> y # S -> w # e ->
    (ctx_ok G -> ctx_weakens G -> ctx_kdom v_ref G = dom p -> renv_corr G p ->
      G §§ objctx_heap y R ⁏ p ⊢ deref p ds ∶ open y R /\ defs_varkinds G (deref p ds)) ->
    heap_correspond G p (S & y ~ item').
Proof.
  intros A G p item' (Hok & Hwk & HS & He & Hloc & Href & Hcorr & Hitem)
    Hy Hw Hneq HyS HwE Hnew.
  assert (HwG : w §# (F § y / v_loc ~ A)) by now apply fresh_pushed_context.
  assert (HG : ctx_ok G) by (unfold G; do 2 (apply ctx_ok_push; [| assumption]); exact Hok).
  assert (HGwk : ctx_weakens G) by (unfold G; now do 2 constructor).
  assert (Hrf : ctx_kdom v_ref G = dom p).
  { unfold G, p. simpl ctx_kdom.
    rewrite If_l by reflexivity. rewrite If_r by discriminate. now rewrite Href, dom_push. }
  assert (Hcorr' : renv_corr G p).
  { unfold G, p.
    eapply renv_corr_ref with (G2 := F § y / v_loc ~ A) (G3 := F) (Tw := A) (Ty := A).
    - apply ctx_binds_k_e.
    - apply ctx_binds_k_e.
    - unfold A. constructor. destruct typing_mode; simpl in *; try discriminate;
        exists typ_bot; auto.
    - apply renv_correspondence_extend_scope;
        [now apply renv_correspondence_extend_scope | exact HwG]. }
  split; [exact HG |]. split; [exact HGwk |].
  split; [now apply ok_push |]. split; [now apply ok_push |].
  split.
  { unfold G. simpl ctx_kdom.
    rewrite If_r by discriminate. rewrite If_l by reflexivity. now rewrite Hloc, dom_push. }
  split; [exact Hrf |]. split; [exact Hcorr' |].
  intros x Hx. rewrite dom_push, in_union, in_singleton in Hx.
  destruct Hx as [-> | Hx].
  - destruct (Hnew HG HGwk Hrf Hcorr') as [Htyped Hk].
    eapply ty_item_obj_s; [| apply binds_push_eq | reflexivity | exact Htyped | exact Hk].
    unfold G, A. apply ctx_binds_n; [congruence | apply ctx_binds_e].
  - assert (Hxy : x <> y) by (intros ->; contradiction).
    specialize (Hitem x Hx). inversion Hitem; subst.
    + pose proof mode_disallows_functions. congruence.
    + assert (Hext : typing_context_extends F G p).
      { unfold G. eapply typing_context_extends_trans with (G := F § y / v_loc ~ A);
          apply extend_context_typing; assumption. }
      assert (Hp : env_binds_more e p).
      { intros b a Hb. unfold p. apply binds_push_neq; [exact Hb |].
        intros ->. exact (binds_fresh_inv Hb HwE). }
      eapply ty_item_obj_s; [| apply binds_push_neq; eassumption | reflexivity | |].
      * match goal with Hb : ctx_binds x ?Tx F |- _ =>
          exact (@fresh_context_extension _ w v_ref A HwG _ Tx
            (@fresh_context_extension F y v_loc A Hy _ Tx Hb))
        end.
      * pose proof (identity_renaming_of_contexts Hext) as Hrename.
        match goal with Hd : F §§ objctx_heap x ?U ⁏ e ⊢ ?defs ∶ open x ?U |- _ =>
          pose proof (proj2 (proj2 (proj2 term_typing_renaming))
            F (objctx_heap x U) e defs _ Hd (fun v => v) \{} G p
            (fun _ _ => eq_refl) (extends_reference_environment Hp) Hrename Hrename)
            as Hdefs
        end.
        cbn [rename_objctx] in Hdefs.
        now rewrite (proj2 (proj2 (proj2 rename_terms_identity))),
          !(proj1 rename_types_identity) in Hdefs.
      * apply (@definitions_keep_kinds _ w v_ref A _ HwG).
        apply (@definitions_keep_kinds F y v_loc A _ Hy). assumption.
Qed.

Local Lemma open_syntax_preserves_tfree_kinds F G w k (t : trm) ds :
    (forall v, ctx_k F v k -> ctx_k G v k) ->
    ctx_k G w k ->
    (forall v, tfree v t -> ctx_k F v k) ->
    (forall v, tfree v ds -> ctx_k F v k) ->
    all_tfree_k_trm G (open w t) k /\ all_tfree_k_defs G (open w ds) k.
Proof.
  intros Hext Hw Ht Hds. split; intros v Hv.
  - destruct (proj1 tfree_opened_mutual t 0 w v Hv) as [Hv' | ->]; auto.
  - destruct (proj2 (proj2 (proj2 tfree_opened_mutual)) ds 0 w v Hv) as [Hv' | ->]; auto.
Qed.

Local Lemma allocation_opens_closed_syntax R ds t w :
    closed (trm_lit (lit_obj R ds) t) ->
    closed (open w t) /\ closed (open w ds).
Proof.
  intros Hclosed.
  assert (Hparts : forall n x,
    open_rec (S n) x t = t /\ open_rec (S n) x ds = ds).
  { intros n x. pose proof (Hclosed n x) as Hopen.
    change (trm_lit (lit_obj (open_rec (S n) x R) (open_rec (S n) x ds))
      (open_rec (S n) x t) = trm_lit (lit_obj R ds) t) in Hopen.
    injection Hopen; auto. }
  split; intros n x; destruct n as [|n].
  - apply (proj1 term_open_absorbs_mutual).
  - rewrite (proj1 term_open_commutes_mutual t (S n) 0 x w) by discriminate.
    now rewrite (proj1 (Hparts n x)).
  - apply (proj2 (proj2 (proj2 term_open_absorbs_mutual))).
  - rewrite (proj2 (proj2 (proj2 term_open_commutes_mutual)) ds (S n) 0 x w) by discriminate.
    now rewrite (proj2 (Hparts n x)).
Qed.

Local Lemma deref_definitions_closed e (ds : defs) :
    closed ds -> closed (deref e ds).
Proof.
  assert (Hvars : forall x, exists y, deref e (avar_f x) = avar_f y).
  { induction e as [| E x y IH] using env_ind; intros z.
    - exists z. rewrite empty_def. reflexivity.
    - rewrite <- cons_to_push.
      change (exists q, deref E (avar_f (If z = x then y else z)) = avar_f q).
      apply IH. }
  induction ds as [| ds IH d]; intros Hclosed.
  - intros n x. reflexivity.
  - assert (Hparts : closed ds /\ closed d).
    { split; intros n x; pose proof (Hclosed n x) as Hopen;
        change (defs_cons (open_rec n x ds) (open_rec n x d) = defs_cons ds d) in Hopen;
        now injection Hopen. }
    destruct Hparts as [Hs Hd]. specialize (IH Hs).
    assert (Hd' : closed (deref e d)).
    { destruct d as [| l a |]; try exact Hd.
      destruct a as [k | z].
      - destruct (var_fresh (\{} : vars)) as [x _].
        pose proof (Hd k x) as Hbad.
        change (def_fld l (open_rec k x (avar_b k)) = def_fld l (avar_b k)) in Hbad.
        rewrite avar_open_here in Hbad. discriminate.
      - destruct (Hvars z) as [q Hq].
        change (closed (def_fld l (deref e (avar_f z)))).
        rewrite Hq. intros n x. reflexivity. }
    intros n x.
    change (defs_cons (open_rec n x (deref e ds)) (open_rec n x (deref e d)) =
      defs_cons (deref e ds) (deref e d)).
    now rewrite IH, Hd'.
Qed.

Local Lemma allocation_step_preservation F s S e Lv y w R ds t U :
    let C := (trm_lit (lit_obj R ds) t ; s ; S ; e ; Lv) in
    let A := typ_objref R (typ_mut_marker typ_bot) in
    let G := F § y / v_loc ~ A § w / v_ref ~ A in
    let p := e & w ~ y in
    let S' := S & y ~ item_obj (deref p (open w ds)) in
    execution_config F C U -> fresh_in_config (y :: w :: nil) C -> w <> y ->
    execution_config G (open w t ; s ; S' ; p ; fv_config C) U /\
    G §§ objctx_heap y R ⁏ p ⊢ open w ds ∶ open y R.
Proof.
  intros C A G p S' Hcfg Hfresh Hneq.
  inversion Hcfg as [F0 e0 s0 S0 Lv0 t0 T U0 HF HS Hstack HKs Hty HKt Hnames Hnull Hclosed HU]; subst.
  destruct (typed_literal_operands Hty eq_refl)
    as (L & K & Tin & Hdefs & Hind & Hbody & Hsub).
  assert (Hy : y \notin fv_config C) by (inversion Hfresh; assumption).
  assert (Hw : w \notin fv_config C).
  { inversion Hfresh; subst.
    match goal with Hf : fresh _ _ (w :: nil) |- _ =>
      inversion Hf; subst
    end.
    match goal with Hf : w \notin _ |- _ =>
      apply notin_union in Hf as [Hf _]; exact Hf
    end. }
  assert (HyS : y # S) by exact (proj1 (fresh_config_keys Hfresh)).
  assert (HwE : w # e).
  { intro Hbad. apply Hw. unfold C; cbn. do 3 (rewrite in_union; right).
    rewrite in_union. left. rewrite in_union. now left. }
  destruct Hnames as ((Hdom & Hfv) & Hres).
  assert (HyF : y §# F) by (intros Hbad; apply Hy, Hdom; exact Hbad).
  assert (HwF : w §# F) by (intros Hbad; apply Hw, Hdom; exact Hbad).
  assert (HwG : w §# (F § y / v_loc ~ A)) by now apply fresh_pushed_context.
  assert (HRnames : fv R \c fv_config C).
  { intros x Hx. unfold C; cbn. rewrite in_union. left.
    change (x \in (fv R \u fv ds) \u fv t).
    rewrite !in_union. auto. }
  assert (HAnames : fv A \c fv_config C).
  { intros x Hx. change (x \in fv R \u (\{} \u \{})) in Hx.
    rewrite !in_union, in_empty in Hx. apply HRnames. tauto. }
  assert (Hp : env_binds_more e p).
  { intros b x Hb. unfold p. apply binds_push_neq; [exact Hb |].
    intros ->. exact (binds_fresh_inv Hb HwE). }
  assert (Hext : typing_context_extends F G p).
  { unfold G. eapply typing_context_extends_trans with (G := F § y / v_loc ~ A);
      apply extend_context_typing; assumption. }
  assert (HextB : includes_bindings F G).
  { intros x B Hb. unfold G.
    exact (@fresh_context_extension _ w v_ref A HwG _ B
      (@fresh_context_extension F y v_loc A HyF _ B Hb)). }
  assert (Hopened : G §§ objctx_lit w R ⁏ p ⊢ open w ds ∶ open w R).
  { eapply open_literal_in_extended_context; try eassumption.
    intros x Hx. exact ((proj2 Hext) x Hx). }
  assert (HwR : w \notin fv R) by (intros Hbad; apply Hw, HRnames; exact Hbad).
  destruct (typed_defs_are_record Hopened) as (Labels & Hrecord & _).
  assert (HR : record_type R).
  { exists Labels. eapply unopened_record_typ; eassumption. }
  assert (HwB : ctx_binds w A G) by (unfold G; apply ctx_binds_e).
  assert (HwY : binds w y p) by (unfold p; apply binds_push_eq).
  assert (Hwvis : ctx_vis G w) by (unfold G; apply ctx_vis_e).
  assert (Halias : p ⊢ open y R ≈ open w R).
  { eapply independent_type_open_alias; [| exact Hind | reflexivity].
    apply tyq_var_sym, tyq_var_binds, HwY. }
  destruct (object_reference_record_views HwY HwB Hind) as [_ HwOwn].
  pose proof (@literal_defs_change_owner G p w y R _ _ Hopened HwOwn Hwvis Halias) as Hdefs_w.
  assert (Hdefs_y : G §§ objctx_heap y R ⁏ p ⊢ open w ds ∶ open y R).
  { eapply heap_defs_substitute_equivalent_type; [exact Hdefs_w | now apply type_equiv_symmetric |].
    eapply opened_literal_record_diagonal; eassumption. }
  split; [| exact Hdefs_y].
  assert (Hkind : forall x k, ctx_k F x k -> ctx_k G x k).
  { intros x k Hk. unfold G.
    exact (@kind_keep_under_binding _ w v_ref A _ _ HwG
      (@kind_keep_under_binding F y v_loc A _ _ HyF Hk)). }
  assert (HwKind : ctx_k G w v_ref)
    by (unfold G; eexists; eexists; apply ctx_binds_k_e).
  destruct (@open_syntax_preserves_tfree_kinds F G w v_ref t ds
    ltac:(intros; now apply Hkind) HwKind
    ltac:(intros; apply HKt, tfree_trm_lit_r; assumption)
    ltac:(intros; apply HKt, tfree_trm_lit_l, tfree_lit_obj; assumption))
    as [HKnext HKdefs].
  assert (HS' : heap_correspond G p S').
  { unfold G, p, S'. eapply allocated_heap_correspondence; try eassumption.
    intros Hok Hwk Href Henv. eapply deref_typed_heap_defs; eassumption. }
  assert (Hscope := identity_renaming_of_contexts Hext).
  assert (Henv := extends_reference_environment Hp).
  assert (Hid : renaming_fixes_outside \{} (fun x => x)) by (intros x _; reflexivity).
  assert (Hnext : G ⁏ p ⊢ open w t ∶ Tin).
  { assert (HbodyG : forall x, x \notin (K \u ctx_dom G) ->
      G § x / v_let ~ A ⁏ p ⊢ open x t ∶ Tin).
    { intros x Hx. apply notin_union in Hx as [HxL HxG].
      pose proof (typing_context_extends_push v_let A HxG Hext) as Hpush.
      pose proof (identity_renaming_of_contexts Hpush) as Hnew.
      pose proof (proj1 term_typing_renaming _ _ _ _ _ (Hbody x HxL)
        (fun v => v) \{} _ p Hid Henv Hnew Hnew) as Hresult.
      cbn [rename_objctx] in Hresult.
      now rewrite (proj1 rename_terms_identity), (proj1 rename_types_identity) in Hresult. }
    eapply instantiate_let_body; [exact HbodyG | now apply ty_var_var | exact Hwvis]. }
  pose proof (@renamed_subtyping F G e p (fun x => x) \{} _ _ Hid Henv (proj1 Hscope) Hsub)
    as Hresult.
  rewrite !(proj1 rename_types_identity) in Hresult.
  pose proof (history_in_config (open w t ; s ; S' ; p ; fv_config C)) as Hcarry.
  eapply execution_config_intro with (T := T); try eassumption.
  - assert (Hcap : inert_typ A v_loc /\ inert_typ A v_ref).
    { split; apply inert_typ_obj; try assumption; unfold refcap_inert_type;
        destruct typing_mode; simpl in *; try discriminate; constructor. }
    destruct Hcap as [Hl Hr]. unfold G.
    apply inert_push; try assumption; [| constructor | |].
    + apply inert_push; try assumption; [constructor | |].
      * intros Hbad. apply Hy, Hfv, Hbad.
      * intros Hbad. apply Hy, HAnames, Hbad.
    + change (w \notin fv A \u ctx_fv F). rewrite notin_union. split;
        intros Hbad; apply Hw; [now apply HAnames | now apply Hfv].
    + intros Hbad. apply Hw, HAnames, Hbad.
  - eapply weaken_stack_env; eassumption.
  - intros x Hx. apply Hkind. now apply HKs.
  - eapply ty_trm_sub; eassumption.
  - split; [split |]; intros x Hx.
    + unfold G in Hx. simpl ctx_dom in Hx. rewrite !in_union, !in_singleton in Hx.
      destruct Hx as [-> | [-> | Hx]].
      * do 3 (rewrite in_union; right). rewrite in_union. left.
        unfold p. rewrite in_union. left. rewrite dom_push, in_union, in_singleton. auto.
      * do 2 (rewrite in_union; right). rewrite in_union. left.
        unfold S'. rewrite in_union. left. rewrite dom_push, in_union, in_singleton. auto.
      * apply Hcarry. now apply Hdom.
    + change (x \in fv A \u (fv A \u ctx_fv F)) in Hx.
      apply Hcarry. rewrite !in_union in Hx. destruct Hx as [Hx | [Hx | Hx]]; auto.
    + apply Hcarry. now apply Hres.
  - destruct Hnull as [z Hz]. exists z. exact (@history_in_config C z Hz).
  - inversion Hclosed; subst.
    destruct (@allocation_opens_closed_syntax R ds t w ltac:(assumption)) as [Hn Hds].
    constructor; try assumption.
    unfold S'. apply heap_closed_push; [assumption |].
    intros n x. change (item_obj (open_rec n x (deref p (open w ds))) =
      item_obj (deref p (open w ds))).
    f_equal. exact (deref_definitions_closed p Hds n x).
Qed.

Local Lemma deref_field_source e (ds : defs) a z :
    defs_has (deref e ds) (def_fld a (avar_f z)) ->
    exists q, defs_has ds (def_fld a q) /\ deref e q = avar_f z.
Proof.
  intros H. unfold defs_has in H. rewrite deref_defs_lookup in H.
  change (option_map (deref e) (get_def (label_fld a) ds) =
    Some (def_fld a (avar_f z))) in H.
  destruct (get_def (label_fld a) ds) as [d |] eqn:Hd; [| discriminate].
  destruct d as [| a' arg |]; cbn [option_map deref deref_def] in H; try discriminate.
  inversion H; subst a'. exists arg. split; [exact Hd |].
  now injection H.
Qed.

Local Lemma definition_member_free (ds : defs) d x :
    defs_has ds d -> tfree x d -> tfree x ds.
Proof.
  induction ds as [| ds IH d']; unfold defs_has in *; simpl get_def; [discriminate |].
  destruct (classic (label_of d' = label_of d)) as [Heq | Hneq].
  - rewrite If_l by assumption. intros Heqd Hfree. inversion Heqd; subst.
    now apply tfree_defs_cons_r.
  - rewrite If_r by assumption. intros Hmember Hfree.
    apply tfree_defs_cons_l. now apply IH.
Qed.

Local Lemma allocation_backward_reachability F s S e Lv y w R ds t U :
    let C := (trm_lit (lit_obj R ds) t ; s ; S ; e ; Lv) in
    let A := typ_objref R (typ_mut_marker typ_bot) in
    let G := F § y / v_loc ~ A § w / v_ref ~ A in
    let p := e & w ~ y in
    let S' := S & y ~ item_obj (deref p (open w ds)) in
    let D := (open w t ; s ; S' ; p ; fv_config C) in
    execution_config F C U -> execution_config G D U ->
    fresh_in_config (y :: w :: nil) C -> w <> y ->
    G §§ objctx_heap y R ⁏ p ⊢ open w ds ∶ open y R ->
    forall target, G ⊢ D mreach target -> target = y \/ F ⊢ C mreach target.
Proof.
  intros C A G p S' D Hcfg Hcfg' Hfresh Hneq Hdefs.
  assert (HF : inert F) by (inversion Hcfg; assumption).
  assert (HG : inert G) by (inversion Hcfg'; assumption).
  assert (HS : heap_correspond F e S) by (inversion Hcfg; assumption).
  assert (HS' : heap_correspond G p S') by (inversion Hcfg'; assumption).
  assert (HK : all_tfree_k_trm F (trm_lit (lit_obj R ds) t) v_ref)
    by (inversion Hcfg; assumption).
  assert (Hnames : ty_nothing_fresh_in_config F U C) by (inversion Hcfg; assumption).
  assert (Hy : y \notin fv_config C) by (inversion Hfresh; assumption).
  assert (Hw : w \notin fv_config C).
  { inversion Hfresh; subst.
    match goal with Hf : fresh _ _ (w :: nil) |- _ => inversion Hf; subst end.
    match goal with Hf : w \notin _ |- _ =>
      apply notin_union in Hf as [Hf _]; exact Hf end. }
  set (L := \{y} \u \{w}).
  assert (HL : names_outside L (fv_config C)).
  { intros x Hx. unfold L. rewrite notin_union, !notin_singleton.
    split; intros ->; contradiction. }
  destruct Hnames as ((Hdom & Hfv) & Hresult).
  assert (Hscope : names_outside L (ctx_fv F)).
  { intros x Hx. apply HL, Hfv, Hx. }
  assert (HenvScope : names_outside L (fv_renv e)).
  { intros x Hx. apply HL. unfold C; cbn.
    do 3 (rewrite in_union; right). rewrite in_union. now left. }
  assert (HyF : y §# F) by (intros Hbad; apply Hy, Hdom, Hbad).
  assert (HwF : w §# F) by (intros Hbad; apply Hw, Hdom, Hbad).
  assert (HwG : w §# (F § y / v_loc ~ A)) by now apply fresh_pushed_context.
  assert (Havoid : forall x, x \notin L -> x <> y /\ x <> w).
  { intros x Hx. unfold L in Hx. now rewrite notin_union, !notin_singleton in Hx. }
  assert (Hstrength : forall x B, x \notin L -> ctx_binds x B G -> ctx_binds x B F).
  { intros x B Hx Hb. destruct (Havoid x Hx).
    unfold G in Hb. inversion Hb; subst; try congruence.
    match goal with Hentry : ctx_binds _ _ (F § _ / _ ~ _) |- _ =>
      inversion Hentry; subst; congruence || assumption end. }
  assert (Hweak : includes_bindings F G).
  { intros x B Hb. exact (@fresh_context_extension _ w v_ref A HwG _ B
      (@fresh_context_extension F y v_loc A HyF _ B Hb)). }
  assert (Hcanon : preserves_old_canonical_locations e p L).
  { unfold p. apply push_same_existing_canonical_locations; [| exact HenvScope].
    unfold L. rewrite in_union, !in_singleton. now right. }
  pose proof (@stable_selection_bounds_from_context F G e p L Hstrength Hscope Hcanon) as Hbounds.
  pose proof HS as (Hok & Hwk & _ & _ & _ & HrefDom & Henv & _).
  pose proof HS' as (Hok' & Hwk' & _ & _ & _ & HrefDom' & Henv' & _).
  assert (HrRef : forall q b, binds q b e ->
    G ⁏ p ⊢ q ∶ typ_mut_marker typ_bot ->
    F ⁏ e ⊢ trm_var (avar_f q) ∶ typ_mut_marker typ_bot).
  { intros q b Hqb Hty.
    destruct (reference_location_annotations Hok Henv Hqb)
      as (R0 & B & Q & Q' & Hq & _).
    pose proof (kind_binding_gives_binding Hq) as HqB.
    assert (Hcap : names_outside L (fv B)).
    { intros x Hx. apply Hscope. eapply bound_type_free_in_context; [exact HqB |].
      cbn [fv TypFreeVar fv_typ fv_dec]. rewrite !in_union. tauto. }
    apply ty_trm_var.
    { intro. apply kind_bound_visible with (k := v_ref).
      exists (typ_objref R0 (typ_mut_marker B)), Q. exact Hq. }
    eapply existing_reference_mutability_reflects; try eassumption.
    now apply Hweak. }
  assert (HrFld : forall q d a b, binds q (item_obj d) S ->
    defs_has d (def_fld a (avar_f b)) ->
    G ⁏ p ⊢ trm_var (avar_f q) ∶ typ_rcd (dec_fld a typ_bot (typ_mut_marker typ_bot)) ->
    F ⁏ e ⊢ trm_var (avar_f q) ∶ typ_rcd (dec_fld a typ_bot (typ_mut_marker typ_bot))).
  { intros q data a b Hq Ha Ht.
    destruct (heap_location_info HS Hq) as [Hloc Hvis].
    destruct (heap_field_annotation HS Hq Ha) as (R0 & B0 & V & Hqb & Hfld).
    assert (HqL : q \notin L).
    { apply HL. unfold C; cbn. do 2 (rewrite in_union; right).
      rewrite in_union. left. rewrite in_union. left. now apply (binding_in_domain Hq). }
    apply ty_trm_var; [intros _; exact Hvis |].
    pose proof (variable_term_typing Ht eq_refl) as Hvar.
    eapply existing_field_mutability_reflects; try eassumption.
    now apply Hweak. }
  assert (HnewHeap : binds y (item_obj (deref p (open w ds))) S')
    by (unfold S'; apply binds_push_eq).
  assert (HyG : ctx_binds y A G)
    by (unfold G; apply ctx_binds_n; [congruence | apply ctx_binds_e]).
  assert (HfromNew : forall a b, defs_has (deref p (open w ds)) (def_fld a (avar_f b)) ->
    G ⁏ p ⊢ trm_var (avar_f y) ∶ typ_rcd (dec_fld a typ_bot (typ_mut_marker typ_bot)) ->
    b = y \/ F ⊢ C mreach b).
  { intros a b Hmember Hmutable.
    destruct (@deref_field_source p (open w ds) a b Hmember) as [av [Horigin Haddr]].
    destruct (typed_defs_member_record Hdefs Horigin) as (Dec & HD & Htyped).
    inversion Htyped; subst.
    pose proof (definition_member_free Horigin (tfree_def_trm t0 a)) as Hinit.
    destruct (proj2 (proj2 (proj2 tfree_opened_mutual)) ds 0 w t0 Hinit)
      as [Hfree | ->].
    + assert (HorigKind : ctx_k F t0 v_ref)
        by (apply HK, tfree_trm_lit_l, tfree_lit_obj, Hfree).
      destruct HorigKind as (Q & Qctx & HrefKind).
      pose proof (kind_binding_in_kind_domain HrefKind) as Href.
      rewrite HrefDom in Href. destruct (get_some Href) as [loc Hb].
      change (binds t0 loc e) in Hb.
      assert (HbP : binds t0 loc p).
      { unfold p. apply binds_push_neq; [exact Hb |].
        intros ->. apply HwF. eapply kind_domain_in_context_domain, kind_binding_in_kind_domain;
          exact HrefKind. }
      pose proof (deref_reference_binding HbP
        (renv_referent_not_key Hok' Hwk' HrefDom' Henv' HbP)) as Hmatch.
      rewrite Hmatch in Haddr. inversion Haddr; subst b.
      destruct (heap_location_info HS' HnewHeap) as [Hlocation _].
      pose proof (variable_term_typing Hmutable eq_refl) as Hmut.
      destruct (field_declaration_gives_bounds HG HS' Hlocation HyG HD Hmut) as [_ Hupper].
      right. unfold C. eapply mreach_trm with (w := t0); try eassumption.
      * left. apply tfree_trm_lit_l, tfree_lit_obj. assumption.
      * eapply HrRef; [exact Hb |]. eapply ty_var_sub; eassumption.
    + assert (HwP : binds w y p) by (unfold p; apply binds_push_eq).
      rewrite (deref_reference_binding HwP
        (renv_referent_not_key Hok' Hwk' HrefDom' Henv' HwP)) in Haddr.
      inversion Haddr; auto. }
  intros target Hreach.
  change (mut_reach typing_mode G D target) in Hreach.
  clear Hcfg'.
  remember D as C' eqn:Heq.
  remember G as G' eqn:HeqG in Hreach.
  induction Hreach as [FF tr fs en mem V y1 y2 ds0 a Hin Hpath IH Hb Hmember Hmut
                      | FF tr fs en mem V loc q Hin Hfree Hb Hmut];
    unfold D, S', p in Heq; inversion Heq; subst.
  - apply binds_push_inv in Hb as [[Heqy Heqds] | [Hy1 Hbind]].
    + inversion Heqds; subst. apply HfromNew with (a := a); assumption.
    + destruct (IH eq_refl eq_refl) as [Heqy | Hpath'].
      * contradiction.
      * right. unfold C in *. eapply mreach_fld; try eassumption.
        eapply HrFld; eassumption.
  - apply binds_push_inv in Hb as [[-> ->] | [Hq Hb]].
    + now left.
    + right. unfold C. eapply mreach_trm with (w := q); try eassumption.
      * destruct Hfree as [Hfree | Hfree]; [left | now right].
        destruct (proj1 tfree_opened_mutual t 0 w q Hfree) as [Hraw | ->].
        -- now apply tfree_trm_lit_r.
        -- contradiction.
      * eapply HrRef; [exact Hb |].
        eapply variable_term_typing; [exact Hmut | reflexivity].
Qed.

Local Definition step_uses_same_context C :=
  match C with
  | (trm_let _ _ ; _ ; _ ; _ ; _)
  | (trm_var _ ; stack_cons (frame_let _) _ ; _ ; _ ; _)
  | (trm_call _ _ _ ; _ ; _ ; _ ; _)
  | (trm_write _ _ _ ; _ ; _ ; _ ; _) => True
  | _ => False
  end.

Local Lemma same_context_step_preservation F C D T :
    execution_config F C T ->
    C ↦ D ->
    step_uses_same_context C ->
    execution_config F D T /\ (forall y, F ⊢ D mreach y -> F ⊢ C mreach y).
Proof.
  intros Hty Hstep. destruct Hstep; simpl; intros Hguard; try contradiction.
  - eapply write_step_typing_and_reachability; eassumption.
  - eapply call_step_typing_and_reachability; eassumption.
  - split.
    + now apply let_pop_preservation.
    + intros y Hy. eapply reachability_let_pop; exact Hy.
  - split.
    + now apply let_push_preservation.
    + intros y Hy. eapply reachability_let_push; exact Hy.
Qed.

Local Lemma typed_function_literal_impossible F e t T A body next :
    F ⁏ e ⊢ t ∶ T ->
    t = trm_lit (lit_fun A body) next ->
    False.
Proof.
  intros Hty. induction Hty; intros Heq; try discriminate.
  - inversion Heq; subst.
    match goal with Hfun : ?G ⁏ ?E ⊢ lit_fun A body ∶ _ |- _ =>
      inversion Hfun
    end.
    pose proof mode_disallows_functions. congruence.
  - auto.
Qed.

Local Lemma execution_step_tracks_existing_object F C D U target contents :
    execution_config F C U ->
    C ↦ D ->
    binds target (item_obj contents) (config_heap C) ->
    exists G, execution_config G D U /\
      (G ⊢ D mreach target -> F ⊢ C mreach target).
Proof.
  intros Hcfg Hstep Hbind.
  destruct (classic (step_uses_same_context C)) as [Hsame | Hfresh].
  - destruct (same_context_step_preservation Hcfg Hstep Hsame) as [Hty Hback].
    exists F. auto.
  - destruct Hstep; simpl in Hfresh; try contradiction.
    + destruct (read_step_preserves_execution Hcfg H H0 H1 H2) as (G & Hty & Hback).
      exists G. split; [exact Hty | apply Hback].
    + exfalso. eapply heap_function_impossible; [exact Hcfg | exact H].
    + exfalso. inversion Hcfg; subst.
      eapply typed_function_literal_impossible; [eassumption | reflexivity].
    + destruct (allocation_step_preservation Hcfg H H0) as [Hpost Hdef].
      eexists. split; [exact Hpost |].
      intros Hreach.
      destruct (allocation_backward_reachability Hcfg Hpost H H0 Hdef Hreach)
        as [Heq | Hprior]; [| exact Hprior].
      exfalso. exact (fresh_heap_binding H Hbind Heq).
Qed.

Local Lemma execution_trace_tracks_existing_object F C D n U y ds :
    execution_config F C U ->
    binds y (item_obj ds) (config_heap C) ->
    C ⊣ n ↦* D ->
    (binds y (item_obj ds) (config_heap D) /\
      exists G, execution_config G D U /\
        (G ⊢ D mreach y -> F ⊢ C mreach y)) \/
    F ⊢ C mreach y.
Proof.
  intros Hty Hbind Htrace.
  induction Htrace as [C | C D E k Hprefix IH Hstep].
  - left. split; [exact Hbind | exists F; auto].
  - destruct (IH Hty Hbind) as [[Hbound [G [Hkind Hprior]]] | Hreach]; [| now right].
    destruct (immutability_step Hbound Hkind Hstep) as [Hstill | Hreach].
    + destruct (execution_step_tracks_existing_object Hkind Hstep Hbound)
        as (J & Hnew & Hback).
      left. split; [exact Hstill |].
      exists J. split; [exact Hnew |].
      intros Hreach. apply Hprior, Hback, Hreach.
    + right. now apply Hprior.
Qed.

Theorem immutability_guarantee t1 s1 S1 e1 Lv1 F T n t2 s2 S2 e2 Lv2 y ds:
    binds y (item_obj ds) S1 ->
    ty_config F (t1 ; s1 ; S1 ; e1; Lv1) T ->
    (t1 ; s1 ; S1 ; e1; Lv1) ⊣ n ↦* (t2 ; s2 ; S2 ; e2; Lv2) -> (
      binds y (item_obj ds) S2 \/
      F ⊢ (t1 ; s1 ; S1 ; e1; Lv1) mreach y
    ).
Proof.
  intros Hbind Hty Htrace.
  destruct (execution_trace_tracks_existing_object
    (typed_config_supports_execution Hty) Hbind Htrace) as [[Hunchanged _] | Hreach].
  - left. exact Hunchanged.
  - right. exact Hreach.
Qed.

End WithRodotMode.
