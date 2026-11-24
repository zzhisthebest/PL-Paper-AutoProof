Set Implicit Arguments.

Require Import LibExtra.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode GeneralTyping RecordTypes InertContext OperationalSemantics HeapCorrespondence HeapUpdate EnvCorrespondence ConfigTyping ConfigVarkinds TFree Deref.

Require Import ConfigNotations Equivalence Indep.

Lemma two_fresh_config_vars C :
  exists y w, fresh_in_config (y :: w :: nil) C /\ y <> w.
Proof.
  destruct (var_freshes (fv_config C) 2) as [xs Fresh].
  destruct xs as [|y [|w [|z rest]]]; simpl in Fresh; try tauto.
  destruct Fresh as [Hy [Hw _]].
  exists y, w. split.
  - simpl. auto.
  - intros ->. apply Hw. rewrite in_union. right. apply in_singleton_self.
Qed.

Lemma tfree_opening :
  (forall v t, tfree_trm v t -> forall n x, tfree_trm v (open_rec n x t)) /\
  (forall v l, tfree_lit v l -> forall n x, tfree_lit v (open_rec n x l)) /\
  (forall v d, tfree_def v d -> forall n x, tfree_def v (open_rec n x d)) /\
  (forall v ds, tfree_defs v ds -> forall n x, tfree_defs v (open_rec n x ds)).
Proof.
  apply tfree_mutind; intros; simpl;
    eauto using tfree_trm, tfree_lit, tfree_def, tfree_defs.
Qed.

Lemma context_binding_in_domain G x T :
  ctx_binds x T G -> x \in ctx_dom G.
Proof.
  induction 1; simpl; try rewrite in_union; auto using in_singleton_self.
Qed.

Lemma variable_typing_in_domain (m : Mode) G Go e x T :
  @ty_var m G Go e x T -> x \in ctx_dom G.
Proof.
  induction 1; eauto using context_binding_in_domain.
Qed.

Lemma visibility_hide_domain (m : Mode) G :
  ctx_dom (vis_hide m G) = ctx_dom G.
Proof.
  destruct (mode_visibility' m); reflexivity.
Qed.

Lemma method_context_domain (m : Mode) G Go z TZ c TC :
  ctx_dom (ctx_obj_met m G Go z TZ c TC) =
  \{c} \u (\{z} \u ctx_dom (ctx_obj G Go)).
Proof.
  destruct Go; simpl; now rewrite visibility_hide_domain.
Qed.

Local Ltac split_core_tfree :=
  match goal with
  | H : tfree_trm _ (trm_var _) |- _ => inversion H; subst
  | H : tfree_trm _ (trm_apply _ _) |- _ => inversion H; subst
  | H : tfree_trm _ (trm_read _ _) |- _ => inversion H; subst
  | H : tfree_trm _ (trm_write _ _ _) |- _ => inversion H; subst
  | H : tfree_trm _ (trm_call _ _ _) |- _ => inversion H; subst
  end.

Lemma executable_vars_in_context (m : Mode) :
  (forall G Go e t T, @ty_trm m G Go e t T ->
    forall v, tfree_trm v t -> v \in ctx_dom G) /\
  (forall G Go e l T, @ty_lit m G Go e l T ->
    forall v, tfree_lit v l -> v \in ctx_dom G) /\
  (forall G Go e d D, @ty_def m G Go e d D ->
    forall v, tfree_def v d -> v \in ctx_dom (ctx_obj G Go)) /\
  (forall G Go e ds T, @ty_defs m G Go e ds T ->
    forall v, tfree_defs v ds -> v \in ctx_dom (ctx_obj G Go)).
Proof.
  destruct tfree_opening as [OpenTrm [OpenLit [OpenDef OpenDefs]]].
  apply rules_mutind; intros.
  all: try (split_core_tfree; eauto using variable_typing_in_domain; fail).
  all: try (solve [eauto using variable_typing_in_domain]).
  all: try match goal with
  | H : tfree_trm _ (trm_let _ _) |- _ => inversion H; subst
  | H : tfree_trm _ (trm_lit _ _) |- _ => inversion H; subst
  | H : tfree_lit _ (lit_fun _ _) |- _ => inversion H; subst
  | H : tfree_lit _ (lit_obj _ _) |- _ => inversion H; subst
  | H : tfree_def _ (def_typ _ _) |- _ => inversion H
  | H : tfree_def _ (def_fld _ _) |- _ => inversion H; subst
  | H : tfree_def _ (def_met _ _) |- _ => inversion H; subst
  | H : tfree_defs _ (defs_cons _ _) |- _ => inversion H; subst
  end.
  all: try (solve [eauto using variable_typing_in_domain]).
  all: try match goal with
  | H : tfree_defs _ defs_nil |- _ => inversion H
  end.
  1-4: destruct (var_fresh (L \u \{v})) as [w Fresh];
    rewrite notin_union in Fresh; destruct Fresh as [Fresh Neq].
  1,2: pose proof (H0 w Fresh v (OpenTrm _ _ H4 0 w)) as Dom.
  3: pose proof (H w Fresh v (OpenTrm _ _ H3 0 w)) as Dom.
  4: pose proof (H w Fresh v (OpenDefs _ _ H3 0 w)) as Dom.
  1-4: simpl in Dom; rewrite in_union in Dom; rewrite notin_singleton in Neq; rewrite in_singleton in Dom; intuition congruence.
  destruct (var_fresh (L \u \{v})) as [z Hz].
  destruct (var_fresh (L \u (\{v} \u \{z}))) as [c Hc].
  rewrite notin_union in Hz. repeat rewrite notin_union in Hc.
  destruct Hz as [HzL HzV].
  destruct Hc as [HcL [HcV HcZ]].
  assert (Hcz : c <> z).
  { intros ->. exact (HcZ (in_singleton_self z)). }
  pose proof (H z HzL c Hcz HcL v (OpenTrm _ _ (OpenTrm _ _ H3 1 c) 0 z)) as Dom.
  rewrite method_context_domain in Dom.
  rewrite !in_union in Dom.
  destruct Dom as [Vc | [Vz | Dom]].
  - rewrite in_singleton in Vc. subst v. exfalso. exact (HcV (in_singleton_self c)).
  - rewrite in_singleton in Vz. subst v. exfalso. exact (HzV (in_singleton_self z)).
  - exact Dom.
Qed.

Local Lemma initial_heap_correspondence (m : Mode) :
  @heap_correspond m ctx_empty empty empty.
Proof.
  unfold heap_correspond.
  rewrite !dom_empty. simpl.
  repeat split; try constructor.
  intros x Bound. rewrite in_empty in Bound. contradiction.
Qed.

Lemma initial_configuration_typing (m : Mode) (t : trm) (T : typ) :
  closed t -> closed T ->
  @ty_trm m ctx_empty objctx_empty empty t T ->
  exists C, config_initial t C /\ @ty_config m ctx_empty C T.
Proof.
  intros ClosedTerm ClosedType Typed.
  destruct (var_fresh (fv t \u fv T)) as [null _].
  exists (t; stack_nil; empty; empty; (\{null} \u fv t \u fv T)).
  split; [constructor|].
  apply (ty_config_c (T:=T)).
  - constructor.
  - apply initial_heap_correspondence.
  - constructor. apply subtyp_refl.
  - intros v Free. inversion Free.
  - exact Typed.
  - intros v Free. exfalso.
    destruct (executable_vars_in_context m) as [TermVars _].
    specialize (TermVars _ _ _ _ _ Typed v Free).
    simpl in TermVars. rewrite in_empty in TermVars. exact TermVars.
  - unfold nothing_fresh_in_config. simpl.
    repeat split; try apply subset_empty_l.
    intro x. repeat rewrite in_union. tauto.
  - exists null. repeat rewrite in_union. auto using in_singleton_self.
  - intros x. reflexivity.
  - constructor.
    + exact ClosedTerm.
    + intros n x. reflexivity.
    + constructor.
  - exact ClosedType.
Qed.

Local Lemma defs_has_field_update ds a value replacement :
  defs_has ds (def_fld a (avar_f value)) ->
  exists ds', defs_update ds a replacement ds'.
Proof.
  unfold defs_has. induction ds as [|ds IH d]; simpl; try discriminate.
  intros Found.
  destruct (classic (label_of d = label_fld a)) as [Same | Other].
  - rewrite If_l in Found by exact Same. injection Found as ->.
    eexists. constructor.
  - rewrite If_r in Found by exact Other.
    destruct (IH Found) as [ds' Updated].
    eexists. eapply defs_update_push; eassumption.
Qed.

Local Lemma heap_replace_object (s : heap) x ds ds' :
  ok s -> binds x (item_obj ds) s ->
  exists s', ok s' /\ dom s' = dom s /\ binds x (item_obj ds') s' /\
    (forall z v, z <> x -> binds z v s -> binds z v s').
Proof.
  induction s as [|s k old IH] using env_ind; intros Ok Bound.
  { exfalso. eapply binds_empty_inv; eassumption. }
  destruct (binds_push_inv Bound) as [[Eq EqItem] | [Other InPrefix]].
  - subst x old. exists (s & k ~ item_obj ds').
    destruct (ok_push_inv Ok) as [OkPrefix Fresh].
    repeat split.
    + auto using ok_push.
    + now rewrite !dom_concat, !dom_single.
    + apply binds_push_eq.
    + intros z v Distinct Old.
      apply binds_push_neq; [|assumption].
      destruct (binds_push_inv Old) as [[? ?] | [? ?]]; congruence.
  - destruct (ok_push_inv Ok) as [OkPrefix Fresh].
    destruct (IH OkPrefix InPrefix) as [s' [Ok' [Dom [Updated Others]]]].
    exists (s' & k ~ old).
    repeat split.
    + apply ok_push; [assumption|now rewrite Dom].
    + now rewrite !dom_concat, Dom.
    + now apply binds_push_neq.
    + intros z v Distinct Old.
      destruct (binds_push_inv Old) as [[-> ->] | [Neq Prefix]].
      * apply binds_push_eq.
      * apply binds_push_neq; auto.
Qed.

Local Lemma heap_update_exists (s : heap) x ds a value replacement :
  ok s -> binds x (item_obj ds) s ->
  defs_has ds (def_fld a (avar_f value)) ->
  exists s', heap_update s x a replacement s'.
Proof.
  intros Ok Bound Found.
  destruct (defs_has_field_update replacement Found) as [ds' Updated].
  destruct (heap_replace_object ds' Ok Bound) as [s' [Ok' [Dom [New Others]]]].
  exists s'. repeat split; auto.
  exists ds, ds'. auto.
Qed.

Local Lemma context_kind_in_kind_domain G x vk T G' :
  ctx_binds_k_after x vk T G G' -> x \in ctx_kdom vk G.
Proof.
  induction 1; simpl.
  - rewrite If_l by reflexivity.
    rewrite in_union. left. apply in_singleton_self.
  - destruct (classic (vk1 = vk2)) as [Eq | Neq].
    + rewrite If_l by exact Eq. rewrite in_union. auto.
    + now rewrite If_r by exact Neq.
Qed.

Local Lemma runtime_reference (e : renv) G x :
  ctx_kdom v_ref G = dom e -> ctx_k G x v_ref ->
  exists y, binds x y e.
Proof.
  intros Dom [T [G' Bound]].
  pose proof (context_kind_in_kind_domain Bound) as Present.
  rewrite Dom in Present.
  destruct (get x e) as [y|] eqn:Lookup.
  - exists y. exact Lookup.
  - exfalso. now apply (get_none_inv Lookup).
Qed.

Definition runtime_canonical_forms (m : Mode) G (e : renv) (s : heap) :=
  (forall x S T, @ty_var m G objctx_empty e x (typ_fun S T) ->
    ctx_k G x v_ref -> exists y body, binds x y e /\ binds y (item_fun body) s) /\
  (forall x a S T, @ty_var m G objctx_empty e x (typ_rcd (dec_fld a S T)) ->
    ctx_k G x v_ref -> exists y ds z,
      binds x y e /\ binds y (item_obj ds) s /\ defs_has ds (def_fld a (avar_f z))) /\
  (forall x a TC TZ TR, @ty_var m G objctx_empty e x (typ_rcd (dec_met a TC TZ TR)) ->
    ctx_k G x v_ref -> exists y ds body,
      binds x y e /\ binds y (item_obj ds) s /\ defs_has ds (def_met a body)).

Section ProgressFromForms.
Context (m : Mode).

Local Lemma term_progress_from_canonical_forms G Go e t T :
  @ty_trm m G Go e t T ->
  forall s fs Lv,
  ok s -> ctx_kdom v_ref G = dom e ->
  runtime_canonical_forms m G e s ->
  all_tfree_k G t v_ref ->
  answer (t; fs; s; e; Lv) \/ exists C', (t; fs; s; e; Lv) ↦ C'.
Proof.
  intros Typed. induction Typed; intros s fs Lv Ok RefDom Forms Free.
  - destruct fs as [|f fs].
    + left. constructor.
    + destruct f. right. eexists. apply red_let_var.
  - destruct Forms as [Fun _]. destruct (Fun x S T H2 (Free x (tfree_trm_apply_l x (avar_f z)))) as [loc [body [Ref Item]]].
    right. eexists. eapply red_apply; eassumption.
  - destruct Forms as [_ [Field _]]. destruct (Field x a S T H0 (Free x (tfree_trm_read x a))) as [loc [ds [ptr [Ref [Item Found]]]]].
    destruct (var_fresh (fv_config (trm_read (avar_f x) a; fs; s; e; Lv))) as [w Fresh].
    right. eexists. eapply red_read with (wVal:=w); try eassumption.
    simpl. auto.
  - destruct Forms as [_ [Field _]]. destruct (Field x a S T H2 (Free x (tfree_trm_write_l x (avar_f y) a))) as [loc [ds [ptr [Ref [Item Found]]]]].
    destruct (runtime_reference RefDom (Free y ltac:(apply tfree_trm_write_r))) as [z Arg].
    destruct (heap_update_exists z Ok Item Found) as [s' Updated].
    right. eexists. eapply red_write; eassumption.
  - destruct Forms as [_ [_ Method]]. destruct (Method x m0 TC TZ TR H1 (Free x (tfree_trm_call_l x (avar_f y) m0))) as [loc [ds [body [Ref [Item Found]]]]].
    right. eexists. eapply red_call; eassumption.
  - right. eexists. apply red_let_push.
  - destruct (two_fresh_config_vars (trm_lit l u; fs; s; e; Lv))
      as [y [w [Fresh Distinct]]].
    right. destruct l.
    + eexists. apply red_let_fun; eauto.
    + eexists. apply red_let_obj; eauto.
  - eauto.
Qed.

End ProgressFromForms.

Lemma type_equiv_symmetric e S T :
  tyq_typ e S T -> tyq_typ e T S.
Proof.
  induction 1.
  - apply tyq_typ_nulary; assumption.
  - apply tyq_typ_andor; assumption.
  - apply tyq_typ_fun; assumption.
  - apply tyq_typ_fld; assumption.
  - apply tyq_typ_typ; assumption.
  - apply tyq_typ_sel_normal, tyq_var_sym; assumption.
  - apply tyq_typ_sel.
  - apply tyq_typ_bnd; assumption.
  - apply tyq_typ_met; assumption.
Qed.

Module ShapeInterpretation.
Section Model.
Context (m : Mode) (base : ctx) (e : renv).
Context (member : var -> typ_normal_label -> typ -> Prop).
Context (has_fun : var -> typ -> typ -> Prop).
Context (has_field : var -> fld_label -> typ -> Prop).
Context (has_method : var -> met_label -> typ -> typ -> typ -> Prop).
Hypothesis member_unique : forall x a U V, member x a U -> member x a V -> U = V.
Hypothesis member_alias : forall x y a U, tyq_var e x y -> member x a U -> member y a U.

Inductive function_cast : typ -> typ -> typ -> typ -> Prop :=
| function_cast_refl A B : function_cast A B A B
| function_cast_compose A B C D E F :
    function_cast A B C D -> function_cast C D E F -> function_cast A B E F
| function_cast_variance L A B C D :
    mode_has_fun' m = true ->
    @subtyp m base objctx_empty e C A ->
    (forall z, z \notin L ->
      @subtyp m (base § z / v_par ~ C) objctx_empty e (open z B) (open z D)) ->
    function_cast A B C D
| function_cast_equivalence A B C D :
    tyq_typ e A C -> (forall z, tyq_typ e (open z B) (open z D)) ->
    function_cast A B C D.

Inductive method_cast : typ -> typ -> typ -> typ -> typ -> typ -> Prop :=
| method_cast_refl C Z R : method_cast C Z R C Z R
| method_cast_compose C1 Z1 R1 C2 Z2 R2 C3 Z3 R3 :
    method_cast C1 Z1 R1 C2 Z2 R2 ->
    method_cast C2 Z2 R2 C3 Z3 R3 ->
    method_cast C1 Z1 R1 C3 Z3 R3
| method_cast_variance L C1 Z1 R1 C2 Z2 R2 :
    @subtyp m base objctx_empty e Z2 Z1 ->
    (forall z, z \notin L ->
      @subtyp m (base § z / v_par ~ Z2) objctx_empty e (open z C2) (open z C1)) ->
    (mode_sef' m = mode_sef_guarantee -> typ_indep_b 0 C2 -> typ_indep_b 0 C1) ->
    (forall z, z \notin L -> forall r, r <> z -> r \notin L ->
      @subtyp m (ctx_met base z Z2 r C2) objctx_empty e (open_met z r R1) (open_met z r R2)) ->
    method_cast C1 Z1 R1 C2 Z2 R2
| method_cast_equivalence C1 Z1 R1 C2 Z2 R2 :
    (forall z, tyq_typ e (open z C1) (open z C2)) ->
    tyq_typ e Z1 Z2 ->
    (forall z r, tyq_typ e (open_met z r R1) (open_met z r R2)) ->
    method_cast C1 Z1 R1 C2 Z2 R2.

Lemma function_cast_sound A B C D :
  function_cast A B C D ->
  @subtyp m base objctx_empty e (typ_fun A B) (typ_fun C D).
Proof.
  induction 1.
  - apply subtyp_refl.
  - eapply subtyp_trans; eassumption.
  - eapply subtyp_fun with (L:=L); eassumption.
  - apply subtyp_tyq, tyq_typ_fun; assumption.
Qed.

Lemma method_cast_sound a C1 Z1 R1 C2 Z2 R2 :
  method_cast C1 Z1 R1 C2 Z2 R2 ->
  @subtyp m base objctx_empty e (typ_rcd (dec_met a C1 Z1 R1)) (typ_rcd (dec_met a C2 Z2 R2)).
Proof.
  induction 1.
  - apply subtyp_refl.
  - eapply subtyp_trans; eassumption.
  - eapply subtyp_met with (L:=L); eassumption.
  - apply subtyp_tyq, tyq_typ_met; assumption.
Qed.

Inductive shape_sub : typ -> typ -> Prop :=
| shape_refl T : shape_sub T T
| shape_trans S T U : shape_sub S T -> shape_sub T U -> shape_sub S U
| shape_top T : shape_sub T typ_top
| shape_bot T : shape_sub typ_bot T
| shape_and_l T U : shape_sub (typ_and T U) T
| shape_and_r T U : shape_sub (typ_and T U) U
| shape_and_intro S T U :
    shape_sub S T -> shape_sub S U -> shape_sub S (typ_and T U)
| shape_or_l T U : shape_sub T (typ_or T U)
| shape_or_r T U : shape_sub U (typ_or T U)
| shape_or_elim S T U :
    shape_sub S U -> shape_sub T U -> shape_sub (typ_or S T) U
| shape_dist S T U :
    shape_sub (typ_and S (typ_or T U))
      (typ_or (typ_and S T) (typ_and S U))
| shape_fld a S T U V :
    shape_sub U S -> shape_sub T V ->
    shape_sub (typ_rcd (dec_fld a S T)) (typ_rcd (dec_fld a U V))
| shape_met a TC TZ TR UC UZ UR :
    method_cast TC TZ TR UC UZ UR ->
    shape_sub (typ_rcd (dec_met a TC TZ TR)) (typ_rcd (dec_met a UC UZ UR))
| shape_fun S T U V : function_cast S T U V ->
    shape_sub (typ_fun S T) (typ_fun U V)
| shape_typ a S T U V :
    (forall x, shape_sub (open x U) (open x S)) ->
    (forall x, shape_sub (open x T) (open x V)) ->
    shape_sub (typ_rcd (dec_typ a S T)) (typ_rcd (dec_typ a U V))
| shape_typ_and a S T U V :
    shape_sub (typ_and (typ_rcd (dec_typ a S T)) (typ_rcd (dec_typ a U V)))
      (typ_rcd (dec_typ a (typ_or S U) (typ_and T V)))
| shape_eq S T : tyq_typ e S T -> shape_sub S T
| shape_member_lower x a U y :
    member x a U ->
    shape_sub (open y U) (typ_sel (avar_f x) (typ_label_normal a) (avar_f y))
| shape_member_upper x a U y :
    member x a U ->
    shape_sub (typ_sel (avar_f x) (typ_label_normal a) (avar_f y)) (open y U)
| shape_cap_lower x c y T :
    shape_sub T typ_bot -> shape_sub T (typ_sel (avar_f x) (typ_label_refcap c) (avar_f y))
| shape_cap_upper x c y T :
    @subtyp m base objctx_empty e (typ_sel (avar_f x) (typ_label_refcap c) (avar_f y)) T ->
    shape_sub (typ_sel (avar_f x) (typ_label_refcap c) (avar_f y)) T
| shape_nocap_bnd T : shape_sub typ_nocap (typ_bnd T)
| shape_nocap_typ a S T : shape_sub typ_nocap (typ_rcd (dec_typ (typ_label_normal a) S T))
| shape_nocap_fld a S T : shape_sub typ_nocap (typ_rcd (dec_fld a S T))
| shape_nocap_met a TC TZ TR : shape_sub typ_nocap (typ_rcd (dec_met a TC TZ TR))
| shape_nocap_fun S T : mode_has_fun' m = true -> shape_sub typ_nocap (typ_fun S T)
| shape_boundless S T :
    mode_top_nm' m = mode_top_nm_subtype ->
    shape_sub typ_top (typ_or typ_nocap (typ_rcd (dec_typ typ_label_mutability S T)))
| shape_complement :
    mode_top_nm' m = mode_top_nm_complement ->
    shape_sub typ_top (typ_or typ_nocap (typ_mut_marker typ_bot))
| shape_exclusive :
    mode_top_nm' m = mode_top_nm_complement ->
    shape_sub (typ_and typ_nocap (typ_mut_marker typ_bot)) typ_bot
| shape_mut_top : mode_mut_top' m = mode_mut_top_subtype -> shape_sub typ_top (typ_mut_marker typ_top).

(* This test tracks capability lower bounds separately from the shapes of
   concrete values. The boundless rule can satisfy it through its nocap arm. *)
Inductive bound_test : typ -> Prop :=
| test_top : bound_test typ_top
| test_nocap : mode_top_nm' m = mode_top_nm_subtype -> bound_test typ_nocap
| test_and T U : bound_test T -> bound_test U -> bound_test (typ_and T U)
| test_or_l T U : bound_test T -> bound_test (typ_or T U)
| test_or_r T U : bound_test U -> bound_test (typ_or T U)
| test_bnd T : bound_test (typ_bnd T)
| test_fun S T : bound_test (typ_fun S T)
| test_fld a S T : bound_test (typ_rcd (dec_fld a S T))
| test_met a TC TZ TR : bound_test (typ_rcd (dec_met a TC TZ TR))
| test_typ a S T : bound_test (typ_rcd (dec_typ (typ_label_normal a) S T))
| test_cap c S T :
    (forall y, shape_sub (open y S) typ_bot) -> bound_test (typ_rcd (dec_typ (typ_label_refcap c) S T))
| test_member x a U y :
    member x a U -> bound_test (open y U) ->
    bound_test (typ_sel (avar_f x) (typ_label_normal a) (avar_f y)).

Inductive value_shape (x : var) : typ -> Prop :=
| value_top : value_shape x typ_top
| value_and T U : value_shape x T -> value_shape x U -> value_shape x (typ_and T U)
| value_or_l T U : value_shape x T -> value_shape x (typ_or T U)
| value_or_r T U : value_shape x U -> value_shape x (typ_or T U)
| value_bnd T : value_shape x (open x T) -> bound_test (open x T) -> value_shape x (typ_bnd T)
| value_fun S T A B : has_fun x A B -> function_cast A B S T ->
    value_shape x (typ_fun S T)
| value_fld a S T U : has_field x a U -> shape_sub S U -> shape_sub U T ->
    value_shape x (typ_rcd (dec_fld a S T))
| value_met a TC TZ TR C Z R : has_method x a C Z R -> method_cast C Z R TC TZ TR ->
    value_shape x (typ_rcd (dec_met a TC TZ TR))
| value_typ a S T U :
    member x a U ->
    (forall v, shape_sub (open v S) (open v U)) ->
    (forall v, shape_sub (open v U) (open v T)) ->
    value_shape x (typ_rcd (dec_typ (typ_label_normal a) S T))
| value_cap c S T : value_shape x (typ_rcd (dec_typ (typ_label_refcap c) S T))
| value_member z a U y :
    member z a U -> value_shape x (open y U) ->
    value_shape x (typ_sel (avar_f z) (typ_label_normal a) (avar_f y)).

Local Hint Constructors bound_test value_shape : shapes.
Local Hint Constructors shape_sub : subshapes.

Lemma bound_test_equiv S T :
  tyq_typ e S T -> bound_test S -> bound_test T.
Proof.
  intros Equiv. remember e as e' in Equiv.
  induction Equiv; intros Test; subst; try assumption.
  - inversion H; subst; inversion Test; subst; eauto with shapes.
  - eauto with shapes.
  - eauto with shapes.
  - destruct B; inversion Test; subst.
    + constructor.
    + apply test_cap. intros y.
      eapply shape_trans with (T:=open y t11); [apply shape_eq, type_equiv_symmetric, H|auto].
  - inversion Test; subst. eapply test_member; eauto.
  - eauto with shapes.
  - eauto with shapes.
Qed.

Lemma value_shape_equiv x S T :
  tyq_typ e S T -> value_shape x S -> value_shape x T.
Proof.
  intros Equiv. remember e as e' in Equiv.
  induction Equiv; intros Shape; subst; try assumption.
  - inversion H; subst; inversion Shape; subst; eauto with shapes.
  - inversion Shape; subst. eapply value_fun; [eassumption|].
    eapply function_cast_compose; [eassumption|]. apply function_cast_equivalence; assumption.
  - inversion Shape; subst.
    eapply value_fld; [eassumption| |].
    + eapply shape_trans with (T:=t11); [apply shape_eq, type_equiv_symmetric; assumption|assumption].
    + eapply shape_trans with (T:=t12); [assumption|apply shape_eq; assumption].
  - destruct B as [a|c]; inversion Shape; subst.
    + eapply value_typ; [eassumption| |].
      * intros v. eapply shape_trans with (T:=open v t11); [apply shape_eq, type_equiv_symmetric, H|auto].
      * intros v. eapply shape_trans with (T:=open v t12); [auto|apply shape_eq, H1].
    + constructor.
  - inversion Shape; subst. eapply value_member; eauto.
  - inversion Shape; subst. apply value_bnd; [apply H0; auto|eapply bound_test_equiv; [apply H|eassumption]].
  - inversion Shape; subst. eapply value_met; [eassumption|].
    eapply method_cast_compose; [eassumption|]. apply method_cast_equivalence; assumption.
Qed.

Local Ltac invert_union :=
  match goal with
  | H : bound_test (typ_or _ _) |- _ => inversion H; subst
  | H : value_shape _ (typ_or _ _) |- _ => inversion H; subst
  end.

Local Ltac same_member :=
  match goal with
  | H1 : member ?x ?a ?U, H2 : member ?x ?a ?V |- _ =>
    first [constr_eq U V; fail 1 | let Eq := fresh in
      assert (Eq : U = V) by (eapply member_unique; [exact H1|exact H2]); subst V]
  end.

Lemma bound_test_sub S T :
  shape_sub S T -> bound_test S -> bound_test T.
Proof.
  induction 1; intros Test; try solve [eauto with shapes].
  - inversion Test.
  - inversion Test; assumption.
  - inversion Test; assumption.
  - invert_union; auto.
  - inversion Test; subst. invert_union; eauto with shapes.
  - destruct a; inversion Test; subst.
    + constructor.
    + apply test_cap. intros y. eapply shape_trans; eauto.
  - inversion Test; subst. destruct a.
    + constructor.
    + apply test_cap. intros y. change (shape_sub (typ_or (open y S) (open y U)) typ_bot).
      apply shape_or_elim; match goal with
      | H : bound_test (typ_rcd (dec_typ (typ_label_refcap _) _ _)) |- _ =>
        solve [inversion H; subst; auto]
      end.
  - eauto using bound_test_equiv.
  - inversion Test; subst; same_member; assumption.
  - exfalso. specialize (IHshape_sub Test). inversion IHshape_sub.
  - inversion Test.
  - apply test_or_r, test_cap. intros y. exact (shape_refl typ_bot).
  - inversion Test; subst.
    match goal with
    | H : bound_test typ_nocap |- _ => inversion H; congruence
    end.
  - apply test_cap. intros y. exact (shape_refl typ_bot).
Qed.

Lemma value_shape_sub x S T :
  shape_sub S T -> value_shape x S -> value_shape x T.
Proof.
  induction 1; intros Test; try solve [eauto with shapes].
  - inversion Test.
  - inversion Test; assumption.
  - inversion Test; assumption.
  - invert_union; auto.
  - inversion Test; subst. invert_union; eauto with shapes.
  - inversion Test; subst. eapply value_fld; [eassumption| |].
    + eapply shape_trans with (T:=S); eassumption.
    + eapply shape_trans with (T:=T); eassumption.
  - inversion Test; subst. eapply value_met; [eassumption|].
    eapply method_cast_compose; eassumption.
  - inversion Test; subst. eapply value_fun; [eassumption|].
    eapply function_cast_compose; eassumption.
  - destruct a; inversion Test; subst.
    + eapply value_typ; [eassumption| |]; intros y; eapply shape_trans; eauto.
    + constructor.
  - inversion Test; subst. destruct a; [|constructor].
    match goal with
    | H1 : value_shape _ (typ_rcd (dec_typ _ S T)),
      H2 : value_shape _ (typ_rcd (dec_typ _ U V)) |- _ =>
      inversion H1; inversion H2; subst
    end.
    try same_member.
    eapply value_typ; [eassumption| |].
    + intros y. change (shape_sub (typ_or (open y S) (open y U)) (open y U0)).
      apply shape_or_elim; auto.
    + intros y. change (shape_sub (open y U0) (typ_and (open y T) (open y V))).
      apply shape_and_intro; auto.
  - eauto using value_shape_equiv.
  - inversion Test; subst; same_member; assumption.
  - exfalso. specialize (IHshape_sub Test). inversion IHshape_sub.
  - inversion Test.
  - inversion Test.
  - inversion Test.
  - inversion Test.
  - inversion Test.
  - inversion Test.
  - inversion Test; subst.
    match goal with H : value_shape _ typ_nocap |- _ => inversion H end.
Qed.

Lemma typing_implies_shape :
  (forall G Go e' x T, @ty_var m G Go e' x T ->
    e' = e -> G = base ->
    (forall v U, ctx_binds v U G -> value_shape v U /\ bound_test U) ->
    value_shape x T /\ bound_test T) /\
  (forall G Go e' S T, @subtyp m G Go e' S T ->
    e' = e -> G = base ->
    (forall v U, ctx_binds v U G -> value_shape v U /\ bound_test U) ->
    shape_sub S T) /\
  (forall G Go e' S T, @ty_incap m G Go e' S T -> True).
Proof.
  apply ts_mutind; simpl; intros; subst; try exact I.
  all: repeat match goal with
  | H : e = e -> base = base -> ?Valid -> _, Hv : ?Valid |- _ =>
      specialize (H eq_refl eq_refl Hv)
  | H : value_shape _ _ /\ bound_test _ |- _ =>
      destruct H
  end.
  all: try solve [eauto 3 with shapes subshapes].
  - match goal with
    | HS : value_shape _ (typ_bnd _) |- _ => inversion HS; auto
    end.
  - split; constructor; assumption.
  - split; [eapply value_shape_sub|eapply bound_test_sub]; eassumption.
  - apply shape_typ; intros; eauto.
  - destruct A.
    + match goal with
      | HS : value_shape _ (typ_rcd (dec_typ _ _ _)) |- _ =>
        inversion HS; subst
      end.
      match goal with
      | Member : member x _ ?Anchor |- _ =>
         eapply shape_trans with (T:=open y Anchor);
           [auto|apply shape_member_lower; exact Member]
      end.
    + match goal with
      | HB : bound_test (typ_rcd (dec_typ _ _ _)) |- _ => inversion HB; subst
      end.
      apply shape_cap_lower. auto.
  - destruct A.
    + match goal with
      | HS : value_shape _ (typ_rcd (dec_typ _ _ _)) |- _ =>
        inversion HS; subst
      end.
      match goal with
      | Member : member x _ ?Anchor |- _ =>
         eapply shape_trans with (T:=open y Anchor);
           [apply shape_member_upper; exact Member|auto]
      end.
    + apply shape_cap_upper. eapply subtyp_sel1; eassumption.
  - apply shape_fun. eapply function_cast_variance with (L:=L); eassumption.
  - apply shape_met. eapply method_cast_variance with (L:=L); eassumption.
Qed.
Lemma shape_sub_sound
  (member_typed : forall x a U, member x a U ->
    @ty_var m base objctx_empty e x (typ_rcd (dec_typ (typ_label_normal a) U U))) S T :
  shape_sub S T -> @subtyp m base objctx_empty e S T.
Proof.
  induction 1.
  - apply subtyp_refl.
  - eapply subtyp_trans with (T:=T); assumption.
  - apply subtyp_top.
  - apply subtyp_bot.
  - apply subtyp_and11.
  - apply subtyp_and12.
  - apply subtyp_and2; assumption.
  - apply subtyp_or11.
  - apply subtyp_or12.
  - apply subtyp_or2; assumption.
  - apply subtyp_dist.
  - apply subtyp_fld; assumption.
  - now apply method_cast_sound.
  - now apply function_cast_sound.
  - apply subtyp_typ; assumption.
  - apply subtyp_typ_and.
  - apply subtyp_tyq; assumption.
  - eapply subtyp_sel2. now apply member_typed.
  - eapply subtyp_sel1. now apply member_typed.
  - eapply subtyp_trans with (T:=typ_bot); [assumption|apply subtyp_bot].
  - assumption.
  - apply subtyp_nocap_bnd.
  - apply subtyp_nocap_typ.
  - apply subtyp_nocap_fld.
  - apply subtyp_nocap_met.
  - now apply subtyp_nocap_fun.
  - now apply subtyp_nocap_mut_top_boundless.
  - now apply subtyp_nocap_mut_top_complement.
  - now apply subtyp_nocap_mut_bot.
  - now apply subtyp_mut_top.
Qed.
End Model.
End ShapeInterpretation.

Local Lemma ctx_kind_binds G G' x k T :
  ctx_binds_k_after x k T G G' -> ctx_binds x T G.
Proof. induction 1; eauto using ctx_binds. Qed.

Local Lemma ctx_bind_unique G x S T :
  ctx_binds x S G -> ctx_binds x T G -> S = T.
Proof.
  intros H. revert T. induction H; intros U Other; inversion Other; subst; eauto; congruence.
Qed.

Local Lemma ctx_kind_unique G G1 G2 x k1 k2 T1 T2 :
  ctx_binds_k_after x k1 T1 G G1 -> ctx_binds_k_after x k2 T2 G G2 -> k1 = k2.
Proof.
  intros H. revert G2 k2 T2. induction H; intros G' k U Other;
    inversion Other; subst; eauto; congruence.
Qed.

Local Lemma inert_context_lookup (m : Mode) G x T :
  @inert m G -> ctx_binds x T G ->
  exists k G', inert_vk k /\ @inert_typ m T k /\ ctx_binds_k_after x k T G G'.
Proof.
  intros Inert. induction Inert; intros Bound; inversion Bound; subst.
  - eexists _, _. split; [eassumption|]. split; [eassumption|constructor].
  - match goal with
    | H : ctx_binds _ _ _ |- _ =>
      destruct (IHInert H) as [k [G' [Kind [Type' Before]]]]
    end.
    exists k, G'. auto using ctx_binds_k_after.
Qed.

Local Lemma inert_kind_lift (m : Mode) G G' G'' x y k1 k2 S T :
  ctx_binds_k_after y k2 T G G' ->
  @inert m G -> ctx_binds_k_after x k1 S G' G'' ->
  ctx_binds_k_after x k1 S G G''.
Proof.
  intros After. induction After; intros Inert Bound; inversion Inert; subst.
  - apply ctx_binds_k_n; [|assumption].
    intro Eq. subst v. eauto using context_binding_in_domain, ctx_kind_binds.
  - apply ctx_binds_k_n.
    + intro Eq. subst v2.
      match goal with H : _ \notin ctx_dom _ |- _ => apply H end.
      eauto using context_binding_in_domain, ctx_kind_binds.
    + auto.
Qed.

Local Lemma corresponding_reference (m : Mode) G e x y :
  @inert m G -> @renv_corr m G e -> binds x y e ->
  exists X Y P Q, ctx_binds_k_after x v_ref X G P /\
    ctx_binds_k_after y v_loc Y G Q /\ @typ_corr m X Y.
Proof.
  intros Inert Corr. induction Corr; intros Bound.
  - exfalso. eapply binds_empty_inv; eassumption.
  - destruct (binds_push_inv Bound) as [[Eqx Eqy] | [_ Prefix]].
    + subst x y. exists Tw, Ty, G2, G3. repeat split; try assumption.
      eapply inert_kind_lift; eassumption.
    + exact (IHCorr Inert Prefix).
Qed.

Local Definition location_of (e : renv) (x : var) : var :=
  match get x e with
  | Some y => y
  | None => x
  end.

Local Lemma location_of_binding e x y :
  binds x y e -> location_of e x = y.
Proof. unfold binds, location_of. now intros ->. Qed.

Local Lemma location_of_location (m : Mode) G e x T P :
  @inert m G -> @renv_corr m G e ->
  ctx_binds_k_after x v_loc T G P -> location_of e x = x.
Proof.
  intros Inert Corr Bound. unfold location_of.
  destruct (get x e) as [y|] eqn:Lookup; [|reflexivity].
  destruct (corresponding_reference Inert Corr Lookup) as [X [Y [P' [Q [Ref _]]]]].
  pose proof (ctx_kind_unique Bound Ref). discriminate.
Qed.

Local Lemma location_of_equiv (m : Mode) G e x y :
  @inert m G -> @renv_corr m G e -> tyq_var e x y ->
  location_of e x = location_of e y.
Proof.
  intros Inert Corr Equiv. induction Equiv.
  - reflexivity.
  - match goal with Bound : binds _ _ _ |- _ =>
      rewrite (location_of_binding Bound);
      destruct (corresponding_reference Inert Corr Bound)
        as [X [Y [P [Q [_ [Loc _]]]]]]
    end.
    symmetry. eapply location_of_location; eassumption.
  - symmetry. auto.
  - rewrite (IHEquiv Corr). exact (IHEquiv0 Corr).
Qed.

Local Lemma location_of_context_binding (m : Mode) G (e : renv) x X :
  @inert m G -> @renv_corr m G e ->
  ctx_kdom v_ref G = dom e -> ctx_binds x X G ->
  exists Y Q, ctx_binds_k_after (location_of e x) v_loc Y G Q /\
    (X = Y \/ @typ_corr m X Y) /\ tyq_var e x (location_of e x).
Proof.
  intros Inert Corr RefDom Bound.
  destruct (inert_context_lookup Inert Bound) as [k [P [Kind [_ KBound]]]].
  destruct Kind.
  - rewrite (location_of_location Inert Corr KBound).
    exists X, P. split; [exact KBound|]. split; [now left|apply tyq_var_refl].
  - destruct (runtime_reference RefDom ltac:(exists X, P; exact KBound)) as [y Lookup].
    rewrite (location_of_binding Lookup).
    destruct (corresponding_reference Inert Corr Lookup)
      as [X' [Y [P' [Q [Ref [Loc CTypes]]]]]].
    assert (X = X') by (eapply ctx_bind_unique; [exact Bound|eapply ctx_kind_binds; exact Ref]).
    subst X'. exists Y, Q. split; [exact Loc|]. split; [now right|now apply tyq_var_binds].
Qed.

Local Lemma distinct_open_avar (v : avar) n k x y :
  n <> k -> open_rec n x (open_rec k y v) = open_rec k y (open_rec n x v).
Proof.
  intros Neq. destruct v; cbn.
  - destruct (classic (k = n0)) as [Eqk | Nek];
    destruct (classic (n = n0)) as [Eqn | Nen]; try congruence.
    + rewrite (If_l _ _ Eqk), (If_r _ _ Nen). cbn. now rewrite (If_l _ _ Eqk).
    + rewrite (If_r _ _ Nek), (If_l _ _ Eqn). cbn. now rewrite (If_l _ _ Eqn).
    + rewrite (If_r _ _ Nek), (If_r _ _ Nen).
      cbn. now rewrite (If_r _ _ Nek), (If_r _ _ Nen).
  - reflexivity.
Qed.

Local Lemma distinct_open_types :
  (forall (T : typ) n k x y, n <> k -> open_rec n x (open_rec k y T) = open_rec k y (open_rec n x T)) /\
  (forall (D : dec) n k x y, n <> k -> open_rec n x (open_rec k y D) = open_rec k y (open_rec n x D)).
Proof.
  apply typ_mutind; intros; cbn; f_equal; eauto using distinct_open_avar; try congruence.
Qed.

Local Lemma open_avar_unaffected (v : avar) n x :
  avar_b n <> v -> open_rec n x v = v.
Proof. intros Neq. destruct v; cbn; [rewrite If_r by congruence|]; reflexivity. Qed.

Local Lemma type_equiv_open e S T :
  tyq_typ e S T -> forall n x, tyq_typ e (open_rec n x S) (open_rec n x T).
Proof.
  destruct distinct_open_types as [Comm _].
  intros Eq. induction Eq; intros n x; cbn.
  - inversion H; subst; apply tyq_typ_nulary; constructor.
  - inversion H; subst; cbn.
    + eapply (tyq_typ_andor (T:=typ_and)); [constructor|apply IHEq|apply IHEq0].
    + eapply (tyq_typ_andor (T:=typ_or)); [constructor|apply IHEq|apply IHEq0].
  - apply tyq_typ_fun.
    + apply IHEq.
    + intros v. rewrite !(Comm _ 0 (S n) v x) by discriminate. apply H1.
  - apply tyq_typ_fld; [apply IHEq|apply IHEq0].
  - apply tyq_typ_typ; intros v; rewrite !(Comm _ 0 (S n) v x) by discriminate;
      [apply H0|apply H2].
  - apply tyq_typ_sel_normal. assumption.
  - apply tyq_typ_sel.
  - apply tyq_typ_bnd. intros v. rewrite !(Comm _ 0 (S n) v x) by discriminate. apply H0.
  - apply tyq_typ_met.
    + intros v. rewrite !(Comm _ 0 (S n) v x) by discriminate. apply H0.
    + apply IHEq.
    + intros v u. rewrite !(Comm _ 1 (S (S n)) u x) by discriminate.
      rewrite !(Comm _ 0 (S (S n)) v x) by discriminate. apply H3.
Qed.

Local Lemma independent_open_equiv e x y T n :
  tyq_var e x y -> typ_indep_b n T ->
  tyq_typ e (open_rec n x T) (open_rec n y T).
Proof.
  intros Eq Indep.
  remember (avar_b n) as w eqn:Index in Indep.
  revert n Index.
  induction Indep; intros k Index; try discriminate;
    try (injection Index as EqIndex; subst k); try subst v; cbn.
  - inversion H; subst; apply tyq_typ_nulary; constructor.
  - apply tyq_typ_andor; [constructor|apply IHIndep1; reflexivity|apply IHIndep2; reflexivity].
  - apply tyq_typ_andor; [constructor|apply IHIndep1; reflexivity|apply IHIndep2; reflexivity].
  - apply tyq_typ_fld; [apply IHIndep1|apply IHIndep2]; reflexivity.
  - apply tyq_typ_typ; intros v; apply type_equiv_open;
      [apply IHIndep1|apply IHIndep2]; reflexivity.
  - apply tyq_typ_fun.
    + apply IHIndep1; reflexivity.
    + intros v. apply type_equiv_open, IHIndep2; reflexivity.
  - change (tyq_typ e (typ_sel (open_rec k x v1) l (open_rec k x v2))
                     (typ_sel (open_rec k y v1) l (open_rec k y v2))).
    repeat rewrite open_avar_unaffected by assumption. apply tyq_typ_sel.
  - change (tyq_typ e (typ_sel (open_rec k x v1) (typ_label_normal l) (open_rec k x v2))
                     (typ_sel (open_rec k y v1) (typ_label_normal l) (open_rec k y v2))).
    rewrite (open_avar_unaffected x H), (open_avar_unaffected y H).
    destruct (classic (v1 = avar_b k)) as [-> | Neq].
    + cbn. rewrite !If_l by reflexivity. now apply tyq_typ_sel_normal.
    + repeat rewrite open_avar_unaffected by congruence. apply tyq_typ_sel.
  - apply tyq_typ_bnd; intros v. apply type_equiv_open, IHIndep; reflexivity.
  - apply tyq_typ_met.
    + intros v. apply type_equiv_open, IHIndep1; reflexivity.
    + apply IHIndep2; reflexivity.
    + intros v u. apply type_equiv_open, type_equiv_open, IHIndep3; reflexivity.
Qed.

Local Lemma record_has_single D D' :
  record_has (typ_rcd D) D' -> D = D'.
Proof. inversion 1; reflexivity. Qed.

Local Lemma typed_definitions_record (m : Mode) G Go e ds T :
  @ty_defs m G Go e ds T ->
  forall D, record_has T D ->
  exists d, defs_has ds d /\ @ty_def m G Go e d D.
Proof.
  intros Typed. induction Typed; intros A Member.
  - apply record_has_single in Member. subst A.
    exists d. split; [|assumption].
    unfold defs_has. simpl. now rewrite If_l by reflexivity.
  - inversion Member; subst.
    + match goal with
      | H : record_has T A |- _ =>
        destruct (IHTyped A H) as [d0 [Found DefTyped]]
      end.
      exists d0. split; [|assumption].
      unfold defs_has in *. simpl.
      rewrite If_r; [assumption|].
      intros Eq. unfold defs_hasnt in H1.
      rewrite <- Eq, H1 in Found. discriminate.
    + match goal with
      | H : record_has (typ_rcd D) A |- _ => apply record_has_single in H; subst A
      end.
      exists d. split; [|assumption].
      unfold defs_has. simpl. now rewrite If_l by reflexivity.
Qed.

Local Lemma record_typ_labels T ls :
  record_typ T ls -> forall D, record_has T D -> label_of D \in ls.
Proof.
  intros Record. induction Record; intros A Member; subst l.
  - apply record_has_single in Member. subst. apply in_singleton_self.
  - inversion Member; subst; rewrite in_union.
    + left; auto.
    + right. match goal with
      | H : record_has (typ_rcd D) A |- _ => apply record_has_single in H; subst A
      end. apply in_singleton_self.
Qed.

Local Lemma record_has_unique T ls :
  record_typ T ls ->
  forall D1 D2, record_has T D1 -> record_has T D2 ->
    label_of D1 = label_of D2 -> D1 = D2.
Proof.
  intros Record. induction Record; intros A B HA HB Label; subst l.
  - apply record_has_single in HA, HB. congruence.
  - inversion HA; inversion HB; subst.
    + auto.
    + match goal with
      | H1 : record_has T A, H2 : record_has (typ_rcd D) B |- _ =>
        apply record_has_single in H2; subst B;
        pose proof (record_typ_labels Record H1) as Present
      end.
      exfalso. apply H1. congruence.
    + match goal with
      | H1 : record_has T B, H2 : record_has (typ_rcd D) A |- _ =>
        apply record_has_single in H2; subst A;
        pose proof (record_typ_labels Record H1) as Present
      end.
      exfalso. apply H1. congruence.
    + match goal with
      | H1 : record_has (typ_rcd D) A, H2 : record_has (typ_rcd D) B |- _ =>
        apply record_has_single in H1, H2; congruence
      end.
Qed.

Local Lemma open_declaration_label (D : dec) n x :
  label_of (open_rec n x D) = label_of D.
Proof. destruct D; reflexivity. Qed.

Local Lemma record_open T ls x :
  record_typ T ls -> record_typ (open x T) ls.
Proof.
  intros Record. induction Record; cbn.
  - apply rt_one; [inversion H; subst; constructor|].
    rewrite <- open_declaration_label with (n:=0) (x:=x) in H0.
    exact H0.
  - apply rt_cons; [assumption|inversion H; subst; constructor| |assumption].
    rewrite <- open_declaration_label with (n:=0) (x:=x) in H0.
    exact H0.
Qed.

Section HeapShapes.
Context (m : Mode) (G : ctx) (e : renv) (s : heap).
Hypothesis Inert : @inert m G.
Hypothesis Correspond : @heap_correspond m G e s.

Local Definition heap_member x a U :=
  exists R C, ctx_binds (location_of e x) (typ_objref R C) G /\
    record_has (open (location_of e x) R) (dec_typ (typ_label_normal a) U U).

Local Definition heap_function x S T :=
  exists t L, binds (location_of e x) (item_fun t) s /\
    (forall z, z \notin L -> @ty_trm m (G § z / v_par ~ S) objctx_empty e (open z t) (open z T)) /\
    all_tfree_k G t v_ref.

Local Definition heap_field x a T :=
  exists ds y R C, binds (location_of e x) (item_obj ds) s /\
    defs_has ds (def_fld a (avar_f y)) /\
    ctx_binds (location_of e x) (typ_objref R C) G /\
    record_has (open (location_of e x) R) (dec_fld a T T).

Local Definition heap_method x a TC TZ TR :=
  exists ds t R C, binds (location_of e x) (item_obj ds) s /\
    defs_has ds (def_met a t) /\
    ctx_binds (location_of e x) (typ_objref R C) G /\
    @ty_def m G (objctx_heap (location_of e x) R) e (def_met a t) (dec_met a TC TZ TR).

Import ShapeInterpretation.
Local Notation value_supported :=
  (value_shape m G e heap_member heap_function heap_field heap_method).
Local Notation satisfies_bounds := (bound_test m G e heap_member).

Local Lemma heap_member_unique x a U V :
  heap_member x a U -> heap_member x a V -> U = V.
Proof.
  intros [R [C [B Left]]] [R' [C' [B' Right]]].
  pose proof (ctx_bind_unique B B') as Eq. injection Eq as EqR EqC. subst R' C'.
  destruct (inert_context_lookup Inert B) as [k [P [_ [Type' _]]]].
  inversion Type'; subst.
  match goal with H : record_type R |- _ => destruct H as [ls Record] end.
  pose proof (record_has_unique (record_open (location_of e x) Record) Left Right eq_refl).
  congruence.
Qed.

Local Lemma heap_member_alias x y a U :
  tyq_var e x y -> heap_member x a U -> heap_member y a U.
Proof.
  intros Eq AtX. unfold heap_member in *.
  destruct Correspond as [_ [_ [_ [_ [_ [_ [Corr _]]]]]]].
  rewrite <- (location_of_equiv Inert Corr Eq). exact AtX.
Qed.

Local Lemma refcap_shape x C ls :
  refcap_typ C ls -> value_supported x C /\ satisfies_bounds C.
Proof.
  induction 1.
  - split; constructor.
  - inversion H; subst. split; [apply value_cap|].
    apply test_cap. intros. apply shape_refl.
  - destruct IHrefcap_typ as [Valid Bounds].
    inversion H0; subst. split.
    + apply value_and; [assumption|apply value_cap].
    + apply test_and; [assumption|].
      apply test_cap. intros. apply shape_refl.
Qed.

Local Lemma inert_capability_shape x C k :
  @refcap_inert_type m C k -> value_supported x C /\ satisfies_bounds C.
Proof.
  unfold refcap_inert_type. destruct (mode_refcaps' m).
  - apply refcap_shape.
  - inversion 1; subst; split; first [apply value_cap | apply test_cap; intros; apply shape_refl].
Qed.

Local Lemma record_supported x T ls :
  record_typ T ls ->
  (forall D, record_has T D -> value_supported x (typ_rcd D) /\ satisfies_bounds (typ_rcd D)) ->
  value_supported x T /\ satisfies_bounds T.
Proof.
  induction 1; intros Supports.
  - apply Supports, rh_one.
  - destruct (IHrecord_typ ltac:(intros; apply Supports, rh_andl; assumption)) as [V1 B1].
    destruct (Supports D (rh_andr T (rh_one D))) as [V2 B2].
    split; constructor; assumption.
Qed.

Local Lemma heap_record_supported x R C ds ls :
  ctx_binds (location_of e x) (typ_objref R C) G ->
  binds (location_of e x) (item_obj ds) s ->
  @ty_defs m G (objctx_heap (location_of e x) R) e ds (open (location_of e x) R) ->
  record_typ R ls ->
  value_supported x (open (location_of e x) R) /\
    satisfies_bounds (open (location_of e x) R).
Proof.
  intros Bound Heap Typed Record.
  eapply record_supported; [apply record_open; eassumption|].
  intros D Member.
  destruct (typed_definitions_record Typed Member) as [d [Found DefTyped]].
  inversion DefTyped; subst.
  - split; [|apply test_typ].
    eapply value_typ; [|intros; apply shape_refl|intros; apply shape_refl].
    exists R, C. split; assumption.
  - split; [eapply value_fld; [|apply shape_refl|apply shape_refl]|apply test_fld].
    eexists _, _, R, C. repeat split; eassumption.
  - split; [eapply value_met; [|apply method_cast_refl]|apply test_met].
    exists ds, t, R, C. repeat split; eassumption.
Qed.

Local Lemma heap_context_supported x X :
  ctx_binds x X G -> value_supported x X /\ satisfies_bounds X.
Proof.
  intros Bound.
  destruct Correspond as [_ [_ [_ [_ [LocDom [RefDom [Corr Items]]]]]]].
  destruct (location_of_context_binding Inert Corr RefDom Bound) as [Y [Q [Located [Related Eq]]]].
  pose proof (ctx_kind_binds Located) as LocBound.
  pose proof (context_kind_in_kind_domain Located) as Present.
  rewrite LocDom in Present.
  pose proof (Items _ Present) as Entry.
  inversion Entry as [G0 e0 s0 p S body L T Fun ItemBound Fn Typed Fvs
    |G0 e0 s0 p R C ds Y' ItemBound Obj EqY Typed Vks]; subst.
  - assert (Y = typ_fun S T) by (eapply ctx_bind_unique; eassumption). subst Y.
    assert (X = typ_fun S T) by (destruct Related as [->|R]; [reflexivity|inversion R; reflexivity]).
    subst X. split; [eapply value_fun; [|apply function_cast_refl]|apply test_fun].
    exists body, L. repeat split; assumption.
  - assert (Y = typ_objref R C) by (eapply ctx_bind_unique; eassumption). subst Y.
    assert (exists D, X = typ_objref R D).
    { destruct Related as [->|Rxy]; [eauto|inversion Rxy; eauto]. }
    destruct H as [D ->].
    destruct (inert_context_lookup Inert Bound) as [k [P [_ [Ty _]]]].
    inversion Ty; subst.
    match goal with
    | H : record_type R |- _ => destruct H as [ls Record]
    end.
    destruct (heap_record_supported x LocBound Obj Typed Record) as [Value Bounds].
    destruct (inert_capability_shape x D k H2) as [CapValue CapBounds].
    assert (Equivalent : tyq_typ e (open (location_of e x) R) (open x R)).
    { apply independent_open_equiv; [apply tyq_var_sym|]; assumption. }
    split.
    + apply value_and.
      * apply value_bnd.
        -- eapply value_shape_equiv; [apply heap_member_alias|exact Equivalent|exact Value].
        -- eapply bound_test_equiv; [apply heap_member_alias|exact Equivalent|exact Bounds].
      * exact CapValue.
    + apply test_and; [apply test_bnd|exact CapBounds].
Qed.

Local Lemma projection_subtyping T D :
  record_has T D -> @subtyp m G objctx_empty e T (typ_rcd D).
Proof.
  induction 1.
  - apply subtyp_refl.
  - eapply subtyp_trans with (T:=T); [apply subtyp_and11|assumption].
  - eapply subtyp_trans with (T:=U); [apply subtyp_and12|assumption].
Qed.

Local Lemma heap_member_typed x a U :
  heap_member x a U ->
  @ty_var m G objctx_empty e x (typ_rcd (dec_typ (typ_label_normal a) U U)).
Proof.
  intros [R [C [Located Member]]].
  destruct (inert_context_lookup Inert Located) as [kind [P [_ [InertType _]]]].
  inversion InertType; subst.
  assert (Independent : typ_indep_b 0 R) by assumption.
  assert (AtX : @ty_var m G objctx_empty e x (open x R) /\ tyq_var e x (location_of e x)).
  { unfold location_of at 1. destruct (get x e) as [y|] eqn:Lookup.
    - destruct Correspond as [_ [_ [_ [_ [_ [_ [Corr _]]]]]]].
      pose proof (location_of_binding Lookup) as Address.
      rewrite Address in Located.
      destruct (corresponding_reference Inert Corr Lookup) as [X [Y [P' [Q [Ref [Loc Related]]]]]].
      assert (Y = typ_objref R C) by
        (eapply ctx_bind_unique; [exact (ctx_kind_binds Loc)|exact Located]).
      subst Y. inversion Related; subst. split.
      + eapply ty_rec_elim; [|exact Independent].
        eapply ty_var_sub; [apply ty_var_var; eapply ctx_kind_binds; exact Ref|apply subtyp_and11].
      + now apply tyq_var_binds.
    - split; [|apply tyq_var_refl].
      assert (location_of e x = x) as Address by (unfold location_of; now rewrite Lookup).
      rewrite Address in Located.
      eapply ty_rec_elim; [|exact Independent].
      eapply ty_var_sub; [apply ty_var_var, Located|apply subtyp_and11]. }
  destruct AtX as [Typed Eq].
  eapply ty_var_sub; [exact Typed|].
  eapply subtyp_trans with (T:=open (location_of e x) R).
  - apply subtyp_tyq. now apply independent_open_equiv.
  - apply projection_subtyping, Member.
Qed.

Local Lemma runtime_field_bounds x a S T :
  @ty_var m G objctx_empty e x (typ_rcd (dec_fld a S T)) ->
  ctx_k G x v_ref ->
  exists y ds ptr R C U,
    binds x y e /\ binds y (item_obj ds) s /\ defs_has ds (def_fld a (avar_f ptr)) /\
    ctx_binds y (typ_objref R C) G /\ record_has (open y R) (dec_fld a U U) /\
    @subtyp m G objctx_empty e S U /\ @subtyp m G objctx_empty e U T.
Proof.
  intros Typed Kind.
  destruct (typing_implies_shape m G heap_member heap_function heap_field heap_method
    heap_member_unique heap_member_alias) as [Supports _].
  destruct (Supports _ _ _ _ _ Typed eq_refl eq_refl heap_context_supported) as [Value _].
  inversion Value as [| | | | | |a0 S0 T0 U Exact Lower Upper| | | |]; subst.
  destruct Exact as [ds [ptr [R [C [Obj [Found [CtxHas Member]]]]]]].
  pose proof Correspond as [_ [_ [_ [_ [_ [RefDom _]]]]]].
  destruct (runtime_reference RefDom Kind) as [y Bound].
  rewrite (location_of_binding Bound) in Obj, CtxHas, Member.
  exists y, ds, ptr, R, C, U. repeat split; try assumption.
  all: (eapply shape_sub_sound; [apply heap_member_typed|eassumption]).
Qed.

Local Lemma runtime_function_signature x S T :
  @ty_var m G objctx_empty e x (typ_fun S T) -> ctx_k G x v_ref ->
  exists y b L A B, binds x y e /\ binds y (item_fun b) s /\
    (forall z, z \notin L -> @ty_trm m (G § z / v_par ~ A) objctx_empty e (open z b) (open z B)) /\
    all_tfree_k G b v_ref /\ function_cast m G e A B S T.
Proof.
  intros Typed Kind.
  destruct (typing_implies_shape m G heap_member heap_function heap_field heap_method
    heap_member_unique heap_member_alias) as [Supports _].
  destruct (Supports _ _ _ _ _ Typed eq_refl eq_refl heap_context_supported) as [Value _].
  inversion Value; subst.
  match goal with
  | Fn : heap_function x ?A ?B, Cast : function_cast _ _ _ ?A ?B S T |- _ =>
      destruct Fn as [b [L [Stored [Body Fvs]]]]
  end.
  pose proof Correspond as [_ [_ [_ [_ [_ [RefDom _]]]]]].
  destruct (runtime_reference RefDom Kind) as [y Bound].
  rewrite (location_of_binding Bound) in Stored.
  eexists y, b, L, _, _. repeat split; eassumption.
Qed.

Local Lemma runtime_method_signature x a TC TZ TR :
  @ty_var m G objctx_empty e x (typ_rcd (dec_met a TC TZ TR)) -> ctx_k G x v_ref ->
  exists y ds b R Cap C Z V, binds x y e /\ binds y (item_obj ds) s /\
    defs_has ds (def_met a b) /\ ctx_binds y (typ_objref R Cap) G /\
    @ty_def m G (objctx_heap y R) e (def_met a b) (dec_met a C Z V) /\
    method_cast m G e C Z V TC TZ TR.
Proof.
  intros Typed Kind.
  destruct (typing_implies_shape m G heap_member heap_function heap_field heap_method
    heap_member_unique heap_member_alias) as [Supports _].
  destruct (Supports _ _ _ _ _ Typed eq_refl eq_refl heap_context_supported) as [Value _].
  inversion Value; subst.
  match goal with Fn : heap_method x a _ _ _ |- _ =>
    destruct Fn as [ds [b [ObjR [Cap [Stored [Found [Bind TypedDef]]]]]]] end.
  pose proof Correspond as [_ [_ [_ [_ [_ [RefDom _]]]]]].
  destruct (runtime_reference RefDom Kind) as [y Bound].
  rewrite (location_of_binding Bound) in Stored, Bind, TypedDef.
  eexists y, ds, b, ObjR, Cap, _, _, _. repeat split; eassumption.
Qed.

Local Lemma runtime_shapes : runtime_canonical_forms m G e s.
Proof.
  destruct (typing_implies_shape m G heap_member heap_function heap_field heap_method
    heap_member_unique heap_member_alias) as [Supports _].
  pose proof Correspond as [_ [_ [_ [_ [_ [RefDom _]]]]]].
  repeat split.
  - intros x S T Typed Kind.
    destruct (Supports _ _ _ _ _ Typed eq_refl eq_refl heap_context_supported) as [Value _].
    inversion Value; subst.
    match goal with H : heap_function x _ _ |- _ => destruct H as [t [L [Fn [Body Free]]]] end.
    destruct (runtime_reference RefDom Kind) as [y Bound].
    exists y, t. rewrite (location_of_binding Bound) in Fn. auto.
  - intros x a S T Typed Kind.
    destruct (Supports _ _ _ _ _ Typed eq_refl eq_refl heap_context_supported) as [Value _].
    inversion Value; subst.
    match goal with H : heap_field x a _ |- _ => destruct H as [ds [ptr [R [C [Obj [Found [CtxHas Member]]]]]]] end.
    destruct (runtime_reference RefDom Kind) as [y Bound].
    exists y, ds, ptr. rewrite (location_of_binding Bound) in Obj. auto.
  - intros x a TC TZ TR Typed Kind.
    destruct (Supports _ _ _ _ _ Typed eq_refl eq_refl heap_context_supported) as [Value _].
    inversion Value; subst.
    match goal with H : heap_method x a _ _ _ |- _ => destruct H as [ds [t [RecTy [CapTy [Obj [Found [CtxBound DefTyped]]]]]]] end.
    destruct (runtime_reference RefDom Kind) as [y Bound].
    exists y, ds, t. rewrite (location_of_binding Bound) in Obj. auto.
Qed.
End HeapShapes.

(* Fresh steps choose names outside both the configuration and the
   context and type expressions used in the proof. *)
Inductive running_config_typed (m : Mode) : ctx -> config -> typ -> Prop :=
| running_config_c G e fs s Lv t T U :
    @inert m G ->
    @heap_correspond m G e s ->
    @ty_stack m G e T fs U ->
    all_tfree_k_stack G fs v_ref ->
    @ty_trm m G objctx_empty e t T ->
    all_tfree_k G t v_ref ->
    config_closed (t; fs; s; e; Lv) ->
    running_config_typed m G (t; fs; s; e; Lv) U.
Arguments running_config_typed m _ _ _ : clear implicits.

Local Lemma configuration_typing_implies_running (m : Mode) G C T :
  @ty_config m G C T -> running_config_typed m G C T.
Proof. inversion 1; subst; econstructor; eassumption. Qed.

Lemma running_configuration_progress (m : Mode) G C T :
  running_config_typed m G C T -> answer C \/ exists C', C ↦ C'.
Proof.
  intros Typed. inversion Typed as
    [G0 e fs s Lv t S U Inert Heap Stack FreeStack Term Free Closed]; subst.
  pose proof (runtime_shapes Inert Heap) as Forms.
  destruct Heap as [_ [_ [Ok [_ [_ [RefDom _]]]]]].
  eapply term_progress_from_canonical_forms; eassumption.
Qed.

Local Definition includes_context (G G' : ctx) :=
  forall x T, ctx_binds x T G -> ctx_binds x T G'.

Local Lemma includes_push G G' x k T :
  includes_context G G' -> includes_context (G § x / k ~ T) (G' § x / k ~ T).
Proof.
  intros Incl y U H. inversion H; subst; eauto using ctx_binds.
Qed.

Local Lemma includes_fresh_binding G x k T :
  x §# G -> includes_context G (G § x / k ~ T).
Proof.
  intros Fresh y U H. apply ctx_binds_n; [|assumption].
  intros ->. apply Fresh. eapply context_binding_in_domain; eassumption.
Qed.

Local Definition includes_environment (e e' : renv) :=
  forall x y, binds x y e -> binds x y e'.

Local Lemma var_equiv_env_weakening e x y :
  tyq_var e x y ->
  forall e', includes_environment e e' -> tyq_var e' x y.
Proof.
  induction 1; intros e' Incl.
  - apply tyq_var_refl.
  - apply tyq_var_binds. auto.
  - apply tyq_var_sym. now apply IHtyq_var.
  - eapply tyq_var_trans with (v2:=v2); [apply IHtyq_var|apply IHtyq_var0]; assumption.
Qed.

Local Lemma type_equiv_env_weakening e T U :
  tyq_typ e T U ->
  forall e', includes_environment e e' -> tyq_typ e' T U.
Proof.
  induction 1; intros e' Incl.
  - apply tyq_typ_nulary; assumption.
  - apply tyq_typ_andor; [assumption|apply IHtyq_typ|apply IHtyq_typ0]; assumption.
  - apply tyq_typ_fun.
    + apply IHtyq_typ; assumption.
    + intros. apply H1; assumption.
  - apply tyq_typ_fld; [apply IHtyq_typ|apply IHtyq_typ0]; assumption.
  - apply tyq_typ_typ; intros; [apply H0|apply H2]; assumption.
  - apply tyq_typ_sel_normal. eapply var_equiv_env_weakening; eassumption.
  - apply tyq_typ_sel.
  - apply tyq_typ_bnd; intros; apply H0; assumption.
  - apply tyq_typ_met.
    + intros; apply H0; assumption.
    + apply IHtyq_typ; assumption.
    + intros; apply H3; assumption.
Qed.

Section StaticWeakening.
Context (m : Mode).

Local Ltac weaken_static_premise :=
  first [assumption
    | solve [eauto 4 using includes_push]
    | solve [eapply type_equiv_env_weakening; eassumption]
    | multimatch goal with
      | IH : forall _ : ctx, _ |- _ =>
          solve [eapply IH; eauto 4 using includes_push]
      | IH : forall _ : var, _ |- _ =>
          solve [eapply IH; eauto 4 using includes_push]
      | IH : _ -> forall _ : ctx, _ |- _ =>
          solve [eapply IH; eauto 4 using includes_push]
      end].

Local Lemma weakening_static :
  (forall G Go e x T, @ty_var m G Go e x T ->
    forall G' e', includes_context G G' -> includes_environment e e' -> @ty_var m G' Go e' x T) /\
  (forall G Go e S T, @subtyp m G Go e S T ->
    forall G' e', includes_context G G' -> includes_environment e e' -> @subtyp m G' Go e' S T) /\
  (forall G Go e S T, @ty_incap m G Go e S T ->
    forall G' e', includes_context G G' -> includes_environment e e' -> @ty_incap m G' Go e' S T).
Proof.
  apply ts_mutind; intros;
    try solve [econstructor; weaken_static_premise].
  all: first
    [ solve [eapply ty_rec_intro; intros; weaken_static_premise]
    | solve [eapply ty_rec_elim; weaken_static_premise]
    | solve [eapply ty_var_and; weaken_static_premise]
    | solve [eapply ty_var_mut_top; weaken_static_premise]
    | solve [eapply ty_var_sub; weaken_static_premise]
    | solve [eapply subtyp_and2; weaken_static_premise]
    | solve [eapply subtyp_or2; weaken_static_premise]
    | solve [eapply subtyp_fld; weaken_static_premise]
    | solve [eapply subtyp_typ; intros; weaken_static_premise]
    | solve [eapply subtyp_sel2; weaken_static_premise]
    | solve [eapply subtyp_sel1; weaken_static_premise]
    | solve [eapply subtyp_fun; intros; weaken_static_premise]
    | solve [eapply subtyp_met; intros; weaken_static_premise]
    | solve [eapply subtyp_tyq; weaken_static_premise]
    | solve [eapply subtyp_trans; weaken_static_premise]
    | solve [eapply ty_incap_sel; weaken_static_premise]
    | solve [eapply ty_incap_and; weaken_static_premise]
    | solve [eapply ty_incap_or; weaken_static_premise]
    | solve [eapply ty_incap_nocap; weaken_static_premise] ].
Qed.

Local Lemma transport_subtype G Go G' e e' S T :
  @subtyp m G Go e S T -> includes_context G G' -> includes_environment e e' -> @subtyp m G' Go e' S T.
Proof.
  intro Typed. exact ((proj1 (proj2 weakening_static)) G Go e S T Typed G' e').
Qed.

Local Lemma weaken_subtype G Go G' e S T :
  @subtyp m G Go e S T -> includes_context G G' -> @subtyp m G' Go e S T.
Proof. intros Typed Incl. eapply transport_subtype; [exact Typed|exact Incl|firstorder]. Qed.

Local Lemma transport_variable G Go G' e e' x T :
  @ty_var m G Go e x T -> includes_context G G' -> includes_environment e e' ->
  @ty_var m G' Go e' x T.
Proof. intro Typed. exact ((proj1 weakening_static) G Go e x T Typed G' e'). Qed.

Local Lemma transport_incap G Go G' e e' T U :
  @ty_incap m G Go e T U -> includes_context G G' -> includes_environment e e' ->
  @ty_incap m G' Go e' T U.
Proof. intro Typed. exact ((proj2 (proj2 weakening_static)) G Go e T U Typed G' e'). Qed.

Local Lemma incapacitation_widens G Go e T U :
  @ty_incap m G Go e T U -> @subtyp m G Go e T U.
Proof.
  induction 1; try apply subtyp_refl; try apply subtyp_top; try apply subtyp_bot.
  - eapply subtyp_trans.
    + eapply subtyp_sel1; eassumption.
    + eassumption.
  - apply subtyp_and2.
    + eapply subtyp_trans; [apply subtyp_and11|eassumption].
    + eapply subtyp_trans; [apply subtyp_and12|eassumption].
  - apply subtyp_or2.
    + eapply subtyp_trans; [eassumption|apply subtyp_or11].
    + eapply subtyp_trans; [eassumption|apply subtyp_or12].
Qed.

Local Lemma invert_let_typing G Go e t u T :
  @ty_trm m G Go e (trm_let t u) T ->
  exists L S U, @ty_trm m G objctx_empty e t S /\
    (forall x, x \notin L -> @ty_trm m (G § x / v_let ~ S) objctx_empty e (open x u) U) /\
    @subtyp m G objctx_empty e U T.
Proof.
  intro H. remember (trm_let t u) as w eqn:Eq in H.
  induction H; inversion Eq; subst.
  - exists L, T, U. repeat split; try assumption. apply subtyp_refl.
  - destruct (IHty_trm eq_refl) as [L [S [V [Typed [Body Sub]]]]].
    exists L, S, V. repeat split; try assumption.
    eapply subtyp_trans; eassumption.
Qed.

Local Lemma extend_let_continuation G e t u T U fs :
  @ty_trm m G objctx_empty e (trm_let t u) T ->
  @ty_stack m G e T fs U ->
  exists S, @ty_trm m G objctx_empty e t S /\
    @ty_stack m G e S (stack_cons (frame_let u) fs) U.
Proof.
  intros Typed StackTyped.
  destruct (invert_let_typing Typed) as [L [S [V [Part [Body Sub]]]]].
  exists S. split; [assumption|].
  eapply ty_stack_let with (L:=L \u ctx_dom G); [exact StackTyped|].
  intros x Fresh. apply notin_union in Fresh as [FL FG].
  eapply ty_trm_sub.
  - apply Body. exact FL.
  - eapply weaken_subtype; [exact Sub|]. apply includes_fresh_binding, FG.
Qed.
End StaticWeakening.

Local Lemma configuration_push_let_preservation (m : Mode)
  G t u fs s e Lv U :
  running_config_typed m G (trm_let t u; fs; s; e; Lv) U ->
  running_config_typed m G (t; stack_cons (frame_let u) fs; s; e;
    fv_config (trm_let t u; fs; s; e; Lv)) U.
Proof.
  intros Typed.
  inversion Typed as [G0 e0 fs0 s0 Lv0 t0 T U0
    Inert Heap StackTyped FreeStack TermTyped FreeTerm Closed];
    subst.
  destruct (extend_let_continuation TermTyped StackTyped) as [Input [Part Extended]].
  apply (running_config_c (T:=Input)); try assumption.
  - intros v Free. inversion Free; subst.
    + apply FreeTerm, tfree_trm_let_r. assumption.
    + apply FreeStack. assumption.
  - intros v Free. apply FreeTerm, tfree_trm_let_l. assumption.
  - inversion Closed as [t' fs' s' e' Lv' ClosedTerm ClosedStack ClosedHeap]; subst.
    constructor; try assumption.
    + intros n x.
      specialize (ClosedTerm n x).
      change (trm_let (open_rec n x t) (open_rec (S n) x u) = trm_let t u) in ClosedTerm.
      now injection ClosedTerm.
    + intros n x.
      specialize (ClosedTerm n x).
      change (trm_let (open_rec n x t) (open_rec (S n) x u) = trm_let t u) in ClosedTerm.
      injection ClosedTerm as _ Body.
      change (stack_cons (frame_let (open_rec (S n) x u)) (open_rec n x fs) =
        stack_cons (frame_let u) fs).
      now rewrite Body, ClosedStack.
Qed.

Section AliasTyping.
Context (m : Mode).

Local Lemma nocap_below_incap_selection G Go e T U :
  @ty_incap m G Go e T U ->
  forall x a y, U = typ_sel x a y -> @subtyp m G Go e typ_nocap U.
Proof.
  induction 1; intros x' a' y' Eq; try discriminate.
  - eapply IHty_incap; eassumption.
  - assumption.
Qed.

Local Lemma nocap_below_self_incap G Go e S T :
  @ty_incap m G Go e S T -> S = T -> @subtyp m G Go e typ_nocap T.
Proof.
  induction 1; intro Eq; try discriminate;
    try solve [first [apply subtyp_top |apply subtyp_nocap_typ |apply subtyp_nocap_met
      |apply subtyp_nocap_fld |apply subtyp_nocap_bnd |now apply subtyp_nocap_fun |assumption]].
  - eapply nocap_below_incap_selection; [eassumption|symmetry; exact Eq].
  - injection Eq as Left Right. apply subtyp_and2; [apply IHty_incap|apply IHty_incap0]; assumption.
  - injection Eq as Left Right. eapply subtyp_trans.
    + apply IHty_incap, Left.
    + apply subtyp_or11.
Qed.

Local Lemma structural_incap_no_selection G Go e T U :
  @ty_incap m G Go e T U ->
  mode_incap' m = mode_incap_structural ->
  forall x a y, U <> typ_sel x a y.
Proof.
  induction 1; intros Mode' x' a' y' Eq; try discriminate; try congruence.
  eapply IHty_incap; eassumption.
Qed.

Local Lemma structural_self_incap_equiv G Go e S T :
  tyq_typ e S T ->
  mode_incap' m = mode_incap_structural ->
  @ty_incap m G Go e S S -> @ty_incap m G Go e T T.
Proof.
  intros Eq. revert G Go. induction Eq; intros G0 Go0 Mode' Self;
    assert (Go0 = objctx_empty) by (inversion Self; reflexivity); subst Go0;
    try assumption.
  - inversion H; subst; inversion Self; subst; try congruence.
    + apply ty_incap_and; [apply IHEq|apply IHEq0]; assumption.
    + apply ty_incap_or; [apply IHEq|apply IHEq0]; assumption.
  - inversion Self; subst; try congruence. now apply ty_incap_fun.
  - apply ty_incap_fld.
  - destruct B.
    + apply ty_incap_typ.
    + inversion Self; subst; congruence.
  - exfalso. eapply structural_incap_no_selection; eassumption || reflexivity.
  - apply ty_incap_rec.
  - apply ty_incap_met.
Qed.

Local Lemma self_incap_equiv G Go e S T :
  tyq_typ e S T ->
  @ty_incap m G Go e S S ->
  mode_has_incap' m = true ->
  @ty_incap m G Go e T T.
Proof.
  intros Eq Self Mode'.
  destruct (mode_incap' m) eqn:IncapMode.
  - unfold mode_has_incap' in Mode'. rewrite IncapMode in Mode'. discriminate.
  - eapply structural_self_incap_equiv; eassumption.
  - assert (Go = objctx_empty) by (inversion Self; reflexivity). subst Go.
    apply ty_incap_nocap; [assumption|].
    eapply subtyp_trans with (T:=S).
    + eapply nocap_below_self_incap; [exact Self|reflexivity].
    + apply subtyp_tyq. exact Eq.
Qed.

Local Lemma alias_variable_typing G Go e x T :
  @ty_var m G Go e x T ->
  forall y, tyq_var e x y ->
  (forall U, ctx_binds x U G -> @ty_var m G objctx_empty e y U) ->
  @ty_var m G Go e y T.
Proof.
  induction 1; intros y Eq Included.
  - apply Included. assumption.
  - eapply ty_rec_intro; [|assumption|].
    + eapply ty_var_sub; [apply IHty_var; assumption|].
      apply subtyp_tyq. now apply independent_open_equiv.
    + intros Mode'. eapply self_incap_equiv with (S:=open x T);
      [now apply independent_open_equiv|now apply H1|assumption].
  - eapply ty_var_sub.
    + eapply ty_rec_elim; [apply IHty_var; assumption|assumption].
    + apply subtyp_tyq, independent_open_equiv; [apply tyq_var_sym|]; assumption.
  - apply ty_var_and; [apply IHty_var|apply IHty_var0]; assumption.
  - eapply ty_var_sub; [apply IHty_var; assumption|assumption].
  - eapply ty_var_mut_top; [assumption|apply IHty_var; assumption].
Qed.

Local Lemma corresponding_location_type G e x y T :
  @inert m G -> @renv_corr m G e ->
  binds x y e -> @ty_var m G objctx_empty e x T ->
  @ty_var m G objctx_empty e y T.
Proof.
  intros Inert Corr Bound Typed.
  destruct (corresponding_reference Inert Corr Bound)
    as [X [Y [P [Q [Ref [Loc Related]]]]]].
  pose proof (ctx_kind_binds Ref) as RefType.
  pose proof (ctx_kind_binds Loc) as LocType.
  eapply alias_variable_typing; [exact Typed|now apply tyq_var_binds|].
  intros U UBound.
  assert (U = X) by (eapply ctx_bind_unique; eassumption). subst U.
  destruct Related.
  - destruct (mode_refcap_corr' m); subst.
    + apply ty_var_var, LocType.
    + destruct H as [B [-> ->]].
      eapply ty_var_sub; [apply ty_var_var, LocType|].
      apply subtyp_and2; [apply subtyp_and11|].
      eapply subtyp_trans; [apply subtyp_and12|].
      apply subtyp_typ; intros; apply subtyp_bot.
  - apply ty_var_var, LocType.
Qed.
End AliasTyping.

Local Lemma defs_update_keeps_absence ds a y ds' :
  defs_update ds a y ds' ->
  forall l, defs_hasnt ds l -> defs_hasnt ds' l.
Proof.
  induction 1; unfold defs_hasnt in *; intros l Absent; simpl in *.
  - destruct (classic (label_fld a = l)) as [Eq | Neq].
    + rewrite If_l in Absent by exact Eq. discriminate.
    + now rewrite If_r in * by exact Neq.
  - destruct (classic (label_of d = l)) as [Eq | Neq].
    + rewrite If_l in Absent by exact Eq. discriminate.
    + rewrite If_r in * by exact Neq. auto.
Qed.

Local Lemma definition_typing_label (m : Mode) G Go e d D :
  @ty_def m G Go e d D -> label_of d = label_of D.
Proof. destruct 1; reflexivity. Qed.

Local Lemma field_update_keeps_definition_typing (m : Mode) G Go e
  ds R a U y ds' :
  @ty_defs m G Go e ds R ->
  record_type R ->
  record_has R (dec_fld a U U) ->
  ((mode_visibility' m = mode_visibility_hide_method) -> ctx_vis (ctx_obj G Go) y) ->
  @ty_var m (ctx_obj G Go) objctx_empty e y U ->
  defs_update ds a y ds' ->
  @ty_defs m G Go e ds' R.
Proof.
  intros Typed. revert ds'.
  induction Typed; intros ds' [ls Record] Member Vis Arg Update.
  - apply record_has_single in Member. subst D.
    inversion Update; subst.
    + apply ty_defs_one. now apply ty_def_fld.
    + match goal with H : defs_update defs_nil _ _ _ |- _ => inversion H end.
  - inversion Update; subst.
    + assert (D = dec_fld a U U).
      { eapply record_has_unique; [exact Record|apply rh_andr, rh_one|exact Member|].
        symmetry. exact (definition_typing_label H0). }
      subst D. apply ty_defs_cons; try assumption. now apply ty_def_fld.
    + apply ty_defs_cons.
      * eapply IHTyped; try eassumption.
        -- inversion Record; subst. eexists; eassumption.
        -- inversion Member; subst; try assumption.
           match goal with H : record_has (typ_rcd D) _ |- _ =>
             apply record_has_single in H; subst D
           end.
           exfalso. match goal with H : label_of d <> label_fld a |- _ => apply H end.
           exact (definition_typing_label H0).
      * assumption.
      * eapply defs_update_keeps_absence; eassumption.
Qed.

Local Lemma field_update_keeps_definition_kinds G ds a y ds' :
  defs_update ds a y ds' -> defs_varkinds G ds -> ctx_k G y v_loc ->
  defs_varkinds G ds'.
Proof.
  induction 1; intros Vks Kind; inversion Vks; subst;
    apply defs_varkinds_cons; auto using def_varkinds.
Qed.

Local Lemma binds_unique {A} (s : env A) x a b :
  binds x a s -> binds x b s -> a = b.
Proof. unfold binds; congruence. Qed.

Local Lemma visible_in_inert_context (m : Mode) G x T :
  @inert m G -> ctx_binds x T G -> ctx_vis G x.
Proof.
  intros Inert. induction Inert; inversion 1; subst; eauto using ctx_vis.
Qed.

Local Lemma heap_correspond_write (m : Mode) G e s s' loc a ptr R C T :
  @inert m G -> @heap_correspond m G e s -> heap_update s loc a ptr s' ->
  ctx_binds loc (typ_objref R C) G ->
  record_has (open loc R) (dec_fld a T T) ->
  @ty_var m G objctx_empty e ptr T ->
  ctx_k G ptr v_loc ->
  @heap_correspond m G e s'.
Proof.
  intros Inert Heap Step ObjType Member Arg Kind.
  destruct Heap as [OkG [PlainG [OkS [OkE [LocDom [RefDom [Corr Entries]]]]]]].
  destruct Step as [_ [OkS' [Dom [Other [ds [ds' [Old [Update New]]]]]]]].
  assert (Record : record_type (open loc R)).
  { destruct (inert_context_lookup Inert ObjType) as [k [P [_ [Ty _]]]].
    inversion Ty; subst. match goal with H : record_type R |- _ =>
      destruct H as [ls Record]; exists ls; now apply record_open end. }
  repeat split; try assumption.
  { now rewrite <- Dom. }
  intros x Present. rewrite <- Dom in Present.
  pose proof (Entries _ Present) as Entry.
  destruct (classic (x = loc)) as [-> | Neq].
  - inversion Entry as [G0 e0 s0 x0 S body L U Fun TBound SBound Check Free
      |G0 e0 s0 x0 R0 C0 d T0 TBound SBound Eq Typed Vks]; subst.
    + pose proof (binds_unique Old SBound). discriminate.
    + pose proof (binds_unique Old SBound) as EqD. injection EqD as <-.
      pose proof (ctx_bind_unique ObjType TBound) as EqType.
      injection EqType as EqR EqC. subst R0 C0.
      eapply ty_item_obj_s with (U:=R) (S:=C) (ds:=ds'); try eassumption.
      * reflexivity.
      * eapply field_update_keeps_definition_typing; try eassumption.
        intros _. destruct Kind as [U [P K]].
        eapply visible_in_inert_context; [exact Inert|exact (ctx_kind_binds K)].
      * eapply field_update_keeps_definition_kinds; eassumption.
  - inversion Entry; subst.
    + eapply ty_item_fun_s; try eassumption. now apply Other.
    + eapply ty_item_obj_s; try eassumption; [now apply Other|reflexivity].
Qed.

Local Lemma heap_closed_items s :
  heap_closed s -> forall x v, binds x v s -> closed v.
Proof.
  induction 1; intros y v Bound.
  - exfalso. eapply binds_empty_inv; eassumption.
  - destruct (binds_push_inv Bound) as [[_ ->] | [_ Other]]; eauto.
Qed.

Local Lemma heap_closed_from_items s :
  ok s -> (forall x v, binds x v s -> closed v) -> heap_closed s.
Proof.
  induction s as [|s k v IH] using env_ind; intros Ok All.
  - constructor.
  - apply heap_closed_push.
    + destruct (ok_push_inv Ok) as [Ok' Fresh].
      apply IH; [assumption|]. intros x a Bound.
      apply (All x), binds_push_neq; [assumption|].
      intros ->. apply Fresh. eapply get_some_inv. exact Bound.
    + eapply All. apply binds_push_eq.
Qed.

Local Lemma field_update_closed ds a y ds' :
  defs_update ds a y ds' -> closed ds -> closed ds'.
Proof.
  induction 1; intros Closed' k z0.
  - specialize (Closed' k z0).
    change (defs_cons (open_rec k z0 ds) (def_fld a (open_rec k z0 t)) =
      defs_cons ds (def_fld a t)) in Closed'.
    injection Closed' as Left _.
    change (defs_cons (open_rec k z0 ds) (def_fld a (avar_f x)) =
      defs_cons ds (def_fld a (avar_f x))).
    now rewrite Left.
  - assert (ClosedPrefix : closed ds).
    { intros n z. specialize (Closed' n z).
      change (defs_cons (open_rec n z ds) (open_rec n z d) = defs_cons ds d) in Closed'.
      now injection Closed'. }
    specialize (Closed' k z0).
    change (defs_cons (open_rec k z0 ds) (open_rec k z0 d) = defs_cons ds d) in Closed'.
    injection Closed' as _ Right.
    change (defs_cons (open_rec k z0 ds') (open_rec k z0 d) = defs_cons ds' d).
    now rewrite (IHdefs_update ClosedPrefix k z0), Right.
Qed.

Local Lemma heap_closed_write s s' loc a ptr :
  heap_closed s -> heap_update s loc a ptr s' -> heap_closed s'.
Proof.
  intros Closed [_ [Ok' [Dom [Other [ds [ds' [Old [Update New]]]]]]]].
  apply heap_closed_from_items; [assumption|].
  intros x v Bound.
  destruct (classic (x = loc)) as [-> | Neq].
  - pose proof (binds_unique Bound New) as ->.
    assert (ClosedDS : closed ds).
    { pose proof (heap_closed_items Closed Old) as H.
      intros n y. specialize (H n y).
      change (item_obj (open_rec n y ds) = item_obj ds) in H.
      now injection H. }
    pose proof (field_update_closed Update ClosedDS) as ClosedDS'.
    intros n y. change (item_obj (open_rec n y ds') = item_obj ds').
    now rewrite ClosedDS'.
  - destruct (get x s) as [v0|] eqn:Lookup.
    + pose proof (binds_unique Bound (Other _ _ Neq Lookup)) as ->.
      eapply heap_closed_items; eassumption.
    + exfalso. apply (get_none_inv Lookup). rewrite Dom. eapply get_some_inv. exact Bound.
Qed.

Local Lemma invert_write_typing (m : Mode) G Go e x a z R :
  @ty_trm m G Go e (trm_write (avar_f x) a (avar_f z)) R ->
  exists S T,
    @ty_var m G objctx_empty e x (typ_rcd (dec_fld a S T)) /\
    @ty_var m G objctx_empty e z S /\
    ((mode_visibility' m = mode_visibility_hide_method) -> ctx_vis G z) /\
    @subtyp m G objctx_empty e T R.
Proof.
  intro H. remember (trm_write (avar_f x) a (avar_f z)) as w eqn:Eq in H.
  induction H; inversion Eq; subst.
  - eexists _, _. repeat split; try eassumption. apply subtyp_refl.
  - destruct (IHty_trm eq_refl) as [S [V [Receiver [Arg [Vis Sub]]]]].
    exists S, V. repeat split; try eassumption.
    eapply subtyp_trans; eassumption.
Qed.

Lemma configuration_write_preservation (m : Mode) G x a z fs s e Lv U s' loc ptr :
  running_config_typed m G (trm_write (avar_f x) a (avar_f z); fs; s; e; Lv) U ->
  binds x loc e -> binds z ptr e -> heap_update s loc a ptr s' ->
  running_config_typed m G (trm_var (avar_f z); fs; s'; e;
    fv_config (trm_write (avar_f x) a (avar_f z); fs; s; e; Lv)) U.
Proof.
  intros Typed ReceiverBinding ArgumentBinding Update.
  inversion Typed as [G0 e0 fs0 s0 Lv0 t0 T U0
    Inert Heap StackTyped FreeStack TermTyped FreeTerm Closed];
    subst.
  destruct (invert_write_typing TermTyped) as [S [W [Receiver [Argument [Visible Return]]]]].
  pose proof (FreeTerm x (tfree_trm_write_l x (avar_f z) a)) as ReceiverKind.
  pose proof (FreeTerm z (tfree_trm_write_r (avar_f x) z a)) as ArgumentKind.
  destruct (runtime_field_bounds Inert Heap Receiver ReceiverKind)
    as [y [ds [old [R [C [FieldType [Binding [Obj [Found [Bound [Member [Lower Upper]]]]]]]]]]]].
  assert (y = loc) by (eapply binds_unique; eassumption). subst y.
  pose proof Heap as [_ [_ [_ [_ [_ [_ [Corr _]]]]]]].
  assert (ArgAtLoc : @ty_var m G objctx_empty e ptr FieldType).
  { eapply corresponding_location_type; [exact Inert|exact Corr|exact ArgumentBinding|].
    eapply ty_var_sub; eassumption. }
  assert (KindAtLoc : ctx_k G ptr v_loc).
  { destruct (corresponding_reference Inert Corr ArgumentBinding)
      as [X [Y [P [Q [_ [Loc _]]]]]].
    exists Y, Q. exact Loc. }
  apply (running_config_c (T:=T)); try assumption.
  - eapply heap_correspond_write; eassumption.
  - eapply ty_trm_sub.
    + apply ty_trm_var; [exact Visible|exact Argument].
    + eapply subtyp_trans with (T:=FieldType); [exact Lower|].
      eapply subtyp_trans with (T:=W); assumption.
  - intros v Free. inversion Free; subst. exact ArgumentKind.
  - inversion Closed as [t' fs' s0' e' Lv' CT CS CH]; subst.
    constructor; try assumption.
    + intros n v; reflexivity.
    + eapply heap_closed_write; eassumption.
Qed.

Local Definition includes_visibility (G G' : ctx) :=
  forall x, ctx_vis G x -> ctx_vis G' x.

Local Lemma includes_push_visibility G G' x k T :
  includes_visibility G G' ->
  includes_visibility (G § x / k ~ T) (G' § x / k ~ T).
Proof. intros Incl y H. inversion H; subst; eauto using ctx_vis. Qed.

Local Lemma includes_hide G G' :
  includes_context G G' -> includes_context (ctx_hide G) (ctx_hide G').
Proof. intros Incl y U H. inversion H; subst; auto using ctx_binds. Qed.

Local Lemma includes_hide_visibility G G' :
  includes_visibility (ctx_hide G) (ctx_hide G').
Proof. intros x H. inversion H. Qed.

Local Lemma includes_object G G' Go :
  includes_context G G' -> includes_context (ctx_obj G Go) (ctx_obj G' Go).
Proof. destruct Go; simpl; auto using includes_push. Qed.

Local Lemma includes_object_visibility G G' Go :
  includes_visibility G G' -> includes_visibility (ctx_obj G Go) (ctx_obj G' Go).
Proof. destruct Go; simpl; auto using includes_push_visibility. Qed.

Local Lemma includes_method m G G' Go z TZ c TC :
  includes_context G G' ->
  includes_context (ctx_obj_met m G Go z TZ c TC) (ctx_obj_met m G' Go z TZ c TC).
Proof.
  destruct Go; unfold ctx_obj_met; destruct (mode_visibility' m);
    eauto using includes_push, includes_hide.
Qed.

Local Lemma includes_method_visibility m G G' Go z TZ c TC :
  includes_visibility G G' ->
  includes_visibility (ctx_obj_met m G Go z TZ c TC) (ctx_obj_met m G' Go z TZ c TC).
Proof.
  destruct Go; unfold ctx_obj_met; destruct (mode_visibility' m);
    eauto using includes_push_visibility, includes_hide_visibility.
Qed.

Local Lemma includes_fresh_binding_visibility G x k T :
  x §# G -> includes_visibility G (G § x / k ~ T).
Proof.
  assert (Dom : forall G y, ctx_vis G y -> y \in ctx_dom G).
  { induction 1; simpl; rewrite in_union; auto using in_singleton_self. }
  intros Fresh y H. apply ctx_vis_n; [|assumption].
  intros ->. apply Fresh. auto.
Qed.

Section SyntaxWeakening.
Context (m : Mode).

Local Ltac weaken_syntax_premise :=
  first [assumption
    | solve [eauto 4 using includes_push, includes_push_visibility, includes_object,
                 includes_object_visibility, includes_method, includes_method_visibility]
    | solve [eapply type_equiv_env_weakening; eassumption]
    | solve [eapply transport_variable; eauto using includes_object]
    | solve [eapply transport_subtype; eassumption]
    | multimatch goal with
      | IH : forall _ : ctx, _ |- _ =>
          solve [eapply IH; eauto 4 using includes_push, includes_push_visibility, includes_method,
                                    includes_method_visibility, includes_object, includes_object_visibility]
      | IH : forall _ : var, _ |- _ =>
          solve [eapply IH; eauto 4 using includes_push, includes_push_visibility, includes_method,
                                    includes_method_visibility, includes_object, includes_object_visibility]
      end].

Local Lemma transport_capability c G Go e S T :
  @ty_capbnd m c G Go e S T ->
  forall G' e', includes_context G G' -> includes_environment e e' ->
  @ty_capbnd m c G' Go e' S T.
Proof. induction 1; intros; econstructor; weaken_syntax_premise. Qed.

Local Lemma transport_adaptation x G Go e S T G' e' :
  @viewpoint_adapt m x G Go e S T ->
  includes_context G G' -> includes_environment e e' ->
  @viewpoint_adapt m x G' Go e' S T.
Proof.
  unfold viewpoint_adapt. destruct (mode_viewpoint_adaptation' m); auto.
  intros H Incl Env. inversion H; subst.
  econstructor; [eapply transport_incap|eapply transport_capability]; eassumption.
Qed.

Local Lemma weakening_syntax :
  (forall G Go e t T, @ty_trm m G Go e t T ->
    forall G' e', includes_context G G' -> includes_visibility G G' ->
    includes_environment e e' -> @ty_trm m G' Go e' t T) /\
  (forall G Go e l T, @ty_lit m G Go e l T ->
    forall G' e', includes_context G G' -> includes_visibility G G' ->
    includes_environment e e' -> @ty_lit m G' Go e' l T) /\
  (forall G Go e d D, @ty_def m G Go e d D ->
    forall G' e', includes_context G G' -> includes_visibility G G' ->
    includes_environment e e' -> @ty_def m G' Go e' d D) /\
  (forall G Go e ds T, @ty_defs m G Go e ds T ->
    forall G' e', includes_context G G' -> includes_visibility G G' ->
    includes_environment e e' -> @ty_defs m G' Go e' ds T).
Proof.
  apply rules_mutind; intros.
  all: try first
    [ solve [eapply ty_trm_var; intros; weaken_syntax_premise]
    | solve [eapply ty_trm_apply; intros; weaken_syntax_premise]
    | solve [eapply ty_trm_read; intros;
         first [weaken_syntax_premise|solve [eapply transport_adaptation; eassumption]]]
    | solve [eapply ty_trm_write; intros; weaken_syntax_premise]
    | solve [eapply ty_trm_call; intros; weaken_syntax_premise]
    | solve [eapply ty_trm_let; intros; weaken_syntax_premise]
    | solve [eapply ty_trm_lit; intros; weaken_syntax_premise]
    | solve [eapply ty_trm_sub; weaken_syntax_premise]
    | solve [eapply ty_lit_fun; intros; weaken_syntax_premise]
    | solve [eapply ty_lit_obj; intros; weaken_syntax_premise]
    | solve [eapply ty_def_typ; intros; weaken_syntax_premise]
    | solve [eapply ty_def_fld; intros; weaken_syntax_premise]
    | solve [eapply ty_def_met; intros; weaken_syntax_premise]
    | solve [eapply ty_defs_one; weaken_syntax_premise]
    | solve [eapply ty_defs_cons; weaken_syntax_premise] ].
  - eapply ty_trm_write with (S:=S); intros;
      try solve [weaken_syntax_premise].
    eapply transport_variable; [now apply o|exact H|exact H1].
  - eapply ty_def_typ with (L:=L). intros x Fresh.
    eapply type_equiv_env_weakening; [apply t, Fresh|exact H1].
  - apply ty_def_fld.
    + intros Mode'. exact ((@includes_object_visibility G G' Go H0) t (c Mode')).
    + eapply transport_variable; [exact o|apply includes_object, H|exact H1].
Qed.

Local Lemma transport_term G Go e t T G' e' :
  @ty_trm m G Go e t T -> includes_context G G' -> includes_visibility G G' ->
  includes_environment e e' -> @ty_trm m G' Go e' t T.
Proof. intro Typed. exact ((proj1 weakening_syntax) G Go e t T Typed G' e'). Qed.

Local Lemma transport_definitions G Go e ds T G' e' :
  @ty_defs m G Go e ds T -> includes_context G G' -> includes_visibility G G' ->
  includes_environment e e' -> @ty_defs m G' Go e' ds T.
Proof. intro Typed. exact ((proj2 (proj2 (proj2 weakening_syntax))) G Go e ds T Typed G' e'). Qed.

Local Lemma transport_stack G e T s U :
  @ty_stack m G e T s U ->
  forall G' e', includes_context G G' -> includes_visibility G G' -> includes_environment e e' ->
  @ty_stack m G' e' T s U.
Proof.
  induction 1; intros.
  - constructor. eapply transport_subtype; eassumption.
  - eapply ty_stack_let with (L:=L).
    + eapply IHty_stack; eassumption.
    + intros x Fresh. eapply transport_term; [now apply H0| | |assumption];
        auto using includes_push, includes_push_visibility.
Qed.
End SyntaxWeakening.

Local Lemma fresh_binding_kind G w k T x k' U P :
  w §# G ->
  ctx_binds_k_after x k' U G P ->
  ctx_binds_k_after x k' U (G § w / k ~ T) P.
Proof.
  intros Fresh Bound. apply ctx_binds_k_n; [|exact Bound].
  intros ->. apply Fresh. eapply context_binding_in_domain, ctx_kind_binds; eassumption.
Qed.

Local Lemma fresh_binding_kind_inclusion G w k T x k' :
  w §# G -> ctx_k G x k' -> ctx_k (G § w / k ~ T) x k'.
Proof.
  intros Fresh [U [P Bound]]. exists U, P. now apply fresh_binding_kind.
Qed.

Local Lemma fresh_binding_tfree {A : Set} {TF : TFree A} G (a : A) w T k k' :
  w §# G -> all_tfree_k G a k' -> all_tfree_k (G § w / k ~ T) a k'.
Proof. intros Fresh Fvs x Free. apply fresh_binding_kind_inclusion; auto. Qed.

Local Lemma fresh_binding_stack_tfree G (fs : stack) w T k k' :
  w §# G -> all_tfree_k_stack G fs k' -> all_tfree_k_stack (G § w / k ~ T) fs k'.
Proof. apply fresh_binding_tfree. Qed.

Local Lemma fresh_binding_definition_kinds G ds w k T :
  w §# G -> defs_varkinds G ds -> defs_varkinds (G § w / k ~ T) ds.
Proof.
  intros Fresh Kinds. induction Kinds; constructor; auto.
  inversion H; subst; constructor.
  - now apply fresh_binding_kind_inclusion.
  - now apply fresh_binding_tfree.
Qed.

Local Lemma fresh_binding_renv_correspondence m G e w k T :
  w §# G -> @renv_corr m G e -> @renv_corr m (G § w / k ~ T) e.
Proof.
  intros Fresh Corr. induction Corr.
  - constructor.
  - eapply renv_corr_ref.
    + eapply fresh_binding_kind; eassumption.
    + eassumption.
    + eassumption.
    + auto.
Qed.

Local Lemma location_type_for_reference (m : Mode) T :
  @inert_typ m T v_loc -> @inert_typ m T v_ref /\ @typ_corr m T T.
Proof.
  intros Ty. inversion Ty; subst.
  - split; [apply inert_typ_fun|apply typ_corr_fun]; assumption.
  - split.
    + apply inert_typ_obj; try assumption.
      unfold refcap_inert_type in *. destruct (mode_refcaps' m); [assumption|].
      match goal with H : refcap_inert_mutability _ v_loc |- _ => inversion H; subst; constructor end.
    + apply typ_corr_obj. destruct (mode_refcap_corr' m) eqn:Mode'; [reflexivity|].
      assert (mode_refcaps' m = mode_refcaps_mutability) as ModeCap.
      { destruct m; simpl in *; congruence. }
      match goal with
      | H : @refcap_inert_type _ _ v_loc |- _ =>
        unfold refcap_inert_type in H; rewrite ModeCap in H; inversion H; subst
      end.
      exists typ_bot. auto.
Qed.

Local Lemma heap_extend_context (m : Mode) G e s x w k Ty :
  ty_item_s m G e s x ->
  w §# G ->
  forall e', includes_environment e e' ->
  ty_item_s m (G § w / k ~ Ty) e' s x.
Proof.
  intros Entry Fresh e' Env. inversion Entry; subst.
  - eapply ty_item_fun_s with (L:=L); try eassumption.
    + eapply includes_fresh_binding; eassumption.
    + intros z F. eapply transport_term.
      * match goal with H : forall x, x \notin L -> _ |- _ => now apply H end.
      * apply includes_push. now apply includes_fresh_binding.
      * apply includes_push_visibility. now apply includes_fresh_binding_visibility.
      * exact Env.
    + apply fresh_binding_tfree; assumption.
  - eapply ty_item_obj_s with (U:=U) (S:=S); try eassumption.
    + eapply includes_fresh_binding; eassumption.
    + reflexivity.
    + eapply transport_definitions;
        eauto using includes_fresh_binding, includes_fresh_binding_visibility.
    + now apply fresh_binding_definition_kinds.
Qed.

Local Lemma includes_fresh_alias e w y :
  w # e -> includes_environment e (e & w ~ y).
Proof.
  intros Fresh x z Bound. apply binds_push_neq; [assumption|].
  intros ->. apply Fresh. eapply get_some_inv. exact Bound.
Qed.

Local Lemma extend_heap_with_reference (m : Mode) G e s x w Ty P :
  @heap_correspond m G e s -> w §# G -> w # e ->
  ctx_binds_k_after x v_loc Ty G P -> @typ_corr m Ty Ty ->
  @heap_correspond m (G § w / v_ref ~ Ty) (e & w ~ x) s.
Proof.
  intros Heap FreshG FreshE Bound TyCorr.
  destruct Heap as [OkG [PlainG [OkS [OkE [LocDom [RefDom [Corr Entries]]]]]]].
  repeat split; try assumption.
  - now apply ctx_ok_push.
  - now apply ctx_weakens_push.
  - now apply ok_push.
  - simpl. now rewrite If_r by discriminate.
  - simpl. rewrite If_l by reflexivity. rewrite RefDom, dom_concat, dom_single.
    apply union_comm.
  - eapply renv_corr_ref; [constructor|exact Bound|exact TyCorr|].
    now apply fresh_binding_renv_correspondence.
  - intros loc Present. eapply heap_extend_context; [apply Entries, Present|exact FreshG|].
    now apply includes_fresh_alias.
Qed.

Local Lemma ctx_type_free_vars G x (T : typ) :
  ctx_binds x T G -> fv T \c ctx_fv G.
Proof.
  induction 1; intros z Present; simpl; try rewrite in_union; auto.
Qed.

Local Lemma defs_has_kind G ds d :
  defs_varkinds G ds -> defs_has ds d -> def_varkinds G d.
Proof.
  unfold defs_has. induction 1; simpl; try discriminate.
  intros Lookup.
  destruct (classic (label_of d0 = label_of d)) as [Same | Distinct].
  - rewrite If_l in Lookup by exact Same. now injection Lookup as ->.
  - rewrite If_r in Lookup by exact Distinct. auto.
Qed.

Local Lemma stored_field_typing (m : Mode) G e s y ds R C a U ptr :
  @heap_correspond m G e s ->
  ctx_binds y (typ_objref R C) G ->
  binds y (item_obj ds) s ->
  record_has (open y R) (dec_fld a U U) ->
  defs_has ds (def_fld a (avar_f ptr)) ->
  @ty_var m G objctx_empty e ptr U /\ ctx_k G ptr v_loc.
Proof.
  intros Heap Located Object Member Found.
  destruct Heap as [_ [_ [_ [_ [_ [_ [_ Items]]]]]]].
  pose proof (Items _ (get_some_inv Object)) as Entry.
  inversion Entry as [G0 e0 s0 x0 S body L V Fun TBound SBound Check Free
    |G0 e0 s0 x0 R0 C0 d T0 TBound SBound Eq Typed Vks]; subst.
  - pose proof (binds_unique Object SBound). discriminate.
  - pose proof (binds_unique Object SBound) as EqD. injection EqD as <-.
    pose proof (ctx_bind_unique Located TBound) as EqType.
    injection EqType as EqR EqC. subst R0 C0.
    split.
    + destruct (typed_definitions_record Typed Member) as [d [Found' Typed']].
      inversion Typed'; subst.
      unfold defs_has in Found, Found'. simpl in Found, Found'.
      assert (ptr = t) by congruence. now subst ptr.
    + pose proof (defs_has_kind Vks Found) as Kind. inversion Kind; assumption.
Qed.

Local Lemma invert_read_typing (m : Mode) G Go e x a R :
  @ty_trm m G Go e (trm_read (avar_f x) a) R ->
  exists S T V,
    @ty_var m G objctx_empty e x (typ_rcd (dec_fld a S T)) /\
    @viewpoint_adapt m x G objctx_empty e T V /\ @subtyp m G objctx_empty e V R.
Proof.
  intro H. remember (trm_read (avar_f x) a) as w eqn:Eq in H.
  induction H; inversion Eq; subst.
  - eexists _, _, _. repeat split; try eassumption. apply subtyp_refl.
  - destruct (IHty_trm eq_refl) as [S [V [W [Receiver [Adapt Sub]]]]].
    exists S, V, W. repeat split; try eassumption. eapply subtyp_trans; eassumption.
Qed.

Local Lemma mutable_location_has_marker (m : Mode) Ty :
  mode_viewpoint_adaptation' m = mode_viewpoint_adapt_mutability ->
  @inert_typ m Ty v_loc -> exists R, Ty = typ_objref R (typ_mut_marker typ_bot).
Proof.
  intros Adapt Inert. inversion Inert; subst.
  - destruct m; simpl in *; congruence.
  - assert (mode_refcaps' m = mode_refcaps_mutability) as Caps
      by (destruct m; simpl in *; congruence).
    match goal with
    | H : @refcap_inert_type _ _ v_loc |- _ =>
      unfold refcap_inert_type in H; rewrite Caps in H; inversion H; subst
    end.
    eauto.
Qed.

Local Lemma adapted_alias_read_type (m : Mode) G e x w Ty T V :
  @inert_typ m Ty v_loc ->
  ctx_binds w Ty G ->
  @ty_var m G objctx_empty e w T ->
  @viewpoint_adapt m x G objctx_empty e T V ->
  @ty_var m G objctx_empty e w V.
Proof.
  intros Loc Binding Typed Adapt.
  unfold viewpoint_adapt in Adapt.
  destruct (mode_viewpoint_adaptation' m) eqn:Mode'; [now subst V|].
  inversion Adapt; subst.
  apply ty_var_and.
  - eapply ty_var_sub; [exact Typed|eapply incapacitation_widens; eassumption].
  - destruct (mutable_location_has_marker Mode' Loc) as [R ->].
    eapply ty_var_sub; [apply ty_var_var, Binding|].
    eapply subtyp_trans; [apply subtyp_and12|].
    apply subtyp_typ; intros; apply subtyp_bot.
Qed.

Lemma configuration_read_preservation (m : Mode) G x a fs s e Lv U loc ptr w ds :
  running_config_typed m G (trm_read (avar_f x) a; fs; s; e; Lv) U ->
  fresh_in_config (w :: nil) (trm_read (avar_f x) a; fs; s; e; Lv) ->
  w §# G -> w \notin ctx_fv G ->
  binds x loc e -> binds loc (item_obj ds) s -> defs_has ds (def_fld a (avar_f ptr)) ->
  exists Ty, running_config_typed m (G § w / v_ref ~ Ty)
    (trm_var (avar_f w); fs; s; e & w ~ ptr;
      fv_config (trm_read (avar_f x) a; fs; s; e; Lv)) U.
Proof.
  intros Typed [FreshW _] FreshG FreshTypes ReceiverBinding ObjectLookup FieldLookup.
  inversion Typed as [G0 e0 fs0 s0 Lv0 t0 T U0
    Inert Heap StackTyped FreeStack TermTyped FreeTerm Closed];
    subst.
  destruct (invert_read_typing TermTyped) as [S [W [V [Receiver [Adapt Return]]]]].
  pose proof (FreeTerm x (tfree_trm_read x a)) as ReceiverKind.
  destruct (runtime_field_bounds Inert Heap Receiver ReceiverKind)
    as [y [ds0 [p [R [C [FieldType [Binding [Obj [Found [Bound [Member [Lower Upper]]]]]]]]]]]].
  assert (y = loc) by (eapply binds_unique; eassumption). subst y.
  pose proof (binds_unique Obj ObjectLookup) as EqObj. injection EqObj as ->.
  assert (p = ptr).
  { unfold defs_has in *. simpl in Found, FieldLookup. congruence. }
  subst p.
  destruct (stored_field_typing Heap Bound ObjectLookup Member FieldLookup)
    as [Stored [Ty [P PtrKind]]].
  pose proof (ctx_kind_binds PtrKind) as PtrBound.
  destruct (inert_context_lookup Inert PtrBound) as [k [Q [_ [TyInert Kind]]]].
  pose proof (ctx_kind_unique Kind PtrKind) as Ek. subst k.
  destruct (location_type_for_reference TyInert) as [NewInert TyCorr].
  assert (FreshTy : w \notin fv Ty).
  { intro H. apply FreshTypes. eapply ctx_type_free_vars; eassumption. }
  assert (FreshE : w # e).
  { intro H. apply FreshW. repeat rewrite in_union; tauto. }
  exists Ty.
  assert (Incl := @includes_fresh_binding G w v_ref Ty FreshG).
  assert (Vis := @includes_fresh_binding_visibility G w v_ref Ty FreshG).
  assert (Env := includes_fresh_alias ptr FreshE).
  assert (TypedW : @ty_var m (G § w / v_ref ~ Ty) objctx_empty (e & w ~ ptr) w W).
  { eapply alias_variable_typing with (x:=ptr).
    - eapply transport_variable; [eapply ty_var_sub; eassumption|exact Incl|exact Env].
    - apply tyq_var_sym, tyq_var_binds, binds_push_eq.
    - intros X BindingX.
      assert (Ty = X) by (eapply ctx_bind_unique; [apply Incl, PtrBound|exact BindingX]).
      subst X. apply ty_var_var. constructor. }
  apply (running_config_c (T:=T)); try assumption.
  - now apply inert_push; [|constructor| | | |].
  - eapply extend_heap_with_reference; eassumption.
  - eapply transport_stack; eassumption.
  - now apply fresh_binding_stack_tfree.
  - eapply ty_trm_sub.
    + apply ty_trm_var.
      * intros _. constructor.
      * eapply adapted_alias_read_type; [exact TyInert|constructor|exact TypedW|].
        eapply transport_adaptation; eassumption.
    + eapply transport_subtype; eassumption.
  - intros v Free. inversion Free; subst.
    exists Ty, G. constructor.
  - inversion Closed; subst. constructor; try assumption. intros n v. reflexivity.
Qed.

Local Definition rename_avar (f : var -> var) (a : avar) :=
  match a with
  | avar_b n => avar_b n
  | avar_f x => avar_f (f x)
  end.

Fixpoint rename_typ (f : var -> var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (rename_dec f D)
  | typ_and T1 T2  => typ_and (rename_typ f T1) (rename_typ f T2)
  | typ_or T1 T2  => typ_or (rename_typ f T1) (rename_typ f T2)
  | typ_sel x L y    => typ_sel (rename_avar f x) L (rename_avar f y)
  | typ_bnd T      => typ_bnd (rename_typ f T)
  | typ_fun T U    => typ_fun (rename_typ f T) (rename_typ f U)
  | typ_nocap => typ_nocap
  end with
rename_dec (f : var -> var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (rename_typ f T) (rename_typ f U)
  | dec_fld L T U => dec_fld L (rename_typ f T) (rename_typ f U)
  | dec_met m TC TZ TR => dec_met m (rename_typ f TC) (rename_typ f TZ) (rename_typ f TR)
  end.

Fixpoint rename_trm (f : var -> var) (t: trm) : trm :=
  match t with
  | trm_var x        => trm_var (rename_avar f x)
  | trm_read x1 L     => trm_read (rename_avar f x1) L
  | trm_apply x1 x2    => trm_apply (rename_avar f x1) (rename_avar f x2)
  | trm_let t1 t2    => trm_let (rename_trm f t1) (rename_trm f t2)
  | trm_lit l t      => trm_lit (rename_lit f l) (rename_trm f t)
  | trm_write x1 L x2  => trm_write (rename_avar f x1) L (rename_avar f x2)
  | trm_call x1 L x2  => trm_call (rename_avar f x1) L (rename_avar f x2)
  end with
rename_lit (f : var -> var) (l: lit) : lit :=
  match l with
  | lit_fun T t   => lit_fun (rename_typ f T) (rename_trm f t)
  | lit_obj T ds =>
    lit_obj (rename_typ f T)
            (rename_defs f ds)
  end with
rename_def (f : var -> var) (d: def) : def :=
  match d with
  | def_typ l t => def_typ l (rename_typ f t)
  | def_fld l v => def_fld l (rename_avar f v)
  | def_met l t => def_met l (rename_trm f t)
  end with
rename_defs (f : var -> var) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons rest d => defs_cons (rename_defs f rest) (rename_def f d)
  end.

Local Lemma rename_avar_open f (a : avar) n x :
  rename_avar f (open_rec n x a) = open_rec n (f x) (rename_avar f a).
Proof.
  destruct a; cbn; [|reflexivity].
  destruct (classic (n = n0)) as [Eq|Neq].
  - now rewrite !If_l by assumption.
  - now rewrite !If_r by assumption.
Qed.

Local Lemma rename_type_open :
  (forall (T : typ) f n x, rename_typ f (open_rec n x T) = open_rec n (f x) (rename_typ f T)) /\
  (forall (D : dec) f n x, rename_dec f (open_rec n x D) = open_rec n (f x) (rename_dec f D)).
Proof.
  apply typ_mutind; intros; cbn; f_equal; eauto using rename_avar_open.
Qed.

Local Lemma rename_term_open :
  (forall (t : trm) f n x, rename_trm f (open_rec n x t) = open_rec n (f x) (rename_trm f t)) /\
  (forall (l : lit) f n x, rename_lit f (open_rec n x l) = open_rec n (f x) (rename_lit f l)) /\
  (forall (d : def) f n x, rename_def f (open_rec n x d) = open_rec n (f x) (rename_def f d)) /\
  (forall (ds : defs) f n x, rename_defs f (open_rec n x ds) = open_rec n (f x) (rename_defs f ds)).
Proof.
  destruct rename_type_open as [OpenType _].
  apply trm_mutind; intros; cbn; f_equal; eauto using rename_avar_open.
Qed.

Local Lemma rename_avar_ext (a : avar) f g :
  (forall x, x \in fv a -> f x = g x) -> rename_avar f a = rename_avar g a.
Proof.
  intros Eq. destruct a; simpl; [reflexivity|].
  f_equal. apply Eq, in_singleton_self.
Qed.

Local Ltac agreement_at_subterm :=
  intros v Present;
  multimatch goal with
  | Eq : forall u : var, _ -> _ = _ |- _ =>
      solve [apply Eq; simpl; repeat rewrite in_union; tauto]
  end.

Local Ltac rename_agree :=
  first [reflexivity | solve [eapply rename_avar_ext; agreement_at_subterm] |
    multimatch goal with
    | IH : forall f g, _ -> _ = _ |- _ =>
      solve [eapply IH; agreement_at_subterm]
    end].

Local Lemma rename_type_ext :
  (forall (T : typ) f g, (forall x, x \in fv T -> f x = g x) -> rename_typ f T = rename_typ g T) /\
  (forall (D : dec) f g, (forall x, x \in fv D -> f x = g x) -> rename_dec f D = rename_dec g D).
Proof.
  apply typ_mutind; intros;
    cbn; f_equal; rename_agree.
Qed.

Local Lemma rename_term_ext :
  (forall (t : trm) f g, (forall x, x \in fv t -> f x = g x) -> rename_trm f t = rename_trm g t) /\
  (forall (l : lit) f g, (forall x, x \in fv l -> f x = g x) -> rename_lit f l = rename_lit g l) /\
  (forall (d : def) f g, (forall x, x \in fv d -> f x = g x) -> rename_def f d = rename_def g d) /\
  (forall (ds : defs) f g, (forall x, x \in fv ds -> f x = g x) -> rename_defs f ds = rename_defs g ds).
Proof.
  destruct rename_type_ext as [TypeExt _].
  apply trm_mutind; intros;
    cbn; f_equal; first [rename_agree | eapply TypeExt; agreement_at_subterm].
Qed.

Local Lemma rename_type_id :
  (forall T, rename_typ (fun x => x) T = T) /\
  (forall D, rename_dec (fun x => x) D = D).
Proof.
  apply typ_mutind; intros; cbn; f_equal; auto;
    match goal with |- rename_avar _ ?a = _ => destruct a; reflexivity end.
Qed.

Local Lemma rename_term_id :
  (forall t, rename_trm (fun x => x) t = t) /\
  (forall l, rename_lit (fun x => x) l = l) /\
  (forall d, rename_def (fun x => x) d = d) /\
  (forall ds, rename_defs (fun x => x) ds = ds).
Proof.
  destruct rename_type_id as [TyId _].
  apply trm_mutind; intros; cbn; f_equal; auto;
    match goal with |- rename_avar _ ?a = _ => destruct a; reflexivity end.
Qed.

Local Definition rename_point (f : var -> var) (x y : var) z :=
  If z = x then y else f z.

Local Lemma rename_point_same f x y :
  rename_point f x y x = y.
Proof. unfold rename_point. now rewrite If_l by reflexivity. Qed.

Local Lemma rename_point_other f x y z :
  z <> x -> rename_point f x y z = f z.
Proof. intros Distinct. unfold rename_point. now rewrite If_r. Qed.

Local Lemma rename_typ_point_fresh (T : typ) f x y :
  x \notin fv T -> rename_typ (rename_point f x y) T = rename_typ f T.
Proof.
  intros Fresh. eapply (proj1 rename_type_ext).
  intros z Present. apply rename_point_other. intros ->. contradiction.
Qed.

Local Definition renames_environment f (e e' : renv) :=
  forall x y, binds x y e -> tyq_var e' (f x) (f y).

Local Lemma environment_footprint (e : renv) :
  exists L : vars, forall x y, binds x y e -> x \in L /\ y \in L.
Proof.
  induction e as [|e x y IH] using env_ind.
  - exists (\{} : vars). intros v z H. exfalso. eapply binds_empty_inv; eassumption.
  - destruct IH as [L Foot]. exists (\{x} \u (\{y} \u L)).
    intros v z Bound. destruct (binds_push_inv Bound) as [[-> ->] | [_ Earlier]].
    + rewrite !in_union. auto using in_singleton_self.
    + specialize (Foot _ _ Earlier). rewrite !in_union. tauto.
Qed.

Local Lemma rename_environment_override f e e' x y L :
  renames_environment f e e' ->
  (forall a b, binds a b e -> a \in L /\ b \in L) ->
  x \notin L ->
  renames_environment (rename_point f x y) e e'.
Proof.
  intros Env Foot Fresh a b Bound.
  destruct (Foot _ _ Bound) as [FA FB].
  rewrite !rename_point_other by congruence.
  now apply Env.
Qed.

Local Lemma rename_var_equiv e x y :
  tyq_var e x y -> forall f e', renames_environment f e e' -> tyq_var e' (f x) (f y).
Proof.
  induction 1; intros f e' Env.
  - apply tyq_var_refl.
  - apply Env. assumption.
  - apply tyq_var_sym. now apply IHtyq_var.
  - eapply tyq_var_trans with (v2:=f v2); [apply IHtyq_var|apply IHtyq_var0]; assumption.
Qed.

(* A fresh source name permits opening the renamed type at any target name. *)
Local Lemma rename_open_types_from_ih e f e' S T k w :
  renames_environment f e e' ->
  (forall z g e'', renames_environment g e e'' ->
    tyq_typ e'' (rename_typ g (open_rec k z S)) (rename_typ g (open_rec k z T))) ->
  tyq_typ e' (open_rec k w (rename_typ f S)) (open_rec k w (rename_typ f T)).
Proof.
  intros Env IH.
  destruct (environment_footprint e) as [E Foot].
  destruct (var_fresh (fv S \u (fv T \u E))) as [z Fresh].
  rewrite !notin_union in Fresh. destruct Fresh as [FS [FT FE]].
  pose proof (IH z (rename_point f z w) e'
    (@rename_environment_override f e e' z w E Env Foot FE)) as Eq.
  destruct rename_type_open as [Open _].
  rewrite !Open, rename_point_same in Eq.
  rewrite (@rename_typ_point_fresh S f z w FS), (@rename_typ_point_fresh T f z w FT) in Eq.
  exact Eq.
Qed.

Local Lemma rename_open_met_types_from_ih e f e' S T w v :
  renames_environment f e e' ->
  (forall z y g e'', renames_environment g e e'' ->
    tyq_typ e'' (rename_typ g (open_met z y S)) (rename_typ g (open_met z y T))) ->
  tyq_typ e' (open_met w v (rename_typ f S)) (open_met w v (rename_typ f T)).
Proof.
  intros Env IH.
  destruct (environment_footprint e) as [E Foot].
  destruct (var_fresh (fv S \u (fv T \u E))) as [z Fresh].
  destruct (var_fresh (fv S \u (fv T \u (E \u \{z})))) as [y Fresh'].
  rewrite !notin_union in Fresh. rewrite !notin_union in Fresh'.
  destruct Fresh as [FS [FT FE]]. destruct Fresh' as [GS [GT [GE GN]]].
  assert (z <> y) by (apply notin_singleton in GN; congruence).
  pose proof (IH z y (rename_point (rename_point f z w) y v) e'
    (@rename_environment_override _ e e' y v E
      (@rename_environment_override f e e' z w E Env Foot FE) Foot GE)) as Eq.
  destruct rename_type_open as [Open _].
  rewrite !Open, (@rename_point_other (rename_point f z w) y v z H), !rename_point_same in Eq.
  rewrite (@rename_typ_point_fresh S (rename_point f z w) y v GS),
    (@rename_typ_point_fresh T (rename_point f z w) y v GT),
    (@rename_typ_point_fresh S f z w FS), (@rename_typ_point_fresh T f z w FT) in Eq.
  exact Eq.
Qed.

Local Lemma rename_type_equiv e S T :
  tyq_typ e S T -> forall f e', renames_environment f e e' ->
    tyq_typ e' (rename_typ f S) (rename_typ f T).
Proof.
  induction 1; intros f e' Env; cbn.
  - inversion H; subst; apply tyq_typ_nulary; constructor.
  - inversion H; subst; cbn.
    + apply (tyq_typ_andor (T:=typ_and)); [constructor|apply IHtyq_typ|apply IHtyq_typ0]; assumption.
    + apply (tyq_typ_andor (T:=typ_or)); [constructor|apply IHtyq_typ|apply IHtyq_typ0]; assumption.
  - apply tyq_typ_fun.
    + now apply IHtyq_typ.
    + intros x. eapply rename_open_types_from_ih; [exact Env|exact H1].
  - apply tyq_typ_fld; [apply IHtyq_typ|apply IHtyq_typ0]; assumption.
  - apply tyq_typ_typ; intros x; eapply rename_open_types_from_ih; [exact Env|exact H0|exact Env|exact H2].
  - apply tyq_typ_sel_normal. eapply rename_var_equiv; eassumption.
  - apply tyq_typ_sel.
  - apply tyq_typ_bnd. intros x. eapply rename_open_types_from_ih; [exact Env|exact H0].
  - apply tyq_typ_met.
    + intros x. eapply rename_open_types_from_ih; [exact Env|exact H0].
    + now apply IHtyq_typ.
    + intros x y. eapply rename_open_met_types_from_ih; [exact Env|exact H3].
Qed.

Local Lemma rename_independent_bound n T :
  typ_indep_b n T -> forall f, typ_indep_b n (rename_typ f T).
Proof.
  intro H. remember (avar_b n) as a eqn:Eq in H.
  revert n Eq.
  induction H; intros k Eq f; try discriminate;
    try (injection Eq as K; subst k); try subst v; cbn.
  - inversion H; subst; apply typ_indep_nulary; constructor.
  - apply typ_indep_and; eauto.
  - apply typ_indep_or; eauto.
  - apply typ_indep_fld; eauto.
  - apply typ_indep_typ_b; eauto.
  - apply typ_indep_fun_b; eauto.
  - apply typ_indep_sel; destruct v1, v2; simpl; congruence.
  - apply typ_indep_sel_normal. destruct v2; simpl; congruence.
  - apply typ_indep_bnd_b; eauto.
  - apply typ_indep_met_b; eauto.
Qed.

Section RenamingContexts.
Context (m : Mode).

Local Definition renames_context f G G' (e' : renv) :=
  forall x T, ctx_binds x T G -> @ty_var m G' objctx_empty e' (f x) (rename_typ f T).

Local Lemma rename_context_override f G G' e' z w :
  renames_context f G G' e' ->
  z §# G -> z \notin ctx_fv G ->
  renames_context (rename_point f z w) G G' e'.
Proof.
  intros Context' FreshDom FreshTypes x T Bound.
  assert (x <> z).
  { intros ->. apply FreshDom. eapply context_binding_in_domain; eassumption. }
  assert (z \notin fv T).
  { intros Present. apply FreshTypes. eapply ctx_type_free_vars; eassumption. }
  rewrite rename_point_other, rename_typ_point_fresh by assumption.
  now apply Context'.
Qed.

Local Lemma rename_context_push f G G' e' z w k (B : typ) :
  renames_context f G G' e' ->
  z §# G -> z \notin ctx_fv G -> z \notin fv B -> w §# G' ->
  renames_context (rename_point f z w)
    (G § z / k ~ B) (G' § w / k ~ rename_typ f B) e'.
Proof.
  intros Context' FreshDom FreshTypes FreshB FreshTarget x T Bound.
  inversion Bound; subst.
  - rewrite rename_point_same, rename_typ_point_fresh by assumption.
    apply ty_var_var. constructor.
  - eapply transport_variable.
    + eapply rename_context_override; eassumption.
    + apply includes_fresh_binding. exact FreshTarget.
    + firstorder.
Qed.

Local Lemma rename_subtyping_open e (L : vars) G f G' e' S T w :
  renames_context f G G' e' -> renames_environment f e e' ->
  (forall z, z \notin L -> forall g H e'', renames_context g G H e'' ->
    renames_environment g e e'' ->
    @subtyp m H objctx_empty e'' (rename_typ g (open z S)) (rename_typ g (open z T))) ->
  @subtyp m G' objctx_empty e' (open w (rename_typ f S)) (open w (rename_typ f T)).
Proof.
  intros Context' Environment IH.
  destruct (environment_footprint e) as [E Foot].
  destruct (var_fresh (L \u (E \u (ctx_dom G \u (ctx_fv G \u (fv S \u fv T)))))) as [z Fresh].
  rewrite !notin_union in Fresh. destruct Fresh as [F1 [F2 [F3 [F4 [F5 F6]]]]].
  pose proof (IH z F1 (rename_point f z w) G' e'
    (@rename_context_override f G G' e' z w Context' F3 F4)
    (@rename_environment_override f e e' z w E Environment Foot F2)) as Sub.
  destruct rename_type_open as [Open _].
  rewrite !Open, !rename_point_same, !rename_typ_point_fresh in Sub by assumption.
  exact Sub.
Qed.

Local Lemma rename_subtyping_under_binder e (L : vars) G f G' e' B S T w :
  renames_context f G G' e' -> renames_environment f e e' -> w §# G' ->
  (forall z, z \notin L -> forall g H e'', renames_context g (G § z / v_par ~ B) H e'' ->
    renames_environment g e e'' ->
    @subtyp m H objctx_empty e'' (rename_typ g (open z S)) (rename_typ g (open z T))) ->
  @subtyp m (G' § w / v_par ~ rename_typ f B) objctx_empty e'
    (open w (rename_typ f S)) (open w (rename_typ f T)).
Proof.
  intros Context' Environment FreshTarget IH.
  destruct (environment_footprint e) as [E Foot].
  destruct (var_fresh (L \u (E \u (ctx_dom G \u (ctx_fv G \u (fv B \u (fv S \u fv T))))))) as [z Fresh].
  rewrite !notin_union in Fresh. destruct Fresh as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
  pose proof (IH z F1 (rename_point f z w) (G' § w / v_par ~ rename_typ f B) e'
    (@rename_context_push f G G' e' z w v_par B Context' F3 F4 F5 FreshTarget)
    (@rename_environment_override f e e' z w E Environment Foot F2)) as Sub.
  destruct rename_type_open as [Open _].
  rewrite !Open, !rename_point_same, !rename_typ_point_fresh in Sub by assumption.
  exact Sub.
Qed.

Local Lemma rename_subtyping_method_result e (L : vars) G f G' e' B C S T w r :
  renames_context f G G' e' -> renames_environment f e e' ->
  w §# G' -> r §# (G' § w / v_par ~ rename_typ f B) ->
  (forall z, z \notin L -> forall y, y <> z -> y \notin L ->
    forall g H e'', renames_context g (ctx_met G z B y C) H e'' ->
    renames_environment g e e'' ->
    @subtyp m H objctx_empty e'' (rename_typ g (open_met z y S)) (rename_typ g (open_met z y T))) ->
  @subtyp m (ctx_met G' w (rename_typ f B) r (rename_typ f C)) objctx_empty e'
    (open_met w r (rename_typ f S)) (open_met w r (rename_typ f T)).
Proof.
  intros Context' Environment FreshTargetZ FreshTargetY IH.
  destruct (environment_footprint e) as [E Foot].
  destruct (var_fresh (L \u (E \u (ctx_dom G \u (ctx_fv G \u (fv B \u (fv C \u (fv S \u fv T)))))))) as [z Fresh].
  rewrite !notin_union in Fresh. destruct Fresh as [F1 [F2 [F3 [F4 [F5 [F6 [F7 F8]]]]]]].
  set (P := G § z / v_par ~ B).
  set (P' := G' § w / v_par ~ rename_typ f B).
  set (g := rename_point f z w).
  assert (ContextZ : renames_context g P P' e').
  { subst P P' g. now apply rename_context_push. }
  assert (EnvZ : renames_environment g e e').
  { subst g. eapply rename_environment_override; eassumption. }
  destruct (var_fresh (L \u (E \u (\{z} \u (ctx_dom P \u (ctx_fv P \u
    (fv (open z C) \u (fv S \u fv T)))))))) as [y Fresh'].
  rewrite !notin_union in Fresh'.
  destruct Fresh' as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].
  apply notin_singleton in H3.
  set (g' := rename_point g y r).
  pose proof (IH z F1 y H3 H1 g' (P' § r / v_recv ~ rename_typ g (open z C)) e'
    (@rename_context_push g P P' e' y r v_recv (open z C) ContextZ H4 H5 H6 FreshTargetY)
    (@rename_environment_override g e e' y r E EnvZ Foot H2)) as Sub.
  destruct rename_type_open as [Open _].
  unfold g', g in Sub.
  rewrite !Open, !rename_point_same in Sub.
  rewrite (@rename_point_other (rename_point f z w) y r z ltac:(congruence)),
    !rename_point_same in Sub.
  rewrite !rename_typ_point_fresh in Sub by assumption.
  exact Sub.
Qed.
End RenamingContexts.

Local Lemma rename_bound_independence_reflect :
  (forall (T : typ) n f, typ_indep_b n (rename_typ f T) -> typ_indep_b n T) /\
  (forall (D : dec) n f, typ_indep_b n (typ_rcd (rename_dec f D)) -> typ_indep_b n (typ_rcd D)).
Proof.
  apply typ_mutind; intros; cbn in *.
  all: try solve [apply typ_indep_nulary; constructor].
  - eauto.
  - inversion H1; subst; try solve [match goal with H : typ_nulary (typ_and _ _) |- _ => inversion H end].
    apply typ_indep_and; eauto.
  - inversion H1; subst; try solve [match goal with H : typ_nulary (typ_or _ _) |- _ => inversion H end].
    apply typ_indep_or; eauto.
  - match goal with H : typ_indep _ (typ_sel _ _ _) |- _ => inversion H; subst end.
    + match goal with H : typ_nulary _ |- _ => inversion H end.
    + apply typ_indep_sel; destruct a, a0; simpl in *; congruence.
    + apply typ_indep_sel_normal. destruct a0; simpl in *; congruence.
  - match goal with H : typ_indep _ (typ_bnd _) |- _ => inversion H; subst end.
    + match goal with H : typ_nulary _ |- _ => inversion H end.
    + apply typ_indep_bnd_b; eauto.
  - match goal with H : typ_indep _ (typ_fun _ _) |- _ => inversion H; subst end.
    + match goal with H : typ_nulary _ |- _ => inversion H end.
    + apply typ_indep_fun_b; eauto.
  - match goal with H : typ_indep _ (typ_rcd (dec_typ _ _ _)) |- _ => inversion H; subst end.
    + match goal with H : typ_nulary _ |- _ => inversion H end.
    + apply typ_indep_typ_b; eauto.
  - match goal with H : typ_indep _ (typ_rcd (dec_fld _ _ _)) |- _ => inversion H; subst end.
    + match goal with H : typ_nulary _ |- _ => inversion H end.
    + apply typ_indep_fld; eauto.
  - match goal with H : typ_indep _ (typ_rcd (dec_met _ _ _ _)) |- _ => inversion H; subst end.
    + match goal with H : typ_nulary _ |- _ => inversion H end.
    + apply typ_indep_met_b; eauto.
Qed.

Section StaticRenaming.
Context (m : Mode).

Local Ltac renaming_premise :=
  first [assumption
    | solve [eapply rename_independent_bound; eassumption]
    | solve [eapply rename_type_equiv; eassumption]
    | multimatch goal with
      | H : forall _ : var -> var, _ |- _ => solve [eapply H; assumption]
      | H : _ -> forall _ : var -> var, _ |- _ => solve [eapply H; assumption]
      | C : renames_context _ _ _ _ _, H : ctx_binds _ _ _ |- _ =>
        exact (C _ _ H)
      end].

Local Lemma rename_static :
  (forall G Go e x T, @ty_var m G Go e x T ->
    forall f G' e', renames_context m f G G' e' -> renames_environment f e e' ->
    @ty_var m G' Go e' (f x) (rename_typ f T)) /\
  (forall G Go e S T, @subtyp m G Go e S T ->
    forall f G' e', renames_context m f G G' e' -> renames_environment f e e' ->
    @subtyp m G' Go e' (rename_typ f S) (rename_typ f T)) /\
  (forall G Go e S T, @ty_incap m G Go e S T ->
    forall f G' e', renames_context m f G G' e' -> renames_environment f e e' ->
    @ty_incap m G' Go e' (rename_typ f S) (rename_typ f T)).
Proof.
  destruct rename_type_open as [Open _].
  apply ts_mutind; intros; cbn.
  all: try first
    [ solve [renaming_premise]
    | solve [econstructor; renaming_premise]
    | solve [eapply ty_var_and; renaming_premise]
    | solve [eapply ty_var_sub; renaming_premise]
    | solve [eapply ty_var_mut_top; renaming_premise]
    | solve [eapply subtyp_trans; renaming_premise]
    | solve [eapply subtyp_and2; renaming_premise]
    | solve [eapply subtyp_or2; renaming_premise]
    | solve [eapply subtyp_fld; renaming_premise]
    | solve [eapply subtyp_tyq; renaming_premise]
    | solve [eapply ty_incap_and; renaming_premise]
    | solve [eapply ty_incap_or; renaming_premise]
    | solve [eapply ty_incap_nocap; renaming_premise] ].
  - apply ty_rec_intro.
    + rewrite <- Open. renaming_premise.
    + renaming_premise.
    + intros Mode'. rewrite <- !Open. renaming_premise.
  - rewrite Open. apply ty_rec_elim; renaming_premise.
  - apply subtyp_typ; intros w.
    + eapply rename_subtyping_open with (L:=(\{} : vars)); try eassumption.
      intros z _. apply H.
    + eapply rename_subtyping_open with (L:=(\{} : vars)); try eassumption.
      intros z _. apply H0.
  - rewrite Open. eapply subtyp_sel2. renaming_premise.
  - rewrite Open. eapply subtyp_sel1. renaming_premise.
  - eapply subtyp_fun with (L:=ctx_dom G'); try renaming_premise.
    intros w Fresh. eapply rename_subtyping_under_binder; eassumption.
  - eapply subtyp_met with (L:=ctx_dom G'); try renaming_premise.
    + intros w Fresh. eapply rename_subtyping_under_binder; eassumption.
    + intros SeF Indep. apply rename_independent_bound, t; [exact SeF|].
      eapply (proj1 rename_bound_independence_reflect). exact Indep.
    + intros w Fresh r Distinct Fresh'. eapply rename_subtyping_method_result;
        try eassumption.
      simpl. rewrite notin_union, notin_singleton. auto.
  - eapply ty_incap_sel.
    + renaming_premise.
    + rewrite <- Open. renaming_premise.
Qed.

Local Lemma rename_variable G Go e x T f G' e' :
  @ty_var m G Go e x T ->
  renames_context m f G G' e' -> renames_environment f e e' ->
  @ty_var m G' Go e' (f x) (rename_typ f T).
Proof. intro H. exact ((proj1 rename_static) G Go e x T H f G' e'). Qed.

Local Lemma rename_subtype G Go e S T f G' e' :
  @subtyp m G Go e S T ->
  renames_context m f G G' e' -> renames_environment f e e' ->
  @subtyp m G' Go e' (rename_typ f S) (rename_typ f T).
Proof. intro H. exact ((proj1 (proj2 rename_static)) G Go e S T H f G' e'). Qed.

Local Lemma rename_incap G Go e S T f G' e' :
  @ty_incap m G Go e S T ->
  renames_context m f G G' e' -> renames_environment f e e' ->
  @ty_incap m G' Go e' (rename_typ f S) (rename_typ f T).
Proof. intro H. exact ((proj2 (proj2 rename_static)) G Go e S T H f G' e'). Qed.
End StaticRenaming.

Local Definition renames_visibility f G G' :=
  forall x, ctx_vis G x -> ctx_vis G' (f x).

Local Lemma context_vis_domain G x :
  ctx_vis G x -> x \in ctx_dom G.
Proof. induction 1; simpl; rewrite in_union; auto using in_singleton_self. Qed.

Local Lemma rename_push_visibility f G G' x k B :
  renames_visibility f G G' -> (f x) §# G' ->
  renames_visibility f (G § x / k ~ B) (G' § f x / k ~ rename_typ f B).
Proof.
  intros Visible Fresh y H. inversion H; subst; [constructor|].
  apply ctx_vis_n.
  - intro Eq. apply Fresh. rewrite <- Eq. eapply context_vis_domain, Visible; eassumption.
  - now apply Visible.
Qed.

Local Lemma rename_override_visibility f G G' z w :
  renames_visibility f G G' -> z §# G ->
  renames_visibility (rename_point f z w) G G'.
Proof.
  intros Vis Fresh x Source.
  rewrite rename_point_other; [now apply Vis|].
  intros ->. apply Fresh. now apply context_vis_domain.
Qed.

Local Lemma rename_binder_visibility f G G' z w k B :
  renames_visibility f G G' -> z §# G -> w §# G' -> z \notin fv B ->
  renames_visibility (rename_point f z w)
    (G § z / k ~ B) (G' § w / k ~ rename_typ f B).
Proof.
  intros Vis Source Target Ty.
  pose proof (@rename_push_visibility (rename_point f z w) G G' z k B
    (@rename_override_visibility f G G' z w Vis Source)
    ltac:(now rewrite rename_point_same)) as Extend.
  rewrite rename_point_same, rename_typ_point_fresh in Extend by assumption.
  exact Extend.
Qed.

Local Definition rename_object f Go :=
  match Go with
  | objctx_empty => objctx_empty
  | objctx_lit x T => objctx_lit (f x) (rename_typ f T)
  | objctx_heap x T => objctx_heap (f x) (rename_typ f T)
  end.

Local Definition object_fresh_in_target f Go G' :=
  match Go with
  | objctx_lit x _ => (f x) §# G'
  | _ => True
  end.

Local Lemma object_renaming_context (m : Mode) f G Go G' e' :
  renames_context m f G G' e' -> object_fresh_in_target f Go G' ->
  renames_context m f (ctx_obj G Go) (ctx_obj G' (rename_object f Go)) e'.
Proof.
  destruct Go; simpl; intros Rel Fresh; try assumption.
  intros y U Bound. inversion Bound; subst.
  - destruct rename_type_open as [Open _].
    rewrite Open. apply ty_var_var. constructor.
  - eapply transport_variable; [now apply Rel| |firstorder].
    now apply includes_fresh_binding.
Qed.

Local Lemma object_renaming_visibility f G Go G' :
  renames_visibility f G G' -> object_fresh_in_target f Go G' ->
  renames_visibility f (ctx_obj G Go) (ctx_obj G' (rename_object f Go)).
Proof.
  destruct Go; simpl; intros Rel Fresh; try assumption.
  destruct rename_type_open as [Open _].
  rewrite <- Open. now apply rename_push_visibility.
Qed.

Local Lemma hidden_renaming_context (m : Mode) f G G' e' :
  renames_context m f G G' e' ->
  renames_context m f (ctx_hide G) (ctx_hide G') e'.
Proof.
  intros Rel x T Bound. inversion Bound; subst.
  eapply transport_variable; [apply Rel; eassumption| |firstorder].
  intros z U H. now apply ctx_binds_hide.
Qed.

Local Lemma hidden_renaming_visibility f G G' :
  renames_visibility f (ctx_hide G) (ctx_hide G').
Proof. intros x H. inversion H. Qed.

Local Definition method_base m G Go := vis_hide m (ctx_obj G Go).

Local Definition method_receiver Go z r TC :=
  match Go with
  | objctx_empty => open z TC
  | objctx_lit y T | objctx_heap y T =>
      typ_and (open z TC) (typ_and (open y T) (open r T))
  end.

Local Lemma method_context_explicit m G Go z r TZ TC :
  ctx_obj_met m G Go z TZ r TC =
  (method_base m G Go § z / v_par ~ TZ § r / v_recv ~ method_receiver Go z r TC).
Proof. destruct Go; reflexivity. Qed.

Local Lemma method_receiver_renamed f Go z r TC :
  rename_typ f (method_receiver Go z r TC) =
  method_receiver (rename_object f Go) (f z) (f r) (rename_typ f TC).
Proof.
  destruct rename_type_open as [Open _].
  destruct Go; cbn; now rewrite !Open.
Qed.

Local Lemma method_base_renames m f G Go G' e' :
  renames_context m f G G' e' ->
  renames_visibility f G G' ->
  object_fresh_in_target f Go G' ->
  renames_context m f (method_base m G Go) (method_base m G' (rename_object f Go)) e' /\
  renames_visibility f (method_base m G Go) (method_base m G' (rename_object f Go)).
Proof.
  intros Incl Vis Fresh. unfold method_base.
  destruct (mode_visibility' m); split;
    eauto using object_renaming_context, object_renaming_visibility,
      hidden_renaming_context, hidden_renaming_visibility.
Qed.

Local Lemma object_rename_point_fresh Go f z w :
  z \notin objctx_fv Go -> z \notin objctx_dom Go ->
  rename_object (rename_point f z w) Go = rename_object f Go.
Proof.
  intros FV Dom.
  destruct Go; simpl in *; [reflexivity| |].
  - f_equal.
    + apply rename_point_other. intros ->. apply Dom, in_singleton_self.
    + now apply rename_typ_point_fresh.
  - rewrite notin_union in FV. destruct FV as [Name Fresh].
    f_equal.
    + apply rename_point_other. intros ->. apply Name, in_singleton_self.
    + now apply rename_typ_point_fresh.
Qed.

Local Lemma rename_capbnd (m : Mode) c G Go e S T :
  @ty_capbnd m c G Go e S T ->
  forall f G' e', renames_context m f G G' e' -> renames_environment f e e' ->
  @ty_capbnd m c G' Go e' (rename_typ f S) (rename_typ f T).
Proof.
  destruct rename_type_open as [Open _].
  induction 1; intros; simpl; try solve [econstructor; try (apply IHty_capbnd1 || apply IHty_capbnd2); assumption].
  - eapply ty_capbnd_sel.
    + exact (@rename_variable m G objctx_empty e x (typ_rcd (dec_typ B S T)) f G' e' H H1 H2).
    + rewrite <- Open. now apply IHty_capbnd.
  - apply ty_capbnd_and; [apply IHty_capbnd|apply IHty_capbnd0]; assumption.
  - apply ty_capbnd_or; [apply IHty_capbnd|apply IHty_capbnd0]; assumption.
Qed.

Local Lemma rename_adaptation (m : Mode) G Go e x T U f G' e' :
  @viewpoint_adapt m x G Go e T U ->
  renames_context m f G G' e' -> renames_environment f e e' ->
  @viewpoint_adapt m (f x) G' Go e' (rename_typ f T) (rename_typ f U).
Proof.
  unfold viewpoint_adapt. destruct (mode_viewpoint_adaptation' m); [congruence|].
  intros Adapt Rel Env. inversion Adapt; subst; cbn.
  econstructor; [eapply rename_incap|eapply rename_capbnd]; eassumption.
Qed.

Local Lemma rename_hasnt ds l f :
  defs_hasnt ds l -> defs_hasnt (rename_defs f ds) l.
Proof.
  unfold defs_hasnt.
  induction ds as [|ds IH d]; simpl; auto.
  assert (label_of (rename_def f d) = label_of d) as Label by (destruct d; reflexivity).
  rewrite Label.
  intros Absent. destruct (classic (label_of d = l)) as [Eq|Neq].
  - rewrite If_l in Absent by exact Eq. discriminate.
  - rewrite If_r in * by exact Neq. auto.
Qed.

Local Definition binder_result (depends : bool) z (U : typ) :=
  if depends then open z U else U.

Local Lemma rename_binder_result depends g z U :
  rename_typ g (binder_result depends z U) =
  binder_result depends (g z) (rename_typ g U).
Proof. destruct depends; unfold binder_result; [apply (proj1 rename_type_open)|reflexivity]. Qed.

Local Lemma rename_context_push_exact (m : Mode) f G G' e' z w k (B : typ) :
  renames_context m f G G' e' ->
  z §# G -> z \notin ctx_fv G -> w §# G' ->
  renames_context m (rename_point f z w)
    (G § z / k ~ B) (G' § w / k ~ rename_typ (rename_point f z w) B) e'.
Proof.
  intros Context' FreshDom FreshTypes FreshTarget x T Bound.
  inversion Bound; subst.
  - rewrite rename_point_same. apply ty_var_var. constructor.
  - eapply transport_variable.
    + eapply rename_context_override; eassumption.
    + apply includes_fresh_binding. exact FreshTarget.
    + firstorder.
Qed.

Local Lemma rename_binder_visibility_exact f G G' z w k B :
  renames_visibility f G G' -> z §# G -> w §# G' ->
  renames_visibility (rename_point f z w)
    (G § z / k ~ B) (G' § w / k ~ rename_typ (rename_point f z w) B).
Proof.
  intros Vis Source Target.
  pose proof (@rename_push_visibility (rename_point f z w) G G' z k B
    (@rename_override_visibility f G G' z w Vis Source)
    ltac:(now rewrite rename_point_same)) as Extend.
  now rewrite rename_point_same in Extend.
Qed.

Section RenameBodies.
Context (m : Mode).

Local Lemma rename_term_under_binder e (L : vars) G f G' e' k B t U depends w :
  renames_context m f G G' e' -> renames_visibility f G G' ->
  renames_environment f e e' -> w §# G' ->
  (forall z, z \notin L -> forall g H e'',
    renames_context m g (G § z / k ~ B) H e'' ->
    renames_visibility g (G § z / k ~ B) H ->
    renames_environment g e e'' ->
    @ty_trm m H objctx_empty e'' (rename_trm g (open z t)) (rename_typ g (binder_result depends z U))) ->
  @ty_trm m (G' § w / k ~ rename_typ f B) objctx_empty e'
    (open w (rename_trm f t)) (binder_result depends w (rename_typ f U)).
Proof.
  intros Context' Visibility Environment FreshTarget IH.
  destruct (environment_footprint e) as [E Foot].
  destruct (var_fresh (L \u (E \u (ctx_dom G \u (ctx_fv G \u (fv B \u (fv U \u fv t))))))) as [z Fresh].
  rewrite !notin_union in Fresh. destruct Fresh as [F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]].
  pose proof (IH z F1 (rename_point f z w) (G' § w / k ~ rename_typ f B) e'
    (@rename_context_push m f G G' e' z w k B Context' F3 F4 F5 FreshTarget)
    (@rename_binder_visibility f G G' z w k B Visibility F3 FreshTarget F5)
    (@rename_environment_override f e e' z w E Environment Foot F2)) as Body.
  rewrite (proj1 rename_term_open), rename_binder_result, !rename_point_same,
    rename_typ_point_fresh in Body by assumption.
  assert (rename_trm (rename_point f z w) t = rename_trm f t) as Eq.
  { eapply (proj1 rename_term_ext). intros v Present.
    apply rename_point_other. intros ->. contradiction. }
  now rewrite Eq in Body.
Qed.

Local Lemma rename_term_under_method e (L : vars) G Go f G' e' B C (t : trm) U w r :
  renames_context m f G G' e' -> renames_visibility f G G' ->
  renames_environment f e e' -> object_fresh_in_target f Go G' ->
  w §# method_base m G' (rename_object f Go) ->
  r §# (method_base m G' (rename_object f Go) § w / v_par ~ rename_typ f B) ->
  (forall z, z \notin L -> forall y, y <> z -> y \notin L -> forall g H e'',
    renames_context m g (ctx_obj_met m G Go z B y C) H e'' ->
    renames_visibility g (ctx_obj_met m G Go z B y C) H ->
    renames_environment g e e'' ->
    @ty_trm m H objctx_empty e'' (rename_trm g (open_met z y t))
      (rename_typ g (open_met z y U))) ->
  @ty_trm m (ctx_obj_met m G' (rename_object f Go) w (rename_typ f B) r (rename_typ f C))
    objctx_empty e' (open_met w r (rename_trm f t)) (open_met w r (rename_typ f U)).
Proof.
  intros Context' Visibility Environment FG FW FR IH.
  destruct (@method_base_renames m f G Go G' e' Context' Visibility FG) as [Scope VScope].
  set (A := method_base m G Go) in *.
  set (A' := method_base m G' (rename_object f Go)) in *.
  destruct (environment_footprint e) as [E Foot].
  set (Avoid := L \u (E \u (objctx_dom Go \u (objctx_fv Go \u (fv C \u (fv t \u fv U)))))).
  destruct (var_fresh (Avoid \u (ctx_dom A \u (ctx_fv A \u fv B)))) as [z Fresh].
  unfold Avoid in Fresh. rewrite !notin_union in Fresh.
  destruct Fresh as [[F1 [F2 [F3 [F4 [F5 [F6 F7]]]]]] [FD [FV FB]]].
  set (P := A § z / v_par ~ B).
  set (P' := A' § w / v_par ~ rename_typ f B).
  set (g := rename_point f z w).
  assert (ScopeZ : renames_context m g P P' e')
    by (subst g P P'; now apply rename_context_push).
  assert (VisibleZ : renames_visibility g P P')
    by (subst g P P'; now apply rename_binder_visibility).
  assert (EnvZ : renames_environment g e e')
    by (subst g; eapply rename_environment_override; eassumption).
  destruct (var_fresh (Avoid \u (\{z} \u (ctx_dom P \u ctx_fv P)))) as [y Fresh'].
  unfold Avoid in Fresh'. rewrite !notin_union in Fresh'.
  destruct Fresh' as [[Y1 [Y2 [Y3 [Y4 [Y5 [Y6 Y7]]]]]] [YD [YP YV]]].
  apply notin_singleton in YD.
  set (g' := rename_point g y r).
  set (Brecv := method_receiver Go z y C).
  assert (RecvScope : renames_context m g' (ctx_obj_met m G Go z B y C)
    (P' § r / v_recv ~ rename_typ g' Brecv) e').
  { rewrite method_context_explicit. subst g' Brecv P. now apply rename_context_push_exact. }
  assert (RecvVis : renames_visibility g' (ctx_obj_met m G Go z B y C)
    (P' § r / v_recv ~ rename_typ g' Brecv)).
  { rewrite method_context_explicit. subst g' Brecv P. now apply rename_binder_visibility_exact. }
  assert (RecvEnv : renames_environment g' e e')
    by (subst g'; eapply rename_environment_override; eassumption).
  pose proof (IH z F1 y YD Y1 g' _ e' RecvScope RecvVis RecvEnv) as Body.
  assert (RenameG : rename_object g' Go = rename_object f Go).
  { subst g' g. now rewrite !object_rename_point_fresh. }
  assert (RenameT : rename_trm g' t = rename_trm f t).
  { subst g' g. apply (proj1 rename_term_ext). intros v InT.
    rewrite !rename_point_other by (intros ->; contradiction). reflexivity. }
  assert (RenameZ : g' z = w).
  { subst g' g. rewrite rename_point_other by congruence. apply rename_point_same. }
  assert (RenameR : g' y = r) by (subst g'; apply rename_point_same).
  rewrite !(proj1 rename_term_open), !(proj1 rename_type_open) in Body.
  unfold Brecv in Body. rewrite method_receiver_renamed in Body.
  rewrite RenameG, RenameT, RenameZ, RenameR in Body.
  subst g' g. rewrite !rename_typ_point_fresh in Body by assumption.
  rewrite method_context_explicit. exact Body.
Qed.
End RenameBodies.

Local Lemma rename_typ_object (m : Mode) f T :
  rename_typ f (typ_objlit m T) = typ_objlit m (rename_typ f T).
Proof. destruct (mode_objlit_refcaps' m); reflexivity. Qed.

Local Lemma rename_equivalent_open_cofinite (L : vars) e S T f e' w :
  (forall z, z \notin L -> tyq_typ e (open z S) (open z T)) ->
  renames_environment f e e' ->
  tyq_typ e' (open w (rename_typ f S)) (open w (rename_typ f T)).
Proof.
  intros Eq Env.
  destruct (environment_footprint e) as [E Foot].
  destruct (var_fresh (L \u (fv S \u (fv T \u E)))) as [z Fresh].
  rewrite !notin_union in Fresh. destruct Fresh as [FL [FS [FT FE]]].
  pose proof (rename_type_equiv (Eq z FL)
    (@rename_environment_override f e e' z w E Env Foot FE)) as Eq'.
  rewrite !(proj1 rename_type_open), !rename_point_same, !rename_typ_point_fresh in Eq' by assumption.
  exact Eq'.
Qed.

Section RenamingSyntax.
Context (m : Mode).

Local Lemma rename_object_literal_body e (L : vars) G f G' e' ds R w :
  renames_context m f G G' e' -> renames_visibility f G G' ->
  renames_environment f e e' -> w §# G' ->
  (forall z, z \notin L -> forall g H e'',
    renames_context m g G H e'' -> renames_visibility g G H ->
    renames_environment g e e'' -> object_fresh_in_target g (objctx_lit z R) H ->
    @ty_defs m H (rename_object g (objctx_lit z R)) e''
      (rename_defs g (open z ds)) (rename_typ g (open z R))) ->
  @ty_defs m G' (objctx_lit w (rename_typ f R)) e'
    (open w (rename_defs f ds)) (open w (rename_typ f R)).
Proof.
  intros Context' Visibility Environment FreshTarget IH.
  destruct (environment_footprint e) as [E Foot].
  destruct (var_fresh (L \u (E \u (ctx_dom G \u (ctx_fv G \u (fv R \u fv ds)))))) as [z Fresh].
  rewrite !notin_union in Fresh. destruct Fresh as [F1 [F2 [F3 [F4 [F5 F6]]]]].
  assert (Target : object_fresh_in_target (rename_point f z w) (objctx_lit z R) G').
  { cbn. now rewrite rename_point_same. }
  pose proof (IH z F1 (rename_point f z w) G' e'
    (@rename_context_override m f G G' e' z w Context' F3 F4)
    (@rename_override_visibility f G G' z w Visibility F3)
    (@rename_environment_override f e e' z w E Environment Foot F2) Target) as Body.
  rewrite (proj2 (proj2 (proj2 rename_term_open))), (proj1 rename_type_open) in Body.
  cbn in Body.
  rewrite !rename_point_same, !rename_typ_point_fresh in Body by assumption.
  assert (rename_defs (rename_point f z w) ds = rename_defs f ds) as Eq.
  { apply (proj2 (proj2 (proj2 rename_term_ext))). intros v Present.
    apply rename_point_other. intros ->. contradiction. }
  now rewrite Eq in Body.
Qed.

Local Ltac solve_renamed_static :=
  first [assumption | solve [eapply rename_independent_bound; eassumption] |
    multimatch goal with
    | Rel : renames_context _ _ _ _ _, Env : renames_environment _ _ _,
      Typed : _ |- _ =>
        first [exact (rename_variable Typed Rel Env)
              |exact (rename_subtype Typed Rel Env)
              |exact (rename_adaptation Typed Rel Env)]
    end
  ].

Local Ltac solve_renamed_syntax :=
  first [solve_renamed_static
    | solve [now apply rename_hasnt]
    | multimatch goal with
      | IH : forall _ : var -> var, _ |- _ => solve [eapply IH; assumption]
      | Vis : renames_visibility _ _ _ |- _ => solve [apply Vis; auto]
      end].

Local Lemma rename_syntax :
  (forall G Go e t T, @ty_trm m G Go e t T ->
    forall f G' e', renames_context m f G G' e' -> renames_visibility f G G' ->
    renames_environment f e e' ->
    @ty_trm m G' Go e' (rename_trm f t) (rename_typ f T)) /\
  (forall G Go e l T, @ty_lit m G Go e l T ->
    forall f G' e', renames_context m f G G' e' -> renames_visibility f G G' ->
    renames_environment f e e' ->
    @ty_lit m G' Go e' (rename_lit f l) (rename_typ f T)) /\
  (forall G Go e d D, @ty_def m G Go e d D ->
    forall f G' e', renames_context m f G G' e' -> renames_visibility f G G' ->
    renames_environment f e e' -> object_fresh_in_target f Go G' ->
    @ty_def m G' (rename_object f Go) e' (rename_def f d) (rename_dec f D)) /\
  (forall G Go e ds T, @ty_defs m G Go e ds T ->
    forall f G' e', renames_context m f G G' e' -> renames_visibility f G G' ->
    renames_environment f e e' -> object_fresh_in_target f Go G' ->
    @ty_defs m G' (rename_object f Go) e' (rename_defs f ds) (rename_typ f T)).
Proof.
  destruct rename_type_open as [Open _].
  apply rules_mutind; intros.
  all: try first
    [ solve [cbn; eapply ty_trm_var; intros; solve_renamed_syntax]
    | solve [cbn; rewrite !Open; eapply ty_trm_apply; intros; solve_renamed_syntax]
    | solve [cbn; eapply ty_trm_read; intros; solve_renamed_syntax]
    | solve [cbn; rewrite !Open; eapply ty_trm_call; intros; solve_renamed_syntax]
    | solve [eapply ty_trm_sub; solve_renamed_syntax]
    | solve [cbn; eapply ty_defs_one; solve_renamed_syntax]
    | solve [cbn; eapply ty_defs_cons; solve_renamed_syntax] ].
  - cbn. eapply ty_trm_read with (S:=rename_typ f S) (T:=rename_typ f T).
    + intros Mode'. apply H0, c, Mode'.
    + exact (rename_variable o H H1).
    + exact (@rename_adaptation m G objctx_empty e x T U f G' e' v H H1).
  - cbn. eapply ty_trm_write with (S:=rename_typ f S); intros; try solve [solve_renamed_syntax].
    match goal with
    | Rel : renames_context _ _ _ _ _, Env : renames_environment _ _ _,
      Mode' : mode_has_mutability' _ = true, Typed : _ -> _ |- _ =>
        exact (rename_variable (Typed Mode') Rel Env)
    end.
  - cbn. rewrite !Open.
    eapply ty_trm_call with (TC:=rename_typ f TC) (TZ:=rename_typ f TZ);
      intros; try solve [solve_renamed_syntax | rewrite <- Open; solve_renamed_syntax].
    apply rename_independent_bound. auto.
  - cbn. eapply ty_trm_let with (L:=ctx_dom G') (T:=rename_typ f T).
    + solve_renamed_syntax.
    + intros w Fresh.
      eapply rename_term_under_binder with (depends:=false); eassumption.
  - cbn. eapply ty_trm_lit with (L:=ctx_dom G') (T:=rename_typ f T).
    + solve_renamed_syntax.
    + intros w Fresh.
      eapply rename_term_under_binder with (depends:=false); eassumption.
  - cbn. eapply ty_lit_fun with (L:=ctx_dom G'); [assumption|].
    intros w Fresh. eapply rename_term_under_binder with (depends:=true); eassumption.
  - rewrite rename_typ_object. cbn. eapply ty_lit_obj with (L:=ctx_dom G').
    + intros w Fresh. eapply rename_object_literal_body; eassumption.
    + now apply rename_independent_bound.
  - cbn. eapply ty_def_typ with (L:=(\{} : vars)).
    intros w _. eapply rename_equivalent_open_cofinite; eassumption.
  - cbn. apply ty_def_fld.
    + intros Mode'. eapply object_renaming_visibility; eauto.
    + eapply rename_variable; [eassumption|apply object_renaming_context; assumption|assumption].
  - cbn. eapply ty_def_met with (L:=ctx_dom (method_base m G' (rename_object f Go))).
    intros w Fresh r Neq Fresh'. eapply rename_term_under_method; try eassumption.
    simpl. rewrite notin_union, notin_singleton. auto.
  - cbn. eapply ty_defs_cons; try solve [solve_renamed_syntax].
    assert (label_of (rename_def f d) = label_of d) as Label by (destruct d; reflexivity).
    rewrite Label. now apply rename_hasnt.
Qed.

Local Lemma rename_term G Go e t T f G' e' :
  @ty_trm m G Go e t T ->
  renames_context m f G G' e' -> renames_visibility f G G' -> renames_environment f e e' ->
  @ty_trm m G' Go e' (rename_trm f t) (rename_typ f T).
Proof. intro H. exact ((proj1 rename_syntax) G Go e t T H f G' e'). Qed.
End RenamingSyntax.

Local Lemma instantiate_typed_body (m : Mode) (L : vars) G e B t U dep k x :
  @ty_var m G objctx_empty e x B -> ctx_vis G x ->
  (forall z, z \notin L ->
    @ty_trm m (G § z / k ~ B) objctx_empty e (open z t) (binder_result dep z U)) ->
  @ty_trm m G objctx_empty e (open x t) (binder_result dep x U).
Proof.
  intros Arg Vis Body.
  destruct (environment_footprint e) as [E Foot].
  destruct (var_fresh (L \u (E \u (ctx_dom G \u (ctx_fv G \u (fv B \u (fv U \u fv t))))))) as [z Fresh].
  rewrite !notin_union in Fresh. destruct Fresh as [FL [FE [FG [FC [FB [FU FT]]]]]].
  set (f := rename_point (fun x => x) z x).
  assert (Renames : renames_context m f (G § z / k ~ B) G e).
  { intros v T Bound. inversion Bound; subst.
    - subst f. rewrite rename_point_same, rename_typ_point_fresh, (proj1 rename_type_id) by assumption. exact Arg.
    - apply (@rename_context_override m (fun x => x) G G e z x); try assumption.
      intros y V K. rewrite (proj1 rename_type_id). now apply ty_var_var.
      }
  assert (Visible : renames_visibility f (G § z / k ~ B) G).
  { intros y V. inversion V; subst.
    - subst f. now rewrite rename_point_same.
    - apply (@rename_override_visibility (fun x => x) G G z x); try assumption. intros a K. exact K. }
  assert (Env : renames_environment f e e).
  { subst f. eapply rename_environment_override; try eassumption.
    intros y v K. now apply tyq_var_binds. }
  pose proof (rename_term (Body z FL) Renames Visible Env) as Result.
  rewrite (proj1 rename_term_open), rename_binder_result in Result.
  subst f. rewrite !rename_point_same, rename_typ_point_fresh, (proj1 rename_type_id) in Result by assumption.
  assert (rename_trm (rename_point (fun x => x) z x) t = t) as Eq.
  { rewrite <- (proj1 rename_term_id t) at 2.
    eapply (proj1 rename_term_ext). intros y P. apply rename_point_other.
    intros ->. contradiction. }
  now rewrite Eq in Result.
Qed.

Local Lemma open_avar_twice n (a : avar) x y :
  open_rec n x (open_rec n y a) = open_rec n y a.
Proof.
  destruct a; simpl; [|reflexivity].
  destruct (classic (n = n0)) as [Eq | Neq].
  - now rewrite If_l by assumption.
  - rewrite If_r by exact Neq. simpl. now rewrite If_r by exact Neq.
Qed.

Local Lemma open_type_twice :
  (forall (T : typ) n x y, open_rec n x (open_rec n y T) = open_rec n y T) /\
  (forall (D : dec) n x y, open_rec n x (open_rec n y D) = open_rec n y D).
Proof. apply typ_mutind; intros; cbn; f_equal; eauto using open_avar_twice. Qed.

Local Lemma open_term_twice :
  (forall (t : trm) n x y, open_rec n x (open_rec n y t) = open_rec n y t) /\
  (forall (l : lit) n x y, open_rec n x (open_rec n y l) = open_rec n y l) /\
  (forall (d : def) n x y, open_rec n x (open_rec n y d) = open_rec n y d) /\
  (forall (ds : defs) n x y, open_rec n x (open_rec n y ds) = open_rec n y ds).
Proof.
  destruct open_type_twice as [Twice _].
  apply trm_mutind; intros; cbn; f_equal; eauto using open_avar_twice.
Qed.

Local Lemma distinct_open_terms :
  (forall (t : trm) n k x y, n <> k -> open_rec n x (open_rec k y t) = open_rec k y (open_rec n x t)) /\
  (forall (l : lit) n k x y, n <> k -> open_rec n x (open_rec k y l) = open_rec k y (open_rec n x l)) /\
  (forall (d : def) n k x y, n <> k -> open_rec n x (open_rec k y d) = open_rec k y (open_rec n x d)) /\
  (forall (ds : defs) n k x y, n <> k -> open_rec n x (open_rec k y ds) = open_rec k y (open_rec n x ds)).
Proof.
  destruct distinct_open_types as [Open _].
  apply trm_mutind; intros; cbn; f_equal; eauto using distinct_open_avar; try congruence.
Qed.

Local Lemma open_closed_term (t : trm) n y :
  (forall k x, k <> n -> open_rec k x t = t) -> closed (open_rec n y t).
Proof.
  intros Closed' k x.
  destruct (classic (k = n)) as [-> | Different].
  - apply (proj1 open_term_twice).
  - rewrite (proj1 distinct_open_terms) by assumption. now rewrite Closed' by assumption.
Qed.

Local Lemma open_avar_result (a : avar) n z x :
  open_rec n z a = avar_f x -> a = avar_f x \/ x = z.
Proof.
  destruct a; simpl; intros Eq.
  - destruct (classic (n = n0)) as [Same | Other].
    + rewrite If_l in Eq by assumption. right. congruence.
    + rewrite If_r in Eq by assumption. discriminate.
  - now left.
Qed.

Local Lemma free_in_opened_syntax :
  (forall (t : trm) x n z, tfree_trm x (open_rec n z t) -> tfree_trm x t \/ x = z) /\
  (forall (l : lit) x n z, tfree_lit x (open_rec n z l) -> tfree_lit x l \/ x = z) /\
  (forall (d : def) x n z, tfree_def x (open_rec n z d) -> tfree_def x d \/ x = z) /\
  (forall (ds : defs) x n z, tfree_defs x (open_rec n z ds) -> tfree_defs x ds \/ x = z).
Proof.
  apply trm_mutind; intros; cbn in *.
  all: match goal with F : tfree_trm _ _ |- _ => inversion F; subst
                     | F : tfree_lit _ _ |- _ => inversion F; subst
                     | F : tfree_def _ _ |- _ => inversion F; subst
                     | F : tfree_defs _ _ |- _ => inversion F; subst
       end.
  all: repeat match goal with
  | Eq : open_rec _ _ _ = avar_f _ |- _ =>
    apply open_avar_result in Eq as [Eq|Eq]; [subst|solve [auto]]
  | Eq : avar_f _ = open_rec _ _ _ |- _ =>
    symmetry in Eq; apply open_avar_result in Eq as [Eq|Eq]; [subst|solve [auto]]
  end.
  all: try solve [left; constructor].
  all: multimatch goal with
  | IH : forall _ _ _, _ -> _ \/ _, F : _ |- _ =>
    destruct (IH _ _ _ F); solve [eauto using tfree_trm, tfree_lit, tfree_def, tfree_defs]
  end.
Qed.

Local Lemma term_variable_type (m : Mode) G Go e x T :
  @ty_trm m G Go e (trm_var (avar_f x)) T ->
  @ty_var m G objctx_empty e x T.
Proof.
  intro Typed. remember (trm_var (avar_f x)) as t eqn:Eq in Typed.
  induction Typed; inversion Eq; subst; try assumption.
  eapply ty_var_sub; [apply IHTyped; reflexivity|assumption].
Qed.

Lemma configuration_pop_let_preservation (m : Mode) G x t fs s e Lv U :
  running_config_typed m G (trm_var (avar_f x); stack_cons (frame_let t) fs; s; e; Lv) U ->
  running_config_typed m G (open x t; fs; s; e;
    fv_config (trm_var (avar_f x); stack_cons (frame_let t) fs; s; e; Lv)) U.
Proof.
  intros Typed.
  inversion Typed as [G0 e0 fs0 s0 Lv0 t0 T U0
    Inert Heap StackTyped FreeStack TermTyped FreeTerm Closed];
    subst.
  inversion StackTyped as [|L G1 e1 rest u S R U1 Rest Body]; subst.
  pose proof (FreeTerm x (tfree_trm_var x)) as Kind.
  assert (Vis : ctx_vis G x).
  { destruct Kind as [B [P Bound]].
    eapply visible_in_inert_context; [exact Inert|exact (ctx_kind_binds Bound)]. }
  assert (BodyTyped : @ty_trm m G objctx_empty e (open x t) R).
  { eapply instantiate_typed_body with (dep:=false); try eassumption.
    exact (term_variable_type TermTyped). }
  apply (running_config_c (T:=R)); try assumption.
  - intros v Free. apply FreeStack. now apply tfree_stack_cons_r.
  - intros v Free.
    destruct ((proj1 free_in_opened_syntax) _ _ _ _ Free) as [Before | ->]; [|exact Kind].
    apply FreeStack. now apply tfree_stack_cons_l.
  - inversion Closed as [t' fs' s' e' Lv' CT CS CH]; subst. constructor; try assumption.
    + apply open_closed_term. intros n v Nonzero. destruct n as [|n]; [congruence|].
      specialize (CS n v).
      change (stack_cons (frame_let (open_rec (S n) v t)) (open_rec n v fs) =
        stack_cons (frame_let t) fs) in CS.
      now injection CS.
    + intros n v. specialize (CS n v).
      change (stack_cons (frame_let (open_rec (S n) v t)) (open_rec n v fs) =
        stack_cons (frame_let t) fs) in CS.
      now injection CS.
Qed.

Local Lemma fresh_for_context_push G (T : typ) x y k :
  x §# G -> x <> y -> x §# (G § y / k ~ T).
Proof. intros Dom Neq. simpl. rewrite notin_union, notin_singleton. auto. Qed.

Local Lemma heap_item_in_larger_heap (m : Mode) G e s s' x :
  subheap_unchanged s s' ->
  ty_item_s m G e s x -> ty_item_s m G e s' x.
Proof.
  intros More Item. inversion Item; subst.
  - eapply ty_item_fun_s; eauto.
  - eapply ty_item_obj_s with (U:=U) (S:=S); eauto.
Qed.

Local Lemma extend_heap_with_location (m : Mode) G e s y i Ty :
  @heap_correspond m G e s -> y §# G -> y # s ->
  ty_item_s m (G § y / v_loc ~ Ty) e (s & y ~ i) y ->
  @heap_correspond m (G § y / v_loc ~ Ty) e (s & y ~ i).
Proof.
  intros Heap FreshG FreshS Added.
  destruct Heap as [OkG [PlainG [OkS [OkE [LocDom [RefDom [Corr Entries]]]]]]].
  repeat split; try assumption.
  - now apply ctx_ok_push.
  - now apply ctx_weakens_push.
  - now apply ok_push.
  - simpl. rewrite If_l by reflexivity. rewrite LocDom, dom_concat, dom_single.
    apply union_comm.
  - simpl. now rewrite If_r by discriminate.
  - now apply fresh_binding_renv_correspondence.
  - intros x Present. rewrite dom_concat, dom_single, in_union, in_singleton in Present.
    destruct Present as [Prior| ->]; [|assumption].
    eapply heap_item_in_larger_heap with (s:=s).
    + intros a v Bound. apply binds_push_neq; [assumption|].
      intros ->. apply FreshS. eapply get_some_inv. exact Bound.
    + eapply heap_extend_context; [apply Entries, Prior|exact FreshG|firstorder].
Qed.

Local Lemma allocation_fresh C (L : vars) :
  exists y w, y \notin L /\ w \notin L /\ y <> w /\
    fresh_in_config (y :: w :: nil) C.
Proof.
  destruct (var_fresh (fv_config C \u L)) as [y FY].
  destruct (var_fresh (fv_config C \u (L \u \{y}))) as [w FW].
  rewrite !notin_union in FY. rewrite !notin_union in FW.
  destruct FY as [FCy FLy]. destruct FW as [FCw [FLw Distinct]].
  exists y, w. repeat split; try assumption.
  - apply notin_singleton in Distinct. congruence.
  - now rewrite notin_union.
Qed.

Local Lemma invert_trm_literal_typing (m : Mode) G Go e l t T :
  @ty_trm m G Go e (trm_lit l t) T ->
  exists L A B,
    @ty_lit m G objctx_empty e l A /\
    (forall x, x \notin L -> @ty_trm m (G § x / v_let ~ A) objctx_empty e (open x t) B) /\
    @subtyp m G objctx_empty e B T.
Proof.
  intros H. remember (trm_lit l t) as w eqn:Eq in H.
  induction H; inversion Eq; subst.
  - exists L,T,U. repeat split; try assumption. apply subtyp_refl.
  - destruct (IHty_trm eq_refl) as [L [A [B [Lit [Body Sub]]]]].
    exists L,A,B. repeat split; try assumption. eapply subtyp_trans; eassumption.
Qed.

Local Lemma includes_let_after_location G y w (T : typ) :
  y §# G -> w <> y ->
  includes_context (G § w / v_let ~ T) (G § y / v_loc ~ T § w / v_ref ~ T) /\
  includes_visibility (G § w / v_let ~ T) (G § y / v_loc ~ T § w / v_ref ~ T).
Proof.
  intros FY Neq. split.
  - intros x U H. inversion H; subst; [constructor|].
    apply ctx_binds_n; [assumption|].
    eapply includes_fresh_binding; eassumption.
  - intros x H. inversion H; subst; [constructor|].
    apply ctx_vis_n; [assumption|].
    eapply includes_fresh_binding_visibility; eassumption.
Qed.

Lemma running_allocate_function (m : Mode) G B body t fs s e Lv U :
  running_config_typed m G (trm_lit (lit_fun B body) t; fs; s; e; Lv) U ->
  exists G' C', (trm_lit (lit_fun B body) t; fs; s; e; Lv) ↦ C' /\
    running_config_typed m G' C' U.
Proof.
  intros Typed.
  inversion Typed as [G0 e0 fs0 s0 Lv0 t0 T U0
    Inert Heap StackTyped FreeStack TermTyped FreeTerm Closed]; subst.
  destruct (invert_trm_literal_typing TermTyped)
    as [L [A [R [Literal [Body Sub]]]]].
  inversion Literal as [Lfn G1 e1 B' b V Enabled FnBody |]; subst.
  set (F := typ_fun B V) in *.
  set (Old := (trm_lit (lit_fun B body) t; fs; s; e; Lv)).
  destruct (allocation_fresh Old (L \u (ctx_dom G \u (ctx_fv G \u fv F))))
    as [y [w [FY [FW [Neq Fresh]]]]].
  rewrite !notin_union in FY. rewrite !notin_union in FW.
  destruct FY as [_ [Ydom [Ytypes Ytype]]]. destruct FW as [WL [Wdom [Wtypes Wtype]]].
  assert (Wdom' : w §# (G § y / v_loc ~ F)) by (apply fresh_for_context_push; congruence).
  assert (Wtypes' : w \notin ctx_fv (G § y / v_loc ~ F)).
  { simpl. rewrite notin_union. auto. }
  assert (FreshS : y # s).
  { destruct Fresh as [H _]. intro K. apply H. unfold Old. repeat rewrite in_union. tauto. }
  assert (FreshE : w # e).
  { destruct Fresh as [_ [H _]]. intro K. apply H. unfold Old. repeat rewrite in_union. tauto. }
  pose proof (@includes_fresh_binding G y v_loc F Ydom) as IY.
  pose proof (@includes_fresh_binding_visibility G y v_loc F Ydom) as VY.
  pose proof (@includes_fresh_binding _ w v_ref F Wdom') as IW.
  pose proof (@includes_fresh_binding_visibility _ w v_ref F Wdom') as VW.
  pose proof (includes_fresh_alias y FreshE) as Env.
   assert (Other : w <> y) by congruence.
  destruct (@includes_let_after_location G y w F Ydom Other) as [LetIncl LetVis].
  assert (InertF : @inert_typ m F v_loc) by (now apply inert_typ_fun).
  destruct (location_type_for_reference InertF) as [InertRef Corr].
  exists (G § y / v_loc ~ F § w / v_ref ~ F).
  exists (open w t; fs; s & y ~ item_fun body; e & w ~ y; fv_config Old).
  split; [apply red_let_fun; assumption|].
  apply (running_config_c (T:=T)); try assumption.
  - apply inert_push; [apply inert_push|constructor| | | |]; try assumption; constructor.
  - eapply extend_heap_with_reference; try eassumption; [|constructor].
    eapply extend_heap_with_location; try eassumption.
    eapply ty_item_fun_s with (L:=Lfn); try eassumption.
    + constructor.
    + apply binds_push_eq.
    + intros z ZL. eapply transport_term; [exact (FnBody z ZL)| | |firstorder].
      * now apply includes_push.
      * now apply includes_push_visibility.
    + apply fresh_binding_tfree; [exact Ydom|].
      intros v Free. apply FreeTerm, tfree_trm_lit_l, tfree_lit_fun. exact Free.
  - eapply transport_stack; [exact StackTyped| | |exact Env].
    + intros v A Bound. apply IW, IY, Bound.
    + intros v Visible. apply VW, VY, Visible.
  - apply fresh_binding_stack_tfree, fresh_binding_stack_tfree; assumption.
  - eapply ty_trm_sub.
    + eapply transport_term; [exact (Body w WL)|exact LetIncl|exact LetVis|exact Env].
    + eapply transport_subtype; [exact Sub| |exact Env].
      intros v A Bound. apply IW, IY, Bound.
  - intros v Free.
    destruct ((proj1 free_in_opened_syntax) _ _ _ _ Free) as [Before | ->].
    + apply fresh_binding_kind_inclusion, fresh_binding_kind_inclusion; try assumption.
      apply FreeTerm, tfree_trm_lit_r. exact Before.
    + exists F, (G § y / v_loc ~ F). constructor.
  - inversion Closed as [t' fs' s' e' Lv' CT CS CH]; subst.
    assert (Openings : forall n z, 
      open_rec (S n) z body = body /\ open_rec (S n) z t = t).
    { intros n z. specialize (CT n z).
      change (trm_lit (lit_fun (open_rec n z B) (open_rec (S n) z body))
        (open_rec (S n) z t) = trm_lit (lit_fun B body) t) in CT.
      injection CT. auto. }
    constructor; try assumption.
    + apply open_closed_term. intros n z NZ. destruct n; [congruence|apply Openings].
    + apply heap_closed_push; [assumption|].
      intros n z. change (item_fun (open_rec (S n) z body) = item_fun body).
      rewrite (proj1 (Openings n z)). reflexivity.
Qed.

Local Lemma rename_scope_substitute (m : Mode) f G G' e z w k B :
  renames_context m f G G' e ->
  z §# G -> z \notin ctx_fv G ->
  @ty_var m G' objctx_empty e w (rename_typ (rename_point f z w) B) ->
  renames_context m (rename_point f z w) (G § z / k ~ B) G' e.
Proof.
  intros Rel Fresh Types Value x T Bound.
  inversion Bound; subst.
  - now rewrite rename_point_same.
  - eapply rename_context_override; eassumption.
Qed.

Local Lemma rename_visibility_substitute f G G' z w k B :
  renames_visibility f G G' -> z §# G -> ctx_vis G' w ->
  renames_visibility (rename_point f z w) (G § z / k ~ B) G'.
Proof.
  intros Rel Fresh Value x Vis. inversion Vis; subst.
  - now rewrite rename_point_same.
  - eapply rename_override_visibility; eassumption.
Qed.

Local Lemma identity_renames_context (m : Mode) G e :
  renames_context m (fun x => x) G G e.
Proof. intros x T Bound. rewrite (proj1 rename_type_id). now apply ty_var_var. Qed.

Local Lemma identity_renames_environment e :
  renames_environment (fun x => x) e e.
Proof. intros x y Bound. now apply tyq_var_binds. Qed.

Local Lemma rename_one_type_identity (T : typ) z w :
  z \notin fv T -> rename_typ (rename_point (fun x => x) z w) T = T.
Proof. intro H. now rewrite rename_typ_point_fresh, (proj1 rename_type_id). Qed.

Local Lemma instantiate_subtype_body (m : Mode) (L : vars) G e B U V x :
  @ty_var m G objctx_empty e x B ->
  (forall z, z \notin L ->
    @subtyp m (G § z / v_par ~ B) objctx_empty e (open z U) (open z V)) ->
  @subtyp m G objctx_empty e (open x U) (open x V).
Proof.
  intros Arg Body.
  destruct (environment_footprint e) as [E Foot].
  destruct (var_fresh (L \u (E \u (ctx_dom G \u (ctx_fv G \u (fv B \u (fv U \u fv V))))))) as [z Fresh].
  rewrite !notin_union in Fresh. destruct Fresh as [FL [FE [FG [FC [FB [FU FV]]]]]].
  set (f := rename_point (fun x => x) z x).
  assert (Renames : renames_context m f (G § z / v_par ~ B) G e).
  { subst f. eapply rename_scope_substitute; [apply identity_renames_context|exact FG|exact FC|].
    now rewrite rename_one_type_identity. }
  assert (Env : renames_environment f e e).
  { subst f. eapply rename_environment_override; [apply identity_renames_environment|exact Foot|exact FE]. }
  pose proof (rename_subtype (Body z FL) Renames Env) as Result.
  rewrite !(proj1 rename_type_open) in Result.
  subst f. now rewrite !rename_point_same, !rename_one_type_identity in Result by assumption.
Qed.

Local Lemma function_cast_opening (m : Mode) G e A B S T :
  ShapeInterpretation.function_cast m G e A B S T ->
  forall x, @ty_var m G objctx_empty e x S ->
    @ty_var m G objctx_empty e x A /\ @subtyp m G objctx_empty e (open x B) (open x T).
Proof.
  induction 1; intros x Arg.
  - split; [assumption|apply subtyp_refl].
  - destruct (IHfunction_cast2 x Arg) as [Arg' Out2].
    destruct (IHfunction_cast1 x Arg') as [Arg'' Out1].
    split; [assumption|eapply subtyp_trans; eassumption].
  - split.
    + eapply ty_var_sub; eassumption.
    + eapply instantiate_subtype_body; eassumption.
  - split.
    + eapply ty_var_sub; [exact Arg|].
      eapply subtyp_tyq, type_equiv_symmetric; eassumption.
    + apply subtyp_tyq. apply H0.
Qed.

Local Lemma invert_apply_typing (m : Mode) G Go e x z R :
  @ty_trm m G Go e (trm_apply (avar_f x) (avar_f z)) R ->
  exists S T,
    @ty_var m G objctx_empty e x (typ_fun S T) /\
    @ty_var m G objctx_empty e z S /\
    @subtyp m G objctx_empty e (open z T) R.
Proof.
  intro H. remember (trm_apply (avar_f x) (avar_f z)) as w eqn:Eq in H.
  induction H; inversion Eq; subst.
  - eexists _, _. repeat split; try eassumption. apply subtyp_refl.
  - destruct (IHty_trm eq_refl) as [S [V [Fn [Arg Sub]]]].
    exists S, V. repeat split; try eassumption. eapply subtyp_trans; eassumption.
Qed.

Lemma configuration_apply_preservation (m : Mode) G x z fs s e Lv U loc body :
  running_config_typed m G (trm_apply (avar_f x) (avar_f z); fs; s; e; Lv) U ->
  binds x loc e -> binds loc (item_fun body) s ->
  running_config_typed m G (open z body; fs; s; e;
    fv_config (trm_apply (avar_f x) (avar_f z); fs; s; e; Lv)) U.
Proof.
  intros Typed Reference Function.
  inversion Typed as [G0 e0 fs0 s0 Lv0 t0 T U0
    Inert Heap StackTyped FreeStack TermTyped FreeTerm Closed]; subst.
  destruct (invert_apply_typing TermTyped) as [S [W [Fn [Arg Sub]]]].
  pose proof (FreeTerm x (tfree_trm_apply_l x (avar_f z))) as FnKind.
  pose proof (FreeTerm z (tfree_trm_apply_r (avar_f x) z)) as ArgKind.
  destruct (runtime_function_signature Inert Heap Fn FnKind)
    as [y [b [L [A [B [Binding [Stored [Body [Free Cast]]]]]]]]].
  assert (y = loc) by (eapply binds_unique; eassumption). subst y.
  pose proof (binds_unique Stored Function) as Eq. injection Eq as ->.
  destruct (function_cast_opening Cast Arg) as [Actual Ret].
  assert (Vis : ctx_vis G z).
  { destruct ArgKind as [? [? K]].
    eapply visible_in_inert_context; [exact Inert|exact (ctx_kind_binds K)]. }
  apply (running_config_c (T:=T)); try assumption.
  - eapply ty_trm_sub.
    + eapply instantiate_typed_body with (dep:=true); [exact Actual|exact Vis|exact Body].
    + eapply subtyp_trans; eassumption.
  - intros v Fv.
    destruct ((proj1 free_in_opened_syntax) _ _ _ _ Fv) as [Before | ->]; [now apply Free|exact ArgKind].
  - inversion Closed as [t' fs' s' e' Lv' CT CS CH]; subst. constructor; try assumption.
    apply open_closed_term. intros n w NZ. destruct n as [|n]; [congruence|].
    pose proof (heap_closed_items CH Function n w) as Both.
    change (item_fun (open_rec (Datatypes.S n) w body) = item_fun body) in Both.
    now injection Both.
Qed.

Local Lemma rename_obj_identity Go : rename_object (fun x => x) Go = Go.
Proof. destruct Go; simpl; try rewrite (proj1 rename_type_id); reflexivity. Qed.

Local Lemma instantiate_method_opening (m : Mode) (L : vars) G Scope Go e
  z r (B C : typ) (t : trm) (S T : typ) (P : trm -> typ -> typ -> Prop) :
  renames_context m (fun x => x) Scope G e ->
  renames_visibility (fun x => x) Scope G ->
  @ty_var m G objctx_empty e z B ->
  @ty_var m G objctx_empty e r (method_receiver Go z r C) ->
  ctx_vis G z -> ctx_vis G r ->
  (forall x, x \notin L -> forall y, y <> x -> y \notin L -> forall f,
    renames_context m f
      (Scope § x / v_par ~ B § y / v_recv ~ method_receiver Go x y C) G e ->
    renames_visibility f
      (Scope § x / v_par ~ B § y / v_recv ~ method_receiver Go x y C) G ->
    renames_environment f e e ->
    P (rename_trm f (open_met x y t)) (rename_typ f (open_met x y S)) (rename_typ f (open_met x y T))) ->
  P (open_met z r t) (open_met z r S) (open_met z r T).
Proof.
  intros Base BaseVis Arg Recv ArgVis RecvVis IH.
  destruct (environment_footprint e) as [E Foot].
  set (Avoid := L \u (E \u (objctx_dom Go \u (objctx_fv Go \u
     (fv C \u (fv t \u (fv S \u fv T))))))).
  destruct (var_fresh (Avoid \u (ctx_dom Scope \u (ctx_fv Scope \u fv B)))) as [x Fresh].
  unfold Avoid in Fresh. rewrite !notin_union in Fresh.
  destruct Fresh as [[X1 [X2 [X3 [X4 [X5 [X6 [X7 X8]]]]]]] [XD [XV XB]]].
  set (ArgCtx := Scope § x / v_par ~ B).
  set (g := rename_point (fun x => x) x z).
  assert (RelX : renames_context m g ArgCtx G e).
  { subst g ArgCtx. apply rename_scope_substitute; try assumption.
    now rewrite rename_one_type_identity. }
  assert (VisX : renames_visibility g ArgCtx G)
    by (subst g ArgCtx; now apply rename_visibility_substitute).
  assert (EnvX : renames_environment g e e).
  { subst g. eapply rename_environment_override; try eassumption. apply identity_renames_environment. }
  destruct (var_fresh (Avoid \u (\{x} \u (ctx_dom ArgCtx \u ctx_fv ArgCtx)))) as [y Fresh'].
  unfold Avoid in Fresh'. rewrite !notin_union in Fresh'.
  destruct Fresh' as [[Y1 [Y2 [Y3 [Y4 [Y5 [Y6 [Y7 Y8]]]]]]] [YN [YD YV]]].
  apply notin_singleton in YN.
  set (g' := rename_point g y r).
  assert (MapsX : g' x = z).
  { subst g' g. rewrite rename_point_other by congruence. apply rename_point_same. }
  assert (MapsY : g' y = r) by (subst g'; apply rename_point_same).
  assert (MapsGo : rename_object g' Go = Go).
  { subst g' g. now rewrite !object_rename_point_fresh, rename_obj_identity. }
  assert (MapsC : rename_typ g' C = C).
  { subst g' g. now rewrite !rename_typ_point_fresh, (proj1 rename_type_id). }
  assert (MapsRecv :
    rename_typ g' (method_receiver Go x y C) = method_receiver Go z r C).
  { now rewrite method_receiver_renamed, MapsGo, MapsX, MapsY, MapsC. }
  assert (RelY : renames_context m g'
    (ArgCtx § y / v_recv ~ method_receiver Go x y C) G e).
  { apply rename_scope_substitute; try assumption. fold g'. now rewrite MapsRecv. }
  assert (VisY : renames_visibility g'
    (ArgCtx § y / v_recv ~ method_receiver Go x y C) G)
    by (subst g'; now apply rename_visibility_substitute).
  assert (EnvY : renames_environment g' e e)
    by (subst g'; eapply rename_environment_override; eassumption).
  pose proof (IH x X1 y YN Y1 g' RelY VisY EnvY) as Result.
  rewrite !(proj1 rename_term_open), !(proj1 rename_type_open), MapsX, MapsY in Result.
  assert (MapsT : rename_trm g' t = t).
  { rewrite <- (proj1 rename_term_id t) at 2. apply (proj1 rename_term_ext).
    intros v Present. subst g' g. rewrite !rename_point_other by (intros ->; contradiction).
    reflexivity. }
  rewrite MapsT in Result.
  subst g' g. now rewrite !rename_typ_point_fresh, !(proj1 rename_type_id) in Result by assumption.
Qed.

Local Lemma identity_visible G :
  renames_visibility (fun x => x) G G.
Proof. intros x H. exact H. Qed.

Local Lemma method_cast_opening (m : Mode) G e C1 Z1 R1 C2 Z2 R2 :
  ShapeInterpretation.method_cast m G e C1 Z1 R1 C2 Z2 R2 ->
  forall z r, ctx_vis G z -> ctx_vis G r ->
  @ty_var m G objctx_empty e z Z2 -> @ty_var m G objctx_empty e r (open z C2) ->
  @ty_var m G objctx_empty e z Z1 /\ @ty_var m G objctx_empty e r (open z C1) /\
  @subtyp m G objctx_empty e (open_met z r R1) (open_met z r R2).
Proof.
  induction 1; intros z r VisZ VisR Arg Recv.
  - repeat split; try assumption. apply subtyp_refl.
  - destruct (IHmethod_cast2 z r VisZ VisR Arg Recv) as [Arg' [Recv' Sub2]].
    destruct (IHmethod_cast1 z r VisZ VisR Arg' Recv') as [Arg'' [Recv'' Sub1]].
    repeat split; try assumption. eapply subtyp_trans; eassumption.
  - split; [eapply ty_var_sub; eassumption|]. split.
    + eapply ty_var_sub; [exact Recv|].
      eapply instantiate_subtype_body with (B:=Z2) (L:=L); eassumption.
    + eapply (@instantiate_method_opening m L G G objctx_empty e z r Z2 C2
        (trm_var (avar_b 0)) R1 R2 (fun _ A B => @subtyp m G objctx_empty e A B));
        try eassumption.
      * apply identity_renames_context.
      * apply identity_visible.
      * intros x FX y Neq FY f Rel Vis Env. eapply rename_subtype; [|exact Rel|exact Env].
        eauto.
  - repeat split.
    + eapply ty_var_sub; [exact Arg|].
      eapply subtyp_tyq, type_equiv_symmetric; eassumption.
    + eapply ty_var_sub; [exact Recv|].
      apply subtyp_tyq, type_equiv_symmetric, H.
    + apply subtyp_tyq, H1.
Qed.

Local Lemma instantiate_heap_method_body (m : Mode) (L : vars) G e loc A B C T z r t :
  ctx_vis G z -> ctx_vis G r ->
  @ty_var m G objctx_empty e z B ->
  @ty_var m G objctx_empty e r (method_receiver (objctx_heap loc A) z r C) ->
  (forall x, x \notin L -> forall y, y <> x -> y \notin L ->
    @ty_trm m (ctx_obj_met m G (objctx_heap loc A) x B y C) objctx_empty e
      (open_met x y t) (open_met x y T)) ->
  @ty_trm m G objctx_empty e (open_met z r t) (open_met z r T).
Proof.
  intros VisZ VisR Arg Recv Body.
  eapply (@instantiate_method_opening m L G (method_base m G (objctx_heap loc A)) (objctx_heap loc A)
    e z r B C t T typ_top (fun code ty _ => @ty_trm m G objctx_empty e code ty)); try assumption.
  - unfold method_base. simpl. destruct (mode_visibility' m).
    + apply identity_renames_context.
    + intros x ty Bound. rewrite (proj1 rename_type_id).
      inversion Bound; subst. now apply ty_var_var.
  - unfold method_base. simpl. destruct (mode_visibility' m).
    + apply identity_visible.
    + intros x FV. inversion FV.
  - intros x FX y Neq FY f Rel Vis Env.
    eapply rename_term; [apply Body; assumption| | |exact Env];
      now rewrite method_context_explicit.
Qed.

Local Lemma receiver_record_types (m : Mode) G e x loc R Cap :
  @inert m G -> @renv_corr m G e -> binds x loc e ->
  ctx_binds loc (typ_objref R Cap) G ->
  @ty_var m G objctx_empty e x (open loc R) /\
  @ty_var m G objctx_empty e x (open x R).
Proof.
  intros Inert Corr Reference Bound.
  destruct (corresponding_reference Inert Corr Reference) as [X [Y [P [Q [Ref [Loc Related]]]]]].
  assert (Y = typ_objref R Cap) by (eapply ctx_bind_unique; [eapply ctx_kind_binds; exact Loc|exact Bound]).
  subst Y. inversion Related; subst.
  destruct (inert_context_lookup Inert Bound) as [k [P' [_ [Ty _]]]].
  inversion Ty; subst.
  assert (TypedX : @ty_var m G objctx_empty e x (open x R)).
  { eapply ty_rec_elim; [|assumption].
    eapply ty_var_sub; [apply ty_var_var, (ctx_kind_binds Ref)|apply subtyp_and11]. }
  split; [|exact TypedX].
  eapply ty_var_sub; [exact TypedX|]. apply subtyp_tyq, independent_open_equiv.
  - now apply tyq_var_binds.
  - assumption.
Qed.

Local Lemma invert_call_typing (m : Mode) G Go e x a z T :
  @ty_trm m G Go e (trm_call (avar_f x) a (avar_f z)) T ->
  exists TC TZ TR,
    @ty_var m G objctx_empty e x (typ_rcd (dec_met a TC TZ TR)) /\
    @ty_var m G objctx_empty e z TZ /\
    @ty_var m G objctx_empty e x (open z TC) /\
    @subtyp m G objctx_empty e (open_met z x TR) T.
Proof.
  intros H. remember (trm_call (avar_f x) a (avar_f z)) as w eqn:Eq in H.
  induction H; inversion Eq; subst.
  - eexists _,_,_. repeat split; try eassumption. apply subtyp_refl.
  - destruct (IHty_trm eq_refl) as [C [Z [R [Meth [Arg [Recv Sub]]]]]].
    exists C,Z,R. repeat split; try eassumption. eapply subtyp_trans; eassumption.
Qed.

Local Lemma heap_object_definition_kinds (m : Mode) G e s y ds :
  @heap_correspond m G e s -> binds y (item_obj ds) s -> defs_varkinds G ds.
Proof.
  intros [_ [_ [_ [_ [_ [_ [_ Items]]]]]]] Bound.
  pose proof (Items _ (get_some_inv Bound)) as Entry.
  inversion Entry; subst.
  - match goal with H : binds y (item_fun _) s |- _ =>
      pose proof (binds_unique Bound H); discriminate
    end.
  - match goal with H : binds y (item_obj ?other) s |- _ =>
      first [constr_eq ds other; fail 1 | pose proof (binds_unique Bound H) as Eq; injection Eq as ->]
    end.
    assumption.
Qed.

Local Lemma heap_closed_object s y ds :
  heap_closed s -> binds y (item_obj ds) s -> closed ds.
Proof.
  intros Closed Bound n x.
  pose proof (heap_closed_items Closed Bound n x) as Eq.
  change (item_obj (open_rec n x ds) = item_obj ds) in Eq.
  now injection Eq.
Qed.

Local Lemma closed_definition_lookup ds d :
  closed ds -> defs_has ds d -> closed d.
Proof.
  unfold defs_has. induction ds as [|ds IH head]; simpl; try discriminate.
  intros Closed Lookup.
  destruct (classic (label_of head = label_of d)) as [Same|Distinct].
  - rewrite If_l in Lookup by exact Same. injection Lookup as ->.
    intros n x. specialize (Closed n x).
    change (defs_cons (open_rec n x ds) (open_rec n x d) = defs_cons ds d) in Closed.
    now injection Closed.
  - rewrite If_r in Lookup by exact Distinct. apply IH; [|exact Lookup].
    intros n x. specialize (Closed n x).
    change (defs_cons (open_rec n x ds) (open_rec n x head) = defs_cons ds head) in Closed.
    now injection Closed.
Qed.

Local Lemma opening_method_is_closed (t : trm) a z r :
  closed (def_met a t) -> closed (open_met z r t).
Proof.
  intros Closed n x.
  destruct n as [|[|n]].
  - apply (proj1 open_term_twice).
  - rewrite (proj1 distinct_open_terms) by discriminate.
    rewrite (proj1 open_term_twice). reflexivity.
  - rewrite (proj1 distinct_open_terms _ (S (S n)) 0) by discriminate.
    rewrite (proj1 distinct_open_terms _ (S (S n)) 1) by discriminate.
    specialize (Closed n x).
    change (def_met a (open_rec (S (S n)) x t) = def_met a t) in Closed.
    injection Closed as Eq. now rewrite Eq.
Qed.

Local Lemma visible_kind (m : Mode) G x k :
  @inert m G -> ctx_k G x k -> ctx_vis G x.
Proof.
  intros Inert [T [P Bound]].
  eapply visible_in_inert_context; [exact Inert|exact (ctx_kind_binds Bound)].
Qed.

Lemma configuration_call_preservation (m : Mode) G x z a fs s e Lv U loc ds body :
  running_config_typed m G (trm_call (avar_f x) a (avar_f z); fs; s; e; Lv) U ->
  binds x loc e -> binds loc (item_obj ds) s -> defs_has ds (def_met a body) ->
  running_config_typed m G (open_met z x body; fs; s; e;
    fv_config (trm_call (avar_f x) a (avar_f z); fs; s; e; Lv)) U.
Proof.
  intros Typed Reference Lookup Found.
  inversion Typed as [G0 e0 fs0 s0 Lv0 t0 T U0
    Inert Heap StackTyped FreeStack TermTyped FreeTerm Closed]; subst.
  destruct (invert_call_typing TermTyped) as [TC [TZ [TR [Method [Arg [Recv Sub]]]]]].
  pose proof (FreeTerm x (tfree_trm_call_l x (avar_f z) a)) as RecvKind.
  pose proof (FreeTerm z (tfree_trm_call_r (avar_f x) z a)) as ArgKind.
  pose proof (visible_kind Inert RecvKind) as VisR.
  pose proof (visible_kind Inert ArgKind) as VisZ.
  destruct (runtime_method_signature Inert Heap Method RecvKind)
    as [y [ds' [b [R [Cap [C [Z [V [Binding [Stored [Found' [Bound [DefTyped Cast]]]]]]]]]]]]].
  assert (y = loc) by (eapply binds_unique; eassumption). subst y.
  pose proof (binds_unique Stored Lookup) as Eq. injection Eq as ->.
  assert (b = body) by (unfold defs_has in *; simpl in Found, Found'; congruence).
  subst b.
  destruct (method_cast_opening Cast VisZ VisR Arg Recv) as [Actual [Receiver Ret]].
  pose proof Heap as [_ [_ [_ [_ [_ [_ [Corr _]]]]]]].
  destruct (receiver_record_types Inert Corr Reference Bound) as [SelfLoc SelfRef].
  assert (Exec : @ty_trm m G objctx_empty e (open_met z x body) (open_met z x V)).
  { inversion DefTyped; subst.
    eapply instantiate_heap_method_body; try eassumption.
    simpl. apply ty_var_and; [exact Receiver|now apply ty_var_and]. }
  pose proof (heap_object_definition_kinds Heap Lookup) as Kinds.
  pose proof (defs_has_kind Kinds Found) as FreeBody.
  inversion FreeBody; subst.
  apply (running_config_c (T:=T)); try assumption.
  - eapply ty_trm_sub; [exact Exec|eapply subtyp_trans; eassumption].
  - intros v FV.
    destruct ((proj1 free_in_opened_syntax) _ _ _ _ FV) as [Before | ->]; [|exact ArgKind].
    destruct ((proj1 free_in_opened_syntax) _ _ _ _ Before) as [Before' | ->]; [|exact RecvKind].
    match goal with H : all_tfree_k _ body v_ref |- _ => apply H, Before' end.
  - inversion Closed as [t' fs' s' e' Lv' CT CS CH]; subst.
    constructor; try assumption.
    eapply opening_method_is_closed.
    eapply closed_definition_lookup; [eapply heap_closed_object; eassumption|exact Found].
Qed.

Local Ltac pointwise_equiv :=
  first [assumption | multimatch goal with
  | Eq : forall _ : var, _ |- _ => solve [apply Eq]
  end].

Local Lemma type_equiv_transitive e S T V :
  tyq_typ e S T -> tyq_typ e T V -> tyq_typ e S V.
Proof.
  intros Eq. revert V. induction Eq; intros V Next.
  - exact Next.
  - inversion H; subst; clear H;
      inversion Next; subst;
      try match goal with K : typ_nulary _ |- _ => inversion K end.
    all: match goal with K : typ_andor _ |- _ => inversion K; subst; try discriminate end.
    all: match goal with
    | K : typ_and _ _ = typ_and _ _ |- _ => injection K; intros; subst
    | K : typ_or _ _ = typ_or _ _ |- _ => injection K; intros; subst
    end.
    all: apply tyq_typ_andor; [constructor|eapply IHEq; eassumption|eapply IHEq0; eassumption].
  - inversion Next; subst; try match goal with K : typ_nulary _ |- _ => inversion K end.
    all: try match goal with K : typ_andor _ |- _ => inversion K; subst; discriminate end.
    apply tyq_typ_fun.
    + eapply IHEq; eassumption.
    + intros v. eapply H1. pointwise_equiv.
  - inversion Next; subst; try match goal with K : typ_nulary _ |- _ => inversion K end.
    all: try match goal with K : typ_andor _ |- _ => inversion K; subst; discriminate end.
    apply tyq_typ_fld; [eapply IHEq|eapply IHEq0]; eassumption.
  - inversion Next; subst; try match goal with K : typ_nulary _ |- _ => inversion K end.
    all: try match goal with K : typ_andor _ |- _ => inversion K; subst; discriminate end.
    apply tyq_typ_typ; intros v; [eapply H0|eapply H2]; pointwise_equiv.
  - inversion Next; subst; try match goal with K : typ_nulary _ |- _ => inversion K end.
    all: try match goal with K : typ_andor _ |- _ => inversion K; subst; discriminate end.
    + apply tyq_typ_sel_normal. eapply tyq_var_trans; eassumption.
    + apply tyq_typ_sel_normal. assumption.
  - exact Next.
  - inversion Next; subst; try match goal with K : typ_nulary _ |- _ => inversion K end.
    all: try match goal with K : typ_andor _ |- _ => inversion K; subst; discriminate end.
    apply tyq_typ_bnd; intros v. eapply H0; pointwise_equiv.
  - inversion Next; subst; try match goal with K : typ_nulary _ |- _ => inversion K end.
    all: try match goal with K : typ_andor _ |- _ => inversion K; subst; discriminate end.
    apply tyq_typ_met.
    + intros v. eapply H0. pointwise_equiv.
    + eapply IHEq; eassumption.
    + intros v w. eapply H3. pointwise_equiv.
Qed.

Local Lemma deref_avar_push e x y z :
  deref (e & x ~ y) (avar_f z) =
  deref e (avar_f (If z = x then y else z)).
Proof. rewrite <- cons_to_push. reflexivity. Qed.

Local Lemma deref_unbound_free e x :
  get x e = None -> deref e (avar_f x) = avar_f x.
Proof.
  induction e as [|e y v IH] using env_ind.
  - rewrite empty_def. reflexivity.
  - rewrite get_push, deref_avar_push.
    destruct (classic (x = y)) as [Eq|Neq].
    + now rewrite If_l by assumption.
    + rewrite !If_r by assumption. exact IH.
Qed.

Local Lemma deref_resolves_reference (m : Mode) G e x y :
  @inert m G -> @renv_corr m G e -> binds x y e ->
  deref e (avar_f x) = avar_f y.
Proof.
  intros Inert Corr. induction Corr; intros Lookup.
  - exfalso. eapply binds_empty_inv; eassumption.
  - rewrite deref_avar_push.
    destruct (binds_push_inv Lookup) as [[-> ->] | [Other Prior]].
    + rewrite If_l by reflexivity. apply deref_unbound_free.
      destruct (get y0 e) as [z|] eqn:Seen; [|reflexivity].
      destruct (corresponding_reference Inert Corr Seen)
        as [X [Y [P [Q [Ref _]]]]].
      match goal with L : ctx_binds_k_after y0 v_loc _ _ _ |- _ =>
        pose proof (inert_kind_lift H Inert L) as Loc
      end.
      pose proof (ctx_kind_unique Ref Loc). discriminate.
    + rewrite If_r by exact Other. now apply IHCorr.
Qed.

Local Lemma deref_definition_label e d :
  label_of (deref e d) = label_of d.
Proof. destruct d; reflexivity. Qed.

Local Lemma deref_definitions_keep_absence e ds l :
  defs_hasnt ds l -> defs_hasnt (deref_defs e ds) l.
Proof.
  unfold defs_hasnt.
  induction ds as [|ds IH d]; cbn; [auto|].
  rewrite deref_definition_label.
  intros Missing.
  destruct (classic (label_of d = l)) as [Eq | Neq].
  - rewrite If_l in Missing by exact Eq. discriminate.
  - rewrite If_r in * by exact Neq. auto.
Qed.

Local Lemma deref_preserves_free_avar (e : renv) x :
  exists y, deref e (avar_f x) = avar_f y.
Proof.
  revert x. induction e as [|[u v] e IH]; intros x.
  - exists x. reflexivity.
  - change (exists y, deref e (avar_f (If x = u then v else x)) = avar_f y).
    apply IH.
Qed.

Local Lemma deref_definition_closed e (d : def) :
  closed d -> closed (deref e d).
Proof.
  destruct d as [A T|a v|a t]; cbn; try auto.
  destruct v as [k|x].
  - intros Closed. exfalso.
    destruct (var_fresh (\{} : vars)) as [z _].
    pose proof (Closed k z) as Eq.
    cbn in Eq. rewrite If_l in Eq by reflexivity. discriminate.
  - destruct (deref_preserves_free_avar e x) as [y Eq].
    rewrite Eq. intros _ n z. reflexivity.
Qed.

Local Lemma deref_definitions_closed e ds :
  closed ds -> closed (deref_defs e ds).
Proof.
  induction ds as [|ds IH d]; intros Closed n x; [reflexivity|].
  assert (CD : closed d).
  { intros k y. specialize (Closed k y).
    change (defs_cons (open_rec k y ds) (open_rec k y d) = defs_cons ds d) in Closed.
    now injection Closed. }
  assert (CP : closed ds).
  { intros k y. specialize (Closed k y).
    change (defs_cons (open_rec k y ds) (open_rec k y d) = defs_cons ds d) in Closed.
    now injection Closed. }
  change (defs_cons (open_rec n x (deref_defs e ds)) (open_rec n x (deref e d)) =
    defs_cons (deref_defs e ds) (deref e d)).
  now rewrite (IH CP n x), (deref_definition_closed e CD n x).
Qed.

Local Lemma open_avar_injective_fresh (a b : avar) n x :
  x \notin fv a -> x \notin fv b ->
  open_rec n x a = open_rec n x b -> a = b.
Proof.
  destruct a as [i|u], b as [j|v]; simpl; intros F1 F2 Eq.
  - destruct (classic (n = i)) as [I|I], (classic (n = j)) as [J|J].
    + congruence.
    + rewrite If_l, If_r in Eq by assumption. discriminate.
    + rewrite If_r, If_l in Eq by assumption. discriminate.
    + rewrite !If_r in Eq by assumption. exact Eq.
  - destruct (classic (n = i)) as [I|I].
    + rewrite If_l in Eq by assumption. exfalso. apply F2. inversion Eq; apply in_singleton_self.
    + rewrite If_r in Eq by assumption. discriminate.
  - destruct (classic (n = j)) as [J|J].
    + rewrite If_l in Eq by assumption. exfalso. apply F1. inversion Eq; apply in_singleton_self.
    + rewrite If_r in Eq by assumption. discriminate.
  - exact Eq.
Qed.

Local Ltac open_injective_component :=
  first [assumption
    | solve [eapply open_avar_injective_fresh; [| |eassumption]; tauto]
    | multimatch goal with
      | IH : forall _ _ _, _ -> _ -> _ -> _ = _ |- _ =>
        solve [eapply IH; [| |eassumption]; tauto]
      end].

Local Lemma open_types_injective_fresh :
  (forall (T U : typ) n x, x \notin fv T -> x \notin fv U ->
    open_rec n x T = open_rec n x U -> T = U) /\
  (forall (D E : dec) n x, x \notin fv D -> x \notin fv E ->
    open_rec n x D = open_rec n x E -> D = E).
Proof.
  apply typ_mutind; intros;
    match goal with Eq : _ = open_rec _ _ ?Other |- _ =>
      destruct Other; cbn in *; try discriminate
    end;
    try reflexivity.
  all: match goal with Eq : _ = _ |- _ =>
    injection Eq; intros; subst; repeat rewrite notin_union in *
  end.
  all: f_equal; open_injective_component.
Qed.

Local Lemma record_declaration_unopen (D : dec) x :
  x \notin fv D -> record_dec (open x D) -> record_dec D.
Proof.
  destruct D as [a A B|a A B|a A B C]; cbn; intros Fresh Recorded.
  - rewrite notin_union in Fresh. destruct Fresh as [FA FB].
    inversion Recorded; subst.
    + assert (A = B) by (eapply (proj1 open_types_injective_fresh); eassumption).
      now subst B; apply rd_typ.
    + destruct A; cbn in *; try discriminate. apply rd_typb.
  - rewrite notin_union in Fresh. destruct Fresh as [FA FB].
    inversion Recorded; subst.
    assert (A = B) by (eapply (proj1 open_types_injective_fresh); eassumption).
    now subst B; apply rd_fld.
  - apply rd_met.
Qed.

Local Lemma record_type_unopen T w ls :
  w \notin fv T -> record_typ (open w T) ls -> record_typ T ls.
Proof.
  intros Fresh Record.
  remember (open w T) as Open eqn:Eq in Record.
  revert T Eq Fresh.
  induction Record; intros Raw Eq Fresh; destruct Raw; cbn in Eq; try discriminate.
  - injection Eq as EqD. subst D. eapply rt_one.
    + eapply record_declaration_unopen with (x:=w); eassumption.
    + rewrite <- open_declaration_label with (n:=0) (x:=w). assumption.
  - injection Eq as EqL EqR. subst T.
    destruct Raw2; cbn in EqR; try discriminate.
    injection EqR as EqD. subst D.
    simpl in Fresh. rewrite notin_union in Fresh. destruct Fresh as [FA FB].
    eapply rt_cons.
    + eapply IHRecord; [reflexivity|exact FA].
    + eapply record_declaration_unopen with (x:=w); eassumption.
    + rewrite <- open_declaration_label with (n:=0) (x:=w). assumption.
    + assumption.
Qed.

Local Lemma definitions_describe_record (m : Mode) G Go e ds T :
  @ty_defs m G Go e ds T ->
  exists ls, record_typ T ls /\ forall a, a \in ls -> get_def a ds <> None.
Proof.
  intros Typed.
  induction Typed.
  - exists (\{label_of d}). split.
    + eapply rt_one; [destruct H; first [apply rd_typ | apply rd_fld | apply rd_met]|exact (definition_typing_label H)].
    + intros a Present. rewrite in_singleton in Present. subst a.
      simpl. rewrite If_l by reflexivity. discriminate.
  - destruct IHTyped as [ls [Record Present]].
    exists (ls \u \{label_of d}). split.
    + apply rt_cons; [exact Record|destruct H0; first [apply rd_typ | apply rd_fld | apply rd_met]|exact (definition_typing_label H0)|].
      intros Found. apply (Present _ Found). exact H1.
    + intros a Found. simpl.
      destruct (classic (label_of d = a)) as [Same|Other].
      * rewrite If_l by exact Same. discriminate.
      * rewrite If_r by exact Other. apply Present.
        rewrite in_union, in_singleton in Found. destruct Found; congruence.
Qed.

Local Lemma types_equiv_refl e :
  (forall T, tyq_typ e T T) /\ (forall D, tyq_typ e (typ_rcd D) (typ_rcd D)).
Proof.
  apply typ_mutind; intros; try solve [apply tyq_typ_nulary; constructor]; try assumption.
  - apply tyq_typ_andor; [constructor|assumption|assumption].
  - apply tyq_typ_andor; [constructor|assumption|assumption].
  - apply tyq_typ_sel.
  - apply tyq_typ_bnd. intros. now apply type_equiv_open.
  - apply tyq_typ_fun; [assumption|]. intros. now apply type_equiv_open.
  - apply tyq_typ_typ; intros; apply type_equiv_open; assumption.
  - apply tyq_typ_fld; assumption.
  - apply tyq_typ_met.
    + intros. now apply type_equiv_open.
    + assumption.
    + intros. apply type_equiv_open, type_equiv_open; assumption.
Qed.

Local Ltac remove_other_type_equivalence :=
  try match goal with H : typ_nulary _ |- _ => inversion H end;
  try match goal with H : typ_andor _ |- _ => inversion H; subst; discriminate end.

Local Lemma equiv_field_output e a S T U V :
  tyq_typ e (typ_rcd (dec_fld a S T)) (typ_rcd (dec_fld a U V)) ->
  tyq_typ e T V.
Proof. inversion 1; subst; remove_other_type_equivalence; assumption. Qed.

Local Lemma equiv_type_output e a S T U V :
  tyq_typ e (typ_rcd (dec_typ a S T)) (typ_rcd (dec_typ a U V)) ->
  forall x, tyq_typ e (open x T) (open x V).
Proof. inversion 1; subst; remove_other_type_equivalence; intros; pointwise_equiv. Qed.

Local Lemma equiv_method_parts e a C Z R C' Z' R' :
  tyq_typ e (typ_rcd (dec_met a C Z R)) (typ_rcd (dec_met a C' Z' R')) ->
  (forall x, tyq_typ e (open x C) (open x C')) /\ tyq_typ e Z Z' /\
  (forall x y, tyq_typ e (open_met x y R) (open_met x y R')).
Proof. inversion 1; subst; remove_other_type_equivalence; repeat split; intros; pointwise_equiv. Qed.

Local Lemma equiv_intersection_parts e S T U V :
  tyq_typ e (typ_and S T) (typ_and U V) -> tyq_typ e S U /\ tyq_typ e T V.
Proof.
  inversion 1; subst.
  - match goal with H : typ_nulary _ |- _ => inversion H end.
  - match goal with H : typ_andor _ |- _ => inversion H; subst; try discriminate end.
    repeat match goal with H : typ_and _ _ = typ_and _ _ |- _ => injection H; clear H; intros; subst end.
    auto.
Qed.

Local Lemma identity_typed_push (m : Mode) G G' e x k A B :
  renames_context m (fun v => v) G G' e ->
  x §# G' ->
  @subtyp m (G' § x / k ~ B) objctx_empty e B A ->
  renames_context m (fun v => v) (G § x / k ~ A) (G' § x / k ~ B) e.
Proof.
  intros Rel Fresh Sub y T Bound. inversion Bound; subst.
  - rewrite (proj1 rename_type_id).
    eapply ty_var_sub; [apply ty_var_var; constructor|exact Sub].
  - eapply transport_variable; [apply Rel; eassumption|now apply includes_fresh_binding|firstorder].
Qed.

Local Lemma identity_visible_push G G' x k A B :
  renames_visibility (fun v => v) G G' ->
  x §# G' ->
  renames_visibility (fun v => v) (G § x / k ~ A) (G' § x / k ~ B).
Proof.
  intros Vis Fresh y Bound. inversion Bound; subst; [constructor|].
  apply ctx_vis_n.
  - intro Eq. subst. apply Fresh. eapply context_vis_domain, Vis; eassumption.
  - apply Vis. assumption.
Qed.

Local Lemma object_self_transport (m : Mode) G G' e w R :
  includes_context G G' -> includes_visibility G G' ->
  @ty_var m G' objctx_empty e w (open w R) -> ctx_vis G' w ->
  renames_context m (fun v => v) (G § w / v_self ~ open w R) G' e /\
  renames_visibility (fun v => v) (G § w / v_self ~ open w R) G'.
Proof.
  intros Incl Vis Self Visible. split.
  - intros x T Bound. inversion Bound; subst; rewrite (proj1 rename_type_id).
    + exact Self.
    + apply ty_var_var, Incl; assumption.
  - intros x Bound. inversion Bound; subst; [assumption|]. apply Vis. assumption.
Qed.

Local Lemma method_move_into_heap (m : Mode) G G' e e' (L : vars) w y R
  b C Z T C' Z' T' :
  renames_context m (fun v => v) (G § w / v_self ~ open w R) G' e' ->
  renames_visibility (fun v => v) (G § w / v_self ~ open w R) G' ->
  includes_environment e e' ->
  tyq_typ e' (open y R) (open w R) ->
  (forall v, tyq_typ e' (open v C) (open v C')) ->
  tyq_typ e' Z Z' ->
  (forall z r, tyq_typ e' (open_met z r T) (open_met z r T')) ->
  (forall z, z \notin L -> forall r, r <> z -> r \notin L ->
    @ty_trm m (ctx_obj_met m G (objctx_lit w R) z Z r C) objctx_empty e
      (open_met z r b) (open_met z r T)) ->
  forall z, z \notin (L \u ctx_dom G') -> forall r, r <> z -> r \notin (L \u ctx_dom G') ->
    @ty_trm m (ctx_obj_met m G' (objctx_heap y R) z Z' r C') objctx_empty e'
      (open_met z r b) (open_met z r T').
Proof.
  intros Rel Vis Env EqRoot EqC EqZ EqT Body z FZ r Distinct FR.
  apply notin_union in FZ as [ZL ZG]. apply notin_union in FR as [RL RG].
  set (A := method_base m G (objctx_lit w R)).
  set (A' := method_base m G' (objctx_heap y R)).
  assert (ZFresh : z §# A') by (unfold A', method_base; simpl; rewrite visibility_hide_domain; assumption).
  assert (RFresh : r §# (A' § z / v_par ~ Z')).
  { apply fresh_for_context_push; [|assumption].
    unfold A', method_base. simpl. now rewrite visibility_hide_domain. }
  assert (MapBase : renames_context m (fun v => v) A A' e' /\
    renames_visibility (fun v => v) A A').
  { unfold A, A', method_base; simpl.
    destruct (mode_visibility' m); split;
      auto using hidden_renaming_context, hidden_renaming_visibility. }
  destruct MapBase as [MapCtx MapVis].
  assert (CR : tyq_typ e'
    (method_receiver (objctx_heap y R) z r C')
    (method_receiver (objctx_lit w R) z r C)).
  { simpl. apply tyq_typ_andor; [constructor|apply type_equiv_symmetric, EqC|].
    apply tyq_typ_andor; [constructor|exact EqRoot|apply (proj1 (types_equiv_refl e'))]. }
  set (Source := ctx_obj_met m G (objctx_lit w R) z Z r C).
  set (Target := ctx_obj_met m G' (objctx_heap y R) z Z' r C').
  assert (Full : renames_context m (fun v => v) Source Target e').
  { unfold Source, Target. rewrite !method_context_explicit.
    apply identity_typed_push; [|exact RFresh|apply subtyp_tyq; exact CR].
    apply identity_typed_push; [exact MapCtx|exact ZFresh|].
    apply subtyp_tyq, type_equiv_symmetric, EqZ. }
  assert (FullVis : renames_visibility (fun v => v) Source Target).
  { unfold Source, Target. rewrite !method_context_explicit.
    apply identity_visible_push; [apply identity_visible_push; assumption|exact RFresh]. }
  assert (RelEnv : renames_environment (fun v => v) e e')
    by (intros a c Bind; now apply tyq_var_binds, Env).
  pose proof (rename_term (Body z ZL r Distinct RL) Full FullVis RelEnv) as Typed.
  rewrite (proj1 rename_term_id), (proj1 rename_type_id) in Typed.
  eapply ty_trm_sub; [exact Typed|apply subtyp_tyq, EqT].
Qed.

Section InstallObject.
Context (m : Mode) (G G' : ctx) (e e' : renv) (w y : var) (R : typ) (f : var -> var).
Hypothesis NewInert : @inert m G'.
Hypothesis NewCorr : @renv_corr m G' e'.
Hypothesis RefDom : ctx_kdom v_ref G' = dom e'.
Hypothesis IncludesEnv : includes_environment e e'.
Hypothesis SelfContext : renames_context m (fun v => v) (G § w / v_self ~ open w R) G' e'.
Hypothesis SelfVisible : renames_visibility (fun v => v) (G § w / v_self ~ open w R) G'.
Hypothesis SameRoot : tyq_typ e' (open y R) (open w R).

Local Lemma install_object_definition d D :
  @ty_def m G (objctx_lit w R) e d D ->
  tyq_typ e' (typ_rcd D) (typ_rcd (rename_dec f D)) ->
  all_tfree_k G' d v_ref ->
  @ty_def m G' (objctx_heap y R) e' (deref e' d) (rename_dec f D) /\
  def_varkinds G' (deref e' d).
Proof.
  intros Typed Equiv Free. inversion Typed; subst; cbn in *.
  - split; [|constructor].
    eapply ty_def_typ with (L:=L). intros z Fresh.
    eapply type_equiv_transitive with (T:=open z U).
    + eapply type_equiv_env_weakening; [apply H, Fresh|exact IncludesEnv].
    + eapply equiv_type_output; exact Equiv.
  - pose proof (Free t (tfree_def_trm t a)) as Kind.
    destruct (runtime_reference RefDom Kind) as [loc Binding].
    rewrite (deref_resolves_reference NewInert NewCorr Binding).
    assert (EnvId : renames_environment (fun v => v) e e')
      by (intros v p Bind; now apply tyq_var_binds, IncludesEnv).
    match goal with Source : (G § w / v_self ~ open w R) ⁏ e ⊢ t ∶ T |- _ =>
      pose proof (rename_variable Source SelfContext EnvId) as Term
    end.
    rewrite (proj1 rename_type_id) in Term.
    pose proof (corresponding_location_type NewInert NewCorr Binding Term) as LocTy.
    destruct (corresponding_reference NewInert NewCorr Binding) as [A [B [P [Q [_ [Bound _]]]]]].
    assert (PtrKind : ctx_k G' loc v_loc) by (exists B, Q; exact Bound).
    split.
    + apply ty_def_fld.
      * intros _. eapply visible_kind; eassumption.
      * eapply ty_var_sub; [exact LocTy|].
        apply subtyp_tyq. eapply equiv_field_output; exact Equiv.
    + now apply def_varkinds_fld.
  - destruct (equiv_method_parts Equiv) as [EC [EZ ET]].
    split.
    + eapply ty_def_met with (L:=L \u ctx_dom G').
      eapply method_move_into_heap; eassumption.
    + apply def_varkinds_met. intros v Fv. apply Free. now apply tfree_def_met.
Qed.

Local Lemma install_object_definitions ds T :
  @ty_defs m G (objctx_lit w R) e ds T ->
  tyq_typ e' T (rename_typ f T) ->
  all_tfree_k G' ds v_ref ->
  @ty_defs m G' (objctx_heap y R) e' (deref_defs e' ds) (rename_typ f T) /\
  defs_varkinds G' (deref_defs e' ds).
Proof.
  intros Typed. remember (objctx_lit w R) as Obj eqn:Eq in Typed.
  remember G as Source eqn:EqG in Typed. remember e as SourceEnv eqn:EqE in Typed.
  induction Typed as [G0 Go e0 d D DefTyped
    |G0 Go e0 ds d T D TailTyped IH DefTyped Absent];
    intros Equiv Free; subst Go G0 e0; cbn in Equiv |- *.
  - destruct (install_object_definition DefTyped Equiv) as [NewDef NewKinds].
    { intros v FreeD. apply Free. now apply tfree_defs_cons_r. }
    split; [now apply ty_defs_one|apply defs_varkinds_cons; [constructor|exact NewKinds]].
  - destruct (equiv_intersection_parts Equiv) as [Eds ED].
    assert (Tail : @ty_defs m G' (objctx_heap y R) e' (deref_defs e' ds) (rename_typ f T) /\
      defs_varkinds G' (deref_defs e' ds)).
    { eapply IH; try reflexivity; try assumption.
      intros v FreeDS. apply Free. now apply tfree_defs_cons_l. }
    destruct Tail as [DS KS].
    destruct (install_object_definition DefTyped ED) as [NewDef NewKinds].
    { intros v FreeD. apply Free. now apply tfree_defs_cons_r. }
    split.
    + apply ty_defs_cons; try assumption.
      rewrite deref_definition_label. now apply deref_definitions_keep_absence.
    + now apply defs_varkinds_cons.
Qed.
End InstallObject.

Local Lemma object_literal_location_type (m : Mode) R :
  record_type R -> typ_indep_b 0 R ->
  @inert_typ m (typ_objlit m R) v_loc.
Proof.
  intros Record Indep.
  destruct m; apply inert_typ_obj; try assumption; constructor.
Qed.

Local Lemma allocated_renv_correspondence (m : Mode) G e y w Ty :
  @renv_corr m G e ->
  y §# G -> w §# (G § y / v_loc ~ Ty) -> @typ_corr m Ty Ty ->
  @renv_corr m (G § y / v_loc ~ Ty § w / v_ref ~ Ty) (e & w ~ y).
Proof.
  intros Old FY FW TypeCorr.
  eapply renv_corr_ref; [constructor|constructor|exact TypeCorr|].
  apply fresh_binding_renv_correspondence, fresh_binding_renv_correspondence; assumption.
Qed.

Local Lemma allocated_reference_domain G (e : renv) y w Ty :
  ctx_kdom v_ref G = dom e ->
  ctx_kdom v_ref (G § y / v_loc ~ Ty § w / v_ref ~ Ty) = dom (e & w ~ y).
Proof.
  intros Dom. simpl. rewrite If_l by reflexivity. rewrite If_r by discriminate.
  rewrite Dom, dom_concat, dom_single. apply union_comm.
Qed.

Local Lemma extend_heap_for_object_literal (m : Mode) G e s y w Ty i :
  @heap_correspond m G e s ->
  y §# G -> w §# (G § y / v_loc ~ Ty) -> y # s -> w # e ->
  @typ_corr m Ty Ty ->
  ty_item_s m (G § y / v_loc ~ Ty § w / v_ref ~ Ty) (e & w ~ y) (s & y ~ i) y ->
  @heap_correspond m (G § y / v_loc ~ Ty § w / v_ref ~ Ty) (e & w ~ y) (s & y ~ i).
Proof.
  intros Heap FY FW FS FE TC New.
  destruct Heap as [OkG [PlainG [OkS [OkE [LocDom [RefDom [Env Items]]]]]]].
  repeat split; try assumption.
  - now apply ctx_ok_push; [apply ctx_ok_push|].
  - now apply ctx_weakens_push, ctx_weakens_push.
  - now apply ok_push.
  - now apply ok_push.
  - simpl. rewrite If_r by discriminate. rewrite If_l by reflexivity.
    rewrite LocDom, dom_concat, dom_single. apply union_comm.
  - now apply allocated_reference_domain.
  - now apply allocated_renv_correspondence.
  - intros z Present.
    rewrite dom_concat, dom_single, in_union, in_singleton in Present.
    destruct Present as [Earlier| ->]; [|assumption].
    eapply heap_item_in_larger_heap with (s:=s).
    + intros x a Bound. apply binds_push_neq; [assumption|].
      intros ->. apply FS. eapply get_some_inv. exact Bound.
    + eapply heap_extend_context; [|exact FW|now apply includes_fresh_alias].
      eapply heap_extend_context; [apply Items, Earlier|exact FY|firstorder].
Qed.

Local Lemma single_opening_closes_definitions (ds : defs) w :
  (forall n z, n <> 0 -> open_rec n z ds = ds) -> closed (open w ds).
Proof.
  intros Closed n z. destruct n as [|n].
  - apply (proj2 (proj2 (proj2 open_term_twice))).
  - rewrite (proj2 (proj2 (proj2 distinct_open_terms))) by discriminate.
    now rewrite Closed by discriminate.
Qed.

Lemma running_allocate_object (m : Mode) G R ds t fs s e Lv U :
  running_config_typed m G (trm_lit (lit_obj R ds) t; fs; s; e; Lv) U ->
  exists G' C', (trm_lit (lit_obj R ds) t; fs; s; e; Lv) ↦ C' /\
    running_config_typed m G' C' U.
Proof.
  intros Typed.
  inversion Typed as [G0 e0 fs0 s0 Lv0 t0 T U0
    Inert Heap StackTyped FreeStack TermTyped FreeTerm Closed]; subst.
  destruct (invert_trm_literal_typing TermTyped) as [L [A [Output [Literal [Body Sub]]]]].
  inversion Literal as [|Lobj G1 e1 R' ds' ObjBody Indep]; subst.
  set (F := typ_objlit m R) in *.
  set (Old := (trm_lit (lit_obj R ds) t; fs; s; e; Lv)).
  destruct (allocation_fresh Old
    (L \u (Lobj \u (ctx_dom G \u (ctx_fv G \u (fv F \u fv R))))))
    as [y [w [FY [FW [Neq Fresh]]]]].
  rewrite !notin_union in FY. rewrite !notin_union in FW.
  destruct FY as [_ [_ [Ydom [Ytypes [Ytype YR]]]]].
  destruct FW as [WL [WObj [Wdom [Wtypes [Wtype WR]]]]].
  assert (Other : w <> y) by congruence.
  assert (Wdom' : w §# (G § y / v_loc ~ F)) by (now apply fresh_for_context_push).
  assert (Wtypes' : w \notin ctx_fv (G § y / v_loc ~ F)).
  { simpl. rewrite notin_union. auto. }
  assert (FreshS : y # s).
  { destruct Fresh as [H _]. intro K. apply H. unfold Old. repeat rewrite in_union. tauto. }
  assert (FreshE : w # e).
  { destruct Fresh as [_ [H _]]. intro K. apply H. unfold Old. repeat rewrite in_union. tauto. }
  pose proof (@includes_fresh_binding G y v_loc F Ydom) as IY.
  pose proof (@includes_fresh_binding_visibility G y v_loc F Ydom) as VY.
  pose proof (@includes_fresh_binding _ w v_ref F Wdom') as IW.
  pose proof (@includes_fresh_binding_visibility _ w v_ref F Wdom') as VW.
  pose proof (includes_fresh_alias y FreshE) as Env.
  destruct (@includes_let_after_location G y w F Ydom Other) as [LetIncl LetVis].
  set (G' := G § y / v_loc ~ F § w / v_ref ~ F).
  set (e' := e & w ~ y) in *.
  assert (CtxIncl : includes_context G G')
    by (intros x A Bound; now apply IW, IY).
  assert (VisIncl : includes_visibility G G')
    by (intros x Visible; now apply VW, VY).
  pose proof (ObjBody w WObj) as InitialDefs.
  destruct (definitions_describe_record InitialDefs) as [ls [Record _]].
  assert (InertF : @inert_typ m F v_loc).
  { apply object_literal_location_type; [|assumption].
    exists ls. eapply record_type_unopen; eassumption. }
  destruct (location_type_for_reference InertF) as [InertRef TC].
  assert (NewInert : @inert m G').
  { unfold G'. apply inert_push; [apply inert_push|constructor| | | |]; try assumption; constructor. }
  pose proof Heap as [_ [_ [_ [_ [_ [RefDom [OldCorr _]]]]]]].
  assert (NewCorr : @renv_corr m G' e')
    by (unfold G', e'; now apply allocated_renv_correspondence).
  assert (NewDom : ctx_kdom v_ref G' = dom e')
    by (unfold G', e'; now apply allocated_reference_domain).
  assert (NewSelf : @ty_var m G' objctx_empty e' w (open w R)).
  { eapply ty_rec_elim; [|assumption].
    eapply ty_var_sub; [apply ty_var_var; constructor|].
    unfold F. destruct (mode_objlit_refcaps' m); apply subtyp_and11. }
  assert (VisibleW : ctx_vis G' w) by constructor.
  destruct (@object_self_transport m G G' e' w R CtxIncl VisIncl NewSelf VisibleW) as [SelfCtx SelfVis].
  assert (Alias : tyq_var e' w y) by (apply tyq_var_binds, binds_push_eq).
  pose proof (independent_open_equiv Alias Indep) as Forward.
  pose proof (type_equiv_symmetric Forward) as Back.
  set (f := rename_point (fun v => v) w y).
  assert (RenameR : rename_typ f (open w R) = open y R).
  { unfold f. rewrite (proj1 rename_type_open), rename_point_same, rename_one_type_identity;
      assumption || reflexivity. }
  assert (EqDefs : tyq_typ e' (open w R) (rename_typ f (open w R)))
    by (rewrite RenameR; exact Forward).
  assert (DefFree : all_tfree_k G' (open w ds) v_ref).
  { intros v FV.
    destruct ((proj2 (proj2 (proj2 free_in_opened_syntax))) _ _ _ _ FV) as [Previous | ->].
    - apply fresh_binding_kind_inclusion, fresh_binding_kind_inclusion; try assumption.
      apply FreeTerm, tfree_trm_lit_l, tfree_lit_obj. exact Previous.
    - exists F, (G § y / v_loc ~ F). constructor. }
  destruct (@install_object_definitions m G G' e e' w y R f NewInert NewCorr
    NewDom Env SelfCtx SelfVis Back _ _ InitialDefs EqDefs DefFree) as [DefsInstalled Kinds].
  rewrite RenameR in DefsInstalled.
  set (Object := deref_defs e' (open w ds)).
  exists G', (open w t; fs; s & y ~ item_obj Object; e'; fv_config Old).
  split; [apply red_let_obj; assumption|].
  apply (running_config_c (T:=T)); try assumption.
  - unfold G', e'. eapply extend_heap_for_object_literal; try eassumption.
    set (Cap := match mode_objlit_refcaps' m with
      | mode_objlit_refcaps_none => typ_top
      | mode_objlit_refcaps_mutable => typ_mut_marker typ_bot
      end).
    eapply ty_item_obj_s with (U:=R) (T:=F) (S:=Cap); try eassumption.
    + apply ctx_binds_n; [exact Neq|constructor].
    + apply binds_push_eq.
    + unfold F, Cap. destruct (mode_objlit_refcaps' m); reflexivity.
  - eapply transport_stack; eassumption.
  - apply fresh_binding_stack_tfree, fresh_binding_stack_tfree; assumption.
  - eapply ty_trm_sub.
    + eapply transport_term; [exact (Body w WL)|exact LetIncl|exact LetVis|exact Env].
    + eapply transport_subtype; eassumption.
  - intros v Free.
    destruct ((proj1 free_in_opened_syntax) _ _ _ _ Free) as [Before | ->].
    + apply fresh_binding_kind_inclusion, fresh_binding_kind_inclusion; try assumption.
      apply FreeTerm, tfree_trm_lit_r. exact Before.
    + exists F, (G § y / v_loc ~ F). constructor.
  - inversion Closed as [t' fs' s' e0' Lv' CT CS CH]; subst.
    assert (Openings : forall n z,
      open_rec (S n) z ds = ds /\ open_rec (S n) z t = t).
    { intros n z. specialize (CT n z).
      change (trm_lit (lit_obj (open_rec (S n) z R) (open_rec (S n) z ds))
        (open_rec (S n) z t) = trm_lit (lit_obj R ds) t) in CT.
      injection CT. auto. }
    constructor; try assumption.
    + apply open_closed_term. intros n z NZ. destruct n; [congruence|apply Openings].
    + apply heap_closed_push; [assumption|].
      unfold Object.
      assert (ClosedDefs : closed (deref_defs e' (open w ds))).
      { apply deref_definitions_closed, single_opening_closes_definitions.
        intros n z NZ. destruct n; [congruence|apply Openings]. }
      intros n z. change (item_obj (open_rec n z (deref_defs e' (open w ds))) =
        item_obj (deref_defs e' (open w ds))).
      now rewrite ClosedDefs.
Qed.

Local Lemma running_configuration_safety (m : Mode) G C U :
  running_config_typed m G C U ->
  answer C \/ exists G' C', C ↦ C' /\ running_config_typed m G' C' U.
Proof.
  intros Typed.
  destruct (running_configuration_progress Typed) as [Answer | [D Step]]; [now left|right].
  destruct Step as
    [loc obj a s e Lv ptr old ds fs InitialFresh Reference Stored Found
    |loc obj a s e Lv ptr arg s' fs Update Reference Argument
    |loc obj a s e Lv arg body ds fs Stored Found Reference
    |loc fn arg s e Lv body fs Stored Reference
    |B body t s e Lv y w fs Fresh Different
    |R ds t s e Lv y w fs Fresh Different
    |t s e Lv x fs
    |t u fs s e Lv].
  - set (C := (trm_read (avar_f obj) a; fs; s; e; Lv)).
    destruct (var_fresh (fv_config C \u (ctx_dom G \u ctx_fv G)))
      as [w Fresh].
    rewrite !notin_union in Fresh. destruct Fresh as [Run [Dom Types]].
    assert (FreshRead : fresh_in_config (w :: nil) C) by (split; [exact Run|exact I]).
    destruct (configuration_read_preservation Typed FreshRead Dom Types Reference Stored Found)
      as [Ty Next].
    eexists (G § w / v_ref ~ Ty), _. split; [|exact Next].
    eapply red_read; eassumption.
  - eexists G, _. split.
    + eapply red_write; eassumption.
    + eapply configuration_write_preservation; eassumption.
  - eexists G, _. split.
    + eapply red_call; eassumption.
    + eapply configuration_call_preservation; eassumption.
  - eexists G, _. split.
    + eapply red_apply; eassumption.
    + eapply configuration_apply_preservation; eassumption.
  - exact (running_allocate_function Typed).
  - exact (running_allocate_object Typed).
  - eexists G, _. split.
    + apply red_let_var.
    + exact (configuration_pop_let_preservation Typed).
  - eexists G, _. split.
    + apply red_let_push.
    + exact (configuration_push_let_preservation Typed).
Qed.

Local Lemma typed_runs_terminate_or_extend (m : Mode) G C U :
  running_config_typed m G C U ->
  config_terminates C \/ forall n, exists Cn, C ⊣n↦* Cn.
Proof.
  intros Typed.
  destruct (classic (config_terminates C)) as [Terminated | NeverTerminates];
    [now left|right].
  assert (AllLengths : forall n, exists Cn Gn, C ⊣n↦* Cn /\ running_config_typed m Gn Cn U).
  { induction n as [|n [Cn [Gn [Prefix TypedN]]]].
    - exists C, G. split; [constructor|exact Typed].
    - destruct (running_configuration_safety TypedN) as [Answer | [G' [C' [Step Typed']]]].
      + exfalso. apply NeverTerminates. exists n, Cn. auto.
      + exists C', G'. split; [eapply red_trans; eassumption|exact Typed']. }
  intros n. destruct (AllLengths n) as [Cn [Gn [Steps _]]]. now exists Cn.
Qed.

Section WithTypingMode.

Context (typing_mode: Mode).

Theorem soundness_initial (t : trm) (T : typ):

    closed t ->
    closed T ->
    ctx_empty⁏empty ⊢ t ∶ T ->
    exists C, (config_initial t C) /\ (

      (exists (n : nat) (Ca : config),
          answer Ca /\ (C ⊣n↦* Ca)) \/

      (forall (n : nat), exists (Cn : config),
            C ⊣n↦* Cn)
    ).

Proof.
  intros ClosedTerm ClosedType Typed.
  destruct (initial_configuration_typing ClosedTerm ClosedType Typed)
    as [C [Initial TypedConfig]].
  exists C. split; [exact Initial|].
  exact (typed_runs_terminate_or_extend (configuration_typing_implies_running TypedConfig)).
Qed.

End WithTypingMode.
