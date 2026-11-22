Set Implicit Arguments.

Require Import LibExtra AbstractSyntax GeneralTyping ConfigTyping.
Require Import HeapUpdate InertContext RecordTypes Indep HeapCorrespondence ConfigVarkinds OperationalSemantics MutableReachability TFree Equivalence EnvCorrespondence Deref.

Section WithRodotMode.
Context (typing_mode: Mode).
Context (Hmm: mode_has_mutability typing_mode).

(* A binding is a member of the domain. *)
Lemma imm_binds_in_dom A (S : env A) x v : @binds A x v S -> x \in dom S.
Proof. intros H. unfolds in H. eapply get_some_inv. eassumption. Qed.

(* A freshly allocated location is not a member of the domain. *)
Lemma imm_fresh_head_notin_dom (S : heap) (t : trm) (st : stack)
      (e : renv) (Lv : fset var) (y w : var) :
  fresh_in_config (y :: w :: nil) (config_mk t st S e Lv) ->
  y \notin dom S.
Proof.
  intros Hf.
  unfold fresh_in_config in Hf.
  cbn [LibList.length] in Hf.
  destruct Hf as [Hy _].
  apply notin_union_r in Hy; destruct Hy as [_ Hy].
  apply notin_union_r in Hy; destruct Hy as [_ Hy].
  apply notin_union_r in Hy; destruct Hy as [Hy _].
  apply notin_union_r in Hy; tauto.
Qed.

(* A location already bound is distinct from a freshly allocated one. *)
Lemma imm_binds_fresh_head_neq (S : heap) (it : item) (z : var) (t : trm)
      (st : stack) (e : renv) (Lv : fset var) (y w : var) :
  binds z it S ->
  fresh_in_config (y :: w :: nil) (config_mk t st S e Lv) ->
  z <> y.
Proof.
  intros Hb Hf E. subst z.
  apply (imm_fresh_head_notin_dom Hf).
  eapply imm_binds_in_dom. eassumption.
Qed.

(* A heap update preserves every binding whose key is not the updated one. *)
Lemma imm_binds_heap_update_neq (S S' : heap) (x a : var) (l : fld_label)
      (y : var) (it : item) :
  heap_update S x l a S' -> y <> x -> binds y it S -> binds y it S'.
Proof.
  intros Hu Hne Hb.
  unfold heap_update in Hu.
  destruct Hu as (_ & _ & _ & Hpres & _).
  eapply Hpres; eauto.
Qed.

Lemma imm_ctx_binds_dom : forall G x T, ctx_binds x T G -> x \in ctx_dom G.
Proof.
  intros G x T H. induction H; cbn [ctx_dom].
  - rewrite in_union, in_singleton. auto.
  - rewrite in_union. right. assumption.
  - assumption.
Qed.

Lemma imm_ctx_binds_unique : forall G x T1 T2,
  ctx_binds x T1 G -> ctx_binds x T2 G -> T1 = T2.
Proof.
  intros G x T1 T2 H1. induction H1; intros H2.
  - inversion H2; subst; auto; try contradiction.
  - inversion H2; subst; try contradiction; eauto.
  - inversion H2; subst; eauto.
Qed.

Lemma imm_inert_binds_typ : forall G x T,
  inert G -> ctx_binds x T G -> exists vk, inert_typ T vk.
Proof.
  intros G x T Hi. induction Hi as [ | G0 y vk T0 IH Hvk HT0 Hy Hcfv Hfv ];
  intros Hb.
  - inversion Hb.
  - inversion Hb; subst; eauto.
Qed.

Lemma imm_ctx_binds_push : forall G X T x vk S,
  ctx_binds X T G -> X <> x -> ctx_binds X T (G § x / vk ~ S).
Proof. intros. eapply ctx_binds_n; eauto. Qed.

Lemma imm_ctx_vis_push : forall G X x vk S,
  ctx_vis G X -> X <> x -> ctx_vis (G § x / vk ~ S) X.
Proof. intros. eapply ctx_vis_n; eauto. Qed.

Lemma imm_ctx_kdom_dom : forall G vk x, x \in ctx_kdom vk G -> x \in ctx_dom G.
Proof.
  intros G. induction G; intros vk x H; cbn [ctx_kdom ctx_dom] in *.
  - rewrite in_empty in H. tauto.
  - destruct (classic (vk = v0)) as [Heq | Hne].
    + subst vk. rewrite If_l in H by reflexivity.
      rewrite in_union in H. destruct H as [H | H].
      * rewrite in_singleton in H. subst. rewrite in_union, in_singleton. auto.
      * rewrite in_union. right. exact (IHG v0 x H).
    + rewrite If_r in H by assumption.
      rewrite in_union. right. exact (IHG vk x H).
  - exact (IHG vk x H).
  - exact (IHG vk x H).
Qed.

Lemma imm_binds_k_after_binds : forall v vk t G G2,
  ctx_binds_k_after v vk t G G2 -> ctx_binds v t G.
Proof.
  intros v vk t G G2 H. induction H.
  - apply ctx_binds_e.
  - eapply ctx_binds_n; eauto.
Qed.

Lemma imm_inert_binds_k_typ : forall G x vk t G2,
  inert G -> ctx_binds_k_after x vk t G G2 -> inert_typ t vk.
Proof.
  intros G x vk t G2 Hi. induction Hi as
    [ | G0 y vk0 t0 IH Hvk0 HT0 Hy Hcfv Hfv ]; intros Hk.
  - inversion Hk.
  - inversion Hk as [ | v v2 vk1 vk2 tt tt2 Hne Hk' G1 G2' ]; subst; eauto.
Qed.

Lemma imm_ctx_weakens_kdom_kind : forall G,
  ctx_weakens G -> ctx_ok G ->
  forall vk x, x \in ctx_kdom vk G -> exists t G2, ctx_binds_k_after x vk t G G2.
Proof.
  intros G Hw. induction Hw as [ | G0 y vk0 t0 Hw IH ]; intros Hok vk x Hx.
  - cbn [ctx_kdom] in Hx. rewrite in_empty in Hx. tauto.
  - cbn [ctx_kdom ctx_dom] in Hx.
    inversion Hok as [ | | | ]; subst.
    rename H into Hok0. rename H0 into Hy.
    destruct (classic (vk = vk0)) as [Heq | Hne].
    + subst vk. rewrite If_l in Hx by reflexivity.
      rewrite in_union in Hx. destruct Hx as [Hx | Hx].
      * rewrite in_singleton in Hx. subst x. exists t0, G0. apply ctx_binds_k_e.
      * assert (Hne2 : x <> y).
        { intro E. subst x. apply Hy. apply imm_ctx_kdom_dom with (vk := vk0). exact Hx. }
        destruct (IH Hok0 vk0 x Hx) as [t [G2 Hk]].
        exists t, G2. eapply ctx_binds_k_n; eauto.
    + rewrite If_r in Hx by assumption.
      assert (Hne2 : x <> y).
      { intro E. subst x. apply Hy. apply imm_ctx_kdom_dom with (vk := vk). exact Hx. }
      destruct (IH Hok0 vk x Hx) as [t [G2 Hk]].
      exists t, G2. eapply ctx_binds_k_n; eauto.
Qed.

Lemma imm_inert_ctx_vis : forall G x T,
  inert G -> ctx_binds x T G -> ctx_vis G x.
Proof.
  intros G x T Hi. induction Hi as
    [ | G0 y vk t0 IH Hvk HT Hy Hcfv Hfv ]; intros Hb.
  - inversion Hb.
  - inversion Hb as [ | v v2 vk2 t2 Hne Hb' | v t2 Hsub ]; subst.
    + apply ctx_vis_e.
    + eapply ctx_vis_n; eauto.
Qed.

(* ---- beginning of the substitution metatheory (SubstFresh for typ/dec) ---- *)
Lemma imm_ni_union (x:var) (E F: vars) : x \notin E \u F -> x \notin E /\ x \notin F.
Proof. intros H. exact (proj1 (notin_union x E F) H). Qed.

Lemma imm_ni_single (x y : var) : x \notin \{y} -> x <> y.
Proof. intros H. exact (notin_singleton_r H). Qed.

Lemma imm_subst_fresh_avar : forall x y (a:avar), x \notin fv a -> subst_var x y a = a.
Proof.
  intros x y a H. destruct a; cbn in *.
  - reflexivity.
  - apply imm_ni_single in H. cbn.
    rewrite If_r. reflexivity.
    intro E. apply H. symmetry. exact E.
Qed.

Lemma imm_subst_fresh_typ_dec : forall x y,
  (forall T : typ, x \notin fv T -> subst_typ x y T = T) /\
  (forall D : dec, x \notin fv D -> subst_dec x y D = D).
Proof.
  intros x y. apply typ_mutind.
  - intros _. reflexivity.
  - intros _. reflexivity.
  - intros d IH Hnot. cbn. rewrite (IH Hnot). reflexivity.
  - intros t IHt t0 IHt0 Hnot. cbn.
    destruct (imm_ni_union Hnot) as [H1 H2].
    rewrite (IHt H1), (IHt0 H2). reflexivity.
  - intros t IHt t0 IHt0 Hnot. cbn.
    destruct (imm_ni_union Hnot) as [H1 H2].
    rewrite (IHt H1), (IHt0 H2). reflexivity.
  - intros a L a0 Hnot. cbn.
    destruct (imm_ni_union Hnot) as [H1 H2].
    rewrite (@imm_subst_fresh_avar x y a H1), (@imm_subst_fresh_avar x y a0 H2). reflexivity.
  - intros t IH Hnot. cbn. rewrite (IH Hnot). reflexivity.
  - intros t IHt t0 IHt0 Hnot. cbn.
    destruct (imm_ni_union Hnot) as [H1 H2].
    rewrite (IHt H1), (IHt0 H2). reflexivity.
  - intros _. reflexivity.
  - intros L t IHt t0 IHt0 Hnot. cbn.
    destruct (imm_ni_union Hnot) as [H1 H2].
    rewrite (IHt H1), (IHt0 H2). reflexivity.
  - intros f t IHt t0 IHt0 Hnot. cbn.
    destruct (imm_ni_union Hnot) as [H1 H2].
    rewrite (IHt H1), (IHt0 H2). reflexivity.
  - intros m t IHt t0 IHt0 t1 IHt1 Hnot. cbn.
    destruct (imm_ni_union Hnot) as [H1 H23].
    destruct (imm_ni_union H23) as [H2 H3].
    rewrite (IHt H1), (IHt0 H2), (IHt1 H3). reflexivity.
Qed.

Lemma imm_subst_avar_commut : forall x y z n (a:avar),
  subst_var x y (open_rec n z a) = open_rec n (subst_var x y z) (subst_var x y a).
Proof.
  intros x y z n a. destruct a.
  - destruct (classic (n = n0)) as [Heq | Hne].
    + cbn.
      assert (H1 : (If n = n0 then avar_f z else avar_b n0) = avar_f z) by (apply If_l; exact Heq).
      rewrite H1.
      assert (H2 : (If n = n0 then avar_f (subst_var x y z) else avar_b n0) = avar_f (subst_var x y z)) by (apply If_l; exact Heq).
      rewrite H2. cbn. reflexivity.
    + cbn.
      assert (H1 : (If n = n0 then avar_f z else avar_b n0) = avar_b n0) by (apply If_r; exact Hne).
      rewrite H1.
      assert (H2 : (If n = n0 then avar_f (subst_var x y z) else avar_b n0) = avar_b n0) by (apply If_r; exact Hne).
      rewrite H2. cbn. reflexivity.
  - cbn. reflexivity.
Qed.

Lemma imm_subst_open_commut_typ_dec : forall x y z,
  (forall (T:typ) n, subst_typ x y (open_rec_typ n z T) = open_rec_typ n (subst_var x y z) (subst_typ x y T)) /\
  (forall (D:dec) n, subst_dec x y (open_rec_dec n z D) = open_rec_dec n (subst_var x y z) (subst_dec x y D)).
Proof.
  intros x y z. apply typ_mutind.
  - intros n. reflexivity.
  - intros n. reflexivity.
  - intros d IH n. cbn. f_equal. apply IH.
  - intros t IHt t0 IHt0 n. cbn. f_equal. apply IHt. apply IHt0.
  - intros t IHt t0 IHt0 n. cbn. f_equal. apply IHt. apply IHt0.
  - intros a L a0 n. cbn. f_equal; apply imm_subst_avar_commut.
  - intros t IHt n. cbn. f_equal. apply IHt.
  - intros t IHt t0 IHt0 n. cbn. f_equal. apply IHt. apply IHt0.
  - intros n. reflexivity.
  - intros L t IHt t0 IHt0 n. cbn. f_equal. apply IHt. apply IHt0.
  - intros f t IHt t0 IHt0 n. cbn. f_equal. apply IHt. apply IHt0.
  - intros m t IHt t0 IHt0 t1 IHt1 n. cbn. f_equal. apply IHt. apply IHt0. apply IHt1.
Qed.

Lemma imm_mode_refcaps_mut (m: Mode) (H: mode_has_mutability' m = true) :
  mode_refcaps' m = mode_refcaps_mutability.
Proof. destruct m; cbn in *; try discriminate; reflexivity. Qed.

Lemma imm_mode_vis_hide (m: Mode) (H: mode_has_mutability' m = true) :
  mode_visibility' m = mode_visibility_hide_method.
Proof. destruct m; cbn in *; try discriminate; reflexivity. Qed.

(* A location's capability is the mutable marker with bottom payload. *)
Lemma imm_inert_typ_loc_obj (U S : typ)
      (H : inert_typ (typ_objref U S) v_loc) :
  S = typ_mut_marker typ_bot.
Proof.
  inversion H as [ S0 T0 vk Hfun | T0 S0 vk Hrec Href Hind ]; subst.
  unfold refcap_inert_type in Href.
  pose proof (imm_mode_refcaps_mut typing_mode Hmm) as Hmr.
  destruct (mode_refcaps' typing_mode) eqn:E.
  + discriminate.
  + cbn in Href.
    inversion Href as [ | Tbnd ]; subst; auto.
Qed.

Lemma imm_inert_typ_loc_full (U S : typ) (H : inert_typ (typ_objref U S) v_loc) :
  record_type U /\ typ_indep_b 0 U /\ S = typ_mut_marker typ_bot.
Proof.
  inversion H as [ S0 T0 vk Hfun | T0 S0 vk Hrec Href Hind ]; subst.
  unfold refcap_inert_type in Href.
  pose proof (imm_mode_refcaps_mut typing_mode Hmm) as Hmr.
  destruct (mode_refcaps' typing_mode) eqn:E.
  - discriminate.
  - cbn in Href.
    inversion Href as [ | Tbnd ]; subst; auto.
Qed.

(* Every initial heap location has a mutable-capability object type. *)
Lemma imm_sv_typ x y (T:typ) : subst_var x y T = subst_typ x y T.
Proof. reflexivity. Qed.

Lemma imm_subst_fresh_trm : forall x y,
  (forall t:trm, x \notin fv_trm t -> subst_trm x y t = t) /\
  (forall l:lit, x \notin fv_lit l -> subst_lit x y l = l) /\
  (forall d:def, x \notin fv_def d -> subst_def x y d = d) /\
  (forall ds:defs, x \notin fv_defs ds -> subst_defs x y ds = ds).
Proof.
  intros x y. apply trm_mutind.
  - intros a H. cbn. rewrite (@imm_subst_fresh_avar x y a H). reflexivity.
  - intros a f H. cbn. rewrite (@imm_subst_fresh_avar x y a H). reflexivity.
  - intros a a0 H. cbn. destruct (imm_ni_union H) as [H1 H2].
    rewrite (@imm_subst_fresh_avar x y a H1), (@imm_subst_fresh_avar x y a0 H2). reflexivity.
  - intros t IHt t0 IHt0 H. cbn. destruct (imm_ni_union H) as [H1 H2].
    rewrite (IHt H1), (IHt0 H2). reflexivity.
  - intros l IHl t IHt H. cbn. destruct (imm_ni_union H) as [H1 H2].
    rewrite (IHl H1), (IHt H2). reflexivity.
  - intros a f a0 H. cbn. destruct (imm_ni_union H) as [H1 H2].
    rewrite (@imm_subst_fresh_avar x y a H1), (@imm_subst_fresh_avar x y a0 H2). reflexivity.
  - intros a m a0 H. cbn. destruct (imm_ni_union H) as [H1 H2].
    rewrite (@imm_subst_fresh_avar x y a H1), (@imm_subst_fresh_avar x y a0 H2). reflexivity.
  - intros T t IHt H. cbn. destruct (imm_ni_union H) as [H1 H2].
    destruct (imm_subst_fresh_typ_dec x y) as [HT _].
    rewrite (imm_sv_typ x y T), (HT T H1), (IHt H2). reflexivity.
  - intros T ds IHds H. cbn. destruct (imm_ni_union H) as [H1 H2].
    destruct (imm_subst_fresh_typ_dec x y) as [HT _].
    rewrite (imm_sv_typ x y T), (HT T H1), (IHds H2). reflexivity.
  - intros l T H. cbn. destruct (imm_subst_fresh_typ_dec x y) as [HT _].
    rewrite (imm_sv_typ x y T), (HT T H). reflexivity.
  - intros f a H. cbn. rewrite (@imm_subst_fresh_avar x y a H). reflexivity.
  - intros m t IHt H. cbn. rewrite (IHt H). reflexivity.
  - intros _. reflexivity.
  - intros ds IHds d IHd H. cbn. destruct (imm_ni_union H) as [H1 H2].
    rewrite (IHds H1), (IHd H2). reflexivity.
Qed.

Lemma imm_or_typ x n (T:typ) : open_rec n x T = open_rec_typ n x T.
Proof. reflexivity. Qed.

Lemma imm_subst_open_commut_trm : forall x y z,
  (forall (t:trm) n, subst_trm x y (open_rec_trm n z t) = open_rec_trm n (subst_var x y z) (subst_trm x y t)) /\
  (forall (l:lit) n, subst_lit x y (open_rec_lit n z l) = open_rec_lit n (subst_var x y z) (subst_lit x y l)) /\
  (forall (d:def) n, subst_def x y (open_rec_def n z d) = open_rec_def n (subst_var x y z) (subst_def x y d)) /\
  (forall (ds:defs) n, subst_defs x y (open_rec_defs n z ds) = open_rec_defs n (subst_var x y z) (subst_defs x y ds)).
Proof.
  intros x y z. apply trm_mutind.
  - intros a n. cbn. rewrite imm_subst_avar_commut. reflexivity.
  - intros a f n. cbn. rewrite imm_subst_avar_commut. reflexivity.
  - intros a a0 n. cbn. f_equal; apply imm_subst_avar_commut.
  - intros t IHt t0 IHt0 n. cbn. f_equal. apply IHt. apply IHt0.
  - intros l IHl t IHt n. cbn. f_equal. apply IHl. apply IHt.
  - intros a f a0 n. cbn. f_equal; apply imm_subst_avar_commut.
  - intros a m a0 n. cbn. f_equal; apply imm_subst_avar_commut.
  - intros T t IHt n. cbn.
    assert (HT : subst_var x y (open_rec n z T) = open_rec n (subst_var x y z) (subst_var x y T)).
    { rewrite (imm_sv_typ x y (open_rec n z T)), (imm_or_typ z n T), (imm_sv_typ x y T).
      destruct (imm_subst_open_commut_typ_dec x y z) as [H _]. apply H. }
    f_equal; [ exact HT | apply IHt ].
  - intros T ds IHds n. cbn.
    assert (HT : subst_var x y (open_rec (S n) z T) = open_rec (S n) (subst_var x y z) (subst_var x y T)).
    { rewrite (imm_sv_typ x y (open_rec (S n) z T)), (imm_or_typ z (S n) T), (imm_sv_typ x y T).
      destruct (imm_subst_open_commut_typ_dec x y z) as [H _]. apply H. }
    f_equal; [ exact HT | apply IHds ].
  - intros l T n. cbn.
    assert (HT : subst_var x y (open_rec (S n) z T) = open_rec (S n) (subst_var x y z) (subst_var x y T)).
    { rewrite (imm_sv_typ x y (open_rec (S n) z T)), (imm_or_typ z (S n) T), (imm_sv_typ x y T).
      destruct (imm_subst_open_commut_typ_dec x y z) as [H _]. apply H. }
    f_equal. exact HT.
  - intros l a n. cbn. f_equal. apply imm_subst_avar_commut.
  - intros m t IHt n. cbn. f_equal. apply IHt.
  - intros n. reflexivity.
  - intros ds IHds d IHd n. cbn. f_equal. apply IHds. apply IHd.
Qed.

Lemma imm_subst_id_avar : forall x (a:avar), subst_var x x a = a.
Proof.
  intros x a. destruct a; cbn.
  - reflexivity.
  - destruct (classic (v = x)) as [Heq | Hne].
    + subst. rewrite If_l by reflexivity. reflexivity.
    + rewrite If_r by exact Hne. reflexivity.
Qed.

Lemma imm_subst_id_typ_dec : forall x,
  (forall T:typ, subst_typ x x T = T) /\ (forall D:dec, subst_dec x x D = D).
Proof.
  intros x. apply typ_mutind.
  - reflexivity.
  - reflexivity.
  - intros d IH. cbn. rewrite IH. reflexivity.
  - intros t IHt t0 IHt0. cbn. rewrite IHt, IHt0. reflexivity.
  - intros t IHt t0 IHt0. cbn. rewrite IHt, IHt0. reflexivity.
  - intros a L a0. cbn. rewrite imm_subst_id_avar, imm_subst_id_avar. reflexivity.
  - intros t IH. cbn. rewrite IH. reflexivity.
  - intros t IHt t0 IHt0. cbn. rewrite IHt, IHt0. reflexivity.
  - reflexivity.
  - intros L t IHt t0 IHt0. cbn. rewrite IHt, IHt0. reflexivity.
  - intros f t IHt t0 IHt0. cbn. rewrite IHt, IHt0. reflexivity.
  - intros m t IHt t0 IHt0 t1 IHt1. cbn. rewrite IHt, IHt0, IHt1. reflexivity.
Qed.

Lemma imm_subst_id_trm : forall x,
  (forall t:trm, subst_trm x x t = t) /\
  (forall l:lit, subst_lit x x l = l) /\
  (forall d:def, subst_def x x d = d) /\
  (forall ds:defs, subst_defs x x ds = ds).
Proof.
  intros x. apply trm_mutind.
  - intros a. cbn. rewrite imm_subst_id_avar. reflexivity.
  - intros a f. cbn. rewrite imm_subst_id_avar. reflexivity.
  - intros a a0. cbn. rewrite imm_subst_id_avar, imm_subst_id_avar. reflexivity.
  - intros t IHt t0 IHt0. cbn. rewrite IHt, IHt0. reflexivity.
  - intros l IHl t IHt. cbn. rewrite IHl, IHt. reflexivity.
  - intros a f a0. cbn. rewrite imm_subst_id_avar, imm_subst_id_avar. reflexivity.
  - intros a m a0. cbn. rewrite imm_subst_id_avar, imm_subst_id_avar. reflexivity.
  - intros T t IHt. cbn. rewrite (imm_sv_typ x x T).
    destruct (imm_subst_id_typ_dec x) as [HT _]. rewrite HT, IHt. reflexivity.
  - intros T ds IHds. cbn. rewrite (imm_sv_typ x x T).
    destruct (imm_subst_id_typ_dec x) as [HT _]. rewrite HT, IHds. reflexivity.
  - intros l T. cbn. rewrite (imm_sv_typ x x T).
    destruct (imm_subst_id_typ_dec x) as [HT _]. rewrite HT. reflexivity.
  - intros l a. cbn. rewrite imm_subst_id_avar. reflexivity.
  - intros m t IHt. cbn. rewrite IHt. reflexivity.
  - reflexivity.
  - intros ds IHds d IHd. cbn. rewrite IHds, IHd. reflexivity.
Qed.

Lemma imm_open_twice_avar : forall n y x (a:avar), open_rec n y (open_rec n x a) = open_rec n x a.
Proof.
  intros n y x a. destruct a; cbn.
  - destruct (classic (n = n0)) as [Heq | Hne].
    + assert (H1 : (If n = n0 then avar_f x else avar_b n0) = avar_f x) by (apply If_l; exact Heq).
      rewrite H1. cbn. reflexivity.
    + assert (H1 : (If n = n0 then avar_f x else avar_b n0) = avar_b n0) by (apply If_r; exact Hne).
      rewrite H1. cbn.
      assert (H2 : (If n = n0 then avar_f y else avar_b n0) = avar_b n0) by (apply If_r; exact Hne).
      rewrite H2. reflexivity.
  - cbn. reflexivity.
Qed.

Lemma imm_open_twice_typ_dec : forall x y,
  (forall (T:typ) n, open_rec_typ n y (open_rec_typ n x T) = open_rec_typ n x T) /\
  (forall (D:dec) n, open_rec_dec n y (open_rec_dec n x D) = open_rec_dec n x D).
Proof.
  intros x y. apply typ_mutind.
  - intros n. reflexivity.
  - intros n. reflexivity.
  - intros d IH n. cbn. f_equal. apply IH.
  - intros t IHt t0 IHt0 n. cbn. f_equal. apply IHt. apply IHt0.
  - intros t IHt t0 IHt0 n. cbn. f_equal. apply IHt. apply IHt0.
  - intros a L a0 n. cbn. f_equal; apply imm_open_twice_avar.
  - intros t IHt n. cbn. f_equal. apply IHt.
  - intros t IHt t0 IHt0 n. cbn. f_equal. apply IHt. apply IHt0.
  - intros n. reflexivity.
  - intros L t IHt t0 IHt0 n. cbn. f_equal. apply IHt. apply IHt0.
  - intros f t IHt t0 IHt0 n. cbn. f_equal. apply IHt. apply IHt0.
  - intros m t IHt t0 IHt0 t1 IHt1 n. cbn. f_equal. apply IHt. apply IHt0. apply IHt1.
Qed.

Lemma imm_fv_open_cases_avar : forall x (a:avar) n,
  fv (open_rec n x a) = fv a \/ fv (open_rec n x a) = \{x} \u fv a.
Proof.
  intros x a n. destruct a.
  - destruct (classic (n = n0)) as [Heq | Hne].
    + assert (H : open_rec n x (avar_b n0) = avar_f x) by (apply If_l; exact Heq).
      rewrite H. right. cbn. rewrite union_empty_r. reflexivity.
    + assert (H : open_rec n x (avar_b n0) = avar_b n0) by (apply If_r; exact Hne).
      rewrite H. left. cbn. reflexivity.
  - left. cbn. reflexivity.
Qed.

(* Opening a type or declaration can only leave the free variables unchanged,
   or add the freshly opened variable. *)
Lemma imm_fv_open_cases_typ_dec : forall x,
  (forall (T:typ) n,
     fv_typ (open_rec_typ n x T) = fv_typ T \/
     fv_typ (open_rec_typ n x T) = \{x} \u fv_typ T) /\
  (forall (D:dec) n,
     fv_dec (open_rec_dec n x D) = fv_dec D \/
     fv_dec (open_rec_dec n x D) = \{x} \u fv_dec D).
Proof.
  intros x. apply typ_mutind.
  - intros n. left. reflexivity.
  - intros n. left. reflexivity.
  - intros d IH n. cbn. apply IH.
  - intros t IHt t0 IHt0 n. cbn.
    destruct (IHt n) as [H1|H1]; destruct (IHt0 n) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros t IHt t0 IHt0 n. cbn.
    destruct (IHt n) as [H1|H1]; destruct (IHt0 n) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros a L a0 n. cbn.
    destruct (imm_fv_open_cases_avar x a n) as [H1|H1];
      destruct (imm_fv_open_cases_avar x a0 n) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros t IHt n. cbn. apply (IHt (S n)).
  - intros t IHt t0 IHt0 n. cbn.
    destruct (IHt n) as [H1|H1]; destruct (IHt0 (S n)) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros n. left. reflexivity.
  - intros L t IHt t0 IHt0 n. cbn.
    destruct (IHt (S n)) as [H1|H1]; destruct (IHt0 (S n)) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros f t IHt t0 IHt0 n. cbn.
    destruct (IHt n) as [H1|H1]; destruct (IHt0 n) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros m t IHt t0 IHt0 t1 IHt1 n. cbn.
    destruct (IHt (S n)) as [H1|H1];
      destruct (IHt0 n) as [H2|H2];
      destruct (IHt1 (S (S n))) as [H3|H3];
      rewrite H1, H2, H3;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
Qed.

(* The same opening/free-variable property, phrased through the class
   projections so it can be rewritten inside term-level goals. *)
Lemma imm_fv_open_cases_typ_dec_proj : forall x,
  (forall (T:typ) n,
     fv (open_rec n x T) = fv T \/
     fv (open_rec n x T) = \{x} \u fv T) /\
  (forall (D:dec) n,
     fv (open_rec n x D) = fv D \/
     fv (open_rec n x D) = \{x} \u fv D).
Proof. intros x. exact (imm_fv_open_cases_typ_dec x). Qed.

(* Opening a term, literal, definition or definition list can only leave the
   free variables unchanged or add the freshly opened variable. *)
Lemma imm_fv_open_cases_trm : forall x,
  (forall (t:trm) n,
     fv_trm (open_rec_trm n x t) = fv_trm t \/
     fv_trm (open_rec_trm n x t) = \{x} \u fv_trm t) /\
  (forall (l:lit) n,
     fv_lit (open_rec_lit n x l) = fv_lit l \/
     fv_lit (open_rec_lit n x l) = \{x} \u fv_lit l) /\
  (forall (d:def) n,
     fv_def (open_rec_def n x d) = fv_def d \/
     fv_def (open_rec_def n x d) = \{x} \u fv_def d) /\
  (forall (ds:defs) n,
     fv_defs (open_rec_defs n x ds) = fv_defs ds \/
     fv_defs (open_rec_defs n x ds) = \{x} \u fv_defs ds).
Proof.
  intros x. apply trm_mutind.
  - intros a n. cbn.
    destruct (imm_fv_open_cases_avar x a n) as [H|H]; rewrite H;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros a f n. cbn.
    destruct (imm_fv_open_cases_avar x a n) as [H|H]; rewrite H;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros a a0 n. cbn.
    destruct (imm_fv_open_cases_avar x a n) as [H1|H1];
      destruct (imm_fv_open_cases_avar x a0 n) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros t IHt t0 IHt0 n. cbn.
    destruct (IHt n) as [H1|H1]; destruct (IHt0 (S n)) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros l IHl t IHt n. cbn.
    destruct (IHl n) as [H1|H1]; destruct (IHt (S n)) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros a f a0 n. cbn.
    destruct (imm_fv_open_cases_avar x a n) as [H1|H1];
      destruct (imm_fv_open_cases_avar x a0 n) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros a m a0 n. cbn.
    destruct (imm_fv_open_cases_avar x a n) as [H1|H1];
      destruct (imm_fv_open_cases_avar x a0 n) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros T t IHt n. cbn.
    destruct (imm_fv_open_cases_typ_dec_proj x) as [HTyp _].
    destruct (HTyp T n) as [H1|H1]; destruct (IHt (S n)) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros T ds IHds n. cbn.
    destruct (imm_fv_open_cases_typ_dec_proj x) as [HTyp _].
    destruct (HTyp T (S n)) as [H1|H1]; destruct (IHds (S n)) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros l T n. cbn.
    destruct (imm_fv_open_cases_typ_dec_proj x) as [HTyp _].
    apply (HTyp T (S n)).
  - intros l a n. cbn.
    destruct (imm_fv_open_cases_avar x a n) as [H|H]; rewrite H;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
  - intros m t IHt n. cbn.
    apply (IHt (S (S n))).
  - intros n. left. reflexivity.
  - intros ds IHds d IHd n. cbn.
    destruct (IHds n) as [H1|H1]; destruct (IHd n) as [H2|H2];
      rewrite H1, H2;
      first [ left; reflexivity
            | right; apply fset_extens; intros z Hz;
              repeat rewrite in_union in *; tauto ].
Qed.

(* The freshness set Lv is part of the free variables of its configuration. *)
Lemma imm_lv_fv_config (t : trm) (s : stack) (Sigma : heap) (e : renv) (Lv : fset var) :
  Lv \c fv_config (t ; s ; Sigma ; e ; Lv).
Proof.
  intros x Hx. cbn. repeat rewrite in_union. auto.
Qed.

Lemma imm_has_null_fv_config (t : trm) (s : stack) (Sigma : heap) (e : renv) (Lv : fset var) :
  (exists n, n \in Lv) -> exists n, n \in fv_config (t ; s ; Sigma ; e ; Lv).
Proof.
  intros [n Hn]. exists n. eapply imm_lv_fv_config. exact Hn.
Qed.

(* How substitution changes free variables: the substituting variable is
   either absent (fv unchanged) or removed and replaced by the new one. *)
Lemma imm_fv_subst_cases_avar (x y : var) (a : avar) :
  fv (subst_var x y a) = fv a /\ (x = y \/ x \notin fv a) \/
  x <> y /\ x \in fv a /\ fv (subst_var x y a) = fv a \- \{x} \u \{y}.
Proof.
  destruct a; cbn.
  - left. split; [reflexivity | right; apply notin_empty].
  - destruct (classic (v = x)) as [Heq | Hne].
    + assert (Hs : (If v = x then y else v) = y) by (apply If_l; exact Heq).
      rewrite Hs. cbn.
      destruct (classic (x = y)) as [Hxy | Hxy].
      * subst. left. split; [reflexivity | left; reflexivity].
      * right. split; [exact Hxy | split].
        { rewrite in_singleton. symmetry. exact Heq. }
        { apply fset_extens; intros z Hz;
          repeat rewrite in_union in *; repeat rewrite in_remove in *;
          repeat rewrite in_singleton in *; repeat rewrite notin_singleton in *;
          try subst; tauto. }
    + assert (Hs : (If v = x then y else v) = v) by (apply If_r; exact Hne).
      rewrite Hs. cbn.
      left. split; [reflexivity | right].
      apply notin_singleton_l. intro E. apply Hne. symmetry. exact E.
Qed.

(* Combining the free-variable/substitution case for two unions. *)
Lemma imm_fv_subst_union_cases (x y : var) (A B A' B' : vars) :
  (A' = A /\ (x = y \/ x \notin A) \/
   x <> y /\ x \in A /\ A' = A \- \{x} \u \{y}) ->
  (B' = B /\ (x = y \/ x \notin B) \/
   x <> y /\ x \in B /\ B' = B \- \{x} \u \{y}) ->
  (A' \u B' = A \u B /\ (x = y \/ x \notin A \u B) \/
   x <> y /\ x \in A \u B /\ A' \u B' = (A \u B) \- \{x} \u \{y}).
Proof.
  intros HA HB.
  destruct HA as [[HA1 Hyx] | [HneA [HAin HA1]]];
  destruct HB as [[HB1 Hyx2] | [HneB [HBin HB1]]].
  - left. split.
    + rewrite HA1, HB1. reflexivity.
    + destruct Hyx as [Hxy | HxA].
      * left. exact Hxy.
      * destruct Hyx2 as [Hxy2 | HxB].
        -- left. exact Hxy2.
        -- right. unfold notin in *. rewrite in_union in *. tauto.
  - right. split; [exact HneB | split].
    + rewrite in_union. right. exact HBin.
    + destruct Hyx as [Hxy | HxA].
      * exfalso. apply HneB. exact Hxy.
      * rewrite HA1, HB1.
        apply fset_extens; intros z Hz;
        destruct (classic (z = x)) as [Hzx | Hzx];
        destruct (classic (z = y)) as [Hzy | Hzy];
        try subst z;
        repeat rewrite in_union in *;
        repeat rewrite in_remove in *;
        repeat rewrite in_union in *;
        repeat rewrite in_remove in *;
        repeat rewrite in_union in *;
        repeat rewrite in_singleton in *;
        repeat rewrite notin_singleton in *;
        unfold notin in *;
        tauto.
  - right. split; [exact HneA | split].
    + rewrite in_union. left. exact HAin.
    + destruct Hyx2 as [Hxy2 | HxB].
      * exfalso. apply HneA. exact Hxy2.
      * rewrite HA1, HB1.
        apply fset_extens; intros z Hz;
        destruct (classic (z = x)) as [Hzx | Hzx];
        destruct (classic (z = y)) as [Hzy | Hzy];
        try subst z;
        repeat rewrite in_union in *;
        repeat rewrite in_remove in *;
        repeat rewrite in_union in *;
        repeat rewrite in_remove in *;
        repeat rewrite in_union in *;
        repeat rewrite in_singleton in *;
        repeat rewrite notin_singleton in *;
        unfold notin in *;
        tauto.
  - right. split; [exact HneA | split].
    + rewrite in_union. left. exact HAin.
    + rewrite HA1, HB1.
      apply fset_extens; intros z Hz;
      destruct (classic (z = x)) as [Hzx | Hzx];
      destruct (classic (z = y)) as [Hzy | Hzy];
      try subst z;
      repeat rewrite in_union in *;
      repeat rewrite in_remove in *;
      repeat rewrite in_union in *;
      repeat rewrite in_remove in *;
      repeat rewrite in_union in *;
      repeat rewrite in_singleton in *;
      repeat rewrite notin_singleton in *;
      unfold notin in *;
      tauto.
Qed.

(* Substitution cases for types and declarations. *)
Lemma imm_fv_subst_cases_typ_dec :
  forall x y,
  (forall (T:typ),
     fv_typ (subst_typ x y T) = fv_typ T /\ (x = y \/ x \notin fv_typ T) \/
     x <> y /\ x \in fv_typ T /\ fv_typ (subst_typ x y T) = fv_typ T \- \{x} \u \{y}) /\
  (forall (D:dec),
     fv_dec (subst_dec x y D) = fv_dec D /\ (x = y \/ x \notin fv_dec D) \/
     x <> y /\ x \in fv_dec D /\ fv_dec (subst_dec x y D) = fv_dec D \- \{x} \u \{y}).
Proof.
  intros x y. apply typ_mutind.
  - cbn. left. split; [reflexivity | right; apply notin_empty].
  - cbn. left. split; [reflexivity | right; apply notin_empty].
  - intros d IH. cbn. exact IH.
  - intros t IHt t0 IHt0. cbn.
    eapply imm_fv_subst_union_cases; [exact IHt | exact IHt0].
  - intros t IHt t0 IHt0. cbn.
    eapply imm_fv_subst_union_cases; [exact IHt | exact IHt0].
  - intros a L a0. cbn.
    eapply imm_fv_subst_union_cases;
      [exact (imm_fv_subst_cases_avar x y a) | exact (imm_fv_subst_cases_avar x y a0)].
  - intros t IHt. cbn. exact IHt.
  - intros t IHt t0 IHt0. cbn.
    eapply imm_fv_subst_union_cases; [exact IHt | exact IHt0].
  - cbn. left. split; [reflexivity | right; apply notin_empty].
  - intros L t IHt t0 IHt0. cbn.
    eapply imm_fv_subst_union_cases; [exact IHt | exact IHt0].
  - intros f t IHt t0 IHt0. cbn.
    eapply imm_fv_subst_union_cases; [exact IHt | exact IHt0].
  - intros m t IHt t0 IHt0 t1 IHt1. cbn.
    pose proof (imm_fv_subst_union_cases
                  (A := fv_typ t0) (B := fv_typ t1)
                  (A' := fv_typ (subst_typ x y t0))
                  (B' := fv_typ (subst_typ x y t1)) IHt0 IHt1) as H23.
    eapply imm_fv_subst_union_cases
      with (A := fv_typ t) (B := fv_typ t0 \u fv_typ t1)
           (A' := fv_typ (subst_typ x y t))
           (B' := fv_typ (subst_typ x y t0) \u fv_typ (subst_typ x y t1));
      [exact IHt | exact H23].
Qed.

(* Projection-form bridge for the substitution fv cases. *)
Lemma imm_fv_subst_cases_typ_dec_proj :
  forall x y,
  (forall (T:typ),
     fv (subst_var x y T) = fv T /\ (x = y \/ x \notin fv T) \/
     x <> y /\ x \in fv T /\ fv (subst_var x y T) = fv T \- \{x} \u \{y}) /\
  (forall (D:dec),
     fv (subst_var x y D) = fv D /\ (x = y \/ x \notin fv D) \/
     x <> y /\ x \in fv D /\ fv (subst_var x y D) = fv D \- \{x} \u \{y}).
Proof. intros x y. exact (imm_fv_subst_cases_typ_dec x y). Qed.

(* Substitution cases for terms, literals, definitions and definition lists. *)
Lemma imm_fv_subst_cases_trm :
  forall x y,
  (forall (t:trm),
     fv_trm (subst_trm x y t) = fv_trm t /\ (x = y \/ x \notin fv_trm t) \/
     x <> y /\ x \in fv_trm t /\ fv_trm (subst_trm x y t) = fv_trm t \- \{x} \u \{y}) /\
  (forall (l:lit),
     fv_lit (subst_lit x y l) = fv_lit l /\ (x = y \/ x \notin fv_lit l) \/
     x <> y /\ x \in fv_lit l /\ fv_lit (subst_lit x y l) = fv_lit l \- \{x} \u \{y}) /\
  (forall (d:def),
     fv_def (subst_def x y d) = fv_def d /\ (x = y \/ x \notin fv_def d) \/
     x <> y /\ x \in fv_def d /\ fv_def (subst_def x y d) = fv_def d \- \{x} \u \{y}) /\
  (forall (ds:defs),
     fv_defs (subst_defs x y ds) = fv_defs ds /\ (x = y \/ x \notin fv_defs ds) \/
     x <> y /\ x \in fv_defs ds /\ fv_defs (subst_defs x y ds) = fv_defs ds \- \{x} \u \{y}).
Proof.
  intros x y. apply trm_mutind.
  - intros a. cbn. exact (imm_fv_subst_cases_avar x y a).
  - intros a f. cbn. exact (imm_fv_subst_cases_avar x y a).
  - intros a a0. cbn.
    eapply imm_fv_subst_union_cases;
      [exact (imm_fv_subst_cases_avar x y a) | exact (imm_fv_subst_cases_avar x y a0)].
  - intros t IHt t0 IHt0. cbn.
    eapply imm_fv_subst_union_cases; [exact IHt | exact IHt0].
  - intros l IHl t IHt. cbn.
    eapply imm_fv_subst_union_cases; [exact IHl | exact IHt].
  - intros a f a0. cbn.
    eapply imm_fv_subst_union_cases;
      [exact (imm_fv_subst_cases_avar x y a) | exact (imm_fv_subst_cases_avar x y a0)].
  - intros a m a0. cbn.
    eapply imm_fv_subst_union_cases;
      [exact (imm_fv_subst_cases_avar x y a) | exact (imm_fv_subst_cases_avar x y a0)].
  - intros T t IHt. cbn.
    destruct (imm_fv_subst_cases_typ_dec_proj x y) as [HTyp _].
    eapply imm_fv_subst_union_cases; [exact (HTyp T) | exact IHt].
  - intros T ds IHds. cbn.
    destruct (imm_fv_subst_cases_typ_dec_proj x y) as [HTyp _].
    eapply imm_fv_subst_union_cases; [exact (HTyp T) | exact IHds].
  - intros l T. cbn.
    destruct (imm_fv_subst_cases_typ_dec_proj x y) as [HTyp _].
    exact (HTyp T).
  - intros l a. cbn. exact (imm_fv_subst_cases_avar x y a).
  - intros m t IHt. cbn. exact IHt.
  - cbn. left. split; [reflexivity | right; apply notin_empty].
  - intros ds IHds d IHd. cbn.
    eapply imm_fv_subst_union_cases; [exact IHds | exact IHd].
Qed.

Lemma imm_fv_open_union_cases (x : var) (a b a' b' : vars) :
  (a' = a \/ a' = \{x} \u a) ->
  (b' = b \/ b' = \{x} \u b) ->
  (a' \u b' = a \u b \/ a' \u b' = \{x} \u (a \u b)).
Proof.
  intros [Ha|Ha] [Hb|Hb]; rewrite Ha, Hb;
    first [ left; reflexivity
          | right; apply fset_extens; intros z Hz;
            repeat rewrite in_union in *; tauto ].
Qed.

Lemma imm_fv_open_cases_trm_proj : forall x,
  (forall (t:trm) n,
     fv (open_rec n x t) = fv t \/ fv (open_rec n x t) = \{x} \u fv t) /\
  (forall (l:lit) n,
     fv (open_rec n x l) = fv l \/ fv (open_rec n x l) = \{x} \u fv l) /\
  (forall (d:def) n,
     fv (open_rec n x d) = fv d \/ fv (open_rec n x d) = \{x} \u fv d) /\
  (forall (ds:defs) n,
     fv (open_rec n x ds) = fv ds \/ fv (open_rec n x ds) = \{x} \u fv ds).
Proof. intros x. exact (imm_fv_open_cases_trm x). Qed.

Lemma imm_fv_open_cases_item : forall x (v:item) n,
  fv (open_rec n x v) = fv v \/ fv (open_rec n x v) = \{x} \u fv v.
Proof.
  intros x v n. destruct (imm_fv_open_cases_trm_proj x) as [Ht [Hl [Hd Hds]]].
  destruct v; cbn.
  - exact (Hds d n).
  - exact (Ht t (S n)).
Qed.

Lemma imm_fv_open_cases_frame : forall x (f:frame) n,
  fv (open_rec n x f) = fv f \/ fv (open_rec n x f) = \{x} \u fv f.
Proof.
  intros x f n. destruct (imm_fv_open_cases_trm_proj x) as [Ht _].
  destruct f; cbn. exact (Ht t n).
Qed.

Lemma imm_fv_open_cases_stack : forall x (s:stack) n,
  fv (open_rec n x s) = fv s \/ fv (open_rec n x s) = \{x} \u fv s.
Proof.
  intros x s n. induction s as [|f fs IH]; cbn.
  - left. reflexivity.
  - eapply imm_fv_open_union_cases.
    + exact (imm_fv_open_cases_frame x f (S n)).
    + exact IH.
Qed.

Lemma imm_fv_subst_cases_trm_proj : forall x y,
  (forall (t:trm),
     fv (subst_var x y t) = fv t /\ (x = y \/ x \notin fv t) \/
     x <> y /\ x \in fv t /\ fv (subst_var x y t) = fv t \- \{x} \u \{y}) /\
  (forall (l:lit),
     fv (subst_var x y l) = fv l /\ (x = y \/ x \notin fv l) \/
     x <> y /\ x \in fv l /\ fv (subst_var x y l) = fv l \- \{x} \u \{y}) /\
  (forall (d:def),
     fv (subst_var x y d) = fv d /\ (x = y \/ x \notin fv d) \/
     x <> y /\ x \in fv d /\ fv (subst_var x y d) = fv d \- \{x} \u \{y}) /\
  (forall (ds:defs),
     fv (subst_var x y ds) = fv ds /\ (x = y \/ x \notin fv ds) \/
     x <> y /\ x \in fv ds /\ fv (subst_var x y ds) = fv ds \- \{x} \u \{y}).
Proof. intros x y. exact (imm_fv_subst_cases_trm x y). Qed.

Lemma imm_fv_subst_cases_item : forall x y (v:item),
  fv (subst_var x y v) = fv v /\ (x = y \/ x \notin fv v) \/
  x <> y /\ x \in fv v /\ fv (subst_var x y v) = fv v \- \{x} \u \{y}.
Proof.
  intros x y v. destruct (imm_fv_subst_cases_trm_proj x y) as [Ht [Hl [Hd Hds]]].
  destruct v; cbn.
  - exact (Hds d).
  - exact (Ht t).
Qed.

Lemma imm_fv_subst_cases_frame : forall x y (f:frame),
  fv (subst_var x y f) = fv f /\ (x = y \/ x \notin fv f) \/
  x <> y /\ x \in fv f /\ fv (subst_var x y f) = fv f \- \{x} \u \{y}.
Proof.
  intros x y f. destruct (imm_fv_subst_cases_trm_proj x y) as [Ht _].
  destruct f; cbn. exact (Ht t).
Qed.

Lemma imm_fv_subst_cases_stack : forall x y (s:stack),
  fv (subst_var x y s) = fv s /\ (x = y \/ x \notin fv s) \/
  x <> y /\ x \in fv s /\ fv (subst_var x y s) = fv s \- \{x} \u \{y}.
Proof.
  intros x y s. induction s as [|f fs IH]; cbn.
  - left. split; [reflexivity | right; apply notin_empty].
  - eapply imm_fv_subst_union_cases.
    + exact (imm_fv_subst_cases_frame x y f).
    + exact IH.
Qed.

(* Register the reconstructed free-variable/open/substitution instances so the
   generic syntax-class machinery can use them. *)
#[export] Instance imm_foc_avar : FvOpenCases AvarAbstractSyntax :=
  { fv_open_cases := imm_fv_open_cases_avar }.
#[export] Instance imm_foc_typ : FvOpenCases TypAbstractSyntax :=
  { fv_open_cases := fun x T n => proj1 (imm_fv_open_cases_typ_dec_proj x) T n }.
#[export] Instance imm_foc_dec : FvOpenCases DecAbstractSyntax :=
  { fv_open_cases := fun x D n => proj2 (imm_fv_open_cases_typ_dec_proj x) D n }.
#[export] Instance imm_foc_trm : FvOpenCases TrmAbstractSyntax :=
  { fv_open_cases := fun x t n => proj1 (imm_fv_open_cases_trm_proj x) t n }.
#[export] Instance imm_foc_lit : FvOpenCases LitAbstractSyntax :=
  { fv_open_cases := fun x l n => proj1 (proj2 (imm_fv_open_cases_trm_proj x)) l n }.
#[export] Instance imm_foc_def : FvOpenCases DefAbstractSyntax :=
  { fv_open_cases := fun x d n => proj1 (proj2 (proj2 (imm_fv_open_cases_trm_proj x))) d n }.
#[export] Instance imm_foc_defs : FvOpenCases DefsAbstractSyntax :=
  { fv_open_cases := fun x ds n => proj2 (proj2 (proj2 (imm_fv_open_cases_trm_proj x))) ds n }.
#[export] Instance imm_foc_item : FvOpenCases ItemAbstractSyntax :=
  { fv_open_cases := imm_fv_open_cases_item }.
#[export] Instance imm_foc_frame : FvOpenCases FrameAbstractSyntax :=
  { fv_open_cases := imm_fv_open_cases_frame }.
#[export] Instance imm_foc_stack : FvOpenCases StackAbstractSyntax :=
  { fv_open_cases := imm_fv_open_cases_stack }.

#[export] Instance imm_fsc_avar : FvSubstCases AvarAbstractSyntax :=
  { fv_subst_cases := imm_fv_subst_cases_avar }.
#[export] Instance imm_fsc_typ : FvSubstCases TypAbstractSyntax :=
  { fv_subst_cases := fun x y T => proj1 (imm_fv_subst_cases_typ_dec_proj x y) T }.
#[export] Instance imm_fsc_dec : FvSubstCases DecAbstractSyntax :=
  { fv_subst_cases := fun x y D => proj2 (imm_fv_subst_cases_typ_dec_proj x y) D }.
#[export] Instance imm_fsc_trm : FvSubstCases TrmAbstractSyntax :=
  { fv_subst_cases := fun x y t => proj1 (imm_fv_subst_cases_trm_proj x y) t }.
#[export] Instance imm_fsc_lit : FvSubstCases LitAbstractSyntax :=
  { fv_subst_cases := fun x y l => proj1 (proj2 (imm_fv_subst_cases_trm_proj x y)) l }.
#[export] Instance imm_fsc_def : FvSubstCases DefAbstractSyntax :=
  { fv_subst_cases := fun x y d => proj1 (proj2 (proj2 (imm_fv_subst_cases_trm_proj x y))) d }.
#[export] Instance imm_fsc_defs : FvSubstCases DefsAbstractSyntax :=
  { fv_subst_cases := fun x y ds => proj2 (proj2 (proj2 (imm_fv_subst_cases_trm_proj x y))) ds }.
#[export] Instance imm_fsc_item : FvSubstCases ItemAbstractSyntax :=
  { fv_subst_cases := imm_fv_subst_cases_item }.
#[export] Instance imm_fsc_frame : FvSubstCases FrameAbstractSyntax :=
  { fv_subst_cases := imm_fv_subst_cases_frame }.
#[export] Instance imm_fsc_stack : FvSubstCases StackAbstractSyntax :=
  { fv_subst_cases := imm_fv_subst_cases_stack }.

(* Bridges between the class projection [subst_var] and the concrete Fixpoints. *)
Lemma imm_sv_dec x y (D:dec) : subst_var x y D = subst_dec x y D.
Proof. reflexivity. Qed.
Lemma imm_sv_trm x y (t:trm) : subst_var x y t = subst_trm x y t.
Proof. reflexivity. Qed.
Lemma imm_sv_lit x y (l:lit) : subst_var x y l = subst_lit x y l.
Proof. reflexivity. Qed.
Lemma imm_sv_def x y (d:def) : subst_var x y d = subst_def x y d.
Proof. reflexivity. Qed.
Lemma imm_sv_defs x y (ds:defs) : subst_var x y ds = subst_defs x y ds.
Proof. reflexivity. Qed.
Lemma imm_sv_item x y (i:item) : subst_var x y i = subst_item x y i.
Proof. reflexivity. Qed.
Lemma imm_sv_frame x y (f:frame) : subst_var x y f = frame_subst_var x y f.
Proof. reflexivity. Qed.
Lemma imm_sv_stack x y (st:stack) : subst_var x y st = stack_subst_var x y st.
Proof. reflexivity. Qed.

Lemma imm_subst_fresh_item : forall x y (i:item), x \notin fv_item i -> subst_item x y i = i.
Proof.
  intros x y i H. destruct i; cbn in *.
  - rewrite (imm_sv_defs x y d).
    destruct (imm_subst_fresh_trm x y) as [_ [_ [_ Hds]]]. rewrite (@Hds d H). reflexivity.
  - rewrite (imm_sv_trm x y t).
    destruct (imm_subst_fresh_trm x y) as [Ht _]. rewrite (@Ht t H). reflexivity.
Qed.

Lemma imm_subst_fresh_frame : forall x y (f:frame), x \notin fv f -> subst_var x y f = f.
Proof.
  intros x y [t] H. cbn in *. rewrite (imm_sv_trm x y t).
  destruct (imm_subst_fresh_trm x y) as [Ht _]. rewrite (@Ht t H). reflexivity.
Qed.

Lemma imm_heap_loc_typ_mut (F : ctx) (e : renv) (S : heap) (y : var) (ds : defs) :
  inert F -> heap_correspond F e S -> binds y (item_obj ds) S ->
  exists U, ctx_binds y (typ_objref U (typ_mut_marker typ_bot)) F.
Proof.
  intros Hinert Hc Hb.
  destruct Hc as (Hok & Hweak & HokS & Hoke & HkL & HkR & Hrenv & Hitem).
  pose proof (imm_binds_in_dom Hb) as Hdom.
  pose proof (Hitem y Hdom) as His.
  inversion His as
    [ G1 e1 s1 x1 S1 t1 L1 T1 Hfun Hcb Hbind Hbody Htf
    | G1 e1 s1 x1 U1 S1 ds1 T1 Hcb Hbind HT Hds Hvk ]; subst.
  - exfalso. pose proof (binds_functional Hbind Hb) as Heq. discriminate Heq.
  - assert (Hdom' : y \in ctx_kdom v_loc F).
    { rewrite HkL. exact Hdom. }
    destruct (imm_ctx_weakens_kdom_kind Hweak Hok v_loc Hdom') as [t [G2 Hk]].
    pose proof (imm_binds_k_after_binds Hk) as Hcb2.
    pose proof (imm_ctx_binds_unique Hcb Hcb2) as Ht.
    pose proof (imm_inert_binds_k_typ Hinert Hk) as Hi.
    assert (Hi' : inert_typ (typ_and (typ_bnd U1) S1) v_loc).
    { rewrite Ht. exact Hi. }
    pose proof (imm_inert_typ_loc_obj Hi') as HS.
    exists U1. rewrite <- HS. exact Hcb.
Qed.

(* Typing of an initial heap item: its defs are typed at the open member type. *)
Lemma imm_heap_item_typ (F : ctx) (e : renv) (S : heap) (y : var) (ds : defs) :
  inert F -> heap_correspond F e S -> binds y (item_obj ds) S ->
  exists U, ctx_binds y (typ_objref U (typ_mut_marker typ_bot)) F
            /\ (F §§ objctx_heap y U ⁏ e ⊢ ds ∶ U /[-> y])
            /\ defs_varkinds F ds.
Proof.
  intros Hinert Hc Hb.
  destruct Hc as (Hok & Hweak & HokS & Hoke & HkL & HkR & Hrenv & Hitem).
  pose proof (imm_binds_in_dom Hb) as Hdom.
  pose proof (Hitem y Hdom) as His.
  inversion His as
    [ G1 e1 s1 x1 S1 t1 L1 T1 Hfun Hcb Hbind Hbody Htf
    | G1 e1 s1 x1 U1 S1 ds1 T1 Hcb Hbind HT Hds Hvk ]; subst.
  - exfalso. pose proof (binds_functional Hbind Hb) as Heq. discriminate Heq.
  - assert (Hdom' : y \in ctx_kdom v_loc F).
    { rewrite HkL. exact Hdom. }
    destruct (imm_ctx_weakens_kdom_kind Hweak Hok v_loc Hdom') as [t [G2 Hk]].
    pose proof (imm_binds_k_after_binds Hk) as Hcb2.
    pose proof (imm_ctx_binds_unique Hcb Hcb2) as Ht.
    pose proof (imm_inert_binds_k_typ Hinert Hk) as Hi.
    assert (Hi' : inert_typ (typ_and (typ_bnd U1) S1) v_loc).
    { rewrite Ht. exact Hi. }
    destruct (imm_inert_typ_loc_full Hi') as (Hrec & Hind & HS).
    assert (Hds_eq : ds1 = ds).
    { injection (binds_functional Hbind Hb) as E. exact E. }
    subst.
    exists U1. split; [| split].
    + exact Hcb.
    + exact Hds.
    + exact Hvk.
Qed.

(* The whole reduction argument, reduced to the write-target reachability
   property (the soundness/metatheory obligation). *)
Lemma immutability_aux (F : ctx) (T : typ) (C1 : config) :
  ty_config F C1 T ->
  (forall (C2 : config) (n : nat) (yObj wObj : var) (m : fld_label)
          (yArg : var) (fs : stack) (Sigma : heap) (e : renv)
          (Lv : fset var) (ds1 : defs),
      red_closure C1 n C2 ->
      C2 = config_mk (trm_write (avar_f wObj) m (avar_f yArg)) fs Sigma e Lv ->
      binds wObj yObj e ->
      binds yObj (item_obj ds1) (config_heap C1) ->
      F ⊢ C1 mreach yObj) ->
  forall n C2, C1 ⊣ n ↦* C2 ->
    forall y ds, binds y (item_obj ds) (config_heap C1) ->
      binds y (item_obj ds) (config_heap C2) \/ F ⊢ C1 mreach y.
Proof.
  intros Hty Hwrite n C2 Hred.
  induction Hred as [C | C1' C2' C3' n' Hred' IH Hstep].
  - intros y ds Hb. left. exact Hb.
  - intros y ds Hb.
    destruct (IH Hty Hwrite y ds Hb) as [Hpres | Hmr]; [| right; assumption].
    destruct Hstep as
      [ yObj0 wObj0 m0 Sigma0 e0 Lv0 yVal0 wVal0 ds0 fs0 Hfresh Hbw0 Hby0 Hdf0
      | yObj0 wObj0 m0 Sigma0 e0 Lv0 yArg0 wArg0 Sigma0' fs0 Hu0 Hbw0 Hby0
      | yObj0 wObj0 m0 Sigma0 e0 Lv0 wArg0 t0 ds0 fs0 Hby0 Hdf0 Hbw0
      | yFun0 wFun0 wArg0 Sigma0 e0 Lv0 t0 fs0 Hby0 Hbw0
      | T0 t10 t20 Sigma0 e0 Lv0 y0 w0 fs0 Hfresh0 Hneq0
      | T0 ds0 t0 Sigma0 e0 Lv0 y0 w0 fs0 Hfresh0 Hneq0
      | t0 Sigma0 e0 Lv0 x0 fs0
      | s0 t0 fs0 Sigma0 e0 Lv0 ].
    + left. exact Hpres.
    + destruct (classic (y = yObj0)) as [-> | Hneq].
      * right.
        eapply Hwrite; eauto.
      * left. eapply imm_binds_heap_update_neq; eauto.
    + left. exact Hpres.
    + left. exact Hpres.
    + left. eapply binds_push_neq; [ exact Hpres | ].
      eapply imm_binds_fresh_head_neq; eauto.
    + left. eapply binds_push_neq; [ exact Hpres | ].
      eapply imm_binds_fresh_head_neq; eauto.
    + left. exact Hpres.
    + left. exact Hpres.
Qed.

(* Subset transitivity, and monotonicity of the heap domain along reduction. *)
Lemma imm_subset_trans A (E F G : fset A) : E \c F -> F \c G -> E \c G.
Proof. intros H1 H2 x Hx. apply H2, H1, Hx. Qed.

Lemma imm_red_dom_mono (C C' : config) :
  C ↦ C' -> dom (config_heap C) \c dom (config_heap C').
Proof.
  intros Hred. destruct Hred as
    [ yObj wObj m Sigma e Lv yVal wVal ds fs Hfresh Hbw Hby Hdf
    | yObj wObj m Sigma e Lv yArg wArg Sigma' fs Hu Hbw Hby
    | yObj wObj m Sigma e Lv wArg t ds fs Hby Hdf Hbw
    | yFun wFun wArg Sigma e Lv t fs Hby Hbw
    | T t1 t2 Sigma e Lv y w fs Hfresh Hneq
    | T ds t Sigma e Lv y w fs Hfresh Hneq
    | t Sigma e Lv x fs
    | s t fs Sigma e Lv ].
  - cbn. apply subset_refl.
  - cbn. destruct Hu as (Hok & Hok' & Hdom & Hrest). rewrite Hdom. apply subset_refl.
  - cbn. apply subset_refl.
  - cbn. apply subset_refl.
  - cbn. rewrite dom_push. apply subset_union_weak_r.
  - cbn. rewrite dom_push. apply subset_union_weak_r.
  - cbn. apply subset_refl.
  - cbn. apply subset_refl.
Qed.

Lemma imm_red_closure_dom_subset (C1 C2 : config) (n : nat) :
  C1 ⊣ n ↦* C2 -> dom (config_heap C1) \c dom (config_heap C2).
Proof.
  intros H. induction H as [C | C1' C2' C3' n' Hred IH Hstep].
  - apply subset_refl.
  - eapply imm_subset_trans; [ exact IH | eapply imm_red_dom_mono; exact Hstep ].
Qed.

(* In the mutable modes, visibility is hidden. *)
Lemma imm_mode_mut_vis :
  mode_visibility' typing_mode = mode_visibility_hide_method.
Proof.
  destruct typing_mode; cbn; try discriminate; reflexivity.
Qed.

(* A well-typed write can only target a variable of mutable capability type. *)
Lemma imm_ty_trm_write_typed (G : ctx) (e : renv) (x y : var) (a : fld_label) (T : typ) :
  G⁏e ⊢ trm_write (avar_f x) a (avar_f y) ∶ T ->
  G⁏e ⊢ trm_var (avar_f x) ∶ (typ_mut_marker typ_bot).
Proof.
  intros H.
  remember (trm_write (avar_f x) a (avar_f y)) as t eqn:E.
  induction H; try discriminate; subst.
  - (* ty_trm_write *)
    injection E as Ex Ey Ea. subst.
    apply ty_trm_var.
    + intros Hv.
      match goal with
      | Hvis : mode_visibility' typing_mode = mode_visibility_hide_method -> _ |- _ =>
          apply Hvis; exact Hv
      end.
    + match goal with
      | Hmw : mode_has_mutability' typing_mode = true -> _ |- _ => exact (Hmw Hmm)
      end.
  - (* ty_trm_sub *)
    match goal with
    | IH : (_ = _) -> _ |- _ => apply IH; reflexivity
    end.
Qed.

(* If the initial configuration is already a write, its target is initially
   mutably reachable (the zero-step case of the provenance obligation). *)
Lemma imm_write_at_start_mreach (F : ctx) (T : typ)
    (wObj yObj : var) (m : fld_label) (yArg : var) (fs : stack) (Sigma : heap)
    (e : renv) (Lv : fset var) (ds : defs) :
  ty_config F (trm_write (avar_f wObj) m (avar_f yArg) ; fs ; Sigma ; e ; Lv) T ->
  binds wObj yObj e ->
  binds yObj (item_obj ds) Sigma ->
  F ⊢ (trm_write (avar_f wObj) m (avar_f yArg) ; fs ; Sigma ; e ; Lv) mreach yObj.
Proof.
  intros Hty Hbw Hby.
  inversion Hty as
    [ G0 e0 s0 Sigma0 Lv0 t0 T0 U0
      Hinert Hcorr Hstk Htfk Ht Htf Hnf Hnull Hseal Hcl HclU ].
  subst.
  eapply mreach_trm.
  - exact Hinert.
  - left. apply tfree_trm_write_l.
  - exact Hbw.
  - eapply imm_ty_trm_write_typed. exact Ht.
Qed.

(* Renv extension is monotone for types/declaration equivalence. *)
Lemma imm_tyq_var_renv_mono (e e' : renv) (Hmore : env_binds_more e e')
      (v1 v2 : var) :
  e ⊢ v1 ≈ v2 -> e' ⊢ v1 ≈ v2.
Proof.
  intros H. induction H.
  - apply tyq_var_refl.
  - apply tyq_var_binds. unfold renv_binds in *. apply Hmore in H. exact H.
  - apply tyq_var_sym. apply IHtyq_var. exact Hmore.
  - eapply tyq_var_trans.
    + apply IHtyq_var. exact Hmore.
    + apply IHtyq_var0. exact Hmore.
Qed.

Lemma imm_tyq_typ_renv_mono (e e' : renv) (Hmore : env_binds_more e e')
      (T U : typ) :
  e ⊢ T ≈ U -> e' ⊢ T ≈ U.
Proof.
  intros H. induction H.
  - apply tyq_typ_nulary. assumption.
  - eapply tyq_typ_andor.
    + exact H.
    + apply IHtyq_typ. exact Hmore.
    + apply IHtyq_typ0. exact Hmore.
  - eapply tyq_typ_fun.
    + apply IHtyq_typ. exact Hmore.
    + intros x. apply H1. exact Hmore.
  - eapply tyq_typ_fld.
    + apply IHtyq_typ. exact Hmore.
    + apply IHtyq_typ0. exact Hmore.
  - eapply tyq_typ_typ.
    + intros x. apply H0. exact Hmore.
    + intros x. apply H2. exact Hmore.
  - eapply tyq_typ_sel_normal.
    eapply imm_tyq_var_renv_mono; [ exact Hmore | eassumption ].
  - apply tyq_typ_sel.
  - apply tyq_typ_bnd. intros x. apply H0. exact Hmore.
  - eapply tyq_typ_met.
    + intros x. apply H0. exact Hmore.
    + apply IHtyq_typ. exact Hmore.
    + intros x y. apply H3. exact Hmore.
Qed.

(* Renv extension is monotone for variable typing, subtyping and incapacity. *)
Lemma imm_ts_renv_mono (e' : renv) :
  (forall (G : ctx) (Go : objctx) (e : renv) (v : var) (T : typ),
      G §§ Go ⁏ e ⊢ v ∶ T -> env_binds_more e e' -> G §§ Go ⁏ e' ⊢ v ∶ T) /\
  (forall (G : ctx) (Go : objctx) (e : renv) (T U : typ),
      subtyping G Go e T U -> env_binds_more e e' -> subtyping G Go e' T U) /\
  (forall (G : ctx) (Go : objctx) (e : renv) (T U : typ),
      G §§ Go ⁏ e ⊢ T ∶icp U -> env_binds_more e e' -> G §§ Go ⁏ e' ⊢ T ∶icp U).
Proof.
  apply (ts_mutind
    (fun G Go e v T d => env_binds_more e e' -> G §§ Go ⁏ e' ⊢ v ∶ T)
    (fun G Go e T U d => env_binds_more e e' -> subtyping G Go e' T U)
    (fun G Go e T U d => env_binds_more e e' -> G §§ Go ⁏ e' ⊢ T ∶icp U)).
  all: try (intros; econstructor; eauto; fail).
  intros G e T1 T2 Heq Hmore.
  apply subtyp_tyq.
  eapply imm_tyq_typ_renv_mono; eassumption.
Qed.

Lemma imm_mode_mut_viewpoint :
  mode_viewpoint_adaptation' typing_mode = mode_viewpoint_adapt_mutability.
Proof.
  destruct typing_mode; cbn; try discriminate; reflexivity.
Qed.

Lemma imm_capbnd_renv_mono (C : typ_refcap_label) (e' : renv) :
  (forall (G : ctx) (Go : objctx) (e : renv) (T U : typ),
      G §§ Go ⁏ e ⊢ T ∶cpb⟦C⟧ U ->
      env_binds_more e e' -> G §§ Go ⁏ e' ⊢ T ∶cpb⟦C⟧ U).
Proof.
  destruct (imm_ts_renv_mono e') as [Htvar [Hsub Hinc]].
  intros G Go e T U H Hmore.
  induction H.
  all: try (intros; econstructor; eauto; fail).
  all: intros; eauto.
Qed.

Lemma imm_viewpoint_cap_renv_mono (C : typ_refcap_label) (x : var) (e' : renv) :
  (forall (G : ctx) (Go : objctx) (e : renv) (T1 T2 : typ),
      viewpoint_adapt_cap typing_mode C x G Go e T1 T2 ->
      env_binds_more e e' -> viewpoint_adapt_cap typing_mode C x G Go e' T1 T2).
Proof.
  destruct (imm_ts_renv_mono e') as [Htvar [Hsub Hinc]].
  intros G Go e T1 T2 H Hmore.
  induction H.
  - econstructor.
    + eapply Hinc; eassumption.
    + eapply imm_capbnd_renv_mono; eassumption.
Qed.

(* Renv extension is monotone for all syntactic typing judgments. *)
Lemma imm_rules_renv_mono (e' : renv) :
  (forall (G : ctx) (Go : objctx) (e : renv) (t : trm) (T : typ),
      G §§ Go ⁏ e ⊢ t ∶ T -> env_binds_more e e' -> G §§ Go ⁏ e' ⊢ t ∶ T) /\
  (forall (G : ctx) (Go : objctx) (e : renv) (l : lit) (T : typ),
      G §§ Go ⁏ e ⊢ l ∶ T -> env_binds_more e e' -> G §§ Go ⁏ e' ⊢ l ∶ T) /\
  (forall (G : ctx) (Go : objctx) (e : renv) (d : def) (D : dec),
      G §§ Go ⁏ e ⊢ d ∶d D -> env_binds_more e e' -> G §§ Go ⁏ e' ⊢ d ∶d D) /\
  (forall (G : ctx) (Go : objctx) (e : renv) (ds : defs) (T : typ),
      G §§ Go ⁏ e ⊢ ds ∶ T -> env_binds_more e e' -> G §§ Go ⁏ e' ⊢ ds ∶ T).
Proof.
  destruct (imm_ts_renv_mono e') as [Htvar [Hsub Hinc]].
  assert (Htyq : forall (e0 : renv) (T U : typ),
             e0 ⊢ T ≈ U -> env_binds_more e0 e' -> e' ⊢ T ≈ U).
  { intros e0 T U Heq Hm. eapply imm_tyq_typ_renv_mono; eassumption. }
  apply (rules_mutind
    (fun G Go e t T d => env_binds_more e e' -> G §§ Go ⁏ e' ⊢ t ∶ T)
    (fun G Go e l T d => env_binds_more e e' -> G §§ Go ⁏ e' ⊢ l ∶ T)
    (fun G Go e d D d0 => env_binds_more e e' -> G §§ Go ⁏ e' ⊢ d ∶d D)
    (fun G Go e ds T d => env_binds_more e e' -> G §§ Go ⁏ e' ⊢ ds ∶ T)).
  all: try (intros; econstructor; eauto; fail).
  intros G e x a S T U Hvis Hfld Hview Hmore.
  eapply ty_trm_read.
  - exact Hvis.
  - eapply Htvar; eassumption.
  - unfold viewpoint_adapt in Hview |- *.
    rewrite imm_mode_mut_viewpoint in Hview |- *.
    cbn in Hview |- *.
    eapply imm_viewpoint_cap_renv_mono; eassumption.
Qed.

Lemma imm_subst_open_commut_avar (x y z : var) (a : avar) (n : nat) :
  subst_var x y (open_rec n z a) = open_rec n (subst_var x y z) (subst_var x y a).
Proof.
  destruct a; cbn.
  - destruct (classic (n = n0)) as [Heq | Hne].
    + assert (H1 : (If n = n0 then avar_f z else avar_b n0) = avar_f z)
        by (apply If_l; exact Heq).
      assert (H2 : (If n = n0 then avar_f z /[ x -> y] else avar_b n0) = avar_f z /[ x -> y])
        by (apply If_l; exact Heq).
      rewrite H1, H2. reflexivity.
    + assert (H1 : (If n = n0 then avar_f z else avar_b n0) = avar_b n0)
        by (apply If_r; exact Hne).
      assert (H2 : (If n = n0 then avar_f z /[ x -> y] else avar_b n0) = avar_b n0)
        by (apply If_r; exact Hne).
      rewrite H1, H2. reflexivity.
  - cbn. reflexivity.
Qed.

Lemma imm_subst_fresh_typ_dec_proj : forall x y,
  (forall (T:typ), x \notin fv T -> subst_var x y T = T) /\
  (forall (D:dec), x \notin fv D -> subst_var x y D = D).
Proof. intros x y. exact (imm_subst_fresh_typ_dec x y). Qed.

Lemma imm_subst_fresh_trm_proj : forall x y,
  (forall (t:trm), x \notin fv t -> subst_var x y t = t) /\
  (forall (l:lit), x \notin fv l -> subst_var x y l = l) /\
  (forall (d:def), x \notin fv d -> subst_var x y d = d) /\
  (forall (ds:defs), x \notin fv ds -> subst_var x y ds = ds).
Proof. intros x y. exact (imm_subst_fresh_trm x y). Qed.

Lemma imm_subst_open_commut_typ_dec_proj : forall x y z,
  (forall (T:typ) n,
     subst_var x y (open_rec n z T) = open_rec n (subst_var x y z) (subst_var x y T)) /\
  (forall (D:dec) n,
     subst_var x y (open_rec n z D) = open_rec n (subst_var x y z) (subst_var x y D)).
Proof. intros x y z. exact (imm_subst_open_commut_typ_dec x y z). Qed.

Lemma imm_subst_open_commut_trm_proj : forall x y z,
  (forall (t:trm) n,
     subst_var x y (open_rec n z t) = open_rec n (subst_var x y z) (subst_var x y t)) /\
  (forall (l:lit) n,
     subst_var x y (open_rec n z l) = open_rec n (subst_var x y z) (subst_var x y l)) /\
  (forall (d:def) n,
     subst_var x y (open_rec n z d) = open_rec n (subst_var x y z) (subst_var x y d)) /\
  (forall (ds:defs) n,
     subst_var x y (open_rec n z ds) = open_rec n (subst_var x y z) (subst_var x y ds)).
Proof. intros x y z. exact (imm_subst_open_commut_trm x y z). Qed.

Lemma imm_subst_fresh_item_proj : forall x y (i:item),
  x \notin fv i -> subst_var x y i = i.
Proof. intros x y i. exact (@imm_subst_fresh_item x y i). Qed.

Lemma imm_subst_fresh_stack : forall x y (s:stack),
  x \notin stack_fv s -> stack_subst_var x y s = s.
Proof.
  intros x y s. induction s as [|f fs IH]; cbn.
  - reflexivity.
  - intros H.
    apply notin_union_r in H. destruct H as [Hf Hfs].
    rewrite (@imm_subst_fresh_frame x y f Hf).
    change (stack_cons f (stack_subst_var x y fs) = stack_cons f fs).
    rewrite (IH Hfs). reflexivity.
Qed.

Lemma imm_subst_fresh_stack_proj : forall x y (s:stack),
  x \notin fv s -> subst_var x y s = s.
Proof. intros x y s H. exact (@imm_subst_fresh_stack x y s H). Qed.

Lemma imm_subst_open_commut_item : forall x y z (i:item) n,
  subst_item x y (open_rec_item n z i) = open_rec_item n (subst_var x y z) (subst_item x y i).
Proof.
  intros x y z i n.
  destruct (imm_subst_open_commut_trm_proj x y z) as [Ht [Hl [Hd Hds]]].
  destruct i; cbn.
  - rewrite (Hds d n). reflexivity.
  - rewrite (Ht t (S n)). reflexivity.
Qed.

Lemma imm_subst_open_commut_item_proj : forall x y z (i:item) n,
  subst_var x y (open_rec n z i) = open_rec n (subst_var x y z) (subst_var x y i).
Proof. intros x y z i n. exact (@imm_subst_open_commut_item x y z i n). Qed.

Lemma imm_subst_open_commut_frame : forall x y z (f:frame) n,
  frame_subst_var x y (frame_open n z f) = frame_open n (subst_var x y z) (frame_subst_var x y f).
Proof.
  intros x y z f n.
  destruct (imm_subst_open_commut_trm_proj x y z) as [Ht _].
  destruct f; cbn. rewrite (Ht t n). reflexivity.
Qed.

Lemma imm_subst_open_commut_frame_proj : forall x y z (f:frame) n,
  subst_var x y (open_rec n z f) = open_rec n (subst_var x y z) (subst_var x y f).
Proof. intros x y z f n. exact (@imm_subst_open_commut_frame x y z f n). Qed.

Lemma imm_subst_open_commut_stack : forall x y z (s:stack) n,
  stack_subst_var x y (stack_open n z s) = stack_open n (subst_var x y z) (stack_subst_var x y s).
Proof.
  intros x y z s n. induction s as [|f fs IH]; cbn.
  - reflexivity.
  - rewrite (imm_subst_open_commut_frame_proj x y z f (S n)).
    f_equal.
    change (stack_subst_var x y (stack_open n z fs)
            = stack_open n (subst_var x y z) (stack_subst_var x y fs)).
    exact IH.
Qed.

Lemma imm_subst_open_commut_stack_proj : forall x y z (s:stack) n,
  subst_var x y (open_rec n z s) = open_rec n (subst_var x y z) (subst_var x y s).
Proof. intros x y z s n. exact (@imm_subst_open_commut_stack x y z s n). Qed.

#[export] Instance imm_sf_avar : SubstFresh AvarAbstractSyntax :=
  { subst_fresh := imm_subst_fresh_avar }.
#[export] Instance imm_sf_typ : SubstFresh TypAbstractSyntax :=
  { subst_fresh := fun x y T => proj1 (imm_subst_fresh_typ_dec_proj x y) T }.
#[export] Instance imm_sf_dec : SubstFresh DecAbstractSyntax :=
  { subst_fresh := fun x y D => proj2 (imm_subst_fresh_typ_dec_proj x y) D }.
#[export] Instance imm_sf_trm : SubstFresh TrmAbstractSyntax :=
  { subst_fresh := fun x y t => proj1 (imm_subst_fresh_trm_proj x y) t }.
#[export] Instance imm_sf_lit : SubstFresh LitAbstractSyntax :=
  { subst_fresh := fun x y l => proj1 (proj2 (imm_subst_fresh_trm_proj x y)) l }.
#[export] Instance imm_sf_def : SubstFresh DefAbstractSyntax :=
  { subst_fresh := fun x y d => proj1 (proj2 (proj2 (imm_subst_fresh_trm_proj x y))) d }.
#[export] Instance imm_sf_defs : SubstFresh DefsAbstractSyntax :=
  { subst_fresh := fun x y ds => proj2 (proj2 (proj2 (imm_subst_fresh_trm_proj x y))) ds }.
#[export] Instance imm_sf_item : SubstFresh ItemAbstractSyntax :=
  { subst_fresh := imm_subst_fresh_item_proj }.
#[export] Instance imm_sf_frame : SubstFresh FrameAbstractSyntax :=
  { subst_fresh := imm_subst_fresh_frame }.
#[export] Instance imm_sf_stack : SubstFresh StackAbstractSyntax :=
  { subst_fresh := imm_subst_fresh_stack_proj }.

#[export] Instance imm_soc_avar : SubstOpenCommut AvarAbstractSyntax :=
  { subst_open_commut := imm_subst_open_commut_avar }.
#[export] Instance imm_soc_typ : SubstOpenCommut TypAbstractSyntax :=
  { subst_open_commut := fun x y z T n => proj1 (imm_subst_open_commut_typ_dec_proj x y z) T n }.
#[export] Instance imm_soc_dec : SubstOpenCommut DecAbstractSyntax :=
  { subst_open_commut := fun x y z D n => proj2 (imm_subst_open_commut_typ_dec_proj x y z) D n }.
#[export] Instance imm_soc_trm : SubstOpenCommut TrmAbstractSyntax :=
  { subst_open_commut := fun x y z t n => proj1 (imm_subst_open_commut_trm_proj x y z) t n }.
#[export] Instance imm_soc_lit : SubstOpenCommut LitAbstractSyntax :=
  { subst_open_commut := fun x y z l n => proj1 (proj2 (imm_subst_open_commut_trm_proj x y z)) l n }.
#[export] Instance imm_soc_def : SubstOpenCommut DefAbstractSyntax :=
  { subst_open_commut := fun x y z d n => proj1 (proj2 (proj2 (imm_subst_open_commut_trm_proj x y z))) d n }.
#[export] Instance imm_soc_defs : SubstOpenCommut DefsAbstractSyntax :=
  { subst_open_commut := fun x y z ds n => proj2 (proj2 (proj2 (imm_subst_open_commut_trm_proj x y z))) ds n }.
#[export] Instance imm_soc_item : SubstOpenCommut ItemAbstractSyntax :=
  { subst_open_commut := imm_subst_open_commut_item_proj }.
#[export] Instance imm_soc_frame : SubstOpenCommut FrameAbstractSyntax :=
  { subst_open_commut := imm_subst_open_commut_frame_proj }.
#[export] Instance imm_soc_stack : SubstOpenCommut StackAbstractSyntax :=
  { subst_open_commut := imm_subst_open_commut_stack_proj }.

Lemma imm_fv_open_cases_var (x v : var) (n : nat) :
  fv (open_rec n x v) = fv v \/ fv (open_rec n x v) = \{x} \u fv v.
Proof. cbn. left. reflexivity. Qed.
#[export] Instance imm_foc_var : FvOpenCases VarAbstractSyntax :=
  { fv_open_cases := imm_fv_open_cases_var }.

Lemma imm_subst_var_self (x y : var) : subst_var x y x = y.
Proof. unfold subst_var, VarSubstVar. cbn. apply If_l. reflexivity. Qed.
Lemma imm_subst_var_neq (x y v : var) : v <> x -> subst_var x y v = v.
Proof. intros H. unfold subst_var, VarSubstVar. cbn. apply If_r. exact H. Qed.

Lemma imm_fv_subst_cases_var (x y v : var) :
  fv (subst_var x y v) = fv v /\ (x = y \/ x \notin fv v) \/
  x <> y /\ x \in fv v /\ fv (subst_var x y v) = fv v \- \{x} \u \{y}.
Proof.
  destruct (classic (v = x)) as [Heq | Hne].
  - rewrite Heq. rewrite imm_subst_var_self.
    unfold fv, VarFreeVar. cbn.
    destruct (classic (x = y)) as [Hxy | Hxy].
    + subst y. left. split; [reflexivity | left; reflexivity].
    + right. split; [exact Hxy | split].
      * rewrite in_singleton. reflexivity.
      * apply fset_extens; intros z Hz;
        repeat rewrite in_union in *; repeat rewrite in_remove in *;
        repeat rewrite in_singleton in *; repeat rewrite notin_singleton in *;
        try subst; tauto.
  - rewrite imm_subst_var_neq; [| exact Hne].
    unfold fv, VarFreeVar. cbn.
    left. split; [reflexivity | right].
    apply notin_singleton_l. intro E. apply Hne. symmetry. exact E.
Qed.
#[export] Instance imm_fsc_var : FvSubstCases VarAbstractSyntax :=
  { fv_subst_cases := imm_fv_subst_cases_var }.

Lemma imm_fv_subst_subset (A : Set) `{AS : AbstractSyntax A} {FSC : FvSubstCases AS}
      (x y : var) (a : A) :
  fv (subst_var x y a) \c fv a \u \{y}.
Proof.
  destruct (fv_subst_cases x y a) as [[Heq1 _] | [_ [_ Heq2]]].
  - rewrite Heq1. apply subset_union_weak_l.
  - rewrite Heq2. apply subset_union_2.
    + intros z Hz. rewrite in_remove in Hz. tauto.
    + apply subset_refl.
Qed.

Lemma imm_subst_fresh_var (x y v : var) : x \notin fv v -> subst_var x y v = v.
Proof.
  intros H. apply imm_subst_var_neq.
  intro E. exact ((notin_singleton_r H) (eq_sym E)).
Qed.
#[export] Instance imm_sf_var : SubstFresh VarAbstractSyntax :=
  { subst_fresh := imm_subst_fresh_var }.

Lemma imm_subst_open_commut_var (x y z v : var) (n : nat) :
  subst_var x y (open_rec n z v) = open_rec n (subst_var x y z) (subst_var x y v).
Proof. cbn. reflexivity. Qed.
#[export] Instance imm_soc_var : SubstOpenCommut VarAbstractSyntax :=
  { subst_open_commut := imm_subst_open_commut_var }.

Lemma imm_fv_subst_subset_mem (A : Set) `{AS : AbstractSyntax A} {FSC : FvSubstCases AS}
      (x y : var) (a : A) (z : var) :
  z \in fv (subst_var x y a) -> z \in fv a \/ z = y.
Proof.
  intros Hz.
  destruct (fv_subst_cases x y a) as [[Heq1 _] | [_ [_ Heq2]]].
  - rewrite Heq1 in Hz. left. exact Hz.
  - rewrite Heq2 in Hz. rewrite in_union in Hz. destruct Hz as [Hz | Hz].
    + left. rewrite in_remove in Hz. tauto.
    + right. rewrite in_singleton in Hz. exact Hz.
Qed.

Lemma imm_fv_var (y : var) : fv y = \{y}.
Proof. unfold fv, VarFreeVar. reflexivity. Qed.

Lemma imm_fv_env_cons (w y : var) (ys : renv) :
  fv_env (cons (w, y) ys) = fv y \u fv_env ys.
Proof. unfold fv_in_values. rewrite values_def. cbn. reflexivity. Qed.

Lemma imm_fv_subst_mem_var (x y v z : var) :
  z \in fv (subst_var x y v) -> z \in fv v \/ z = y.
Proof.
  intros Hz. destruct (imm_fv_subst_cases_var x y v) as [[Heq1 _] | [_ [_ Heq2]]].
  - rewrite Heq1 in Hz. left. exact Hz.
  - rewrite Heq2 in Hz. rewrite in_union in Hz. destruct Hz as [Hz | Hz].
    + left. rewrite in_remove in Hz. tauto.
    + right. rewrite in_singleton in Hz. exact Hz.
Qed.

Lemma imm_fv_subst_mem_avar (x y : var) (a : avar) (z : var) :
  z \in fv (subst_var x y a) -> z \in fv a \/ z = y.
Proof.
  intros Hz. destruct (imm_fv_subst_cases_avar x y a) as [[Heq1 _] | [_ [_ Heq2]]].
  - rewrite Heq1 in Hz. left. exact Hz.
  - rewrite Heq2 in Hz. rewrite in_union in Hz. destruct Hz as [Hz | Hz].
    + left. rewrite in_remove in Hz. tauto.
    + right. rewrite in_singleton in Hz. exact Hz.
Qed.

Lemma imm_deref_var_mem (e : renv) :
  forall (d : var) (z : var),
    z \in fv (deref_base VarSubstVar e d) -> z \in fv d \/ z \in fv_env e.
Proof.
  induction e as [| [w y] ys IH]; intros d z H; cbn in *.
  - left. exact H.
  - apply IH in H. destruct H as [H | H].
    + pose proof (@imm_fv_subst_mem_var w y d z H) as K. destruct K as [Hd | Hy].
      * left. exact Hd.
      * subst z. right. rewrite imm_fv_env_cons. rewrite in_union. left.
        rewrite imm_fv_var. apply in_singleton_self.
    + right. rewrite imm_fv_env_cons. rewrite in_union. right. exact H.
Qed.

#[export] Instance imm_dif_var : @DerefInFv var deref_var VarFreeVar :=
  { deref_in_fv := fun (x : var) (e : renv) (d : var) (H : x \in fv (deref_var e d)) => @imm_deref_var_mem e d x H }.

Lemma imm_deref_avar_mem (e : renv) :
  forall (d : avar) (z : var),
    z \in fv (deref_base AvarSubstVar e d) -> z \in fv d \/ z \in fv_env e.
Proof.
  induction e as [| [w y] ys IH]; intros d z H; cbn in *.
  - left. exact H.
  - apply IH in H. destruct H as [H | H].
    + pose proof (@imm_fv_subst_mem_avar w y d z H) as K. destruct K as [Hd | Hy].
      * left. exact Hd.
      * subst z. right. rewrite imm_fv_env_cons. rewrite in_union. left.
        rewrite imm_fv_var. apply in_singleton_self.
    + right. rewrite imm_fv_env_cons. rewrite in_union. right. exact H.
Qed.

#[export] Instance imm_dif_avar : @DerefInFv avar deref_avar AvarFreeVar :=
  { deref_in_fv := fun (x : var) (e : renv) (d : avar) (H : x \in fv (deref_avar e d)) => @imm_deref_avar_mem e d x H }.

Lemma imm_deref_def_mem (e : renv) :
  forall (d : def) (z : var),
    z \in fv (deref_def e d) -> z \in fv d \/ z \in fv_env e.
Proof.
  intros d z H. destruct d; cbn in *.
  - left. exact H.
  - pose proof (@imm_deref_avar_mem e a z H) as K. destruct K as [Ha | He].
    + left. exact Ha.
    + right. exact He.
  - left. exact H.
Qed.

#[export] Instance imm_dif_def : @DerefInFv def deref_def DefFreeVar :=
  { deref_in_fv := fun (x : var) (e : renv) (d : def) (H : x \in fv (deref_def e d)) => @imm_deref_def_mem e d x H }.

Lemma imm_deref_defs_mem (e : renv) :
  forall (ds : defs) (z : var),
    z \in fv (deref_defs_fix e ds) -> z \in fv ds \/ z \in fv_env e.
Proof.
  induction ds as [| ds IH d]; intros z H; cbn in *.
  - apply in_empty_inv in H. destruct H.
  - rewrite in_union in H. destruct H as [H | H].
    + apply IH in H. destruct H as [H | H].
      * left. rewrite in_union. left. exact H.
      * right. exact H.
    + pose proof (@imm_deref_def_mem e d z H) as K. destruct K as [Hd | He].
      * left. rewrite in_union. right. exact Hd.
      * right. exact He.
Qed.

#[export] Instance imm_dif_defs : @DerefInFv defs deref_defs DefsFreeVar :=
  { deref_in_fv := fun (x : var) (e : renv) (d : defs) (H : x \in fv (deref_defs e d)) => @imm_deref_defs_mem e d x H }.

Lemma imm_dom_env_fv_config_mem (t : trm) (s : stack) (Sigma : heap) (e : renv)
      (Lv : fset var) (x : var) :
  x \in dom e -> x \in fv_config (t ; s ; Sigma ; e ; Lv).
Proof.
  intros Hx. cbn. repeat rewrite in_union. tauto.
Qed.

Lemma imm_dom_env_fv_config (t : trm) (s : stack) (Sigma : heap) (e : renv) (Lv : fset var) :
  dom e \c fv_config (t ; s ; Sigma ; e ; Lv).
Proof.
  intros x Hx. eapply imm_dom_env_fv_config_mem. exact Hx.
Qed.

Lemma imm_notin_dom_env_of_notin_fv_config (t : trm) (s : stack) (Sigma : heap)
      (e : renv) (Lv : fset var) (y : var) :
  y \notin fv_config (t ; s ; Sigma ; e ; Lv) -> y \notin dom e.
Proof.
  intros H Hin. apply H. eapply imm_dom_env_fv_config_mem. exact Hin.
Qed.

Lemma imm_fresh_one (v : var) (t : trm) (s : stack) (Sigma : heap) (e : renv) (Lv : fset var) :
  fresh_in_config (v :: nil) (t ; s ; Sigma ; e ; Lv) ->
  v \notin fv_config (t ; s ; Sigma ; e ; Lv).
Proof.
  intros Hf. unfold fresh_in_config in Hf. cbn [LibList.length] in Hf. cbn [fresh] in Hf.
  destruct Hf as [H _]. exact H.
Qed.

Lemma imm_fresh_two (y w : var) (t : trm) (s : stack) (Sigma : heap) (e : renv) (Lv : fset var) :
  fresh_in_config (y :: w :: nil) (t ; s ; Sigma ; e ; Lv) ->
  y \notin fv_config (t ; s ; Sigma ; e ; Lv) /\
  w \notin fv_config (t ; s ; Sigma ; e ; Lv).
Proof.
  intros Hf. unfold fresh_in_config in Hf. cbn [LibList.length] in Hf. cbn [fresh] in Hf.
  destruct Hf as [Hy [Hw _]]. split; [exact Hy | ].
  intro Hin. apply Hw. apply subset_union_weak_l. exact Hin.
Qed.

Lemma imm_red_renv_dom_mono (C C' : config) :
  C ↦ C' -> dom (config_env C) \c dom (config_env C').
Proof.
  intros Hred. destruct Hred as
    [ yObj wObj m Sigma e Lv yVal wVal ds fs Hfresh Hbw Hby Hdf
    | yObj wObj m Sigma e Lv yArg wArg Sigma' fs Hu Hbw Hby
    | yObj wObj m Sigma e Lv wArg t ds fs Hby Hdf Hbw
    | yFun wFun wArg Sigma e Lv t fs Hby Hbw
    | T t1 t2 Sigma e Lv y w fs Hfresh Hneq
    | T ds t Sigma e Lv y w fs Hfresh Hneq
    | t Sigma e Lv x fs
    | s t fs Sigma e Lv ].
  - cbn. rewrite dom_push. apply subset_union_weak_r.
  - cbn. apply subset_refl.
  - cbn. apply subset_refl.
  - cbn. apply subset_refl.
  - cbn. rewrite dom_push. apply subset_union_weak_r.
  - cbn. rewrite dom_push. apply subset_union_weak_r.
  - cbn. apply subset_refl.
  - cbn. apply subset_refl.
Qed.

Lemma imm_red_closure_renv_dom_subset (C1 C2 : config) (n : nat) :
  C1 ⊣ n ↦* C2 -> dom (config_env C1) \c dom (config_env C2).
Proof.
  intros H. induction H as [C | C1' C2' C3' n' Hred IH Hstep].
  - apply subset_refl.
  - eapply imm_subset_trans; [ exact IH | eapply imm_red_renv_dom_mono; exact Hstep ].
Qed.

Lemma imm_red_renv_binds_mono (C C' : config) :
  C ↦ C' -> forall w y, binds w y (config_env C) -> binds w y (config_env C').
Proof.
  intros Hred. destruct Hred as
    [ yObj wObj m Sigma e Lv yVal wVal ds fs Hfresh Hbw Hby Hdf
    | yObj wObj m Sigma e Lv yArg wArg Sigma' fs Hu Hbw Hby
    | yObj wObj m Sigma e Lv wArg t ds fs Hby Hdf Hbw
    | yFun wFun wArg Sigma e Lv t fs Hby Hbw
    | T t1 t2 Sigma e Lv y w fs Hfresh Hneq
    | T ds t Sigma e Lv y w fs Hfresh Hneq
    | t Sigma e Lv x fs
    | s t fs Sigma e Lv ].
  - intros w0 y0 Hb. cbn in *. eapply binds_push_neq; [ exact Hb | ].
    destruct Hfresh as [Hnf _].
    assert (Hnd : wVal \notin dom e).
    { intro Hin. apply Hnf. repeat rewrite in_union. tauto. }
    intro E. subst w0. apply Hnd. eapply imm_binds_in_dom. exact Hb.
  - intros w0 y0 Hb. cbn in *. exact Hb.
  - intros w0 y0 Hb. cbn in *. exact Hb.
  - intros w0 y0 Hb. cbn in *. exact Hb.
  - intros w0 y0 Hb. cbn in *. eapply binds_push_neq; [ exact Hb | ].
    destruct Hfresh as [Hy [Hw _]].
    assert (Hnd : w \notin dom e).
    { intro Hin. apply Hw. repeat rewrite in_union. tauto. }
    intro E. subst w0. apply Hnd. eapply imm_binds_in_dom. exact Hb.
  - intros w0 y0 Hb. cbn in *. eapply binds_push_neq; [ exact Hb | ].
    destruct Hfresh as [Hy [Hw _]].
    assert (Hnd : w \notin dom e).
    { intro Hin. apply Hw. repeat rewrite in_union. tauto. }
    intro E. subst w0. apply Hnd. eapply imm_binds_in_dom. exact Hb.
  - intros w0 y0 Hb. cbn in *. exact Hb.
  - intros w0 y0 Hb. cbn in *. exact Hb.
Qed.

Lemma imm_red_closure_renv_binds_mono (C1 C2 : config) (n : nat) :
  C1 ⊣ n ↦* C2 -> forall w y, binds w y (config_env C1) -> binds w y (config_env C2).
Proof.
  intros H. induction H as [C | C1' C2' C3' n' Hred IH Hstep].
  - intros w0 y0 Hb. exact Hb.
  - intros w0 y0 Hb. apply IH in Hb.
    eapply imm_red_renv_binds_mono; eassumption.
Qed.

Lemma imm_fv_open_subset (A : Set) `{AS : AbstractSyntax A} {FOC : FvOpenCases AS}
      (x : var) (a : A) (n : nat) :
  fv (open_rec n x a) \c fv a \u \{x}.
Proof.
  destruct (fv_open_cases x a n) as [Heq | Heq]; rewrite Heq.
  - apply subset_union_weak_l.
  - intros z Hz. rewrite in_union in Hz. destruct Hz as [Hz | Hz].
    + rewrite in_singleton in Hz. subst z.
      rewrite in_union. right. apply in_singleton_self.
    + rewrite in_union. left. exact Hz.
Qed.

Lemma imm_fv_open_subset_mem (A : Set) `{AS : AbstractSyntax A} {FOC : FvOpenCases AS}
      (x : var) (a : A) (n : nat) (z : var) :
  z \in fv (open_rec n x a) -> z \in fv a \/ z = x.
Proof.
  intros Hz.
  destruct (fv_open_cases x a n) as [Heq | Heq].
  - rewrite Heq in Hz. left. exact Hz.
  - rewrite Heq in Hz. rewrite in_union in Hz. destruct Hz as [Hz | Hz].
    + right. rewrite in_singleton in Hz. exact Hz.
    + left. exact Hz.
Qed.

(* Removing one binder from a context (the topmost binder of a given name). *)
Inductive ctx_rem : var -> ctx -> ctx -> Prop :=
| ctx_rem_top G x vk T : ctx_rem x (G § x / vk ~ T) G
| ctx_rem_push G1 G2 x y vk T :
    ctx_rem x G1 G2 -> ctx_rem x (G1 § y / vk ~ T) (G2 § y / vk ~ T)
| ctx_rem_stop G1 G2 x :
    ctx_rem x G1 G2 -> ctx_rem x (ctx_stop G1) (ctx_stop G2)
| ctx_rem_hide G1 G2 x :
    ctx_rem x G1 G2 -> ctx_rem x (ctx_hide G1) (ctx_hide G2).

Lemma imm_ctx_binds_rem (x : var) (G G' : ctx) (Hrem : ctx_rem x G G') :
  forall (v : var) (T : typ), v <> x -> ctx_binds v T G -> ctx_binds v T G'.
Proof.
  induction Hrem as [G0 x0 vk T0 | G1 G2 x0 y vk T0 Hrem IH
                    | G1 G2 x0 Hrem IH | G1 G2 x0 Hrem IH];
    intros v T Hneq Hb.
  - inversion Hb; subst.
    + exfalso. apply Hneq. reflexivity.
    + assumption.
  - inversion Hb; subst.
    + apply ctx_binds_e.
    + eapply ctx_binds_n; [ eassumption | ].
      eapply IH; [ exact Hneq | eassumption ].
  - inversion Hb.
  - inversion Hb; subst. apply ctx_binds_hide. eapply IH; eassumption.
Qed.

Lemma imm_ctx_vis_rem (x : var) (G G' : ctx) (Hrem : ctx_rem x G G') :
  forall (v : var), v <> x -> ctx_vis G v -> ctx_vis G' v.
Proof.
  induction Hrem as [G0 x0 vk T0 | G1 G2 x0 y vk T0 Hrem IH
                    | G1 G2 x0 Hrem IH | G1 G2 x0 Hrem IH];
    intros v Hneq Hv.
  - inversion Hv; subst.
    + exfalso. apply Hneq. reflexivity.
    + assumption.
  - inversion Hv; subst.
    + apply ctx_vis_e.
    + eapply ctx_vis_n; [ eassumption | ].
      eapply IH; [ exact Hneq | eassumption ].
  - inversion Hv.
  - inversion Hv.
Qed.

Lemma imm_subst_ctx_push (x y : var) (G : ctx) (v : var) (vk : varkind) (T : typ) :
  subst_ctx x y (G § v / vk ~ T) =
  (subst_ctx x y G) § v / vk ~ (subst_var x y T).
Proof. reflexivity. Qed.

Lemma imm_subst_ctx_hide (x y : var) (G : ctx) :
  subst_ctx x y (ctx_hide G) = ctx_hide (subst_ctx x y G).
Proof. reflexivity. Qed.

Lemma imm_subst_ctx_stop (x y : var) (G : ctx) :
  subst_ctx x y (ctx_stop G) = ctx_stop (subst_ctx x y G).
Proof. reflexivity. Qed.

Lemma imm_ctx_rem_dom_in (x : var) (G G' : ctx) :
  ctx_rem x G G' -> x \in ctx_dom G.
Proof.
  intros H. induction H as
    [G0 x0 vk T0 | G1 G2 x0 y vk T0 Hrem IH | G1 G2 x0 Hrem IH | G1 G2 x0 Hrem IH].
  - cbn. rewrite in_union. left. rewrite in_singleton. reflexivity.
  - cbn. rewrite in_union. right. exact IH.
  - cbn. exact IH.
  - cbn. exact IH.
Qed.

Lemma imm_ctx_rem_dom_subset (x : var) (G G' : ctx) :
  ctx_rem x G G' -> ctx_dom G' \c ctx_dom G.
Proof.
  intros H. induction H as
    [G0 x0 vk T0 | G1 G2 x0 y vk T0 Hrem IH | G1 G2 x0 Hrem IH | G1 G2 x0 Hrem IH].
  - cbn [ctx_dom]. apply subset_union_weak_r.
  - cbn [ctx_dom]. apply subset_union_2; [ apply subset_refl | exact IH ].
  - cbn [ctx_dom]. exact IH.
  - cbn [ctx_dom]. exact IH.
Qed.

Lemma imm_ctx_binds_subst (z y : var) (G : ctx) (v : var) (T : typ) :
  ctx_binds v T G -> ctx_binds v (subst_var z y T) (subst_ctx z y G).
Proof.
  intros Hb. induction Hb as [v0 vk t G0 | v0 v2 vk t t2 G0 Hneq Hb IH
                             | v0 t G0 Hb IH].
  - cbn. apply ctx_binds_e.
  - cbn. eapply ctx_binds_n; [ exact Hneq | exact IH ].
  - cbn. apply ctx_binds_hide. exact IH.
Qed.

Lemma imm_ctx_vis_subst (z y : var) (G : ctx) (v : var) :
  ctx_vis G v -> ctx_vis (subst_ctx z y G) v.
Proof.
  intros Hv. induction Hv as [v0 vk t G0 | v0 v2 vk t G0 Hneq Hv IH].
  - cbn. apply ctx_vis_e.
  - cbn. eapply ctx_vis_n; [ exact Hneq | exact IH ].
Qed.

Lemma imm_ctx_dom_subst (z y : var) (G : ctx) :
  ctx_dom (subst_ctx z y G) = ctx_dom G.
Proof.
  induction G as [| G0 IH v vk t | G0 IH | G0 IH].
  - reflexivity.
  - cbn [ctx_map ctx_dom]. rewrite IH. reflexivity.
  - cbn [ctx_map ctx_dom]. rewrite IH. reflexivity.
  - cbn [ctx_map ctx_dom]. rewrite IH. reflexivity.
Qed.

Lemma imm_ctx_ok_subst (z y : var) (G : ctx) :
  ctx_ok G -> ctx_ok (subst_ctx z y G).
Proof.
  induction G as [| G0 IH v vk t | G0 IH | G0 IH]; intros Hok.
  - apply ctx_ok_empty.
  - cbn [ctx_map]. apply ctx_ok_push.
    + apply IH. inversion Hok; assumption.
    + rewrite imm_ctx_dom_subst. inversion Hok; assumption.
  - cbn [ctx_map]. apply ctx_ok_stop. apply IH. inversion Hok; assumption.
  - cbn [ctx_map]. apply ctx_ok_hide. apply IH. inversion Hok; assumption.
Qed.

Lemma imm_ctx_k_weaken_fresh (G : ctx) (x : var) (vk : varkind) (T : typ)
      (v : var) (vk0 : varkind) :
  ctx_k G v vk0 -> x §# G -> ctx_k (G § x / vk ~ T) v vk0.
Proof.
  intros [t [G2 Hk]] Hfresh. exists t, G2.
  pose proof (imm_binds_k_after_binds Hk) as Hb.
  pose proof (@imm_ctx_binds_dom G v t Hb) as Hdom.
  assert (Hneq : v <> x).
  { intro E. subst v. apply Hfresh. exact Hdom. }
  eapply ctx_binds_k_n; [ exact Hneq | exact Hk ].
Qed.

Lemma imm_all_tfree_k_push (A : Set) (AT : TFree A) (G : ctx) (x : var)
      (vk : varkind) (T : typ) (t : A) (vk0 : varkind) :
  @all_tfree_k A AT G t vk0 -> x §# G ->
  @all_tfree_k A AT (G § x / vk ~ T) t vk0.
Proof.
  intros H Hfresh v Hv.
  eapply imm_ctx_k_weaken_fresh; [ exact (H v Hv) | exact Hfresh ].
Qed.

Lemma imm_tfree_open_trm (x : var) :
  (forall (v : var) (t : trm), tfree v t -> forall n, tfree v (open_rec n x t)) /\
  (forall (v : var) (l : lit), tfree v l -> forall n, tfree v (open_rec n x l)) /\
  (forall (v : var) (d : def), tfree v d -> forall n, tfree v (open_rec n x d)) /\
  (forall (v : var) (ds : defs), tfree v ds -> forall n, tfree v (open_rec n x ds)).
Proof.
  apply tfree_mutind.
  all: try (intros; cbn; econstructor; eauto; fail).
  - intros v t1 t2 h IH n. cbn. apply tfree_trm_let_l. apply (IH n).
  - intros v t1 t2 h IH n. cbn. apply tfree_trm_let_r. apply (IH (S n)).
  - intros v t1 t2 h IH n. cbn. apply tfree_trm_lit_l. apply (IH n).
  - intros v t1 t2 h IH n. cbn. apply tfree_trm_lit_r. apply (IH (S n)).
  - intros v t T h IH n. cbn. apply tfree_lit_fun. apply (IH (S n)).
  - intros v ds T h IH n. cbn. apply tfree_lit_obj. apply (IH (S n)).
  - intros v t l h IH n. cbn. apply tfree_def_met. apply (IH (S (S n))).
  - intros v tl d h IH n. cbn. apply tfree_defs_cons_l. apply (IH n).
  - intros v tl d h IH n. cbn. apply tfree_defs_cons_r. apply (IH n).
Qed.

Lemma imm_tfree_open_stack (x : var) (s : stack) :
  forall (v : var), tfree v s -> forall n, tfree v (open_rec n x s).
Proof.
  destruct (imm_tfree_open_trm x) as [Htrm _].
  induction s as [| f fs IH]; intros v H n.
  - change (tfree_stack v stack_nil) in H. inversion H.
  - destruct f as [t]. cbn.
    change (tfree_stack v (stack_cons (frame_let t) fs)) in H.
    inversion H as [v0 t0 st0 Ht | v0 f0 fs0 Hfs]; subst.
    + cbn. apply tfree_stack_cons_l. exact (Htrm v t Ht (S n)).
    + cbn. apply tfree_stack_cons_r. exact (IH v Hfs n).
Qed.

Lemma imm_avar_open_eq (k : nat) (x v : var) (a : avar) :
  open_rec k x a = avar_f v -> a = avar_f v \/ v = x.
Proof.
  intros E. destruct a.
  - unfold open_rec, AvarOpenable in E. cbn in E.
    destruct (classic (k = n)) as [Heq | Hne].
    + assert (Hi : (If k = n then avar_f x else avar_b n) = avar_f x) by (apply If_l; exact Heq).
      rewrite Hi in E. injection E as E. right. symmetry. exact E.
    + assert (Hi : (If k = n then avar_f x else avar_b n) = avar_b n) by (apply If_r; exact Hne).
      rewrite Hi in E. discriminate E.
  - unfold open_rec, AvarOpenable in E. cbn in E.
    injection E as E. left. subst. reflexivity.
Qed.

Lemma imm_tfree_open_inv_trm :
  (forall (v:var) (t:trm), tfree v t ->
     forall (k:nat) (x:var) (tR:trm), t = open_rec k x tR -> tfree v tR \/ v = x) /\
  (forall (v:var) (l:lit), tfree v l ->
     forall (k:nat) (x:var) (lR:lit), l = open_rec k x lR -> tfree v lR \/ v = x) /\
  (forall (v:var) (d:def), tfree v d ->
     forall (k:nat) (x:var) (dR:def), d = open_rec k x dR -> tfree v dR \/ v = x) /\
  (forall (v:var) (ds:defs), tfree v ds ->
     forall (k:nat) (x:var) (dsR:defs), ds = open_rec k x dsR -> tfree v dsR \/ v = x).
Proof.
  apply tfree_mutind.
  - (* var *) intros v k x tR H. destruct tR; cbn in H; try discriminate.
    injection H as H. symmetry in H.
    destruct (@imm_avar_open_eq k x v a H) as [E | E].
    + left. rewrite E. apply tfree_trm_var.
    + right. exact E.
  - (* read *) intros v l k x tR H. destruct tR; cbn in H; try discriminate.
    injection H as Ha Hl. symmetry in Ha.
    destruct (@imm_avar_open_eq k x v a Ha) as [E | E].
    + left. rewrite E. apply tfree_trm_read.
    + right. exact E.
  - (* apply_l *) intros v a2 k x tR H. destruct tR; cbn in H; try discriminate.
    injection H as Ha Ha2. symmetry in Ha.
    destruct (@imm_avar_open_eq k x v a Ha) as [E | E].
    + left. rewrite E. apply tfree_trm_apply_l.
    + right. exact E.
  - (* apply_r *) intros a1 v k x tR H. destruct tR; cbn in H; try discriminate.
    injection H as Ha1 Ha2. symmetry in Ha2.
    destruct (@imm_avar_open_eq k x v a0 Ha2) as [E | E].
    + left. rewrite E. apply tfree_trm_apply_r.
    + right. exact E.
  - (* let_l *) intros v t1 t2 Ht IHt k x tR H. destruct tR; cbn in H; try discriminate.
    injection H as H1 H2.
    destruct (IHt k x _ H1) as [H' | E].
    + left. eapply tfree_trm_let_l. exact H'.
    + right. exact E.
  - (* let_r *) intros v t1 t2 Ht IHt k x tR H. destruct tR; cbn in H; try discriminate.
    injection H as H1 H2.
    destruct (IHt (S k) x _ H2) as [H' | E].
    + left. eapply tfree_trm_let_r. exact H'.
    + right. exact E.
  - (* lit_l *) intros v l t Hl IHl k x tR H. destruct tR; cbn in H; try discriminate.
    injection H as H1 H2.
    destruct (IHl k x _ H1) as [H' | E].
    + left. eapply tfree_trm_lit_l. exact H'.
    + right. exact E.
  - (* lit_r *) intros v l t Ht IHt k x tR H. destruct tR; cbn in H; try discriminate.
    injection H as H1 H2.
    destruct (IHt (S k) x _ H2) as [H' | E].
    + left. eapply tfree_trm_lit_r. exact H'.
    + right. exact E.
  - (* write_l *) intros v a2 l k x tR H. destruct tR; cbn in H; try discriminate.
    injection H as Ha Hl Ha2. symmetry in Ha.
    destruct (@imm_avar_open_eq k x v a Ha) as [E | E].
    + left. rewrite E. apply tfree_trm_write_l.
    + right. exact E.
  - (* write_r *) intros a1 v l k x tR H. destruct tR; cbn in H; try discriminate.
    injection H as Ha Hl Ha2. symmetry in Ha2.
    destruct (@imm_avar_open_eq k x v a0 Ha2) as [E | E].
    + left. rewrite E. apply tfree_trm_write_r.
    + right. exact E.
  - (* call_l *) intros v a2 m k x tR H. destruct tR; cbn in H; try discriminate.
    injection H as Ha Hm Ha2. symmetry in Ha.
    destruct (@imm_avar_open_eq k x v a Ha) as [E | E].
    + left. rewrite E. apply tfree_trm_call_l.
    + right. exact E.
  - (* call_r *) intros a1 v m k x tR H. destruct tR; cbn in H; try discriminate.
    injection H as Ha Hm Ha2. symmetry in Ha2.
    destruct (@imm_avar_open_eq k x v a0 Ha2) as [E | E].
    + left. rewrite E. apply tfree_trm_call_r.
    + right. exact E.
  - (* lit_fun *) intros v t T Ht IHt k x lR H. destruct lR; cbn in H; try discriminate.
    injection H as HT Ht'.
    destruct (IHt (S k) x _ Ht') as [H' | E].
    + left. eapply tfree_lit_fun. exact H'.
    + right. exact E.
  - (* lit_obj *) intros v ds T Hds IHds k x lR H. destruct lR; cbn in H; try discriminate.
    injection H as HT Hds'.
    destruct (IHds (S k) x _ Hds') as [H' | E].
    + left. eapply tfree_lit_obj. exact H'.
    + right. exact E.
  - (* def_fld *) intros v l k x dR H. destruct dR; cbn in H; try discriminate.
    injection H as Hl Ha. symmetry in Ha.
    destruct (@imm_avar_open_eq k x v a Ha) as [E | E].
    + left. rewrite E. apply tfree_def_trm.
    + right. exact E.
  - (* def_met *) intros v t l Ht IHt k x dR H. destruct dR; cbn in H; try discriminate.
    injection H as Hl Ht'.
    destruct (IHt (S (S k)) x _ Ht') as [H' | E].
    + left. eapply tfree_def_met. exact H'.
    + right. exact E.
  - (* defs_cons_l *) intros v d ds Hds IHds k x dsR H. destruct dsR; cbn in H; try discriminate.
    injection H as Hds' Hd'.
    destruct (IHds k x _ Hds') as [H' | E].
    + left. eapply tfree_defs_cons_l. exact H'.
    + right. exact E.
  - (* defs_cons_r *) intros v d ds Hd IHd k x dsR H. destruct dsR; cbn in H; try discriminate.
    injection H as Hds' Hd'.
    destruct (IHd k x _ Hd') as [H' | E].
    + left. eapply tfree_defs_cons_r. exact H'.
    + right. exact E.
Qed.

Lemma imm_tfree_open_inv (v x : var) (t : trm) (n : nat) :
  tfree v (open_rec n x t) -> tfree v t \/ v = x.
Proof.
  intros H. destruct imm_tfree_open_inv_trm as [Htrm _].
  exact (Htrm v (open_rec n x t) H n x t eq_refl).
Qed.

Lemma imm_tfree_open_inv_lit (v x : var) (l : lit) (n : nat) :
  tfree v (open_rec n x l) -> tfree v l \/ v = x.
Proof.
  intros H. destruct imm_tfree_open_inv_trm as [_ [Hlit _]].
  exact (Hlit v (open_rec n x l) H n x l eq_refl).
Qed.

Lemma imm_tfree_open_inv_def (v x : var) (d : def) (n : nat) :
  tfree v (open_rec n x d) -> tfree v d \/ v = x.
Proof.
  intros H. destruct imm_tfree_open_inv_trm as [_ [_ [Hdef _]]].
  exact (Hdef v (open_rec n x d) H n x d eq_refl).
Qed.

Lemma imm_tfree_open_inv_defs (v x : var) (ds : defs) (n : nat) :
  tfree v (open_rec n x ds) -> tfree v ds \/ v = x.
Proof.
  intros H. destruct imm_tfree_open_inv_trm as [_ [_ [_ Hdefs]]].
  exact (Hdefs v (open_rec n x ds) H n x ds eq_refl).
Qed.

Lemma imm_tfree_open_inv_stack (v x : var) (s : stack) (n : nat) :
  tfree v (open_rec n x s) -> tfree v s \/ v = x.
Proof.
  destruct imm_tfree_open_inv_trm as [Htrm _].
  induction s as [| f fs IH]; intros H.
  - change (tfree_stack v stack_nil) in H. inversion H.
  - destruct f as [t]. cbn in H.
    change (tfree_stack v (stack_cons (frame_let (open_rec (S n) x t)) (open_rec n x fs))) in H.
    inversion H as [v0 t0 st0 Ht | v0 f0 fs0 Hfs]; subst.
    + destruct (Htrm v (open_rec (S n) x t) Ht (S n) x t eq_refl) as [H' | E].
      * left. cbn. apply tfree_stack_cons_l. exact H'.
      * right. exact E.
    + destruct (IH Hfs) as [H' | E].
      * left. cbn. apply tfree_stack_cons_r. exact H'.
      * right. exact E.
Qed.

#[export] Instance imm_toi_trm : @TFreeOpenInv trm tfree_trm TrmOpenable :=
  { tfree_open_inv := imm_tfree_open_inv }.
#[export] Instance imm_toi_lit : @TFreeOpenInv lit tfree_lit LitOpenable :=
  { tfree_open_inv := imm_tfree_open_inv_lit }.
#[export] Instance imm_toi_def : @TFreeOpenInv def tfree_def DefOpenable :=
  { tfree_open_inv := imm_tfree_open_inv_def }.
#[export] Instance imm_toi_defs : @TFreeOpenInv defs tfree_defs DefsOpenable :=
  { tfree_open_inv := imm_tfree_open_inv_defs }.
#[export] Instance imm_toi_stack : @TFreeOpenInv stack tfree_stack StackOpenable :=
  { tfree_open_inv := imm_tfree_open_inv_stack }.


Lemma imm_tfree_in_fv_trm :
  (forall (v:var) (t:trm), tfree v t -> v \in fv_trm t) /\
  (forall (v:var) (l:lit), tfree v l -> v \in fv_lit l) /\
  (forall (v:var) (d:def), tfree v d -> v \in fv_def d) /\
  (forall (v:var) (ds:defs), tfree v ds -> v \in fv_defs ds).
Proof.
  apply tfree_mutind.
  all: try (intros; cbn; try rewrite in_union; auto using in_singleton_self; fail).
  all: intros; eauto using in_singleton_self.
Qed.

Lemma imm_tfree_in_fv (v : var) (t : trm) : tfree v t -> v \in fv t.
Proof. intros H. exact (proj1 imm_tfree_in_fv_trm v t H). Qed.
Lemma imm_tfree_in_fv_lit (v : var) (l : lit) : tfree v l -> v \in fv l.
Proof. intros H. exact (proj1 (proj2 imm_tfree_in_fv_trm) v l H). Qed.
Lemma imm_tfree_in_fv_def (v : var) (d : def) : tfree v d -> v \in fv d.
Proof. intros H. exact (proj1 (proj2 (proj2 imm_tfree_in_fv_trm)) v d H). Qed.
Lemma imm_tfree_in_fv_defs (v : var) (ds : defs) : tfree v ds -> v \in fv ds.
Proof. intros H. exact (proj2 (proj2 (proj2 imm_tfree_in_fv_trm)) v ds H). Qed.

Lemma imm_tfree_in_fv_stack (v : var) (s : stack) : tfree v s -> v \in fv s.
Proof.
  intros H. induction H as [v0 t st Ht | v0 f st Hfs IH]; cbn.
  - rewrite in_union. left. exact (proj1 imm_tfree_in_fv_trm v0 t Ht).
  - rewrite in_union. right. exact IH.
Qed.

Lemma imm_tfree_open_trm1 (v x : var) (t : trm) (n : nat) :
  tfree v t -> tfree v (open_rec n x t).
Proof. intros H. exact (proj1 (imm_tfree_open_trm x) v t H n). Qed.
Lemma imm_tfree_open_lit1 (v x : var) (l : lit) (n : nat) :
  tfree v l -> tfree v (open_rec n x l).
Proof. intros H. exact (proj1 (proj2 (imm_tfree_open_trm x)) v l H n). Qed.
Lemma imm_tfree_open_def1 (v x : var) (d : def) (n : nat) :
  tfree v d -> tfree v (open_rec n x d).
Proof. intros H. exact (proj1 (proj2 (proj2 (imm_tfree_open_trm x))) v d H n). Qed.
Lemma imm_tfree_open_defs1 (v x : var) (ds : defs) (n : nat) :
  tfree v ds -> tfree v (open_rec n x ds).
Proof. intros H. exact (proj2 (proj2 (proj2 (imm_tfree_open_trm x))) v ds H n). Qed.
Lemma imm_tfree_open_stack1 (v x : var) (s : stack) (n : nat) :
  tfree v s -> tfree v (open_rec n x s).
Proof. intros H. exact (@imm_tfree_open_stack x s v H n). Qed.

#[export] Instance imm_to_trm : @TFreeOpen trm tfree_trm TrmOpenable :=
  { tfree_open := imm_tfree_open_trm1 }.
#[export] Instance imm_to_lit : @TFreeOpen lit tfree_lit LitOpenable :=
  { tfree_open := imm_tfree_open_lit1 }.
#[export] Instance imm_to_def : @TFreeOpen def tfree_def DefOpenable :=
  { tfree_open := imm_tfree_open_def1 }.
#[export] Instance imm_to_defs : @TFreeOpen defs tfree_defs DefsOpenable :=
  { tfree_open := imm_tfree_open_defs1 }.
#[export] Instance imm_to_stack : @TFreeOpen stack tfree_stack StackOpenable :=
  { tfree_open := imm_tfree_open_stack1 }.


Lemma imm_avar_subst_self (x y : var) : subst_var x y (avar_f x) = avar_f y.
Proof.
  unfold subst_var, AvarSubstVar. cbn.
  assert (Hi : (If x = x then y else x) = y) by (apply If_l; reflexivity).
  rewrite Hi. reflexivity.
Qed.
Lemma imm_avar_subst_neq (x y v : var) : v <> x -> subst_var x y (avar_f v) = avar_f v.
Proof.
  intros H. unfold subst_var, AvarSubstVar. cbn.
  assert (Hi : (If v = x then y else v) = v) by (apply If_r; exact H).
  rewrite Hi. reflexivity.
Qed.

Lemma imm_avar_subst_intro (x y : var) (n : nat) (a : avar) :
  x \notin fv a -> open_rec n y a = subst_var x y (open_rec n x a).
Proof.
  intros H. destruct a.
  - unfold open_rec, AvarOpenable. cbn.
    destruct (classic (n = n0)) as [Heq | Hne].
    + assert (H1 : (If n = n0 then avar_f y else avar_b n0) = avar_f y) by (apply If_l; exact Heq).
      assert (H2 : (If n = n0 then avar_f x else avar_b n0) = avar_f x) by (apply If_l; exact Heq).
      rewrite H1, H2. rewrite imm_avar_subst_self. reflexivity.
    + assert (H1 : (If n = n0 then avar_f y else avar_b n0) = avar_b n0) by (apply If_r; exact Hne).
      assert (H2 : (If n = n0 then avar_f x else avar_b n0) = avar_b n0) by (apply If_r; exact Hne).
      rewrite H1, H2. cbn. reflexivity.
  - apply notin_singleton_r in H.
    unfold open_rec, AvarOpenable.
    rewrite imm_avar_subst_neq; [reflexivity | intro E; apply H; symmetry; exact E].
Qed.

Lemma imm_typ_subst_intro (x y : var) :
  (forall (T:typ) n, x \notin fv_typ T ->
     open_rec_typ n y T = subst_typ x y (open_rec_typ n x T)) /\
  (forall (D:dec) n, x \notin fv_dec D ->
     open_rec_dec n y D = subst_dec x y (open_rec_dec n x D)).
Proof.
  apply typ_mutind.
  - intros n H. reflexivity.
  - intros n H. reflexivity.
  - intros d IH n H. cbn. f_equal. apply IH. exact H.
  - intros t IHt t0 IHt0 n H. cbn. f_equal.
    + apply IHt. apply notin_union_r in H. exact (proj1 H).
    + apply IHt0. apply notin_union_r in H. exact (proj2 H).
  - intros t IHt t0 IHt0 n H. cbn. f_equal.
    + apply IHt. apply notin_union_r in H. exact (proj1 H).
    + apply IHt0. apply notin_union_r in H. exact (proj2 H).
  - intros a L a0 n H. cbn. f_equal.
    + apply imm_avar_subst_intro. apply notin_union_r in H. exact (proj1 H).
    + apply imm_avar_subst_intro. apply notin_union_r in H. exact (proj2 H).
  - intros t IHt n H. cbn. f_equal. apply IHt. exact H.
  - intros t IHt t0 IHt0 n H. cbn. f_equal.
    + apply IHt. apply notin_union_r in H. exact (proj1 H).
    + apply IHt0. apply notin_union_r in H. exact (proj2 H).
  - intros n H. reflexivity.
  - intros L t IHt t0 IHt0 n H. cbn. f_equal.
    + apply IHt. apply notin_union_r in H. exact (proj1 H).
    + apply IHt0. apply notin_union_r in H. exact (proj2 H).
  - intros f t IHt t0 IHt0 n H. cbn. f_equal.
    + apply IHt. apply notin_union_r in H. exact (proj1 H).
    + apply IHt0. apply notin_union_r in H. exact (proj2 H).
  - intros m t IHt t0 IHt0 t1 IHt1 n H. cbn. f_equal.
    + apply IHt. apply notin_union_r in H. exact (proj1 H).
    + apply IHt0. apply notin_union_r in H. destruct H as [H1 H2].
      apply notin_union_r in H2. exact (proj1 H2).
    + apply IHt1. apply notin_union_r in H. destruct H as [H1 H2].
      apply notin_union_r in H2. exact (proj2 H2).
Qed.

Lemma imm_trm_subst_intro (x y : var) :
  (forall (t:trm) n, x \notin fv_trm t ->
     open_rec_trm n y t = subst_trm x y (open_rec_trm n x t)) /\
  (forall (l:lit) n, x \notin fv_lit l ->
     open_rec_lit n y l = subst_lit x y (open_rec_lit n x l)) /\
  (forall (d:def) n, x \notin fv_def d ->
     open_rec_def n y d = subst_def x y (open_rec_def n x d)) /\
  (forall (ds:defs) n, x \notin fv_defs ds ->
     open_rec_defs n y ds = subst_defs x y (open_rec_defs n x ds)).
Proof.
  destruct (imm_typ_subst_intro x y) as [Htyp Hdec].
  apply trm_mutind.
  - intros a n H. cbn. f_equal. apply imm_avar_subst_intro. exact H.
  - intros a f n H. cbn. f_equal. apply imm_avar_subst_intro. exact H.
  - intros a a0 n H. cbn. f_equal.
    + apply imm_avar_subst_intro. apply notin_union_r in H. exact (proj1 H).
    + apply imm_avar_subst_intro. apply notin_union_r in H. exact (proj2 H).
  - intros t IHt t0 IHt0 n H. cbn. f_equal.
    + apply IHt. apply notin_union_r in H. exact (proj1 H).
    + apply IHt0. apply notin_union_r in H. exact (proj2 H).
  - intros l IHl t IHt n H. cbn. f_equal.
    + apply IHl. apply notin_union_r in H. exact (proj1 H).
    + apply IHt. apply notin_union_r in H. exact (proj2 H).
  - intros a f a0 n H. cbn. f_equal.
    + apply imm_avar_subst_intro. apply notin_union_r in H. exact (proj1 H).
    + apply imm_avar_subst_intro. apply notin_union_r in H. exact (proj2 H).
  - intros a m a0 n H. cbn. f_equal.
    + apply imm_avar_subst_intro. apply notin_union_r in H. exact (proj1 H).
    + apply imm_avar_subst_intro. apply notin_union_r in H. exact (proj2 H).
  - intros T t IHt n H. cbn. f_equal.
    + apply Htyp. apply notin_union_r in H. exact (proj1 H).
    + apply IHt. apply notin_union_r in H. exact (proj2 H).
  - intros T ds IHds n H. cbn. f_equal.
    + apply Htyp. apply notin_union_r in H. exact (proj1 H).
    + apply IHds. apply notin_union_r in H. exact (proj2 H).
  - intros l T n H. cbn. f_equal. apply Htyp. exact H.
  - intros l a n H. cbn. f_equal. apply imm_avar_subst_intro. exact H.
  - intros m t IHt n H. cbn. f_equal. apply IHt. exact H.
  - intros n H. reflexivity.
  - intros ds IHds d IHd n H. cbn. f_equal.
    + apply IHds. apply notin_union_r in H. exact (proj1 H).
    + apply IHd. apply notin_union_r in H. exact (proj2 H).
Qed.

Lemma imm_frame_subst_intro (x y : var) (f : frame) (n : nat) :
  x \notin fv f -> open_rec n y f = subst_var x y (open_rec n x f).
Proof.
  destruct f as [t]. intros H. cbn. f_equal.
  destruct (imm_trm_subst_intro x y) as [Htrm _]. apply Htrm. exact H.
Qed.

Lemma imm_item_subst_intro (x y : var) (i : item) (n : nat) :
  x \notin fv i -> open_rec n y i = subst_var x y (open_rec n x i).
Proof.
  intros H. destruct i; cbn.
  - destruct (imm_trm_subst_intro x y) as [_ [_ [_ Hdefs]]]. f_equal.
    apply Hdefs. exact H.
  - destruct (imm_trm_subst_intro x y) as [Htrm _]. f_equal.
    apply Htrm. exact H.
Qed.

Lemma imm_stack_subst_intro (x y : var) (s : stack) :
  forall n, x \notin fv s -> open_rec n y s = subst_var x y (open_rec n x s).
Proof.
  induction s as [| f fs IH]; intros n H.
  - reflexivity.
  - cbn. f_equal.
    + apply imm_frame_subst_intro. cbn in H.
      apply notin_union_r in H. exact (proj1 H).
    + apply IH. cbn in H. apply notin_union_r in H. exact (proj2 H).
Qed.

#[export] Instance imm_si_trm : @SubstIntro trm TrmOpenable TrmFreeVar TrmSubstVar TrmAbstractSyntax :=
  { subst_intro := fun x y n t H => (proj1 (imm_trm_subst_intro x y)) t n H }.
#[export] Instance imm_si_lit : @SubstIntro lit LitOpenable LitFreeVar LitSubstVar LitAbstractSyntax :=
  { subst_intro := fun x y n l H => (proj1 (proj2 (imm_trm_subst_intro x y))) l n H }.
#[export] Instance imm_si_def : @SubstIntro def DefOpenable DefFreeVar DefSubstVar DefAbstractSyntax :=
  { subst_intro := fun x y n d H => (proj1 (proj2 (proj2 (imm_trm_subst_intro x y)))) d n H }.
#[export] Instance imm_si_defs : @SubstIntro defs DefsOpenable DefsFreeVar DefsSubstVar DefsAbstractSyntax :=
  { subst_intro := fun x y n ds H => (proj2 (proj2 (proj2 (imm_trm_subst_intro x y)))) ds n H }.
#[export] Instance imm_si_frame : @SubstIntro frame FrameOpenable FrameFreeVar FrameSubstVar FrameAbstractSyntax :=
  { subst_intro := fun x y n f H => @imm_frame_subst_intro x y f n H }.
#[export] Instance imm_si_item : @SubstIntro item ItemOpenable ItemFreeVar ItemSubstVar ItemAbstractSyntax :=
  { subst_intro := fun x y n i H => @imm_item_subst_intro x y i n H }.
#[export] Instance imm_si_stack : @SubstIntro stack StackOpenable StackFreeVar StackSubstVar StackAbstractSyntax :=
  { subst_intro := fun x y n s H => @imm_stack_subst_intro x y s n H }.

Lemma imm_get_def_cons_eq (l : label) (ds : defs) (d : def) :
  label_of d = l -> get_def l (defs_cons ds d) = Some d.
Proof.
  intros E. cbn. apply If_l. exact E.
Qed.
Lemma imm_get_def_cons_neq (l : label) (ds : defs) (d : def) :
  label_of d <> l -> get_def l (defs_cons ds d) = get_def l ds.
Proof.
  intros E. cbn. apply If_r. exact E.
Qed.
Lemma imm_defs_has_cons (ds : defs) (d d0 : def) :
  defs_has (defs_cons ds d) d0 ->
  (d0 = d) \/ defs_has ds d0.
Proof.
  intros H. unfold defs_has in *. destruct (classic (label_of d = label_of d0)) as [E | E].
  - rewrite (@imm_get_def_cons_eq (label_of d0) ds d E) in H.
    injection H as H. left. symmetry. exact H.
  - rewrite (@imm_get_def_cons_neq (label_of d0) ds d E) in H. right. exact H.
Qed.

Lemma imm_defs_has_nil (d : def) : defs_has defs_nil d -> False.
Proof. intros H. unfold defs_has, get_def in H. discriminate H. Qed.

Lemma imm_dec_typing_fld (G : ctx) (Go : objctx) (e : renv) (a : fld_label) (v : var) (D : dec) :
  @ty_def typing_mode G Go e (def_fld a (avar_f v)) D ->
  exists S, D = dec_fld a S S /\
             @ty_var typing_mode (ctx_obj G Go) objctx_empty e v S.
Proof.
  intros H. inversion H; subst. eexists. split; [ reflexivity | eassumption ].
Qed.

Lemma imm_defs_typing_has_fld (G : ctx) (Go : objctx) (e : renv) (ds : defs)
      (T : typ) (a : fld_label) (v : var) :
  @ty_defs typing_mode G Go e ds T ->
  defs_has ds (def_fld a (avar_f v)) ->
  exists S, record_has T (dec_fld a S S) /\
             @ty_var typing_mode (ctx_obj G Go) objctx_empty e v S.
Proof.
  intros Hds Hh. revert T Hds.
  induction ds as [| ds IH d]; intros T Hds.
  - inversion Hds.
  - inversion Hds; subst.
    + destruct (@imm_defs_has_cons defs_nil d (def_fld a (avar_f v)) Hh) as [E | Htail].
      * subst d.
        destruct (@imm_dec_typing_fld G Go e a v D H5) as [S [HD Hty]].
        exists S. split.
        -- rewrite HD. apply rh_one.
        -- exact Hty.
      * exfalso. eapply imm_defs_has_nil. exact Htail.
    + destruct (@imm_defs_has_cons ds d (def_fld a (avar_f v)) Hh) as [E | Htail].
      * subst d.
        destruct (@imm_dec_typing_fld G Go e a v D H5) as [S [HD Hty]].
        exists S. split.
        -- rewrite HD. apply rh_andr. apply rh_one.
        -- exact Hty.
      * destruct (IH Htail T0 H1) as [S [Hrec Hty]].
        exists S. split.
        -- apply rh_andl. exact Hrec.
        -- exact Hty.
Qed.


Lemma imm_defs_has_varkind (G : ctx) (ds : defs) (a : fld_label) (v : var) :
  defs_varkinds G ds ->
  defs_has ds (def_fld a (avar_f v)) ->
  ctx_k G v v_loc.
Proof.
  intros Hvk Hh. revert Hh. induction Hvk as [G0 | G0 ds0 d Hvk IH Hdv]; intros Hh.
  - apply imm_defs_has_nil in Hh. destruct Hh.
  - destruct (@imm_defs_has_cons ds0 d (def_fld a (avar_f v)) Hh) as [E | Htail].
    + subst d. inversion Hdv; subst. assumption.
    + eapply IH. exact Htail.
Qed.

Lemma imm_heap_item_has_fld (F : ctx) (e : renv) (S : heap) (y v : var)
      (ds : defs) (a : fld_label) :
  inert F -> heap_correspond F e S -> binds y (item_obj ds) S ->
  defs_has ds (def_fld a (avar_f v)) ->
  exists U S0, ctx_binds y (typ_objref U (typ_mut_marker typ_bot)) F /\
              record_has (open_rec 0 y U) (dec_fld a S0 S0) /\
              @ty_var typing_mode F objctx_empty e v S0.
Proof.
  intros Hinert Hc Hb Hh.
  destruct (@imm_heap_item_typ F e S y ds Hinert Hc Hb) as (U & Hcb & Hds & Hvk).
  destruct (@imm_defs_typing_has_fld F (objctx_heap y U) e ds (open_rec 0 y U) a v Hds Hh)
    as (S0 & Hrec & Htv).
  exists U, S0. split; [ exact Hcb | split; assumption ].
Qed.


(* Bindings/varkinds are monotone when pushing the same binder onto both contexts. *)
Lemma imm_ctx_binds_push_mono (G G' : ctx) (x : var) (vk : varkind) (T : typ) :
  (forall v U, ctx_binds v U G -> ctx_binds v U G') ->
  (forall v U, ctx_binds v U (ctx_push G x vk T) ->
              ctx_binds v U (ctx_push G' x vk T)).
Proof.
  intros Hm v U Hb.
  inversion Hb; subst.
  - apply ctx_binds_e.
  - eapply ctx_binds_n; [ eassumption | eapply Hm; eassumption ].
Qed.

Lemma imm_ctx_vis_push_mono (G G' : ctx) (x : var) (vk : varkind) (T : typ) :
  (forall v, ctx_vis G v -> ctx_vis G' v) ->
  (forall v, ctx_vis (ctx_push G x vk T) v ->
            ctx_vis (ctx_push G' x vk T) v).
Proof.
  intros Hm v Hv.
  inversion Hv; subst.
  - apply ctx_vis_e.
  - eapply ctx_vis_n; [ eassumption | eapply Hm; eassumption ].
Qed.

(* Mutable reachability is monotone in the runtime environment and the heap. *)
Lemma imm_mreach_renv_heap_mono (F : ctx) (t : trm) (fs : stack) (Lv : fset var)
      (Sigma : heap) (e : renv) (y : var) :
  F ⊢ (t ; fs ; Sigma ; e ; Lv) mreach y ->
  forall (Sigma' : heap) (e' : renv),
    (forall a b, binds b a e -> binds b a e') ->
    (forall z it, binds z it Sigma -> binds z it Sigma') ->
    F ⊢ (t ; fs ; Sigma' ; e' ; Lv) mreach y.
Proof.
  intros Hmr.
  refine (mut_reach_ind
    (fun (F0 : ctx) (C0 : config) (y0 : var) =>
       match C0 with
       | config_mk t0 fs0 Sigma0 e0 Lv0 =>
           forall (Sigma' : heap) (e' : renv),
             (forall a b, binds b a e0 -> binds b a e') ->
             (forall z it, binds z it Sigma0 -> binds z it Sigma') ->
             @mut_reach typing_mode F0 (config_mk t0 fs0 Sigma' e' Lv0) y0
       end)
    _ _ Hmr).
  - intros F0 t0 fs0 e0 Sigma0 Lv0 y1 y2 ds a Hinert Hmr0 IH Hby Hdf Hty
           Sigma' e' Hrenv0 Hheap0.
    eapply mreach_fld.
    + exact Hinert.
    + eapply IH; [ exact Hrenv0 | exact Hheap0 ].
    + eapply Hheap0. exact Hby.
    + exact Hdf.
    + eapply (proj1 (imm_rules_renv_mono e')).
      * exact Hty.
      * exact Hrenv0.
  - intros F0 t0 fs0 e0 Sigma0 Lv0 y0 w Hinert Htf Hbw Hty
           Sigma' e' Hrenv0 Hheap0.
    eapply mreach_trm.
    + exact Hinert.
    + exact Htf.
    + eapply Hrenv0. exact Hbw.
    + eapply (proj1 (imm_rules_renv_mono e')).
      * exact Hty.
      * exact Hrenv0.
Qed.

(* A record component can be projected by subtyping. *)
Lemma imm_record_has_subtyp (G : ctx) (e : renv) (T : typ) (D : dec) :
  record_has T D ->
  @subtyp typing_mode G objctx_empty e T (typ_rcd D).
Proof.
  intros H. induction H.
  - apply subtyp_refl.
  - eapply subtyp_trans.
    + apply subtyp_and11.
    + exact IHrecord_has.
  - eapply subtyp_trans.
    + apply subtyp_and12.
    + exact IHrecord_has.
Qed.

(* A variable whose type has a record component also has the record type. *)
Lemma imm_ty_var_record_has (G : ctx) (e : renv) (x : var) (T : typ) (D : dec) :
  @ty_var typing_mode G objctx_empty e x T ->
  record_has T D ->
  @ty_var typing_mode G objctx_empty e x (typ_rcd D).
Proof.
  intros Hx Hr.
  eapply ty_var_sub; [ exact Hx | apply imm_record_has_subtyp; exact Hr ].
Qed.

(* The object-reference type projects to the recursive record body. *)
Lemma imm_ty_var_obj_body (G : ctx) (e : renv) (x : var) (U : typ) :
  ctx_binds x (typ_objref U (typ_mut_marker typ_bot)) G ->
  typ_indep_b 0 U ->
  @ty_var typing_mode G objctx_empty e x (open x U).
Proof.
  intros Hcb Hind.
  assert (Hobj : @ty_var typing_mode G objctx_empty e x
      (typ_objref U (typ_mut_marker typ_bot)))
    by (apply ty_var_var; exact Hcb).
  assert (Hbnd : @ty_var typing_mode G objctx_empty e x (typ_bnd U)).
  { eapply ty_var_sub; [ exact Hobj | apply subtyp_and11 ]. }
  eapply ty_rec_elim; [ exact Hbnd | exact Hind ].
Qed.

(* A mutably-typed field of an object yields the canonical write-receiver type
   required by mreach_fld.  The only extra input is that the field's stored
   (declared = value) type is a subtype of the mutability marker. *)
Lemma imm_ty_var_obj_field_mut (G : ctx) (e : renv) (x : var) (U : typ)
      (a : fld_label) (S : typ) :
  ctx_binds x (typ_objref U (typ_mut_marker typ_bot)) G ->
  typ_indep_b 0 U ->
  record_has (open x U) (dec_fld a S S) ->
  @subtyp typing_mode G objctx_empty e S (typ_mut_marker typ_bot) ->
  @ty_var typing_mode G objctx_empty e x
    (typ_rcd (dec_fld a typ_bot (typ_mut_marker typ_bot))).
Proof.
  intros Hcb Hind Hrec Hsub.
  pose proof (@imm_ty_var_obj_body G e x U Hcb Hind) as Hopen.
  pose proof (@imm_ty_var_record_has G e x (open x U) (dec_fld a S S) Hopen Hrec) as Hfield.
  eapply ty_var_sub; [ exact Hfield | ].
  eapply subtyp_fld.
  - apply subtyp_bot.
  - exact Hsub.
Qed.

(* Field-level provenance: if an object is already mutably reachable and its
   record type gives field [a] the mutability-marker type, then the location
   stored in that field is mutably reachable too (this is exactly mreach_fld,
   with the receiver typing transported across the record subtyping). *)
Lemma imm_mreach_fld_of_mut_field (F : ctx) (t : trm) (fs : stack)
      (Sigma : heap) (e : renv) (Lv : fset var) (y1 y2 : var)
      (ds : defs) (a : fld_label) :
  inert F ->
  @mut_reach typing_mode F (t ; fs ; Sigma ; e ; Lv) y1 ->
  binds y1 (item_obj ds) Sigma ->
  defs_has ds (def_fld a (avar_f y2)) ->
  @ty_trm typing_mode F objctx_empty e (trm_var (avar_f y1))
    (typ_rcd (dec_fld a (typ_mut_marker typ_bot) (typ_mut_marker typ_bot))) ->
  @mut_reach typing_mode F (t ; fs ; Sigma ; e ; Lv) y2.
Proof.
  intros Hinert Hmr Hb Hdf Hty.
  eapply mreach_fld.
  - exact Hinert.
  - exact Hmr.
  - exact Hb.
  - exact Hdf.
  - eapply ty_trm_sub; [ exact Hty | ].
    eapply subtyp_fld.
    + apply subtyp_bot.
    + apply subtyp_refl.
Qed.


(* Every object location of the initial heap has a well-formed recursive body
   type, and therefore is typed at its opened body. *)
Lemma imm_heap_item_obj_ty (F : ctx) (e : renv) (S : heap) (y : var) (ds : defs) :
  inert F -> heap_correspond F e S -> binds y (item_obj ds) S ->
  exists U,
    ctx_binds y (typ_objref U (typ_mut_marker typ_bot)) F /\
    typ_indep_b 0 U /\
    @ty_var typing_mode F objctx_empty e y (open y U) /\
    (F §§ objctx_heap y U ⁏ e ⊢ ds ∶ U /[-> y]) /\
    defs_varkinds F ds.
Proof.
  intros Hinert Hc Hb.
  destruct (@imm_heap_item_typ F e S y ds Hinert Hc Hb) as (U & Hcb & Hds & Hvk).
  pose proof (imm_binds_in_dom Hb) as Hdom.
  destruct Hc as (Hok & Hweak & _ & _ & HkL & _ & _ & Hitem).
  assert (Hdom' : y \in ctx_kdom v_loc F) by (rewrite HkL; exact Hdom).
  destruct (imm_ctx_weakens_kdom_kind Hweak Hok v_loc Hdom')
    as [t [G2 Hk]].
  pose proof (imm_binds_k_after_binds Hk) as Hcb2.
  pose proof (imm_ctx_binds_unique Hcb Hcb2) as Ht.
  pose proof (imm_inert_binds_k_typ Hinert Hk) as Hi.
  assert (Hi' : inert_typ (typ_and (typ_bnd U) (typ_mut_marker typ_bot)) v_loc).
  { rewrite Ht. exact Hi. }
  destruct (imm_inert_typ_loc_full Hi') as (Hrec & Hind & HS).
  exists U. split; [ exact Hcb | split; [ exact Hind | split ] ].
  - eapply @imm_ty_var_obj_body; [ exact Hcb | exact Hind ].
  - split; assumption.
Qed.

(* Field-level provenance from the initial heap shape: given that the stored
   field type is (a subtype of) the mutability marker, the field's value
   location is mutably reachable. *)
Lemma imm_mreach_fld_of_heap_item (F : ctx) (t : trm) (fs : stack)
      (Sigma : heap) (e : renv) (Lv : fset var) (y1 y2 : var)
      (ds : defs) (a : fld_label) (U : typ) (S0 : typ) :
  inert F ->
  @mut_reach typing_mode F (t ; fs ; Sigma ; e ; Lv) y1 ->
  binds y1 (item_obj ds) Sigma ->
  defs_has ds (def_fld a (avar_f y2)) ->
  vis_var typing_mode F y1 ->
  ctx_binds y1 (typ_objref U (typ_mut_marker typ_bot)) F ->
  typ_indep_b 0 U ->
  record_has (open y1 U) (dec_fld a S0 S0) ->
  @subtyp typing_mode F objctx_empty e S0 (typ_mut_marker typ_bot) ->
  @mut_reach typing_mode F (t ; fs ; Sigma ; e ; Lv) y2.
Proof.
  intros Hinert Hmr Hb Hdf Hvis Hcb Hind Hrec Hsub.
  eapply mreach_fld.
  - exact Hinert.
  - exact Hmr.
  - exact Hb.
  - exact Hdf.
  - eapply ty_trm_var.
    + exact Hvis.
    + eapply @imm_ty_var_obj_field_mut; eassumption.
Qed.

(* Composed static provenance step: for an initial heap item [y1] with a field
   [a] whose stored value [y2] has mutable-capability type, mutable
   reachability of [y1] yields mutable reachability of [y2]. *)
Lemma imm_heap_item_mut_field_mreach (F : ctx) (t : trm) (fs : stack)
      (Sigma : heap) (e : renv) (Lv : fset var) (y1 y2 : var) (ds : defs)
      (a : fld_label) :
  inert F ->
  heap_correspond F e Sigma ->
  binds y1 (item_obj ds) Sigma ->
  defs_has ds (def_fld a (avar_f y2)) ->
  vis_var typing_mode F y1 ->
  @mut_reach typing_mode F (t ; fs ; Sigma ; e ; Lv) y1 ->
  (forall S0, @ty_var typing_mode F objctx_empty e y2 S0 ->
              @subtyp typing_mode F objctx_empty e S0 (typ_mut_marker typ_bot)) ->
  @mut_reach typing_mode F (t ; fs ; Sigma ; e ; Lv) y2.
Proof.
  intros Hinert Hc Hb Hdf Hvis Hmr Hsub.
  destruct (@imm_heap_item_has_fld F e Sigma y1 y2 ds a Hinert Hc Hb Hdf)
    as (U & S0 & Hcb & Hrec & Htv).
  destruct Hc as (Hok & Hweak & _ & _ & HkL & _ & _ & Hitem).
  assert (Hdom : y1 \in dom Sigma) by (eapply imm_binds_in_dom; exact Hb).
  assert (Hdom' : y1 \in ctx_kdom v_loc F) by (rewrite HkL; exact Hdom).
  destruct (imm_ctx_weakens_kdom_kind Hweak Hok v_loc Hdom') as [t0 [G2 Hk]].
  pose proof (imm_binds_k_after_binds Hk) as Hcb2.
  pose proof (imm_ctx_binds_unique Hcb Hcb2) as Ht.
  pose proof (imm_inert_binds_k_typ Hinert Hk) as Hi.
  assert (Hi' : inert_typ (typ_and (typ_bnd U) (typ_mut_marker typ_bot)) v_loc).
  { rewrite Ht. exact Hi. }
  destruct (imm_inert_typ_loc_full Hi') as (_ & Hind & _).
  eapply (@imm_mreach_fld_of_heap_item F t fs Sigma e Lv y1 y2 ds a U S0);
    [ exact Hinert | exact Hmr | exact Hb | exact Hdf | exact Hvis
    | exact Hcb | exact Hind | exact Hrec | apply Hsub; exact Htv ].
Qed.

(* An object location in an inert context has a mutable-capability refcap. *)
Lemma imm_inert_loc_objref_marker (G : ctx) (x : var) (U S : typ) :
  inert G -> ctx_k G x v_loc -> ctx_binds x (typ_objref U S) G ->
  S = typ_mut_marker typ_bot.
Proof.
  intros Hinert Hk Hcb.
  destruct Hk as (t & G2 & Hk).
  pose proof (imm_binds_k_after_binds Hk) as Hcb2.
  pose proof (imm_ctx_binds_unique Hcb Hcb2) as Ht.
  pose proof (imm_inert_binds_k_typ Hinert Hk) as Hi.
  assert (Hi' : inert_typ (typ_objref U S) v_loc) by (rewrite Ht; exact Hi).
  destruct (imm_inert_typ_loc_full Hi') as (_ & _ & HS). exact HS.
Qed.

(* Hence its object-reference type is a subtype of the mutability marker. *)
Lemma imm_inert_loc_objref_subtyp_mut (G : ctx) (e : renv) (x : var) (U S : typ) :
  inert G -> ctx_k G x v_loc -> ctx_binds x (typ_objref U S) G ->
  @subtyp typing_mode G objctx_empty e (typ_objref U S) (typ_mut_marker typ_bot).
Proof.
  intros Hinert Hk Hcb.
  pose proof (@imm_inert_loc_objref_marker G x U S Hinert Hk Hcb) as HS.
  rewrite HS. apply subtyp_and12.
Qed.

(* And it is typed at the mutability marker. *)
Lemma imm_inert_loc_objref_ty_var_mut (G : ctx) (e : renv) (x : var) (U S : typ) :
  inert G -> ctx_k G x v_loc -> ctx_binds x (typ_objref U S) G ->
  @ty_var typing_mode G objctx_empty e x (typ_mut_marker typ_bot).
Proof.
  intros Hinert Hk Hcb.
  assert (Hobj : @ty_var typing_mode G objctx_empty e x (typ_objref U S))
    by (apply ty_var_var; exact Hcb).
  eapply ty_var_sub;
    [ exact Hobj | eapply (@imm_inert_loc_objref_subtyp_mut G e x U S); eassumption ].
Qed.

(* Term-level version (usable as an mreach_fld/mreach_trm receiver typing). *)
Lemma imm_inert_loc_objref_ty_trm_mut (G : ctx) (e : renv) (x : var) (U S : typ) :
  inert G -> ctx_k G x v_loc -> ctx_binds x (typ_objref U S) G ->
  vis_var typing_mode G x ->
  @ty_trm typing_mode G objctx_empty e (trm_var (avar_f x)) (typ_mut_marker typ_bot).
Proof.
  intros Hinert Hk Hcb Hvis.
  eapply ty_trm_var; [ exact Hvis | ].
  eapply (@imm_inert_loc_objref_ty_var_mut G e x U S); eassumption.
Qed.

(* Every object location of the initial heap is typed at the mutability marker.
   This is the canonical mutable-capability fact for initial heap objects. *)
Lemma imm_heap_item_loc_marker (F : ctx) (e : renv) (S : heap) (y : var) (ds : defs) :
  inert F -> heap_correspond F e S -> binds y (item_obj ds) S ->
  @ty_var typing_mode F objctx_empty e y (typ_mut_marker typ_bot).
Proof.
  intros Hinert Hc Hb.
  destruct (@imm_heap_item_typ F e S y ds Hinert Hc Hb) as (U & Hcb & Hds & Hvk).
  pose proof (imm_binds_in_dom Hb) as Hdom.
  destruct Hc as (Hok & Hweak & _ & _ & HkL & _ & _ & _).
  assert (Hdom' : y \in ctx_kdom v_loc F) by (rewrite HkL; exact Hdom).
  destruct (imm_ctx_weakens_kdom_kind Hweak Hok v_loc Hdom') as (t & G2 & Hk).
  eapply (@imm_inert_loc_objref_ty_var_mut F e y U (typ_mut_marker typ_bot));
    [ exact Hinert | exists t, G2; exact Hk | exact Hcb ].
Qed.

(* -------- full weakening for the type-level judgments -------- *)

Ltac imm_ts_mono_binds :=
  first
  [ match goal with
    | Hm : (forall (a:var) (U:typ), @ctx_binds a U ?G -> @ctx_binds a U ?G')
      |- (forall (a:var) (U:typ), @ctx_binds a U ?G -> @ctx_binds a U ?G') =>
        exact Hm
    end
  | match goal with
    | Hm : (forall (a:var) (U:typ), @ctx_binds a U ?G -> @ctx_binds a U ?G')
      |- @ctx_binds ?a ?U ?X =>
        unify X G'; eapply Hm; eassumption
    end
  | match goal with
    | Hm : (forall (a:var) (U:typ), @ctx_binds a U ?G -> @ctx_binds a U ?G')
      |- (forall (a:var) (U:typ),
             @ctx_binds a U (ctx_push ?G ?x ?vk ?T) ->
             @ctx_binds a U (ctx_push ?G' ?x ?vk ?T)) =>
        intros a U Hb; inversion Hb; subst;
        [ apply ctx_binds_e
        | eapply ctx_binds_n; [ eassumption | imm_ts_mono_binds ] ]
    end ].

Ltac imm_ts_mono_vis :=
  first
  [ match goal with
    | Hv : (forall a:var, @ctx_vis ?G a -> @ctx_vis ?G' a)
      |- (forall a:var, @ctx_vis ?G a -> @ctx_vis ?G' a) =>
        exact Hv
    end
  | match goal with
    | Hv : (forall a:var, @ctx_vis ?G a -> @ctx_vis ?G' a)
      |- @ctx_vis ?X ?a =>
        unify X G'; eapply Hv; eassumption
    end
  | match goal with
    | Hv : (forall a:var, @ctx_vis ?G a -> @ctx_vis ?G' a)
      |- (forall (a:var),
             @ctx_vis (ctx_push ?G ?x ?vk ?T) a ->
             @ctx_vis (ctx_push ?G' ?x ?vk ?T) a) =>
        intros a Hc; inversion Hc; subst;
        [ apply ctx_vis_e
        | eapply ctx_vis_n; [ eassumption | imm_ts_mono_vis ] ]
    end ].

Ltac imm_ts_apply_ih_var :=
  match goal with
  | |- @obj_typing var (ty_var typing_mode) ?G' objctx_empty ?e ?v ?T =>
      match goal with
      | IH : (forall (X : ctx),
                 (forall a U, @ctx_binds a U ?G -> @ctx_binds a U X) ->
                 (forall a, @ctx_vis ?G a -> @ctx_vis X a) ->
                 @ty_var typing_mode X objctx_empty ?e ?v ?T) |- _ =>
          refine (IH G' _ _); [ imm_ts_mono_binds | imm_ts_mono_vis ]
      end
  end.

Ltac imm_ts_apply_ih_sub :=
  match goal with
  | |- @subtyping (subtyp typing_mode) ?G' objctx_empty ?e ?T ?U =>
      match goal with
      | IH : (forall (X : ctx),
                 (forall a U0, @ctx_binds a U0 ?G -> @ctx_binds a U0 X) ->
                 (forall a, @ctx_vis ?G a -> @ctx_vis X a) ->
                 @subtyp typing_mode X objctx_empty ?e ?T ?U) |- _ =>
          refine (IH G' _ _); [ imm_ts_mono_binds | imm_ts_mono_vis ]
      end
  end.

Ltac imm_ts_apply_ih_inc :=
  match goal with
  | |- @obj_ref_incap (ty_incap typing_mode) ?G' objctx_empty ?e ?T ?U =>
      match goal with
      | IH : (forall (X : ctx),
                 (forall a U0, @ctx_binds a U0 ?G -> @ctx_binds a U0 X) ->
                 (forall a, @ctx_vis ?G a -> @ctx_vis X a) ->
                 @ty_incap typing_mode X objctx_empty ?e ?T ?U) |- _ =>
          refine (IH G' _ _); [ imm_ts_mono_binds | imm_ts_mono_vis ]
      end
  end.

Ltac imm_ts_prem :=
  first
  [ imm_ts_apply_ih_var
  | imm_ts_apply_ih_sub
  | imm_ts_apply_ih_inc
  | imm_ts_mono_binds
  | imm_ts_mono_vis
  | solve [eassumption]
  | solve [eauto 15 using imm_ctx_binds_push_mono, imm_ctx_vis_push_mono]
  | match goal with
    | H : (forall (z : var), _) |- _ => eapply H; imm_ts_prem
    end
  | match goal with
    | H : (?A -> ?B) |- _ =>
        let HA := fresh "Hmode" in
        assert (HA : A) by assumption;
        eapply (H HA); imm_ts_prem
    end
  | match goal with
    | |- ?P -> ?Q => let H := fresh "Hprem" in intro H; imm_ts_prem
    | |- forall x : var, _ => let x := fresh "x" in intro x; imm_ts_prem
    end ].

Ltac imm_ts_case :=
  first
  [ eapply ty_var_var; imm_ts_prem
  | eapply ty_rec_intro; imm_ts_prem
  | eapply ty_rec_elim; imm_ts_prem
  | eapply ty_var_and; imm_ts_prem
  | eapply ty_var_sub; imm_ts_prem
  | eapply ty_var_mut_top; imm_ts_prem
  | eapply subtyp_top; imm_ts_prem
  | eapply subtyp_bot; imm_ts_prem
  | eapply subtyp_refl; imm_ts_prem
  | eapply subtyp_trans; imm_ts_prem
  | eapply subtyp_and11; imm_ts_prem
  | eapply subtyp_and12; imm_ts_prem
  | eapply subtyp_and2; imm_ts_prem
  | eapply subtyp_or11; imm_ts_prem
  | eapply subtyp_or12; imm_ts_prem
  | eapply subtyp_or2; imm_ts_prem
  | eapply subtyp_fld; imm_ts_prem
  | eapply subtyp_typ; imm_ts_prem
  | eapply subtyp_sel2; imm_ts_prem
  | eapply subtyp_sel1; imm_ts_prem
  | eapply subtyp_fun; imm_ts_prem
  | eapply subtyp_met; imm_ts_prem
  | eapply subtyp_tyq; imm_ts_prem
  | eapply subtyp_typ_and; imm_ts_prem
  | eapply subtyp_dist; imm_ts_prem
  | eapply subtyp_nocap_bnd; imm_ts_prem
  | eapply subtyp_nocap_typ; imm_ts_prem
  | eapply subtyp_nocap_fld; imm_ts_prem
  | eapply subtyp_nocap_met; imm_ts_prem
  | eapply subtyp_nocap_fun; imm_ts_prem
  | eapply subtyp_nocap_mut_top_boundless; imm_ts_prem
  | eapply subtyp_nocap_mut_top_complement; imm_ts_prem
  | eapply subtyp_nocap_mut_bot; imm_ts_prem
  | eapply subtyp_mut_top; imm_ts_prem
  | eapply ty_incap_top; imm_ts_prem
  | eapply ty_incap_bot; imm_ts_prem
  | eapply ty_incap_typ; imm_ts_prem
  | eapply ty_incap_cap; imm_ts_prem
  | eapply ty_incap_met; imm_ts_prem
  | eapply ty_incap_fld; imm_ts_prem
  | eapply ty_incap_sel; imm_ts_prem
  | eapply ty_incap_rec; imm_ts_prem
  | eapply ty_incap_and; imm_ts_prem
  | eapply ty_incap_or; imm_ts_prem
  | eapply ty_incap_fun; imm_ts_prem
  | eapply ty_incap_nocap; imm_ts_prem ].

Lemma imm_ts_ctx_weaken :
  (forall (G : ctx) (Go : objctx) (e : renv) (v : var) (T : typ),
      @ty_var typing_mode G Go e v T ->
      forall G', (forall a U, ctx_binds a U G -> ctx_binds a U G') ->
                 (forall a, ctx_vis G a -> ctx_vis G' a) ->
                 @ty_var typing_mode G' Go e v T) /\
  (forall (G : ctx) (Go : objctx) (e : renv) (T U : typ),
      @subtyp typing_mode G Go e T U ->
      forall G', (forall a U0, ctx_binds a U0 G -> ctx_binds a U0 G') ->
                 (forall a, ctx_vis G a -> ctx_vis G' a) ->
                 @subtyp typing_mode G' Go e T U) /\
  (forall (G : ctx) (Go : objctx) (e : renv) (T U : typ),
      @ty_incap typing_mode G Go e T U ->
      forall G', (forall a U0, ctx_binds a U0 G -> ctx_binds a U0 G') ->
                 (forall a, ctx_vis G a -> ctx_vis G' a) ->
                 @ty_incap typing_mode G' Go e T U).
Proof.
  apply (ts_mutind
    (fun G Go e v T d =>
       forall G', (forall a U, @ctx_binds a U G -> @ctx_binds a U G') ->
                  (forall a, @ctx_vis G a -> @ctx_vis G' a) ->
                  @ty_var typing_mode G' Go e v T)
    (fun G Go e T U d =>
       forall G', (forall a U0, @ctx_binds a U0 G -> @ctx_binds a U0 G') ->
                  (forall a, @ctx_vis G a -> @ctx_vis G' a) ->
                  @subtyp typing_mode G' Go e T U)
    (fun G Go e T U d =>
       forall G', (forall a U0, @ctx_binds a U0 G -> @ctx_binds a U0 G') ->
                  (forall a, @ctx_vis G a -> @ctx_vis G' a) ->
                  @ty_incap typing_mode G' Go e T U)).
  all: try (intros; imm_ts_case).
  all: try (let G := match goal with |- ?G => constr:(G) end in idtac "REMAINING:" G).
Qed.

(* -------- context lifting for the term-level judgments -------- *)

Lemma imm_ctx_binds_hide (G G' : ctx) :
  (forall v U, ctx_binds v U G -> ctx_binds v U G') ->
  (forall v U, ctx_binds v U (ctx_hide G) -> ctx_binds v U (ctx_hide G')).
Proof.
  intros Hm v U H. inversion H; subst.
  apply ctx_binds_hide. eapply Hm. eassumption.
Qed.

Lemma imm_ctx_vis_hide (G G' : ctx) :
  (forall v, ctx_vis G v -> ctx_vis G' v) ->
  (forall v, ctx_vis (ctx_hide G) v -> ctx_vis (ctx_hide G') v).
Proof.
  intros Hm v H. inversion H.
Qed.

Lemma imm_ctx_binds_ctx_obj (G G' : ctx) (Go : objctx) :
  (forall v U, ctx_binds v U G -> ctx_binds v U G') ->
  (forall v U, ctx_binds v U (ctx_obj G Go) -> ctx_binds v U (ctx_obj G' Go)).
Proof.
  intros Hm v U H. destruct Go; cbn [ctx_obj].
  - eapply Hm. exact H.
  - inversion H; subst.
    + apply ctx_binds_e.
    + eapply ctx_binds_n; [ eassumption | eapply Hm; eassumption ].
  - eapply Hm. exact H.
Qed.

Lemma imm_ctx_vis_ctx_obj (G G' : ctx) (Go : objctx) :
  (forall v, ctx_vis G v -> ctx_vis G' v) ->
  (forall v, ctx_vis (ctx_obj G Go) v -> ctx_vis (ctx_obj G' Go) v).
Proof.
  intros Hm v H. destruct Go; cbn [ctx_obj].
  - eapply Hm. exact H.
  - inversion H; subst.
    + apply ctx_vis_e.
    + eapply ctx_vis_n; [ eassumption | eapply Hm; eassumption ].
  - eapply Hm. exact H.
Qed.

Lemma imm_ctx_binds_hide_gen (G G' : ctx) (Go : objctx) :
  (forall v U, ctx_binds v U G -> ctx_binds v U G') ->
  (forall v U, ctx_binds v U (ctx_hide G) -> ctx_binds v U (ctx_hide G')).
Proof. apply imm_ctx_binds_hide. Qed.

(* ctx_obj_met is built from vis_hide (which is ctx_hide in every mode that
   has mutability) and two pushes. *)
Lemma imm_ctx_binds_ctx_obj_met (G G' : ctx) (Go : objctx)
      (xz : var) (TZ : typ) (xc : var) (TC : typ) :
  (forall v U, ctx_binds v U G -> ctx_binds v U G') ->
  (forall v U, ctx_binds v U (ctx_obj_met typing_mode G Go xz TZ xc TC) ->
              ctx_binds v U (ctx_obj_met typing_mode G' Go xz TZ xc TC)).
Proof.
  intros Hm.
  assert (E : mode_visibility' typing_mode = mode_visibility_hide_method)
    by apply imm_mode_mut_vis.
  destruct Go; cbn [ctx_obj_met]; rewrite E; cbn;
    repeat first [ apply imm_ctx_binds_push_mono
                 | apply imm_ctx_binds_hide
                 | exact Hm ].
Qed.

Lemma imm_ctx_vis_ctx_obj_met (G G' : ctx) (Go : objctx)
      (xz : var) (TZ : typ) (xc : var) (TC : typ) :
  (forall v, ctx_vis G v -> ctx_vis G' v) ->
  (forall v, ctx_vis (ctx_obj_met typing_mode G Go xz TZ xc TC) v ->
              ctx_vis (ctx_obj_met typing_mode G' Go xz TZ xc TC) v).
Proof.
  intros Hm.
  assert (E : mode_visibility' typing_mode = mode_visibility_hide_method)
    by apply imm_mode_mut_vis.
  destruct Go; cbn [ctx_obj_met]; rewrite E; cbn;
    repeat first [ apply imm_ctx_vis_push_mono
                 | apply imm_ctx_vis_hide
                 | exact Hm ].
Qed.

(* -------- wrappers for the type-level weakening -------- *)

Lemma imm_ts_var_weaken (G G' : ctx) (Go : objctx) (e : renv) (x : var) (T : typ) :
  @ty_var typing_mode G Go e x T ->
  (forall a W, ctx_binds a W G -> ctx_binds a W G') ->
  (forall a, ctx_vis G a -> ctx_vis G' a) ->
  @ty_var typing_mode G' Go e x T.
Proof.
  intros H Hm Hv.
  destruct imm_ts_ctx_weaken as [Hvar _].
  eapply Hvar; [ exact H | exact Hm | exact Hv ].
Qed.

Lemma imm_ts_sub_weaken (G G' : ctx) (Go : objctx) (e : renv) (T U : typ) :
  @subtyp typing_mode G Go e T U ->
  (forall a W, ctx_binds a W G -> ctx_binds a W G') ->
  (forall a, ctx_vis G a -> ctx_vis G' a) ->
  @subtyp typing_mode G' Go e T U.
Proof.
  intros H Hm Hv.
  destruct imm_ts_ctx_weaken as [_ [Hsub _]].
  eapply Hsub; [ exact H | exact Hm | exact Hv ].
Qed.

Lemma imm_ts_incap_weaken (G G' : ctx) (Go : objctx) (e : renv) (T U : typ) :
  @ty_incap typing_mode G Go e T U ->
  (forall a W, ctx_binds a W G -> ctx_binds a W G') ->
  (forall a, ctx_vis G a -> ctx_vis G' a) ->
  @ty_incap typing_mode G' Go e T U.
Proof.
  intros H Hm Hv.
  destruct imm_ts_ctx_weaken as [_ [_ Hinc]].
  eapply Hinc; [ exact H | exact Hm | exact Hv ].
Qed.

(* -------- weakening for capability bounds (and viewpoint adaptation) -------- *)

Lemma imm_capbnd_ctx_weaken (C : typ_refcap_label) :
  forall (G : ctx) (Go : objctx) (e : renv) (T U : typ),
    @ty_capbnd typing_mode C G Go e T U ->
    forall G', (forall a W, ctx_binds a W G -> ctx_binds a W G') ->
               (forall a, ctx_vis G a -> ctx_vis G' a) ->
               @ty_capbnd typing_mode C G' Go e T U.
Proof.
  apply (ty_capbnd_ind
    (fun G Go e T U =>
       forall G', (forall a W, @ctx_binds a W G -> @ctx_binds a W G') ->
                  (forall a, @ctx_vis G a -> @ctx_vis G' a) ->
                  @ty_capbnd typing_mode C G' Go e T U)).
  all: try (intros; econstructor; eauto using imm_ts_var_weaken).
  all: try (match goal with
            | IH : (forall X, (forall a W, @ctx_binds a W ?G -> @ctx_binds a W X) ->
                              (forall a, @ctx_vis ?G a -> @ctx_vis X a) ->
                              @ty_capbnd typing_mode ?CC X objctx_empty ?e ?TI ?UI),
              Hm : (forall a W, @ctx_binds a W ?G -> @ctx_binds a W ?G'),
              Hv : (forall a, @ctx_vis ?G a -> @ctx_vis ?G' a)
              |- @obj_cap_bnd ?CC (ty_capbnd typing_mode ?CC) ?G' objctx_empty ?e ?TG ?UG =>
                unify TG TI; unify UG UI; refine (IH G' Hm Hv)
            end).
  all: try (match goal with
            | Hvar : @obj_typing var (ty_var typing_mode) ?G objctx_empty ?e ?x ?TH,
              Hm : (forall a W, @ctx_binds a W ?G -> @ctx_binds a W ?G'),
              Hv : (forall a, @ctx_vis ?G a -> @ctx_vis ?G' a)
              |- @obj_typing var (ty_var typing_mode) ?G' objctx_empty ?e ?x ?TG =>
                unify TG TH;
                refine (@imm_ts_var_weaken G G' objctx_empty e x TH Hvar Hm Hv)
            end).
Qed.


Lemma imm_viewpoint_ctx_weaken (C : typ_refcap_label) (x : var) :
  forall (G : ctx) (Go : objctx) (e : renv) (T1 T2 : typ),
    viewpoint_adapt_cap typing_mode C x G Go e T1 T2 ->
    forall G', (forall a W, ctx_binds a W G -> ctx_binds a W G') ->
               (forall a, ctx_vis G a -> ctx_vis G' a) ->
               viewpoint_adapt_cap typing_mode C x G' Go e T1 T2.
Proof.
  apply (viewpoint_adapt_cap_ind
    (fun (C0 : typ_refcap_label) (x0 : var) (G : ctx) (Go : objctx) (e : renv)
         (T1 T2 : typ) =>
       forall G', (forall a W, @ctx_binds a W G -> @ctx_binds a W G') ->
                  (forall a, @ctx_vis G a -> @ctx_vis G' a) ->
                  viewpoint_adapt_cap typing_mode C0 x0 G' Go e T1 T2)).
  intros C0 x0 G Go e T Tstrip Tcap Hinc Hcap G' Hm Hv.
  econstructor.
  - eapply imm_ts_incap_weaken; [ exact Hinc | exact Hm | exact Hv ].
  - eapply imm_capbnd_ctx_weaken; [ exact Hcap | exact Hm | exact Hv ].
Qed.

(* -------- weakening for the term/definition judgments -------- *)

Lemma imm_vis_var_weaken (G G' : ctx) (x : var) :
  ((mode_visibility' typing_mode = mode_visibility_hide_method) -> ctx_vis G x) ->
  (forall a, ctx_vis G a -> ctx_vis G' a) ->
  ((mode_visibility' typing_mode = mode_visibility_hide_method) -> ctx_vis G' x).
Proof. intros Hvis Hv Hm. eapply Hv, Hvis, Hm. Qed.

Lemma imm_mut_var_weaken (G G' : ctx) (e : renv) (x : var) (T : typ) :
  ((mode_has_mutability' typing_mode = true) ->
     @ty_var typing_mode G objctx_empty e x T) ->
  (forall a W, ctx_binds a W G -> ctx_binds a W G') ->
  (forall a, ctx_vis G a -> ctx_vis G' a) ->
  ((mode_has_mutability' typing_mode = true) ->
     @ty_var typing_mode G' objctx_empty e x T).
Proof.
  intros Hmw Hm Hv Hmode.
  eapply imm_ts_var_weaken; [ exact (Hmw Hmode) | exact Hm | exact Hv ].
Qed.

Lemma imm_viewpoint_weaken (x : var) (G G' : ctx) (e : renv) (T U : typ) :
  viewpoint_adapt typing_mode x G objctx_empty e T U ->
  (forall a W, ctx_binds a W G -> ctx_binds a W G') ->
  (forall a, ctx_vis G a -> ctx_vis G' a) ->
  viewpoint_adapt typing_mode x G' objctx_empty e T U.
Proof.
  intros Hv Hm Hv'.
  unfold viewpoint_adapt in *.
  rewrite imm_mode_mut_viewpoint in *.
  cbn in *.
  eapply imm_viewpoint_ctx_weaken; eassumption.
Qed.

Ltac imm_lift_mono :=
  first
  [ match goal with
    | Hm : (forall a W, @ctx_binds a W ?G -> @ctx_binds a W ?G')
      |- (forall a W, @ctx_binds a W ?G -> @ctx_binds a W ?G') => exact Hm
    end
  | match goal with
    | |- (forall a W, @ctx_binds a W (ctx_push ?G ?x ?vk ?T) ->
                     @ctx_binds a W (ctx_push ?G' ?x ?vk ?T)) =>
        apply imm_ctx_binds_push_mono; imm_lift_mono
    end
  | match goal with
    | |- (forall a W, @ctx_binds a W (ctx_obj ?G ?Go) ->
                     @ctx_binds a W (ctx_obj ?G' ?Go)) =>
        apply imm_ctx_binds_ctx_obj; imm_lift_mono
    end
  | match goal with
    | |- (forall a W, @ctx_binds a W (ctx_obj_met typing_mode ?G ?Go ?xz ?TZ ?xc ?TC) ->
                     @ctx_binds a W (ctx_obj_met typing_mode ?G' ?Go ?xz ?TZ ?xc ?TC)) =>
        apply imm_ctx_binds_ctx_obj_met; imm_lift_mono
    end
  | match goal with
    | |- (forall a W, @ctx_binds a W (ctx_hide ?G) ->
                     @ctx_binds a W (ctx_hide ?G')) =>
        apply imm_ctx_binds_hide; imm_lift_mono
    end ].

Ltac imm_lift_vis :=
  first
  [ match goal with
    | Hv : (forall a, @ctx_vis ?G a -> @ctx_vis ?G' a)
      |- (forall a, @ctx_vis ?G a -> @ctx_vis ?G' a) => exact Hv
    end
  | match goal with
    | |- (forall a, @ctx_vis (ctx_push ?G ?x ?vk ?T) a ->
                    @ctx_vis (ctx_push ?G' ?x ?vk ?T) a) =>
        apply imm_ctx_vis_push_mono; imm_lift_vis
    end
  | match goal with
    | |- (forall a, @ctx_vis (ctx_obj ?G ?Go) a -> @ctx_vis (ctx_obj ?G' ?Go) a) =>
        apply imm_ctx_vis_ctx_obj; imm_lift_vis
    end
  | match goal with
    | |- (forall a, @ctx_vis (ctx_obj_met typing_mode ?G ?Go ?xz ?TZ ?xc ?TC) a ->
                    @ctx_vis (ctx_obj_met typing_mode ?G' ?Go ?xz ?TZ ?xc ?TC) a) =>
        apply imm_ctx_vis_ctx_obj_met; imm_lift_vis
    end
  | match goal with
    | |- (forall a, @ctx_vis (ctx_hide ?G) a -> @ctx_vis (ctx_hide ?G') a) =>
        apply imm_ctx_vis_hide; imm_lift_vis
    end ].

Ltac imm_r_prem :=
  first
  [ match goal with
    | Hvis : ((mode_visibility' typing_mode = mode_visibility_hide_method) ->
                @ctx_vis ?G ?v)
      |- ((mode_visibility' typing_mode = mode_visibility_hide_method) ->
            @ctx_vis ?Gg ?v) =>
        refine (@imm_vis_var_weaken G Gg v Hvis _); [ imm_lift_vis ]
    end
  | match goal with
    | Hmw : ((mode_has_mutability' typing_mode = true) ->
                @obj_typing var (ty_var typing_mode) ?G objctx_empty ?e ?x ?T)
      |- ((mode_has_mutability' typing_mode = true) ->
            @obj_typing var (ty_var typing_mode) ?Gg objctx_empty ?e ?x ?T) =>
        refine (@imm_mut_var_weaken G Gg e x T Hmw _ _);
        [ imm_lift_mono | imm_lift_vis ]
    end
  | match goal with
    | Hv : viewpoint_adapt typing_mode ?x ?G objctx_empty ?e ?T ?U
      |- viewpoint_adapt typing_mode ?x ?Gg objctx_empty ?e ?T ?U =>
        refine (@imm_viewpoint_weaken x G Gg e T U Hv _ _);
        [ imm_lift_mono | imm_lift_vis ]
    end
  | match goal with
    | H : @subtyping (subtyp typing_mode) ?G objctx_empty ?e ?T ?U
      |- @subtyping (subtyp typing_mode) ?Gg objctx_empty ?e ?T ?U =>
        refine (@imm_ts_sub_weaken G Gg objctx_empty e T U H _ _);
        [ imm_lift_mono | imm_lift_vis ]
    end
  | match goal with
    | H : @obj_typing var (ty_var typing_mode) ?G ?Go ?e ?x ?TH
      |- @obj_typing var (ty_var typing_mode) ?Gg ?Go ?e ?x ?TG =>
        unify TG TH;
        refine (@imm_ts_var_weaken G Gg Go e x TH H _ _);
        [ imm_lift_mono | imm_lift_vis ]
    end
  | match goal with
    | IH : (forall X, (forall a W, @ctx_binds a W ?G -> @ctx_binds a W X) ->
                      (forall a, @ctx_vis ?G a -> @ctx_vis X a) ->
                      @ty_trm typing_mode X ?Go ?e ?t ?T)
      |- @obj_typing trm (ty_trm typing_mode) ?Gg ?GGo ?Ge ?Gt ?GT =>
        unify GGo Go; unify Ge e; unify Gt t; unify GT T;
        refine (IH Gg _ _); [ imm_lift_mono | imm_lift_vis ]
    end
  | match goal with
    | IH : (forall X, (forall a W, @ctx_binds a W ?G -> @ctx_binds a W X) ->
                      (forall a, @ctx_vis ?G a -> @ctx_vis X a) ->
                      @ty_lit typing_mode X ?Go ?e ?l ?T)
      |- @obj_typing lit (ty_lit typing_mode) ?Gg ?GGo ?Ge ?Gl ?GT =>
        unify GGo Go; unify Ge e; unify Gl l; unify GT T;
        refine (IH Gg _ _); [ imm_lift_mono | imm_lift_vis ]
    end
  | match goal with
    | IH : (forall X, (forall a W, @ctx_binds a W ?G -> @ctx_binds a W X) ->
                      (forall a, @ctx_vis ?G a -> @ctx_vis X a) ->
                      @ty_def typing_mode X ?Go ?e ?d ?D)
      |- @obj_dec_typing def (ty_def typing_mode) ?Gg ?GGo ?Ge ?Gd ?GD =>
        unify GGo Go; unify Ge e; unify Gd d; unify GD D;
        refine (IH Gg _ _); [ imm_lift_mono | imm_lift_vis ]
    end
  | match goal with
    | IH : (forall X, (forall a W, @ctx_binds a W ?G -> @ctx_binds a W X) ->
                      (forall a, @ctx_vis ?G a -> @ctx_vis X a) ->
                      @ty_defs typing_mode X ?Go ?e ?ds ?T)
      |- @obj_typing defs (ty_defs typing_mode) ?Gg ?GGo ?Ge ?Gds ?GT =>
        unify GGo Go; unify Ge e; unify Gds ds; unify GT T;
        refine (IH Gg _ _); [ imm_lift_mono | imm_lift_vis ]
    end
  | match goal with
    | IH : (forall (z : var), _) |- _ =>
        eapply IH; first [ imm_lift_mono | imm_lift_vis | solve [eassumption] ]
    end
  | solve [eassumption]
  | match goal with |- forall z : var, _ => let z := fresh "z" in intro z; imm_r_prem end
  | match goal with |- (?P -> ?Q) => let Hp := fresh "Hp" in intro Hp; imm_r_prem end ].

Ltac imm_r_case :=
  first
  [ eapply ty_trm_var; imm_r_prem
  | eapply ty_trm_apply; imm_r_prem
  | eapply ty_trm_read; imm_r_prem
  | eapply ty_trm_write; imm_r_prem
  | eapply ty_trm_call; imm_r_prem
  | eapply ty_trm_let; imm_r_prem
  | eapply ty_trm_lit; imm_r_prem
  | eapply ty_trm_sub; imm_r_prem
  | eapply ty_lit_fun; imm_r_prem
  | eapply ty_lit_obj; imm_r_prem
  | eapply ty_def_typ; imm_r_prem
  | eapply ty_def_fld; imm_r_prem
  | eapply ty_def_met; imm_r_prem
  | eapply ty_defs_one; imm_r_prem
  | eapply ty_defs_cons; imm_r_prem ].

Lemma imm_rules_ctx_weaken :
  (forall (G : ctx) (Go : objctx) (e : renv) (t : trm) (T : typ),
      @ty_trm typing_mode G Go e t T ->
      forall G', (forall a W, ctx_binds a W G -> ctx_binds a W G') ->
                 (forall a, ctx_vis G a -> ctx_vis G' a) ->
                 @ty_trm typing_mode G' Go e t T) /\
  (forall (G : ctx) (Go : objctx) (e : renv) (l : lit) (T : typ),
      @ty_lit typing_mode G Go e l T ->
      forall G', (forall a W, ctx_binds a W G -> ctx_binds a W G') ->
                 (forall a, ctx_vis G a -> ctx_vis G' a) ->
                 @ty_lit typing_mode G' Go e l T) /\
  (forall (G : ctx) (Go : objctx) (e : renv) (d : def) (D : dec),
      @ty_def typing_mode G Go e d D ->
      forall G', (forall a W, ctx_binds a W G -> ctx_binds a W G') ->
                 (forall a, ctx_vis G a -> ctx_vis G' a) ->
                 @ty_def typing_mode G' Go e d D) /\
  (forall (G : ctx) (Go : objctx) (e : renv) (ds : defs) (T : typ),
      @ty_defs typing_mode G Go e ds T ->
      forall G', (forall a W, ctx_binds a W G -> ctx_binds a W G') ->
                 (forall a, ctx_vis G a -> ctx_vis G' a) ->
                 @ty_defs typing_mode G' Go e ds T).
Proof.
  apply (rules_mutind
    (fun G Go e t T d =>
       forall G', (forall a W, @ctx_binds a W G -> @ctx_binds a W G') ->
                  (forall a, @ctx_vis G a -> @ctx_vis G' a) ->
                  @ty_trm typing_mode G' Go e t T)
    (fun G Go e l T d =>
       forall G', (forall a W, @ctx_binds a W G -> @ctx_binds a W G') ->
                  (forall a, @ctx_vis G a -> @ctx_vis G' a) ->
                  @ty_lit typing_mode G' Go e l T)
    (fun G Go e d D d0 =>
       forall G', (forall a W, @ctx_binds a W G -> @ctx_binds a W G') ->
                  (forall a, @ctx_vis G a -> @ctx_vis G' a) ->
                  @ty_def typing_mode G' Go e d D)
    (fun G Go e ds T d =>
       forall G', (forall a W, @ctx_binds a W G -> @ctx_binds a W G') ->
                  (forall a, @ctx_vis G a -> @ctx_vis G' a) ->
                  @ty_defs typing_mode G' Go e ds T)).
  all: try (intros; imm_r_case).
Qed.

(* -------- environment correspondence under context extension -------- *)

Lemma imm_renv_corr_push (G : ctx) (e : renv) (y0 : var)
      (vk : varkind) (T0 : typ) :
  renv_corr G e -> y0 §# G -> renv_corr (ctx_push G y0 vk T0) e.
Proof.
  intros H. induction H as
    [ G1 | G1 G2 G3 e w y Tw Ty Hw Hy Hc Hrec IH ]; intros Hfresh.
  - apply renv_corr_empty.
  - eapply renv_corr_ref.
    + eapply ctx_binds_k_n.
      * intro E. subst w. apply Hfresh.
        eapply imm_ctx_binds_dom. eapply imm_binds_k_after_binds. exact Hw.
      * exact Hw.
    + exact Hy.
    + exact Hc.
    + apply IH. exact Hfresh.
Qed.

(* -------- context extension helpers for heap correspondence -------- *)

Lemma imm_ctx_vis_push_any (G : ctx) (x : var) (vk : varkind) (T : typ) :
  (forall v, ctx_vis G v -> ctx_vis (ctx_push G x vk T) v).
Proof.
  intros v Hv. destruct (classic (v = x)) as [E | Hne].
  - subst v. apply ctx_vis_e.
  - eapply ctx_vis_n; [ exact Hne | exact Hv ].
Qed.

Lemma imm_ctx_binds_push_fresh (G : ctx) (x : var) (vk : varkind) (T : typ) :
  x §# G ->
  (forall v W, ctx_binds v W G -> ctx_binds v W (ctx_push G x vk T)).
Proof.
  intros Hf v W Hb. destruct (classic (v = x)) as [E | Hne].
  - subst v. exfalso. apply Hf. eapply imm_ctx_binds_dom. exact Hb.
  - eapply ctx_binds_n; [ exact Hne | exact Hb ].
Qed.

Lemma imm_ctx_binds_swap (G : ctx) (x y : var) (vk vk2 : varkind) (T T2 : typ) :
  y §# G ->
  (forall v W, ctx_binds v W (ctx_push G x vk T) ->
              ctx_binds v W (ctx_push (ctx_push G y vk2 T2) x vk T)).
Proof.
  intros Hf.
  apply imm_ctx_binds_push_mono.
  apply imm_ctx_binds_push_fresh. exact Hf.
Qed.

Lemma imm_ctx_vis_swap (G : ctx) (x y : var) (vk vk2 : varkind) (T T2 : typ) :
  y §# G ->
  (forall v, ctx_vis (ctx_push G x vk T) v ->
            ctx_vis (ctx_push (ctx_push G y vk2 T2) x vk T) v).
Proof.
  intros Hf.
  apply imm_ctx_vis_push_mono.
  apply imm_ctx_vis_push_any.
Qed.

Lemma imm_def_varkinds_push (G : ctx) (x : var) (vk : varkind) (T : typ) (d : def) :
  def_varkinds G d -> x §# G -> def_varkinds (ctx_push G x vk T) d.
Proof.
  intros H Hf. inversion H; subst.
  - eapply def_varkinds_fld. eapply imm_ctx_k_weaken_fresh; [ eassumption | exact Hf ].
  - apply def_varkinds_typ.
  - eapply def_varkinds_met. eapply imm_all_tfree_k_push; [ eassumption | exact Hf ].
Qed.

Lemma imm_defs_varkinds_push (G : ctx) (x : var) (vk : varkind) (T : typ) (ds : defs) :
  defs_varkinds G ds -> x §# G -> defs_varkinds (ctx_push G x vk T) ds.
Proof.
  intros H. induction H as [G0 | G0 ds0 d Hds IH Hd]; intros Hf.
  - apply defs_varkinds_nil.
  - eapply defs_varkinds_cons.
    + apply IH. exact Hf.
    + eapply imm_def_varkinds_push; [ exact Hd | exact Hf ].
Qed.

(* A heap item stays well-typed when the context is extended by a fresh binder. *)
Lemma imm_ty_item_s_push (G : ctx) (e : renv) (S : heap) (z : var)
      (x : var) (vk : varkind) (T : typ) :
  @ty_item_s typing_mode G e S z -> x §# G ->
  @ty_item_s typing_mode (ctx_push G x vk T) e S z.
Proof.
  intros His Hf.
  revert x vk T Hf.
  refine (ty_item_s_ind
    (fun (G0 : ctx) (e0 : renv) (s0 : heap) (z0 : var) =>
       forall (x : var) (vk : varkind) (T : typ),
         x §# G0 -> @ty_item_s typing_mode (ctx_push G0 x vk T) e0 s0 z0)
    _ _ His).
  - intros G0 e0 s0 x0 S0 t0 L0 T0 Hfun Hcb Hbind Hbody Htf
           x1 vk1 T1 Hf.
    eapply ty_item_fun_s.
    + exact Hfun.
    + eapply imm_ctx_binds_push_fresh; [ exact Hf | exact Hcb ].
    + exact Hbind.
    + intros y Hy.
      eapply (proj1 imm_rules_ctx_weaken)
        with (G := ctx_push G0 y v_par S0)
             (G' := ctx_push (ctx_push G0 x1 vk1 T1) y v_par S0).
      * apply Hbody. exact Hy.
      * exact (@imm_ctx_binds_swap G0 y x1 v_par vk1 S0 T1 Hf).
      * exact (@imm_ctx_vis_swap G0 y x1 v_par vk1 S0 T1 Hf).
    + eapply imm_all_tfree_k_push; [ exact Htf | exact Hf ].
  - intros G0 e0 s0 x0 U0 S0 ds0 T0 Hcb Hbind HT Hds Hvk
           x1 vk1 T1 Hf.
    eapply ty_item_obj_s.
    + eapply imm_ctx_binds_push_fresh; [ exact Hf | exact Hcb ].
    + exact Hbind.
    + exact HT.
    + eapply (proj2 (proj2 (proj2 imm_rules_ctx_weaken)))
        with (G := G0) (G' := ctx_push G0 x1 vk1 T1).
      * exact Hds.
      * apply imm_ctx_binds_push_fresh. exact Hf.
      * apply imm_ctx_vis_push_any.
    + eapply imm_defs_varkinds_push; [ exact Hvk | exact Hf ].
Qed.

(* A heap item stays well-typed when a fresh item is added to the heap. *)
Lemma imm_ty_item_s_heap_push (G : ctx) (e : renv) (s : heap) (z : var) :
  @ty_item_s typing_mode G e s z ->
  forall (y : var) (it : item), y \notin dom s ->
    @ty_item_s typing_mode G e (s & y ~ it) z.
Proof.
  intros His.
  refine (ty_item_s_ind
    (fun (G0 : ctx) (e0 : renv) (s0 : heap) (z0 : var) =>
       forall (y : var) (it : item), y \notin dom s0 ->
         @ty_item_s typing_mode G0 e0 (s0 & y ~ it) z0)
    _ _ His).
  - intros G0 e0 s0 x0 S0 t0 L0 T0 Hfun Hcb Hbind Hbody Htf y it Hf.
    eapply ty_item_fun_s.
    + exact Hfun.
    + exact Hcb.
    + eapply binds_push_neq.
      * exact Hbind.
      * intro E. subst x0. apply Hf. eapply imm_binds_in_dom. exact Hbind.
    + exact Hbody.
    + exact Htf.
  - intros G0 e0 s0 x0 U0 S0 ds0 T0 Hcb Hbind HT Hds Hvk y it Hf.
    eapply ty_item_obj_s.
    + exact Hcb.
    + eapply binds_push_neq.
      * exact Hbind.
      * intro E. subst x0. apply Hf. eapply imm_binds_in_dom. exact Hbind.
    + exact HT.
    + exact Hds.
    + exact Hvk.
Qed.

(* Heap correspondence is preserved by adding a fresh, well-typed item and the
   matching fresh location binder. *)
Lemma imm_heap_correspond_push (F : ctx) (e : renv) (S : heap)
      (y : var) (it : item) (T : typ) :
  @heap_correspond typing_mode F e S ->
  y \notin ctx_dom F ->
  y \notin dom S ->
  @ty_item_s typing_mode (ctx_push F y v_loc T) e (S & y ~ it) y ->
  @heap_correspond typing_mode (ctx_push F y v_loc T) e (S & y ~ it).
Proof.
  intros Hc HfF HfS Hnew.
  destruct Hc as (Hok & Hweak & HokS & Hoke & HkL & HkR & Hrenv & Hitem).
  repeat split.
  1: apply ctx_ok_push; assumption.
  1: apply ctx_weakens_push; assumption.
  1: apply ok_push; assumption.
  1: exact Hoke.
  1: rewrite dom_push. cbn [ctx_kdom].
     assert (Hif : (If v_loc = v_loc then (\{y} \u ctx_kdom v_loc F)
                    else ctx_kdom v_loc F) = (\{y} \u ctx_kdom v_loc F))
       by (apply If_l; reflexivity).
     rewrite Hif. rewrite HkL. reflexivity.
  1: cbn [ctx_kdom].
     assert (Hif : (If v_ref = v_loc then (\{y} \u ctx_kdom v_ref F)
                    else ctx_kdom v_ref F) = ctx_kdom v_ref F)
       by (apply If_r; intro E; discriminate E).
     rewrite Hif. exact HkR.
  1: apply imm_renv_corr_push; assumption.
  1: intros x Hx. rewrite dom_push in Hx.
     rewrite in_union, in_singleton in Hx.
     destruct Hx as [E | Hx].
     - subst x. exact Hnew.
     - eapply imm_ty_item_s_push.
       + eapply imm_ty_item_s_heap_push.
         * apply Hitem. exact Hx.
         * exact HfS.
       + exact HfF.
Qed.
(* -------- extending the reference environment with a matched pair -------- *)

Lemma imm_renv_corr_extend (G : ctx) (e : renv) (w y : var)
      (Tw Ty : typ) (G2 : ctx) :
  renv_corr G e ->
  w §# G ->
  typ_corr Tw Ty ->
  ctx_binds_k_after y v_loc Ty G G2 ->
  renv_corr (ctx_push G w v_ref Tw) (renv_bind e w y).
Proof.
  intros Hrec Hf Hcorr Hsplit.
  eapply renv_corr_ref.
  - apply ctx_binds_k_e.
  - exact Hsplit.
  - exact Hcorr.
  - apply imm_renv_corr_push; assumption.
Qed.

(* A heap item stays well-typed when the reference environment is extended. *)
Lemma imm_ty_item_s_renv_mono (G : ctx) (e e' : renv) (S : heap) (z : var) :
  @ty_item_s typing_mode G e S z ->
  env_binds_more e e' ->
  @ty_item_s typing_mode G e' S z.
Proof.
  intros His. revert e'.
  refine (ty_item_s_ind
    (fun (G0 : ctx) (e0 : renv) (s0 : heap) (z0 : var) =>
       forall (e' : renv), env_binds_more e0 e' ->
         @ty_item_s typing_mode G0 e' s0 z0)
    _ _ His).
  - intros G0 e0 s0 x0 S0 t0 L0 T0 Hfun Hcb Hbind Hbody Htf e' Hmore.
    eapply ty_item_fun_s.
    + exact Hfun.
    + exact Hcb.
    + exact Hbind.
    + intros x1 Hx1.
      eapply (proj1 (imm_rules_renv_mono e')).
      * apply Hbody. exact Hx1.
      * exact Hmore.
    + exact Htf.
  - intros G0 e0 s0 x0 U0 S0 ds0 T0 Hcb Hbind HT Hds Hvk e' Hmore.
    eapply ty_item_obj_s.
    + exact Hcb.
    + exact Hbind.
    + exact HT.
    + eapply (proj2 (proj2 (proj2 (imm_rules_renv_mono e')))).
      * exact Hds.
      * exact Hmore.
    + exact Hvk.
Qed.

(* Heap correspondence is preserved by extending the reference environment with
   a fresh reference pointing at an existing location of the context. *)
Lemma imm_heap_correspond_renv_push (F : ctx) (e : renv) (S : heap)
      (w y : var) (Tw Ty : typ) (G2 : ctx) :
  @heap_correspond typing_mode F e S ->
  w §# F ->
  typ_corr Tw Ty ->
  ctx_binds_k_after y v_loc Ty F G2 ->
  @heap_correspond typing_mode (ctx_push F w v_ref Tw) (renv_bind e w y) S.
Proof.
  intros Hc Hf Hcorr Hsplit.
  destruct Hc as (Hok & Hweak & HokS & Hoke & HkL & HkR & Hrenv & Hitem).
  assert (Hwf : w \notin dom e).
  { intro E. apply Hf. rewrite <- HkR in E. eapply imm_ctx_kdom_dom. exact E. }
  repeat split.
  1: apply ctx_ok_push; assumption.
  1: apply ctx_weakens_push; assumption.
  1: exact HokS.
  1: (apply ok_push; [ exact Hoke | exact Hwf ]).
  1: cbn [ctx_kdom].
     assert (Hif : (If v_loc = v_ref then (\{w} \u ctx_kdom v_loc F)
                    else ctx_kdom v_loc F) = ctx_kdom v_loc F)
       by (apply If_r; intro E; discriminate E).
     rewrite Hif. exact HkL.
  1: rewrite dom_push. cbn [ctx_kdom].
     assert (Hif : (If v_ref = v_ref then (\{w} \u ctx_kdom v_ref F)
                    else ctx_kdom v_ref F) = (\{w} \u ctx_kdom v_ref F))
       by (apply If_l; reflexivity).
     rewrite Hif. rewrite HkR. reflexivity.
  1: eapply imm_renv_corr_extend; eassumption.
  1: intros x Hx.
     eapply imm_ty_item_s_renv_mono.
     - eapply imm_ty_item_s_push.
       + apply Hitem. exact Hx.
       + exact Hf.
     - intros a b Hab. eapply binds_push_neq.
       + exact Hab.
       + intro E. subst b. apply Hwf. eapply imm_binds_in_dom. exact Hab.
Qed.

Lemma imm_ty_trm_var_inv (G : ctx) (e : renv) (x : var) (T : typ) :
  @ty_trm typing_mode G objctx_empty e (trm_var (avar_f x)) T ->
  @ty_var typing_mode G objctx_empty e x T.
Proof.
  intros H. remember (trm_var (avar_f x)) as t eqn:E.
  induction H; try discriminate; subst.
  - injection E as Ex. subst. eassumption.
  - match goal with
    | IH : ((_ = _) -> @ty_var typing_mode G objctx_empty e x ?U)
      |- @ty_var typing_mode G objctx_empty e x ?Tv =>
        eapply ty_var_sub with (T := U);
        [ apply IH; reflexivity | eassumption ]
    end.
Qed.

Lemma imm_ty_trm_let_inv (G : ctx) (e : renv) (a b : trm) (R : typ) :
  @ty_trm typing_mode G objctx_empty e (trm_let a b) R ->
  exists (L : fset var) (S : typ),
    @ty_trm typing_mode G objctx_empty e a S /\
    (forall x, x \notin L ->
       @ty_trm typing_mode (ctx_push G x v_let S) objctx_empty e (open x b) R).
Proof.
  intros H. remember (trm_let a b) as u eqn:E.
  induction H; try discriminate; subst.
  - injection E as Ea Eb. subst.
    match goal with
    | Ha : @obj_typing trm (ty_trm typing_mode) G objctx_empty e a ?S |- _ =>
        match goal with
        | Hbody : (forall x, x \notin ?L -> _) |- _ =>
            exists (L \u ctx_dom G), S;
            split; [ exact Ha
                   | intros x Hx;
                     pose proof (notin_union_r1 Hx) as HxL;
                     apply Hbody; exact HxL ]
        end
    end.
  - match goal with
    | IH : ((_ = _) -> exists (L : fset var) (S : typ), _) |- _ =>
        destruct (IH eq_refl) as (L0 & S & Hs & Hbody);
        exists (L0 \u ctx_dom G), S;
        split; [ exact Hs
               | intros x Hx;
                 pose proof (notin_union_r1 Hx) as HxL;
                 pose proof (notin_union_r2 Hx) as HxG;
                 eapply ty_trm_sub;
                 [ apply Hbody; exact HxL
                 | eapply imm_ts_sub_weaken;
                   [ eassumption
                   | apply imm_ctx_binds_push_fresh; exact HxG
                   | apply imm_ctx_vis_push_any ] ] ]
    end.
Qed.

Lemma imm_ty_stack_cons_inv (G : ctx) (e : renv) (T : typ) (t : trm)
      (st : stack) (W : typ) :
  @ty_stack typing_mode G e T (stack_cons (frame_let t) st) W ->
  exists (L : fset var) (U : typ),
    @ty_stack typing_mode G e U st W /\
    (forall x, x \notin L ->
       @ty_trm typing_mode (ctx_push G x v_let T) objctx_empty e (open x t) U).
Proof.
  intros H.
  inversion H as
    [ G0 e0 T0 U0 Hsub
    | L0 G0 e0 s0 t0 S0 T0 U0 Hrest Hbody ]; subst.
  exists L0, T0. split; [ exact Hrest | exact Hbody ].
Qed.

Lemma imm_stack_push_let (G : ctx) (e : renv) (a b : trm) (st : stack)
      (U W : typ) :
  @ty_stack typing_mode G e U st W ->
  @ty_trm typing_mode G objctx_empty e (trm_let a b) U ->
  exists S,
    @ty_trm typing_mode G objctx_empty e a S /\
    @ty_stack typing_mode G e S (stack_cons (frame_let b) st) W.
Proof.
  intros Hst Hlet.
  destruct (@imm_ty_trm_let_inv G e a b U Hlet) as (L & S & Ha & Hbody).
  exists S. split; [ exact Ha | ].
  eapply ty_stack_let.
  - exact Hst.
  - exact Hbody.
Qed.

Lemma imm_ty_lit_fun_inv (G : ctx) (e : renv) (S : typ) (t : trm) (R : typ) :
  @ty_lit typing_mode G objctx_empty e (lit_fun S t) R ->
  exists (L : fset var) (U : typ),
    R = typ_fun S U /\
    (forall x, x \notin L ->
       @ty_trm typing_mode (ctx_push G x v_par S) objctx_empty e (open x t) (open x U)).
Proof.
  intros H. remember (lit_fun S t) as l eqn:E.
  induction H; try discriminate; subst.
  match goal with Ex : lit_fun ?T0 ?t0 = lit_fun S t |- _ =>
    injection Ex as ET Et; subst end.
  match goal with
  | Hbody : (forall x, x \notin ?L ->
               @obj_typing trm (ty_trm typing_mode) (ctx_push G x v_par S)
                 objctx_empty e (open x t) (open x ?U)) |- _ =>
      exists L, U; split; [ reflexivity | exact Hbody ]
  end.
Qed.

Lemma imm_ty_lit_obj_inv (G : ctx) (e : renv) (S : typ) (ds : defs) (R : typ) :
  @ty_lit typing_mode G objctx_empty e (lit_obj S ds) R ->
  R = typ_objlit typing_mode S /\
  exists (L : fset var),
    (forall x, x \notin L ->
       @ty_defs typing_mode G (objctx_lit x S) e (open x ds) (open x S)).
Proof.
  intros H. remember (lit_obj S ds) as l eqn:E.
  induction H; try discriminate; subst.
  match goal with Ex : lit_obj ?T0 ?ds0 = lit_obj S ds |- _ =>
    injection Ex as ET Ed; subst end.
  match goal with
  | Hbody : (forall x, x \notin ?L ->
               @obj_typing defs (ty_defs typing_mode) G (objctx_lit x S)
                 e (open x ds) (open x S)) |- _ =>
      split; [ reflexivity | exists L; exact Hbody ]
  end.
Qed.


Lemma imm_ty_trm_lit_inv (G : ctx) (e : renv) (l : lit) (u : trm) (R : typ) :
  G ⁏ e ⊢ trm_lit l u ∶ R ->
  exists (L : fset var) (T : typ) (U : typ),
    (G ⁏ e ⊢ l ∶ T) /\
    (G ⁏ e ⊢ U <: R) /\
    (forall x, x \notin L ->
       ctx_push G x v_let T ⁏ e ⊢ open x u ∶ U).
Proof.
  intros H. remember (trm_lit l u) as t0 eqn:E.
  induction H; try discriminate; subst.
  - match goal with Ex : trm_lit ?l0 ?u0 = trm_lit l u |- _ =>
      injection Ex as El Eu; subst end.
    match goal with
    | Hlit : @obj_typing lit (ty_lit typing_mode) G objctx_empty e l ?T |- _ =>
        match goal with
        | Hbody : (forall x, x \notin ?L ->
                     @obj_typing trm (ty_trm typing_mode) (ctx_push G x v_let T)
                       objctx_empty e (open x u) ?U) |- _ =>
            exists L, T, U;
            split; [ exact Hlit | split; [ apply subtyp_refl | exact Hbody ] ]
        end
    end.
  - match goal with
    | IH : ((_ = _) -> exists (L : fset var) (T : typ) (U : typ), _) |- _ =>
        assert (Hz : trm_lit l u = trm_lit l u) by reflexivity;
        pose proof (IH Hz) as Hzz;
        repeat match goal with Hx : exists _, _ |- _ => destruct Hx | Hx : (_ /\ _) |- _ => destruct Hx end;
        eexists; eexists; eexists;
        split; [ eassumption | split; [ | eassumption ] ];
        match goal with
        | H2 : (G ⁏ e ⊢ ?U0 <: ?T0) |- _ =>
            eapply subtyp_trans with (S := U0) (T := T0);
            [ exact H2 | eassumption ]
        end
    end.
Qed.


Lemma imm_ty_trm_apply_inv (G : ctx) (e : renv) (x z : var) (R : typ) :
  G ⁏ e ⊢ trm_apply (avar_f x) (avar_f z) ∶ R ->
  exists (S T : typ),
    (G ⁏ e ⊢ x ∶ typ_fun S T) /\
    (G ⁏ e ⊢ z ∶ S) /\
    (G ⁏ e ⊢ open z T <: R).
Proof.
  intros H. remember (trm_apply (avar_f x) (avar_f z)) as t0 eqn:E.
  induction H; try discriminate; subst.
  - match goal with Ex : trm_apply (avar_f ?x0) (avar_f ?z0) =
                           trm_apply (avar_f x) (avar_f z) |- _ =>
      injection Ex as Exx Ezz; subst end.
    match goal with
    | Hx : @obj_typing var (ty_var typing_mode) G objctx_empty e x (typ_fun ?S ?T) |- _ =>
        match goal with
        | Hz : @obj_typing var (ty_var typing_mode) G objctx_empty e z ?S |- _ =>
            exists S, T; split; [ exact Hx | split; [ exact Hz | apply subtyp_refl ] ]
        end
    end.
  - match goal with
    | IH : ((_ = _) -> exists (S : typ) (T : typ), _) |- _ =>
        assert (Hz : trm_apply (avar_f x) (avar_f z) =
                    trm_apply (avar_f x) (avar_f z)) by reflexivity;
        pose proof (IH Hz) as Hzz;
        repeat match goal with
               | Hx : exists _, _ |- _ => destruct Hx
               | Hx : (_ /\ _) |- _ => destruct Hx
               end;
        eexists; eexists;
        split; [ eassumption | split; [ eassumption | ] ];
        match goal with
        | H2 : (G ⁏ e ⊢ ?U0 <: ?T0) |- _ =>
            eapply subtyp_trans with (S := U0) (T := T0);
            [ exact H2 | eassumption ]
        end
    end.
Qed.

Lemma imm_ty_trm_call_inv (G : ctx) (e : renv) (x y : var) (m : met_label) (R : typ) :
  G ⁏ e ⊢ trm_call (avar_f x) m (avar_f y) ∶ R ->
  exists (TC TZ TR : typ),
    (G ⁏ e ⊢ x ∶ typ_rcd (dec_met m TC TZ TR)) /\
    (G ⁏ e ⊢ y ∶ TZ) /\
    (G ⁏ e ⊢ x ∶ open y TC) /\
    (G ⁏ e ⊢ open_met y x TR <: R).
Proof.
  intros H. remember (trm_call (avar_f x) m (avar_f y)) as t0 eqn:E.
  induction H; try discriminate; subst.
  - match goal with Ex : trm_call (avar_f ?x0) ?m0 (avar_f ?y0) =
                           trm_call (avar_f x) m (avar_f y) |- _ =>
      injection Ex as Exx Em Eyy; subst end.
    match goal with
    | Hx : @obj_typing var (ty_var typing_mode) G objctx_empty e x
             (typ_rcd (dec_met m ?TC ?TZ ?TR)) |- _ =>
        match goal with
        | Hy : @obj_typing var (ty_var typing_mode) G objctx_empty e y ?TZ |- _ =>
            match goal with
            | Hx2 : @obj_typing var (ty_var typing_mode) G objctx_empty e x
                      (open y TC) |- _ =>
                exists TC, TZ, TR;
                split; [ exact Hx | split; [ exact Hy | split; [ exact Hx2 | apply subtyp_refl ] ] ]
            end
        end
    end.
  - match goal with
    | IH : ((_ = _) -> exists (TC TZ TR : typ), _) |- _ =>
        assert (Hz : trm_call (avar_f x) m (avar_f y) =
                    trm_call (avar_f x) m (avar_f y)) by reflexivity;
        pose proof (IH Hz) as Hzz;
        repeat match goal with
               | Hs : exists _, _ |- _ => destruct Hs
               | Hs : (_ /\ _) |- _ => destruct Hs
               end;
        eexists; eexists; eexists;
        split; [ eassumption | split; [ eassumption | split; [ eassumption | ] ] ];
        match goal with
        | H2 : (G ⁏ e ⊢ ?U0 <: ?T0) |- _ =>
            eapply subtyp_trans with (S := U0) (T := T0);
            [ exact H2 | eassumption ]
        end
    end.
Qed.

Lemma imm_ty_trm_read_inv (G : ctx) (e : renv) (x : var) (a : fld_label) (R : typ) :
  G ⁏ e ⊢ trm_read (avar_f x) a ∶ R ->
  exists (S Tf U : typ),
    (G ⁏ e ⊢ x ∶ typ_rcd (dec_fld a S Tf)) /\
    viewpoint_adapt typing_mode x G objctx_empty e Tf U /\
    (G ⁏ e ⊢ U <: R).
Proof.
  intros H. remember (trm_read (avar_f x) a) as t0 eqn:E.
  induction H; try discriminate; subst.
  - match goal with Ex : trm_read (avar_f ?x0) ?a0 = trm_read (avar_f x) a |- _ =>
      injection Ex as Exx Eaa; subst end.
    match goal with
    | Hx : @obj_typing var (ty_var typing_mode) G objctx_empty e x
             (typ_rcd (dec_fld a ?S ?Tf)) |- _ =>
        match goal with
        | Hview : viewpoint_adapt typing_mode x G objctx_empty e Tf ?U |- _ =>
            exists S, Tf, U;
            split; [ exact Hx | split; [ exact Hview | apply subtyp_refl ] ]
        end
    end.
  - match goal with
    | IH : ((_ = _) -> exists (S Tf U : typ), _) |- _ =>
        assert (Hz : trm_read (avar_f x) a = trm_read (avar_f x) a) by reflexivity;
        pose proof (IH Hz) as Hzz;
        repeat match goal with
               | Hs : exists _, _ |- _ => destruct Hs
               | Hs : (_ /\ _) |- _ => destruct Hs
               end;
        eexists; eexists; eexists;
        split; [ eassumption | split; [ eassumption | ] ];
        match goal with
        | H2 : (G ⁏ e ⊢ ?U0 <: ?T0) |- _ =>
            eapply subtyp_trans with (S := U0) (T := T0);
            [ exact H2 | eassumption ]
        end
    end.
Qed.

Lemma imm_ty_trm_write_inv (G : ctx) (e : renv) (x y : var) (a : fld_label) (R : typ) :
  G ⁏ e ⊢ trm_write (avar_f x) a (avar_f y) ∶ R ->
  exists (S Tf : typ),
    (G ⁏ e ⊢ x ∶ typ_rcd (dec_fld a S Tf)) /\
    (G ⁏ e ⊢ y ∶ S) /\
    (G ⁏ e ⊢ Tf <: R).
Proof.
  intros H. remember (trm_write (avar_f x) a (avar_f y)) as t0 eqn:E.
  induction H; try discriminate; subst.
  - match goal with Ex : trm_write (avar_f ?x0) ?a0 (avar_f ?y0) =
                           trm_write (avar_f x) a (avar_f y) |- _ =>
      injection Ex as Exx Eaa Eyy; subst end.
    match goal with
    | Hx : @obj_typing var (ty_var typing_mode) G objctx_empty e x
             (typ_rcd (dec_fld a ?S ?Tf)) |- _ =>
        match goal with
        | Hy : @obj_typing var (ty_var typing_mode) G objctx_empty e y ?S |- _ =>
            exists S, Tf;
            split; [ exact Hx | split; [ exact Hy | apply subtyp_refl ] ]
        end
    end.
  - match goal with
    | IH : ((_ = _) -> exists (S Tf : typ), _) |- _ =>
        assert (Hz : trm_write (avar_f x) a (avar_f y) =
                    trm_write (avar_f x) a (avar_f y)) by reflexivity;
        pose proof (IH Hz) as Hzz;
        repeat match goal with
               | Hs : exists _, _ |- _ => destruct Hs
               | Hs : (_ /\ _) |- _ => destruct Hs
               end;
        eexists; eexists;
        split; [ eassumption | split; [ eassumption | ] ];
        match goal with
        | H2 : (G ⁏ e ⊢ ?U0 <: ?T0) |- _ =>
            eapply subtyp_trans with (S := U0) (T := T0);
            [ exact H2 | eassumption ]
        end
    end.
Qed.

(* -------- stack typing under context and environment extension -------- *)

Lemma imm_ty_stack_ctx_weaken (G G' : ctx) (e : renv) (T : typ)
      (s : stack) (U : typ) :
  @ty_stack typing_mode G e T s U ->
  (forall a W, @ctx_binds a W G -> @ctx_binds a W G') ->
  (forall a, @ctx_vis G a -> @ctx_vis G' a) ->
  @ty_stack typing_mode G' e T s U.
Proof.
  intros H. induction H as
    [ G0 e0 T0 U0 Hsub
    | L0 G0 e0 s0 t0 S0 T0 U0 Hrest IH Hbody ];
    intros Hm Hv.
  - eapply ty_stack_nil.
    eapply imm_ts_sub_weaken; [ exact Hsub | exact Hm | exact Hv ].
  - eapply ty_stack_let.
    + apply IH; assumption.
    + intros x Hx.
      eapply (proj1 imm_rules_ctx_weaken).
      * apply Hbody. exact Hx.
      * apply imm_ctx_binds_push_mono. exact Hm.
      * apply imm_ctx_vis_push_mono. exact Hv.
Qed.

Lemma imm_ty_stack_renv_mono (G : ctx) (e e' : renv) (T : typ)
      (s : stack) (U : typ) :
  @ty_stack typing_mode G e T s U ->
  env_binds_more e e' ->
  @ty_stack typing_mode G e' T s U.
Proof.
  intros H. induction H as
    [ G0 e0 T0 U0 Hsub
    | L0 G0 e0 s0 t0 S0 T0 U0 Hrest IH Hbody ];
    intros Hmore.
  - eapply ty_stack_nil.
    eapply (proj1 (proj2 (imm_ts_renv_mono e'))); [ exact Hsub | exact Hmore ].
  - eapply ty_stack_let.
    + apply IH. exact Hmore.
    + intros x Hx.
      eapply (proj1 (imm_rules_renv_mono e')); [ apply Hbody; exact Hx | exact Hmore ].
Qed.

(* -------- free-variable kind facts for reducing the active term -------- *)

Lemma imm_all_tfree_k_let (G : ctx) (a b : trm) (vk : varkind) :
  all_tfree_k G (trm_let a b) vk ->
  all_tfree_k G a vk /\ all_tfree_k G b vk.
Proof.
  intros H. split; intros w Hw.
  - apply H. apply tfree_trm_let_l. exact Hw.
  - apply H. apply tfree_trm_let_r. exact Hw.
Qed.

Lemma imm_all_tfree_k_lit_l (G : ctx) (l : lit) (u : trm) (vk : varkind) :
  all_tfree_k G (trm_lit l u) vk -> all_tfree_k G l vk.
Proof.
  intros H w Hw. apply H. apply tfree_trm_lit_l. exact Hw.
Qed.

Lemma imm_all_tfree_k_lit_r (G : ctx) (l : lit) (u : trm) (vk : varkind) :
  all_tfree_k G (trm_lit l u) vk -> all_tfree_k G u vk.
Proof.
  intros H w Hw. apply H. apply tfree_trm_lit_r. exact Hw.
Qed.

Lemma imm_all_tfree_k_stack_cons (G : ctx) (t : trm) (st : stack)
      (vk : varkind) :
  all_tfree_k G t vk ->
  all_tfree_k_stack G st vk ->
  all_tfree_k_stack G (stack_cons (frame_let t) st) vk.
Proof.
  intros Ht Hs w Hw. inversion Hw; subst.
  - apply Ht. assumption.
  - apply Hs. assumption.
Qed.

Lemma imm_all_tfree_k_var (G : ctx) (v : var) (vk : varkind) :
  (forall w, tfree w (trm_var (avar_f v)) -> ctx_k G w vk) ->
  (forall w, w = v -> ctx_k G w vk).
Proof.
  intros H w E. subst w. apply H. apply tfree_trm_var.
Qed.

(* -------- renaming the typing-equivalence judgment -------- *)

Lemma imm_binds_val_neq (e : renv) (v1 v2 z : var) :
  binds v1 v2 e -> z \notin fv_env e -> v2 <> z.
Proof.
  intros Hb Hf E. subst v2.
  pose proof (@fv_in_values_binds var z (@fv var VarFreeVar) v1 z e Hb Hf) as Hz.
  apply Hz. cbn. apply in_singleton_self.
Qed.

Lemma imm_tyq_var_subst (z x : var) (e : renv) :
  z \notin dom e -> z \notin fv_env e ->
  forall (v1 v2 : var), e ⊢ v1 ≈ v2 -> e ⊢ subst_var z x v1 ≈ subst_var z x v2.
Proof.
  intros Hd Hf v1 v2 H.
  induction H as [ e0 v0 | e0 a b Hb | e0 a b Hp IH | e0 a b c Hp1 IH1 Hp2 IH2 ].
  - apply tyq_var_refl.
  - assert (E1 : a <> z).
    { intro E. subst a. apply Hd. eapply imm_binds_in_dom. exact Hb. }
    assert (E2 : b <> z).
    { eapply imm_binds_val_neq; [ exact Hb | exact Hf ]. }
    rewrite (@imm_subst_var_neq z x a E1), (@imm_subst_var_neq z x b E2).
    apply tyq_var_binds. exact Hb.
  - apply tyq_var_sym. first [ exact IH | exact (IH Hd Hf) ].
  - eapply tyq_var_trans;
      [ first [ exact IH1 | exact (IH1 Hd Hf) ]
      | first [ exact IH2 | exact (IH2 Hd Hf) ] ].
Qed.

Lemma imm_typ_nulary_subst (z x : var) (T : typ) :
  typ_nulary T -> subst_var z x T = T.
Proof. intros H. inversion H; reflexivity. Qed.

Lemma imm_soc_typ_open (z x y : var) (T : typ) (n : nat) :
  subst_var z x (open_rec n y T) = open_rec n (subst_var z x y) (subst_var z x T).
Proof. intros. exact (proj1 (imm_subst_open_commut_typ_dec z x y) T n). Qed.

Lemma imm_tyq_typ_subst (z x : var) (e : renv) :
  z \notin dom e -> z \notin fv_env e ->
  forall (T1 T2 : typ), z \notin fv T1 -> z \notin fv T2 ->
    e ⊢ T1 ≈ T2 -> e ⊢ subst_var z x T1 ≈ subst_var z x T2.
Proof.
  intros Hd Hf T1 T2 Hn1 Hn2 H.
  induction H as
    [ e0 U0 Hnu
    | T0 e0 a11 a12 a21 a22 Htyp H1 IH1 H2 IH2
    | e0 a11 a12 a21 a22 H1 IH1 Hbody IHbody
    | e0 l0 a11 a12 a21 a22 H1 IH1 H2 IH2
    | e0 B0 a11 a12 a21 a22 H1 IH1 H2 IH2
    | e0 v1 v2 v3 l0 Hv
    | e0 v1 v2 l0
    | e0 a1 a2 Hbody IHbody
    | m0 e0 a11 a12 a13 a21 a22 a23 H1 IH1 H2 IH2 H3 IH3 ].
  - rewrite (@imm_typ_nulary_subst z x U0 Hnu).
    apply tyq_typ_nulary. exact Hnu.
  - match goal with Ha : typ_andor T0 |- _ => inversion Ha; subst end.
    all: cbn;
      assert (Hn11 : z \notin fv a11)
        by (intro E; apply Hn1; cbn; rewrite in_union; left; exact E);
      assert (Hn12 : z \notin fv a12)
        by (intro E; apply Hn1; cbn; rewrite in_union; right; exact E);
      assert (Hn21 : z \notin fv a21)
        by (intro E; apply Hn2; cbn; rewrite in_union; left; exact E);
      assert (Hn22 : z \notin fv a22)
        by (intro E; apply Hn2; cbn; rewrite in_union; right; exact E);
      eapply tyq_typ_andor;
      [ constructor
      | exact (IH1 Hd Hf Hn11 Hn21)
      | exact (IH2 Hd Hf Hn12 Hn22) ].
  - cbn.
    assert (Hn11 : z \notin fv a11)
      by (intro E; apply Hn1; cbn; rewrite in_union; left; exact E).
    assert (Hn12 : z \notin fv a12)
      by (intro E; apply Hn1; cbn; rewrite in_union; right; exact E).
    assert (Hn21 : z \notin fv a21)
      by (intro E; apply Hn2; cbn; rewrite in_union; left; exact E).
    assert (Hn22 : z \notin fv a22)
      by (intro E; apply Hn2; cbn; rewrite in_union; right; exact E).
    eapply tyq_typ_fun.
    + exact (IH1 Hd Hf Hn11 Hn21).
    + intros y. destruct (classic (y = z)) as [E | Hne].
      * subst y.
        rewrite ((proj1 (imm_subst_fresh_typ_dec_proj z x) a12 Hn12)),
                ((proj1 (imm_subst_fresh_typ_dec_proj z x) a22 Hn22)).
        apply Hbody.
      * assert (Hf1 : z \notin fv (open y a12)).
        { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y a12 0 z Ez) as [E1 | E2].
          - apply Hn12. exact E1.
          - apply Hne. symmetry. exact E2. }
        assert (Hf2 : z \notin fv (open y a22)).
        { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y a22 0 z Ez) as [E1 | E2].
          - apply Hn22. exact E1.
          - apply Hne. symmetry. exact E2. }
        pose proof (IHbody y Hd Hf Hf1 Hf2) as Hr.
        rewrite (imm_soc_typ_open z x y a12 0),
                (imm_soc_typ_open z x y a22 0),
                (@imm_subst_var_neq z x y Hne) in Hr.
        exact Hr.
  - cbn.
    assert (Hn11 : z \notin fv a11)
      by (intro E; apply Hn1; cbn; rewrite in_union; left; exact E).
    assert (Hn12 : z \notin fv a12)
      by (intro E; apply Hn1; cbn; rewrite in_union; right; exact E).
    assert (Hn21 : z \notin fv a21)
      by (intro E; apply Hn2; cbn; rewrite in_union; left; exact E).
    assert (Hn22 : z \notin fv a22)
      by (intro E; apply Hn2; cbn; rewrite in_union; right; exact E).
    eapply tyq_typ_fld.
    + exact (IH1 Hd Hf Hn11 Hn21).
    + exact (IH2 Hd Hf Hn12 Hn22).
  - cbn.
    assert (Hn11 : z \notin fv a11)
      by (intro E; apply Hn1; cbn; rewrite in_union; left; exact E).
    assert (Hn12 : z \notin fv a12)
      by (intro E; apply Hn1; cbn; rewrite in_union; right; exact E).
    assert (Hn21 : z \notin fv a21)
      by (intro E; apply Hn2; cbn; rewrite in_union; left; exact E).
    assert (Hn22 : z \notin fv a22)
      by (intro E; apply Hn2; cbn; rewrite in_union; right; exact E).
    eapply tyq_typ_typ.
    + intros y. destruct (classic (y = z)) as [E | Hne].
      * subst y.
        change (e0 ⊢ open z (subst_var z x a11) ≈ open z (subst_var z x a21)).
        rewrite ((proj1 (imm_subst_fresh_typ_dec_proj z x) a11 Hn11)),
                ((proj1 (imm_subst_fresh_typ_dec_proj z x) a21 Hn21)).
        apply H1.
      * assert (Hf1 : z \notin fv (open y a11)).
        { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y a11 0 z Ez) as [E1 | E2].
          - apply Hn11. exact E1.
          - apply Hne. symmetry. exact E2. }
        assert (Hf2 : z \notin fv (open y a21)).
        { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y a21 0 z Ez) as [E1 | E2].
          - apply Hn21. exact E1.
          - apply Hne. symmetry. exact E2. }
        pose proof (IH1 y Hd Hf Hf1 Hf2) as Hr.
        rewrite (imm_soc_typ_open z x y a11 0),
                (imm_soc_typ_open z x y a21 0),
                (@imm_subst_var_neq z x y Hne) in Hr.
        exact Hr.
    + intros y. destruct (classic (y = z)) as [E | Hne].
      * subst y.
        change (e0 ⊢ open z (subst_var z x a12) ≈ open z (subst_var z x a22)).
        rewrite ((proj1 (imm_subst_fresh_typ_dec_proj z x) a12 Hn12)),
                ((proj1 (imm_subst_fresh_typ_dec_proj z x) a22 Hn22)).
        apply H2.
      * assert (Hf1 : z \notin fv (open y a12)).
        { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y a12 0 z Ez) as [E1 | E2].
          - apply Hn12. exact E1.
          - apply Hne. symmetry. exact E2. }
        assert (Hf2 : z \notin fv (open y a22)).
        { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y a22 0 z Ez) as [E1 | E2].
          - apply Hn22. exact E1.
          - apply Hne. symmetry. exact E2. }
        pose proof (IH2 y Hd Hf Hf1 Hf2) as Hr.
        rewrite (imm_soc_typ_open z x y a12 0),
                (imm_soc_typ_open z x y a22 0),
                (@imm_subst_var_neq z x y Hne) in Hr.
        exact Hr.
  - cbn. eapply tyq_typ_sel_normal.
    apply imm_tyq_var_subst; assumption.
  - cbn. apply tyq_typ_sel.
  - cbn.
    assert (Hn1' : z \notin fv a1)
      by (intro E; apply Hn1; cbn; exact E).
    assert (Hn2' : z \notin fv a2)
      by (intro E; apply Hn2; cbn; exact E).
    eapply tyq_typ_bnd.
    intros y. destruct (classic (y = z)) as [E | Hne].
    + subst y.
      change (e0 ⊢ open z (subst_var z x a1) ≈ open z (subst_var z x a2)).
      rewrite ((proj1 (imm_subst_fresh_typ_dec_proj z x) a1 Hn1')),
              ((proj1 (imm_subst_fresh_typ_dec_proj z x) a2 Hn2')).
      apply Hbody.
    + assert (Hf1 : z \notin fv (open y a1)).
      { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y a1 0 z Ez) as [E1 | E2].
        - apply Hn1'. exact E1.
        - apply Hne. symmetry. exact E2. }
      assert (Hf2 : z \notin fv (open y a2)).
      { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y a2 0 z Ez) as [E1 | E2].
        - apply Hn2'. exact E1.
        - apply Hne. symmetry. exact E2. }
      pose proof (IHbody y Hd Hf Hf1 Hf2) as Hr.
      rewrite (imm_soc_typ_open z x y a1 0),
              (imm_soc_typ_open z x y a2 0),
              (@imm_subst_var_neq z x y Hne) in Hr.
      exact Hr.
  - cbn.
    assert (Hn11 : z \notin fv a11)
      by (intro E; apply Hn1; cbn; rewrite in_union; left; exact E).
    assert (Hn12 : z \notin fv a12)
      by (intro E; apply Hn1; cbn; rewrite in_union; right;
          rewrite in_union; left; exact E).
    assert (Hn13 : z \notin fv a13)
      by (intro E; apply Hn1; cbn; rewrite in_union; right;
          rewrite in_union; right; exact E).
    assert (Hn21 : z \notin fv a21)
      by (intro E; apply Hn2; cbn; rewrite in_union; left; exact E).
    assert (Hn22 : z \notin fv a22)
      by (intro E; apply Hn2; cbn; rewrite in_union; right;
          rewrite in_union; left; exact E).
    assert (Hn23 : z \notin fv a23)
      by (intro E; apply Hn2; cbn; rewrite in_union; right;
          rewrite in_union; right; exact E).
    eapply tyq_typ_met.
    + intros y. destruct (classic (y = z)) as [E | Hne].
      * subst y.
        change (e0 ⊢ open z (subst_var z x a11) ≈ open z (subst_var z x a21)).
        rewrite ((proj1 (imm_subst_fresh_typ_dec_proj z x) a11 Hn11)),
                ((proj1 (imm_subst_fresh_typ_dec_proj z x) a21 Hn21)).
        apply H1.
      * assert (Hf1 : z \notin fv (open y a11)).
        { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y a11 0 z Ez) as [E1 | E2].
          - apply Hn11. exact E1.
          - apply Hne. symmetry. exact E2. }
        assert (Hf2 : z \notin fv (open y a21)).
        { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y a21 0 z Ez) as [E1 | E2].
          - apply Hn21. exact E1.
          - apply Hne. symmetry. exact E2. }
        pose proof (IH1 y Hd Hf Hf1 Hf2) as Hr.
        rewrite (imm_soc_typ_open z x y a11 0),
                (imm_soc_typ_open z x y a21 0),
                (@imm_subst_var_neq z x y Hne) in Hr.
        exact Hr.
    + exact (IH2 Hd Hf Hn12 Hn22).
    + intros y1 y2.
      destruct (classic (y1 = z)) as [E1 | Hne1].
      * subst y1. destruct (classic (y2 = z)) as [E2 | Hne2].
        -- subst y2.
           change (e0 ⊢ open_rec 0 z (open_rec 1 z (subst_var z x a13))
                     ≈ open_rec 0 z (open_rec 1 z (subst_var z x a23))).
           rewrite ((proj1 (imm_subst_fresh_typ_dec_proj z x) a13 Hn13)),
                   ((proj1 (imm_subst_fresh_typ_dec_proj z x) a23 Hn23)).
           apply H3.
        -- change (e0 ⊢ open_rec 0 z (open_rec 1 y2 (subst_var z x a13))
                     ≈ open_rec 0 z (open_rec 1 y2 (subst_var z x a23))).
           rewrite ((proj1 (imm_subst_fresh_typ_dec_proj z x) a13 Hn13)),
                  ((proj1 (imm_subst_fresh_typ_dec_proj z x) a23 Hn23)).
           apply H3.
      * destruct (classic (y2 = z)) as [E2 | Hne2].
        -- subst y2.
           change (e0 ⊢ open_rec 0 y1 (open_rec 1 z (subst_var z x a13))
                     ≈ open_rec 0 y1 (open_rec 1 z (subst_var z x a23))).
           rewrite ((proj1 (imm_subst_fresh_typ_dec_proj z x) a13 Hn13)),
                   ((proj1 (imm_subst_fresh_typ_dec_proj z x) a23 Hn23)).
           apply H3.
        -- assert (Hi1 : z \notin fv (open_rec 1 y2 a13)).
           { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y2 a13 1 z Ez) as [E1 | E2].
             - apply Hn13. exact E1.
             - apply Hne2. symmetry. exact E2. }
           assert (Hi2 : z \notin fv (open_rec 1 y2 a23)).
           { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y2 a23 1 z Ez) as [E1 | E2].
             - apply Hn23. exact E1.
             - apply Hne2. symmetry. exact E2. }
           assert (Hf1 : z \notin fv (open_met y1 y2 a13)).
           { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y1 (open_rec 1 y2 a13) 0 z Ez)
               as [E1 | E2].
             - apply Hi1. exact E1.
             - apply Hne1. symmetry. exact E2. }
           assert (Hf2 : z \notin fv (open_met y1 y2 a23)).
           { intro Ez. destruct (@imm_fv_open_subset_mem typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax imm_foc_typ y1 (open_rec 1 y2 a23) 0 z Ez)
               as [E1 | E2].
             - apply Hi2. exact E1.
             - apply Hne1. symmetry. exact E2. }
           pose proof (IH3 y1 y2 Hd Hf Hf1 Hf2) as Hr.
           rewrite (imm_soc_typ_open z x y1 (open_rec 1 y2 a13) 0),
                   (imm_soc_typ_open z x y2 a13 1),
                   (imm_soc_typ_open z x y1 (open_rec 1 y2 a23) 0),
                   (imm_soc_typ_open z x y2 a23 1),
                   (@imm_subst_var_neq z x y1 Hne1),
                   (@imm_subst_var_neq z x y2 Hne2) in Hr.
           exact Hr.
Qed.

(* ================= list substitutions and tyq invariance ================= *)

Definition imm_hfix (e : renv) (l : list (var * var)) : Prop :=
  forall z x, List.In (z, x) l -> z \notin dom e /\ z \notin fv_env e.

Fixpoint imm_pairs_fv (l : list (var * var)) : vars :=
  match l with
  | nil => \{}
  | cons (z, x) l' => \{z} \u \{x} \u imm_pairs_fv l'
  end.

Fixpoint imm_substl_var (l : list (var * var)) (v : var) : var :=
  match l with
  | nil => v
  | cons (z, x) l' => subst_var z x (imm_substl_var l' v)
  end.

Fixpoint imm_substl_avar (l : list (var * var)) (a : avar) : avar :=
  match l with
  | nil => a
  | cons (z, x) l' => subst_var z x (imm_substl_avar l' a)
  end.

Fixpoint imm_substl_typ (l : list (var * var)) (T : typ) : typ :=
  match l with
  | nil => T
  | cons (z, x) l' => subst_var z x (imm_substl_typ l' T)
  end.

Fixpoint imm_substl_dec (l : list (var * var)) (D : dec) : dec :=
  match l with
  | nil => D
  | cons (z, x) l' => subst_var z x (imm_substl_dec l' D)
  end.

(* A fresh variable can always be found outside a finite set. *)
Lemma imm_pick_fresh (L : vars) : exists w : var, w \notin L.
Proof.
  destruct (var_freshes L 1) as [xs Hxs].
  destruct xs as [| w xs].
  - cbn in Hxs. destruct Hxs.
  - cbn in Hxs. destruct Hxs as [Hw _]. exists w. exact Hw.
Qed.

(* A binding's value is mentioned by the free variables of the environment. *)
Lemma imm_binds_val_in_fv_env (E : renv) (x y : var) :
  binds x y E -> y \in fv_env E.
Proof.
  intros Hb. destruct (classic (y \in fv_env E)) as [H | H]; [ exact H | ].
  exfalso.
  assert (Hy : y \in fv y) by (rewrite imm_fv_var; apply in_singleton_self).
  exact ((@fv_in_values_binds var y (@fv var VarFreeVar) x y E Hb H) Hy).
Qed.

(* Constructor push equations for the list substitution. *)
Lemma imm_substl_typ_top l : imm_substl_typ l typ_top = typ_top.
Proof. induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity]. Qed.
Lemma imm_substl_typ_bot l : imm_substl_typ l typ_bot = typ_bot.
Proof. induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity]. Qed.
Lemma imm_substl_typ_nocap l : imm_substl_typ l typ_nocap = typ_nocap.
Proof. induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity]. Qed.

Lemma imm_substl_typ_and l a b :
  imm_substl_typ l (typ_and a b) = typ_and (imm_substl_typ l a) (imm_substl_typ l b).
Proof.
  induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_typ_or l a b :
  imm_substl_typ l (typ_or a b) = typ_or (imm_substl_typ l a) (imm_substl_typ l b).
Proof.
  induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_typ_fun l a b :
  imm_substl_typ l (typ_fun a b) = typ_fun (imm_substl_typ l a) (imm_substl_typ l b).
Proof.
  induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_typ_bnd l a :
  imm_substl_typ l (typ_bnd a) = typ_bnd (imm_substl_typ l a).
Proof.
  induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_typ_rcd l D :
  imm_substl_typ l (typ_rcd D) = typ_rcd (imm_substl_dec l D).
Proof.
  induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_typ_sel l a A b :
  imm_substl_typ l (typ_sel a A b) =
  typ_sel (imm_substl_avar l a) A (imm_substl_avar l b).
Proof.
  induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_dec_typ l A X Y :
  imm_substl_dec l (dec_typ A X Y) =
  dec_typ A (imm_substl_typ l X) (imm_substl_typ l Y).
Proof.
  induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_dec_fld l a X Y :
  imm_substl_dec l (dec_fld a X Y) =
  dec_fld a (imm_substl_typ l X) (imm_substl_typ l Y).
Proof.
  induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_dec_met l m X Y Z :
  imm_substl_dec l (dec_met m X Y Z) =
  dec_met m (imm_substl_typ l X) (imm_substl_typ l Y) (imm_substl_typ l Z).
Proof.
  induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.

Lemma imm_substl_typ_nulary l T :
  typ_nulary T -> imm_substl_typ l T = T.
Proof.
  intros H. inversion H; subst;
    [ apply imm_substl_typ_top | apply imm_substl_typ_bot | apply imm_substl_typ_nocap ].
Qed.

(* Commutation of the list substitution with opening. *)
Lemma imm_substl_typ_open l n y T :
  imm_substl_typ l (open_rec n y T) =
  open_rec n (imm_substl_var l y) (imm_substl_typ l T).
Proof.
  induction l as [|[z x] l' IH]; cbn; [reflexivity |].
  rewrite IH.
  rewrite (imm_soc_typ_open z x (imm_substl_var l' y) (imm_substl_typ l' T) n).
  reflexivity.
Qed.

(* Membership in the set of variables mentioned by a pair list. *)
Lemma imm_pairs_fv_in (l : list (var * var)) (z x : var) :
  List.In (z, x) l -> z \in imm_pairs_fv l /\ x \in imm_pairs_fv l.
Proof.
  induction l as [|[a b] l' IH]; intros Hin.
  - inversion Hin.
  - cbn [imm_pairs_fv]. destruct Hin as [E | Hin].
    + injection E as E1 E2. subst z x. split.
      * rewrite in_union. left. apply in_singleton_self.
      * rewrite in_union. right. rewrite in_union. left. apply in_singleton_self.
    + destruct (IH Hin) as [Hz Hx]. split.
      * rewrite in_union. right. rewrite in_union. right. exact Hz.
      * rewrite in_union. right. rewrite in_union. right. exact Hx.
Qed.

Lemma imm_pairs_fv_notin (l : list (var * var)) (w z x : var) :
  w \notin imm_pairs_fv l -> List.In (z, x) l -> w <> z /\ w <> x.
Proof.
  induction l as [|[a b] l' IH]; intros H Hin.
  - inversion Hin.
  - cbn [imm_pairs_fv] in H.
    apply notin_union in H. destruct H as [Ha H].
    apply notin_union in H. destruct H as [Hb Hl].
    destruct Hin as [E | Hin].
    + injection E as E1 E2. subst z x. split;
        [ apply notin_singleton in Ha | apply notin_singleton in Hb ]; assumption.
    + eapply IH; eassumption.
Qed.

(* The list substitution fixes variables that are not among its sources. *)
Lemma imm_substl_var_notin_src l w :
  (forall z x, List.In (z, x) l -> w <> z) -> imm_substl_var l w = w.
Proof.
  induction l as [|[z x] l' IH]; intros H; cbn; [reflexivity |].
  assert (Hw : w <> z) by (apply (H z x); left; reflexivity).
  rewrite (IH (fun a b Hin => H a b (or_intror Hin))).
  apply imm_subst_var_neq. exact Hw.
Qed.

(* The list substitution does not introduce a fresh variable. *)
Lemma imm_fv_substl_notin l w T :
  w \notin fv T ->
  (forall z x, List.In (z, x) l -> w <> z /\ w <> x) ->
  w \notin fv (imm_substl_typ l T).
Proof.
  intros HT Hl. induction l as [|[z x] l' IH]; cbn; [exact HT |].
  assert (Htail : forall a b, List.In (a, b) l' -> w <> a /\ w <> b).
  { intros a b Hin. apply Hl. right. exact Hin. }
  assert (Hnot : w \notin fv (imm_substl_typ l' T)) by (apply IH; exact Htail).
  destruct (proj1 (imm_fv_subst_cases_typ_dec_proj z x) (imm_substl_typ l' T))
    as [[Hfv _] | [Hne [Hin Hfv]]].
  - rewrite Hfv. exact Hnot.
  - rewrite Hfv. apply notin_union. split.
    + intro E. rewrite in_remove in E. destruct E as [E _]. exact (Hnot E).
    + apply notin_singleton. apply (Hl z x (or_introl eq_refl)).
Qed.

(* Opening a binder and then extending the substitution at the fresh variable. *)
Lemma imm_substl_open_push l w y T :
  (forall z x, List.In (z, x) l -> w <> z /\ w <> x) ->
  w \notin fv (imm_substl_typ l T) ->
  imm_substl_typ ((w, y) :: l) (open_rec 0 w T) =
  open_rec 0 y (imm_substl_typ l T).
Proof.
  intros Hl Hfv. cbn [imm_substl_typ].
  rewrite (@imm_substl_typ_open l 0 w T).
  rewrite (@imm_substl_var_notin_src l w (fun z x Hin => proj1 (Hl z x Hin))).
  rewrite (imm_soc_typ_open w y w (imm_substl_typ l T) 0).
  rewrite (proj1 (imm_subst_fresh_typ_dec_proj w y) (imm_substl_typ l T) Hfv).
  rewrite imm_subst_var_self.
  reflexivity.
Qed.

(* Two nested openings, as in the method-branch premise. *)
Lemma imm_substl_open_met_push l w1 w2 y1 y2 T :
  (forall z x, List.In (z, x) l -> w1 <> z /\ w1 <> x) ->
  (forall z x, List.In (z, x) l -> w2 <> z /\ w2 <> x) ->
  w1 \notin fv (imm_substl_typ l T) ->
  w2 \notin fv (imm_substl_typ l T) ->
  w1 <> w2 ->
  w2 <> y1 ->
  imm_substl_typ ((w2, y2) :: (w1, y1) :: l) (open_met w1 w2 T) =
  open_met y1 y2 (imm_substl_typ l T).
Proof.
  intros H1 H2 Hf1 Hf2 Hne Hne2.
  assert (HV : imm_substl_var ((w1, y1) :: l) w1 = y1).
  { cbn [imm_substl_var].
    rewrite (@imm_substl_var_notin_src l w1 (fun z x Hin => proj1 (H1 z x Hin))).
    apply imm_subst_var_self. }
  assert (HT1 : imm_substl_typ ((w1, y1) :: l) (open_rec 1 w2 T) =
                open_rec 1 w2 (imm_substl_typ l T)).
  { cbn [imm_substl_typ].
    rewrite (@imm_substl_typ_open l 1 w2 T).
    rewrite (@imm_substl_var_notin_src l w2 (fun z x Hin => proj1 (H2 z x Hin))).
    rewrite (imm_soc_typ_open w1 y1 w2 (imm_substl_typ l T) 1).
    rewrite (@imm_subst_var_neq w1 y1 w2 (fun E => Hne (eq_sym E))).
    rewrite (proj1 (imm_subst_fresh_typ_dec_proj w1 y1) (imm_substl_typ l T) Hf1).
    reflexivity. }
  unfold open_met.
  change (subst_var w2 y2
            (imm_substl_typ ((w1, y1) :: l) (open_rec 0 w1 (open_rec 1 w2 T)))
          = open_rec 0 y1 (open_rec 1 y2 (imm_substl_typ l T))).
  rewrite (@imm_substl_typ_open ((w1, y1) :: l) 0 w1 (open_rec 1 w2 T)).
  rewrite HV, HT1.
  rewrite (imm_soc_typ_open w2 y2 y1 (open_rec 1 w2 (imm_substl_typ l T)) 0).
  rewrite (imm_soc_typ_open w2 y2 w2 (imm_substl_typ l T) 1).
  rewrite (@imm_subst_var_neq w2 y2 y1 (fun E => Hne2 (eq_sym E))).
  rewrite imm_subst_var_self.
  rewrite (proj1 (imm_subst_fresh_typ_dec_proj w2 y2) (imm_substl_typ l T) Hf2).
  reflexivity.
Qed.


(* ---------- variable equivalence is stable under list substitution ---------- *)

Lemma imm_tyq_var_substl (e : renv) :
  forall (a b : var), e ⊢ a ≈ b ->
  forall (l : list (var * var)), imm_hfix e l ->
    e ⊢ imm_substl_var l a ≈ imm_substl_var l b.
Proof.
  intros a b H.
  induction H as
    [ e0 v
    | e0 v1 v2 Hb
    | e0 v1 v2 Hv IH
    | e0 v1 v2 v3 H1 IH1 H2 IH2 ].
  all: intros l Hfix.
  - apply tyq_var_refl.
  - assert (Hv1 : v1 \in dom e0) by (eapply imm_binds_in_dom; eassumption).
    assert (Hv2 : v2 \in fv_env e0) by (eapply imm_binds_val_in_fv_env; eassumption).
    assert (Hs1 : forall z x, List.In (z, x) l -> v1 <> z).
    { intros z x Hin E. apply (proj1 (Hfix z x Hin)). rewrite <- E. exact Hv1. }
    assert (Hs2 : forall z x, List.In (z, x) l -> v2 <> z).
    { intros z x Hin E. apply (proj2 (Hfix z x Hin)). rewrite <- E. exact Hv2. }
    rewrite (@imm_substl_var_notin_src l v1 Hs1).
    rewrite (@imm_substl_var_notin_src l v2 Hs2).
    apply tyq_var_binds. exact Hb.
  - apply tyq_var_sym. exact (IH l Hfix).
  - eapply tyq_var_trans; [ exact (IH1 l Hfix) | exact (IH2 l Hfix) ].
Qed.

(* ---------- pushing the list substitution through an opening ---------- *)

Lemma imm_substl_avar_f l v :
  imm_substl_avar l (avar_f v) = avar_f (imm_substl_var l v).
Proof.
  induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.

Lemma imm_substl_avar_b l n :
  imm_substl_avar l (avar_b n) = avar_b n.
Proof.
  induction l as [|[z x] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.

(* The common transfer for a binder premise of the type equivalence. *)
Lemma imm_tyq_typ_open_prem (e : renv) (l : list (var * var)) (a b : typ) :
  imm_hfix e l ->
  (forall x l', imm_hfix e l' ->
     e ⊢ imm_substl_typ l' (open x a) ≈ imm_substl_typ l' (open x b)) ->
  forall y, e ⊢ open y (imm_substl_typ l a) ≈ open y (imm_substl_typ l b).
Proof.
  intros Hfix IHbody y.
  destruct (imm_pick_fresh (dom e \u fv_env e \u imm_pairs_fv l \u fv a \u fv b))
    as [w Hw].
  apply notin_union in Hw. destruct Hw as [Hwd Hw].
  apply notin_union in Hw. destruct Hw as [Hwf Hw].
  apply notin_union in Hw. destruct Hw as [Hwp Hw].
  apply notin_union in Hw. destruct Hw as [Hwa Hwb].
  assert (Hlw : forall z x, List.In (z, x) l -> w <> z /\ w <> x).
  { intros z x Hin. exact (@imm_pairs_fv_notin l w z x Hwp Hin). }
  assert (HfA : w \notin fv (imm_substl_typ l a))
    by (apply imm_fv_substl_notin; [ exact Hwa | exact Hlw ]).
  assert (HfB : w \notin fv (imm_substl_typ l b))
    by (apply imm_fv_substl_notin; [ exact Hwb | exact Hlw ]).
  assert (Hfix' : imm_hfix e (cons (w, y) l)).
  { intros z x Hin. destruct Hin as [E | Hin].
    - injection E as <- <-. split; assumption.
    - exact (Hfix z x Hin). }
  pose proof (IHbody w (cons (w, y) l) Hfix') as Hr.
  rewrite (@imm_substl_open_push l w y a Hlw HfA),
          (@imm_substl_open_push l w y b Hlw HfB) in Hr.
  exact Hr.
Qed.

(* The same transfer for the two-binder premise of method types. *)
Lemma imm_tyq_typ_open_met_prem (e : renv) (l : list (var * var)) (a b : typ) :
  imm_hfix e l ->
  (forall x y l', imm_hfix e l' ->
     e ⊢ imm_substl_typ l' (open_met x y a) ≈ imm_substl_typ l' (open_met x y b)) ->
  forall y1 y2,
    e ⊢ open_met y1 y2 (imm_substl_typ l a) ≈ open_met y1 y2 (imm_substl_typ l b).
Proof.
  intros Hfix IH3 y1 y2.
  destruct (imm_pick_fresh (dom e \u fv_env e \u imm_pairs_fv l \u fv a \u fv b))
    as [w1 Hw1].
  apply notin_union in Hw1. destruct Hw1 as [H1d Hw1].
  apply notin_union in Hw1. destruct Hw1 as [H1f Hw1].
  apply notin_union in Hw1. destruct Hw1 as [H1p Hw1].
  apply notin_union in Hw1. destruct Hw1 as [H1a H1b].
  destruct (imm_pick_fresh ((dom e \u fv_env e \u imm_pairs_fv l \u fv a \u fv b)
                              \u \{w1} \u \{y1})) as [w2 Hw2].
  apply notin_union in Hw2. destruct Hw2 as [Hw2L Hw2].
  apply notin_union in Hw2. destruct Hw2 as [Hw2w1 Hw2y1].
  apply notin_union in Hw2L. destruct Hw2L as [H2d Hw2L].
  apply notin_union in Hw2L. destruct Hw2L as [H2f Hw2L].
  apply notin_union in Hw2L. destruct Hw2L as [H2p Hw2L].
  apply notin_union in Hw2L. destruct Hw2L as [H2a H2b].
  assert (Hne : w1 <> w2).
  { apply notin_singleton in Hw2w1. intro E. apply Hw2w1. symmetry. exact E. }
  assert (Hne2 : w2 <> y1).
  { apply notin_singleton in Hw2y1. exact Hw2y1. }
  assert (Hl1 : forall z x, List.In (z, x) l -> w1 <> z /\ w1 <> x).
  { intros z x Hin. exact (@imm_pairs_fv_notin l w1 z x H1p Hin). }
  assert (Hl2 : forall z x, List.In (z, x) l -> w2 <> z /\ w2 <> x).
  { intros z x Hin. exact (@imm_pairs_fv_notin l w2 z x H2p Hin). }
  assert (Hf1a : w1 \notin fv (imm_substl_typ l a))
    by (apply imm_fv_substl_notin; [ exact H1a | exact Hl1 ]).
  assert (Hf1b : w1 \notin fv (imm_substl_typ l b))
    by (apply imm_fv_substl_notin; [ exact H1b | exact Hl1 ]).
  assert (Hf2a : w2 \notin fv (imm_substl_typ l a))
    by (apply imm_fv_substl_notin; [ exact H2a | exact Hl2 ]).
  assert (Hf2b : w2 \notin fv (imm_substl_typ l b))
    by (apply imm_fv_substl_notin; [ exact H2b | exact Hl2 ]).
  assert (Hfix' : imm_hfix e (cons (w2, y2) (cons (w1, y1) l))).
  { intros z x Hin. destruct Hin as [E | Hin].
    - injection E as <- <-. split; assumption.
    - destruct Hin as [E | Hin].
      + injection E as <- <-. split; assumption.
      + exact (Hfix z x Hin). }
  pose proof (IH3 w1 w2 (cons (w2, y2) (cons (w1, y1) l)) Hfix') as Hr.
  rewrite (@imm_substl_open_met_push l w1 w2 y1 y2 a Hl1 Hl2 Hf1a Hf2a Hne Hne2),
          (@imm_substl_open_met_push l w1 w2 y1 y2 b Hl1 Hl2 Hf1b Hf2b Hne Hne2) in Hr.
  exact Hr.
Qed.


(* ---------- the type equivalence is stable under list substitution ---------- *)

Lemma imm_tyq_typ_substl (e : renv) :
  forall (T1 T2 : typ), e ⊢ T1 ≈ T2 ->
  forall (l : list (var * var)), imm_hfix e l ->
    e ⊢ imm_substl_typ l T1 ≈ imm_substl_typ l T2.
Proof.
  intros T1 T2 H.
  induction H as
    [ e0 U0 Hnu
    | T0 e0 a11 a12 a21 a22 Hand H1 IH1 H2 IH2
    | e0 a11 a12 a21 a22 H1 IH1 Hbody IHbody
    | e0 a0 a11 a12 a21 a22 H1 IH1 H2 IH2
    | e0 B0 a11 a12 a21 a22 H1 IH1 H2 IH2
    | e0 v1 v2 v3 l0 Hv
    | e0 v1 v2 l0
    | e0 a1 a2 Hbody IHbody
    | m0 e0 a11 a12 a13 a21 a22 a23 H1 IH1 H2 IH2 H3 IH3 ].
  all: intros l Hfix.
  - rewrite (@imm_substl_typ_nulary l U0 Hnu). apply tyq_typ_nulary. exact Hnu.
  - inversion Hand; subst.
    all: try (rewrite (@imm_substl_typ_and l a11 a12), (@imm_substl_typ_and l a21 a22)).
    all: try (rewrite (@imm_substl_typ_or l a11 a12), (@imm_substl_typ_or l a21 a22)).
    all: eapply tyq_typ_andor; [ constructor | exact (IH1 l Hfix) | exact (IH2 l Hfix) ].
  - rewrite (@imm_substl_typ_fun l a11 a12), (@imm_substl_typ_fun l a21 a22).
    eapply tyq_typ_fun.
    + exact (IH1 l Hfix).
    + exact (@imm_tyq_typ_open_prem e0 l a12 a22 Hfix IHbody).
  - rewrite (@imm_substl_typ_rcd l (dec_fld a0 a11 a12)),
            (@imm_substl_typ_rcd l (dec_fld a0 a21 a22)).
    rewrite (@imm_substl_dec_fld l a0 a11 a12), (@imm_substl_dec_fld l a0 a21 a22).
    eapply tyq_typ_fld; [ exact (IH1 l Hfix) | exact (IH2 l Hfix) ].
  - rewrite (@imm_substl_typ_rcd l (dec_typ B0 a11 a12)),
            (@imm_substl_typ_rcd l (dec_typ B0 a21 a22)).
    rewrite (@imm_substl_dec_typ l B0 a11 a12), (@imm_substl_dec_typ l B0 a21 a22).
    eapply tyq_typ_typ.
    + exact (@imm_tyq_typ_open_prem e0 l a11 a21 Hfix IH1).
    + exact (@imm_tyq_typ_open_prem e0 l a12 a22 Hfix IH2).
  - rewrite (@imm_substl_typ_sel l (avar_f v1) (typ_label_normal l0) v3),
            (@imm_substl_typ_sel l (avar_f v2) (typ_label_normal l0) v3).
    rewrite (@imm_substl_avar_f l v1), (@imm_substl_avar_f l v2).
    eapply tyq_typ_sel_normal.
    exact (@imm_tyq_var_substl e0 v1 v2 Hv l Hfix).
  - rewrite (@imm_substl_typ_sel l v1 l0 v2).
    apply tyq_typ_sel.
  - rewrite (@imm_substl_typ_bnd l a1), (@imm_substl_typ_bnd l a2).
    eapply tyq_typ_bnd.
    exact (@imm_tyq_typ_open_prem e0 l a1 a2 Hfix IHbody).
  - rewrite (@imm_substl_typ_rcd l (dec_met m0 a11 a12 a13)),
            (@imm_substl_typ_rcd l (dec_met m0 a21 a22 a23)).
    rewrite (@imm_substl_dec_met l m0 a11 a12 a13),
            (@imm_substl_dec_met l m0 a21 a22 a23).
    eapply tyq_typ_met.
    + exact (@imm_tyq_typ_open_prem e0 l a11 a21 Hfix IH1).
    + exact (IH2 l Hfix).
    + exact (@imm_tyq_typ_open_met_prem e0 l a13 a23 Hfix IH3).
Qed.


(* ---------- substitution for the type-level judgments ---------- *)

Definition imm_rb (z x : var) (G G' : ctx) : Prop :=
  forall a U, @ctx_binds a U G -> @ctx_binds (subst_var z x a) (subst_var z x U) G'.

Definition imm_rv (z x : var) (G G' : ctx) : Prop :=
  forall a, @ctx_vis G a -> @ctx_vis G' (subst_var z x a).

Lemma imm_subst_var_same (z x : var) : subst_var z x x = x.
Proof.
  destruct (classic (z = x)) as [E | E].
  - subst z. apply imm_subst_var_self.
  - apply imm_subst_var_neq. intro H. exact (E (eq_sym H)).
Qed.

Lemma imm_ctx_binds_push_inv (G : ctx) (y : var) (vk : varkind) (T : typ)
      (a : var) (U : typ) :
  @ctx_binds a U (G § y / vk ~ T) ->
  (a = y /\ U = T) \/ (a <> y /\ @ctx_binds a U G).
Proof. intros H. inversion H; subst; auto. Qed.

Lemma imm_ctx_vis_push_inv (G : ctx) (y : var) (vk : varkind) (T : typ) (a : var) :
  @ctx_vis (G § y / vk ~ T) a -> a = y \/ (a <> y /\ @ctx_vis G a).
Proof. intros H. inversion H; subst; auto. Qed.

Lemma imm_ctx_binds_hide_inv (G : ctx) (a : var) (U : typ) :
  @ctx_binds a U (ctx_hide G) -> @ctx_binds a U G.
Proof. intros H. inversion H; subst; auto. Qed.

Lemma imm_rb_push (z x : var) (G G' : ctx) (y : var) (vk : varkind) (T : typ) :
  imm_rb z x G G' -> y <> z -> y <> x ->
  imm_rb z x (G § y / vk ~ T) (G' § y / vk ~ (subst_var z x T)).
Proof.
  intros Hm Hne Hne2 a U Hb. unfold imm_rb in Hm.
  destruct (@imm_ctx_binds_push_inv G y vk T a U Hb) as [[Ea EU] | [Hneq Hb0]].
  - subst a U. rewrite (@imm_subst_var_neq z x y Hne). apply ctx_binds_e.
  - assert (Hs : subst_var z x a <> y).
    { intro E. destruct (classic (a = z)) as [Ea | Ea].
      - subst a. rewrite imm_subst_var_self in E. apply Hne2. symmetry. exact E.
      - rewrite (@imm_subst_var_neq z x a Ea) in E. exact (Hneq E). }
    eapply ctx_binds_n; [ exact Hs | apply Hm; exact Hb0 ].
Qed.

Lemma imm_rv_push (z x : var) (G G' : ctx) (y : var) (vk : varkind) (T : typ) :
  imm_rv z x G G' -> y <> z -> y <> x ->
  imm_rv z x (G § y / vk ~ T) (G' § y / vk ~ (subst_var z x T)).
Proof.
  intros Hm Hne Hne2 a Hv. unfold imm_rv in Hm.
  destruct (@imm_ctx_vis_push_inv G y vk T a Hv) as [Ea | [Hneq Hv0]].
  - subst a. rewrite (@imm_subst_var_neq z x y Hne). apply ctx_vis_e.
  - assert (Hs : subst_var z x a <> y).
    { intro E. destruct (classic (a = z)) as [Ea | Ea].
      - subst a. rewrite imm_subst_var_self in E. apply Hne2. symmetry. exact E.
      - rewrite (@imm_subst_var_neq z x a Ea) in E. exact (Hneq E). }
    eapply ctx_vis_n; [ exact Hs | apply Hm; exact Hv0 ].
Qed.

Lemma imm_rb_hide (z x : var) (G G' : ctx) :
  imm_rb z x G G' -> imm_rb z x (ctx_hide G) (ctx_hide G').
Proof.
  intros Hm a U Hb. unfold imm_rb in Hm.
  apply ctx_binds_hide. apply Hm. eapply imm_ctx_binds_hide_inv. exact Hb.
Qed.

Lemma imm_rv_hide (z x : var) (G G' : ctx) :
  imm_rv z x G G' -> imm_rv z x (ctx_hide G) (ctx_hide G').
Proof. intros Hm a Hv. unfold imm_rv in Hm. inversion Hv. Qed.

(* Push equations for a single substitution. *)
Lemma imm_sub_typ_top z x : subst_var z x typ_top = typ_top.
Proof. cbn. reflexivity. Qed.
Lemma imm_sub_typ_bot z x : subst_var z x typ_bot = typ_bot.
Proof. cbn. reflexivity. Qed.
Lemma imm_sub_typ_nocap z x : subst_var z x typ_nocap = typ_nocap.
Proof. cbn. reflexivity. Qed.
Lemma imm_sub_typ_and z x a b :
  subst_var z x (typ_and a b) = typ_and (subst_var z x a) (subst_var z x b).
Proof. cbn. reflexivity. Qed.
Lemma imm_sub_typ_or z x a b :
  subst_var z x (typ_or a b) = typ_or (subst_var z x a) (subst_var z x b).
Proof. cbn. reflexivity. Qed.
Lemma imm_sub_typ_fun z x a b :
  subst_var z x (typ_fun a b) = typ_fun (subst_var z x a) (subst_var z x b).
Proof. cbn. reflexivity. Qed.
Lemma imm_sub_typ_bnd z x a :
  subst_var z x (typ_bnd a) = typ_bnd (subst_var z x a).
Proof. cbn. reflexivity. Qed.
Lemma imm_sub_typ_rcd z x D :
  subst_var z x (typ_rcd D) = typ_rcd (subst_var z x D).
Proof. cbn. reflexivity. Qed.
Lemma imm_sub_typ_sel z x a L b :
  subst_var z x (typ_sel a L b) =
  typ_sel (subst_var z x a) L (subst_var z x b).
Proof. cbn. reflexivity. Qed.
Lemma imm_sub_dec_typ z x A X Y :
  subst_var z x (dec_typ A X Y) =
  dec_typ A (subst_var z x X) (subst_var z x Y).
Proof. cbn. reflexivity. Qed.
Lemma imm_sub_dec_fld z x a X Y :
  subst_var z x (dec_fld a X Y) =
  dec_fld a (subst_var z x X) (subst_var z x Y).
Proof. cbn. reflexivity. Qed.
Lemma imm_sub_dec_met z x m X Y Z :
  subst_var z x (dec_met m X Y Z) =
  dec_met m (subst_var z x X) (subst_var z x Y) (subst_var z x Z).
Proof. cbn. reflexivity. Qed.

(* A bound variable is never produced by free-variable substitution. *)
Lemma imm_avar_b_neq_subst (n : nat) (z x : var) (a : avar) :
  avar_b n <> a -> avar_b n <> subst_var z x a.
Proof.
  intros H E. apply H.
  destruct a; cbn in E.
  - exact E.
  - discriminate E.
Qed.

(* Bound-variable independence is preserved by free-variable substitution. *)
Lemma imm_typ_indep_b_subst (z x : var) :
  forall (n : nat) (T : typ),
    typ_indep (avar_b n) T -> typ_indep (avar_b n) (subst_var z x T).
Proof.
  intros n T H.
  assert (Hgen : forall (v : avar) (T0 : typ), typ_indep v T0 ->
                 forall n0, v = avar_b n0 ->
                   typ_indep (avar_b n0) (subst_var z x T0)).
  { intros v T0 H0. induction H0 as
      [ v0 T1 Hnu
      | v0 t1 t2 H1 IH1 H2 IH2
      | v0 t1 t2 H1 IH1 H2 IH2
      | v0 a t1 t2 H1 IH1 H2 IH2
      | v0 a t1 t2 H1 IH1 H2 IH2
      | n0 a t1 t2 H1 IH1 H2 IH2
      | v0 t1 t2 H1 IH1 H2 IH2
      | n0 t1 t2 H1 IH1 H2 IH2
      | v0 v1 v2 l0 Hne1 Hne2
      | v0 v1 v2 l0 Hne2
      | v0 t1 H1 IH1
      | n0 t1 H1 IH1
      | v0 t1 t2 t3 l0 H1 IH1 H2 IH2 H3 IH3
      | n0 t1 t2 t3 l0 H1 IH1 H2 IH2 H3 IH3 ].
    all: intros n1 Ev.
    - subst v0. inversion Hnu; subst T1;
        [ rewrite imm_sub_typ_top | rewrite imm_sub_typ_bot | rewrite imm_sub_typ_nocap ];
        apply typ_indep_nulary; constructor.
    - subst v0. rewrite imm_sub_typ_and. apply typ_indep_and;
        [ exact (IH1 n1 eq_refl) | exact (IH2 n1 eq_refl) ].
    - subst v0. rewrite imm_sub_typ_or. apply typ_indep_or;
        [ exact (IH1 n1 eq_refl) | exact (IH2 n1 eq_refl) ].
    - subst v0. rewrite imm_sub_typ_rcd, imm_sub_dec_fld. apply typ_indep_fld;
        [ exact (IH1 n1 eq_refl) | exact (IH2 n1 eq_refl) ].
    - discriminate Ev.
    - injection Ev as En. subst n0.
      rewrite imm_sub_typ_rcd, imm_sub_dec_typ. apply typ_indep_typ_b;
        [ exact (IH1 (S n1) eq_refl) | exact (IH2 (S n1) eq_refl) ].
    - discriminate Ev.
    - injection Ev as En. subst n0.
      rewrite imm_sub_typ_fun. apply typ_indep_fun_b;
        [ exact (IH1 n1 eq_refl) | exact (IH2 (S n1) eq_refl) ].
    - subst v0. rewrite imm_sub_typ_sel. apply typ_indep_sel;
        [ apply imm_avar_b_neq_subst; exact Hne1
        | apply imm_avar_b_neq_subst; exact Hne2 ].
    - subst v0. rewrite imm_sub_typ_sel. apply typ_indep_sel_normal.
      apply imm_avar_b_neq_subst. exact Hne2.
    - discriminate Ev.
    - injection Ev as En. subst n0.
      rewrite imm_sub_typ_bnd. apply typ_indep_bnd_b.
      exact (IH1 (S n1) eq_refl).
    - discriminate Ev.
    - injection Ev as En. subst n0.
      rewrite imm_sub_typ_rcd, imm_sub_dec_met. apply typ_indep_met_b;
        [ exact (IH1 (S n1) eq_refl)
        | exact (IH2 n1 eq_refl)
        | exact (IH3 (S (S n1)) eq_refl) ]. }
  exact (Hgen (avar_b n) T H n eq_refl).
Qed.


(* ---------- list-version relations and type-level substitution ---------- *)

Definition imm_rb_l (l : list (var * var)) (G G' : ctx) : Prop :=
  forall a U, @ctx_binds a U G ->
    @ctx_binds (imm_substl_var l a) (imm_substl_typ l U) G'.

Definition imm_rv_l (l : list (var * var)) (G G' : ctx) : Prop :=
  forall a, @ctx_vis G a -> @ctx_vis G' (imm_substl_var l a).

Lemma imm_substl_var_neq_fresh (l : list (var * var)) (y a : var) :
  (forall z x, List.In (z, x) l -> y <> z /\ y <> x) ->
  a <> y -> imm_substl_var l a <> y.
Proof.
  induction l as [|[z x] l' IH]; intros Hfresh Ha; cbn [imm_substl_var].
  - exact Ha.
  - assert (Htail : forall a0 b, List.In (a0, b) l' -> y <> a0 /\ y <> b).
    { intros a0 b Hin. apply Hfresh. right. exact Hin. }
    pose proof (IH Htail Ha) as Hv.
    destruct (classic (imm_substl_var l' a = z)) as [E | E].
    + rewrite E, imm_subst_var_self. intro Exy.
      exact ((proj2 (Hfresh z x (or_introl eq_refl))) (eq_sym Exy)).
    + rewrite (@imm_subst_var_neq z x (imm_substl_var l' a) E).
      exact Hv.
Qed.

Lemma imm_rb_l_push (l : list (var * var)) (G G' : ctx)
      (y : var) (vk : varkind) (T : typ) :
  imm_rb_l l G G' ->
  (forall z x, List.In (z, x) l -> y <> z /\ y <> x) ->
  imm_rb_l l (G § y / vk ~ T) (G' § y / vk ~ (imm_substl_typ l T)).
Proof.
  intros Hm Hfresh a U Hb. unfold imm_rb_l in Hm.
  destruct (@imm_ctx_binds_push_inv G y vk T a U Hb) as [[Ea EU] | [Hneq Hb0]].
  - subst a U.
    rewrite (@imm_substl_var_notin_src l y (fun z x Hin => proj1 (Hfresh z x Hin))).
    apply ctx_binds_e.
  - assert (Hs : imm_substl_var l a <> y)
      by (apply imm_substl_var_neq_fresh; [ exact Hfresh | exact Hneq ]).
    eapply ctx_binds_n; [ exact Hs | apply Hm; exact Hb0 ].
Qed.

Lemma imm_rv_l_push (l : list (var * var)) (G G' : ctx)
      (y : var) (vk : varkind) (T : typ) :
  imm_rv_l l G G' ->
  (forall z x, List.In (z, x) l -> y <> z /\ y <> x) ->
  imm_rv_l l (G § y / vk ~ T) (G' § y / vk ~ (imm_substl_typ l T)).
Proof.
  intros Hm Hfresh a Hv. unfold imm_rv_l in Hm.
  destruct (@imm_ctx_vis_push_inv G y vk T a Hv) as [Ea | [Hneq Hv0]].
  - subst a.
    rewrite (@imm_substl_var_notin_src l y (fun z x Hin => proj1 (Hfresh z x Hin))).
    apply ctx_vis_e.
  - assert (Hs : imm_substl_var l a <> y)
      by (apply imm_substl_var_neq_fresh; [ exact Hfresh | exact Hneq ]).
    eapply ctx_vis_n; [ exact Hs | apply Hm; exact Hv0 ].
Qed.

Lemma imm_rb_l_hide (l : list (var * var)) (G G' : ctx) :
  imm_rb_l l G G' -> imm_rb_l l (ctx_hide G) (ctx_hide G').
Proof.
  intros Hm a U Hb. unfold imm_rb_l in Hm.
  apply ctx_binds_hide. apply Hm. eapply imm_ctx_binds_hide_inv. exact Hb.
Qed.

Lemma imm_rv_l_hide (l : list (var * var)) (G G' : ctx) :
  imm_rv_l l G G' -> imm_rv_l l (ctx_hide G) (ctx_hide G').
Proof. intros Hm a Hv. unfold imm_rv_l in Hm. inversion Hv. Qed.

Lemma imm_typ_indep_b_substl (l : list (var * var)) (n : nat) (T : typ) :
  typ_indep (avar_b n) T -> typ_indep (avar_b n) (imm_substl_typ l T).
Proof.
  intros H. induction l as [|[z x] l' IH]; cbn [imm_substl_typ]; [ exact H | ].
  apply imm_typ_indep_b_subst. exact IH.
Qed.


(* ---------- inverse bound-independence under substitution ---------- *)

Lemma imm_ctx_binds_fv (G : ctx) (a : var) (U : typ) :
  @ctx_binds a U G -> forall z, z \in fv U -> z \in ctx_fv G.
Proof.
  intros Hb. induction Hb as [v0 vk t G0 | v0 v2 vk t t2 G0 Hneq Hb0 IH
                            | v0 t G0 Hb0 IH]; intros z Hz.
  - cbn [ctx_fv ctx_collect_values]. rewrite in_union. left. exact Hz.
  - cbn [ctx_fv ctx_collect_values]. rewrite in_union. right. apply IH. exact Hz.
  - cbn [ctx_fv ctx_collect_values]. apply IH. exact Hz.
Qed.

Lemma imm_ctx_vis_dom (G : ctx) (a : var) :
  @ctx_vis G a -> a \in ctx_dom G.
Proof.
  intros Hv. induction Hv as [v0 vk t G0 | v0 v2 vk t G0 Hneq Hv0 IH].
  - cbn [ctx_dom]. rewrite in_union. left. apply in_singleton_self.
  - cbn [ctx_dom]. rewrite in_union. right. exact IH.
Qed.

Lemma imm_avar_b_neq_subst_inv (n : nat) (z x : var) (a : avar) :
  avar_b n <> subst_var z x a -> avar_b n <> a.
Proof.
  intros H E. apply H. destruct a; cbn.
  - exact E.
  - discriminate E.
Qed.

Definition imm_dec_indep (z x : var) (D : dec) : Prop :=
  match D with
  | dec_typ A X Y =>
      (forall n, typ_indep (avar_b (S n)) (subst_var z x X) -> typ_indep (avar_b (S n)) X) /\
      (forall n, typ_indep (avar_b (S n)) (subst_var z x Y) -> typ_indep (avar_b (S n)) Y)
  | dec_fld a X Y =>
      (forall n, typ_indep (avar_b n) (subst_var z x X) -> typ_indep (avar_b n) X) /\
      (forall n, typ_indep (avar_b n) (subst_var z x Y) -> typ_indep (avar_b n) Y)
  | dec_met m TC TZ TR =>
      (forall n, typ_indep (avar_b (S n)) (subst_var z x TC) -> typ_indep (avar_b (S n)) TC) /\
      (forall n, typ_indep (avar_b n) (subst_var z x TZ) -> typ_indep (avar_b n) TZ) /\
      (forall n, typ_indep (avar_b (S (S n))) (subst_var z x TR) -> typ_indep (avar_b (S (S n))) TR)
  end.

Ltac imm_kill_nulary :=
  try (match goal with Hnu : typ_nulary _ |- _ => inversion Hnu end).

Lemma imm_typ_indep_b_subst_inv (z x : var) :
  (forall (T : typ) (n : nat),
      typ_indep (avar_b n) (subst_var z x T) -> typ_indep (avar_b n) T) /\
  (forall (D : dec), imm_dec_indep z x D).
Proof.
  apply (typ_mutind
    (fun T => forall n, typ_indep (avar_b n) (subst_var z x T) -> typ_indep (avar_b n) T)
    (fun D => imm_dec_indep z x D)).
  - intros n _. apply typ_indep_nulary. constructor.
  - intros n _. apply typ_indep_nulary. constructor.
  - intros d IHD n H.
    destruct d as [A X Y | a X Y | m TC TZ TR].
    + cbn [imm_dec_indep] in IHD.
      change (typ_indep (avar_b n)
                (typ_rcd (dec_typ A (subst_var z x X) (subst_var z x Y)))) in H.
      remember (subst_var z x X) as X' eqn:EX.
      remember (subst_var z x Y) as Y' eqn:EY.
      rewrite EX, EY in H.
      inversion H; subst. imm_kill_nulary.
      apply typ_indep_typ_b.
      * apply (proj1 IHD n). assumption.
      * apply (proj2 IHD n). assumption.
    + cbn [imm_dec_indep] in IHD.
      change (typ_indep (avar_b n)
                (typ_rcd (dec_fld a (subst_var z x X) (subst_var z x Y)))) in H.
      remember (subst_var z x X) as X' eqn:EX.
      remember (subst_var z x Y) as Y' eqn:EY.
      rewrite EX, EY in H.
      inversion H; subst. imm_kill_nulary.
      apply typ_indep_fld.
      * apply (proj1 IHD n). assumption.
      * apply (proj2 IHD n). assumption.
    + cbn [imm_dec_indep] in IHD.
      change (typ_indep (avar_b n)
                (typ_rcd (dec_met m (subst_var z x TC) (subst_var z x TZ) (subst_var z x TR)))) in H.
      remember (subst_var z x TC) as TC' eqn:EC.
      remember (subst_var z x TZ) as TZ' eqn:EZ.
      remember (subst_var z x TR) as TR' eqn:ER.
      rewrite EC, EZ, ER in H.
      inversion H; subst. imm_kill_nulary.
      apply typ_indep_met_b.
      * apply (proj1 IHD n). assumption.
      * apply (proj1 (proj2 IHD) n). assumption.
      * apply (proj2 (proj2 IHD) n). assumption.
  - intros t IHt t0 IHt0 n H.
    change (typ_indep (avar_b n) (typ_and (subst_var z x t) (subst_var z x t0))) in H.
    remember (subst_var z x t) as t' eqn:Et.
    remember (subst_var z x t0) as t0' eqn:Et0.
    rewrite Et, Et0 in H.
    inversion H; subst. imm_kill_nulary.
    apply typ_indep_and.
    + apply (IHt n). assumption.
    + apply (IHt0 n). assumption.
  - intros t IHt t0 IHt0 n H.
    change (typ_indep (avar_b n) (typ_or (subst_var z x t) (subst_var z x t0))) in H.
    remember (subst_var z x t) as t' eqn:Et.
    remember (subst_var z x t0) as t0' eqn:Et0.
    rewrite Et, Et0 in H.
    inversion H; subst. imm_kill_nulary.
    apply typ_indep_or.
    + apply (IHt n). assumption.
    + apply (IHt0 n). assumption.
  - intros a L a0 n H.
    change (typ_indep (avar_b n)
              (typ_sel (subst_var z x a) L (subst_var z x a0))) in H.
    remember (subst_var z x a) as a' eqn:Ea.
    remember (subst_var z x a0) as a0' eqn:Ea0.
    rewrite Ea, Ea0 in H.
    inversion H; subst. imm_kill_nulary.
    + apply typ_indep_sel.
      * apply (@imm_avar_b_neq_subst_inv n z x a). assumption.
      * apply (@imm_avar_b_neq_subst_inv n z x a0). assumption.
    + apply typ_indep_sel_normal.
      apply (@imm_avar_b_neq_subst_inv n z x a0). assumption.
  - intros t IHt n H.
    change (typ_indep (avar_b n) (typ_bnd (subst_var z x t))) in H.
    remember (subst_var z x t) as t' eqn:Et.
    rewrite Et in H.
    inversion H; subst. imm_kill_nulary.
    apply typ_indep_bnd_b. apply (IHt (S n)). assumption.
  - intros t IHt t0 IHt0 n H.
    change (typ_indep (avar_b n) (typ_fun (subst_var z x t) (subst_var z x t0))) in H.
    remember (subst_var z x t) as t' eqn:Et.
    remember (subst_var z x t0) as t0' eqn:Et0.
    rewrite Et, Et0 in H.
    inversion H; subst. imm_kill_nulary.
    apply typ_indep_fun_b.
    + apply (IHt n). assumption.
    + apply (IHt0 (S n)). assumption.
  - intros n _. apply typ_indep_nulary. constructor.
  - intros A X IHS Y IHY. cbn [imm_dec_indep]. split;
      intros n0 H; [ apply IHS | apply IHY ]; exact H.
  - intros a X IHS Y IHY. cbn [imm_dec_indep]. split;
      intros n0 H; [ apply IHS | apply IHY ]; exact H.
  - intros m TC IHC TZ IHZ TR IHR. cbn [imm_dec_indep]. split; [ | split ];
      intros n0 H; [ apply IHC | apply IHZ | apply IHR ]; exact H.
Qed.

Lemma imm_typ_indep_b_substl_inv (l : list (var * var)) (n : nat) (T : typ) :
  typ_indep (avar_b n) (imm_substl_typ l T) -> typ_indep (avar_b n) T.
Proof.
  intros H. induction l as [|[z x] l' IH]; cbn [imm_substl_typ] in *; [ exact H | ].
  apply IH. apply (proj1 (imm_typ_indep_b_subst_inv z x)). exact H.
Qed.


(* ---------- substitution for the type-level judgments ---------- *)

Lemma imm_rb_l_ext (l : list (var * var)) (G G' : ctx) (w y : var) :
  imm_rb_l l G G' ->
  (forall a b, List.In (a, b) l -> w <> a /\ w <> b) ->
  w \notin ctx_dom G -> w \notin ctx_fv G ->
  imm_rb_l ((w, y) :: l) G G'.
Proof.
  intros Hm Hfresh Hdom Hfv a U Hb. unfold imm_rb_l in Hm.
  assert (Ha : a <> w).
  { intro E. subst a. apply Hdom. eapply imm_ctx_binds_dom. exact Hb. }
  assert (Hsl : imm_substl_var l a <> w)
    by (apply imm_substl_var_neq_fresh; [ exact Hfresh | exact Ha ]).
  assert (HfvU : w \notin fv U).
  { intro E. apply Hfv. eapply imm_ctx_binds_fv; eassumption. }
  assert (Hfvs : w \notin fv (imm_substl_typ l U))
    by (apply imm_fv_substl_notin; [ exact HfvU | exact Hfresh ]).
  cbn [imm_substl_var imm_substl_typ].
  rewrite (@imm_subst_var_neq w y (imm_substl_var l a) Hsl).
  rewrite (proj1 (imm_subst_fresh_typ_dec_proj w y) (imm_substl_typ l U) Hfvs).
  apply Hm. exact Hb.
Qed.

Lemma imm_rv_l_ext (l : list (var * var)) (G G' : ctx) (w y : var) :
  imm_rv_l l G G' ->
  (forall a b, List.In (a, b) l -> w <> a /\ w <> b) ->
  w \notin ctx_dom G ->
  imm_rv_l ((w, y) :: l) G G'.
Proof.
  intros Hm Hfresh Hdom a Hv. unfold imm_rv_l in Hm.
  assert (Ha : a <> w).
  { intro E. subst a. apply Hdom. apply imm_ctx_vis_dom. exact Hv. }
  assert (Hsl : imm_substl_var l a <> w)
    by (apply imm_substl_var_neq_fresh; [ exact Hfresh | exact Ha ]).
  cbn [imm_substl_var].
  rewrite (@imm_subst_var_neq w y (imm_substl_var l a) Hsl).
  apply Hm. exact Hv.
Qed.

Lemma imm_substl_var_ext_head (l : list (var * var)) (w y : var) :
  (forall a b, List.In (a, b) l -> w <> a) ->
  imm_substl_var ((w, y) :: l) w = y.
Proof.
  intros H. cbn [imm_substl_var].
  rewrite (@imm_substl_var_notin_src l w H).
  apply imm_subst_var_self.
Qed.

Lemma imm_substl_typ_ext_fresh (l : list (var * var)) (w y : var) (T : typ) :
  w \notin fv T ->
  (forall a b, List.In (a, b) l -> w <> a /\ w <> b) ->
  imm_substl_typ ((w, y) :: l) T = imm_substl_typ l T.
Proof.
  intros HT Hfresh. cbn [imm_substl_typ].
  apply (proj1 (imm_subst_fresh_typ_dec_proj w y)).
  apply imm_fv_substl_notin; [ exact HT | exact Hfresh ].
Qed.

(* Transfer of a universally-opened premise (as in dec_typ / subtyp_typ). *)
Ltac imm_open_subst_prem IH A B e l G G' Rb Rv Hfix :=
  intros x;
  destruct (imm_pick_fresh (dom e \u fv_env e \u imm_pairs_fv l \u ctx_dom G
                             \u ctx_fv G \u fv A \u fv B \u \{x})) as [w Hw];
  apply notin_union in Hw; destruct Hw as [Hwd Hw];
  apply notin_union in Hw; destruct Hw as [Hwf Hw];
  apply notin_union in Hw; destruct Hw as [Hwp Hw];
  apply notin_union in Hw; destruct Hw as [HwdG Hw];
  apply notin_union in Hw; destruct Hw as [HwfG Hw];
  apply notin_union in Hw; destruct Hw as [HwA Hw];
  apply notin_union in Hw; destruct Hw as [HwB Hwx];
  apply notin_singleton in Hwx;
  let Hlw := fresh "Hlw" in
  assert (Hlw : forall a b, List.In (a, b) l -> w <> a /\ w <> b)
    by (intros a b Hin; eapply imm_pairs_fv_notin; eassumption);
  let Hfix' := fresh "Hfix'" in
  assert (Hfix' : imm_hfix e (cons (w, x) l));
  [ intros a b Hin; destruct Hin as [E | Hin];
    [ injection E as <- <-; split; assumption
    | exact (Hfix a b Hin) ]
  | ];
  let Rb' := fresh "Rb'" in
  assert (Rb' : imm_rb_l (cons (w, x) l) G G')
    by (apply (@imm_rb_l_ext l G G' w x Rb Hlw HwdG HwfG));
  let Rv' := fresh "Rv'" in
  assert (Rv' : imm_rv_l (cons (w, x) l) G G')
    by (apply (@imm_rv_l_ext l G G' w x Rv Hlw HwdG));
  let Hr := fresh "Hr" in
  pose proof (IH w (cons (w, x) l) G' Hfix' Rb' Rv') as Hr;
  rewrite (@imm_substl_typ_open (cons (w, x) l) 0 w A) in Hr;
  rewrite (@imm_substl_typ_open (cons (w, x) l) 0 w B) in Hr;
  rewrite (@imm_substl_var_ext_head l w x (fun a b Hin => proj1 (Hlw a b Hin))) in Hr;
  rewrite (@imm_substl_typ_ext_fresh l w x A HwA Hlw) in Hr;
  rewrite (@imm_substl_typ_ext_fresh l w x B HwB Hlw) in Hr;
  exact Hr.

Lemma imm_ts_substl :
  (forall (G : ctx) (Go : objctx) (e : renv) (v : var) (T : typ),
      @ty_var typing_mode G Go e v T ->
      forall (l : list (var * var)) (G' : ctx),
        imm_hfix e l -> imm_rb_l l G G' -> imm_rv_l l G G' ->
        @ty_var typing_mode G' Go e (imm_substl_var l v) (imm_substl_typ l T)) /\
  (forall (G : ctx) (Go : objctx) (e : renv) (T U : typ),
      @subtyp typing_mode G Go e T U ->
      forall l G', imm_hfix e l -> imm_rb_l l G G' -> imm_rv_l l G G' ->
        @subtyp typing_mode G' Go e (imm_substl_typ l T) (imm_substl_typ l U)) /\
  (forall (G : ctx) (Go : objctx) (e : renv) (T U : typ),
      @ty_incap typing_mode G Go e T U ->
      forall l G', imm_hfix e l -> imm_rb_l l G G' -> imm_rv_l l G G' ->
        @ty_incap typing_mode G' Go e (imm_substl_typ l T) (imm_substl_typ l U)).
Proof.
  apply (@ts_mutind typing_mode
    (fun G Go e v T d => forall l G',
        imm_hfix e l -> imm_rb_l l G G' -> imm_rv_l l G G' ->
        @ty_var typing_mode G' Go e (imm_substl_var l v) (imm_substl_typ l T))
    (fun G Go e T U d => forall l G',
        imm_hfix e l -> imm_rb_l l G G' -> imm_rv_l l G G' ->
        @subtyp typing_mode G' Go e (imm_substl_typ l T) (imm_substl_typ l U))
    (fun G Go e T U d => forall l G',
        imm_hfix e l -> imm_rb_l l G G' -> imm_rv_l l G G' ->
        @ty_incap typing_mode G' Go e (imm_substl_typ l T) (imm_substl_typ l U))).
  - intros G e x T Hcb l G' Hfix Rb Rv. unfold imm_rb_l in Rb.
    apply ty_var_var. apply Rb. exact Hcb.
  - intros G e x T o IH ti o0 IHinc l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_bnd l T).
    apply ty_rec_intro with (T := imm_substl_typ l T).
    + pose proof (IH l G' Hfix Rb Rv) as Hr.
      rewrite (@imm_substl_typ_open l 0 x T) in Hr. exact Hr.
    + apply imm_typ_indep_b_substl. exact ti.
    + intro Ha. pose proof (IHinc Ha l G' Hfix Rb Rv) as Hr.
      rewrite (@imm_substl_typ_open l 0 x T) in Hr. exact Hr.
  - intros G e x T o IH ti l G' Hfix Rb Rv.
    pose proof (IH l G' Hfix Rb Rv) as Hr.
    rewrite (@imm_substl_typ_bnd l T) in Hr.
    rewrite (@imm_substl_typ_open l 0 x T).
    eapply ty_rec_elim; [ exact Hr | apply imm_typ_indep_b_substl; exact ti ].
  - intros G e x T U o1 IH1 o2 IH2 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_and l T U).
    apply ty_var_and;
      [ exact (IH1 l G' Hfix Rb Rv) | exact (IH2 l G' Hfix Rb Rv) ].
  - intros G e x T U o IH s IHs l G' Hfix Rb Rv.
    eapply ty_var_sub;
      [ exact (IH l G' Hfix Rb Rv) | exact (IHs l G' Hfix Rb Rv) ].
  - intros G e x T Hm o IH l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_rcd l (dec_typ (typ_label_refcap typ_refcap_mutability) typ_bot typ_top)).
    rewrite (@imm_substl_dec_typ l (typ_label_refcap typ_refcap_mutability) typ_bot typ_top).
    rewrite (@imm_substl_typ_bot l), (@imm_substl_typ_top l).
    apply ty_var_mut_top with (T := imm_substl_typ l T); [ exact Hm | exact (IH l G' Hfix Rb Rv) ].
  - intros G e T l G' Hfix Rb Rv. rewrite (@imm_substl_typ_top l). apply subtyp_top.
  - intros G e T l G' Hfix Rb Rv. rewrite (@imm_substl_typ_bot l). apply subtyp_bot.
  - intros G e T l G' Hfix Rb Rv. apply subtyp_refl.
  - intros G e S T U s IH s0 IH0 l G' Hfix Rb Rv.
    eapply subtyp_trans;
      [ exact (IH l G' Hfix Rb Rv) | exact (IH0 l G' Hfix Rb Rv) ].
  - intros G e T U l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_and l T U). apply subtyp_and11.
  - intros G e T U l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_and l T U). apply subtyp_and12.
  - intros G e S T U s IH s0 IH0 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_and l T U).
    eapply subtyp_and2;
      [ exact (IH l G' Hfix Rb Rv) | exact (IH0 l G' Hfix Rb Rv) ].
  - intros G e T U l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_or l T U). apply subtyp_or11.
  - intros G e T U l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_or l T U). apply subtyp_or12.
  - intros G e S T U s IH s0 IH0 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_or l S U).
    eapply subtyp_or2;
      [ exact (IH l G' Hfix Rb Rv) | exact (IH0 l G' Hfix Rb Rv) ].
  - intros G e a T1 T2 U1 U2 s IH s0 IH0 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_rcd l (dec_fld a T2 U1)),
            (@imm_substl_typ_rcd l (dec_fld a T1 U2)).
    rewrite (@imm_substl_dec_fld l a T2 U1), (@imm_substl_dec_fld l a T1 U2).
    eapply subtyp_fld;
      [ exact (IH l G' Hfix Rb Rv) | exact (IH0 l G' Hfix Rb Rv) ].
  - intros G e A S1 T1 S2 T2 s IH s0 IH0 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_rcd l (dec_typ A S1 T1)),
            (@imm_substl_typ_rcd l (dec_typ A S2 T2)).
    rewrite (@imm_substl_dec_typ l A S1 T1), (@imm_substl_dec_typ l A S2 T2).
    eapply subtyp_typ.
    + imm_open_subst_prem IH S2 S1 e l G G' Rb Rv Hfix.
    + imm_open_subst_prem IH0 T1 T2 e l G G' Rb Rv Hfix.
  - intros G e x A y S T o IH l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_open l 0 y S).
    rewrite (@imm_substl_typ_sel l (avar_f x) A (avar_f y)).
    rewrite (@imm_substl_avar_f l x), (@imm_substl_avar_f l y).
    eapply subtyp_sel2.
    pose proof (IH l G' Hfix Rb Rv) as Hr.
    rewrite (@imm_substl_typ_rcd l (dec_typ A S T)), (@imm_substl_dec_typ l A S T) in Hr.
    exact Hr.
  - intros G e x A y S T o IH l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_sel l (avar_f x) A (avar_f y)).
    rewrite (@imm_substl_avar_f l x), (@imm_substl_avar_f l y).
    rewrite (@imm_substl_typ_open l 0 y T).
    eapply subtyp_sel1.
    pose proof (IH l G' Hfix Rb Rv) as Hr.
    rewrite (@imm_substl_typ_rcd l (dec_typ A S T)), (@imm_substl_dec_typ l A S T) in Hr.
    exact Hr.
  - intros L G e S1 T1 S2 T2 Hfun s IH s0 IH0 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_fun l S1 T1), (@imm_substl_typ_fun l S2 T2).
    eapply subtyp_fun with (L := L \u imm_pairs_fv l).
    + exact Hfun.
    + exact (IH l G' Hfix Rb Rv).
    + intros x Hx.
      apply notin_union in Hx; destruct Hx as [HxL Hxp].
      assert (Hlw : forall a b, List.In (a, b) l -> x <> a /\ x <> b)
        by (intros a b Hin; eapply imm_pairs_fv_notin; eassumption).
      assert (Rb' : imm_rb_l l (G § x / v_par ~ S2)
                              (G' § x / v_par ~ imm_substl_typ l S2))
        by (apply (@imm_rb_l_push l G G' x v_par S2 Rb Hlw)).
      assert (Rv' : imm_rv_l l (G § x / v_par ~ S2)
                              (G' § x / v_par ~ imm_substl_typ l S2))
        by (apply (@imm_rv_l_push l G G' x v_par S2 Rv Hlw)).
      pose proof (IH0 x HxL l (G' § x / v_par ~ imm_substl_typ l S2) Hfix Rb' Rv') as Hr.
      rewrite (@imm_substl_typ_open l 0 x T1) in Hr.
      rewrite (@imm_substl_typ_open l 0 x T2) in Hr.
      rewrite (@imm_substl_var_notin_src l x (fun a b Hin => proj1 (Hlw a b Hin))) in Hr.
      exact Hr.
  - intros L G e m TC1 TZ1 TR1 TC2 TZ2 TR2 s IH s0 IH0 t s1 IH2 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_rcd l (dec_met m TC1 TZ1 TR1)),
            (@imm_substl_typ_rcd l (dec_met m TC2 TZ2 TR2)).
    rewrite (@imm_substl_dec_met l m TC1 TZ1 TR1), (@imm_substl_dec_met l m TC2 TZ2 TR2).
    eapply subtyp_met with (L := L \u imm_pairs_fv l).
    + exact (IH l G' Hfix Rb Rv).
    + intros x Hx.
      apply notin_union in Hx; destruct Hx as [HxL Hxp].
      assert (Hlw : forall a b, List.In (a, b) l -> x <> a /\ x <> b)
        by (intros a b Hin; eapply imm_pairs_fv_notin; eassumption).
      assert (Rb' : imm_rb_l l (G § x / v_par ~ TZ2)
                              (G' § x / v_par ~ imm_substl_typ l TZ2))
        by (apply (@imm_rb_l_push l G G' x v_par TZ2 Rb Hlw)).
      assert (Rv' : imm_rv_l l (G § x / v_par ~ TZ2)
                              (G' § x / v_par ~ imm_substl_typ l TZ2))
        by (apply (@imm_rv_l_push l G G' x v_par TZ2 Rv Hlw)).
      pose proof (IH0 x HxL l (G' § x / v_par ~ imm_substl_typ l TZ2) Hfix Rb' Rv') as Hr.
      rewrite (@imm_substl_typ_open l 0 x TC2) in Hr.
      rewrite (@imm_substl_typ_open l 0 x TC1) in Hr.
      rewrite (@imm_substl_var_notin_src l x (fun a b Hin => proj1 (Hlw a b Hin))) in Hr.
      exact Hr.
    + intros Hsef H2. apply imm_typ_indep_b_substl.
      apply (t Hsef). apply (@imm_typ_indep_b_substl_inv l 0 TC2). exact H2.
    + intros x Hx y Hyx Hy.
      apply notin_union in Hx; destruct Hx as [HxL Hxp].
      apply notin_union in Hy; destruct Hy as [HyL Hyp].
      assert (Hlwx : forall a b, List.In (a, b) l -> x <> a /\ x <> b)
        by (intros a b Hin; eapply imm_pairs_fv_notin; eassumption).
      assert (Hlwy : forall a b, List.In (a, b) l -> y <> a /\ y <> b)
        by (intros a b Hin; eapply imm_pairs_fv_notin; eassumption).
      set (G1 := G § x / v_par ~ TZ2).
      set (G1' := G' § x / v_par ~ imm_substl_typ l TZ2).
      assert (Rb1 : imm_rb_l l G1 G1')
        by (apply (@imm_rb_l_push l G G' x v_par TZ2 Rb Hlwx)).
      assert (Rv1 : imm_rv_l l G1 G1')
        by (apply (@imm_rv_l_push l G G' x v_par TZ2 Rv Hlwx)).
      assert (Rb2 : imm_rb_l l (G1 § y / v_recv ~ (open_rec 0 x TC2))
                                (G1' § y / v_recv ~ imm_substl_typ l (open_rec 0 x TC2)))
        by (apply (@imm_rb_l_push l G1 G1' y v_recv (open_rec 0 x TC2) Rb1 Hlwy)).
      assert (Rv2 : imm_rv_l l (G1 § y / v_recv ~ (open_rec 0 x TC2))
                                (G1' § y / v_recv ~ imm_substl_typ l (open_rec 0 x TC2)))
        by (apply (@imm_rv_l_push l G1 G1' y v_recv (open_rec 0 x TC2) Rv1 Hlwy)).
      rewrite (@imm_substl_typ_open l 0 x TC2) in Rb2.
      rewrite (@imm_substl_typ_open l 0 x TC2) in Rv2.
      rewrite (@imm_substl_var_notin_src l x (fun a b Hin => proj1 (Hlwx a b Hin))) in Rb2.
      rewrite (@imm_substl_var_notin_src l x (fun a b Hin => proj1 (Hlwx a b Hin))) in Rv2.
      pose proof (IH2 x HxL y Hyx HyL l (G1' § y / v_recv ~ (open_rec 0 x (imm_substl_typ l TC2))) Hfix Rb2 Rv2) as Hr.
      change (subtyp typing_mode (G1' § y / v_recv ~ (open_rec 0 x (imm_substl_typ l TC2))) objctx_empty e
                       (imm_substl_typ l (open_rec 0 x (open_rec 1 y TR1)))
                       (imm_substl_typ l (open_rec 0 x (open_rec 1 y TR2)))) in Hr.
      rewrite (@imm_substl_typ_open l 0 x (open_rec 1 y TR1)) in Hr.
      rewrite (@imm_substl_typ_open l 0 x (open_rec 1 y TR2)) in Hr.
      rewrite (@imm_substl_typ_open l 1 y TR1) in Hr.
      rewrite (@imm_substl_typ_open l 1 y TR2) in Hr.
      rewrite (@imm_substl_var_notin_src l x (fun a b Hin => proj1 (Hlwx a b Hin))) in Hr.
      rewrite (@imm_substl_var_notin_src l y (fun a b Hin => proj1 (Hlwy a b Hin))) in Hr.
      exact Hr.
  - intros G e T1 T2 t l G' Hfix Rb Rv.
    apply subtyp_tyq. exact (@imm_tyq_typ_substl e T1 T2 t l Hfix).
  - intros G e A S1 T1 S2 T2 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_and l (typ_rcd (dec_typ A S1 T1)) (typ_rcd (dec_typ A S2 T2))).
    rewrite (@imm_substl_typ_rcd l (dec_typ A S1 T1)).
    rewrite (@imm_substl_typ_rcd l (dec_typ A S2 T2)).
    rewrite (@imm_substl_dec_typ l A S1 T1), (@imm_substl_dec_typ l A S2 T2).
    rewrite (@imm_substl_typ_rcd l (dec_typ A (typ_or S1 S2) (typ_and T1 T2))).
    rewrite (@imm_substl_dec_typ l A (typ_or S1 S2) (typ_and T1 T2)).
    rewrite (@imm_substl_typ_or l S1 S2), (@imm_substl_typ_and l T1 T2).
    apply subtyp_typ_and.
  - intros G e T1 T2 T3 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_and l T1 (typ_or T2 T3)).
    rewrite (@imm_substl_typ_or l T2 T3).
    rewrite (@imm_substl_typ_or l (typ_and T1 T2) (typ_and T1 T3)).
    rewrite (@imm_substl_typ_and l T1 T2), (@imm_substl_typ_and l T1 T3).
    apply subtyp_dist.
  - intros G e T l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_nocap l), (@imm_substl_typ_bnd l T).
    apply subtyp_nocap_bnd.
  - intros G e A T1 T2 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_nocap l).
    rewrite (@imm_substl_typ_rcd l (dec_typ (typ_label_normal A) T1 T2)).
    rewrite (@imm_substl_dec_typ l (typ_label_normal A) T1 T2).
    apply subtyp_nocap_typ.
  - intros G e a T1 T2 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_nocap l).
    rewrite (@imm_substl_typ_rcd l (dec_fld a T1 T2)).
    rewrite (@imm_substl_dec_fld l a T1 T2).
    apply subtyp_nocap_fld.
  - intros G e a TC TZ TR l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_nocap l).
    rewrite (@imm_substl_typ_rcd l (dec_met a TC TZ TR)).
    rewrite (@imm_substl_dec_met l a TC TZ TR).
    apply subtyp_nocap_met.
  - intros G e TZ TR Hfun l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_nocap l), (@imm_substl_typ_fun l TZ TR).
    apply subtyp_nocap_fun. exact Hfun.
  - intros G e T1 T2 Htop l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_top l).
    rewrite (@imm_substl_typ_or l typ_nocap
               (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability) T1 T2))).
    rewrite (@imm_substl_typ_nocap l).
    rewrite (@imm_substl_typ_rcd l (dec_typ (typ_label_refcap typ_refcap_mutability) T1 T2)).
    rewrite (@imm_substl_dec_typ l (typ_label_refcap typ_refcap_mutability) T1 T2).
    apply subtyp_nocap_mut_top_boundless. exact Htop.
  - intros G e Htop l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_top l).
    rewrite (@imm_substl_typ_or l typ_nocap
               (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability) typ_bot typ_bot))).
    rewrite (@imm_substl_typ_nocap l).
    rewrite (@imm_substl_typ_rcd l (dec_typ (typ_label_refcap typ_refcap_mutability) typ_bot typ_bot)).
    rewrite (@imm_substl_dec_typ l (typ_label_refcap typ_refcap_mutability) typ_bot typ_bot).
    rewrite (@imm_substl_typ_bot l).
    apply subtyp_nocap_mut_top_complement. exact Htop.
  - intros G e Htop l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_and l typ_nocap
               (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability) typ_bot typ_bot))).
    rewrite (@imm_substl_typ_nocap l).
    rewrite (@imm_substl_typ_rcd l (dec_typ (typ_label_refcap typ_refcap_mutability) typ_bot typ_bot)).
    rewrite (@imm_substl_dec_typ l (typ_label_refcap typ_refcap_mutability) typ_bot typ_bot).
    rewrite (@imm_substl_typ_bot l).
    apply subtyp_nocap_mut_bot. exact Htop.
  - intros G e Htop l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_top l).
    rewrite (@imm_substl_typ_rcd l (dec_typ (typ_label_refcap typ_refcap_mutability) typ_bot typ_top)).
    rewrite (@imm_substl_dec_typ l (typ_label_refcap typ_refcap_mutability) typ_bot typ_top).
    rewrite (@imm_substl_typ_bot l), (@imm_substl_typ_top l).
    apply subtyp_mut_top. exact Htop.
  - intros G e l G' Hfix Rb Rv. rewrite (@imm_substl_typ_top l). apply ty_incap_top.
  - intros G e l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_bot l), (@imm_substl_typ_nocap l). apply ty_incap_bot.
  - intros G e A S T l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_rcd l (dec_typ (typ_label_normal A) S T)).
    rewrite (@imm_substl_dec_typ l (typ_label_normal A) S T).
    apply ty_incap_typ.
  - intros G e M S T l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_rcd l (dec_typ (typ_label_refcap M) S T)).
    rewrite (@imm_substl_dec_typ l (typ_label_refcap M) S T).
    rewrite (@imm_substl_typ_top l).
    apply ty_incap_cap.
  - intros G e m TC TZ TR l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_rcd l (dec_met m TC TZ TR)).
    rewrite (@imm_substl_dec_met l m TC TZ TR).
    apply ty_incap_met.
  - intros G e a T1 T2 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_rcd l (dec_fld a T1 T2)).
    rewrite (@imm_substl_dec_fld l a T1 T2).
    apply ty_incap_fld.
  - intros G e x B y S T T' o IH o' IHo l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_sel l (avar_f x) B (avar_f y)).
    rewrite (@imm_substl_avar_f l x), (@imm_substl_avar_f l y).
    eapply ty_incap_sel.
    + pose proof (IH l G' Hfix Rb Rv) as Hr.
      rewrite (@imm_substl_typ_rcd l (dec_typ B S T)), (@imm_substl_dec_typ l B S T) in Hr.
      exact Hr.
    + pose proof (IHo l G' Hfix Rb Rv) as Hr.
      rewrite (@imm_substl_typ_open l 0 y T) in Hr.
      exact Hr.
  - intros G e T l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_bnd l T). apply ty_incap_rec.
  - intros G e S1 T1 S2 T2 s IH s0 IH0 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_and l S1 T1), (@imm_substl_typ_and l S2 T2).
    apply ty_incap_and;
      [ exact (IH l G' Hfix Rb Rv) | exact (IH0 l G' Hfix Rb Rv) ].
  - intros G e S1 T1 S2 T2 s IH s0 IH0 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_or l S1 T1), (@imm_substl_typ_or l S2 T2).
    apply ty_incap_or;
      [ exact (IH l G' Hfix Rb Rv) | exact (IH0 l G' Hfix Rb Rv) ].
  - intros G e S T Hfun l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_fun l S T). apply ty_incap_fun. exact Hfun.
  - intros G e T Hnocap s IH l G' Hfix Rb Rv.
    pose proof (IH l G' Hfix Rb Rv) as Hr.
    rewrite (@imm_substl_typ_nocap l) in Hr.
    eapply ty_incap_nocap; [ exact Hnocap | exact Hr ].
Qed.


(* ---------- list substitution on terms, literals, definitions ---------- *)

Fixpoint imm_substl_trm (l : list (var * var)) (t : trm) : trm :=
  match l with
  | nil => t
  | cons (z, x) l' => subst_var z x (imm_substl_trm l' t)
  end.

Fixpoint imm_substl_lit (l : list (var * var)) (L : lit) : lit :=
  match l with
  | nil => L
  | cons (z, x) l' => subst_var z x (imm_substl_lit l' L)
  end.

Fixpoint imm_substl_def (l : list (var * var)) (d : def) : def :=
  match l with
  | nil => d
  | cons (z, x) l' => subst_var z x (imm_substl_def l' d)
  end.

Fixpoint imm_substl_defs (l : list (var * var)) (ds : defs) : defs :=
  match l with
  | nil => ds
  | cons (z, x) l' => subst_var z x (imm_substl_defs l' ds)
  end.

Definition imm_substl_objctx (l : list (var * var)) (Go : objctx) : objctx :=
  match Go with
  | objctx_empty => objctx_empty
  | objctx_lit x T => objctx_lit (imm_substl_var l x) (imm_substl_typ l T)
  | objctx_heap y T => objctx_heap (imm_substl_var l y) (imm_substl_typ l T)
  end.

(* Push equations for the term-level constructors. *)
Lemma imm_substl_trm_var l x :
  imm_substl_trm l (trm_var (avar_f x)) = trm_var (avar_f (imm_substl_var l x)).
Proof.
  induction l as [|[z y] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_trm_read l x a :
  imm_substl_trm l (trm_read (avar_f x) a) =
  trm_read (avar_f (imm_substl_var l x)) a.
Proof.
  induction l as [|[z y] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_trm_apply l x y :
  imm_substl_trm l (trm_apply (avar_f x) (avar_f y)) =
  trm_apply (avar_f (imm_substl_var l x)) (avar_f (imm_substl_var l y)).
Proof.
  induction l as [|[z w] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_trm_write l x a y :
  imm_substl_trm l (trm_write (avar_f x) a (avar_f y)) =
  trm_write (avar_f (imm_substl_var l x)) a (avar_f (imm_substl_var l y)).
Proof.
  induction l as [|[z w] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_trm_call l x m y :
  imm_substl_trm l (trm_call (avar_f x) m (avar_f y)) =
  trm_call (avar_f (imm_substl_var l x)) m (avar_f (imm_substl_var l y)).
Proof.
  induction l as [|[z w] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_trm_let l t u :
  imm_substl_trm l (trm_let t u) =
  trm_let (imm_substl_trm l t) (imm_substl_trm l u).
Proof.
  induction l as [|[z w] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_trm_lit l L t :
  imm_substl_trm l (trm_lit L t) =
  trm_lit (imm_substl_lit l L) (imm_substl_trm l t).
Proof.
  induction l as [|[z w] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_lit_fun l T t :
  imm_substl_lit l (lit_fun T t) =
  lit_fun (imm_substl_typ l T) (imm_substl_trm l t).
Proof.
  induction l as [|[z w] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_lit_obj l T ds :
  imm_substl_lit l (lit_obj T ds) =
  lit_obj (imm_substl_typ l T) (imm_substl_defs l ds).
Proof.
  induction l as [|[z w] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_def_typ l a T :
  imm_substl_def l (def_typ a T) = def_typ a (imm_substl_typ l T).
Proof.
  induction l as [|[z w] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_def_fld l a x :
  imm_substl_def l (def_fld a (avar_f x)) = def_fld a (avar_f (imm_substl_var l x)).
Proof.
  induction l as [|[z w] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_def_met l a t :
  imm_substl_def l (def_met a t) = def_met a (imm_substl_trm l t).
Proof.
  induction l as [|[z w] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_defs_nil l : imm_substl_defs l defs_nil = defs_nil.
Proof.
  induction l as [|[z w] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.
Lemma imm_substl_defs_cons l ds d :
  imm_substl_defs l (defs_cons ds d) =
  defs_cons (imm_substl_defs l ds) (imm_substl_def l d).
Proof.
  induction l as [|[z w] l' IH]; cbn; [reflexivity | rewrite IH; cbn; reflexivity].
Qed.

(* Commutation with opening. *)
Lemma imm_substl_trm_open (l : list (var * var)) (z : var) :
  (forall (t : trm) n,
      imm_substl_trm l (open_rec n z t) =
      open_rec n (imm_substl_var l z) (imm_substl_trm l t)) /\
  (forall (L : lit) n,
      imm_substl_lit l (open_rec n z L) =
      open_rec n (imm_substl_var l z) (imm_substl_lit l L)) /\
  (forall (d : def) n,
      imm_substl_def l (open_rec n z d) =
      open_rec n (imm_substl_var l z) (imm_substl_def l d)) /\
  (forall (ds : defs) n,
      imm_substl_defs l (open_rec n z ds) =
      open_rec n (imm_substl_var l z) (imm_substl_defs l ds)).
Proof.
  intros. induction l as [|[a b] l' IH].
  - cbn. repeat split; intros; reflexivity.
  - cbn [imm_substl_trm imm_substl_lit imm_substl_def imm_substl_defs]. repeat split.
    + intros t n. rewrite (proj1 IH t n).
      exact (proj1 (imm_subst_open_commut_trm_proj a b (imm_substl_var l' z)) (imm_substl_trm l' t) n).
    + intros L n. rewrite (proj1 (proj2 IH) L n).
      exact (proj1 (proj2 (imm_subst_open_commut_trm_proj a b (imm_substl_var l' z))) (imm_substl_lit l' L) n).
    + intros d n. rewrite (proj1 (proj2 (proj2 IH)) d n).
      exact (proj1 (proj2 (proj2 (imm_subst_open_commut_trm_proj a b (imm_substl_var l' z)))) (imm_substl_def l' d) n).
    + intros ds n. rewrite (proj2 (proj2 (proj2 IH)) ds n).
      exact (proj2 (proj2 (proj2 (imm_subst_open_commut_trm_proj a b (imm_substl_var l' z)))) (imm_substl_defs l' ds) n).
Qed.


(* ---------- freshness and renaming pushes for term substitutions ---------- *)

Lemma imm_fv_substl_notin_trm (l : list (var * var)) (w : var) :
  (forall a b, List.In (a, b) l -> w <> a /\ w <> b) ->
  (forall (t : trm), w \notin fv t -> w \notin fv (imm_substl_trm l t)) /\
  (forall (L : lit), w \notin fv L -> w \notin fv (imm_substl_lit l L)) /\
  (forall (d : def), w \notin fv d -> w \notin fv (imm_substl_def l d)) /\
  (forall (ds : defs), w \notin fv ds -> w \notin fv (imm_substl_defs l ds)).
Proof.
  intros Hf. induction l as [|[a b] l' IH].
  - cbn. repeat split; intros; assumption.
  - assert (Htail : forall a0 b0, List.In (a0, b0) l' -> w <> a0 /\ w <> b0).
    { intros a0 b0 Hin. apply Hf. right. exact Hin. }
    destruct (IH Htail) as [IHt [IHl [IHd IHds]]].
    repeat split.
    + intros t Ht. cbn. destruct (proj1 (imm_fv_subst_cases_trm_proj a b) (imm_substl_trm l' t))
        as [[Hfv _] | [Hne [Hin Hfv]]].
      * rewrite Hfv. apply IHt. exact Ht.
      * rewrite Hfv. apply notin_union. split.
        -- intro E. rewrite in_remove in E. destruct E as [E _]. exact ((IHt t Ht) E).
        -- apply notin_singleton. exact (proj2 (Hf a b (or_introl eq_refl))).
    + intros L HL. cbn. destruct (proj1 (proj2 (imm_fv_subst_cases_trm_proj a b)) (imm_substl_lit l' L))
        as [[Hfv _] | [Hne [Hin Hfv]]].
      * rewrite Hfv. apply IHl. exact HL.
      * rewrite Hfv. apply notin_union. split.
        -- intro E. rewrite in_remove in E. destruct E as [E _]. exact ((IHl L HL) E).
        -- apply notin_singleton. exact (proj2 (Hf a b (or_introl eq_refl))).
    + intros d Hd. cbn. destruct (proj1 (proj2 (proj2 (imm_fv_subst_cases_trm_proj a b))) (imm_substl_def l' d))
        as [[Hfv _] | [Hne [Hin Hfv]]].
      * rewrite Hfv. apply IHd. exact Hd.
      * rewrite Hfv. apply notin_union. split.
        -- intro E. rewrite in_remove in E. destruct E as [E _]. exact ((IHd d Hd) E).
        -- apply notin_singleton. exact (proj2 (Hf a b (or_introl eq_refl))).
    + intros ds Hds. cbn. destruct (proj2 (proj2 (proj2 (imm_fv_subst_cases_trm_proj a b))) (imm_substl_defs l' ds))
        as [[Hfv _] | [Hne [Hin Hfv]]].
      * rewrite Hfv. apply IHds. exact Hds.
      * rewrite Hfv. apply notin_union. split.
        -- intro E. rewrite in_remove in E. destruct E as [E _]. exact ((IHds ds Hds) E).
        -- apply notin_singleton. exact (proj2 (Hf a b (or_introl eq_refl))).
Qed.

Lemma imm_substl_trm_ext_fresh (l : list (var * var)) (w y : var) :
  (forall a b, List.In (a, b) l -> w <> a /\ w <> b) ->
  (forall (t : trm), w \notin fv t ->
      imm_substl_trm ((w, y) :: l) t = imm_substl_trm l t) /\
  (forall (L : lit), w \notin fv L ->
      imm_substl_lit ((w, y) :: l) L = imm_substl_lit l L) /\
  (forall (d : def), w \notin fv d ->
      imm_substl_def ((w, y) :: l) d = imm_substl_def l d) /\
  (forall (ds : defs), w \notin fv ds ->
      imm_substl_defs ((w, y) :: l) ds = imm_substl_defs l ds).
Proof.
  intros Hf. destruct (@imm_fv_substl_notin_trm l w Hf) as [Ht [Hl [Hd Hds]]].
  repeat split.
  - intros t H. cbn. apply (proj1 (imm_subst_fresh_trm_proj w y) (imm_substl_trm l t)).
    apply Ht. exact H.
  - intros L H. cbn. apply (proj1 (proj2 (imm_subst_fresh_trm_proj w y)) (imm_substl_lit l L)).
    apply Hl. exact H.
  - intros d H. cbn. apply (proj1 (proj2 (proj2 (imm_subst_fresh_trm_proj w y))) (imm_substl_def l d)).
    apply Hd. exact H.
  - intros ds H. cbn. apply (proj2 (proj2 (proj2 (imm_subst_fresh_trm_proj w y))) (imm_substl_defs l ds)).
    apply Hds. exact H.
Qed.

Lemma imm_substl_var_neq_avoid (l : list (var * var)) (a x : var) :
  a <> x -> x \notin imm_pairs_fv l -> imm_substl_var l a <> x.
Proof.
  intros Ha Hx. induction l as [|[z w] l' IH].
  - cbn. exact Ha.
  - cbn. assert (Htail : x \notin imm_pairs_fv l').
    { intro E. apply Hx. cbn [imm_pairs_fv]. rewrite in_union. right.
      rewrite in_union. right. exact E. }
    pose proof (IH Htail) as Hv.
    destruct (classic (imm_substl_var l' a = z)) as [E | E].
    + rewrite E, imm_subst_var_self. intro Hwx. apply Hx.
      cbn [imm_pairs_fv]. rewrite in_union. right. rewrite in_union. left.
      rewrite in_singleton. symmetry. exact Hwx.
    + rewrite (@imm_subst_var_neq z w (imm_substl_var l' a) E). exact Hv.
Qed.

Lemma imm_rb_l_push_ren (l : list (var * var)) (G G' : ctx)
      (y x : var) (vk : varkind) (T0 : typ) :
  imm_rb_l l G G' ->
  imm_substl_var l y = x ->
  x \notin ctx_dom G ->
  x \notin imm_pairs_fv l ->
  imm_rb_l l (G § y / vk ~ T0) (G' § x / vk ~ (imm_substl_typ l T0)).
Proof.
  intros Hm Hxy Hxd Hxp a U Hb. unfold imm_rb_l in Hm.
  destruct (@imm_ctx_binds_push_inv G y vk T0 a U Hb) as [[Ea EU] | [Hneq Hb0]].
  - subst a U. rewrite Hxy. apply ctx_binds_e.
  - assert (Ha : a <> x).
    { intro E. subst a. apply Hxd. eapply imm_ctx_binds_dom. exact Hb0. }
    assert (Hs : imm_substl_var l a <> x)
      by (apply imm_substl_var_neq_avoid; [ exact Ha | exact Hxp ]).
    eapply ctx_binds_n; [ exact Hs | apply Hm; exact Hb0 ].
Qed.

Lemma imm_rv_l_push_ren (l : list (var * var)) (G G' : ctx)
      (y x : var) (vk : varkind) (T0 : typ) :
  imm_rv_l l G G' ->
  imm_substl_var l y = x ->
  x \notin ctx_dom G ->
  x \notin imm_pairs_fv l ->
  imm_rv_l l (G § y / vk ~ T0) (G' § x / vk ~ (imm_substl_typ l T0)).
Proof.
  intros Hm Hxy Hxd Hxp a Hv. unfold imm_rv_l in Hm.
  destruct (@imm_ctx_vis_push_inv G y vk T0 a Hv) as [Ea | [Hneq Hv0]].
  - subst a. rewrite Hxy. apply ctx_vis_e.
  - assert (Ha : a <> x).
    { intro E. subst a. apply Hxd. apply imm_ctx_vis_dom. exact Hv0. }
    assert (Hs : imm_substl_var l a <> x)
      by (apply imm_substl_var_neq_avoid; [ exact Ha | exact Hxp ]).
    eapply ctx_vis_n; [ exact Hs | apply Hm; exact Hv0 ].
Qed.


(* ---------- capability bounds and viewpoint adaptation under substitution ---------- *)

Lemma imm_substl_typ_cap_adapt (l : list (var * var))
      (C : typ_refcap_label) (x : var) (T : typ) :
  imm_substl_typ l (typ_cap_adapt C x T) =
  typ_cap_adapt C (imm_substl_var l x) (imm_substl_typ l T).
Proof.
  rewrite (@imm_substl_typ_rcd l
    (dec_typ (typ_label_refcap C) typ_bot
       (typ_or T (typ_sel (avar_f x) (typ_label_refcap C) (avar_b 0))))).
  rewrite (@imm_substl_dec_typ l (typ_label_refcap C) typ_bot
    (typ_or T (typ_sel (avar_f x) (typ_label_refcap C) (avar_b 0)))).
  rewrite (@imm_substl_typ_bot l).
  rewrite (@imm_substl_typ_or l T
    (typ_sel (avar_f x) (typ_label_refcap C) (avar_b 0))).
  rewrite (@imm_substl_typ_sel l (avar_f x) (typ_label_refcap C) (avar_b 0)).
  rewrite (@imm_substl_avar_f l x), (@imm_substl_avar_b l 0).
  reflexivity.
Qed.

Lemma imm_capbnd_substl (C : typ_refcap_label) :
  forall (G : ctx) (Go : objctx) (e : renv) (T U : typ),
    @ty_capbnd typing_mode C G Go e T U ->
    forall (l : list (var * var)) (G' : ctx),
      imm_hfix e l -> imm_rb_l l G G' -> imm_rv_l l G G' ->
      @ty_capbnd typing_mode C G' Go e
        (imm_substl_typ l T) (imm_substl_typ l U).
Proof.
  intros G Go e T U H.
  revert G Go e T U H.
  apply (@ty_capbnd_ind typing_mode C
    (fun G Go e T U => forall l G',
        imm_hfix e l -> imm_rb_l l G G' -> imm_rv_l l G G' ->
        @ty_capbnd typing_mode C G' Go e
          (imm_substl_typ l T) (imm_substl_typ l U))).
  - intros G e l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_top l). apply ty_capbnd_top.
  - intros G e l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_bot l). apply ty_capbnd_bot.
  - intros G e A S T l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_rcd l (dec_typ (typ_label_normal A) S T)).
    rewrite (@imm_substl_dec_typ l (typ_label_normal A) S T).
    rewrite (@imm_substl_typ_top l).
    apply ty_capbnd_typ.
  - intros G e S T l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_rcd l (dec_typ (typ_label_refcap C) S T)).
    rewrite (@imm_substl_dec_typ l (typ_label_refcap C) S T).
    apply ty_capbnd_cap_sel.
  - intros G e C' S T Hne l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_rcd l (dec_typ (typ_label_refcap C') S T)).
    rewrite (@imm_substl_dec_typ l (typ_label_refcap C') S T).
    rewrite (@imm_substl_typ_top l).
    apply ty_capbnd_cap_ignore. exact Hne.
  - intros G e m TC TZ TR l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_rcd l (dec_met m TC TZ TR)).
    rewrite (@imm_substl_dec_met l m TC TZ TR).
    rewrite (@imm_substl_typ_top l).
    apply ty_capbnd_met.
  - intros G e a T1 T2 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_rcd l (dec_fld a T1 T2)).
    rewrite (@imm_substl_dec_fld l a T1 T2).
    rewrite (@imm_substl_typ_top l).
    apply ty_capbnd_fld.
  - intros G e x B y S T T' o1 o2 IH l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_sel l (avar_f x) B (avar_f y)).
    rewrite (@imm_substl_avar_f l x), (@imm_substl_avar_f l y).
    eapply ty_capbnd_sel.
    + pose proof (proj1 imm_ts_substl G objctx_empty e x
                    (typ_rcd (dec_typ B S T)) o1 l G' Hfix Rb Rv) as Hr.
      rewrite (@imm_substl_typ_rcd l (dec_typ B S T)),
              (@imm_substl_dec_typ l B S T) in Hr.
      exact Hr.
    + pose proof (IH l G' Hfix Rb Rv) as Hr.
      rewrite (@imm_substl_typ_open l 0 y T) in Hr.
      exact Hr.
  - intros G e T l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_bnd l T), (@imm_substl_typ_top l).
    apply ty_capbnd_rec.
  - intros G e S1 T1 S2 T2 o1 IH1 o2 IH2 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_and l S1 T1), (@imm_substl_typ_and l S2 T2).
    apply ty_capbnd_and;
      [ exact (IH1 l G' Hfix Rb Rv) | exact (IH2 l G' Hfix Rb Rv) ].
  - intros G e S1 T1 S2 T2 o1 IH1 o2 IH2 l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_or l S1 T1), (@imm_substl_typ_or l S2 T2).
    apply ty_capbnd_or;
      [ exact (IH1 l G' Hfix Rb Rv) | exact (IH2 l G' Hfix Rb Rv) ].
  - intros G e S T l G' Hfix Rb Rv.
    rewrite (@imm_substl_typ_fun l S T), (@imm_substl_typ_top l).
    apply ty_capbnd_all.
Qed.

Lemma imm_viewpoint_substl (G : ctx) (Go : objctx) (e : renv)
      (x : var) (Tf Tr : typ) :
  @viewpoint_adapt typing_mode x G Go e Tf Tr ->
  forall (l : list (var * var)) (G' : ctx),
    imm_hfix e l -> imm_rb_l l G G' -> imm_rv_l l G G' ->
    @viewpoint_adapt typing_mode (imm_substl_var l x) G' Go e
      (imm_substl_typ l Tf) (imm_substl_typ l Tr).
Proof.
  intros H l G' Hfix Rb Rv.
  unfold viewpoint_adapt in *.
  rewrite imm_mode_mut_viewpoint in H.
  rewrite imm_mode_mut_viewpoint.
  inversion H as [C x0 G0 Go0 e0 T0 Tstrip Tcap Hinc Hcap]; subst.
  rewrite (@imm_substl_typ_and l Tstrip
             (typ_cap_adapt typ_refcap_mutability x Tcap)).
  rewrite (@imm_substl_typ_cap_adapt l typ_refcap_mutability x Tcap).
  eapply viewpoint_adapt_cap_strip_combine.
  - exact (proj2 (proj2 imm_ts_substl) G Go e Tf Tstrip Hinc l G' Hfix Rb Rv).
  - exact (@imm_capbnd_substl typ_refcap_mutability G Go e Tf Tcap Hcap l G' Hfix Rb Rv).
Qed.


(* ---------- renaming push through a freshly opened binder ---------- *)

Lemma imm_rb_l_push_ren_ext (l : list (var * var)) (G G' : ctx)
      (w x : var) (vk : varkind) (T0 : typ) :
  imm_rb_l l G G' ->
  (forall a b, List.In (a, b) l -> w <> a /\ w <> b) ->
  w \notin ctx_dom G -> w \notin ctx_fv G ->
  x \notin ctx_dom G -> x \notin imm_pairs_fv l ->
  imm_rb_l ((w, x) :: l)
    (G § w / vk ~ T0) (G' § x / vk ~ imm_substl_typ ((w, x) :: l) T0).
Proof.
  intros Hm Hl Hwd Hwf Hxd Hxp a U Hb. unfold imm_rb_l in Hm.
  destruct (@imm_ctx_binds_push_inv G w vk T0 a U Hb) as [[Ea EU] | [Hneq Hb0]].
  - subst a U. rewrite (@imm_substl_var_ext_head l w x (fun a b H => proj1 (Hl a b H))).
    apply ctx_binds_e.
  - assert (Ha : a \in ctx_dom G) by (eapply imm_ctx_binds_dom; exact Hb0).
    assert (Hav : a <> w) by (intro E; subst a; exact (Hwd Ha)).
    assert (Hax : a <> x) by (intro E; subst a; exact (Hxd Ha)).
    assert (Hwv : imm_substl_var l a <> w)
      by (apply (@imm_substl_var_neq_fresh l w a Hl); exact Hav).
    assert (Hsx : imm_substl_var l a <> x)
      by (apply (@imm_substl_var_neq_avoid l a x); [ exact Hax | exact Hxp ]).
    assert (HfvU : w \notin fv U).
    { intro E. apply Hwf. exact (@imm_ctx_binds_fv G a U Hb0 w E). }
    assert (Hfvs : w \notin fv (imm_substl_typ l U))
      by (apply imm_fv_substl_notin; [ exact HfvU | exact Hl ]).
    rewrite (@imm_substl_typ_ext_fresh l w x U HfvU Hl).
    cbn [imm_substl_var imm_substl_typ].
    rewrite (@imm_subst_var_neq w x (imm_substl_var l a) Hwv).
    eapply ctx_binds_n; [ exact Hsx | apply Hm; exact Hb0 ].
Qed.

Lemma imm_rv_l_push_ren_ext (l : list (var * var)) (G G' : ctx)
      (w x : var) (vk : varkind) (T0 : typ) :
  imm_rv_l l G G' ->
  (forall a b, List.In (a, b) l -> w <> a /\ w <> b) ->
  w \notin ctx_dom G ->
  x \notin ctx_dom G -> x \notin imm_pairs_fv l ->
  imm_rv_l ((w, x) :: l)
    (G § w / vk ~ T0) (G' § x / vk ~ imm_substl_typ ((w, x) :: l) T0).
Proof.
  intros Hm Hl Hwd Hxd Hxp a Hv. unfold imm_rv_l in Hm.
  destruct (@imm_ctx_vis_push_inv G w vk T0 a Hv) as [Ea | [Hneq Hv0]].
  - subst a. rewrite (@imm_substl_var_ext_head l w x (fun a b H => proj1 (Hl a b H))).
    apply ctx_vis_e.
  - assert (Ha : a \in ctx_dom G) by (apply imm_ctx_vis_dom; exact Hv0).
    assert (Hav : a <> w) by (intro E; subst a; exact (Hwd Ha)).
    assert (Hax : a <> x) by (intro E; subst a; exact (Hxd Ha)).
    assert (Hwv : imm_substl_var l a <> w)
      by (apply (@imm_substl_var_neq_fresh l w a Hl); exact Hav).
    assert (Hsx : imm_substl_var l a <> x)
      by (apply (@imm_substl_var_neq_avoid l a x); [ exact Hax | exact Hxp ]).
    cbn [imm_substl_var].
    rewrite (@imm_subst_var_neq w x (imm_substl_var l a) Hwv).
    eapply ctx_vis_n; [ exact Hsx | apply Hm; exact Hv0 ].
Qed.


(* ---------- mutual substitution for the term-level judgments ---------- *)
Definition imm_cast_trm (G : ctx) (Go : objctx) (e : renv)
    (t1 t2 : trm) (T1 T2 : typ) (Et : t1 = t2) (ET : T1 = T2)
    (d : @ty_trm typing_mode G Go e t1 T1) : @ty_trm typing_mode G Go e t2 T2 :=
  match Et with eq_refl => match ET with eq_refl => d end end.

Definition imm_cast_lit (G : ctx) (Go : objctx) (e : renv)
    (L1 L2 : lit) (T1 T2 : typ) (EL : L1 = L2) (ET : T1 = T2)
    (d : @ty_lit typing_mode G Go e L1 T1) : @ty_lit typing_mode G Go e L2 T2 :=
  match EL with eq_refl => match ET with eq_refl => d end end.

Definition imm_cast_def (G : ctx) (Go : objctx) (e : renv)
    (d1 d2 : def) (D1 D2 : dec) (Ed : d1 = d2) (ED : D1 = D2)
    (dd : @ty_def typing_mode G Go e d1 D1) : @ty_def typing_mode G Go e d2 D2 :=
  match Ed with eq_refl => match ED with eq_refl => dd end end.

Definition imm_cast_defs (G : ctx) (Go : objctx) (e : renv)
    (ds1 ds2 : defs) (T1 T2 : typ) (Es : ds1 = ds2) (ET : T1 = T2)
    (dd : @ty_defs typing_mode G Go e ds1 T1) : @ty_defs typing_mode G Go e ds2 T2 :=
  match Es with eq_refl => match ET with eq_refl => dd end end.

Definition imm_cast_var (G : ctx) (Go : objctx) (e : renv) (x : var)
    (T1 T2 : typ) (ET : T1 = T2)
    (d : @ty_var typing_mode G Go e x T1) : @ty_var typing_mode G Go e x T2 :=
  match ET with eq_refl => d end.

Lemma imm_eq_typ_fun l S T :
  imm_substl_typ l (typ_fun S T) =
  typ_fun (imm_substl_typ l S) (imm_substl_typ l T).
Proof. apply imm_substl_typ_fun. Qed.

Lemma imm_eq_rcd_fld l a S T :
  imm_substl_typ l (typ_rcd (dec_fld a S T)) =
  typ_rcd (dec_fld a (imm_substl_typ l S) (imm_substl_typ l T)).
Proof.
  rewrite (@imm_substl_typ_rcd l (dec_fld a S T)).
  rewrite (@imm_substl_dec_fld l a S T). reflexivity.
Qed.

Lemma imm_eq_rcd_met l m TC TZ TR :
  imm_substl_typ l (typ_rcd (dec_met m TC TZ TR)) =
  typ_rcd (dec_met m (imm_substl_typ l TC) (imm_substl_typ l TZ) (imm_substl_typ l TR)).
Proof.
  rewrite (@imm_substl_typ_rcd l (dec_met m TC TZ TR)).
  rewrite (@imm_substl_dec_met l m TC TZ TR). reflexivity.
Qed.

Lemma imm_eq_mut l :
  imm_substl_typ l
    (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability) typ_bot typ_bot)) =
  typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability) typ_bot typ_bot).
Proof.
  rewrite (@imm_substl_typ_rcd l
             (dec_typ (typ_label_refcap typ_refcap_mutability) typ_bot typ_bot)).
  rewrite (@imm_substl_dec_typ l (typ_label_refcap typ_refcap_mutability) typ_bot typ_bot).
  rewrite (@imm_substl_typ_bot l). reflexivity.
Qed.

Lemma imm_substl_typ_objlit l T :
  imm_substl_typ l (typ_objlit typing_mode T) =
  typ_objlit typing_mode (imm_substl_typ l T).
Proof.
  destruct (mode_objlit_refcaps' typing_mode); cbn.
  - rewrite (@imm_substl_typ_and l (typ_bnd T) typ_top),
            (@imm_substl_typ_bnd l T), (@imm_substl_typ_top l).
    reflexivity.
  - rewrite (@imm_substl_typ_and l (typ_bnd T)
               (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability)
                           typ_bot typ_bot))),
            (@imm_substl_typ_bnd l T),
            (@imm_substl_typ_rcd l
               (dec_typ (typ_label_refcap typ_refcap_mutability) typ_bot typ_bot)),
            (@imm_substl_dec_typ l (typ_label_refcap typ_refcap_mutability)
               typ_bot typ_bot),
            (@imm_substl_typ_bot l).
    reflexivity.
Qed.

Lemma imm_label_of_subst_def z x d : label_of (subst_def z x d) = label_of d.
Proof. destruct d; reflexivity. Qed.

Lemma imm_get_def_subst_defs z x ds l0 :
  get_def l0 (subst_defs z x ds) = option_map (subst_def z x) (get_def l0 ds).
Proof.
  induction ds as [|ds IH d]; cbn [subst_defs get_def].
  - reflexivity.
  - rewrite imm_label_of_subst_def.
    destruct (classic (label_of d = l0)) as [E | E].
    + rewrite (If_l (A:=option def) (P:=label_of d = l0)
                 (Some (subst_def z x d))
                 (get_def l0 (subst_defs z x ds))) by exact E.
      rewrite (If_l (A:=option def) (P:=label_of d = l0)
                 (Some d) (get_def l0 ds)) by exact E.
      reflexivity.
    + rewrite (If_r (A:=option def) (P:=label_of d = l0)
                 (Some (subst_def z x d))
                 (get_def l0 (subst_defs z x ds))) by exact E.
      rewrite (If_r (A:=option def) (P:=label_of d = l0)
                 (Some d) (get_def l0 ds)) by exact E.
      exact IH.
Qed.

Lemma imm_label_of_substl_def l d : label_of (imm_substl_def l d) = label_of d.
Proof.
  induction l as [|[z x] l' IH]; cbn [imm_substl_def]; [reflexivity|].
  rewrite imm_label_of_subst_def, IH. reflexivity.
Qed.

Lemma imm_get_def_substl_defs l ds l0 :
  get_def l0 (imm_substl_defs l ds) =
  option_map (imm_substl_def l) (get_def l0 ds).
Proof.
  induction l as [|[z x] l' IH]; cbn [imm_substl_defs imm_substl_def].
  - destruct (get_def l0 ds); reflexivity.
  - rewrite imm_get_def_subst_defs, IH.
    destruct (get_def l0 ds); cbn [option_map]; reflexivity.
Qed.

Lemma imm_defs_hasnt_substl l ds d :
  defs_hasnt ds (label_of d) ->
  defs_hasnt (imm_substl_defs l ds) (label_of (imm_substl_def l d)).
Proof.
  intros H. unfold defs_hasnt in *.
  rewrite imm_label_of_substl_def, imm_get_def_substl_defs, H. reflexivity.
Qed.

(* Substitution pushes through the met-typing context.  The binders xz and xc
   are chosen fresh for the substitution, so they are fixed by it. *)
Lemma imm_rb_l_ctx_obj_met_substl l G G' Go Go' xz xc TZ TC :
  imm_rb_l l (ctx_obj G Go) (ctx_obj G' Go') ->
  Go' = imm_substl_objctx l Go ->
  xz \notin ctx_dom (ctx_obj G Go) ->
  xz \notin imm_pairs_fv l ->
  xc \notin ctx_dom (ctx_obj G Go) ->
  xc <> xz ->
  xc \notin imm_pairs_fv l ->
  imm_rb_l l (ctx_obj_met typing_mode G Go xz TZ xc TC)
             (ctx_obj_met typing_mode G' Go' xz (imm_substl_typ l TZ)
                         xc (imm_substl_typ l TC)).
Proof.
  intros Rb Ego Hxd Hxp Hcd Hcne Hcp.
  assert (Hslvz : imm_substl_var l xz = xz)
    by (apply imm_substl_var_notin_src; intros z x' Hin;
        apply (proj1 (@imm_pairs_fv_notin l xz z x' Hxp Hin))).
  assert (Hslvc : imm_substl_var l xc = xc)
    by (apply imm_substl_var_notin_src; intros z x' Hin;
        apply (proj1 (@imm_pairs_fv_notin l xc z x' Hcp Hin))).
  destruct Go as [|xl Tl|yh Th].
  - cbn [imm_substl_objctx] in Ego. subst Go'.
    cbn [ctx_obj_met ctx_obj].
    rewrite (imm_mode_vis_hide typing_mode Hmm). cbn.
    assert (Hdh : xz \notin ctx_dom (ctx_hide (ctx_obj G objctx_empty)))
      by (cbn [ctx_dom]; exact Hxd).
    assert (Hdhc : xc \notin ctx_dom (ctx_hide (ctx_obj G objctx_empty)))
      by (cbn [ctx_dom]; exact Hcd).
    pose proof (@imm_rb_l_hide l (ctx_obj G objctx_empty)
                  (ctx_obj G' objctx_empty) Rb) as Hb.
    pose proof (@imm_rb_l_push_ren l (ctx_hide (ctx_obj G objctx_empty))
                  (ctx_hide (ctx_obj G' objctx_empty)) xz xz v_par TZ
                  Hb Hslvz Hdh Hxp) as H1.
    assert (Hdh2 : xc \notin ctx_dom
              ((ctx_hide (ctx_obj G objctx_empty)) § xz / v_par ~ TZ))
      by (cbn [ctx_dom]; apply notin_union; split;
          [ apply notin_singleton; exact Hcne | exact Hdhc ]).
    pose proof (@imm_rb_l_push_ren l
                  ((ctx_hide (ctx_obj G objctx_empty)) § xz / v_par ~ TZ)
                  ((ctx_hide (ctx_obj G' objctx_empty)) § xz / v_par
                     ~ imm_substl_typ l TZ)
                  xc xc v_recv (open_rec 0 xz TC) H1 Hslvc Hdh2 Hcp) as H2.
    rewrite (@imm_substl_typ_open l 0 xz TC) in H2.
    rewrite Hslvz in H2.
    cbn [ctx_obj]. exact H2.
  - cbn [imm_substl_objctx] in Ego. subst Go'.
    cbn [ctx_obj_met ctx_obj].
    rewrite (imm_mode_vis_hide typing_mode Hmm). cbn.
    assert (Hdh : xz \notin ctx_dom
              (ctx_hide (ctx_obj G (objctx_lit xl Tl))))
      by (cbn [ctx_dom]; exact Hxd).
    assert (Hdhc : xc \notin ctx_dom
              (ctx_hide (ctx_obj G (objctx_lit xl Tl))))
      by (cbn [ctx_dom]; exact Hcd).
    pose proof (@imm_rb_l_hide l (ctx_obj G (objctx_lit xl Tl))
                  (ctx_obj G' (objctx_lit (imm_substl_var l xl)
                                  (imm_substl_typ l Tl))) Rb) as Hb.
    pose proof (@imm_rb_l_push_ren l
                  (ctx_hide (ctx_obj G (objctx_lit xl Tl)))
                  (ctx_hide (ctx_obj G' (objctx_lit (imm_substl_var l xl)
                                             (imm_substl_typ l Tl))))
                  xz xz v_par TZ Hb Hslvz Hdh Hxp) as H1.
    assert (Hdh2 : xc \notin ctx_dom
              ((ctx_hide (ctx_obj G (objctx_lit xl Tl))) § xz / v_par ~ TZ))
      by (cbn [ctx_dom]; apply notin_union; split;
          [ apply notin_singleton; exact Hcne | exact Hdhc ]).
    pose proof (@imm_rb_l_push_ren l
                  ((ctx_hide (ctx_obj G (objctx_lit xl Tl))) § xz / v_par ~ TZ)
                  ((ctx_hide (ctx_obj G' (objctx_lit (imm_substl_var l xl)
                                              (imm_substl_typ l Tl))))
                     § xz / v_par ~ imm_substl_typ l TZ)
                  xc xc v_recv
                  (typ_and (open_rec 0 xz TC)
                     (typ_and (open_rec 0 xl Tl) (open_rec 0 xc Tl)))
                  H1 Hslvc Hdh2 Hcp) as H2.
    rewrite (@imm_substl_typ_and l (open_rec 0 xz TC)
               (typ_and (open_rec 0 xl Tl) (open_rec 0 xc Tl))) in H2.
    rewrite (@imm_substl_typ_and l (open_rec 0 xl Tl)
               (open_rec 0 xc Tl)) in H2.
    rewrite (@imm_substl_typ_open l 0 xz TC) in H2.
    rewrite (@imm_substl_typ_open l 0 xl Tl) in H2.
    rewrite (@imm_substl_typ_open l 0 xc Tl) in H2.
    rewrite Hslvz in H2.
    rewrite Hslvc in H2.
    cbn [ctx_obj]. exact H2.
  - cbn [imm_substl_objctx] in Ego. subst Go'.
    cbn [ctx_obj_met ctx_obj].
    rewrite (imm_mode_vis_hide typing_mode Hmm). cbn.
    assert (Hdh : xz \notin ctx_dom (ctx_hide G))
      by (cbn [ctx_dom]; exact Hxd).
    assert (Hdhc : xc \notin ctx_dom (ctx_hide G))
      by (cbn [ctx_dom]; exact Hcd).
    pose proof (@imm_rb_l_hide l (ctx_obj G (objctx_heap yh Th))
                  (ctx_obj G' (objctx_heap (imm_substl_var l yh)
                                  (imm_substl_typ l Th))) Rb) as Hb.
    cbn [ctx_obj] in Hb.
    pose proof (@imm_rb_l_push_ren l (ctx_hide G) (ctx_hide G')
                  xz xz v_par TZ Hb Hslvz Hdh Hxp) as H1.
    assert (Hdh2 : xc \notin ctx_dom (ctx_hide G § xz / v_par ~ TZ))
      by (cbn [ctx_dom]; apply notin_union; split;
          [ apply notin_singleton; exact Hcne | exact Hdhc ]).
    pose proof (@imm_rb_l_push_ren l
                  (ctx_hide G § xz / v_par ~ TZ)
                  (ctx_hide G' § xz / v_par ~ imm_substl_typ l TZ)
                  xc xc v_recv
                  (typ_and (open_rec 0 xz TC)
                     (typ_and (open_rec 0 yh Th) (open_rec 0 xc Th)))
                  H1 Hslvc Hdh2 Hcp) as H2.
    rewrite (@imm_substl_typ_and l (open_rec 0 xz TC)
               (typ_and (open_rec 0 yh Th) (open_rec 0 xc Th))) in H2.
    rewrite (@imm_substl_typ_and l (open_rec 0 yh Th)
               (open_rec 0 xc Th)) in H2.
    rewrite (@imm_substl_typ_open l 0 xz TC) in H2.
    rewrite (@imm_substl_typ_open l 0 yh Th) in H2.
    rewrite (@imm_substl_typ_open l 0 xc Th) in H2.
    rewrite Hslvz in H2.
    rewrite Hslvc in H2.
    exact H2.
Qed.

Lemma imm_rv_l_ctx_obj_met_substl l G G' Go Go' xz xc TZ TC :
  imm_rv_l l (ctx_obj G Go) (ctx_obj G' Go') ->
  Go' = imm_substl_objctx l Go ->
  xz \notin ctx_dom (ctx_obj G Go) ->
  xz \notin imm_pairs_fv l ->
  xc \notin ctx_dom (ctx_obj G Go) ->
  xc <> xz ->
  xc \notin imm_pairs_fv l ->
  imm_rv_l l (ctx_obj_met typing_mode G Go xz TZ xc TC)
             (ctx_obj_met typing_mode G' Go' xz (imm_substl_typ l TZ)
                         xc (imm_substl_typ l TC)).
Proof.
  intros Rb Ego Hxd Hxp Hcd Hcne Hcp.
  assert (Hslvz : imm_substl_var l xz = xz)
    by (apply imm_substl_var_notin_src; intros z x' Hin;
        apply (proj1 (@imm_pairs_fv_notin l xz z x' Hxp Hin))).
  assert (Hslvc : imm_substl_var l xc = xc)
    by (apply imm_substl_var_notin_src; intros z x' Hin;
        apply (proj1 (@imm_pairs_fv_notin l xc z x' Hcp Hin))).
  destruct Go as [|xl Tl|yh Th].
  - cbn [imm_substl_objctx] in Ego. subst Go'.
    cbn [ctx_obj_met ctx_obj].
    rewrite (imm_mode_vis_hide typing_mode Hmm). cbn.
    assert (Hdh : xz \notin ctx_dom (ctx_hide (ctx_obj G objctx_empty)))
      by (cbn [ctx_dom]; exact Hxd).
    assert (Hdhc : xc \notin ctx_dom (ctx_hide (ctx_obj G objctx_empty)))
      by (cbn [ctx_dom]; exact Hcd).
    pose proof (@imm_rv_l_hide l (ctx_obj G objctx_empty)
                  (ctx_obj G' objctx_empty) Rb) as Hb.
    pose proof (@imm_rv_l_push_ren l (ctx_hide (ctx_obj G objctx_empty))
                  (ctx_hide (ctx_obj G' objctx_empty)) xz xz v_par TZ
                  Hb Hslvz Hdh Hxp) as H1.
    assert (Hdh2 : xc \notin ctx_dom
              ((ctx_hide (ctx_obj G objctx_empty)) § xz / v_par ~ TZ))
      by (cbn [ctx_dom]; apply notin_union; split;
          [ apply notin_singleton; exact Hcne | exact Hdhc ]).
    pose proof (@imm_rv_l_push_ren l
                  ((ctx_hide (ctx_obj G objctx_empty)) § xz / v_par ~ TZ)
                  ((ctx_hide (ctx_obj G' objctx_empty)) § xz / v_par
                     ~ imm_substl_typ l TZ)
                  xc xc v_recv (open_rec 0 xz TC) H1 Hslvc Hdh2 Hcp) as H2.
    rewrite (@imm_substl_typ_open l 0 xz TC) in H2.
    rewrite Hslvz in H2.
    cbn [ctx_obj]. exact H2.
  - cbn [imm_substl_objctx] in Ego. subst Go'.
    cbn [ctx_obj_met ctx_obj].
    rewrite (imm_mode_vis_hide typing_mode Hmm). cbn.
    assert (Hdh : xz \notin ctx_dom
              (ctx_hide (ctx_obj G (objctx_lit xl Tl))))
      by (cbn [ctx_dom]; exact Hxd).
    assert (Hdhc : xc \notin ctx_dom
              (ctx_hide (ctx_obj G (objctx_lit xl Tl))))
      by (cbn [ctx_dom]; exact Hcd).
    pose proof (@imm_rv_l_hide l (ctx_obj G (objctx_lit xl Tl))
                  (ctx_obj G' (objctx_lit (imm_substl_var l xl)
                                  (imm_substl_typ l Tl))) Rb) as Hb.
    pose proof (@imm_rv_l_push_ren l
                  (ctx_hide (ctx_obj G (objctx_lit xl Tl)))
                  (ctx_hide (ctx_obj G' (objctx_lit (imm_substl_var l xl)
                                             (imm_substl_typ l Tl))))
                  xz xz v_par TZ Hb Hslvz Hdh Hxp) as H1.
    assert (Hdh2 : xc \notin ctx_dom
              ((ctx_hide (ctx_obj G (objctx_lit xl Tl))) § xz / v_par ~ TZ))
      by (cbn [ctx_dom]; apply notin_union; split;
          [ apply notin_singleton; exact Hcne | exact Hdhc ]).
    pose proof (@imm_rv_l_push_ren l
                  ((ctx_hide (ctx_obj G (objctx_lit xl Tl))) § xz / v_par ~ TZ)
                  ((ctx_hide (ctx_obj G' (objctx_lit (imm_substl_var l xl)
                                              (imm_substl_typ l Tl))))
                     § xz / v_par ~ imm_substl_typ l TZ)
                  xc xc v_recv
                  (typ_and (open_rec 0 xz TC)
                     (typ_and (open_rec 0 xl Tl) (open_rec 0 xc Tl)))
                  H1 Hslvc Hdh2 Hcp) as H2.
    rewrite (@imm_substl_typ_and l (open_rec 0 xz TC)
               (typ_and (open_rec 0 xl Tl) (open_rec 0 xc Tl))) in H2.
    rewrite (@imm_substl_typ_and l (open_rec 0 xl Tl)
               (open_rec 0 xc Tl)) in H2.
    rewrite (@imm_substl_typ_open l 0 xz TC) in H2.
    rewrite (@imm_substl_typ_open l 0 xl Tl) in H2.
    rewrite (@imm_substl_typ_open l 0 xc Tl) in H2.
    rewrite Hslvz in H2.
    rewrite Hslvc in H2.
    cbn [ctx_obj]. exact H2.
  - cbn [imm_substl_objctx] in Ego. subst Go'.
    cbn [ctx_obj_met ctx_obj].
    rewrite (imm_mode_vis_hide typing_mode Hmm). cbn.
    assert (Hdh : xz \notin ctx_dom (ctx_hide G))
      by (cbn [ctx_dom]; exact Hxd).
    assert (Hdhc : xc \notin ctx_dom (ctx_hide G))
      by (cbn [ctx_dom]; exact Hcd).
    pose proof (@imm_rv_l_hide l (ctx_obj G (objctx_heap yh Th))
                  (ctx_obj G' (objctx_heap (imm_substl_var l yh)
                                  (imm_substl_typ l Th))) Rb) as Hb.
    cbn [ctx_obj] in Hb.
    pose proof (@imm_rv_l_push_ren l (ctx_hide G) (ctx_hide G')
                  xz xz v_par TZ Hb Hslvz Hdh Hxp) as H1.
    assert (Hdh2 : xc \notin ctx_dom (ctx_hide G § xz / v_par ~ TZ))
      by (cbn [ctx_dom]; apply notin_union; split;
          [ apply notin_singleton; exact Hcne | exact Hdhc ]).
    pose proof (@imm_rv_l_push_ren l
                  (ctx_hide G § xz / v_par ~ TZ)
                  (ctx_hide G' § xz / v_par ~ imm_substl_typ l TZ)
                  xc xc v_recv
                  (typ_and (open_rec 0 xz TC)
                     (typ_and (open_rec 0 yh Th) (open_rec 0 xc Th)))
                  H1 Hslvc Hdh2 Hcp) as H2.
    rewrite (@imm_substl_typ_and l (open_rec 0 xz TC)
               (typ_and (open_rec 0 yh Th) (open_rec 0 xc Th))) in H2.
    rewrite (@imm_substl_typ_and l (open_rec 0 yh Th)
               (open_rec 0 xc Th)) in H2.
    rewrite (@imm_substl_typ_open l 0 xz TC) in H2.
    rewrite (@imm_substl_typ_open l 0 yh Th) in H2.
    rewrite (@imm_substl_typ_open l 0 xc Th) in H2.
    rewrite Hslvz in H2.
    rewrite Hslvc in H2.
    exact H2.
Qed.


Fixpoint imm_trm_subst (G : ctx) (Go : objctx) (e : renv) (t : trm) (T : typ)
    (d : @ty_trm typing_mode G Go e t T) {struct d} :
  forall (l : list (var * var)) (G' : ctx),
    imm_hfix e l -> imm_rb_l l G G' -> imm_rv_l l G G' ->
    @ty_trm typing_mode G' Go e (imm_substl_trm l t) (imm_substl_typ l T) :=
  match d in @ty_trm _ Gi Goi ei ti Ti return
      (forall (l : list (var * var)) (G' : ctx),
          imm_hfix ei l -> imm_rb_l l Gi G' -> imm_rv_l l Gi G' ->
          @ty_trm typing_mode G' Goi ei
            (imm_substl_trm l ti) (imm_substl_typ l Ti))
  with
  | @ty_trm_var _ G0 e0 x0 T0 c o =>
      fun l G' Hfix Rb Rv =>
        @imm_cast_trm G' objctx_empty e0
          (trm_var (avar_f (imm_substl_var l x0)))
          (imm_substl_trm l (trm_var (avar_f x0)))
          (imm_substl_typ l T0) (imm_substl_typ l T0)
          (eq_sym (imm_substl_trm_var l x0)) eq_refl
          (@ty_trm_var typing_mode G' e0
             (imm_substl_var l x0) (imm_substl_typ l T0)
             (fun Heq => Rv x0 (c Heq))
             (proj1 imm_ts_substl G0 objctx_empty e0 x0 T0 o l G' Hfix Rb Rv))
  | @ty_trm_apply _ G0 e0 x0 z0 S0 T0 Hfun cx cz o o0 =>
      fun l G' Hfix Rb Rv =>
        @imm_cast_trm G' objctx_empty e0
          (trm_apply (avar_f (imm_substl_var l x0)) (avar_f (imm_substl_var l z0)))
          (imm_substl_trm l (trm_apply (avar_f x0) (avar_f z0)))
          (open_rec 0 (imm_substl_var l z0) (imm_substl_typ l T0))
          (imm_substl_typ l (open_rec 0 z0 T0))
          (eq_sym (imm_substl_trm_apply l x0 z0))
          (eq_sym (imm_substl_typ_open l 0 z0 T0))
          (@ty_trm_apply typing_mode G' e0
             (imm_substl_var l x0) (imm_substl_var l z0)
             (imm_substl_typ l S0) (imm_substl_typ l T0) Hfun
             (fun Heq => Rv x0 (cx Heq))
             (fun Heq => Rv z0 (cz Heq))
             (@imm_cast_var G' objctx_empty e0 (imm_substl_var l x0)
                (imm_substl_typ l (typ_fun S0 T0))
                (typ_fun (imm_substl_typ l S0) (imm_substl_typ l T0))
                (imm_eq_typ_fun l S0 T0)
                (proj1 imm_ts_substl G0 objctx_empty e0 x0 (typ_fun S0 T0) o
                   l G' Hfix Rb Rv))
             (proj1 imm_ts_substl G0 objctx_empty e0 z0 S0 o0 l G' Hfix Rb Rv))
  | @ty_trm_read _ G0 e0 x0 a0 S0 T0 U0 c o v =>
      fun l G' Hfix Rb Rv =>
        @imm_cast_trm G' objctx_empty e0
          (trm_read (avar_f (imm_substl_var l x0)) a0)
          (imm_substl_trm l (trm_read (avar_f x0) a0))
          (imm_substl_typ l U0) (imm_substl_typ l U0)
          (eq_sym (imm_substl_trm_read l x0 a0)) eq_refl
          (@ty_trm_read typing_mode G' e0
             (imm_substl_var l x0) a0
             (imm_substl_typ l S0) (imm_substl_typ l T0) (imm_substl_typ l U0)
             (fun Heq => Rv x0 (c Heq))
             (@imm_cast_var G' objctx_empty e0 (imm_substl_var l x0)
                (imm_substl_typ l (typ_rcd (dec_fld a0 S0 T0)))
                (typ_rcd (dec_fld a0 (imm_substl_typ l S0) (imm_substl_typ l T0)))
                (imm_eq_rcd_fld l a0 S0 T0)
                (proj1 imm_ts_substl G0 objctx_empty e0 x0
                   (typ_rcd (dec_fld a0 S0 T0)) o l G' Hfix Rb Rv))
             (@imm_viewpoint_substl G0 objctx_empty e0 x0 T0 U0 v l G' Hfix Rb Rv))
  | @ty_trm_write _ G0 e0 x0 y0 a0 S0 T0 cx cy om o0 o1 =>
      fun l G' Hfix Rb Rv =>
        @imm_cast_trm G' objctx_empty e0
          (trm_write (avar_f (imm_substl_var l x0)) a0 (avar_f (imm_substl_var l y0)))
          (imm_substl_trm l (trm_write (avar_f x0) a0 (avar_f y0)))
          (imm_substl_typ l T0) (imm_substl_typ l T0)
          (eq_sym (imm_substl_trm_write l x0 a0 y0)) eq_refl
          (@ty_trm_write typing_mode G' e0
             (imm_substl_var l x0) (imm_substl_var l y0) a0
             (imm_substl_typ l S0) (imm_substl_typ l T0)
             (fun Heq => Rv x0 (cx Heq))
             (fun Heq => Rv y0 (cy Heq))
             (fun Hm =>
                @imm_cast_var G' objctx_empty e0 (imm_substl_var l x0)
                  (imm_substl_typ l
                     (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability)
                                 typ_bot typ_bot)))
                  (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability)
                              typ_bot typ_bot))
                  (imm_eq_mut l)
                  (proj1 imm_ts_substl G0 objctx_empty e0 x0
                     (typ_rcd (dec_typ (typ_label_refcap typ_refcap_mutability)
                                 typ_bot typ_bot)) (om Hm) l G' Hfix Rb Rv))
             (@imm_cast_var G' objctx_empty e0 (imm_substl_var l x0)
                (imm_substl_typ l (typ_rcd (dec_fld a0 S0 T0)))
                (typ_rcd (dec_fld a0 (imm_substl_typ l S0) (imm_substl_typ l T0)))
                (imm_eq_rcd_fld l a0 S0 T0)
                (proj1 imm_ts_substl G0 objctx_empty e0 x0
                   (typ_rcd (dec_fld a0 S0 T0)) o0 l G' Hfix Rb Rv))
             (proj1 imm_ts_substl G0 objctx_empty e0 y0 S0 o1 l G' Hfix Rb Rv))
  | @ty_trm_call _ G0 e0 x0 y0 m0 TC0 TZ0 TR0 cx cy o o0 t0 o1 =>
      fun l G' Hfix Rb Rv =>
        @imm_cast_trm G' objctx_empty e0
          (trm_call (avar_f (imm_substl_var l x0)) m0 (avar_f (imm_substl_var l y0)))
          (imm_substl_trm l (trm_call (avar_f x0) m0 (avar_f y0)))
          (open_met (imm_substl_var l y0) (imm_substl_var l x0)
             (imm_substl_typ l TR0))
          (imm_substl_typ l (open_met y0 x0 TR0))
          (eq_sym (imm_substl_trm_call l x0 m0 y0))
          (eq_sym (@eq_trans typ
                    (open_rec 0 (imm_substl_var l y0)
                       (imm_substl_typ l (open_rec 1 x0 TR0)))
                    (imm_substl_typ l (open_rec 0 y0 (open_rec 1 x0 TR0)))
                    (open_rec 0 (imm_substl_var l y0)
                       (open_rec 1 (imm_substl_var l x0) (imm_substl_typ l TR0)))
                    (imm_substl_typ_open l 0 y0 (open_rec 1 x0 TR0))
                    (f_equal (fun Z => open_rec 0 (imm_substl_var l y0) Z)
                       (imm_substl_typ_open l 1 x0 TR0))))
          (@ty_trm_call typing_mode G' e0
             (imm_substl_var l x0) (imm_substl_var l y0) m0
             (imm_substl_typ l TC0) (imm_substl_typ l TZ0) (imm_substl_typ l TR0)
             (fun Heq => Rv x0 (cx Heq))
             (fun Heq => Rv y0 (cy Heq))
             (@imm_cast_var G' objctx_empty e0 (imm_substl_var l x0)
                (imm_substl_typ l (typ_rcd (dec_met m0 TC0 TZ0 TR0)))
                (typ_rcd (dec_met m0 (imm_substl_typ l TC0)
                            (imm_substl_typ l TZ0) (imm_substl_typ l TR0)))
                (imm_eq_rcd_met l m0 TC0 TZ0 TR0)
                (proj1 imm_ts_substl G0 objctx_empty e0 x0
                   (typ_rcd (dec_met m0 TC0 TZ0 TR0)) o l G' Hfix Rb Rv))
             (proj1 imm_ts_substl G0 objctx_empty e0 y0 TZ0 o0 l G' Hfix Rb Rv)
             (fun Hsef => @imm_typ_indep_b_substl l 0 TC0 (t0 Hsef))
             (@imm_cast_var G' objctx_empty e0 (imm_substl_var l x0)
                (imm_substl_typ l (open_rec 0 y0 TC0))
                (open_rec 0 (imm_substl_var l y0) (imm_substl_typ l TC0))
                (imm_substl_typ_open l 0 y0 TC0)
                (proj1 imm_ts_substl G0 objctx_empty e0 x0 (open_rec 0 y0 TC0) o1
                   l G' Hfix Rb Rv)))
  | @ty_trm_let _ L0 G0 e0 t0 u0 T0 U0 o o0 =>
      fun l G' Hfix Rb Rv =>
        @imm_cast_trm G' objctx_empty e0
          (trm_let (imm_substl_trm l t0) (imm_substl_trm l u0))
          (imm_substl_trm l (trm_let t0 u0))
          (imm_substl_typ l U0) (imm_substl_typ l U0)
          (eq_sym (imm_substl_trm_let l t0 u0)) eq_refl
          (@ty_trm_let typing_mode (L0 \u imm_pairs_fv l \u fv T0 \u fv U0 \u ctx_dom G0)
             G' e0 (imm_substl_trm l t0) (imm_substl_trm l u0)
             (imm_substl_typ l T0) (imm_substl_typ l U0)
             (@imm_trm_subst G0 objctx_empty e0 t0 T0 o l G' Hfix Rb Rv)
             (fun x HxL => ltac:(
                apply notin_union in HxL; destruct HxL as [HxL0 HxL];
                apply notin_union in HxL; destruct HxL as [Hxp HxL];
                apply notin_union in HxL; destruct HxL as [HxT HxL];
                apply notin_union in HxL; destruct HxL as [HxU HxG];
                destruct (imm_pick_fresh (dom e0 \u fv_env e0 \u imm_pairs_fv l
                           \u ctx_dom G0 \u ctx_fv G0 \u L0 \u fv T0 \u fv U0
                           \u fv u0 \u \{x})) as [w Hw];
                apply notin_union in Hw; destruct Hw as [Hwd Hw];
                apply notin_union in Hw; destruct Hw as [Hwf Hw];
                apply notin_union in Hw; destruct Hw as [Hwp Hw];
                apply notin_union in Hw; destruct Hw as [HwdG Hw];
                apply notin_union in Hw; destruct Hw as [HwfG Hw];
                apply notin_union in Hw; destruct Hw as [HwL0 Hw];
                apply notin_union in Hw; destruct Hw as [HwT Hw];
                apply notin_union in Hw; destruct Hw as [HwU Hw];
                apply notin_union in Hw; destruct Hw as [Hwu Hwx];
                apply notin_singleton in Hwx;
                assert (Hlw : forall a b, List.In (a, b) l -> w <> a /\ w <> b)
                  by (intros a b Hin; apply (@imm_pairs_fv_notin l w a b); [ exact Hwp | exact Hin ]);
                assert (Hfix' : imm_hfix e0 (cons (w, x) l))
                  by (intros a b Hin; destruct Hin as [E | Hin];
                      [ injection E as <- <-; split; assumption
                      | exact (Hfix a b Hin) ]);
                pose proof (@imm_rb_l_push_ren_ext l G0 G' w x v_let T0
                              Rb Hlw HwdG HwfG HxG Hxp) as Rb0;
                rewrite (@imm_substl_typ_ext_fresh l w x T0 HwT Hlw) in Rb0;
                pose proof (@imm_rv_l_push_ren_ext l G0 G' w x v_let T0
                              Rv Hlw HwdG HxG Hxp) as Rv0;
                rewrite (@imm_substl_typ_ext_fresh l w x T0 HwT Hlw) in Rv0;
                pose proof (@imm_trm_subst (G0 § w / v_let ~ T0) objctx_empty e0
                              (open_rec 0 w u0) U0 (o0 w HwL0)
                              (cons (w, x) l) (G' § x / v_let ~ imm_substl_typ l T0)
                              Hfix' Rb0 Rv0) as Hr;
                rewrite ((proj1 (@imm_substl_trm_open (cons (w, x) l) w)) u0 0) in Hr;
                rewrite (@imm_substl_var_ext_head l w x
                           (fun a b Hin => proj1 (Hlw a b Hin))) in Hr;
                rewrite (proj1 (@imm_substl_trm_ext_fresh l w x Hlw) u0 Hwu) in Hr;
                rewrite (@imm_substl_typ_ext_fresh l w x U0 HwU Hlw) in Hr;
                exact Hr)))
  | @ty_trm_lit _ L0 G0 e0 l0 u0 T0 U0 o o0 =>
      fun l G' Hfix Rb Rv =>
        @imm_cast_trm G' objctx_empty e0
          (trm_lit (imm_substl_lit l l0) (imm_substl_trm l u0))
          (imm_substl_trm l (trm_lit l0 u0))
          (imm_substl_typ l U0) (imm_substl_typ l U0)
          (eq_sym (imm_substl_trm_lit l l0 u0)) eq_refl
          (@ty_trm_lit typing_mode (L0 \u imm_pairs_fv l \u fv T0 \u fv U0 \u ctx_dom G0)
             G' e0 (imm_substl_lit l l0) (imm_substl_trm l u0)
             (imm_substl_typ l T0) (imm_substl_typ l U0)
             (@imm_lit_subst G0 objctx_empty e0 l0 T0 o l G' Hfix Rb Rv)
             (fun x HxL => ltac:(
                apply notin_union in HxL; destruct HxL as [HxL0 HxL];
                apply notin_union in HxL; destruct HxL as [Hxp HxL];
                apply notin_union in HxL; destruct HxL as [HxT HxL];
                apply notin_union in HxL; destruct HxL as [HxU HxG];
                destruct (imm_pick_fresh (dom e0 \u fv_env e0 \u imm_pairs_fv l
                           \u ctx_dom G0 \u ctx_fv G0 \u L0 \u fv T0 \u fv U0
                           \u fv u0 \u \{x})) as [w Hw];
                apply notin_union in Hw; destruct Hw as [Hwd Hw];
                apply notin_union in Hw; destruct Hw as [Hwf Hw];
                apply notin_union in Hw; destruct Hw as [Hwp Hw];
                apply notin_union in Hw; destruct Hw as [HwdG Hw];
                apply notin_union in Hw; destruct Hw as [HwfG Hw];
                apply notin_union in Hw; destruct Hw as [HwL0 Hw];
                apply notin_union in Hw; destruct Hw as [HwT Hw];
                apply notin_union in Hw; destruct Hw as [HwU Hw];
                apply notin_union in Hw; destruct Hw as [Hwu Hwx];
                apply notin_singleton in Hwx;
                assert (Hlw : forall a b, List.In (a, b) l -> w <> a /\ w <> b)
                  by (intros a b Hin; apply (@imm_pairs_fv_notin l w a b); [ exact Hwp | exact Hin ]);
                assert (Hfix' : imm_hfix e0 (cons (w, x) l))
                  by (intros a b Hin; destruct Hin as [E | Hin];
                      [ injection E as <- <-; split; assumption
                      | exact (Hfix a b Hin) ]);
                pose proof (@imm_rb_l_push_ren_ext l G0 G' w x v_let T0
                              Rb Hlw HwdG HwfG HxG Hxp) as Rb0;
                rewrite (@imm_substl_typ_ext_fresh l w x T0 HwT Hlw) in Rb0;
                pose proof (@imm_rv_l_push_ren_ext l G0 G' w x v_let T0
                              Rv Hlw HwdG HxG Hxp) as Rv0;
                rewrite (@imm_substl_typ_ext_fresh l w x T0 HwT Hlw) in Rv0;
                pose proof (@imm_trm_subst (G0 § w / v_let ~ T0) objctx_empty e0
                              (open_rec 0 w u0) U0 (o0 w HwL0)
                              (cons (w, x) l) (G' § x / v_let ~ imm_substl_typ l T0)
                              Hfix' Rb0 Rv0) as Hr;
                rewrite ((proj1 (@imm_substl_trm_open (cons (w, x) l) w)) u0 0) in Hr;
                rewrite (@imm_substl_var_ext_head l w x
                           (fun a b Hin => proj1 (Hlw a b Hin))) in Hr;
                rewrite (proj1 (@imm_substl_trm_ext_fresh l w x Hlw) u0 Hwu) in Hr;
                rewrite (@imm_substl_typ_ext_fresh l w x U0 HwU Hlw) in Hr;
                exact Hr)))
  | @ty_trm_sub _ G0 e0 t0 T0 U0 o s =>
      fun l G' Hfix Rb Rv =>
        @ty_trm_sub typing_mode G' e0
          (imm_substl_trm l t0) (imm_substl_typ l T0) (imm_substl_typ l U0)
          (@imm_trm_subst G0 objctx_empty e0 t0 T0 o l G' Hfix Rb Rv)
          (proj1 (proj2 imm_ts_substl) G0 objctx_empty e0 T0 U0 s
             l G' Hfix Rb Rv)
  end
with imm_lit_subst (G : ctx) (Go : objctx) (e : renv) (L : lit) (T : typ)
    (d : @ty_lit typing_mode G Go e L T) {struct d} :
  forall (l : list (var * var)) (G' : ctx),
    imm_hfix e l -> imm_rb_l l G G' -> imm_rv_l l G G' ->
    @ty_lit typing_mode G' Go e (imm_substl_lit l L) (imm_substl_typ l T) :=
  match d in @ty_lit _ Gi Goi ei Li Ti return
      (forall (l : list (var * var)) (G' : ctx),
          imm_hfix ei l -> imm_rb_l l Gi G' -> imm_rv_l l Gi G' ->
          @ty_lit typing_mode G' Goi ei
            (imm_substl_lit l Li) (imm_substl_typ l Ti))
  with
  | @ty_lit_fun _ L0 G0 e0 T0 t0 U0 Hfun o =>
      fun l G' Hfix Rb Rv =>
        @imm_cast_lit G' objctx_empty e0
          (lit_fun (imm_substl_typ l T0) (imm_substl_trm l t0))
          (imm_substl_lit l (lit_fun T0 t0))
          (typ_fun (imm_substl_typ l T0) (imm_substl_typ l U0))
          (imm_substl_typ l (typ_fun T0 U0))
          (eq_sym (imm_substl_lit_fun l T0 t0))
          (eq_sym (imm_substl_typ_fun l T0 U0))
          (@ty_lit_fun typing_mode (L0 \u imm_pairs_fv l \u fv T0 \u fv U0 \u ctx_dom G0)
             G' e0 (imm_substl_typ l T0) (imm_substl_trm l t0)
             (imm_substl_typ l U0) Hfun
             (fun x HxL => ltac:(
                apply notin_union in HxL; destruct HxL as [HxL0 HxL];
                apply notin_union in HxL; destruct HxL as [Hxp HxL];
                apply notin_union in HxL; destruct HxL as [HxT HxL];
                apply notin_union in HxL; destruct HxL as [HxU HxG];
                destruct (imm_pick_fresh (dom e0 \u fv_env e0 \u imm_pairs_fv l
                           \u ctx_dom G0 \u ctx_fv G0 \u L0 \u fv T0 \u fv U0
                           \u fv t0 \u \{x})) as [w Hw];
                apply notin_union in Hw; destruct Hw as [Hwd Hw];
                apply notin_union in Hw; destruct Hw as [Hwf Hw];
                apply notin_union in Hw; destruct Hw as [Hwp Hw];
                apply notin_union in Hw; destruct Hw as [HwdG Hw];
                apply notin_union in Hw; destruct Hw as [HwfG Hw];
                apply notin_union in Hw; destruct Hw as [HwL0 Hw];
                apply notin_union in Hw; destruct Hw as [HwT Hw];
                apply notin_union in Hw; destruct Hw as [HwU Hw];
                apply notin_union in Hw; destruct Hw as [Hwt Hwx];
                apply notin_singleton in Hwx;
                assert (Hlw : forall a b, List.In (a, b) l -> w <> a /\ w <> b)
                  by (intros a b Hin; apply (@imm_pairs_fv_notin l w a b); [ exact Hwp | exact Hin ]);
                assert (Hfix' : imm_hfix e0 (cons (w, x) l))
                  by (intros a b Hin; destruct Hin as [E | Hin];
                      [ injection E as <- <-; split; assumption
                      | exact (Hfix a b Hin) ]);
                pose proof (@imm_rb_l_push_ren_ext l G0 G' w x v_par T0
                              Rb Hlw HwdG HwfG HxG Hxp) as Rb0;
                rewrite (@imm_substl_typ_ext_fresh l w x T0 HwT Hlw) in Rb0;
                pose proof (@imm_rv_l_push_ren_ext l G0 G' w x v_par T0
                              Rv Hlw HwdG HxG Hxp) as Rv0;
                rewrite (@imm_substl_typ_ext_fresh l w x T0 HwT Hlw) in Rv0;
                pose proof (@imm_trm_subst (G0 § w / v_par ~ T0) objctx_empty e0
                              (open_rec 0 w t0) (open_rec 0 w U0) (o w HwL0)
                              (cons (w, x) l) (G' § x / v_par ~ imm_substl_typ l T0)
                              Hfix' Rb0 Rv0) as Hr;
                rewrite ((proj1 (@imm_substl_trm_open (cons (w, x) l) w)) t0 0) in Hr;
                rewrite (@imm_substl_typ_open (cons (w, x) l) 0 w U0) in Hr;
                rewrite (@imm_substl_var_ext_head l w x
                           (fun a b Hin => proj1 (Hlw a b Hin))) in Hr;
                rewrite (proj1 (@imm_substl_trm_ext_fresh l w x Hlw) t0 Hwt) in Hr;
                rewrite (@imm_substl_typ_ext_fresh l w x U0 HwU Hlw) in Hr;
                exact Hr)))
  | @ty_lit_obj _ L0 G0 e0 T0 ds0 o t0 =>
      fun l G' Hfix Rb Rv =>
        @imm_cast_lit G' objctx_empty e0
          (lit_obj (imm_substl_typ l T0) (imm_substl_defs l ds0))
          (imm_substl_lit l (lit_obj T0 ds0))
          (typ_objlit typing_mode (imm_substl_typ l T0))
          (imm_substl_typ l (typ_objlit typing_mode T0))
          (eq_sym (imm_substl_lit_obj l T0 ds0))
          (eq_sym (imm_substl_typ_objlit l T0))
          (@ty_lit_obj typing_mode
             (L0 \u imm_pairs_fv l \u fv T0 \u fv ds0 \u ctx_dom G0)
             G' e0 (imm_substl_typ l T0) (imm_substl_defs l ds0)
             (fun x HxL => ltac:(
                apply notin_union in HxL; destruct HxL as [HxL0 HxL];
                apply notin_union in HxL; destruct HxL as [Hxp HxL];
                apply notin_union in HxL; destruct HxL as [HxT HxL];
                apply notin_union in HxL; destruct HxL as [Hxds HxG];
                destruct (imm_pick_fresh (dom e0 \u fv_env e0 \u imm_pairs_fv l
                           \u ctx_dom G0 \u ctx_fv G0 \u L0 \u fv T0 \u fv ds0
                           \u \{x})) as [w Hw];
                apply notin_union in Hw; destruct Hw as [Hwd Hw];
                apply notin_union in Hw; destruct Hw as [Hwf Hw];
                apply notin_union in Hw; destruct Hw as [Hwp Hw];
                apply notin_union in Hw; destruct Hw as [HwdG Hw];
                apply notin_union in Hw; destruct Hw as [HwfG Hw];
                apply notin_union in Hw; destruct Hw as [HwL0 Hw];
                apply notin_union in Hw; destruct Hw as [HwT Hw];
                apply notin_union in Hw; destruct Hw as [Hwds Hwx];
                apply notin_singleton in Hwx;
                assert (Hlw : forall a b, List.In (a, b) l -> w <> a /\ w <> b)
                  by (intros a b Hin; apply (@imm_pairs_fv_notin l w a b);
                      [ exact Hwp | exact Hin ]);
                assert (Hfix' : imm_hfix e0 (cons (w, x) l))
                  by (intros a b Hin; destruct Hin as [E | Hin];
                      [ injection E as <- <-; split; assumption
                      | exact (Hfix a b Hin) ]);
                pose proof (@imm_rb_l_push_ren_ext l G0 G' w x v_self
                              (open_rec 0 w T0) Rb Hlw HwdG HwfG HxG Hxp) as Rb0;
                rewrite (@imm_substl_typ_open (cons (w, x) l) 0 w T0) in Rb0;
                rewrite (@imm_substl_var_ext_head l w x
                           (fun a b Hin => proj1 (Hlw a b Hin))) in Rb0;
                rewrite (@imm_substl_typ_ext_fresh l w x T0 HwT Hlw) in Rb0;
                change (imm_rb_l ((w, x) :: l) (ctx_obj G0 (objctx_lit w T0))
                          (ctx_obj G' (objctx_lit x (imm_substl_typ l T0)))) in Rb0;
                pose proof (@imm_rv_l_push_ren_ext l G0 G' w x v_self
                              (open_rec 0 w T0) Rv Hlw HwdG HxG Hxp) as Rv0;
                rewrite (@imm_substl_typ_open (cons (w, x) l) 0 w T0) in Rv0;
                rewrite (@imm_substl_var_ext_head l w x
                           (fun a b Hin => proj1 (Hlw a b Hin))) in Rv0;
                rewrite (@imm_substl_typ_ext_fresh l w x T0 HwT Hlw) in Rv0;
                change (imm_rv_l ((w, x) :: l) (ctx_obj G0 (objctx_lit w T0))
                          (ctx_obj G' (objctx_lit x (imm_substl_typ l T0)))) in Rv0;
                assert (Ego : objctx_lit x (imm_substl_typ l T0) =
                              imm_substl_objctx ((w, x) :: l) (objctx_lit w T0))
                  by (cbn [imm_substl_objctx];
                      rewrite (@imm_substl_var_ext_head l w x
                                 (fun a b Hin => proj1 (Hlw a b Hin))),
                              (@imm_substl_typ_ext_fresh l w x T0 HwT Hlw);
                      reflexivity);
                pose proof (@imm_defs_subst G0 (objctx_lit w T0) e0
                              (open_rec 0 w ds0) (open_rec 0 w T0)
                              (o w HwL0) (cons (w, x) l) G'
                              (objctx_lit x (imm_substl_typ l T0))
                              Ego Hfix' Rb0 Rv0) as Hr;
                rewrite ((proj2 (proj2 (proj2
                           (@imm_substl_trm_open (cons (w, x) l) w)))) ds0 0) in Hr;
                rewrite (@imm_substl_typ_open (cons (w, x) l) 0 w T0) in Hr;
                rewrite (@imm_substl_var_ext_head l w x
                           (fun a b Hin => proj1 (Hlw a b Hin))) in Hr;
                rewrite ((proj2 (proj2 (proj2
                           (@imm_substl_trm_ext_fresh l w x Hlw)))) ds0 Hwds) in Hr;
                rewrite (@imm_substl_typ_ext_fresh l w x T0 HwT Hlw) in Hr;
                exact Hr))
             (@imm_typ_indep_b_substl l 0 T0 t0))
  end
with imm_def_subst (G : ctx) (Go : objctx) (e : renv) (d : def) (D : dec)
    (dd : @ty_def typing_mode G Go e d D) {struct dd} :
  forall (l : list (var * var)) (G' : ctx) (Go' : objctx),
    Go' = imm_substl_objctx l Go -> imm_hfix e l ->
    imm_rb_l l (ctx_obj G Go) (ctx_obj G' Go') ->
    imm_rv_l l (ctx_obj G Go) (ctx_obj G' Go') ->
    @ty_def typing_mode G' Go' e (imm_substl_def l d) (imm_substl_dec l D) :=
  match dd in @ty_def _ Gi Goi ei di Di return
      (forall (l : list (var * var)) (G' : ctx) (Go' : objctx),
          Go' = imm_substl_objctx l Goi -> imm_hfix ei l ->
          imm_rb_l l (ctx_obj Gi Goi) (ctx_obj G' Go') ->
          imm_rv_l l (ctx_obj Gi Goi) (ctx_obj G' Go') ->
          @ty_def typing_mode G' Go' ei
            (imm_substl_def l di) (imm_substl_dec l Di))
  with
  | @ty_def_typ _ L0 G0 Go0 e0 A0 T0 U0 t0 =>
      fun l G' Go' Ego Hfix Rb Rv =>
        @imm_cast_def G' Go' e0
          (def_typ (typ_label_normal A0) (imm_substl_typ l T0))
          (imm_substl_def l (def_typ (typ_label_normal A0) T0))
          (dec_typ (typ_label_normal A0) (imm_substl_typ l U0)
             (imm_substl_typ l U0))
          (imm_substl_dec l (dec_typ (typ_label_normal A0) U0 U0))
          (eq_sym (imm_substl_def_typ l (typ_label_normal A0) T0))
          (eq_sym (imm_substl_dec_typ l (typ_label_normal A0) U0 U0))
          (@ty_def_typ typing_mode (L0 \u imm_pairs_fv l) G' Go' e0 A0
             (imm_substl_typ l T0) (imm_substl_typ l U0)
             (fun x HxL => ltac:(
                apply notin_union in HxL; destruct HxL as [HxL0 Hxp];
                assert (Hs : e0 ⊢ imm_substl_typ l (open_rec 0 x T0)
                                 ≈ imm_substl_typ l (open_rec 0 x U0))
                  by (apply (@imm_tyq_typ_substl e0
                               (open_rec 0 x T0) (open_rec 0 x U0));
                      [ exact (t0 x HxL0) | exact Hfix ]);
                rewrite (@imm_substl_typ_open l 0 x T0) in Hs;
                rewrite (@imm_substl_typ_open l 0 x U0) in Hs;
                rewrite (@imm_substl_var_notin_src l x
                           (fun z x' Hin =>
                              proj1 (@imm_pairs_fv_notin l x z x' Hxp Hin))) in Hs;
                exact Hs)))
  | @ty_def_fld _ G0 Go0 e0 a0 t0 T0 c o =>
      fun l G' Go' Ego Hfix Rb Rv =>
        @imm_cast_def G' Go' e0
          (def_fld a0 (avar_f (imm_substl_var l t0)))
          (imm_substl_def l (def_fld a0 (avar_f t0)))
          (dec_fld a0 (imm_substl_typ l T0) (imm_substl_typ l T0))
          (imm_substl_dec l (dec_fld a0 T0 T0))
          (eq_sym (imm_substl_def_fld l a0 t0))
          (eq_sym (imm_substl_dec_fld l a0 T0 T0))
          (@ty_def_fld typing_mode G' Go' e0 a0 (imm_substl_var l t0)
             (imm_substl_typ l T0)
             (fun Heq => Rv t0 (c Heq))
             (proj1 imm_ts_substl (ctx_obj G0 Go0) objctx_empty e0 t0 T0 o
                l (ctx_obj G' Go') Hfix Rb Rv))
  | @ty_def_met _ L0 G0 Go0 e0 m0 t0 TC0 TZ0 TR0 o =>
      fun l G' Go' Ego Hfix Rb Rv =>
        @imm_cast_def G' Go' e0
          (def_met m0 (imm_substl_trm l t0))
          (imm_substl_def l (def_met m0 t0))
          (dec_met m0 (imm_substl_typ l TC0) (imm_substl_typ l TZ0)
             (imm_substl_typ l TR0))
          (imm_substl_dec l (dec_met m0 TC0 TZ0 TR0))
          (eq_sym (imm_substl_def_met l m0 t0))
          (eq_sym (imm_substl_dec_met l m0 TC0 TZ0 TR0))
          (@ty_def_met typing_mode
             (L0 \u imm_pairs_fv l \u ctx_dom (ctx_obj G0 Go0)
                \u fv TZ0 \u fv TC0 \u fv TR0)
             G' Go' e0 m0 (imm_substl_trm l t0)
             (imm_substl_typ l TC0) (imm_substl_typ l TZ0)
             (imm_substl_typ l TR0)
             (fun xz HxzL xc Hcne HxcL => ltac:(
                apply notin_union in HxzL; destruct HxzL as [HxzL0 HxzL];
                apply notin_union in HxzL; destruct HxzL as [Hxzp HxzL];
                apply notin_union in HxzL; destruct HxzL as [Hxzd HxzL];
                apply notin_union in HxzL; destruct HxzL as [HxzTZ HxzL];
                apply notin_union in HxzL; destruct HxzL as [HxzTC HxzTR];
                apply notin_union in HxcL; destruct HxcL as [HxcL0 HxcL];
                apply notin_union in HxcL; destruct HxcL as [Hxcp HxcL];
                apply notin_union in HxcL; destruct HxcL as [Hxcd HxcL];
                apply notin_union in HxcL; destruct HxcL as [HxcTZ HxcL];
                apply notin_union in HxcL; destruct HxcL as [HxcTC HxcTR];
                assert (Hslvz : imm_substl_var l xz = xz)
                  by (apply imm_substl_var_notin_src; intros z x' Hin;
                      apply (proj1 (@imm_pairs_fv_notin l xz z x' Hxzp Hin)));
                assert (Hslvc : imm_substl_var l xc = xc)
                  by (apply imm_substl_var_notin_src; intros z x' Hin;
                      apply (proj1 (@imm_pairs_fv_notin l xc z x' Hxcp Hin)));
                pose proof (@imm_rb_l_ctx_obj_met_substl l G0 G' Go0 Go'
                              xz xc TZ0 TC0 Rb Ego Hxzd Hxzp Hxcd Hcne Hxcp)
                  as Rbm;
                pose proof (@imm_rv_l_ctx_obj_met_substl l G0 G' Go0 Go'
                              xz xc TZ0 TC0 Rv Ego Hxzd Hxzp Hxcd Hcne Hxcp)
                  as Rvm;
                pose proof (@imm_trm_subst
                              (ctx_obj_met typing_mode G0 Go0 xz TZ0 xc TC0)
                              objctx_empty e0
                              (open_met xz xc t0) (open_met xz xc TR0)
                              (o xz HxzL0 xc Hcne HxcL0) l
                              (ctx_obj_met typing_mode G' Go' xz
                                 (imm_substl_typ l TZ0) xc
                                 (imm_substl_typ l TC0))
                              Hfix Rbm Rvm) as Hr;
                rewrite ((proj1 (@imm_substl_trm_open l xz))
                           (open_rec 1 xc t0) 0) in Hr;
                rewrite ((proj1 (@imm_substl_trm_open l xc)) t0 1) in Hr;
                rewrite (@imm_substl_typ_open l 0 xz (open_rec 1 xc TR0)) in Hr;
                rewrite (@imm_substl_typ_open l 1 xc TR0) in Hr;
                rewrite Hslvz in Hr;
                rewrite Hslvc in Hr;
                exact Hr)))
  end
with imm_defs_subst (G : ctx) (Go : objctx) (e : renv) (ds : defs) (T : typ)
    (dd : @ty_defs typing_mode G Go e ds T) {struct dd} :
  forall (l : list (var * var)) (G' : ctx) (Go' : objctx),
    Go' = imm_substl_objctx l Go -> imm_hfix e l ->
    imm_rb_l l (ctx_obj G Go) (ctx_obj G' Go') ->
    imm_rv_l l (ctx_obj G Go) (ctx_obj G' Go') ->
    @ty_defs typing_mode G' Go' e (imm_substl_defs l ds) (imm_substl_typ l T) :=
  match dd in @ty_defs _ Gi Goi ei dsi Ti return
      (forall (l : list (var * var)) (G' : ctx) (Go' : objctx),
          Go' = imm_substl_objctx l Goi -> imm_hfix ei l ->
          imm_rb_l l (ctx_obj Gi Goi) (ctx_obj G' Go') ->
          imm_rv_l l (ctx_obj Gi Goi) (ctx_obj G' Go') ->
          @ty_defs typing_mode G' Go' ei
            (imm_substl_defs l dsi) (imm_substl_typ l Ti))
  with
  | @ty_defs_one _ G0 Go0 e0 d0 D0 o =>
      fun l G' Go' Ego Hfix Rb Rv =>
        @imm_cast_defs G' Go' e0
          (defs_cons defs_nil (imm_substl_def l d0))
          (imm_substl_defs l (defs_cons defs_nil d0))
          (typ_rcd (imm_substl_dec l D0))
          (imm_substl_typ l (typ_rcd D0))
          (eq_sym (@eq_trans defs
                    (defs_cons (imm_substl_defs l defs_nil) (imm_substl_def l d0))
                    (imm_substl_defs l (defs_cons defs_nil d0))
                    (defs_cons defs_nil (imm_substl_def l d0))
                    (imm_substl_defs_cons l defs_nil d0)
                    (f_equal (fun X => defs_cons X (imm_substl_def l d0))
                       (imm_substl_defs_nil l))))
          (eq_sym (imm_substl_typ_rcd l D0))
          (@ty_defs_one typing_mode G' Go' e0 (imm_substl_def l d0)
             (imm_substl_dec l D0) (@imm_def_subst G0 Go0 e0 d0 D0 o l G' Go' Ego Hfix Rb Rv))
  | @ty_defs_cons _ G0 Go0 e0 ds0 d0 T0 D0 o o0 d1 =>
      fun l G' Go' Ego Hfix Rb Rv =>
        @imm_cast_defs G' Go' e0
          (defs_cons (imm_substl_defs l ds0) (imm_substl_def l d0))
          (imm_substl_defs l (defs_cons ds0 d0))
          (typ_and (imm_substl_typ l T0) (typ_rcd (imm_substl_dec l D0)))
          (imm_substl_typ l (typ_and T0 (typ_rcd D0)))
          (eq_sym (imm_substl_defs_cons l ds0 d0))
          (eq_sym (@eq_trans typ
                    (typ_and (imm_substl_typ l T0) (imm_substl_typ l (typ_rcd D0)))
                    (imm_substl_typ l (typ_and T0 (typ_rcd D0)))
                    (typ_and (imm_substl_typ l T0) (typ_rcd (imm_substl_dec l D0)))
                    (imm_substl_typ_and l T0 (typ_rcd D0))
                    (f_equal (fun X => typ_and (imm_substl_typ l T0) X)
                       (imm_substl_typ_rcd l D0))))
          (@ty_defs_cons typing_mode G' Go' e0
             (imm_substl_defs l ds0) (imm_substl_def l d0)
             (imm_substl_typ l T0) (imm_substl_dec l D0)
             (@imm_defs_subst G0 Go0 e0 ds0 T0 o l G' Go' Ego Hfix Rb Rv)
             (@imm_def_subst G0 Go0 e0 d0 D0 o0 l G' Go' Ego Hfix Rb Rv)
             (@imm_defs_hasnt_substl l ds0 d0 d1))
  end.

(* In the mutable modes, capability correspondence relates a mutable marker
   with the bottom-refined marker, which is a subtype of it. *)
Lemma imm_mode_refcap_corr_mut :
  mode_refcap_corr' typing_mode = mode_refcap_corr_ref_mutability.
Proof. destruct typing_mode; cbn in *; try discriminate; reflexivity. Qed.

Lemma imm_mode_has_fun_false : mode_has_fun' typing_mode = false.
Proof. destruct typing_mode; cbn in *; try discriminate; reflexivity. Qed.

Lemma imm_typ_corr_mut (Tw Ty : typ) :
  typ_corr Tw Ty ->
  exists (T Tbnd : typ),
    Tw = typ_objref T (typ_mut_marker Tbnd) /\
    Ty = typ_objref T (typ_mut_marker typ_bot).
Proof.
  intros H. inversion H as [T S U Hcorr | t1 t2 Hfun]; subst.
  - rewrite imm_mode_refcap_corr_mut in Hcorr. cbn in Hcorr.
    destruct Hcorr as (Tbnd & ES & EU). subst S U.
    exists T, Tbnd. split; reflexivity.
  - rewrite imm_mode_has_fun_false in Hfun. discriminate Hfun.
Qed.

(* The object-shaped capability is a subtype of the source-shaped one. *)
Lemma imm_objref_corr_subtyp (G : ctx) (e : renv) (T Tw Ty : typ) :
  @subtyp typing_mode G objctx_empty e Ty Tw ->
  @subtyp typing_mode G objctx_empty e (typ_objref T Ty) (typ_objref T Tw).
Proof.
  intros H. eapply subtyp_and2.
  - apply subtyp_and11.
  - eapply subtyp_trans; [ apply subtyp_and12 | exact H ].
Qed.

Lemma imm_typ_corr_subtyp (G : ctx) (e : renv) (Tw Ty : typ) :
  typ_corr Tw Ty ->
  @subtyp typing_mode G objctx_empty e Ty Tw.
Proof.
  intros H. destruct (@imm_typ_corr_mut Tw Ty H)
    as (T & Tbnd & Ew & Ey).
  subst Tw Ty.
  apply imm_objref_corr_subtyp.
  eapply subtyp_typ.
  - intros y. apply subtyp_refl.
  - intros y. apply subtyp_bot.
Qed.

(* Dereferencing definitions preserves labels and field lookups. *)
Lemma imm_label_of_deref_def (e : renv) (d : def) :
  label_of (deref e d) = label_of d.
Proof. destruct d; reflexivity. Qed.

Lemma imm_get_def_deref_defs (e : renv) (ds : defs) (l : label) :
  get_def l (deref e ds) = option_map (deref e) (get_def l ds).
Proof.
  induction ds as [|ds IH d].
  - reflexivity.
  - destruct d as [L T | a v0 | m t]; cbn.
    + destruct (classic (label_typ L = l)) as [E | E].
      * rewrite (If_l (A:=option def) (P:=label_typ L = l)
                   (Some (def_typ L T)) (get_def l (deref e ds))) by exact E.
        rewrite (If_l (A:=option def) (P:=label_typ L = l)
                   (Some (def_typ L T)) (get_def l ds)) by exact E.
        cbn; reflexivity.
      * rewrite (If_r (A:=option def) (P:=label_typ L = l)
                   (Some (def_typ L T)) (get_def l (deref e ds))) by exact E.
        rewrite (If_r (A:=option def) (P:=label_typ L = l)
                   (Some (def_typ L T)) (get_def l ds)) by exact E.
        exact IH.
    + destruct (classic (label_fld a = l)) as [E | E].
      * rewrite (If_l (A:=option def) (P:=label_fld a = l)
                   (Some (def_fld a (deref e v0)))
                   (get_def l (deref e ds))) by exact E.
        rewrite (If_l (A:=option def) (P:=label_fld a = l)
                   (Some (def_fld a v0)) (get_def l ds)) by exact E.
        cbn; reflexivity.
      * rewrite (If_r (A:=option def) (P:=label_fld a = l)
                   (Some (def_fld a (deref e v0)))
                   (get_def l (deref e ds))) by exact E.
        rewrite (If_r (A:=option def) (P:=label_fld a = l)
                   (Some (def_fld a v0)) (get_def l ds)) by exact E.
        exact IH.
    + destruct (classic (label_met m = l)) as [E | E].
      * rewrite (If_l (A:=option def) (P:=label_met m = l)
                   (Some (def_met m t)) (get_def l (deref e ds))) by exact E.
        rewrite (If_l (A:=option def) (P:=label_met m = l)
                   (Some (def_met m t)) (get_def l ds)) by exact E.
        cbn; reflexivity.
      * rewrite (If_r (A:=option def) (P:=label_met m = l)
                   (Some (def_met m t)) (get_def l (deref e ds))) by exact E.
        rewrite (If_r (A:=option def) (P:=label_met m = l)
                   (Some (def_met m t)) (get_def l ds)) by exact E.
        exact IH.
Qed.

Lemma imm_defs_has_deref (e : renv) (ds : defs) (d : def) :
  defs_has ds d -> defs_has (deref e ds) (deref e d).
Proof.
  intros H. unfold defs_has in *.
  rewrite imm_label_of_deref_def, imm_get_def_deref_defs, H. reflexivity.
Qed.

Lemma imm_get_def_deref_defs_notin (e : renv) (ds : defs) (l : label) :
  get_def l ds = None -> get_def l (deref e ds) = None.
Proof.
  intros H. rewrite imm_get_def_deref_defs. rewrite H. reflexivity.
Qed.

(* Updating a field preserves lookups of all other fields, and the updated
   field itself becomes the new value. *)
Lemma imm_get_def_defs_update_neq (ds ds' : defs) (a : fld_label) (y : var)
      (l : label) :
  defs_update ds a y ds' -> label_fld a <> l ->
  get_def l ds' = get_def l ds.
Proof.
  intros Hu Hne. induction Hu as [ds0 a0 t0 x | ds0 d0 a0 x0 ds0' Hrec IHfun Hneq].
  - cbn.
    rewrite (If_r (A:=option def) (P:=label_fld a0 = l)
               (Some (def_fld a0 (avar_f x))) (get_def l ds0)) by exact Hne.
    rewrite (If_r (A:=option def) (P:=label_fld a0 = l)
               (Some (def_fld a0 t0)) (get_def l ds0)) by exact Hne.
    reflexivity.
  - cbn.
    destruct (classic (label_of d0 = l)) as [E | E].
    + rewrite (If_l (A:=option def) (P:=label_of d0 = l) (Some d0)
                 (get_def l ds0')) by exact E.
      rewrite (If_l (A:=option def) (P:=label_of d0 = l) (Some d0)
                 (get_def l ds0)) by exact E.
      reflexivity.
    + rewrite (If_r (A:=option def) (P:=label_of d0 = l) (Some d0)
                 (get_def l ds0')) by exact E.
      rewrite (If_r (A:=option def) (P:=label_of d0 = l) (Some d0)
                 (get_def l ds0)) by exact E.
      exact (IHfun Hne).
Qed.

Lemma imm_get_def_defs_update_eq (ds ds' : defs) (a : fld_label) (y : var) :
  defs_update ds a y ds' ->
  get_def (label_fld a) ds' = Some (def_fld a (avar_f y)).
Proof.
  intros Hu. induction Hu as [ds0 a0 t0 x | ds0 d0 a0 x0 ds0' Hrec IHfun Hneq].
  - cbn. rewrite If_l by reflexivity. reflexivity.
  - cbn.
    rewrite (If_r (A:=option def) (P:=label_of d0 = label_fld a0)
               (Some d0) (get_def (label_fld a0) ds0')) by exact Hneq.
    exact IHfun.
Qed.

(* ---------- small decompositions used by subject reduction ---------- *)

Lemma imm_fv_config_let_push_lr (a b : trm) (fs : stack) (Sigma : heap)
      (e : renv) (Lv : fset var) :
  fv_config (trm_let a b ; fs ; Sigma ; e ; Lv) \c
  fv_config (a ; stack_cons (frame_let b) fs ; Sigma ; e ; Lv).
Proof.
  intros x Hx. cbn in *. repeat rewrite in_union in *. tauto.
Qed.

Lemma imm_fv_config_let_push_rl (a b : trm) (fs : stack) (Sigma : heap)
      (e : renv) (Lv : fset var) :
  fv_config (a ; stack_cons (frame_let b) fs ; Sigma ; e ; Lv) \c
  fv_config (trm_let a b ; fs ; Sigma ; e ; Lv).
Proof.
  intros x Hx. cbn in *. repeat rewrite in_union in *. tauto.
Qed.

Lemma imm_closed_trm_let_l (a b : trm) :
  closed (trm_let a b) -> closed a.
Proof.
  intros H n x. specialize (H n x). cbn in H. injection H as E _. exact E.
Qed.

Lemma imm_frame_open_let n x (t : trm) :
  open_rec n x (frame_let t) = frame_let (open_rec n x t).
Proof. reflexivity. Qed.

Lemma imm_stack_open_cons n x (f : frame) (fs : stack) :
  open_rec n x (stack_cons f fs) =
  stack_cons (open_rec (S n) x f) (open_rec n x fs).
Proof. reflexivity. Qed.

Lemma imm_closed_stack_cons_of_let (a b : trm) (fs : stack) :
  closed (trm_let a b) -> closed fs ->
  closed (stack_cons (frame_let b) fs).
Proof.
  intros H Hfs n x. rewrite imm_stack_open_cons, imm_frame_open_let.
  specialize (H n x). cbn in H. injection H as _ Eb.
  rewrite Eb, (Hfs n x). reflexivity.
Qed.

(* Subject reduction for the let-push step. *)
Lemma imm_ty_config_red_let_push (F : ctx) (T : typ)
    (s t : trm) (fs : stack) (Sigma : heap) (e : renv) (Lv : fset var) :
  @ty_config typing_mode F (trm_let s t ; fs ; Sigma ; e ; Lv) T ->
  @ty_config typing_mode F (s ; stack_cons (frame_let t) fs ; Sigma ; e ; Lv) T.
Proof.
  intros Hty. inversion Hty as
    [ G0 e0 s0 Sigma0 Lv0 t0 T0 U0
      Hinert Hcorr Hstk Htfk Ht Htf Hnf Hnull Hseal Hcl HclU ]; subst.
  destruct (@imm_stack_push_let F e s t fs T0 T Hstk Ht) as (S & Ha & Hstk').
  eapply ty_config_c.
  - exact Hinert.
  - exact Hcorr.
  - exact Hstk'.
  - destruct (@imm_all_tfree_k_let F s t v_ref Htf) as [Hsa Hta].
    eapply imm_all_tfree_k_stack_cons; [ exact Hta | exact Htfk ].
  - exact Ha.
  - destruct (@imm_all_tfree_k_let F s t v_ref Htf) as [Hsa Hta].
    exact Hsa.
  - destruct Hnf as [Hnf1 Hnf2]. split.
    + destruct Hnf1 as [Hdom HnfG]. split.
      * eapply imm_subset_trans; [ exact Hdom | apply imm_fv_config_let_push_lr ].
      * unfold nothing_fresh_in_config in *. eapply imm_subset_trans;
          [ exact HnfG | apply imm_fv_config_let_push_lr ].
    + unfold nothing_fresh_in_config in *. eapply imm_subset_trans;
        [ exact Hnf2 | apply imm_fv_config_let_push_lr ].
  - exact Hnull.
  - exact Hseal.
  - inversion Hcl as [t1 s1 Sigma1 e1 Lv1 Hct Hcs Hch]; subst.
    eapply config_sealed_cfg.
    + eapply imm_closed_trm_let_l. exact Hct.
    + eapply imm_closed_stack_cons_of_let; [ exact Hct | exact Hcs ].
    + exact Hch.
  - exact HclU.
Qed.

(* ---------- removing one specific binder (with its type remembered) ---------- *)

Inductive imm_ctx_ext : var -> typ -> ctx -> ctx -> Prop :=
| imm_ctx_ext_top G x vk T :
    imm_ctx_ext x T (G § x / vk ~ T) G
| imm_ctx_ext_push G1 G2 x T y vk S :
    imm_ctx_ext x T G1 G2 ->
    imm_ctx_ext x T (G1 § y / vk ~ S) (G2 § y / vk ~ S)
| imm_ctx_ext_stop G1 G2 x T :
    imm_ctx_ext x T G1 G2 ->
    imm_ctx_ext x T (ctx_stop G1) (ctx_stop G2)
| imm_ctx_ext_hide G1 G2 x T :
    imm_ctx_ext x T G1 G2 ->
    imm_ctx_ext x T (ctx_hide G1) (ctx_hide G2).

(* Any binding in the larger context is either already present in the smaller
   one, or is exactly the removed binder. *)
Lemma imm_ctx_ext_binds (x T : typ) (x0 : var) (H G : ctx) :
  imm_ctx_ext x0 T H G ->
  forall v V, ctx_binds v V H ->
    ctx_binds v V G \/ (v = x0 /\ V = T).
Proof.
  intros Hext. induction Hext as
    [ G0 x1 vk T0 | G1 G2 x1 T1 y vk S Hext IH
    | G1 G2 x1 T1 Hext IH | G1 G2 x1 T1 Hext IH ];
    intros v V Hb.
  - inversion Hb; subst.
    + right. split; reflexivity.
    + left. assumption.
  - inversion Hb; subst.
    + left. apply ctx_binds_e.
    + match goal with Hbb : ctx_binds v V G1 |- _ =>
        destruct (IH v V Hbb) as [Hg | [Ev EV]];
        [ left; eapply ctx_binds_n; [ eassumption | exact Hg ]
        | right; split; assumption ] end.
  - inversion Hb.
  - inversion Hb; subst.
    match goal with Hbb : ctx_binds v V G1 |- _ =>
      destruct (IH v V Hbb) as [Hg | [Ev EV]];
      [ left; apply ctx_binds_hide; exact Hg
      | right; split; assumption ] end.
Qed.

Lemma imm_ctx_ext_vis (x T : typ) (x0 : var) (H G : ctx) :
  imm_ctx_ext x0 T H G ->
  forall v, ctx_vis H v -> ctx_vis G v \/ v = x0.
Proof.
  intros Hext. induction Hext as
    [ G0 x1 vk T0 | G1 G2 x1 T1 y vk S Hext IH
    | G1 G2 x1 T1 Hext IH | G1 G2 x1 T1 Hext IH ];
    intros v Hv.
  - inversion Hv; subst.
    + right. reflexivity.
    + left. assumption.
  - inversion Hv; subst.
    + left. apply ctx_vis_e.
    + match goal with Hvv : ctx_vis G1 v |- _ =>
        destruct (IH v Hvv) as [Hg | E];
        [ left; eapply ctx_vis_n; [ eassumption | exact Hg ]
        | right; exact E ] end.
  - inversion Hv.
  - inversion Hv.
Qed.

(* A context extension, represented as binders pushed outermost-first. *)
Fixpoint imm_ctx_plug (E : list (var * varkind * typ)) (G : ctx) : ctx :=
  match E with
  | nil => G
  | cons ((y, vk), S0) E' => imm_ctx_plug E' G § y / vk ~ S0
  end.

(* Bindings transfer when one binder is removed from under an extension,
   using the typing of the removed variable at the base context. *)
Lemma imm_ctx_plug_binds_var (e : renv)
      (E : list (var * varkind * typ)) (B : ctx)
      (x0 : var) (vk : varkind) (T0 : typ) :
  @ty_var typing_mode B objctx_empty e x0 T0 ->
  forall v V,
    ctx_binds v V (imm_ctx_plug E (B § x0 / vk ~ T0)) ->
    @ty_var typing_mode (imm_ctx_plug E B) objctx_empty e v V.
Proof.
  intros Hx. induction E as [| ((y, vk0), S0) E' IH]; intros v V Hb.
  - cbn in Hb. inversion Hb; subst.
    + exact Hx.
    + apply ty_var_var. exact H1.
  - cbn in Hb. inversion Hb; subst.
    + apply ty_var_var. apply ctx_binds_e.
    + apply ty_var_var. eapply ctx_binds_n; [ eassumption | ].
      specialize (IH v V H1). inversion IH; subst. assumption.
Qed.

(* Visibility transfers the same way, using the visibility of the removed
   variable at the base context. *)
Lemma imm_ctx_plug_vis (B : ctx) (x0 : var) (vk : varkind) (T0 : typ) :
  ctx_vis B x0 ->
  forall (E : list (var * varkind * typ)) (v : var),
    ctx_vis (imm_ctx_plug E (B § x0 / vk ~ T0)) v ->
    ctx_vis (imm_ctx_plug E B) v.
Proof.
  intros Hvis. induction E as [| ((y, vk0), S0) E' IH]; intros v Hv.
  - cbn in Hv. inversion Hv; subst.
    + exact Hvis.
    + assumption.
  - cbn in Hv. inversion Hv; subst.
    + apply ctx_vis_e.
    + apply ctx_vis_n; [ eassumption | apply IH; exact H1 ].
Qed.

Theorem immutability_guarantee t1 s1 S1 e1 Lv1 F T n t2 s2 S2 e2 Lv2 y ds:
    binds y (item_obj ds) S1 ->
    ty_config F (t1 ; s1 ; S1 ; e1; Lv1) T ->
    (t1 ; s1 ; S1 ; e1; Lv1) ⊣ n ↦* (t2 ; s2 ; S2 ; e2; Lv2) -> (
      binds y (item_obj ds) S2 \/
      F ⊢ (t1 ; s1 ; S1 ; e1; Lv1) mreach y
    ).

End WithRodotMode.
