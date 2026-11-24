Set Implicit Arguments.

Require Import Coq.Program.Equality List String.

Require Import Sequences.

Require Import Binding Definitions Lookup Reduction PreciseTyping RecordAndInertTypes TightTyping.

Close Scope string_scope.

Section Safety.

Reserved Notation "x '==>' T '=' bs '=>' U" (at level 40, T at level 20).

Inductive lookup_fields_typ : var -> typ -> list trm_label -> typ -> Prop :=
| lft_empty : forall x T,
    x ==> T =nil=> T
| lft_cons : forall T bs U x a S,
    x ==> T =bs=> μ U ->
    record_has (open_typ_p (p_sel (avar_f x) bs) U) {a ⦂ S} ->
    x ==> T =a::bs=> S

where "x '==>' T '=' bs '=>' U" := (lookup_fields_typ x T bs U).

Local Hint Constructors ty_trm ty_def ty_defs subtyp : pdot.

(* Typing is stable under inclusion of bindings. *)
Definition ctx_incl (G H : ctx) :=
  forall x T, binds x T G -> binds x T H.

Lemma ctx_incl_push G H x T :
  ctx_incl G H -> ctx_incl (G & x ~ T) (H & x ~ T).
Proof.
  intros I y U B. apply binds_push_inv in B as [[-> ->]|[N B]].
  - apply binds_push_eq.
  - apply binds_push_neq; auto.
Qed.

Lemma weakening_all :
  (forall G t T, G ⊢ t : T -> forall H, ctx_incl G H -> H ⊢ t : T) /\
  (forall x bs G d D, x; bs; G ⊢ d : D ->
    forall H, ctx_incl G H -> x; bs; H ⊢ d : D) /\
  (forall x bs G ds T, x; bs; G ⊢ ds :: T ->
    forall H, ctx_incl G H -> x; bs; H ⊢ ds :: T) /\
  (forall G S T, G ⊢ S <: T -> forall H, ctx_incl G H -> H ⊢ S <: T).
Proof.
  apply tds_mutind; intros;
    eauto 7 using ctx_incl_push with pdot.
Qed.

Lemma typing_weaken G H t T :
  G ⊢ t : T -> ctx_incl G H -> H ⊢ t : T.
Proof. intros; eapply (proj1 weakening_all); eauto. Qed.

Lemma defs_weaken x bs G H ds T :
  x; bs; G ⊢ ds :: T -> ctx_incl G H -> x; bs; H ⊢ ds :: T.
Proof. intros; eapply (proj1 (proj2 (proj2 weakening_all))); eauto. Qed.

Lemma ctx_incl_fresh G x T :
  x # G -> ctx_incl G (G & x ~ T).
Proof.
  intros F y U B. apply binds_push_neq; auto.
  intro E; subst. eapply binds_fresh_inv; eauto.
Qed.

Lemma sel_fields_assoc p bs cs :
  (p••bs)••cs = p••(cs ++ bs).
Proof. destruct p; cbn. rewrite app_assoc. reflexivity. Qed.

Lemma sel_fields_nil p : p••nil = p.
Proof. now destruct p. Qed.

Lemma subst_sel_fields z q p bs :
  subst_path z q (p••bs) = (subst_path z q p)••bs.
Proof. destruct p as [x cs]; cbn [subst_path sel_fields]; destruct (subst_avar z q x); cbn. now rewrite app_assoc. Qed.

Lemma subst_sel_field z q p a :
  subst_path z q (p•a) = (subst_path z q p)•a.
Proof. apply (subst_sel_fields z q p (a::nil)).
Qed.

Lemma subst_pvar_same z p : subst_path z p (pvar z) = p.
Proof.
  cbn [subst_path subst_avar subst_var_p].
  unfold subst_var_p. destruct (classicT (z = z)); [apply sel_fields_nil | contradiction].
Qed.

Lemma subst_pvar_other z p x :
  x <> z -> subst_path z p (pvar x) = pvar x.
Proof.
  intro N. cbn [subst_path subst_avar subst_var_p].
  unfold subst_var_p. destruct (classicT (x = z)); [contradiction | reflexivity].
Qed.

Lemma open_path_var k x p : open_rec_path k x p = open_rec_path_p k (pvar x) p.
Proof.
  destruct p as [[i|y] bs]; cbn; auto.
  destruct (classicT (k = i)); simpl; now rewrite ?app_nil_r.
Qed.

Lemma open_typ_var_mut :
  (forall T k x, open_rec_typ k x T = open_rec_typ_p k (pvar x) T) /\
  (forall D k x, open_rec_dec k x D = open_rec_dec_p k (pvar x) D).
Proof.
  apply typ_mutind; intros; cbn; f_equal; auto using open_path_var.
Qed.

Lemma open_trm_var_mut :
  (forall t k x, open_rec_trm k x t = open_rec_trm_p k (pvar x) t) /\
  (forall v k x, open_rec_val k x v = open_rec_val_p k (pvar x) v) /\
  (forall d k x, open_rec_def k x d = open_rec_def_p k (pvar x) d) /\
  (forall ds k x, open_rec_defs k x ds = open_rec_defs_p k (pvar x) ds) /\
  (forall r k x, open_rec_defrhs k x r = open_rec_defrhs_p k (pvar x) r).
Proof.
  apply trm_mutind; intros; cbn; f_equal; auto using open_path_var,
    (proj1 open_typ_var_mut).
Qed.

Lemma open_typ_var x T : open_typ x T = open_typ_p (pvar x) T.
Proof. apply (proj1 open_typ_var_mut). Qed.
Lemma open_trm_var x t : open_trm x t = open_trm_p (pvar x) t.
Proof. apply (proj1 open_trm_var_mut). Qed.
Lemma open_defs_var x ds : open_defs x ds = open_defs_p (pvar x) ds.
Proof. apply (proj1 (proj2 (proj2 (proj2 open_trm_var_mut)))). Qed.

Lemma subst_bpath z q i bs : subst_path z q (p_sel (avar_b i) bs) = p_sel (avar_b i) bs.
Proof. cbn. now rewrite app_nil_r. Qed.

Lemma subst_open_path k z q p r :
  named_path q ->
  subst_path z q (open_rec_path_p k p r) =
  open_rec_path_p k (subst_path z q p) (subst_path z q r).
Proof.
  intros [x [cs ->]]. destruct r as [[i|y] bs]; destruct p as [u ds].
  - rewrite subst_bpath. cbn [open_rec_path_p].
    destruct (classicT (k = i)) eqn:E.
    + exact (subst_sel_fields z (p_sel (avar_f x) cs) (p_sel u ds) bs).
    + rewrite subst_bpath. destruct (subst_path z (p_sel (avar_f x) cs) (p_sel u ds)); reflexivity.
  - cbn [open_rec_path_p subst_path subst_avar sel_fields].
    unfold subst_var_p. destruct (classicT (y = z));
      destruct (subst_avar z (p_sel (avar_f x) cs) u); reflexivity.
Qed.

Lemma subst_open_typ_mut z q (N : named_path q) :
  (forall T k p, subst_typ z q (open_rec_typ_p k p T) =
        open_rec_typ_p k (subst_path z q p) (subst_typ z q T)) /\
  (forall D k p, subst_dec z q (open_rec_dec_p k p D) =
        open_rec_dec_p k (subst_path z q p) (subst_dec z q D)).
Proof.
  apply typ_mutind; intros; cbn; f_equal; auto using subst_open_path.
Qed.

Lemma subst_open_trm_mut z q (N : named_path q) :
  (forall t k p, subst_trm z q (open_rec_trm_p k p t) =
        open_rec_trm_p k (subst_path z q p) (subst_trm z q t)) /\
  (forall v k p, subst_val z q (open_rec_val_p k p v) =
        open_rec_val_p k (subst_path z q p) (subst_val z q v)) /\
  (forall d k p, subst_def z q (open_rec_def_p k p d) =
        open_rec_def_p k (subst_path z q p) (subst_def z q d)) /\
  (forall ds k p, subst_defs z q (open_rec_defs_p k p ds) =
        open_rec_defs_p k (subst_path z q p) (subst_defs z q ds)) /\
  (forall r k p, subst_defrhs z q (open_rec_defrhs_p k p r) =
        open_rec_defrhs_p k (subst_path z q p) (subst_defrhs z q r)).
Proof.
  apply trm_mutind; intros; cbn; f_equal; auto using subst_open_path,
    (proj1 (subst_open_typ_mut z N)).
Qed.

Lemma subst_open_typ z q p T :
  named_path q -> subst_typ z q (open_typ_p p T) =
    open_typ_p (subst_path z q p) (subst_typ z q T).
Proof. intro N; apply (proj1 (subst_open_typ_mut z N)). Qed.
Lemma subst_open_trm z q p t :
  named_path q -> subst_trm z q (open_trm_p p t) =
    open_trm_p (subst_path z q p) (subst_trm z q t).
Proof. intro N; apply (proj1 (subst_open_trm_mut z N)). Qed.
Lemma subst_open_defs z q p ds :
  named_path q -> subst_defs z q (open_defs_p p ds) =
    open_defs_p (subst_path z q p) (subst_defs z q ds).
Proof. intro N; apply (proj1 (proj2 (proj2 (proj2 (subst_open_trm_mut z N))))). Qed.

Lemma subst_path_fresh z q p :
  z \notin fv_path p -> subst_path z q p = p.
Proof.
  destruct p as [[i|x] bs]; cbn.
  - now rewrite app_nil_r.
  - rewrite notin_singleton. intro N.
    unfold subst_var_p. destruct (classicT (x = z)); [congruence | now cbn; rewrite app_nil_r].
Qed.

Lemma subst_typ_fresh_mut z q :
  (forall T, z \notin fv_typ T -> subst_typ z q T = T) /\
  (forall D, z \notin fv_dec D -> subst_dec z q D = D).
Proof.
  apply typ_mutind; intros; cbn in *;
    repeat match goal with H : _ \notin _ \u _ |- _ => apply notin_union in H as [? ?] end;
    f_equal; auto using subst_path_fresh.
Qed.

Lemma subst_trm_fresh_mut z q :
  (forall t, z \notin fv_trm t -> subst_trm z q t = t) /\
  (forall v, z \notin fv_val v -> subst_val z q v = v) /\
  (forall d, z \notin fv_def d -> subst_def z q d = d) /\
  (forall ds, z \notin fv_defs ds -> subst_defs z q ds = ds) /\
  (forall r, z \notin fv_defrhs r -> subst_defrhs z q r = r).
Proof.
  apply trm_mutind; intros; cbn in *;
    repeat match goal with H : _ \notin _ \u _ |- _ => apply notin_union in H as [? ?] end;
    f_equal; auto using subst_path_fresh, (proj1 (subst_typ_fresh_mut z q)).
Qed.

Lemma subst_typ_fresh z q T : z \notin fv_typ T -> subst_typ z q T = T.
Proof. apply (proj1 (subst_typ_fresh_mut z q)). Qed.
Lemma subst_trm_fresh z q t : z \notin fv_trm t -> subst_trm z q t = t.
Proof. apply (proj1 (subst_trm_fresh_mut z q)). Qed.

Lemma subst_repl_mut z q :
  (forall p r T U, repl_typ p r T U ->
    repl_typ (subst_path z q p) (subst_path z q r) (subst_typ z q T) (subst_typ z q U)) /\
  (forall p r D E, repl_dec p r D E ->
    repl_dec (subst_path z q p) (subst_path z q r) (subst_dec z q D) (subst_dec z q E)).
Proof.
  apply repl_mutind; intros; cbn; try rewrite !subst_sel_fields; constructor; auto.
Qed.

Lemma subst_tight_mut z q :
  (forall T, tight_bounds T -> tight_bounds (subst_typ z q T)) /\
  (forall D, tight_bounds_dec D -> tight_bounds_dec (subst_dec z q D)).
Proof. apply typ_mutind; cbn; intros; intuition congruence. Qed.

Lemma subst_label_def z q d : label_of_def (subst_def z q d) = label_of_def d.
Proof. now destruct d. Qed.

Lemma subst_defs_hasnt z q ds l :
  defs_hasnt ds l -> defs_hasnt (subst_defs z q ds) l.
Proof.
  unfold defs_hasnt. induction ds; cbn; auto.
  rewrite subst_label_def. destruct (classicT (label_of_def d = l)); auto; discriminate.
Qed.

(* Substitution maps each variable typing to a typing of the substituted path. *)
Definition ctx_subst z q (G H : ctx) :=
  forall x T, binds x T G -> H ⊢ trm_path (subst_path z q (pvar x)) : subst_typ z q T.

Lemma ctx_subst_push z q G H x T :
  ctx_subst z q G H -> x <> z -> x # H ->
  ctx_subst z q (G & x ~ T) (H & x ~ subst_typ z q T).
Proof.
  intros M N F y U B. apply binds_push_inv in B as [[-> ->]|[D B]].
  - rewrite subst_pvar_other by assumption. apply ty_var, binds_push_eq.
  - eapply typing_weaken; [apply M; exact B | now apply ctx_incl_fresh].
Qed.

Local Ltac pdot_fresh H :=
  repeat match type of H with
    | _ \notin _ \u _ =>
      let F := fresh "Fr" in let K := fresh "Fr" in
      apply notin_union in H as [F K]; pdot_fresh F; pdot_fresh K
    | _ \notin \{_} => apply notin_singleton in H
  end.

Lemma typing_subst_all z q (N : named_path q) :
  (forall G t T, G ⊢ t : T -> forall H, ctx_subst z q G H ->
    H ⊢ subst_trm z q t : subst_typ z q T) /\
  (forall x bs G d D, x; bs; G ⊢ d : D ->
    forall H, ctx_subst z q G H -> x <> z ->
    x; bs; H ⊢ subst_def z q d : subst_dec z q D) /\
  (forall x bs G ds T, x; bs; G ⊢ ds :: T ->
    forall H, ctx_subst z q G H -> x <> z ->
    x; bs; H ⊢ subst_defs z q ds :: subst_typ z q T) /\
  (forall G S T, G ⊢ S <: T -> forall H, ctx_subst z q G H ->
    H ⊢ subst_typ z q S <: subst_typ z q T).
Proof.
  apply tds_mutind; intros; cbn in *;
    try rewrite ?subst_open_typ, ?subst_sel_field in * by exact N;
    try solve [eauto 4 using subst_defs_hasnt, (proj1 (subst_repl_mut z q)) with pdot].
  all: try match goal with M : ctx_subst _ _ ?G ?K |- _ =>
    try rename H into IH; try rename K into H
  end.
  - eapply ty_all_intro with (L := L \u dom H \u \{z}).
    intros x F. pdot_fresh F.
    specialize (IH x Fr _ (ctx_subst_push H1 Fr2 Fr1)).
    rewrite open_trm_var, open_typ_var, subst_open_trm, subst_open_typ,
      subst_pvar_other in IH by assumption.
    now rewrite open_trm_var, open_typ_var.
  - eapply ty_new_intro with (L := L \u dom H \u \{z}).
    intros x F. pdot_fresh F.
    specialize (IH x Fr _ (ctx_subst_push H1 Fr2 Fr1) Fr2).
    rewrite open_defs_var, open_typ_var, subst_open_defs, subst_open_typ,
      subst_pvar_other in IH by assumption.
    now rewrite open_defs_var, open_typ_var.
  - eapply ty_let with (L := L \u dom H \u \{z}); [eauto |].
    intros x F. pdot_fresh F.
    specialize (H0 x Fr _ (ctx_subst_push H2 Fr2 Fr1)).
    rewrite open_trm_var, subst_open_trm, subst_pvar_other in H0 by assumption.
    now rewrite open_trm_var.
  - subst p. eapply ty_def_new; [reflexivity | apply (proj1 (subst_tight_mut z q)); assumption |].
    specialize (IH H H1 H2).
    rewrite subst_open_defs, subst_sel_field in IH by assumption.
    assert (F : z \notin fv_path (p_sel (avar_f x) bs)).
    { cbn. apply notin_singleton. congruence. }
    now rewrite (@subst_path_fresh z q _ F) in IH.
  - eapply ty_defs_cons; [eauto | eauto |].
    rewrite subst_label_def. now apply subst_defs_hasnt.
  - eapply subtyp_sngl_pq; [eauto | eauto |].
    now apply (proj1 (subst_repl_mut z q)).
  - eapply subtyp_sngl_qp; [eauto | eauto |].
    now apply (proj1 (subst_repl_mut z q)).
  - eapply subtyp_all with (L := L \u dom H \u \{z}); [eauto |].
    intros x F. pdot_fresh F.
    specialize (H0 x Fr _ (ctx_subst_push H2 Fr2 Fr1)).
    rewrite !open_typ_var, !subst_open_typ, !subst_pvar_other in H0 by assumption.
    now rewrite !open_typ_var.
Qed.

Lemma subst_ctx_remove G x p T :
  x \notin fv_ctx_types G -> x \notin fv_typ T ->
  G ⊢ trm_path p : T -> ctx_subst x p (G & x ~ T) G.
Proof.
  intros F FT P z U B. apply binds_push_inv in B as [[-> ->]|[D B]].
  - now rewrite subst_pvar_same, subst_typ_fresh.
  - rewrite subst_pvar_other by assumption.
    rewrite subst_typ_fresh; [now apply ty_var |].
    eapply fv_in_values_binds; eauto.
Qed.

Lemma let_inst G L t T U p :
  named_path p ->
  (forall x, x \notin L -> G & x ~ T ⊢ open_trm x t : U) ->
  G ⊢ trm_path p : T ->
  G ⊢ open_trm_p p t : U.
Proof.
  intros N B P.
  destruct (var_fresh (L \u fv_ctx_types G \u fv_trm t \u fv_typ T \u fv_typ U)) as [x F].
  pdot_fresh F.
  pose proof ((proj1 (typing_subst_all x N)) _ _ _ (B x Fr)
    _ (subst_ctx_remove Fr1 Fr2 P)) as H.
  now rewrite open_trm_var, subst_open_trm, subst_pvar_same,
    subst_trm_fresh, subst_typ_fresh in H by assumption.
Qed.

Lemma lambda_inst G L t T U p :
  named_path p ->
  (forall x, x \notin L -> G & x ~ T ⊢ open_trm x t : open_typ x U) ->
  G ⊢ trm_path p : T ->
  G ⊢ open_trm_p p t : open_typ_p p U.
Proof.
  intros N B P.
  destruct (var_fresh (L \u fv_ctx_types G \u fv_trm t \u fv_typ T \u fv_typ U)) as [x F].
  pdot_fresh F.
  pose proof ((proj1 (typing_subst_all x N)) _ _ _ (B x Fr)
    _ (subst_ctx_remove Fr1 Fr2 P)) as H.
  now rewrite open_trm_var, open_typ_var, subst_open_trm, subst_open_typ,
    !subst_pvar_same, subst_trm_fresh, subst_typ_fresh in H by assumption.
Qed.

Lemma all_sub_inst G L S U V p :
  named_path p ->
  (forall x, x \notin L -> G & x ~ S ⊢ open_typ x U <: open_typ x V) ->
  G ⊢ trm_path p : S ->
  G ⊢ open_typ_p p U <: open_typ_p p V.
Proof.
  intros N B P.
  destruct (var_fresh (L \u fv_ctx_types G \u fv_typ S \u fv_typ U \u fv_typ V)) as [x F].
  pdot_fresh F.
  pose proof ((proj2 (proj2 (proj2 (typing_subst_all x N)))) _ _ _ (B x Fr)
    _ (subst_ctx_remove Fr1 Fr0 P)) as H.
  now rewrite !open_typ_var, !subst_open_typ, !subst_pvar_same,
    !subst_typ_fresh in H by assumption.
Qed.

Lemma named_sel p a : named_path p -> named_path (p•a).
Proof. intros [x [bs ->]]. exists x, (a :: bs). reflexivity. Qed.

Lemma named_sel_inv p a : named_path (p•a) -> named_path p.
Proof.
  destruct p as [[i|x] bs]; [intros [y [cs E]]; discriminate |].
  exists x, bs. reflexivity.
Qed.

Lemma typing_named G p T : G ⊢ trm_path p : T -> named_path p.
Proof.
  assert (K : forall t T, G ⊢ t : T ->
    match t with trm_path q => named_path q | _ => True end).
  { intros t U P. induction P; cbn in *; try exact Logic.I;
      try solve [eauto using named_sel].
    - exists x, (@nil trm_label). reflexivity.
    - eapply named_sel_inv; exact IHP. }
  exact (K (trm_path p) T).
Qed.

Definition ctx_morph (G H : ctx) :=
  forall x T, binds x T G -> H ⊢ tvar x : T.

Lemma ctx_morph_push G H x T :
  ctx_morph G H -> x # H -> ctx_morph (G & x ~ T) (H & x ~ T).
Proof.
  intros M F y U B. apply binds_push_inv in B as [[-> ->]|[N B]].
  - apply ty_var, binds_push_eq.
  - eapply typing_weaken; [eauto | now apply ctx_incl_fresh].
Qed.

Lemma typing_morph_all :
  (forall G t T, G ⊢ t : T -> forall H, ctx_morph G H -> H ⊢ t : T) /\
  (forall x bs G d D, x; bs; G ⊢ d : D ->
    forall H, ctx_morph G H -> x; bs; H ⊢ d : D) /\
  (forall x bs G ds T, x; bs; G ⊢ ds :: T ->
    forall H, ctx_morph G H -> x; bs; H ⊢ ds :: T) /\
  (forall G S T, G ⊢ S <: T -> forall H, ctx_morph G H -> H ⊢ S <: T).
Proof.
  apply tds_mutind; intros; try solve [eauto 5 with pdot].
  all: match goal with M : ctx_morph _ ?K |- _ =>
    first [eapply ty_all_intro with (L := L \u dom K)
      | eapply ty_new_intro with (L := L \u dom K)
      | eapply ty_let with (L := L \u dom K)
      | eapply subtyp_all with (L := L \u dom K)];
    try solve [eauto];
    intros x F; pdot_fresh F; eauto using ctx_morph_push
  end.
Qed.

Lemma typing_morph G H t T :
  G ⊢ t : T -> ctx_morph G H -> H ⊢ t : T.
Proof. intros; eapply (proj1 typing_morph_all); eauto. Qed.

Lemma defs_morph x bs G H ds T :
  x; bs; G ⊢ ds :: T -> ctx_morph G H -> x; bs; H ⊢ ds :: T.
Proof. intros; eapply (proj1 (proj2 (proj2 typing_morph_all))); eauto. Qed.

Lemma narrow_push G x S T :
  x # G -> G & x ~ S ⊢ tvar x : T ->
  ctx_morph (G & x ~ T) (G & x ~ S).
Proof.
  intros F P y U B. apply binds_push_inv in B as [[-> ->]|[N B]]; auto.
  apply ty_var, binds_push_neq; auto.
Qed.

(* Object definitions determine the shape and exact type members of a record. *)
Local Hint Constructors record_dec record_typ inert_typ record_has : pdot_record.

Lemma open_label_dec k p D :
  label_of_dec (open_rec_dec_p k p D) = label_of_dec D.
Proof. destruct D; reflexivity. Qed.

Lemma open_label_def k p d :
  label_of_def (open_rec_def_p k p d) = label_of_def d.
Proof. destruct d; reflexivity. Qed.

Lemma record_open_all :
  (forall D, record_dec D -> forall k p, record_dec (open_rec_dec_p k p D)) /\
  (forall T L, record_typ T L -> forall k p, record_typ (open_rec_typ_p k p T) L) /\
  (forall T, inert_typ T -> forall k p, inert_typ (open_rec_typ_p k p T)).
Proof.
  apply rcd_mutind; intros; cbn; eauto using open_label_dec with pdot_record.
  - apply rt_one; auto. now rewrite open_label_dec.
  - apply rt_cons; auto. now rewrite open_label_dec.
Qed.

Lemma record_open T L p :
  record_typ T L -> record_typ (open_typ_p p T) L.
Proof. intros R; eapply (proj1 (proj2 record_open_all)); exact R. Qed.

Lemma record_tight_all :
  (forall D, record_dec D -> tight_bounds_dec D) /\
  (forall T L, record_typ T L -> tight_bounds T) /\
  (forall T, inert_typ T -> tight_bounds T).
Proof. apply rcd_mutind; cbn; auto. Qed.

Definition close_path k x (p : path) :=
  match p with
  | p_sel (avar_f y) bs => If y = x then p_sel (avar_b k) bs else p
  | p_sel (avar_b _) _ => p
  end.

Fixpoint close_typ k x T :=
  match T with
  | typ_rcd D => typ_rcd (close_dec k x D)
  | T ∧ U => close_typ k x T ∧ close_typ k x U
  | p ↓ A => close_path k x p ↓ A
  | μ T => μ (close_typ (S k) x T)
  | ∀(U) T => ∀(close_typ k x U) (close_typ (Datatypes.S k) x T)
  | {{p}} => {{close_path k x p}}
  | _ => T
  end
with close_dec k x D :=
  match D with
  | {A >: T <: U} => {A >: close_typ k x T <: close_typ k x U}
  | {a ⦂ T} => {a ⦂ close_typ k x T}
  end.

Lemma close_open_path k x p :
  x \notin fv_path p -> close_path k x (open_rec_path_p k (pvar x) p) = p.
Proof.
  destruct p as [[i|y] bs]; cbn.
  - intros _. destruct (classicT (k = i)) as [->|N]; cbn; auto.
    destruct (classicT (x = x)); [now rewrite app_nil_r | contradiction].
  - rewrite notin_singleton. intro N.
    destruct (classicT (y = x)); [congruence | reflexivity].
Qed.

Lemma close_open_typ x :
  (forall T k, x \notin fv_typ T -> close_typ k x (open_rec_typ_p k (pvar x) T) = T) /\
  (forall D k, x \notin fv_dec D -> close_dec k x (open_rec_dec_p k (pvar x) D) = D).
Proof.
  apply typ_mutind; intros; cbn in *;
    repeat match goal with H : _ \notin _ \u _ |- _ => apply notin_union in H as [? ?] end;
    f_equal; auto using close_open_path.
Qed.

Lemma open_tight_fresh x :
  (forall T k, x \notin fv_typ T -> tight_bounds (open_rec_typ_p k (pvar x) T) -> tight_bounds T) /\
  (forall D k, x \notin fv_dec D -> tight_bounds_dec (open_rec_dec_p k (pvar x) D) -> tight_bounds_dec D).
Proof.
  apply typ_mutind; cbn; intros;
    repeat match goal with H : _ \notin _ \u _ |- _ => apply notin_union in H as [? ?] end;
    try solve [intuition eauto].
  match goal with H : open_rec_typ_p _ _ _ = open_rec_typ_p _ _ _ |- _ =>
    pose proof (f_equal (close_typ k x) H) as E;
    now rewrite !(proj1 (close_open_typ x)) in E by assumption
  end.
Qed.

Lemma record_unopen_all :
  (forall T k p, tight_bounds T ->
    (forall L, record_typ (open_rec_typ_p k p T) L -> record_typ T L) /\
    (inert_typ (open_rec_typ_p k p T) -> inert_typ T)) /\
  (forall D k p, tight_bounds_dec D ->
    record_dec (open_rec_dec_p k p D) -> record_dec D).
Proof.
  apply typ_mutind; intros; cbn in *.
  - split; intros; inversion H0.
  - split; intros; inversion H0.
  - split; intros; inversion H1; subst; eauto using open_label_dec with pdot_record.
  - destruct H1. split; intros; inversion H3; subst.
    destruct t0; cbn in *; try discriminate.
    match goal with E : typ_rcd _ = typ_rcd _ |- _ => inversion E; subst end.
    rewrite open_label_dec in *.
    apply rt_cons; auto.
    + now apply (proj1 (H k p H1)).
    + pose proof (proj1 (H0 k p H2) _ (rt_one H7 eq_refl)) as J. inversion J; auto.
  - split; intros; inversion H0.
  - split; intros; inversion H1; subst.
    destruct (H (S k) p H0); eauto with pdot_record.
  - split; intros; [inversion H2 | constructor].
  - split; intros; match goal with J : record_typ _ _ |- _ => inversion J | J : inert_typ _ |- _ => inversion J end.
  - subst; constructor.
  - destruct (H k p H0) as [_ IH]. inversion H1; subst; eauto with pdot_record.
    destruct t0; cbn in *; try discriminate.
    apply rd_trm_sngl.
Qed.

Lemma record_unopen T k p L :
  tight_bounds T -> record_typ (open_rec_typ_p k p T) L -> record_typ T L.
Proof. intros B R. eapply (proj1 (proj1 record_unopen_all T k p B)); eauto. Qed.

Lemma ty_def_label x bs G d D :
  x; bs; G ⊢ d : D -> label_of_def d = label_of_dec D.
Proof. intros H; inversion H; reflexivity. Qed.

Definition no_defs_labels ds (L : fset label) :=
  forall l, l \in L -> get_def l ds <> None.

Lemma defs_record_all :
  (forall x bs G d D, x; bs; G ⊢ d : D -> record_dec D) /\
  (forall x bs G ds T, x; bs; G ⊢ ds :: T ->
    exists L, record_typ T L /\ no_defs_labels ds L).
Proof.
  apply ty_def_mutind; intros; eauto with pdot_record.
  - destruct H as [L [R _]]. constructor; econstructor. eapply record_unopen; eauto.
  - exists (\{label_of_def d}). split.
    + eapply rt_one; eauto using ty_def_label.
    + intros l I. rewrite in_singleton in I. subst l.
      cbn. destruct (classicT (label_of_def d = label_of_def d)); congruence.
  - destruct H as [L [R W]]. exists (L \u \{label_of_def d}). split.
    + eapply rt_cons; eauto using ty_def_label.
      intro I. eapply W; eauto.
    + intros l I. rewrite in_union, in_singleton in I. cbn.
      destruct (classicT (label_of_def d = l)); [discriminate |].
      destruct I as [I|I]; [now apply W | congruence].
Qed.

Lemma ty_defs_record x bs G ds T :
  x; bs; G ⊢ ds :: T -> record_type T.
Proof. intros H. destruct (proj2 defs_record_all _ _ _ _ _ H) as [L [R _]]. now exists L. Qed.

Lemma precise_val_inert G v T : G ⊢!v v : T -> inert_typ T.
Proof.
  intro H; inversion H; subst; [constructor |].
  destruct (var_fresh (L \u fv_typ T0)) as [x F].
  apply notin_union in F as [F K].
  destruct (ty_defs_record (H0 x F)) as [ls R].
  rewrite open_typ_var in R. econstructor.
  eapply record_unopen; [|exact R].
  eapply (proj1 (open_tight_fresh x)); [exact K |].
  eapply (proj1 (proj2 record_tight_all)); exact R.
Qed.

Lemma precise_val_typing G v T : G ⊢!v v : T -> G ⊢ trm_val v : T.
Proof. intro H; inversion H; subst; eauto with pdot. Qed.

Lemma value_typing_precise G v T :
  G ⊢ trm_val v : T -> exists U, G ⊢!v v : U /\ G ⊢ U <: T.
Proof.
  intros H. remember (trm_val v) as t eqn:E. revert v E.
  induction H; intros v E; inversion E; subst.
  - eexists; split; [eapply ty_all_intro_p; eauto | constructor].
  - eexists; split; [eapply ty_new_intro_p; eauto | constructor].
  - destruct (IHty_trm _ eq_refl) as [V [P S]]. exists V; split; eauto with pdot.
Qed.

Lemma record_has_one D E :
  record_has (typ_rcd D) E -> D = E.
Proof. inversion 1; reflexivity. Qed.

Lemma record_has_cons T D E :
  record_has (T ∧ typ_rcd D) E -> record_has T E \/ D = E.
Proof. inversion 1; subst; auto using record_has_one. Qed.

Lemma record_has_info T L D :
  record_typ T L -> record_has T D -> record_dec D /\ label_of_dec D \in L.
Proof.
  intros R. induction R as [D0 l D' ->|T L D0 l R IH D' -> F]; intro E.
  - apply record_has_one in E as <-. split; auto. now rewrite in_singleton.
  - apply record_has_cons in E as [E|<-].
    + destruct (IH E) as [? ?]. split; auto. rewrite in_union; auto.
    + split; auto. rewrite in_union, in_singleton; auto.
Qed.

Lemma record_has_unique T L D E :
  record_typ T L -> record_has T D -> record_has T E ->
  label_of_dec D = label_of_dec E -> D = E.
Proof.
  intros R. induction R as [D' l D0 ->|T L D' l R IH D0 -> F]; intros HD HE Eq.
  - apply record_has_one in HD, HE. congruence.
  - apply record_has_cons in HD as [HD|<-];
    apply record_has_cons in HE as [HE|<-]; eauto.
    + exfalso. apply F. rewrite <- Eq. exact (proj2 (record_has_info R HD)).
    + exfalso. apply F. rewrite Eq. exact (proj2 (record_has_info R HE)).
Qed.

Lemma inert_binds G x T :
  inert G -> binds x T G -> inert_typ T.
Proof.
  induction 1; intro B.
  - exact (False_rect _ (binds_empty_inv B)).
  - apply binds_push_inv in B as [[_ ->]|[_ B]]; auto.
Qed.

Lemma inert_ok G : inert G -> ok G.
Proof. induction 1; eauto using ok_empty, ok_push. Qed.

(* A slot follows the annotations of physical object fields. A singleton slot
   redirects lookup to another path. *)
Inductive slot (G : ctx) : path -> typ -> Prop :=
| slot_var : forall x T, binds x T G -> slot G (pvar x) T
| slot_field : forall p U a T, slot G p (μ U) ->
    record_has (open_typ_p p U) {a ⦂ T} -> slot G (p•a) T.

Lemma slot_var_inv G x T : slot G (pvar x) T -> binds x T G.
Proof.
  intro H; inversion H; subst; auto.
  destruct p; discriminate.
Qed.

Lemma slot_field_inv G p a T : slot G (p•a) T ->
  exists U, slot G p (μ U) /\ record_has (open_typ_p p U) {a ⦂ T}.
Proof.
  destruct p. intro H. inversion H; subst.
  destruct p; cbn in *; repeat match goal with E : p_sel _ _ = p_sel _ _ |- _ => inversion E; clear E; subst end.
  eauto.
Qed.

Lemma slot_named G p T : slot G p T -> named_path p.
Proof. induction 1; [exists x, (@nil trm_label); reflexivity | eauto using named_sel]. Qed.

Lemma slot_shape G p T :
  inert G -> slot G p T -> inert_typ T \/ is_sngl T.
Proof.
  intros I H; induction H.
  - left; eauto using inert_binds.
  - destruct IHslot as [R|[q E]]; [|discriminate].
    inversion R as [|? L B]; subst.
    destruct (record_has_info (record_open p B) H0) as [D _].
    inversion D; subst; eauto. right; eexists; reflexivity.
Qed.

Lemma slot_unique G p T U :
  inert G -> slot G p T -> slot G p U -> T = U.
Proof.
  intros I H. revert U. induction H; intros V K.
  - apply slot_var_inv in K. eauto using binds_functional.
  - apply slot_field_inv in K as [W [K D]].
    specialize (IHslot _ K); injection IHslot as E; subst W.
    pose proof (slot_shape I H) as [R|[? E]]; [|discriminate].
    inversion R as [|? L B]; subst.
    pose proof (record_has_unique (record_open p B) H0 D eq_refl) as E.
    now injection E.
Qed.

Lemma record_has_typing G p U D :
  G ⊢ trm_path p : U -> record_has U D -> G ⊢ trm_path p : typ_rcd D.
Proof.
  intros P H. induction H; eauto using ty_sub, subtyp_and11, subtyp_and12.
Qed.

Lemma slot_typing G p T : slot G p T -> G ⊢ trm_path p : T.
Proof.
  induction 1; eauto using ty_var, ty_rec_elim, record_has_typing, ty_new_elim.
Qed.

Lemma record_has_flow G p T U D :
  G ⊢! p : T ⪼ U -> record_has U D -> G ⊢! p : T ⪼ typ_rcd D.
Proof. intros P H; induction H; eauto using pf_and1, pf_and2. Qed.

Lemma slot_flow G p T : ok G -> slot G p T -> G ⊢! p : T ⪼ T.
Proof. intros O H; induction H; eauto 6 using pf_bind, pf_fld, pf_open, record_has_flow. Qed.

Inductive record_part : typ -> typ -> Prop :=
| part_self : forall T, record_part T T
| part_left : forall T U V, record_part T V -> record_part (T ∧ U) V
| part_right : forall T U V, record_part U V -> record_part (T ∧ U) V.

Lemma record_part_decl T V D :
  record_part T V -> V = typ_rcd D -> record_has T D.
Proof. induction 1; intros E; subst; eauto with pdot_record. Qed.

Lemma record_part_shape T V L :
  record_typ T L -> record_part T V -> record_type V.
Proof.
  intros R P; revert L R. induction P; intros L R.
  - now exists L.
  - inversion R; subst; eauto.
  - inversion R; subst. apply IHP with (L:=\{label_of_dec D}).
    eauto with pdot_record.
Qed.

Lemma record_part_trans T U V :
  record_part T U -> record_part U V -> record_part T V.
Proof. induction 1; eauto using part_left, part_right. Qed.

Lemma flow_slot G p T V :
  inert G -> G ⊢! p : T ⪼ V ->
  slot G p T /\ (T = V \/ exists U, T = μ U /\ record_part (open_typ_p p U) V).
Proof.
  intros I H; induction H; try specialize (IHprecise_flow I).
  - split; [now constructor | auto].
  - destruct IHprecise_flow as [W [E|[U0 [E P]]]].
    + subst. destruct (slot_shape I W) as [J|[q E]]; [inversion J | discriminate].
    + subst. split; [econstructor; eauto using record_part_decl | auto].
  - destruct IHprecise_flow as [W [E|[U0 [E P]]]].
    + subst. split; auto. right. eauto using part_self.
    + subst. destruct (slot_shape I W) as [J|[q E]]; [|discriminate].
      inversion J as [|? L R]; subst.
      destruct (record_part_shape (record_open p R) P) as [L0 RR]; inversion RR.
  - destruct IHprecise_flow as [W [E|[U0 [E P]]]].
    + subst. destruct (slot_shape I W) as [J|[q E]]; [inversion J | discriminate].
    + split; auto. right. exists U0; split; auto.
      eapply record_part_trans; [exact P | apply part_left, part_self].
  - destruct IHprecise_flow as [W [E|[U0 [E P]]]].
    + subst. destruct (slot_shape I W) as [J|[q E]]; [inversion J | discriminate].
    + split; auto. right. exists U0; split; auto.
      eapply record_part_trans; [exact P | apply part_right, part_self].
Qed.

Lemma pdot_star_trans A (R : A -> A -> Prop) a b c :
  star R a b -> star R b c -> star R a c.
Proof. induction 1; eauto using star_step. Qed.

Inductive alias_step G : path -> path -> Prop :=
| alias_slot : forall p q, slot G p {{q}} -> alias_step G p q
| alias_field : forall p q a, alias_step G p q -> alias_step G (p•a) (q•a).

Lemma slot_inert_terminal G p T :
  inert G -> slot G p T -> inert_typ T -> forall q, ~ alias_step G p q.
Proof.
  intros I H. induction H as [x T B|p U a T P IH D]; intros J q A.
  - inversion A; subst.
    + assert (T = {{q}}) by (eapply slot_unique; eauto using slot_var). subst; inversion J.
    + destruct p; discriminate.
  - inversion A; subst.
    + assert (T = {{q}}) by (eapply slot_unique; eauto using slot_field). subst; inversion J.
    + destruct p as [x bs], p0 as [y cs]; cbn in *.
      repeat match goal with E : p_sel _ _ = p_sel _ _ |- _ => inversion E; clear E; subst end.
      eapply IH; [|eassumption].
      destruct (slot_shape I P) as [R|[? E]]; auto; discriminate.
Qed.

Lemma alias_det G :
  inert G -> forall p q r, alias_step G p q -> alias_step G p r -> q = r.
Proof.
  intros I p q r H; revert r. induction H; intros r K.
  - inversion K; subst.
    + now injection (slot_unique I H H0).
    + destruct (slot_field_inv p0 a H) as [U [B _]].
      exfalso. eapply slot_inert_terminal; [exact I|exact B| |exact H0].
      destruct (slot_shape I B) as [J|[? E]]; auto; discriminate.
  - inversion K; subst.
    + destruct (slot_field_inv p a H0) as [U [B _]].
      exfalso. eapply slot_inert_terminal; [exact I|exact B| |exact H].
      destruct (slot_shape I B) as [J|[? E]]; auto; discriminate.
    + destruct p as [x bs], p0 as [y cs]; cbn in *.
      repeat match goal with E : p_sel _ _ = p_sel _ _ |- _ => inversion E; clear E; subst end.
      f_equal; eauto.
Qed.

Lemma alias_star_field G p q a :
  star (alias_step G) p q -> star (alias_step G) (p•a) (q•a).
Proof. induction 1; eauto using star_refl, star_step, alias_field. Qed.

(* Paths are equivalent when their deterministic alias lookups can meet.
   The common path can be a singleton slot. *)
Definition path_eq G p q :=
  exists r, star (alias_step G) p r /\ star (alias_step G) q r.

Lemma path_eq_refl G p : path_eq G p p.
Proof. exists p; auto using star_refl. Qed.
Lemma path_eq_sym G p q : path_eq G p q -> path_eq G q p.
Proof. intros [r [H K]]; exists r; auto. Qed.

Lemma pdot_star_join A (R : A -> A -> Prop) :
  (forall a b c, R a b -> R a c -> b = c) ->
  forall a b c, star R a b -> star R a c ->
  exists d, star R b d /\ star R c d.
Proof.
  intros D a b c H. revert c. induction H; intros d K.
  - eauto using star_refl.
  - inversion K; subst.
    + eauto using star_refl, star_step.
    + match goal with H : R ?a ?b, K : R ?a ?c |- _ =>
        pose proof (D _ _ _ H K) as E; subst
      end. eauto.
Qed.

Lemma path_eq_trans G p q r :
  inert G -> path_eq G p q -> path_eq G q r -> path_eq G p r.
Proof.
  intros I [a [P Q]] [b [Q' R]].
  destruct (pdot_star_join (alias_det I) Q Q') as [c [? ?]].
  exists c; split; eauto using pdot_star_trans.
Qed.

Lemma path_eq_field G p q a :
  path_eq G p q -> path_eq G (p•a) (q•a).
Proof. intros [r [? ?]]; exists (r•a); eauto using alias_star_field. Qed.

Lemma path_eq_fields G p q bs :
  path_eq G p q -> path_eq G (p••bs) (q••bs).
Proof.
  induction bs; intro E.
  - now rewrite !sel_fields_nil.
  - pose proof (path_eq_field a (IHbs E)) as F.
    change (path_eq G ((p••bs)••(a::nil)) ((q••bs)••(a::nil))) in F.
    now rewrite !sel_fields_assoc in F.
Qed.

Lemma path_eq_slot G p q T :
  inert G -> slot G q T -> inert_typ T -> path_eq G p q ->
  star (alias_step G) p q.
Proof.
  intros I S J [r [P Q]]. inversion Q; subst; auto.
  exfalso. eapply slot_inert_terminal; eauto.
Qed.

Inductive accessible (G : ctx) : path -> Prop :=
| access_var : forall x T, binds x T G -> accessible G (pvar x)
| access_field : forall p r U a T, star (alias_step G) p r ->
    slot G r (μ U) -> record_has (open_typ_p r U) {a ⦂ T} ->
    accessible G (p•a).

Lemma slot_accessible G p T : slot G p T -> accessible G p.
Proof. destruct 1; eauto using access_var, access_field, star_refl. Qed.

Lemma accessible_field_inv G p a :
  accessible G (p•a) ->
  exists r U T, star (alias_step G) p r /\ slot G r (μ U) /\
    record_has (open_typ_p r U) {a ⦂ T}.
Proof.
  destruct p. intro H. inversion H; subst.
  destruct p; cbn in *; repeat match goal with E : p_sel _ _ = p_sel _ _ |- _ => inversion E; clear E; subst end.
  eauto 8.
Qed.

Lemma access_step_back G p q :
  alias_step G p q -> accessible G q -> accessible G p.
Proof.
  intros A S. induction A.
  - eauto using slot_accessible.
  - apply accessible_field_inv in S as [r [U [T [H [K R]]]]].
    econstructor; eauto using star_step.
Qed.

Lemma accessible_parent G p a : accessible G (p•a) -> accessible G p.
Proof.
  intros H. apply accessible_field_inv in H as [r [U [T [H [K R]]]]].
  assert (accessible G r) by eauto using slot_accessible.
  induction H; eauto using access_step_back.
Qed.

Lemma accessible_field_eq G p q a :
  inert G -> path_eq G p q -> accessible G (p•a) -> accessible G (q•a).
Proof.
  intros I E H. apply accessible_field_inv in H as [r [U [T [P [K R]]]]].
  assert (J : inert_typ (μ U)).
  { destruct (slot_shape I K) as [J|[? J]]; auto; discriminate. }
  eapply access_field; [|exact K|exact R].
  eapply path_eq_slot; eauto.
  assert (Q : path_eq G p r) by (exists r; eauto using star_refl).
  eapply path_eq_trans; [exact I | exact (path_eq_sym E) | exact Q].
Qed.

Lemma get_def_open k p ds l :
  get_def l (open_rec_defs_p k p ds) =
  option_map (open_rec_def_p k p) (get_def l ds).
Proof.
  induction ds; cbn; auto. rewrite open_label_def.
  destruct (classicT (label_of_def d = l)); auto.
Qed.

Lemma defs_has_open_inv p ds d :
  defs_has (open_defs_p p ds) d ->
  exists d0, defs_has ds d0 /\ open_def_p p d0 = d.
Proof.
  unfold defs_has, open_defs_p, open_def_p. rewrite get_def_open.
  destruct (get_def (label_of_def d) ds) as [d0|] eqn:E; cbn; try discriminate.
  intros K; injection K as <-. exists d0. rewrite open_label_def in E. auto.
Qed.

Lemma ty_defs_get x bs G ds T D :
  x; bs; G ⊢ ds :: T -> record_has T D ->
  exists d, x; bs; G ⊢ d : D /\ defs_has ds d.
Proof.
  intros H. induction H; intro R.
  - inversion R; subst. exists d. split; auto.
    unfold defs_has; cbn. destruct (classicT (label_of_def d = label_of_def d)); congruence.
  - inversion R; subst.
    + match goal with K : record_has T _ |- _ => destruct (IHty_defs K) as [e [P Q]] end.
      exists e; split; auto. unfold defs_has, defs_hasnt in *; cbn.
      destruct (classicT (label_of_def d = label_of_def e)) as [E|N]; auto.
      rewrite E in *. congruence.
    + match goal with K : record_has (typ_rcd _) _ |- _ => inversion K; subst end.
      exists d; split; auto. unfold defs_has; cbn.
      destruct (classicT (label_of_def d = label_of_def d)); congruence.
Qed.

Lemma precise_val_weaken G H v T :
  G ⊢!v v : T -> ctx_incl G H -> H ⊢!v v : T.
Proof.
  intros P I; destruct P.
  - eapply ty_all_intro_p with (L:=L). intros.
    eapply typing_weaken; [eauto | now apply ctx_incl_push].
  - eapply ty_new_intro_p with (L:=L). intros.
    eapply defs_weaken; [eauto | now apply ctx_incl_push].
Qed.

(* Each allocated root retains its precise function typing or the typing of
   its object definitions opened at the allocated name. *)
Inductive root_val (G : ctx) (x : var) : val -> typ -> Prop :=
| root_fun : forall S t U, G ⊢!v λ(S) t : ∀(S) U -> root_val G x (λ(S) t) (∀(S) U)
| root_obj : forall T ds,
    x; nil; G ⊢ open_defs_p (pvar x) ds :: open_typ_p (pvar x) T ->
    root_val G x (ν(T) ds) (μ T).

Lemma root_val_weaken G H x v T :
  root_val G x v T -> ctx_incl G H -> root_val H x v T.
Proof.
  intros P I. destruct P; constructor; eauto using precise_val_weaken, defs_weaken.
Qed.

Definition precise_heap G γ :=
  forall x T, binds x T G -> exists v, binds x v γ /\ root_val G x v T.

Lemma precise_heap_push G γ x v T :
  precise_heap G γ -> x # G -> x # γ -> root_val (G & x ~ T) x v T ->
  precise_heap (G & x ~ T) (γ & x ~ v).
Proof.
  intros H F K P y U B. apply binds_push_inv in B as [[-> ->]|[N B]].
  - exists v; split; auto using binds_push_eq.
  - destruct (H _ _ B) as [w [W Q]]. exists w; split.
    + now apply binds_push_neq.
    + eauto using root_val_weaken, ctx_incl_fresh.
Qed.

Inductive slot_contents G γ : path -> typ -> Prop :=
| contents_obj : forall x bs T ds,
    γ ⟦ p_sel (avar_f x) bs ⤳ defv (ν(T) ds) ⟧ ->
    x; bs; G ⊢ open_defs_p (p_sel (avar_f x) bs) ds
            :: open_typ_p (p_sel (avar_f x) bs) T ->
    slot_contents G γ (p_sel (avar_f x) bs) (μ T)
| contents_fun : forall p S t S' U,
    γ ⟦ p ⤳ defv (λ(S) t) ⟧ ->
    G ⊢ trm_val (λ(S) t) : ∀(S') U ->
    slot_contents G γ p (∀(S') U)
| contents_alias : forall p q U,
    γ ⟦ p ⤳ defp q ⟧ -> G ⊢ trm_path q : U -> slot_contents G γ p {{q}}.

Lemma contents_from_field G γ x bs a r T :
  x; bs; G ⊢ {a := r} : {a ⦂ T} ->
  γ ⟦ (p_sel (avar_f x) bs)•a ⤳ r ⟧ ->
  slot_contents G γ ((p_sel (avar_f x) bs)•a) T.
Proof.
  intros D H. dependent destruction D; cbn in *;
    eauto using contents_fun, contents_alias, contents_obj.
Qed.

Lemma slot_contents_sound G γ p T :
  precise_heap G γ -> slot G p T -> slot_contents G γ p T.
Proof.
  intros W H. induction H.
  - destruct (W _ _ H) as [v [B R]]. destruct R.
    + eapply contents_fun; eauto using lookup_var, precise_val_typing.
    + eapply contents_obj; eauto using lookup_var.
  - inversion IHslot; subst.
    destruct (ty_defs_get H4 H0) as [d [D K]].
    pose proof (ty_def_label D) as Lab.
    destruct d as [A V|b r]; cbn in Lab; try discriminate.
    injection Lab as ->.
    eapply contents_from_field; [exact D |].
    destruct (defs_has_open_inv (p_sel (avar_f x) bs) ds K) as [d0 [K0 EO]].
    destruct d0 as [A V|b s]; cbn [open_def_p open_rec_def_p] in EO; try discriminate.
    injection EO as B E. subst b r.
    eapply lookup_sel_v; eauto.
Qed.

Definition alias_targets_typed G :=
  forall p q, slot G p {{q}} -> exists T, G ⊢ trm_path q : T.

Lemma heap_alias_targets G γ :
  precise_heap G γ -> alias_targets_typed G.
Proof.
  intros H p q S. pose proof (slot_contents_sound H S) as R.
  inversion R; subst; eauto.
Qed.

Lemma alias_lookup G γ p q :
  precise_heap G γ -> alias_step G p q -> γ ⟦ p ⤳ defp q ⟧.
Proof.
  intros H A. induction A; eauto using lookup_sel_p.
  pose proof (slot_contents_sound H H0) as R. inversion R; auto.
Qed.

Lemma alias_star_lookup G γ p q :
  precise_heap G γ -> star (alias_step G) p q -> γ ⟦ defp p ⤳* defp q ⟧.
Proof. intros H A. induction A; eauto using star_refl, star_step, alias_lookup. Qed.

Lemma flow_field_parent G p a T U :
  G ⊢! p•a : T ⪼ U -> exists S V, G ⊢! p : S ⪼ V.
Proof.
  intros H. remember (p•a) as r eqn:E. revert p a E.
  induction H; intros r b E; eauto.
  - destruct r; discriminate.
  - destruct p, r; cbn in E. inversion E; subst; eauto.
Qed.

Lemma precise_field_parent G p a T :
  G ⊢!! p•a : T -> exists U, G ⊢!! p : U.
Proof.
  intros H. inversion H; subst.
  - edestruct flow_field_parent as [S [V P]]; eauto using pt2.
  - destruct p, p0; cbn in *. inversion H0; subst; eauto.
Qed.

Lemma alias_precise_back G p q T :
  ok G -> alias_step G p q -> G ⊢!! q : T -> G ⊢!! p : {{q}}.
Proof.
  intros O H. revert T. induction H; intros T Q.
  - apply pt2 with (T := {{q}}). now apply slot_flow.
  - destruct (precise_field_parent q a Q) as [U P].
    eauto using pt2_sngl_trans.
Qed.

Lemma accessible_precise G p :
  inert G -> accessible G p -> exists T, G ⊢!! p : T.
Proof.
  intros I A. destruct A as [x T H|p r U a T H K R].
  - eauto using pt2, pf_bind, inert_ok.
  - assert (P : G ⊢!! r•a : T).
    { apply pt2 with (T:=T). eauto using slot_flow, slot_field, inert_ok. }
    clear K R. apply alias_star_field with (a := a) in H.
    induction H; eauto.
    destruct (IHstar P) as [V Q]. exists {{b}}.
    eapply alias_precise_back; eauto using inert_ok.
Qed.

Lemma alias_names G p q :
  alias_targets_typed G -> alias_step G p q -> named_path p /\ named_path q.
Proof.
  intros W A. induction A.
  - split; eauto using slot_named.
    destruct (W _ _ H); eauto using typing_named.
  - destruct IHA. split; auto using named_sel.
Qed.

Lemma alias_star_named G p q :
  alias_targets_typed G -> star (alias_step G) p q -> named_path p -> named_path q.
Proof.
  intros W H. induction H; auto.
  intros _. apply IHstar. exact (proj2 (alias_names W H)).
Qed.

Lemma eq_names G p q :
  alias_targets_typed G -> path_eq G p q -> p = q \/ (named_path p /\ named_path q).
Proof.
  intros W [r [H K]]. destruct H as [p|p b r P H].
  - destruct K as [p|q b p Q K]; auto.
    right. split; eauto using alias_star_named, (proj2 (alias_names W Q)), (proj1 (alias_names W Q)).
  - right. split; [exact (proj1 (alias_names W P))|].
    destruct K as [r|q c r Q K].
    + eapply alias_star_named; eauto using (proj2 (alias_names W P)).
    + exact (proj1 (alias_names W Q)).
Qed.

Lemma alias_core G p q :
  alias_step G p q -> exists l r bs, slot G l {{r}} /\ p = l••bs /\ q = r••bs.
Proof.
  induction 1.
  - exists p, q, (@nil trm_label). now rewrite !sel_fields_nil.
  - destruct IHalias_step as [l [r [bs [S [-> ->]]]]].
    exists l, r, (a::bs). destruct l, r; auto.
Qed.

Lemma repl_prefix_all :
  (forall p q T U, repl_typ p q T U -> forall l r bs,
    p = l••bs -> q = r••bs -> repl_typ l r T U) /\
  (forall p q D E, repl_dec p q D E -> forall l r bs,
    p = l••bs -> q = r••bs -> repl_dec l r D E).
Proof.
  apply repl_mutind; intros; subst; try rewrite !sel_fields_assoc; constructor; eauto.
Qed.

Lemma repl_template_all :
  (forall p q T U, repl_typ p q T U ->
    exists f : path -> typ, f p = T /\ f q = U /\ forall a b, repl_typ a b (f a) (f b)) /\
  (forall p q D E, repl_dec p q D E ->
    exists f : path -> dec, f p = D /\ f q = E /\ forall a b, repl_dec a b (f a) (f b)).
Proof.
  apply repl_mutind; intros;
    repeat match goal with H : @ex _ _ |- _ => destruct H as [f [E [F H]]]; rewrite <- E, <- F end.
  - exists (fun x => typ_rcd (f x)); repeat split; constructor; auto.
  - exists (fun x => f x ∧ U); repeat split; constructor; auto.
  - exists (fun x => U ∧ f x); repeat split; constructor; auto.
  - exists (fun x => x••bs ↓ A); repeat split; constructor.
  - exists (fun x => μ (f x)); repeat split; constructor; auto.
  - exists (fun x => ∀(f x) U); repeat split; constructor; auto.
  - exists (fun x => ∀(U) (f x)); repeat split; constructor; auto.
  - exists (fun x => {{x••bs}}); repeat split; constructor.
  - exists (fun x => {A >: f x <: U}); repeat split; constructor; auto.
  - exists (fun x => {A >: U <: f x}); repeat split; constructor; auto.
  - exists (fun x => {a ⦂ f x}); repeat split; constructor; auto.
Qed.

Lemma alias_template_sub G p q f :
  alias_targets_typed G -> (forall a b, repl_typ a b (f a) (f b)) ->
  alias_step G p q -> G ⊢ f p <: f q /\ G ⊢ f q <: f p.
Proof.
  intros W R A. destruct (alias_core A) as [l [r [bs [S [E F]]]]].
  destruct (W _ _ S) as [U H]. pose proof (slot_typing S) as J.
  split.
  - eapply subtyp_sngl_pq; eauto.
    eapply (proj1 repl_prefix_all); [apply R | exact E | exact F].
  - eapply subtyp_sngl_qp; eauto.
    eapply (proj1 repl_prefix_all); [apply R | exact F | exact E].
Qed.

Lemma alias_star_template_sub G p q f :
  alias_targets_typed G -> (forall a b, repl_typ a b (f a) (f b)) ->
  star (alias_step G) p q -> G ⊢ f p <: f q /\ G ⊢ f q <: f p.
Proof.
  intros W R A. induction A.
  - split; constructor.
  - destruct (alias_template_sub f W R H); intuition eauto using subtyp_trans.
Qed.

Lemma eq_repl_sub G p q T U :
  alias_targets_typed G -> path_eq G p q -> repl_typ p q T U ->
  G ⊢ T <: U.
Proof.
  intros W [r [P Q]] R.
  destruct (proj1 repl_template_all _ _ _ _ R) as [f [<- [<- F]]].
  destruct (alias_star_template_sub f W F P), (alias_star_template_sub f W F Q).
  eauto using subtyp_trans.
Qed.

(* Type replacement acts on paths inside otherwise identical type syntax. *)
Inductive typ_eq G : typ -> typ -> Prop :=
| te_top : typ_eq G ⊤ ⊤
| te_bot : typ_eq G ⊥ ⊥
| te_rcd : forall D E, dec_eq G D E -> typ_eq G (typ_rcd D) (typ_rcd E)
| te_and : forall S S' T T', typ_eq G S S' -> typ_eq G T T' -> typ_eq G (S ∧ T) (S' ∧ T')
| te_sel : forall p q A, path_eq G p q -> typ_eq G (p ↓ A) (q ↓ A)
| te_rec : forall T U, typ_eq G T U -> typ_eq G (μ T) (μ U)
| te_all : forall S S' T T', typ_eq G S S' -> typ_eq G T T' -> typ_eq G (∀(S) T) (∀(S') T')
| te_sngl : forall p q, path_eq G p q -> typ_eq G {{p}} {{q}}
with dec_eq G : dec -> dec -> Prop :=
| de_fld : forall a T U, typ_eq G T U -> dec_eq G {a ⦂ T} {a ⦂ U}
| de_typ : forall A S S' T T', typ_eq G S S' -> typ_eq G T T' ->
    dec_eq G {A >: S <: T} {A >: S' <: T'}.

Scheme typ_eq_ind' := Induction for typ_eq Sort Prop
  with dec_eq_ind' := Induction for dec_eq Sort Prop.
Combined Scheme typ_eq_mut from typ_eq_ind', dec_eq_ind'.

Local Hint Constructors typ_eq dec_eq : pdot_eq.

Lemma typ_eq_refl_all G :
  (forall T, typ_eq G T T) /\ (forall D, dec_eq G D D).
Proof. apply typ_mutind; eauto using path_eq_refl with pdot_eq. Qed.

Lemma typ_eq_sym_all G :
  (forall T U, typ_eq G T U -> typ_eq G U T) /\
  (forall D E, dec_eq G D E -> dec_eq G E D).
Proof. apply typ_eq_mut; eauto using path_eq_sym with pdot_eq. Qed.

Lemma typ_eq_trans_all G (I : inert G) :
  (forall T U, typ_eq G T U -> forall V, typ_eq G U V -> typ_eq G T V) /\
  (forall D E, dec_eq G D E -> forall F, dec_eq G E F -> dec_eq G D F).
Proof.
  apply typ_eq_mut; intros;
    match goal with H : typ_eq _ _ ?V |- typ_eq _ _ ?V => inversion H; subst
    | H : dec_eq _ _ ?V |- dec_eq _ _ ?V => inversion H; subst end;
    eauto using path_eq_trans with pdot_eq.
Qed.

Lemma typ_eq_repl_all G p q (P : path_eq G p q) :
  (forall p' q' T U, repl_typ p' q' T U -> p' = p -> q' = q -> typ_eq G T U) /\
  (forall p' q' D E, repl_dec p' q' D E -> p' = p -> q' = q -> dec_eq G D E).
Proof.
  apply repl_mutind; intros; subst;
    eauto using path_eq_fields, (proj1 (typ_eq_refl_all G)), (proj2 (typ_eq_refl_all G)) with pdot_eq.
Qed.

Lemma open_eq_path G k p q r s :
  alias_targets_typed G -> path_eq G p q -> path_eq G r s ->
  path_eq G (open_rec_path_p k p r) (open_rec_path_p k q s).
Proof.
  intros W P Q. destruct (eq_names W Q) as [->|[[x [bs ->]] [y [cs ->]]]].
  - destruct s as [[i|x] bs], p, q; cbn; auto.
    destruct (classicT (k = i)); auto using path_eq_refl.
    exact (path_eq_fields bs P).
  - destruct p, q; exact Q.
Qed.

Lemma open_eq_typ_all G p q (W : alias_targets_typed G) (P : path_eq G p q) :
  (forall T U, typ_eq G T U -> forall k,
    typ_eq G (open_rec_typ_p k p T) (open_rec_typ_p k q U)) /\
  (forall D E, dec_eq G D E -> forall k,
    dec_eq G (open_rec_dec_p k p D) (open_rec_dec_p k q E)).
Proof. apply typ_eq_mut; intros; cbn; eauto using open_eq_path with pdot_eq. Qed.

Definition typ_rewrite G T U := exists p q, path_eq G p q /\ repl_typ p q T U.
Definition dec_rewrite G D E := exists p q, path_eq G p q /\ repl_dec p q D E.

Lemma pdot_star_map A B (R : A -> A -> Prop) (S : B -> B -> Prop) (f : A -> B) :
  (forall x y, R x y -> S (f x) (f y)) ->
  forall x y, star R x y -> star S (f x) (f y).
Proof. intros M x y H; induction H; eauto using star_refl, star_step. Qed.

Local Hint Constructors repl_typ repl_dec : pdot_eq.
Local Ltac pdot_rewrite_map f :=
  match goal with H : star ?R _ _ |- star ?S _ _ =>
    eapply (@pdot_star_map _ _ R S f); [|exact H];
    intros ? ? [? [? [? ?]]]; do 2 eexists; split; [eassumption | eauto with pdot_eq]
  end.

Lemma typ_eq_rewrites_all G :
  (forall T U, typ_eq G T U -> star (typ_rewrite G) T U) /\
  (forall D E, dec_eq G D E -> star (dec_rewrite G) D E).
Proof.
  apply typ_eq_mut; intros; try solve [apply star_refl].
  - pdot_rewrite_map typ_rcd.
  - eapply pdot_star_trans with (b:=S' ∧ T).
    + pdot_rewrite_map (fun x => x ∧ T).
    + pdot_rewrite_map (fun x => S' ∧ x).
  - eapply star_step; [|apply star_refl].
    exists p, q. split; auto.
    pose proof (rpath p q nil A) as R. now rewrite !sel_fields_nil in R.
  - pdot_rewrite_map typ_bnd.
  - eapply pdot_star_trans with (b:=∀(S') T).
    + pdot_rewrite_map (fun x => ∀(x) T).
    + pdot_rewrite_map (fun x => ∀(S') x).
  - eapply star_step; [|apply star_refl].
    exists p, q. split; auto.
    pose proof (rsngl p q nil) as R. now rewrite !sel_fields_nil in R.
  - pdot_rewrite_map (dec_trm a).
  - eapply pdot_star_trans with (b:={A >: S' <: T}).
    + pdot_rewrite_map (fun x => {A >: x <: T}).
    + pdot_rewrite_map (fun x => {A >: S' <: x}).
Qed.

Lemma typ_eq_sub G T U :
  alias_targets_typed G -> typ_eq G T U -> G ⊢ T <: U.
Proof.
  intros W E. pose proof (proj1 (typ_eq_rewrites_all G) _ _ E) as R.
  clear E. induction R; eauto using subtyp_refl.
  destruct H as [p [q [P Q]]]. eauto using eq_repl_sub, subtyp_trans.
Qed.

Definition member_at G p A T :=
  exists r U, path_eq G p r /\ slot G r (μ U) /\
    record_has (open_typ_p r U) {A >: T <: T}.

Lemma member_at_move G p q A T :
  inert G -> path_eq G p q -> member_at G p A T -> member_at G q A T.
Proof.
  intros I E [r [U [P K]]]. exists r, U. split; auto.
  eauto using path_eq_trans, path_eq_sym.
Qed.

Lemma object_slot_inert G p U :
  inert G -> slot G p (μ U) -> inert_typ (μ U).
Proof. intros I P. destruct (slot_shape I P) as [J|[q E]]; auto; discriminate. Qed.

Lemma member_at_unique G p A T V :
  inert G -> member_at G p A T -> member_at G p A V -> T = V.
Proof.
  intros I [r [U [E [P R]]]] [s [W [F [Q K]]]].
  assert (C : path_eq G r s) by eauto using path_eq_trans, path_eq_sym.
  pose proof (path_eq_slot I Q (object_slot_inert I Q) C) as B.
  inversion B; subst.
  - pose proof (slot_unique I P Q) as J. injection J as <-.
    pose proof (object_slot_inert I P) as H. inversion H; subst.
    match goal with Z : record_typ U ?L |- _ =>
      pose proof (record_has_unique (record_open s Z) R K eq_refl) as D;
      now injection D
    end.
  - exfalso. eapply slot_inert_terminal; [exact I | exact P | eauto using object_slot_inert | eassumption].
Qed.

(* An exposed head is reached through intersection projections and exact type
   selections. The observation depth bounds descent under fields and recursive
   types. Typing validates the observations at every depth. *)
Definition is_head T : Prop :=
  match T with
  | typ_top | typ_and _ _ | typ_path _ _ => False
  | _ => True
  end.

Inductive exposes G : typ -> typ -> Prop :=
| exp_head : forall T, is_head T -> exposes G T T
| exp_left : forall T U A, exposes G T A -> exposes G (T ∧ U) A
| exp_right : forall T U A, exposes G U A -> exposes G (T ∧ U) A
| exp_sel : forall p A T U, member_at G p A T -> exposes G T U -> exposes G (p ↓ A) U.

Local Hint Constructors exposes : pdot_exp.

Lemma exposes_is_head G T A : exposes G T A -> is_head A.
Proof. induction 1; auto. Qed.

Lemma exposes_atomic G T A : is_head T -> exposes G T A -> T = A.
Proof. intros H E. inversion E; subst; cbn in H; tauto. Qed.

Lemma typ_eq_exposes G T U A :
  inert G -> typ_eq G T U -> exposes G U A ->
  exists B, exposes G T B /\ typ_eq G B A.
Proof.
  intros I E H. revert T E. induction H; intros V E; inversion E; subst;
    cbn in *; try contradiction; eauto 6 using (proj1 (typ_eq_refl_all G)) with pdot_exp pdot_eq.
  - first [edestruct IHexposes as [B [P Q]]; [eassumption | exists B; eauto with pdot_exp]].
  - first [edestruct IHexposes as [B [P Q]]; [eassumption | exists B; eauto with pdot_exp]].
  - exists U. split; eauto using member_at_move, path_eq_sym, (proj1 (typ_eq_refl_all G)) with pdot_exp.
Qed.

Lemma record_exposes G T L A :
  record_typ T L -> exposes G T A -> exists D, A = typ_rcd D /\ record_has T D.
Proof.
  intros R. revert A. induction R; intros V E.
  - assert (typ_rcd D = V) by (eapply exposes_atomic; [exact Logic.I | exact E]).
    subst V. exists D. split; [reflexivity | constructor].
  - inversion E as [|? ? ? Lft|? ? ? Rgt|]; subst; cbn in *; try contradiction.
    + destruct (IHR _ Lft) as [D0 [-> Q]]. exists D0. split; eauto with pdot_record.
    + assert (typ_rcd D = V) by (eapply exposes_atomic; [exact Logic.I | exact Rgt]).
      subst V. exists D. split; [reflexivity | apply rh_andr; constructor].
Qed.

Definition arrow_le G S T U V :=
  forall p, G ⊢ trm_path p : U ->
  G ⊢ trm_path p : S /\ G ⊢ open_typ_p p T <: open_typ_p p V.

Lemma arrow_le_trans G S T U V W X :
  arrow_le G S T U V -> arrow_le G U V W X -> arrow_le G S T W X.
Proof.
  intros F K p H. destruct (K _ H) as [P Q]. destruct (F _ P).
  split; eauto using subtyp_trans.
Qed.

Lemma arrow_le_eq G S T U V :
  alias_targets_typed G -> typ_eq G S U -> typ_eq G T V -> arrow_le G S T U V.
Proof.
  intros W E F p H. split.
  - eapply ty_sub; [exact H|].
    eauto using typ_eq_sub, (proj1 (typ_eq_sym_all G)).
  - apply typ_eq_sub; auto.
    eapply (proj1 (open_eq_typ_all W (path_eq_refl G p))); exact F.
Qed.

Definition head_le G (le : typ -> typ -> Prop) S T : Prop :=
  match S, T with
  | typ_bot, _ => True
  | typ_rcd (dec_trm a U), typ_rcd (dec_trm b V) => a = b /\ le U V
  | typ_rcd (dec_typ a U U'), typ_rcd (dec_typ b V V') =>
      a = b /\ le V U /\ le U' V'
  | typ_bnd U, typ_bnd V => typ_eq G U V
  | typ_all U U', typ_all V V' => arrow_le G U U' V V'
  | typ_sngl p, typ_sngl q => path_eq G p q
  | _, _ => False
  end.

Fixpoint viewed_sub G n (T U : typ) : Prop :=
  match n with
  | 0 => True
  | S k => forall B, exposes G U B ->
    exists A, exposes G T A /\ head_le G (viewed_sub G k) A B
  end.

Lemma head_le_trans G (R : typ -> typ -> Prop) :
  inert G -> (forall T U V, R T U -> R U V -> R T V) ->
  forall T U V, head_le G R T U -> head_le G R U V -> head_le G R T V.
Proof.
  intros I Trans T U V P Q.
  destruct T, U, V;
    repeat match goal with d : dec |- _ => destruct d end;
    cbn in *; try contradiction; try exact Logic.I;
    try solve [intuition subst; eauto using path_eq_trans, arrow_le_trans, (proj1 (typ_eq_trans_all I))].
Qed.

Lemma viewed_sub_trans G n T U V :
  inert G -> viewed_sub G n T U -> viewed_sub G n U V -> viewed_sub G n T V.
Proof.
  intros I. revert T U V. induction n; intros T U V P Q; cbn in *; auto.
  intros B H. destruct (Q _ H) as [A [J K]]. destruct (P _ J) as [C [L M]].
  exists C. split; eauto using head_le_trans.
Qed.

Lemma viewed_sub_eq G n T U :
  inert G -> alias_targets_typed G -> typ_eq G T U -> viewed_sub G n T U.
Proof.
  intros I W. revert T U. induction n; cbn; intros T U E; auto.
  intros B H. destruct (typ_eq_exposes I E H) as [A [K R]]. exists A; split; auto.
  pose proof (exposes_is_head H) as HB.
  inversion R; subst; cbn in *; try contradiction; auto using arrow_le_eq.
  - match goal with D : dec_eq _ _ _ |- _ => inversion D; subst end.
    all: cbn; repeat split; try reflexivity; apply IHn;
      first [assumption | eapply (proj1 (typ_eq_sym_all G)); eassumption].
Qed.

Lemma viewed_sub_refl G n T :
  inert G -> alias_targets_typed G -> viewed_sub G n T T.
Proof. eauto using viewed_sub_eq, (proj1 (typ_eq_refl_all G)). Qed.

Definition at_head G (valid : path -> typ -> Prop) (le : typ -> typ -> Prop) p T :=
  match T with
  | typ_bot => False
  | typ_rcd (dec_trm a U) => valid (p•a) U
  | typ_rcd (dec_typ A D U) => exists V, member_at G p A V /\ le D V /\ le V U
  | typ_bnd U => valid p (open_typ_p p U)
  | typ_all D U => exists r S' U',
      path_eq G p r /\ slot G r (∀(S') U') /\ arrow_le G S' U' D U
  | typ_sngl q => path_eq G p q
  | _ => True
  end.

Fixpoint viewed_path G n p T : Prop :=
  match n with
  | 0 => accessible G p
  | S k => accessible G p /\
      forall A, exposes G T A -> at_head G (viewed_path G k) (viewed_sub G k) p A
  end.

Lemma viewed_accessible G n p T : viewed_path G n p T -> accessible G p.
Proof. destruct n; cbn; tauto. Qed.

Lemma viewed_move G n p q T U :
  inert G -> alias_targets_typed G ->
  path_eq G p q -> accessible G q -> viewed_sub G n T U ->
  viewed_path G n p T -> viewed_path G n q U.
Proof.
  intros I W. revert p q T U.
  induction n; intros p q T U E Ac L P; cbn in *; auto.
  split; auto. intros B H.
  destruct (L _ H) as [A [R J]]. destruct P as [P M].
  specialize (M _ R).
  destruct A, B; repeat match goal with d : dec |- _ => destruct d end;
    cbn in *; try contradiction; auto.
  - destruct J as [-> [S1 S2]]. destruct M as [V [K [Q1 Q2]]].
    exists V. eauto 7 using member_at_move, viewed_sub_trans.
  - destruct J as [-> J].
    eapply IHn; [eauto using path_eq_field |
      eauto using viewed_accessible, accessible_field_eq | exact J | exact M].
  - eapply IHn; [exact E|exact Ac| |exact M].
    apply viewed_sub_eq; auto.
    eapply (proj1 (open_eq_typ_all W E)); exact J.
  - destruct M as [r [S [V [K [Q F]]]]].
    exists r, S, V. eauto 7 using path_eq_trans, path_eq_sym, arrow_le_trans.
  - eauto 7 using path_eq_trans, path_eq_sym.
Qed.

Lemma viewed_slot G n :
  inert G -> alias_targets_typed G ->
  (forall p T, slot G p T -> viewed_path G n p T) /\
  (forall p U, slot G p (μ U) -> viewed_path G n p (open_typ_p p U)).
Proof.
  intros I W. induction n.
  - split; cbn; eauto using slot_accessible.
  - split.
    + intros p T H. cbn. split; eauto using slot_accessible.
      intros B E. destruct (slot_shape I H) as [J|[q ->]].
      * destruct J as [S U|U L R].
        -- assert (B = ∀(S) U) by (symmetry; eapply exposes_atomic; cbn; eauto). subst.
           cbn. exists p, S, U. split; [apply path_eq_refl | split; auto].
           intros q Q. split; auto using subtyp_refl.
        -- assert (B = μ U) by (symmetry; eapply exposes_atomic; cbn; eauto). subst.
           cbn. now apply (proj2 IHn).
      * assert (B = {{q}}) by (symmetry; eapply exposes_atomic; cbn; eauto). subst.
        cbn. exists q. split; eauto using alias_slot, star_refl, star_step.
    + intros p U H. pose proof (object_slot_inert I H) as J. inversion J; subst.
      cbn. split; eauto using slot_accessible.
      intros A E.
      match goal with R : record_typ U _ |- _ =>
        destruct (record_exposes (record_open p R) E) as [D [-> Q]];
        destruct (record_has_info (record_open p R) Q) as [K _]
      end.
      inversion K; subst; cbn.
      * eexists. split; [exists p, U; eauto using path_eq_refl |].
        split; eauto using viewed_sub_refl.
      * apply (proj1 IHn). econstructor; eauto.
      * apply (proj1 IHn). econstructor; eauto.
Qed.

Definition path_sound G p T := forall n, viewed_path G n p T.
Definition sub_sound G T U := forall n, viewed_sub G n T U.

Lemma sound_single G p q : path_sound G p {{q}} -> path_eq G p q.
Proof.
  intros H. specialize (H 1). apply (proj2 H {{q}}). constructor. exact I.
Qed.

Lemma sound_access G p T : path_sound G p T -> accessible G p.
Proof. intros H; exact (H 0). Qed.

Lemma sound_field G p a T : path_sound G p (typ_rcd {a ⦂ T}) -> path_sound G (p•a) T.
Proof. intros H n. apply (proj2 (H (S n)) (typ_rcd {a ⦂ T})); constructor; exact I. Qed.

Lemma sound_rec G p T : path_sound G p (μ T) -> path_sound G p (open_typ_p p T).
Proof. intros H n. apply (proj2 (H (S n)) (μ T)); constructor; exact I. Qed.

Lemma sound_member G p A S T n :
  path_sound G p (typ_rcd {A >: S <: T}) ->
  exists V, member_at G p A V /\ viewed_sub G n S V /\ viewed_sub G n V T.
Proof.
  intros H. apply (proj2 (H (Datatypes.S n)) (typ_rcd {A >: S <: T})); constructor; exact I.
Qed.

Lemma sound_arrow G p S T :
  path_sound G p (∀(S) T) ->
  exists r U V, path_eq G p r /\ slot G r (∀(U) V) /\ arrow_le G U V S T.
Proof. intros H. apply (proj2 (H 1) (∀(S) T)); constructor; exact I. Qed.

Lemma sound_let_sub G p T U :
  inert G -> alias_targets_typed G -> path_sound G p T -> sub_sound G T U -> path_sound G p U.
Proof. intros I W P S n; eauto using viewed_move, path_eq_refl, sound_access. Qed.

Lemma head_le_refl G n T :
  inert G -> alias_targets_typed G -> is_head T -> head_le G (viewed_sub G n) T T.
Proof.
  intros I W H. destruct T; cbn in *; try contradiction;
    eauto using path_eq_refl, (proj1 (typ_eq_refl_all G)).
  - destruct d; cbn; repeat split; auto using viewed_sub_refl.
  - intros p P. split; auto using subtyp_refl.
Qed.

Lemma typing_sound_all :
  (forall G t T, G ⊢ t : T ->
    inert G -> alias_targets_typed G ->
    match t with trm_path p => path_sound G p T | _ => True end) /\
  (forall G T U, G ⊢ T <: U -> inert G -> alias_targets_typed G -> sub_sound G T U).
Proof.
  apply ts_mutind; cbn; intros; try exact Logic.I.
  all: repeat match goal with
    | IH : inert ?G -> alias_targets_typed ?G -> _,
      I : inert ?G, W : alias_targets_typed ?G |- _ => specialize (IH I W)
    end.
  - intro n. apply (proj1 (viewed_slot n H H0)); now constructor.
  - eauto using sound_field.
  - intro n. assert (A : accessible G p) by eauto using accessible_parent, sound_access.
    destruct n; cbn; auto. split; auto. intros B E.
    assert (B = typ_rcd {a ⦂ T}) by (symmetry; eapply exposes_atomic; cbn; eauto).
    subst; cbn. exact (H n).
  - intro n. eapply viewed_move; eauto using sound_single, path_eq_sym, sound_access, viewed_sub_refl.
  - intro n. assert (E : path_eq G p q) by eauto using sound_single.
    assert (A : accessible G (p•a)) by eauto using accessible_field_eq, path_eq_sym, sound_access.
    destruct n; cbn; auto. split; auto. intros B P.
    assert (B = {{q•a}}) by (symmetry; eapply exposes_atomic; cbn; eauto). subst; cbn.
    eauto using path_eq_field.
  - intro n. destruct n; [exact (H 0) |].
    cbn. split; [exact (H 0) |]. intros B E.
    assert (B = μ T) by (symmetry; eapply exposes_atomic; cbn; eauto). subst; cbn.
    exact (H n).
  - eauto using sound_rec.
  - intro n. destruct n; [exact (H 0) |].
    cbn. split; [exact (H 0) |]. intros B E. inversion E; subst; cbn in *; try contradiction;
      solve [match goal with H : path_sound _ _ _ |- _ =>
        eapply (proj2 (H (Datatypes.S n))); eassumption
      end].
  - destruct t; cbn in *; try exact Logic.I. eauto using sound_let_sub.
  - intro n. destruct n; cbn; auto. intros B E; inversion E; subst; contradiction.
  - intro n. destruct n; cbn; auto. intros B E; exists ⊥; split; [constructor |]; exact Logic.I.
  - intro n; apply viewed_sub_refl; assumption.
  - intro n; eapply viewed_sub_trans; eauto.
  - intro n. destruct n; cbn; auto. intros B E. exists B; split; eauto with pdot_exp.
    eauto using head_le_refl, exposes_is_head.
  - intro n. destruct n; cbn; auto. intros B E. exists B; split; eauto with pdot_exp.
    eauto using head_le_refl, exposes_is_head.
  - intro n. destruct n; cbn; auto. intros B E. inversion E; subst; cbn in *; try contradiction;
      solve [match goal with H : sub_sound _ _ _ |- _ =>
        eapply (H (Datatypes.S n)); assumption
      end].
  - intro n. destruct n; cbn; auto. intros B E.
    assert (B = typ_rcd {a ⦂ U}) by (symmetry; eapply exposes_atomic; cbn; eauto). subst.
    exists (typ_rcd {a ⦂ T}); split; [constructor; exact Logic.I |].
    cbn. split; [reflexivity | exact (H n)].
  - intro n. destruct n; cbn; auto. intros B E.
    assert (B = typ_rcd {A >: S2 <: T2}) by (symmetry; eapply exposes_atomic; cbn; eauto). subst.
    exists (typ_rcd {A >: S1 <: T1}); split; [constructor; exact Logic.I |].
    cbn. repeat split; [exact (H n) | exact (H0 n)].
  - intro n. apply viewed_sub_eq; auto.
    assert (E : path_eq G p q) by eauto using sound_single.
    eapply (proj1 (typ_eq_repl_all E)); eauto.
  - intro n. apply viewed_sub_eq; auto.
    assert (E : path_eq G p q) by eauto using sound_single.
    eapply (proj1 (typ_eq_repl_all (path_eq_sym E))); eauto.
  - intro n.
    destruct (sound_member n H) as [V [M [K J]]].
    destruct n; cbn in *; auto. intros B E. inversion E; subst; cbn in *; try contradiction.
    assert (V = T0) by eauto using member_at_unique. subst. eauto.
  - intro n.
    destruct (sound_member n H) as [V [M [K J]]].
    destruct n; cbn in *; auto. intros B E. destruct (J _ E) as [C [D F]].
    exists C; eauto with pdot_exp.
  - intro n. destruct n; cbn; auto. intros B E.
    assert (B = ∀(S2) T2) by (symmetry; eapply exposes_atomic; cbn; eauto). subst.
    exists (∀(S1) T1); split; [constructor; exact Logic.I|].
    cbn. intros p P. split; eauto using ty_sub, all_sub_inst, typing_named.
Qed.

Lemma typed_path_sound G p T :
  inert G -> alias_targets_typed G -> G ⊢ trm_path p : T -> path_sound G p T.
Proof. intros I W P. exact (proj1 typing_sound_all _ _ _ P I W). Qed.

Lemma typed_sub_sound G T U :
  inert G -> alias_targets_typed G -> G ⊢ T <: U -> sub_sound G T U.
Proof. intros I W P. exact (proj2 typing_sound_all _ _ _ P I W). Qed.

Lemma typed_wf G γ :
  inert G -> precise_heap G γ -> wf G ->
  forall x v T, x # G -> inert_typ T ->
  precise_heap (G & x ~ T) (γ & x ~ v) -> wf (G & x ~ T).
Proof.
  intros I H W x v T F J K.
  constructor; auto. intros bs q P.
  assert (I' : inert (G & x ~ T)) by (constructor; auto).
  destruct (flow_slot I' P) as [B _].
  pose proof (heap_alias_targets K) as A.
  destruct (A _ _ B) as [U Q].
  eapply accessible_precise; [exact I' |].
  eapply sound_access. eapply typed_path_sound; eauto.
Qed.

Lemma arrow_sub_inv G S T U V :
  inert G -> alias_targets_typed G ->
  G ⊢ ∀(S) T <: ∀(U) V -> arrow_le G S T U V.
Proof.
  intros I W H. pose proof (typed_sub_sound I W H 1) as J. cbn in J.
  assert (E : exposes G (∀(U) V) (∀(U) V)) by (constructor; exact Logic.I).
  destruct (J _ E) as [A [K R]].
  assert (A = ∀(S) T) by (symmetry; eapply exposes_atomic; cbn; eauto).
  subst; exact R.
Qed.

Lemma application_step G γ p q S T :
  inert G -> precise_heap G γ ->
  G ⊢ trm_path p : ∀(S) T -> G ⊢ trm_path q : S ->
  exists u, (γ, trm_app p q) ⟼ (γ, u) /\ G ⊢ u : open_typ_p q T.
Proof.
  intros I W P Q.
  pose proof (heap_alias_targets W) as A.
  destruct (sound_arrow (typed_path_sound I A P)) as [r [S' [T' [E [B L]]]]].
  assert (J : star (alias_step G) p r) by eauto using path_eq_slot, inert_typ_all.
  pose proof (slot_contents_sound W B) as H. inversion H; subst.
  match goal with K : G ⊢ trm_val (λ(_) _) : _ |- _ =>
    destruct (value_typing_precise K) as [V [C D]]
  end.
  inversion C; subst.
  assert (F : arrow_le G S0 U S T).
  { eapply arrow_le_trans; [eapply arrow_sub_inv; eauto | exact L]. }
  destruct (F q Q) as [PQ ST].
  eexists; split.
  - eapply red_app. eapply pdot_star_trans; [eapply alias_star_lookup; eauto |].
    eapply star_step; [eassumption | apply star_refl].
  - eapply ty_sub; [eapply lambda_inst; eauto using typing_named | exact ST].
Qed.

Lemma extend_root G x v T L :
  x # G ->
  (match v with
   | λ(D) t => G ⊢!v λ(D) t : T
   | ν(V) ds => T = μ V /\
       (forall z, z \notin L ->
         z; nil; G & z ~ open_typ z V ⊢ open_defs z ds :: open_typ z V)
   end) ->
  x \notin L -> root_val (G & x ~ T) x v T.
Proof.
  intros F P K; destruct v as [V ds|S t]; cbn in P.
  - destruct P as [-> B]. apply root_obj. rewrite <- open_defs_var, <- open_typ_var.
    eapply defs_morph; [exact (B x K) |].
    apply narrow_push; auto. rewrite open_typ_var.
    eapply ty_rec_elim. apply ty_var, binds_push_eq.
  - inversion P; subst. apply root_fun.
    eapply precise_val_weaken; eauto using ctx_incl_fresh.
Qed.

Lemma value_cofinite G v T :
  G ⊢!v v : T ->
  exists L, match v with
   | λ(D) t => G ⊢!v λ(D) t : T
   | ν(V) ds => T = μ V /\
       (forall z, z \notin L ->
         z; nil; G & z ~ open_typ z V ⊢ open_defs z ds :: open_typ z V)
   end.
Proof.
  intro P; destruct P.
  - exists (\{} : vars). eapply ty_all_intro_p; eauto.
  - exists L. auto.
Qed.

Definition heap_safe G γ :=
  γ ⫶ G /\ wf G /\ inert G /\ precise_heap G γ.

Lemma heap_safe_empty : heap_safe empty empty.
Proof.
  repeat split; try constructor. intros ? ? H. exact (False_rect _ (binds_empty_inv H)).
Qed.

Lemma heap_safe_push G γ x v T :
  heap_safe G γ -> x # G -> x # γ -> G ⊢!v v : T ->
  root_val (G & x ~ T) x v T -> heap_safe (G & x ~ T) (γ & x ~ v).
Proof.
  intros [H [W [I P]]] F K J R.
  assert (S : inert_typ T) by eauto using precise_val_inert.
  assert (Q : precise_heap (G & x ~ T) (γ & x ~ v)) by eauto using precise_heap_push.
  repeat split; eauto using well_typed_push, precise_val_typing, typed_wf, inert_push.
Qed.

(* Choose a reduction that preserves the heap invariants and extends the
   typing context. Allocation chooses the name from the cofinite premises. *)
Lemma safe_next G t T :
  G ⊢ t : T -> forall γ, heap_safe G γ ->
  norm_form t \/
  exists γ' u G', (γ,t) ⟼ (γ',u) /\ G' ⊢ u : T /\
    heap_safe G' γ' /\ ctx_incl G G'.
Proof.
  intros H; induction H; intros γ W;
    try solve [left; constructor].
  - right. destruct W as [B [W [I K]]].
    destruct (application_step I K H H0) as [u [R P]].
    exists γ, u, G; repeat split; auto. intros ? ? Q; exact Q.
  - right. destruct (IHty_trm _ W) as [N|[γ' [u' [G' [R [P [K C]]]]]]].
    + destruct N as [p|v].
      * exists γ, (open_trm_p p u), G.
        split; [constructor |]. split; [eauto using let_inst, typing_named |].
        split; auto. intros ? ? Q; exact Q.
      * destruct (value_typing_precise H) as [V [J D]].
        destruct (value_cofinite J) as [K B].
        destruct (var_fresh (L \u K \u dom G \u dom γ)) as [x F]. pdot_fresh F.
        exists (γ & x ~ v), (open_trm x u), (G & x ~ V).
        split; [constructor; assumption |]. split.
        -- eapply typing_morph; [eauto |]. apply narrow_push; auto.
           eapply ty_sub; [apply ty_var, binds_push_eq |].
           eapply (proj2 (proj2 (proj2 weakening_all))); eauto using ctx_incl_fresh.
        -- split; [|now apply ctx_incl_fresh].
           eapply heap_safe_push; eauto using extend_root.
    + exists γ', (trm_let u' u), G'.
      split; [now apply red_let_tgt |]. split; [|auto].
      eapply ty_let with (L := L); [exact P|].
      intros x F. eapply typing_weaken; eauto using ctx_incl_push.
  - destruct (IHty_trm _ W) as [N|[γ' [u [G' [R [P [K C]]]]]]]; auto.
    right. exists γ', u, G'. split; auto.
    split; [|auto]. eapply ty_sub; [exact P |].
    eapply (proj2 (proj2 (proj2 weakening_all))); eauto.
Qed.

Definition diverges := infseq red.

Lemma safe_alternatives G γ t T :
  heap_safe G γ -> G ⊢ t : T ->
  diverges (γ,t) \/
  exists γ' u G', (γ,t) ⟼* (γ',u) /\
      norm_form u /\ G' ⊢ u : T /\ γ' ⫶ G' /\ wf G' /\ inert G'.
Proof.
  intros W H.
  destruct (classic (exists γ' u G', (γ,t) ⟼* (γ',u) /\
      norm_form u /\ G' ⊢ u : T /\ γ' ⫶ G' /\ wf G' /\ inert G')) as [Q|Q]; auto.
  (* In the absence of a reachable well-typed normal form, each chosen step
     supplies one constructor of the infinite reduction sequence. *)
  left. revert G γ t W H Q. cofix CO. intros G γ t W H Q.
  destruct (safe_next H W) as [N|[γ' [u [G' [R [P [K _]]]]]]].
  - exfalso. destruct W as [A [B [C _]]].
    apply Q. exists γ, t, G. repeat split; auto using star_refl.
  - eapply infseq_step; [exact R |].
    eapply (CO G' γ' u K P). intros [γ'' [v [G'' [S V]]]].
    apply Q. exists γ'', v, G''. split; auto.
    eapply star_step; eauto.
Qed.


Theorem safety t T :
  empty ⊢ t : T ->
  diverges (empty, t) \/
  (exists γ u G, (empty, t) ⟼* (γ, u) /\
            norm_form u /\
            G ⊢ u : T /\
            γ ⫶ G /\
            wf G /\
            inert G).

Proof.
  intro H. exact (safe_alternatives heap_safe_empty H).
Qed.

End Safety.
