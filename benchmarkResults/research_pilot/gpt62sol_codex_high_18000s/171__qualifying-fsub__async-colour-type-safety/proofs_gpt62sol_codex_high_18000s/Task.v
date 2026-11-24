From Fsub.FuncColour Require Import Fsub_LetSum_Definitions.

Local Hint Constructors wf_qua wf_typ wf_qtyp wf_env qual type qtype
  subqual sub subqtype typing typing_ctx typing_state value expr : core.

Lemma sq_regular : forall E P Q, subqual E P Q ->
  wf_env E /\ wf_qua E P /\ wf_qua E Q.
Proof. induction 1; intuition eauto. Qed.

Lemma sq_refl : forall E Q, wf_env E -> wf_qua E Q -> subqual E Q Q.
Proof. intros E Q HE H; induction H; eauto 8. Qed.

Lemma sq_trans : forall E P Q R, subqual E P Q -> subqual E Q R ->
  subqual E P R.
Proof.
  intros E P Q R H. revert R.
  induction H; intros S HS;
    try solve [destruct (sq_regular _ _ _ HS) as [? [? ?]]; eauto].
  all: try solve [induction HS; eauto].
  all: try match goal with
  | H : subqual ?E ?Q _, HS : subqual ?E ?M ?S |- subqual ?E ?Q ?S =>
    pose proof (proj1 (proj2 (sq_regular _ _ _ H)))
  end.
  all: try solve [remember qua_top as M eqn:HM;
    induction HS; inversion HM; subst; eauto].
  all: try solve [remember (qua_join R1 R2) as M eqn:HM;
    induction HS; inversion HM; subst; eauto].
  all: try solve [remember (qua_meet R1 R2) as M eqn:HM;
    induction HS; inversion HM; subst; eauto].
  all: try solve [remember (qua_fvar X) as M eqn:HM;
    induction HS; inversion HM; subst; eauto].
Qed.

Lemma sq_meet_l : forall E P Q, wf_env E -> wf_qua E P -> wf_qua E Q ->
  subqual E (qua_meet P Q) P.
Proof. eauto using sq_refl. Qed.

Lemma sq_meet_r : forall E P Q, wf_env E -> wf_qua E P -> wf_qua E Q ->
  subqual E (qua_meet P Q) Q.
Proof. eauto using sq_refl. Qed.

Lemma wf_qua_qual : forall E Q, wf_qua E Q -> qual Q.
Proof. induction 1; eauto. Qed.

Lemma concrete_total : forall Q, wf_qua empty Q -> exists s, concretize Q = Some s.
Proof.
  intros Q H; remember empty as E; induction H; subst; simpl in *; eauto.
  - inversion H.
  - destruct IHwf_qua1 as [[] ?]; auto; rewrite H1; eauto.
  - destruct IHwf_qua1 as [[] ?]; auto; rewrite H1; eauto.
Qed.

Lemma concrete_order : forall E P Q,
  subqual E P Q -> forall s t, concretize P = Some s -> concretize Q = Some t -> s ≤ t.
Proof.
  induction 1; simpl; intros s t HP HQ;
    try solve [inversion HP; inversion HQ; subst; destruct s || destruct t; constructor];
    try discriminate.
  - destruct (concretize R1) as [[]|] eqn:HR; inversion HQ; subst;
      try (destruct s; constructor).
    pose proof (IHsubqual _ _ HP eq_refl) as Hle.
    inversion Hle; subst; destruct t; constructor.
  - destruct (concretize R1) as [[]|] eqn:HR; inversion HQ; subst;
      eauto; destruct s; constructor.
  - destruct (concretize R1) as [[]|] eqn:HR; inversion HP; subst; eauto.
  - destruct (concretize R1) as [[]|] eqn:HR; inversion HP; subst;
      try (destruct t; constructor).
    pose proof (IHsubqual _ _ eq_refl HQ) as Hle.
    inversion Hle; subst; destruct s; constructor.
  - destruct (concretize R1) as [[]|] eqn:HR; inversion HP; subst;
      eauto; destruct t; constructor.
  - destruct (concretize R1) as [[]|] eqn:HR; inversion HQ; subst; eauto.
Qed.

Lemma concrete_equiv : forall E Q, wf_env E -> wf_qua E Q ->
  forall s, concretize Q = Some s ->
  subqual E Q (abstractize s) /\ subqual E (abstractize s) Q.
Proof.
  intros E Q HE H; induction H; simpl; intros s HS; try discriminate;
    try solve [inversion HS; subst; simpl; eauto].
  - destruct (concretize Q1) as [[]|] eqn:H1; try discriminate.
    + destruct (IHwf_qua1 HE _ eq_refl); destruct (IHwf_qua2 HE _ HS); split; eauto. destruct s; simpl in *; eauto.
    + inversion HS; subst; destruct (IHwf_qua1 HE _ eq_refl); simpl in *; split; eauto.
  - destruct (concretize Q1) as [[]|] eqn:H1; try discriminate.
    + inversion HS; subst; destruct (IHwf_qua1 HE _ eq_refl); simpl in *; split; eauto.
    + destruct (IHwf_qua1 HE _ eq_refl); destruct (IHwf_qua2 HE _ HS) as [HA HB].
      split; eauto.
      apply subqual_join_elim; auto. destruct s; simpl in *; eauto.
Qed.

(* Environment changes that preserve each sort of variable membership. *)
Definition keep_sub (E F : env) :=
  forall X T, binds X (bind_sub T) E -> exists U, binds X (bind_sub U) F.
Definition keep_qua (E F : env) :=
  forall X Q, binds X (bind_qua Q) E -> exists R, binds X (bind_qua R) F.
Definition keep_binds (E F : env) :=
  forall (X : atom) b, binds X b E -> binds X b F.

Lemma keep_sub_cons : forall E F X b, keep_sub E F ->
  keep_sub ((X,b)::E) ((X,b)::F).
Proof.
  unfold keep_sub; intros E F X b H Y T B.
  apply binds_cons_iff in B. destruct B as [[? ?]|B].
  - subst; eexists; apply binds_cons_iff; eauto.
  - destruct (H _ _ B); eexists; apply binds_cons_iff; eauto.
Qed.

Lemma keep_qua_cons : forall E F X b, keep_qua E F ->
  keep_qua ((X,b)::E) ((X,b)::F).
Proof.
  unfold keep_qua; intros E F X b H Y Q B.
  apply binds_cons_iff in B. destruct B as [[? ?]|B].
  - subst; eexists; apply binds_cons_iff; eauto.
  - destruct (H _ _ B); eexists; apply binds_cons_iff; eauto.
Qed.

Lemma keep_binds_cons : forall E F X b, keep_binds E F ->
  keep_binds ((X,b)::E) ((X,b)::F).
Proof.
  unfold keep_binds; intros E F X b H Y a B.
  apply binds_cons_iff in B; apply binds_cons_iff; intuition eauto.
Qed.

Lemma keep_binds_sort : forall E F, keep_binds E F -> keep_sub E F /\ keep_qua E F.
Proof. unfold keep_binds, keep_sub, keep_qua; intros E F H; split; intros; eauto. Qed.

Lemma keep_binds_head : forall E X b, keep_binds E ((X,b)::E).
Proof. unfold keep_binds; intros; apply binds_cons_iff; auto. Qed.

Lemma wf_qua_env : forall E Q, wf_qua E Q -> forall F, keep_qua E F -> wf_qua F Q.
Proof. induction 1; intros F HF; eauto. destruct (HF _ _ H); eauto. Qed.

Scheme wf_t_ind := Induction for wf_typ Sort Prop
  with wf_qt_ind := Induction for wf_qtyp Sort Prop.
Combined Scheme wf_ty_ind from wf_t_ind, wf_qt_ind.

Lemma wf_ty_env :
  (forall E T, wf_typ E T -> forall F, keep_sub E F -> keep_qua E F -> wf_typ F T) /\
  (forall E T, wf_qtyp E T -> forall F, keep_sub E F -> keep_qua E F -> wf_qtyp F T).
Proof.
  apply wf_ty_ind; intros; eauto using wf_qua_env, keep_sub_cons, keep_qua_cons.
  - destruct (H _ _ b); eauto.
  - eapply wf_typ_all with (L := L); eauto using keep_sub_cons, keep_qua_cons.
    intros; eapply H0; cbn; eauto using keep_sub_cons, keep_qua_cons.
  - eapply wf_typ_qall with (L := L); eauto using wf_qua_env, keep_sub_cons, keep_qua_cons.
    intros; eapply H; cbn; eauto using keep_sub_cons, keep_qua_cons.
Qed.

Local Hint Resolve wf_qua_env : core.
Lemma wf_typ_env : forall E T, wf_typ E T ->
  forall F, keep_sub E F -> keep_qua E F -> wf_typ F T.
Proof. exact (proj1 wf_ty_env). Qed.
Lemma wf_qtyp_env : forall E T, wf_qtyp E T ->
  forall F, keep_sub E F -> keep_qua E F -> wf_qtyp F T.
Proof. exact (proj2 wf_ty_env). Qed.

Lemma wf_env_bind :
  forall E, wf_env E ->
  forall X b, binds X b E ->
  match b with
  | bind_sub T => wf_typ E T
  | bind_typ T => wf_qtyp E T
  | bind_qua Q => wf_qua E Q
  end.
Proof.
  induction 1; intros Y b HB; [inversion HB|..];
    apply binds_cons_iff in HB; destruct HB as [[? ?]|HB]; subst;
    try specialize (IHwf_env _ _ HB);
    try destruct b; cbn;
    match goal with |- context[((?X,?c)::?E)] =>
      destruct (keep_binds_sort _ _ (keep_binds_head E X c))
    end;
    eauto using wf_typ_env, wf_qtyp_env.
Qed.

Lemma wf_env_tail : forall X b E, wf_env ((X,b)::E) -> wf_env E.
Proof. inversion 1; auto. Qed.

Lemma wf_term_drop : forall E X V,
  keep_sub ((X, bind_typ V)::E) E /\ keep_qua ((X, bind_typ V)::E) E.
Proof.
  unfold keep_sub, keep_qua; split; intros Y B H;
    apply binds_cons_iff in H; destruct H as [[? H]|H]; try discriminate; eauto.
Qed.

Lemma wf_ty_local :
  (forall E T, wf_typ E T -> type T) /\ (forall E T, wf_qtyp E T -> qtype T).
Proof. apply wf_ty_ind; intros; eauto using wf_qua_qual. Qed.

Scheme sub_t_ind := Induction for sub Sort Prop
  with sub_qt_ind := Induction for subqtype Sort Prop.
Combined Scheme sub_ty_ind from sub_t_ind, sub_qt_ind.

Lemma sq_env : forall E P Q, subqual E P Q ->
  forall F, wf_env F -> keep_binds E F -> subqual F P Q.
Proof.
  induction 1; intros F HF HB; destruct (keep_binds_sort _ _ HB);
    unfold keep_binds in HB; eauto.
Qed.

Lemma keep_sub_change : forall E X T U,
  keep_sub ((X,bind_sub T)::E) ((X,bind_sub U)::E).
Proof.
  unfold keep_sub; intros E X T U Y V H; apply binds_cons_iff in H.
  destruct H as [[? ?]|?]; subst; eexists; apply binds_cons_iff; eauto.
Qed.
Lemma keep_qua_change : forall E X P Q,
  keep_qua ((X,bind_qua P)::E) ((X,bind_qua Q)::E).
Proof.
  unfold keep_qua; intros E X P Q Y R H; apply binds_cons_iff in H.
  destruct H as [[? ?]|?]; subst; eexists; apply binds_cons_iff; eauto.
Qed.
Lemma keep_sub_qua_change : forall E X P Q,
  keep_sub ((X,bind_qua P)::E) ((X,bind_qua Q)::E).
Proof.
  unfold keep_sub; intros E X P Q Y R H; apply binds_cons_iff in H.
  destruct H as [[? H]|?]; try discriminate; eexists; apply binds_cons_iff; eauto.
Qed.
Lemma keep_qua_sub_change : forall E X T U,
  keep_qua ((X,bind_sub T)::E) ((X,bind_sub U)::E).
Proof.
  unfold keep_qua; intros E X T U Y R H; apply binds_cons_iff in H.
  destruct H as [[? H]|?]; try discriminate; eexists; apply binds_cons_iff; eauto.
Qed.

Lemma sub_ty_regular :
  (forall E S T, sub E S T -> wf_env E /\ wf_typ E S /\ wf_typ E T) /\
  (forall E S T, subqtype E S T -> wf_env E /\ wf_qtyp E S /\ wf_qtyp E T).
Proof.
  apply sub_ty_ind; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with H : subqual _ _ _ |- _ =>
      destruct (sq_regular _ _ _ H) as [? [? ?]]; clear H end;
    try solve [intuition eauto].
  - repeat split; eauto.
    + eapply wf_typ_all with (L := L); eauto.
      intros X HX; destruct (H0 X HX) as [_ [HS _]].
      eapply wf_qtyp_env; [exact HS|cbn|cbn]; eauto using wf_qtyp_env, keep_sub_change, keep_qua_sub_change.
    + eapply wf_typ_all with (L := L); eauto.
      intros X HX; destruct (H0 X HX) as [_ [_ HT]]; exact HT.
  - repeat split; eauto.
    + eapply wf_typ_qall with (L := L); eauto.
      intros X HX; destruct (H X HX) as [_ [HS _]].
      eapply wf_qtyp_env; [exact HS|cbn|cbn]; eauto using wf_qtyp_env, keep_qua_change, keep_sub_qua_change.
    + eapply wf_typ_qall with (L := L); eauto.
      intros X HX; destruct (H X HX) as [_ [_ HT]]; exact HT.
Qed.

Lemma sub_regular : forall E S T, sub E S T -> wf_env E /\ wf_typ E S /\ wf_typ E T.
Proof. exact (proj1 sub_ty_regular). Qed.
Lemma subq_regular : forall E S T, subqtype E S T -> wf_env E /\ wf_qtyp E S /\ wf_qtyp E T.
Proof. exact (proj2 sub_ty_regular). Qed.

Lemma sub_ty_env :
  (forall E S T, sub E S T -> forall F, wf_env F -> keep_binds E F -> sub F S T) /\
  (forall E S T, subqtype E S T -> forall F, wf_env F -> keep_binds E F -> subqtype F S T).
Proof.
  apply sub_ty_ind; intros; try match goal with
  | H : keep_binds _ _ |- _ => destruct (keep_binds_sort _ _ H)
  end; eauto using wf_typ_env, sq_env.
  - eapply sub_all with (L := union L (dom F)); eauto.
    intros X HX. eapply H0; cbn; eauto using keep_binds_cons; try solve_notin.
    apply wf_env_sub; eauto; try solve_notin.
    destruct (sub_regular _ _ _ s) as [_ [HT _]].
    eauto using wf_typ_env.
  - eapply sub_qall with (L := union L (dom F)); eauto using sq_env.
    intros X HX. eapply H; cbn; eauto using keep_binds_cons; try solve_notin.
    apply wf_env_qua; eauto; try solve_notin.
    destruct (sq_regular _ _ _ s) as [_ [HT _]]; eauto.
Qed.

Lemma sub_env : forall E S T, sub E S T ->
  forall F, wf_env F -> keep_binds E F -> sub F S T.
Proof. exact (proj1 sub_ty_env). Qed.
Lemma subq_env : forall E S T, subqtype E S T ->
  forall F, wf_env F -> keep_binds E F -> subqtype F S T.
Proof. exact (proj2 sub_ty_env). Qed.

Lemma sub_ty_refl :
  (forall E T, wf_typ E T -> wf_env E -> sub E T T) /\
  (forall E T, wf_qtyp E T -> wf_env E -> subqtype E T T).
Proof.
  apply wf_ty_ind; intros; eauto using sq_refl.
  - eapply sub_all with (L := union L (dom E)); eauto; try solve_notin.
  - eapply sub_qall with (L := union L (dom E)); eauto using sq_refl; try solve_notin.
Qed.
Lemma sub_refl : forall E T, wf_typ E T -> wf_env E -> sub E T T.
Proof. exact (proj1 sub_ty_refl). Qed.
Lemma subq_refl : forall E T, wf_qtyp E T -> wf_env E -> subqtype E T T.
Proof. exact (proj2 sub_ty_refl). Qed.

Definition trans_at (M : typ) :=
  forall E S T, sub E S M -> sub E M T -> sub E S T.

(* These environment relations describe changes to a single bound, with the
   rest of the bindings carried through unchanged. *)
Record narrow_env (M : typ) (E F : env) : Prop := {
  ne_sub : forall X U, binds X (bind_sub U) E ->
    binds X (bind_sub U) F \/ (U = M /\ sub F (typ_fvar X) M);
  ne_qua : forall X Q, binds X (bind_qua Q) E -> subqual F (qua_fvar X) Q;
  ne_typ : forall X T, binds X (bind_typ T) E -> binds X (bind_typ T) F
}.
Local Hint Resolve ne_sub ne_qua ne_typ : core.

Lemma ne_sorts : forall M E F, narrow_env M E F -> keep_sub E F /\ keep_qua E F.
Proof.
  intros M E F H; split; intros X U B.
  - destruct (ne_sub _ _ _ H _ _ B) as [BH|[? HS]]; eauto.
    destruct (sub_regular _ _ _ HS) as [_ [HV _]]. inversion HV; subst; eauto.
  - pose proof (ne_qua _ _ _ H _ _ B) as HS.
    destruct (sq_regular _ _ _ HS) as [_ [HV _]]. inversion HV; subst; eauto.
Qed.

Lemma ne_cons : forall M E F X b, narrow_env M E F -> wf_env ((X,b)::F) ->
  narrow_env M ((X,b)::E) ((X,b)::F).
Proof.
  intros M E F X b H HF; constructor; intros Y U B;
    apply binds_cons_iff in B; destruct B as [[? ?]|B]; subst.
  - left; apply binds_cons_iff; auto.
  - destruct (ne_sub _ _ _ H _ _ B) as [HB|[? HS]]; subst.
    + left; apply binds_cons_iff; auto.
    + eauto using sub_env, keep_binds_head.
  - apply subqual_trans_qvar with (R := U).
    + apply binds_cons_iff; auto.
    + apply sq_refl; auto. eapply (wf_env_bind _ HF X (bind_qua U)).
      apply binds_cons_iff; auto.
  - eauto using sq_env, keep_binds_head.
  - apply binds_cons_iff; auto.
  - apply binds_cons_iff; eauto.
Qed.

Lemma ne_head_sub : forall E X M N,
  wf_env ((X,bind_sub N)::E) -> sub E N M ->
  narrow_env M ((X,bind_sub M)::E) ((X,bind_sub N)::E).
Proof.
  intros E X M N HE HN; constructor; intros Y U HB;
    apply binds_cons_iff in HB; destruct HB as [[? ?]|HB]; try discriminate; subst.
  - right; split; [congruence|]. eapply sub_trans_tvar.
    + apply binds_cons_iff; auto.
    + eauto using sub_env, keep_binds_head.
  - left; apply binds_cons_iff; auto.
  - assert (B : binds Y (bind_qua U) ((X,bind_sub N)::E)) by (apply binds_cons_iff; auto).
    eapply subqual_trans_qvar; [exact B|].
    apply sq_refl; auto. exact (wf_env_bind _ HE _ _ B).
  - apply binds_cons_iff; auto.
Qed.

Lemma ne_head_qua : forall M E X P Q,
  wf_env ((X,bind_qua Q)::E) -> subqual E Q P ->
  narrow_env M ((X,bind_qua P)::E) ((X,bind_qua Q)::E).
Proof.
  intros M E X P Q HE HQ; constructor; intros Y U HB;
    apply binds_cons_iff in HB; destruct HB as [[? ?]|HB]; try discriminate; subst; try (injection H0 as ->).
  - left; apply binds_cons_iff; auto.
  - eapply subqual_trans_qvar.
    + apply binds_cons_iff; auto.
    + eauto using sq_env, keep_binds_head.
  - assert (B : binds Y (bind_qua U) ((X,bind_qua Q)::E)) by (apply binds_cons_iff; auto).
    eapply subqual_trans_qvar; [exact B|].
    apply sq_refl; auto. exact (wf_env_bind _ HE _ _ B).
  - apply binds_cons_iff; auto.
Qed.

Lemma sq_narrow : forall E P Q, subqual E P Q ->
  forall M F, narrow_env M E F -> wf_env F -> subqual F P Q.
Proof.
  induction 1; intros M F HN HF; destruct (ne_sorts _ _ _ HN); eauto.
  eauto using sq_trans.
Qed.

Lemma sub_ty_narrow :
  forall M, trans_at M ->
  (forall E S T, sub E S T -> forall F, narrow_env M E F -> wf_env F -> sub F S T) /\
  (forall E S T, subqtype E S T -> forall F, narrow_env M E F -> wf_env F -> subqtype F S T).
Proof.
  intros M HM; apply sub_ty_ind; intros;
    try match goal with H : narrow_env _ _ _ |- _ => destruct (ne_sorts _ _ _ H) end;
    eauto using wf_typ_env, sq_narrow.
  - match goal with HN : narrow_env _ _ _, B : binds _ _ _ |- _ =>
      destruct (ne_sub _ _ _ HN _ _ B) as [HB|[? HS]]; subst
    end; eauto; eapply HM; eauto.
  - eapply sub_all with (L := union L (dom F)); eauto.
    intros X HX. assert (HF : wf_env ((X,bind_sub T1)::F)).
    { destruct (sub_regular _ _ _ s) as [_ [HT _]].
      apply wf_env_sub; eauto using wf_typ_env; solve_notin. }
    eapply H0; cbn; eauto using ne_cons; solve_notin.
  - eapply sub_qall with (L := union L (dom F)); eauto using sq_narrow.
    intros X HX. assert (HF : wf_env ((X,bind_qua T1)::F)).
    { destruct (sq_regular _ _ _ s) as [_ [HT _]].
      apply wf_env_qua; eauto; solve_notin. }
    eapply H; cbn; eauto using ne_cons; solve_notin.
Qed.

Lemma subq_narrow : forall M, trans_at M ->
  forall E S T, subqtype E S T -> forall F, narrow_env M E F -> wf_env F -> subqtype F S T.
Proof. intros M H; exact (proj2 (sub_ty_narrow M H)). Qed.

Lemma trans_at_top : trans_at typ_top.
Proof. unfold trans_at; intros E S T HS HT; inversion HT; subst; auto. Qed.

Fixpoint typ_size (T : typ) : nat :=
  match T with
  | typ_arrow A B | typ_sum A B | typ_pair A B => S (qtyp_size A + qtyp_size B)
  | typ_all A B => S (typ_size A + qtyp_size B)
  | typ_qall _ B | typ_ref B => S (qtyp_size B)
  | _ => 1
  end
with qtyp_size (T : qtyp) : nat :=
  match T with qtyp_qtyp _ A => S (typ_size A) end.

Scheme typ_mut := Induction for typ Sort Prop with qtyp_mut := Induction for qtyp Sort Prop.
Combined Scheme ty_mut from typ_mut, qtyp_mut.

Lemma size_open_t :
  (forall T k (X : atom), typ_size (open_tt_rec k X T) = typ_size T) /\
  (forall T k (X : atom), qtyp_size (open_tqt_rec k X T) = qtyp_size T).
Proof.
  apply ty_mut; intros; simpl; try (repeat (erewrite H || erewrite H0); reflexivity).
  destruct (k == n); reflexivity.
Qed.

Lemma size_open_q :
  (forall T k Q, typ_size (open_qt_rec k Q T) = typ_size T) /\
  (forall T k Q, qtyp_size (open_qqt_rec k Q T) = qtyp_size T).
Proof. apply ty_mut; intros; simpl; try (repeat (erewrite H || erewrite H0); reflexivity). Qed.

From Stdlib Require Import Lia.

Lemma trans_by_size : forall n,
  (forall M, typ_size M <= n -> trans_at M) /\
  (forall M, qtyp_size M <= n ->
    forall E S T, subqtype E S M -> subqtype E M T -> subqtype E S T).
Proof.
  induction n as [|n [IH IQ]]; split.
  - destruct M; simpl; intros; lia.
  - destruct M; simpl; intros; lia.
  - intros M HM. unfold trans_at. intros E S T HS; revert T.
    pose proof HS as Hsource.
    induction HS; intros V HV;
      try solve [inversion HV; subst; eauto using sub_trans_tvar].
    all: inversion HV; subst; clear HV.
    all: try solve [destruct (sub_regular _ _ _ Hsource) as [? [? ?]]; eauto].
    all: try solve [constructor;
      match goal with
      | H : subqtype _ ?S ?M, H' : subqtype _ ?M ?T |- subqtype _ ?S ?T =>
        eapply (IQ M); [simpl in HM; lia|exact H|exact H']
      end].
    + (* Bounded type abstraction. *)
      assert (HN : sub E T0 S1).
      { eapply (IH T1); [simpl in HM; lia|exact H3|exact HS]. }
      eapply sub_all with (L := union L (union L0 (dom E))); [exact HN|].
      intros X HX.
      assert (HR : wf_env (X ~ bind_sub T0 ++ E)).
      { match goal with HB : sub E T0 _ |- _ =>
          destruct (sub_regular _ _ _ HB) as [? [? ?]] end.
        apply wf_env_sub; auto; solve_notin. }
      eapply (IQ (open_tqt T2 X)).
      * unfold open_tqt; rewrite (proj2 size_open_t); simpl in HM; lia.
      * eapply subq_narrow with (M := T1).
        -- apply IH; simpl in HM; lia.
        -- apply H; solve_notin.
        -- cbn; eapply ne_head_sub; eauto.
        -- exact HR.
      * apply H5; solve_notin.
    + (* Bounded qualifier abstraction. *)
      eapply sub_qall with (L := union L (union L0 (dom E))); eauto using sq_trans.
      intros X HX.
      match goal with
      | HB : subqual E ?U T1 |- _ =>
        assert (HR : wf_env (X ~ bind_qua U ++ E)) by
          (destruct (sq_regular _ _ _ HB) as [? [? ?]]; apply wf_env_qua; auto; solve_notin)
      end.
      eapply (IQ (open_qqt T2 X)).
      * unfold open_qqt; rewrite (proj2 size_open_q); simpl in HM; lia.
      * eapply subq_narrow with (M := typ_top).
        -- exact trans_at_top.
        -- apply H0; solve_notin.
        -- cbn; eapply ne_head_qua; eauto.
        -- exact HR.
      * apply H6; solve_notin.
  - intros [Q M] HM E [R S] [P T] HS HT.
    inversion HS; inversion HT; subst. constructor; eauto using sq_trans.
    eapply (IH M); eauto; simpl in HM; lia.
Qed.

Lemma sub_trans : forall E S M T, sub E S M -> sub E M T -> sub E S T.
Proof. intros; eapply (proj1 (trans_by_size (typ_size M)) M); eauto. Qed.

Lemma subq_trans : forall E S M T, subqtype E S M -> subqtype E M T -> subqtype E S T.
Proof. intros; eapply (proj2 (trans_by_size (qtyp_size M))); eauto. Qed.

(* Simultaneous free-variable substitution for the three namespaces. *)
Section SyntaxSubstitution.
Variable X : atom.
Variable A : typ.
Variable R : qua.
Variable v : exp.

Fixpoint replace_q (Q : qua) : qua :=
  match Q with
  | qua_fvar Y => if X == Y then R else Q
  | qua_meet P Q => qua_meet (replace_q P) (replace_q Q)
  | qua_join P Q => qua_join (replace_q P) (replace_q Q)
  | _ => Q
  end.

Fixpoint replace_t (T : typ) : typ :=
  match T with
  | typ_fvar Y => if X == Y then A else T
  | typ_arrow B T => typ_arrow (replace_qt B) (replace_qt T)
  | typ_all B T => typ_all (replace_t B) (replace_qt T)
  | typ_qall Q T => typ_qall (replace_q Q) (replace_qt T)
  | typ_sum B T => typ_sum (replace_qt B) (replace_qt T)
  | typ_pair B T => typ_pair (replace_qt B) (replace_qt T)
  | typ_ref T => typ_ref (replace_qt T)
  | _ => T
  end
with replace_qt (T : qtyp) : qtyp :=
  match T with qtyp_qtyp Q T => qtyp_qtyp (replace_q Q) (replace_t T) end.

Fixpoint replace_e (e : exp) : exp :=
  match e with
  | exp_fvar Y => if X == Y then v else e
  | exp_abs P T b => exp_abs (replace_q P) (replace_qt T) (replace_e b)
  | exp_app a b => exp_app (replace_e a) (replace_e b)
  | exp_tabs P T b => exp_tabs (replace_q P) (replace_t T) (replace_e b)
  | exp_tapp a T => exp_tapp (replace_e a) (replace_t T)
  | exp_qabs P Q b => exp_qabs (replace_q P) (replace_q Q) (replace_e b)
  | exp_qapp a Q => exp_qapp (replace_e a) (replace_q Q)
  | exp_let a b => exp_let (replace_e a) (replace_e b)
  | exp_inl P a => exp_inl (replace_q P) (replace_e a)
  | exp_inr P a => exp_inr (replace_q P) (replace_e a)
  | exp_case a b c => exp_case (replace_e a) (replace_e b) (replace_e c)
  | exp_pair P a b => exp_pair (replace_q P) (replace_e a) (replace_e b)
  | exp_first a => exp_first (replace_e a)
  | exp_second a => exp_second (replace_e a)
  | exp_ref P a => exp_ref (replace_q P) (replace_e a)
  | exp_ref_label P l => exp_ref_label (replace_q P) l
  | exp_deref a => exp_deref (replace_e a)
  | exp_set_ref a b => exp_set_ref (replace_e a) (replace_e b)
  | exp_upqual P a => exp_upqual (replace_q P) (replace_e a)
  | exp_check P a => exp_check (replace_q P) (replace_e a)
  | _ => e
  end.
End SyntaxSubstitution.

Fixpoint atoms_q (Q : qua) : atoms :=
  match Q with
  | qua_fvar Y => singleton Y
  | qua_meet P Q | qua_join P Q => union (atoms_q P) (atoms_q Q)
  | _ => AtomSetImpl.empty
  end.

Fixpoint atoms_t (T : typ) : atoms :=
  match T with
  | typ_fvar Y => singleton Y
  | typ_arrow B T | typ_sum B T | typ_pair B T => union (atoms_qt B) (atoms_qt T)
  | typ_all B T => union (atoms_t B) (atoms_qt T)
  | typ_qall Q T => union (atoms_q Q) (atoms_qt T)
  | typ_ref T => atoms_qt T
  | _ => AtomSetImpl.empty
  end
with atoms_qt (T : qtyp) : atoms :=
  match T with qtyp_qtyp Q T => union (atoms_q Q) (atoms_t T) end.

Fixpoint atoms_e (e : exp) : atoms :=
  match e with
  | exp_fvar Y => singleton Y
  | exp_abs P T b => union (atoms_q P) (union (atoms_qt T) (atoms_e b))
  | exp_app a b | exp_let a b | exp_set_ref a b => union (atoms_e a) (atoms_e b)
  | exp_tabs P T b => union (atoms_q P) (union (atoms_t T) (atoms_e b))
  | exp_tapp a T => union (atoms_e a) (atoms_t T)
  | exp_qabs P Q b => union (atoms_q P) (union (atoms_q Q) (atoms_e b))
  | exp_qapp a Q => union (atoms_e a) (atoms_q Q)
  | exp_inl P a | exp_inr P a | exp_ref P a | exp_upqual P a | exp_check P a =>
      union (atoms_q P) (atoms_e a)
  | exp_case a b c => union (atoms_e a) (union (atoms_e b) (atoms_e c))
  | exp_pair P a b => union (atoms_q P) (union (atoms_e a) (atoms_e b))
  | exp_first a | exp_second a | exp_deref a => atoms_e a
  | exp_ref_label P _ => atoms_q P
  | _ => AtomSetImpl.empty
  end.

Lemma replace_q_fresh : forall Q X R, X `notin` atoms_q Q -> replace_q X R Q = Q.
Proof.
  induction Q; intros; simpl in *; f_equal; eauto; try solve_notin.
  destruct (X == a); subst; auto; exfalso; solve_notin.
Qed.

Lemma replace_ty_fresh :
  (forall T X A R, X `notin` atoms_t T -> replace_t X A R T = T) /\
  (forall T X A R, X `notin` atoms_qt T -> replace_qt X A R T = T).
Proof.
  apply ty_mut; intros; simpl in *; try solve [f_equal; eauto using replace_q_fresh; try solve_notin].
  destruct (X == a); subst; auto; exfalso; solve_notin.
Qed.

Lemma replace_t_fresh : forall T X A R, X `notin` atoms_t T -> replace_t X A R T = T.
Proof. exact (proj1 replace_ty_fresh). Qed.
Lemma replace_qt_fresh : forall T X A R, X `notin` atoms_qt T -> replace_qt X A R T = T.
Proof. exact (proj2 replace_ty_fresh). Qed.

Lemma replace_e_fresh : forall e X A R v,
  X `notin` atoms_e e -> replace_e X A R v e = e.
Proof.
  induction e; intros; simpl in *;
    try solve [f_equal; eauto using replace_q_fresh, replace_t_fresh, replace_qt_fresh; try solve_notin].
  destruct (X == a); subst; auto; exfalso; solve_notin.
Qed.

(* A common depth bounds all three kinds of bound index. *)
Fixpoint scope_q (k : nat) (Q : qua) : Prop :=
  match Q with
  | qua_bvar i => i < k
  | qua_meet P Q | qua_join P Q => scope_q k P /\ scope_q k Q
  | _ => True
  end.

Fixpoint scope_t (k : nat) (T : typ) : Prop :=
  match T with
  | typ_bvar i => i < k
  | typ_arrow A B => scope_qt k A /\ scope_qt (S k) B
  | typ_all A B => scope_t k A /\ scope_qt (S k) B
  | typ_qall P B => scope_q k P /\ scope_qt (S k) B
  | typ_sum A B | typ_pair A B => scope_qt k A /\ scope_qt k B
  | typ_ref A => scope_qt k A
  | _ => True
  end
with scope_qt (k : nat) (T : qtyp) : Prop :=
  match T with qtyp_qtyp P A => scope_q k P /\ scope_t k A end.

Fixpoint scope_e (k : nat) (e : exp) : Prop :=
  match e with
  | exp_bvar i => i < k
  | exp_abs P T b => scope_q k P /\ scope_qt k T /\ scope_e (S k) b
  | exp_app a b | exp_set_ref a b => scope_e k a /\ scope_e k b
  | exp_tabs P T b => scope_q k P /\ scope_t k T /\ scope_e (S k) b
  | exp_tapp a T => scope_e k a /\ scope_t k T
  | exp_qabs P Q b => scope_q k P /\ scope_q k Q /\ scope_e (S k) b
  | exp_qapp a Q => scope_e k a /\ scope_q k Q
  | exp_let a b => scope_e k a /\ scope_e (S k) b
  | exp_inl P a | exp_inr P a | exp_ref P a | exp_upqual P a | exp_check P a =>
      scope_q k P /\ scope_e k a
  | exp_case a b c => scope_e k a /\ scope_e (S k) b /\ scope_e (S k) c
  | exp_pair P a b => scope_q k P /\ scope_e k a /\ scope_e k b
  | exp_first a | exp_second a | exp_deref a => scope_e k a
  | exp_ref_label P _ => scope_q k P
  | _ => True
  end.

Ltac break_pairs :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end.

Ltac scope_mono :=
  intros; simpl in *; break_pairs; repeat split; eauto;
  try lia;
  match goal with
  | IH : forall k l, k <= l -> _ -> ?F l ?A, H : ?F ?k ?A |- ?F ?l ?A =>
    exact (IH k l ltac:(lia) H)
  end.

Lemma scope_q_mono : forall Q k l, k <= l -> scope_q k Q -> scope_q l Q.
Proof. induction Q; scope_mono. Qed.
Local Hint Resolve scope_q_mono : core.

Lemma scope_ty_mono :
  (forall T k l, k <= l -> scope_t k T -> scope_t l T) /\
  (forall T k l, k <= l -> scope_qt k T -> scope_qt l T).
Proof. apply ty_mut; scope_mono. Qed.
Lemma scope_t_mono : forall T k l, k <= l -> scope_t k T -> scope_t l T.
Proof. exact (proj1 scope_ty_mono). Qed.
Lemma scope_qt_mono : forall T k l, k <= l -> scope_qt k T -> scope_qt l T.
Proof. exact (proj2 scope_ty_mono). Qed.
Local Hint Resolve scope_t_mono scope_qt_mono : core.

Lemma scope_e_mono : forall e k l, k <= l -> scope_e k e -> scope_e l e.
Proof. induction e; scope_mono. Qed.
Local Hint Resolve scope_e_mono : core.

Ltac scope_open_back :=
  intros; simpl in *;
  repeat match goal with
  | H : context [if ?k == ?i then _ else _] |- _ => destruct (k == i); subst; simpl in H
  end;
  break_pairs; repeat split; eauto; lia.

Lemma scope_q_open : forall Q k (X : atom),
  scope_q k (open_qq_rec k X Q) -> scope_q (S k) Q.
Proof. induction Q; scope_open_back. Qed.
Local Hint Resolve scope_q_open : core.

Lemma scope_ty_open_t :
  (forall T k (X : atom), scope_t k (open_tt_rec k X T) -> scope_t (S k) T) /\
  (forall T k (X : atom), scope_qt k (open_tqt_rec k X T) -> scope_qt (S k) T).
Proof. apply ty_mut; scope_open_back. Qed.
Lemma scope_ty_open_q :
  (forall T k (X : atom), scope_t k (open_qt_rec k X T) -> scope_t (S k) T) /\
  (forall T k (X : atom), scope_qt k (open_qqt_rec k X T) -> scope_qt (S k) T).
Proof. apply ty_mut; scope_open_back. Qed.

Lemma scope_t_open_t : forall T k (X : atom), scope_t k (open_tt_rec k X T) -> scope_t (S k) T.
Proof. exact (proj1 scope_ty_open_t). Qed.
Lemma scope_qt_open_t : forall T k (X : atom), scope_qt k (open_tqt_rec k X T) -> scope_qt (S k) T.
Proof. exact (proj2 scope_ty_open_t). Qed.
Lemma scope_t_open_q : forall T k (X : atom), scope_t k (open_qt_rec k X T) -> scope_t (S k) T.
Proof. exact (proj1 scope_ty_open_q). Qed.
Lemma scope_qt_open_q : forall T k (X : atom), scope_qt k (open_qqt_rec k X T) -> scope_qt (S k) T.
Proof. exact (proj2 scope_ty_open_q). Qed.
Local Hint Resolve scope_t_open_t scope_qt_open_t scope_t_open_q scope_qt_open_q : core.

Lemma scope_e_open_e : forall e k (X : atom),
  scope_e k (open_ee_rec k X e) -> scope_e (S k) e.
Proof. induction e; scope_open_back. Qed.
Lemma scope_e_open_t : forall e k (X : atom),
  scope_e k (open_te_rec k X e) -> scope_e (S k) e.
Proof. induction e; scope_open_back. Qed.
Lemma scope_e_open_q : forall e k (X : atom),
  scope_e k (open_qe_rec k X e) -> scope_e (S k) e.
Proof. induction e; scope_open_back. Qed.

Lemma qual_scoped : forall Q, qual Q -> scope_q 0 Q.
Proof. induction 1; simpl; auto. Qed.
Local Hint Resolve qual_scoped : core.

Scheme type_mut := Induction for type Sort Prop with qtype_mut := Induction for qtype Sort Prop.
Combined Scheme local_ty_mut from type_mut, qtype_mut.

Ltac scope_cofinite :=
  match goal with
  | IH : forall X : atom, X `notin` ?L -> _ |- _ =>
    let X := fresh "X" in let HX := fresh "HX" in
    destruct (atom_fresh L) as [X HX];
    specialize (IH X HX); unfold open_ee, open_te, open_qe, open_tqt, open_qqt in IH;
    eauto using scope_e_open_e, scope_e_open_t, scope_e_open_q
  end.

Lemma type_scoped :
  (forall T, type T -> scope_t 0 T) /\ (forall T, qtype T -> scope_qt 0 T).
Proof.
  apply local_ty_mut; intros; simpl; repeat split; eauto;
    try solve [eapply scope_qt_mono; [|eassumption]; lia];
    scope_cofinite.
Qed.
Lemma typ_scoped : forall T, type T -> scope_t 0 T.
Proof. exact (proj1 type_scoped). Qed.
Lemma qtyp_scoped : forall T, qtype T -> scope_qt 0 T.
Proof. exact (proj2 type_scoped). Qed.
Local Hint Resolve typ_scoped qtyp_scoped : core.

Lemma expr_scoped : forall e, expr e -> scope_e 0 e.
Proof.
  induction 1; simpl; repeat split; eauto;
    first [solve [scope_cofinite] |
    match goal with
    | IH : forall X : atom, X `notin` ?L -> scope_e _ (open_ee ?b X)
      |- scope_e _ ?b =>
      destruct (atom_fresh L) as [X HX]; apply (scope_e_open_e _ 0 X (IH X HX))
    end].
Qed.

Ltac scope_identity :=
  intros; simpl in *; break_pairs;
  repeat match goal with |- context[if ?i == ?j then _ else _] =>
    destruct (i == j); subst; try lia end;
  f_equal; eauto.

Lemma open_q_identity : forall Q k R, scope_q k Q -> open_qq_rec k R Q = Q.
Proof. induction Q; scope_identity. Qed.
Local Hint Resolve open_q_identity : core.

Lemma open_ty_identity_t :
  (forall T k A, scope_t k T -> open_tt_rec k A T = T) /\
  (forall T k A, scope_qt k T -> open_tqt_rec k A T = T).
Proof. apply ty_mut; scope_identity. Qed.
Lemma open_ty_identity_q :
  (forall T k R, scope_t k T -> open_qt_rec k R T = T) /\
  (forall T k R, scope_qt k T -> open_qqt_rec k R T = T).
Proof. apply ty_mut; scope_identity. Qed.
Lemma open_t_identity_t : forall T k A, scope_t k T -> open_tt_rec k A T = T.
Proof. exact (proj1 open_ty_identity_t). Qed.
Lemma open_qt_identity_t : forall T k A, scope_qt k T -> open_tqt_rec k A T = T.
Proof. exact (proj2 open_ty_identity_t). Qed.
Lemma open_t_identity_q : forall T k R, scope_t k T -> open_qt_rec k R T = T.
Proof. exact (proj1 open_ty_identity_q). Qed.
Lemma open_qt_identity_q : forall T k R, scope_qt k T -> open_qqt_rec k R T = T.
Proof. exact (proj2 open_ty_identity_q). Qed.
Local Hint Resolve open_t_identity_t open_qt_identity_t open_t_identity_q open_qt_identity_q : core.

Lemma open_e_identity_e : forall e k v, scope_e k e -> open_ee_rec k v e = e.
Proof. induction e; scope_identity. Qed.
Lemma open_e_identity_t : forall e k A, scope_e k e -> open_te_rec k A e = e.
Proof. induction e; scope_identity. Qed.
Lemma open_e_identity_q : forall e k R, scope_e k e -> open_qe_rec k R e = e.
Proof. induction e; scope_identity. Qed.
Local Hint Resolve open_e_identity_e open_e_identity_t open_e_identity_q : core.

Ltac commute_open :=
  intros; simpl;
  repeat match goal with |- context[if ?i == ?j then _ else _] =>
    destruct (i == j); subst; simpl end;
  try reflexivity; try solve [symmetry; eauto using le_0_n];
  f_equal; eauto.

Lemma replace_open_q : forall Q X R k P, scope_q 0 R ->
  replace_q X R (open_qq_rec k P Q) = open_qq_rec k (replace_q X R P) (replace_q X R Q).
Proof. induction Q; commute_open. Qed.
Local Hint Resolve replace_open_q : core.

Lemma replace_open_ty_t :
  (forall T X A R k B, scope_t 0 A ->
    replace_t X A R (open_tt_rec k B T) =
    open_tt_rec k (replace_t X A R B) (replace_t X A R T)) /\
  (forall T X A R k B, scope_t 0 A ->
    replace_qt X A R (open_tqt_rec k B T) =
    open_tqt_rec k (replace_t X A R B) (replace_qt X A R T)).
Proof. apply ty_mut; commute_open. Qed.

Lemma replace_open_ty_q :
  (forall T X A R k P, scope_t 0 A -> scope_q 0 R ->
    replace_t X A R (open_qt_rec k P T) =
    open_qt_rec k (replace_q X R P) (replace_t X A R T)) /\
  (forall T X A R k P, scope_t 0 A -> scope_q 0 R ->
    replace_qt X A R (open_qqt_rec k P T) =
    open_qqt_rec k (replace_q X R P) (replace_qt X A R T)).
Proof. apply ty_mut; commute_open. Qed.

Lemma replace_open_t_t : forall T X A R k B, scope_t 0 A ->
    replace_t X A R (open_tt_rec k B T) =
    open_tt_rec k (replace_t X A R B) (replace_t X A R T).
Proof. exact (proj1 replace_open_ty_t). Qed.
Lemma replace_open_qt_t : forall T X A R k B, scope_t 0 A ->
    replace_qt X A R (open_tqt_rec k B T) =
    open_tqt_rec k (replace_t X A R B) (replace_qt X A R T).
Proof. exact (proj2 replace_open_ty_t). Qed.
Lemma replace_open_t_q : forall T X A R k P, scope_t 0 A -> scope_q 0 R ->
    replace_t X A R (open_qt_rec k P T) =
    open_qt_rec k (replace_q X R P) (replace_t X A R T).
Proof. exact (proj1 replace_open_ty_q). Qed.
Lemma replace_open_qt_q : forall T X A R k P, scope_t 0 A -> scope_q 0 R ->
    replace_qt X A R (open_qqt_rec k P T) =
    open_qqt_rec k (replace_q X R P) (replace_qt X A R T).
Proof. exact (proj2 replace_open_ty_q). Qed.
Local Hint Resolve replace_open_t_t replace_open_qt_t replace_open_t_q replace_open_qt_q : core.

Lemma replace_open_e_e : forall e X A R v k u, scope_e 0 v ->
  replace_e X A R v (open_ee_rec k u e) =
  open_ee_rec k (replace_e X A R v u) (replace_e X A R v e).
Proof. induction e; commute_open. Qed.
Lemma replace_open_e_t : forall e X A R v k B, scope_e 0 v -> scope_t 0 A ->
  replace_e X A R v (open_te_rec k B e) =
  open_te_rec k (replace_t X A R B) (replace_e X A R v e).
Proof. induction e; commute_open. Qed.
Lemma replace_open_e_q : forall e X A R v k P, scope_e 0 v -> scope_t 0 A -> scope_q 0 R ->
  replace_e X A R v (open_qe_rec k P e) =
  open_qe_rec k (replace_q X R P) (replace_e X A R v e).
Proof. induction e; commute_open. Qed.

Lemma replace_q_id : forall X Q, replace_q X (qua_fvar X) Q = Q.
Proof. intros X Q; induction Q; simpl; f_equal; auto. destruct (X == a); congruence. Qed.
Lemma replace_t_id :
  (forall T X, replace_t X (typ_fvar X) (qua_fvar X) T = T) /\
  (forall T X, replace_qt X (typ_fvar X) (qua_fvar X) T = T).
Proof. apply ty_mut; intros; simpl; f_equal; auto using replace_q_id. destruct (X == a); congruence. Qed.
Lemma replace_qt_id : forall T X, replace_qt X (typ_fvar X) (qua_fvar X) T = T.
Proof. exact (proj2 replace_t_id). Qed.

Ltac rewrite_open :=
  unfold open_ee, open_te, open_qe, open_tqt, open_qqt;
  first [rewrite replace_open_e_e by assumption | rewrite replace_open_e_t by assumption |
         rewrite replace_open_e_q by assumption | rewrite replace_open_qt_t by assumption |
         rewrite replace_open_qt_q by assumption];
  try match goal with H : ?X `notin` atoms_e ?e |- _ => rewrite (replace_e_fresh e X) by exact H end;
  try match goal with H : ?X `notin` atoms_qt ?T |- _ => rewrite (replace_qt_fresh T X) by exact H end;
  simpl; match goal with |- context[if ?x == ?x then _ else _] =>
    destruct (x == x); congruence end.

Lemma replace_intro_e : forall e X A R v,
  scope_e 0 v -> X `notin` atoms_e e ->
  replace_e X A R v (open_ee e X) = open_ee e v.
Proof. intros; rewrite_open; auto. Qed.
Lemma replace_intro_et : forall e X A R v,
  scope_e 0 v -> scope_t 0 A -> X `notin` atoms_e e ->
  replace_e X A R v (open_te e X) = open_te e A.
Proof. intros; rewrite_open; auto. Qed.
Lemma replace_intro_eq : forall e X A R v,
  scope_e 0 v -> scope_t 0 A -> scope_q 0 R -> X `notin` atoms_e e ->
  replace_e X A R v (open_qe e X) = open_qe e R.
Proof. intros; rewrite_open; auto. Qed.
Lemma replace_intro_qt_t : forall T X A R,
  scope_t 0 A -> X `notin` atoms_qt T ->
  replace_qt X A R (open_tqt T X) = open_tqt T A.
Proof. intros; rewrite_open; auto. Qed.
Lemma replace_intro_qt_q : forall T X A R,
  scope_t 0 A -> scope_q 0 R -> X `notin` atoms_qt T ->
  replace_qt X A R (open_qqt T X) = open_qqt T R.
Proof. intros; rewrite_open; auto. Qed.

Lemma typing_env_regular : forall E Q e T, typing E Q e T -> wf_env E.
Proof.
  induction 1; eauto;
    match goal with
    | H : forall X : atom, X `notin` ?L -> wf_env (X ~ ?b ++ ?E) |- _ =>
      destruct (atom_fresh L) as [X HX]; exact (wf_env_tail _ _ _ (H X HX))
    end.
Qed.

Lemma wf_env_bound : forall E X b, wf_env ((X,b)::E) ->
  match b with bind_sub T => wf_typ E T | bind_typ T => wf_qtyp E T
             | bind_qua Q => wf_qua E Q end.
Proof. inversion 1; auto. Qed.

Lemma cofinite_bound : forall L E b,
  (forall X : atom, X `notin` L -> wf_env ((X,b)::E)) ->
  match b with bind_sub T => wf_typ E T | bind_typ T => wf_qtyp E T
             | bind_qua Q => wf_qua E Q end.
Proof.
  intros L E b H; destruct (atom_fresh L) as [X HX]; exact (wf_env_bound _ _ _ (H X HX)).
Qed.

Ltac bound_from H L E b :=
  let HW := fresh "Hbound" in
  pose proof (cofinite_bound L E b
    (fun X HX => typing_env_regular _ _ _ _ (H X HX))) as HW; cbn in HW.

Ltac pick_bound :=
  match goal with
  | H : forall X : atom, X `notin` ?L -> typing (X ~ ?b ++ ?E) _ _ _ |- _ =>
    bound_from H L E b
  | H : forall X : atom, X `notin` ?L -> typing ((X,?b)::?E) _ _ _ |- _ =>
    bound_from H L E b
  end.

Local Hint Resolve sub_env subq_env sq_env wf_typ_env wf_qtyp_env : core.

Ltac env_sorts :=
  match goal with H : keep_binds _ _ |- _ => destruct (keep_binds_sort _ _ H) end.

Lemma typing_env : forall E Q e T, typing E Q e T ->
  forall F, wf_env F -> keep_binds E F -> typing F Q e T.
Proof.
  induction 1; intros F HF HB; env_sorts; try solve [unfold keep_binds in HB; eauto].
  - pick_bound. eapply typing_abs with (L := union L (dom F)).
    intros; eapply H0; cbn; eauto using keep_binds_cons; try solve_notin.
    apply wf_env_typ; eauto; solve_notin.
  - pick_bound. eapply typing_tabs with (L := union L (dom F)).
    intros; eapply H0; cbn; eauto using keep_binds_cons; try solve_notin.
    apply wf_env_sub; eauto; solve_notin.
  - pick_bound. eapply typing_qabs with (L := union L (dom F)); eauto.
    intros; eapply H1; cbn; eauto using keep_binds_cons; try solve_notin.
    apply wf_env_qua; eauto; solve_notin.
  - pick_bound. eapply typing_let with (L := union L (dom F)); eauto.
    intros; eapply H1; cbn; eauto using keep_binds_cons; try solve_notin.
    apply wf_env_typ; eauto; solve_notin.
  - pick_bound.
    pose proof (cofinite_bound L E (bind_typ T1)
      (fun X HX => typing_env_regular _ _ _ _ (H0 X HX))) as HW; cbn in HW.
    eapply typing_case with (L := union L (dom F)); eauto.
    + intros; eapply H1; cbn; eauto using keep_binds_cons; try solve_notin.
      apply wf_env_typ; eauto; solve_notin.
    + intros; eapply H3; cbn; eauto using keep_binds_cons; try solve_notin.
      apply wf_env_typ; eauto; solve_notin.
Qed.

Definition replace_binding X A R b :=
  match b with
  | bind_sub T => bind_sub (replace_t X A R T)
  | bind_typ T => bind_typ (replace_qt X A R T)
  | bind_qua P => bind_qua (replace_q X R P)
  end.

Section ReplaceDerivations.
Variables (X : atom) (A : typ) (R : qua) (v : exp).
Hypotheses (scA : scope_t 0 A) (scR : scope_q 0 R) (scv : scope_e 0 v).

Local Notation rq := (replace_q X R).
Local Notation rt := (replace_t X A R).
Local Notation rqt := (replace_qt X A R).
Local Notation re := (replace_e X A R v).
Local Notation rb := (replace_binding X A R).

Record replace_env (E F : env) : Prop := {
  re_sub : forall Y U, binds Y (bind_sub U) E ->
    if X == Y then sub F A (rt U) else binds Y (bind_sub (rt U)) F;
  re_qua : forall Y P, binds Y (bind_qua P) E ->
    if X == Y then subqual F R (rq P) else binds Y (bind_qua (rq P)) F;
  re_typ : forall Y T, binds Y (bind_typ T) E ->
    if X == Y then typing F qua_bot v (rqt T) else binds Y (bind_typ (rqt T)) F
}.

Lemma replace_env_cons : forall E F Y b, X <> Y ->
  replace_env E F -> wf_env ((Y,rb b)::F) ->
  replace_env ((Y,b)::E) ((Y,rb b)::F).
Proof.
  intros E F Y b HXY HE HF; constructor; intros Z U HB;
    apply binds_cons_iff in HB; destruct HB as [[? ?]|HB]; subst;
    try solve [destruct (X == Y); [contradiction|]; apply binds_cons_iff; left; split; reflexivity].
  - pose proof (re_sub _ _ HE _ _ HB); destruct (X == Z);
      eauto using keep_binds_head; apply binds_cons_iff; auto.
  - pose proof (re_qua _ _ HE _ _ HB); destruct (X == Z);
      eauto using keep_binds_head; apply binds_cons_iff; auto.
  - pose proof (re_typ _ _ HE _ _ HB); destruct (X == Z);
      eauto using typing_env, keep_binds_head; apply binds_cons_iff; auto.
Qed.

Ltac rw_replace_open :=
  unfold open_ee, open_te, open_qe, open_tqt, open_qqt in *;
  repeat match goal with
  | H : context[re (open_ee_rec _ _ _)] |- _ => rewrite replace_open_e_e in H by assumption
  | H : context[re (open_te_rec _ _ _)] |- _ => rewrite replace_open_e_t in H by assumption
  | H : context[re (open_qe_rec _ _ _)] |- _ => rewrite replace_open_e_q in H by assumption
  | H : context[rqt (open_tqt_rec _ _ _)] |- _ => rewrite replace_open_qt_t in H by assumption
  | H : context[rqt (open_qqt_rec _ _ _)] |- _ => rewrite replace_open_qt_q in H by assumption
  end;
  cbn in *;
  repeat match goal with H : context[if X == ?Y then _ else _] |- _ =>
    let Hne := fresh "Hne" in
    assert (Hne : X <> Y) by solve_notin;
    destruct (X == Y); [contradiction|]
  end.

Lemma wf_qua_replace : forall E P, wf_qua E P ->
  forall F, replace_env E F -> wf_qua F (rq P).
Proof.
  induction 1; intros F HB; simpl; eauto.
  pose proof (re_qua _ _ HB _ _ H) as HR; destruct (X == X0); eauto.
  exact (proj1 (proj2 (sq_regular _ _ _ HR))).
Qed.

Lemma sq_replace : forall E P Q, subqual E P Q ->
  forall F, replace_env E F -> wf_env F -> subqual F (rq P) (rq Q).
Proof.
  induction 1; intros F HB HF; simpl; eauto using wf_qua_replace.
  - pose proof (wf_qua_replace _ _ H0 _ HB) as HW. apply sq_refl; auto.
  - pose proof (re_qua _ _ HB _ _ H) as HQ; destruct (X == X0); eauto using sq_trans.
Qed.

Lemma wf_ty_replace :
  (forall E T, wf_typ E T -> forall F, replace_env E F -> wf_env F -> wf_typ F (rt T)) /\
  (forall E T, wf_qtyp E T -> forall F, replace_env E F -> wf_env F -> wf_qtyp F (rqt T)).
Proof.
  apply wf_ty_ind; intros; simpl; try solve [eauto using wf_qua_replace].
  - pose proof (re_sub _ _ H _ _ b) as HS; destruct (X == X0); eauto.
    exact (proj1 (proj2 (sub_regular _ _ _ HS))).
  - eapply wf_typ_all with (L := union L (union (singleton X) (dom F))); eauto.
    intros Y HY.
    assert (HF : wf_env ((Y,bind_sub (rt T1))::F)) by (apply wf_env_sub; eauto; solve_notin).
    specialize (H0 Y ltac:(solve_notin) _ ltac:(cbn; apply replace_env_cons; eauto; solve_notin) HF).
    rw_replace_open; auto.
  - eapply wf_typ_qall with (L := union L (union (singleton X) (dom F))); eauto using wf_qua_replace.
    intros Y HY.
    assert (HF : wf_env ((Y,bind_qua (rq T1))::F)) by
      (apply wf_env_qua; eauto using wf_qua_replace; solve_notin).
    specialize (H Y ltac:(solve_notin) _ ltac:(cbn; apply replace_env_cons; eauto; solve_notin) HF).
    rw_replace_open; auto.
Qed.

Lemma wf_typ_replace : forall E T, wf_typ E T ->
  forall F, replace_env E F -> wf_env F -> wf_typ F (rt T).
Proof. exact (proj1 wf_ty_replace). Qed.
Lemma wf_qtyp_replace : forall E T, wf_qtyp E T ->
  forall F, replace_env E F -> wf_env F -> wf_qtyp F (rqt T).
Proof. exact (proj2 wf_ty_replace). Qed.
Local Hint Resolve wf_typ_replace wf_qtyp_replace wf_qua_replace sq_replace : core.

Lemma sub_ty_replace :
  (forall E T U, sub E T U -> forall F, replace_env E F -> wf_env F -> sub F (rt T) (rt U)) /\
  (forall E T U, subqtype E T U -> forall F, replace_env E F -> wf_env F -> subqtype F (rqt T) (rqt U)).
Proof.
  apply sub_ty_ind; intros; simpl; eauto.
  - pose proof (wf_typ_replace _ _ w0 _ H H0) as HW. apply sub_refl; auto.
  - pose proof (re_sub _ _ H0 _ _ b) as HB; destruct (X == X0); eauto using sub_trans.
  - eapply sub_all with (L := union L (union (singleton X) (dom F))); eauto.
    intros Y HY.
    assert (HF : wf_env ((Y,bind_sub (rt T1))::F)).
    { destruct (sub_regular _ _ _ s) as [_ [? _]]. apply wf_env_sub; eauto; solve_notin. }
    specialize (H0 Y ltac:(solve_notin) _ ltac:(cbn; apply replace_env_cons; eauto; solve_notin) HF).
    rw_replace_open; auto.
  - eapply sub_qall with (L := union L (union (singleton X) (dom F))); eauto.
    intros Y HY.
    assert (HF : wf_env ((Y,bind_qua (rq T1))::F)).
    { destruct (sq_regular _ _ _ s) as [_ [? _]]. apply wf_env_qua; eauto; solve_notin. }
    specialize (H Y ltac:(solve_notin) _ ltac:(cbn; apply replace_env_cons; eauto; solve_notin) HF).
    rw_replace_open; auto.
Qed.

Lemma sub_replace : forall E T U, sub E T U ->
  forall F, replace_env E F -> wf_env F -> sub F (rt T) (rt U).
Proof. exact (proj1 sub_ty_replace). Qed.
Lemma subq_replace : forall E T U, subqtype E T U ->
  forall F, replace_env E F -> wf_env F -> subqtype F (rqt T) (rqt U).
Proof. exact (proj2 sub_ty_replace). Qed.
Local Hint Resolve sub_replace subq_replace : core.

Ltac replace_body F IH b :=
  let Y := fresh "Y" in let HY := fresh "HY" in
  intros Y HY;
  let HF := fresh "HF" in
  assert (HF : wf_env ((Y,rb b)::F)) by (cbn; constructor; eauto; solve_notin);
  specialize (IH Y ltac:(solve_notin) _ ltac:(cbn; apply replace_env_cons; eauto; solve_notin) HF);
  rw_replace_open; auto.

Lemma typing_replace : forall E P e T, typing E P e T ->
  forall F, replace_env E F -> wf_env F -> typing F (rq P) (re e) (rqt T).
Proof.
  induction 1; intros F HB HF; cbn in *; try solve [eauto].
  - pose proof (re_typ _ _ HB _ _ H0) as HT; destruct (X == x); eauto.
  - pick_bound. eapply typing_abs with (L := union L (union (singleton X) (dom F))).
    replace_body F H0 (bind_typ V).
  - pick_bound. eapply typing_tabs with (L := union L (union (singleton X) (dom F))).
    replace_body F H0 (bind_sub V).
  - unfold open_tqt; rewrite replace_open_qt_t by assumption.
    eapply typing_tapp; [eapply IHtyping; eassumption|eapply sub_replace; eassumption].
  - pick_bound. eapply typing_qabs with (L := union L (union (singleton X) (dom F))); eauto.
    replace_body F H1 (bind_qua Q).
  - unfold open_qqt; rewrite replace_open_qt_q by assumption.
    eapply typing_qapp; [eapply IHtyping; eassumption|eapply sq_replace; eassumption].
  - pick_bound. eapply typing_let with (L := union L (union (singleton X) (dom F))); eauto.
    replace_body F H1 (bind_typ T1).
  - pick_bound.
    pose proof (cofinite_bound L E (bind_typ T1)
      (fun X HX => typing_env_regular _ _ _ _ (H0 X HX))) as HW; cbn in HW.
    eapply typing_case with (L := union L (union (singleton X) (dom F))); eauto.
    + replace_body F H1 (bind_typ T1).
    + replace_body F H3 (bind_typ T2).
Qed.
End ReplaceDerivations.

Definition atoms_binding b :=
  match b with bind_sub T => atoms_t T | bind_typ T => atoms_qt T | bind_qua P => atoms_q P end.

Fixpoint atoms_env (E : env) : atoms :=
  match E with
  | (_, b)::F => union (atoms_binding b) (atoms_env F)
  | nil => AtomSetImpl.empty
  end.

Lemma atoms_env_bound : forall E X Y b, X `notin` atoms_env E ->
  binds Y b E -> X `notin` atoms_binding b.
Proof.
  induction E as [|[Z B] E IH]; intros X Y b HX HB; [inversion HB|].
  apply binds_cons_iff in HB; destruct HB as [[? ?]|HB]; subst; simpl in HX;
    first [solve_notin|eapply IH; [solve_notin|exact HB]].
Qed.

Lemma replace_env_start : forall X A R v E b,
  X `notin` dom E -> X `notin` atoms_env E ->
  (match b with
   | bind_sub T => sub E A (replace_t X A R T)
   | bind_qua P => subqual E R (replace_q X R P)
   | bind_typ T => typing E qua_bot v (replace_qt X A R T)
   end) ->
  replace_env X A R v ((X,b)::E) E.
Proof.
  intros X A R v E b HD HA HH; constructor; intros Y U HB;
    apply binds_cons_iff in HB; destruct HB as [[? ?]|HB]; subst;
    match goal with |- context[if X == ?Y then _ else _] => destruct (X == Y) end; subst;
    try solve [exact HH | congruence | exfalso; apply HD; eapply binds_In; eassumption].
  - rewrite replace_t_fresh; auto. exact (atoms_env_bound _ _ _ _ HA HB).
  - rewrite replace_q_fresh; auto. exact (atoms_env_bound _ _ _ _ HA HB).
  - rewrite replace_qt_fresh; auto. exact (atoms_env_bound _ _ _ _ HA HB).
Qed.

Lemma value_expr : forall v, value v -> expr v.
Proof. induction 1; auto. Qed.

Lemma inst_term : forall L E P e U T v,
  (forall X : atom, X `notin` L -> typing (X ~ bind_typ U ++ E) P (open_ee e X) T) ->
  typing E qua_bot v U -> value v ->
  typing E P (open_ee e v) T.
Proof.
  intros L E P e U T v HB HV Hv.
  destruct (atom_fresh (union L (union (dom E) (union (atoms_env E) (atoms_e e))))) as [X HX].
  assert (scv : scope_e 0 v) by eauto using expr_scoped, value_expr.
  assert (HR : replace_env X (typ_fvar X) (qua_fvar X) v ((X,bind_typ U)::E) E).
  { apply replace_env_start; try solve_notin. rewrite replace_qt_id; exact HV. }
  pose proof (typing_replace X (typ_fvar X) (qua_fvar X) v I I scv
    _ _ _ _ (HB X ltac:(solve_notin)) _ HR (typing_env_regular _ _ _ _ HV)) as H.
  rewrite replace_q_id, replace_qt_id, replace_intro_e in H; auto; solve_notin.
Qed.

Ltac inst_fresh L E extra :=
  let merged := constr:(union L (union (dom E) (union (atoms_env E) extra))) in
  destruct (atom_fresh merged) as [X HX].

Ltac solve_scoped :=
  eauto using typ_scoped, qual_scoped, wf_qua_qual;
  match goal with |- scope_t 0 _ => apply typ_scoped; eapply (proj1 wf_ty_local); eassumption end.

Lemma inst_wf_t : forall L E B A T,
  (forall X : atom, X `notin` L ->
    wf_qtyp (X ~ bind_sub B ++ E) (open_tqt T X)) ->
  sub E A B -> wf_qtyp E (open_tqt T A).
Proof.
  intros L E B A T H HS.
  destruct (sub_regular _ _ _ HS) as [HE [HA _]].
  inst_fresh L E (union (atoms_t B) (atoms_qt T)).
  assert (HR : replace_env X A (qua_fvar X) (exp_fvar X) ((X,bind_sub B)::E) E).
  { apply replace_env_start; try solve_notin. rewrite replace_t_fresh by solve_notin; exact HS. }
  assert (scA : scope_t 0 A) by solve_scoped.
  pose proof (wf_qtyp_replace X A (qua_fvar X) (exp_fvar X) scA I
    _ _ (H X ltac:(solve_notin)) _ HR HE) as HT.
  rewrite replace_intro_qt_t in HT; auto; solve_notin.
Qed.

Lemma inst_wf_q : forall L E B R T,
  (forall X : atom, X `notin` L ->
    wf_qtyp (X ~ bind_qua B ++ E) (open_qqt T X)) ->
  subqual E R B -> wf_qtyp E (open_qqt T R).
Proof.
  intros L E B R T H HS.
  destruct (sq_regular _ _ _ HS) as [HE [HA _]].
  inst_fresh L E (union (atoms_q B) (atoms_qt T)).
  assert (HR : replace_env X (typ_fvar X) R (exp_fvar X) ((X,bind_qua B)::E) E).
  { apply replace_env_start; try solve_notin. rewrite replace_q_fresh by solve_notin; exact HS. }
  assert (scR : scope_q 0 R) by solve_scoped.
  pose proof (wf_qtyp_replace X (typ_fvar X) R (exp_fvar X) I scR
    _ _ (H X ltac:(solve_notin)) _ HR HE) as HT.
  rewrite replace_intro_qt_q in HT; auto; solve_notin.
Qed.

Lemma inst_sub_t : forall L E B A T U,
  (forall X : atom, X `notin` L ->
    subqtype (X ~ bind_sub B ++ E) (open_tqt T X) (open_tqt U X)) ->
  sub E A B -> subqtype E (open_tqt T A) (open_tqt U A).
Proof.
  intros L E B A T U H HS.
  destruct (sub_regular _ _ _ HS) as [HE [HA _]].
  inst_fresh L E (union (atoms_t B) (union (atoms_qt T) (atoms_qt U))).
  assert (HR : replace_env X A (qua_fvar X) (exp_fvar X) ((X,bind_sub B)::E) E).
  { apply replace_env_start; try solve_notin. rewrite replace_t_fresh by solve_notin; exact HS. }
  assert (scA : scope_t 0 A) by solve_scoped.
  pose proof (subq_replace X A (qua_fvar X) (exp_fvar X) scA I
    _ _ _ (H X ltac:(solve_notin)) _ HR HE) as HT.
  repeat rewrite replace_intro_qt_t in HT by (auto; solve_notin); exact HT.
Qed.

Lemma inst_sub_q : forall L E B R T U,
  (forall X : atom, X `notin` L ->
    subqtype (X ~ bind_qua B ++ E) (open_qqt T X) (open_qqt U X)) ->
  subqual E R B -> subqtype E (open_qqt T R) (open_qqt U R).
Proof.
  intros L E B R T U H HS.
  destruct (sq_regular _ _ _ HS) as [HE [HA _]].
  inst_fresh L E (union (atoms_q B) (union (atoms_qt T) (atoms_qt U))).
  assert (HR : replace_env X (typ_fvar X) R (exp_fvar X) ((X,bind_qua B)::E) E).
  { apply replace_env_start; try solve_notin. rewrite replace_q_fresh by solve_notin; exact HS. }
  assert (scR : scope_q 0 R) by solve_scoped.
  pose proof (subq_replace X (typ_fvar X) R (exp_fvar X) I scR
    _ _ _ (H X ltac:(solve_notin)) _ HR HE) as HT.
  repeat rewrite replace_intro_qt_q in HT by (auto; solve_notin); exact HT.
Qed.

Lemma inst_body_t : forall L E B A T P e,
  (forall X : atom, X `notin` L ->
    typing (X ~ bind_sub B ++ E) P (open_te e X) (open_tqt T X)) ->
  sub E A B -> typing E P (open_te e A) (open_tqt T A).
Proof.
  intros L E B A T P e H HS.
  destruct (sub_regular _ _ _ HS) as [HE [HA _]].
  inst_fresh L E (union (atoms_t B) (union (atoms_qt T) (atoms_e e))).
  assert (HR : replace_env X A (qua_fvar X) (exp_fvar X) ((X,bind_sub B)::E) E).
  { apply replace_env_start; try solve_notin. rewrite replace_t_fresh by solve_notin; exact HS. }
  assert (scA : scope_t 0 A) by solve_scoped.
  pose proof (typing_replace X A (qua_fvar X) (exp_fvar X) scA I I
    _ _ _ _ (H X ltac:(solve_notin)) _ HR HE) as HT.
  rewrite replace_q_id, replace_intro_et, replace_intro_qt_t in HT;
    first [exact HT | exact I | assumption | solve_notin].
Qed.

Lemma inst_body_q : forall L E B R T P e,
  (forall X : atom, X `notin` L ->
    typing (X ~ bind_qua B ++ E) P (open_qe e X) (open_qqt T X)) ->
  subqual E R B -> typing E P (open_qe e R) (open_qqt T R).
Proof.
  intros L E B R T P e H HS.
  destruct (sq_regular _ _ _ HS) as [HE [HA _]].
  inst_fresh L E (union (atoms_q B) (union (atoms_q P) (union (atoms_qt T) (atoms_e e)))).
  assert (HR : replace_env X (typ_fvar X) R (exp_fvar X) ((X,bind_qua B)::E) E).
  { apply replace_env_start; try solve_notin. rewrite replace_q_fresh by solve_notin; exact HS. }
  assert (scR : scope_q 0 R) by solve_scoped.
  pose proof (typing_replace X (typ_fvar X) R (exp_fvar X) I scR I
    _ _ _ _ (H X ltac:(solve_notin)) _ HR HE) as HT.
  rewrite (replace_q_fresh P X R) in HT by solve_notin.
  rewrite replace_intro_eq, replace_intro_qt_q in HT;
    first [exact HT | exact I | assumption | solve_notin].
Qed.

Lemma keep_qua_drop_sub : forall E X T, keep_qua ((X,bind_sub T)::E) E.
Proof.
  unfold keep_qua; intros E X T Y R B; apply binds_cons_iff in B.
  destruct B as [[? H]|B]; try discriminate; eauto.
Qed.

Lemma typing_regular : forall E Q e T, typing E Q e T -> wf_qua E Q /\ wf_qtyp E T.
Proof.
  induction 1; break_pairs; try solve [inversion H0; subst; eauto];
    try solve [split; eauto using wf_env_bind].
  - split; auto. exact (wf_env_bind _ H _ _ H0).
  - pick_bound. destruct (atom_fresh L) as [Y HY].
    destruct (H0 Y HY) as [HP HT].
    destruct (wf_term_drop E Y V) as [HS HQ].
    split; eauto.
  - match goal with H : wf_qtyp _ (qtyp_qtyp _ (typ_arrow _ _)) |- _ => inversion H; subst end.
    match goal with H : wf_typ _ (typ_arrow _ _) |- _ => inversion H; subst; auto end.
  - pick_bound. split; auto.
    constructor.
    + destruct (atom_fresh L) as [Y HY].
      destruct (H0 Y HY) as [HP HT].
      eapply wf_qua_env; [exact HP|apply keep_qua_drop_sub].
    + eapply wf_typ_all with (L := L); eauto.
      intros Y HY; exact (proj2 (H0 Y HY)).
  - inversion H2; subst.
    match goal with H : wf_typ E (typ_all _ _) |- _ => inversion H; subst end.
    split; eauto using inst_wf_t.
  - pick_bound. split; auto.
    constructor; auto. eapply wf_typ_qall with (L := L); eauto.
    intros Y HY; exact (proj2 (H1 Y HY)).
  - match goal with H : wf_qtyp E (qtyp_qtyp _ (typ_qall _ _)) |- _ => inversion H; subst end.
    match goal with H : wf_typ E (typ_qall _ _) |- _ => inversion H; subst end.
    split; eauto using inst_wf_q.
  - destruct (subq_regular _ _ _ H0) as [? [? ?]]; eauto.
  - destruct (sq_regular _ _ _ H0) as [? [? ?]]; eauto.
  - destruct (atom_fresh L) as [Y HY].
    destruct (H1 Y HY) as [_ HT].
    destruct (wf_term_drop E Y T1); eauto.
  - destruct (atom_fresh L) as [Y HY].
    destruct (H1 Y HY) as [_ HT].
    destruct (wf_term_drop E Y T1); eauto.
  - match goal with H : wf_qtyp E (qtyp_qtyp _ (typ_pair _ _)) |- _ => inversion H; subst end.
    match goal with H : wf_typ E (typ_pair _ _) |- _ => inversion H; subst; auto end.
  - match goal with H : wf_qtyp E (qtyp_qtyp _ (typ_pair _ _)) |- _ => inversion H; subst end.
    match goal with H : wf_typ E (typ_pair _ _) |- _ => inversion H; subst; auto end.
  - destruct (sq_regular _ _ _ H0) as [? [? ?]].
    match goal with H : wf_qtyp E (qtyp_qtyp _ _) |- _ => inversion H; subst; auto end.
Qed.

Lemma typing_ctx_regular : forall E Q c T, typing_ctx E Q c T ->
  wf_env E /\ wf_qua E Q /\ wf_qtyp E T.
Proof.
  induction 1; break_pairs;
    repeat match goal with H : typing _ _ _ _ |- _ =>
      destruct (typing_regular _ _ _ _ H) as [? ?]; clear H end;
    repeat match goal with H : subqual _ _ _ |- _ =>
      destruct (sq_regular _ _ _ H) as [? [? ?]]; clear H end;
    repeat match goal with H : sub _ _ _ |- _ =>
      destruct (sub_regular _ _ _ H) as [? [? ?]]; clear H end;
    repeat match goal with H : subqtype _ _ _ |- _ =>
      destruct (subq_regular _ _ _ H) as [? [? ?]]; clear H end;
    try solve [repeat split; auto].
  - inversion H6; subst.
    match goal with H : wf_typ _ (typ_arrow _ _) |- _ => inversion H; subst; auto end.
  - repeat split; auto. eapply wf_typ_all with (L := L); eauto.
  - repeat split; auto. eapply wf_typ_qall with (L := L); eauto.
  - destruct (atom_fresh L) as [X HX].
    pose proof (typing_env_regular _ _ _ _ (H0 X HX)) as HF.
    pose proof (wf_env_bound _ _ _ HF) as HT; cbn in HT; auto.
  - inversion H2; subst.
    match goal with H : wf_typ _ (typ_sum _ _) |- _ => inversion H; subst; auto end.
  - inversion H2; subst.
    match goal with H : wf_typ _ (typ_sum _ _) |- _ => inversion H; subst; auto end.
  - assert (wf_qtyp E T1) by
      (destruct (atom_fresh L) as [X HX];
       exact (wf_env_bound _ _ _ (typing_env_regular _ _ _ _ (H1 X HX)))).
    assert (wf_qtyp E T2) by
      (destruct (atom_fresh L) as [X HX];
       exact (wf_env_bound _ _ _ (typing_env_regular _ _ _ _ (H2 X HX)))).
    repeat split; auto.
  - match goal with H : wf_qtyp _ (qtyp_qtyp _ (typ_pair _ _)) |- _ => inversion H; subst end.
    match goal with H : wf_typ _ (typ_pair _ _) |- _ => inversion H; subst; auto end.
  - match goal with H : wf_qtyp _ (qtyp_qtyp _ (typ_pair _ _)) |- _ => inversion H; subst end.
    match goal with H : wf_typ _ (typ_pair _ _) |- _ => inversion H; subst; auto end.
  - destruct t; simpl; auto.
  - auto.
  - match goal with H : wf_qtyp _ (qtyp_qtyp _ _) |- _ => inversion H; subst; auto end.
Qed.

Lemma typing_local : forall E Q e T, typing E Q e T -> expr e.
Proof.
  induction 1; eauto.
  - pick_bound. destruct (typing_regular _ _ _ _ (typing_abs L E P V e1 T1 H)) as [_ HT].
    inversion HT; subst.
    match goal with HW : wf_typ _ (typ_arrow _ _) |- _ => inversion HW; subst end.
    eapply expr_abs with (L := L); eauto using wf_qua_qual.
    eapply (proj2 wf_ty_local); eassumption.
  - pick_bound. destruct (typing_regular _ _ _ _ (typing_tabs L E P V e1 T1 H)) as [_ HT].
    inversion HT; subst.
    eapply expr_tabs with (L := L); eauto using wf_qua_qual.
    eapply (proj1 wf_ty_local); eassumption.
  - eapply expr_tapp; eauto. apply (proj1 wf_ty_local) with (E := E).
    exact (proj1 (proj2 (sub_regular _ _ _ H0))).
  - pick_bound. eapply expr_qabs with (L := L); eauto using wf_qua_qual.
  - eapply expr_qapp; eauto. eapply wf_qua_qual.
    exact (proj1 (proj2 (sq_regular _ _ _ H0))).
  - eauto using wf_qua_qual.
  - eauto using wf_qua_qual.
  - eauto using wf_qua_qual.
  - eapply expr_upqual; eauto. eapply wf_qua_qual.
    exact (proj2 (proj2 (sq_regular _ _ _ H0))).
  - eapply expr_check; eauto. eapply wf_qua_qual.
    exact (proj2 (proj2 (sq_regular _ _ _ H0))).
Qed.

Lemma typing_value_bot : forall E Q e T,
  typing E Q e T -> value e -> typing E qua_bot e T.
Proof. induction 1; intros HV; inversion HV; subst; eauto. Qed.

Lemma typing_value_at : forall E Q e T P,
  typing E Q e T -> value e -> wf_qua E P -> typing E P e T.
Proof. eauto using typing_value_bot, typing_env_regular. Qed.

(* The premises of the constructor for the top frame, after applying any
   input subsumption to the focused expression. *)
Definition frame_input E Q f k T : Prop :=
  match f with
  | frame_abs e => exists U V, T = qtyp_qtyp Q (typ_arrow U V) /\
      typing_ctx E Q k V /\ typing E Q e U
  | frame_app e => exists V, typing_ctx E Q k V /\ value e /\
      typing E Q e (qtyp_qtyp Q (typ_arrow T V))
  | frame_tabs A => exists L B U, T = qtyp_qtyp Q (typ_all B U) /\
      typing_ctx E Q k (open_tqt U A) /\ sub E A B /\
      (forall X : atom, X `notin` L -> wf_qtyp (X ~ bind_sub B ++ E) (open_tqt U X))
  | frame_qabs R => exists L P U, T = qtyp_qtyp Q (typ_qall P U) /\
      typing_ctx E Q k (open_qqt U R) /\ subqual E R P /\
      (forall X : atom, X `notin` L -> wf_qtyp (X ~ bind_qua P ++ E) (open_qqt U X))
  | frame_let e => exists L U, typing_ctx E Q k U /\
      (forall X : atom, X `notin` L -> typing (X ~ bind_typ T ++ E) Q (open_ee e X) U)
  | frame_inl P => exists U, typing_ctx E Q k (qtyp_qtyp P (typ_sum T U))
  | frame_inr P => exists U, typing_ctx E Q k (qtyp_qtyp P (typ_sum U T))
  | frame_case e1 e2 => exists L P U V W, T = qtyp_qtyp P (typ_sum U V) /\
      wf_qua E P /\ typing_ctx E Q k W /\
      (forall X : atom, X `notin` L -> typing (X ~ bind_typ U ++ E) Q (open_ee e1 X) W) /\
      (forall X : atom, X `notin` L -> typing (X ~ bind_typ V ++ E) Q (open_ee e2 X) W)
  | frame_pair_1 P e => exists U, wf_qua E P /\
      typing_ctx E Q k (qtyp_qtyp P (typ_pair T U)) /\ typing E Q e U
  | frame_pair_2 P e => exists U, wf_qua E P /\
      typing_ctx E Q k (qtyp_qtyp P (typ_pair U T)) /\ value e /\ typing E Q e U
  | frame_first => exists P U V, T = qtyp_qtyp P (typ_pair U V) /\
      wf_qua E P /\ typing_ctx E Q k U /\ wf_qtyp E V
  | frame_second => exists P U V, T = qtyp_qtyp P (typ_pair U V) /\
      wf_qua E P /\ typing_ctx E Q k V /\ wf_qtyp E U
  | frame_barrier t => exists P s, Q = abstractize t /\
      typing_ctx E P k T /\ concretize P = Some s /\ t ≤ s
  | frame_upqual P => exists U, T = qtyp_qtyp P U /\ typing_ctx E Q k T
  | frame_check R => exists P U, T = qtyp_qtyp (qua_meet P R) U /\
      wf_qua E R /\ typing_ctx E Q k (qtyp_qtyp P U)
  end.

Lemma expose_ctx : forall E Q c T, typing_ctx E Q c T ->
  match c with
  | nil => True
  | f::k => forall e, typing E Q e T ->
      exists P U, typing E P e U /\ frame_input E P f k U
  end.
Proof.
  induction 1; simpl; try exact I;
    try solve [intros term HT; do 2 eexists; split; [exact HT|];
               repeat (first [eassumption | reflexivity | eexists | split])].
  - destruct c as [|f c]; simpl in *; eauto.
  - destruct c as [|f c]; simpl in *; eauto.
Qed.

Ltac wf_pair_parts :=
  repeat match goal with
  | H : wf_qtyp _ (qtyp_qtyp _ _) |- _ => inversion H; clear H; subst
  | H : wf_typ _ (typ_pair _ _) |- _ => inversion H; clear H; subst
  | H : wf_typ _ (typ_sum _ _) |- _ => inversion H; clear H; subst
  end.

Definition focus e (k : ctx) : option state :=
  match e with
  | exp_app a b => Some 〈 a | frame_abs b :: k 〉
  | exp_tapp a T => Some 〈 a | frame_tabs T :: k 〉
  | exp_qapp a R => Some 〈 a | frame_qabs R :: k 〉
  | exp_let a b => Some 〈 a | frame_let b :: k 〉
  | exp_inl P a => Some 〈 a | frame_inl P :: k 〉
  | exp_inr P a => Some 〈 a | frame_inr P :: k 〉
  | exp_case a b c => Some 〈 a | frame_case b c :: k 〉
  | exp_pair P a b => Some 〈 a | frame_pair_1 P b :: k 〉
  | exp_first a => Some 〈 a | frame_first :: k 〉
  | exp_second a => Some 〈 a | frame_second :: k 〉
  | exp_upqual P a => Some 〈 a | frame_upqual P :: k 〉
  | exp_check P a => Some 〈 a | frame_check P :: k 〉
  | _ => None
  end.

Lemma focus_preserves : forall E Q e T, typing E Q e T ->
  forall k, typing_ctx E Q k T ->
  match focus e k with Some s => typing_state E s | None => True end.
Proof.
  induction 1; simpl; intros k HK; try exact I.
  - eapply typing_step; [exact H|]. eapply typing_ctx_abs; eassumption.
  - eapply typing_step; [exact H|].
    destruct (typing_regular _ _ _ _ H) as [_ HW].
    inversion HW; subst.
    match goal with H : wf_typ _ (typ_all _ _) |- _ => inversion H; subst end.
    eapply typing_ctx_tabs; eauto.
  - eapply typing_step; [exact H|].
    destruct (typing_regular _ _ _ _ H) as [_ HW].
    inversion HW; subst.
    match goal with H : wf_typ _ (typ_qall _ _) |- _ => inversion H; subst end.
    eapply typing_ctx_qabs; eauto.
  - specialize (IHtyping k (typing_ctx_sub E Q k S T HK H0)). destruct (focus e k); exact IHtyping.
  - specialize (IHtyping k (typing_ctx_subqual E R Q k T HK H0)). destruct (focus e k); exact IHtyping.
  - eapply typing_step; [exact H|]. eapply typing_ctx_let; eauto.
  - eapply typing_step; [eassumption|]. eapply typing_ctx_inl; eassumption.
  - eapply typing_step; [eassumption|]. eapply typing_ctx_inr; eassumption.
  - eapply typing_step; [exact H|].
    destruct (typing_regular _ _ _ _ H) as [_ HW]; wf_pair_parts.
    eapply typing_ctx_case; eauto.
  - eapply typing_step; [eassumption|]. eapply typing_ctx_pair_1; eassumption.
  - eapply typing_step; [exact H|].
    destruct (typing_regular _ _ _ _ H) as [_ HW]; wf_pair_parts.
    eapply typing_ctx_first; eauto.
  - eapply typing_step; [exact H|].
    destruct (typing_regular _ _ _ _ H) as [_ HW]; wf_pair_parts.
    eapply typing_ctx_second; eauto.
  - destruct (sq_regular _ _ _ H0) as [HE [HQ HP]].
    destruct (typing_regular _ _ _ _ H) as [_ HW]; inversion HW; subst.
    eapply typing_step; [|apply typing_ctx_upqual; exact HK].
    eapply typing_sub; [exact H|]; eauto using sub_refl.
  - destruct (sq_regular _ _ _ H0) as [HE [HQ HP]].
    destruct (typing_regular _ _ _ _ H) as [_ HW]; inversion HW; subst.
    eapply typing_step; [|apply typing_ctx_check; eauto].
    eapply typing_sub; [exact H|]; eauto using sq_refl, sub_refl.
Qed.

Definition value_qua e :=
  match e with
  | exp_abs P _ _ | exp_tabs P _ _ | exp_qabs P _ _
  | exp_inl P _ | exp_inr P _ | exp_pair P _ _ => P
  | _ => qua_bot
  end.

Definition value_head E Q e B : Prop :=
  match e with
  | exp_abs P V b => exists L T, B = typ_arrow V T /\
      (forall X : atom, X `notin` L -> typing (X ~ bind_typ V ++ E) P (open_ee b X) T)
  | exp_tabs P V b => exists L T, B = typ_all V T /\
      (forall X : atom, X `notin` L -> typing (X ~ bind_sub V ++ E) P (open_te b X) (open_tqt T X))
  | exp_qabs P R b => exists L T, B = typ_qall R T /\
      (forall X : atom, X `notin` L -> typing (X ~ bind_qua R ++ E) P (open_qe b X) (open_qqt T X))
  | exp_inl P v => exists T U, B = typ_sum T U /\ typing E Q v T /\ wf_qtyp E U
  | exp_inr P v => exists T U, B = typ_sum T U /\ typing E Q v U /\ wf_qtyp E T
  | exp_pair P v w => exists T U, B = typ_pair T U /\ typing E Q v T /\ typing E Q w U
  | _ => False
  end.

Lemma view_value : forall E Q e T, typing E Q e T -> value e ->
  exists B, value_head E Q e B /\ subqtype E (qtyp_qtyp (value_qua e) B) T.
Proof.
  intros E Q e T HT.
  pose proof HT as Horig.
  induction HT; intros HV; inversion HV; subst; simpl;
    try solve [eexists; split;
      [repeat (first [eassumption | reflexivity | eexists | split]) |
       apply subq_refl; [exact (proj2 (typing_regular _ _ _ _ Horig))|eauto using typing_env_regular]]].
  all: try solve [destruct (IHHT HT HV) as [B [HB HS]];
                  eexists; split; [exact HB|eauto using subq_trans]].
  all: destruct (IHHT HT HV) as [B [HB HS]];
    exists B; split; auto;
    cbn in *; repeat match goal with H : exists _, _ |- _ => destruct H end; break_pairs; subst;
    repeat (first [eassumption | reflexivity | eexists | split | eapply typing_subqual; eassumption]).
Qed.

Lemma value_qualifier : forall E Q e P B, typing E Q e (qtyp_qtyp P B) -> value e ->
  subqual E (value_qua e) P.
Proof.
  intros E Q e P B HT HV.
  destruct (view_value _ _ _ _ HT HV) as [A [_ HA]].
  inversion HA; subst; auto.
Qed.

Definition change_value_qua (P : qua) e :=
  match e with
  | exp_abs _ A b => exp_abs P A b
  | exp_tabs _ A b => exp_tabs P A b
  | exp_qabs _ R b => exp_qabs P R b
  | exp_inl _ v => exp_inl P v
  | exp_inr _ v => exp_inr P v
  | exp_pair _ v w => exp_pair P v w
  | _ => e
  end.

Lemma value_head_raise : forall E Q e B P,
  value_head E Q e B -> subqual E (value_qua e) P ->
  wf_qua E Q -> typing E Q (change_value_qua P e) (qtyp_qtyp P B).
Proof.
  intros E Q e B P HH HS HQ.
  destruct e; cbn in *; try contradiction;
    repeat match goal with H : exists _, _ |- _ => destruct H end;
    break_pairs; subst;
    destruct (sq_regular _ _ _ HS) as [HE [_ HP]];
    try solve [eauto].
  all: eapply typing_subqual; [|apply subqual_bot; assumption].
  - eapply typing_abs with (L := x). intros Y HY.
    pose proof (H0 Y HY) as HB.
    eapply typing_subqual; [exact HB|].
    eapply sq_env; [exact HS|eauto using typing_env_regular|apply keep_binds_head].
  - eapply typing_tabs with (L := x). intros Y HY.
    pose proof (H0 Y HY) as HB.
    eapply typing_subqual; [exact HB|].
    eapply sq_env; [exact HS|eauto using typing_env_regular|apply keep_binds_head].
  - eapply typing_qabs with (L := x); auto. intros Y HY.
    pose proof (H0 Y HY) as HB.
    eapply typing_subqual; [exact HB|].
    eapply sq_env; [exact HS|eauto using typing_env_regular|apply keep_binds_head].
Qed.

Lemma type_raised_value : forall E Q e P T,
  typing E Q e (qtyp_qtyp P T) -> value e ->
  typing E Q (change_value_qua P e) (qtyp_qtyp P T).
Proof.
  intros E Q e P T HT HV.
  destruct (view_value _ _ _ _ HT HV) as [B [HB HS]].
  destruct (typing_regular _ _ _ _ HT) as [HQ _].
  inversion HS; subst.
  eapply typing_sub.
  - eapply value_head_raise; eassumption.
  - constructor; auto.
    match goal with H : subqual _ _ _ |- _ => destruct (sq_regular _ _ _ H) as [? [? ?]] end; eauto using sq_refl.
Qed.

Lemma type_checked_value : forall E Q e P R T,
  typing E Q e (qtyp_qtyp (qua_meet P R) T) ->
  typing E Q e (qtyp_qtyp P T).
Proof.
  intros E Q e P R T HT.
  destruct (typing_regular _ _ _ _ HT) as [_ HW].
  inversion HW; subst.
  match goal with H : wf_qua _ (qua_meet _ _) |- _ => inversion H; subst end.
  pose proof (typing_env_regular _ _ _ _ HT).
  eapply typing_sub; [exact HT|].
  constructor; eauto using sq_meet_l, sub_refl.
Qed.

Ltac unpack_exists :=
  repeat match goal with H : exists _, _ |- _ => destruct H end;
  break_pairs; subst.

Ltac invert_value_head HT HV :=
  let HH := fresh "Hhead" in let HS := fresh "Hsub" in let B := fresh "Body" in
  destruct (view_value _ _ _ _ HT HV) as [B [HH HS]];
  cbn in HH, HS; unpack_exists;
  inversion HS; clear HS; subst;
  match goal with H : sub _ _ _ |- _ => inversion H; subst end.

Lemma push_barrier_typed : forall E P Q e k S T t,
  typing E P e S -> typing_ctx E Q k T ->
  subqtype E S T -> subqual E P Q -> concretize P = Some t ->
  typing_state E 〈 e | frame_barrier t :: k 〉.
Proof.
  intros E P Q e k U T t HT HK HS HP HC.
  destruct (sq_regular _ _ _ HP) as [HE [HW _]].
  destruct (concrete_equiv _ _ HE HW _ HC) as [Hup Hdown].
  eapply typing_step.
  - eapply typing_subqual; [eapply typing_sub; eassumption|exact Hup].
  - eapply typing_ctx_barrier with (Q := abstractize t) (s := t).
    + eapply typing_ctx_subqual; [exact HK|eauto using sq_trans].
    + destruct t; reflexivity.
    + constructor.
Qed.

Lemma preserve_beta_abs : forall E Q P V b v U T k t,
  typing E Q (exp_abs P V b) (qtyp_qtyp Q (typ_arrow U T)) ->
  typing E Q v U -> value (exp_abs P V b) -> value v ->
  typing_ctx E Q k T -> concretize P = Some t ->
  typing_state E 〈 open_ee b v | frame_barrier t :: k 〉.
Proof.
  intros E Q P V b v U T k t Hfun Harg HV Hv HK HC.
  invert_value_head Hfun HV.
  eapply push_barrier_typed; try eassumption.
  eapply inst_term; [exact H0| |exact Hv].
  eapply typing_sub; [eapply typing_value_bot; eassumption|eassumption].
Qed.

Lemma preserve_beta_tabs : forall E Q P B b A U T k t,
  typing E Q (exp_tabs P B b) (qtyp_qtyp Q (typ_all U T)) ->
  sub E A U -> typing_ctx E Q k (open_tqt T A) -> concretize P = Some t ->
  typing_state E 〈 open_te b A | frame_barrier t :: k 〉.
Proof.
  intros E Q P B b A U T k t HT HA HK HC.
  assert (HV : value (exp_tabs P B b)) by (constructor; eapply typing_local; eassumption).
  invert_value_head HT HV.
  eapply push_barrier_typed; try eassumption.
  - eapply inst_body_t; [exact H0|eauto using sub_trans].
  - eapply inst_sub_t; [exact H8|exact HA].
Qed.

Lemma preserve_beta_qabs : forall E Q P B b A U T k t,
  typing E Q (exp_qabs P B b) (qtyp_qtyp Q (typ_qall U T)) ->
  subqual E A U -> typing_ctx E Q k (open_qqt T A) -> concretize P = Some t ->
  typing_state E 〈 open_qe b A | frame_barrier t :: k 〉.
Proof.
  intros E Q P B b A U T k t HT HA HK HC.
  assert (HV : value (exp_qabs P B b)) by (constructor; eapply typing_local; eassumption).
  invert_value_head HT HV.
  eapply push_barrier_typed; try eassumption.
  - eapply inst_body_q; [exact H0|eauto using sq_trans].
  - match goal with H : forall X : atom, X `notin` _ -> subqtype _ _ _ |- _ =>
      eapply inst_sub_q; [exact H|exact HA] end.
Qed.

Lemma value_from_components : forall E Q e T, typing E Q e T ->
  match e with
  | exp_abs _ _ _ | exp_tabs _ _ _ | exp_qabs _ _ _ => value e
  | exp_inl _ v | exp_inr _ v => value v -> value e
  | exp_pair _ v w => value v -> value w -> value e
  | _ => True
  end.
Proof.
  intros E Q e T H. pose proof (typing_local _ _ _ _ H) as HL.
  destruct e; simpl; intros; eauto; inversion HL; subst; auto.
Qed.

Ltac decompose_frame :=
  match goal with
  | HT : typing ?E ?Q ?e ?T, HK : typing_ctx ?E ?Q (_ :: _) ?T |- _ =>
    let Hfocus := fresh "Hfocus" in
    destruct (expose_ctx _ _ _ _ HK e HT) as [? [? [Hfocus ?]]];
    clear HT HK; cbn in *; unpack_exists
  end.

Ltac make_value e HV :=
  assert (HV : value e) by
    (first [assumption | match goal with H : typing _ _ e _ |- _ =>
       pose proof (value_from_components _ _ _ _ H) as Hval;
       cbn in Hval; auto end]).

Ltac typed_head e :=
  let HV := fresh "HV" in make_value e HV;
  match goal with HT : typing _ _ e _ |- _ => invert_value_head HT HV end.

Ltac use_open_term :=
  match goal with
  | H : forall X : atom, X `notin` _ -> typing ((X,bind_typ _)::_) _ _ _ |- _ => exact H
  end.

Theorem preservation : forall E s s',
  typing_state E s ->
  s --> s' ->
  typing_state E s'.
Proof.
  intros E s s' HT HS. destruct HS; inversion HT; subst; clear HT.
  all: try solve [match goal with
  | HT : typing _ _ _ _, HK : typing_ctx _ _ _ _ |- _ =>
    exact (focus_preserves _ _ _ _ HT _ HK)
  end].
  all: decompose_frame.
  all: try solve [
    match goal with HT : typing _ _ ?e (qtyp_qtyp ?P _) |- _ =>
      let HV := fresh "HV" in make_value e HV;
      eapply typing_step; [exact (type_raised_value _ _ _ _ _ HT HV)|eassumption]
    end].
  all: try solve [eapply typing_step; [eapply type_checked_value; eassumption|eassumption]].
  - eapply typing_step; [|eassumption].
    match goal with HK : typing_ctx _ _ _ _ |- _ =>
      destruct (typing_ctx_regular _ _ _ _ HK) as [_ [? _]]
    end.
    eapply typing_value_at; eassumption.
  - eapply typing_step; [eassumption|]. eapply typing_ctx_app; eassumption.
  - eapply typing_step; [eassumption|]. eapply typing_ctx_pair_2; eassumption.
  - eapply preserve_beta_abs; eassumption.
  - eapply preserve_beta_tabs; eassumption.
  - eapply preserve_beta_qabs; eassumption.
  - eapply typing_step; [|eassumption].
    eapply inst_term; [use_open_term|eapply typing_value_bot; eassumption|assumption].
  - typed_head (exp_inl P v1).
    eapply typing_step; [|eassumption].
    eapply inst_term; [use_open_term| |assumption].
    eapply typing_sub; [eapply typing_value_bot; eassumption|eassumption].
  - typed_head (exp_inr P v1).
    eapply typing_step; [|eassumption].
    eapply inst_term; [use_open_term| |assumption].
    eapply typing_sub; [eapply typing_value_bot; eassumption|eassumption].
  - typed_head (exp_pair P v1 v2).
    eapply typing_step; [eapply typing_sub; eassumption|eassumption].
  - typed_head (exp_pair P v1 v2).
    eapply typing_step; [eapply typing_sub; eassumption|eassumption].
  - match goal with HK : typing_ctx _ _ _ _ |- _ =>
      destruct (typing_ctx_regular _ _ _ _ HK) as [_ [_ HW]]; wf_pair_parts
    end.
    eapply typing_step; [|eassumption]. eapply typing_inl; eassumption.
  - match goal with HK : typing_ctx _ _ _ _ |- _ =>
      destruct (typing_ctx_regular _ _ _ _ HK) as [_ [_ HW]]; wf_pair_parts
    end.
    eapply typing_step; [|eassumption]. eapply typing_inr; eassumption.
  - eapply typing_step; [|eassumption]. eapply typing_pair; eassumption.
Qed.

Lemma concrete_le_trans : forall r s t, r ≤ s -> s ≤ t -> r ≤ t.
Proof. intros r s t H1 H2; inversion H1; subst; inversion H2; subst; constructor. Qed.

Lemma barrier_down : forall k s, barrier_compatible k s ->
  forall t, t ≤ s -> barrier_compatible k t.
Proof.
  induction 1; intros u Hu; eauto using barrier_compatible, concrete_le_trans.
Qed.

Lemma closed_ctx_barriers : forall Q k T, typing_ctx empty Q k T ->
  forall t, concretize Q = Some t -> barrier_compatible k t.
Proof.
  intros Q k T H; remember empty as E eqn:HE.
  induction H; subst; intros u HU;
    try solve [apply barrier_compatible_done];
    try solve [apply barrier_compatible_other; [eauto|discriminate]].
  - assert (u = t) by (destruct t; simpl in HU; congruence); subst.
    apply barrier_compatible_frame; [|constructor].
    eapply barrier_down; eauto.
  - eauto.
  - destruct (sq_regular _ _ _ H0) as [_ [_ HQ]].
    destruct (concrete_total _ HQ) as [t Ht].
    eapply barrier_down; eauto using concrete_order.
Qed.

Lemma qualifier_comparison : forall P Q, subqual empty P Q ->
  exists s t, concretize P = Some s /\ concretize Q = Some t /\ s ≤ t.
Proof.
  intros P Q H.
  destruct (sq_regular _ _ _ H) as [_ [HP HQ]].
  destruct (concrete_total _ HP) as [s Hs], (concrete_total _ HQ) as [t Ht].
  exists s, t. repeat split; auto. eapply concrete_order; eassumption.
Qed.

Lemma ready_call : forall Q e B k T,
  typing empty Q e (qtyp_qtyp Q B) -> value e -> typing_ctx empty Q k T ->
  exists s, concretize (value_qua e) = Some s /\ barrier_compatible k s.
Proof.
  intros Q e B k T HE HV HK.
  pose proof (value_qualifier _ _ _ _ _ HE HV) as HS.
  destruct (qualifier_comparison _ _ HS) as [s [t [Hs [Ht Hst]]]].
  eauto using closed_ctx_barriers, barrier_down.
Qed.

Definition canonical_at e B : Prop :=
  match B with
  | typ_arrow _ _ => exists P U b, e = exp_abs P U b
  | typ_all _ _ => exists P U b, e = exp_tabs P U b
  | typ_qall _ _ => exists P U b, e = exp_qabs P U b
  | typ_sum _ _ => (exists P v, e = exp_inl P v /\ value v) \/
                   (exists P v, e = exp_inr P v /\ value v)
  | typ_pair _ _ => exists P v w, e = exp_pair P v w /\ value v /\ value w
  | _ => True
  end.

Lemma canonical_value : forall E Q e P B,
  typing E Q e (qtyp_qtyp P B) -> value e -> canonical_at e B.
Proof.
  intros E Q e P B HT HV.
  destruct (view_value _ _ _ _ HT HV) as [A [HH HS]].
  inversion HS; subst; clear HS.
  destruct HV; cbn in HH; unpack_exists;
    match goal with H : sub _ _ _ |- _ => inversion H; subst end;
    simpl; eauto 8.
Qed.

Lemma closed_fvar_impossible : forall Q x T, ~ typing empty Q (exp_fvar x) T.
Proof.
  intros Q x T H.
  remember (exp_fvar x) as e; remember empty as E.
  induction H; inversion Heqe; subst; eauto.
Qed.

Lemma focus_progress : forall Q e T, typing empty Q e T ->
  forall k, value e \/ exists s', 〈 e | k 〉 --> s'.
Proof.
  intros Q e T HT k.
  pose proof (typing_local _ _ _ _ HT) as HL.
  destruct e;
    try solve [inversion HL];
    try solve [left; constructor; exact HL];
    try solve [right; eexists; constructor].
  exfalso; eapply closed_fvar_impossible; eassumption.
Qed.

Lemma step_qual_ready : forall Q e P T,
  typing empty Q e (qtyp_qtyp P T) -> value e ->
  exists s t, concretize (value_qua e) = Some s /\ concretize P = Some t /\ s ≤ t.
Proof. intros; apply qualifier_comparison; eauto using value_qualifier. Qed.

Lemma step_check_ready : forall Q e P R T,
  typing empty Q e (qtyp_qtyp (qua_meet P R) T) -> value e ->
  exists s t, concretize (value_qua e) = Some s /\ concretize R = Some t /\ s ≤ t.
Proof.
  intros Q e P R T HT HV.
  pose proof (value_qualifier _ _ _ _ _ HT HV) as HS.
  destruct (sq_regular _ _ _ HS) as [HE [_ HM]].
  inversion HM; subst.
  apply qualifier_comparison; eauto using sq_trans, sq_meet_r.
Qed.

Ltac canonicalize e :=
  match goal with
  | HT : typing _ _ e (qtyp_qtyp _ _) , HV : value e |- _ =>
    let HC := fresh "Hcanonical" in
    pose proof (canonical_value _ _ _ _ _ HT HV) as HC; cbn in HC;
    try (destruct HC); unpack_exists
  end.

Ltac call_ready e :=
  match goal with
  | HT : typing _ ?Q e (qtyp_qtyp ?Q _), HK : typing_ctx _ ?Q _ _, HV : value e |- _ =>
    let s := fresh "s" in let Hc := fresh "Hconcrete" in let Hb := fresh "Hbarriers" in
    destruct (ready_call _ _ _ _ _ HT HV HK) as [s [Hc Hb]]; cbn in Hc
  end.

Lemma progress_value_frame : forall Q e T f k,
  typing empty Q e T -> value e -> frame_input empty Q f k T ->
  exists s', 〈 e | f :: k 〉 --> s'.
Proof.
  intros Q e T f k HT HV HF. destruct f; cbn in HF; unpack_exists.
  - eexists; apply step_app_2; assumption.
  - canonicalize f.
    match goal with H : typing _ _ (exp_abs ?P ?V ?b) _ |- _ =>
      call_ready (exp_abs P V b)
    end.
    eexists; eapply step_app_abs; eassumption.
  - canonicalize e.
    match goal with H : typing _ _ (exp_tabs ?P ?V ?b) _ |- _ =>
      call_ready (exp_tabs P V b)
    end.
    eexists; eapply step_app_tabs; try eassumption.
    match goal with H : sub _ _ _ |- _ =>
      apply (proj1 wf_ty_local) with (E := empty);
      exact (proj1 (proj2 (sub_regular _ _ _ H)))
    end.
  - canonicalize e.
    match goal with H : typing _ _ (exp_qabs ?P ?V ?b) _ |- _ =>
      call_ready (exp_qabs P V b)
    end.
    eexists; eapply step_app_qabs; try eassumption.
    match goal with H : subqual _ _ _ |- _ =>
      apply wf_qua_qual with (E := empty);
      exact (proj1 (proj2 (sq_regular _ _ _ H)))
    end.
  - eexists; apply step_let_value; assumption.
  - eexists; apply step_make_inl; assumption.
  - eexists; apply step_make_inr; assumption.
  - canonicalize e;
      eexists; first [apply step_case_inl; assumption | apply step_case_inr; assumption].
  - eexists; apply step_pair_2; assumption.
  - eexists; apply step_make_pair; assumption.
  - canonicalize e. eexists; apply step_first_pair; assumption.
  - canonicalize e. eexists; apply step_second_pair; assumption.
  - destruct (step_qual_ready _ _ _ _ HT HV) as [s [t [Hs [Ht Hle]]]].
    destruct HV; cbn in Hs; eexists;
      first [eapply step_upqual_abs | eapply step_upqual_tabs | eapply step_upqual_qabs |
             eapply step_upqual_inl | eapply step_upqual_inr | eapply step_upqual_pair];
      eassumption.
  - destruct (step_check_ready _ _ _ _ _ HT HV) as [s [t [Hs [Ht Hle]]]].
    destruct HV; cbn in Hs; eexists;
      first [eapply step_check_abs | eapply step_check_tabs | eapply step_check_qabs |
             eapply step_check_inl | eapply step_check_inr | eapply step_check_pair];
      eassumption.
  - eexists; apply step_barrier; assumption.
Qed.

Theorem progress : forall s,
  typing_state empty s ->
  done_state s \/ exists s', s --> s'.
Proof.
  intros s HT. inversion HT as [E Q e k T HE HK]; subst.
  destruct (focus_progress _ _ _ HE k) as [HV|HS]; [|right; exact HS].
  destruct k as [|f k].
  - left. constructor; exact HV.
  - right.
    destruct (expose_ctx _ _ _ _ HK e HE) as [P [U [Htyped Hframe]]].
    eapply progress_value_frame; eassumption.
Qed.
