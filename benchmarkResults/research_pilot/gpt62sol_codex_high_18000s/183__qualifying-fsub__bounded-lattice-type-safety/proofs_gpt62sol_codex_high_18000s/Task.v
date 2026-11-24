From Fsub.ExtendedBase Require Import Fsub_LetSum_Definitions.
From Stdlib Require Import Lia Arith.Wf_nat.

Local Hint Constructors wf_qua wf_typ wf_qtyp wf_env
  qual type qtype expr : core.

Scheme wf_typ_mut := Induction for wf_typ Sort Prop
with wf_qtyp_mut := Induction for wf_qtyp Sort Prop.
Combined Scheme wf_types_mut from wf_typ_mut, wf_qtyp_mut.

Scheme sub_mut := Induction for sub Sort Prop
with subqtype_mut := Induction for subqtype Sort Prop.
Combined Scheme sub_types_mut from sub_mut, subqtype_mut.

Local Ltac split_binds H :=
  apply binds_app_1 in H; destruct H as [H | H];
  [let Ex := fresh in let Eb := fresh in
   pose proof (binds_one_1 _ _ _ _ _ H) as Ex;
   pose proof (binds_one_2 _ _ _ _ _ H) as Eb; inversion Eb; subst | idtac].

Definition includes_env (E F : env) :=
  forall x b, binds x b E -> binds x b F.

Lemma includes_push : forall E F x b,
  includes_env E F -> includes_env (x ~ b ++ E) (x ~ b ++ F).
Proof.
  unfold includes_env. intros E F x b I y c H.
  split_binds H; auto using binds_app_2, binds_app_3.
Qed.

Lemma wf_qua_weaken_local : forall E Q, wf_qua E Q ->
  forall F, includes_env E F -> wf_qua F Q.
Proof. induction 1; unfold includes_env in *; eauto. Qed.

Lemma wf_types_weaken :
  (forall E T, wf_typ E T -> forall F, includes_env E F -> wf_typ F T) /\
  (forall E T, wf_qtyp E T -> forall F, includes_env E F -> wf_qtyp F T).
Proof.
  apply wf_types_mut; intros; eauto using includes_push, wf_qua_weaken_local.
Qed.

Definition wf_typ_weaken_local := proj1 wf_types_weaken.
Definition wf_qtyp_weaken_local := proj2 wf_types_weaken.

Local Hint Resolve wf_qua_weaken_local wf_typ_weaken_local wf_qtyp_weaken_local
  includes_push : core.

Lemma wf_lookup : forall E, wf_env E -> forall x b, binds x b E ->
  match b with
  | bind_sub T => wf_typ E T
  | bind_typ T => wf_qtyp E T
  | bind_qua Q => wf_qua E Q
  end.
Proof.
  induction 1; intros x0 b Hb; [inversion Hb| ..];
    split_binds Hb;
    try match goal with
    | IH : forall _ _, binds _ _ _ -> _, H : binds _ _ ?E |- _ =>
        specialize (IH _ _ H)
    end;
    try destruct b; simpl in *;
    (eapply wf_typ_weaken_local || eapply wf_qtyp_weaken_local
      || eapply wf_qua_weaken_local); eauto; red; auto using binds_app_3.
Qed.

Lemma subqual_regular : forall E Q R, subqual E Q R ->
  wf_env E /\ wf_qua E Q /\ wf_qua E R.
Proof.
  induction 1; intuition eauto;
    match goal with H : binds _ (bind_qua _) _ |- _ => eauto end.
Qed.

Lemma sub_types_env :
  (forall E S T, sub E S T -> wf_env E) /\
  (forall E S T, subqtype E S T -> wf_env E).
Proof.
  apply sub_types_mut; intros; eauto;
    match goal with H : subqual _ _ _ |- _ => exact (proj1 (subqual_regular _ _ _ H)) end.
Qed.

Lemma typing_env_local : forall E e T, typing E e T -> wf_env E.
Proof.
  induction 1; eauto.
  all: destruct (atom_fresh L) as [y Hy];
    specialize (H1 y Hy); inversion H1; assumption.
Qed.

Lemma qua_locally_closed : forall E Q, wf_qua E Q -> qual Q.
Proof. induction 1; auto. Qed.

Lemma types_locally_closed :
  (forall E T, wf_typ E T -> type T) /\
  (forall E T, wf_qtyp E T -> qtype T).
Proof. apply wf_types_mut; eauto using qua_locally_closed. Qed.

Lemma qua_reflexivity : forall E Q, wf_env E -> wf_qua E Q -> subqual E Q Q.
Proof.
  intros E Q WE W; induction W.
  - apply subqual_lift_elem; [assumption|apply reflexive].
  - eauto using subqual_refl_qvar.
  - apply subqual_meet_intro; eauto using subqual_meet_eliml, subqual_meet_elimr.
  - apply subqual_join_elim; eauto using subqual_join_inl, subqual_join_inr.
Qed.

Lemma lattice_upper : forall b : B, b ≤ top.
Proof. intro; apply meet_consistent; symmetry; apply meet_top. Qed.

Lemma lattice_lower : forall b : B, bot ≤ b.
Proof.
  intro; apply join_consistent. rewrite join_commutative, join_bot. reflexivity.
Qed.

Local Ltac unpack_qua :=
  repeat match goal with
  | H : subqual _ _ _ |- _ =>
      let W := fresh "W" in pose proof (subqual_regular _ _ _ H) as W;
      clear H; destruct W as [? [? ?]]
  end.

Lemma qua_transitivity : forall E A M C, subqual E A M -> subqual E M C ->
  subqual E A C.
Proof.
  intros E A M C H; revert C.
  induction H; intros C HC.
  all: try solve [apply subqual_bot; unpack_qua; assumption].
  all: try solve [eapply subqual_eval_elim; [eassumption|eassumption|eauto]].
  all: try solve [eapply subqual_eval_intro; [|eassumption|eassumption]; eauto].
  all: try assumption.
  all: try solve [eapply subqual_trans_qvar; eauto].
  all: try solve [eapply subqual_join_elim; eauto].
  all: try solve [eapply subqual_meet_eliml; eauto].
  all: try solve [eapply subqual_meet_elimr; eauto].
  all: match goal with HC : subqual ?E ?M ?C |- _ =>
    remember M as middle eqn:Em in HC;
    induction HC; inversion Em; subst; try clear Em
  end.
  all: try solve [apply subqual_top; solve [assumption | unpack_qua; auto]].
  all: try solve [eapply subqual_eval_elim; [eapply IHHC1; eauto|eassumption|eassumption]].
  all: try solve [eapply subqual_eval_intro; [eassumption|eassumption|eapply IHHC2; eauto]].
  all: try solve [apply subqual_join_inl; auto].
  all: try solve [apply subqual_join_inr; auto].
  all: try solve [apply subqual_meet_intro; auto].
  all: try solve [eauto using subqual_lift_elem, transitive].
  all: try solve [
    match goal with H : top ≤ ?b |- _ =>
      assert (b = top) by (apply antisymmetric; auto using lattice_upper); subst; auto using subqual_top
    | H : ?b ≤ bot |- _ =>
      assert (b = bot) by (apply antisymmetric; auto using lattice_lower); subst;
      apply subqual_bot; assumption
    | H : top = bot |- _ => exfalso; eapply nontrivial; eauto
    end ].
  all: eauto.
  all: try solve [exfalso; eapply nontrivial; symmetry; eassumption].
  all: try solve [apply subqual_lift_elem; [assumption|eapply transitive; eassumption]].
Qed.

(* Well-formedness of syntax depends on which kind of variable is bound. *)
Definition binding_kind (b : binding) :=
  match b with bind_sub _ => 0 | bind_qua _ => 1 | bind_typ _ => 2 end.

Definition kind_inclusion (E F : env) :=
  forall x b, binds x b E ->
    exists c, binds x c F /\ binding_kind b = binding_kind c.

Lemma kinds_includes : forall E F, includes_env E F -> kind_inclusion E F.
Proof. unfold includes_env, kind_inclusion; eauto. Qed.

Lemma kinds_push : forall E F x b c,
  kind_inclusion E F -> binding_kind b = binding_kind c ->
  kind_inclusion (x ~ b ++ E) (x ~ c ++ F).
Proof.
  unfold kind_inclusion. intros E F x b c I K y d H.
  split_binds H.
  - exists c; eauto using binds_app_2.
  - destruct (I _ _ H) as [a [Ha Ka]]. exists a; auto using binds_app_3.
Qed.

Lemma wf_qua_kinds : forall E Q, wf_qua E Q ->
  forall F, kind_inclusion E F -> wf_qua F Q.
Proof.
  induction 1; intros; eauto.
  match goal with I : kind_inclusion _ _, H : binds _ _ _ |- _ =>
    destruct (I _ _ H) as [[?|?|?] [? K]]; inversion K; eauto
  end.
Qed.

Lemma wf_types_kinds :
  (forall E T, wf_typ E T -> forall F, kind_inclusion E F -> wf_typ F T) /\
  (forall E T, wf_qtyp E T -> forall F, kind_inclusion E F -> wf_qtyp F T).
Proof.
  apply wf_types_mut; intros; eauto using kinds_push, wf_qua_kinds.
  match goal with I : kind_inclusion _ _, H : binds _ _ _ |- _ =>
    destruct (I _ _ H) as [[?|?|?] [? K]]; inversion K; eauto
  end.
Qed.

Definition wf_typ_kinds := proj1 wf_types_kinds.
Definition wf_qtyp_kinds := proj2 wf_types_kinds.

Lemma kinds_bound_sub : forall E X S T,
  kind_inclusion (X ~ bind_sub S ++ E) (X ~ bind_sub T ++ E).
Proof. intros; apply kinds_push; try reflexivity; apply kinds_includes; red; auto. Qed.

Lemma kinds_bound_qua : forall E X S T,
  kind_inclusion (X ~ bind_qua S ++ E) (X ~ bind_qua T ++ E).
Proof. intros; apply kinds_push; try reflexivity; apply kinds_includes; red; auto. Qed.

Local Ltac add_qua_regular :=
  match goal with H : subqual _ _ _ |- _ =>
    let W := fresh "W" in pose proof (subqual_regular _ _ _ H) as W;
    destruct W as [? [? ?]]
  end.

Lemma sub_types_regular :
  (forall E S T, sub E S T -> wf_typ E S /\ wf_typ E T) /\
  (forall E S T, subqtype E S T -> wf_qtyp E S /\ wf_qtyp E T).
Proof.
  apply sub_types_mut; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try add_qua_regular; split; eauto.
  - eapply wf_typ_all with (L := L); eauto.
    intros X FX. destruct (H0 X FX) as [W _].
    eauto using wf_qtyp_kinds, kinds_bound_sub.
  - eapply wf_typ_all with (L := L); eauto. intros X FX. apply (H0 X FX).
  - eapply wf_typ_qall with (L := L); eauto.
    intros X FX. destruct (H X FX) as [W _].
    eauto using wf_qtyp_kinds, kinds_bound_qua.
  - eapply wf_typ_qall with (L := L); eauto. intros X FX. apply (H X FX).
Qed.

Definition sub_regular := proj1 sub_types_regular.
Definition subqtype_regular := proj2 sub_types_regular.
Definition sub_env_local := proj1 sub_types_env.
Definition subqtype_env_local := proj2 sub_types_env.
Definition typ_locally_closed := proj1 types_locally_closed.
Definition qtyp_locally_closed := proj2 types_locally_closed.

Local Hint Resolve qua_locally_closed typ_locally_closed qtyp_locally_closed
  typing_env_local sub_env_local subqtype_env_local : core.

Lemma typing_expr_local : forall E e T, typing E e T -> expr e.
Proof.
  induction 1; eauto 6;
    try solve [add_qua_regular; eauto 5];
    try solve [
      match goal with H : sub _ _ _ |- _ =>
        destruct (sub_regular _ _ _ H); eauto
      end ];
    match goal with H : forall x : atom, x `notin` ?L -> typing _ _ _ |- _ =>
      let y := fresh "y" in let Fy := fresh "Fy" in
      destruct (atom_fresh L) as [y Fy];
      pose proof (typing_env_local _ _ _ (H y Fy)) as W;
      inversion W; eauto
    end.
Qed.

Lemma type_reflexivity :
  (forall E T, wf_typ E T -> wf_env E -> sub E T T) /\
  (forall E T, wf_qtyp E T -> wf_env E -> subqtype E T T).
Proof.
  apply wf_types_mut; intros;
    eauto using sub_top, sub_refl_tvar, sub_arrow, sub_sum, sub_pair,
      sub_qtyp_qtyp, qua_reflexivity.
  - apply sub_all with (L := L `union` dom E); eauto.
  - apply sub_qall with (L := L `union` dom E); auto using qua_reflexivity.
Qed.

Definition typ_reflexivity := proj1 type_reflexivity.
Lemma subqual_weaken_local : forall E Q R, subqual E Q R ->
  forall F, includes_env E F -> wf_env F -> subqual F Q R.
Proof.
  induction 1; intros;
    eauto using subqual_top, subqual_bot, subqual_eval_elim, subqual_eval_intro,
    subqual_lift_elem, subqual_refl_qvar, subqual_trans_qvar, subqual_join_inl,
    subqual_join_inr, subqual_join_elim, subqual_meet_eliml, subqual_meet_elimr,
    subqual_meet_intro.
Qed.

Local Ltac push_wf :=
  match goal with
  | W : wf_env ?F, I : includes_env ?E ?F,
    V : wf_env (?x ~ ?b ++ ?E) |- wf_env (?x ~ ?b ++ ?F) =>
      inversion V; subst; constructor; eauto; solve_notin
  end.

Lemma sub_types_weaken :
  (forall E S T, sub E S T -> forall F, includes_env E F -> wf_env F -> sub F S T) /\
  (forall E S T, subqtype E S T ->
     forall F, includes_env E F -> wf_env F -> subqtype F S T).
Proof.
  apply sub_types_mut; intros;
    eauto using sub_top, sub_refl_tvar, sub_trans_tvar, sub_arrow,
    sub_sum, sub_pair, sub_qtyp_qtyp, subqual_weaken_local.
  - apply sub_all with (L := L `union` dom F); eauto.
    intros X FX. assert (X `notin` L) by solve_notin.
    apply H0; eauto using includes_push.
    pose proof (subqtype_env_local _ _ _ (s0 X H3)) as W; push_wf.
  - apply sub_qall with (L := L `union` dom F); eauto using subqual_weaken_local.
    intros X FX. assert (X `notin` L) by solve_notin.
    apply H; eauto using includes_push.
    pose proof (subqtype_env_local _ _ _ (s0 X H2)) as W; push_wf.
Qed.

Definition sub_weaken_local := proj1 sub_types_weaken.
Definition subqtype_weaken_local := proj2 sub_types_weaken.

Local Hint Resolve sub_weaken_local subqtype_weaken_local subqual_weaken_local : core.

Lemma includes_tail : forall (E G : env), includes_env E (G ++ E).
Proof. unfold includes_env; auto using binds_app_3. Qed.

Lemma typing_weaken_local : forall E e T, typing E e T ->
  forall F, includes_env E F -> wf_env F -> typing F e T.
Proof.
  induction 1; intros F I W; eauto 6 using typing_var, typing_app, typing_tapp, typing_qapp,
    typing_sub, typing_inl, typing_inr, typing_pair, typing_first, typing_second,
    typing_upqual, typing_check.
  all: let M := constr:(L `union` dom F) in
    first [eapply typing_abs with (L := M) | eapply typing_tabs with (L := M) |
      eapply typing_qabs with (L := M) | eapply typing_let with (L := M) |
      eapply typing_case with (L := M)]; eauto.
  all: intros X FX; assert (X `notin` L) by solve_notin.
  all: match goal with IH : forall x : atom, x `notin` ?L ->
          forall F, includes_env _ F -> wf_env F -> typing F _ _ |- _ =>
          eapply (IH X); [solve_notin|apply includes_push; assumption|]
       end.
  all: match goal with H : forall x : atom, x `notin` ?L -> typing _ _ _ |- _ =>
      let K := fresh "K" in assert (K : X `notin` L) by solve_notin;
      pose proof (typing_env_local _ _ _ (H X K)); push_wf
    end.
Qed.

(* A change of bounds provides the variable rules in every larger context. *)
Record entails_bounds (E F : env) : Prop := {
  entails_kinds : kind_inclusion E F;
  entails_sub : forall X U, binds X (bind_sub U) E ->
    forall G T, includes_env F G -> wf_env G ->
    sub G U T -> sub G (typ_fvar X) T;
  entails_qua : forall X U, binds X (bind_qua U) E ->
    forall G Q, includes_env F G -> wf_env G ->
    subqual G U Q -> subqual G (qua_fvar X) Q
}.

Lemma entails_push : forall E F X b, entails_bounds E F ->
  entails_bounds (X ~ b ++ E) (X ~ b ++ F).
Proof.
  intros E F X b [K ST SQ]; constructor.
  - apply kinds_push; auto.
  - intros y U Hb G T I W H. split_binds Hb.
    + eapply sub_trans_tvar; [apply I; eauto using binds_app_2|exact H].
    + eapply ST; eauto. red; eauto using binds_app_3.
  - intros y U Hb G Q I W H. split_binds Hb.
    + eapply subqual_trans_qvar; [apply I; eauto using binds_app_2|exact H].
    + eapply SQ; eauto. red; eauto using binds_app_3.
Qed.

Lemma subqual_change_bounds : forall E Q R, subqual E Q R ->
  forall F, entails_bounds E F -> wf_env F -> subqual F Q R.
Proof.
  induction 1; intros;
    eauto using subqual_top, subqual_bot, subqual_eval_elim, subqual_eval_intro,
    subqual_lift_elem, subqual_refl_qvar, subqual_join_inl, subqual_join_inr,
    subqual_join_elim, subqual_meet_eliml, subqual_meet_elimr, subqual_meet_intro,
    wf_qua_kinds, entails_kinds.
  eapply entails_qua; eauto. red; auto.
Qed.

Lemma sub_types_change_bounds :
  (forall E S T, sub E S T -> forall F, entails_bounds E F -> wf_env F -> sub F S T) /\
  (forall E S T, subqtype E S T ->
    forall F, entails_bounds E F -> wf_env F -> subqtype F S T).
Proof.
  apply sub_types_mut; intros;
    eauto using sub_top, sub_refl_tvar, sub_arrow, sub_sum, sub_pair, sub_qtyp_qtyp,
    wf_typ_kinds, entails_kinds, subqual_change_bounds.
  - eapply entails_sub; eauto. red; auto.
  - apply sub_all with (L := L `union` dom F); eauto.
    intros X FX. apply H0; eauto using entails_push; try solve_notin.
    apply wf_env_sub; try solve_notin; auto.
    destruct (sub_regular _ _ _ s); eauto using wf_typ_kinds, entails_kinds.
  - apply sub_qall with (L := L `union` dom F); eauto using subqual_change_bounds.
    intros X FX. apply H; eauto using entails_push; try solve_notin.
    apply wf_env_qua; try solve_notin; auto.
    add_qua_regular; eauto using wf_qua_kinds, entails_kinds.
Qed.

Definition subqtype_change_bounds := proj2 sub_types_change_bounds.

Lemma entails_narrow_sub : forall E X P M,
  sub E P M ->
  (forall F A C, sub F A M -> sub F M C -> sub F A C) ->
  entails_bounds (X ~ bind_sub M ++ E) (X ~ bind_sub P ++ E).
Proof.
  intros E X P M H Cut; constructor.
  - apply kinds_bound_sub.
  - intros y U Hb G T I W HUT. split_binds Hb.
    + eapply sub_trans_tvar with (U := P).
      * apply I. eauto using binds_app_2.
      * eapply Cut; [|exact HUT].
        eapply sub_weaken_local; [exact H| |exact W].
        red; eauto using binds_app_3.
    + eapply sub_trans_tvar; [apply I; eauto using binds_app_3|exact HUT].
  - intros y U Hb G Q I W HUQ. split_binds Hb.
    eapply subqual_trans_qvar; [apply I; eauto using binds_app_3|exact HUQ].
Qed.

Lemma entails_narrow_qua : forall E X P M,
  subqual E P M ->
  entails_bounds (X ~ bind_qua M ++ E) (X ~ bind_qua P ++ E).
Proof.
  intros E X P M H; constructor.
  - apply kinds_bound_qua.
  - intros y U Hb G T I W HUT. split_binds Hb.
    eapply sub_trans_tvar; [apply I; eauto using binds_app_3|exact HUT].
  - intros y U Hb G Q I W HUQ. split_binds Hb.
    + eapply subqual_trans_qvar with (R := P).
      * apply I. eauto using binds_app_2.
      * eapply qua_transitivity; [|exact HUQ].
        eapply subqual_weaken_local; [exact H| |exact W].
        red; eauto using binds_app_3.
    + eapply subqual_trans_qvar; [apply I; eauto using binds_app_3|exact HUQ].
Qed.

Fixpoint typ_size (T : typ) : nat :=
  match T with
  | typ_top | typ_bvar _ | typ_fvar _ => 1
  | typ_arrow A C | typ_sum A C | typ_pair A C => S (qtyp_size A + qtyp_size C)
  | typ_all A C => S (typ_size A + qtyp_size C)
  | typ_qall _ C | typ_ref C => S (qtyp_size C)
  end
with qtyp_size (T : qtyp) : nat :=
  match T with qtyp_qtyp _ A => S (typ_size A) end.

Scheme typ_mut := Induction for typ Sort Prop
with qtyp_mut := Induction for qtyp Sort Prop.
Combined Scheme syntax_types_mut from typ_mut, qtyp_mut.

Lemma type_size_open :
  (forall T k (X : atom),
    typ_size (open_tt_rec k X T) = typ_size T /\
    typ_size (open_qt_rec k X T) = typ_size T) /\
  (forall T k (X : atom),
    qtyp_size (open_tqt_rec k X T) = qtyp_size T /\
    qtyp_size (open_qqt_rec k X T) = qtyp_size T).
Proof.
  apply syntax_types_mut; intros; simpl;
    try (destruct (k == n); split; reflexivity);
    repeat match goal with H : forall _ _, _ |- _ =>
      first [progress rewrite (proj1 (H k X)) | progress rewrite (proj2 (H k X))
        | progress rewrite (proj1 (H (S k) X)) | progress rewrite (proj2 (H (S k) X))]
    end; auto.
Qed.

Lemma size_open_tqt : forall T (X : atom), qtyp_size (open_tqt T X) = qtyp_size T.
Proof. intros; apply (proj1 (proj2 type_size_open T 0 X)). Qed.
Lemma size_open_qqt : forall T (X : atom), qtyp_size (open_qqt T X) = qtyp_size T.
Proof. intros; apply (proj2 (proj2 type_size_open T 0 X)). Qed.

Lemma type_transitivity_size : forall n,
  (forall E A M C, typ_size M = n -> sub E A M -> sub E M C -> sub E A C) /\
  (forall E A M C, qtyp_size M = n -> subqtype E A M ->
    subqtype E M C -> subqtype E A C).
Proof.
  intro n; induction n as [n IH] using lt_wf_ind.
  assert (CT : forall M, typ_size M < n ->
     forall E A C, sub E A M -> sub E M C -> sub E A C).
  { intros M K; intros E A C; apply (proj1 (IH _ K) E A M C); reflexivity. }
  assert (CQ : forall M, qtyp_size M < n ->
     forall E A C, subqtype E A M -> subqtype E M C -> subqtype E A C).
  { intros M K; intros E A C; apply (proj2 (IH _ K) E A M C); reflexivity. }
  clear IH. split.
  - intros E A M C Hsize H; revert C.
    induction H; intros C HC; try solve [eauto using sub_trans_tvar].
    all: try solve [inversion HC; subst; eauto using sub_top].
    all: try solve [
      inversion HC; subst; apply sub_top;
      [eauto|destruct (sub_regular _ _ _ H); eauto] ].
    + inversion HC; subst; try discriminate.
      * apply sub_top; auto. destruct (subqtype_regular _ _ _ H), (subqtype_regular _ _ _ H0); auto.
      * apply sub_arrow; (eapply CQ; [|eassumption|eassumption]); simpl in *; lia.
    + inversion HC; subst; try discriminate.
      * apply sub_top; auto.
        apply (proj1 (sub_regular _ _ _ (sub_all L E S1 S2 T1 T2 H H0))).
      * apply sub_all with (L := L `union` L0 `union` dom E).
        -- eapply CT; [|eassumption|eassumption]; simpl in *; lia.
        -- intros X FX.
           assert (F1 : X `notin` L) by solve_notin.
           assert (F2 : X `notin` L0) by solve_notin.
           eapply CQ with (M := open_tqt T2 X).
           ++ rewrite size_open_tqt; simpl in *; lia.
           ++ eapply subqtype_change_bounds; [apply H0; exact F1| |].
              ** apply entails_narrow_sub; [eassumption|].
                 apply CT. simpl in *; lia.
              ** eapply subqtype_env_local; eauto.
           ++ eauto.
    + inversion HC; subst; try discriminate.
      * apply sub_top; auto.
        exact (proj1 (sub_regular _ _ _ (sub_qall L E S1 S2 T1 T2 H H0))).
      * apply sub_qall with (L := L `union` L0).
        -- eapply qua_transitivity; eassumption.
        -- intros X FX.
           assert (F1 : X `notin` L) by solve_notin.
           assert (F2 : X `notin` L0) by solve_notin.
           eapply CQ with (M := open_qqt T2 X).
           ++ rewrite size_open_qqt; simpl in *; lia.
           ++ eapply subqtype_change_bounds; [apply H0; exact F1| |].
              ** apply entails_narrow_qua; eassumption.
              ** eapply subqtype_env_local; eauto.
           ++ eauto.
    + inversion HC; subst; try discriminate.
      * apply sub_top; auto. destruct (subqtype_regular _ _ _ H), (subqtype_regular _ _ _ H0); auto.
      * apply sub_sum; (eapply CQ; [|eassumption|eassumption]; simpl in *; lia).
    + inversion HC; subst; try discriminate.
      * apply sub_top; auto. destruct (subqtype_regular _ _ _ H), (subqtype_regular _ _ _ H0); auto.
      * apply sub_pair; (eapply CQ; [|eassumption|eassumption]; simpl in *; lia).
  - intros E A M C Hsize H H2; inversion H; subst; inversion H2; subst.
    apply sub_qtyp_qtyp; [eapply qua_transitivity; eassumption|].
    eapply CT; [|eassumption|eassumption]; simpl in *; lia.
Qed.

Lemma typ_transitivity : forall E A M C, sub E A M -> sub E M C -> sub E A C.
Proof. intros; eapply (proj1 (type_transitivity_size (typ_size M))); eauto. Qed.

(* Closed qualifier subtyping is sound for evaluation in the bounded lattice. *)
Lemma closed_concretize : forall Q, wf_qua empty Q ->
  exists b, concretize Q = Some b.
Proof.
  intros Q H; remember empty as E eqn:HE; induction H; subst; cbn; eauto.
  - inversion H.
  - destruct IHwf_qua1 as [b Hb], IHwf_qua2 as [c Hc]; try rewrite Hb, Hc; eauto.
  - destruct IHwf_qua1 as [b Hb], IHwf_qua2 as [c Hc]; try rewrite Hb, Hc; eauto.
Qed.

Lemma lattice_join_left : forall a b : B, a ≤ a ⊔ b.
Proof.
  intros; apply meet_consistent. symmetry; apply meet_absorptive.
Qed.
Lemma lattice_join_right : forall a b : B, b ≤ a ⊔ b.
Proof. intros; rewrite join_commutative; apply lattice_join_left. Qed.
Lemma lattice_meet_left : forall a b : B, a ⊓ b ≤ a.
Proof.
  intros; apply join_consistent. rewrite join_commutative, join_absorptive; reflexivity.
Qed.
Lemma lattice_meet_right : forall a b : B, a ⊓ b ≤ b.
Proof. intros; rewrite meet_commutative; apply lattice_meet_left. Qed.

Lemma closed_qual_order : forall E Q R, subqual E Q R -> E = empty ->
  forall q r, concretize Q = Some q -> concretize R = Some r -> q ≤ r.
Proof.
  induction 1; intros Eq q r Hq Hr; subst E; cbn in *;
    try discriminate; try solve [inversion Hq; inversion Hr; subst; assumption].
  - inversion Hr; subst; apply lattice_upper.
  - inversion Hq; subst; apply lattice_lower.
  - eapply transitive; [eapply IHsubqual1|eapply IHsubqual2]; eauto.
  - eapply transitive; [eapply IHsubqual2|eapply IHsubqual1]; eauto.
  - destruct (concretize R1) as [b1|], (concretize R2) as [b2|]; try discriminate.
    inversion Hr; subst. eapply transitive; [eapply IHsubqual; eauto|apply lattice_join_left].
  - destruct (concretize R1) as [b1|], (concretize R2) as [b2|]; try discriminate.
    inversion Hr; subst. eapply transitive; [eapply IHsubqual; eauto|apply lattice_join_right].
  - destruct (concretize R1) as [b1|], (concretize R2) as [b2|]; try discriminate.
    inversion Hq; subst. apply join_is_lub; split; eauto.
  - destruct (concretize R1) as [b1|], (concretize R2) as [b2|]; try discriminate.
    inversion Hq; subst. eapply transitive; [apply lattice_meet_left|eapply IHsubqual; eauto].
  - destruct (concretize R1) as [b1|], (concretize R2) as [b2|]; try discriminate.
    inversion Hq; subst. eapply transitive; [apply lattice_meet_right|eapply IHsubqual; eauto].
  - destruct (concretize R1) as [b1|], (concretize R2) as [b2|]; try discriminate.
    inversion Hr; subst. apply meet_is_glb; split; eauto.
Qed.

Definition value_shape (e : exp) (T : typ) : Prop :=
  match T with
  | typ_top => True
  | typ_arrow _ _ => match e with exp_abs _ _ _ => True | _ => False end
  | typ_all _ _ => match e with exp_tabs _ _ _ => True | _ => False end
  | typ_qall _ _ => match e with exp_qabs _ _ _ => True | _ => False end
  | typ_sum _ _ => match e with exp_inl _ _ | exp_inr _ _ => True | _ => False end
  | typ_pair _ _ => match e with exp_pair _ _ _ => True | _ => False end
  | _ => False
  end.

Lemma sub_value_shape : forall E S T e, sub E S T -> value_shape e S -> value_shape e T.
Proof. destruct 1; intros; cbn in *; tauto. Qed.

Lemma qtype_value_shape : forall E e U, typing E e U -> value e ->
  match U with qtyp_qtyp _ T => value_shape e T end.
Proof.
  induction 1; intros Hv; try solve [inversion Hv]; try exact I.
  inversion H0; subst. eauto using sub_value_shape.
Qed.

Definition annotation (e : exp) : option qua :=
  match e with
  | exp_abs Q _ _ | exp_tabs Q _ _ | exp_qabs Q _ _
  | exp_inl Q _ | exp_inr Q _ | exp_pair Q _ _ => Some Q
  | _ => None
  end.

Lemma value_initial_qualifier : forall E e U, typing E e U -> value e ->
  exists P, annotation e = Some P /\
    match U with qtyp_qtyp Q _ => subqual E P Q end.
Proof.
  induction 1; intros Hv; try solve [inversion Hv];
    try solve [eexists; split; [reflexivity|apply qua_reflexivity; eauto 6
      using typing_abs, typing_tabs, typing_qabs, typing_inl, typing_inr, typing_pair]].
  destruct (IHtyping Hv) as [P [Ann SP]].
  inversion H0; subst; exists P; split; eauto using qua_transitivity.
Qed.

Lemma value_expr_local : forall e, value e -> expr e.
Proof. induction 1; auto. Qed.

Lemma qualifier_value_steps : forall e Q T P, value e ->
  typing empty e (qtyp_qtyp Q T) -> subqual empty Q P ->
  (exists e', red (exp_upqual P e) e') /\ red (exp_check P e) e.
Proof.
  intros e Q T P V Ty H.
  destruct (value_initial_qualifier _ _ _ Ty V) as [A [Ann SA]].
  pose proof (qua_transitivity _ _ _ _ SA H) as S.
  destruct (subqual_regular _ _ _ S) as [_ [WA WP]].
  destruct (closed_concretize _ WA) as [a Ha], (closed_concretize _ WP) as [p Hp].
  pose proof (closed_qual_order _ _ _ S eq_refl _ _ Ha Hp) as Le.
  pose proof (value_expr_local _ V) as Expr.
  destruct V; cbn in Ann; inversion Ann; subst; split;
    try (eexists; solve [eauto using red_upqual_abs, red_upqual_tabs, red_upqual_qabs,
      red_upqual_inl, red_upqual_inr, red_upqual_pair]);
    eauto using red_check_abs, red_check_tabs, red_check_qabs,
      red_check_inl, red_check_inr, red_check_pair.
Qed.

Local Hint Resolve typing_expr_local : core.

(* A single traversal acts on free atoms and bound indices in all three
   syntactic classes. The depth increases at the binders used by opening. *)
Record syntax_action : Type := {
  free_qua : atom -> qua;
  free_typ : atom -> typ;
  free_exp : atom -> exp;
  bound_qua : nat -> nat -> qua;
  bound_typ : nat -> nat -> typ;
  bound_exp : nat -> nat -> exp
}.

Fixpoint run_qua (r : syntax_action) (k : nat) (s : qua) {struct s} : qua :=
  match s with
  | qua_base b => qua_base b
  | qua_bvar i => bound_qua r k i
  | qua_fvar X => free_qua r X
  | qua_meet A C => qua_meet (run_qua r k A) (run_qua r k C)
  | qua_join A C => qua_join (run_qua r k A) (run_qua r k C)
  end.

Fixpoint run_typ (r : syntax_action) (k : nat) (s : typ) {struct s} : typ :=
  match s with
  | typ_top => typ_top
  | typ_bvar i => bound_typ r k i
  | typ_fvar X => free_typ r X
  | typ_arrow A C => typ_arrow (run_qtyp r k A) (run_qtyp r (S k) C)
  | typ_all A C => typ_all (run_typ r k A) (run_qtyp r (S k) C)
  | typ_qall A C => typ_qall (run_qua r k A) (run_qtyp r (S k) C)
  | typ_sum A C => typ_sum (run_qtyp r k A) (run_qtyp r k C)
  | typ_pair A C => typ_pair (run_qtyp r k A) (run_qtyp r k C)
  | typ_ref T => typ_ref (run_qtyp r k T)
  end
with run_qtyp (r : syntax_action) (k : nat) (s : qtyp) {struct s} : qtyp :=
  match s with
  | qtyp_qtyp Q T => qtyp_qtyp (run_qua r k Q) (run_typ r k T)
  end.

Fixpoint run_exp (r : syntax_action) (k : nat) (s : exp) {struct s} : exp :=
  match s with
  | exp_bvar i => bound_exp r k i
  | exp_fvar x => free_exp r x
  | exp_abs P V e => exp_abs (run_qua r k P) (run_qtyp r k V) (run_exp r (S k) e)
  | exp_app e f => exp_app (run_exp r k e) (run_exp r k f)
  | exp_tabs P V e => exp_tabs (run_qua r k P) (run_typ r k V) (run_exp r (S k) e)
  | exp_tapp e V => exp_tapp (run_exp r k e) (run_typ r k V)
  | exp_qabs P Q e => exp_qabs (run_qua r k P) (run_qua r k Q) (run_exp r (S k) e)
  | exp_qapp e Q => exp_qapp (run_exp r k e) (run_qua r k Q)
  | exp_let e f => exp_let (run_exp r k e) (run_exp r (S k) f)
  | exp_inl P e => exp_inl (run_qua r k P) (run_exp r k e)
  | exp_inr P e => exp_inr (run_qua r k P) (run_exp r k e)
  | exp_case e f g => exp_case (run_exp r k e) (run_exp r (S k) f) (run_exp r (S k) g)
  | exp_pair P e f => exp_pair (run_qua r k P) (run_exp r k e) (run_exp r k f)
  | exp_first e => exp_first (run_exp r k e)
  | exp_second e => exp_second (run_exp r k e)
  | exp_ref P e => exp_ref (run_qua r k P) (run_exp r k e)
  | exp_ref_label P l => exp_ref_label (run_qua r k P) l
  | exp_deref e => exp_deref (run_exp r k e)
  | exp_set_ref e f => exp_set_ref (run_exp r k e) (run_exp r k f)
  | exp_upqual P e => exp_upqual (run_qua r k P) (run_exp r k e)
  | exp_check P e => exp_check (run_qua r k P) (run_exp r k e)
  end.

Fixpoint ok_qua (F : atom -> Prop) (D : nat -> nat -> Prop) (k : nat) (s : qua) {struct s} : Prop :=
  match s with
  | qua_base b => True
  | qua_bvar i => D k i
  | qua_fvar X => F X
  | qua_meet A C => ok_qua F D k A /\ ok_qua F D k C
  | qua_join A C => ok_qua F D k A /\ ok_qua F D k C
  end.

Fixpoint ok_typ (F : atom -> Prop) (D : nat -> nat -> Prop) (k : nat) (s : typ) {struct s} : Prop :=
  match s with
  | typ_top => True
  | typ_bvar i => D k i
  | typ_fvar X => F X
  | typ_arrow A C => ok_qtyp F D k A /\ ok_qtyp F D (S k) C
  | typ_all A C => ok_typ F D k A /\ ok_qtyp F D (S k) C
  | typ_qall A C => ok_qua F D k A /\ ok_qtyp F D (S k) C
  | typ_sum A C => ok_qtyp F D k A /\ ok_qtyp F D k C
  | typ_pair A C => ok_qtyp F D k A /\ ok_qtyp F D k C
  | typ_ref T => ok_qtyp F D k T
  end
with ok_qtyp (F : atom -> Prop) (D : nat -> nat -> Prop) (k : nat) (s : qtyp) {struct s} : Prop :=
  match s with
  | qtyp_qtyp Q T => ok_qua F D k Q /\ ok_typ F D k T
  end.

Fixpoint ok_exp (F : atom -> Prop) (D : nat -> nat -> Prop) (k : nat) (s : exp) {struct s} : Prop :=
  match s with
  | exp_bvar i => D k i
  | exp_fvar x => F x
  | exp_abs P V e => ok_qua F D k P /\ ok_qtyp F D k V /\ ok_exp F D (S k) e
  | exp_app e f => ok_exp F D k e /\ ok_exp F D k f
  | exp_tabs P V e => ok_qua F D k P /\ ok_typ F D k V /\ ok_exp F D (S k) e
  | exp_tapp e V => ok_exp F D k e /\ ok_typ F D k V
  | exp_qabs P Q e => ok_qua F D k P /\ ok_qua F D k Q /\ ok_exp F D (S k) e
  | exp_qapp e Q => ok_exp F D k e /\ ok_qua F D k Q
  | exp_let e f => ok_exp F D k e /\ ok_exp F D (S k) f
  | exp_inl P e => ok_qua F D k P /\ ok_exp F D k e
  | exp_inr P e => ok_qua F D k P /\ ok_exp F D k e
  | exp_case e f g => ok_exp F D k e /\ ok_exp F D (S k) f /\ ok_exp F D (S k) g
  | exp_pair P e f => ok_qua F D k P /\ ok_exp F D k e /\ ok_exp F D k f
  | exp_first e => ok_exp F D k e
  | exp_second e => ok_exp F D k e
  | exp_ref P e => ok_qua F D k P /\ ok_exp F D k e
  | exp_ref_label P l => ok_qua F D k P
  | exp_deref e => ok_exp F D k e
  | exp_set_ref e f => ok_exp F D k e /\ ok_exp F D k f
  | exp_upqual P e => ok_qua F D k P /\ ok_exp F D k e
  | exp_check P e => ok_qua F D k P /\ ok_exp F D k e
  end.

Definition choose_index {A : Type} (var : nat -> A) (u : option A) k j :=
  match u with
  | Some a => if k == j then a else var j
  | None => var j
  end.

Definition opening (Q : option qua) (T : option typ) (e : option exp) : syntax_action :=
  {| free_qua := qua_fvar; free_typ := typ_fvar; free_exp := exp_fvar;
     bound_qua := choose_index qua_bvar Q;
     bound_typ := choose_index typ_bvar T;
     bound_exp := choose_index exp_bvar e |}.

Definition substitution (q : atom -> qua) (t : atom -> typ) (e : atom -> exp) :
  syntax_action :=
  {| free_qua := q; free_typ := t; free_exp := e;
     bound_qua := fun _ => qua_bvar; bound_typ := fun _ => typ_bvar;
     bound_exp := fun _ => exp_bvar |}.

Lemma run_qua_open : forall Q k R,
  run_qua (opening (Some R) None None) k Q = open_qq_rec k R Q /\
  (forall T e, run_qua (opening None T e) k Q = Q).
Proof.
  induction Q; intros; cbn; split; intros; f_equal; try reflexivity;
    try match goal with H : forall _ _, _ |- _ =>
      first [exact (proj1 (H k R)) | exact (proj2 (H k R) T e)]
    end.
Qed.

Lemma run_types_open :
  (forall S k R U e,
    run_typ (opening (Some R) None None) k S = open_qt_rec k R S /\
    run_typ (opening None (Some U) None) k S = open_tt_rec k U S /\
    run_typ (opening None None e) k S = S) /\
  (forall S k R U e,
    run_qtyp (opening (Some R) None None) k S = open_qqt_rec k R S /\
    run_qtyp (opening None (Some U) None) k S = open_tqt_rec k U S /\
    run_qtyp (opening None None e) k S = S).
Proof.
  apply syntax_types_mut; intros; cbn; repeat split; f_equal; try reflexivity;
    try solve [apply (proj1 (run_qua_open _ _ _))];
    try solve [apply (proj2 (run_qua_open _ _ R))];
    match goal with IH : forall _ _ _ _, _ |- _ =>
      first [solve [pose proof (IH k R U e); tauto] |
        solve [pose proof (IH (S k) R U e); tauto]]
    end.
Qed.

Lemma run_exp_open : forall s k R U e,
  run_exp (opening (Some R) None None) k s = open_qe_rec k R s /\
  run_exp (opening None (Some U) None) k s = open_te_rec k U s /\
  run_exp (opening None None (Some e)) k s = open_ee_rec k e s.
Proof.
  induction s; intros; cbn; repeat split; f_equal; try reflexivity;
    try solve [apply (proj1 (run_qua_open _ _ _))];
    try solve [apply (proj2 (run_qua_open _ _ R))];
    try solve [
      match goal with |- run_typ _ ?k0 ?s0 = _ =>
        pose proof (proj1 run_types_open s0 k0 R U (Some e)); tauto
      | |- run_qtyp _ ?k0 ?s0 = _ =>
        pose proof (proj2 run_types_open s0 k0 R U (Some e)); tauto
      end ];
    match goal with IH : forall _ _ _ _, _ |- _ =>
      first [solve [pose proof (IH k R U e); tauto] |
        solve [pose proof (IH (S k) R U e); tauto]]
    end.
Qed.

Lemma run_open_qqt : forall T R,
  run_qtyp (opening (Some R) None None) 0 T = open_qqt T R.
Proof. intros; exact (proj1 (proj2 run_types_open T 0 R typ_top None)). Qed.
Lemma run_open_tqt : forall T U,
  run_qtyp (opening None (Some U) None) 0 T = open_tqt T U.
Proof. intros; exact (proj1 (proj2 (proj2 run_types_open T 0 (qua_base top) U None))). Qed.
Lemma run_open_qe : forall e R,
  run_exp (opening (Some R) None None) 0 e = open_qe e R.
Proof. intros; exact (proj1 (run_exp_open e 0 R typ_top (exp_bvar 0))). Qed.
Lemma run_open_te : forall e U,
  run_exp (opening None (Some U) None) 0 e = open_te e U.
Proof. intros; exact (proj1 (proj2 (run_exp_open e 0 (qua_base top) U (exp_bvar 0)))). Qed.
Lemma run_open_ee : forall e f,
  run_exp (opening None None (Some f)) 0 e = open_ee e f.
Proof. intros; exact (proj2 (proj2 (run_exp_open e 0 (qua_base top) typ_top f))). Qed.

Definition scoped_qua := ok_qua (fun _ => True) (fun k i => i < k).
Definition scoped_typ := ok_typ (fun _ => True) (fun k i => i < k).
Definition scoped_qtyp := ok_qtyp (fun _ => True) (fun k i => i < k).
Definition scoped_exp := ok_exp (fun _ => True) (fun k i => i < k).

Definition fixes_atoms (r : syntax_action) (F : atom -> Prop) :=
  forall x, F x ->
    free_qua r x = qua_fvar x /\ free_typ r x = typ_fvar x /\ free_exp r x = exp_fvar x.
Definition fixes_indices (r : syntax_action) (D : nat -> nat -> Prop) :=
  forall k i, D k i ->
    bound_qua r k i = qua_bvar i /\ bound_typ r k i = typ_bvar i /\
    bound_exp r k i = exp_bvar i.

Local Ltac prove_run_identity :=
  intros; cbn in *; try reflexivity;
  try solve [
    match goal with H : fixes_atoms _ ?F, V : ?F ?x |- _ =>
      pose proof (H x V); tauto
    | H : fixes_indices _ ?D, V : ?D ?k ?i |- _ =>
      pose proof (H k i V); tauto
    end ];
  f_equal; intuition eauto.

Lemma run_qua_identity : forall s r F D k,
  fixes_atoms r F -> fixes_indices r D -> ok_qua F D k s -> run_qua r k s = s.
Proof. induction s; prove_run_identity. Qed.

Lemma run_types_identity :
  (forall s r F D k, fixes_atoms r F -> fixes_indices r D ->
    ok_typ F D k s -> run_typ r k s = s) /\
  (forall s r F D k, fixes_atoms r F -> fixes_indices r D ->
    ok_qtyp F D k s -> run_qtyp r k s = s).
Proof. apply syntax_types_mut; prove_run_identity; eauto using run_qua_identity. Qed.

Definition run_typ_identity := proj1 run_types_identity.
Definition run_qtyp_identity := proj2 run_types_identity.

Lemma run_exp_identity : forall s r F D k,
  fixes_atoms r F -> fixes_indices r D -> ok_exp F D k s -> run_exp r k s = s.
Proof.
  induction s; prove_run_identity;
    eauto using run_qua_identity, run_typ_identity, run_qtyp_identity.
Qed.

Local Ltac prove_scope_mono :=
  unfold scoped_qua, scoped_typ, scoped_qtyp, scoped_exp in *;
  intros; cbn in *; intuition eauto using le_n_S; try lia.

Lemma scoped_qua_mono : forall s k l, k <= l -> scoped_qua k s -> scoped_qua l s.
Proof. induction s; prove_scope_mono. Qed.
Lemma scoped_types_mono :
  (forall s k l, k <= l -> scoped_typ k s -> scoped_typ l s) /\
  (forall s k l, k <= l -> scoped_qtyp k s -> scoped_qtyp l s).
Proof. apply syntax_types_mut; prove_scope_mono; eapply scoped_qua_mono; eassumption. Qed.
Definition scoped_typ_mono := proj1 scoped_types_mono.
Definition scoped_qtyp_mono := proj2 scoped_types_mono.
Lemma scoped_exp_mono : forall s k l, k <= l -> scoped_exp k s -> scoped_exp l s.
Proof.
  induction s; prove_scope_mono;
    first [eapply scoped_qua_mono | eapply scoped_typ_mono | eapply scoped_qtyp_mono]; eassumption.
Qed.

Local Ltac prove_scope_back :=
  unfold scoped_qua, scoped_typ, scoped_qtyp, scoped_exp in *;
  intros; cbn in *; intuition eauto;
  try solve [
    match goal with
    | F : fixes_indices ?r lt, W : context [bound_qua ?r ?k ?i] |- _ =>
        destruct (le_lt_dec i k) as [Hi|Hi]; [lia|];
        rewrite (proj1 (F k i Hi)) in W; cbn in W; lia
    | F : fixes_indices ?r lt, W : context [bound_typ ?r ?k ?i] |- _ =>
        destruct (le_lt_dec i k) as [Hi|Hi]; [lia|];
        rewrite (proj1 (proj2 (F k i Hi))) in W; cbn in W; lia
    | F : fixes_indices ?r lt, W : context [bound_exp ?r ?k ?i] |- _ =>
        destruct (le_lt_dec i k) as [Hi|Hi]; [lia|];
        rewrite (proj2 (proj2 (F k i Hi))) in W; cbn in W; lia
    end ].

Lemma scoped_qua_back : forall s r k, fixes_indices r lt ->
  scoped_qua k (run_qua r k s) -> scoped_qua (S k) s.
Proof. induction s; prove_scope_back. Qed.
Lemma scoped_types_back :
  (forall s r k, fixes_indices r lt ->
    scoped_typ k (run_typ r k s) -> scoped_typ (S k) s) /\
  (forall s r k, fixes_indices r lt ->
    scoped_qtyp k (run_qtyp r k s) -> scoped_qtyp (S k) s).
Proof. apply syntax_types_mut; prove_scope_back; eapply scoped_qua_back; eassumption. Qed.
Definition scoped_typ_back := proj1 scoped_types_back.
Definition scoped_qtyp_back := proj2 scoped_types_back.
Lemma scoped_exp_back : forall s r k, fixes_indices r lt ->
  scoped_exp k (run_exp r k s) -> scoped_exp (S k) s.
Proof.
  induction s; prove_scope_back;
    first [eapply scoped_qua_back | eapply scoped_typ_back | eapply scoped_qtyp_back]; eassumption.
Qed.

Lemma opening_fixes_above : forall Q T e, fixes_indices (opening Q T e) lt.
Proof.
  unfold fixes_indices. intros Q T e k i H. destruct Q, T, e;
    cbn; destruct (k == i); subst; try lia; auto.
Qed.
Lemma opening_fixes_below : forall Q T e,
  fixes_indices (opening Q T e) (fun k i => i < k).
Proof.
  unfold fixes_indices. intros Q T e k i H. destruct Q, T, e;
    cbn; destruct (k == i); subst; try lia; auto.
Qed.
Lemma opening_fixes_atoms : forall Q T e F, fixes_atoms (opening Q T e) F.
Proof. red; cbn; auto. Qed.

Scheme type_mut := Induction for type Sort Prop
with qtype_mut := Induction for qtype Sort Prop.
Combined Scheme lc_types_mut from type_mut, qtype_mut.

Lemma qual_scoped : forall Q, qual Q -> scoped_qua 0 Q.
Proof. induction 1; cbn in *; auto. Qed.

Lemma lc_types_scoped :
  (forall T, type T -> scoped_typ 0 T) /\
  (forall T, qtype T -> scoped_qtyp 0 T).
Proof.
  apply lc_types_mut; intros; cbn in *;
    intuition eauto using qual_scoped, scoped_qtyp_mono, Nat.le_0_l.
  all: try solve [eapply scoped_qtyp_mono with (k := 0); [lia|assumption]].
  all: try solve [apply qual_scoped; assumption].
  - destruct (atom_fresh L) as [X FX].
    eapply scoped_qtyp_back with (r := opening None (Some (typ_fvar X)) None);
      [apply opening_fixes_above|rewrite run_open_tqt; eauto].
  - destruct (atom_fresh L) as [X FX].
    eapply scoped_qtyp_back with (r := opening (Some (qua_fvar X)) None None);
      [apply opening_fixes_above|rewrite run_open_qqt; eauto].
Qed.

Definition type_scoped := proj1 lc_types_scoped.
Definition qtype_scoped := proj2 lc_types_scoped.

Lemma expr_scoped : forall e, expr e -> scoped_exp 0 e.
Proof.
  induction 1; cbn in *; intuition eauto using qual_scoped, type_scoped, qtype_scoped.
  all: try solve [apply qual_scoped; assumption |
                  apply type_scoped; assumption | apply qtype_scoped; assumption].
  all: destruct (atom_fresh L) as [X FX].
  all: first [
    solve [eapply scoped_exp_back with (r := opening None None (Some (exp_fvar X)));
      [apply opening_fixes_above|rewrite run_open_ee; eauto]] |
    solve [eapply scoped_exp_back with (r := opening None (Some (typ_fvar X)) None);
      [apply opening_fixes_above|rewrite run_open_te; eauto]] |
    solve [eapply scoped_exp_back with (r := opening (Some (qua_fvar X)) None None);
      [apply opening_fixes_above|rewrite run_open_qe; eauto]] ].
Qed.
Fixpoint fv_qua (s : qua) : atoms :=
  match s with
  | qua_base b => {}
  | qua_bvar i => {}
  | qua_fvar X => singleton X
  | qua_meet A C => (fv_qua A) `union` (fv_qua C)
  | qua_join A C => (fv_qua A) `union` (fv_qua C)
  end.

Fixpoint fv_typ (s : typ) : atoms :=
  match s with
  | typ_top => {}
  | typ_bvar i => {}
  | typ_fvar X => singleton X
  | typ_arrow A C => (fv_qtyp A) `union` (fv_qtyp C)
  | typ_all A C => (fv_typ A) `union` (fv_qtyp C)
  | typ_qall A C => (fv_qua A) `union` (fv_qtyp C)
  | typ_sum A C => (fv_qtyp A) `union` (fv_qtyp C)
  | typ_pair A C => (fv_qtyp A) `union` (fv_qtyp C)
  | typ_ref T => (fv_qtyp T)
  end
with fv_qtyp (s : qtyp) : atoms :=
  match s with
  | qtyp_qtyp Q T => (fv_qua Q) `union` (fv_typ T)
  end.

Fixpoint fv_exp (s : exp) : atoms :=
  match s with
  | exp_bvar i => {}
  | exp_fvar x => singleton x
  | exp_abs P V e => (fv_qua P) `union` (fv_qtyp V) `union` (fv_exp e)
  | exp_app e f => (fv_exp e) `union` (fv_exp f)
  | exp_tabs P V e => (fv_qua P) `union` (fv_typ V) `union` (fv_exp e)
  | exp_tapp e V => (fv_exp e) `union` (fv_typ V)
  | exp_qabs P Q e => (fv_qua P) `union` (fv_qua Q) `union` (fv_exp e)
  | exp_qapp e Q => (fv_exp e) `union` (fv_qua Q)
  | exp_let e f => (fv_exp e) `union` (fv_exp f)
  | exp_inl P e => (fv_qua P) `union` (fv_exp e)
  | exp_inr P e => (fv_qua P) `union` (fv_exp e)
  | exp_case e f g => (fv_exp e) `union` (fv_exp f) `union` (fv_exp g)
  | exp_pair P e f => (fv_qua P) `union` (fv_exp e) `union` (fv_exp f)
  | exp_first e => (fv_exp e)
  | exp_second e => (fv_exp e)
  | exp_ref P e => (fv_qua P) `union` (fv_exp e)
  | exp_ref_label P l => (fv_qua P)
  | exp_deref e => (fv_exp e)
  | exp_set_ref e f => (fv_exp e) `union` (fv_exp f)
  | exp_upqual P e => (fv_qua P) `union` (fv_exp e)
  | exp_check P e => (fv_qua P) `union` (fv_exp e)
  end.

Definition atom_avoids (X y : atom) := y <> X.
Definition any_index (_ _ : nat) := True.
Definition bare_qua X := ok_qua (atom_avoids X) any_index.
Definition bare_typ X := ok_typ (atom_avoids X) any_index.
Definition bare_qtyp X := ok_qtyp (atom_avoids X) any_index.
Definition bare_exp X := ok_exp (atom_avoids X) any_index.

Local Ltac prove_fv_avoids :=
  unfold bare_qua, bare_typ, bare_qtyp, bare_exp in *;
  intros; cbn in *; unfold atom_avoids, any_index;
    repeat split; try solve [auto | solve_notin].

Lemma qua_fv_avoids : forall s X k, X `notin` fv_qua s -> bare_qua X k s.
Proof. induction s; prove_fv_avoids; eauto using notin_union_1, notin_union_2. Qed.
Lemma types_fv_avoids :
  (forall s X k, X `notin` fv_typ s -> bare_typ X k s) /\
  (forall s X k, X `notin` fv_qtyp s -> bare_qtyp X k s).
Proof.
  apply syntax_types_mut; prove_fv_avoids;
    eauto using notin_union_1, notin_union_2;
    eapply qua_fv_avoids; solve_notin.
Qed.
Definition typ_fv_avoids := proj1 types_fv_avoids.
Definition qtyp_fv_avoids := proj2 types_fv_avoids.
Lemma exp_fv_avoids : forall s X k, X `notin` fv_exp s -> bare_exp X k s.
Proof.
  induction s; prove_fv_avoids;
    eauto using notin_union_1, notin_union_2;
    first [eapply qua_fv_avoids | eapply typ_fv_avoids | eapply qtyp_fv_avoids];
    solve_notin.
Qed.

Local Ltac prove_bare_back :=
  unfold bare_qua, bare_typ, bare_qtyp in *;
  intros; cbn in *; intuition eauto; try exact I;
  try solve [
    match goal with
    | H : fixes_atoms ?r (fun _ => True), V : context [free_qua ?r ?x] |- _ =>
        rewrite (proj1 (H x I)) in V; exact V
    | H : fixes_atoms ?r (fun _ => True), V : context [free_typ ?r ?x] |- _ =>
        rewrite (proj1 (proj2 (H x I))) in V; exact V
    end ].

Lemma bare_qua_back : forall s r X k, fixes_atoms r (fun _ => True) ->
  bare_qua X k (run_qua r k s) -> bare_qua X k s.
Proof. induction s; prove_bare_back. Qed.
Lemma bare_types_back :
  (forall s r X k, fixes_atoms r (fun _ => True) ->
    bare_typ X k (run_typ r k s) -> bare_typ X k s) /\
  (forall s r X k, fixes_atoms r (fun _ => True) ->
    bare_qtyp X k (run_qtyp r k s) -> bare_qtyp X k s).
Proof. apply syntax_types_mut; prove_bare_back; eapply bare_qua_back; eassumption. Qed.
Definition bare_qtyp_back := proj2 bare_types_back.

Lemma qua_avoids_binding : forall E Q, wf_qua E Q ->
  forall X k, X `notin` dom E -> bare_qua X k Q.
Proof.
  induction 1; intros; cbn in *; auto.
  unfold atom_avoids. intro; subst. eapply binds_dom_contradiction; eassumption.
Qed.
Local Ltac prove_bare_depth :=
  unfold bare_qua, bare_typ, bare_qtyp in *; intros; cbn in *; intuition eauto.

Lemma bare_qua_depth : forall s X k l, bare_qua X k s -> bare_qua X l s.
Proof. induction s; prove_bare_depth. Qed.
Lemma bare_types_depth :
  (forall s X k l, bare_typ X k s -> bare_typ X l s) /\
  (forall s X k l, bare_qtyp X k s -> bare_qtyp X l s).
Proof. apply syntax_types_mut; prove_bare_depth; eapply bare_qua_depth; eassumption. Qed.
Definition bare_qtyp_depth := proj2 bare_types_depth.

Lemma types_avoid_binding :
  (forall E T, wf_typ E T -> forall X k, X `notin` dom E -> bare_typ X k T) /\
  (forall E T, wf_qtyp E T -> forall X k, X `notin` dom E -> bare_qtyp X k T).
Proof.
  apply wf_types_mut; unfold bare_typ, bare_qtyp in *; intros; cbn in *; intuition eauto;
    try solve [eapply qua_avoids_binding; eassumption].
  - unfold atom_avoids. intro; subst. eapply binds_dom_contradiction; eassumption.
  - destruct (atom_fresh (L `union` singleton X)) as [Y FY].
    apply bare_qtyp_depth with (k := 0).
    eapply bare_qtyp_back with (r := opening None (Some (typ_fvar Y)) None);
      [apply opening_fixes_atoms|rewrite run_open_tqt; apply H0; try solve_notin].
    intro Hin. apply H1. eapply AtomSetImpl.add_3; [|exact Hin]. solve_notin.
  - destruct (atom_fresh (L `union` singleton X)) as [Y FY].
    apply bare_qtyp_depth with (k := 0).
    eapply bare_qtyp_back with (r := opening (Some (qua_fvar Y)) None None);
      [apply opening_fixes_atoms|rewrite run_open_qqt; apply H; try solve_notin].
    intro Hin. eapply AtomSetImpl.add_3 in Hin; [contradiction|solve_notin].
Qed.

Definition typ_avoids_binding := proj1 types_avoid_binding.
Definition qtyp_avoids_binding := proj2 types_avoid_binding.

Record composes (r2 r1 r : syntax_action) : Prop := {
  comp_free_qua : forall k x, run_qua r2 k (free_qua r1 x) = free_qua r x;
  comp_free_typ : forall k x, run_typ r2 k (free_typ r1 x) = free_typ r x;
  comp_free_exp : forall k x, run_exp r2 k (free_exp r1 x) = free_exp r x;
  comp_bound_qua : forall k i, run_qua r2 k (bound_qua r1 k i) = bound_qua r k i;
  comp_bound_typ : forall k i, run_typ r2 k (bound_typ r1 k i) = bound_typ r k i;
  comp_bound_exp : forall k i, run_exp r2 k (bound_exp r1 k i) = bound_exp r k i
}.

Local Ltac prove_composition :=
  intros; cbn; f_equal; auto using comp_free_qua, comp_free_typ, comp_free_exp,
    comp_bound_qua, comp_bound_typ, comp_bound_exp.

Lemma run_qua_compose : forall s r2 r1 r k, composes r2 r1 r ->
  run_qua r2 k (run_qua r1 k s) = run_qua r k s.
Proof. induction s; prove_composition. Qed.

Lemma run_types_compose :
  (forall s r2 r1 r k, composes r2 r1 r ->
    run_typ r2 k (run_typ r1 k s) = run_typ r k s) /\
  (forall s r2 r1 r k, composes r2 r1 r ->
    run_qtyp r2 k (run_qtyp r1 k s) = run_qtyp r k s).
Proof. apply syntax_types_mut; prove_composition; eauto using run_qua_compose. Qed.

Definition run_typ_compose := proj1 run_types_compose.
Definition run_qtyp_compose := proj2 run_types_compose.

Lemma run_exp_compose : forall s r2 r1 r k, composes r2 r1 r ->
  run_exp r2 k (run_exp r1 k s) = run_exp r k s.
Proof.
  induction s; prove_composition;
    eauto using run_qua_compose, run_typ_compose, run_qtyp_compose.
Qed.

Record free_subst : Type := {
  subst_qvar : atom -> qua;
  subst_tvar : atom -> typ;
  subst_evar : atom -> exp
}.
Definition subst_action r := substitution (subst_qvar r) (subst_tvar r) (subst_evar r).

Definition subst_qua r := run_qua (subst_action r) 0.
Definition subst_typ r := run_typ (subst_action r) 0.
Definition subst_qtyp r := run_qtyp (subst_action r) 0.
Definition subst_exp r := run_exp (subst_action r) 0.

Lemma run_qua_depth : forall s r k l, run_qua (subst_action r) k s = run_qua (subst_action r) l s.
Proof. induction s; intros; cbn; f_equal; auto. Qed.
Lemma run_types_depth :
  (forall s r k l, run_typ (subst_action r) k s = run_typ (subst_action r) l s) /\
  (forall s r k l, run_qtyp (subst_action r) k s = run_qtyp (subst_action r) l s).
Proof. apply syntax_types_mut; intros; cbn; f_equal; auto using run_qua_depth. Qed.
Definition run_typ_depth := proj1 run_types_depth.
Definition run_qtyp_depth := proj2 run_types_depth.
Lemma run_exp_depth : forall s r k l, run_exp (subst_action r) k s = run_exp (subst_action r) l s.
Proof.
  induction s; intros; cbn; f_equal;
    auto using run_qua_depth, run_typ_depth, run_qtyp_depth.
Qed.

Record scoped_subst (r : free_subst) : Prop := {
  subst_qua_scoped : forall X, scoped_qua 0 (subst_qvar r X);
  subst_typ_scoped : forall X, scoped_typ 0 (subst_tvar r X);
  subst_exp_scoped : forall X, scoped_exp 0 (subst_evar r X)
}.

Definition mapped_opening r Q T e :=
  opening (option_map (subst_qua r) Q) (option_map (subst_typ r) T) (option_map (subst_exp r) e).

Definition opening_after r Q T e : syntax_action :=
  let o := mapped_opening r Q T e in
  {| free_qua := subst_qvar r; free_typ := subst_tvar r; free_exp := subst_evar r;
     bound_qua := bound_qua o; bound_typ := bound_typ o; bound_exp := bound_exp o |}.

Lemma subst_after_opening : forall r Q T e,
  composes (subst_action r) (opening Q T e) (opening_after r Q T e).
Proof.
  intros; constructor; intros; try reflexivity.
  - destruct Q; cbn; [destruct (k == i)|]; try reflexivity; apply run_qua_depth.
  - destruct T; cbn; [destruct (k == i)|]; try reflexivity; apply run_typ_depth.
  - destruct e; cbn; [destruct (k == i)|]; try reflexivity; apply run_exp_depth.
Qed.

Lemma opening_after_subst : forall r Q T e, scoped_subst r ->
  composes (mapped_opening r Q T e) (subst_action r) (opening_after r Q T e).
Proof.
  intros r Q T e W; constructor; intros; try reflexivity;
    change (run_qua (mapped_opening r Q T e) k (subst_qvar r x) = subst_qvar r x)
      || change (run_typ (mapped_opening r Q T e) k (subst_tvar r x) = subst_tvar r x)
      || change (run_exp (mapped_opening r Q T e) k (subst_evar r x) = subst_evar r x);
    unfold mapped_opening.
  - eapply run_qua_identity; [apply opening_fixes_atoms|apply opening_fixes_below|].
    eapply scoped_qua_mono; eauto using subst_qua_scoped, Nat.le_0_l.
  - eapply run_typ_identity; [apply opening_fixes_atoms|apply opening_fixes_below|].
    eapply scoped_typ_mono; eauto using subst_typ_scoped, Nat.le_0_l.
  - eapply run_exp_identity; [apply opening_fixes_atoms|apply opening_fixes_below|].
    eapply scoped_exp_mono; eauto using subst_exp_scoped, Nat.le_0_l.
Qed.

Lemma sqt_opening : forall r Q T e s, scoped_subst r ->
  subst_qtyp r (run_qtyp (opening Q T e) 0 s) = run_qtyp (mapped_opening r Q T e) 0 (subst_qtyp r s).
Proof.
  unfold subst_qtyp; intros.
  rewrite (run_qtyp_compose _ _ _ _ _ (subst_after_opening r Q T e)).
  unfold subst_qtyp; symmetry.
  apply run_qtyp_compose, opening_after_subst; assumption.
Qed.

Lemma se_opening : forall r Q T e s, scoped_subst r ->
  subst_exp r (run_exp (opening Q T e) 0 s) = run_exp (mapped_opening r Q T e) 0 (subst_exp r s).
Proof.
  unfold subst_exp; intros.
  rewrite (run_exp_compose _ _ _ _ _ (subst_after_opening r Q T e)).
  unfold subst_exp; symmetry.
  apply run_exp_compose, opening_after_subst; assumption.
Qed.

Lemma sqt_open_type : forall r T U, scoped_subst r ->
  subst_qtyp r (open_tqt T U) = open_tqt (subst_qtyp r T) (subst_typ r U).
Proof.
  intros; rewrite <- run_open_tqt, sqt_opening by assumption.
  apply run_open_tqt.
Qed.
Lemma sqt_open_qua : forall r T Q, scoped_subst r ->
  subst_qtyp r (open_qqt T Q) = open_qqt (subst_qtyp r T) (subst_qua r Q).
Proof.
  intros; rewrite <- run_open_qqt, sqt_opening by assumption.
  apply run_open_qqt.
Qed.
Lemma se_open_type : forall r e U, scoped_subst r ->
  subst_exp r (open_te e U) = open_te (subst_exp r e) (subst_typ r U).
Proof.
  intros; rewrite <- run_open_te, se_opening by assumption.
  apply run_open_te.
Qed.
Lemma se_open_qua : forall r e Q, scoped_subst r ->
  subst_exp r (open_qe e Q) = open_qe (subst_exp r e) (subst_qua r Q).
Proof.
  intros; rewrite <- run_open_qe, se_opening by assumption.
  apply run_open_qe.
Qed.
Lemma se_open_exp : forall r e f, scoped_subst r ->
  subst_exp r (open_ee e f) = open_ee (subst_exp r e) (subst_exp r f).
Proof.
  intros; rewrite <- run_open_ee, se_opening by assumption.
  apply run_open_ee.
Qed.

(* The environment relation records the typing and bounds of the images of
   its variables. It extends at fresh binders by weakening those images. *)
Record subst_env (r : free_subst) (E F : env) : Prop := {
  subst_bound_qua : forall X Q, binds X (bind_qua Q) E ->
    subqual F (subst_qvar r X) (subst_qua r Q);
  subst_bound_typ : forall X T, binds X (bind_sub T) E ->
    sub F (subst_tvar r X) (subst_typ r T);
  subst_bound_exp : forall X T, binds X (bind_typ T) E ->
    typing F (subst_evar r X) (subst_qtyp r T)
}.

Definition subst_binding r b :=
  match b with
  | bind_qua Q => bind_qua (subst_qua r Q)
  | bind_sub T => bind_sub (subst_typ r T)
  | bind_typ T => bind_typ (subst_qtyp r T)
  end.

Definition fixes_outside r L :=
  fixes_atoms (subst_action r) (fun X => X `notin` L).

Local Hint Resolve includes_tail : core.

Lemma subst_env_push : forall r E F X b L,
  subst_env r E F -> fixes_outside r L -> X `notin` L ->
  wf_env (X ~ subst_binding r b ++ F) ->
  subst_env r (X ~ b ++ E) (X ~ subst_binding r b ++ F).
Proof.
  intros r E F X b L [SQ ST SE] K FX W.
  destruct (K X FX) as [EqQ [EqT EqE]]; cbn in EqQ, EqT, EqE.
  constructor; intros y U Hb; split_binds Hb; cbn.
  - rewrite EqQ. eapply subqual_trans_qvar with (R := subst_qua r U).
    + eauto using binds_app_2.
    + apply qua_reflexivity; [exact W|].
      exact (wf_lookup _ W X (bind_qua (subst_qua r U)) ltac:(eauto using binds_app_2)).
  - eapply subqual_weaken_local; [exact (SQ _ _ Hb)|exact (includes_tail F (X ~ subst_binding r b))|exact W].
  - rewrite EqT. eapply sub_trans_tvar with (U := subst_typ r U).
    + eauto using binds_app_2.
    + apply typ_reflexivity; [|exact W].
      exact (wf_lookup _ W X (bind_sub (subst_typ r U)) ltac:(eauto using binds_app_2)).
  - eapply sub_weaken_local; [exact (ST _ _ Hb)|exact (includes_tail F (X ~ subst_binding r b))|exact W].
  - rewrite EqE. apply typing_var; eauto using binds_app_2.
  - eapply typing_weaken_local; [exact (SE _ _ Hb)|exact (includes_tail F (X ~ subst_binding r b))|exact W].
Qed.

Local Ltac simplify_subst r :=
  cbn [subst_qua subst_typ subst_qtyp subst_exp run_qua run_typ run_qtyp run_exp];
  repeat match goal with
  | |- context [run_qua (subst_action r) 1 ?t] => rewrite (run_qua_depth t r 1 0)
  | |- context [run_typ (subst_action r) 1 ?t] => rewrite (run_typ_depth t r 1 0)
  | |- context [run_qtyp (subst_action r) 1 ?t] => rewrite (proj2 run_types_depth t r 1 0)
  | |- context [run_exp (subst_action r) 1 ?t] => rewrite (run_exp_depth t r 1 0)
  end;
  fold (subst_qua r) (subst_typ r) (subst_qtyp r) (subst_exp r).

Local Ltac simplify_subst_in r H :=
  cbn [subst_qua subst_typ subst_qtyp subst_exp run_qua run_typ run_qtyp run_exp] in H;
  repeat match type of H with
  | context [run_qua (subst_action r) 1 ?t] => rewrite (run_qua_depth t r 1 0) in H
  | context [run_typ (subst_action r) 1 ?t] => rewrite (run_typ_depth t r 1 0) in H
  | context [run_qtyp (subst_action r) 1 ?t] => rewrite (run_qtyp_depth t r 1 0) in H
  | context [run_exp (subst_action r) 1 ?t] => rewrite (run_exp_depth t r 1 0) in H
  end;
  fold (subst_qua r) (subst_typ r) (subst_qtyp r) (subst_exp r) in H.

Lemma wf_qua_subst : forall E Q, wf_qua E Q ->
  forall r F, subst_env r E F -> wf_qua F (subst_qua r Q).
Proof.
  induction 1; intros; simplify_subst r; eauto.
  match goal with M : subst_env _ _ _, Hb : binds _ _ _ |- _ =>
    exact (proj1 (proj2 (subqual_regular _ _ _ (subst_bound_qua _ _ _ M _ _ Hb))))
  end.
Qed.

Local Hint Resolve wf_qua_subst : core.

Lemma wf_types_subst : forall r L, scoped_subst r -> fixes_outside r L ->
  (forall E T, wf_typ E T -> forall F, subst_env r E F -> wf_env F -> wf_typ F (subst_typ r T)) /\
  (forall E T, wf_qtyp E T -> forall F, subst_env r E F -> wf_env F -> wf_qtyp F (subst_qtyp r T)).
Proof.
  intros r Lr Closed Fix; apply wf_types_mut; intros; simplify_subst r; eauto.
  - match goal with M : subst_env _ _ _, Hb : binds _ _ _ |- _ =>
      exact (proj1 (sub_regular _ _ _ (subst_bound_typ _ _ _ M _ _ Hb)))
    end.
  - apply wf_typ_all with (L := L `union` Lr `union` dom F); eauto.
    intros X FX.
    assert (Fresh : X `notin` Lr) by solve_notin.
    assert (Fresh0 : X `notin` L) by solve_notin.
    assert (W : wf_env (X ~ bind_sub (subst_typ r T1) ++ F)) by
      (constructor; eauto; solve_notin).
    pose proof (H0 X Fresh0 _ ltac:(eapply subst_env_push; eauto) W) as J.
    rewrite sqt_open_type in J by assumption.
    destruct (Fix X Fresh) as [_ [Eq _]].
    change (subst_typ r (typ_fvar X) = typ_fvar X) in Eq.
    now rewrite Eq in J.
  - apply wf_typ_qall with (L := L `union` Lr `union` dom F); eauto.
    intros X FX.
    assert (Fresh : X `notin` Lr) by solve_notin.
    assert (Fresh0 : X `notin` L) by solve_notin.
    assert (W : wf_env (X ~ bind_qua (subst_qua r T1) ++ F)) by
      (constructor; eauto; solve_notin).
    pose proof (H X Fresh0 _ ltac:(eapply subst_env_push; eauto) W) as J.
    rewrite sqt_open_qua in J by assumption.
    destruct (Fix X Fresh) as [Eq _].
    change (subst_qua r (qua_fvar X) = qua_fvar X) in Eq.
    now rewrite Eq in J.
Qed.

Definition wf_typ_subst r L C K := proj1 (wf_types_subst r L C K).
Definition wf_qtyp_subst r L C K := proj2 (wf_types_subst r L C K).

Lemma subst_concrete : forall Q r b, concretize Q = Some b -> subst_qua r Q = Q.
Proof.
  induction Q; intros; cbn in H; try discriminate; try reflexivity;
    destruct (concretize Q1), (concretize Q2); try discriminate;
    simplify_subst r; f_equal; eauto.
Qed.

Lemma subqual_subst_local : forall E Q R, subqual E Q R ->
  forall r F, subst_env r E F -> wf_env F -> subqual F (subst_qua r Q) (subst_qua r R).
Proof.
  induction 1; intros; simplify_subst r;
    eauto using qua_reflexivity, subqual_top, subqual_bot, subqual_lift_elem,
      subqual_join_inl, subqual_join_inr, subqual_join_elim, subqual_meet_eliml,
      subqual_meet_elimr, subqual_meet_intro.
  - eapply subqual_eval_elim; [apply IHsubqual1; eassumption| |apply IHsubqual2; eassumption].
    erewrite subst_concrete; eauto.
  - eapply subqual_eval_intro; [apply IHsubqual1; eassumption| |apply IHsubqual2; eassumption].
    erewrite subst_concrete; eauto.
  - change (subqual F (subst_qua r (qua_fvar X)) (subst_qua r (qua_fvar X))).
    eauto using qua_reflexivity.
  - eapply qua_transitivity; [eapply subst_bound_qua; eassumption|eauto].
Qed.

Local Hint Resolve subqual_subst_local : core.

Lemma subst_push_wf : forall r L E F X b,
  scoped_subst r -> fixes_outside r L -> subst_env r E F -> wf_env F ->
  X `notin` dom F -> wf_env (X ~ b ++ E) ->
  wf_env (X ~ subst_binding r b ++ F).
Proof.
  intros r L E F X b C K M W Fr Wsrc.
  pose proof (wf_typ_subst r L C K) as WT.
  pose proof (wf_qtyp_subst r L C K) as WQ.
  inversion Wsrc; subst; cbn; constructor; eauto.
Qed.

Local Ltac rewrite_subst_openings J :=
  repeat first [rewrite sqt_open_type in J by assumption |
    rewrite sqt_open_qua in J by assumption |
    rewrite se_open_type in J by assumption |
    rewrite se_open_qua in J by assumption |
    rewrite se_open_exp in J by assumption].

Local Ltac use_substituted_body r Lr F :=
  let X := fresh "X" in let FX := fresh "FX" in intros X FX;
  let Fresh := fresh "Fresh" in assert (Fresh : X `notin` Lr) by solve_notin;
  let K := fresh "K" in
  match goal with IH : forall x : atom, x `notin` ?L ->
       forall G, subst_env r _ G -> wf_env G -> _ |- _ =>
    pose proof (IH X ltac:(solve_notin)) as K;
    match type of K with forall G, subst_env r (?Y ~ ?b ++ ?E) G -> _ =>
      let Wsrc := fresh "Wsrc" in
      assert (Wsrc : wf_env (Y ~ b ++ E)) by
        (match goal with HB : forall x : atom, x `notin` ?L0 -> _ |- _ =>
           first [eapply typing_env_local; exact (HB X ltac:(solve_notin)) |
                  eapply subqtype_env_local; exact (HB X ltac:(solve_notin))]
         end);
      let W := fresh "W" in
      assert (W : wf_env (X ~ subst_binding r b ++ F)) by
        (eapply subst_push_wf; eauto; solve_notin);
      specialize (K _ ltac:(eapply subst_env_push; eauto) W)
    end;
    rewrite_subst_openings K;
    match goal with Fix : fixes_outside r Lr |- _ =>
      let EqQ := fresh "EqQ" in let EqT := fresh "EqT" in let EqE := fresh "EqE" in
      destruct (Fix X Fresh) as [EqQ [EqT EqE]];
      change (subst_qua r (qua_fvar X) = qua_fvar X) in EqQ;
      change (subst_typ r (typ_fvar X) = typ_fvar X) in EqT;
      change (subst_exp r (exp_fvar X) = exp_fvar X) in EqE;
      try rewrite EqQ in K; try rewrite EqT in K; try rewrite EqE in K
    end;
    exact K
  end.

Lemma sub_types_subst : forall r L, scoped_subst r -> fixes_outside r L ->
  (forall E S T, sub E S T -> forall F, subst_env r E F -> wf_env F ->
    sub F (subst_typ r S) (subst_typ r T)) /\
  (forall E S T, subqtype E S T -> forall F, subst_env r E F -> wf_env F ->
    subqtype F (subst_qtyp r S) (subst_qtyp r T)).
Proof.
  intros r Lr Closed Fix.
  pose proof (wf_typ_subst r Lr Closed Fix) as WT.
  apply sub_types_mut; intros; simplify_subst r;
    eauto using sub_top, typ_reflexivity, sub_arrow, sub_sum, sub_pair, sub_qtyp_qtyp.
  - change (sub F (subst_typ r (typ_fvar X)) (subst_typ r (typ_fvar X))).
    eauto using typ_reflexivity.
  - match goal with M : subst_env _ _ _, Hb : binds _ _ _ |- _ =>
      eapply typ_transitivity; [exact (subst_bound_typ _ _ _ M _ _ Hb)|eauto]
    end.
  - apply sub_all with (L := L `union` Lr `union` dom F); eauto.
    use_substituted_body r Lr F.
  - apply sub_qall with (L := L `union` Lr `union` dom F); eauto.
    use_substituted_body r Lr F.
Qed.

Definition sub_subst r L C K := proj1 (sub_types_subst r L C K).
Definition subqtype_subst r L C K := proj2 (sub_types_subst r L C K).

Lemma typing_subst : forall r L, scoped_subst r -> fixes_outside r L ->
  forall E e T, typing E e T -> forall F, subst_env r E F -> wf_env F ->
  typing F (subst_exp r e) (subst_qtyp r T).
Proof.
  intros r Lr Closed Fix E e T Ty.
  pose proof (sub_subst r Lr Closed Fix) as ST.
  pose proof (subqtype_subst r Lr Closed Fix) as SQ.
  pose proof (wf_qtyp_subst r Lr Closed Fix) as WQ.
  induction Ty; intros F M W;
    repeat match goal with IH : forall G, subst_env r _ G -> wf_env G -> typing G _ _ |- _ =>
      specialize (IH F M W); simplify_subst_in r IH
    end;
    simplify_subst r;
    eauto 6 using typing_app, typing_sub, typing_inl, typing_inr,
      typing_pair, typing_first, typing_second, typing_upqual, typing_check.
  - match goal with Hb : binds _ (bind_typ _) _ |- _ =>
      exact (subst_bound_exp _ _ _ M _ _ Hb)
    end.
  - eapply typing_abs with (L := L `union` Lr `union` dom F); eauto.
    use_substituted_body r Lr F.
  - eapply typing_tabs with (L := L `union` Lr `union` dom F); eauto.
    use_substituted_body r Lr F.
  - rewrite sqt_open_type by assumption.
    eapply typing_tapp; eauto.
  - eapply typing_qabs with (L := L `union` Lr `union` dom F); eauto.
    use_substituted_body r Lr F.
  - rewrite sqt_open_qua by assumption.
    eapply typing_qapp; eauto.
  - eapply typing_let with (L := L `union` Lr `union` dom F) (T1 := subst_qtyp r T1); eauto.
    use_substituted_body r Lr F.
  - eapply typing_case with (L := L `union` Lr `union` dom F)
      (Q := subst_qua r Q) (T1 := subst_qtyp r T1) (T2 := subst_qtyp r T2); eauto;
    use_substituted_body r Lr F.
Qed.

Definition atom_override {A : Type} (X : atom) (u : option A) (var : atom -> A) y :=
  match u with Some a => if X == y then a else var y | None => var y end.

Definition single_subst X Q T e : free_subst :=
  {| subst_qvar := atom_override X Q qua_fvar;
     subst_tvar := atom_override X T typ_fvar;
     subst_evar := atom_override X e exp_fvar |}.

Lemma atom_override_same : forall (A : Type) X (u : A) var,
  atom_override X (Some u) var X = u.
Proof. intros; unfold atom_override; destruct (X == X); congruence. Qed.

Lemma single_fixes_other : forall X Q T e,
  fixes_atoms (subst_action (single_subst X Q T e)) (atom_avoids X).
Proof.
  intros X Q T e Y FY. unfold atom_avoids in FY.
  destruct Q, T, e; cbn [subst_action substitution single_subst free_qua free_typ
    free_exp subst_qvar subst_tvar subst_evar atom_override];
    destruct (X == Y); congruence || auto.
Qed.

Lemma single_fixes_outside : forall X Q T e, fixes_outside (single_subst X Q T e) (singleton X).
Proof.
  intros X Q T e Y FY; apply single_fixes_other; unfold atom_avoids; solve_notin.
Qed.

Local Ltac single_identity :=
  first [eapply run_qua_identity | eapply run_typ_identity |
         eapply run_qtyp_identity | eapply run_exp_identity];
  [apply single_fixes_other | red; cbn; auto | eassumption].

Lemma single_preserves_bound : forall E X Q T e b,
  wf_env E -> X `notin` dom E ->
  (match b with
   | bind_qua R => wf_qua E R
   | bind_sub U => wf_typ E U
   | bind_typ U => wf_qtyp E U
   end) ->
  subst_binding (single_subst X Q T e) b = b.
Proof.
  intros E X Q T e b W Fr Hb. destruct b; cbn in Hb |- *; f_equal.
  - assert (bare_typ X 0 t) by eauto using typ_avoids_binding. unfold subst_typ; single_identity.
  - assert (bare_qtyp X 0 q) by eauto using qtyp_avoids_binding. unfold subst_qtyp; single_identity.
  - assert (bare_qua X 0 q) by eauto using qua_avoids_binding. unfold subst_qua; single_identity.
Qed.

Lemma single_env : forall X Q T e E b,
  wf_env (X ~ b ++ E) ->
  (match b with
   | bind_qua R => subqual E (subst_qvar (single_subst X Q T e) X) R
   | bind_sub V => sub E (subst_tvar (single_subst X Q T e) X) V
   | bind_typ V => typing E (subst_evar (single_subst X Q T e) X) V
   end) ->
  subst_env (single_subst X Q T e) (X ~ b ++ E) E.
Proof.
  intros X Q T e E b W H.
  assert (WE : wf_env E) by (inversion W; auto).
  assert (Fr : X `notin` dom E) by (inversion W; auto).
  assert (Eq : subst_binding (single_subst X Q T e) b = b).
  { eapply single_preserves_bound; eauto. inversion W; auto. }
  constructor; intros Y U Hb; split_binds Hb.
  - cbn in Eq; injection Eq as Eq; rewrite Eq; exact H.
  - pose proof (wf_lookup _ WE _ _ Hb) as Wu.
    pose proof (single_preserves_bound E X Q T e (bind_qua U) WE Fr Wu) as Eb.
    pose proof (single_fixes_other X Q T e Y ltac:(unfold atom_avoids; intro; subst;
      eapply binds_dom_contradiction; eassumption)) as [Er _].
    change (subst_qvar (single_subst X Q T e) Y = qua_fvar Y) in Er.
    cbn in Eb; injection Eb as Eb; rewrite Eb, Er.
    eapply subqual_trans_qvar; [exact Hb|apply qua_reflexivity; auto].
  - cbn in Eq; injection Eq as Eq; rewrite Eq; exact H.
  - pose proof (wf_lookup _ WE _ _ Hb) as Wu.
    pose proof (single_preserves_bound E X Q T e (bind_sub U) WE Fr Wu) as Eb.
    pose proof (single_fixes_other X Q T e Y ltac:(unfold atom_avoids; intro; subst;
      eapply binds_dom_contradiction; eassumption)) as [_ [Er _]].
    change (subst_tvar (single_subst X Q T e) Y = typ_fvar Y) in Er.
    cbn in Eb; injection Eb as Eb; rewrite Eb, Er.
    eapply sub_trans_tvar; [exact Hb|apply typ_reflexivity; auto].
  - cbn in Eq; injection Eq as Eq; rewrite Eq; exact H.
  - pose proof (wf_lookup _ WE _ _ Hb) as Wu.
    pose proof (single_preserves_bound E X Q T e (bind_typ U) WE Fr Wu) as Eb.
    pose proof (single_fixes_other X Q T e Y ltac:(unfold atom_avoids; intro; subst;
      eapply binds_dom_contradiction; eassumption)) as [_ [_ Er]].
    change (subst_evar (single_subst X Q T e) Y = exp_fvar Y) in Er.
    cbn in Eb; injection Eb as Eb; rewrite Eb, Er.
    apply typing_var; auto.
Qed.

Lemma single_scoped : forall X Q T e,
  (match Q with Some q => scoped_qua 0 q | None => True end) ->
  (match T with Some t => scoped_typ 0 t | None => True end) ->
  (match e with Some f => scoped_exp 0 f | None => True end) ->
  scoped_subst (single_subst X Q T e).
Proof.
  intros; constructor; intros Y; destruct Q, T, e; cbn [single_subst
    subst_qvar subst_tvar subst_evar atom_override];
    destruct (X == Y); cbn; auto.
Qed.

Lemma single_exp_fresh : forall X Q T e f, X `notin` fv_exp f ->
  subst_exp (single_subst X Q T e) f = f.
Proof.
  intros. assert (bare_exp X 0 f) by eauto using exp_fv_avoids.
  unfold subst_exp; single_identity.
Qed.
Lemma single_qtyp_fresh : forall X Q T e U, X `notin` fv_qtyp U ->
  subst_qtyp (single_subst X Q T e) U = U.
Proof.
  intros. assert (bare_qtyp X 0 U) by eauto using qtyp_fv_avoids.
  unfold subst_qtyp; single_identity.
Qed.

Lemma type_argument_subst : forall E X V U,
  sub E U V -> wf_env (X ~ bind_sub V ++ E) ->
  scoped_subst (single_subst X None (Some U) None) /\
  subst_env (single_subst X None (Some U) None) (X ~ bind_sub V ++ E) E.
Proof.
  intros E X V U S W; split.
  - apply single_scoped; simpl; auto.
    apply type_scoped, typ_locally_closed with (E := E), (proj1 (sub_regular _ _ _ S)).
  - apply single_env; auto. cbn [single_subst subst_tvar].
    rewrite atom_override_same. exact S.
Qed.

Lemma qua_argument_subst : forall E X V U,
  subqual E U V -> wf_env (X ~ bind_qua V ++ E) ->
  scoped_subst (single_subst X (Some U) None None) /\
  subst_env (single_subst X (Some U) None None) (X ~ bind_qua V ++ E) E.
Proof.
  intros E X V U S W; split.
  - apply single_scoped; simpl; auto.
    apply qual_scoped, qua_locally_closed with (E := E), (proj1 (proj2 (subqual_regular _ _ _ S))).
  - apply single_env; auto. cbn [single_subst subst_qvar].
    rewrite atom_override_same. exact S.
Qed.

Lemma exp_argument_subst : forall E X V u,
  typing E u V -> wf_env (X ~ bind_typ V ++ E) ->
  scoped_subst (single_subst X None None (Some u)) /\
  subst_env (single_subst X None None (Some u)) (X ~ bind_typ V ++ E) E.
Proof.
  intros E X V u S W; split.
  - apply single_scoped; simpl; try exact I.
    apply expr_scoped. eapply typing_expr_local; exact S.
  - apply single_env; auto. cbn [single_subst subst_evar].
    rewrite atom_override_same. exact S.
Qed.

Local Ltac finish_instantiation J :=
  rewrite_subst_openings J;
  repeat first [rewrite single_exp_fresh in J by solve_notin |
                rewrite single_qtyp_fresh in J by solve_notin];
  cbn [subst_exp subst_typ subst_qua run_exp run_typ run_qua subst_action substitution free_exp
       free_typ free_qua single_subst subst_evar subst_tvar subst_qvar] in J;
  rewrite atom_override_same in J; exact J.

Lemma instantiate_exp_body : forall L E e V T u,
  (forall X : atom, X `notin` L -> typing (X ~ bind_typ V ++ E) (open_ee e X) T) ->
  typing E u V -> typing E (open_ee e u) T.
Proof.
  intros L E e V T u Body H.
  destruct (atom_fresh (L `union` fv_exp e `union` fv_qtyp T)) as [X FX].
  pose proof (Body X ltac:(solve_notin)) as Hbody.
  destruct (exp_argument_subst _ _ _ _ H (typing_env_local _ _ _ Hbody)) as [C M].
  pose proof (typing_subst _ _ C (single_fixes_outside X None None (Some u))
    _ _ _ Hbody _ M (typing_env_local _ _ _ H)) as J.
  finish_instantiation J.
Qed.

Lemma instantiate_type_body : forall L E e V T U,
  (forall X : atom, X `notin` L ->
    typing (X ~ bind_sub V ++ E) (open_te e X) (open_tqt T X)) ->
  sub E U V -> typing E (open_te e U) (open_tqt T U).
Proof.
  intros L E e V T U Body H.
  destruct (atom_fresh (L `union` fv_exp e `union` fv_qtyp T)) as [X FX].
  pose proof (Body X ltac:(solve_notin)) as Hbody.
  destruct (type_argument_subst _ _ _ _ H (typing_env_local _ _ _ Hbody)) as [C M].
  pose proof (typing_subst _ _ C (single_fixes_outside X None (Some U) None)
    _ _ _ Hbody _ M (sub_env_local _ _ _ H)) as J.
  finish_instantiation J.
Qed.

Lemma instantiate_qua_body : forall L E e V T U,
  (forall X : atom, X `notin` L ->
    typing (X ~ bind_qua V ++ E) (open_qe e X) (open_qqt T X)) ->
  subqual E U V -> typing E (open_qe e U) (open_qqt T U).
Proof.
  intros L E e V T U Body H.
  destruct (atom_fresh (L `union` fv_exp e `union` fv_qtyp T)) as [X FX].
  pose proof (Body X ltac:(solve_notin)) as Hbody.
  destruct (qua_argument_subst _ _ _ _ H (typing_env_local _ _ _ Hbody)) as [C M].
  pose proof (typing_subst _ _ C (single_fixes_outside X (Some U) None None)
    _ _ _ Hbody _ M (proj1 (subqual_regular _ _ _ H))) as J.
  finish_instantiation J.
Qed.

Lemma instantiate_type_sub : forall L E V S T U,
  (forall X : atom, X `notin` L ->
    subqtype (X ~ bind_sub V ++ E) (open_tqt S X) (open_tqt T X)) ->
  sub E U V -> subqtype E (open_tqt S U) (open_tqt T U).
Proof.
  intros L E V S T U Body H.
  destruct (atom_fresh (L `union` fv_qtyp S `union` fv_qtyp T)) as [X FX].
  pose proof (Body X ltac:(solve_notin)) as Hbody.
  destruct (type_argument_subst _ _ _ _ H (subqtype_env_local _ _ _ Hbody)) as [C M].
  pose proof (subqtype_subst _ _ C (single_fixes_outside X None (Some U) None)
    _ _ _ Hbody _ M (sub_env_local _ _ _ H)) as J.
  finish_instantiation J.
Qed.

Lemma instantiate_qua_sub : forall L E V S T U,
  (forall X : atom, X `notin` L ->
    subqtype (X ~ bind_qua V ++ E) (open_qqt S X) (open_qqt T X)) ->
  subqual E U V -> subqtype E (open_qqt S U) (open_qqt T U).
Proof.
  intros L E V S T U Body H.
  destruct (atom_fresh (L `union` fv_qtyp S `union` fv_qtyp T)) as [X FX].
  pose proof (Body X ltac:(solve_notin)) as Hbody.
  destruct (qua_argument_subst _ _ _ _ H (subqtype_env_local _ _ _ Hbody)) as [C M].
  pose proof (subqtype_subst _ _ C (single_fixes_outside X (Some U) None None)
    _ _ _ Hbody _ M (proj1 (subqual_regular _ _ _ H))) as J.
  finish_instantiation J.
Qed.

(* Elimination remains valid after any number of subsumption rules. *)
Definition value_payload E e U : Prop :=
  let '(qtyp_qtyp _ T) := U in
  match e, T with
  | exp_abs _ _ b, typ_arrow A C =>
      forall a, typing E a A -> typing E (open_ee b a) C
  | exp_tabs _ _ b, typ_all A C =>
      forall U, sub E U A -> typing E (open_te b U) (open_tqt C U)
  | exp_qabs _ _ b, typ_qall A C =>
      forall Q, subqual E Q A -> typing E (open_qe b Q) (open_qqt C Q)
  | exp_inl _ a, typ_sum A _ => typing E a A
  | exp_inr _ a, typ_sum _ A => typing E a A
  | exp_pair _ a b, typ_pair A C => typing E a A /\ typing E b C
  | _, _ => True
  end.

Lemma typing_value_payload : forall E e U,
  typing E e U -> value e -> value_payload E e U.
Proof.
  induction 1; intro Hv; try solve [inversion Hv]; cbn;
    eauto using instantiate_exp_body, instantiate_type_body, instantiate_qua_body.
  pose proof (qtype_value_shape _ _ _ H Hv) as Shape.
  specialize (IHtyping Hv).
  inversion H0; subst.
  match goal with S : sub _ _ _ |- _ => destruct S end;
    cbn in *; try contradiction; try exact I.
  all: inversion Hv; subst; cbn in *; try exact I.
  - intros a Ha. eapply typing_sub; [apply IHtyping; eauto using typing_sub|eassumption].
  - intros U HU. eapply typing_sub.
    + apply IHtyping. eapply typ_transitivity; eassumption.
    + eapply instantiate_type_sub with (L := L) (V := T1); eassumption.
  - intros U HU. eapply typing_sub.
    + apply IHtyping. eapply qua_transitivity; eassumption.
    + eapply instantiate_qua_sub with (L := L) (V := T1); eassumption.
  - eauto using typing_sub.
  - eauto using typing_sub.
  - destruct IHtyping; split; eauto using typing_sub.
Qed.

Definition annotate P e :=
  match e with
  | exp_abs _ T b => exp_abs P T b
  | exp_tabs _ T b => exp_tabs P T b
  | exp_qabs _ Q b => exp_qabs P Q b
  | exp_inl _ a => exp_inl P a
  | exp_inr _ a => exp_inr P a
  | exp_pair _ a b => exp_pair P a b
  | _ => e
  end.

Lemma annotate_typing : forall E e U, typing E e U ->
  forall P, wf_qua E P -> annotation e <> None ->
  match U with qtyp_qtyp _ T => typing E (annotate P e) (qtyp_qtyp P T) end.
Proof.
  induction 1; intros New WNew Ann; try solve [elim Ann; reflexivity];
    cbn; eauto using typing_abs, typing_tabs, typing_qabs, typing_inl, typing_inr, typing_pair.
  inversion H0; subst. eapply typing_sub.
  - eapply IHtyping; eauto.
  - apply sub_qtyp_qtyp; eauto using qua_reflexivity.
Qed.

Local Ltac use_value_payload :=
  match goal with
  | H : typing _ ?e _ |- _ =>
    let V := fresh "V" in
    assert (V : value e) by eauto using value_abs, value_tabs, value_qabs,
      value_inl, value_inr, value_pair;
    let K := fresh "K" in
    pose proof (typing_value_payload _ _ _ H V) as K;
    cbn in K;
    solve [eauto using instantiate_exp_body | destruct K; eauto]
  end.

Theorem preservation : forall E e e' T,
  typing E e T ->
  red e e' ->
  typing E e' T.
Proof.
  intros E e e' T Ty; revert e'.
  induction Ty; intros e' Step; inversion Step; subst;
    eauto using typing_app, typing_tapp, typing_qapp, typing_sub, typing_let,
    typing_inl, typing_inr, typing_case, typing_pair, typing_first, typing_second,
    typing_upqual, typing_check, instantiate_exp_body.
  all: try solve [use_value_payload].
  all: add_qua_regular;
    match goal with H : typing _ ?e (qtyp_qtyp _ _) |- typing _ _ (qtyp_qtyp ?P _) =>
      pose proof (annotate_typing _ _ _ H P ltac:(assumption) ltac:(discriminate)) as J;
      exact J
    end.
Qed.

Theorem progress : forall e T,
  typing empty e T ->
  value e \/ exists e', red e e'.
Proof.
  intros e T H; remember empty as E eqn:HE; induction H; subst.
  - inversion H0.
  - left; apply value_abs. eauto using typing_abs.
  - right. destruct (IHtyping1 eq_refl) as [V1|[f Hf]];
      [destruct (IHtyping2 eq_refl) as [V2|[g Hg]]|].
    + pose proof (qtype_value_shape _ _ _ H V1) as Shape.
      inversion V1; subst; cbn in Shape; try contradiction.
      eexists; eauto using red_abs.
    + eexists; eauto using red_app_2.
    + eexists; eauto using red_app_1.
  - left; apply value_tabs. eauto using typing_tabs.
  - right. destruct (sub_regular _ _ _ H0) as [WT _].
    destruct (IHtyping eq_refl) as [V|[f Hf]].
    + pose proof (qtype_value_shape _ _ _ H V) as Shape.
      inversion V; subst; cbn in Shape; try contradiction.
      eexists; eauto using red_tabs.
    + eexists; eauto using red_tapp.
  - left; apply value_qabs. eauto using typing_qabs.
  - right. add_qua_regular.
    destruct (IHtyping eq_refl) as [V|[f Hf]].
    + pose proof (qtype_value_shape _ _ _ H V) as Shape.
      inversion V; subst; cbn in Shape; try contradiction.
      eexists; eauto using red_qabs.
    + eexists; eauto using red_qapp.
  - auto.
  - right.
    assert (Body : body_e e2) by (exists L; eauto).
    destruct (IHtyping eq_refl) as [V|[f Hf]]; eexists; eauto using red_let, red_let_1.
  - destruct (IHtyping eq_refl) as [V|[f Hf]].
    + left; eauto using value_inl.
    + right; eexists; eauto using red_inl_1.
  - destruct (IHtyping eq_refl) as [V|[f Hf]].
    + left; eauto using value_inr.
    + right; eexists; eauto using red_inr_1.
  - right.
    assert (Body1 : body_e e2) by (exists L; eauto).
    assert (Body2 : body_e e3) by (exists L; eauto).
    destruct (IHtyping eq_refl) as [V|[f Hf]].
    + pose proof (qtype_value_shape _ _ _ H V) as Shape.
      inversion V; subst; cbn in Shape; try contradiction;
        eexists; eauto using red_case_inl, red_case_inr.
    + eexists; eauto using red_case_1.
  - destruct (IHtyping1 eq_refl) as [V1|[f Hf]];
      [destruct (IHtyping2 eq_refl) as [V2|[g Hg]]|].
    + left; eauto using value_pair.
    + right; eexists; eauto using red_pair_2.
    + right; eexists; eauto using red_pair_1.
  - right. destruct (IHtyping eq_refl) as [V|[f Hf]].
    + pose proof (qtype_value_shape _ _ _ H V) as Shape.
      inversion V; subst; cbn in Shape; try contradiction.
      eexists; eauto using red_pair_first_2.
    + eexists; eauto using red_pair_first_1.
  - right. destruct (IHtyping eq_refl) as [V|[f Hf]].
    + pose proof (qtype_value_shape _ _ _ H V) as Shape.
      inversion V; subst; cbn in Shape; try contradiction.
      eexists; eauto using red_pair_second_2.
    + eexists; eauto using red_pair_second_1.
  - right. destruct (IHtyping eq_refl) as [V|[f Hf]].
    + exact (proj1 (qualifier_value_steps _ _ _ _ V H H0)).
    + add_qua_regular. eexists; eauto using red_upqual_1.
  - right. destruct (IHtyping eq_refl) as [V|[f Hf]].
    + exists e. exact (proj2 (qualifier_value_steps _ _ _ _ V H H0)).
    + add_qua_regular. eexists; eauto using red_check_1.
Qed.
