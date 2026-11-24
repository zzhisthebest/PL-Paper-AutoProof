Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export LinearRule.

Inductive binding : Set :=
  | bind_sub : binding
  | bind_typ : typ -> binding.

Definition env := list (atom * binding).

Notation empty := (@nil (atom * binding)).

Inductive WFS : env -> typ -> Prop :=
| WFS_top : forall E, WFS E typ_top
| WFS_nat : forall E, WFS E typ_nat
| WFS_fvar : forall X E ,
    binds X (bind_sub) E ->
    WFS E (typ_fvar X)
| WFS_arrow : forall E A B,
    WFS E A ->
    WFS E B ->
    WFS E (typ_arrow A B)
| WFS_rec : forall L E A,


      (forall  X , X \notin L ->
        WFS (X ~ bind_sub ++ E) (open_tt A X)) ->
      WFS E (typ_mu A).

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) ,
      wf_env E ->
      X \notin dom E ->
      wf_env (X ~ bind_sub ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      WFS E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E).

Inductive sub_amber2: env -> typ -> typ -> Prop :=
| sam2_nat: forall E,
    wf_env E ->
    sub_amber2 E typ_nat typ_nat
| sam2_top: forall E A,
    WFS E A ->
    wf_env E ->
    sub_amber2 E A typ_top
| sam2_fvar: forall E X,
    binds X (bind_sub) E ->
    wf_env E ->
    sub_amber2 E (typ_fvar X) (typ_fvar X)
| sam2_arrow: forall E A1 A2 B1 B2,
    sub_amber2 E B1 A1 ->
    sub_amber2 E A2 B2 ->
    sub_amber2 E (typ_arrow A1 A2) (typ_arrow B1 B2)
| sam2_rec: forall E A B L,
    (forall X , X \notin L ->
                sub_amber2 (X ~ bind_sub ++ E) (open_tt A X) (open_tt B X)) ->
    (forall X , X \notin L ->
                posvar Pos X (typ_mu A) (typ_mu B)) ->
    sub_amber2 E (typ_mu A) (typ_mu B)
.

Definition drop_im b :=
  match b with
  | Rules.bind_sub _ => bind_sub
  | Rules.bind_typ t => bind_typ t
  end.

Definition drop_im_env := map drop_im.

Local Hint Constructors WFS wf_env Rules.WFS Rules.wf_env type : core.

Lemma drop_im_binds : forall E X im,
  binds X (Rules.bind_sub im) E -> binds X bind_sub (map drop_im E).
Proof.
  intros E X im H. exact (binds_map _ _ drop_im _ _ _ H).
Qed.

Lemma drop_im_binds_inv : forall E X,
  binds X bind_sub (map drop_im E) ->
  exists im, binds X (Rules.bind_sub im) E.
Proof.
  induction E as [| [Y b] E IH]; intros X H.
  - inversion H.
  - apply binds_cons_1 in H as [[-> Hb] | H].
    + destruct b; simpl in Hb; try discriminate. eauto using binds_cons_2.
    + destruct (IH X H) as [im Hbind]. eauto using binds_cons.
Qed.

Lemma drop_im_wfs : forall E A,
  Rules.WFS E A -> WFS (map drop_im E) A.
Proof.
  intros E A H. induction H; eauto using drop_im_binds.
Qed.

Lemma lift_im_wfs : forall E A,
  WFS E A -> forall F, E = map drop_im F -> Rules.WFS F A.
Proof.
  intros E A H. induction H; intros F HF; subst.
  - constructor.
  - constructor.
  - destruct (drop_im_binds_inv _ _ H) as [im Hbind]. eauto.
  - constructor; eauto.
  - eapply Rules.WFS_rec with (L := L) (im := Pos).
    intros X HX. apply H0; auto.
Qed.

Lemma drop_im_wf_env : forall E,
  Rules.wf_env E -> wf_env (map drop_im E).
Proof.
  intros E H. induction H; simpl; auto.
  - constructor; auto.
  - constructor; auto using drop_im_wfs.
Qed.

Lemma quicksub_wfs_type : forall E A, Rules.WFS E A -> type A.
Proof.
  intros E A H. induction H; eauto.
Qed.

Lemma quicksub_regular : forall im cm evs E A B,
  Sub im cm evs E A B ->
  Rules.wf_env E /\ Rules.WFS E A /\ Rules.WFS E B.
Proof.
  intros im cm evs E A B H. induction H; try solve [intuition eauto].
  all: match goal with
  | IH : forall X, X \notin ?L -> _ |- _ =>
    split; [pick fresh X for L; specialize (IH X ltac:(fsetdec));
            destruct IH as [HE _]; inversion HE; assumption |
            split; eapply Rules.WFS_rec with (L := L) (im := im); intros X HX;
            specialize (IH X HX); tauto]
  end.
Qed.

Lemma quicksub_flip_xor : forall im im_x,
  mode_xor (flip_im im) im_x = flip_im (mode_xor im im_x).
Proof. destruct im, im_x; reflexivity. Qed.

Lemma quicksub_same_xor : forall im, mode_xor im im = Pos.
Proof. destruct im; reflexivity. Qed.

Lemma quicksub_other_xor : forall im, mode_xor im (flip_im im) = Neg.
Proof. destruct im; reflexivity. Qed.

Lemma quicksub_wf_uniq : forall E, Rules.wf_env E -> uniq E.
Proof.
  intros E H. induction H; eauto using uniq_nil, uniq_push.
Qed.

Lemma quicksub_open_fv : forall A k X Y,
  X <> Y ->
  (X `in` fv_tt (open_tt_rec k Y A) <-> X `in` fv_tt A).
Proof.
  induction A; intros k X Y HXY; simpl; try tauto.
  - destruct (k === n); simpl; fsetdec.
  - apply IHA. assumption.
  - rewrite !AtomSetFacts.union_iff, IHA1, IHA2 by assumption. tauto.
Qed.

Lemma quicksub_open_inj : forall A B k X,
  X \notin fv_tt A -> X \notin fv_tt B ->
  open_tt_rec k X A = open_tt_rec k X B -> A = B.
Proof.
  induction A; destruct B; intros k X HA HB H;
    simpl in *;
    repeat match goal with
    | H : context [if ?d then _ else _] |- _ => destruct d; subst
    end;
    try discriminate; try contradiction; try reflexivity;
    inversion H; subst; try reflexivity; try solve [exfalso; fsetdec].
  - f_equal. eapply IHA; eauto.
  - f_equal; [eapply IHA1 | eapply IHA2]; eauto; fsetdec.
Qed.

Lemma quicksub_open_eq : forall L A B,
  (forall X, X \notin L -> open_tt A X = open_tt B X) -> A = B.
Proof.
  intros L A B H. pick fresh X for (L \u fv_tt A \u fv_tt B).
  eapply quicksub_open_inj with (k := 0) (X := X); try fsetdec.
  apply H. fsetdec.
Qed.

Lemma quicksub_compose_eq : forall cm1 cm2 evs1 evs2,
  compose_cm cm1 cm2 evs1 evs2 = Some Eq -> cm1 = Eq /\ cm2 = Eq.
Proof.
  destruct cm1, cm2; intros evs1 evs2 H; simpl in H;
    try (destruct (AtomSetImpl.is_empty evs1));
    try (destruct (AtomSetImpl.is_empty evs2)); congruence || auto.
Qed.

Lemma quicksub_eq_types : forall im cm evs E A B,
  Sub im cm evs E A B -> cm = Eq -> A = B.
Proof.
  intros im cm evs E A B H. induction H; intros Hcm; subst;
    try discriminate; try reflexivity; auto.
  - apply quicksub_compose_eq in H1 as [-> ->].
    f_equal; auto using eq_sym.
  - f_equal. apply (quicksub_open_eq L). intros X HX. now apply H0.
  - f_equal. apply (quicksub_open_eq L). intros X HX. now apply H0.
Qed.

Lemma quicksub_eq_evs_fv : forall im cm evs E A B,
  Sub im cm evs E A B -> cm = Eq -> AtomSetImpl.Subset evs (fv_tt A).
Proof.
  intros im cm evs E A B H.
  induction H; intros Hcm Z HX; subst;
    try discriminate; try solve [simpl in *; unfold emp in *; fsetdec].
  - apply quicksub_compose_eq in H1 as [-> ->].
    simpl. apply AtomSetFacts.union_iff in HX as [HX | HX].
    + apply AtomSetFacts.union_iff. left.
      rewrite <- (quicksub_eq_types _ _ _ _ _ _ H eq_refl). apply IHSub1; [reflexivity | exact HX].
    + apply AtomSetFacts.union_iff. right. apply IHSub2; [reflexivity | exact HX].
  - pick fresh Y for (L \u {{Z}}).
    apply (proj1 (quicksub_open_fv A1 0 Z Y ltac:(fsetdec))).
    apply H0; fsetdec || assumption || reflexivity.
  - apply AtomSetFacts.union_iff in HX as [HX | HX]; [| exact HX].
    pick fresh Y for (L \u {{Z}}).
    apply (proj1 (quicksub_open_fv A1 0 Z Y ltac:(fsetdec))).
    apply H0; fsetdec || reflexivity.
  - apply IHSub; [reflexivity | fsetdec].
Qed.

Lemma quicksub_open_eq_pos : forall L im evs E A B,
  (forall Y, Y \notin L ->
     Sub im Eq (add Y evs) (Y ~ Rules.bind_sub im ++ E)
       (open_tt A Y) (open_tt B Y)) ->
  forall X m, X \notin fv_tt A -> posvar m X (typ_mu A) (typ_mu B).
Proof.
  intros L im evs E A B H X m HX.
  assert (A = B) as ->.
  { apply (quicksub_open_eq L). intros Y HY.
    eapply quicksub_eq_types; [apply H; exact HY | reflexivity]. }
  eapply pos_rec_t with (L := L); auto.
  intros Y HY. eapply quicksub_wfs_type.
  destruct (quicksub_regular _ _ _ _ _ _ (H Y ltac:(fsetdec))) as [_ [HW _]].
  exact HW.
Qed.

(* An atom outside the evidence satisfies variance at the mode allowed by
   its binding. An unbound atom can be checked at either mode. *)
Lemma quicksub_posvar : forall im cm evs E A B,
  Sub im cm evs E A B ->
  forall X m,
  (forall im_x, binds X (Rules.bind_sub im_x) E -> m = mode_xor im im_x) ->
  X \notin evs -> posvar m X A B.
Proof.
  intros im cm evs E A B H. induction H; intros Y m HM HY.
  - constructor.
  - apply pos_top. constructor.
  - apply pos_top. eauto using quicksub_wfs_type.
  - destruct (Y == X) as [-> | Hne]; [| now apply pos_fvar_y].
    rewrite (HM im H0), quicksub_same_xor. constructor.
  - apply pos_fvar_y. fsetdec.
  - apply pos_arrow.
    + apply IHSub1; [| fsetdec].
      intros im_y HB. rewrite quicksub_flip_xor, (HM im_y HB). reflexivity.
    + apply IHSub2; [assumption | fsetdec].
  - eapply pos_rec with (L := L \u evs \u dom E).
    + intros X HX. apply H0; try fsetdec.
      intros im_y HB. apply binds_cons_1 in HB as [[Heq _] | HB]; [fsetdec | auto].
    + intros X HX. apply H0; try fsetdec.
      intros im_x HB. apply binds_cons_1 in HB as [[_ Heq] | HB].
      * inversion Heq; subst. symmetry. apply quicksub_same_xor.
      * exfalso. eapply binds_dom_contradiction; [exact HB | fsetdec].
  - eapply pos_rec with (L := L \u evs \u dom E).
    + intros X HX. apply H0; try fsetdec.
      intros im_y HB. apply binds_cons_1 in HB as [[Heq _] | HB]; [fsetdec | auto].
    + intros X HX. apply H0; try fsetdec.
      intros im_x HB. apply binds_cons_1 in HB as [[_ Heq] | HB].
      * inversion Heq; subst. symmetry. apply quicksub_same_xor.
      * exfalso. eapply binds_dom_contradiction; [exact HB | fsetdec].
  - eapply quicksub_open_eq_pos; [exact H | fsetdec].
  - apply IHSub; [assumption | fsetdec].
Qed.

Theorem pos_esa_sound: forall im cm evs E A B,
  Sub im cm evs E A B ->
  sub_amber2 (map drop_im E) A B.
Proof.
  intros im cm evs E A B H. induction H.
  - constructor. auto using drop_im_wf_env.
  - apply sam2_top; auto using drop_im_wf_env.
  - apply sam2_top; auto using drop_im_wf_env, drop_im_wfs.
  - apply sam2_fvar; eauto using drop_im_wf_env, drop_im_binds.
  - apply sam2_fvar; eauto using drop_im_wf_env, drop_im_binds.
  - apply sam2_arrow; assumption.
  - eapply sam2_rec with (L := L \u evs \u dom E).
    + intros X HX. apply H0. fsetdec.
    + intros X HX. eapply quicksub_posvar.
      * eapply Sa_rec_lt; exact H.
      * intros im_x HB. exfalso. eapply binds_dom_contradiction; [exact HB | fsetdec].
      * fsetdec.
  - eapply sam2_rec with (L := L \u evs \u dom E).
    + intros X HX. apply H0. fsetdec.
    + intros X HX. eapply quicksub_posvar.
      * eapply Sa_rec_eq_notin; exact H.
      * intros im_x HB. exfalso. eapply binds_dom_contradiction; [exact HB | fsetdec].
      * fsetdec.
  - eapply sam2_rec with (L := L \u fv_tt A1).
    + intros X HX. apply H0. fsetdec.
    + intros X HX. eapply quicksub_open_eq_pos; [exact H | fsetdec].
  - assumption.
Qed.

(* Renaming a fresh opening makes the equality evidence uniform over the binder. *)
Section QuickSubRenaming.
  Variable p : atom -> atom.
  Hypothesis p_involutive : forall X, p (p X) = X.

  Lemma quicksub_rename_inj : forall X Y, p X = p Y -> X = Y.
  Proof.
    intros X Y H. rewrite <- (p_involutive X), <- (p_involutive Y), H.
    reflexivity.
  Qed.

  Definition quicksub_rename_set (s : atoms) : atoms :=
    AtomSetImpl.fold (fun X acc => add (p X) acc) s {}.

  Lemma quicksub_rename_set_mem : forall s X,
    p X `in` quicksub_rename_set s <-> X `in` s.
  Proof.
    unfold quicksub_rename_set.
    intro s. apply (AtomSetProperties.fold_rec
      (P := fun s acc => forall X, p X `in` acc <-> X `in` s)).
    - intros s' Hempty X. rewrite AtomSetFacts.empty_iff.
      specialize (Hempty X). tauto.
    - intros Y acc s' s'' _ _ Hadd IH X.
      rewrite AtomSetFacts.add_iff, IH, (Hadd X).
      split; intros [H | H]; auto using quicksub_rename_inj.
      left. now f_equal.
  Qed.

  Lemma quicksub_rename_fresh : forall s X,
    X \notin quicksub_rename_set s -> p X \notin s.
  Proof.
    intros s X HX Hin. apply HX. rewrite <- (p_involutive X) at 1.
    now apply quicksub_rename_set_mem.
  Qed.

  Lemma quicksub_rename_empty : quicksub_rename_set {} [=] {}.
  Proof.
    intro X. rewrite <- (p_involutive X) at 1.
    rewrite quicksub_rename_set_mem. fsetdec.
  Qed.

  Lemma quicksub_rename_add : forall X s,
    quicksub_rename_set (add X s) [=] add (p X) (quicksub_rename_set s).
  Proof.
    intros X s Y. replace Y with (p (p Y)) by apply p_involutive.
    rewrite quicksub_rename_set_mem, !AtomSetFacts.add_iff, quicksub_rename_set_mem.
    split; intros [H | H]; auto using quicksub_rename_inj.
    left. now f_equal.
  Qed.

  Lemma quicksub_rename_singleton : forall X,
    quicksub_rename_set {{X}} [=] {{p X}}.
  Proof.
    intros X Y. replace Y with (p (p Y)) by apply p_involutive.
    rewrite quicksub_rename_set_mem, !AtomSetFacts.singleton_iff.
    split; auto using quicksub_rename_inj.
    intro H. now f_equal.
  Qed.

  Lemma quicksub_rename_union : forall s t,
    quicksub_rename_set (s \u t) [=] quicksub_rename_set s \u quicksub_rename_set t.
  Proof.
    intros s t X. replace X with (p (p X)) by apply p_involutive.
    rewrite !AtomSetFacts.union_iff, !quicksub_rename_set_mem,
      AtomSetFacts.union_iff. reflexivity.
  Qed.

  Lemma quicksub_rename_fixed : forall s,
    (forall X, X `in` s -> p X = X) -> quicksub_rename_set s [=] s.
  Proof.
    intros s H X. split; intro HX.
    - assert (Hp : p X `in` s).
      { apply quicksub_rename_set_mem. now rewrite p_involutive. }
      pose proof (H (p X) Hp) as Hfix.
      rewrite p_involutive in Hfix. now rewrite Hfix.
    - rewrite <- (H X HX) at 1. now apply quicksub_rename_set_mem.
  Qed.

  Fixpoint quicksub_rename_typ (A : typ) : typ :=
    match A with
    | typ_fvar X => typ_fvar (p X)
    | typ_mu B => typ_mu (quicksub_rename_typ B)
    | typ_arrow B C => typ_arrow (quicksub_rename_typ B) (quicksub_rename_typ C)
    | _ => A
    end.

  Lemma quicksub_rename_open_rec : forall A k (X : atom),
    quicksub_rename_typ (open_tt_rec k X A) =
      open_tt_rec k (p X) (quicksub_rename_typ A).
  Proof.
    induction A; intros k X; simpl; try reflexivity.
    - destruct (k === n); reflexivity.
    - now rewrite IHA.
    - now rewrite IHA1, IHA2.
  Qed.

  Lemma quicksub_rename_open : forall A (X : atom),
    quicksub_rename_typ (open_tt A X) = open_tt (quicksub_rename_typ A) (p X).
  Proof. intros. apply quicksub_rename_open_rec. Qed.

  Lemma quicksub_rename_fv : forall A,
    quicksub_rename_set (fv_tt A) [=] fv_tt (quicksub_rename_typ A).
  Proof.
    induction A; simpl; try apply quicksub_rename_empty; auto.
    - apply quicksub_rename_singleton.
    - rewrite quicksub_rename_union, IHA1, IHA2. reflexivity.
  Qed.

  Lemma quicksub_rename_typ_fixed : forall A,
    (forall X, X `in` fv_tt A -> p X = X) -> quicksub_rename_typ A = A.
  Proof.
    induction A; intros H; simpl in *; try reflexivity.
    - f_equal. apply H. fsetdec.
    - f_equal. auto.
    - f_equal; [apply IHA1 | apply IHA2]; intros X HX; apply H; fsetdec.
  Qed.

  Definition quicksub_rename_binding (b : Rules.binding) : Rules.binding :=
    match b with
    | Rules.bind_sub im => Rules.bind_sub im
    | Rules.bind_typ A => Rules.bind_typ (quicksub_rename_typ A)
    end.

  Definition quicksub_rename_env (E : Rules.env) : Rules.env :=
    List.map (fun '(X, b) => (p X, quicksub_rename_binding b)) E.

  Lemma quicksub_rename_binds : forall E X b,
    binds X b E -> binds (p X) (quicksub_rename_binding b) (quicksub_rename_env E).
  Proof.
    induction E as [|[Y c] E IH]; intros X b H; simpl.
    - inversion H.
    - apply binds_cons_1 in H as [[-> ->] | H].
      + apply binds_cons_2; reflexivity.
      + apply binds_cons. auto.
  Qed.

  Lemma quicksub_rename_dom : forall E X,
    p X `in` dom (quicksub_rename_env E) <-> X `in` dom E.
  Proof.
    induction E as [|[Y b] E IH]; intro X; simpl; [fsetdec |].
    rewrite !AtomSetFacts.add_iff, IH.
    split; intros [H | H]; auto using quicksub_rename_inj.
    left. now f_equal.
  Qed.

  Lemma quicksub_rename_wfs : forall E A,
    Rules.WFS E A -> Rules.WFS (quicksub_rename_env E) (quicksub_rename_typ A).
  Proof.
    intros E A H. induction H; simpl.
    - constructor.
    - constructor.
    - eapply Rules.WFS_fvar with (im := im). exact (quicksub_rename_binds _ _ _ H).
    - constructor; assumption.
    - eapply Rules.WFS_rec with (L := quicksub_rename_set L) (im := im).
      intros X HX.
      specialize (H0 (p X) (quicksub_rename_fresh L X HX)).
      rewrite quicksub_rename_open, p_involutive in H0.
      simpl in H0. now rewrite p_involutive in H0.
  Qed.

  Lemma quicksub_rename_wf : forall E,
    Rules.wf_env E -> Rules.wf_env (quicksub_rename_env E).
  Proof.
    intros E H. induction H; simpl.
    - apply Rules.wf_env_empty.
    - apply Rules.wf_env_sub; [assumption |].
      intro Hin. apply (proj1 (quicksub_rename_dom E X)) in Hin. contradiction.
    - apply Rules.wf_env_typ; [assumption | now apply quicksub_rename_wfs |].
      intro Hin. apply (proj1 (quicksub_rename_dom E x)) in Hin. contradiction.
  Qed.

  Lemma quicksub_rename_eq : forall im cm evs E A B,
    Sub im cm evs E A B -> cm = Eq ->
    Sub im Eq (quicksub_rename_set evs) (quicksub_rename_env E)
      (quicksub_rename_typ A) (quicksub_rename_typ B).
  Proof.
    intros im cm evs E A B H. induction H; intro HC; subst; simpl;
      try discriminate.
    - eapply Sa_evs_proper; [apply Sa_nat; auto using quicksub_rename_wf |].
      unfold emp. symmetry. apply quicksub_rename_empty.
    - eapply Sa_evs_proper; [apply Sa_top_eq; auto using quicksub_rename_wf |].
      unfold emp. symmetry. apply quicksub_rename_empty.
    - eapply Sa_evs_proper; [apply Sa_fvar_pos |].
      + auto using quicksub_rename_wf.
      + exact (quicksub_rename_binds _ _ _ H0).
      + unfold emp. symmetry. apply quicksub_rename_empty.
    - eapply Sa_evs_proper; [apply Sa_fvar_neg |].
      + auto using quicksub_rename_wf.
      + exact (quicksub_rename_binds _ _ _ H0).
      + symmetry. apply quicksub_rename_singleton.
    - apply quicksub_compose_eq in H1 as [-> ->].
      eapply Sa_evs_proper.
      + eapply Sa_arrow with (cm1 := Eq) (cm2 := Eq); eauto.
      + symmetry. apply quicksub_rename_union.
    - eapply Sa_rec_eq_notin with (L := quicksub_rename_set L).
      intros X HX.
      specialize (H0 (p X) (quicksub_rename_fresh L X HX) eq_refl).
      rewrite !quicksub_rename_open, p_involutive in H0.
      simpl in H0. now rewrite p_involutive in H0.
    - eapply Sa_evs_proper.
      + eapply Sa_rec_eq_in with (L := quicksub_rename_set L)
          (evs := quicksub_rename_set evs).
        intros X HX.
        specialize (H0 (p X) (quicksub_rename_fresh L X HX) eq_refl).
        rewrite !quicksub_rename_open in H0. simpl in H0.
        rewrite p_involutive in H0.
        eapply Sa_evs_proper; [exact H0 |].
        rewrite quicksub_rename_add, p_involutive. reflexivity.
      + rewrite quicksub_rename_union, quicksub_rename_fv. reflexivity.
    - eapply Sa_evs_proper; [apply IHSub; reflexivity |].
      intro X. replace X with (p (p X)) by apply p_involutive.
      rewrite !quicksub_rename_set_mem. apply H0.
  Qed.
End QuickSubRenaming.

Definition quicksub_swap (X Y Z : atom) : atom :=
  if Z == X then Y else if Z == Y then X else Z.

Lemma quicksub_swap_left : forall X Y, quicksub_swap X Y X = Y.
Proof. intros. unfold quicksub_swap. destruct (X == X); congruence. Qed.

Lemma quicksub_swap_right : forall X Y, quicksub_swap X Y Y = X.
Proof.
  intros. unfold quicksub_swap. destruct (Y == X), (Y == Y); congruence.
Qed.

Lemma quicksub_swap_fixed : forall X Y Z,
  Z <> X -> Z <> Y -> quicksub_swap X Y Z = Z.
Proof.
  intros. unfold quicksub_swap. destruct (Z == X), (Z == Y); congruence.
Qed.

Lemma quicksub_swap_involutive : forall X Y Z,
  quicksub_swap X Y (quicksub_swap X Y Z) = Z.
Proof.
  intros X Y Z. destruct (Z == X) as [-> | HZX].
  - rewrite quicksub_swap_left. apply quicksub_swap_right.
  - destruct (Z == Y) as [-> | HZY].
    + rewrite quicksub_swap_right. apply quicksub_swap_left.
    + now rewrite !(quicksub_swap_fixed X Y Z HZX HZY).
Qed.

Fixpoint quicksub_env_support (E : Rules.env) : atoms :=
  match E with
  | nil => {}
  | (X, Rules.bind_sub _) :: F => add X (quicksub_env_support F)
  | (X, Rules.bind_typ A) :: F => add X (fv_tt A \u quicksub_env_support F)
  end.

Lemma quicksub_rename_env_fixed : forall p E,
  (forall X, X `in` quicksub_env_support E -> p X = X) ->
  quicksub_rename_env p E = E.
Proof.
  intros p E. induction E as [|[X b] E IH]; intro H; simpl; auto.
  destruct b; simpl in *;
    rewrite (H X) by fsetdec;
    rewrite IH by (intros Y HY; apply H; fsetdec).
  - reflexivity.
  - rewrite quicksub_rename_typ_fixed; [reflexivity |].
    intros Y HY. apply H. fsetdec.
Qed.

Lemma quicksub_swap_eq_open : forall F A im X Y evs,
  X \notin fv_tt A -> X \notin quicksub_env_support F ->
  Y \notin fv_tt A -> Y \notin quicksub_env_support F ->
  Sub im Eq evs (X ~ Rules.bind_sub im ++ F) (open_tt A X) (open_tt A X) ->
  Sub im Eq (quicksub_rename_set (quicksub_swap X Y) evs)
    (Y ~ Rules.bind_sub im ++ F) (open_tt A Y) (open_tt A Y).
Proof.
  intros F A im X Y evs HXA HXF HYA HYF H.
  pose proof (quicksub_rename_eq (quicksub_swap X Y)
    (quicksub_swap_involutive X Y) _ _ _ _ _ _ H eq_refl) as Hr.
  rewrite quicksub_rename_open in Hr. simpl in Hr.
  rewrite quicksub_swap_left, quicksub_rename_typ_fixed,
    quicksub_rename_env_fixed in Hr; try exact Hr;
    intros Z HZ; apply quicksub_swap_fixed; fsetdec.
Qed.

Lemma quicksub_swap_set_fixed : forall X Y s,
  X \notin s -> Y \notin s -> quicksub_rename_set (quicksub_swap X Y) s [=] s.
Proof.
  intros. apply quicksub_rename_fixed; [apply quicksub_swap_involutive |].
  intros Z HZ. apply quicksub_swap_fixed; fsetdec.
Qed.

(* A reflexive comparison may report evidence even in a well-formed
   environment. In the recursive case, it matters whether that evidence
   contains the fresh name for the recursive variable. *)
Lemma quicksub_reflexive : forall E A,
  WFS E A -> forall F im, E = map drop_im F -> Rules.wf_env F ->
  exists evs, Sub im Eq evs F A A.
Proof.
  intros E A HW. induction HW; intros F im Hmap Hwf; subst.
  - exists emp. now apply Sa_top_eq.
  - exists emp. now apply Sa_nat.
  - destruct (drop_im_binds_inv _ _ H) as [im_x Hbind].
    destruct im, im_x; simpl in *;
      eauto using Sa_fvar_pos, Sa_fvar_neg.
  - destruct (IHHW1 F (flip_im im) eq_refl Hwf) as [s Hs].
    destruct (IHHW2 F im eq_refl Hwf) as [t Ht].
    exists (s \u t). eapply Sa_arrow with (cm1 := Eq) (cm2 := Eq); eauto.
  - pick fresh X for (L \u dom F \u fv_tt A \u quicksub_env_support F).
    assert (HwfX : Rules.wf_env (X ~ Rules.bind_sub im ++ F)).
    { constructor; auto; fsetdec. }
    destruct (H0 X ltac:(fsetdec) (X ~ Rules.bind_sub im ++ F) im eq_refl HwfX) as [evs Hevs].
    set (L' := {{X}} \u fv_tt A \u quicksub_env_support F).
    assert (Hfresh : forall Y, Y \notin L' -> Y \notin evs).
    { intros Y HY Hin.
      pose proof (quicksub_eq_evs_fv _ _ _ _ _ _ Hevs eq_refl Y Hin) as Hfv.
      apply (proj1 (quicksub_open_fv A 0 Y X ltac:(unfold L' in HY; fsetdec))) in Hfv.
      unfold L' in HY. fsetdec. }
    destruct (AtomSetImpl.mem X evs) eqn:HX.
    + apply AtomSetFacts.mem_iff in HX.
      set (rest := AtomSetImpl.remove X evs).
      exists (rest \u fv_tt A). eapply Sa_rec_eq_in with (L := L').
      intros Y HY.
      assert (Hbody : Sub im Eq (add X rest) (X ~ Rules.bind_sub im ++ F)
                        (open_tt A X) (open_tt A X)).
      { eapply Sa_evs_proper; [exact Hevs |]. unfold rest. fsetdec. }
      eapply Sa_evs_proper.
      * eapply (quicksub_swap_eq_open F A im X Y); [fsetdec | fsetdec | unfold L' in HY; fsetdec |
                                       unfold L' in HY; fsetdec | exact Hbody].
      * rewrite quicksub_rename_add by apply quicksub_swap_involutive.
        rewrite quicksub_swap_left, quicksub_swap_set_fixed; try reflexivity.
        -- unfold rest. fsetdec.
        -- pose proof (Hfresh Y HY). unfold rest. fsetdec.
    + assert (HX' : X \notin evs).
      { intro Hin. apply AtomSetFacts.mem_iff in Hin. congruence. }
      exists evs. eapply Sa_rec_eq_notin with (L := L').
      intros Y HY. eapply Sa_evs_proper.
      * eapply (quicksub_swap_eq_open F A im X Y); [fsetdec | fsetdec | unfold L' in HY; fsetdec |
                                       unfold L' in HY; fsetdec | exact Hevs].
      * apply quicksub_swap_set_fixed; auto.
Qed.

Lemma quicksub_posvar_mu_inv : forall m X A B,
  posvar m X (typ_mu A) (typ_mu B) ->
  (A = B /\ X \notin fv_tt A) \/
  exists L,
    (forall Y, Y \notin L -> posvar m X (open_tt A Y) (open_tt B Y)) /\
    (forall Y, Y \notin L -> posvar Pos Y (open_tt A Y) (open_tt B Y)).
Proof.
  intros m X A B H. inversion H; subst.
  - right. eauto.
  - left. auto.
Qed.

Lemma quicksub_eq_excludes : forall im cm evs E A B,
  Sub im cm evs E A B -> cm = Eq ->
  forall X im_x, binds X (Rules.bind_sub im_x) E ->
  posvar (mode_xor im im_x) X A B -> X \notin evs.
Proof.
  intros im cm evs E A B H. induction H; intros HC Y im_y HB HP; subst;
    try discriminate; try solve [unfold emp; fsetdec].
  - intro Hin. assert (Y = X) as -> by fsetdec.
    assert (im_y = flip_im im) as ->.
    { injection (binds_unique _ _ _ _ _ HB H0 (quicksub_wf_uniq _ H)); auto. }
    rewrite quicksub_other_xor in HP. inversion HP; congruence.
  - apply quicksub_compose_eq in H1 as [-> ->].
    inversion HP; subst. intro Hin.
    apply AtomSetFacts.union_iff in Hin as [Hin | Hin].
    + apply (IHSub1 eq_refl Y im_y HB); [rewrite quicksub_flip_xor; eassumption | exact Hin].
    + apply (IHSub2 eq_refl Y im_y HB); assumption.
  - destruct (quicksub_posvar_mu_inv _ _ _ _ HP) as [[-> HF] | [L' [HV _]]].
    + pick fresh Z for (L \u {{Y}}).
      intro Hin.
      pose proof (quicksub_eq_evs_fv _ _ _ _ _ _ (H Z ltac:(fsetdec)) eq_refl Y Hin) as Hfv.
      apply HF. eapply (proj1 (quicksub_open_fv A2 0 Y Z ltac:(fsetdec))). exact Hfv.
    + pick fresh Z for (L \u L').
      apply (H0 Z ltac:(fsetdec) eq_refl Y im_y); [now apply binds_cons |].
      apply HV. fsetdec.
  - destruct (quicksub_posvar_mu_inv _ _ _ _ HP) as [[-> HF] | [L' [_ HV]]].
    + pick fresh Z for (L \u {{Y}}).
      intro Hin. apply AtomSetFacts.union_iff in Hin as [Hin | Hin]; [| contradiction].
      assert (Hin' : Y `in` add Z evs) by fsetdec.
      pose proof (quicksub_eq_evs_fv _ _ _ _ _ _ (H Z ltac:(fsetdec)) eq_refl Y Hin') as Hfv.
      apply HF. eapply (proj1 (quicksub_open_fv A2 0 Y Z ltac:(fsetdec))). exact Hfv.
    + pick fresh Z for (L \u L').
      exfalso. apply (H0 Z ltac:(fsetdec) eq_refl Z im).
      * apply binds_cons_2; reflexivity.
      * rewrite quicksub_same_xor. apply HV. fsetdec.
      * fsetdec.
  - intro Hin. apply (IHSub eq_refl Y im_y HB HP). fsetdec.
Qed.

Lemma quicksub_wfs_fv : forall E A,
  Rules.WFS E A -> forall X, X `in` fv_tt A ->
  exists im, binds X (Rules.bind_sub im) E.
Proof.
  intros E A HW. induction HW; intros Y HY; simpl in HY; try solve [fsetdec].
  - assert (Y = X) as -> by fsetdec. eauto.
  - apply AtomSetFacts.union_iff in HY as [HY | HY]; auto.
  - pick fresh Z for (L \u {{Y}}).
    assert (Hin : Y `in` fv_tt (open_tt A Z)).
    { apply quicksub_open_fv; [fsetdec | exact HY]. }
    destruct (H0 Z ltac:(fsetdec) Y Hin) as [m Hbind].
    apply binds_cons_1 in Hbind as [[Hbad _] | Hbind]; [fsetdec | eauto].
Qed.

Lemma quicksub_reflexive_empty : forall E A F im,
  WFS E A -> E = map drop_im F -> Rules.wf_env F ->
  well_bind_env im F A A -> Sub im Eq emp F A A.
Proof.
  intros E A F im HW HE HF HV.
  destruct (quicksub_reflexive _ _ HW F im HE HF) as [evs HS].
  eapply Sa_evs_proper; [exact HS |].
  apply AtomSetProperties.empty_is_empty_1. intros X HX.
  pose proof (quicksub_eq_evs_fv _ _ _ _ _ _ HS eq_refl X HX) as Hfv.
  destruct (quicksub_wfs_fv _ _ (lift_im_wfs _ _ HW F HE) X Hfv) as [im_x HB].
  exact (quicksub_eq_excludes _ _ _ _ _ _ HS eq_refl X im_x HB (HV X im_x HB) HX).
Qed.

Lemma quicksub_well_bind_mu : forall F im A B,
  A <> B -> well_bind_env im F (typ_mu A) (typ_mu B) ->
  exists L, forall Y, Y \notin L ->
    well_bind_env im F (open_tt A Y) (open_tt B Y).
Proof.
  induction F as [| [X b] F IH]; intros im A B Hne HV.
  - exists {}. intros Y HY Z m Hbind. inversion Hbind.
  - assert (Htail : well_bind_env im F (typ_mu A) (typ_mu B)).
    { intros Z m Hbind. apply HV. auto using binds_cons. }
    destruct (IH im A B Hne Htail) as [L HL].
    destruct b as [im_x | T].
    + assert (Hbind : binds X (Rules.bind_sub im_x) ((X, Rules.bind_sub im_x) :: F)).
      { apply binds_cons_2; reflexivity. }
      destruct (quicksub_posvar_mu_inv _ _ _ _ (HV _ _ Hbind))
        as [[Heq _] | [L' [Houter _]]]; [contradiction |].
      exists (L \u L'). intros Y HY Z m HZ.
      apply binds_cons_1 in HZ as [[-> Hmode] | HZ].
      * inversion Hmode; subst. apply Houter. fsetdec.
      * apply (HL Y ltac:(fsetdec) Z m HZ).
    + exists L. intros Y HY Z m HZ.
      apply binds_cons_1 in HZ as [[_ Hbad] | HZ]; [discriminate |].
      apply (HL Y HY Z m HZ).
Qed.

Lemma quicksub_amber_wfs : forall E A B, sub_amber2 E A B -> WFS E A /\ WFS E B.
Proof.
  intros E A B H. induction H; try solve [intuition eauto].
  split; eapply WFS_rec with (L := L); intros X HX; specialize (H0 X HX); tauto.
Qed.

Lemma quicksub_typ_eq_dec : forall A B : typ, {A = B} + {A <> B}.
Proof. decide equality; first [apply eq_nat_dec | apply Atom.eq_dec]. Defined.

Lemma quicksub_emp_is_empty : AtomSetImpl.is_empty emp = true.
Proof. apply AtomSetImpl.is_empty_1. unfold AtomSetImpl.Empty, emp. fsetdec. Qed.

(* The variance requirement on the annotated environment lets all
   subcomparisons use empty evidence, including equality inside arrows. *)
Lemma quicksub_amber_complete : forall E A B,
  sub_amber2 E A B ->
  forall F im, E = map drop_im F -> Rules.wf_env F -> well_bind_env im F A B ->
  exists cm, Sub im cm emp F A B.
Proof.
  intros E A B H.
  induction H as [E | E A HW | E X Hbind | E A1 A2 B1 B2 Hleft IHleft Hright IHright
                 | E A B L Hopen IHopen Hpos]; intros F im HE HF HV.
  - exists Eq. now apply Sa_nat.
  - destruct (quicksub_typ_eq_dec A typ_top) as [-> | Hne].
    + exists Eq. now apply Sa_top_eq.
    + exists Lt. apply Sa_top_lt; eauto using lift_im_wfs.
  - subst E. destruct (drop_im_binds_inv _ _ Hbind) as [im_x HB].
    assert (im_x = im) as ->.
    { pose proof (HV X im_x HB) as HP.
      destruct im, im_x; try reflexivity; simpl in HP; inversion HP; congruence. }
    exists Eq. now apply Sa_fvar_pos.
  - assert (HL : well_bind_env (flip_im im) F B1 A1).
    { intros X im_x HB. rewrite quicksub_flip_xor.
      pose proof (HV X im_x HB) as HP. inversion HP; subst; assumption. }
    assert (HR : well_bind_env im F A2 B2).
    { intros X im_x HB.
      pose proof (HV X im_x HB) as HP. inversion HP; subst; assumption. }
    destruct (IHleft F (flip_im im) HE HF HL) as [cm1 HS1].
    destruct (IHright F im HE HF HR) as [cm2 HS2].
    destruct cm1, cm2; eexists;
      (eapply Sa_evs_proper;
       [eapply Sa_arrow; [exact HS1 | exact HS2 | simpl; rewrite ?quicksub_emp_is_empty; reflexivity]
       | unfold emp; fsetdec]).
  - destruct (quicksub_typ_eq_dec A B) as [-> | Hne].
    + exists Eq. eapply quicksub_reflexive_empty; try eassumption.
      eapply WFS_rec with (L := L). intros X HX.
      exact (proj1 (quicksub_amber_wfs _ _ _ (Hopen X HX))).
    + destruct (quicksub_well_bind_mu _ _ _ _ Hne HV) as [L' HL].
      pick fresh Z for L.
      destruct (quicksub_posvar_mu_inv _ _ _ _ (Hpos Z ltac:(fsetdec)))
        as [[Heq _] | [L'' [_ Hself]]]; [contradiction |].
      exists Lt. eapply Sa_rec_lt with (L := L \u L' \u L'' \u dom F \u fv_tt A \u fv_tt B).
      intros X HX.
      assert (HFX : Rules.wf_env (X ~ Rules.bind_sub im ++ F)).
      { constructor; auto; fsetdec. }
      assert (HVX : well_bind_env im (X ~ Rules.bind_sub im ++ F) (open_tt A X) (open_tt B X)).
      { intros Y m HB. apply binds_cons_1 in HB as [[-> Hmode] | HB].
        - inversion Hmode; subst. rewrite quicksub_same_xor. apply Hself. fsetdec.
        - apply (HL X ltac:(fsetdec) Y m HB). }
      assert (HE' : (X ~ bind_sub ++ E) = map drop_im (X ~ Rules.bind_sub im ++ F)).
      { now rewrite HE. }
      destruct (IHopen X ltac:(fsetdec) _ im HE' HFX HVX) as [cm HS].
      destruct cm; [exact HS |].
      exfalso. apply Hne. eapply quicksub_open_inj with (k := 0) (X := X); try fsetdec.
      eapply quicksub_eq_types; [exact HS | reflexivity].
Qed.

Theorem pos_esa_complete_final: forall A B,
    sub_amber2 nil A B ->
    exists cm evs, Sub Pos cm evs nil A B.
Proof.
  intros A B H.
  assert (HV : well_bind_env Pos nil A B).
  { intros X im HX. inversion HX. }
  destruct (quicksub_amber_complete _ _ _ H nil Pos eq_refl Rules.wf_env_empty HV)
    as [cm HS].
  exists cm, emp. exact HS.
Qed.
