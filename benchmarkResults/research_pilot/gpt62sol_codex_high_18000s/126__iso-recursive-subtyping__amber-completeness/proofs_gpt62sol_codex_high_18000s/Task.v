Require Import AmberBase.

Require Import Metalib.Metatheory.

Require Import Program.Equality.

Definition env_mode := list ( Mode).

Definition eqMode (a b: Mode)  : bool :=
  match a,b with
  | Pos, Pos => true
  | Neg, Neg => true
  | _,_ => false
  end.

Fixpoint amber_cov (Ea : env_amber) (Em : env_mode) (T:typ) (m:Mode) : typ :=
  match Ea, Em with
  | (X,Y)::E, m'::Em' => if (eqMode m' m) then amber_cov E Em' (subst_tt X Y T) m
                         else amber_cov E Em' T m
  | _,_ => T
  end.

From Stdlib Require Import Lia.

(* Simultaneous instantiation of free variables, leaving binders in place. *)
Fixpoint ac_inst (f : atom -> typ) (T : typ) : typ :=
  match T with
  | typ_fvar X => f X
  | typ_mu A => typ_mu (ac_inst f A)
  | typ_arrow A B => typ_arrow (ac_inst f A) (ac_inst f B)
  | _ => T
  end.

Fixpoint ac_closed (k : nat) (T : typ) : Prop :=
  match T with
  | typ_bvar j => j < k
  | typ_mu A => ac_closed (S k) A
  | typ_arrow A B => ac_closed k A /\ ac_closed k B
  | _ => True
  end.

Lemma ac_inst_ext : forall T f g,
    (forall X, X \in fv_tt T -> f X = g X) ->
    ac_inst f T = ac_inst g T.
Proof.
  induction T; intros f g H; simpl in *; try reflexivity.
  - apply H. fsetdec.
  - f_equal. apply IHT. exact H.
  - f_equal.
    + apply IHT1. intros. apply H. fsetdec.
    + apply IHT2. intros. apply H. fsetdec.
Qed.

Lemma ac_inst_id : forall T, ac_inst typ_fvar T = T.
Proof. induction T; simpl; congruence. Qed.

Lemma ac_inst_eq_fvar : forall T f g X,
    ac_inst f T = ac_inst g T -> X \in fv_tt T -> f X = g X.
Proof.
  induction T; intros f g X H HX; simpl in *; try solve [fsetdec].
  - assert (X = a) by fsetdec. subst. exact H.
  - injection H as H. eauto.
  - injection H as H1 H2.
    assert (X \in fv_tt T1 \/ X \in fv_tt T2) as [H | H] by fsetdec;
      eauto.
Qed.

Lemma ac_inst_fv : forall T f S,
    (forall X, X \in fv_tt T -> fv_tt (f X) [<=] S) ->
    fv_tt (ac_inst f T) [<=] S.
Proof.
  induction T; intros f S H; simpl in *; try solve [fsetdec].
  - apply H. fsetdec.
  - auto.
  - assert (fv_tt (ac_inst f T1) [<=] S) by (apply IHT1; intros; apply H; fsetdec).
    assert (fv_tt (ac_inst f T2) [<=] S) by (apply IHT2; intros; apply H; fsetdec).
    fsetdec.
Qed.

Lemma ac_inst_closed : forall T f k,
    (forall X j, ac_closed j (f X)) ->
    ac_closed k T -> ac_closed k (ac_inst f T).
Proof. induction T; simpl; firstorder. Qed.

Lemma ac_closed_open_id : forall T k U,
    ac_closed k T -> open_tt_rec k U T = T.
Proof.
  induction T; intros k U H; simpl in *; try reflexivity.
  - destruct (k === n); [lia | reflexivity].
  - f_equal. auto.
  - destruct H. f_equal; auto.
Qed.

Lemma ac_closed_le : forall T k j,
    k <= j -> ac_closed k T -> ac_closed j T.
Proof.
  induction T; simpl; intros; try exact I.
  - lia.
  - eapply (IHT (S k)); [lia | exact H0].
  - destruct H0. split; eauto.
Qed.

Lemma ac_inst_open : forall T f k U,
    (forall X, ac_closed 0 (f X)) ->
    ac_inst f (open_tt_rec k U T) =
    open_tt_rec k (ac_inst f U) (ac_inst f T).
Proof.
  induction T; intros f k U H; simpl; try reflexivity.
  - destruct (k === n); reflexivity.
  - symmetry. apply ac_closed_open_id. eapply (ac_closed_le _ 0); [lia | apply H].
  - f_equal. auto.
  - f_equal; auto.
Qed.

Lemma ac_open_closed_inv : forall T k X,
    ac_closed k (open_tt_rec k (typ_fvar X) T) ->
    ac_closed (S k) T.
Proof.
  induction T; simpl; intros k X H; try exact I.
  - destruct (k === n); simpl in H; lia.
  - eauto.
  - destruct H. split; eauto.
Qed.

Lemma ac_open_closed : forall T k X,
    ac_closed (S k) T -> ac_closed k (open_tt_rec k (typ_fvar X) T).
Proof.
  induction T; simpl; intros k X H; try exact I.
  - destruct (k === n); simpl; [exact I | lia].
  - auto.
  - destruct H. split; auto.
Qed.

Lemma ac_open_fv : forall T k U,
    fv_tt T [<=] fv_tt (open_tt_rec k U T) /\
    fv_tt (open_tt_rec k U T) [<=] (fv_tt T \u fv_tt U).
Proof.
  induction T; simpl; intros k U; try solve [split; fsetdec].
  - destruct (k === n); simpl; split; fsetdec.
  - auto.
  - specialize (IHT1 k U). specialize (IHT2 k U). destruct IHT1, IHT2. split; fsetdec.
Qed.

Lemma ac_open_inj : forall A B k X,
    X \notin fv_tt A -> X \notin fv_tt B ->
    open_tt_rec k (typ_fvar X) A = open_tt_rec k (typ_fvar X) B ->
    A = B.
Proof.
  induction A; destruct B; intros k X HA HB H; simpl in *;
    repeat match goal with
    | H : context [ ?k === ?n ] |- _ => destruct (k === n)
    end;
    try discriminate; try reflexivity; try congruence;
    try solve [injection H as H; subst; exfalso; fsetdec].
  - injection H as H. f_equal. eauto.
  - injection H as H1 H2. f_equal.
    + eapply IHA1; try eassumption; fsetdec.
    + eapply IHA2; try eassumption; fsetdec.
Qed.

Lemma ac_sub_wf : forall E A B, sub E A B -> WF E A /\ WF E B.
Proof.
  intros E A B H. induction H.
  - split; constructor.
  - split; constructor; assumption.
  - split; auto using WF_top.
  - destruct IHsub1, IHsub2. split; constructor; assumption.
  - split; eapply WF_rec with (L := L); intros;
      [apply (H0 X) | apply (H2 X) | apply (H0 X) | apply (H2 X)];
      assumption.
Qed.

Lemma ac_wf_scope : forall E T, WF E T ->
    ac_closed 0 T /\ fv_tt T [<=] dom E.
Proof.
  intros E T H. induction H; simpl in *; try solve [split; [exact I | fsetdec]].
  - split; [exact I |].
    assert (X \in dom E) by (eapply binds_In; eauto).
    fsetdec.
  - destruct IHWF1, IHWF2. split; [auto | fsetdec].
  - pick fresh X for (L \u fv_tt A).
    destruct (H0 X) as [HC HF]; [fsetdec |].
    unfold open_tt in *.
    split.
    + eapply ac_open_closed_inv. exact HC.
    + destruct (ac_open_fv A 0 (typ_fvar X)) as [HI _].
      simpl in HF. fsetdec.
Qed.

Lemma ac_sub_antisym : forall E A B, sub E A B ->
    forall F, sub F B A -> A = B.
Proof.
  intros E A B H.
  induction H as
    [E HE | E X HE HX | E A HE HA
    | E A1 A2 B1 B2 Hdom IHdom Hcod IHcod
    | L A B E Honce IHonce Htwice IHtwice];
    intros F HR; try reflexivity.
  - inversion HR. reflexivity.
  - inversion HR; subst. f_equal; [symmetry; eauto | eauto].
  - inversion HR as [ | | | | K C D F' Hreverse Hreverse_twice]; subst.
    pick fresh X for (L \u K \u fv_tt A \u fv_tt B).
    f_equal. eapply (ac_open_inj A B 0 X); try fsetdec.
    eapply IHonce; [fsetdec |]. apply Hreverse. fsetdec.
Qed.

Fixpoint ac_size (T : typ) : nat :=
  match T with
  | typ_mu A => S (ac_size A)
  | typ_arrow A B => S (ac_size A + ac_size B)
  | _ => 1
  end.

Lemma ac_size_open : forall T k X,
    ac_size (open_tt_rec k (typ_fvar X) T) = ac_size T.
Proof.
  induction T; simpl; intros; try reflexivity.
  - destruct (k === n); reflexivity.
  - rewrite IHT. reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
Qed.

Lemma ac_dom_pair : forall E X,
    X \in domA E -> exists Y, In (X,Y) E \/ In (Y,X) E.
Proof.
  induction E as [|[U V] E IH]; intros X H; simpl in H.
  - fsetdec.
  - assert (X = U \/ X = V \/ X \in domA E) as [-> | [-> | HX]] by fsetdec.
    + exists V. simpl. auto.
    + exists U. simpl. auto.
    + destruct (IH X HX) as [Y HY]. exists Y. simpl. tauto.
Qed.

Lemma ac_wf_amber : forall E T,
    wfe_amber E -> ac_closed 0 T -> fv_tt T [<=] domA E -> wf_amber E T.
Proof.
  intros E T. remember (ac_size T) as n eqn:Hn. revert E T Hn.
  induction n as [n IH] using lt_wf_ind.
  intros E T Hn HE HC HF.
  destruct T; simpl in *.
  - constructor. exact HE.
  - constructor. exact HE.
  - lia.
  - assert (a \in domA E) by fsetdec.
    destruct (ac_dom_pair E a H) as [Y [HY | HY]]; eauto using wfa_fvarl, wfa_fvarr.
  - eapply wfa_rec with (L := domA E). intros X Y HX HY.
    eapply IH with (m := ac_size T).
    + lia.
    + unfold open_tt. symmetry. apply ac_size_open.
    + constructor; try assumption; fsetdec.
    + apply ac_open_closed. exact HC.
    + destruct (ac_open_fv T 0 (typ_fvar X)) as [_ H]. simpl in *. fsetdec.
  - destruct HC. constructor.
    + eapply IH with (m := ac_size T1); try lia; try eassumption. fsetdec.
    + eapply IH with (m := ac_size T2); try lia; try eassumption. fsetdec.
Qed.

Definition ac_context := list (atom * atom * Mode).

Definition ac_iso (G : ac_context) : env :=
  List.map (fun p : (atom * atom * Mode)%type => (fst (fst p), bind_sub)) G.

Definition ac_pairs (G : ac_context) : env_amber :=
  List.map (@fst (atom * atom) Mode) G.

Definition ac_modes (G : ac_context) : env_mode :=
  List.map (@snd (atom * atom) Mode) G.

Fixpoint ac_rename (G : ac_context) (m : Mode) (Z : atom) : atom :=
  match G with
  | ((X, Y), q) :: G' =>
      if Z == X then (if eqMode q m then Y else X) else ac_rename G' m Z
  | nil => Z
  end.

Definition ac_translate G m := ac_inst (fun X => typ_fvar (ac_rename G m X)).

Lemma ac_iso_dom : forall G, dom (ac_iso G) [<=] domA (ac_pairs G).
Proof.
  induction G as [|[[X Y] q] G IH]; simpl; fsetdec.
Qed.

Lemma ac_iso_member : forall G X,
    X \in dom (ac_iso G) -> exists Y q, In (X, Y, q) G.
Proof.
  induction G as [|[[U V] p] G IH]; intros X HX; simpl in HX.
  - fsetdec.
  - assert (X = U \/ X \in dom (ac_iso G)) as [-> | H] by fsetdec.
    + exists V, p. simpl. auto.
    + destruct (IH X H) as [Y [q Hmem]]. exists Y, q. simpl. auto.
Qed.

Lemma ac_pair_member : forall G X Y q,
    In (X, Y, q) G -> In (X, Y) (ac_pairs G).
Proof.
  intros G X Y q H. apply (in_map (@fst (atom * atom) Mode)) in H.
  exact H.
Qed.

Lemma ac_pair_dom : forall G X Y q,
    In (X, Y, q) G -> X \in domA (ac_pairs G) /\ Y \in domA (ac_pairs G).
Proof.
  induction G as [|[[U V] p] G IH]; intros X Y q H; simpl in *;
    [contradiction |].
  destruct H as [H | H].
  - injection H as -> -> ->. split; fsetdec.
  - destruct (IH X Y q H). split; fsetdec.
Qed.

Lemma ac_rename_unbound : forall G m X,
    X \notin dom (ac_iso G) -> ac_rename G m X = X.
Proof.
  induction G as [|[[U V] q] G IH]; simpl; intros m X HX.
  - reflexivity.
  - destruct (X == U); [exfalso; fsetdec |]. apply IH. fsetdec.
Qed.

Lemma ac_rename_member : forall G m X Y q,
    wfe_amber (ac_pairs G) -> In (X, Y, q) G ->
    ac_rename G m X = if eqMode q m then Y else X.
Proof.
  induction G as [|[[U V] p] G IH]; simpl; intros m X Y q HE H.
  - contradiction.
  - inversion HE; subst.
    destruct H as [H | H].
    + injection H as -> -> ->. destruct (X == X); congruence.
    + destruct (X == U) as [-> | Hne].
      * destruct (ac_pair_dom G U Y q H). contradiction.
      * auto.
Qed.

Lemma ac_inst_subst : forall T f X U,
    ac_inst f (subst_tt X U T) =
    ac_inst (fun Z => if Z == X then ac_inst f U else f Z) T.
Proof.
  induction T; simpl; intros; try congruence.
  - destruct (a == X); reflexivity.
  - rewrite IHT. reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
Qed.

Lemma ac_translate_cov : forall G m T,
    wfe_amber (ac_pairs G) ->
    amber_cov (ac_pairs G) (ac_modes G) T m = ac_translate G m T.
Proof.
  induction G as [|[[X Y] q] G IH]; intros m T HE.
  - simpl. symmetry. apply ac_inst_id.
  - inversion HE; subst.
    unfold ac_translate in *. simpl.
    destruct (eqMode q m).
    + rewrite IH, ac_inst_subst by assumption.
      apply ac_inst_ext. intros Z HZ. destruct (Z == X); [|reflexivity].
      simpl. rewrite ac_rename_unbound by (pose proof (ac_iso_dom G); fsetdec).
      reflexivity.
    + rewrite IH by assumption. apply ac_inst_ext.
      intros Z HZ. destruct (Z == X) as [-> | Hne]; [|reflexivity].
      rewrite ac_rename_unbound by (pose proof (ac_iso_dom G); fsetdec).
      reflexivity.
Qed.

Lemma ac_rename_wf : forall G m T,
    wfe_amber (ac_pairs G) -> WF (ac_iso G) T ->
    wf_amber (ac_pairs G) (ac_translate G m T).
Proof.
  intros G m T HE HT. destruct (ac_wf_scope _ _ HT) as [HC HF].
  apply ac_wf_amber; [exact HE | |].
  - apply ac_inst_closed; [simpl; auto | exact HC].
  - apply ac_inst_fv. intros X HX.
    assert (X \in dom (ac_iso G)) as HD by fsetdec.
    destruct (ac_iso_member G X HD) as [Y [q H]].
    rewrite (ac_rename_member G m X Y q HE H).
    destruct (ac_pair_dom G X Y q H).
    destruct (eqMode q m); simpl; fsetdec.
Qed.

Lemma ac_translate_open : forall G m X Y q T,
    X \notin fv_tt T ->
    ac_translate ((X,Y,q)::G) m (open_tt T X) =
    open_tt (ac_translate G m T) (if eqMode q m then Y else X).
Proof.
  intros G m X Y q T HF. unfold ac_translate, open_tt.
  rewrite ac_inst_open by (simpl; auto).
  assert (ac_inst (fun Z => typ_fvar (ac_rename ((X,Y,q)::G) m Z)) T =
          ac_inst (fun Z => typ_fvar (ac_rename G m Z)) T) as ->.
  { apply ac_inst_ext. intros Z HZ. simpl.
    destruct (Z == X); [exfalso; fsetdec | reflexivity]. }
  simpl. destruct (X == X); [destruct (eqMode q m); reflexivity | contradiction].
Qed.

Lemma ac_eqmode_flip : forall m, eqMode (Rules.flip m) m = false.
Proof. destruct m; reflexivity. Qed.

Lemma ac_eqmode_same : forall m, eqMode m m = true.
Proof. destruct m; reflexivity. Qed.

Lemma ac_flip_flip : forall m, Rules.flip (Rules.flip m) = m.
Proof. destruct m; reflexivity. Qed.

Definition ac_variant := Mode -> atom -> typ.

Definition ac_id : ac_variant := fun _ X => typ_fvar X.

Record ac_valid (E : env) (r : ac_variant) : Prop := {
  ac_valid_closed : forall m X, ac_closed 0 (r m X);
  ac_valid_scope : forall m X, X \in dom E -> fv_tt (r m X) [<=] dom E;
  ac_valid_outside : forall m X, X \notin dom E -> r m X = typ_fvar X
}.

Definition ac_checks E m A B (R : list ac_variant) :=
  forall r, In r R ->
    ac_valid E r /\ sub E (ac_inst (r m) A) (ac_inst (r (Rules.flip m)) B).

(* Each recursive variable has a test that distinguishes its two images.
   The test has a forward derivation, so antisymmetry rules out reversal. *)
Definition ac_distinguishes (G : ac_context) (R : list ac_variant) :=
  forall X Y q, In (X,Y,q) G ->
    exists r, In r R /\
      r (Rules.flip q) X <> r q X /\
      forall F, ~ sub F (r q X) (r (Rules.flip q) X).

Lemma ac_id_checks : forall E m A B,
    sub E A B -> ac_checks E m A B (ac_id :: nil).
Proof.
  intros E m A B H r [<- | Hnone]; [|contradiction].
  split.
  - constructor; unfold ac_id; simpl; intros; try exact I; try reflexivity.
    fsetdec.
  - unfold ac_id. rewrite !ac_inst_id. exact H.
Qed.

Definition ac_update (r : ac_variant) X m U V : ac_variant :=
  fun p Z => if Z == X then (if eqMode m p then U else V) else r p Z.

Lemma ac_update_same : forall r X m U V,
    ac_update r X m U V m X = U.
Proof.
  intros. unfold ac_update. destruct (X == X);
    [rewrite ac_eqmode_same; reflexivity | contradiction].
Qed.

Lemma ac_update_flip : forall r X m U V,
    ac_update r X m U V (Rules.flip m) X = V.
Proof. intros; destruct m; unfold ac_update; destruct (X == X);
  [reflexivity | contradiction | reflexivity | contradiction]. Qed.

Lemma ac_valid_extend : forall E r X,
    ac_valid E r -> ac_valid ((X,bind_sub)::E) r.
Proof.
  intros E r X [HC HF HI]. constructor; simpl.
  - exact HC.
  - intros m Z HZ.
    destruct (AtomSetProperties.In_dec Z (dom E)) as [HZ' | HZ'];
      [specialize (HF m Z HZ'); fsetdec | rewrite HI by exact HZ'; simpl; fsetdec].
  - intros m Z HZ. apply HI. fsetdec.
Qed.

Lemma ac_valid_update : forall E r X m U V,
    ac_valid E r ->
    WF ((X,bind_sub)::E) U -> WF ((X,bind_sub)::E) V ->
    ac_valid ((X,bind_sub)::E) (ac_update r X m U V).
Proof.
  intros E r X m U V Hr HU HV.
  destruct (ac_valid_extend E r X Hr) as [HC HF HI].
  destruct (ac_wf_scope _ _ HU) as [HCU HFU].
  destruct (ac_wf_scope _ _ HV) as [HCV HFV].
  constructor; unfold ac_update; intros p Z; destruct (Z == X) as [-> | Hne].
  - destruct (eqMode m p); assumption.
  - auto.
  - destruct (eqMode m p); auto.
  - auto.
  - simpl. intros. exfalso. fsetdec.
  - auto.
Qed.

Lemma ac_inst_fresh : forall E r m T X,
    ac_valid E r -> X \notin dom E -> X \notin fv_tt T ->
    X \notin fv_tt (ac_inst (r m) T).
Proof.
  intros E r m T X [HC HF HI] HE HT.
  assert (fv_tt (ac_inst (r m) T) [<=] (dom E \u fv_tt T)).
  { apply ac_inst_fv. intros Z HZ.
    destruct (AtomSetProperties.In_dec Z (dom E)) as [H | H].
    - specialize (HF m Z H). fsetdec.
    - rewrite HI by exact H. simpl. fsetdec. }
  fsetdec.
Qed.

Definition ac_expand (m : Mode) (X : atom) (A B : typ) (r : ac_variant) :=
  ac_update r X m (open_tt (ac_inst (r m) A) X)
                  (open_tt (ac_inst (r (Rules.flip m)) B) X).

Lemma ac_inst_update_body : forall T r X m U V p,
    X \notin fv_tt T ->
    ac_inst (ac_update r X m U V p) T = ac_inst (r p) T.
Proof.
  intros. apply ac_inst_ext. intros Z HZ. unfold ac_update.
  destruct (Z == X); [exfalso; fsetdec | reflexivity].
Qed.

Lemma ac_expand_open : forall E r m X A B,
    ac_valid ((X,bind_sub)::E) (ac_expand m X A B r) ->
    X \notin fv_tt A -> X \notin fv_tt B ->
    ac_inst (ac_expand m X A B r m) (open_tt A X) =
      open_tt (ac_inst (r m) A) (open_tt (ac_inst (r m) A) X) /\
    ac_inst (ac_expand m X A B r (Rules.flip m)) (open_tt B X) =
      open_tt (ac_inst (r (Rules.flip m)) B) (open_tt (ac_inst (r (Rules.flip m)) B) X).
Proof.
  intros E r m X A B HR HA HB. unfold open_tt.
  split; rewrite ac_inst_open by (apply (ac_valid_closed _ _ HR));
    unfold ac_expand; cbn [ac_inst].
  - rewrite ac_update_same, ac_inst_update_body by exact HA. reflexivity.
  - rewrite ac_update_flip, ac_inst_update_body by exact HB. reflexivity.
Qed.

Definition ac_open_checks E m A B X (r : ac_variant) :=
  let C := ac_inst (r m) A in
  let D := ac_inst (r (Rules.flip m)) B in
  sub ((X,bind_sub)::E) (open_tt C X) (open_tt D X) /\
  sub ((X,bind_sub)::E) (open_tt C (open_tt C X)) (open_tt D (open_tt D X)).

Lemma ac_collect_open : forall R E m A B,
    ac_checks E m (typ_mu A) (typ_mu B) R ->
    exists L, forall X, X \notin L -> forall r, In r R -> ac_open_checks E m A B X r.
Proof.
  induction R as [|r R IH]; intros E m A B H.
  - exists {}. contradiction.
  - destruct (IH E m A B) as [L HL].
    { intros s HS. apply H. right. exact HS. }
    destruct (H r (or_introl eq_refl)) as [_ Hsub].
    inversion Hsub as [ | | | | L' C D F H1 H2]; subst.
    exists (L \u L'). intros X HX s [<- | HS].
    + split; [apply H1 | apply H2]; fsetdec.
    + apply HL; [fsetdec | exact HS].
Qed.

(* Keep the old tests and add a copy of each that instantiates the new
   variable with the corresponding once-opened body on each side. *)
Lemma ac_extend_checks : forall R E m A B X,
    ac_checks E m (typ_mu A) (typ_mu B) R ->
    X \notin dom E -> X \notin fv_tt A -> X \notin fv_tt B ->
    (forall r, In r R -> ac_open_checks E m A B X r) ->
    ac_checks ((X,bind_sub)::E) m (open_tt A X) (open_tt B X)
      (R ++ List.map (ac_expand m X A B) R).
Proof.
  intros R E m A B X HR HX HA HB HO s HS.
  apply in_app_or in HS. destruct HS as [HS | HS].
  - destruct (HR s HS) as [HV _]. split.
    + apply ac_valid_extend. exact HV.
    + unfold open_tt.
      rewrite !ac_inst_open by (apply (ac_valid_closed _ _ HV)).
      cbn [ac_inst]. rewrite !(ac_valid_outside _ _ HV) by exact HX.
      exact (proj1 (HO s HS)).
  - apply in_map_iff in HS. destruct HS as [r [<- Hr]].
    destruct (HR r Hr) as [HV _].
    destruct (HO r Hr) as [H1 H2].
    destruct (ac_sub_wf _ _ _ H1) as [HU HW].
    assert (ac_valid ((X,bind_sub)::E) (ac_expand m X A B r)) as Hexp.
    { apply ac_valid_update; assumption. }
    split; [exact Hexp |].
    destruct (ac_expand_open E r m X A B Hexp HA HB) as [Hleft Hright].
    rewrite Hleft, Hright. exact H2.
Qed.

Lemma ac_types_eq_dec : forall A B : typ, {A = B} + {A <> B}.
Proof. decide equality; first [apply Nat.eq_dec | apply Atom.eq_dec]. Defined.

Lemma ac_agreement : forall R m A B,
    (forall r, In r R -> ac_inst (r m) A = ac_inst (r (Rules.flip m)) B) \/
    (exists r, In r R /\ ac_inst (r m) A <> ac_inst (r (Rules.flip m)) B).
Proof.
  induction R as [|r R IH]; intros m A B.
  - left. contradiction.
  - destruct (ac_types_eq_dec (ac_inst (r m) A) (ac_inst (r (Rules.flip m)) B)).
    + destruct (IH m A B) as [H | [s [Hs Hne]]].
      * left. intros s [<- | Hs]; auto.
      * right. exists s. simpl. auto.
    + right. exists r. simpl. auto.
Qed.

(* Agreement forces the bodies to coincide and excludes every free
   variable whose two images would be renamed differently. *)
Lemma ac_agreement_translate : forall G R m A B,
    In ac_id R -> ac_distinguishes G R ->
    (forall r, In r R -> ac_inst (r m) A = ac_inst (r (Rules.flip m)) B) ->
    ac_translate G m A = ac_translate G (Rules.flip m) B.
Proof.
  intros G R m A B HI HD HA.
  assert (A = B) as <-.
  { specialize (HA ac_id HI). unfold ac_id in HA.
    rewrite !ac_inst_id in HA. exact HA. }
  apply ac_inst_ext. intros X HX.
  destruct (AtomSetProperties.In_dec X (dom (ac_iso G))) as [H | H].
  - destruct (ac_iso_member G X H) as [Y [q Hmem]].
    destruct (HD X Y q Hmem) as [r [Hr [Hne _]]].
    pose proof (ac_inst_eq_fvar A _ _ X (HA r Hr) HX) as Heq.
    destruct m, q; simpl in *; congruence.
  - rewrite !ac_rename_unbound by exact H. reflexivity.
Qed.

Lemma ac_extend_distinguishes : forall G R m A B X Y r,
    ac_distinguishes G R -> In r R ->
    ac_open_checks (ac_iso G) m A B X r ->
    open_tt (ac_inst (r m) A) X <> open_tt (ac_inst (r (Rules.flip m)) B) X ->
    ac_distinguishes ((X,Y,Rules.flip m)::G) (R ++ List.map (ac_expand m X A B) R).
Proof.
  intros G R m A B X Y r HD Hr HO Hne U V q [H | H].
  - injection H as <- <- <-.
    exists (ac_expand m X A B r). split.
    + apply in_or_app. right. apply in_map. exact Hr.
    + unfold ac_expand. rewrite ac_flip_flip, ac_update_same, ac_update_flip.
      split; [exact Hne |].
      intros F Hrev. apply Hne.
      eapply ac_sub_antisym; [exact (proj1 HO) | exact Hrev].
  - destruct (HD U V q H) as [s [Hs Hdist]].
    exists s. split; [apply in_or_app; left; exact Hs | exact Hdist].
Qed.

Lemma ac_complete : forall E A B, sub E A B ->
    forall G m R,
      E = ac_iso G ->
      wfe_amber (ac_pairs G) ->
      In ac_id R ->
      ac_distinguishes G R ->
      ac_checks E m A B R ->
      sub_amber (ac_pairs G) (ac_translate G m A) (ac_translate G (Rules.flip m) B).
Proof.
  intros E A B H.
  induction H as
    [ E Henv
    | E X Henv Hbind
    | E A Henv Hwf
    | E A1 A2 B1 B2 Hdom IHdom Hcod IHcod
    | L A B E Honce IHonce Htwice IHtwice ];
    intros G m R HE HW HI HD HC; subst E.
  - apply sam_nat. exact HW.
  - assert (X \in dom (ac_iso G)) as HX by (eapply binds_In; eauto).
    destruct (ac_iso_member G X HX) as [Y [q Hmem]].
    destruct (HD X Y q Hmem) as [r [Hr [_ Hrev]]].
    destruct (HC r Hr) as [_ Hsub].
    assert (q = Rules.flip m) as ->.
    { destruct m, q; try reflexivity; exfalso; eapply Hrev; exact Hsub. }
    unfold ac_translate. simpl.
    rewrite !(ac_rename_member _ _ _ _ _ HW Hmem), ac_eqmode_flip, ac_eqmode_same.
    apply sam_fvar; [eapply ac_pair_member; eassumption | exact HW].
  - apply sam_top; [apply ac_rename_wf |]; assumption.
  - apply sam_arrow.
    + pose proof (IHdom G (Rules.flip m) R eq_refl HW HI HD) as IH.
      rewrite ac_flip_flip in IH. apply IH.
      intros r Hr. destruct (HC r Hr) as [HV Hsub].
      split; [exact HV |]. rewrite ac_flip_flip.
      inversion Hsub. assumption.
    + apply (IHcod G m R); try assumption; [reflexivity |].
      intros r Hr. destruct (HC r Hr) as [HV Hsub].
      split; [exact HV |]. inversion Hsub. assumption.
  - change (sub_amber (ac_pairs G)
      (typ_mu (ac_translate G m A)) (typ_mu (ac_translate G (Rules.flip m) B))).
    destruct (ac_agreement R m A B) as [Hagree | [r [Hr Hne]]].
    + rewrite <- (ac_agreement_translate G R m A B HI HD Hagree).
      apply sam_refl; [exact HW |].
      apply (ac_rename_wf G m (typ_mu A)); [exact HW |].
      apply (proj1 (ac_sub_wf _ _ _ (sa_rec L A B (ac_iso G) Honce Htwice))).
    + destruct (ac_collect_open _ _ _ _ _ HC) as [K HK].
      eapply sam_rec with (L := L \u K \u domA (ac_pairs G) \u fv_tt A \u fv_tt B).
      intros X Y HX HY.
      assert (X \notin domA (ac_pairs G)) as HXd by (clear - HX; fsetdec).
      assert (Y \notin {{X}} \u domA (ac_pairs G)) as HYd by (clear - HY; fsetdec).
      assert (X \notin dom (ac_iso G)) as HXi by
        (clear - HXd; pose proof (ac_iso_dom G); fsetdec).
      assert (X \notin fv_tt A) as HXA by (clear - HX; fsetdec).
      assert (X \notin fv_tt B) as HXB by (clear - HX; fsetdec).
      assert (X \notin L) as HXL by (clear - HX; fsetdec).
      assert (forall s, In s R -> ac_open_checks (ac_iso G) m A B X s) as HO
        by (apply HK; clear - HX; fsetdec).
      pose proof (proj1 (HC r Hr)) as HV.
      assert (open_tt (ac_inst (r m) A) X <>
              open_tt (ac_inst (r (Rules.flip m)) B) X) as Hopen.
      { intro Heq. apply Hne.
        eapply ac_open_inj; [eapply ac_inst_fresh | eapply ac_inst_fresh | exact Heq];
          eassumption. }
      pose proof (IHonce X HXL ((X,Y,Rules.flip m)::G) m
        (R ++ List.map (ac_expand m X A B) R) eq_refl) as IH.
      simpl in IH.
      rewrite (ac_translate_open G m X Y (Rules.flip m) A HXA),
              (ac_translate_open G (Rules.flip m) X Y (Rules.flip m) B HXB),
              ac_eqmode_flip, ac_eqmode_same in IH.
      apply IH.
      * constructor; assumption.
      * apply in_or_app. left. exact HI.
      * eapply ac_extend_distinguishes; [exact HD | exact Hr | apply HO | exact Hopen].
        exact Hr.
      * apply ac_extend_checks; assumption.
Qed.

Theorem amber_complete: forall  A B,
    sub nil A B ->
    sub_amber nil (amber_cov nil nil A Neg) (amber_cov nil nil B Pos) .
Proof.
  intros A B H.
  assert (wfe_amber (ac_pairs nil)) as HW by constructor.
  change (sub_amber (ac_pairs nil)
    (amber_cov (ac_pairs nil) (ac_modes nil) A Neg)
    (amber_cov (ac_pairs nil) (ac_modes nil) B (Rules.flip Neg))).
  rewrite !ac_translate_cov by exact HW.
  eapply ac_complete with (R := ac_id :: nil).
  - exact H.
  - reflexivity.
  - exact HW.
  - simpl. auto.
  - intros X Y q HF. contradiction.
  - apply ac_id_checks. exact H.
Qed.
