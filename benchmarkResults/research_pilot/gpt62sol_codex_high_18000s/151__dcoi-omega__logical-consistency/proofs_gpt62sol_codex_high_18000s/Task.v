Require Import imports conv par geq typing.
From Stdlib Require Import Lia PeanoNat.

Module consistency
  (Import lattice : Lattice)
  (Import syntax : syntax_sig lattice)
  (Import par : par_sig lattice syntax)
  (Import ieq : geq_sig lattice syntax)
  (Import conv : conv_sig lattice syntax par ieq)
  (Import typing : typing_sig lattice syntax par ieq conv).

Local Open Scope lattice_scope.
Local Open Scope subst_scope.
Local Notation "a ≤ₗ b" := (a ⊆ b) (at level 70).

Local Lemma level_refl k : k ≤ₗ k.
Proof. apply meet_idempotent. Qed.
Local Lemma level_trans j k l : j ≤ₗ k -> k ≤ₗ l -> j ≤ₗ l.
Proof.
  intros H K.
  change (meet j l = j).
  rewrite <- H at 1. now rewrite meet_associative K.
Qed.

Local Definition visible j k := T_eqb (meet j k) j.
Local Lemma visibleP j k : reflect (j ≤ₗ k) (visible j k).
Proof. apply T_eqdec. Qed.

Local Hint Constructors Par rtc : core.

(* Substitution and renaming are used both before and after taking a view. *)
Local Lemma ren_ext r q a :
  (forall i, r i = q i) -> ren_tm r a = ren_tm q a.
Proof.
  revert r q; induction a; intros r q H; simpl; f_equal;
    eauto; (apply IHa || apply IHa2); intros [|[|i]];
    cbv beta delta [upRen_tm_tm up_ren scons unscoped.funcomp axioms.funcomp] iota;
    now rewrite ?H.
Qed.
Local Lemma sub_ext s q a :
  (forall i, s i = q i) -> a[s] = a[q].
Proof.
  revert s q; induction a; intros s q H; simpl; f_equal; eauto;
    (eapply IHa || eapply IHa2); intros [|[|i]];
    cbv beta delta [up_tm_tm scons unscoped.funcomp axioms.funcomp] iota; now rewrite ?H.
Qed.
Local Lemma ren_comp r q a :
  (a⟨r⟩)⟨q⟩ = a⟨r >> q⟩.
Proof.
  revert r q; induction a; intros r q; simpl; f_equal; eauto;
    rewrite ?IHa ?IHa2;
    apply ren_ext; intros [|[|i]]; reflexivity.
Qed.
Local Lemma sub_ren r s a :
  (a⟨r⟩)[s] = a[r >> s].
Proof.
  revert r s; induction a; intros r s; simpl; f_equal; eauto;
    rewrite ?IHa ?IHa2;
    apply sub_ext; intros [|[|i]]; reflexivity.
Qed.
Local Lemma ren_sub r s a :
  (a[s])⟨r⟩ = a[s >> ren_tm r].
Proof.
  revert r s; induction a; intros r s; simpl; f_equal; eauto;
    rewrite ?IHa ?IHa2;
    apply sub_ext; intros [|[|i]]; cbv beta delta [up_tm_tm upRen_tm_tm up_ren scons unscoped.funcomp axioms.funcomp] iota; cbn -[upRen_tm_tm];
    rewrite ?ren_comp; apply ren_ext || reflexivity; reflexivity.
Qed.
Local Lemma sub_comp s q a :
  (a[s])[q] = a[s >> subst_tm q].
Proof.
  revert s q; induction a; intros s q; simpl; f_equal; eauto;
    rewrite ?IHa ?IHa2;
    apply sub_ext; intros [|[|i]]; cbv beta delta [up_tm_tm scons unscoped.funcomp axioms.funcomp] iota; cbn -[up_tm_tm];
    repeat rewrite ?sub_ren ?ren_sub; reflexivity.
Qed.
Local Lemma sub_ids a : a[var_tm] = a.
Proof.
  induction a; simpl; f_equal; auto;
    (etransitivity; [apply sub_ext | eassumption]);
    intros [|[|i]]; reflexivity.
Qed.
Local Lemma sub_up1 (s : nat -> tm) a b :
  (a[up_tm_tm s])[b..] = a[b .: s].
Proof.
  rewrite sub_comp. apply sub_ext. intros [|i]; cbv beta delta [up_tm_tm scons unscoped.funcomp axioms.funcomp] iota; auto.
  rewrite sub_ren. apply sub_ids.
Qed.
Local Lemma sub_up2 (s : nat -> tm) a b c :
  (a[up_tm_tm (up_tm_tm s)])[b .: c ..] = a[b .: (c .: s)].
Proof.
  rewrite sub_comp. apply sub_ext. intros [|[|i]]; cbv beta delta [up_tm_tm scons unscoped.funcomp axioms.funcomp] iota; auto.
  repeat rewrite sub_ren. apply sub_ids.
Qed.
Local Lemma sub_single (s : nat -> tm) a b :
  (a[b..])[s] = a[b[s] .: s].
Proof. rewrite sub_comp. apply sub_ext. now intros [|i]. Qed.
Local Lemma sub_double (s : nat -> tm) a b c :
  (a[b .: c ..])[s] = a[b[s] .: (c[s] .: s)].
Proof. rewrite sub_comp. apply sub_ext. now intros [|[|i]]. Qed.

Local Lemma par_refl a : a ⇒ a.
Proof. induction a; now constructor. Qed.

Local Lemma ren_single r a b :
  (a[b..])⟨r⟩ = (a⟨upRen_tm_tm r⟩)[(b⟨r⟩)..].
Proof. rewrite ren_sub sub_ren. apply sub_ext. now intros [|i]. Qed.
Local Lemma ren_double r a b c :
  (a[b .: c ..])⟨r⟩ =
    (a⟨upRen_tm_tm (upRen_tm_tm r)⟩)[(b⟨r⟩) .: (c⟨r⟩)..].
Proof. rewrite ren_sub sub_ren. apply sub_ext. now intros [|[|i]]. Qed.

Local Lemma par_ren r a b : a ⇒ b -> a⟨r⟩ ⇒ b⟨r⟩.
Proof.
  intro H; revert r; induction H; intro r; simpl;
    rewrite ?ren_single ?ren_double; simpl; eauto using Par.
Qed.

Local Lemma par_up s q :
  (forall i, s i ⇒ q i) -> forall i, up_tm_tm s i ⇒ up_tm_tm q i.
Proof. intros H [|i]; simpl; eauto using par_ren. Qed.
Local Lemma par_sub a b s q :
  a ⇒ b -> (forall i, s i ⇒ q i) -> a[s] ⇒ b[q].
Proof.
  intros H; revert s q; induction H; intros s q Hs; simpl;
    try solve [apply Hs | constructor; eauto 6 using par_up].
  - rewrite sub_single -sub_up1. eauto using par_up.
  - rewrite sub_double -sub_up2. simpl. econstructor; eauto 8 using par_up.
  - rewrite sub_double -sub_up2. simpl. econstructor; eauto 8 using par_up.
Qed.

Local Definition label_eq (j k : T) : {j = k} + {j <> k}.
Proof. destruct (T_eqdec j k); auto. Defined.

(* Parallel reduction is confluent on the raw syntax. *)
Local Fixpoint develop (a : tm) : tm :=
  match a with
  | var_tm i => var_tm i
  | tAbs k b => tAbs k (develop b)
  | tApp f k a =>
      match f with
      | tAbs j b =>
          if label_eq j k then (develop b)[(develop a)..]
          else tApp (tAbs j (develop b)) k (develop a)
      | _ => tApp (develop f) k (develop a)
      end
  | tPi k A B => tPi k (develop A) (develop B)
  | tUniv n => tUniv n
  | tVoid => tVoid
  | tAbsurd a => tAbsurd (develop a)
  | tEq k a b => tEq k (develop a) (develop b)
  | tJ k a p =>
      match p with
      | tRefl => develop a
      | _ => tJ k (develop a) (develop p)
      end
  | tRefl => tRefl
  | tSig k A B => tSig k (develop A) (develop B)
  | tPack k a b => tPack k (develop a) (develop b)
  | tLet j k p b =>
      match p with
      | tPack i a c =>
          if label_eq i j then (develop b)[(develop c) .: (develop a)..]
          else tLet j k (tPack i (develop a) (develop c)) (develop b)
      | _ => tLet j k (develop p) (develop b)
      end
  | tZero => tZero
  | tSuc n => tSuc (develop n)
  | tInd k a b n =>
      match n with
      | tZero => develop a
      | tSuc n =>
          (develop b)[tInd k (develop a) (develop b) (develop n) .: (develop n)..]
      | _ => tInd k (develop a) (develop b) (develop n)
      end
  | tNat => tNat
  | tTT => tTT
  | tSeq k a b =>
      match a with
      | tTT => develop b
      | _ => tSeq k (develop a) (develop b)
      end
  | tUnit => tUnit
  end.

Local Ltac inv_par H := inversion H; subst; clear H.

Local Lemma par_triangle a b : a ⇒ b -> b ⇒ develop a.
Proof.
  intro H; induction H; simpl; try solve [assumption | constructor; assumption || constructor].
  - destruct a0; try solve [constructor; auto].
    destruct (label_eq t ℓ0) as [->|]; inv_par H; inv_par IHPar1; simpl; auto.
  - destruct (label_eq ℓ0 ℓ0) as [Heq|Hneq]; [|contradiction].
    simpl. apply par_sub; auto. intros [|i]; simpl; auto.
  - destruct p0; try solve [constructor; auto]. inv_par H0; auto.
  - destruct a0; try solve [constructor; auto].
    destruct (label_eq t ℓ0) as [->|]; inv_par H; inv_par IHPar1; simpl; auto.
  - destruct (label_eq ℓ0 ℓ0) as [Heq|Hneq]; [|contradiction].
    simpl. apply par_sub; auto. intros [|[|i]]; simpl; auto.
  - destruct c0; try solve [constructor; auto].
    + inv_par H1; auto.
    + inv_par H1. inv_par IHPar3. auto.
  - apply par_sub; auto. intros [|[|i]]; simpl; auto.
  - destruct a0; try solve [constructor; auto]. inv_par H; auto.
Qed.

Local Lemma rtc_trans a b c : a ⇒* b -> b ⇒* c -> a ⇒* c.
Proof. intros H K; induction H; eauto. Qed.

Local Lemma par_rtc a b : a ⇒ b -> a ⇒* b.
Proof. eauto. Qed.

Local Lemma par_strip a b c : a ⇒ b -> a ⇒* c ->
  exists d, b ⇒* d /\ c ⇒ d.
Proof.
  intros H K; revert b H; induction K as [a|a c e H K IH]; intros b J.
  - eauto.
  - destruct (IH (develop a)) as [d [H1 H2]]; eauto using par_triangle.
Qed.

Local Lemma par_confluent a b c : a ⇒* b -> a ⇒* c ->
  exists d, b ⇒* d /\ c ⇒* d.
Proof.
  intros H; revert c; induction H as [a|a b e H K IH]; intros c J.
  - eauto.
  - destruct (par_strip _ _ _ H J) as [d [H1 H2]].
    destruct (IH _ H1) as [f [H3 H4]].
    exists f. split; eauto.
Qed.

Local Definition joinable a b := exists c, a ⇒* c /\ b ⇒* c.
Local Lemma join_refl a : joinable a a.
Proof. exists a; auto. Qed.
Local Lemma join_sym a b : joinable a b -> joinable b a.
Proof. intros [c [? ?]]; exists c; auto. Qed.
Local Lemma join_trans a b c : joinable a b -> joinable b c -> joinable a c.
Proof.
  intros [d [H K]] [e [L M]].
  destruct (par_confluent _ _ _ K L) as [f [? ?]].
  exists f; eauto using rtc_trans.
Qed.
Local Lemma join_rtc a b : a ⇒* b -> joinable a b.
Proof. exists b; auto. Qed.
Local Lemma join_par a b : a ⇒ b -> joinable a b.
Proof. auto using join_rtc, par_rtc. Qed.

Local Lemma rtc_map (F : tm -> tm) :
  (forall a b, a ⇒ b -> F a ⇒ F b) -> forall a b, a ⇒* b -> F a ⇒* F b.
Proof. intros H a b Hred; induction Hred; eauto. Qed.
Local Lemma rtc_sub a b s : a ⇒* b -> a[s] ⇒* b[s].
Proof. apply rtc_map. eauto using par_sub, par_refl. Qed.

Local Lemma rtc_Abs k a a' :
  a ⇒* a' -> tAbs k a ⇒* tAbs k a'.
Proof.
  intros Ha.
  exact (rtc_map (fun x => tAbs k x) (ltac:(intros; constructor; auto using par_refl)) _ _ Ha).
Qed.

Local Lemma rtc_App a k b a' b' :
  a ⇒* a' -> b ⇒* b' -> tApp a k b ⇒* tApp a' k b'.
Proof.
  intros Ha Hb.
  eapply rtc_trans with (b := tApp a' k b).
    exact (rtc_map (fun x => tApp x k b) (ltac:(intros; constructor; auto using par_refl)) _ _ Ha).
  exact (rtc_map (fun x => tApp a' k x) (ltac:(intros; constructor; auto using par_refl)) _ _ Hb).
Qed.

Local Lemma rtc_Pi k a b a' b' :
  a ⇒* a' -> b ⇒* b' -> tPi k a b ⇒* tPi k a' b'.
Proof.
  intros Ha Hb.
  eapply rtc_trans with (b := tPi k a' b).
    exact (rtc_map (fun x => tPi k x b) (ltac:(intros; constructor; auto using par_refl)) _ _ Ha).
  exact (rtc_map (fun x => tPi k a' x) (ltac:(intros; constructor; auto using par_refl)) _ _ Hb).
Qed.

Local Lemma rtc_Absurd a a' :
  a ⇒* a' -> tAbsurd a ⇒* tAbsurd a'.
Proof.
  intros Ha.
  exact (rtc_map (fun x => tAbsurd x) (ltac:(intros; constructor; auto using par_refl)) _ _ Ha).
Qed.

Local Lemma rtc_Eq k a b a' b' :
  a ⇒* a' -> b ⇒* b' -> tEq k a b ⇒* tEq k a' b'.
Proof.
  intros Ha Hb.
  eapply rtc_trans with (b := tEq k a' b).
    exact (rtc_map (fun x => tEq k x b) (ltac:(intros; constructor; auto using par_refl)) _ _ Ha).
  exact (rtc_map (fun x => tEq k a' x) (ltac:(intros; constructor; auto using par_refl)) _ _ Hb).
Qed.

Local Lemma rtc_J k a b a' b' :
  a ⇒* a' -> b ⇒* b' -> tJ k a b ⇒* tJ k a' b'.
Proof.
  intros Ha Hb.
  eapply rtc_trans with (b := tJ k a' b).
    exact (rtc_map (fun x => tJ k x b) (ltac:(intros; constructor; auto using par_refl)) _ _ Ha).
  exact (rtc_map (fun x => tJ k a' x) (ltac:(intros; constructor; auto using par_refl)) _ _ Hb).
Qed.

Local Lemma rtc_Sig k a b a' b' :
  a ⇒* a' -> b ⇒* b' -> tSig k a b ⇒* tSig k a' b'.
Proof.
  intros Ha Hb.
  eapply rtc_trans with (b := tSig k a' b).
    exact (rtc_map (fun x => tSig k x b) (ltac:(intros; constructor; auto using par_refl)) _ _ Ha).
  exact (rtc_map (fun x => tSig k a' x) (ltac:(intros; constructor; auto using par_refl)) _ _ Hb).
Qed.

Local Lemma rtc_Pack k a b a' b' :
  a ⇒* a' -> b ⇒* b' -> tPack k a b ⇒* tPack k a' b'.
Proof.
  intros Ha Hb.
  eapply rtc_trans with (b := tPack k a' b).
    exact (rtc_map (fun x => tPack k x b) (ltac:(intros; constructor; auto using par_refl)) _ _ Ha).
  exact (rtc_map (fun x => tPack k a' x) (ltac:(intros; constructor; auto using par_refl)) _ _ Hb).
Qed.

Local Lemma rtc_Let k j a b a' b' :
  a ⇒* a' -> b ⇒* b' -> tLet k j a b ⇒* tLet k j a' b'.
Proof.
  intros Ha Hb.
  eapply rtc_trans with (b := tLet k j a' b).
    exact (rtc_map (fun x => tLet k j x b) (ltac:(intros; constructor; auto using par_refl)) _ _ Ha).
  exact (rtc_map (fun x => tLet k j a' x) (ltac:(intros; constructor; auto using par_refl)) _ _ Hb).
Qed.

Local Lemma rtc_Suc a a' :
  a ⇒* a' -> tSuc a ⇒* tSuc a'.
Proof.
  intros Ha.
  exact (rtc_map (fun x => tSuc x) (ltac:(intros; constructor; auto using par_refl)) _ _ Ha).
Qed.

Local Lemma rtc_Ind k a b c a' b' c' :
  a ⇒* a' -> b ⇒* b' -> c ⇒* c' -> tInd k a b c ⇒* tInd k a' b' c'.
Proof.
  intros Ha Hb Hc.
  eapply rtc_trans with (b := tInd k a' b c).
    exact (rtc_map (fun x => tInd k x b c) (ltac:(intros; constructor; auto using par_refl)) _ _ Ha).
  eapply rtc_trans with (b := tInd k a' b' c).
    exact (rtc_map (fun x => tInd k a' x c) (ltac:(intros; constructor; auto using par_refl)) _ _ Hb).
  exact (rtc_map (fun x => tInd k a' b' x) (ltac:(intros; constructor; auto using par_refl)) _ _ Hc).
Qed.

Local Lemma rtc_Seq k a b a' b' :
  a ⇒* a' -> b ⇒* b' -> tSeq k a b ⇒* tSeq k a' b'.
Proof.
  intros Ha Hb.
  eapply rtc_trans with (b := tSeq k a' b).
    exact (rtc_map (fun x => tSeq k x b) (ltac:(intros; constructor; auto using par_refl)) _ _ Ha).
  exact (rtc_map (fun x => tSeq k a' x) (ltac:(intros; constructor; auto using par_refl)) _ _ Hb).
Qed.

Local Hint Resolve rtc_Abs rtc_App rtc_Pi rtc_Absurd rtc_Eq rtc_J rtc_Sig rtc_Pack rtc_Let rtc_Suc rtc_Ind rtc_Seq : core.

Local Lemma join_map (F : tm -> tm) :
  (forall a b, a ⇒ b -> F a ⇒ F b) ->
  forall a b, joinable a b -> joinable (F a) (F b).
Proof. intros H a b [c [? ?]]; exists (F c); eauto using rtc_map. Qed.

(* A view keeps the arguments that the observer can distinguish. *)
Local Fixpoint view (k : T) (a : tm) : tm :=
  match a with
  | var_tm i => var_tm i
  | tAbs j b => tAbs j (view k b)
  | tApp f j a => tApp (view k f) j (if visible j k then view k a else tRefl)
  | tPi j A B => tPi j (view k A) (view k B)
  | tUniv n => tUniv n
  | tVoid => tVoid
  | tAbsurd _ => tAbsurd tRefl
  | tEq j a b => tEq j (view k a) (view k b)
  | tJ j a b => tJ j (view k a) (view k b)
  | tRefl => tRefl
  | tSig j A B => tSig j (view k A) (view k B)
  | tPack j a b => tPack j (if visible j k then view k a else tRefl) (view k b)
  | tLet i j a b => tLet i j (view k a) (view k b)
  | tZero => tZero
  | tSuc n => tSuc (view k n)
  | tInd j a b n => tInd j (view k a) (view k b) (view k n)
  | tNat => tNat
  | tTT => tTT
  | tSeq j a b => tSeq j (view k a) (view k b)
  | tUnit => tUnit
  end.

Local Lemma view_ren k r a : view k (a⟨r⟩) = (view k a)⟨r⟩.
Proof.
  revert r; induction a; intros r; simpl;
    try destruct (visible t k); f_equal; auto.
Qed.
Local Lemma view_sub k s a : view k a[s] = (view k a)[s >> view k].
Proof.
  revert s; induction a; intros s; simpl;
    try destruct (visible t k); f_equal; auto;
    rewrite ?IHa ?IHa2;
    apply sub_ext; intros [|[|i]];
    cbv beta delta [up_tm_tm scons unscoped.funcomp axioms.funcomp] iota;
    cbn -[up_tm_tm]; now rewrite ?view_ren.
Qed.
Local Lemma view_single k a b : view k a[b..] = (view k a)[(view k b)..].
Proof. rewrite view_sub. apply sub_ext. now intros [|i]. Qed.
Local Lemma view_double k a b c :
  view k a[b .: c ..] = (view k a)[(view k b) .: (view k c)..].
Proof. rewrite view_sub. apply sub_ext. now intros [|[|i]]. Qed.
Local Lemma view_down j k a : j ≤ₗ k -> view j (view k a) = view j a.
Proof.
  intros H; induction a; simpl; f_equal; auto;
    destruct (visibleP t j) as [Hj|Hj]; auto;
    destruct (visibleP t k); simpl; eauto using level_trans;
    exfalso; eauto using level_trans.
Qed.

(* Scoping a view checks the visible variables and the levels of equality types. *)
Local Definition under k (P : nat -> Prop) j :=
  fun i => match i with 0 => j ≤ₗ k | S n => P n end.
Local Fixpoint good k (P : nat -> Prop) a : Prop :=
  match a with
  | var_tm i => P i
  | tAbs j a => good k (under k P j) a
  | tApp a _ b => good k P a /\ good k P b
  | tPi j A B | tSig j A B => good k P A /\ good k (under k P j) B
  | tEq j a b => j ≤ₗ k /\ good k P a /\ good k P b
  | tJ _ a b | tPack _ a b | tSeq _ a b => good k P a /\ good k P b
  | tLet i j a b => good k P a /\ good k (under k (under k P i) j) b
  | tInd j a b n => good k P a /\ good k (under k (under k P j) j) b /\ good k P n
  | tSuc a | tAbsurd a => good k P a
  | _ => True
  end.

Local Ltac split_hyps :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
Local Lemma good_ren k P Q r a :
  good k P a -> (forall i, P i -> Q (r i)) -> good k Q (a⟨r⟩).
Proof.
  revert P Q r; induction a; intros P Q r H R; simpl in *;
    split_hyps; repeat split; eauto;
    (eapply IHa || eapply IHa2); try eassumption;
    intros [|[|i]]; simpl; auto.
Qed.
Local Lemma good_up k P Q s :
  (forall i, P i -> good k Q (s i)) ->
  forall j i, under k P j i -> good k (under k Q j) (up_tm_tm s i).
Proof.
  intros H j [|i] K; simpl in *; auto.
  eapply good_ren; eauto.
Qed.
Local Lemma good_sub k P Q s a :
  good k P a -> (forall i, P i -> good k Q (s i)) -> good k Q a[s].
Proof.
  revert P Q s; induction a; intros P Q s H R; simpl in *;
    split_hyps; repeat split; eauto 6 using good_up.
Qed.
Local Lemma good_sub_agree k P a s q :
  good k P a -> (forall i, P i -> s i = q i) -> a[s] = a[q].
Proof.
  revert P s q; induction a; intros P s q H R; simpl in *;
    split_hyps; f_equal; eauto;
    (eapply IHa || eapply IHa2); try eassumption;
    intros [|[|i]]; cbv beta delta [under up_tm_tm scons unscoped.funcomp axioms.funcomp] iota;
    intro Hi; now rewrite ?(R _ Hi).
Qed.

Local Lemma good_par k P a b : a ⇒ b -> good k P a -> good k P b.
Proof.
  intro H; revert P; induction H; intros P K; simpl in *;
    split_hyps; repeat split; eauto;
    eapply good_sub; try solve [eauto];
    intros [|[|i]] Hscope; simpl in *; repeat split; eauto.
Qed.

Local Fixpoint allowed (k : T) (Ξ : econtext) (i : nat) : Prop :=
  match Ξ, i with
  | nil, _ => False
  | j :: _, 0 => j ≤ₗ k
  | _ :: Ξ, S i => allowed k Ξ i
  end.
Local Definition well (k : T) (Ξ : econtext) a := good k (allowed k Ξ) (view k a).

Local Lemma view_par k P a b :
  a ⇒ b -> good k P (view k a) -> view k a ⇒ view k b.
Proof.
  intro H; revert P; induction H; intros P K; simpl in *;
    try solve [split_hyps; eauto using par_refl];
    try solve [destruct (visible ℓ0 k); simpl in *; split_hyps; eauto using par_refl].
  - rewrite view_single.
    destruct (visibleP ℓ0 k) as [Hv|Hv]; simpl in *; split_hyps.
    + eapply P_AppAbs; eauto.
    + erewrite (good_sub_agree k (under k P ℓ0) (view k a0) _ (tRefl..)).
      * eapply P_AppAbs; eauto.
      * eapply (good_par _ _ (view k a)); eauto.
      * intros [|i] Hi; simpl in *; tauto.
  - destruct (visible ℓ k); simpl in *; split_hyps; eauto.
  - rewrite view_double.
    destruct (visibleP ℓ0 k) as [Hv|Hv]; simpl in *; split_hyps.
    + eapply P_LetPack; eauto.
    + erewrite (good_sub_agree k (under k (under k P ℓ0) ℓ1) (view k c1) _ ((view k b1) .: tRefl ..)).
      * eapply P_LetPack; eauto.
      * eapply (good_par _ _ (view k c0)); eauto.
      * intros [|[|i]] Hi; simpl in *; tauto.
  - rewrite view_double. simpl. split_hyps. eapply P_IndSuc; eauto.
Qed.

Local Lemma well_par k Ξ a b : a ⇒ b -> well k Ξ a -> well k Ξ b.
Proof. unfold well; eauto using view_par, good_par. Qed.
Local Lemma well_rtc k Ξ a b : a ⇒* b -> well k Ξ a -> well k Ξ b.
Proof. intros H K; induction H; eauto using well_par. Qed.
Local Lemma view_rtc k Ξ a b : a ⇒* b -> well k Ξ a -> view k a ⇒* view k b.
Proof.
  intros H; induction H; intro K; [constructor|].
  eapply rtc_l.
  - eapply view_par; eassumption.
  - apply IHrtc. eapply well_par; eassumption.
Qed.

Local Lemma allowed_lookup k Ξ i j :
  elookup i Ξ j -> j ≤ₗ k -> allowed k Ξ i.
Proof.
  unfold elookup. revert i; induction Ξ; intros [|i] H K;
    simpl in *; try discriminate; eauto.
  now injection H as ->.
Qed.

Local Lemma ieq_views Ξ k :
  (forall a b, IEq Ξ k a b ->
    well k Ξ a /\ well k Ξ b /\ view k a = view k b) /\
  (forall j a b, GIEq Ξ k j a b ->
    if visible j k then well k Ξ a /\ well k Ξ b /\ view k a = view k b else True).
Proof.
  apply (IEq_mutual
    (fun Ξ k a b _ => well k Ξ a /\ well k Ξ b /\ view k a = view k b)
    (fun Ξ k j a b _ =>
      if visible j k then well k Ξ a /\ well k Ξ b /\ view k a = view k b else True));
    unfold well; intros; simpl in *; split_hyps;
    try solve [repeat split; congruence || eauto using allowed_lookup].
  - destruct (visible ℓ0 ℓ); split_hyps; repeat split; congruence || auto.
  - destruct (visible ℓ0 ℓ); split_hyps; repeat split; congruence || auto.
  - destruct (visibleP ℓ0 ℓ); tauto.
  - destruct (visibleP ℓ0 ℓ); tauto.
Qed.

Local Lemma lookup_label Γ i j A : lookup i Γ j A -> elookup i (c2e Γ) j.
Proof. intro H; induction H; assumption || reflexivity. Qed.

Local Lemma typing_well :
  (forall Γ j a A, Γ ⊢ a ; j ∈ A -> forall k, j ≤ₗ k -> well k (c2e Γ) a) /\
  (forall Γ, ⊢ Γ -> True).
Proof.
  apply (wt_mutual
    (fun Γ j a A _ => forall k, j ≤ₗ k -> well k (c2e Γ) a)
    (fun _ _ => True)); unfold well; intros; simpl in *;
    try solve [repeat split; eauto 6 using level_trans].
  - eapply allowed_lookup; eauto using lookup_label, level_trans.
  - destruct (visibleP ℓ0 k); simpl; split; eauto.
  - destruct (visibleP ℓ0 k); simpl; split; eauto.
Qed.

Local Definition valid j (a : tm) := forall k, j ≤ₗ k -> well k nil a.
Local Definition well_env Ξ (s : nat -> tm) :=
  forall k i, allowed k Ξ i -> well k nil (s i).

Local Lemma well_sub Ξ k a s :
  well k Ξ a ->
  (forall i, allowed k Ξ i -> well k nil (s i)) ->
  well k nil a[s].
Proof. unfold well; rewrite view_sub; eauto using good_sub. Qed.
Local Lemma valid_sub Γ j a A s :
  Γ ⊢ a ; j ∈ A -> well_env (c2e Γ) s -> valid j a[s].
Proof.
  intros H K k L. apply well_sub with (Ξ := c2e Γ); auto.
  eapply (proj1 typing_well); eauto.
Qed.
Local Lemma valid_rtc j a b : a ⇒* b -> valid j a -> valid j b.
Proof. intros H K k L; eapply well_rtc; eauto. Qed.

(* Related terms reach scoped representatives whose views have a common reduct. *)
Local Definition observed k Ξ a b := exists a' b',
  a ⇒* a' /\ b ⇒* b' /\ well k Ξ a' /\ well k Ξ b' /\
  joinable (view k a') (view k b').

Local Lemma observed_refl k Ξ a : well k Ξ a -> observed k Ξ a a.
Proof. intros; exists a,a; repeat split; eauto using join_refl. Qed.
Local Lemma observed_move k Ξ a b c d :
  joinable a c -> joinable b d -> observed k Ξ a b -> observed k Ξ c d.
Proof.
  intros Ha Hb [a' [b' [H1 [H2 [H3 [H4 H5]]]]]].
  destruct (join_trans _ _ _ (join_sym _ _ (join_rtc _ _ H1)) Ha) as [a'' [H6 H7]].
  destruct (join_trans _ _ _ (join_sym _ _ (join_rtc _ _ H2)) Hb) as [b'' [H8 H9]].
  exists a'', b''. repeat split; auto; eauto using well_rtc.
  eapply join_trans with (b := view k a'); [apply join_sym, join_rtc; eapply view_rtc with (Ξ:=Ξ); eassumption|].
  eapply join_trans; [exact H5|].
  apply join_rtc. eapply view_rtc with (Ξ:=Ξ); eassumption.
Qed.

Local Lemma observed_direct k Ξ a b :
  well k Ξ a -> well k Ξ b ->
  observed k Ξ a b -> joinable (view k a) (view k b).
Proof.
  intros Ha Hb [a' [b' [H1 [H2 [_ [_ H5]]]]]].
  eapply join_trans with (b := view k a'); [apply join_rtc; eapply view_rtc with (Ξ:=Ξ); eassumption|].
  eapply join_trans; [exact H5|].
  apply join_sym, join_rtc. eapply view_rtc with (Ξ:=Ξ); eassumption.
Qed.
Local Lemma observed_down j k Ξ a b :
  j ≤ₗ k -> well j Ξ a -> well j Ξ b -> observed k Ξ a b -> observed j Ξ a b.
Proof.
  intros Hjk Ha Hb [a' [b' [H1 [H2 [H3 [H4 [v [H5 H6]]]]]]]].
  pose proof (well_rtc _ _ _ _ H1 Ha) as H7.
  pose proof (well_rtc _ _ _ _ H2 Hb) as H8.
  exists a', b'. repeat split; auto.
  assert (well j Ξ (view k a')) as K1 by (unfold well in *; now rewrite view_down).
  assert (well j Ξ (view k b')) as K2 by (unfold well in *; now rewrite view_down).
  exists (view j v).
  split; rewrite -[view j a'](view_down j k _ Hjk) || rewrite -[view j b'](view_down j k _ Hjk);
    eapply view_rtc; eassumption.
Qed.

Local Lemma join_ren r a b : joinable a b -> joinable (a⟨r⟩) (b⟨r⟩).
Proof. apply join_map. auto using par_ren. Qed.
Local Lemma join_sub_same s a b : joinable a b -> joinable a[s] b[s].
Proof. apply join_map. auto using par_sub, par_refl. Qed.
Local Lemma join_up k P s q :
  (forall i, P i -> joinable (s i) (q i)) ->
  forall j i, under k P j i -> joinable (up_tm_tm s i) (up_tm_tm q i).
Proof. intros K j [|i]; simpl; eauto using join_refl, join_ren. Qed.

Local Lemma join_Abs k a a' :
  joinable a a' -> 
  joinable (tAbs k a) (tAbs k a').
Proof. intros [a0 [? ?]]; exists (tAbs k a0); split; apply rtc_Abs; assumption. Qed.

Local Lemma join_App a k b a' b' :
  joinable a a' -> joinable b b' -> 
  joinable (tApp a k b) (tApp a' k b').
Proof. intros [a0 [? ?]] [b0 [? ?]]; exists (tApp a0 k b0); split; apply rtc_App; assumption. Qed.

Local Lemma join_Pi k a b a' b' :
  joinable a a' -> joinable b b' -> 
  joinable (tPi k a b) (tPi k a' b').
Proof. intros [a0 [? ?]] [b0 [? ?]]; exists (tPi k a0 b0); split; apply rtc_Pi; assumption. Qed.

Local Lemma join_Absurd a a' :
  joinable a a' -> 
  joinable (tAbsurd a) (tAbsurd a').
Proof. intros [a0 [? ?]]; exists (tAbsurd a0); split; apply rtc_Absurd; assumption. Qed.

Local Lemma join_Eq k a b a' b' :
  joinable a a' -> joinable b b' -> 
  joinable (tEq k a b) (tEq k a' b').
Proof. intros [a0 [? ?]] [b0 [? ?]]; exists (tEq k a0 b0); split; apply rtc_Eq; assumption. Qed.

Local Lemma join_J k a b a' b' :
  joinable a a' -> joinable b b' -> 
  joinable (tJ k a b) (tJ k a' b').
Proof. intros [a0 [? ?]] [b0 [? ?]]; exists (tJ k a0 b0); split; apply rtc_J; assumption. Qed.

Local Lemma join_Sig k a b a' b' :
  joinable a a' -> joinable b b' -> 
  joinable (tSig k a b) (tSig k a' b').
Proof. intros [a0 [? ?]] [b0 [? ?]]; exists (tSig k a0 b0); split; apply rtc_Sig; assumption. Qed.

Local Lemma join_Pack k a b a' b' :
  joinable a a' -> joinable b b' -> 
  joinable (tPack k a b) (tPack k a' b').
Proof. intros [a0 [? ?]] [b0 [? ?]]; exists (tPack k a0 b0); split; apply rtc_Pack; assumption. Qed.

Local Lemma join_Let k j a b a' b' :
  joinable a a' -> joinable b b' -> 
  joinable (tLet k j a b) (tLet k j a' b').
Proof. intros [a0 [? ?]] [b0 [? ?]]; exists (tLet k j a0 b0); split; apply rtc_Let; assumption. Qed.

Local Lemma join_Suc a a' :
  joinable a a' -> 
  joinable (tSuc a) (tSuc a').
Proof. intros [a0 [? ?]]; exists (tSuc a0); split; apply rtc_Suc; assumption. Qed.

Local Lemma join_Ind k a b c a' b' c' :
  joinable a a' -> joinable b b' -> joinable c c' -> 
  joinable (tInd k a b c) (tInd k a' b' c').
Proof. intros [a0 [? ?]] [b0 [? ?]] [c0 [? ?]]; exists (tInd k a0 b0 c0); split; apply rtc_Ind; assumption. Qed.

Local Lemma join_Seq k a b a' b' :
  joinable a a' -> joinable b b' -> 
  joinable (tSeq k a b) (tSeq k a' b').
Proof. intros [a0 [? ?]] [b0 [? ?]]; exists (tSeq k a0 b0); split; apply rtc_Seq; assumption. Qed.

Local Lemma join_good_sub k P a s q :
  good k P a ->
  (forall i, P i -> joinable (s i) (q i)) ->
  joinable a[s] a[q].
Proof.
  revert P s q; induction a; intros P s q H K; simpl in *;
    split_hyps; try solve [eauto using join_refl];
    first [apply join_Abs | apply join_App | apply join_Pi | apply join_Absurd | apply join_Eq | apply join_J | apply join_Sig | apply join_Pack | apply join_Let | apply join_Suc | apply join_Ind | apply join_Seq];
    eauto 8 using join_up.
Qed.

Local Lemma observed_sub k Ξ a b s q :
  observed k Ξ a b ->
  (forall i, allowed k Ξ i ->
      well k nil (s i) /\ well k nil (q i) /\ observed k nil (s i) (q i)) ->
  observed k nil a[s] b[q].
Proof.
  intros [a' [b' [H1 [H2 [H3 [H4 H5]]]]]] K.
  exists a'[s], b'[q]. repeat split;
    eauto using rtc_sub, well_sub; try solve [eapply well_sub; eauto; intros; apply K; auto].
  rewrite !view_sub.
  eapply join_trans.
  - apply join_sub_same. exact H5.
  - eapply join_good_sub; [exact H4|].
    intros i Hi. destruct (K i Hi) as [? [? ?]].
    eapply observed_direct with (Ξ:=nil); eassumption.
Qed.
Local Lemma observed_sub_same k Ξ a b s :
  observed k Ξ a b -> well_env Ξ s -> observed k nil a[s] b[s].
Proof.
  intros H K; apply observed_sub with (Ξ:=Ξ); auto.
  intros i Hi. specialize (K k i Hi); eauto using observed_refl.
Qed.
Local Lemma conv_sub_observed Γ a b s :
  conv (c2e Γ) a b -> well_env (c2e Γ) s ->
  exists k, observed k nil a[s] b[s].
Proof.
  intros [k [a' [b' [H1 [H2 H3]]]]] K.
  exists k. apply observed_sub_same with (Ξ:=c2e Γ); auto.
  destruct (proj1 (ieq_views _ _) _ _ H3) as [? [? E]].
  exists a', b'. repeat split; auto. rewrite E. apply join_refl.
Qed.

(* Rigid heads survive reduction, including the universe index and binder labels. *)
Inductive head :=
| HUniv : nat -> head
| HPi : T -> head
| HSig : T -> head
| HEq : T -> head
| HPack : T -> head
| HVoid | HNat | HUnit | HZero | HSuc | HTT | HRefl.

Local Definition head_of a :=
  match a with
  | tUniv n => Some (HUniv n)
  | tPi k _ _ => Some (HPi k)
  | tSig k _ _ => Some (HSig k)
  | tEq k _ _ => Some (HEq k)
  | tPack k _ _ => Some (HPack k)
  | tVoid => Some HVoid
  | tNat => Some HNat
  | tUnit => Some HUnit
  | tZero => Some HZero
  | tSuc _ => Some HSuc
  | tTT => Some HTT
  | tRefl => Some HRefl
  | _ => None
  end.
Local Lemma head_rtc a b h : a ⇒* b -> head_of a = Some h -> head_of b = Some h.
Proof. intros H; induction H; auto. destruct H; simpl in *; auto; discriminate. Qed.
Local Lemma head_join a b h h' :
  joinable a b -> head_of a = Some h -> head_of b = Some h' -> h = h'.
Proof.
  intros [v [H K]] Ha Hb.
  pose proof (head_rtc _ _ _ H Ha); pose proof (head_rtc _ _ _ K Hb); congruence.
Qed.
Local Lemma view_head k a : head_of (view k a) = head_of a.
Proof. destruct a; reflexivity. Qed.
Local Lemma observed_head k Ξ a b h h' :
  observed k Ξ a b -> head_of a = Some h -> head_of b = Some h' -> h = h'.
Proof.
  intros [a' [b' [Ha [Hb [_ [_ H]]]]]] Ka Kb.
  eapply head_join; [exact H| |]; rewrite view_head; eauto using head_rtc.
Qed.

Local Lemma observed_from_view k Ξ a b :
  well k Ξ a -> well k Ξ b ->
  joinable (view k a) (view k b) -> observed k Ξ a b.
Proof. intros; exists a,b; repeat split; auto. Qed.

Local Lemma join_up_all s q :
  (forall i, joinable (s i) (q i)) ->
  forall i, joinable (up_tm_tm s i) (up_tm_tm q i).
Proof. intros H [|i]; simpl; eauto using join_ren, join_refl. Qed.

Local Lemma join_inst s q a :
  (forall i, joinable (s i) (q i)) -> joinable a[s] a[q].
Proof.
  revert s q; induction a; intros s q H; simpl;
    try solve [eauto using join_refl];
    first [apply join_Abs | apply join_App | apply join_Pi | apply join_Absurd |
           apply join_Eq | apply join_J | apply join_Sig | apply join_Pack |
           apply join_Let | apply join_Suc | apply join_Ind | apply join_Seq];
    eauto 8 using join_up_all.
Qed.

Local Lemma rtc_Pi_inv j a b t :
  tPi j a b ⇒* t -> exists a' b', t = tPi j a' b' /\ a ⇒* a' /\ b ⇒* b'.
Proof.
  intro H; remember (tPi j a b) as src eqn:E in H.
  revert j a b E; induction H; intros j a b E; subst.
  - exists a, b; auto.
  - inv_par H. destruct (IHrtc j _ _ eq_refl) as [a' [b' [-> [? ?]]]].
    exists a', b'; eauto.
Qed.

Local Lemma join_Pi_inv j a b a' b' :
  joinable (tPi j a b) (tPi j a' b') -> joinable a a' /\ joinable b b'.
Proof.
  intros [v [H K]].
  destruct (rtc_Pi_inv _ _ _ _ H) as [a0 [b0 [-> [? ?]]]].
  destruct (rtc_Pi_inv _ _ _ _ K) as [a1 [b1 [E [? ?]]]].
  inversion E; subst; split; eexists; eauto.
Qed.

Local Lemma rtc_Sig_inv j a b t :
  tSig j a b ⇒* t -> exists a' b', t = tSig j a' b' /\ a ⇒* a' /\ b ⇒* b'.
Proof.
  intro H; remember (tSig j a b) as src eqn:E in H.
  revert j a b E; induction H; intros j a b E; subst.
  - exists a, b; auto.
  - inv_par H. destruct (IHrtc j _ _ eq_refl) as [a' [b' [-> [? ?]]]].
    exists a', b'; eauto.
Qed.

Local Lemma join_Sig_inv j a b a' b' :
  joinable (tSig j a b) (tSig j a' b') -> joinable a a' /\ joinable b b'.
Proof.
  intros [v [H K]].
  destruct (rtc_Sig_inv _ _ _ _ H) as [a0 [b0 [-> [? ?]]]].
  destruct (rtc_Sig_inv _ _ _ _ K) as [a1 [b1 [E [? ?]]]].
  inversion E; subst; split; eexists; eauto.
Qed.

Local Lemma rtc_Eq_inv j a b t :
  tEq j a b ⇒* t -> exists a' b', t = tEq j a' b' /\ a ⇒* a' /\ b ⇒* b'.
Proof.
  intro H; remember (tEq j a b) as src eqn:E in H.
  revert j a b E; induction H; intros j a b E; subst.
  - exists a, b; auto.
  - inv_par H. destruct (IHrtc j _ _ eq_refl) as [a' [b' [-> [? ?]]]].
    exists a', b'; eauto.
Qed.

Local Lemma join_Eq_inv j a b a' b' :
  joinable (tEq j a b) (tEq j a' b') -> joinable a a' /\ joinable b b'.
Proof.
  intros [v [H K]].
  destruct (rtc_Eq_inv _ _ _ _ H) as [a0 [b0 [-> [? ?]]]].
  destruct (rtc_Eq_inv _ _ _ _ K) as [a1 [b1 [E [? ?]]]].
  inversion E; subst; split; eexists; eauto.
Qed.

Local Lemma rtc_Pack_inv j a b t :
  tPack j a b ⇒* t -> exists a' b', t = tPack j a' b' /\ a ⇒* a' /\ b ⇒* b'.
Proof.
  intro H; remember (tPack j a b) as src eqn:E in H.
  revert j a b E; induction H; intros j a b E; subst.
  - exists a, b; auto.
  - inv_par H. destruct (IHrtc j _ _ eq_refl) as [a' [b' [-> [? ?]]]].
    exists a', b'; eauto.
Qed.

Local Lemma rtc_Suc_inv a t :
  tSuc a ⇒* t -> exists a', t = tSuc a' /\ a ⇒* a'.
Proof.
  intro H; remember (tSuc a) as src eqn:E in H.
  revert a E; induction H; intros a E; subst.
  - exists a; auto.
  - inv_par H. destruct (IHrtc _ eq_refl) as [a' [-> ?]].
    exists a'; eauto.
Qed.

Local Lemma rigid_constant a h : head_of a = Some h ->
  (h = HZero \/ h = HTT \/ h = HRefl \/ h = HNat \/ h = HVoid \/ h = HUnit) ->
  forall b, a ⇒* b -> b = a.
Proof.
  intros H K b R. pose proof (head_rtc _ _ _ R H) as E.
  destruct a, b; simpl in *; try congruence;
    repeat (destruct K as [K|K]; try congruence).
Qed.

Local Lemma observed_Pi k Ξ j a b a' b' :
  observed k Ξ (tPi j a b) (tPi j a' b') ->
  observed k Ξ a a' /\ observed k (j :: Ξ) b b'.
Proof.
  intros [v [w [H [K [S1 [S2 J]]]]]].
  destruct (rtc_Pi_inv _ _ _ _ H) as [a0 [b0 [-> [Ha Hb]]]].
  destruct (rtc_Pi_inv _ _ _ _ K) as [a1 [b1 [-> [Ha' Hb']]]].
  simpl in J; apply join_Pi_inv in J. unfold well in S1,S2; simpl in S1,S2.
  split; [exists a0,a1|exists b0,b1]; split_hyps; repeat split; auto.
Qed.
Local Lemma observed_Sig k Ξ j a b a' b' :
  observed k Ξ (tSig j a b) (tSig j a' b') ->
  observed k Ξ a a' /\ observed k (j :: Ξ) b b'.
Proof.
  intros [v [w [H [K [S1 [S2 J]]]]]].
  destruct (rtc_Sig_inv _ _ _ _ H) as [a0 [b0 [-> [Ha Hb]]]].
  destruct (rtc_Sig_inv _ _ _ _ K) as [a1 [b1 [-> [Ha' Hb']]]].
  simpl in J; apply join_Sig_inv in J. unfold well in S1,S2; simpl in S1,S2.
  split; [exists a0,a1|exists b0,b1]; split_hyps; repeat split; auto.
Qed.
Local Lemma observed_Eq k Ξ j a b a' b' :
  observed k Ξ (tEq j a b) (tEq j a' b') ->
  j ≤ₗ k /\ observed k Ξ a a' /\ observed k Ξ b b'.
Proof.
  intros [v [w [H [K [S1 [S2 J]]]]]].
  destruct (rtc_Eq_inv _ _ _ _ H) as [a0 [b0 [-> [Ha Hb]]]].
  destruct (rtc_Eq_inv _ _ _ _ K) as [a1 [b1 [-> [Ha' Hb']]]].
  simpl in J; apply join_Eq_inv in J. unfold well in S1,S2; simpl in S1,S2.
  split_hyps. split; auto. split; [exists a0,a1|exists b0,b1]; repeat split; auto.
Qed.

Local Lemma observed_single k j a b x :
  observed k (j :: nil) a b -> valid j x -> observed k nil a[x..] b[x..].
Proof.
  intros H K. eapply observed_sub; [exact H|].
  intros [|i] Hi; simpl in *; [|contradiction].
  specialize (K _ Hi); repeat split; auto using observed_refl.
Qed.

(* Universe n is interpreted using the interpretations at indices below n.
   The predicates interpreting the domains of products are indices of Code. *)
Local Fixpoint numeral n :=
  match n with 0 => tZero | S n => tSuc (numeral n) end.

Local Definition product_member j (D : tm -> Prop) (C : tm -> tm -> Prop) f :=
  forall x, valid j x -> D x -> C x (tApp f j x).
Local Definition sum_member j (D : tm -> Prop) (C : tm -> tm -> Prop) p :=
  exists x y, joinable p (tPack j x y) /\ valid j x /\ D x /\ C x y.
Local Definition eq_member j a b p :=
  joinable p tRefl /\ observed j nil a b.
Local Definition nat_member a := exists n, joinable a (numeral n).

Inductive Code (n : nat) (U : nat -> tm -> Prop) : tm -> (tm -> Prop) -> Prop :=
| code_void A P :
    joinable A tVoid -> (forall x, P x <-> False) -> Code n U A P
| code_nat A P :
    joinable A tNat -> (forall x, P x <-> nat_member x) -> Code n U A P
| code_unit A P :
    joinable A tUnit -> (forall x, P x <-> joinable x tTT) -> Code n U A P
| code_univ A i P :
    joinable A (tUniv i) -> i < n ->
    (forall a, P a <-> U i a) -> Code n U A P
| code_pi A j D C PD PC P :
    joinable A (tPi j D C) ->
    Code n U D PD ->
    (forall x, valid j x -> PD x -> Code n U C[x..] (PC x)) ->
    (forall x, P x <-> product_member j PD PC x) -> Code n U A P
| code_sig A j D C PD PC P :
    joinable A (tSig j D C) ->
    Code n U D PD ->
    (forall x, valid j x -> PD x -> Code n U C[x..] (PC x)) ->
    (forall x, P x <-> sum_member j PD PC x) -> Code n U A P
| code_eq A j a b P :
    joinable A (tEq j a b) -> well j nil a -> well j nil b ->
    (forall x, P x <-> eq_member j a b x) -> Code n U A P.

Local Fixpoint universe n : nat -> tm -> Prop :=
  match n with
  | 0 => fun _ _ => False
  | S n => fun i a =>
      if Nat.eqb i n then exists P, Code n (universe n) a P
      else universe n i a
  end.
Local Definition interprets n := Code n (universe n).
Local Definition type_denotes A := exists n P, interprets n A P.
Local Definition realizes A a := exists n P, interprets n A P /\ P a.

Local Lemma universe_spec n i a : i < n ->
  universe n i a <-> exists P, interprets i a P.
Proof.
  induction n as [|n IH]; intro L; [lia|].
  simpl. destruct (Nat.eqb_spec i n) as [->|H]; [reflexivity|].
  apply IH. lia.
Qed.

Local Lemma code_change_type n U A B P :
  Code n U A P -> joinable A B -> Code n U B P.
Proof.
  intros H J; destruct H;
    solve [eapply code_void; eauto using join_trans, join_sym
          |eapply code_nat; eauto using join_trans, join_sym
          |eapply code_unit; eauto using join_trans, join_sym
          |eapply code_univ; [eapply join_trans; [apply join_sym; exact J | eassumption]|eassumption..]
          |eapply code_pi; [eapply join_trans; [apply join_sym; exact J | eassumption]|eassumption..]
          |eapply code_sig; [eapply join_trans; [apply join_sym; exact J | eassumption]|eassumption..]
          |eapply code_eq; [eapply join_trans; [apply join_sym; exact J | eassumption]|eassumption..]].
Qed.

Local Lemma code_present n U A P Q :
  Code n U A P -> (forall x, Q x <-> P x) -> Code n U A Q.
Proof.
  intros H E; destruct H.
  - eapply code_void; [eassumption|intros; rewrite E; auto].
  - eapply code_nat; [eassumption|intros; rewrite E; auto].
  - eapply code_unit; [eassumption|intros; rewrite E; auto].
  - eapply code_univ; [eassumption|eassumption|intros; rewrite E; auto].
  - eapply code_pi; [eassumption..|intros; rewrite E; auto].
  - eapply code_sig; [eassumption..|intros; rewrite E; auto].
  - eapply code_eq; [eassumption..|intros; rewrite E; auto].
Qed.

Local Lemma code_lift n A P :
  interprets n A P -> forall m, n <= m -> interprets m A P.
Proof.
  unfold interprets. intro H; induction H; intros m L;
    try solve [eapply code_void; eassumption
              |eapply code_nat; eassumption
              |eapply code_unit; eassumption
              |eapply code_eq; eassumption
              |eapply code_pi; eauto
              |eapply code_sig; eauto].
  eapply code_univ; [eassumption|lia|].
  intros x. rewrite H1 (universe_spec n i x H0) (universe_spec m i x ltac:(lia)). reflexivity.
Qed.

Local Lemma code_member_move n A P a b :
  interprets n A P -> joinable a b -> P a -> P b.
Proof.
  unfold interprets. intro H; revert a b; induction H; intros x y J K; simpl in *;
    try match goal with E : forall a, P a <-> _ |- _ =>
      solve [apply E in K; apply E; contradiction] || (apply E in K; apply E)
    end.
  - destruct K as [v Kv]; exists v; eauto using join_trans, join_sym.
  - eauto using join_trans, join_sym.
  - apply (universe_spec n i x H0) in K. destruct K as [Q Qx].
    apply (universe_spec n i y H0). exists Q. eapply code_change_type; eassumption.
  - intros v V Dv. eapply H2; try eassumption; [|apply K; assumption].
    eapply join_App; auto using join_refl.
  - destruct K as [v [w [Kv [L [M N]]]]].
    exists v,w; repeat split; auto. eauto using join_trans, join_sym.
  - destruct K as [Hr Ho]. split; auto. eauto using join_trans, join_sym.
Qed.

Local Lemma eq_endpoints k j a b a' b' :
  j ≤ₗ k ->
  well j nil a -> well j nil b -> well j nil a' -> well j nil b' ->
  observed k nil a a' -> observed k nil b b' ->
  (observed j nil a b <-> observed j nil a' b').
Proof.
  intros L Ha Hb Ha' Hb' K1 K2.
  pose proof (observed_down _ _ _ _ _ L Ha Ha' K1) as J1.
  pose proof (observed_down _ _ _ _ _ L Hb Hb' K2) as J2.
  pose proof (observed_direct _ _ _ _ Ha Ha' J1) as V1.
  pose proof (observed_direct _ _ _ _ Hb Hb' J2) as V2.
  split; intro E; apply observed_from_view; try assumption.
  - eapply join_trans; [apply join_sym; exact V1|].
    eapply join_trans; [exact (observed_direct _ _ _ _ Ha Hb E)|exact V2].
  - eapply join_trans; [exact V1|].
    eapply join_trans; [exact (observed_direct _ _ _ _ Ha' Hb' E)|apply join_sym; exact V2].
Qed.

Local Definition comparable Ξ a b :=
  joinable a b \/ exists k, observed k Ξ a b.

Local Lemma comparable_move Ξ a b c d :
  joinable a c -> joinable b d -> comparable Ξ a b -> comparable Ξ c d.
Proof.
  intros J K [L|[k L]].
  - left. eapply join_trans; [apply join_sym; exact J|].
    eapply join_trans; eassumption.
  - right. exists k. eapply observed_move; eassumption.
Qed.
Local Lemma comparable_head Ξ a b h h' :
  comparable Ξ a b -> head_of a = Some h -> head_of b = Some h' -> h = h'.
Proof. intros [H|[k H]]; eauto using head_join, observed_head. Qed.
Local Lemma comparable_pi Ξ j a b a' b' :
  comparable Ξ (tPi j a b) (tPi j a' b') ->
  comparable Ξ a a' /\ comparable (j :: Ξ) b b'.
Proof.
  intros [H|[k H]]; [apply join_Pi_inv in H|apply observed_Pi in H];
    destruct H; unfold comparable; split; [left|left|right; exists k|right; exists k]; assumption.
Qed.
Local Lemma comparable_sig Ξ j a b a' b' :
  comparable Ξ (tSig j a b) (tSig j a' b') ->
  comparable Ξ a a' /\ comparable (j :: Ξ) b b'.
Proof.
  intros [H|[k H]]; [apply join_Sig_inv in H|apply observed_Sig in H];
    destruct H; unfold comparable; split; [left|left|right; exists k|right; exists k]; assumption.
Qed.
Local Lemma comparable_single j a b x :
  comparable (j :: nil) a b -> valid j x -> comparable nil a[x..] b[x..].
Proof. intros [H|[k H]] V; unfold comparable; eauto using join_sub_same, observed_single. Qed.
Local Lemma comparable_eq j a b a' b' :
  comparable nil (tEq j a b) (tEq j a' b') ->
  well j nil a -> well j nil b -> well j nil a' -> well j nil b' ->
  (observed j nil a b <-> observed j nil a' b').
Proof.
  intros [H|[k H]] Ka Kb Ka' Kb'.
  - apply join_Eq_inv in H. destruct H as [J K].
    split; eauto using observed_move, join_sym.
  - apply observed_Eq in H. destruct H as [L [J K]].
    eapply eq_endpoints; eassumption.
Qed.

(* Each type has the same members in any two interpretations related by a view. *)
Local Lemma code_agree n A P :
  interprets n A P ->
  forall m B Q, interprets m B Q -> comparable nil A B ->
    forall x, P x <-> Q x.
Proof.
  unfold interprets. intro HA; induction HA; intros m B Q HB O x; destruct HB;
    match goal with
    | V : comparable nil ?a ?b, L : joinable ?a ?a', R : joinable ?b ?b' |- _ =>
        let W := fresh "W" in
        pose proof (comparable_move _ _ _ _ _ L R V) as W;
        let E := fresh "E" in
        pose proof (comparable_head _ _ _ _ _ W eq_refl eq_refl) as E;
        inversion E; subst; clear E
    end;
    match goal with
    | E : forall a, ?P a <-> _, F : forall b, ?Q b <-> _ |- ?P ?x <-> ?Q ?x =>
        rewrite (E x) (F x)
    end; try reflexivity.
  - rewrite (universe_spec n i0 x ltac:(lia)) (universe_spec m i0 x ltac:(lia)). reflexivity.
  - apply comparable_pi in W. destruct W as [WD WC].
    unfold product_member. split; intros F a Va Da.
    + pose proof (proj2 (IHHA _ _ _ HB WD a) Da) as Da'.
      apply (proj1 (H1 a Va Da' _ _ _ (H4 a Va Da)
        (comparable_single _ _ _ _ WC Va) (tApp x j0 a))).
      auto.
    + pose proof (proj1 (IHHA _ _ _ HB WD a) Da) as Da'.
      apply (proj2 (H1 a Va Da _ _ _ (H4 a Va Da')
        (comparable_single _ _ _ _ WC Va) (tApp x j0 a))).
      auto.
  - apply comparable_sig in W. destruct W as [WD WC].
    unfold sum_member. split; intros [a [b [J [Va [Da Db]]]]].
    + pose proof (proj1 (IHHA _ _ _ HB WD a) Da) as Da'.
      exists a,b. repeat split; auto.
      apply (proj1 (H1 a Va Da _ _ _ (H4 a Va Da')
        (comparable_single _ _ _ _ WC Va) b)). exact Db.
    + pose proof (proj2 (IHHA _ _ _ HB WD a) Da) as Da'.
      exists a,b. repeat split; auto.
      apply (proj2 (H1 a Va Da' _ _ _ (H4 a Va Da)
        (comparable_single _ _ _ _ WC Va) b)). exact Db.
  - unfold eq_member.
    now rewrite (comparable_eq _ _ _ _ _ W H0 H1 H4 H5).
Qed.

Local Lemma realizes_as n A P a :
  interprets n A P -> realizes A a -> P a.
Proof.
  intros HP [m [Q [HQ Ha]]].
  apply (proj1 (code_agree _ _ _ HQ _ _ _ HP (or_introl (join_refl _)) a)).
  exact Ha.
Qed.

Local Lemma realizes_change A B a b :
  joinable A B -> joinable a b -> realizes A a -> realizes B b.
Proof.
  intros J K [n [P [H V]]]. exists n,P. split.
  - eapply code_change_type; eassumption.
  - eapply code_member_move; eassumption.
Qed.

Local Lemma realizes_observed A B a k :
  realizes A a -> type_denotes B -> observed k nil A B -> realizes B a.
Proof.
  intros [n [P [HP Ha]]] [m [Q HQ]] O.
  exists m,Q. split; auto. eapply (proj1 (code_agree _ _ _ HP _ _ _ HQ (or_intror (ex_intro _ k O)) a)); exact Ha.
Qed.

Local Ltac invert_rigid_code H :=
  inversion H; subst; clear H;
  match goal with
  | J : joinable ?a ?b |- _ =>
      let E := fresh "E" in
      pose proof (head_join _ _ _ _ J eq_refl eq_refl) as E;
      inversion E; subst; clear E
  end.

Local Lemma realizes_univ_intro i a P :
  interprets i a P -> realizes (tUniv i) a.
Proof.
  intros H. exists (S i), (fun a => exists Q, interprets i a Q).
  split; [|eauto].
  eapply code_univ with (i:=i).
  - apply join_refl.
  - lia.
  - intros x. symmetry. apply universe_spec. lia.
Qed.
Local Lemma realizes_univ_elim i a :
  realizes (tUniv i) a -> exists P, interprets i a P.
Proof.
  intros [n [P [H K]]]. unfold interprets in H. invert_rigid_code H.
  match goal with E : forall x, P x <-> universe n ?i x |- _ =>
    apply (proj1 (universe_spec n i a ltac:(lia))), E; exact K
  end.
Qed.
Local Lemma univ_denotes i a :
  realizes (tUniv i) a -> type_denotes a.
Proof. intro H. exists i. exact (realizes_univ_elim _ _ H). Qed.

Local Lemma interprets_pi_inv n j A B P :
  interprets n (tPi j A B) P ->
  exists PA PB,
    interprets n A PA /\
    (forall x, valid j x -> PA x -> interprets n B[x..] (PB x)) /\
    (forall f, P f <-> product_member j PA PB f).
Proof.
  unfold interprets; intro H; invert_rigid_code H.
  match goal with J : joinable (tPi _ _ _) (tPi _ _ _) |- _ =>
    apply join_Pi_inv in J; destruct J as [J K]
  end.
  do 2 eexists. split; [|split].
  - eapply code_change_type; [eassumption|apply join_sym; eassumption].
  - intros x V Dx. eapply code_change_type.
    + eauto.
    + apply join_sub_same, join_sym; eassumption.
  - assumption.
Qed.

Local Lemma interprets_sig_inv n j A B P :
  interprets n (tSig j A B) P ->
  exists PA PB,
    interprets n A PA /\
    (forall x, valid j x -> PA x -> interprets n B[x..] (PB x)) /\
    (forall p, P p <-> sum_member j PA PB p).
Proof.
  unfold interprets; intro H; invert_rigid_code H.
  match goal with J : joinable (tSig _ _ _) (tSig _ _ _) |- _ =>
    apply join_Sig_inv in J; destruct J as [J K]
  end.
  do 2 eexists. split; [|split].
  - eapply code_change_type; [eassumption|apply join_sym; eassumption].
  - intros x V Dx. eapply code_change_type.
    + eauto.
    + apply join_sub_same, join_sym; eassumption.
  - assumption.
Qed.

Local Lemma realizes_nat_intro n a : a ⇒* numeral n -> realizes tNat a.
Proof.
  intros H. exists 0, nat_member. split; [eapply code_nat; [apply join_refl|reflexivity]|].
  exists n. exact (join_rtc _ _ H).
Qed.
Local Lemma numeral_rigid n a : numeral n ⇒* a -> a = numeral n.
Proof.
  revert a; induction n; intros a H; simpl in H.
  - eapply (rigid_constant tZero HZero); eauto.
  - destruct (rtc_Suc_inv _ _ H) as [b [-> Hb]]. now rewrite (IHn _ Hb).
Qed.
Local Lemma realizes_nat_elim a : realizes tNat a -> exists n, a ⇒* numeral n.
Proof.
  intros [n [P [H K]]]. unfold interprets in H. invert_rigid_code H.
  match goal with E : forall x, P x <-> _ |- _ => apply E in K end.
  destruct K as [i [v [Hv J]]]. now rewrite (numeral_rigid _ _ J) in Hv; exists i.
Qed.
Local Lemma valid_numeral j n : valid j (numeral n).
Proof. induction n; unfold valid, well in *; simpl; tauto. Qed.

Local Lemma realizes_unit_intro : realizes tUnit tTT.
Proof. exists 0, (fun a => joinable a tTT); split; [eapply code_unit; [apply join_refl|reflexivity]|apply join_refl]. Qed.
Local Lemma realizes_unit_elim a : realizes tUnit a -> a ⇒* tTT.
Proof.
  intros [n [P [H K]]]. unfold interprets in H. invert_rigid_code H.
  match goal with E : forall x, P x <-> _ |- _ => apply E in K end.
  destruct K as [v [Hv J]].
  now rewrite (rigid_constant tTT HTT eq_refl ltac:(auto) _ J) in Hv.
Qed.
Local Lemma realizes_eq_intro j a :
  well j nil a -> realizes (tEq j a a) tRefl.
Proof.
  intro V. exists 0, (eq_member j a a); split.
  - eapply code_eq; try eassumption; [apply join_refl|reflexivity].
  - split; auto using join_refl, observed_refl.
Qed.
Local Lemma realizes_eq_elim j a b p :
  realizes (tEq j a b) p -> p ⇒* tRefl /\ observed j nil a b.
Proof.
  intros [n [P [H K]]]. unfold interprets in H. invert_rigid_code H.
  match goal with E : forall x, P x <-> _ |- _ => apply E in K end.
  destruct K as [[v [Hv J]] O]. split.
  - now rewrite (rigid_constant tRefl HRefl eq_refl ltac:(auto) _ J) in Hv.
  - match goal with J : joinable (tEq _ _ _) (tEq _ _ _) |- _ =>
      apply join_Eq_inv in J; destruct J
    end.
    eapply observed_move; eauto using join_sym.
Qed.

Local Lemma join_single B x y : joinable x y -> joinable B[x..] B[y..].
Proof. intros H; apply join_inst; intros [|i]; simpl; auto using join_refl. Qed.

Local Lemma realizes_sig_elim j A B p k :
  realizes (tSig j A B) p -> valid k p ->
  exists x y, p ⇒* tPack j x y /\ valid j x /\ realizes A x /\
    valid k y /\ realizes B[x..] y.
Proof.
  intros [n [P [H V]]] W.
  destruct (interprets_sig_inv _ _ _ _ _ H) as [PA [PB [HA [HB E]]]].
  apply E in V. destruct V as [x [y [[z [R S]] [Vx [Dx Dy]]]]].
  destruct (rtc_Pack_inv _ _ _ _ S) as [x' [y' [-> [X Y]]]].
  exists x',y'. repeat split; auto.
  - eapply valid_rtc; eassumption.
  - eapply realizes_change; [apply join_refl|apply join_rtc; exact X|].
    exists n,PA; auto.
  - intros k' L. specialize (W k' L).
    pose proof (well_rtc _ _ _ _ R W) as Hpack.
    unfold well in Hpack. simpl in Hpack. exact (proj2 Hpack).
  - eapply realizes_change.
    + apply join_single, join_rtc; exact X.
    + apply join_rtc; exact Y.
    + exists n, (PB x); auto.
Qed.

Local Lemma no_void_member a : ~ realizes tVoid a.
Proof.
  intro H. eapply (realizes_as 0 tVoid (fun _ => False)); [|exact H].
  apply code_void; [apply join_refl|reflexivity].
Qed.

(* Each substitution entry realizes its declared type in the tail environment. *)
Local Fixpoint semantic_env (Γ : context) (s : nat -> tm) : Prop :=
  match Γ with
  | nil => True
  | (j,A) :: Γ => semantic_env Γ (S >> s) /\ valid j (s 0) /\
                    realizes A[S >> s] (s 0)
  end.
Local Lemma env_cons Γ s j A a :
  semantic_env Γ s -> valid j a -> realizes A[s] a ->
  semantic_env ((j,A)::Γ) (a .: s).
Proof. simpl. auto. Qed.
Local Lemma env_well Γ s : semantic_env Γ s -> well_env (c2e Γ) s.
Proof.
  revert s; induction Γ as [|[j A] Γ IH]; intros s H k [|i] K;
    simpl in *; split_hyps; try contradiction; eauto.
  exact (IH (S >> s) H k i K).
Qed.
Local Lemma env_lookup Γ i j A :
  lookup i Γ j A -> forall s, semantic_env Γ s -> realizes A[s] (s i).
Proof.
  intros H; induction H; intros s K.
  - rewrite sub_ren. exact (proj2 (proj2 K)).
  - destruct B as [k D]. rewrite sub_ren. apply IHlookup. exact (proj1 K).
Qed.
Local Lemma wt_valid Γ s j a A :
  Γ ⊢ a ; j ∈ A -> semantic_env Γ s -> valid j a[s].
Proof. eauto using valid_sub, env_well. Qed.

Local Lemma sub_shift s a x : (a⟨S⟩)[x .: s] = a[s].
Proof. rewrite sub_ren. reflexivity. Qed.
Local Lemma sub_ind_step s A n r :
  (A[tSuc (var_tm 0) .: (S >> var_tm)]⟨S⟩)[r .: (n .: s)] =
  A[tSuc n .: s].
Proof.
  rewrite sub_ren sub_comp. apply sub_ext. now intros [|i].
Qed.
Local Lemma sub_let_step s C j a b :
  C[tPack j (var_tm 1) (var_tm 0) .: (S >> S >> var_tm)][b .: (a .: s)] =
  C[tPack j a b .: s].
Proof. rewrite sub_comp. apply sub_ext. now intros [|i]. Qed.

(* A codomain family can use the realization predicate at each argument. *)
Local Lemma canonical_predicate n A :
  (exists P, interprets n A P) -> interprets n A (realizes A).
Proof.
  intros [P H]. eapply code_present; [exact H|].
  split; [apply (realizes_as _ _ _ x H)|].
  intro K. exists n,P; auto.
Qed.

Local Lemma family_denotes Γ s j A B i h :
  semantic_env Γ s ->
  realizes (tUniv i) A[s] ->
  (forall q, semantic_env ((j,A)::Γ) q -> realizes (tUniv h) B[q]) ->
  exists PA,
    interprets (Nat.max i h) A[s] PA /\
    forall x, valid j x -> PA x ->
      interprets (Nat.max i h) (B[up_tm_tm s])[x..] (realizes ((B[up_tm_tm s])[x..])).
Proof.
  intros E HA HB. destruct (realizes_univ_elim _ _ HA) as [PA DA].
  exists PA; split.
  - eapply code_lift; [exact DA|apply Nat.le_max_l].
  - intros x V Dx. rewrite sub_up1.
    eapply code_lift with (n := h); [|apply Nat.le_max_r].
    apply canonical_predicate, realizes_univ_elim.
    apply HB, env_cons; auto. exists i,PA; auto.
Qed.

Local Lemma realizes_expand A a b :
  a ⇒* b -> realizes A b -> realizes A a.
Proof.
  intros H K. eapply realizes_change; [apply join_refl|apply join_sym, join_rtc; exact H|exact K].
Qed.
Local Lemma join_scons C a b s :
  joinable a b -> joinable C[a .: s] C[b .: s].
Proof. intros H; apply join_inst; intros [|i]; simpl; auto using join_refl. Qed.
Local Lemma valid_refl_term j : valid j tRefl.
Proof. unfold valid, well; simpl; auto. Qed.

Local Lemma valid_ind_input j a b c n :
  valid j (tInd j a b c) -> valid j n -> valid j (tInd j a b n).
Proof.
  unfold valid, well; simpl. intros H K k L; specialize (H k L); specialize (K k L); tauto.
Qed.
Local Lemma realizes_induction j A a b c :
  realizes tNat c ->
  valid j (tInd j a b c) ->
  realizes A[tZero..] a ->
  (forall n r, valid j r -> realizes A[(numeral n)..] r ->
    realizes A[(tSuc (numeral n))..] b[r .: (numeral n)..]) ->
  realizes A[c..] (tInd j a b c).
Proof.
  intros Hc V Hzero Hsuc.
  assert (Hnum : forall n, realizes A[(numeral n)..] (tInd j a b (numeral n))).
  { intro n; induction n as [|n IH]; simpl.
    - eapply realizes_expand; [apply par_rtc, P_IndZero, par_refl|exact Hzero].
    - pose proof (valid_ind_input _ _ _ _ _ V (valid_numeral j n)) as Vr.
      eapply realizes_expand;
        [apply par_rtc, P_IndSuc; apply par_refl|exact (Hsuc n _ Vr IH)]. }
  destruct (realizes_nat_elim _ Hc) as [n R].
  eapply realizes_change; [| |exact (Hnum n)].
  - apply join_single, join_sym, join_rtc; exact R.
  - apply join_sym, join_rtc, rtc_Ind; auto.
Qed.

(* A well-typed term realizes its type under every realizing substitution. *)
Local Lemma typing_realizes Γ j a A :
  Γ ⊢ a ; j ∈ A -> forall s, semantic_env Γ s -> realizes A[s] a[s].
Proof.
  revert Γ j a A.
  apply (wt_ind
    (fun Γ j a A _ => forall s, semantic_env Γ s -> realizes A[s] a[s])
    (fun _ _ => True)).
  - intros Γ ℓ0 ℓ i A _ _ K _ s E. eapply env_lookup; eassumption.
  - intros Γ i h ℓ ℓ0 A B _ IHA _ IHB s E. simpl.
    destruct (family_denotes _ _ _ _ _ _ _ E (IHA s E) IHB) as [PA [DA DB]].
    eapply realizes_univ_intro. eapply code_pi; [apply join_refl|exact DA|exact DB|reflexivity].
  - intros Γ ℓ ℓ0 ℓ1 A a B i _ IHAB _ IHa s E. simpl.
    destruct (realizes_univ_elim _ _ (IHAB s E)) as [P HP].
    destruct (interprets_pi_inv _ _ _ _ _ HP) as [PA [PB [DA [DB DP]]]].
    exists i,P. split; [exact HP|].
    apply DP. intros x V Dx.
    assert (Ex : semantic_env ((ℓ0,A)::Γ) (x .: s)).
    { apply env_cons; auto. exists i, PA; auto. }
    pose proof (IHa _ Ex) as R.
    eapply code_member_move; [apply DB; eassumption | |].
    + apply join_sym, join_par. rewrite -sub_up1.
      apply P_AppAbs; apply par_refl.
    + eapply realizes_as; [apply DB; eassumption|].
      now rewrite !sub_up1.
  - intros Γ ℓ ℓ0 a A B b _ IHa Hb IHb s E. simpl.
    destruct (IHa s E) as [n [P [HP R]]].
    destruct (interprets_pi_inv _ _ _ _ _ HP) as [PA [PB [DA [DB DP]]]].
    assert (Vb : valid ℓ0 b[s]) by (eapply wt_valid; eassumption).
    assert (Db : PA b[s]) by (eapply realizes_as; [exact DA|apply IHb; exact E]).
    rewrite sub_single -sub_up1.
    exists n,(PB b[s]). split; [auto|].
    exact (proj1 (DP _) R _ Vb Db).
  - intros Γ ℓ ℓ0 a A B i _ IHa _ IHB C s E.
    destruct (conv_sub_observed _ _ _ _ C (env_well _ _ E)) as [k O].
    eapply realizes_observed; [apply IHa|eapply univ_denotes, IHB|exact O]; exact E.
  - intros Γ ℓ _ _ s E. apply (realizes_nat_intro 0). constructor.
  - intros Γ ℓ a _ IHa s E. simpl.
    destruct (realizes_nat_elim _ (IHa s E)) as [n R].
    apply (realizes_nat_intro (S n)); simpl; auto.
  - intros Γ ℓ ℓ0 a b c A ℓA i L HA IHA Ha IHa Hb IHb Hc IHc s E.
    simpl. rewrite sub_single -sub_up1.
    apply realizes_induction.
    + apply IHc; exact E.
    + change (valid ℓ0 (tInd ℓ0 a b c)[s]).
      eapply wt_valid; [eapply T_Ind; [apply level_refl|eassumption..]|exact E].
    + rewrite sub_up1.
      pose proof (IHa s E) as R. now rewrite sub_single in R.
    + intros n r Vr Rr. rewrite sub_up1 in Rr.
      assert (En : semantic_env ((ℓ0,tNat)::Γ) (numeral n .: s)).
      { apply env_cons; auto using valid_numeral.
        apply (realizes_nat_intro n); constructor. }
      pose proof (env_cons _ _ ℓ0 _ _ En Vr Rr) as Er.
      specialize (IHb _ Er). rewrite sub_ind_step in IHb.
      now rewrite sub_up1 sub_up2.
  - intros Γ ℓ i _ _ s E. eapply realizes_univ_intro.
    eapply code_nat; [apply join_refl|reflexivity].
  - intros Γ ℓ i _ _ s E. eapply realizes_univ_intro.
    eapply code_univ with (i:=i); [apply join_refl|lia|reflexivity].
  - intros Γ ℓ i _ _ s E. eapply realizes_univ_intro.
    eapply code_void with (P := fun _ => False); [apply join_refl|reflexivity].
  - intros Γ ℓ ℓ0 ℓ1 i a A _ IHa _ _ s E.
    exfalso. apply (no_void_member a[s]). exact (IHa s E).
  - intros Γ ℓ a ℓ0 A Ha _ s E. simpl.
    apply realizes_eq_intro. exact (wt_valid _ _ _ _ _ Ha E _ (level_refl _)).
  - intros Γ ℓ ℓ0 a b A i L Ha _ Hb _ s E. simpl.
    eapply realizes_univ_intro. eapply code_eq.
    + apply join_refl.
    + exact (wt_valid _ _ _ _ _ Ha E _ (level_refl _)).
    + exact (wt_valid _ _ _ _ _ Hb E _ (level_refl _)).
    + reflexivity.
  - intros Γ t a b p A i h C ℓ ℓp ℓT ℓ0 ℓ1 L1 Lp Ha IHa Hb IHb _ _ Hp IHp HC IHC _ IHt s E.
    simpl. rewrite sub_double.
    destruct (realizes_eq_elim _ _ _ _ (IHp s E)) as [R O].
    pose proof (wt_valid _ _ _ _ _ Ha E) as Va.
    pose proof (wt_valid _ _ _ _ _ Hb E) as Vb.
    pose proof (wt_valid _ _ _ _ _ Hp E) as Vp.
    assert (Eb : semantic_env ((ℓ1,A)::Γ) (b[s] .: s)) by
      (apply env_cons; auto).
    assert (Ep : semantic_env
      ((ℓp,tEq ℓ0 (a⟨S⟩) (var_tm 0))::(ℓ1,A)::Γ) (p[s] .: (b[s] .: s))).
    { apply env_cons; auto. simpl. rewrite sub_shift. apply IHp; exact E. }
    assert (M : observed ℓ0 nil C[tRefl .: (a[s] .: s)] C[p[s] .: (b[s] .: s)]).
    { eapply observed_sub.
      - apply observed_refl. eapply (proj1 typing_well); [exact HC|apply level_refl].
      - intros [|[|v]] Hv; simpl in *.
        + repeat split; auto using valid_refl_term.
          eapply observed_move; [apply join_refl|apply join_sym, join_rtc; exact R|].
          apply observed_refl. exact (valid_refl_term ℓ0 ℓ0 (level_refl _)).
        + repeat split; auto.
        + pose proof (env_well _ _ E ℓ0 v Hv) as V.
          repeat split; auto using observed_refl. }
    eapply realizes_expand.
    + eapply rtc_trans; [apply rtc_J; [constructor|exact R]|].
      apply par_rtc, P_JRefl, par_refl.
    + eapply realizes_observed; [|eapply univ_denotes, IHC; exact Ep|exact M].
      pose proof (IHt s E) as Rt. now rewrite sub_double in Rt.
  - intros Γ i h ℓ ℓ0 A B _ IHA _ IHB s E. simpl.
    destruct (family_denotes _ _ _ _ _ _ _ E (IHA s E) IHB) as [PA [DA DB]].
    eapply realizes_univ_intro. eapply code_sig; [apply join_refl|exact DA|exact DB|reflexivity].
  - intros Γ ℓ ℓ0 a A b B ℓT i Ha IHa _ IHb _ IHAB s E. simpl.
    destruct (realizes_univ_elim _ _ (IHAB s E)) as [P HP].
    destruct (interprets_sig_inv _ _ _ _ _ HP) as [PA [PB [DA [DB DP]]]].
    assert (Va : valid ℓ0 a[s]) by (eapply wt_valid; eassumption).
    assert (Da : PA a[s]) by (eapply realizes_as; [exact DA|apply IHa; exact E]).
    exists i,P. split; [exact HP|]. apply DP. exists a[s],b[s].
    repeat split; auto using join_refl.
    eapply realizes_as; [apply DB; eassumption|].
    rewrite sub_up1. pose proof (IHb s E) as R. now rewrite sub_single in R.
  - intros Γ ℓ ℓp ℓ0 a b ℓT A B C i h k L _ _ _ _ Ha IHa _ IHb _ _ s E.
    simpl. rewrite sub_single.
    pose proof (wt_valid _ _ _ _ _ Ha E) as V.
    destruct (realizes_sig_elim _ _ _ _ _ (IHa s E) V)
      as [x [y [R [Vx [Dx [Vy Dy]]]]]].
    rewrite sub_up1 in Dy.
    pose proof (env_cons _ _ ℓ0 _ _ E Vx Dx) as Ex.
    pose proof (env_cons _ _ ℓp _ _ Ex Vy Dy) as Ey.
    pose proof (IHb _ Ey) as K. rewrite sub_let_step in K.
    eapply realizes_change; [| |exact K].
    + apply join_scons, join_sym, join_rtc; exact R.
    + apply join_sym, join_rtc.
      eapply rtc_trans; [apply rtc_Let; [exact R|constructor]|].
      rewrite -sub_up2. apply par_rtc, P_LetPack; apply par_refl.
  - intros Γ ℓ _ _ s E. apply realizes_unit_intro.
  - intros Γ ℓ i _ _ s E. eapply realizes_univ_intro.
    eapply code_unit with (P := fun a => joinable a tTT); [apply join_refl|reflexivity].
  - intros Γ ℓ ℓ0 ℓC a b C i L _ IHa _ IHb _ _ s E.
    simpl. rewrite sub_single.
    pose proof (realizes_unit_elim _ (IHa s E)) as R.
    pose proof (IHb s E) as K. rewrite sub_single in K.
    eapply realizes_change; [| |exact K].
    + apply join_scons, join_sym, join_rtc; exact R.
    + apply join_sym, join_rtc.
      eapply rtc_trans; [apply rtc_Seq; [exact R|constructor]|].
      apply par_rtc, P_SeqTT, par_refl.
  - exact I.
  - intros; exact I.
Qed.

Theorem consistency a ℓ : ~nil ⊢ a ; ℓ ∈ tVoid.
Proof.
  intro H.
  apply (no_void_member a[var_tm]).
  exact (typing_realizes _ _ _ _ H var_tm I).
Qed.

End consistency.
