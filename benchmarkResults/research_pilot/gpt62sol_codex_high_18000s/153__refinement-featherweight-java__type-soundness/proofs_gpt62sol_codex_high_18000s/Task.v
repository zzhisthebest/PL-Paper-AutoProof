Require Import Definitions.Syntax Definitions.Semantics Definitions.Typing
  Definitions.CTSanity.

From Stdlib Require Import List Arith Lia ListSet.
Require Import Definitions.FJTyping Definitions.SubDenotation.
Require Import RFJ.Utils.Referable.

(* Refinement predicates erase without changing the expression. *)
Local Lemma erase_subtype g s t :
  Subtype g s t -> FJSubtype (erase s) (erase t).
Proof. intros H; inversion H; assumption. Qed.

Local Lemma erase_self t e : erase (self t e) = erase t.
Proof. destruct t; reflexivity. Qed.

Local Lemma erase_subBV j e t : erase (tsubBV_at j e t) = erase t.
Proof. destruct t; reflexivity. Qed.

Local Lemma erase_open j x t : erase (openT_at j x t) = erase t.
Proof. destruct t; reflexivity. Qed.

Local Lemma erase_lookup g x t :
  bound_in x t g -> bound_inF x (erase t) (erase_env g).
Proof.
  induction g as [|y s g IH]; simpl; tauto || intros [[-> ->] | H]; auto.
Qed.

Local Lemma erase_typing g e t :
  Hastype g e t -> HasFJtype (erase_env g) e (erase t).
Proof.
  revert g e t.
  fix IH 4.
  intros g e t H; destruct H.
  - constructor.
  - constructor.
  - unfold tsubBV; rewrite erase_subBV. apply FTUnOP.
    eapply FTSub; [apply IH; eassumption | now apply erase_subtype in H0].
  - unfold tsubBV in *. rewrite !erase_subBV. apply FTBinOP.
    + eapply FTSub; [apply IH; eassumption | now apply erase_subtype in H0].
    + eapply FTSub; [apply IH; eassumption |].
      apply erase_subtype in H2. now rewrite erase_subBV in H2.
  - rewrite erase_self. apply FTVar. now apply erase_lookup.
  - unfold tsubBV in *. rewrite erase_self, !erase_subBV.
    eapply FTInvok; [exact (IH _ _ _ H) | eassumption |].
    eapply FTSub; [apply IH; eassumption |].
    apply erase_subtype in H3. now rewrite erase_subBV in H3.
  - unfold tsubBV in *. rewrite erase_self, !erase_subBV.
    eapply FTInvokI; [exact (IH _ _ _ H) | eassumption |].
    eapply FTSub; [apply IH; eassumption |].
    apply erase_subtype in H3. now rewrite erase_subBV in H3.
  - unfold tsubBV. rewrite erase_self, erase_subBV.
    eapply FTField; try eassumption; [exact (IH _ _ _ H0) | reflexivity].
  - rewrite erase_self. subst Us fs.
    eapply FTNew; [reflexivity | | eassumption |].
    + apply map_ext. intros []; reflexivity.
    + clear H1 H2. unfold tsubBV in H4.
      remember (ExpNew C es) as obj in H4. clear Heqobj.
      revert Fs H4.
      induction H3 as [|a t args tys Ha Hts IHts]; intros [|f Fs] Hsub;
        inversion Hsub; subst; simpl; constructor.
      * eapply FTSub; [exact (IH _ _ _ Ha) |].
        match goal with Hs : Subtype _ _ _ |- _ =>
          apply erase_subtype in Hs; now rewrite erase_subBV in Hs
        end.
      * eauto.
  - rewrite erase_self. eapply FTLet with (nms := nms).
    + apply IH; eassumption.
    + intros y Hy. specialize (IH _ _ _ (H1 y Hy)).
      unfold unbindT in IH. now rewrite erase_open in IH.
  - eapply FTSub; [apply IH; eassumption | eapply erase_subtype; eassumption].
Qed.

(* The ordinary induction scheme does not recurse into constructor arguments. *)
Local Lemma fj_typing_ind (P : fjenv -> expr -> fjtype -> Prop)
    (bool_case : forall g b, P g (Bc b) TBool)
    (int_case : forall g n, P g (Ic n) TInt)
    (var_case : forall g x t, bound_inF x t g -> P g (FV x) t)
    (un_case : forall g e op,
      HasFJtype g e (erase (intype op)) -> P g e (erase (intype op)) ->
      P g (ExpUnOp op e) (erase (ty' op)))
    (bin_case : forall g e1 e2 op,
      HasFJtype g e1 (erase (fst (intype2 op))) ->
      P g e1 (erase (fst (intype2 op))) ->
      HasFJtype g e2 (erase (snd (intype2 op))) ->
      P g e2 (erase (snd (intype2 op))) ->
      P g (ExpBinOp op e1 e2) (erase (ty'2 op)))
    (class_case : forall g e1 e2 m t rt C ps,
      HasFJtype g e1 (TNom (TClass C)) -> P g e1 (TNom (TClass C)) ->
      m_type m C ps t rt -> HasFJtype g e2 (erase t) -> P g e2 (erase t) ->
      P g (ExpMethodInvoc e1 m e2) (erase rt))
    (interface_case : forall g e1 e2 m t rt I ps,
      HasFJtype g e1 (TNom (TInterface I)) -> P g e1 (TNom (TInterface I)) ->
      m_type_i m I ps t rt -> HasFJtype g e2 (erase t) -> P g e2 (erase t) ->
      P g (ExpMethodInvoc e1 m e2) (erase rt))
    (field_case : forall g e f C Fs i fi,
      HasFJtype g e (TNom (TClass C)) -> P g e (TNom (TClass C)) ->
      Reffields C Fs -> nth_error Fs i = Some fi -> ref fi = f ->
      P g (ExpFieldAccess e f) (erase (ReffieldType fi)))
    (new_case : forall g es C Fs,
      Reffields C Fs ->
      Forall2 (fun e t => HasFJtype g e t /\ P g e t)
        es (map erase (map ReffieldType Fs)) ->
      P g (ExpNew C es) (TNom (TClass C)))
    (let_case : forall g e b body t nms,
      HasFJtype g e b -> P g e b ->
      (forall y, ~ Elem y nms -> HasFJtype (FCons y b g) (unbind y body) t) ->
      (forall y, ~ Elem y nms -> P (FCons y b g) (unbind y body) t) ->
      P g (ExpLet e body) t)
    (sub_case : forall g e s t,
      HasFJtype g e s -> P g e s -> FJSubtype s t -> P g e t) :
    forall g e t, HasFJtype g e t -> P g e t.
Proof.
  fix IH 4.
  intros g e t H; destruct H.
  - apply bool_case.
  - apply int_case.
  - now apply var_case.
  - eapply un_case; eauto.
  - eapply bin_case; eauto.
  - eapply class_case; eauto.
  - eapply interface_case; eauto.
  - subst T; eapply field_case; eauto.
  - subst Us fs. apply new_case with Fs; [assumption |].
    clear H1. induction H2; constructor; auto.
  - eapply let_case with (nms := nms); eauto.
  - eapply sub_case; eauto.
Qed.

Local Lemma fj_sub_refl t : FJSubtype t t.
Proof. destruct t; constructor; constructor. Qed.

Local Lemma fj_sub_trans s t u :
  FJSubtype s t -> FJSubtype t u -> FJSubtype s u.
Proof.
  intros Hst Htu; destruct Htu; try solve [constructor | assumption].
  inversion Hst; subst. constructor. eapply SubCTrans; eassumption.
Qed.

Local Lemma fresh_absent xs : ~ Elem (fresh xs) xs.
Proof.
  unfold fresh, Elem, set_In.
  intros H.
  assert (Hmax : Forall (fun x => x <= list_max xs) xs).
  { apply list_max_le; reflexivity. }
  rewrite Forall_forall in Hmax. specialize (Hmax _ H); lia.
Qed.

Local Lemma fj_expr_ind (P : expr -> Prop) :
  (forall b, P (Bc b)) ->
  (forall n, P (Ic n)) ->
  (forall i, P (BV i)) ->
  (forall x, P (FV x)) ->
  (forall op e, P e -> P (ExpUnOp op e)) ->
  (forall op e1, P e1 -> forall e2, P e2 -> P (ExpBinOp op e1 e2)) ->
  (forall e1, P e1 -> forall m e2, P e2 -> P (ExpMethodInvoc e1 m e2)) ->
  (forall e, P e -> forall f, P (ExpFieldAccess e f)) ->
  (forall C es, Forall P es -> P (ExpNew C es)) ->
  (forall e1, P e1 -> forall e2, P e2 -> P (ExpLet e1 e2)) ->
  forall e, P e.
Proof.
  intros Hbc Hic Hbv Hfv Hun Hbin Hmethod Hfield Hnew Hlet.
  exact (proj1 (syntax_mutind' P (fun _ => True) (fun _ => True)
    Hbc Hic Hbv Hfv Hun Hbin Hmethod Hfield Hnew Hlet
    (fun _ _ _ => I) I (fun _ _ _ _ => I))).
Qed.

Local Lemma value_subFV e :
  isValue e -> forall x a, subFV x a e = e.
Proof.
  induction e using fj_expr_ind; simpl; try tauto.
  intros Hval x a. f_equal.
  induction H as [|e es He Hes IH]; simpl in *; [reflexivity |].
  destruct Hval; now rewrite He, IH.
Qed.

Local Lemma value_open e :
  isValue e -> forall j x, open_at j x e = e.
Proof.
  induction e using fj_expr_ind; simpl; try tauto.
  intros Hval j x. f_equal.
  induction H as [|e es He Hes IH]; simpl in *; [reflexivity |].
  destruct Hval; now rewrite He, IH.
Qed.

Local Lemma subFV_open e x a :
  isValue a -> forall j y, x <> y ->
    subFV x a (open_at j y e) = open_at j y (subFV x a e).
Proof.
  intros Ha. induction e using fj_expr_ind; intros j y Hxy; simpl;
    try solve [reflexivity | f_equal; auto].
  - destruct (j =? i); simpl; [rewrite (proj2 (Nat.eqb_neq _ _) Hxy) |]; reflexivity.
  - destruct (x =? x0); simpl; [symmetry; now apply value_open | reflexivity].
  - f_equal. induction H as [|e es He Hes IH]; simpl; auto.
    now rewrite He, IH.
Qed.

Local Lemma fresh_sub_open e :
  forall j x a, ~ Elem x (fv e) ->
    subFV x a (open_at j x e) = subBV_at j a e.
Proof.
  induction e using fj_expr_ind; intros j y a Hfresh; simpl in *;
    try solve [reflexivity | f_equal; auto].
  - destruct (j =? i); simpl; now rewrite ?Nat.eqb_refl.
  - destruct (y =? x) eqn:Heq; auto.
    apply Nat.eqb_eq in Heq; subst; exfalso; apply Hfresh.
    now left.
  - f_equal; [apply IHe1 | apply IHe2];
      intro H; apply Hfresh; apply set_union_intro; auto.
  - f_equal; [apply IHe1 | apply IHe2];
      intro H; apply Hfresh; apply set_union_intro; auto.
  - f_equal. induction H as [|e es He Hes IH]; simpl in *; auto.
    rewrite He, IH; auto;
      intro Hin; apply Hfresh; apply set_union_intro; auto.
  - f_equal; [apply IHe1 | apply IHe2];
      intro H; apply Hfresh; apply set_union_intro; auto.
Qed.

Local Lemma value_subBV e :
  isValue e -> forall j a, subBV_at j a e = e.
Proof.
  induction e using fj_expr_ind; simpl; try tauto.
  intros Hval j a. f_equal.
  induction H as [|e es He Hes IH]; simpl in *; [reflexivity |].
  destruct Hval; now rewrite He, IH.
Qed.

Local Lemma method_sub_open e :
  forall j x y r a, x <> y ->
    ~ Elem x (fv e) -> ~ Elem y (fv e) -> isValue r -> isValue a ->
    subFV y a (subFV x r (open_at (S j) x (open_at j y e))) =
    subBV_at (S j) r (subBV_at j a e).

Proof.
  induction e using fj_expr_ind;
    intros j p q r a Hpq Hp Hq Hr Ha; simpl in *;
    try solve [reflexivity | f_equal; auto].
  - destruct (j =? i) eqn:Hj; simpl.
    + rewrite (proj2 (Nat.eqb_neq _ _) Hpq).
      simpl; now rewrite ?Nat.eqb_refl, value_subBV.
    + change (subFV q a (subFV p r (if S j =? i then FV p else BV i)) =
        (if S j =? i then r else BV i)).
      destruct (S j =? i); simpl; [|reflexivity].
      rewrite Nat.eqb_refl. now rewrite value_subFV.
  - assert (p <> x) as Hpx by (intro; subst; apply Hp; now left).
    assert (q <> x) as Hqx by (intro; subst; apply Hq; now left).
    rewrite (proj2 (Nat.eqb_neq _ _) Hpx). simpl.
    now rewrite (proj2 (Nat.eqb_neq _ _) Hqx).
  - f_equal; [apply IHe1 | apply IHe2]; auto;
      intro Hin; [apply Hp | apply Hq | apply Hp | apply Hq];
      apply set_union_intro; auto.
  - f_equal; [apply IHe1 | apply IHe2]; auto;
      intro Hin; [apply Hp | apply Hq | apply Hp | apply Hq];
      apply set_union_intro; auto.
  - f_equal. induction H as [|e es He Hes IH]; simpl in *; auto.
    rewrite He, IH; auto;
      intro Hin; [apply Hp | apply Hq | apply Hp | apply Hq];
      apply set_union_intro; auto.
  - replace (S j + 1) with (S (j + 1)) by lia.
    f_equal; [apply IHe1 | apply IHe2]; auto;
      intro Hin; [apply Hp | apply Hq | apply Hp | apply Hq];
      apply set_union_intro; auto.
Qed.

Local Lemma fj_weaken g e t :
  HasFJtype g e t ->
  forall h, (forall x s, bound_inF x s g -> bound_inF x s h) ->
  HasFJtype h e t.
Proof.
  induction 1 using fj_typing_ind; intros h Hinc;
    eauto using FTBC, FTIC, FTVar, FTUnOP, FTBinOP,
      FTInvok, FTInvokI, FTField, FTSub.
  - eapply FTNew; [reflexivity | reflexivity | eassumption |].
    match goal with Hargs : Forall2 _ _ _ |- _ =>
      induction Hargs; constructor; intuition
    end.
  - eapply FTLet with (nms := nms); eauto.
    intros y Hy. apply H1; [assumption |].
    simpl; intros x s [Hhead | Htail]; auto.
Qed.

Local Lemma fj_substitute x a g e t :
  isValue a -> HasFJtype g e t ->
  forall h, (forall y s, bound_inF y s g -> HasFJtype h (subFV x a (FV y)) s) ->
  HasFJtype h (subFV x a e) t.
Proof.
  intros Ha Hty. induction Hty using fj_typing_ind; intros h Hmap; simpl;
    eauto using FTBC, FTIC, FTUnOP, FTBinOP, FTInvok, FTInvokI, FTField, FTSub.
  - eapply FTNew; [reflexivity | reflexivity | eassumption |].
    match goal with Hargs : Forall2 _ _ _ |- _ =>
      induction Hargs; simpl; constructor; intuition
    end.
  - eapply FTLet with (nms := x :: nms); eauto.
    intros y Hy. change (~ (x = y \/ Elem y nms)) in Hy.
    assert (Hxy : x <> y) by tauto.
    unfold unbind in *. rewrite <- subFV_open by assumption.
    apply H0; [tauto |].
    simpl; intros z s [[-> ->] | Hz].
    + rewrite (proj2 (Nat.eqb_neq _ _) Hxy).
      apply FTVar. left; auto.
    + eapply fj_weaken; [apply Hmap; exact Hz |].
      simpl; auto.
Qed.

Local Lemma fj_substitute_top g e t x s a :
  HasFJtype (FCons x s g) e t ->
  isValue a -> HasFJtype g a s ->
  (forall u, ~ bound_inF x u g) ->
  HasFJtype g (subFV x a e) t.
Proof.
  intros Hty Ha Hat Hfresh. eapply fj_substitute; try eassumption.
  simpl; intros y u [[-> ->] | Hy].
  - now rewrite Nat.eqb_refl.
  - destruct (x =? y) eqn:Hxy.
    + apply Nat.eqb_eq in Hxy; subst; now specialize (Hfresh _ Hy).
    + now apply FTVar.
Qed.

(* Method signatures transport through inheritance and interface implementation. *)
Local Lemma method_find_in m (ms : list MethodDefn) md :
  find m ms = Some md -> In md ms /\ ref md = m.
Proof.
  induction ms as [|a ms IH]; [discriminate |].
  change ((if m =? ref a then Some a else find m ms) = Some md -> In md (a :: ms) /\ ref md = m).
  destruct (m =? ref a) eqn:Heq; intros H.
  - inversion H; subst. apply Nat.eqb_eq in Heq; simpl; auto.
  - apply IH in H. simpl; tauto.
Qed.

Local Lemma method_entry_ok C D Is Fs nf K Ms nm m md :
  find C RefCT = Some (RefCDecl C D Is Fs nf K Ms nm) ->
  find m Ms = Some md -> MType_OK C md.
Proof.
  intros Hclass Hmethod.
  pose proof (cok _ _ _ _ _ _ _ _ Hclass) as Hvalid.
  inversion Hvalid; subst. eapply Forall_forall; [eassumption |].
  exact (proj1 (method_find_in _ _ _ Hmethod)).
Qed.

Local Definition fj_method (m : MethodName) (N : nomtype) :=
  match N with
  | TClass C => m_type m C
  | TInterface J => m_type_i m J
  end.

Local Lemma fj_override C D Is Fs nf K Ms nm m p t r :
  find C RefCT = Some (RefCDecl C D Is Fs nf K Ms nm) ->
  m_type m D p t r ->
  exists p' t' r', m_type m C p' t' r' /\
    FJSubtype (erase t) (erase t') /\ FJSubtype (erase r') (erase r).
Proof.
  intros Hclass Hparent.
  destruct (find m Ms) as [md|] eqn:Hlookup.
  - pose proof (method_entry_ok _ _ _ _ _ _ _ _ _ _ Hclass Hlookup) as Hvalid.
    destruct Hvalid as [p' r' t' body C D' Is' Fs' nf' K' Ms' nm' m'
      Hclass' Hlookup' Hover Hwf Hwfa Hwfr Hbody Hfv Hft Hfr].
    assert (D' = D) by congruence. subst D'.
    pose proof (proj2 (method_find_in _ _ _ Hlookup)) as Hname.
    change (m' = m) in Hname.
    subst m'.
    destruct (Hover _ _ _ Hparent) as [_ [Ha Hr]].
    exists p', t', r'. split; [eapply mty_ok; eassumption |].
    unfold subtype_under, subtype_under2 in Ha, Hr.
    specialize (Ha 0). specialize (Hr 0 1 ltac:(lia)).
    apply erase_subtype in Ha, Hr. rewrite !erase_open in Ha; rewrite !erase_open in Hr; auto.
  - exists p, t, r. split; [eapply mty_no_override; eassumption |].
    auto using fj_sub_refl.
Qed.

Local Lemma fj_implementation C D Is Fs nf K Ms nm J i m p t r :
  find C RefCT = Some (RefCDecl C D Is Fs nf K Ms nm) ->
  nth_error Is i = Some J -> m_type_i m J p t r ->
  exists p' t' r', m_type m C p' t' r' /\
    FJSubtype (erase t) (erase t') /\ FJSubtype (erase r') (erase r).
Proof.
  intros Hclass Hi Hmethod.
  pose proof (cok _ _ _ _ _ _ _ _ Hclass) as Hvalid.
  assert (Himpl : Class_implemented C J).
  { inversion Hvalid; subst; eauto. }
  destruct Himpl as [C J ms nd Htable Himpl].
  inversion Hmethod as [I' ms' m' r' t' p' nd' Htable' Hlookup]; subst.
  assert (ms' = ms) by congruence. subst ms'.
  specialize (Himpl _ _ _ _ Hlookup). unfold implement in Himpl.
  destruct Himpl as (ta & tr & pa & Hm & _ & Ha & Hr).
  exists pa, ta, tr. split; [assumption |].
  unfold subtype_under, subtype_under2 in Ha, Hr.
  specialize (Ha 0). specialize (Hr 0 1 ltac:(lia)).
  apply erase_subtype in Ha, Hr. rewrite !erase_open in Ha; rewrite !erase_open in Hr; auto.
Qed.

Local Lemma fj_method_inherited N N' :
  SubClass N N' -> forall m p t r, fj_method m N' p t r ->
  exists p' t' r', fj_method m N p' t' r' /\
    FJSubtype (erase t) (erase t') /\ FJSubtype (erase r') (erase r).
Proof.
  induction 1; intros m p t r Hm; simpl in *.
  - exists p, t, r; auto using fj_sub_refl.
  - destruct (IHSubClass2 _ _ _ _ Hm) as (p2 & t2 & r2 & H2 & Ha2 & Hr2).
    destruct (IHSubClass1 _ _ _ _ H2) as (p1 & t1 & r1 & H1 & Ha1 & Hr1).
    exists p1, t1, r1; eauto using fj_sub_trans.
  - eapply fj_override; eassumption.
  - eapply fj_implementation; eassumption.
Qed.

Local Lemma fj_method_body m C p t r :
  m_type m C p t r ->
  exists body D, m_body m C body /\ SubClass (TClass C) (TClass D) /\
    fv body = empty /\
    forall x y, x <> y ->
      HasFJtype (FCons y (erase t) (FCons x (TNom (TClass D)) FEmpty))
        (open_at 1 x (open_at 0 y body)) (erase r).
Proof.
  induction 1.
  - exists e, C. split; [eapply mbdy_ok; eassumption |].
    split; [constructor |].
    pose proof (method_entry_ok _ _ _ _ _ _ _ _ _ _ H H0) as Hvalid.
    inversion Hvalid as [p' r' t' body C' D' Is' Fs' nf' K' Ms' nm' m'
      Hclass' Hlookup' Hover Hwf Hwfa Hwfr Hbody Hfv Hft Hfr]; subst.
    split; [assumption |].
    intros x y Hxy. pose proof (erase_typing _ _ _ (Hbody x y Hxy)) as Herased.
    simpl erase_env in Herased. now rewrite !erase_open in Herased.
  - destruct IHm_type as (body & owner & Hbody & Howner & Hfv & Hty).
    exists body, owner. split; [eapply mbdy_no_override; eassumption |].
    split; [|auto].
    eapply SubCTrans; [eapply SubCInh |]; eassumption.
Qed.

(* A subclass extends its superclass field list at the end. *)
Local Definition fj_fields (N : nomtype) (Fs : list RefFieldDecl) : Prop :=
  match N with
  | TClass C => Reffields C Fs
  | TInterface _ => False
  end.

Local Lemma fields_functional C Fs :
  Reffields C Fs -> forall Gs, Reffields C Gs -> Fs = Gs.
Proof.
  induction 1 as [|C D Is fs nf K Ms nm parent Htable Hparent IH Hnd].
  - intros Gs HG. inversion HG; subst; [reflexivity |].
    rewrite obj_notin_dom in H; discriminate.
  - intros Gs HG. inversion HG; subst.
    + rewrite obj_notin_dom in Htable; discriminate.
    + match goal with
      | Hother : find C RefCT = Some (RefCDecl C ?D' _ ?fs' _ _ _ _) |- _ =>
        assert (D' = D) by congruence;
        assert (fs' = fs) by congruence
      end.
      subst. f_equal. now apply IH.
Qed.

Local Lemma fields_names_unique C Fs :
  Reffields C Fs -> NoDup (refs Fs).
Proof. destruct 1; [constructor | assumption]. Qed.

Local Lemma fields_prefix N N' :
  SubClass N N' ->
  forall Fs, fj_fields N' Fs -> exists tail, fj_fields N (Fs ++ tail).
Proof.
  induction 1; intros Fs' HFs.
  - exists nil; now rewrite app_nil_r.
  - destruct (IHSubClass2 _ HFs) as [tail Htail].
    destruct (IHSubClass1 _ Htail) as [tail' Htail'].
    exists (tail ++ tail'); now rewrite app_assoc.
  - simpl in *. exists fs.
    pose proof (cok _ _ _ _ _ _ _ _ H) as Hvalid.
    inversion Hvalid; subst.
    match goal with
    | Hparent : Reffields D ?parent, Hnodup : NoDup (refs (?parent ++ fs)) |- _ =>
      pose proof (fields_functional _ _ HFs _ Hparent) as Heq; subst
    end.
    eapply RefF_Decl; eassumption.
  - contradiction.
Qed.

Local Lemma fj_new_inv g C es t :
  HasFJtype g (ExpNew C es) t ->
  FJSubtype (TNom (TClass C)) t /\
  exists Fs, Reffields C Fs /\
    Forall2 (HasFJtype g) es (map erase (map ReffieldType Fs)).
Proof.
  intros Hty. remember (ExpNew C es) as obj eqn:He.
  induction Hty; inversion He; subst; try clear He.
  - split; [apply fj_sub_refl | eauto].
  - destruct (IHHty eq_refl); eauto using fj_sub_trans.
Qed.

Local Lemma fj_bool_inv g b t :
  HasFJtype g (Bc b) t -> FJSubtype TBool t.
Proof.
  intros Hty. remember (Bc b) as e eqn:He.
  induction Hty; inversion He; subst; eauto using fj_sub_refl, fj_sub_trans.
Qed.

Local Lemma fj_int_inv g n t :
  HasFJtype g (Ic n) t -> FJSubtype TInt t.
Proof.
  intros Hty. remember (Ic n) as e eqn:He.
  induction Hty; inversion He; subst; eauto using fj_sub_refl, fj_sub_trans.
Qed.

Local Lemma fj_bool_value g e :
  HasFJtype g e TBool -> isValue e -> exists b, e = Bc b.
Proof.
  intros Hty Hv; destruct e; try contradiction; eauto.
  - apply fj_int_inv in Hty; inversion Hty.
  - apply fj_new_inv in Hty as [Hsub _]; inversion Hsub.
Qed.

Local Lemma fj_nominal_value g e N :
  HasFJtype g e (TNom N) -> isValue e ->
  exists C es, e = ExpNew C es /\ SubClass (TClass C) N.
Proof.
  intros Hty Hv; destruct e; try contradiction.
  - apply fj_bool_inv in Hty; inversion Hty.
  - apply fj_int_inv in Hty; inversion Hty.
  - apply fj_new_inv in Hty as [Hsub _]; inversion Hsub; subst. eauto.
Qed.

Local Lemma fj_dispatch C es m a N p t r :
  HasFJtype FEmpty (ExpNew C es) (TNom N) ->
  fj_method m N p t r ->
  HasFJtype FEmpty a (erase t) ->
  isValue (ExpNew C es) -> isValue a ->
  exists body, m_body m C body /\
    HasFJtype FEmpty (subBV_at 1 (ExpNew C es) (subBV a body)) (erase r).
Proof.
  intros Hrecv Hsig Harg Hvr Hva.
  pose proof (fj_new_inv _ _ _ _ Hrecv) as [Hnom _].
  inversion Hnom as [| | |src dst Hsub]; subst.
  destruct (fj_method_inherited _ _ Hsub _ _ _ _ Hsig)
    as (p' & t' & r' & Hsig' & Ha & Hr).
  destruct (fj_method_body _ _ _ _ _ Hsig')
    as (body & owner & Hbody & Howner & Hfv & Htyped).
  exists body. split; [exact Hbody |].
  assert (Hxy : 0 <> 1) by lia.
  specialize (Htyped 0 1 Hxy).
  assert (Hown : HasFJtype FEmpty (ExpNew C es) (TNom (TClass owner))).
  { destruct (fj_new_inv _ _ _ _ Hrecv) as [_ (Fs & HFs & Hargs)].
    eapply FTSub with (s := TNom (TClass C)); [|now apply SubBClass].
    eapply FTNew; [reflexivity | reflexivity | eassumption | eassumption]. }
  assert (Hs : HasFJtype (FCons 1 (erase t') FEmpty)
    (subFV 0 (ExpNew C es) (open_at 1 0 (open_at 0 1 body))) (erase r')).
  { eapply fj_substitute with (g := FCons 1 (erase t') (FCons 0 (TNom (TClass owner)) FEmpty));
      [exact Hvr | exact Htyped |].
    simpl. intros y u [[-> ->] | [[-> ->] | Hbad]].
    - apply FTVar; simpl; auto.
    - eapply fj_weaken; [exact Hown | simpl; tauto].
    - contradiction. }
  assert (Hres := fj_substitute_top _ _ _ _ _ _ Hs Hva
    (FTSub _ _ _ _ Harg Ha) ltac:(simpl; tauto)).
  rewrite (method_sub_open body 0 0 1) in Hres; auto.
  - eapply FTSub; eassumption.
  - rewrite Hfv; simpl; tauto.
  - rewrite Hfv; simpl; tauto.
Qed.

Local Lemma args_at {A B : Type} (R : A -> B -> Prop) xs ys i :
  Forall2 R xs ys -> forall x, nth_error xs i = Some x ->
  exists y, nth_error ys i = Some y /\ R x y.
Proof.
  intros H; revert i. induction H; intros [|i] z Hz;
    simpl in Hz; try discriminate; eauto.
  inversion Hz; subst. exists y; auto.
Qed.

Local Lemma fj_field_index g C es D Fs i fi :
  HasFJtype g (ExpNew C es) (TNom (TClass D)) ->
  Reffields D Fs -> nth_error Fs i = Some fi ->
  exists Gs ei, Reffields C Gs /\ nth_error Gs i = Some fi /\
    nth_error es i = Some ei /\ HasFJtype g ei (erase (ReffieldType fi)).
Proof.
  intros Hty HFs Hi.
  destruct (fj_new_inv _ _ _ _ Hty) as [Hnom (Gs & HGs & Hargs)].
  inversion Hnom as [| | |src dst Hsub]; subst.
  destruct (fields_prefix _ _ Hsub _ HFs) as [tail Hpref].
  simpl in Hpref. pose proof (fields_functional _ _ HGs _ Hpref) as Heq. subst Gs.
  assert (Hi' : nth_error (Fs ++ tail) i = Some fi).
  { rewrite nth_error_app1; [exact Hi |].
    apply nth_error_Some. congruence. }
  assert (Hmapped : nth_error (map erase (map ReffieldType (Fs ++ tail))) i =
      Some (erase (ReffieldType fi))) by now rewrite !nth_error_map, Hi'.
  destruct (args_at _ _ _ _ (Forall2_flip Hargs) _ Hmapped)
    as (ei & Hei & Htei).
  exists (Fs ++ tail), ei. auto.
Qed.

Local Lemma method_body_functional m C body :
  m_body m C body -> forall body', m_body m C body' -> body = body'.
Proof.
  intros H; induction H; intros body' Hbody';
    inversion Hbody' as
      [C' D' Is' m' p' r' t' e' Fs' K' Ms' nf' nm' Htable' Hlookup'
      |C' D' Is' m' e' Fs' K' Ms' nf' nm' Htable' Hlookup' Hparent'];
    subst;
    assert (Ms' = Ms) by congruence; subst Ms'; try congruence.
  assert (D' = D) by congruence. subst D'. auto.
Qed.

Local Lemma fj_field_reduct g C es D Fs i fi Gs j fj ej :
  HasFJtype g (ExpNew C es) (TNom (TClass D)) ->
  Reffields D Fs -> nth_error Fs i = Some fi ->
  Reffields C Gs -> nth_error Gs j = Some fj ->
  ref fi = ref fj -> nth_error es j = Some ej ->
  HasFJtype g ej (erase (ReffieldType fi)).
Proof.
  intros Hty HFs Hi HGs Hj Hname Hej.
  destruct (fj_field_index _ _ _ _ _ _ _ Hty HFs Hi)
    as (Gs' & ei & HGs' & Hi' & Hei & Htei).
  pose proof (fields_functional _ _ HGs _ HGs') as Heq. subst Gs'.
  assert (Hindex : i = j).
  { apply (proj1 (NoDup_nth_error _) (fields_names_unique _ _ HGs)).
    - unfold refs; rewrite length_map. apply nth_error_Some. congruence.
    - unfold refs. rewrite !nth_error_map, Hi', Hj. change (Some (ref fi) = Some (ref fj)). now rewrite Hname. }
  subst j. assert (ei = ej) by congruence. now subst ei.
Qed.

Local Lemma fj_let_reduct e b body t nms :
  HasFJtype FEmpty e b -> isValue e ->
  (forall y, ~ Elem y nms -> HasFJtype (FCons y b FEmpty) (unbind y body) t) ->
  HasFJtype FEmpty (subBV e body) t.
Proof.
  intros He Hv Hbody.
  set (y := fresh (nms ++ fv body)).
  assert (Hy := fresh_absent (nms ++ fv body)).
  change (~ In y (nms ++ fv body)) in Hy.
  rewrite in_app_iff in Hy.
  unfold subBV. rewrite <- (fresh_sub_open body 0 y) by tauto.
  eapply fj_substitute_top; [apply Hbody; tauto | exact Hv | exact He |].
  simpl; tauto.
Qed.

Local Definition can_step e := exists e', Step e e'.

Local Lemma fj_invoke_progress e1 e2 m N p t r :
  HasFJtype FEmpty e1 (TNom N) -> fj_method m N p t r ->
  HasFJtype FEmpty e2 (erase t) ->
  (isValue e1 \/ can_step e1) -> (isValue e2 \/ can_step e2) ->
  can_step (ExpMethodInvoc e1 m e2).
Proof.
  intros H1 Hm H2 [Hv1 | [e1' Hstep1]] [Hv2 | [e2' Hstep2]];
    try solve [eexists; eauto using Refc_Invok1, Refc_Invok2].
  destruct (fj_nominal_value _ _ _ H1 Hv1) as (C & es & -> & _).
  destruct (fj_dispatch _ _ _ _ _ _ _ _ H1 Hm H2 Hv1 Hv2) as [body [Hb _]].
  eexists; eauto using Refc_Invok3.
Qed.

Local Lemma fj_args_progress es Ts :
  Forall2 (fun e (_ : fjtype) => isValue e \/ can_step e) es Ts ->
  Forall isValue es \/
  exists es' i ei ei', Step ei ei' /\
    nth_error es i = Some ei /\ nth_error es' i = Some ei' /\
    (forall j, j <> i -> nth_error es j = nth_error es' j) /\ length es = length es'.
Proof.
  induction 1 as [|e t es ts He Hes IH].
  - left; constructor.
  - destruct He as [Hv | [e' Hstep]].
    + destruct IH as [Hvs | (es' & i & ei & ei' & Hstep & Hi & Hi' & Hother & Hlen)].
      * left; now constructor.
      * right. exists (e :: es'), (S i), ei, ei'. simpl.
        repeat split; auto. intros [|j] Hj; simpl; auto.
    + right. exists (e' :: es), 0, e, e'. simpl.
      repeat split; auto. intros [|j] Hj; [contradiction | reflexivity].
Qed.

Local Lemma new_is_value C es :
  Forall isValue es -> isValue (ExpNew C es).
Proof. induction 1; simpl; auto. Qed.

Local Lemma fj_progress e t :
  HasFJtype FEmpty e t -> isValue e \/ can_step e.
Proof.
  intros Hty. remember FEmpty as g eqn:Hg.
  induction Hty using fj_typing_ind; subst g.
  - left; exact I.
  - left; exact I.
  - contradiction.
  - right. destruct IHHty as [Hv | [e' Hstep]]; auto.
    + destruct op. destruct (fj_bool_value _ _ Hty Hv) as [b ->].
      eexists; apply EUnOp2 with (pf := isCpt_Not b); exact I.
    + exists (ExpUnOp op e'). now apply EUnOp1.
  - right. specialize (IHHty1 eq_refl). specialize (IHHty2 eq_refl).
    destruct IHHty1 as [Hv1 | [e1' Hs1]]; [|exists (ExpBinOp op e1' e2); now apply EBinOp1].
    destruct IHHty2 as [Hv2 | [e2' Hs2]]; [|exists (ExpBinOp op e1 e2'); now apply EBinOp2].
    destruct op.
    + destruct (fj_bool_value _ _ Hty1 Hv1) as [b1 ->].
      destruct (fj_bool_value _ _ Hty2 Hv2) as [b2 ->].
      eexists; apply EBinOp3 with (pf := isCpt_And b1 b2); exact I.
    + destruct (fj_bool_value _ _ Hty1 Hv1) as [b1 ->].
      destruct (fj_bool_value _ _ Hty2 Hv2) as [b2 ->].
      eexists; apply EBinOp3 with (pf := isCpt_Or b1 b2); exact I.
    + eexists; exact (EBinOp3 _ _ _ (isCpt_Eq _ _ Hv1 Hv2) Hv1 Hv2).
  - right; eapply fj_invoke_progress with (N := TClass C); eauto.
  - right; eapply fj_invoke_progress with (N := TInterface I); eauto.
  - right. destruct IHHty as [Hv | [e' Hstep]]; auto.
    + destruct (fj_nominal_value _ _ _ Hty Hv) as (D & es & -> & _).
      destruct (fj_field_index _ _ _ _ _ _ _ Hty H H0)
        as (Gs & ei & HGs & Hi & Hei & _).
      subst f. eexists; eauto using Refc_Field.
    + exists (ExpFieldAccess e' f); now apply RefRC_Field.
  - pose proof (Forall2_impl (fun e (_ : fjtype) => isValue e \/ can_step e)
      (fun _ _ Ha => proj2 Ha eq_refl) H0) as Hprogress.
    destruct (fj_args_progress _ _ Hprogress) as [Hvs | (es' & i & ei & ei' & Hs & Hi & Hi' & Hother & Hlen)].
    + left; now apply new_is_value.
    + right. exists (ExpNew C es'). eapply RefRC_New_Arg; eassumption.
  - right. destruct IHHty as [Hv | [e' Hstep]]; auto.
    + exists (subBV e body); now apply ELetV.
    + exists (ExpLet e' body); now apply ELet.
  - auto.
Qed.

Local Lemma fj_invoke_reduct C es m a N p t r body :
  HasFJtype FEmpty (ExpNew C es) (TNom N) ->
  fj_method m N p t r ->
  HasFJtype FEmpty a (erase t) ->
  m_body m C body -> isValue a -> isValue (ExpNew C es) ->
  HasFJtype FEmpty (subBV_at 1 (ExpNew C es) (subBV a body)) (erase r).
Proof.
  intros Hrecv Hsig Harg Hbody Hva Hvr.
  destruct (fj_dispatch _ _ _ _ _ _ _ _ Hrecv Hsig Harg Hvr Hva)
    as (body' & Hbody' & Hty).
  now rewrite (method_body_functional _ _ _ Hbody _ Hbody').
Qed.

Local Lemma fj_args_preserved es Ts es' i ei ei' :
  Forall2 (fun e t => HasFJtype FEmpty e t /\
    (forall e', Step e e' -> HasFJtype FEmpty e' t)) es Ts ->
  Step ei ei' -> nth_error es i = Some ei -> nth_error es' i = Some ei' ->
  (forall j, j <> i -> nth_error es j = nth_error es' j) ->
  length es = length es' ->
  Forall2 (HasFJtype FEmpty) es' Ts.
Proof.
  intros Hargs Hstep. revert es' i.
  induction Hargs as [|a t es Ts [Ha IH_a] Hargs IH_es];
    intros es' i Hi Hi' Hother Hlen.
  - destruct i; discriminate.
  - destruct es' as [|a' es']; [discriminate |].
    destruct i as [|i]; simpl in Hi, Hi'.
    + inversion Hi; inversion Hi'; subst a a'.
      assert (es = es') as ->.
      { apply nth_error_ext. intros j. exact (Hother (S j) (Nat.neq_succ_0 j)). }
      constructor; [now apply IH_a |].
      eapply Forall2_impl; [|exact Hargs]. intros x s Hx; exact (proj1 Hx).
    + assert (Hhead : Some a = Some a') by exact (Hother 0 (Nat.neq_0_succ i)).
      inversion Hhead; subst a'. constructor; [exact Ha |].
      eapply IH_es; try eassumption.
      * intros j Hj. apply (Hother (S j)). congruence.
      * now inversion Hlen.
Qed.

Local Lemma fj_preservation e e' t :
  HasFJtype FEmpty e t -> Step e e' -> HasFJtype FEmpty e' t.
Proof.
  intros Hty. revert e'. remember FEmpty as g eqn:Hg.
  induction Hty using fj_typing_ind; intros e' Hstep; subst g;
    try solve [eapply FTSub; [eapply IHHty; [reflexivity | exact Hstep] | eassumption]];
    inversion Hstep; subst.
  - destruct op, c. apply FTUnOP; eauto.
  - destruct op, pf; destruct b; apply FTBC.
  - apply FTBinOP; eauto.
  - apply FTBinOP; eauto.
  - destruct pf; apply FTBC.
  - eapply FTInvok; eauto.
  - eapply FTInvok; eauto.
  - eapply fj_invoke_reduct with (N := TClass C); eauto.
  - eapply FTInvokI; eauto.
  - eapply FTInvokI; eauto.
  - eapply fj_invoke_reduct with (N := TInterface I); eauto.
  - eapply fj_field_reduct; eauto.
  - eapply FTField; eauto.
  - eapply FTNew; [reflexivity | reflexivity | eassumption |].
    eapply fj_args_preserved; try eassumption.
    eapply Forall2_impl; [|eassumption].
    intros a t [Ha IH]; split; [exact Ha | exact (IH eq_refl)].
  - eapply FTLet with (nms := nms); eauto.
  - eapply fj_let_reduct; eauto.
Qed.

Theorem type_soundness : forall (e e':expr) (t:type),
    EvalsTo e e' -> Hastype Empty e t -> isValue e' \/  exists e'', Step e' e''.
Proof.
  intros e e' t Heval Hty.
  pose proof (erase_typing _ _ _ Hty) as Hfj. simpl in Hfj.
  clear Hty. induction Heval.
  - eapply fj_progress; exact Hfj.
  - apply IHHeval. eapply fj_preservation; eassumption.
Qed.
