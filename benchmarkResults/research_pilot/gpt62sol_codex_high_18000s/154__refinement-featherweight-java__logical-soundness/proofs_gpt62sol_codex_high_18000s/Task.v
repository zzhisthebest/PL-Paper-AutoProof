Require Import Definitions.Syntax Definitions.Semantics Definitions.Typing
  Definitions.CTSanity Definitions.SubDenotation.

From Stdlib Require Import List ListSet Arith Lia Bool ZArith.
Require Import Definitions.FJTyping RFJ.Utils.Referable.

Local Lemma ls_expr_ind (P : expr -> Prop) :
  (forall b, P (Bc b)) ->
  (forall i, P (Ic i)) ->
  (forall i, P (BV i)) ->
  (forall x, P (FV x)) ->
  (forall o e, P e -> P (ExpUnOp o e)) ->
  (forall o e d, P e -> P d -> P (ExpBinOp o e d)) ->
  (forall e m d, P e -> P d -> P (ExpMethodInvoc e m d)) ->
  (forall e f, P e -> P (ExpFieldAccess e f)) ->
  (forall c es, Forall P es -> P (ExpNew c es)) ->
  (forall e d, P e -> P d -> P (ExpLet e d)) ->
  forall e, P e.
Proof.
  intros B Int BV' FV' U Bi M F N L.
  exact (proj1 (syntax_mutind' P (fun _ => True) (fun _ => True)
    B Int BV' FV' U (fun o e He d Hd => Bi o e d He Hd)
    (fun e He m d Hd => M e m d He Hd) (fun e He f => F e f He)
    N (fun e He d Hd => L e d He Hd)
    (fun _ _ _ => I) I (fun _ _ _ _ => I))).
Qed.

(* The index bounds the height of the evaluation tree. *)
Inductive ls_eval : nat -> expr -> expr -> Prop :=
| ls_bool : forall n b, ls_eval (S n) (Bc b) (Bc b)
| ls_int : forall n i, ls_eval (S n) (Ic i) (Ic i)
| ls_un : forall n o e a r,
    ls_eval n e a -> udelta' o a = Some r ->
    ls_eval (S n) (ExpUnOp o e) r
| ls_bin : forall n o e d a b r,
    ls_eval n e a -> ls_eval n d b -> bdelta' o a b = Some r ->
    ls_eval (S n) (ExpBinOp o e d) r
| ls_new : forall n c es vs,
    Forall2 (ls_eval n) es vs -> ls_eval (S n) (ExpNew c es) (ExpNew c vs)
| ls_field : forall n e f c vs fs i fi r,
    ls_eval n e (ExpNew c vs) ->
    Reffields c fs -> nth_error fs i = Some fi -> ref fi = f ->
    nth_error vs i = Some r ->
    ls_eval (S n) (ExpFieldAccess e f) r
| ls_call : forall n e m d c vs a body r,
    ls_eval n e (ExpNew c vs) -> ls_eval n d a -> m_body m c body ->
    ls_eval n (subBV_at 1 (ExpNew c vs) (subBV a body)) r ->
    ls_eval (S n) (ExpMethodInvoc e m d) r
| ls_let : forall n e d a r,
    ls_eval n e a -> ls_eval n (subBV a d) r ->
    ls_eval (S n) (ExpLet e d) r.

Local Definition ls_runs e v := exists n, ls_eval n e v.

Local Lemma ls_values_new c es :
  isValue (ExpNew c es) <-> Forall isValue es.
Proof.
  change ((fix go l := match l with nil => True | (a :: l)%list => isValue a /\ go l end) es
          <-> Forall isValue es).
  induction es; simpl.
  - split; intro; constructor.
  - rewrite IHes. split.
    + intros [Ha Hes]; now constructor.
    + intro H; inversion H; auto.
Qed.

Local Lemma ls_forall2_map_rel {A B} (P Q : A -> B -> Prop) xs ys :
  (forall x y, P x y -> Q x y) -> Forall2 P xs ys -> Forall2 Q xs ys.
Proof. intros HP H; induction H; constructor; auto. Qed.

Local Lemma ls_eval_raise n e v :
  ls_eval n e v -> ls_eval (S n) e v.
Proof.
  revert e v; induction n; intros e v H; inversion H; subst; try solve [econstructor; eauto].
  apply ls_new. eapply ls_forall2_map_rel; eauto.
Qed.

Local Lemma ls_eval_le n k e v : n <= k -> ls_eval n e v -> ls_eval k e v.
Proof. intros H; induction H; auto using ls_eval_raise. Qed.

Local Lemma ls_eval_value n e v : ls_eval n e v -> isValue v.
Proof.
  revert e v; induction n; intros e v H; inversion H; subst; try exact I; eauto.
  - destruct o, a; cbn in *; try discriminate. destruct b; inversion H2; exact I.
  - destruct o, a, b; cbn in *; try discriminate; inversion H3; exact I.
  - apply ls_values_new. match goal with F : Forall2 _ _ _ |- _ => clear H; induction F end; constructor; eauto.
  - eapply Forall_forall; [apply (proj1 (ls_values_new _ _) (ltac:(eapply IHn; eassumption)))|].
    eapply nth_error_In; eauto.
Qed.

Local Lemma ls_value_runs v : isValue v -> ls_runs v v.
Proof.
  induction v using ls_expr_ind; intro V; try contradiction.
  - exists 1; constructor.
  - exists 1; constructor.
  - apply ls_values_new in V. assert (exists n, Forall2 (ls_eval n) es es) as [n Hn].
    { induction H as [|a es Ha Hes IH]; inversion V as [|? ? Va Ves]; subst.
      - exists 0; constructor.
      - destruct (Ha Va) as [n1 H1], (IH Ves) as [n2 Hn2].
        exists (max n1 n2); constructor.
        + eapply ls_eval_le; eauto using Nat.le_max_l.
        + eapply ls_forall2_map_rel; [|eassumption].
          intros; eapply ls_eval_le; eauto using Nat.le_max_r. }
    exists (S n); now constructor.
Qed.

(* Substitution and freshness for the locally nameless syntax. *)
Local Lemma ls_union x a b : Elem x (union a b) <-> Elem x a \/ Elem x b.
Proof. split; [apply set_union_elim|intros [H|H]; [apply set_union_intro1|apply set_union_intro2]; exact H]. Qed.

Local Lemma ls_add x y a : Elem x (names_add y a) <-> x = y \/ Elem x a.
Proof.
  split.
  - intro H; apply set_add_elim in H; intuition.
  - intros [->|H]; [apply set_add_intro2|apply set_add_intro1]; auto.
Qed.

Local Lemma ls_fresh xs : ~ Elem (fresh xs) xs.
Proof.
  unfold fresh, Elem, set_In. intro H.
  pose proof (proj1 (list_max_le xs (list_max xs)) (Nat.le_refl _) ) as F.
  apply Forall_forall with (x := 1 + list_max xs) in F; lia || assumption.
Qed.

Local Lemma ls_bv_unused e :
  forall k w, isLC_at k e -> subBV_at k w e = e.
Proof.
  induction e using ls_expr_ind; intros k w L; cbn in *; try reflexivity;
    try solve [f_equal; intuition].
  - destruct (k =? i)%nat eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal. induction H; cbn in *; auto. destruct L; f_equal; auto.
Qed.

Local Lemma ls_fv_unused e :
  forall x w, ~ Elem x (fv e) -> subFV x w e = e.
Proof.
  induction e using ls_expr_ind; intros y w N; cbn [fv subFV] in *;
    try reflexivity; try solve [f_equal; eauto].
  - destruct (y =? x)%nat eqn:E; [|reflexivity].
    apply Nat.eqb_eq in E; subst. exfalso; apply N, ls_add; auto.
  - rewrite ls_union in N. f_equal; intuition.
  - rewrite ls_union in N. f_equal; intuition.
  - f_equal. induction H; cbn in *; auto.
    rewrite ls_union in N. f_equal; intuition.
  - rewrite ls_union in N. f_equal; intuition.
Qed.

Local Lemma ls_value_closed e :
  isValue e -> (forall k, isLC_at k e) /\ (forall x, ~ Elem x (fv e)).
Proof.
  induction e using ls_expr_ind; intro V; try contradiction;
    try solve [split; unfold Elem, set_In, empty; simpl; intuition].
  induction H as [|a es Ha Hes IH]; cbn [fv isValue] in *.
  - split; unfold Elem, set_In, empty; simpl; intuition.
  - destruct V as [Va Ves]. destruct (Ha Va) as [La Fa], (IH Ves) as [Les Fes].
    split.
    + intro k; change (isLC_at k a /\ isLC_at k (ExpNew c es)); auto.
    + intro x; change (~ Elem x (union (fv a) (fv (ExpNew c es)))); rewrite ls_union.
      intros [Hx|Hx]; [exact (Fa x Hx)|exact (Fes x Hx)].
Qed.

Local Lemma ls_pfv_unused ps x w :
  ~ Elem x (fvP ps) -> psubFV x w ps = ps.
Proof.
  induction ps; cbn; auto. rewrite ls_union. intros N.
  f_equal; auto using ls_fv_unused.
Qed.

Local Lemma ls_pbv_unused ps k w :
  isLCP_at k ps -> psubBV_at k w ps = ps.
Proof. induction ps; cbn; intros H; auto. destruct H; f_equal; auto using ls_bv_unused. Qed.

Local Lemma ls_open_sub e :
  forall x k w, ~ Elem x (fv e) ->
  subFV x w (open_at k x e) = subBV_at k w e.
Proof.
  induction e using ls_expr_ind; intros y k w N; cbn [fv subFV open_at subBV_at] in *;
    try reflexivity; try solve [f_equal; eauto].
  - destruct (k =? i)%nat; cbn; now rewrite ?Nat.eqb_refl.
  - change (subFV y w (FV x) = FV x). now apply ls_fv_unused.
  - rewrite ls_union in N. f_equal; intuition.
  - rewrite ls_union in N. f_equal; intuition.
  - f_equal. induction H; cbn in *; auto.
    rewrite ls_union in N. f_equal; intuition.
  - rewrite ls_union in N. f_equal; intuition.
Qed.

Local Lemma ls_popen_sub ps x k w :
  ~ Elem x (fvP ps) -> psubFV x w (openP_at k x ps) = psubBV_at k w ps.
Proof.
  induction ps; cbn; auto. rewrite ls_union. intros N. f_equal; auto using ls_open_sub.
Qed.

Local Lemma ls_fv_bv e :
  forall x u j w, isValue u ->
    subFV x u (subBV_at j w e) = subBV_at j (subFV x u w) (subFV x u e).
Proof.
  induction e using ls_expr_ind; intros y u j w V; cbn; try reflexivity;
    try solve [f_equal; auto].
  - now destruct (j =? i)%nat.
  - destruct (y =? x)%nat; cbn; auto.
    symmetry; apply ls_bv_unused, (proj1 (ls_value_closed _ V)).
  - f_equal. induction H; cbn; auto. f_equal; auto.
Qed.

Local Lemma ls_pfv_bv ps x u j w :
  isValue u ->
  psubFV x u (psubBV_at j w ps) = psubBV_at j (subFV x u w) (psubFV x u ps).
Proof. induction ps; cbn; intros; f_equal; auto using ls_fv_bv. Qed.


Local Lemma ls_open_as_bv e :
  forall j x, open_at j x e = subBV_at j (FV x) e.
Proof.
  induction e using ls_expr_ind; intros j y; cbn; try reflexivity;
    try solve [f_equal; auto].
  f_equal. induction H; cbn; auto. f_equal; auto.
Qed.

Local Lemma ls_fields_unique c fs gs :
  Reffields c fs -> Reffields c gs -> fs = gs.
Proof.
  intros F; revert gs; induction F; intros gs G; inversion G; subst; auto.
  - rewrite obj_notin_dom in H; discriminate.
  - rewrite obj_notin_dom in H; discriminate.
  - match goal with
    | A : find ?C RefCT = Some _, B : find ?C RefCT = Some _ |- _ =>
        rewrite A in B; injection B; intros; subst
    end.
    f_equal; auto.
Qed.

Local Lemma ls_body_unique m c body body' :
  m_body m c body -> m_body m c body' -> body = body'.
Proof.
  intros H; revert body'; induction H; intros body' H'; inversion H'; subst;
    match goal with
    | A : find ?C RefCT = Some _, B : find ?C RefCT = Some _ |- _ =>
        rewrite A in B; injection B; intros; subst
    end; try congruence; eauto.
Qed.

Local Lemma ls_nth2 {A B} (P : A -> B -> Prop) xs ys i x :
  Forall2 P xs ys -> nth_error xs i = Some x ->
  exists y, nth_error ys i = Some y /\ P x y.
Proof.
  intros H; revert i x; induction H; intros [|i] a E; simpl in E; try discriminate.
  - inversion E; subst; eexists; split; [reflexivity|eassumption].
  - exact (IHForall2 _ _ E).
Qed.

Local Lemma ls_find_in {A} {R : Referable A} k (xs : list A) x :
  find k xs = Some x -> In x xs.
Proof.
  induction xs as [|a xs IH]; simpl; try discriminate.
  destruct (k =? ref a)%nat; [intro E; inversion E; auto|auto].
Qed.

Local Lemma ls_nodup_nth {A} (xs : list A) i j x :
  NoDup xs -> nth_error xs i = Some x -> nth_error xs j = Some x -> i = j.
Proof.
  intros N; revert i j; induction N; intros [|i] [|j] E F; simpl in *;
    try discriminate; auto.
  - inversion E; subst. exfalso; apply H. eapply nth_error_In; eauto.
  - inversion F; subst. exfalso; apply H. eapply nth_error_In; eauto.
Qed.

Local Lemma ls_field_index c fs gs i j fi fj :
  Reffields c fs -> Reffields c gs ->
  nth_error fs i = Some fi -> nth_error gs j = Some fj ->
  ref fi = ref fj -> i = j.
Proof.
  intros F G A B E. pose proof (ls_fields_unique _ _ _ F G); subst gs.
  eapply ls_nodup_nth with (xs := refs fs) (x := ref fi).
  - inversion F; subst; [constructor|assumption].
  - unfold refs; now rewrite nth_error_map, A.
  - unfold refs; rewrite nth_error_map, B. change (Some (ref fj) = Some (ref fi)); congruence.
Qed.

Local Lemma ls_eval_unique n :
  forall e v, ls_eval n e v -> forall k w, ls_eval k e w -> v = w.
Proof.
  induction n as [|n IH]; intros e v E k w F; [inversion E|].
  inversion E; subst; inversion F; subst; auto.
  all: repeat match goal with
       | K : forall e v, ls_eval ?n e v -> _,
         A : ls_eval ?n ?e ?v, B : ls_eval ?k ?e ?w |- _ =>
           tryif constr_eq v w then fail else
           let E := fresh "Heq" in pose proof (K _ _ A _ _ B) as E;
           first [progress subst | solve [discriminate E] |
             progress (injection E; intros; clear E; subst)]
       end; try congruence.
  - destruct o, o0; congruence.
  - f_equal.
    match goal with A : Forall2 (ls_eval _) ?es ?vs,
                    B : Forall2 (ls_eval _) ?es ?ws |- _ =>
      clear E F; revert ws B; induction A; intros ws B; inversion B; subst; f_equal; eauto
    end.
  - assert (i = i0) by (eapply ls_field_index; [exact H1|exact H6|exact H2|exact H7|symmetry; exact H9]). subst. congruence.
  - assert (body = body0) by (eapply ls_body_unique; eauto). subst.
    eapply IH; eauto.
Qed.

Local Lemma ls_delta_un o a (pf : isCompat o a) :
  udelta' o a = Some (udelta o a pf).
Proof. destruct pf; destruct b; reflexivity. Qed.

Local Lemma ls_delta_bin o a b (pf : isCompat2 o a b) :
  bdelta' o a b = Some (bdelta o a b pf).
Proof. destruct pf; reflexivity. Qed.

Local Lemma ls_delta_un' o a r :
  udelta' o a = Some r -> Step (ExpUnOp o a) r.
Proof.
  destruct o, a; simpl; try discriminate.
  destruct b; intro E; inversion E; subst r; [exact (EUnOp2 _ _ (isCpt_Not true) I)|exact (EUnOp2 _ _ (isCpt_Not false) I)].
Qed.

Local Lemma ls_delta_bin' o a b r :
  isValue a -> isValue b -> bdelta' o a b = Some r -> Step (ExpBinOp o a b) r.
Proof.
  intros Va Vb; destruct o.
  - destruct a, b; simpl; try discriminate. intro E; inversion E; subst r.
    apply (EBinOp3 _ _ _ (isCpt_And _ _)); exact I.
  - destruct a, b; simpl; try discriminate. intro E; inversion E; subst r.
    apply (EBinOp3 _ _ _ (isCpt_Or _ _)); exact I.
  - cbn; intro E; inversion E; subst r. apply (EBinOp3 _ _ _ (isCpt_Eq _ _ Va Vb)); assumption.
Qed.

Local Lemma ls_trans e d r : EvalsTo e d -> EvalsTo d r -> EvalsTo e r.
Proof. intros E F; induction E; eauto using EvalsTo. Qed.

Local Lemma ls_context (f : expr -> expr) :
  (forall e d, Step e d -> Step (f e) (f d)) ->
  forall e d, EvalsTo e d -> EvalsTo (f e) (f d).
Proof. intros H e d E; induction E; eauto using EvalsTo. Qed.

Local Lemma ls_step_new c (pre suf : list expr) a b :
  Step a b -> Step (ExpNew c (pre ++ a :: suf)) (ExpNew c (pre ++ b :: suf)).
Proof.
  intro H. eapply RefRC_New_Arg with (i := length pre); eauto.
  - rewrite nth_error_app2 by lia. now rewrite Nat.sub_diag.
  - rewrite nth_error_app2 by lia. now rewrite Nat.sub_diag.
  - intros j J. destruct (Nat.lt_ge_cases j (length pre)).
    + now rewrite !nth_error_app1.
    + rewrite !nth_error_app2 by lia.
      destruct (j - length pre) eqn:E; [lia|reflexivity].
  - now rewrite !length_app.
Qed.

(* The height-indexed relation agrees with the supplied small-step semantics. *)
Local Lemma ls_eval_small n :
  forall e r, ls_eval n e r -> EvalsTo e r.
Proof.
  induction n as [|n IH]; intros e r E; inversion E; subst; try constructor.
  - eapply ls_trans; [eapply ls_context with (f := ExpUnOp o); eauto using Step|].
    eapply AddStep; [eapply ls_delta_un'; eassumption|constructor].
  - eapply ls_trans; [eapply ls_context with (f := fun h => ExpBinOp o h d); eauto using Step|].
    eapply ls_trans; [eapply ls_context with (f := ExpBinOp o a); eauto using Step, ls_eval_value|].
    eapply AddStep; [eapply ls_delta_bin'; eauto using ls_eval_value|constructor].
  - assert (Run : forall (as' bs' : list expr),
        Forall2 (ls_eval n) as' bs' -> forall pre,
        EvalsTo (ExpNew c (pre ++ as')) (ExpNew c (pre ++ bs'))).
    { intros as' bs' F; induction F; intro pre; [constructor|].
      eapply ls_trans; [eapply ls_context with (f := fun h => ExpNew c (pre ++ h :: l));
        eauto using ls_step_new|].
      specialize (IHF (pre ++ y :: nil)).
      now rewrite <- !app_assoc in IHF. }
    exact (Run es vs ltac:(assumption) nil).
  - eapply ls_trans; [eapply ls_context with (f := fun h => ExpFieldAccess h (ref fi)); eauto using Step|].
    eapply AddStep; [eapply Refc_Field; eauto using ls_eval_value|constructor].
  - eapply ls_trans; [eapply ls_context with (f := fun h => ExpMethodInvoc h m d); eauto using Step|].
    eapply ls_trans; [eapply ls_context with (f := ExpMethodInvoc (ExpNew c vs) m); eauto using Step, ls_eval_value|].
    eapply AddStep; eauto using Step, ls_eval_value.
  - eapply ls_trans; [eapply ls_context with (f := fun h => ExpLet h d); eauto using Step|].
    eapply AddStep; eauto using Step, ls_eval_value.
Qed.

Local Lemma ls_eval_list es vs :
  Forall2 ls_runs es vs -> exists n, Forall2 (ls_eval n) es vs.
Proof.
  intro F; induction F.
  - exists 0; constructor.
  - destruct H as [a Ha], IHF as [b Hb].
    exists (max a b); constructor.
    + eapply ls_eval_le; eauto using Nat.le_max_l.
    + eapply ls_forall2_map_rel; [|exact Hb].
      intros; eapply ls_eval_le; eauto using Nat.le_max_r.
Qed.

Local Lemma ls_run_un o e a r :
  ls_runs e a -> udelta' o a = Some r -> ls_runs (ExpUnOp o e) r.
Proof. intros [n H] D; exists (S n); eauto using ls_un. Qed.

Local Lemma ls_run_bin o e d a b r :
  ls_runs e a -> ls_runs d b -> bdelta' o a b = Some r -> ls_runs (ExpBinOp o e d) r.
Proof.
  intros [n H] [k F] D. exists (S (max n k)); eapply ls_bin;
    eauto using ls_eval_le, Nat.le_max_l, Nat.le_max_r.
Qed.

Local Lemma ls_run_new c es vs :
  Forall2 ls_runs es vs -> ls_runs (ExpNew c es) (ExpNew c vs).
Proof. intros F; destruct (ls_eval_list _ _ F) as [n H]; exists (S n); now constructor. Qed.

Local Lemma ls_run_field e f c vs fs i fi r :
  ls_runs e (ExpNew c vs) ->
  Reffields c fs -> nth_error fs i = Some fi -> ref fi = f ->
  nth_error vs i = Some r -> ls_runs (ExpFieldAccess e f) r.
Proof. intros [n H]; exists (S n); eauto using ls_field. Qed.

Local Lemma ls_run_call e m d c vs a body r :
  ls_runs e (ExpNew c vs) -> ls_runs d a -> m_body m c body ->
  ls_runs (subBV_at 1 (ExpNew c vs) (subBV a body)) r ->
  ls_runs (ExpMethodInvoc e m d) r.
Proof.
  intros [n H] [k F] M [l B]. exists (S (max n (max k l))); eapply ls_call; eauto.
  - eapply ls_eval_le; [apply Nat.le_max_l|eassumption].
  - eapply ls_eval_le; [|eassumption]. eapply Nat.le_trans; [apply Nat.le_max_l|apply Nat.le_max_r].
  - eapply ls_eval_le; [|eassumption]. eapply Nat.le_trans; [apply Nat.le_max_r|apply Nat.le_max_r].
Qed.

Local Lemma ls_run_let e d a r :
  ls_runs e a -> ls_runs (subBV a d) r -> ls_runs (ExpLet e d) r.
Proof.
  intros [n H] [k F]. exists (S (max n k)); eapply ls_let;
    eauto using ls_eval_le, Nat.le_max_l, Nat.le_max_r.
Qed.

Local Lemma ls_value_result n e r :
  isValue e -> ls_eval n e r -> r = e.
Proof.
  intros V E. destruct (ls_value_runs _ V) as [j J]. eapply ls_eval_unique; eauto.
Qed.

Local Lemma ls_patch es ds vs i a b :
  nth_error es i = Some a -> nth_error ds i = Some b ->
  (forall j, j <> i -> nth_error es j = nth_error ds j) ->
  length es = length ds ->
  (forall u, ls_runs b u -> ls_runs a u) ->
  Forall2 ls_runs ds vs -> Forall2 ls_runs es vs.
Proof.
  revert es ds vs; induction i; intros [|e es] [|d ds] vs A B Same Len P F;
    simpl in A, B; try discriminate;
    inversion F as [|? ? ? ? R Rs]; subst.
  - inversion A; inversion B; subst a b. constructor; [auto|].
    assert (es = ds) as ->.
    { apply nth_error_ext. intro j. exact (Same (S j) ltac:(lia)). }
    exact Rs.
  - assert (e = d) as -> by (specialize (Same 0 ltac:(lia)); cbn in Same; congruence).
    constructor; [exact R|].
    eapply IHi; eauto.
    + intros j J; exact (Same (S j) ltac:(lia)).
Qed.

Local Lemma ls_step_back e d :
  Step e d -> forall r, ls_runs d r -> ls_runs e r.
Proof.
  intro S; induction S; intros r [n E].
  - inversion E; subst. destruct c, o. eapply ls_run_un; [apply IHS; eexists; eassumption|eassumption].
  - assert (isValue (udelta c w pf)).
    { destruct pf; destruct b; exact I. }
    pose proof (ls_value_result _ _ _ H0 E); subst.
    eapply ls_run_un; eauto using ls_value_runs, ls_delta_un.
  - inversion E; subst. eapply ls_run_bin; [apply IHS| |]; try (eexists; eassumption); eassumption.
  - inversion E; subst. eapply ls_run_bin; [|apply IHS|]; try (eexists; eassumption); eassumption.
  - assert (isValue (bdelta c v1 v2 pf)) by (destruct pf; exact I).
    pose proof (ls_value_result _ _ _ H1 E); subst.
    eapply ls_run_bin; eauto using ls_value_runs, ls_delta_bin.
  - inversion E; subst. eapply ls_run_call; [apply IHS| | |]; try (eexists; eassumption); eassumption.
  - inversion E; subst. eapply ls_run_call; [|apply IHS| |]; try (eexists; eassumption); eassumption.
  - eapply ls_run_call; [apply ls_value_runs|apply ls_value_runs|eassumption|eexists]; eassumption.
  - assert (isValue ei).
    { apply ls_values_new in H2. eapply Forall_forall; eauto using nth_error_In. }
    pose proof (ls_value_result _ _ _ H3 E); subst.
    eapply ls_run_field; [apply ls_value_runs| | |reflexivity|]; eassumption.
  - inversion E; subst. eapply ls_run_field; [apply IHS| | | |];
      try (eexists; eassumption); eassumption.
  - inversion E; subst. apply ls_run_new.
    eapply ls_patch; eauto.
    eapply ls_forall2_map_rel; [|eassumption]. intros; eexists; eassumption.
  - inversion E; subst. eapply ls_run_let; [apply IHS|]; eexists; eassumption.
  - eapply ls_run_let; [apply ls_value_runs|eexists]; eassumption.
Qed.

Local Lemma ls_small_eval e r :
  EvalsTo e r -> isValue r -> ls_runs e r.
Proof. intros H V; induction H; eauto using ls_value_runs, ls_step_back. Qed.

Local Lemma ls_bv_reflect e :
  forall j k w, j <= k ->
  isLC_at k (subBV_at j w e) -> isLC_at (S k) e.
Proof.
  induction e using ls_expr_ind; intros j k w J L; cbn [subBV_at isLC_at] in *;
    try solve [intuition eauto].
  - destruct (j =? i)%nat eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + cbn in L; lia.
  - induction H; cbn in *; intuition eauto.
  - destruct L as [L1 L2]. split; eauto.
    replace (S k + 1) with (S (k + 1)) by lia. eapply IHe2 with (j := j+1); eauto; lia.
Qed.

Local Lemma ls_lc_new k c es :
  isLC_at k (ExpNew c es) <-> Forall (isLC_at k) es.
Proof.
  induction es; cbn [isLC_at].
  - split; intro; constructor.
  - change ((isLC_at k a /\ isLC_at k (ExpNew c es)) <-> Forall (isLC_at k) (a :: es)).
    rewrite IHes. split; [intros []; constructor|intro H; inversion H]; auto.
Qed.

Local Lemma ls_eval_lc n :
  forall e r, ls_eval n e r -> isLC e.
Proof.
  unfold isLC. induction n as [|n IH]; intros e r H; inversion H; subst; cbn [isLC_at]; eauto.
  - change (isLC_at 0 (ExpNew c es)). apply ls_lc_new.
    match goal with F : Forall2 _ _ _ |- _ => clear H; induction F end;
      constructor; eauto.
  - split; eauto. replace (0+1) with (S 0) by lia.
    eapply ls_bv_reflect with (j := 0); [lia|eauto].
Qed.

Local Lemma ls_veq_refl e : isValue e -> veq e e = true.
Proof.
  induction e using ls_expr_ind; intro V; try contradiction.
  - destruct b; reflexivity.
  - cbn; apply Z.eqb_refl.
  - cbn [veq]. rewrite Nat.eqb_refl. simpl.
    apply ls_values_new in V.
    induction H as [|a es Ha Hes IH]; inversion V as [|? ? Va Ves]; subst; cbn; auto.
    now rewrite (Ha Va), (IH Ves).
Qed.

Local Lemma ls_eq_runs e d v :
  ls_runs e v -> ls_runs d v -> EvalsTo (ExpBinOp Eq e d) (Bc true).
Proof.
  intros [n E] F.
  assert (ls_runs (ExpBinOp Eq e d) (Bc true)) as [k K].
  { eapply ls_run_bin with (a := v) (b := v); [now exists n|exact F|].
    cbn; now rewrite ls_veq_refl by (eapply ls_eval_value; eassumption). }
  eapply ls_eval_small; eassumption.
Qed.

(* A congruence whose leaves may replace two closed expressions that
   terminate at the same value. Bound variables can remain in the context. *)
Inductive ls_equiv : expr -> expr -> Prop :=
| ls_eq_leaf : forall e d r, ls_runs e r -> ls_runs d r -> ls_equiv e d
| ls_eq_same : forall e, ls_equiv e e
| ls_eq_un : forall o e d, ls_equiv e d -> ls_equiv (ExpUnOp o e) (ExpUnOp o d)
| ls_eq_bin : forall o e d e' d', ls_equiv e e' -> ls_equiv d d' ->
    ls_equiv (ExpBinOp o e d) (ExpBinOp o e' d')
| ls_eq_field : forall e d f, ls_equiv e d -> ls_equiv (ExpFieldAccess e f) (ExpFieldAccess d f)
| ls_eq_call : forall e d e' d' m, ls_equiv e e' -> ls_equiv d d' ->
    ls_equiv (ExpMethodInvoc e m d) (ExpMethodInvoc e' m d')
| ls_eq_new : forall c es ds, Forall2 ls_equiv es ds ->
    ls_equiv (ExpNew c es) (ExpNew c ds)
| ls_eq_let : forall e d e' d', ls_equiv e e' -> ls_equiv d d' ->
    ls_equiv (ExpLet e d) (ExpLet e' d').
#[local] Hint Constructors ls_equiv : core.

Local Lemma ls_lc_le e :
  forall j k, j <= k -> isLC_at j e -> isLC_at k e.
Proof.
  induction e using ls_expr_ind; intros j k J L; cbn [isLC_at] in *;
    try solve [intuition eauto | lia].
  - induction H; cbn in *; intuition eauto.
  - destruct L; split; eauto. eapply IHe2 with (j := j+1); [lia|eassumption].
Qed.

Local Lemma ls_sub_same e :
  forall j v w, ls_equiv v w ->
  ls_equiv (subBV_at j v e) (subBV_at j w e).
Proof.
  induction e using ls_expr_ind; intros j u w R; cbn [subBV_at];
    try solve [auto].
  - destruct (j =? i)%nat; auto.
  - apply ls_eq_new. induction H; cbn; constructor; auto.
Qed.

Local Lemma ls_equiv_sub e :
  forall d j v w, ls_equiv e d -> ls_equiv v w ->
    ls_equiv (subBV_at j v e) (subBV_at j w d).
Proof.
  induction e using ls_expr_ind; intros d' j u w E V;
    inversion E; subst; try solve [apply ls_sub_same; assumption].
  all: try solve [
    match goal with
    | A : ls_runs ?e ?r, B : ls_runs ?d ?r |- _ =>
       destruct A as [n A]; destruct B as [k B];
       rewrite !ls_bv_unused by (eapply ls_lc_le; [apply Nat.le_0_l|eapply ls_eval_lc; eassumption]);
       eapply ls_eq_leaf; eexists; eassumption
    end].
  all: cbn [subBV_at]; try solve [auto].
  - destruct o, o0; cbn; eauto.
  - apply ls_eq_new. match goal with F : Forall2 _ _ _ |- _ =>
    clear E; revert ds F; induction H; intros ds F; inversion F; subst; cbn; constructor; eauto
  end.
Qed.

Local Lemma ls_equiv_runs n :
  forall e r, ls_eval n e r -> forall d, ls_equiv e d -> ls_runs d r.
Proof.
  induction n as [|n IH]; intros e r E d Q; [inversion E|].
  inversion Q; subst; [|now exists (S n)|..].
  all: try solve [destruct H as [j H]; pose proof (ls_eval_unique _ _ _ E _ _ H); subst; assumption].
  all: inversion E; subst.
  - destruct o, o0; eapply ls_run_un; eauto.
  - eapply ls_run_bin; eauto.
  - eapply ls_run_field; eauto.
  - eapply ls_run_call; eauto .
  - apply ls_run_new.
    match goal with F : Forall2 (ls_eval _) _ ?vs, R : Forall2 ls_equiv _ _ |- _ =>
      clear E Q; revert vs F; induction R; intros vs F; inversion F; subst; constructor; eauto
    end.
  - eapply ls_run_let; eauto. eapply IH; [eassumption|].
    unfold subBV. eapply ls_equiv_sub; eauto.
Qed.

Local Lemma ls_replace_pred ps :
  forall j e d, ls_equiv e d ->
  PEvalsTrue (psubBV_at j e ps) -> PEvalsTrue (psubBV_at j d ps).
Proof.
  induction ps; intros j e d Q P; cbn in *; [constructor|].
  inversion P; subst. constructor; [|eauto].
  match goal with E : EvalsTo _ _ |- _ =>
    destruct (ls_small_eval _ _ E I) as [n N]
  end.
  eapply ls_equiv_runs in N; [|eapply ls_equiv_sub; eauto].
  destruct N as [n' N]; eauto using ls_eval_small.
Qed.

Local Lemma ls_fv_preserve_bv e :
  forall x j w, Elem x (fv e) -> Elem x (fv (subBV_at j w e)).
Proof.
  induction e using ls_expr_ind; intros y j w F; cbn [fv subBV_at] in *;
    try solve [exact F | inversion F | eauto].
  - rewrite ls_union in *; intuition.
  - rewrite ls_union in *; intuition.
  - induction H as [|a es Ha Hes IH]; [inversion F|].
    change (Elem y (union (fv a) (fv (ExpNew c es)))) in F.
    change (Elem y (union (fv (subBV_at j w a)) (fv (subBV_at j w (ExpNew c es))))).
    rewrite ls_union in *; intuition.
  - rewrite ls_union in *; intuition.
Qed.

Local Lemma ls_eval_fv n :
  forall e r, ls_eval n e r -> forall x, ~ Elem x (fv e).
Proof.
  induction n as [|n IH]; intros e r E x F; inversion E; subst; cbn [fv] in F;
    try solve [inversion F].
  all: try (rewrite ls_union in F; destruct F as [F|F]).
  all: try solve [match goal with
       | A : ls_eval _ ?e ?r, K : Elem ?xx (fv ?e) |- _ => exact (IH _ _ A xx K)
       | A : ls_eval _ (subBV ?v ?e) ?r, K : Elem ?xx (fv ?e) |- _ =>
           exact (IH _ _ A xx (ls_fv_preserve_bv _ _ 0 v K))
       end].
  match goal with N : Forall2 _ es vs |- _ => clear E; induction N end.
  - inversion F.
  - change (Elem x (union (fv x0) (fv (ExpNew c l)))) in F.
    rewrite ls_union in F; destruct F as [F|F].
    + exact (IH _ _ H x F).
    + auto.
Qed.

Local Lemma ls_pe_fv ps :
  PEvalsTrue ps -> forall x, ~ Elem x (fvP ps).
Proof.
  intro P; induction P; intros x F; cbn [fvP] in F; [inversion F|].
  apply ls_union in F as [F|F]; [|exact (IHP _ F)].
  destruct (ls_small_eval _ _ H I) as [n E].
  exact (ls_eval_fv _ _ _ E _ F).
Qed.

Local Lemma ls_denotes_preds b ps v :
  Denotes (TRefn b ps) v -> PEvalsTrue (psubBV v ps).
Proof.
  intro D; remember (TRefn b ps) as t in D; revert b ps Heqt.
  induction D; intros b0 ps0 E; inversion E; subst; eauto.
Qed.

Local Lemma ls_denotes_value t v :
  Denotes t v -> isValue v.
Proof. induction 1; auto; exact I. Qed.

Local Lemma ls_denotes_fv t v :
  Denotes t v -> forall x, ~ Elem x (free t).
Proof.
  destruct t as [b ps]; intros D x.
  pose proof (ls_denotes_preds _ _ _ D) as P.
  apply ls_pe_fv with (x := x) in P.
  intro F; apply P; clear P D.
  unfold psubBV in *. induction ps; cbn [free fvP psubBV_at] in *; auto.
  rewrite ls_union in *. intuition eauto using ls_fv_preserve_bv.
Qed.

Local Lemma ls_denotes_change b ps v :
  Denotes (TRefn b ps) v ->
  forall qs, PEvalsTrue (psubBV v qs) -> Denotes (TRefn b qs) v.
Proof.
  intro D; remember (TRefn b ps) as t in D; revert b ps Heqt.
  induction D; intros b0 ps0 E qs P; inversion E; subst;
    eauto using DenotesInt, DenotesBool, DenotesClass, DenotesUpcast.
Qed.

Local Lemma ls_denotes_empty b ps v :
  Denotes (TRefn b ps) v -> Denotes (TRefn b PEmpty) v.
Proof. intro H; eapply ls_denotes_change; [exact H|constructor]. Qed.

Local Lemma ls_csubst_bv g th :
  DenotesEnv g th ->
  forall e j w, csubst th (subBV_at j w e) =
    subBV_at j (csubst th w) (csubst th e).
Proof.
  induction 1; intros e j w; cbn [csubst]; auto.
  rewrite ls_fv_bv by (eapply ls_denotes_value; eassumption). auto.
Qed.

Local Lemma ls_cpsubst_bv g th :
  DenotesEnv g th ->
  forall ps j w, cpsubst th (psubBV_at j w ps) =
    psubBV_at j (csubst th w) (cpsubst th ps).
Proof.
  induction 1; intros ps j w; cbn [csubst cpsubst]; auto.
  rewrite ls_pfv_bv by (eapply ls_denotes_value; eassumption). auto.
Qed.

Local Lemma ls_cpsubst_refn th b ps :
  ctsubst th (TRefn b ps) = TRefn b (cpsubst th ps).
Proof. revert ps; induction th; cbn; auto. Qed.

Local Lemma ls_ctsubst_bv g th t j w :
  DenotesEnv g th -> ctsubst th (tsubBV_at j w t) =
    tsubBV_at j (csubst th w) (ctsubst th t).
Proof.
  destruct t; intro D; cbn [tsubBV_at].
  rewrite !ls_cpsubst_refn, (ls_cpsubst_bv _ _ D). reflexivity.
Qed.

Local Lemma ls_csubst_closed th e :
  (forall x, ~ Elem x (fv e)) -> csubst th e = e.
Proof. induction th; cbn [csubst]; intros F; auto; rewrite ls_fv_unused; auto. Qed.

Local Lemma ls_csubst_value th e : isValue e -> csubst th e = e.
Proof. intro V; apply ls_csubst_closed, (proj2 (ls_value_closed _ V)). Qed.

Local Lemma ls_ctsubst_closed th t :
  (forall x, ~ Elem x (free t)) -> ctsubst th t = t.
Proof.
  induction th; cbn [ctsubst]; intro F; auto.
  destruct t. cbn [tsubFV]. rewrite ls_pfv_unused; auto.
Qed.

Local Lemma ls_fv_fv e :
  forall x y a b, x <> y -> isValue a -> isValue b ->
  subFV x a (subFV y b e) = subFV y b (subFV x a e).
Proof.
  induction e using ls_expr_ind; intros y z u w N V W; cbn [subFV]; try reflexivity;
    try solve [f_equal; eauto].
  - destruct (z =? x)%nat eqn:A, (y =? x)%nat eqn:B; cbn [subFV]; rewrite ?A, ?B.
    + apply Nat.eqb_eq in A, B; congruence.
    + apply ls_fv_unused, (proj2 (ls_value_closed _ W)).
    + symmetry; apply ls_fv_unused, (proj2 (ls_value_closed _ V)).
    + reflexivity.
  - f_equal. induction H; cbn; auto; f_equal; auto.
Qed.

Local Lemma ls_pfv_fv ps x y a b :
  x <> y -> isValue a -> isValue b ->
  psubFV x a (psubFV y b ps) = psubFV y b (psubFV x a ps).
Proof. induction ps; intros; cbn; f_equal; auto using ls_fv_fv. Qed.

Local Lemma ls_ctsubst_fv g th :
  DenotesEnv g th ->
  forall x w t, ~ in_env x g -> isValue w ->
  ctsubst th (tsubFV x w t) = tsubFV x w (ctsubst th t).
Proof.
  induction 1; intros y w u N W; cbn [ctsubst]; auto.
  unfold in_env in N; cbn [binds] in N; rewrite ls_add in N.
  assert (y <> x /\ ~ in_env y g) as [NE No] by tauto.
  rewrite <- IHDenotesEnv by assumption.
  destruct u; cbn [tsubFV]; rewrite ls_pfv_fv; eauto using ls_denotes_value.
Qed.

Local Lemma ls_lookup g th :
  DenotesEnv g th -> forall x t, bound_in x t g ->
  Denotes (ctsubst th t) (csubst th (FV x)).
Proof.
  induction 1; intros y u B; [contradiction|].
  cbn [bound_in] in B. cbn [ctsubst csubst subFV].
  destruct B as [[-> ->]|B].
  - rewrite Nat.eqb_refl, ls_csubst_value by (eapply ls_denotes_value; eassumption).
    rewrite (ls_ctsubst_fv _ _ H) by eauto using ls_denotes_value.
    destruct (ctsubst th t) eqn:T. cbn [tsubFV]. rewrite ls_pfv_unused.
    + exact H1.
    + exact (ls_denotes_fv _ _ H1 x).
  - assert (y <> x) as N.
    { intros ->; apply H0. clear -B. induction g; [contradiction|].
      destruct B as [[-> _]|B]; unfold in_env in *; cbn [binds]; apply ls_add; auto. }
    rewrite (proj2 (Nat.eqb_neq x y) ltac:(congruence)).
    rewrite (ls_ctsubst_fv _ _ H) by eauto using ls_denotes_value.
    specialize (IHDenotesEnv _ _ B).
    destruct (ctsubst th u) eqn:T; cbn [tsubFV].
    rewrite ls_pfv_unused; [exact IHDenotesEnv|exact (ls_denotes_fv _ _ IHDenotesEnv x)].
Qed.

Local Lemma ls_cpsubst_empty th : cpsubst th PEmpty = PEmpty.
Proof. induction th; cbn; auto. Qed.

(* Subtyping transports denotation under each closing environment. *)
Local Lemma ls_sem_sub g s t :
  Subtype g s t ->
  forall th v, DenotesEnv g th -> Denotes (ctsubst th s) v -> Denotes (ctsubst th t) v.
Proof.
  intros S0; destruct S0 as [g b1 b2 p1 p2 nms Sub Imp].
  intros th v D V. rewrite !ls_cpsubst_refn in *.
  set (x := fresh (nms ++ binds g ++ fvP p1 ++ fvP p2)).
  assert (Fresh : ~ Elem x (nms ++ binds g ++ fvP p1 ++ fvP p2)) by apply ls_fresh.
  unfold Elem, set_In in Fresh. rewrite !in_app_iff in Fresh.
  assert (X : ~ in_env x g) by (unfold in_env; tauto).
  assert (A : ~ Elem x (fvP p1)) by tauto.
  assert (B : ~ Elem x (fvP p2)) by tauto.
  pose proof (Imp x ltac:(tauto)) as Im. inversion Im as [g' p' q' H]; subst.
  pose proof (ls_denotes_empty _ _ _ V) as V0.
  assert (D' : DenotesEnv (Cons x (TRefn b1 PEmpty) g) (CCons x v th)).
  { constructor; auto. rewrite ls_cpsubst_refn.
    rewrite ls_cpsubst_empty.
    exact V0. }
  specialize (H _ D'). cbn [cpsubst] in H. unfold unbindP in H.
  rewrite ls_popen_sub, ls_popen_sub in H by assumption.
  rewrite !(ls_cpsubst_bv _ _ D), ls_csubst_value in H by (eapply ls_denotes_value; eassumption).
  eapply DenotesUpcast; [|exact Sub].
  eapply ls_denotes_change; [exact V|].
  apply H. eapply ls_denotes_preds; eassumption.
Qed.

Local Lemma ls_cpsubst_cons th e ps :
  cpsubst th (PCons e ps) = PCons (csubst th e) (cpsubst th ps).
Proof. revert e ps; induction th; cbn; auto. Qed.

Local Lemma ls_csubst_un th o e :
  csubst th (ExpUnOp o e) = ExpUnOp o (csubst th e).
Proof. revert e; induction th; cbn; auto. Qed.

Local Lemma ls_csubst_bin th o e d :
  csubst th (ExpBinOp o e d) = ExpBinOp o (csubst th e) (csubst th d).
Proof. revert e d; induction th; cbn; auto. Qed.

Local Lemma ls_csubst_field th e f :
  csubst th (ExpFieldAccess e f) = ExpFieldAccess (csubst th e) f.
Proof. revert e; induction th; cbn; auto. Qed.

Local Lemma ls_csubst_call th e m d :
  csubst th (ExpMethodInvoc e m d) = ExpMethodInvoc (csubst th e) m (csubst th d).
Proof. revert e d; induction th; cbn; auto. Qed.

Local Lemma ls_csubst_let th e d :
  csubst th (ExpLet e d) = ExpLet (csubst th e) (csubst th d).
Proof. revert e d; induction th; cbn; auto. Qed.

Local Lemma ls_csubst_new th c es :
  csubst th (ExpNew c es) = ExpNew c (map (csubst th) es).
Proof.
  revert es; induction th; intro es; cbn [csubst].
  - now rewrite map_id.
  - change (csubst th (ExpNew c (map (subFV x v_x) es)) =
      ExpNew c (map (fun e => csubst th (subFV x v_x e)) es)).
    rewrite IHth, map_map. reflexivity.
Qed.

Local Lemma ls_csubst_BV th j : csubst th (BV j) = BV j.
Proof. induction th; cbn; auto. Qed.

Local Lemma ls_denotes_self th t e r :
  Denotes (ctsubst th t) r ->
  ls_runs (csubst th e) r ->
  Denotes (ctsubst th (self t e)) r.
Proof.
  destruct t as [b ps]; intros D E.
  rewrite ls_cpsubst_refn in D. cbn [self eqlPred].
  rewrite ls_cpsubst_refn.
  change (Denotes (TRefn b (cpsubst th (PCons (ExpBinOp Eq e (BV 0)) ps))) r).
  rewrite ls_cpsubst_cons, ls_csubst_bin, ls_csubst_BV.
  eapply ls_denotes_change; [exact D|].
  unfold psubBV; cbn [psubBV_at subBV_at].
  rewrite ls_bv_unused by (destruct E as [n H]; eapply ls_eval_lc; eassumption).
  constructor.
  - eapply ls_eq_runs; [exact E|apply ls_value_runs; eauto using ls_denotes_value].
  - eapply ls_denotes_preds; eassumption.
Qed.

Local Lemma ls_denotes_replace j t e d r :
  ls_equiv e d ->
  Denotes (tsubBV_at j e t) r -> Denotes (tsubBV_at j d t) r.
Proof.
  destruct t; intros Q D; cbn [tsubBV_at] in *.
  eapply ls_denotes_change; [exact D|].
  pose proof (ls_denotes_preds _ _ _ D) as P.
  clear D. unfold psubBV in *.
  revert P; generalize (j + 1) as k; clear j.
  induction ps; intros k P; cbn [psubBV_at] in *; [constructor|].
  inversion P; subst. constructor; [|eauto].
  match goal with E : EvalsTo _ _ |- _ => destruct (ls_small_eval _ _ E I) as [n H] end.
  eapply ls_equiv_runs in H.
  - destruct H; eauto using ls_eval_small.
  - eapply ls_equiv_sub; [eapply ls_sub_same; exact Q|constructor].
Qed.

(* Well-formed predicates supply the scope facts needed at binders. *)
Local Lemma ls_fj_bound x b g : bound_inF x b g -> in_envFJ x g.
Proof.
  induction g; intro H; [contradiction|].
  destruct H as [[-> _]|H]; unfold in_envFJ in *; cbn [bindsFJ]; apply ls_add; auto.
Qed.

Local Definition ls_fj_scope g e :=
  isLC e /\ (forall x, Elem x (fv e) -> in_envFJ x g).

Local Lemma ls_fj_scoped g e b : HasFJtype g e b -> ls_fj_scope g e.
Proof.
  revert g e b; fix IH 4; intros g e b T.
  destruct T; unfold ls_fj_scope; unfold isLC; cbn [isLC_at fv];
    try solve [split; [exact I|intros x F; inversion F]].
  - split; [exact I|]. intros y F; apply ls_add in F as [->|F]; [eapply ls_fj_bound; eassumption|inversion F].
  - exact (IH _ _ _ T).
  - destruct (IH _ _ _ T1), (IH _ _ _ T2).
    split; [auto|intros x F; apply ls_union in F; destruct F; auto].
  - destruct (IH _ _ _ T1), (IH _ _ _ T2).
    split; [auto|intros x F; apply ls_union in F; destruct F; auto].
  - destruct (IH _ _ _ T1), (IH _ _ _ T2).
    split; [auto|intros x F; apply ls_union in F; destruct F; auto].
  - exact (IH _ _ _ T0).
  - change (ls_fj_scope g (ExpNew C es)).
    clear H H0 H1.
    revert es Us H2.
    fix Fields 3. intros es Us H2.
    destruct H2 as [|e t es ts Ht Hts].
    + split; [exact I|intros x F; inversion F].
    + destruct (IH _ _ _ Ht) as [L F], (Fields _ _ Hts) as [Ls Fes].
      split.
      * change (isLC e /\ isLC (ExpNew C es)); auto.
      * intros x N. change (Elem x (union (fv e) (fv (ExpNew C es)))) in N.
        apply ls_union in N; destruct N; auto.
  - destruct (IH _ _ _ T) as [L F].
    split.
    + split; [exact L|].
      destruct (IH _ _ _ (H (fresh nms) (ls_fresh nms))) as [Ld _].
      unfold isLC, unbind in Ld. rewrite ls_open_as_bv in Ld.
      eapply ls_bv_reflect with (j := 0); [lia|exact Ld].
    + intros x N. apply ls_union in N as [N|N]; [now apply F|].
      set (y := fresh (x :: nms)).
      assert (Nfy : ~ Elem y (x :: nms)) by apply ls_fresh.
      change (~ (x = y \/ Elem y nms)) in Nfy.
      destruct (IH _ _ _ (H y ltac:(tauto))) as [_ Fd].
      unfold unbind in Fd. rewrite ls_open_as_bv in Fd.
      specialize (Fd x (ls_fv_preserve_bv _ _ _ _ N)).
      unfold in_envFJ in Fd; cbn [bindsFJ] in Fd. apply ls_add in Fd. tauto.
  - exact (IH _ _ _ T).
Qed.

Local Lemma ls_fj_preds_lc g ps :
  PIsBool g ps -> isLCP_at 0 ps.
Proof.
  induction 1; cbn; auto. split; auto. exact (proj1 (ls_fj_scoped _ _ _ H)).
Qed.

Local Lemma ls_open_preds_lc ps x :
  isLCP_at 0 (unbindP x ps) -> isLCP_at 1 ps.
Proof.
  unfold unbindP. induction ps; cbn; auto. intros [L LP].
  split; auto. rewrite ls_open_as_bv in L.
  eapply ls_bv_reflect with (j := 0); eauto.
Qed.

Local Lemma ls_wf_lc g b ps :
  WFtype g (TRefn b ps) -> isLCP_at 1 ps.
Proof.
  intro W; inversion W; subst; [exact I|].
  eapply ls_open_preds_lc.
  apply ls_fj_preds_lc with (g := FCons (fresh nms) b (erase_env g)).
  eauto using ls_fresh.
Qed.

Local Lemma ls_fj_preds_fv g ps :
  PIsBool g ps -> forall x, Elem x (fvP ps) -> in_envFJ x g.
Proof.
  induction 1; intros x F; cbn [fvP] in F; [inversion F|].
  apply ls_union in F as [F|F]; auto.
  exact (proj2 (ls_fj_scoped _ _ _ H) _ F).
Qed.

Local Lemma ls_fv_preserve_openP ps y k x :
  Elem x (fvP ps) -> Elem x (fvP (openP_at k y ps)).
Proof.
  induction ps; cbn [fvP openP_at]; auto.
  setoid_rewrite ls_union. rewrite ls_open_as_bv.
  intuition eauto using ls_fv_preserve_bv.
Qed.

Local Lemma ls_wf_empty_fv b ps :
  WFtype Empty (TRefn b ps) -> forall x, ~ Elem x (fvP ps).
Proof.
  intros W x F; inversion W; subst; [inversion F|].
  set (y := fresh (x :: nms)).
  assert (N : ~ Elem y (x :: nms)) by apply ls_fresh.
  change (~ (x = y \/ Elem y nms)) in N.
  match goal with P : forall y, ~ Elem y nms -> _ |- _ =>
    pose proof (ls_fj_preds_fv _ _ (P y ltac:(tauto)) _
      (ls_fv_preserve_openP _ y 0 _ F)) as In
  end.
  unfold in_envFJ in In; cbn [bindsFJ] in In.
  apply ls_add in In as [E|E]; [tauto|inversion E].
Qed.

Local Lemma ls_two_open e :
  forall i j x y a b, x <> y -> i <> j -> isValue b ->
  ~ Elem x (fv e) -> ~ Elem y (fv e) ->
  subFV x a (subFV y b (open_at i x (open_at j y e))) =
  subBV_at i a (subBV_at j b e).
Proof.
  induction e using ls_expr_ind; intros j k x' y u w N M V X Y;
    cbn [fv subFV open_at subBV_at] in *; try reflexivity;
    try solve [f_equal; eauto].
  - destruct (k =? i)%nat eqn:K; cbn [open_at subFV].
    + rewrite Nat.eqb_refl.
      rewrite ls_fv_unused, ls_bv_unused by
        (first [apply (proj1 (ls_value_closed _ V)) | apply (proj2 (ls_value_closed _ V))]).
      reflexivity.
    + destruct (j =? i)%nat eqn:J; cbn [subFV subBV_at]; rewrite ?J.
      * rewrite (proj2 (Nat.eqb_neq y x') ltac:(congruence)).
        cbn [subFV]; now rewrite Nat.eqb_refl.
      * reflexivity.
  - change (~ Elem x' (fv (FV x))) in X.
    change (~ Elem y (fv (FV x))) in Y.
    change (subFV x' u (subFV y w (FV x)) = FV x).
    rewrite (ls_fv_unused (FV x) y w Y), (ls_fv_unused (FV x) x' u X). reflexivity.
  - rewrite ls_union in X, Y; f_equal; intuition.
  - rewrite ls_union in X, Y; f_equal; intuition.
  - f_equal. induction H; cbn in *; auto.
    rewrite ls_union in X, Y; f_equal; intuition.
  - rewrite ls_union in X, Y. f_equal; [intuition|].
    apply IHe2; try lia; intuition.
Qed.

Local Lemma ls_two_openP ps i j x y a b :
  x <> y -> i <> j -> isValue b ->
  ~ Elem x (fvP ps) -> ~ Elem y (fvP ps) ->
  psubFV x a (psubFV y b (openP_at i x (openP_at j y ps))) =
  psubBV_at i a (psubBV_at j b ps).
Proof.
  induction ps; cbn; intros; auto. rewrite ls_union in *.
  f_equal; intuition eauto using ls_two_open.
Qed.

Local Definition ls_result recv arg t := tsubBV_at 1 recv (tsubBV arg t).

Local Lemma ls_sem_under c t u :
  subtype_under c t u ->
  forall a b, Denotes c a -> Denotes (tsubBV a t) b -> Denotes (tsubBV a u) b.
Proof.
  intros S a b A B.
  destruct t as [bt pt], u as [bu pu].
  set (x := fresh (fvP pt ++ fvP pu)).
  assert (N : ~ Elem x (fvP pt ++ fvP pu)) by apply ls_fresh.
  unfold Elem, set_In in N; rewrite in_app_iff in N.
  assert (D : DenotesEnv (Cons x c Empty) (CCons x a CEmpty)).
  { constructor; auto using DEmp. }
  specialize (ls_sem_sub _ _ _ (S x) _ b D) as H.
  cbn [openT_at ctsubst tsubFV] in H. rewrite !ls_popen_sub in H by tauto.
  exact (H B).
Qed.

Local Lemma ls_sem_under2 c t s u :
  subtype_under2 c t s u ->
  forall a b r, Denotes c a -> Denotes (tsubBV a t) b ->
  Denotes (ls_result a b s) r -> Denotes (ls_result a b u) r.
Proof.
  intros S a b r A B R.
  destruct t as [bt pt], s as [bs ps], u as [bu pu].
  set (xs := fvP pt ++ fvP ps ++ fvP pu).
  set (x := fresh xs).
  set (y := fresh (x :: xs)).
  assert (N : ~ Elem x xs) by apply ls_fresh.
  assert (N' : ~ Elem y (x :: xs)) by apply ls_fresh.
  unfold xs, Elem, set_In in *. cbn [In] in N'. rewrite !in_app_iff in N, N'.
  assert (X : x <> y) by tauto.
  assert (D : DenotesEnv (Cons x c Empty) (CCons x a CEmpty)).
  { constructor; auto using DEmp. }
  assert (D' : DenotesEnv (Cons y (openT_at 0 x (TRefn bt pt)) (Cons x c Empty))
                          (CCons y b (CCons x a CEmpty))).
  { constructor; auto.
    - unfold in_env; cbn [binds]. rewrite ls_add. intros [E|E]; [congruence|inversion E].
    - cbn [ctsubst openT_at tsubFV]. rewrite ls_popen_sub by tauto. exact B. }
  specialize (ls_sem_sub _ _ _ (S x y X) _ r D') as H.
  cbn [openT_at ctsubst tsubFV] in H.
  rewrite !ls_two_openP in H by (try tauto; try discriminate; eauto using ls_denotes_value).
  exact (H R).
Qed.

Inductive ls_ancestor : ClassName -> ClassName -> Prop :=
| ls_anc_refl : forall c, ls_ancestor c c
| ls_anc_parent : forall c d a Is fs nf K ms nm,
    find c RefCT = Some (RefCDecl c d Is fs nf K ms nm) ->
    ls_ancestor d a -> ls_ancestor c a.

Local Lemma ls_anc_trans c d a :
  ls_ancestor c d -> ls_ancestor d a -> ls_ancestor c a.
Proof. intros H; induction H; eauto using ls_anc_parent. Qed.

Local Lemma ls_anc_sub c d :
  ls_ancestor c d -> FJSubtype (TNom (TClass c)) (TNom (TClass d)).
Proof.
  intro H; apply SubBClass. induction H; [constructor|].
  eapply SubCTrans; [eapply SubCInh; eassumption|assumption].
Qed.

Local Lemma ls_class_cases n n' :
  SubClass n n' ->
  match n, n' with
  | TClass c, TClass d => ls_ancestor c d
  | TClass c, TInterface i => exists d, ls_ancestor c d /\ Class_implemented d i
  | TInterface i, TInterface j => i = j
  | TInterface _, TClass _ => False
  end.
Proof.
  induction 1.
  - destruct b; auto using ls_anc_refl.
  - destruct b1, b2, b3; cbn in *; try contradiction; subst;
      eauto using ls_anc_trans.
    destruct IHSubClass2 as [d [D I]]. exists d; eauto using ls_anc_trans.
  - eapply ls_anc_parent; eauto using ls_anc_refl.
  - exists C; split; [constructor|].
    pose proof (cok _ _ _ _ _ _ _ _ H) as OK. inversion OK; subst; eauto.
Qed.

Local Lemma ls_object_info t v :
  Denotes t v ->
  match t with
  | TRefn (TNom n) ps =>
      exists c es fs, v = ExpNew c es /\
        SubClass (TClass c) n /\ Reffields c fs /\
        Forall2 Denotes (map (tsubBV (ExpNew c es)) (map ReffieldType fs)) es
  | _ => True
  end.
Proof.
  induction 1; try exact I.
  - eexists _, _, _; repeat split; eauto using SubCRefl.
  - destruct H0; try exact I. destruct IHDenotes as [c [es [fs [-> [S [F R]]]]]].
    eexists _, _, _; repeat split; eauto using SubCTrans.
Qed.

Local Lemma ls_object_down n ps c es :
  Denotes (TRefn (TNom n) ps) (ExpNew c es) ->
  Denotes (TRefn (TNom (TClass c)) ps) (ExpNew c es).
Proof.
  intro D. destruct (ls_object_info _ _ D) as [d [ds [fs [E [_ [F R]]]]]].
  inversion E; subst. eapply DenotesClass; eauto using ls_denotes_preds, ls_denotes_value.
Qed.

Local Lemma ls_fields_prefix c d :
  ls_ancestor c d -> forall fs gs, Reffields c fs -> Reffields d gs ->
  exists tail, fs = gs ++ tail.
Proof.
  induction 1; intros fs' gs F G.
  - exists nil. rewrite app_nil_r. eauto using ls_fields_unique.
  - inversion F; subst.
    + rewrite obj_notin_dom in H; discriminate.
    + match goal with
      | A : find ?c RefCT = Some _, B : find ?c RefCT = Some _ |- _ =>
          rewrite A in B; injection B; intros; subst
      end.
      destruct (IHls_ancestor _ _ H2 G) as [tail ->].
      exists (tail ++ fs0); symmetry; apply app_assoc.
Qed.

Local Lemma ls_field_free c fs :
  Reffields c fs -> forall f, In f fs -> free (ReffieldType f) = empty.
Proof.
  induction 1; intros f F; [contradiction|].
  apply in_app_iff in F as [F|F]; auto.
  pose proof (cok _ _ _ _ _ _ _ _ H) as OK.
  inversion OK; subst.
  match goal with L : Forall (FType_OK _) _ |- _ =>
    apply Forall_forall with (x := f) in L; [inversion L; auto|exact F]
  end.
Qed.

Local Lemma ls_method_ok c d is fs nf k ms nm m ps t rt body :
  find c RefCT = Some (RefCDecl c d is fs nf k ms nm) ->
  find m ms = Some (MDefn (MDecl rt m ps t) body) ->
  MType_OK c (MDefn (MDecl rt m ps t) body).
Proof.
  intros C M. pose proof (cok _ _ _ _ _ _ _ _ C) as OK.
  inversion OK; subst.
  match goal with F : Forall (MType_OK _) _ |- _ =>
    eapply Forall_forall; [exact F|eapply ls_find_in; exact M]
  end.
Qed.

Local Lemma ls_find_key {A} {R : Referable A} k (xs : list A) a :
  find k xs = Some a -> ref a = k.
Proof.
  induction xs as [|b xs IH]; cbn [find]; try discriminate.
  destruct (k =? ref b)%nat eqn:E; auto.
  intro H; inversion H; subst. apply Nat.eqb_eq in E; congruence.
Qed.

Inductive ls_sig : MethodName -> nomtype -> preds -> type -> type -> Prop :=
| ls_sig_c : forall m c ps t rt, mtype(m,c) = ps ~> t ~> rt ->
    ls_sig m (TClass c) ps t rt
| ls_sig_i : forall m i ps t rt, mtypei(m,i) = ps ~> t ~> rt ->
    ls_sig m (TInterface i) ps t rt.

Local Lemma ls_signature_closed m b ps t rt :
  ls_sig m b ps t rt ->
  (forall x, ~ Elem x (fvP ps)) /\ free t = empty /\ free rt = empty.
Proof.
  intro S; destruct S as [m c ps t rt S|m i ps t rt S].
  - induction S.
    + pose proof (ls_method_ok _ _ _ _ _ _ _ _ _ _ _ _ _ H H0) as OK.
      inversion OK; subst. repeat split; eauto using ls_wf_empty_fv.
    + exact IHS.
  - inversion S; subst.
    pose proof (iok _ _ _ H) as OK. inversion OK; subst.
    match goal with F : Forall (MType_OK_I _) _ |- _ =>
      pose proof (proj1 (Forall_forall _ _) F _ (ls_find_in _ _ _ H0)) as M;
      inversion M; subst; repeat split; eauto using ls_wf_empty_fv
    end.
Qed.

Local Lemma ls_ctsubst_empty_free th t :
  free t = empty -> ctsubst th t = t.
Proof. intro E; apply ls_ctsubst_closed; intro x; rewrite E; intro F; inversion F. Qed.

Local Definition ls_sound_at n :=
  forall g e t th r, Hastype g e t -> DenotesEnv g th ->
  ls_eval n (csubst th e) r -> Denotes (ctsubst th t) r.

Local Lemma ls_body_checked n m c ps t rt :
  ls_sound_at n ->
  mtype(m,c) = ps ~> t ~> rt ->
  exists body, m_body m c body /\
  forall recv a r,
    Denotes (TRefn (TNom (TClass c)) ps) recv ->
    Denotes (tsubBV recv t) a ->
    ls_eval n (subBV_at 1 recv (subBV a body)) r ->
    Denotes (ls_result recv a rt) r.
Proof.
  intros IH M; induction M.
  - exists e; split; [eapply mbdy_ok; eassumption|].
    pose proof (ls_method_ok _ _ _ _ _ _ _ _ _ _ _ _ _ H H0) as OK.
    inversion OK; subst.
    intros recv a r Rec Arg Run.
    assert (ArgV : isValue a) by (eapply ls_denotes_value; exact Arg).
    assert (Env : DenotesEnv (Cons 0 (TRefn (TNom (TClass C)) ps) Empty)
                           (CCons 0 recv CEmpty)) by (constructor; auto using DEmp).
    assert (D' : DenotesEnv
      (Cons 1 (openT_at 0 0 t) (Cons 0 (TRefn (TNom (TClass C)) ps) Empty))
      (CCons 1 a (CCons 0 recv CEmpty))).
    { constructor; auto.
      - unfold in_env; cbn [binds]; rewrite ls_add; intros [E|E]; [discriminate|inversion E].
      - destruct t; cbn [ctsubst openT_at tsubFV].
        rewrite ls_popen_sub; [exact Arg|].
        match goal with F : free (TRefn _ _) = empty |- _ =>
          cbn [free] in F; rewrite F; intro E; inversion E
        end. }
    match goal with T : forall y y', y <> y' -> Hastype _ _ _ |- _ =>
      pose proof (IH _ _ _ _ r (T 0 1 ltac:(discriminate)) D') as Sound
    end.
    cbn [csubst] in Sound.
    rewrite ls_two_open in Sound by (try discriminate; try assumption;
      match goal with F : fv e = empty |- _ => rewrite F; intro E; inversion E end).
    specialize (Sound Run). destruct rt; cbn [openT_at ctsubst tsubFV] in Sound.
    rewrite ls_two_openP in Sound by (try discriminate; try assumption;
      match goal with F : free (TRefn _ _) = empty |- _ =>
        cbn [free] in F; rewrite F; intro E; inversion E
      end).
    exact Sound.
  - destruct IHM as [body [B Safe]]. exists body; split.
    + eapply mbdy_no_override; eassumption.
    + intros recv a r Rec Arg Run. apply (Safe recv a r); auto.
      eapply DenotesUpcast; [exact Rec|]. apply SubBClass. eapply SubCInh; eassumption.
Qed.

(* Follow the class table from the static signature to the runtime signature. *)
Local Lemma ls_transport_class c d :
  ls_ancestor c d ->
  forall m ps t rt recv a,
  mtype(m,d) = ps ~> t ~> rt ->
  Denotes (TRefn (TNom (TClass c)) ps) recv ->
  Denotes (tsubBV recv t) a ->
  exists qs u ru, mtype(m,c) = qs ~> u ~> ru /\
    Denotes (TRefn (TNom (TClass c)) qs) recv /\
    Denotes (tsubBV recv u) a /\
    (forall r, Denotes (ls_result recv a ru) r -> Denotes (ls_result recv a rt) r).
Proof.
  intro P; induction P; intros m ps t rt recv arg M R A.
  - exists ps, t, rt; auto.
  - assert (Super : Denotes (TRefn (TNom (TClass d)) ps) recv).
    { eapply DenotesUpcast; [exact R|]. apply SubBClass. eapply SubCInh; eassumption. }
    destruct (IHP _ _ _ _ _ _ M Super A) as [qs [u [ru [Mt [Rec [Arg Ret]]]]]].
    assert (Child : Denotes (TRefn (TNom (TClass c)) qs) recv).
    { eapply ls_denotes_change; [exact R|eapply ls_denotes_preds; exact Rec]. }
    destruct (find m ms) as [[[rt' m' ps' t'] body]|] eqn:F.
    + pose proof (ls_find_key _ _ _ F) as K'. change (m' = m) in K'; subst m'.
      pose proof (ls_method_ok _ _ _ _ _ _ _ _ _ _ _ _ _ H F) as OK.
      inversion OK; subst.
      rewrite H in H5; injection H5; intros; subst.
      destruct (H7 _ _ _ Mt) as [SP [SA SR]].
      exists ps', t', rt'. split; [eapply mty_ok; eassumption|].
      split.
      * exact (ls_sem_sub _ _ _ SP CEmpty recv DEmp Child).
      * split.
        -- eapply ls_sem_under; eassumption.
        -- intros r R'. apply Ret. eapply ls_sem_under2; eassumption.
    + exists qs, u, ru; repeat split; auto. eapply mty_no_override; eassumption.
Qed.

Local Lemma ls_interface_implementation c i m ps t rt :
  Class_implemented c i -> mtypei(m,i) = ps ~> t ~> rt ->
  implement c m rt ps t.
Proof.
  intros C M; inversion C; subst; inversion M; subst.
  match goal with A : find ?i RefIT = Some _, B : find ?i RefIT = Some _ |- _ =>
    rewrite A in B; injection B; intros; subst
  end. eauto.
Qed.

Local Lemma ls_transport_signature n m ps t rt c es a :
  ls_sig m n ps t rt ->
  Denotes (TRefn (TNom n) ps) (ExpNew c es) ->
  Denotes (tsubBV (ExpNew c es) t) a ->
  exists qs u ru, mtype(m,c) = qs ~> u ~> ru /\
    Denotes (TRefn (TNom (TClass c)) qs) (ExpNew c es) /\
    Denotes (tsubBV (ExpNew c es) u) a /\
    (forall r, Denotes (ls_result (ExpNew c es) a ru) r ->
               Denotes (ls_result (ExpNew c es) a rt) r).
Proof.
  intros M R A.
  pose proof (ls_object_down _ _ _ _ R) as D.
  destruct (ls_object_info _ _ R) as [d [ds [fs [E [P _]]]]].
  inversion E; subst. apply ls_class_cases in P.
  destruct M as [m s ps t rt M|m i ps t rt M].
  - eapply ls_transport_class; eassumption.
  - destruct P as [s [P Impl]].
    destruct (ls_interface_implementation _ _ _ _ _ _ Impl M)
      as [u [ru [qs [Mt [SP [SA SR]]]]]].
    assert (R' : Denotes (TRefn (TNom (TClass s)) ps) (ExpNew d ds)).
    { eapply DenotesUpcast; [exact D|now apply ls_anc_sub]. }
    pose proof (ls_sem_sub _ _ _ SP CEmpty _ DEmp R') as Rec.
    pose proof (ls_sem_under _ _ _ SA _ _ R' A) as Arg.
    assert (D' : Denotes (TRefn (TNom (TClass d)) qs) (ExpNew d ds)).
    { eapply ls_denotes_change; [exact D|eapply ls_denotes_preds; exact Rec]. }
    destruct (ls_transport_class _ _ P _ _ _ _ _ _ Mt D' Arg)
      as [p' [t' [rt' [Mt' [Rec' [Arg' Ret]]]]]].
    exists p', t', rt'; repeat split; auto.
    intros r Res. eapply ls_sem_under2; [exact SR|exact R'|exact A|auto].
Qed.

Local Lemma ls_run_equiv n e v :
  ls_eval n e v -> ls_equiv e v /\ ls_equiv v e.
Proof.
  intro E. pose proof (ls_value_runs _ (ls_eval_value _ _ _ E)) as V.
  split; eapply ls_eq_leaf; try exact V; eexists; exact E.
Qed.

Local Lemma ls_call_checked n g th m b ps t rt e d c vs a body r :
  ls_sound_at n -> DenotesEnv g th ->
  ls_sig m b ps t rt ->
  ls_eval n (csubst th e) (ExpNew c vs) -> ls_eval n (csubst th d) a ->
  m_body m c body -> ls_eval n (subBV_at 1 (ExpNew c vs) (subBV a body)) r ->
  Denotes (ctsubst th (TRefn (TNom b) ps)) (ExpNew c vs) ->
  Denotes (ctsubst th (tsubBV e t)) a ->
  Denotes (ctsubst th (ls_result e d rt)) r.
Proof.
  intros IH Env Sig E A Body Run Rec Arg.
  destruct (ls_signature_closed _ _ _ _ _ Sig) as [P [T R]].
  rewrite ls_ctsubst_closed in Rec by exact P.
  unfold tsubBV in Arg. rewrite (ls_ctsubst_bv _ _ _ _ _ Env), (ls_ctsubst_empty_free th _ T) in Arg.
  destruct (ls_run_equiv _ _ _ E) as [EF EB], (ls_run_equiv _ _ _ A) as [AF AB].
  apply (ls_denotes_replace _ _ _ _ _ EF) in Arg.
  destruct (ls_transport_signature _ _ _ _ _ _ _ _ Sig Rec Arg)
    as [qs [u [ru [M [Rec' [Arg' Ret]]]]]].
  destruct (ls_body_checked _ _ _ _ _ _ IH M) as [body' [B Safe]].
  pose proof (ls_body_unique _ _ _ _ Body B); subst body'.
  specialize (Ret _ (Safe _ _ _ Rec' Arg' Run)).
  unfold ls_result, tsubBV in *.
  rewrite !(ls_ctsubst_bv _ _ _ _ _ Env), (ls_ctsubst_empty_free th _ R).
  apply (ls_denotes_replace _ _ _ _ _ EB).
  (* Preserve the argument occurrence under the outer receiver substitution. *)
  destruct rt as [br pr]; cbn [tsubBV_at] in *.
  eapply ls_denotes_change; [exact Ret|].
  pose proof (ls_denotes_preds _ _ _ Ret) as P0. clear Ret.
  unfold psubBV in *. clear -P0 AB.
  induction pr as [|p pr IHp]; cbn [psubBV_at] in *; [constructor|].
  inversion P0; subst. constructor; [|eauto].
  match goal with E : EvalsTo _ (Bc true) |- _ => destruct (ls_small_eval _ _ E I) as [k F] end.
  eapply ls_equiv_runs in F.
  - destruct F; eauto using ls_eval_small.
  - eapply ls_equiv_sub; [|constructor].
    eapply ls_equiv_sub; [eapply ls_sub_same; exact AB|constructor].
Qed.

Local Lemma ls_field_checked g th e c vs C fs gs i j fi fj r ps :
  DenotesEnv g th -> ls_eval i (csubst th e) (ExpNew c vs) ->
  Denotes (ctsubst th (TRefn (TNom (TClass C)) ps)) (ExpNew c vs) ->
  Reffields C fs -> Reffields c gs ->
  forall k, nth_error fs k = Some fi -> nth_error gs j = Some fj ->
  ref fi = ref fj -> nth_error vs j = Some r ->
  Denotes (ctsubst th (tsubBV e (ReffieldType fi))) r.
Proof.
  intros Env E Rec Fs Gs k Fi Fj Key V.
  rewrite ls_cpsubst_refn in Rec.
  destruct (ls_object_info _ _ Rec) as [c' [vs' [fs' [Ident [A [F Ds]]]]]].
  inversion Ident; subst. apply ls_class_cases in A.
  pose proof (ls_fields_unique _ _ _ Gs F) as G; subst fs'.
  destruct (ls_fields_prefix _ _ A _ _ Gs Fs) as [tail Len].
  assert (Nth : nth_error gs k = Some fi).
  { rewrite Len, nth_error_app1; auto. apply nth_error_Some; congruence. }
  assert (k = j) as -> by (eapply ls_field_index; eassumption).
  assert (NthT : nth_error (map (tsubBV (ExpNew c' vs'))
                         (map ReffieldType gs)) j =
                 Some (tsubBV (ExpNew c' vs') (ReffieldType fi))).
  { now rewrite !nth_error_map, Nth. }
  destruct (ls_nth2 _ _ _ _ _ Ds NthT) as [r' [R D]]. rewrite V in R; inversion R; subst.
  unfold tsubBV in *. rewrite (ls_ctsubst_bv _ _ _ _ _ Env), ls_ctsubst_empty_free.
  - apply (ls_denotes_replace _ _ _ _ _ (proj2 (ls_run_equiv _ _ _ E))); exact D.
  - eapply ls_field_free; eauto using nth_error_In.
Qed.

Local Lemma ls_new_fields n g th src obj es ts fs vs :
  ls_sound_at n -> DenotesEnv g th ->
  ls_equiv (csubst th src) obj ->
  Forall2 (Hastype g) es ts ->
  Forall2 (Subtype g) ts (map (tsubBV src) (map ReffieldType fs)) ->
  Forall (fun f => free (ReffieldType f) = empty) fs ->
  Forall2 (ls_eval n) (map (csubst th) es) vs ->
  Forall2 Denotes (map (tsubBV obj) (map ReffieldType fs)) vs.
Proof.
  intros IH Env Rel Ty.
  revert fs vs; induction Ty as [|e t es ts Te Tes IT]; intros [|f fs] vs S F E;
    inversion S; inversion E; subst; cbn [map]; try constructor.
  - inversion F; subst.
    unfold tsubBV. apply (ls_denotes_replace _ _ _ _ _ Rel).
    match goal with
      | Sub : Subtype g t (tsubBV src (ReffieldType f)),
        Run : ls_eval n (csubst th e) ?r |- _ =>
        pose proof (ls_sem_sub _ _ _ Sub th r Env (IH _ _ _ _ _ Te Env Run)) as D
    end.
    unfold tsubBV in D. rewrite (ls_ctsubst_bv _ _ _ _ _ Env), ls_ctsubst_empty_free in D by assumption.
    exact D.
  - inversion F; subst. eapply IT; eassumption.
Qed.

Local Lemma ls_let_checked n g th d b t nms a r :
  ls_sound_at n -> DenotesEnv g th ->
  WFtype g t -> Denotes (ctsubst th b) a ->
  (forall y, ~ Elem y nms -> Hastype (Cons y b g) (unbind y d) (unbindT y t)) ->
  ls_eval n (subBV a (csubst th d)) r ->
  Denotes (ctsubst th t) r.
Proof.
  intros IH Env W A T E. destruct t as [bt pt].
  set (x := fresh (nms ++ binds g ++ fv d ++ fvP pt)).
  assert (N : ~ Elem x (nms ++ binds g ++ fv d ++ fvP pt)) by apply ls_fresh.
  unfold Elem, set_In in N. rewrite !in_app_iff in N.
  assert (Env' : DenotesEnv (Cons x b g) (CCons x a th)).
  { constructor; auto. }
  pose proof (IH _ _ _ _ r (T x ltac:(tauto)) Env') as D.
  cbn [csubst] in D. unfold unbind in D.
  rewrite ls_open_sub, (ls_csubst_bv _ _ Env), ls_csubst_value in D by
    (try tauto; eapply ls_denotes_value; exact A).
  specialize (D E). unfold unbindT in D. cbn [ctsubst openT_at tsubFV] in D.
  rewrite ls_popen_sub, ls_pbv_unused in D by (try tauto; eapply ls_wf_lc; exact W).
  exact D.
Qed.

Local Lemma ls_un_type n th o e r :
  ls_eval n (csubst th (ExpUnOp o e)) r ->
  Denotes (ctsubst th (tsubBV e (ty' o))) r.
Proof.
  intro E. destruct o. rewrite ls_csubst_un in E.
  assert (exists b, r = Bc b) as [b ->].
  { inversion E; subst. destruct o, a; cbn in *; try discriminate.
    destruct b; [exists false|exists true]; congruence. }
  change (Denotes (ctsubst th (self (TRefn TBool PEmpty) (ExpUnOp Not e))) (Bc b)).
  apply ls_denotes_self.
  - rewrite ls_cpsubst_refn, ls_cpsubst_empty. constructor; constructor.
  - exists n. now rewrite ls_csubst_un.
Qed.

Local Lemma ls_bin_type n th o e d r :
  isLC d -> ls_eval n (csubst th (ExpBinOp o e d)) r ->
  Denotes (ctsubst th (tsubBV_at 1 e (tsubBV d (ty'2 o)))) r.
Proof.
  intros L E. rewrite ls_csubst_bin in E.
  assert (exists b, r = Bc b) as [b ->].
  { inversion E; subst. destruct o, a, b; cbn in *; try discriminate;
    match goal with H : Some (Bc ?bol) = Some r |- _ => exists bol; congruence end. }
  assert (R : Denotes (ctsubst th (self (TRefn TBool PEmpty) (ExpBinOp o e d))) (Bc b)).
  { apply ls_denotes_self.
    - rewrite ls_cpsubst_refn, ls_cpsubst_empty. constructor; constructor.
    - exists n. now rewrite ls_csubst_bin. }
  destruct o; cbn [ty'2 refn_pred2 tsubBV tsubBV_at psubBV_at subBV_at Nat.add Nat.eqb];
    rewrite ls_bv_unused by (eapply ls_lc_le; [|exact L]; lia); exact R.
Qed.

(* Evaluation height decreases at calls and in constructor fields. Within
   a fixed height, subsumption decreases the typing derivation. *)
Local Lemma ls_fundamental n : ls_sound_at n.
Proof.
  induction n as [|n IH].
  - intros g e t th r T Env Run; inversion Run.
  - intros g e t th r T. revert th r.
    induction T; intros th r Env Run.
    + rewrite ls_csubst_value in Run by exact I. inversion Run; subst.
      rewrite ls_ctsubst_empty_free by reflexivity.
      constructor; constructor; [eapply ls_eq_runs; apply ls_value_runs; exact I|constructor].
    + rewrite ls_csubst_value in Run by exact I. inversion Run; subst.
      rewrite ls_ctsubst_empty_free by reflexivity.
      constructor; constructor; [eapply ls_eq_runs; apply ls_value_runs; exact I|constructor].
    + eapply ls_un_type; exact Run.
    + eapply ls_bin_type; eassumption.
    + pose proof (ls_lookup _ _ Env _ _ H) as D.
      pose proof (ls_value_result _ _ _ (ls_denotes_value _ _ D) Run); subst.
      apply ls_denotes_self; [exact D|exists (S n); exact Run].
    + apply ls_denotes_self; [|exists (S n); exact Run].
      rewrite ls_csubst_call in Run. inversion Run; subst.
      eapply ls_call_checked with (g := g) (n := n); try eassumption.
      * exact (ls_sig_c _ _ _ _ _ H).
      * eapply ls_sem_sub; [eassumption|exact Env|eapply IH; eassumption].
      * eapply ls_sem_sub; [eassumption|exact Env|eapply IH; eassumption].
    + apply ls_denotes_self; [|exists (S n); exact Run].
      rewrite ls_csubst_call in Run. inversion Run; subst.
      eapply ls_call_checked with (g := g) (n := n); try eassumption.
      * exact (ls_sig_i _ _ _ _ _ H).
      * eapply ls_sem_sub; [eassumption|exact Env|eapply IH; eassumption].
      * eapply ls_sem_sub; [eassumption|exact Env|eapply IH; eassumption].
    + apply ls_denotes_self; [|exists (S n); exact Run].
      rewrite ls_csubst_field in Run; inversion Run; subst.
      eapply ls_field_checked with (g := g) (i := n) (C := C) (fs := Fs) (k := i) (ps := ps);
        try eassumption; [exact (IH _ _ _ _ _ T Env H6)|symmetry; exact H9].
    + apply ls_denotes_self; [|exists (S n); exact Run].
      pose proof Run as E. rewrite ls_csubst_new in E. inversion E; subst.
      rewrite ls_cpsubst_refn, ls_cpsubst_empty.
      eapply DenotesClass with (Fs := Fs).
      * eapply ls_eval_value; exact E.
      * constructor.
      * assumption.
      * eapply ls_new_fields; try eassumption.
        -- exact (proj1 (ls_run_equiv _ _ _ Run)).
        -- apply Forall_forall; intros; eapply ls_field_free; eassumption.
    + apply ls_denotes_self; [|exists (S n); exact Run].
      rewrite ls_csubst_let in Run; inversion Run; subst.
      eapply ls_let_checked with (n := n) (g := g) (b := b);
        try eassumption; eapply IH; eassumption.
    + eapply ls_sem_sub; [eassumption|exact Env|].
      apply IHT; assumption.
Qed.

Theorem logical_soundness: forall (e e':expr) (t:type) g b ps,
  Hastype g e (TRefn b ps) -> WFEnv g -> Terminating g e -> LEntails g (psubBV e ps).
Proof.
  intros e e' t g b ps T W Term th Env.
  destruct (Term th Env) as [v [Eval Value]].
  destruct (ls_small_eval _ _ Eval Value) as [n Run].
  pose proof (ls_fundamental n _ _ _ _ _ T Env Run) as D.
  rewrite ls_cpsubst_refn in D.
  unfold psubBV in *. rewrite (ls_cpsubst_bv _ _ Env).
  eapply ls_replace_pred.
  - exact (proj2 (ls_run_equiv _ _ _ Run)).
  - eapply ls_denotes_preds; exact D.
Qed.
