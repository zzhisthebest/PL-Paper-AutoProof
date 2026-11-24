Require Import Metalib.Metatheory.
Require Import syntax_ott.
From Stdlib Require Import Lia Arith.Wf_nat.

Fixpoint scoped (k : nat) (e : exp) : Prop :=
  match e with
  | e_var_b n => n < k
  | e_abs _ body _ | e_fixpoint body _ => scoped (S k) body
  | e_app e1 e2 | e_merge e1 e2 => scoped k e1 /\ scoped k e2
  | e_anno body _ => scoped k body
  | _ => True
  end.

Lemma scoped_mono : forall e k l,
    scoped k e -> k <= l -> scoped l e.
Proof.
  induction e; simpl in *; intuition (eauto with arith).
Qed.

Lemma open_scoped_identity : forall e k u,
    scoped k e -> open_exp_wrt_exp_rec k u e = e.
Proof.
  induction e; intros k u H; simpl in *; try reflexivity;
    try solve [f_equal; intuition eauto].
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; try reflexivity; lia.
Qed.

Lemma scoped_open : forall e k u,
    scoped (S k) e -> scoped 0 u ->
    scoped k (open_exp_wrt_exp_rec k u e).
Proof.
  induction e; intros k u H Hu; simpl in *; try solve [intuition eauto].
  destruct (lt_eq_lt_dec n k) as [[Hlt|Heq]|Hgt]; simpl.
  - exact Hlt.
  - eapply scoped_mono; [exact Hu | lia].
  - lia.
Qed.

Lemma scoped_open_inv : forall e k x,
    scoped k (open_exp_wrt_exp_rec k (e_var_f x) e) -> scoped (S k) e.
Proof.
  induction e; intros k y H; simpl in *; try solve [intuition eauto].
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl in *; lia.
Qed.

Fixpoint exp_size (e : exp) : nat :=
  match e with
  | e_abs _ body _ | e_fixpoint body _ | e_anno body _ => S (exp_size body)
  | e_app e1 e2 | e_merge e1 e2 => S (exp_size e1 + exp_size e2)
  | _ => 1
  end.

Lemma exp_size_open_var : forall e k x,
    exp_size (open_exp_wrt_exp_rec k (e_var_f x) e) = exp_size e.
Proof.
  induction e; intros; simpl; try now rewrite ?IHe, ?IHe1, ?IHe2.
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Lemma scoped_lc : forall e, scoped 0 e -> lc_exp e.
Proof.
  apply (well_founded_induction (well_founded_ltof exp exp_size)
           (fun e => scoped 0 e -> lc_exp e)).
  intros e IH H. destruct e; simpl in H; try solve [constructor | lia].
  all: constructor; intros; apply IH.
  all: try solve [unfold ltof; simpl; lia | tauto].
  all: try solve [unfold ltof, open_exp_wrt_exp;
                  rewrite exp_size_open_var; simpl; lia].
  all: apply scoped_open; [exact H | exact I].
Qed.

Lemma typing_scoped : forall G e A, Etyping G e A -> scoped 0 e.
Proof.
  intros G e A H. induction H; simpl; intuition.
  all: destruct (atom_fresh L) as [x Hx];
    eapply scoped_open_inv; eauto.
Qed.

Lemma typing_lc : forall G e A, Etyping G e A -> lc_exp e.
Proof.
  eauto using typing_scoped, scoped_lc.
Qed.

Lemma fv_open_includes : forall e k u x,
    x \in fv_exp e -> x \in fv_exp (open_exp_wrt_exp_rec k u e).
Proof.
  induction e; intros k u y H; simpl in *; try solve [fsetdec | eauto].
  all: assert (Hx : y \in fv_exp e1 \/ y \in fv_exp e2) by fsetdec;
    destruct Hx; [apply IHe1 with (k := k) (u := u) in H0 |
                  apply IHe2 with (k := k) (u := u) in H0]; fsetdec.
Qed.

Lemma typing_fv : forall G e A,
    Etyping G e A -> forall x, x \in fv_exp e -> x \in dom G.
Proof.
  intros G e A H. induction H; intros y Hy; simpl in Hy.
  - fsetdec.
  - fsetdec.
  - assert (y = x) by fsetdec. subst. eauto using binds_In.
  - destruct (atom_fresh (L \u {{y}})) as [x Hx].
    assert (HxL : x \notin L) by fsetdec.
    specialize (H0 x HxL y (fv_open_includes e 0 (e_var_f x) y Hy)).
    simpl in H0. fsetdec.
  - assert (y \in fv_exp e1 \/ y \in fv_exp e2) as [Hy'|Hy'] by fsetdec;
      eauto.
  - assert (y \in fv_exp e1 \/ y \in fv_exp e2) as [Hy'|Hy'] by fsetdec;
      eauto.
  - eauto.
  - destruct (atom_fresh (L \u {{y}})) as [x Hx].
    assert (HxL : x \notin L) by fsetdec.
    specialize (H0 x HxL y (fv_open_includes e 0 (e_var_f x) y Hy)).
    simpl in H0. fsetdec.
  - assert (y \in fv_exp v1 \/ y \in fv_exp v2) as [Hy'|Hy'] by fsetdec;
      [specialize (IHEtyping1 y Hy') | specialize (IHEtyping2 y Hy')];
      simpl in *; fsetdec.
Qed.

Lemma subst_fresh_exp : forall e u x, x \notin fv_exp e -> subst_exp u x e = e.
Proof.
  induction e; intros u y H; simpl in *; try reflexivity;
    try solve [f_equal; eauto using notin_union_1, notin_union_2].
  destruct (eq_var x y); [subst; fsetdec | reflexivity].
Qed.

Lemma subst_open_exp : forall e u x v k,
    scoped 0 u ->
    subst_exp u x (open_exp_wrt_exp_rec k v e) =
    open_exp_wrt_exp_rec k (subst_exp u x v) (subst_exp u x e).
Proof.
  induction e; intros u y v k H; simpl; try solve [f_equal; eauto].
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
  - destruct (eq_var x y); simpl; [symmetry | reflexivity].
    apply open_scoped_identity. eauto using scoped_mono with arith.
Qed.

Lemma subst_intro_exp : forall e u x k,
    x \notin fv_exp e ->
    subst_exp u x (open_exp_wrt_exp_rec k (e_var_f x) e) =
    open_exp_wrt_exp_rec k u e.
Proof.
  induction e; intros u y k H; simpl in *; try reflexivity;
    try solve [f_equal; eauto using notin_union_1, notin_union_2].
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; try reflexivity.
    destruct (eq_var y y); congruence.
  - destruct (eq_var x y); [subst; fsetdec | reflexivity].
Qed.

Lemma typing_weaken : forall G e A, Etyping G e A ->
    forall G', uniq G' ->
      (forall x B, binds x B G -> binds x B G') ->
      Etyping G' e A.
Proof.
  intros G e A H. induction H; intros G' Hu Hb;
    eauto using Etyp_top, Etyp_lit, Etyp_var, Etyp_app, Etyp_merge,
      Etyp_anno, Etyp_mergev.
  - eapply Etyp_abs with (L := L \u dom G'); [|eassumption|eassumption].
    intros x Hx. apply H0; [fsetdec | apply uniq_cons; [exact Hu|fsetdec] |].
    intros y T HT. apply binds_cons_1 in HT as [[-> ->]|HT];
      [apply binds_cons_2; reflexivity | apply binds_cons; auto].
  - eapply Etyp_fix with (L := L \u dom G').
    intros x Hx. apply H0; [fsetdec | apply uniq_cons; [exact Hu|fsetdec] |].
    intros y T HT. apply binds_cons_1 in HT as [[-> ->]|HT];
      [apply binds_cons_2; reflexivity | apply binds_cons; auto].
Qed.

Lemma typing_subst_closed : forall x A u,
    Etyping nil u A ->
    forall G e B, Etyping G e B ->
      forall F, G = F ++ [(x,A)] -> Etyping F (subst_exp u x e) B.
Proof.
  intros x A u Hu G e B H. induction H; intros F HF; subst G; simpl.
  - constructor. eauto using uniq_app_1.
  - constructor. eauto using uniq_app_1.
  - destruct (eq_var x0 x) as [->|Hneq].
    + assert (A0 = A) by
        (eapply binds_unique; [exact H0 | apply binds_app_r | exact H];
         apply binds_cons_2; reflexivity).
      subst A0. eapply typing_weaken; eauto using uniq_app_1.
      intros y T Hy. inversion Hy.
    + apply binds_app_1 in H0 as [H0|H0].
      * constructor; eauto using uniq_app_1.
      * apply binds_cons_1 in H0 as [[Heq _]|H0]; [congruence | inversion H0].
  - eapply Etyp_abs with (L := L \u {{x}}); [|eassumption|eassumption].
    intros y Hy.
    assert (Hneq : y <> x) by (intro Heq; subst; fsetdec).
    unfold open_exp_wrt_exp.
    pose proof (subst_open_exp e u x (e_var_f y) 0 (typing_scoped _ _ _ Hu)) as Heq.
    simpl in Heq. destruct (eq_var y x); [contradiction | rewrite <- Heq].
    apply H0; [fsetdec | reflexivity].
  - eauto using Etyp_app.
  - eauto using Etyp_merge.
  - eauto using Etyp_anno.
  - apply Etyp_fix with (L := L \u {{x}}). intros y Hy.
    assert (Hneq : y <> x) by (intro Heq; subst; fsetdec).
    unfold open_exp_wrt_exp.
    pose proof (subst_open_exp e u x (e_var_f y) 0 (typing_scoped _ _ _ Hu)) as Heq.
    simpl in Heq. destruct (eq_var y x); [contradiction | rewrite <- Heq].
    apply H0; [fsetdec | reflexivity].
  - rewrite (subst_fresh_exp v1 u x), (subst_fresh_exp v2 u x);
      eauto using Etyp_mergev, uniq_app_1.
    + intro Hin. pose proof (typing_fv _ _ _ H2 _ Hin) as Hdom.
      simpl in Hdom. fsetdec.
    + intro Hin. pose proof (typing_fv _ _ _ H1 _ Hin) as Hdom.
      simpl in Hdom. fsetdec.
Qed.

Lemma typing_open_closed : forall L e u A B,
    (forall x, x \notin L -> Etyping [(x,A)] (open_exp_wrt_exp e (e_var_f x)) B) ->
    Etyping nil u A ->
    Etyping nil (open_exp_wrt_exp e u) B.
Proof.
  intros L e u A B H Hu.
  destruct (atom_fresh (L \u fv_exp e)) as [x Hx].
  assert (HxL : x \notin L) by fsetdec.
  unfold open_exp_wrt_exp.
  rewrite <- (subst_intro_exp e u x 0) by fsetdec.
  eapply typing_subst_closed; [exact Hu | exact (H x HxL) | reflexivity].
Qed.

Lemma toplike_dec : forall A, {topLike A} + {~ topLike A}.
Proof.
  induction A as [| | A IHA B IHB | A IHA B IHB].
  - right. intro H. inversion H.
  - left. constructor.
  - destruct IHB; [left; constructor; assumption | right; intro H; inversion H; auto].
  - destruct IHA, IHB;
      try solve [left; constructor; assumption | right; intro H; inversion H; auto].
Qed.

Lemma toplike_sub : forall B, topLike B -> forall A, sub A B.
Proof.
  intros B H. induction H; intro; eauto using S_top, S_toparr, S_andr.
Qed.

Lemma sub_top_inv : forall B, sub t_top B -> topLike B.
Proof.
  intros B H. remember t_top as A eqn:HA.
  induction H; inversion HA; subst; eauto using topLike.
Qed.

Lemma sub_preserves_toplike : forall A B, sub A B -> topLike A -> topLike B.
Proof.
  intros A B H. induction H; intro HA;
    inversion HA; subst; eauto using topLike, sub_top_inv.
Qed.

Lemma sub_and_inv : forall A B C,
    sub A (t_and B C) -> sub A B /\ sub A C.
Proof.
  intros A B C H. remember (t_and B C) as T eqn:HT.
  induction H; inversion HT; subst; intuition eauto using S_andl1, S_andl2.
Qed.

Lemma sub_refl : forall A, sub A A.
Proof.
  induction A; eauto using sub.
Qed.

Lemma sub_arrow_inv : forall A B C D,
    sub (t_arrow A B) (t_arrow C D) -> ~ topLike D ->
    sub C A /\ sub B D.
Proof.
  intros A B C D H Hnt. inversion H; subst; eauto using sub_top_inv.
  exfalso. eauto using sub_top_inv.
Qed.

Lemma sub_into_arrow : forall X A B C D,
    sub X (t_arrow A B) -> ~ topLike B ->
    (forall T, sub A T -> sub C A -> sub C T) ->
    (forall T, sub T B -> sub T D) ->
    sub C A -> sub X (t_arrow C D).
Proof.
  intros X A B C D H Hnt Hcontra Hco HC.
  remember (t_arrow A B) as T eqn:HT.
  induction H; inversion HT; subst; eauto using S_arr, S_andl1, S_andl2.
  exfalso. eauto using sub_top_inv.
Qed.

Lemma sub_trans : forall A B C, sub A B -> sub B C -> sub A C.
Proof.
  intros X B. revert X.
  induction B as [| | A IHA B IHB | A IHA B IHB];
    intros X C HX; induction C as [| | C IHC D IHD | C IHC D IHD]; intro HC;
    try solve [apply S_top | apply sub_and_inv in HC as [HC HD]; auto using S_andr].
  - exact HX.
  - inversion HC; subst. apply S_toparr. assumption.
  - inversion HC.
  - inversion HC; subst. apply S_toparr. assumption.
  - inversion HC.
  - destruct (toplike_dec D) as [HD|HD].
    + apply toplike_sub. constructor. exact HD.
    + apply sub_arrow_inv in HC as [HCA HBD]; [|exact HD].
      assert (HB : ~ topLike B) by (intro HB; apply HD; eauto using sub_preserves_toplike).
      eapply sub_into_arrow; eauto.
  - apply sub_and_inv in HX as [HXA HXB].
    inversion HC; subst; eauto.
  - apply sub_and_inv in HX as [HXA HXB].
    inversion HC; subst; eauto using S_toparr.
Qed.

Lemma sub_merge_ord_inv : forall A B C,
    sub (t_and A B) C -> ord C -> ~ topLike C -> sub A C \/ sub B C.
Proof.
  intros A B C H Ho Hnt.
  inversion H; subst; eauto.
  - exfalso. apply Hnt. constructor.
  - exfalso. apply Hnt. constructor. eauto using sub_top_inv.
  - inversion Ho.
Qed.

Fixpoint toplike_result (A : typ) : exp :=
  match A with
  | t_int | t_top => e_top
  | t_arrow _ B => e_abs t_top e_top B
  | t_and B C => e_merge (toplike_result B) (toplike_result C)
  end.

Lemma reduce_toplike : forall A v,
    topLike A -> lc_exp v -> TypedReduce v A (toplike_result A).
Proof.
  intros A v H. induction H; intro Hlc; simpl;
    eauto using TReduce_top, TReduce_toparr, TReduce_and.
Qed.

Lemma reduce_toplike_unique : forall v A w,
    TypedReduce v A w -> topLike A -> w = toplike_result A.
Proof.
  intros v A w H. induction H; intro HT; simpl in *; auto.
  - inversion HT.
  - exfalso. inversion HT; auto.
  - inversion HT; subst; f_equal; auto.
Qed.

Lemma reduce_source_lc : forall v A w, TypedReduce v A w -> lc_exp v.
Proof.
  intros v A w H. induction H; eauto using lc_exp.
Qed.

Lemma reduce_result_value : forall v A w, TypedReduce v A w -> value w.
Proof.
  intros v A w H. induction H;
    eauto using value_unit, value_lit, value_merge.
  - apply value_anno. constructor. intro. constructor.
  - apply value_anno. inversion H; subst. constructor. assumption.
Qed.

Lemma reduce_to_and_inv : forall v A B w,
    TypedReduce v (t_and A B) w ->
    exists w1 w2, w = e_merge w1 w2 /\ TypedReduce v A w1 /\ TypedReduce v B w2.
Proof.
  intros v A B w H. inversion H; subst; try solve [match goal with Ho : ord (t_and _ _) |- _ => inversion Ho end].
  eauto.
Qed.

Lemma reduce_merge_ord_inv : forall v1 v2 A w,
    TypedReduce (e_merge v1 v2) A w -> ord A -> ~ topLike A ->
    TypedReduce v1 A w \/ TypedReduce v2 A w.
Proof.
  intros v1 v2 A w H Ho Hnt. inversion H; subst; eauto.
  - exfalso. apply Hnt. constructor.
  - exfalso. apply Hnt. constructor. assumption.
  - inversion Ho.
Qed.

Lemma reduce_lift_left : forall A v1 v2 w,
    lc_exp v2 -> TypedReduce v1 A w -> TypedReduce (e_merge v1 v2) A w.
Proof.
  induction A; intros v1 v2 w Hlc H;
    try solve [eapply TReduce_mergevl; eauto using ord].
  destruct (reduce_to_and_inv _ _ _ _ H) as (w1 & w2 & -> & H1 & H2).
  apply TReduce_and; eauto.
Qed.

Lemma reduce_lift_right : forall A v1 v2 w,
    lc_exp v1 -> TypedReduce v2 A w -> TypedReduce (e_merge v1 v2) A w.
Proof.
  induction A; intros v1 v2 w Hlc H;
    try solve [eapply TReduce_mergevr; eauto using ord].
  destruct (reduce_to_and_inv _ _ _ _ H) as (w1 & w2 & -> & H1 & H2).
  apply TReduce_and; eauto.
Qed.

Lemma reduce_toplike_source : forall v A w,
    TypedReduce v A w ->
    (v = e_top \/ exists C e D, v = e_abs C e D /\ topLike D) ->
    topLike A.
Proof.
  intros v A w H. induction H; intro HS; eauto using topLike;
    destruct HS as [Heq | (X & body & Y & Heq & HY)]; try discriminate.
  inversion Heq; subst. constructor. eauto using sub_preserves_toplike.
Qed.

Lemma reduce_from_toplike_source : forall v u A w,
    lc_exp v ->
    (u = e_top \/ exists C e D, u = e_abs C e D /\ topLike D) ->
    TypedReduce u A w -> TypedReduce v A w.
Proof.
  intros v u A w Hlc Hu H.
  pose proof (reduce_toplike_source _ _ _ H Hu) as HA.
  rewrite (reduce_toplike_unique _ _ _ H HA).
  auto using reduce_toplike.
Qed.

Lemma reduce_abs_source : forall X e B D A w,
    lc_exp (e_abs X e B) -> sub B D ->
    TypedReduce (e_abs X e D) A w -> TypedReduce (e_abs X e B) A w.
Proof.
  intros X e B D A w Hlc HBD H.
  remember (e_abs X e D) as v eqn:Hv.
  induction H; inversion Hv; subst;
    eauto using TReduce_top, TReduce_toparr, TReduce_and.
  eapply TReduce_arrow; eauto using sub_trans.
Qed.

Lemma reduce_merge_source : forall v v1 v2 A w,
    lc_exp v ->
    (forall C u, TypedReduce v1 C u -> TypedReduce v C u) ->
    (forall C u, TypedReduce v2 C u -> TypedReduce v C u) ->
    TypedReduce (e_merge v1 v2) A w -> TypedReduce v A w.
Proof.
  intros v v1 v2 A w Hlc H1 H2 H.
  remember (e_merge v1 v2) as u eqn:Hu.
  induction H; inversion Hu; subst;
    eauto using TReduce_top, TReduce_toparr, TReduce_and.
Qed.

Lemma reduce_compose : forall v A u B w,
    TypedReduce v A u -> TypedReduce u B w -> TypedReduce v B w.
Proof.
  intros v A u B w H. revert B w.
  induction H; intros T w Hnext; auto.
  - eapply reduce_from_toplike_source; [eassumption | left; reflexivity | exact Hnext].
  - eapply reduce_from_toplike_source; [eassumption | | exact Hnext].
    right. exists t_top, e_top, B. auto.
  - eauto using reduce_abs_source.
  - eauto using reduce_lift_left.
  - eauto using reduce_lift_right.
  - eapply reduce_merge_source with (v1 := v1) (v2 := v2);
      eauto using reduce_source_lc.
Qed.

Lemma merge_typing_inv : forall v1 v2 T,
    Etyping nil (e_merge v1 v2) T ->
    exists A B, T = t_and A B /\ Etyping nil v1 A /\ Etyping nil v2 B /\
      (disjointSpec A B \/ consistencySpec v1 v2).
Proof.
  intros v1 v2 T H. inversion H; subst; eauto 8.
Qed.

(* An abstraction can be typed with a narrower domain than the one in its
   syntax. For disjointness it suffices to retain the cast's codomain. *)
Definition cast_observable (S T : typ) : Prop :=
  match T with
  | t_int => sub S t_int
  | t_arrow _ D => exists C, sub S (t_arrow C D)
  | _ => True
  end.

Lemma cast_observable_left : forall T A B,
    cast_observable A T -> cast_observable (t_and A B) T.
Proof.
  destruct T; simpl; intros; eauto using S_andl1.
  destruct H; eauto using S_andl1.
Qed.

Lemma cast_observable_right : forall T A B,
    cast_observable B T -> cast_observable (t_and A B) T.
Proof.
  destruct T; simpl; intros; eauto using S_andl2.
  destruct H; eauto using S_andl2.
Qed.

Lemma reduce_observable : forall v T w,
    TypedReduce v T w -> forall S,
    Etyping nil v S -> ~ topLike T -> cast_observable S T.
Proof.
  intros v T w H. induction H; intros S HT Hnt; simpl.
  - inversion HT; subst. constructor.
  - exact I.
  - exfalso. apply Hnt. constructor. assumption.
  - inversion HT; subst. eexists. apply S_arr; eauto using sub_refl.
  - destruct (merge_typing_inv _ _ _ HT) as (X & Y & -> & HX & HY & _).
    eauto using cast_observable_left.
  - destruct (merge_typing_inv _ _ _ HT) as (X & Y & -> & HX & HY & _).
    eauto using cast_observable_right.
  - exact I.
Qed.

Lemma disjoint_observable : forall T X Y,
    ord T -> disjointSpec X Y ->
    cast_observable X T -> cast_observable Y T -> topLike T.
Proof.
  intros T X Y Ho Hd. destruct Ho; simpl; intros HX HY.
  - constructor.
  - eauto.
  - destruct HX as [C HC], HY as [D HD].
    assert (H : topLike (t_arrow (t_and C D) B)).
    { apply Hd; eapply sub_trans; [eassumption | apply S_arr |
                                  eassumption | apply S_arr];
        eauto using S_andl1, S_andl2, sub_refl. }
    inversion H; subst. constructor. assumption.
Qed.

Lemma merge_cross_agree : forall v1 v2 X Y A w1 w2,
    Etyping nil v1 X -> Etyping nil v2 Y ->
    disjointSpec X Y \/ consistencySpec v1 v2 ->
    ord A -> ~ topLike A ->
    TypedReduce v1 A w1 -> TypedReduce v2 A w2 -> w1 = w2.
Proof.
  intros v1 v2 X Y A w1 w2 HX HY [Hd|Hc] Ho Hnt H1 H2.
  - exfalso. apply Hnt. eapply disjoint_observable; eauto using reduce_observable.
  - eapply Hc; eauto.
Qed.

Lemma reduce_deterministic : forall v A u,
    TypedReduce v A u -> forall S w,
    Etyping nil v S -> TypedReduce v A w -> u = w.
Proof.
  intros v A u H. induction H; intros S w HT Hw.
  - inversion Hw; reflexivity.
  - symmetry. apply (reduce_toplike_unique _ _ _ Hw). constructor; assumption.
  - symmetry. apply (reduce_toplike_unique _ _ _ Hw). constructor; assumption.
  - inversion Hw; subst; try contradiction; reflexivity.
  - destruct (toplike_dec A) as [Htop|Hnot].
    + rewrite (reduce_toplike_unique _ _ _ H0 Htop).
      symmetry. eauto using reduce_toplike_unique.
    + destruct (merge_typing_inv _ _ _ HT) as (X & Y & -> & HX & HY & Hm).
      destruct (reduce_merge_ord_inv _ _ _ _ Hw H1 Hnot);
        eauto using merge_cross_agree.
  - destruct (toplike_dec A) as [Htop|Hnot].
    + rewrite (reduce_toplike_unique _ _ _ H0 Htop).
      symmetry. eauto using reduce_toplike_unique.
    + destruct (merge_typing_inv _ _ _ HT) as (X & Y & -> & HX & HY & Hm).
      destruct (reduce_merge_ord_inv _ _ _ _ Hw H1 Hnot).
      * symmetry. eauto using merge_cross_agree.
      * eauto.
  - destruct (reduce_to_and_inv _ _ _ _ Hw) as (w1 & w2 & -> & H1 & H2).
    f_equal; eauto.
Qed.

Lemma reduce_preserves_typing : forall v A w,
    TypedReduce v A w -> forall S, Etyping nil v S -> Etyping nil w A.
Proof.
  intros v A w H. induction H; intros S HT.
  - constructor. constructor.
  - constructor. constructor.
  - eapply Etyp_abs with (L := {}) (B := t_top).
    + intros x Hx. constructor. apply uniq_cons; [constructor | simpl; fsetdec].
    + apply S_top.
    + auto using toplike_sub.
  - inversion HT; subst. eapply Etyp_abs; eauto using sub_trans.
  - destruct (merge_typing_inv _ _ _ HT) as (X & Y & -> & HX & HY & _). eauto.
  - destruct (merge_typing_inv _ _ _ HT) as (X & Y & -> & HX & HY & _). eauto.
  - apply Etyp_mergev.
    + constructor.
    + constructor; eauto using reduce_result_value.
    + eauto.
    + eauto.
    + intros C u1 u2 H1 H2. eapply (reduce_deterministic v C u1).
      * eapply reduce_compose; [exact H | exact H1].
      * exact HT.
      * eapply reduce_compose; [exact H0 | exact H2].
Qed.

Lemma value_lc : forall v, value v -> lc_exp v.
Proof.
  intros v H. induction H; eauto using lc_exp.
Qed.

Lemma reduce_exists_ordinary : forall v,
    value v -> forall S T, Etyping nil v S -> sub S T ->
    ord T -> ~ topLike T -> exists w, TypedReduce v T w.
Proof.
  intros v H. induction H; intros S T HT Hsub Ho Hnt.
  - inversion HT; subst. exfalso. eauto using sub_top_inv.
  - inversion HT; subst. inversion Hsub; subst;
      eauto using TReduce_lit, topLike, sub_top_inv;
      try solve [exfalso; apply Hnt; eauto using topLike, sub_top_inv | inversion Ho].
  - inversion HT; subst. destruct T as [| | C' D | C' D].
    + inversion Hsub.
    + exfalso. apply Hnt. constructor.
    + assert (HD : ~ topLike D) by (intro HD; apply Hnt; constructor; exact HD).
      apply sub_arrow_inv in Hsub as [Hdom Hcod]; [|exact HD].
      eexists. apply TReduce_arrow; eauto using sub_trans.
    + inversion Ho.
  - destruct (merge_typing_inv _ _ _ HT) as (X & Y & -> & HX & HY & _).
    destruct (sub_merge_ord_inv _ _ _ Hsub Ho Hnt) as [HS|HS].
    + destruct (IHvalue1 _ _ HX HS Ho Hnt) as [w Hw].
      exists w. eauto using TReduce_mergevl, value_lc.
    + destruct (IHvalue2 _ _ HY HS Ho Hnt) as [w Hw].
      exists w. eauto using TReduce_mergevr, value_lc.
Qed.

Lemma reduce_exists : forall T v S,
    value v -> Etyping nil v S -> sub S T -> exists w, TypedReduce v T w.
Proof.
  induction T; intros v S Hv HT Hsub.
  - eapply reduce_exists_ordinary; eauto using ord.
    intro H. inversion H.
  - exists e_top. eauto using TReduce_top, value_lc.
  - destruct (toplike_dec T2) as [Htop|Hnot].
    + exists (e_abs t_top e_top T2). eauto using TReduce_toparr, value_lc.
    + eapply reduce_exists_ordinary; eauto using ord.
      intro H. inversion H; contradiction.
  - destruct (sub_and_inv _ _ _ Hsub) as [H1 H2].
    destruct (IHT1 _ _ Hv HT H1) as [w1 Hw1].
    destruct (IHT2 _ _ Hv HT H2) as [w2 Hw2].
    exists (e_merge w1 w2). auto using TReduce_and.
Qed.

Lemma value_no_step : forall v, value v -> forall e, ~ step v e.
Proof.
  intros v H. induction H; intros e' Hstep; inversion Hstep; subst.
  - eapply IHvalue1. eassumption.
  - eapply IHvalue2. eassumption.
Qed.

Lemma arrow_value_inv : forall v A B,
    value v -> Etyping nil v (t_arrow A B) ->
    exists C e, v = e_abs C e B /\ sub A C.
Proof.
  intros v A B Hv HT. inversion Hv; subst; inversion HT; subst; eauto.
Qed.

Theorem preservation : forall e e' A,
    Etyping nil e A ->
    step e e' ->
    Etyping nil e' A.
Proof.
  intros e e' A HT Hstep. revert A HT.
  induction Hstep; intros T HT; inversion HT; subst.
  - match goal with
    | Habs : Etyping nil (e_abs _ _ _) _ |- _ => inversion Habs; subst
    end.
    eapply Etyp_anno; [eapply typing_open_closed |]; eauto using reduce_preserves_typing.
  - eauto using reduce_preserves_typing.
  - eauto using Etyp_app.
  - eauto using Etyp_app.
  - eauto using Etyp_merge.
  - exfalso. eapply (value_no_step _ H3). eapply Step_mergel; eassumption.
  - eauto using Etyp_merge.
  - exfalso. eapply (value_no_step _ H3). eapply Step_merger; eassumption.
  - eauto using Etyp_anno.
  - eapply typing_open_closed; [eassumption | exact HT].
Qed.

Theorem progress : forall e A,
    Etyping nil e A ->
    value e \/ exists e', step e e'.
Proof.
  intros e A HT. remember (@nil (atom * typ)) as G eqn:HG.
  induction HT; subst G.
  - left. constructor.
  - left. constructor.
  - inversion H0.
  - left. apply value_anno. eapply typing_lc. eauto using Etyp_abs.
  - right. destruct (IHHT2 eq_refl) as [Hv1|[e1' Hs1]].
    + destruct (IHHT1 eq_refl) as [Hv2|[e2' Hs2]].
      * destruct (arrow_value_inv _ _ _ Hv1 HT2) as (C & e & -> & HC).
        destruct (reduce_exists _ _ _ Hv2 HT1 HC) as [w Hw].
        eexists. eapply Step_beta; eauto using value_lc.
      * eexists. eauto using Step_appr.
    + eexists. eauto using Step_appl, typing_lc.
  - destruct (IHHT1 eq_refl) as [Hv1|[e1' Hs1]].
    + destruct (IHHT2 eq_refl) as [Hv2|[e2' Hs2]].
      * left. auto using value_merge.
      * right. eexists. eauto using Step_merger.
    + right. eexists. eauto using Step_mergel, typing_lc.
  - right. destruct (IHHT eq_refl) as [Hv|[e' Hs]].
    + destruct (reduce_exists _ _ _ Hv HT H) as [w Hw].
      exists w. auto using Step_annov.
    + eexists. eauto using Step_anno.
  - right. eexists. apply Step_fix. eapply typing_lc. eauto using Etyp_fix.
  - left. assumption.
Qed.
