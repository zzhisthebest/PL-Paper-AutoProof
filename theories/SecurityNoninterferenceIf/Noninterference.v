From AutoProof.SecurityNoninterferenceIf Require Export Typing.
From AutoProof.SecurityNoninterferenceIf Require Import LogicalRelation.
From AutoProof.SecurityNoninterferenceIf Require Import Evaluation.
Import ListNotations.

(* program_context 表示一个留了空位的程序模板。
它本身还不是完整程序；用 plug C t 把程序 t 填进去，才得到完整程序。 *)
Inductive program_context : Type :=
  | C_Hole : program_context
  | C_Abs : ty -> program_context -> security -> program_context
  | C_AppLeft : program_context -> tm -> label -> program_context
  | C_AppRight : tm -> program_context -> label -> program_context
  | C_PairLeft : program_context -> tm -> security -> program_context
  | C_PairRight : tm -> program_context -> security -> program_context
  | C_Fst : program_context -> label -> program_context
  | C_Snd : program_context -> label -> program_context
  | C_Inl : program_context -> security -> program_context
  | C_Inr : program_context -> security -> program_context
  | C_CaseScrutinee : program_context -> tm -> tm -> label -> program_context
  | C_CaseLeft : tm -> program_context -> tm -> label -> program_context
  | C_CaseRight : tm -> tm -> program_context -> label -> program_context
  | C_Protect : label -> program_context -> program_context
  | C_IfCondition : program_context -> tm -> tm -> label -> program_context
  | C_IfThen : tm -> program_context -> tm -> label -> program_context
  | C_IfElse : tm -> tm -> program_context -> label -> program_context.

(* plug C t 就是：把程序 t 填进模板 C 的空位。 *)
Fixpoint plug (C : program_context) (t : tm) : tm :=
  match C with
  | C_Hole => t
  | C_Abs T C' kappa => tm_abs T (plug C' t) kappa
  | C_AppLeft C' t2 r => tm_app (plug C' t) t2 r
  | C_AppRight t1 C' r => tm_app t1 (plug C' t) r
  | C_PairLeft C' t2 kappa => tm_pair (plug C' t) t2 kappa
  | C_PairRight t1 C' kappa => tm_pair t1 (plug C' t) kappa
  | C_Fst C' r => tm_fst (plug C' t) r
  | C_Snd C' r => tm_snd (plug C' t) r
  | C_Inl C' kappa => tm_inl (plug C' t) kappa
  | C_Inr C' kappa => tm_inr (plug C' t) kappa
  | C_CaseScrutinee C' body1 body2 r => tm_case (plug C' t) body1 body2 r
  | C_CaseLeft t0 C' body2 r => tm_case t0 (plug C' t) body2 r
  | C_CaseRight t0 body1 C' r => tm_case t0 body1 (plug C' t) r
  | C_Protect l C' => tm_protect l (plug C' t)
  | C_IfCondition C' y n r => tm_if (plug C' t) y n r
  | C_IfThen c C' n r => tm_if c (plug C' t) n r
  | C_IfElse c y C' r => tm_if c y (plug C' t) r
  end.

(* context_has_type C T_hole T_result 表示：模板 C 的空位需要一个 T_hole 类型的程序；
填好后，整个程序的类型是 T_result *)
Definition context_has_type (C : program_context) (T_hole T_result : ty) : Prop :=
  exists L : list atom, forall x : atom, ~ In x L ->
    has_type (update empty x T_hole) (plug C (tm_fvar x)) T_result.

(* ground T 表示：类型 T 里面没有函数类型 Ty_Arrow。 *)
Fixpoint ground (T : ty) : Prop :=
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ => ground T1 /\ ground T2
  | Ty_Arrow _ _ _ => False
  end.

(* transparent_at kappa T 表示：类型 T 自己和内部各层的安全标注，都不高于 kappa。 *)
Fixpoint transparent_at (kappa : security) (T : ty) : Prop :=
  security_le (security_of T) kappa /\
  match T with
  | Ty_Unit _ => True
  | Ty_Sum T1 T2 _ | Ty_Prod T1 T2 _ | Ty_Arrow T1 T2 _ =>
      transparent_at kappa T1 /\ transparent_at kappa T2
  end.

(* transparent T 表示 T 内部每层的 reader 和 indirect_reader 都不高于
   T 最外层的对应级别：能看到整个值，就不会在里面遇到更秘密的成员。 *)
Definition transparent (T : ty) : Prop := transparent_at (security_of T) T.

(* same_result t1 t2 表示：只要 t1 和 t2 都算完，它们的结果在忽略安全标注后相同。 *)
Definition same_result (t1 t2 : tm) : Prop :=
  forall v1 v2 : tm,
    evaluates t1 v1 -> evaluates t2 v2 ->
    erase_security v1 = erase_security v2.

Lemma ground_related_values_equal : forall T kappa observer v1 v2,
  ground T -> transparent_at kappa T ->
  flows_to kappa.(indirect_reader) observer ->
  value_relation observer T v1 v2 ->
  erase_security v1 = erase_security v2.
Proof.
  induction T; intros kappa observer v1 v2 Hground Htransparent Hflow Hrelated;
    simpl in Hground; try contradiction;
    destruct Hrelated as [_ [_ [_ [_ Hrelated]]]];
    destruct Htransparent as [Hsecurity Hchildren];
    specialize (Hrelated (flows_to_trans _ _ _ (proj2 Hsecurity) Hflow)).
  - destruct Hrelated as [k1 [k2 [-> ->]]]. reflexivity.
  - destruct Hground as [Hground1 Hground2].
    destruct Hchildren as [Htransparent1 Htransparent2].
    destruct Hrelated as [Hleft | Hright].
    + destruct Hleft as [u1 [u2 [k1 [k2 [-> [-> Hrelated]]]]]].
      simpl. f_equal. eapply IHT1; eassumption.
    + destruct Hright as [u1 [u2 [k1 [k2 [-> [-> Hrelated]]]]]].
      simpl. f_equal. eapply IHT2; eassumption.
  - destruct Hground as [Hground1 Hground2].
    destruct Hchildren as [Htransparent1 Htransparent2].
    destruct Hrelated as [a1 [b1 [a2 [b2 [k1 [k2 [-> [-> [Ha Hb]]]]]]]]].
    simpl. f_equal; [eapply IHT1 | eapply IHT2]; eassumption.
Qed.

Lemma expression_relation_same_result : forall T t1 t2,
  ground T -> transparent T ->
  expression_relation (security_of T).(indirect_reader) T t1 t2 ->
  same_result t1 t2.
Proof.
  intros T t1 t2 Hground Htransparent [_ [_ Hrelated]] v1 v2 Heval1 Heval2.
  eapply ground_related_values_equal with (kappa := security_of T).
  - exact Hground.
  - exact Htransparent.
  - apply flows_to_refl.
  - exact (Hrelated v1 v2 Heval1 Heval2).
Qed.

(* Theorem 2.3 packages secret expressions as values without evaluating them
   first. The unused binder does not shift a locally closed t. *)
Definition delay (t : tm) : tm := tm_abs (Ty_Unit public) t public.
Definition force (t : tm) : tm := tm_app t (tm_unit public) High.

Lemma open_locally_closed : forall t u,
  locally_closed t -> open t u = t.
Proof.
  intros t u H. unfold open. apply (open_rec_lc_at t 0 0 u H).
  apply Nat.le_refl.
Qed.

Lemma typing_delay : forall t T,
  has_type empty t T ->
  has_type empty (delay t) (Ty_Arrow (Ty_Unit public) T public).
Proof.
  intros t T Ht. unfold delay. apply T_Abs with (L := []).
  - exact I.
  - exact I.
  - intros x _. rewrite open_locally_closed.
    + apply typing_weaken_empty; exact Ht.
    + exact (proj1 (typing_regular _ _ _ Ht)).
Qed.

Lemma delay_secret_expressions_related : forall observer T t1 t2,
  has_type empty t1 T -> has_type empty t2 T ->
  ~ flows_to (security_of T).(indirect_reader) observer ->
  value_relation observer (Ty_Arrow (Ty_Unit public) T public)
    (delay t1) (delay t2).
Proof.
  intros observer T t1 t2 Ht1 Ht2 Hhidden.
  pose proof (typing_delay _ _ Ht1) as Hd1.
  pose proof (typing_delay _ _ Ht2) as Hd2.
  pose proof (proj1 (typing_regular _ _ _ Hd1)) as Hlc1.
  pose proof (proj1 (typing_regular _ _ _ Hd2)) as Hlc2.
  assert (expression_relation observer (Ty_Arrow (Ty_Unit public) T public)
    (delay t1) (delay t2)) as Hrelated.
  { apply expression_relation_abs.
    - exact (typing_erasure _ _ _ Hd1).
    - exact (typing_erasure _ _ _ Hd2).
    - exact Hlc1.
    - exact Hlc2.
    - intros a1 a2 _. rewrite !open_locally_closed.
      + apply hidden_expressions_related; [exact Hhidden | |].
        * exact (typing_erasure _ _ _ Ht1).
        * exact (typing_erasure _ _ _ Ht2).
      + exact (proj1 (typing_regular _ _ _ Ht2)).
      + exact (proj1 (typing_regular _ _ _ Ht1)). }
  destruct Hrelated as [_ [_ Hrelated]]. apply Hrelated;
    apply evaluates_value; apply v_abs; assumption.
Qed.

Lemma force_delay_evaluates : forall t T v,
  has_type empty t T -> (evaluates (force (delay t)) v <-> evaluates t v).
Proof.
  intros t T v Ht.
  assert (step (force (delay t)) (tm_protect Low t)) as Hstep.
  { replace t with (open t (tm_unit public)) at 2
      by (apply open_locally_closed; exact (proj1 (typing_regular _ _ _ Ht))).
    apply ST_AppAbs.
    - apply v_abs. exact (proj1 (typing_regular _ _ _ (typing_delay _ _ Ht))).
    - apply v_unit.
    - exact I. }
  rewrite (evaluates_step_iff _ _ _ Hstep).
  split; intros Heval; apply big_step_iff_evaluates in Heval;
    apply big_step_iff_evaluates.
  - inversion Heval; subst. rewrite protect_value_low. assumption.
  - rewrite <- (protect_value_low v). apply B_Protect. exact Heval.
Qed.

Lemma subst_plug_fresh : forall C x u,
  ~ In x (fv (plug C (tm_unit public))) ->
  subst x u (plug C (tm_fvar x)) = plug C u.
Proof.
  induction C; intros x u Hfresh; simpl in *;
    repeat rewrite in_app_iff in Hfresh;
    try rewrite IHC by tauto;
    repeat rewrite subst_fresh by tauto;
    try reflexivity.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(* ground T_result 排除结果类型中任何位置的函数：same_result 比较的是求值后的值
   去掉安全标注后是否代码相同，而语义相同的函数可能有不同代码。例如忽略安全标注时，
   lambda x : T, x 和 lambda x : T, (lambda y : T, y) x 对任何合法的值 v 都返回 v，
   后者只是多做一次恒等函数应用。而ground 的最终值
   只由 unit、pair、inl、inr 构成，去掉安全标注后，语义相同一定代码相同。 *)
(*  *)
Theorem noninterference : forall (C : program_context) (t1 t2 : tm)
    (T_secret T_result : ty),
  has_type empty t1 T_secret ->
  has_type empty t2 T_secret ->
  context_has_type C T_secret T_result ->
  ground T_result ->
  (* 关键就是这个： 既然transparent T_result，那么t1和t2一定信息被丢弃了，T_secret才消失了*)
  (* 例（省略安全标注）：C[s] = fst (pair (inl unit) s)。其中第一项和 pair 外层公开，
     s 是秘密，fst 的读取级别为 Low。取 t1 = inl unit、t2 = inr unit，二者都标为秘密：
     C[t1] -> fst (pair (inl unit) (inl unit)) -> inl unit；
     C[t2] -> fst (pair (inl unit) (inr unit)) -> inl unit。 *)
  transparent T_result ->
  (* T_secret 的信息不允许流向 T_result 所代表的观察级别。 *)
  ~ flows_to (security_of T_secret).(indirect_reader)
      (security_of T_result).(indirect_reader) ->
  same_result (plug C t1) (plug C t2).
Proof.
  intros C t1 t2 Tsecret Tresult Ht1 Ht2 [L HC] Hground Htransparent Hhidden.
  destruct (fresh_atom (L ++ fv (plug C (tm_unit public)))) as [x Hfresh].
  rewrite in_app_iff in Hfresh.
  assert (expression_relation (security_of Tresult).(indirect_reader) Tsecret t1 t2)
    as Hsecret.
  { apply hidden_expressions_related; [exact Hhidden | |].
    - exact (typing_erasure _ _ _ Ht1).
    - exact (typing_erasure _ _ _ Ht2). }
  assert (related_expression_substitutions (security_of Tresult).(indirect_reader)
    (update empty x Tsecret)
    (substitution_update tm_fvar x t1) (substitution_update tm_fvar x t2)) as Henv.
  { intros y U HU. simpl in HU. destruct (Nat.eqb y x) eqn:E; [|discriminate].
    apply Nat.eqb_eq in E. subst y. inversion HU; subst U.
    unfold substitution_update. rewrite Nat.eqb_refl. exact Hsecret. }
  assert (~ In x L) as Hx by tauto.
  pose proof (fundamental_expressions _ _ _ (HC x Hx) _ _ _ Henv) as Hrelated.
  rewrite !instantiate_single, !subst_plug_fresh in Hrelated by tauto.
  apply expression_relation_same_result with (T := Tresult); assumption.
Qed.
