From strictness.cbpv Require Import strict_semtyping.
From Stdlib Require Import Lia Logic.Eqdep_dec.

Local Lemma down_env_lookup {X n m} (f : fin n -> X) (H : m <= n) i :
  down_env_until f m H i = f (up_fin_until n H i).
Proof.
  unfold down_env_until, down_env_until', ren_env, up_fin_until.
  generalize (shift_p (n - m) i), (le_minus_plus m n H).
  generalize (n - m + m).
  intros p j e. destruct e. reflexivity.
Qed.

Local Lemma up_fin_same n (H : n <= n) i : up_fin_until n H i = i.
Proof.
  unfold up_fin_until. generalize (le_minus_plus n n H).
  replace (n - n) with 0 by lia. simpl. intros e.
  replace e with (@eq_refl nat n) by (apply UIP_dec; exact Nat.eq_dec).
  reflexivity.
Qed.

Local Lemma up_fin_step m n (H : m <= n) (H' : m <= S n) i :
  up_fin_until (S n) H' i = shift (up_fin_until n H i).
Proof.
  unfold up_fin_until.
  generalize (le_minus_plus m (S n) H').
  replace (S n - m) with (S (n - m)) by lia.
  change (forall e' : S n = S (n - m + m),
    eq_rec_r fin (shift (shift_p (n - m) i)) e' =
    shift (eq_rec_r fin (shift_p (n - m) i) (le_minus_plus m n H))).
  generalize (shift_p (n - m) i), (le_minus_plus m n H).
  generalize (n - m + m).
  intros p j e. destruct e. intros e'.
  replace e' with (@eq_refl nat (S n)) by (apply UIP_dec; exact Nat.eq_dec).
  reflexivity.
Qed.

Local Lemma up_fin_compose l m n (Hlm : l <= m) (Hmn : m <= n)
    (Hln : l <= n) i :
  up_fin_until n Hmn (up_fin_until m Hlm i) = up_fin_until n Hln i.
Proof.
  revert Hmn Hln. induction n as [|n IH]; intros Hmn Hln.
  - assert (m = 0) by lia. subst m.
    rewrite up_fin_same. f_equal. apply Peano_dec.le_unique.
  - destruct (Nat.eq_dec m (S n)) as [->|Hne].
    + rewrite up_fin_same. f_equal. apply Peano_dec.le_unique.
    + assert (Hm : m <= n) by lia.
      rewrite (up_fin_step _ _ Hm).
      rewrite (up_fin_step _ _ (Nat.le_trans _ _ _ Hlm Hm)). f_equal. apply IH.
Qed.

Local Ltac strict_injections :=
  repeat match goal with
  | H : @existT ?A ?P ?i ?x = @existT ?A ?P ?i ?y |- _ =>
      let dec := constr:(ltac:(decide equality) : forall a b : A, {a = b} + {a <> b}) in
      let E := fresh in
      pose proof (inj_pair2_eq_dec A dec P i x y H) as E;
      clear H; subst
  end.

Local Lemma attrs_equiv_down k (C D : Clos k) s :
  eq_up_to_attrs C D -> eq_up_to_attrs (down_clos s C) (down_clos s D).
Proof. induction 1; simpl; constructor; auto. Qed.

Local Lemma attrs_equiv_cons n W W' (ρ ρ' : env n) :
  eq_up_to_attrs W W' -> eq_env_up_to_attrs ρ ρ' ->
  eq_env_up_to_attrs (W .: ρ) (W' .: ρ').
Proof. intros HW Hρ [j|]; [apply Hρ | exact HW]. Qed.

Local Ltac strict_invert H := inversion H; subst; clear H; strict_injections.

(* Evaluation determines the result up to attributes. This lets a failure in a
   continuation rule out every possible evaluation of the enclosing term. *)
Local Lemma strict_eval_val_unique n γ (ρ : env n) V W :
  EvalVal γ ρ V W ->
  forall γ' ρ' W', eq_env_up_to_attrs ρ ρ' -> EvalVal γ' ρ' V W' ->
    eq_up_to_attrs W W'.
Proof.
  induction 1; intros γe ρe We Heq He; strict_invert He;
    eauto using eq_up_to_attrs.
Qed.

Local Lemma strict_eval_comp_unique n γ (ρ : env n) M T :
  EvalComp γ ρ M T ->
  forall γ' ρ' T', eq_env_up_to_attrs ρ ρ' -> EvalComp γ' ρ' M T' ->
    eq_up_to_attrs T T'.
Proof.
  induction 1; intros γe ρe Te Heq He; strict_invert He;
    try solve [eauto using eq_up_to_attrs, strict_eval_val_unique].
  all: try match goal with
  | Henv : eq_env_up_to_attrs ?r ?r',
    H1 : EvalVal _ ?r ?V _, H2 : EvalVal _ ?r' ?V _ |- _ =>
      let HW := fresh "HW" in
      pose proof (strict_eval_val_unique _ _ _ _ _ H1 _ _ _ Henv H2) as HW;
      try solve [inversion HW]
  end.
  - match goal with
    | H : EvalComp _ ρe _ (Closure _ _ _ _ _) |- _ =>
        pose proof (IHEvalComp1 _ _ _ Heq H) as HF
    end.
    strict_invert HF.
    apply attrs_equiv_down. eapply IHEvalComp2; [|eassumption].
    apply attrs_equiv_cons; [apply attrs_equiv_down |]; assumption.
  - strict_invert HW. apply attrs_equiv_down. eapply IHEvalComp; [|eassumption].
    repeat apply attrs_equiv_cons; assumption.
  - match goal with
    | H : EvalComp _ ρe _ (Return _) |- _ =>
        pose proof (IHEvalComp1 _ _ _ Heq H) as HR
    end.
    strict_invert HR. apply attrs_equiv_down. eapply IHEvalComp2; [|eassumption].
    apply attrs_equiv_cons; assumption.
  - strict_invert HW. apply attrs_equiv_down. eapply IHEvalComp; eassumption.
  - strict_invert HW. apply attrs_equiv_down. eapply IHEvalComp; [|eassumption].
    apply attrs_equiv_cons; assumption.
  - strict_invert HW. apply attrs_equiv_down. eapply IHEvalComp; [|eassumption].
    apply attrs_equiv_cons; assumption.
Qed.

Local Lemma down_env_same {X n} (f : fin n -> X) (H : n <= n) :
  down_env_until f n H = f.
Proof.
  unfold down_env_until. generalize (le_minus_plus n n H).
  replace (n - n) with 0 by lia. simpl. intros e.
  replace e with (@eq_refl nat n) by (apply UIP_dec; exact Nat.eq_dec).
  reflexivity.
Qed.

Local Lemma down_env_step {X m n} (f : fin (S n) -> X) (H : m <= n) (H' : m <= S n) :
  down_env_until f m H' = down_env_until (ren_env f shift) m H.
Proof.
  unfold down_env_until.
  generalize (le_minus_plus m (S n) H').
  replace (S n - m) with (S (n - m)) by lia.
  change (forall e' : S n = S (n - m + m),
    (fun i => eq_rect_r (fun p => fin p -> X) f (eq_sym e') (shift (shift_p (n - m) i))) =
    (fun i => eq_rect_r (fun p => fin p -> X) (ren_env f shift)
      (eq_sym (le_minus_plus m n H)) (shift_p (n - m) i))).
  generalize (shift_p (n - m) : fin m -> fin (n - m + m)), (le_minus_plus m n H).
  generalize (n - m + m).
  intros p j e. destruct e. intros e'.
  replace e' with (@eq_refl nat (S n)) by (apply UIP_dec; exact Nat.eq_dec).
  reflexivity.
Qed.

Local Lemma down_env_compose {X l m n} (f : fin n -> X)
    (Hlm : l <= m) (Hmn : m <= n) (Hln : l <= n) :
  down_env_until (down_env_until f m Hmn) l Hlm = down_env_until f l Hln.
Proof.
  revert f Hmn Hln. induction n as [|n IH]; intros f Hmn Hln.
  - assert (m = 0) by lia. subst m.
    rewrite down_env_same. f_equal. apply Peano_dec.le_unique.
  - destruct (Nat.eq_dec m (S n)) as [->|Hne].
    + rewrite down_env_same. f_equal. apply Peano_dec.le_unique.
    + assert (Hm : m <= n) by lia.
      rewrite (down_env_step f Hm Hmn).
      rewrite (down_env_step f (Nat.le_trans _ _ _ Hlm Hm) Hln).
      apply IH.
Qed.

Local Lemma down_ty_same n k (A : Ty n k) (H : n <= n) :
  down_ty_until A n H = A.
Proof. induction A; cbn; f_equal; auto using down_env_same. Qed.

Local Lemma down_ty_lift n k (A : Ty n k) q (H : n <= S n) :
  down_ty_until (up_Ty q A) n H = A.
Proof.
  induction A; cbn [up_Ty map_Ty down_ty_until]; f_equal; auto.
  rewrite (down_env_step _ (Nat.le_refl n)), down_env_same. reflexivity.
Qed.

Local Lemma down_clos_compose k (C : Clos k) a b :
  down_clos a (down_clos b C) = down_clos (Nat.min b a) C.
Proof.
  induction C; cbn [down_clos]; try reflexivity; try (f_equal; assumption).
  - rewrite down_env_compose with (Hln := Nat.le_trans _ _ _
      (min_le _ _) (min_le _ _)).
    generalize (Nat.le_trans _ _ _ (min_le (Nat.min mOuter b) a) (min_le mOuter b)).
    generalize (min_le mOuter (Nat.min b a)).
    rewrite (Nat.min_assoc mOuter b a). intros H1 H2.
    replace H2 with H1 by apply Peano_dec.le_unique. reflexivity.
  - rewrite down_env_compose with (Hln := Nat.le_trans _ _ _
      (min_le _ _) (min_le _ _)).
    generalize (Nat.le_trans _ _ _ (min_le (Nat.min mOuter b) a) (min_le mOuter b)).
    generalize (min_le mOuter (Nat.min b a)).
    rewrite (Nat.min_assoc mOuter b a). intros H1 H2.
    replace H2 with H1 by apply Peano_dec.le_unique. reflexivity.
Qed.

Local Lemma down_clos_smaller k (C : Clos k) a b :
  a <= b -> down_clos a (down_clos b C) = down_clos a C.
Proof. intros H. rewrite down_clos_compose, Nat.min_r; auto. Qed.

Local Lemma down_clos_larger k (C : Clos k) a b :
  a <= b -> down_clos b (down_clos a C) = down_clos a C.
Proof. intros H. rewrite down_clos_compose, Nat.min_l; auto. Qed.

Local Lemma non_func_down n m (B : CompTy n) (H : m <= n) :
  non_func (down_ty_until B m H) <-> non_func B.
Proof.
  assert (P : forall k (A : Ty n k),
    match k as k' return Ty n k' -> Prop with
    | ValFlag => fun _ => True
    | CompFlag => fun B => non_func (down_ty_until B m H) <-> non_func B
    end A).
  { destruct A; simpl; auto; unfold non_func.
    - split; intros HF; exfalso; eapply HF; reflexivity.
    - split; intros _ ? ? ? E; discriminate. }
  exact (P CompFlag B).
Qed.

Local Definition maybe_result {n m} (B : CompTy n) l (x : fin l)
    (δ : attrs m) (ρ : env m) M (f : ClosComp -> ClosComp) :=
  EvalCompFail ρ M \/ exists T, EvalComp δ ρ M T /\ LR_maybe B (f T) l x.

Local Definition strict_result {n m} (B : CompTy n) l (x : fin l)
    (δ : attrs m) (ρ : env m) M (f : ClosComp -> ClosComp) :=
  (non_func B -> EvalCompFail ρ M) /\
  (~ non_func B -> EvalCompFail ρ M \/ exists T, EvalComp δ ρ M T /\ LR_no B (f T) l x).

Local Lemma maybe_result_map n n' m (B : CompTy n) (B' : CompTy n')
    l (x : fin l) (δ : attrs m) ρ M f g :
  (forall T, LR_maybe B (f T) l x -> LR_maybe B' (g T) l x) ->
  maybe_result B l x δ ρ M f -> maybe_result B' l x δ ρ M g.
Proof.
  intros Hmap [HF | (T & HE & HT)]; [left | right]; eauto.
Qed.

Local Lemma strict_result_map n n' m (B : CompTy n) (B' : CompTy n')
    l (x : fin l) (δ : attrs m) ρ M f g :
  (non_func B' <-> non_func B) ->
  (forall T, LR_no B (f T) l x -> LR_no B' (g T) l x) ->
  strict_result B l x δ ρ M f -> strict_result B' l x δ ρ M g.
Proof.
  intros HH Hmap [HF HT]; split; intros HB; [apply HF; tauto |].
  destruct HT as [HF' | (T & HE & HR)]; [tauto | left; exact HF' | right; eauto].
Qed.

Local Lemma lr_results_map n n' m (B : CompTy n) (B' : CompTy n')
    l (x : fin l) (δ : attrs m) ρ M f g :
  (non_func B' <-> non_func B) ->
  (forall T, LR_maybe B (f T) l x -> LR_maybe B' (g T) l x) ->
  (forall T, LR_no B (f T) l x -> LR_no B' (g T) l x) ->
  (maybe_result B l x δ ρ M f -> maybe_result B' l x δ ρ M g) /\
  (strict_result B l x δ ρ M f -> strict_result B' l x δ ρ M g).
Proof. split; eauto using maybe_result_map, strict_result_map. Qed.

Local Definition lr_scope_change {n k} (R : forall n, Ty n k -> Clos k ->
    forall l, fin l -> Prop) (A : Ty n k) m (H : m <= n) l (x : fin l) :=
  (forall C s, l <= s -> s <= m -> R n A C l x ->
    R m (down_ty_until A m H) (down_clos s C) l x) /\
  (forall C, R m (down_ty_until A m H) C l x -> R n A C l x).

(* Narrowing clips closures and types together. Extending a type leaves the
   closure as it is, because its recorded scope already fits the smaller type. *)
Local Lemma lr_scope n k (A : Ty n k) :
  forall m (H : m <= n) l (x : fin l),
  lr_scope_change (fun n => @LR_maybe n k) A m H l x /\
  lr_scope_change (fun n => @LR_no n k) A m H l x.
Proof.
  induction A as [|γ B IHB|A IHA B IHB|A IHA B IHB|q A IHA B IHB|A IHA];
    intros m H l x; unfold lr_scope_change in *;
    (try specialize (IHA m H l x) as [[trimA liftA] _]);
    (try specialize (IHB m H l x) as [[trimB liftB] [trimNo liftNo]]);
    repeat split; try (intros; contradiction).
  { intros C s Hls Hsm HC. cbn [LR_maybe] in HC. subst. reflexivity. }
  { intros C HC. exact HC. }
  { intros C s Hls Hsm HC.
    cbn [LR_maybe] in HC.
    destruct HC as (o & inner & δ & δi & ρ & M & Hoi & Hon & Hlo & Hli &
      Hδ & Hi & -> & HC).
    set (r := Nat.min o s).
    assert (Hlr : l <= r) by (unfold r; lia).
    assert (Hrm : r <= m) by (unfold r; lia).
    assert (Hri : r <= inner) by (unfold r; lia).
    cbn [down_ty_until LR_maybe down_clos].
    exists r, inner, (down_env_until δ r (min_le o s)), δi, ρ, M,
      Hri, Hrm, Hlr, Hli.
    split.
    { rewrite (down_env_compose γ Hrm H (Nat.le_trans _ _ _ Hrm H)), <- Hδ.
      symmetry. apply down_env_compose. }
    split.
    { rewrite <- Hi. symmetry. apply down_env_compose. }
    split; [reflexivity|].
    pose proof (@lr_results_map n m inner B (down_ty_until B m H) l x δi ρ M
      (fun T => o T↓ T) (fun T => r T↓ T)) as Hmap.
    specialize (Hmap (non_func_down n m B H)).
    assert (Hr : r <= o) by (unfold r; lia).
    assert (Hm : forall T, LR_maybe B (o T↓ T) l x ->
      LR_maybe (down_ty_until B m H) (r T↓ T) l x).
    { intros T HT. unfold down_comp in *. rewrite <- (down_clos_smaller _ T r o Hr). eauto. }
    assert (Hn : forall T, LR_no B (o T↓ T) l x ->
      LR_no (down_ty_until B m H) (r T↓ T) l x).
    { intros T HT. unfold down_comp in *. rewrite <- (down_clos_smaller _ T r o Hr). eauto. }
    destruct (Hmap Hm Hn) as [HM HN].
    unfold LRM in *. split; intros HS; [apply HN; exact (proj1 HC HS) | apply HM; exact (proj2 HC HS)]. }
  { intros C HC. cbn [down_ty_until LR_maybe] in HC.
    destruct HC as (o & inner & δ & δi & ρ & M & Hoi & Hom & Hlo & Hli &
      Hδ & Hi & -> & HC).
    assert (Hon : o <= n) by lia.
    cbn [LR_maybe].
    exists o, inner, δ, δi, ρ, M, Hoi, Hon, Hlo, Hli.
    split; [rewrite <- Hδ; symmetry; apply down_env_compose|].
    split; [exact Hi|]. split; [reflexivity|].
    destruct (@lr_results_map m n inner (down_ty_until B m H) B l x δi ρ M
      (fun T => o T↓ T) (fun T => o T↓ T) (iff_sym (non_func_down n m B H))
      (fun T => liftB (o T↓ T)) (fun T => liftNo (o T↓ T))) as [HM HN].
    unfold LRM in *. split; intros HS; [apply HN; exact (proj1 HC HS) | apply HM; exact (proj2 HC HS)]. }
  { intros C s Hls Hsm (U & V & -> & HU & HV).
    exists (down_clos s U), (down_clos s V). eauto. }
  { intros C (U & V & -> & HU & HV). exists U, V. eauto. }
  { intros C s Hls Hsm (W & [(-> & HW) | (-> & HW)]);
      exists (down_clos s W); [left | right]; eauto. }
  { intros C (W & [(-> & HW) | (-> & HW)]); exists W; [left | right]; eauto. }
  (* Function arguments are clipped before the original body is run. *)
  1,3: (intros C s Hls Hsm HC;
    cbn [LR_maybe LR_no] in HC;
    destruct HC as (o & inner & δ & δi & ρ & M & Hon & Hoi & Hlo & Hli &
      Hi & -> & HC);
    set (r := Nat.min o s);
    assert (Hr : r <= o) by (unfold r; lia);
    assert (Hlr : l <= r) by (unfold r; lia);
    assert (Hrm : r <= m) by (unfold r; lia);
    assert (Hri : r <= inner) by (unfold r; lia);
    cbn [down_ty_until LR_maybe LR_no down_clos];
    exists r, inner, (down_env_until δ r (min_le o s)), δi, ρ, M,
      Hrm, Hri, Hlr, Hli;
    split; [rewrite <- Hi; symmetry; apply down_env_compose |];
    split; [reflexivity |]; intros W HW;
    assert (HW' : LR_maybe A (r W↓ W) l x) by (apply liftA, trimA; auto);
    specialize (HC _ HW');
    unfold down_value in HC; rewrite down_clos_larger in HC by exact Hr;
    assert (HM : forall T, LR_maybe B (o T↓ T) l x ->
      LR_maybe (down_ty_until B m H) (r T↓ T) l x)
      by (intros T HT; unfold down_comp in *;
        rewrite <- (down_clos_smaller _ T r o Hr); eauto);
    assert (HN : forall T, LR_no B (o T↓ T) l x ->
      LR_no (down_ty_until B m H) (r T↓ T) l x)
      by (intros T HT; unfold down_comp in *;
        rewrite <- (down_clos_smaller _ T r o Hr); eauto);
    pose proof (@lr_results_map n m (S inner) B (down_ty_until B m H)
      l x (q .: δi) ((r W↓ W) .: ρ) M (fun T => o T↓ T) (fun T => r T↓ T)
      (non_func_down n m B H) HM HN) as Hmap;
    first [exact (proj1 Hmap HC) | exact (proj2 Hmap HC)]).
  1,2: (intros C HC; cbn [down_ty_until LR_maybe LR_no] in HC;
    destruct HC as (o & inner & δ & δi & ρ & M & Hom & Hoi & Hlo & Hli &
      Hi & -> & HC);
    assert (Hon : o <= n) by lia;
    cbn [LR_maybe LR_no];
    exists o, inner, δ, δi, ρ, M, Hon, Hoi, Hlo, Hli;
    split; [exact Hi |]; split; [reflexivity |]; intros W HW;
    assert (HW' : LR_maybe (down_ty_until A m H) (o W↓ W) l x)
      by (apply trimA; auto);
    specialize (HC _ HW');
    unfold down_value in HC; rewrite down_clos_larger in HC by lia;
    pose proof (@lr_results_map m n (S inner) (down_ty_until B m H) B
      l x (q .: δi) ((o W↓ W) .: ρ) M (fun T => o T↓ T) (fun T => o T↓ T)
      (iff_sym (non_func_down n m B H)) (fun T => liftB _) (fun T => liftNo _)) as Hmap;
    first [exact (proj1 Hmap HC) | exact (proj2 Hmap HC)]).
  { intros C s Hls Hsm (W & -> & HW). exists (down_clos s W). eauto. }
  { intros C (W & -> & HW). exists W. eauto. }
Qed.

Local Lemma lr_maybe_trim n k (A : Ty n k) C m (H : m <= n) l (x : fin l) s :
  l <= s -> s <= m ->
  LR_maybe A C l x -> LR_maybe (down_ty_until A m H) (down_clos s C) l x.
Proof. exact (proj1 (proj1 (lr_scope n k A m H l x)) C s). Qed.

Local Lemma lr_maybe_lift n k (A : Ty n k) C m (H : m <= n) l (x : fin l) :
  LR_maybe (down_ty_until A m H) C l x -> LR_maybe A C l x.
Proof. exact (proj2 (proj1 (lr_scope n k A m H l x)) C). Qed.

Local Lemma lr_maybe_clip n k (A : Ty n k) C l (x : fin l) :
  l <= n -> LR_maybe A C l x -> LR_maybe A (down_clos n C) l x.
Proof.
  intros Hl HC. rewrite <- (down_ty_same n k A (Nat.le_refl n)).
  eauto using lr_maybe_trim.
Qed.

Local Lemma non_func_dec n (B : CompTy n) : non_func B \/ ~ non_func B.
Proof.
  assert (P : forall k (A : Ty n k),
    match k return Ty n k -> Prop with
    | ValFlag => fun _ => True
    | CompFlag => fun B => non_func B \/ ~ non_func B
    end A).
  { destruct A; auto; unfold non_func.
    - right. intros H. eapply H. reflexivity.
    - left. intros ? ? ? E. discriminate. }
  exact (P CompFlag B).
Qed.

Local Lemma lr_no_non_func n (B : CompTy n) T l (x : fin l) :
  LR_no B T l x -> ~ non_func B.
Proof.
  assert (P : forall k (A : Ty n k),
    match k return Ty n k -> Prop with
    | ValFlag => fun _ => True
    | CompFlag => fun B => forall T, LR_no B T l x -> ~ non_func B
    end A).
  { destruct A; auto; cbn [LR_no].
    intros U HU H. eapply H. reflexivity. }
  exact (P CompFlag B T).
Qed.

Local Definition result_lr {n} (B : CompTy n) l (x : fin l) (b : bool) T :=
  if b then LR_no B T l x else LR_maybe B T l x.

Local Definition comp_result {n m} (B : CompTy n) l (x : fin l) b
    (δ : attrs m) (ρ : env m) M (f : ClosComp -> ClosComp) :=
  EvalCompFail ρ M \/ exists T, EvalComp δ ρ M T /\ result_lr B l x b (f T).

Local Lemma strict_comp_result n m B l x (δ : attrs m) ρ M f :
  @strict_result n m B l x δ ρ M f <-> comp_result B l x true δ ρ M f.
Proof.
  split.
  - intros [HF HS]. destruct (non_func_dec n B); [left; auto | apply HS; auto].
  - intros [HF | (T & HE & HT)].
    + split; intros; [exact HF | left; exact HF].
    + split.
      * intros HB. exfalso. exact (lr_no_non_func n B (f T) l x HT HB).
      * intros _. right. exists T. exact (conj HE HT).
Qed.

Local Lemma lr_no_maybe n k (A : Ty n k) :
  forall C l (x : fin l), LR_no A C l x -> LR_maybe A C l x.
Proof.
  induction A; cbn [LR_no]; try contradiction.
  intros C l x (o & m & δ & δi & ρ & M & Hon & Hom & Hlo & Hlm & Hi & -> & HC).
  exists o, m, δ, δi, ρ, M, Hon, Hom, Hlo, Hlm.
  split; [exact Hi|]. split; [reflexivity|].
  intros W HW. specialize (HC W HW).
  apply strict_comp_result in HC.
  destruct HC as [HF | (T & HE & HT)]; [left|right]; eauto.
Qed.

Local Lemma result_lr_trim n (B : CompTy n) T m (H : m <= n) l (x : fin l) s b :
  l <= s -> s <= m ->
  result_lr B l x b T ->
  result_lr (down_ty_until B m H) l x b (down_clos s T).
Proof.
  destruct b; intros; [eapply (proj1 (proj2 (lr_scope n _ B m H l x))) |
    eapply lr_maybe_trim]; eauto.
Qed.

Local Definition missing_env {n} (Γ : context n) (ρ : env n) l (x : fin l)
    (H : l <= n) :=
  ρ (up_fin_until n H x) = Absent /\
  forall j, j <> up_fin_until n H x -> LR_maybe (Γ j) (ρ j) l x.

Local Lemma missing_env_cons n (Γ : context n) (ρ : env n) A W l (x : fin l)
    (H : l <= n) (H' : l <= S n) :
  missing_env Γ ρ l x H -> LR_maybe A W l x ->
  missing_env (ctx_insert A Γ) (W .: ρ) l x H'.
Proof.
  intros [HM HΓ] HW. unfold missing_env. rewrite (up_fin_step _ _ H).
  split; [exact HM|].
  intros [j|] Hne; cbn [ctx_insert scons].
  - eapply (lr_maybe_lift (S n) _ _ _ n (Nat.le_succ_diag_r n)).
    change (LR_maybe (down_ty_until (up_Ty Lazy (Γ j)) n (Nat.le_succ_diag_r n))
      (ρ j) l x).
    rewrite down_ty_lift. apply HΓ. intros ->. apply Hne. reflexivity.
  - eapply (lr_maybe_lift (S n) _ _ _ n (Nat.le_succ_diag_r n)).
    change (LR_maybe (down_ty_until (up_Ty Lazy A) n (Nat.le_succ_diag_r n))
      W l x).
    rewrite down_ty_lift. exact HW.
Qed.

Local Definition is_strict (a : attr) : bool :=
  match a with Strict => true | _ => false end.

Local Definition strict_at {n} (γ : attrs n) l (x : fin l) (H : l <= n) :=
  is_strict (γ (up_fin_until n H x)).

Local Lemma strict_at_add n (γ1 γ2 : attrs n) l (x : fin l) (H : l <= n) :
  strict_at (γ1 γ+ γ2) l x H =
  strict_at γ1 l x H || strict_at γ2 l x H.
Proof. unfold strict_at, attr_vector_add. destruct (γ1 _), (γ2 _); reflexivity. Qed.

Local Lemma strict_at_cons n q (γ : attrs n) l (x : fin l) (H : l <= n) (H' : l <= S n) :
  strict_at (q .: γ) l x H' = strict_at γ l x H.
Proof. unfold strict_at. rewrite (up_fin_step _ _ H). reflexivity. Qed.

Local Lemma strict_at_scoped n m o l (x : fin l) (γ : attrs n) (δ : attrs m)
    (Hln : l <= n) (Hlm : l <= m) (Hlo : l <= o) (Hon : o <= n) (Hom : o <= m) :
  down_env_until γ o Hon = down_env_until δ o Hom ->
  strict_at γ l x Hln = strict_at δ l x Hlm.
Proof.
  intros E. unfold strict_at. f_equal.
  rewrite <- (up_fin_compose _ _ _ Hlo Hon Hln), <- down_env_lookup, E, down_env_lookup.
  apply f_equal, up_fin_compose.
Qed.

Local Lemma lr_absent n (A : ValTy n) l (x : fin l) : ~ LR_maybe A Absent l x.
Proof.
  assert (P : forall k (B : Ty n k),
    match k return Ty n k -> Prop with
    | ValFlag => fun A => ~ LR_maybe A Absent l x
    | CompFlag => fun _ => True
    end B).
  { destruct B; cbn [LR_maybe]; auto.
    - discriminate.
    - intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _ & _ & E & _).
      discriminate.
    - intros (? & ? & E & _). discriminate.
    - intros (? & [(E & _) | (E & _)]); discriminate. }
  exact (P ValFlag A).
Qed.

Local Lemma strict_fin_eqb n (i j : fin n) : fin_eqb i j = true <-> i = j.
Proof.
  revert i j. induction n; intros i j; [destruct i|].
  destruct i as [i|], j as [j|]; simpl;
    try (split; congruence).
  destruct (fin_eqb i j) eqn:E; simpl; split; intros H; try discriminate.
  - f_equal. apply IHn. exact E.
  - reflexivity.
  - injection H as ->. assert (fin_eqb j j = true) by (apply IHn; reflexivity).
    congruence.
Qed.

Local Definition value_result {n} (γ : attrs n) (ρ : env n) V (A : ValTy n)
    l (x : fin l) (H : l <= n) :=
  EvalValFail ρ V \/ (strict_at γ l x H = false /\
    exists W, EvalVal γ ρ V W /\ LR_maybe A W l x).

Local Definition typed_val_property {n} (γ : attrs n) (Γ : context n) V (A : ValTy n) :=
  forall ρ l (x : fin l) (H : l <= n), missing_env Γ ρ l x H ->
  value_result γ ρ V A l x H.

Local Definition typed_comp_property {n} (γ : attrs n) (Γ : context n) M (B : CompTy n) :=
  forall ρ l (x : fin l) (H : l <= n), missing_env Γ ρ l x H ->
  comp_result B l x (strict_at γ l x H) γ ρ M (fun T => T).

Local Lemma comp_result_unwrap n (γ : attrs n) (ρ : env n) M (A : ValTy n) l (x : fin l) b :
  comp_result (CF A) l x b γ ρ M (fun T => T) ->
  EvalCompFail ρ M \/ (b = false /\ exists W, EvalComp γ ρ M (Return W) /\ LR_maybe A W l x).
Proof.
  intros [HF | (T & HE & HT)]; [left; exact HF|].
  destruct b; [contradiction|].
  destruct HT as (W & -> & HW). right. eauto.
Qed.

Local Lemma comp_result_trim n m j (B : CompTy n) (H : m <= n)
    l (x : fin l) b (δ : attrs j) ρ M :
  l <= m ->
  comp_result B l x b δ ρ M (fun T => T) ->
  comp_result (down_ty_until B m H) l x b δ ρ M (fun T => m T↓ T).
Proof.
  intros Hl [HF | (T & HE & HT)]; [left; exact HF|].
  right. exists T. split; [exact HE|].
  eapply result_lr_trim; eauto.
Qed.

Local Lemma closure_result n q (A : ValTy n) B l (x : fin l) b T :
  result_lr (CAbs q A B) l x b T ->
  exists o m δ δi ρ M (Hom : o <= m),
    δ = down_env_until δi o Hom /\ T = Closure o m δ ρ M /\
    forall W, LR_maybe A W l x ->
    comp_result B l x b (q .: δi) ((o W↓ W) .: ρ) M (fun U => o T↓ U).
Proof.
  destruct b; cbn [result_lr LR_maybe LR_no]; intros
    (o & m & δ & δi & ρ & M & Hon & Hom & Hlo & Hlm & Hδ & -> & HC);
    exists o, m, δ, δi, ρ, M, Hom.
  all: split; [symmetry; exact Hδ|]; split; [reflexivity|];
    intros W HW; specialize (HC W HW).
  - apply (proj1 (strict_comp_result n (S m) B l x _ _ _ _)). exact HC.
  - exact HC.
Qed.

Local Ltac contradict_eval :=
  match goal with
  | H : EvalValFail _ _ |- False => eapply H; [|eassumption];
      eauto 8 using attrs_equiv_cons, attrs_equiv_down
  | H : EvalCompFail _ _ |- False => eapply H; [|eassumption];
      eauto 8 using attrs_equiv_cons, attrs_equiv_down
  end.

Local Ltac compare_eval Henv Hwitness HW :=
  lazymatch type of Henv with
  | eq_env_up_to_attrs ?r ?r' =>
    lazymatch type of Hwitness with
    | EvalVal _ r ?V _ =>
        match goal with H : EvalVal _ r' V _ |- _ =>
          pose proof (strict_eval_val_unique _ _ _ _ _ Hwitness _ _ _ Henv H) as HW
        end
    | EvalComp _ r ?M _ =>
        match goal with H : EvalComp _ r' M _ |- _ =>
          pose proof (strict_eval_comp_unique _ _ _ _ _ Hwitness _ _ _ Henv H) as HW
        end
    end
  end.

Local Ltac fail_eval :=
  let HE := fresh "HE" in
  left; intros ? ? ? ? HE; strict_invert HE; contradict_eval.

Local Ltac fail_after Hwitness :=
  let HE := fresh "HE" in let Henv := fresh "Henv" in let HW := fresh "HW" in
  left; intros ? ? ? Henv HE; strict_invert HE;
  compare_eval Henv Hwitness HW; strict_invert HW; contradict_eval.

(* A successful value has a non-strict attribute at the missing index.
   A successful strict computation must satisfy LR_no, which excludes a return. *)
Local Lemma strict_typed :
  forall n (γ : attrs n) (Γ : context n),
  (forall V A, VWt γ Γ V A -> typed_val_property γ Γ V A) /\
  (forall M B, CWt γ Γ M B -> typed_comp_property γ Γ M B).
Proof.
  apply (Wt_mutual
    (fun n γ Γ V A _ => typed_val_property γ Γ V A)
    (fun n γ Γ M B _ => typed_comp_property γ Γ M B)).
  - intros n γ Γ j A -> -> ρ l x H [HM HΓ].
    unfold value_result, strict_at, env_set.
    destruct (fin_eqb j (up_fin_until n H x)) eqn:E.
    + apply strict_fin_eqb in E. subst j.
      left. intros δ W ρ' Henv HE. strict_invert HE.
      specialize (Henv (up_fin_until n H x)). rewrite HM in Henv.
      strict_invert Henv. congruence.
    + assert (Hne : j <> up_fin_until n H x).
      { intros ->. assert (Heq : fin_eqb (up_fin_until n H x) (up_fin_until n H x) = true)
          by (apply strict_fin_eqb; reflexivity). congruence. }
      specialize (HΓ j Hne). right. split; [reflexivity|].
      exists (ρ j). split; [|exact HΓ].
      apply E_Var; try reflexivity.
      intros E'. rewrite E' in HΓ. eapply lr_absent; eassumption.
  - intros n γ Γ -> ρ l x H Henv.
    right. split; [reflexivity|]. exists Unit. split; [constructor|]; reflexivity.
  - intros n γ Γ δ M B Hwt IH -> ρ l x H Henv.
    right. split; [reflexivity|].
    exists (Thunk n n δ ρ M). split; [constructor; reflexivity|].
    exists n, n, δ, δ, ρ, M, (Nat.le_refl n), (Nat.le_refl n), H, H.
    split; [apply down_env_same|]. split; [apply down_env_same|].
    split; [reflexivity|]. unfold LRM.
    specialize (IH ρ l x H Henv).
    pose proof (comp_result_trim n n n B (Nat.le_refl n) l x _
      δ ρ M H IH) as HC.
    rewrite down_ty_same in HC. unfold strict_at in HC.
    rewrite down_env_lookup. split; intros HS.
    + rewrite HS in HC. exact (proj2 (strict_comp_result n n B l x _ _ _ _) HC).
    + destruct (δ (up_fin_until n H x)); [exact HC | contradiction | exact HC].
  - intros n γ Γ γ1 γ2 V1 V2 A1 A2 H1 IH1 H2 IH2 -> ρ l x H Henv.
    destruct (IH1 ρ l x H Henv) as [HF | (HS1 & W1 & HE1 & HW1)]; [fail_eval|].
    destruct (IH2 ρ l x H Henv) as [HF | (HS2 & W2 & HE2 & HW2)]; [fail_eval|].
    right. split; [rewrite strict_at_add, HS1, HS2; reflexivity|].
    exists (Pair W1 W2). split; [eapply E_VPair; eauto|].
    exists W1, W2. auto.
  - intros n γ Γ V A1 A2 Hwt IH ρ l x H Henv.
    destruct (IH ρ l x H Henv) as [HF | (HS & W & HE & HW)]; [fail_eval|].
    right. split; [exact HS|]. exists (Inl W). split; [constructor; exact HE|].
    exists W. auto.
  - intros n γ Γ V A1 A2 Hwt IH ρ l x H Henv.
    destruct (IH ρ l x H Henv) as [HF | (HS & W & HE & HW)]; [fail_eval|].
    right. split; [exact HS|]. exists (Inr W). split; [constructor; exact HE|].
    exists W. auto.
  - intros n γ Γ V A Hwt IH ρ l x H Henv.
    destruct (IH ρ l x H Henv) as [HF | (HS & W & HE & HW)]; [fail_eval|].
    right. exists (Return W). split; [constructor; exact HE|].
    rewrite HS. cbn [result_lr LR_maybe]. eauto.
  - intros n γ Γ q M N A B B' γ1 γ2 HM IHM HN IHN -> -> ρ l x H Henv.
    destruct (comp_result_unwrap _ _ _ _ _ _ _ _ (IHM ρ l x H Henv))
      as [HF | (HS & W & HE & HW)]; [fail_eval|].
    assert (H' : l <= S n) by lia.
    specialize (IHN (W .: ρ) l x H' (missing_env_cons _ _ _ _ _ _ _ _ _ Henv HW)).
    destruct IHN as [HF | (T & HET & HT)]; [fail_after HE|].
    right. exists (n T↓ T). split; [eapply E_LetRet; eauto|].
    rewrite strict_at_add, HS. simpl.
    rewrite (strict_at_cons _ _ _ _ _ H) in HT.
    eapply result_lr_trim; eauto.
  - intros n γ Γ V B γ1 γ2 HV IHV -> ρ l x H Henv.
    destruct (IHV ρ l x H Henv) as [HF | (HS & W & HE & HW)]; [fail_eval|].
    destruct HW as (o & m & δ & δi & ρi & M & Hom & Hon & Hlo & Hlm &
      Hδ & Hδi & -> & HC).
    assert (HS' : strict_at γ2 l x H = strict_at δi l x Hlm).
    { apply (strict_at_scoped n m o l x γ2 δi H Hlm Hlo Hon Hom).
      congruence. }
    assert (HR : comp_result B l x (strict_at δi l x Hlm) δi ρi M
      (fun T => o T↓ T)).
    { unfold LRM in HC. rewrite down_env_lookup in HC. unfold strict_at.
      destruct (δi (up_fin_until m Hlm x)).
      - exact (proj2 HC ltac:(discriminate)).
      - apply (proj1 (strict_comp_result n m B l x _ _ _ _)).
        exact (proj1 HC eq_refl).
      - exact (proj2 HC ltac:(discriminate)). }
    destruct HR as [HF | (T & HET & HT)]; [fail_after HE|].
    right. exists (o T↓ T). split.
    + eapply E_Force with (γ2'' := γ2) (Hn := Hon) (HInner := Hom); eauto.
    + rewrite strict_at_add, HS, HS'. exact HT.
  - intros n γ Γ V M B γ1 γ2 HV IHV HM IHM -> ρ l x H Henv.
    destruct (IHV ρ l x H Henv) as [HF | (HS & W & HE & HW)]; [fail_eval|].
    change (W = Unit) in HW. subst W.
    destruct (IHM ρ l x H Henv) as [HF | (T & HET & HT)]; [fail_eval|].
    right. exists T. split; [eapply E_Seq; eauto|].
    rewrite strict_at_add, HS. exact HT.
  - intros n γ Γ q1 q2 V M γ1 γ2 A1 A2 B B' HV IHV HM IHM -> -> ρ l x H Henv.
    destruct (IHV ρ l x H Henv) as [HF | (HS & W & HE & HW)]; [fail_eval|].
    destruct HW as (W1 & W2 & -> & HW1 & HW2).
    assert (H' : l <= S n) by lia. assert (H'' : l <= S (S n)) by lia.
    assert (HW1' : LR_maybe (Lazy A↑ A1) W1 l x).
    { eapply (lr_maybe_lift (S n) _ _ _ n (Nat.le_succ_diag_r n)).
      change (LR_maybe (down_ty_until (up_Ty Lazy A1) n (Nat.le_succ_diag_r n))
        W1 l x). rewrite down_ty_lift. exact HW1. }
    assert (Henv' : missing_env (ctx_insert A2 Γ) (W2 .: ρ) l x H')
      by (eapply missing_env_cons; eassumption).
    assert (Henv'' : missing_env (ctx_insert (Lazy A↑ A1) (ctx_insert A2 Γ))
      (W1 .: (W2 .: ρ)) l x H'') by (eapply missing_env_cons; eassumption).
    destruct (IHM _ l x H'' Henv'') as [HF | (T & HET & HT)]; [fail_after HE|].
    right. exists (n T↓ T). split; [eapply E_Split; eauto|].
    rewrite strict_at_add, HS. simpl.
    rewrite (strict_at_cons _ _ _ _ _ H'), (strict_at_cons _ _ _ _ _ H) in HT.
    eapply result_lr_trim; eauto.
  - intros n γ Γ q1 q2 V M1 M2 γ1 γ2 A1 A2 B B1 B2
      HV IHV HM1 IHM1 HM2 IHM2 -> EB1 EB2 ρ l x H Henv.
    destruct (IHV ρ l x H Henv) as [HF | (HS & W & HE & HW)]; [fail_eval|].
    assert (H' : l <= S n) by lia.
    destruct HW as (U & [(-> & HU) | (-> & HU)]).
    + assert (Henv' : missing_env (ctx_insert A1 Γ) (U .: ρ) l x H')
        by (eapply missing_env_cons; eassumption).
      destruct (IHM1 _ l x H' Henv') as [HF | (T & HET & HT)]; [fail_after HE|].
      right. exists (n T↓ T). split; [eapply E_Casel; eauto|].
      rewrite EB1, strict_at_add, HS. simpl.
      rewrite (strict_at_cons _ _ _ _ _ H) in HT.
      eapply result_lr_trim; eauto.
    + assert (Henv' : missing_env (ctx_insert A2 Γ) (U .: ρ) l x H')
        by (eapply missing_env_cons; eassumption).
      destruct (IHM2 _ l x H' Henv') as [HF | (T & HET & HT)]; [fail_after HE|].
      right. exists (n T↓ T). split; [eapply E_Caser; eauto|].
      rewrite EB2, strict_at_add, HS. simpl.
      rewrite (strict_at_cons _ _ _ _ _ H) in HT.
      eapply result_lr_trim; eauto.
  - intros n γ Γ q M A B B' HM IHM -> ρ l x H Henv.
    right. exists (Closure n n γ ρ M). split; [constructor|].
    assert (H' : l <= S n) by lia.
    destruct (strict_at γ l x H) eqn:HS; cbn [result_lr LR_maybe LR_no].
    all: exists n, n, γ, γ, ρ, M, (Nat.le_refl n), (Nat.le_refl n), H, H.
    all: split; [apply down_env_same|]; split; [reflexivity|]; intros W HW.
    all: assert (HW' : LR_maybe A (n W↓ W) l x) by (apply lr_maybe_clip; auto).
    all: specialize (IHM _ l x H' (missing_env_cons _ _ _ _ _ _ _ _ _ Henv HW')).
    all: pose proof (comp_result_trim (S n) n (S n) B' (Nat.le_succ_diag_r n)
      l x _ _ _ _ H IHM) as HC;
      rewrite (strict_at_cons _ _ _ _ _ H), HS in HC.
    + exact (proj2 (strict_comp_result n (S n) _ l x _ _ _ _) HC).
    + exact HC.
  - intros n γ Γ M q V γ1 γ2 A B HM IHM HV IHV -> ρ l x H Henv.
    destruct (IHM ρ l x H Henv) as [HF | (F & HEF & HF)]; [fail_eval|].
    destruct (IHV ρ l x H Henv) as [HVF | (HS & W & HEW & HW)]; [fail_eval|].
    destruct (closure_result _ _ _ _ _ _ _ _ HF) as
      (o & m & δ & δi & ρi & Mi & Hom & Hδ & -> & HC).
    destruct (HC W HW) as [HFail | (T & HET & HT)].
    + left. intros δe T ρe Henv' HE. strict_invert HE.
      compare_eval Henv' HEF HFC. strict_invert HFC.
      compare_eval Henv' HEW HWC. unfold down_value in *.
      contradict_eval.
    + right. exists (o T↓ T). split.
      * eapply E_AppAbs; eauto.
      * rewrite strict_at_add, HS, orb_false_r. exact HT.
  - intros n γ Γ M δ B HM IHM Hle ρ l x H Henv.
    destruct (IHM ρ l x H Henv) as [HF | (T & HE & HT)]; [fail_eval|].
    right. exists T. split; [eapply E_CSub; eauto|].
    specialize (Hle (up_fin_until n H x)). unfold strict_at in *.
    destruct (γ (up_fin_until n H x)), (δ (up_fin_until n H x));
      cbn [is_strict result_lr attr_le] in *; try contradiction;
      eauto using lr_no_maybe.
Qed.

Theorem strict_explosion : forall n (γ : attrs n) (Γ : context n) (ρ : env n) i,
  ρ_not_ok γ ρ Γ n i ltac:(auto) ->
  (forall V A, VWt γ Γ V A -> EvalValFail ρ V) /\
  (forall M A, CWt γ Γ M (CF A) -> EvalCompFail ρ M).
Proof.
  intros n γ Γ ρ i (HS & HM & HΓ).
  rewrite down_env_lookup in HS. rewrite down_env_lookup in HM.
  destruct (strict_typed n γ Γ) as [HV HC].
  split.
  - intros V A Hwt.
    destruct (HV V A Hwt ρ n i _ (conj HM HΓ)) as [HF | (Hb & _)].
    + exact HF.
    + unfold strict_at in Hb. rewrite HS in Hb. discriminate.
  - intros M A Hwt.
    destruct (HC M (CF A) Hwt ρ n i _ (conj HM HΓ)) as [HF | (T & _ & HT)].
    + exact HF.
    + unfold strict_at in HT. rewrite HS in HT. contradiction.
Qed.
