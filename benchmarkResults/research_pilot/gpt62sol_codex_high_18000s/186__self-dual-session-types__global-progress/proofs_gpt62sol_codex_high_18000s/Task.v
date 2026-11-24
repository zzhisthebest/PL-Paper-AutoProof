From diris.lambdabar Require Import definitions.
From Stdlib Require Import Lia Logic.Eqdep_dec.

(* A barrier has two endpoints with opposite input and output types. *)
Definition endpoint := (nat * bool)%type.
Definition footprint := gset endpoint.
Definition protocol := nat -> (type * type)%type.

Definition endpoint_type (P : protocol) n (b : bool) :=
  let '(a,c) := P n in
  if b then FunT Lin c a else FunT Lin a c.

Definition fp_split (R A B : footprint) := R = A ∪ B ∧ A ## B.

(* In a runtime value all ordinary variables are bound. The footprint
   accounts for the linear endpoints captured by that value. *)
Inductive runtime_typed (P : protocol) : env -> footprint -> expr -> type -> Prop :=
  | RT_var G x t :
      env_var G x t -> runtime_typed P G ∅ (Var x) t
  | RT_fun G G' R x e a b l :
      env_bind G' x a G ->
      (l = Unr -> env_unr G ∧ R = ∅) ->
      runtime_typed P G' R e b ->
      runtime_typed P G R (Fun x e) (FunT l a b)
  | RT_funv G R x e a b l :
      env_unr G -> (l = Unr -> R = ∅) ->
      runtime_typed P {[x := a]} R e b ->
      runtime_typed P G R (Val (FunV x e)) (FunT l a b)
  | RT_app G G1 G2 R R1 R2 e1 e2 a b l :
      env_split G G1 G2 -> fp_split R R1 R2 ->
      runtime_typed P G1 R1 e1 (FunT l a b) -> runtime_typed P G2 R2 e2 a ->
      runtime_typed P G R (App e1 e2) b
  | RT_unit G :
      env_unr G -> runtime_typed P G ∅ Unit UnitT
  | RT_unitv G :
      env_unr G -> runtime_typed P G ∅ (Val UnitV) UnitT
  | RT_pair G G1 G2 R R1 R2 e1 e2 a b :
      env_split G G1 G2 -> fp_split R R1 R2 ->
      runtime_typed P G1 R1 e1 a -> runtime_typed P G2 R2 e2 b ->
      runtime_typed P G R (Pair e1 e2) (PairT a b)
  | RT_pairv G R R1 R2 v1 v2 a b :
      env_unr G -> fp_split R R1 R2 ->
      runtime_typed P ∅ R1 (Val v1) a -> runtime_typed P ∅ R2 (Val v2) b ->
      runtime_typed P G R (Val (PairV v1 v2)) (PairT a b)
  | RT_letpair G G1 G2 R R1 R2 e1 e2 a b t :
      env_split G G1 G2 -> fp_split R R1 R2 ->
      runtime_typed P G1 R1 e1 (PairT a b) ->
      runtime_typed P G2 R2 e2 (FunT Lin a (FunT Lin b t)) ->
      runtime_typed P G R (LetPair e1 e2) t
  | RT_sum G R n (ts : fin n -> type) i e :
      runtime_typed P G R e (ts i) -> runtime_typed P G R (Sum i e) (SumT n ts)
  | RT_sumv G R n (ts : fin n -> type) i v :
      env_unr G -> runtime_typed P ∅ R (Val v) (ts i) ->
      runtime_typed P G R (Val (SumV i v)) (SumT n ts)
  | RT_match G G1 G2 R R1 R2 n (ts : fin n -> type) es e t :
      env_split G G1 G2 -> fp_split R R1 R2 ->
      (n = 0 -> env_unr G2 ∧ R2 = ∅) ->
      runtime_typed P G1 R1 e (SumT n ts) ->
      (∀ i, runtime_typed P G2 R2 (es i) (FunT Lin (ts i) t)) ->
      runtime_typed P G R (MatchSum n e es) t
  | RT_fork G R e a b :
      runtime_typed P G R e (FunT Lin (FunT Lin b a) UnitT) ->
      runtime_typed P G R (Fork e) (FunT Lin a b)
  | RT_endpoint G n b :
      env_unr G ->
      runtime_typed P G ({[(n,b)]} : footprint) (Val (BarrierV n)) (endpoint_type P n b).

Lemma source_runtime P G e t :
  typed G e t -> runtime_typed P G ∅ e t.
Proof.
  induction 1; try solve [econstructor; eauto; unfold fp_split; set_solver].
Qed.

Lemma env_unr_empty : env_unr ∅.
Proof. unfold env_unr. intros x t H. simplify_map_eq. Qed.

Lemma env_unr_delete G x : env_unr G -> env_unr (delete x G).
Proof. intros H y t Hy. apply lookup_delete_Some in Hy. naive_solver. Qed.

Lemma env_split_empty G1 G2 :
  env_split ∅ G1 G2 -> G1 = ∅ ∧ G2 = ∅.
Proof.
  intros [H _]. unfold env in *. split; apply map_empty; intros x;
    apply (proj1 (lookup_union_None G1 G2 x)); rewrite <- H; apply lookup_empty.
Qed.

Lemma empty_env_split : env_split ∅ ∅ ∅.
Proof. split; [reflexivity|]. intros x a b H. simplify_map_eq. Qed.

Lemma env_split_delete G G1 G2 x :
  env_split G G1 G2 -> env_split (delete x G) (delete x G1) (delete x G2).
Proof.
  intros [-> Hd]. unfold env_split, disj, env in *. split.
  - apply map_eq. intros y. destruct (decide (x = y)) as [->|Hxy].
    + by rewrite !lookup_delete_eq, lookup_union, !lookup_delete_eq.
    + by rewrite lookup_delete_ne, !lookup_union, !lookup_delete_ne.
  - intros y a b H1 H2. apply lookup_delete_Some in H1, H2. naive_solver.
Qed.

Lemma fp_split_left R : fp_split R R ∅.
Proof. unfold fp_split. set_solver. Qed.

Lemma fp_split_right R : fp_split R ∅ R.
Proof. unfold fp_split. set_solver. Qed.

Lemma value_retype_env P G D R v t :
  runtime_typed P G R (Val v) t -> env_unr D -> runtime_typed P D R (Val v) t.
Proof.
  intros H HD. inversion H; subst;
    eauto using RT_funv, RT_unitv, RT_pairv, RT_sumv, RT_endpoint.
Qed.

Lemma unrestricted_value P G R e t :
  runtime_typed P G R e t ->
  (∃ v, e = Val v) -> unr t -> R = ∅.
Proof.
  induction 1; intros [w Hw] Hu; try discriminate; inversion Hw; subst.
  - inversion Hu; subst. auto.
  - reflexivity.
  - inversion Hu; subst. destruct H0 as [-> _].
    erewrite IHruntime_typed1, IHruntime_typed2; eauto.
  - inversion Hu; subst. apply (inj_pair2_eq_dec _ Nat.eq_dec) in H3. subst ts1.
    eapply IHruntime_typed; eauto.
  - unfold endpoint_type in Hu. destruct (P n) as [a c]. destruct b; inversion Hu.
Qed.

Definition supplies P (G : env) x a (S : footprint) v :=
  (G !! x = Some a ∧ runtime_typed P ∅ S (Val v) a) ∨
  (G !! x = None ∧ S = ∅).

Lemma supplies_empty P G x a S v :
  supplies P G x a S v ->
  (∀ t, G !! x = Some t -> unr t) -> S = ∅.
Proof.
  intros [[Hx Hv]|[_ ->]] Hun; [|reflexivity].
  eapply unrestricted_value; eauto.
Qed.

Lemma supplies_split P G G1 G2 x a S v :
  env_split G G1 G2 -> supplies P G x a S v ->
  ∃ S1 S2, fp_split S S1 S2 ∧
    supplies P G1 x a S1 v ∧ supplies P G2 x a S2 v.
Proof.
  intros [-> Hd] Hs.
  unfold supplies, env in *. rewrite lookup_union in Hs.
  destruct (G1 !! x) as [a1|] eqn:H1, (G2 !! x) as [a2|] eqn:H2; simpl in Hs.
  - destruct Hs as [[[= <-] Hv]|[H _]]; [|discriminate].
    destruct (Hd _ _ _ H1 H2) as [<- Hu].
    assert (S = ∅) as -> by (eapply unrestricted_value; eauto).
    exists ∅, ∅. split; [apply fp_split_left|auto].
  - destruct Hs as [[[= <-] Hv]|[H _]]; [|discriminate].
    exists S, ∅. split; [apply fp_split_left|auto].
  - destruct Hs as [[[= <-] Hv]|[H _]]; [|discriminate].
    exists ∅, S. split; [apply fp_split_right|auto].
  - destruct Hs as [[H _]|[_ ->]]; [discriminate|].
    exists ∅, ∅. split; [apply fp_split_left|auto].
Qed.

Lemma fp_split_add R R1 R2 S S1 S2 :
  fp_split R R1 R2 -> fp_split S S1 S2 -> R ## S ->
  fp_split (R ∪ S) (R1 ∪ S1) (R2 ∪ S2).
Proof. unfold fp_split. set_solver. Qed.

Lemma runtime_subst P G R e t :
  runtime_typed P G R e t ->
  ∀ x v a S, supplies P G x a S v -> R ## S ->
    runtime_typed P (delete x G) (R ∪ S) (subst x v e) t.
Proof.
  induction 1 as
    [G y t Hvar
    |G G' R y e a b l Hbind Hun He IH
    |G R y e a b l HG Hun He IH
    |G G1 G2 R R1 R2 e1 e2 a b l HG HR H1 IH1 H2 IH2
    |G HG
    |G HG
    |G G1 G2 R R1 R2 e1 e2 a b HG HR H1 IH1 H2 IH2
    |G R R1 R2 v1 v2 a b HG HR H1 IH1 H2 IH2
    |G G1 G2 R R1 R2 e1 e2 a b t HG HR H1 IH1 H2 IH2
    |G R n ts i e He IH
    |G R n ts i w HG Hw IH
    |G G1 G2 R R1 R2 n ts es e t HG HR Hzero He IH1 Hes IH2
    |G R e a b He IH
    |G n side HG];
    intros x v u S Hs Hd; simpl.
  - destruct Hvar as [D [-> HD]].
    unfold supplies, env in *.
    case_decide as Hxy.
    + subst y. destruct Hs as [[Hx Hv]|[Hx _]]; [|simplify_map_eq].
      assert (u = t) as -> by (simplify_map_eq; congruence).
      replace (∅ ∪ S) with S by set_solver.
      replace (delete x (<[x:=t]> D)) with (delete x D).
      2:{ apply map_eq. intros z. destruct (decide (x = z)) as [->|Hne].
          - by rewrite !lookup_delete_eq.
          - by rewrite !lookup_delete_ne, lookup_insert_ne. }
      eapply value_retype_env; eauto using env_unr_delete.
    + assert (S = ∅) as ->.
      { eapply supplies_empty; [exact Hs|].
        intros z Hz. rewrite (lookup_insert_ne D) in Hz by congruence. eauto. }
      rewrite (delete_insert_ne D) by done.
      apply RT_var. exists (delete x D). eauto using env_unr_delete.
  - destruct Hbind as [-> Hshadow].
    case_decide as Hxy.
    + subst y. assert (S = ∅) as -> by (eapply supplies_empty; eauto).
      replace (R ∪ ∅) with R by set_solver.
      eapply RT_fun; [| |exact He].
      * unfold env_bind, env in *. split.
        -- rewrite (insert_delete G). by case_decide.
        -- intros t Ht. simplify_map_eq.
      * intros Hl. destruct (Hun Hl). eauto using env_unr_delete.
    + eapply RT_fun.
      * unfold env_bind, env in *. split.
        -- apply delete_insert_ne. done.
        -- intros t Ht. apply lookup_delete_Some in Ht. naive_solver.
      * intros Hl. destruct (Hun Hl) as [HG ->].
        assert (S = ∅) as -> by (eapply supplies_empty; eauto).
        split; [apply env_unr_delete; done|set_solver].
      * eapply IH; [|exact Hd].
        unfold supplies, env in *. by rewrite (lookup_insert_ne G) by congruence.
  - assert (S = ∅) as -> by (eapply supplies_empty; eauto).
    replace (R ∪ ∅) with R by set_solver.
    eapply value_retype_env; eauto using RT_funv, env_unr_delete.
  - destruct (supplies_split _ _ _ _ _ _ _ _ HG Hs) as (S1 & S2 & HS & Hs1 & Hs2).
    eapply RT_app; [apply env_split_delete; done|eapply fp_split_add; eauto| |].
    + eapply IH1; eauto. unfold fp_split in *. set_solver.
    + eapply IH2; eauto. unfold fp_split in *. set_solver.
  - assert (S = ∅) as -> by (eapply supplies_empty; eauto).
    apply RT_unit. eauto using env_unr_delete.
  - assert (S = ∅) as -> by (eapply supplies_empty; eauto).
    apply RT_unitv. eauto using env_unr_delete.
  - destruct (supplies_split _ _ _ _ _ _ _ _ HG Hs) as (S1 & S2 & HS & Hs1 & Hs2).
    eapply RT_pair; [apply env_split_delete; done|eapply fp_split_add; eauto| |].
    + eapply IH1; eauto. unfold fp_split in *. set_solver.
    + eapply IH2; eauto. unfold fp_split in *. set_solver.
  - assert (S = ∅) as -> by (eapply supplies_empty; eauto).
    replace (R ∪ ∅) with R by set_solver.
    eapply RT_pairv; eauto using env_unr_delete.
  - destruct (supplies_split _ _ _ _ _ _ _ _ HG Hs) as (S1 & S2 & HS & Hs1 & Hs2).
    eapply RT_letpair; [apply env_split_delete; done|eapply fp_split_add; eauto| |].
    + eapply IH1; eauto. unfold fp_split in *. set_solver.
    + eapply IH2; eauto. unfold fp_split in *. set_solver.
  - eapply RT_sum. eauto.
  - assert (S = ∅) as -> by (eapply supplies_empty; eauto).
    replace (R ∪ ∅) with R by set_solver.
    eapply RT_sumv; eauto using env_unr_delete.
  - destruct (supplies_split _ _ _ _ _ _ _ _ HG Hs) as (S1 & S2 & HS & Hs1 & Hs2).
    eapply RT_match; [apply env_split_delete; done|eapply fp_split_add; eauto| | |].
    + intros Hn. destruct (Hzero Hn) as [HG2 ->].
      assert (S2 = ∅) as -> by (eapply supplies_empty; eauto).
      split; [eauto using env_unr_delete|set_solver].
    + eapply IH1; eauto. unfold fp_split in *. set_solver.
    + intros i. unfold compose. eapply IH2; eauto.
      unfold fp_split in *. set_solver.
  - eapply RT_fork. eauto.
  - assert (S = ∅) as -> by (eapply supplies_empty; eauto).
    replace (({[(n,side)]} : footprint) ∪ ∅) with ({[(n,side)]} : footprint) by set_solver.
    apply RT_endpoint. eauto using env_unr_delete.
Qed.

Local Ltac equal_fin_indices :=
  repeat match goal with
  | H : existT (P:=?F) ?n _ = existT ?n _ |- _ =>
      apply (inj_pair2_eq_dec _ Nat.eq_dec) in H; subst
  end.

Local Ltac empty_splits :=
  repeat match goal with
  | H : env_split ∅ _ _ |- _ =>
      destruct (env_split_empty _ _ H); clear H; subst
  end.

Lemma runtime_sum_payload P G R v n (ts : fin n -> type) (i : fin n) :
  runtime_typed P G R (Val (SumV i v)) (SumT n ts) ->
  runtime_typed P ∅ R (Val v) (ts i).
Proof.
  intros H. remember (Val (SumV i v)) as w eqn:Hw.
  remember (SumT n ts) as t eqn:Ht.
  destruct H; try discriminate Hw; try discriminate Ht.
  - injection Hw as Hi <-.
    assert (n0 = n) by (injection Ht; auto). subst n0.
    assert (ts0 = ts) by (injection Ht; intros Hsig; apply (inj_pair2_eq_dec _ Nat.eq_dec) in Hsig; auto).
    subst ts0. apply (inj fin_to_nat) in Hi. subst. assumption.
Qed.

Lemma fp_split_letpair R L F A B :
  fp_split R L F -> fp_split L A B ->
  fp_split R (F ∪ A) B ∧ fp_split (F ∪ A) F A.
Proof. unfold fp_split. set_solver. Qed.

Lemma runtime_pure P R e e' t :
  pure_step e e' -> runtime_typed P ∅ R e t -> runtime_typed P ∅ R e' t.
Proof.
  intros H. revert R t. induction H; intros R t Ht; inversion Ht; subst; clear Ht;
    empty_splits; equal_fin_indices.
  - match goal with H : env_bind ?G x ?a ∅ |- _ => destruct H as [-> _] end.
    eapply RT_funv; eauto using env_unr_empty. intros Hl. exact (proj2 (H4 Hl)).
  - match goal with
    | H : runtime_typed P ∅ _ (Val (FunV _ _)) _ |- _ =>
        inversion H; subst; clear H
    end.
    destruct H2 as [-> Hd].
    pose proof (runtime_subst _ _ _ _ _ H11 x a a0 R2) as Hsub.
    assert (delete x ({[x:=a0]} : env) = ∅) as Hd0.
    { unfold env. rewrite delete_singleton. by case_decide. }
    rewrite Hd0 in Hsub. apply Hsub; [left; split; [apply lookup_singleton_eq|assumption]|done].
  - apply RT_unitv. apply env_unr_empty.
  - eapply RT_pairv; eauto using env_unr_empty.
  - match goal with
    | H : runtime_typed P ∅ _ (Val (PairV _ _)) _ |- _ =>
        inversion H; subst; clear H
    end.
    match goal with
    | Hf : runtime_typed P ∅ ?F e _,
      Hv1 : runtime_typed P ∅ ?A (Val v1) _,
      Hv2 : runtime_typed P ∅ ?B (Val v2) _,
      HR : fp_split R ?L ?F, HL : fp_split ?L ?A ?B |- _ =>
        let Hsplit := fresh in
        destruct (fp_split_letpair _ _ _ _ _ HR HL) as [Hsplit Hinner];
        eapply RT_app;
          [apply empty_env_split|exact Hsplit| |exact Hv2];
        eapply RT_app; [apply empty_env_split|exact Hinner|exact Hf|exact Hv1]
    end.
  - eapply RT_sumv; eauto using env_unr_empty.
  - eapply RT_app with (R1:=R2) (R2:=R1);
      [apply empty_env_split| |apply H9|eapply runtime_sum_payload; exact H8].
    unfold fp_split in *. clear - H3. set_solver.
Qed.

Lemma runtime_protocol P Q G R e t :
  runtime_typed P G R e t ->
  (∀ n b, (n,b) ∈ R -> P n = Q n) ->
  runtime_typed Q G R e t.
Proof.
  induction 1; intros Hag; try solve [econstructor; eauto].
  all: try solve [
    first [eapply RT_app with (R1:=R1) (R2:=R2)
          |eapply RT_pair with (R1:=R1) (R2:=R2)
          |eapply RT_pairv with (R1:=R1) (R2:=R2)
          |eapply RT_letpair with (R1:=R1) (R2:=R2)
          |eapply RT_match with (R1:=R1) (R2:=R2) (ts:=ts)];
    try eassumption;
    first [apply IHruntime_typed1 | apply IHruntime_typed2 |
           apply IHruntime_typed | intros i; apply H4];
    intros m s Hm; apply (Hag m s); unfold fp_split in *; set_solver ].
  all: try solve [unfold endpoint_type at 1; rewrite (Hag n b) by set_solver;
                  fold (endpoint_type Q n b); eapply RT_endpoint; eauto].
Qed.

(* The context can be reused after a protocol update that agrees on
   every endpoint outside the hole. *)
Definition typed_hole P k e R t :=
  ∃ A F u, fp_split R A F ∧ runtime_typed P ∅ A e u ∧
    ∀ Q B e', (∀ n b, (n,b) ∈ F -> P n = Q n) ->
      F ## B -> runtime_typed Q ∅ B e' u ->
      runtime_typed Q ∅ (B ∪ F) (k e') t.

Lemma runtime_context1 P k :
  ctx1 k -> ∀ e R t, runtime_typed P ∅ R (k e) t -> typed_hole P k e R t.
Proof.
  intros Hk. destruct Hk; intros y R t Ht; simpl in *;
    inversion Ht; subst; clear Ht; empty_splits; equal_fin_indices.
  all: lazymatch goal with |- typed_hole ?P ?k ?y ?R ?t =>
    unfold typed_hole;
    first [
      match goal with
      | Hs : fp_split R ?A ?F, H : runtime_typed P ∅ ?A y ?u |- _ =>
          exists A, F, u; split; [exact Hs|split; [exact H|]]
      | Hs : fp_split R ?F ?A, H : runtime_typed P ∅ ?A y ?u |- _ =>
          exists A, F, u; split; [unfold fp_split in *; set_solver|split; [exact H|]]
      end
    | match goal with
      | H : runtime_typed P ∅ R y ?u |- _ =>
          exists R, (∅ : footprint), u; split; [apply fp_split_left|split; [exact H|]]
      end ];
    intros Q B z Hag Hd Hz; cbn
  end.
  all: try solve [
      replace (B ∪ ∅) with B by set_solver;
      first [eapply RT_sum | eapply RT_fork]; exact Hz
    | first
      [ eapply RT_app
      | eapply RT_pair
      | eapply RT_letpair
      | eapply RT_match ];
      [apply empty_env_split|shelve|..];
      try solve [exact Hz | intros ?; eassumption |
        apply runtime_protocol with (P:=P); [eassumption|exact Hag] |
        intros ?; apply runtime_protocol with (P:=P); [eauto|exact Hag]] ].
  all: try solve [
    eapply RT_match with (ts:=ts) (R1:=B) (R2:=R2);
      [apply empty_env_split|shelve|exact H6|exact Hz|];
    intros i; eapply runtime_protocol; [exact (H9 i)|exact Hag] ].
  Unshelve. all: clear - Hd; unfold fp_split; set_solver.
Qed.

Lemma runtime_context P k :
  ctx k -> ∀ e R t, runtime_typed P ∅ R (k e) t -> typed_hole P k e R t.
Proof.
  induction 1 as [|k1 k2 H1 H2 IH]; intros e R t Ht.
  - exists R, ∅, t. split; [apply fp_split_left|]. split; [exact Ht|].
    intros Q B e' _ _ He'. replace (B ∪ ∅) with B by set_solver. exact He'.
  - destruct (runtime_context1 _ _ H1 _ _ _ Ht) as (A & F & u & HR & Ha & Hplug).
    destruct (IH _ _ _ Ha) as (B & D & w & HA & Hb & Hfill).
    exists B, (D ∪ F), w. split; [clear - HR HA; unfold fp_split in *; set_solver|].
    split; [exact Hb|]. intros Q S e' Hag Hd He'.
    replace (S ∪ (D ∪ F)) with ((S ∪ D) ∪ F) by (clear; set_solver).
    apply Hplug.
    + intros n b Hnb. apply (Hag n b). clear - Hnb. set_solver.
    + clear - HR HA Hd. unfold fp_split in *. set_solver.
    + apply Hfill; [intros n b Hnb; apply (Hag n b); clear - Hnb; set_solver|clear - Hd; set_solver|exact He'].
Qed.

Definition owners := endpoint -> nat.
(* Every nonempty set of vertices spans fewer edges than vertices. *)
Definition session_forest (B : gset nat) (O : owners) :=
  ∀ (E V : gset nat), E ⊆ B ->
    (∀ n b, n ∈ E -> O (n,b) ∈ V) ->
    V ≠ ∅ -> size E < size V.

Lemma forest_weaken B B' O O' :
  session_forest B O -> B' ⊆ B ->
  (∀ n b, n ∈ B' -> O' (n,b) = O (n,b)) ->
  session_forest B' O'.
Proof.
  intros HF HB HO E V HE HV Hne. apply (HF E V); [set_solver| |done].
  intros n b Hn. rewrite <- HO by set_solver. auto.
Qed.

Definition collapse (i j k : nat) := if decide (k = j) then i else k.
Definition collapse_owners i j (O : owners) : owners := collapse i j ∘ O.

Lemma size_add_vertex k (V : gset nat) :
  k ∉ V -> size ({[k]} ∪ V) = S (size V).
Proof.
  intros Hk. rewrite size_union, size_singleton; [lia|set_solver].
Qed.

Lemma size_remove_vertex k (V : gset nat) :
  k ∈ V -> size V = S (size (V ∖ {[k]})).
Proof.
  intros Hk. rewrite <- (size_add_vertex k (V ∖ {[k]})) by set_solver.
  assert (V = {[k]} ∪ (V ∖ {[k]})) as HV by (apply set_eq; intros x; destruct (decide (x = k)) as [->|Hne]; set_solver).
  exact (f_equal (size : gset nat -> nat) HV).
Qed.

Lemma forest_uncollapse B O i j :
  session_forest B (collapse_owners i j O) -> session_forest B O.
Proof.
  intros HF E V HE HV Hne. unfold collapse_owners, compose, collapse in HF.
  destruct (decide (j ∈ V)) as [Hj|Hj].
  - set (V' := {[i]} ∪ (V ∖ {[j]})).
    assert (size E < size V') as Hlt.
    { apply HF; [exact HE| |unfold V'; set_solver].
      intros n b Hn. specialize (HV n b Hn).
      unfold V'. case_decide; set_solver. }
    assert (size V' ≤ size V) as Hsize.
    { unfold V'. rewrite (size_remove_vertex j V Hj).
      rewrite size_union_alt, size_singleton.
      pose proof (subseteq_size ((V ∖ {[j]}) ∖ {[i]}) (V ∖ {[j]})
        ltac:(set_solver)). lia. }
    lia.
  - apply (HF E V); [exact HE| |exact Hne].
    intros n b Hn. specialize (HV n b Hn). case_decide; set_solver.
Qed.

Lemma forest_expand B O i j n :
  i ≠ j -> n ∉ B -> O (n,false) = i -> O (n,true) = j ->
  session_forest B (collapse_owners i j O) ->
  session_forest ({[n]} ∪ B) O.
Proof.
  intros Hij Hfresh Hni Hnj HF E V HE HV Hne.
  destruct (decide (n ∈ E)) as [Hn|Hn].
  - assert (i ∈ V) as Hi by (rewrite <- Hni; auto).
    assert (j ∈ V) as Hj by (rewrite <- Hnj; auto).
    assert (size (E ∖ {[n]}) < size (V ∖ {[j]})) as Hlt.
    { apply HF; [set_solver| |set_solver].
      intros m b Hm. unfold collapse_owners, compose, collapse.
      assert (O (m,b) ∈ V) by (apply HV; set_solver).
      case_decide; set_solver. }
    rewrite (size_remove_vertex n E Hn), (size_remove_vertex j V Hj). lia.
  - apply (forest_uncollapse B O i j HF E V); [set_solver|done|done].
Qed.

Lemma forest_contract B O i j n b :
  i ≠ j -> n ∈ B -> O (n,b) = i -> O (n,negb b) = j ->
  session_forest B O -> session_forest (B ∖ {[n]}) (collapse_owners i j O).
Proof.
  intros Hij Hn Hni Hnj HF E V HE HV Hne.
  unfold collapse_owners, compose, collapse in HV.
  destruct (decide (i ∈ V)) as [Hi|Hi].
  - assert (size ({[n]} ∪ E) < size ({[j]} ∪ V)) as Hlt.
    { apply HF; [set_solver| |set_solver].
      intros m c Hm. apply elem_of_union in Hm as [Hm|Hm].
      - assert (m = n) as -> by set_solver.
        destruct b, c; simpl in *; rewrite ?Hni, ?Hnj; set_solver.
      - specialize (HV m c Hm). case_decide; set_solver. }
    rewrite size_add_vertex in Hlt by set_solver.
    rewrite size_union_alt, size_singleton in Hlt.
    pose proof (subseteq_size (V ∖ {[j]}) V ltac:(set_solver)). lia.
  - apply (HF E V); [set_solver| |done].
    intros m c Hm. specialize (HV m c Hm). case_decide; set_solver.
Qed.

Definition owns (B : gset nat) (O : owners) i (R : footprint) :=
  ∀ n b, (n,b) ∈ R ↔ n ∈ B ∧ O (n,b) = i.

Record configuration_typed (P : protocol) (B : gset nat) (O : owners)
    (ρ : cfg) : Prop := {
  cfg_barriers n : n ∈ B ↔ ρ !! n = Some Barrier;
  cfg_live n b : n ∈ B -> ∃ e, ρ !! O (n,b) = Some (Thread e);
  cfg_threads i e : ρ !! i = Some (Thread e) ->
    ∃ R, owns B O i R ∧ runtime_typed P ∅ R e UnitT;
  cfg_forest : session_forest B O
}.

Definition well_formed (ρ : cfg) :=
  ∃ P B O, configuration_typed P B O ρ.

Lemma rebuild_configuration P B O ρ Q C U σ (I : gset nat) :
  configuration_typed P B O ρ ->
  (∀ n, n ∈ C ↔ σ !! n = Some Barrier) ->
  session_forest C U ->
  (∀ i, i ∈ I -> ∀ e, σ !! i = Some (Thread e) ->
      ∃ R, owns C U i R ∧ runtime_typed Q ∅ R e UnitT) ->
  (∀ n b, n ∈ C -> U (n,b) ∈ I -> ∃ e, σ !! U (n,b) = Some (Thread e)) ->
  (∀ i, i ∉ I -> ∀ e, σ !! i = Some (Thread e) ↔ ρ !! i = Some (Thread e)) ->
  (∀ i, i ∉ I -> ∀ n b, n ∈ C ∧ U (n,b) = i ↔ n ∈ B ∧ O (n,b) = i) ->
  (∀ n b, n ∈ B -> O (n,b) ∉ I -> P n = Q n) ->
  configuration_typed Q C U σ.
Proof.
  intros [Hbar Hlive Hthreads HF] HC Hforest Htype Hnew Hag Hown Hp.
  constructor; [exact HC| | |exact Hforest].
  - intros n b Hn. destruct (decide (U (n,b) ∈ I)) as [Hi|Hi]; [auto|].
    destruct (proj1 (Hown _ Hi n b) (conj Hn eq_refl)) as [HnB Ho].
    destruct (Hlive n b HnB) as [e He]. exists e. apply Hag; [done|congruence].
  - intros i e He. destruct (decide (i ∈ I)) as [Hi|Hi]; [auto|].
    apply Hag in He; [|done]. destruct (Hthreads _ _ He) as (R & HR & Ht).
    exists R. split.
    + intros n b. transitivity (n ∈ B ∧ O (n,b) = i).
      * exact (HR n b).
      * symmetry. exact (Hown i Hi n b).
    + eapply runtime_protocol; [exact Ht|].
      intros n b Hnb. apply (proj1 (HR n b)) in Hnb as [Hn Ho]. apply (Hp _ b); [exact Hn|congruence].
Qed.

Lemma pure_configuration P B O ρ σ i e e' :
  configuration_typed P B O ρ ->
  ρ !! i = Some (Thread e) -> σ !! i = Some (Thread e') ->
  (∀ k, k ≠ i -> σ !! k = ρ !! k) ->
  (∀ R, runtime_typed P ∅ R e UnitT -> runtime_typed P ∅ R e' UnitT) ->
  configuration_typed P B O σ.
Proof.
  intros Hcfg Hi Hi' Hag Hty.
  destruct (cfg_threads _ _ _ _ Hcfg _ _ Hi) as (R & HR & Ht).
  eapply rebuild_configuration with (I:={[i]}); [exact Hcfg| | | | | | |].
  - intros n. rewrite (cfg_barriers _ _ _ _ Hcfg n).
    destruct (decide (n = i)) as [->|Hn]; [rewrite Hi, Hi'; split; discriminate|by rewrite Hag].
  - exact (cfg_forest _ _ _ _ Hcfg).
  - intros k Hk w Hw. apply elem_of_singleton in Hk. subst k.
    rewrite Hi' in Hw. injection Hw as <-. eauto.
  - intros n b Hn Hown. apply elem_of_singleton in Hown. rewrite Hown. eauto.
  - intros k Hk w. rewrite Hag by (intros ->; apply Hk, elem_of_singleton; reflexivity). tauto.
  - tauto.
  - reflexivity.
Qed.

Lemma exit_configuration P B O ρ σ i v :
  configuration_typed P B O ρ ->
  ρ !! i = Some (Thread (Val v)) -> σ !! i = None ->
  (∀ k, k ≠ i -> σ !! k = ρ !! k) ->
  configuration_typed P B O σ.
Proof.
  intros Hcfg Hi Hi' Hag.
  destruct (cfg_threads _ _ _ _ Hcfg _ _ Hi) as (R & HR & Ht).
  assert (R = ∅) as -> by (eapply unrestricted_value; eauto using Unit_unr).
  eapply rebuild_configuration with (I:={[i]}); [exact Hcfg| | | | | | |].
  - intros n. rewrite (cfg_barriers _ _ _ _ Hcfg n).
    destruct (decide (n = i)) as [->|Hn]; [rewrite Hi, Hi'; split; discriminate|by rewrite Hag].
  - exact (cfg_forest _ _ _ _ Hcfg).
  - intros k Hk w Hw. apply elem_of_singleton in Hk. subst k. congruence.
  - intros n b Hn Hown. exfalso. apply (not_elem_of_empty (n,b) (C:=footprint)).
    apply (proj2 (HR n b)). split; [done|apply elem_of_singleton in Hown; exact Hown].
  - intros k Hk w. rewrite Hag by (intros ->; apply Hk, elem_of_singleton; reflexivity). tauto.
  - tauto.
  - reflexivity.
Qed.

Definition reassign (O : owners) (i j : nat) (A D : footprint) : owners :=
  λ p, if decide (p ∈ A) then i else if decide (p ∈ D) then j else O p.

(* Replacing two thread footprints redirects their endpoints. Other
   threads retain their endpoints, even when a session is added or removed. *)
Lemma reassign_ownership (B C : gset nat) O i j A D :
  i ≠ j -> A ## D ->
  (∀ n b, (n,b) ∈ A ∪ D ↔ n ∈ C ∧ (n ∉ B ∨ O (n,b) = i ∨ O (n,b) = j)) ->
  (∀ n b, n ∈ B -> n ∉ C -> O (n,b) = i ∨ O (n,b) = j) ->
  let U := reassign O i j A D in
  owns C U i A ∧ owns C U j D ∧
  (∀ k, k ≠ i -> k ≠ j -> ∀ n b, n ∈ C ∧ U (n,b) = k ↔ n ∈ B ∧ O (n,b) = k) ∧
  (∀ n b, n ∈ C -> n ∈ B ->
      collapse_owners i j U (n,b) = collapse_owners i j O (n,b)).
Proof.
  intros Hij Hd Hpart Hdel U. split; [|split; [|split]].
  - intros n b. specialize (Hpart n b).
    unfold U, reassign. repeat case_decide; set_solver.
  - intros n b. specialize (Hpart n b).
    unfold U, reassign. repeat case_decide; set_solver.
  - intros k Hki Hkj n b. specialize (Hpart n b). specialize (Hdel n b).
    unfold U, reassign. repeat case_decide;
      destruct (decide (n ∈ B)), (decide (n ∈ C)); set_solver.
  - intros n b HC HB. specialize (Hpart n b).
    unfold collapse_owners, compose, U, reassign, collapse.
    repeat case_decide; set_solver.
Qed.

Lemma runtime_fork P R v t :
  runtime_typed P ∅ R (Fork (Val v)) t ->
  ∃ a b, t = FunT Lin a b ∧
    runtime_typed P ∅ R (Val v) (FunT Lin (FunT Lin b a) UnitT).
Proof. inversion 1; subst; eauto. Qed.

Lemma runtime_call P R n v t :
  runtime_typed P ∅ R (App (Val (BarrierV n)) (Val v)) t ->
  ∃ b A a, fp_split R ({[(n,b)]} : footprint) A ∧
    endpoint_type P n b = FunT Lin a t ∧ runtime_typed P ∅ A (Val v) a.
Proof.
  inversion 1; subst; empty_splits.
  match goal with H : runtime_typed _ _ _ (Val (BarrierV _)) _ |- _ =>
    inversion H; subst; clear H
  end.
  assert (l = Lin) as ->.
  { unfold endpoint_type in H4. destruct (P n), b; congruence. }
  exists b, R2, a. auto.
Qed.

Lemma endpoints_dual P n b a c d f :
  endpoint_type P n b = FunT Lin a c ->
  endpoint_type P n (negb b) = FunT Lin d f ->
  d = c ∧ f = a.
Proof.
  unfold endpoint_type. destruct (P n) as [x y], b; simpl; intros H1 H2; split; congruence.
Qed.

Lemma affected_threads (k i j : nat) :
  k ∈ ({[i]} ∪ {[j]} : gset nat) ↔ k = i ∨ k = j.
Proof. rewrite elem_of_union, !elem_of_singleton. reflexivity. Qed.

Lemma fork_configuration P B O ρ σ i j n k v :
  configuration_typed P B O ρ ->
  i ≠ j -> i ≠ n -> j ≠ n -> ctx k ->
  ρ !! i = Some (Thread (k (Fork (Val v)))) ->
  ρ !! j = None -> ρ !! n = None ->
  σ !! i = Some (Thread (k (Val (BarrierV n)))) ->
  σ !! j = Some (Thread (App (Val v) (Val (BarrierV n)))) ->
  σ !! n = Some Barrier ->
  (∀ m, m ≠ i -> m ≠ j -> m ≠ n -> σ !! m = ρ !! m) ->
  well_formed σ.
Proof.
  intros Hcfg Hij Hin Hjn Hk Hi Hj Hn Hi' Hj' Hn' Hag.
  destruct (cfg_threads _ _ _ _ Hcfg _ _ Hi) as (R & Hown & Ht).
  destruct (runtime_context P k Hk _ _ _ Ht) as (A & F & u & HR & Hfork & Hplug).
  destruct (runtime_fork _ _ _ _ Hfork) as (a & b & -> & Hv).
  assert (n ∉ B) as Hfresh.
  { intros H. apply (cfg_barriers _ _ _ _ Hcfg) in H. congruence. }
  assert (∀ m s, m ∈ B -> O (m,s) ≠ j) as Hnoj.
  { intros m s Hm Heq. destruct (cfg_live _ _ _ _ Hcfg m s Hm) as [w Hw].
    congruence. }
  assert (∀ s, (n,s) ∉ R) as Hno.
  { intros s Hs. apply Hown in Hs. tauto. }
  set (Q := λ m, if decide (m = n) then (a,b) else P m).
  set (C := {[n]} ∪ B).
  set (X := ({[ (n,false) ]} ∪ F : footprint)).
  set (Y := (A ∪ {[ (n,true) ]} : footprint)).
  assert (X ## Y) as Hd.
  { pose proof (Hno false) as Hnf. pose proof (Hno true) as Hnt.
    unfold X, Y, fp_split in *. clear - HR Hnf Hnt. set_solver. }
  assert (∀ m s, (m,s) ∈ X ∪ Y ↔
      m ∈ C ∧ (m ∉ B ∨ O (m,s) = i ∨ O (m,s) = j)) as Hpart.
  { intros m s. pose proof (Hown m s) as HO.
    pose proof (Hnoj m s) as HJ.
    unfold X, Y, C, fp_split in *.
    clear - HR HO HJ Hfresh. destruct (decide (m = n)) as [->|Hne]; destruct s; set_solver. }
  destruct (reassign_ownership B C O i j X Y Hij Hd Hpart
    ltac:(unfold C; set_solver)) as (HX & HY & Hout & Hcollapse).
  set (U := reassign O i j X Y) in *.
  assert (∀ m s, m ∈ B -> collapse_owners i j U (m,s) = O (m,s)) as Hcoll.
  { intros m s Hm. rewrite Hcollapse by (unfold C; set_solver).
    unfold collapse_owners, compose, collapse.
    case_decide as Heq; [exact (False_rect _ (Hnoj m s Hm Heq))|reflexivity]. }
  assert (∀ m s, (m,s) ∈ R -> P m = Q m) as HQ.
  { intros m s Hm. apply Hown in Hm. unfold Q.
    case_decide; [subst; tauto|done]. }
  assert (endpoint_type Q n false = FunT Lin a b) as Hfalse.
  { unfold endpoint_type, Q. by case_decide. }
  assert (endpoint_type Q n true = FunT Lin b a) as Htrue.
  { unfold endpoint_type, Q. by case_decide. }
  exists Q, C, U.
  eapply rebuild_configuration with (I := {[i]} ∪ {[j]}); [exact Hcfg| | | | | | |].
  - intros m. destruct (decide (m = n)) as [->|Hm]; [unfold C; set_solver|].
    assert (m ∈ C ↔ m ∈ B) as HC by (unfold C; set_solver).
    rewrite HC, (cfg_barriers _ _ _ _ Hcfg m).
    destruct (decide (m = i)) as [->|Hmi].
    + rewrite Hi, Hi'. split; discriminate.
    + destruct (decide (m = j)) as [->|Hmj].
      * rewrite Hj, Hj'. split; discriminate.
      * by rewrite Hag.
  - unfold C. apply forest_expand with (i:=i) (j:=j); [done|done| | |].
    + refine (proj2 (proj1 (HX n false) _)). unfold X. apply elem_of_union. left. set_solver.
    + refine (proj2 (proj1 (HY n true) _)). unfold Y. apply elem_of_union. right. set_solver.
    + eapply forest_weaken; [exact (cfg_forest _ _ _ _ Hcfg)|done|exact Hcoll].
  - intros l Hl w Hw. apply affected_threads in Hl as [-> | ->].
    + rewrite Hi' in Hw. injection Hw as <-. exists X. split; [exact HX|].
      apply Hplug.
      * intros m s Hm. apply (HQ m s). clear - HR Hm. unfold fp_split in HR. set_solver.
      * pose proof (Hno false) as Hnf. clear - HR Hnf. unfold fp_split in HR. set_solver.
      * rewrite <- Hfalse. apply RT_endpoint. apply env_unr_empty.
    + rewrite Hj' in Hw. injection Hw as <-. exists Y. split; [exact HY|].
      eapply RT_app with (R1:=A) (R2:={[(n,true)]}) (l:=Lin).
      * apply empty_env_split.
      * unfold fp_split, Y. split; [reflexivity|].
        apply elem_of_disjoint. intros p Hp Hsingle.
        apply elem_of_singleton in Hsingle. subst p.
        apply (Hno true). destruct HR as [-> _]. apply elem_of_union. auto.
      * eapply runtime_protocol; [exact Hv|].
        intros m s Hm. apply (HQ m s). clear - HR Hm. unfold fp_split in HR. set_solver.
      * rewrite <- Htrue. apply RT_endpoint. apply env_unr_empty.
  - intros m s Hm Hs. apply affected_threads in Hs as [-> | ->]; eauto.
  - intros l Hl w. destruct (decide (l = n)) as [->|Hln]; [rewrite Hn, Hn'; split; discriminate|].
    assert (l ≠ i ∧ l ≠ j) as [Hli Hlj] by (rewrite affected_threads in Hl; tauto).
    rewrite Hag by done. tauto.
  - intros l Hl. rewrite affected_threads in Hl. apply Hout; tauto.
  - intros m s Hm _. unfold Q. case_decide; [subst; contradiction|reflexivity].
Qed.

Lemma sync_configuration P B O ρ σ i j n k1 k2 v1 v2 :
  configuration_typed P B O ρ ->
  i ≠ j -> i ≠ n -> j ≠ n -> ctx k1 -> ctx k2 ->
  ρ !! i = Some (Thread (k1 (App (Val (BarrierV n)) (Val v1)))) ->
  ρ !! j = Some (Thread (k2 (App (Val (BarrierV n)) (Val v2)))) ->
  ρ !! n = Some Barrier ->
  σ !! i = Some (Thread (k1 (Val v2))) -> σ !! j = Some (Thread (k2 (Val v1))) ->
  σ !! n = None ->
  (∀ m, m ≠ i -> m ≠ j -> m ≠ n -> σ !! m = ρ !! m) ->
  well_formed σ.
Proof.
  intros Hcfg Hij Hin Hjn Hk1 Hk2 Hi Hj Hn Hi' Hj' Hn' Hag.
  destruct (cfg_threads _ _ _ _ Hcfg _ _ Hi) as (R1 & Hown1 & Hty1).
  destruct (cfg_threads _ _ _ _ Hcfg _ _ Hj) as (R2 & Hown2 & Hty2).
  destruct (runtime_context _ _ Hk1 _ _ _ Hty1) as (L1 & F1 & t1 & HR1 & Hcall1 & Hplug1).
  destruct (runtime_context _ _ Hk2 _ _ _ Hty2) as (L2 & F2 & t2 & HR2 & Hcall2 & Hplug2).
  destruct (runtime_call _ _ _ _ _ Hcall1) as (s1 & A1 & a1 & HL1 & Hd1 & Hv1).
  destruct (runtime_call _ _ _ _ _ Hcall2) as (s2 & A2 & a2 & HL2 & Hd2 & Hv2).
  assert (n ∈ B) as HB by (apply (cfg_barriers _ _ _ _ Hcfg); exact Hn).
  assert (O (n,s1) = i) as Hoi.
  { refine (proj2 (proj1 (Hown1 n s1) _)). clear - HR1 HL1. unfold fp_split in *. set_solver. }
  assert (O (n,s2) = j) as Hoj.
  { refine (proj2 (proj1 (Hown2 n s2) _)). clear - HR2 HL2. unfold fp_split in *. set_solver. }
  assert (s2 = negb s1) as -> by (destruct s1, s2; simpl in *; congruence).
  destruct (endpoints_dual _ _ _ _ _ _ _ Hd1 Hd2) as [-> ->].
  assert (R1 ## R2) as Hdisj.
  { apply elem_of_disjoint. intros [m s] H1 H2. apply Hown1 in H1 as [_ H1]. apply Hown2 in H2 as [_ H2]. congruence. }
  set (C := B ∖ {[n]}).
  set (X := A2 ∪ F1).
  set (Y := A1 ∪ F2).
  assert (X ## Y) as Hd.
  { unfold X, Y, fp_split in *. clear - HR1 HR2 HL1 HL2 Hdisj. set_solver. }
  assert (∀ s, (n,s) ∉ X ∪ Y) as Hno.
  { intros s. unfold X, Y, fp_split in *.
    clear - HR1 HR2 HL1 HL2 Hdisj.
    destruct s1, s; simpl in *; set_solver. }
  assert (∀ m s, (m,s) ∈ X ∪ Y ↔
      m ∈ C ∧ (m ∉ B ∨ O (m,s) = i ∨ O (m,s) = j)) as Hpart.
  { intros m s. pose proof (Hown1 m s) as HO1. pose proof (Hown2 m s) as HO2.
    destruct (decide (m = n)) as [->|Hne]; [specialize (Hno s); unfold C; set_solver|].
    destruct HR1 as [-> _], HR2 as [-> _], HL1 as [-> _], HL2 as [-> _].
    unfold X, Y, C. rewrite !elem_of_union, !elem_of_singleton in HO1, HO2.
    rewrite !elem_of_union, elem_of_difference, elem_of_singleton.
    assert ((m,s) ≠ (n,s1)) by congruence.
    assert ((m,s) ≠ (n,negb s1)) by congruence.
    tauto. }
  assert (∀ m s, m ∈ B -> m ∉ C -> O (m,s) = i ∨ O (m,s) = j) as Hdel.
  { intros m s Hm HmC.
    destruct (decide (m = n)) as [->|Hne].
    - destruct s1, s; simpl in *; auto.
    - exfalso. apply HmC. unfold C. apply elem_of_difference.
      split; [exact Hm|intros He; apply elem_of_singleton in He; contradiction]. }
  destruct (reassign_ownership B C O i j X Y Hij Hd Hpart Hdel)
    as (HX & HY & Hout & Hcollapse).
  set (U := reassign O i j X Y) in *.
  exists P, C, U.
  eapply rebuild_configuration with (I := {[i]} ∪ {[j]}); [exact Hcfg| | | | | | |].
  - intros m. destruct (decide (m = n)) as [->|Hm]; [rewrite Hn'; unfold C; set_solver|].
    assert (m ∈ C ↔ m ∈ B) as HC by (unfold C; set_solver).
    rewrite HC, (cfg_barriers _ _ _ _ Hcfg m).
    destruct (decide (m = i)) as [->|Hmi].
    + rewrite Hi, Hi'. split; discriminate.
    + destruct (decide (m = j)) as [->|Hmj].
      * rewrite Hj, Hj'. split; discriminate.
      * by rewrite Hag.
  - apply forest_uncollapse with (i:=i) (j:=j).
    eapply forest_weaken with (B:=C) (O:=collapse_owners i j O); [|done|].
    + apply (forest_contract B O i j n s1); eauto using cfg_forest.
    + intros m s Hm. apply Hcollapse; [done|unfold C in *; set_solver].
  - intros l Hl w Hw. apply affected_threads in Hl as [-> | ->].
    + rewrite Hi' in Hw. injection Hw as <-. exists X. split; [exact HX|].
      apply Hplug1; [reflexivity| |exact Hv2].
      unfold fp_split in *. clear - HR1 HR2 HL1 HL2 Hdisj. set_solver.
    + rewrite Hj' in Hw. injection Hw as <-. exists Y. split; [exact HY|].
      apply Hplug2; [reflexivity| |exact Hv1].
      unfold fp_split in *. clear - HR1 HR2 HL1 HL2 Hdisj. set_solver.
  - intros m s Hm Hs. apply affected_threads in Hs as [-> | ->]; eauto.
  - intros l Hl w. destruct (decide (l = n)) as [->|Hln]; [rewrite Hn, Hn'; split; discriminate|].
    assert (l ≠ i ∧ l ≠ j) as [Hli Hlj] by (rewrite affected_threads in Hl; tauto).
    rewrite Hag by done. tauto.
  - intros l Hl. rewrite affected_threads in Hl. apply Hout; tauto.
  - reflexivity.
Qed.

Lemma frame_at (L L' F : gmap nat obj) k :
  L ##ₘ F -> L' ##ₘ F ->
  (is_Some (L !! k) ∨ is_Some (L' !! k)) ->
  (L ∪ F) !! k = L !! k ∧ (L' ∪ F) !! k = L' !! k.
Proof.
  intros Hd Hd' Hk.
  assert (F !! k = None) as HF.
  { destruct (F !! k) as [o|] eqn:Ho; [|reflexivity].
    destruct Hk as [[w Hw]|[w Hw]]; exfalso.
    - eapply (proj1 (map_disjoint_spec L F) Hd); eauto.
    - eapply (proj1 (map_disjoint_spec L' F) Hd'); eauto. }
  rewrite (lookup_union L F), (lookup_union L' F), HF.
  destruct (L !! k), (L' !! k); split; reflexivity.
Qed.

Lemma frame_agree (L L' F : gmap nat obj) k :
  L' !! k = L !! k -> (L' ∪ F) !! k = (L ∪ F) !! k.
Proof. intros H. by rewrite (lookup_union L' F), (lookup_union L F), H. Qed.

Local Ltac simplify_cfg := unfold cfg in *; simplify_map_eq.

Local Ltac step_point k Hdis Hdis' :=
  let H1 := fresh "Hbefore" in let H2 := fresh "Hafter" in
  destruct (frame_at _ _ _ k Hdis Hdis'
    ltac:(first [left; eexists; simplify_cfg; reflexivity |
                 right; eexists; simplify_cfg; reflexivity])) as [H1 H2].

Lemma well_formed_step ρ σ i :
  step i ρ σ -> well_formed ρ -> well_formed σ.
Proof.
  intros Hs. destruct Hs as [L L' F i Hdis Hdis' Hloc].
  intros (P & B & O & Hcfg).
  destruct Hloc as
    [i k e e' Hk He
    |i v
    |i j n k v Hij Hin Hjn Hk
    |i j n k1 k2 v1 v2 Hij Hin Hjn Hk1 Hk2];
    unfold cfg in *.
  - step_point i Hdis Hdis'. simplify_cfg.
    exists P, B, O. eapply (pure_configuration P B O _ _ i (k e) (k e')); [exact Hcfg|eassumption|eassumption| |].
    + intros m Hm. apply frame_agree. simplify_cfg; reflexivity.
    + intros R Hty. destruct (runtime_context _ _ Hk _ _ _ Hty) as (A & D & u & [-> HA] & Ht & Hplug).
      apply Hplug; [reflexivity|clear - HA; set_solver|eapply runtime_pure; eauto].
  - step_point i Hdis Hdis'. simplify_cfg.
    exists P, B, O. eapply (exit_configuration P B O _ _ i v); [exact Hcfg|eassumption|eassumption|].
    intros m Hm. apply frame_agree. simplify_cfg; reflexivity.
  - step_point i Hdis Hdis'. step_point j Hdis Hdis'. step_point n Hdis Hdis'. simplify_cfg.
    eapply (fork_configuration P B O _ _ i j n k v); try eassumption.
    intros m Hmi Hmj Hmn. apply frame_agree. simplify_cfg; reflexivity.
  - step_point i Hdis Hdis'. step_point j Hdis Hdis'. step_point n Hdis Hdis'. simplify_cfg.
    eapply (sync_configuration P B O _ _ i j n k1 k2 v1 v2); try eassumption.
    intros m Hmi Hmj Hmn. apply frame_agree. simplify_cfg; reflexivity.
Qed.

Inductive focused (R : footprint) : expr -> Prop :=
  | Focus_pure k e e' : ctx k -> pure_step e e' -> focused R (k e)
  | Focus_fork k v : ctx k -> focused R (k (Fork (Val v)))
  | Focus_call k n b v :
      ctx k -> (n,b) ∈ R -> focused R (k (App (Val (BarrierV n)) (Val v))).

Lemma focus_in_context R S k e :
  ctx1 k -> R ⊆ S -> focused R e -> focused S (k e).
Proof.
  intros Hk Hsub Hf. destruct Hf as [k' y z Hctx Hp|k' v Hctx|k' n b v Hctx Hn].
  - exact (Focus_pure S (k ∘ k') y z (Ctx_comp _ _ Hk Hctx) Hp).
  - exact (Focus_fork S (k ∘ k') v (Ctx_comp _ _ Hk Hctx)).
  - exact (Focus_call S (k ∘ k') n b v (Ctx_comp _ _ Hk Hctx) (Hsub _ Hn)).
Qed.

Lemma focus_pure R e e' : pure_step e e' -> focused R e.
Proof. exact (Focus_pure R id e e' Ctx_id). Qed.

Lemma arrow_value P G R v a b l :
  runtime_typed P G R (Val v) (FunT l a b) ->
  (∃ x e, v = FunV x e) ∨ (∃ n s, v = BarrierV n ∧ (n,s) ∈ R).
Proof.
  inversion 1; subst; eauto. right. exists n, b0. split; [reflexivity|].
  apply elem_of_singleton. reflexivity.
Qed.

Lemma pair_value P G R v a b :
  runtime_typed P G R (Val v) (PairT a b) -> ∃ v1 v2, v = PairV v1 v2.
Proof.
  inversion 1; subst; eauto.
  unfold endpoint_type in *. destruct (P n), b0; discriminate.
Qed.

Lemma sum_value P G R v n (ts : fin n -> type) :
  runtime_typed P G R (Val v) (SumT n ts) -> ∃ i : fin n, ∃ w, v = SumV i w.
Proof.
  intros H. remember (Val v) as e eqn:He. remember (SumT n ts) as t eqn:Ht.
  destruct H; try discriminate He; try discriminate Ht.
  - injection He as <-. assert (n0 = n) by (injection Ht; auto). subst n0. eauto.
  - unfold endpoint_type in Ht. destruct (P n0), b; discriminate.
Qed.

Lemma runtime_progress P G R e t :
  runtime_typed P G R e t -> G = ∅ -> (∃ v, e = Val v) ∨ focused R e.
Proof.
  induction 1; intros ->; try (left; eexists; reflexivity).
  - destruct H as [D [H _]]. pose proof (lookup_insert_eq D x t) as Hx.
    unfold env in *. rewrite <- H in Hx. simplify_cfg.
  - right. eauto using focus_pure, Fun_step.
  - empty_splits. right.
    destruct (IHruntime_typed2 eq_refl) as [[v2 ->]|Hf2].
    + destruct (IHruntime_typed1 eq_refl) as [[v1 ->]|Hf1].
      * destruct (arrow_value _ _ _ _ _ _ _ H1) as [(x & body & ->)|(n & side & -> & Hn)].
        -- eauto using focus_pure, App_step.
        --
           apply (Focus_call R id n side v2 Ctx_id). unfold fp_split in *. set_solver.
      * apply (focus_in_context R1 R (λ x, App x (Val v2)));
          [constructor|unfold fp_split in *; set_solver|done].
    + apply (focus_in_context R2 R (λ x, App e1 x));
        [constructor|unfold fp_split in *; set_solver|done].
  - right. eauto using focus_pure, Unit_step.
  - empty_splits. right.
    destruct (IHruntime_typed1 eq_refl) as [[v1 ->]|Hf1].
    + destruct (IHruntime_typed2 eq_refl) as [[v2 ->]|Hf2].
      * eauto using focus_pure, Pair_step.
      * apply (focus_in_context R2 R (λ x, Pair (Val v1) x));
          [constructor|unfold fp_split in *; set_solver|done].
    + apply (focus_in_context R1 R (λ x, Pair x e2));
        [constructor|unfold fp_split in *; set_solver|done].
  - empty_splits. right.
    destruct (IHruntime_typed1 eq_refl) as [[v ->]|Hf].
    + destruct (pair_value _ _ _ _ _ _ H1) as (v1 & v2 & ->).
      eauto using focus_pure, LetPair_step.
    + apply (focus_in_context R1 R (λ x, LetPair x e2));
        [constructor|unfold fp_split in *; set_solver|done].
  - right. destruct (IHruntime_typed eq_refl) as [[v ->]|Hf].
    + eauto using focus_pure, Sum_step.
    + eapply (focus_in_context R R (λ x, Sum i x)); [constructor|reflexivity|done].
  - empty_splits. right.
    destruct (IHruntime_typed eq_refl) as [[v ->]|Hf].
    + match goal with Hs : runtime_typed P ∅ _ (Val v) (SumT _ _) |- _ =>
        destruct (sum_value _ _ _ _ _ _ Hs) as (i & w & ->)
      end.
      eauto using focus_pure, MatchSum_step.
    + eapply (focus_in_context R1 R (λ x, MatchSum n x es));
        [constructor|unfold fp_split in *; set_solver|done].
  - right. destruct (IHruntime_typed eq_refl) as [[v ->]|Hf].
    + change (Fork (Val v)) with (id (Fork (Val v))). eauto using Focus_fork, Ctx_id.
    + eapply (focus_in_context R R Fork); [constructor|reflexivity|done].
Qed.

Lemma framed_reduction (ρ L L' : gmap nat obj) i :
  local_step i L L' ->
  (∀ k o, L !! k = Some o -> ρ !! k = Some o) ->
  (∀ k o, L' !! k = Some o -> L !! k = None -> ρ !! k = None) ->
  can_step ρ i.
Proof.
  intros Hstep Hsub Hfresh. set (F := ρ ∖ L).
  assert (ρ = L ∪ F) as Heq.
  { apply map_eq. intros k. destruct (L !! k) as [o|] eqn:Ho.
    - rewrite (lookup_union L F), Ho. destruct (F !! k); exact (Hsub k o Ho).
    - rewrite (lookup_union_r L F k Ho). unfold F. destruct (ρ !! k) as [w|] eqn:Hρ.
      + symmetry. apply lookup_difference_Some. auto.
      + symmetry. apply lookup_difference_None. auto. }
  exists (L' ∪ F). rewrite Heq. apply Frame_step; [| |done].
  - apply map_disjoint_spec. intros k o w Ho Hw.
    apply lookup_difference_Some in Hw as [_ Hnone]. congruence.
  - apply map_disjoint_spec. intros k o w Ho Hw.
    apply lookup_difference_Some in Hw as [Hw Hk].
    specialize (Hfresh _ _ Ho Hk). congruence.
Qed.

Definition thread_at (ρ : cfg) i := ∃ e, ρ !! i = Some (Thread e).
Definition thread_waits (ρ : cfg) i n :=
  ∃ e, ρ !! i = Some (Thread e) ∧ expr_waiting e n.

Lemma two_threads_sync (ρ : gmap nat obj) i j n :
  i ≠ j -> ρ !! n = Some Barrier ->
  thread_waits ρ i n -> thread_waits ρ j n -> can_step ρ n.
Proof.
  intros Hij Hn (e1 & Hi & k1 & v1 & Hk1 & ->) (e2 & Hj & k2 & v2 & Hk2 & ->).
  unfold cfg in *.
  assert (i ≠ n) as Hin by (intros ->; rewrite Hn in Hi; discriminate).
  assert (j ≠ n) as Hjn by (intros ->; rewrite Hn in Hj; discriminate).
  eapply framed_reduction; [exact (Sync_step i j n k1 k2 v1 v2 Hij Hin Hjn Hk1 Hk2)| |].
  - intros m o Hm.
    destruct (decide (m = i)) as [Hmi|Hmi], (decide (m = j)) as [Hmj|Hmj],
      (decide (m = n)) as [Hmn|Hmn]; try subst m; simplify_cfg; congruence.
  - intros m o Hm Hnone.
    destruct (decide (m = i)) as [Hmi|Hmi], (decide (m = j)) as [Hmj|Hmj];
      try subst m; simplify_cfg.
Qed.

Lemma thread_progress P B O ρ i :
  configuration_typed P B O ρ -> thread_at ρ i ->
  can_step ρ i ∨ ∃ n, n ∈ B ∧ thread_waits ρ i n.
Proof.
  intros Hcfg [e Hi]. unfold cfg in *.
  destruct (cfg_threads _ _ _ _ Hcfg _ _ Hi) as (R & HR & Ht).
  destruct (runtime_progress _ _ _ _ _ Ht eq_refl) as [[v ->]|Hf].
  - left. eapply framed_reduction; [exact (Exit_step i v)| |].
    + intros m o Hm. destruct (decide (m = i)); simplify_cfg; congruence.
    + intros m o Hm. simplify_cfg.
  - destruct Hf as [k y z Hk Hp|k v Hk|k n b v Hk Hnb].
    + left. eapply framed_reduction; [exact (Pure_step i k y z Hk Hp)| |].
      * intros m o Hm. destruct (decide (m = i)); simplify_cfg; congruence.
      * intros m o Hm Hnone. destruct (decide (m = i)); simplify_cfg.
    + left. set (D := dom ρ : gset nat).
      set (j := fresh D). set (n := fresh ({[j]} ∪ D)).
      assert (i ∈ D) as Hdi by (unfold D; eapply elem_of_dom_2; exact Hi).
      assert (j ∉ D) as Hdj by (unfold j; apply is_fresh).
      assert (n ∉ {[j]} ∪ D) as Hdn by (unfold n; apply is_fresh).
      assert (i ≠ j ∧ i ≠ n ∧ j ≠ n) as (Hij & Hin & Hjn) by set_solver.
      assert (ρ !! j = None) as Hj by (apply not_elem_of_dom; exact Hdj).
      assert (ρ !! n = None) as Hn by (apply not_elem_of_dom; set_solver).
      eapply framed_reduction; [exact (Fork_step i j n k v Hij Hin Hjn Hk)| |].
      * intros m o Hm. destruct (decide (m = i)); simplify_cfg; congruence.
      * intros m o Hm Hnone.
        destruct (decide (m = i)) as [Hmi|Hmi], (decide (m = j)) as [Hmj|Hmj],
          (decide (m = n)) as [Hmn|Hmn]; try subst m; simplify_cfg; congruence.
    + right. exists n. split.
      * apply HR in Hnb. tauto.
      * eexists. split; [exact Hi|]. exists k, v. auto.
Qed.

Local Instance thread_at_dec (ρ : cfg) i : Decision (thread_at ρ i).
Proof.
  unfold thread_at. destruct (ρ !! i) as [[e|]|].
  - left. eauto.
  - right. intros [e He]. discriminate.
  - right. intros [e He]. discriminate.
Defined.

Definition thread_ids (ρ : gmap nat obj) : gset nat :=
  filter (thread_at ρ) (dom ρ).

Lemma elem_of_thread_ids (ρ : gmap nat obj) i :
  i ∈ thread_ids ρ ↔ thread_at ρ i.
Proof.
  unfold thread_ids. rewrite elem_of_filter. split; [tauto|].
  intros [e He]. split; [exists e; exact He|eapply elem_of_dom_2; exact He].
Qed.

(* A scan of the threads either finds a reduction or assigns distinct
   barriers to the threads that have to wait. *)
Lemma waiting_cover P B O ρ :
  configuration_typed P B O ρ ->
  ∀ V : gset nat, V ⊆ thread_ids ρ ->
    (∃ i, can_step ρ i) ∨
    ∃ E : gset nat, E ⊆ B ∧ size E = size V ∧
      ∀ n, n ∈ E -> ∃ i, i ∈ V ∧ thread_waits ρ i n.
Proof.
  intros Hcfg. induction V as [|i V Hi IH] using set_ind_L; intros HV.
  - right. exists ∅. split; [set_solver|]. split; [reflexivity|set_solver].
  - destruct (IH ltac:(set_solver)) as [Hstep|(E & HE & Hsize & Hcover)]; [auto|].
    assert (thread_at ρ i) as Hthread by (apply elem_of_thread_ids; set_solver).
    destruct (thread_progress _ _ _ _ _ Hcfg Hthread) as [Hstep|(n & Hn & Hwait)].
    + left. eauto.
    + destruct (decide (n ∈ E)) as [Hne|Hne].
      * destruct (Hcover n Hne) as (j & Hj & Hwaitj).
        left. exists n. apply (two_threads_sync ρ i j n); [intros ->; exact (Hi Hj)| |exact Hwait|exact Hwaitj].
        apply (cfg_barriers _ _ _ _ Hcfg). exact Hn.
      * right. exists ({[n]} ∪ E). split; [set_solver|]. split.
        -- rewrite !size_add_vertex by done. congruence.
        -- intros m Hm. apply elem_of_union in Hm as [Hm|Hm].
           ++ assert (m = n) as -> by set_solver. exists i. split; [set_solver|done].
           ++ destruct (Hcover m Hm) as (j & Hj & Hw). exists j. split; [set_solver|done].
Qed.

Lemma well_formed_progress ρ : well_formed ρ -> global_progress ρ.
Proof.
  intros (P & B & O & Hcfg).
  destruct (decide (thread_ids ρ = ∅)) as [Hempty|Hactive].
  - left. intros i. unfold inactive.
    destruct (ρ !! i) as [[e|]|] eqn:Hi; [| |reflexivity].
    + exfalso. assert (i ∈ thread_ids ρ) as Hti by (apply elem_of_thread_ids; exists e; exact Hi).
      rewrite Hempty in Hti. set_solver.
    + exfalso. apply (cfg_barriers _ _ _ _ Hcfg) in Hi.
      destruct (cfg_live _ _ _ _ Hcfg i false Hi) as [e He].
      assert (O (i,false) ∈ thread_ids ρ) as Hti by (apply elem_of_thread_ids; exists e; exact He).
      rewrite Hempty in Hti. set_solver.
  - right.
    destruct (waiting_cover _ _ _ _ Hcfg (thread_ids ρ) ltac:(reflexivity))
      as [Hstep|(E & HE & Hsize & _)]; [done|].
    exfalso. pose proof (cfg_forest _ _ _ _ Hcfg E (thread_ids ρ) HE) as Hlt.
    assert (∀ n b, n ∈ E -> O (n,b) ∈ thread_ids ρ) as Howners.
    { intros n b Hn. apply elem_of_thread_ids, (cfg_live _ _ _ _ Hcfg).
      apply HE. exact Hn. }
    specialize (Hlt Howners Hactive). lia.
Qed.

Lemma well_formed_initial e :
  typed ∅ e UnitT -> well_formed {[0 := Thread e]}.
Proof.
  intros Ht. exists (λ _, (UnitT,UnitT)), (∅ : gset nat), (λ _, 0).
  constructor.
  - intros n. split; [set_solver|]. intros Hn.
    unfold cfg in *. destruct (decide (n = 0)); simplify_cfg.
  - intros n b Hn. set_solver.
  - intros i w Hi. unfold cfg in *.
    destruct (decide (i = 0)); simplify_cfg.
    exists ∅. split; [unfold owns; set_solver|apply source_runtime; exact Ht].
  - intros E V HE HV Hne. assert (E = ∅) as -> by set_solver.
    rewrite size_empty. assert (size V ≠ 0).
    { intros Hsz. apply Hne. apply leibniz_equiv. by apply size_empty_inv. }
    lia.
Qed.

Theorem typed_global_progress e ρ :
  typed ∅ e UnitT -> steps {[ 0 := Thread e ]} ρ -> global_progress ρ.
Proof.
  intros Ht Hsteps. apply well_formed_progress.
  eapply rtc_ind_r; [exact (well_formed_initial e Ht)| |exact Hsteps].
  intros σ τ _ [i Hstep] Hwf. eapply well_formed_step; eauto.
Qed.
