From strictness.cbpv Require Import lazy_semtyping.
From Stdlib Require Import Arith.Peano_dec Logic.Eqdep_dec Lia.

Scheme lazy_le_ind := Induction for le Sort Prop.

(* Restricting an environment drops its most recently added entries. *)
Lemma lazy_down_same {X n} (f : fin n -> X) (H : n <= n) :
  down_env_until f n H = f.
Proof.
  unfold down_env_until.
  generalize (le_minus_plus n n H).
  rewrite Nat.sub_diag. intro e.
  replace e with (@eq_refl nat n) by (apply UIP_dec; apply Nat.eq_dec).
  reflexivity.
Qed.

Lemma lazy_down_step {X n} (f : fin (S n) -> X) m
    (H : m <= n) (H' : m <= S n) :
  down_env_until f m H' =
  down_env_until (fun i => f (Some i)) m H.
Proof.
  unfold down_env_until.
  generalize (le_minus_plus m (S n) H').
  rewrite (Nat.sub_succ_l _ _ H).
  generalize (le_minus_plus m n H).
  generalize (n - m) as d.
  intros d e. subst n.
  intro e. replace e with (@eq_refl nat (S (d + m))) by (apply UIP_dec; apply Nat.eq_dec).
  reflexivity.
Qed.

Lemma lazy_down_compose {X n} (f : fin n -> X) m k
    (H : m <= n) (G : k <= m) (I : k <= n) :
  down_env_until (down_env_until f m H) k G = down_env_until f k I.
Proof.
  revert f I. induction H as [|n H IH] using lazy_le_ind; intros f I.
  - rewrite lazy_down_same. f_equal. apply le_unique.
  - rewrite (lazy_down_step f m H), (lazy_down_step f k (Nat.le_trans _ _ _ G H)).
    apply IH.
Qed.

Lemma lazy_pad_same n (β : attrs n) (H : n <= n) :
  pad_with Strict β n H = β.
Proof.
  unfold pad_with.
  generalize (le_minus_plus n n H).
  rewrite Nat.sub_diag. intro e.
  replace e with (@eq_refl nat n) by (apply UIP_dec; apply Nat.eq_dec).
  reflexivity.
Qed.

Lemma lazy_pad_step k n (β : attrs k) (H : k <= n) (H' : k <= S n) :
  pad_with Strict β (S n) H' = Strict .: pad_with Strict β n H.
Proof.
  unfold pad_with.
  generalize (le_minus_plus k (S n) H').
  rewrite (Nat.sub_succ_l _ _ H).
  generalize (le_minus_plus k n H).
  generalize (n - k) as d.
  intros d e. subst n.
  intro e. replace e with (@eq_refl nat (S (d + k))) by (apply UIP_dec; apply Nat.eq_dec).
  reflexivity.
Qed.

Lemma lazy_pad_compare k n (β : attrs k) (γ : attrs n) (H : k <= n) :
  (pad_with Strict β n H) γS<= γ <->
  β γS<= (down_env_until γ k H).
Proof.
  revert γ. induction H as [|n H IH] using lazy_le_ind; intro γ.
  - rewrite lazy_pad_same, lazy_down_same. reflexivity.
  - rewrite (lazy_pad_step _ _ _ H), (lazy_down_step γ k H).
    rewrite <- IH. unfold attr_vector_stricter.
    split.
    + intros Hle i. exact (Hle (Some i)).
    + intros Hle [i|]; [apply Hle | exact I].
Qed.

Lemma lazy_map_down {n k} (A : Ty n k) m (H : m <= n) :
  down_ty_until A m H = map_Ty (fun γ => down_env_until γ m H) A.
Proof. induction A; simpl; congruence. Qed.

Lemma lazy_clos_down_same {k} (C : Clos k) m :
  well_scoped_clos C m -> down_clos m C = C.
Proof.
  induction C; simpl; intro Hscope; try reflexivity;
    try solve [destruct Hscope; f_equal; auto | f_equal; auto].
  all: generalize (min_le mOuter m);
    rewrite (Nat.min_l _ _ Hscope); intro; rewrite lazy_down_same; reflexivity.
Qed.

Lemma lazy_clos_down_compose {k} (C : Clos k) m n :
  down_clos m (down_clos n C) = down_clos (Nat.min n m) C.
Proof.
  induction C; simpl; try solve [f_equal; auto].
  all: generalize (min_le (Nat.min mOuter n) m)
                  (min_le mOuter (Nat.min n m));
    rewrite <- (Nat.min_assoc mOuter n m); intros;
    f_equal; apply lazy_down_compose.
Qed.

Lemma lazy_clos_down_argument {k} (W : Clos k) o n m :
  o <= n -> well_scoped_clos W m ->
  down_clos o (down_clos n W) = down_clos (Nat.min o m) W.
Proof.
  intros Ho HW. rewrite lazy_clos_down_compose, (Nat.min_r n o Ho).
  rewrite (Nat.min_comm o m), <- (lazy_clos_down_compose W o m).
  now rewrite (lazy_clos_down_same W m HW).
Qed.

(* The logical relation keeps the attributes of the original context fixed
   as evaluation enters binders. Only the suffix at that scope is compared. *)
Fixpoint lazy_scoped {lower n k} (β : attrs lower)
    (A : Ty n k) (C : Clos k) : Prop :=
  (match A in Ty _ k return Clos k -> Prop with
   | VUnit => fun C => C = Unit
   | VThunk γ B => fun C =>
       exists o p δ γ' ρ M (H : o <= n) (H' : o <= p) (L : lower <= o),
         down_env_until γ o H = δ /\
         down_env_until γ' o H' = δ /\
         C = Thunk o p δ ρ M /\
         (forall I : lower <= n,
           β γS<= (down_env_until γ lower I) ->
           exists T, EvalComp γ' ρ M T /\ lazy_scoped β B (o T↓ T))
   | VProd A1 A2 => fun C =>
       exists W1 W2, C = Pair W1 W2 /\
         lazy_scoped β A1 W1 /\ lazy_scoped β A2 W2
   | VSum A1 A2 => fun C =>
       exists W, (C = Inl W /\ lazy_scoped β A1 W) \/
                 (C = Inr W /\ lazy_scoped β A2 W)
   | CF A => fun C => exists W, C = Return W /\ lazy_scoped β A W
   | CAbs q A B => fun C =>
       exists o p δ γ' ρ M (H : o <= n) (H' : o <= p) (L : lower <= o),
         down_env_until γ' o H' = δ /\
         C = Closure o p δ ρ M /\
         (forall W, lazy_scoped β A W ->
           exists T, EvalComp (q .: γ') ((o W↓ W) .: ρ) M T /\
             lazy_scoped β B (o T↓ T))
   end) C.

Lemma lazy_scoped_from_LR {lower n k} (A : Ty n k) (C : Clos k)
    (γ : attrs n) (L : lower <= n) :
  LR A C lower γ <-> lazy_scoped (down_env_until γ lower L) A C.
Proof.
  revert C. induction A; intro C; cbn [LR lazy_scoped].
  - reflexivity.
  - split.
    + intros (o & p & δ & γ' & ρ & M & H' & H & Lo & Hδ & Hδ' & -> & Heval).
      exists o, p, δ, γ', ρ, M, H, H', Lo.
      repeat split; try assumption.
      intros I HI. replace L with I in HI by apply le_unique.
      destruct (Heval I HI) as (T & HT & HR).
      exists T. split; [exact HT | now apply IHA].
    + intros (o & p & δ & γ' & ρ & M & H & H' & Lo & Hδ & Hδ' & -> & Heval).
      exists o, p, δ, γ', ρ, M, H', H, Lo.
      repeat split; try assumption.
      intros I HI. replace I with L in HI by apply le_unique.
      destruct (Heval L HI) as (T & HT & HR).
      exists T. split; [exact HT | now apply IHA].
  - setoid_rewrite IHA1. setoid_rewrite IHA2. reflexivity.
  - setoid_rewrite IHA1. setoid_rewrite IHA2. reflexivity.
  - setoid_rewrite IHA1. setoid_rewrite IHA2. reflexivity.
  - setoid_rewrite IHA. reflexivity.
Qed.

Lemma lazy_scoped_bound {lower n k} (β : attrs lower)
    (A : Ty n k) (C : Clos k) :
  lazy_scoped β A C -> well_scoped_clos C n.
Proof.
  revert C. induction A; intros C HR; cbn [lazy_scoped] in HR.
  - now subst C.
  - destruct HR as (o & p & δ & γ' & ρ & M & H & H' & L & _ & _ & -> & _).
    exact H.
  - destruct HR as (W1 & W2 & -> & H1 & H2). simpl; split; auto.
  - destruct HR as (W & [[-> HW] | [-> HW]]); simpl; auto.
  - destruct HR as (o & p & δ & γ' & ρ & M & H & H' & L & _ & -> & _).
    exact H.
  - destruct HR as (W & -> & HW). simpl; auto.
Qed.

Lemma lazy_scoped_present {lower n} (β : attrs lower) (A : ValTy n) W :
  lazy_scoped β A W -> W <> Absent.
Proof.
  assert (H : forall k (T : Ty n k) C, lazy_scoped β T C ->
      match k as k return Clos k -> Prop with
      | ValFlag => fun V => V <> Absent
      | CompFlag => fun _ => True
      end C).
  { destruct T; cbn [lazy_scoped]; try tauto; intros C HR ->; firstorder discriminate. }
  apply (H ValFlag A W).
Qed.

(* Type annotations agree at every suffix retained by both scopes.
   The two directions are proved together for function arguments. *)
Lemma lazy_scoped_map {lower n m k} (β : attrs lower)
    (f : attrs n -> attrs m) (A : Ty n k)
    (Ln : lower <= n) (Lm : lower <= m)
    (Hmap : forall γ o (Hn : o <= n) (Hm : o <= m),
      down_env_until (f γ) o Hm = down_env_until γ o Hn) :
  (forall C, lazy_scoped β A C ->
    lazy_scoped β (map_Ty f A) (down_clos m C)) /\
  (forall C, lazy_scoped β (map_Ty f A) C ->
    lazy_scoped β A (down_clos n C)).
Proof.
  induction A; cbn [map_Ty lazy_scoped]; split; intros C HR;
    unfold down_comp, down_value in *.
  - now subst C.
  - now subst C.
  - destruct HR as (o & p & δ & γ' & ρ & M & H & H' & L & Hδ & Hδ' & -> & Heval).
    pose proof (Nat.le_min_l o m) as Ho.
    exists (Nat.min o m), p, (down_env_until δ _ (min_le o m)), γ', ρ, M,
      (Nat.le_min_r o m), (Nat.le_trans _ _ _ Ho H'), (Nat.min_glb _ _ _ L Lm).
    repeat split.
    + rewrite (Hmap _ _ (Nat.le_trans _ _ _ Ho H)).
      subst δ. symmetry. apply lazy_down_compose.
    + rewrite <- Hδ'. symmetry. apply lazy_down_compose.
    + intros I HI. rewrite (Hmap _ _ Ln I) in HI.
      destruct (Heval Ln HI) as (T & HE & HT).
      exists T. split; [exact HE |].
      rewrite <- lazy_clos_down_compose. now apply IHA.
  - destruct HR as (o & p & δ & γ' & ρ & M & H & H' & L & Hδ & Hδ' & -> & Heval).
    pose proof (Nat.le_min_l o n) as Ho.
    exists (Nat.min o n), p, (down_env_until δ _ (min_le o n)), γ', ρ, M,
      (Nat.le_min_r o n), (Nat.le_trans _ _ _ Ho H'), (Nat.min_glb _ _ _ L Ln).
    repeat split.
    + rewrite <- (Hmap _ _ _ (Nat.le_trans _ _ _ Ho H)).
      subst δ. symmetry. apply lazy_down_compose.
    + rewrite <- Hδ'. symmetry. apply lazy_down_compose.
    + intros I HI. rewrite <- (Hmap _ _ I Lm) in HI.
      destruct (Heval Lm HI) as (T & HE & HT).
      exists T. split; [exact HE |].
      rewrite <- lazy_clos_down_compose. now apply IHA.
  - destruct HR as (W1 & W2 & -> & H1 & H2).
    exists (down_clos m W1), (down_clos m W2). repeat split; [now apply IHA1 | now apply IHA2].
  - destruct HR as (W1 & W2 & -> & H1 & H2).
    exists (down_clos n W1), (down_clos n W2). repeat split; [now apply IHA1 | now apply IHA2].
  - destruct HR as (W & [[-> HW] | [-> HW]]); exists (down_clos m W);
      [left | right]; split; try reflexivity; [now apply IHA1 | now apply IHA2].
  - destruct HR as (W & [[-> HW] | [-> HW]]); exists (down_clos n W);
      [left | right]; split; try reflexivity; [now apply IHA1 | now apply IHA2].
  - destruct HR as (o & p & δ & γ' & ρ & M & H & H' & L & Hδ & -> & Heval).
    pose proof (Nat.le_min_l o m) as Ho.
    exists (Nat.min o m), p, (down_env_until δ _ (min_le o m)), γ', ρ, M,
      (Nat.le_min_r o m), (Nat.le_trans _ _ _ Ho H'), (Nat.min_glb _ _ _ L Lm).
    repeat split.
    + subst δ. symmetry. apply lazy_down_compose.
    + intros W HW.
      destruct (Heval _ (proj2 IHA1 W HW)) as (T & HE & HT).
      exists T. split.
      * rewrite (lazy_clos_down_argument W o n m H) in HE.
        -- exact HE.
        -- now apply (lazy_scoped_bound β (map_Ty f A1)).
      * rewrite <- lazy_clos_down_compose. now apply IHA2.
  - destruct HR as (o & p & δ & γ' & ρ & M & H & H' & L & Hδ & -> & Heval).
    pose proof (Nat.le_min_l o n) as Ho.
    exists (Nat.min o n), p, (down_env_until δ _ (min_le o n)), γ', ρ, M,
      (Nat.le_min_r o n), (Nat.le_trans _ _ _ Ho H'), (Nat.min_glb _ _ _ L Ln).
    repeat split.
    + subst δ. symmetry. apply lazy_down_compose.
    + intros W HW.
      destruct (Heval _ (proj1 IHA1 W HW)) as (T & HE & HT).
      exists T. split.
      * rewrite (lazy_clos_down_argument W o m n H) in HE.
        -- exact HE.
        -- now apply (lazy_scoped_bound β A1).
      * rewrite <- lazy_clos_down_compose. now apply IHA2.
  - destruct HR as (W & -> & HW).
    exists (down_clos m W). split; [reflexivity | now apply IHA].
  - destruct HR as (W & -> & HW).
    exists (down_clos n W). split; [reflexivity | now apply IHA].
Qed.

Lemma lazy_scoped_up {lower n k} (β : attrs lower) (A : Ty n k)
    (L : lower <= n) q C :
  lazy_scoped β A C -> lazy_scoped β (up_Ty q A) C.
Proof.
  intro HC.
  pose proof (lazy_scoped_map β (fun γ => q .: γ) A L
    (Nat.le_trans _ _ _ L (Nat.le_succ_diag_r n))) as Hmap.
  specialize (Hmap (fun γ o H H' => lazy_down_step (q .: γ) o H H')).
  destruct Hmap as [Hup _].
  specialize (Hup C HC).
  pose proof (lazy_clos_down_same C n (lazy_scoped_bound β A C HC)) as Hsame.
  assert (Hlift : down_clos (S n) C = C).
  { rewrite <- Hsame at 1.
    rewrite lazy_clos_down_compose, Nat.min_l by lia.
    exact Hsame. }
  now rewrite Hlift in Hup.
Qed.

Lemma lazy_scoped_down {lower n k} (β : attrs lower) (A : Ty n k)
    m (H : m <= n) (L : lower <= m) C :
  lazy_scoped β A C ->
  lazy_scoped β (down_ty_until A m H) (down_clos m C).
Proof.
  rewrite lazy_map_down.
  apply (lazy_scoped_map β _ A (Nat.le_trans _ _ _ L H) L).
  intros. apply lazy_down_compose.
Qed.

Definition lazy_env_ok {lower n} (β : attrs lower) (L : lower <= n)
    (ρ : env n) (Γ : context n) : Prop :=
  forall i, pad_with Strict β n L i <> Lazy -> lazy_scoped β (Γ i) (ρ i).

Lemma lazy_env_cons {lower n} (β : attrs lower) (L : lower <= n)
    (L' : lower <= S n) (ρ : env n) (Γ : context n) A W :
  lazy_env_ok β L ρ Γ ->
  lazy_scoped β A W ->
  lazy_env_ok β L' (W .: ρ) (ctx_insert A Γ).
Proof.
  intros Hρ HW. unfold lazy_env_ok, ctx_insert.
  rewrite (lazy_pad_step _ _ _ L).
  intros [i|] Hi; cbn [scons] in *; apply (lazy_scoped_up β _ L Lazy).
  - now apply Hρ.
  - exact HW.
Qed.

Lemma lazy_compare_cons {lower n} (β : attrs lower) (L : lower <= n)
    (L' : lower <= S n) q (γ : attrs n) :
  (pad_with Strict β n L) γS<= γ ->
  (pad_with Strict β (S n) L') γS<= (q .: γ).
Proof.
  rewrite (lazy_pad_step _ _ _ L).
  intros H [i|]; [apply H | exact I].
Qed.

Lemma lazy_compare_add {n} (φ γ1 γ2 : attrs n) :
  φ γS<= (γ1 γ+ γ2) -> φ γS<= γ1 /\ φ γS<= γ2.
Proof.
  intro H. split; intro i; specialize (H i);
    unfold attr_vector_add in H;
    destruct (φ i), (γ1 i), (γ2 i); simpl in *; tauto.
Qed.

Lemma lazy_compare_sub {n} (φ γ γ' : attrs n) :
  φ γS<= γ -> γ γ<= γ' -> φ γS<= γ'.
Proof.
  intros H H' i. specialize (H i). specialize (H' i).
  destruct (φ i), (γ i), (γ' i); simpl in *; tauto.
Qed.

Lemma lazy_fin_eqb_step {n} (i j : fin n) :
  @fin_eqb (S n) (Some i) (Some j) = fin_eqb i j.
Proof.
  change ((if fin_eqb i j as b return (fin_eqb i j = b -> bool)
           then fun _ => true else fun _ => false) eq_refl = fin_eqb i j).
  now destruct (fin_eqb i j).
Qed.

Lemma lazy_fin_eqb {n} (i j : fin n) : fin_eqb i j = true -> i = j.
Proof.
  induction n as [|n IH]; [contradiction |].
  destruct i as [i|], j as [j|]; cbn [fin_eqb]; try discriminate; try reflexivity.
  rewrite lazy_fin_eqb_step. intro E. f_equal. now apply IH.
Qed.

Lemma lazy_fin_eqb_refl {n} (i : fin n) : fin_eqb i i = true.
Proof.
  induction n as [|n IH]; [contradiction |].
  destruct i as [i|]; [now rewrite lazy_fin_eqb_step | reflexivity].
Qed.

Definition lazy_sem_wt {n k} (γ : attrs n) (Γ : context n) (A : Ty n k)
    (eval : env n -> Clos k -> Prop) : Prop :=
  forall lower (β : attrs lower) (L : lower <= n) ρ,
    lazy_env_ok β L ρ Γ ->
    (pad_with Strict β n L) γS<= γ ->
    exists C, eval ρ C /\ lazy_scoped β A C.

Lemma lazy_fundamental n (γ : attrs n) (Γ : context n) :
  (forall V A, VWt γ Γ V A ->
    lazy_sem_wt γ Γ A (fun ρ => EvalVal γ ρ V)) /\
  (forall M B, CWt γ Γ M B ->
    lazy_sem_wt γ Γ B (fun ρ => EvalComp γ ρ M)).
Proof.
  apply (Wt_mutual
    (fun n γ Γ V A _ => lazy_sem_wt γ Γ A (fun ρ => EvalVal γ ρ V))
    (fun n γ Γ M B _ => lazy_sem_wt γ Γ B (fun ρ => EvalComp γ ρ M))).
  - intros m φ Δ i A -> -> lower β L ρ Hρ Hcmp.
    assert (Hstrict : (lazyvector <- Strict @ i) i = Strict).
    { unfold env_set. now rewrite lazy_fin_eqb_refl. }
    assert (HW : lazy_scoped β (Δ i) (ρ i)).
    { apply Hρ. specialize (Hcmp i). rewrite Hstrict in Hcmp.
      intro H. rewrite H in Hcmp. exact Hcmp. }
    exists (ρ i). split; [|exact HW].
    apply E_Var; [reflexivity | reflexivity | now apply (lazy_scoped_present β (Δ i))].
  - intros m φ Δ -> lower β L ρ Hρ Hcmp.
    exists Unit. split; [apply E_Unit |]; reflexivity.
  - intros m φ Δ γ' M B Hwt IH -> lower β L ρ Hρ Hcmp.
    exists (Thunk m m γ' ρ M). split; [apply E_Thunk; reflexivity |].
    exists m, m, γ', γ', ρ, M, (le_n m), (le_n m), L.
    rewrite !lazy_down_same. repeat split.
    intros I H. replace I with L in H by apply le_unique.
    destruct (IH lower β L ρ Hρ (proj2 (lazy_pad_compare _ _ _ _ _) H))
      as (T & HT & HR).
    exists T. split; [exact HT |].
    unfold down_comp. rewrite lazy_clos_down_same; [exact HR |].
    now apply (lazy_scoped_bound β B).
  - intros m φ Δ γ1 γ2 V1 V2 A1 A2 H1 IH1 H2 IH2 -> lower β L ρ Hρ Hcmp.
    apply lazy_compare_add in Hcmp as [Hcmp1 Hcmp2].
    destruct (IH1 lower β L ρ Hρ Hcmp1) as (W1 & HW1 & HR1).
    destruct (IH2 lower β L ρ Hρ Hcmp2) as (W2 & HW2 & HR2).
    exists (Pair W1 W2). split.
    + eapply E_VPair; eauto.
    + exists W1, W2. auto.
  - intros m φ Δ V A1 A2 Hwt IH lower β L ρ Hρ Hcmp.
    destruct (IH lower β L ρ Hρ Hcmp) as (W & HW & HR).
    exists (Inl W). split; [now apply E_Inl |].
    exists W. left. auto.
  - intros m φ Δ V A1 A2 Hwt IH lower β L ρ Hρ Hcmp.
    destruct (IH lower β L ρ Hρ Hcmp) as (W & HW & HR).
    exists (Inr W). split; [now apply E_Inr |].
    exists W. right. auto.
  - intros m φ Δ V A Hwt IH lower β L ρ Hρ Hcmp.
    destruct (IH lower β L ρ Hρ Hcmp) as (W & HW & HR).
    exists (Return W). split; [now apply E_Ret |].
    exists W. auto.
  - intros m φ Δ q M N A B B' γ1 γ2 H1 IH1 H2 IH2 -> -> lower β L ρ Hρ Hcmp.
    apply lazy_compare_add in Hcmp as [Hcmp1 Hcmp2].
    destruct (IH1 lower β L ρ Hρ Hcmp1) as (R & HR & W & -> & HW).
    pose proof (lazy_env_cons β L (le_S _ _ L) ρ Δ A W Hρ HW) as Hρ'.
    destruct (IH2 lower β _ _ Hρ' (lazy_compare_cons β L _ q γ2 Hcmp2))
      as (T & HT & HRT).
    exists (m T↓ T). split.
    + eapply E_LetRet; eauto.
    + now apply lazy_scoped_down.
  - intros m φ Δ V B γ1 γ2 Hwt IH -> lower β L ρ Hρ Hcmp.
    apply lazy_compare_add in Hcmp as [Hcmp1 Hcmp2].
    destruct (IH lower β L ρ Hρ Hcmp1)
      as (W & HW & o & p & δ & γ' & ρ' & M & H & H' & Lo & Hδ & Hδ' & -> & Heval).
    destruct (Heval L (proj1 (lazy_pad_compare _ _ _ _ _) Hcmp2))
      as (T & HT & HRT).
    exists (o T↓ T). split; [|exact HRT].
    eapply E_Force; eauto.
  - intros m φ Δ V M B γ1 γ2 H1 IH1 H2 IH2 -> lower β L ρ Hρ Hcmp.
    apply lazy_compare_add in Hcmp as [Hcmp1 Hcmp2].
    destruct (IH1 lower β L ρ Hρ Hcmp1) as (W & HW & ->).
    destruct (IH2 lower β L ρ Hρ Hcmp2) as (T & HT & HRT).
    exists T. split; [|exact HRT].
    eapply E_Seq; eauto.
  - intros m φ Δ q1 q2 V M γ1 γ2 A1 A2 B B' H1 IH1 H2 IH2 -> -> lower β L ρ Hρ Hcmp.
    apply lazy_compare_add in Hcmp as [Hcmp1 Hcmp2].
    destruct (IH1 lower β L ρ Hρ Hcmp1) as (W & HW & W1 & W2 & -> & HW1 & HW2).
    pose (L' := le_S _ _ L).
    pose proof (lazy_scoped_up β A1 L Lazy W1 HW1) as HW1'.
    pose proof (lazy_env_cons β L L' ρ Δ A2 W2 Hρ HW2) as Hρ'.
    pose proof (lazy_env_cons β L' (le_S _ _ L') _ _ _ W1 Hρ' HW1') as Hρ''.
    pose proof (lazy_compare_cons β L L' q2 γ2 Hcmp2) as Hcmp'.
    destruct (IH2 lower β _ _ Hρ'' (lazy_compare_cons β L' _ q1 _ Hcmp'))
      as (T & HT & HRT).
    exists (m T↓ T). split.
    + eapply E_Split; eauto.
    + now apply lazy_scoped_down.
  - intros m φ Δ q1 q2 V M1 M2 γ1 γ2 A1 A2 B B1 B2
      Hwt IH H1 IH1 H2 IH2 -> -> HB lower β L ρ Hρ Hcmp.
    apply lazy_compare_add in Hcmp as [Hcmp1 Hcmp2].
    destruct (IH lower β L ρ Hρ Hcmp1) as (W & HW & W' & [[-> HW'] | [-> HW']]).
    + pose proof (lazy_env_cons β L (le_S _ _ L) ρ Δ A1 W' Hρ HW') as Hρ'.
      destruct (IH1 lower β _ _ Hρ' (lazy_compare_cons β L _ q1 γ2 Hcmp2))
        as (T & HT & HRT).
      exists (m T↓ T). split.
      * eapply E_Casel; eauto.
      * now apply lazy_scoped_down.
    + pose proof (lazy_env_cons β L (le_S _ _ L) ρ Δ A2 W' Hρ HW') as Hρ'.
      destruct (IH2 lower β _ _ Hρ' (lazy_compare_cons β L _ q2 γ2 Hcmp2))
        as (T & HT & HRT).
      exists (m T↓ T). split.
      * eapply E_Caser; eauto.
      * rewrite HB. now apply lazy_scoped_down.
  - intros m φ Δ q M A B B' Hwt IH -> lower β L ρ Hρ Hcmp.
    exists (Closure m m φ ρ M). split; [apply E_Abs |].
    exists m, m, φ, φ, ρ, M, (le_n m), (le_n m), L.
    rewrite lazy_down_same. repeat split.
    intros W HW.
    pose proof (lazy_env_cons β L (le_S _ _ L) ρ Δ A W Hρ HW) as Hρ'.
    destruct (IH lower β _ _ Hρ' (lazy_compare_cons β L _ q φ Hcmp))
      as (T & HT & HRT).
    exists T. split.
    + unfold down_value. rewrite lazy_clos_down_same; [exact HT |].
      now apply (lazy_scoped_bound β A).
    + now apply lazy_scoped_down.
  - intros m φ Δ M q V γ1 γ2 A B H1 IH1 H2 IH2 -> lower β L ρ Hρ Hcmp.
    apply lazy_compare_add in Hcmp as [Hcmp1 Hcmp2].
    destruct (IH1 lower β L ρ Hρ Hcmp1)
      as (F & HF & o & p & δ & γ' & ρ' & N & H & H' & Lo & Hδ & -> & Heval).
    destruct (IH2 lower β L ρ Hρ Hcmp2) as (W & HW & HRW).
    destruct (Heval W HRW) as (T & HT & HRT).
    exists (o T↓ T). split; [|exact HRT].
    eapply E_AppAbs; eauto.
  - intros m φ Δ M γ' B Hwt IH Hsub lower β L ρ Hρ Hcmp.
    destruct (IH lower β L ρ Hρ (lazy_compare_sub _ _ _ Hcmp Hsub))
      as (T & HT & HRT).
    exists T. split; [|exact HRT].
    eapply E_CSub; eauto.
Qed.

Theorem lazy_soundness : forall n (γ : attrs n) (Γ : context n) (ρ : env n),
  ρ_ok γ ρ Γ n γ ->
  forall i, γ i = Lazy ->
  (forall V A, VWt γ Γ V A ->
    exists W, EvalVal γ (ρ <- Absent @ i) V W) /\
  (forall M B, CWt γ Γ M B ->
    exists T, EvalComp γ (ρ <- Absent @ i) M T).
Proof.
  intros n γ Γ ρ Hρ i Hi.
  pose (L := le_n n).
  assert (Henv : lazy_env_ok γ L (ρ <- Absent @ i) Γ).
  { unfold lazy_env_ok. rewrite lazy_pad_same.
    intros j Hj.
    unfold env_set.
    destruct (fin_eqb i j) eqn:Hsame.
    - apply lazy_fin_eqb in Hsame. subst j. contradiction.
    - pose proof (Hρ j Hj) as Hentry.
      apply (proj1 (lazy_scoped_from_LR (Γ j) (ρ j) γ L)) in Hentry.
      now rewrite lazy_down_same in Hentry. }
  assert (Hcmp : (pad_with Strict γ n L) γS<= γ).
  { rewrite lazy_pad_same. intro j. now destruct (γ j). }
  destruct (lazy_fundamental n γ Γ) as [HV HM].
  split.
  - intros V A Hwt.
    destruct (HV V A Hwt n γ L _ Henv Hcmp) as (W & HW & _).
    now exists W.
  - intros M B Hwt.
    destruct (HM M B Hwt n γ L _ Henv Hcmp) as (T & HT & _).
    now exists T.
Qed.
