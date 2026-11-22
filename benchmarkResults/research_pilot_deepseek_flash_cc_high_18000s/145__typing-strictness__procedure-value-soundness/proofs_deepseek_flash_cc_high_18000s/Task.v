From strictness.cbpv Require Import semtyping.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import Arith.
Require Import Coq.Logic.Eqdep_dec.
Require Import Psatz.

Lemma eq_rect_r_fun_apply : forall {A : Type} {x y : nat} (f : fin x -> A) (e : y = x) (z : fin y),
  eq_rect_r (fun n => fin n -> A) f e z = f (eq_rect y (fun n => fin n) z x e).
Proof. intros. destruct e. reflexivity. Qed.

Lemma eq_rect_fin_refl : forall (n : nat) (z : fin n) (e : n = n),
  eq_rect n (fun m => fin m) z n e = z.
Proof. intros. rewrite (UIP_dec Nat.eq_dec e eq_refl). reflexivity. Qed.

Definition fin_nat_val : forall {n : nat}, fin n -> nat :=
  fix f (n : nat) {struct n} : fin n -> nat :=
    match n as n0 return (fin n0 -> nat) with
    | 0 => fun x => False_rect nat x
    | S m => fun x => match x with
                      | None => 0
                      | Some y => S (f m y)
                      end
    end.

Lemma fin_nat_val_eq_rect : forall {a b : nat} (e : a = b) (x : fin a),
  fin_nat_val (eq_rect a (fun t => fin t) x b e) = fin_nat_val x.
Proof. intros. destruct e. reflexivity. Qed.

Lemma fin_nat_val_shift_p : forall k {n : nat} (x : fin n),
  fin_nat_val (shift_p k x) = k + fin_nat_val x.
Proof.
  induction k; intros n x.
  - reflexivity.
  - simpl. rewrite IHk. reflexivity.
Qed.

Lemma fin_nat_val_inj : forall n (x y : fin n), fin_nat_val x = fin_nat_val y -> x = y.
Proof.
  induction n as [|n IH]; intros x y H.
  - destruct x.
  - destruct x as [x'|], y as [y'|]; cbn [fin_nat_val] in H.
    + f_equal. apply IH. injection H. auto.
    + discriminate.
    + discriminate.
    + reflexivity.
Qed.

Lemma fin_nat_val_Some : forall {n : nat} (x : fin n),
  @fin_nat_val (S n) (Some x) = S (@fin_nat_val n x).
Proof. reflexivity. Qed.

Lemma fin_sub_diag_cast : forall (n : nat) (i : fin n) (s : n - n + n = n),
  eq_rect (n - n + n) (fun k => fin k) (shift_p (n - n) i) n s = i.
Proof.
  intros n i s.
  remember (n - n) as k eqn:Hk.
  rewrite Nat.sub_diag in Hk.
  subst k.
  cbn [Nat.add shift_p].
  change (eq_rect n (fun m => fin m) i n s = i).
  apply eq_rect_fin_refl.
Qed.

Lemma down_env_until_id : forall {A : Type} {n : nat} (gamma : fin n -> A) (H : n <= n),
  down_env_until gamma n H = gamma.
Proof.
  intros A n gamma H.
  unfold down_env_until, down_env_until', ren_env.
  cbn [Nat.sub].
  apply functional_extensionality. intro i.
  rewrite eq_rect_r_fun_apply.
  rewrite fin_sub_diag_cast.
  reflexivity.
Qed.

Lemma le_irrel : forall (a b : nat) (H1 H2 : a <= b), H1 = H2.
Proof. intros. apply le_unique. Qed.

Lemma down_env_until_proof_irrel : forall {A : Type} {n : nat} (gamma : fin n -> A) (m : nat)
  (H1 H2 : m <= n), down_env_until gamma m H1 = down_env_until gamma m H2.
Proof. intros. rewrite (le_irrel m n H1 H2). reflexivity. Qed.

Lemma down_env_until_comp : forall {A : Type} {n m : nat} (gamma : fin n -> A) (H : m <= n)
   (j : nat) (Hj : j <= m),
   down_env_until (down_env_until gamma m H) j Hj = down_env_until gamma j (Nat.le_trans j m n Hj H).
Proof.
  intros A n m gamma H j Hj.
  apply functional_extensionality. intro i.
  unfold down_env_until, down_env_until', ren_env.
  cbn [Nat.sub].
  rewrite !eq_rect_r_fun_apply.
  cbn [Nat.sub].
  f_equal.
  apply fin_nat_val_inj.
  repeat (rewrite fin_nat_val_shift_p || rewrite fin_nat_val_eq_rect).
  cbn [Nat.add].
  lia.
Qed.

Lemma down_env_until_cons_aux : forall {n : nat} (q : attr) (gamma : fin n -> attr)
  (mo : nat) (Hn : mo <= n) (i : fin mo) (s : (S n - mo) + mo = S n)
  (s' : (n - mo) + mo = n),
  (q .: gamma) (eq_rect ((S n - mo) + mo) (fun t => fin t) (shift_p (S n - mo) i) (S n) s)
  = gamma (eq_rect ((n - mo) + mo) (fun t => fin t) (shift_p (n - mo) i) n s').
Proof.
  intros n q gamma mo Hn i s s'.
  set (J := eq_rect ((S n - mo) + mo) (fun t => fin t) (shift_p (S n - mo) i) (S n) s).
  set (J' := eq_rect ((n - mo) + mo) (fun t => fin t) (shift_p (n - mo) i) n s').
  assert (HJ : J = Some J').
  { apply fin_nat_val_inj.
    unfold J, J'.
    rewrite fin_nat_val_Some.
    repeat (rewrite fin_nat_val_shift_p || rewrite fin_nat_val_eq_rect).
    cbn [Nat.add].
    lia. }
  rewrite HJ.
  reflexivity.
Qed.

Lemma down_env_until_cons : forall {n : nat} (q : attr) (gamma : fin n -> attr)
  (mo : nat) (Hn : mo <= n) (H : mo <= S n),
  down_env_until (q .: gamma) mo H = down_env_until gamma mo Hn.
Proof.
  intros n q gamma mo Hn H.
  apply functional_extensionality. intro i.
  unfold down_env_until, down_env_until', ren_env.
  cbn [Nat.sub].
  rewrite !eq_rect_r_fun_apply.
  apply down_env_until_cons_aux.
  exact Hn.
Qed.

Lemma attrs_eq_rect_apply : forall {a b : nat} (e : a = b) (f : attrs a) (z : fin b),
  (eq_rect a (fun x => attrs x) f b e) z = f (eq_rect b (fun t => fin t) z a (eq_sym e)).
Proof. intros. destruct e. reflexivity. Qed.

Lemma down_env_until_cast : forall {A : Type} {n : nat} (gamma : fin n -> A) a b (e : a = b)
  (Ha : a <= n) (Hb : b <= n) (z : fin b),
  down_env_until gamma a Ha (eq_rect b (fun t => fin t) z a (eq_sym e)) = down_env_until gamma b Hb z.
Proof.
  intros A n gamma a b e Ha Hb z.
  unfold down_env_until, down_env_until', ren_env.
  cbn [Nat.sub].
  rewrite !eq_rect_r_fun_apply.
  cbn [Nat.sub].
  f_equal.
  apply fin_nat_val_inj.
  repeat (rewrite fin_nat_val_shift_p || rewrite fin_nat_val_eq_rect).
  cbn [Nat.add].
  lia.
Qed.

Lemma Thunk_eq_gen : forall a b mInner (gamma1 : attrs a) (gamma2 : attrs b)
  (rho : fin mInner -> Clos ValFlag) M (e : a = b),
  eq_rect a (fun x => attrs x) gamma1 b e = gamma2 ->
  Thunk a mInner gamma1 rho M = Thunk b mInner gamma2 rho M.
Proof.
  intros a b mInner gamma1 gamma2 rho M e h.
  destruct e. cbn in h. rewrite h. reflexivity.
Qed.

Lemma min_min_absorb : forall n j k', j <= k' -> Nat.min (Nat.min n k') j = Nat.min n j.
Proof. intros. rewrite <- Nat.min_assoc. rewrite (Nat.min_r k' j H). reflexivity. Qed.

Lemma Closure_eq_gen : forall a b mInner (gamma1 : attrs a) (gamma2 : attrs b)
  (rho : fin mInner -> Clos ValFlag) M (e : a = b),
  eq_rect a (fun x => attrs x) gamma1 b e = gamma2 ->
  Closure a mInner gamma1 rho M = Closure b mInner gamma2 rho M.
Proof.
  intros a b mInner gamma1 gamma2 rho M e h.
  destruct e. cbn in h. rewrite h. reflexivity.
Qed.

Lemma down_clos_idem : forall (k : Kind) (W : Clos k) j k', j <= k' ->
  @down_clos k j (@down_clos k k' W) = @down_clos k j W.
Proof.
  intros k W.
  induction W using Clos_ind; intros j k' Hjk; simpl.
  - reflexivity.
  - reflexivity.
  - eapply Thunk_eq_gen with (e := min_min_absorb mOuter j k' Hjk).
    apply functional_extensionality. intro z.
    rewrite attrs_eq_rect_apply.
    rewrite down_env_until_comp.
    apply down_env_until_cast.
  - (* Pair *)
    f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - (* Closure *)
    eapply Closure_eq_gen with (e := min_min_absorb mOuter j k' Hjk).
    apply functional_extensionality. intro z.
    rewrite attrs_eq_rect_apply.
    rewrite down_env_until_comp.
    apply down_env_until_cast.
Qed.

Definition not_absent (k : Kind) (W : Clos k) : Prop :=
  (match k return Clos k -> Prop with
  | ValFlag => fun W => W <> Absent
  | CompFlag => fun _ => True
  end) W.

Lemma LR_not_absent : forall n (k : Kind) (A : Ty n k) (W : Clos k),
  LR A W -> not_absent k W.
Proof.
  intros n k A W.
  induction A using Ty_ind; intros HLR; cbn [not_absent].
  - cbn [LR] in HLR. subst W. intro H. discriminate H.
  - destruct HLR as (mo & mi & gs & gi & r & M & Hi & Hn & H1 & H2 & HC & T & HE & HL).
    subst W. intro H. discriminate H.
  - destruct HLR as (W1 & W2 & HC & H1 & H2). subst W. intro H. discriminate H.
  - destruct HLR as (W' & [[HC H1]|[HC H1]]); subst W; intro H; discriminate H.
  - exact I.
  - exact I.
Qed.

Lemma min_min_absorb' : forall n j k', j <= k' -> Nat.min (Nat.min n j) k' = Nat.min n j.
Proof. intros. rewrite <- Nat.min_assoc. rewrite (Nat.min_l j k' H). reflexivity. Qed.

Lemma down_clos_swap : forall (k : Kind) (W : Clos k) j k', j <= k' ->
  @down_clos k k' (@down_clos k j W) = @down_clos k j W.
Proof.
  intros k W.
  induction W using Clos_ind; intros j k' Hjk; simpl.
  - reflexivity.
  - reflexivity.
  - eapply Thunk_eq_gen with (e := min_min_absorb' mOuter j k' Hjk).
    apply functional_extensionality. intro z.
    rewrite attrs_eq_rect_apply.
    rewrite down_env_until_comp.
    apply down_env_until_cast.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - eapply Closure_eq_gen with (e := min_min_absorb' mOuter j k' Hjk).
    apply functional_extensionality. intro z.
    rewrite attrs_eq_rect_apply.
    rewrite down_env_until_comp.
    apply down_env_until_cast.
Qed.

Lemma LR_down_value : forall n (k : Kind) (A : Ty n k) (W : Clos k),
  LR A W -> forall j, LR A (@down_clos k j W).
Proof.
  intros n k A.
  induction A using Ty_ind; intros W HLR j; cbn [LR] in *.
  - (* VUnit *) subst W. reflexivity.
  - (* VThunk *)
    destruct HLR as (mo & mi & gs & gi & r & M & Hi & Hn & Heq1 & Heq2 & HC & T & HE & HL).
    subst W. cbn [down_clos].
    cbn [LR].
    exists (Nat.min mo j), mi, (down_env_until gs (Nat.min mo j) (min_le mo j)), gi, r, M,
      (Nat.le_trans (Nat.min mo j) mo mi (min_le mo j) Hi),
      (Nat.le_trans (Nat.min mo j) mo n (min_le mo j) Hn).
    split.
    + rewrite <- Heq1. rewrite down_env_until_comp. reflexivity.
    + split.
      * rewrite <- Heq2. rewrite down_env_until_comp. reflexivity.
      * split.
        -- reflexivity.
        -- exists T. split; [exact HE |].
           pose proof (IHA (down_clos mo T) HL (Nat.min mo j)) as H'.
           rewrite (down_clos_idem CompFlag T (Nat.min mo j) mo (Nat.le_min_l mo j)) in H'.
           exact H'.
  - (* VProd *)
    destruct HLR as (W1 & W2 & HC & H1 & H2). subst W. cbn [down_clos]. cbn [LR].
    exists (down_clos j W1), (down_clos j W2). split.
    + reflexivity.
    + split; [apply IHA1 | apply IHA2]; assumption.
  - (* VSum *)
    destruct HLR as (W' & [[HC H1] | [HC H1]]); subst W; cbn [down_clos]; cbn [LR].
    + exists (down_clos j W'). left. split; [reflexivity | apply IHA1; assumption].
    + exists (down_clos j W'). right. split; [reflexivity | apply IHA2; assumption].
  - (* CAbs *)
    destruct HLR as (mo & mi & gs & gi & r & M & Hn & Hi & Heq & HC & HB).
    subst W. cbn [down_clos]. cbn [LR].
    exists (Nat.min mo j), mi, (down_env_until gs (Nat.min mo j) (min_le mo j)), gi, r, M,
      (Nat.le_trans (Nat.min mo j) mo n (min_le mo j) Hn),
      (Nat.le_trans (Nat.min mo j) mo mi (min_le mo j) Hi).
    split.
    + rewrite <- Heq. rewrite down_env_until_comp. reflexivity.
    + split.
      * reflexivity.
      * intros W0 HLR0.
        pose proof (IHA1 W0 HLR0 (Nat.min mo j)) as HLR0'.
        destruct (HB (down_clos (Nat.min mo j) W0) HLR0') as (T & HE & HLB).
        exists T. split.
        -- assert (HX : down_value mo (down_value (Nat.min mo j) W0) = down_value (Nat.min mo j) W0).
           { apply down_clos_swap. apply Nat.le_min_l. }
           rewrite <- HX. exact HE.
        -- pose proof (IHA2 (down_clos mo T) HLB (Nat.min mo j)) as H'.
           rewrite (down_clos_idem CompFlag T (Nat.min mo j) mo (Nat.le_min_l mo j)) in H'.
           exact H'.
  - (* CF *)
    destruct HLR as (W' & HC & H1). subst W. cbn [down_clos]. cbn [LR].
    exists (down_clos j W'). split; [reflexivity | apply IHA; assumption].
Qed.

Definition upT {n k} (q : attr) (A : Ty n k) : Ty (S n) k :=
  @map_Ty n (S n) k (fun g => q .: g) A.

Lemma LR_up_bwd : forall n (k : Kind) (A : Ty n k),
  (forall q W, LR A W -> LR (upT q A) W)
  /\ (forall q W j, LR (upT q A) W -> j <= n -> LR A (@down_clos k j W)).
Proof.
  intros n k A.
  induction A using Ty_ind.
  - (* VUnit *) cbn [upT map_Ty LR]. split.
    + intros q W H. exact H.
    + intros q W j H Hj. subst W. reflexivity.
  - (* VThunk *)
    cbn [upT map_Ty].
    destruct IHA as [IHAup IHAbwd]. split.
    + intros q W HLR. cbn [LR] in *.
      destruct HLR as (mo & mi & gs & gi & r & M & Hi & Hn & Heq1 & Heq2 & HC & T & HE & HL).
      exists mo, mi, gs, gi, r, M, Hi, (Nat.le_trans mo n (S n) Hn (Nat.le_succ_diag_r n)).
      split.
      * assert (Hc : down_env_until (q .: γ) mo (Nat.le_trans mo n (S n) Hn (Nat.le_succ_diag_r n)) = down_env_until γ mo Hn)
          by (apply down_env_until_cons).
        rewrite Hc. exact Heq1.
      * split.
        -- exact Heq2.
        -- split.
           ++ exact HC.
           ++ exists T. split; [exact HE | apply IHAup; exact HL].
    + intros q W j HLR Hj. cbn [LR] in *.
      destruct HLR as (mo & mi & gs & gi & r & M & Hi & Hn & Heq1 & Heq2 & HC & T & HE & HL).
      subst W. cbn [down_clos]. cbn [LR].
      exists (Nat.min mo j), mi, (down_env_until gs (Nat.min mo j) (min_le mo j)), gi, r, M,
        (Nat.le_trans (Nat.min mo j) mo mi (min_le mo j) Hi),
        (Nat.le_trans (Nat.min mo j) j n (Nat.le_min_r mo j) Hj).
      split.
      * rewrite <- Heq1.
        rewrite (@down_env_until_comp attr (S n) mo (q .: γ) Hn (Nat.min mo j) (min_le mo j)).
        rewrite (down_env_until_cons q γ (Nat.min mo j)
                   (Nat.le_trans (Nat.min mo j) j n (Nat.le_min_r mo j) Hj)
                   (Nat.le_trans (Nat.min mo j) mo (S n) (min_le mo j) Hn)).
        apply down_env_until_proof_irrel.
      * split.
        -- rewrite <- Heq2.
           rewrite (@down_env_until_comp attr mi mo gi Hi (Nat.min mo j) (min_le mo j)).
           apply down_env_until_proof_irrel.
        -- split.
           ++ reflexivity.
           ++ exists T. split; [exact HE |].
              pose proof (IHAbwd q (down_clos mo T) (Nat.min mo j) HL (Nat.le_trans (Nat.min mo j) j n (Nat.le_min_r mo j) Hj)) as H'.
              rewrite (down_clos_idem CompFlag T (Nat.min mo j) mo (Nat.le_min_l mo j)) in H'.
              exact H'.
  - (* VProd *)
    cbn [upT map_Ty].
    destruct IHA1 as [IH1up IH1bwd], IHA2 as [IH2up IH2bwd]. split.
    + intros q W HLR. cbn [LR] in *.
      destruct HLR as (W1 & W2 & HC & H1 & H2).
      exists W1, W2. split; [exact HC | split; [apply IH1up; exact H1 | apply IH2up; exact H2]].
    + intros q W j HLR Hj. cbn [LR] in *.
      destruct HLR as (W1 & W2 & HC & H1 & H2). subst W. cbn [down_clos]. cbn [LR].
      exists (down_clos j W1), (down_clos j W2). split.
      * reflexivity.
      * split; [apply IH1bwd with (q:=q) (j:=j) | apply IH2bwd with (q:=q) (j:=j)]; assumption.
  - (* VSum *)
    cbn [upT map_Ty].
    destruct IHA1 as [IH1up IH1bwd], IHA2 as [IH2up IH2bwd]. split.
    + intros q W HLR. cbn [LR] in *.
      destruct HLR as (W' & [[HC H1]|[HC H1]]).
      * exists W'. left. split; [exact HC | apply IH1up; exact H1].
      * exists W'. right. split; [exact HC | apply IH2up; exact H1].
    + intros q W j HLR Hj. cbn [LR] in *.
      destruct HLR as (W' & [[HC H1]|[HC H1]]); subst W; cbn [down_clos]; cbn [LR].
      * exists (down_clos j W'). left. split; [reflexivity | apply IH1bwd with (q:=q) (j:=j); assumption].
      * exists (down_clos j W'). right. split; [reflexivity | apply IH2bwd with (q:=q) (j:=j); assumption].
  - (* CAbs *)
    cbn [upT map_Ty].
    destruct IHA1 as [IH1up IH1bwd], IHA2 as [IH2up IH2bwd]. split.
    + intros qq W HLR. cbn [LR] in *.
      destruct HLR as (mo & mi & gs & gi & r & M & Hn & Hi & Heq & HC & HB).
      exists mo, mi, gs, gi, r, M, (Nat.le_trans mo n (S n) Hn (Nat.le_succ_diag_r n)), Hi.
      split; [exact Heq | split; [exact HC |]].
      intros W0 HLR0.
      pose proof (IH1bwd qq W0 mo HLR0 Hn) as HLR0'.
      destruct (HB (down_clos mo W0) HLR0') as (T & HE & HLB).
      exists T. split.
      * assert (HX : down_value mo (down_value mo W0) = down_value mo W0).
        { apply down_clos_idem. apply le_n. }
        rewrite <- HX. exact HE.
      * apply IH2up. exact HLB.
    + intros qq W j HLR Hj. cbn [LR] in *.
      destruct HLR as (mo & mi & gs & gi & r & M & Hn & Hi & Heq & HC & HB).
      subst W. cbn [down_clos]. cbn [LR].
      exists (Nat.min mo j), mi, (down_env_until gs (Nat.min mo j) (min_le mo j)), gi, r, M,
        (Nat.le_trans (Nat.min mo j) j n (Nat.le_min_r mo j) Hj),
        (Nat.le_trans (Nat.min mo j) mo mi (min_le mo j) Hi).
      split.
      * rewrite <- Heq. rewrite (@down_env_until_comp attr mi mo gi Hi (Nat.min mo j) (min_le mo j)).
        apply down_env_until_proof_irrel.
      * split.
        -- reflexivity.
        -- intros W0 HLR0.
           pose proof (IH1up qq W0 HLR0) as HW0.
           pose proof (LR_down_value (S n) ValFlag (upT qq A1) W0 HW0 (Nat.min mo j)) as HW0'.
           destruct (HB (down_clos (Nat.min mo j) W0) HW0') as (T & HE & HLB).
           exists T. split.
           ++ assert (HX : down_value mo (down_value (Nat.min mo j) W0) = down_value (Nat.min mo j) W0).
              { apply down_clos_swap. apply Nat.le_min_l. }
              rewrite <- HX. exact HE.
           ++ pose proof (IH2bwd qq (down_clos mo T) (Nat.min mo j) HLB (Nat.le_trans (Nat.min mo j) j n (Nat.le_min_r mo j) Hj)) as H'.
              rewrite (down_clos_idem CompFlag T (Nat.min mo j) mo (Nat.le_min_l mo j)) in H'.
              exact H'.
  - (* CF *)
    cbn [upT map_Ty].
    destruct IHA as [IHAup IHAbwd]. split.
    + intros q W HLR. cbn [LR] in *.
      destruct HLR as (W' & HC & H1).
      exists W'. split; [exact HC | apply IHAup; exact H1].
    + intros q W j HLR Hj. cbn [LR] in *.
      destruct HLR as (W' & HC & H1). subst W. cbn [down_clos]. cbn [LR].
      exists (down_clos j W'). split.
      * reflexivity.
      * apply IHAbwd with (q:=q) (j:=j); assumption.
Qed.

Definition downT {n m k} (H : m <= n) (A : Ty n k) : Ty m k := down_ty_until A m H.

Lemma LR_down_bwd : forall n (k : Kind) (A : Ty n k),
  (forall m (H : m <= n) j W, j <= m -> LR A W -> LR (@downT n m k H A) (@down_clos k j W))
  /\ (forall m (H : m <= n) W, LR (@downT n m k H A) W -> LR A W).
Proof.
  intros n k A.
  induction A using Ty_ind.
  - (* VUnit *) cbn [downT down_ty_until LR]. split.
    + intros m H j W Hj HLR. subst W. reflexivity.
    + intros m H W HLR. subst W. reflexivity.
  - (* VThunk *)
    cbn [downT down_ty_until].
    destruct IHA as [IHAfwd IHAbwd]. split.
    + intros m H j W Hj HLR. cbn [LR] in *.
      destruct HLR as (mo & mi & gs & gi & r & M & Hi & Hn & Heq1 & Heq2 & HC & T & HE & HL).
      subst W. cbn [down_clos]. cbn [LR].
      exists (Nat.min mo j), mi, (down_env_until gs (Nat.min mo j) (min_le mo j)), gi, r, M,
        (Nat.le_trans (Nat.min mo j) mo mi (min_le mo j) Hi),
        (Nat.le_trans (Nat.min mo j) j m (Nat.le_min_r mo j) Hj).
      split.
      * rewrite (@down_env_until_comp attr n m (γ) H (Nat.min mo j) (Nat.le_trans (Nat.min mo j) j m (Nat.le_min_r mo j) Hj)).
        rewrite <- Heq1.
        rewrite (@down_env_until_comp attr n mo γ Hn (Nat.min mo j) (min_le mo j)).
        apply down_env_until_proof_irrel.
      * split.
        -- rewrite <- Heq2.
           rewrite (@down_env_until_comp attr mi mo gi Hi (Nat.min mo j) (min_le mo j)).
           apply down_env_until_proof_irrel.
        -- split.
           ++ reflexivity.
           ++ exists T. split; [exact HE |].
              pose proof (IHAfwd m H (Nat.min mo j) (down_clos mo T)
                            (Nat.le_trans (Nat.min mo j) j m (Nat.le_min_r mo j) Hj) HL) as H'.
              rewrite (down_clos_idem CompFlag T (Nat.min mo j) mo (Nat.le_min_l mo j)) in H'.
              exact H'.
    + intros m H W HLR. cbn [LR] in *.
      destruct HLR as (mo & mi & gs & gi & r & M & Hi & Hn & Heq1 & Heq2 & HC & T & HE & HL).
      exists mo, mi, gs, gi, r, M, Hi, (Nat.le_trans mo m n Hn H).
      split.
      * rewrite <- (@down_env_until_comp attr n m γ H mo Hn). exact Heq1.
      * split.
        -- exact Heq2.
        -- split.
           ++ exact HC.
           ++ exists T. split; [exact HE | apply IHAbwd with (m:=m) (H:=H); exact HL].
  - (* VProd *)
    cbn [downT down_ty_until].
    destruct IHA1 as [IH1f IH1b], IHA2 as [IH2f IH2b]. split.
    + intros m H j W Hj HLR. cbn [LR] in *.
      destruct HLR as (W1 & W2 & HC & H1 & H2). subst W. cbn [down_clos]. cbn [LR].
      exists (down_clos j W1), (down_clos j W2). split.
      * reflexivity.
      * split.
        -- apply IH1f with (m:=m) (H:=H) (j:=j); assumption.
        -- apply IH2f with (m:=m) (H:=H) (j:=j); assumption.
    + intros m H W HLR. cbn [LR] in *.
      destruct HLR as (W1 & W2 & HC & H1 & H2).
      exists W1, W2. split.
      * exact HC.
      * split; [apply IH1b with (m:=m) (H:=H); exact H1 | apply IH2b with (m:=m) (H:=H); exact H2].
  - (* VSum *)
    cbn [downT down_ty_until].
    destruct IHA1 as [IH1f IH1b], IHA2 as [IH2f IH2b]. split.
    + intros m H j W Hj HLR. cbn [LR] in *.
      destruct HLR as (W' & [[HC H1]|[HC H1]]); subst W; cbn [down_clos]; cbn [LR].
      * exists (down_clos j W'). left. split; [reflexivity | apply IH1f with (m:=m) (H:=H) (j:=j); assumption].
      * exists (down_clos j W'). right. split; [reflexivity | apply IH2f with (m:=m) (H:=H) (j:=j); assumption].
    + intros m H W HLR. cbn [LR] in *.
      destruct HLR as (W' & [[HC H1]|[HC H1]]).
      * exists W'. left. split; [exact HC | apply IH1b with (m:=m) (H:=H); exact H1].
      * exists W'. right. split; [exact HC | apply IH2b with (m:=m) (H:=H); exact H1].
  - (* CAbs *)
    cbn [downT down_ty_until].
    destruct IHA1 as [IH1f IH1b], IHA2 as [IH2f IH2b]. split.
    + intros m H j W Hj HLR. cbn [LR] in *.
      destruct HLR as (mo & mi & gs & gi & r & M & Hn & Hi & Heq & HC & HB).
      subst W. cbn [down_clos]. cbn [LR].
      exists (Nat.min mo j), mi, (down_env_until gs (Nat.min mo j) (min_le mo j)), gi, r, M,
        (Nat.le_trans (Nat.min mo j) j m (Nat.le_min_r mo j) Hj),
        (Nat.le_trans (Nat.min mo j) mo mi (min_le mo j) Hi).
      split.
      * rewrite <- Heq.
        rewrite (@down_env_until_comp attr mi mo gi Hi (Nat.min mo j) (min_le mo j)).
        apply down_env_until_proof_irrel.
      * split.
        -- reflexivity.
        -- intros W0 HLR0.
           pose proof (IH1b m H W0 HLR0) as HLR0'.
           pose proof (LR_down_value n ValFlag A1 W0 HLR0' (Nat.min mo j)) as HLR0''.
           destruct (HB (down_clos (Nat.min mo j) W0) HLR0'') as (T & HE & HLB).
           exists T. split.
           ++ assert (HX : down_value mo (down_value (Nat.min mo j) W0) = down_value (Nat.min mo j) W0).
              { apply down_clos_swap. apply Nat.le_min_l. }
              rewrite <- HX. exact HE.
           ++ pose proof (IH2f m H (Nat.min mo j) (down_clos mo T)
                           (Nat.le_trans (Nat.min mo j) j m (Nat.le_min_r mo j) Hj) HLB) as H'.
              rewrite (down_clos_idem CompFlag T (Nat.min mo j) mo (Nat.le_min_l mo j)) in H'.
              exact H'.
    + intros m H W HLR. cbn [LR] in *.
      destruct HLR as (mo & mi & gs & gi & r & M & Hn & Hi & Heq & HC & HB).
      exists mo, mi, gs, gi, r, M, (Nat.le_trans mo m n Hn H), Hi.
      split.
      * exact Heq.
      * split.
        -- exact HC.
        -- intros W0 HLR0.
           assert (HW0 : LR (@downT n m ValFlag H A1) (down_clos mo W0)).
           { apply IH1f with (j:=mo); [exact Hn | exact HLR0]. }
           destruct (HB (down_clos mo W0) HW0) as (T & HE & HLB).
           exists T. split.
           ++ assert (HX : down_value mo (down_value mo W0) = down_value mo W0).
              { apply down_clos_idem. apply le_n. }
              rewrite <- HX. exact HE.
           ++ apply IH2b with (m:=m) (H:=H); exact HLB.
  - (* CF *)
    cbn [downT down_ty_until].
    destruct IHA as [IHAf IHAb]. split.
    + intros m H j W Hj HLR. cbn [LR] in *.
      destruct HLR as (W' & HC & H1). subst W. cbn [down_clos]. cbn [LR].
      exists (down_clos j W'). split.
      * reflexivity.
      * apply IHAf with (m:=m) (H:=H) (j:=j); assumption.
    + intros m H W HLR. cbn [LR] in *.
      destruct HLR as (W' & HC & H1).
      exists W'. split.
      * exact HC.
      * apply IHAb with (m:=m) (H:=H); exact H1.
Qed.

Lemma LR_up_val : forall n (A : ValTy n) (W : Clos ValFlag),
  LR A W -> LR (up_valTy Lazy A) W.
Proof.
  intros n A W H.
  exact (proj1 (LR_up_bwd n ValFlag A) Lazy W H).
Qed.

Lemma rho_ok_cons : forall n (A : ValTy n) (Γ : context n) (W : Clos ValFlag) (ρ : env n),
  ρ_ok ρ Γ -> LR (up_valTy Lazy A) W ->
  ρ_ok (scons W ρ) (ctx_insert A Γ).
Proof.
  intros n A Γ W ρ Hok HW i.
  destruct i as [j|]; cbn [ctx_insert scons].
  - apply LR_up_val. apply Hok.
  - exact HW.
Qed.

Lemma Wt_sound_mutual : forall n (γ : attrs n) (Γ : context n),
  (forall (V : Val n) (A : ValTy n), VWt γ Γ V A -> SemVWt γ Γ V A) /\
  (forall (M : Comp n) (B : CompTy n), CWt γ Γ M B -> SemCWt γ Γ M B).
Proof.
  intros n γ Γ.
  apply (Wt_mutual
    (fun n γ Γ V A _ => SemVWt γ Γ V A)
    (fun n γ Γ M B _ => SemCWt γ Γ M B)).
  - (* T_Var *)
    intros n0 γ0 Γ0 i A e e0. unfold SemVWt. intros ρ Hρ.
    exists (ρ i). split.
    + eapply E_Var; [reflexivity | exact e0 |].
      intro Habs. exact (LR_not_absent n0 ValFlag (Γ0 i) (ρ i) (Hρ i) Habs).
    + rewrite e. apply Hρ.
  - (* T_Unit *)
    intros n0 γ0 Γ0 e. unfold SemVWt. intros ρ Hρ.
    exists Unit. split; [apply E_Unit; exact e | reflexivity].
  - (* T_Thunk *)
    intros n0 γ0 Γ0 γ' M B c IHc e. unfold SemVWt. intros ρ Hρ.
    destruct (IHc ρ Hρ) as (T & HE & HL).
    exists (Thunk n0 n0 γ' ρ M). split.
    + apply E_Thunk; exact e.
    + cbn [LR].
      exists n0, n0, γ', γ', ρ, M, (le_n n0), (le_n n0).
      split; [apply down_env_until_id | split; [apply down_env_until_id | split; [reflexivity |]]].
      exists T. split; [exact HE | apply LR_down_value with (n:=n0) (k:=CompFlag); exact HL].
  - (* T_Pair *)
    intros n0 γ0 Γ0 γ1 γ2 V1 V2 A1 A2 v IHv v0 IHv0 e. unfold SemVWt. intros ρ Hρ.
    destruct (IHv ρ Hρ) as (W1 & HE1 & HL1).
    destruct (IHv0 ρ Hρ) as (W2 & HE2 & HL2).
    exists (Pair W1 W2). split.
    + apply E_VPair with (γ1:=γ1) (γ2:=γ2); [exact HE1 | exact HE2 | exact e].
    + cbn [LR]. exists W1, W2. split; [reflexivity | split; assumption].
  - (* T_Inl *)
    intros n0 γ0 Γ0 V1 A1 A2 v IHv. unfold SemVWt. intros ρ Hρ.
    destruct (IHv ρ Hρ) as (W & HE & HL).
    exists (Inl W). split.
    + apply E_Inl; exact HE.
    + cbn [LR]. exists W. left. split; [reflexivity | exact HL].
  - (* T_Inr *)
    intros n0 γ0 Γ0 V2 A1 A2 v IHv. unfold SemVWt. intros ρ Hρ.
    destruct (IHv ρ Hρ) as (W & HE & HL).
    exists (Inr W). split.
    + apply E_Inr; exact HE.
    + cbn [LR]. exists W. right. split; [reflexivity | exact HL].
  - (* T_Ret *)
    intros n0 γ0 Γ0 V A v IHv. unfold SemCWt. intros ρ Hρ.
    destruct (IHv ρ Hρ) as (W & HE & HL).
    exists (Return W). split.
    + apply E_Ret; exact HE.
    + cbn [LR]. exists W. split; [reflexivity | exact HL].
  - (* T_Let *)
    intros n0 γ0 Γ0 q M M' A B B' γ1 γ2 c IHc c0 IHc0 e e0. unfold SemCWt. intros ρ Hρ.
    destruct (IHc ρ Hρ) as (T0 & HE & HL0). cbn [LR] in HL0.
    destruct HL0 as (W & HT0 & HLW). subst T0.
    destruct (IHc0 (scons W ρ) (rho_ok_cons n0 A Γ0 W ρ Hρ (LR_up_val n0 A W HLW))) as (T' & HE' & HL').
    rewrite e0.
    exists (down_comp n0 T'). split.
    + eapply E_LetRet; [exact HE | exact HE' | exact e | reflexivity].
    + exact (proj1 (LR_down_bwd (S n0) CompFlag B') n0 (Nat.le_succ_diag_r n0) n0 T' (le_n n0) HL').
  - (* T_Force *)
    intros n0 γ0 Γ0 V B γ1 γ2 v IHv e. unfold SemCWt. intros ρ Hρ.
    destruct (IHv ρ Hρ) as (W & HE & HL). cbn [LR] in HL.
    destruct HL as (mo & mi & gs & gi & r & M & Hi & Hn & Heq1 & Heq2 & HC & T' & HE' & HL').
    subst W.
    exists (down_comp mo T'). split.
    + eapply E_Force with (γ2 := gs) (γ2' := gi) (γ2'' := γ2) (ρ' := r) (M := M) (T' := T');
        [exact HE | exact HE' | exact Heq2 | exact Heq1 | exact e | reflexivity].
    + exact HL'.
  - (* T_Seq *)
    intros n0 γ0 Γ0 V M B γ1 γ2 v IHv c IHc e. unfold SemCWt. intros ρ Hρ.
    destruct (IHv ρ Hρ) as (W & HE & HL). cbn [LR] in HL. subst W.
    destruct (IHc ρ Hρ) as (T & HE' & HL').
    exists T. split.
    + eapply E_Seq; [exact HE | exact HE' | exact e].
    + exact HL'.
  - (* T_Split *)
    intros n0 γ0 Γ0 q1 q2 V M γ1 γ2 A1 A2 B B' v IHv c IHc e e0. unfold SemCWt. intros ρ Hρ.
    destruct (IHv ρ Hρ) as (W & HE & HL). cbn [LR] in HL.
    destruct HL as (W1 & W2 & HW & HL1 & HL2). subst W.
    set (Hok2 := rho_ok_cons n0 A2 Γ0 W2 ρ Hρ (LR_up_val n0 A2 W2 HL2)).
    set (Hok1 := rho_ok_cons (S n0) (up_valTy Lazy A1) (ctx_insert A2 Γ0) W1 (scons W2 ρ) Hok2
                              (LR_up_val (S n0) (up_valTy Lazy A1) W1 (LR_up_val n0 A1 W1 HL1))).
    destruct (IHc (scons W1 (scons W2 ρ)) Hok1) as (T' & HE' & HL').
    rewrite e0.
    exists (down_comp n0 T'). split.
    + eapply E_Split; [exact HE | exact HE' | exact e | reflexivity].
    + exact (proj1 (LR_down_bwd (S (S n0)) CompFlag B') n0 (le_succ_succ_diag_r n0) n0 T' (le_n n0) HL').
  - (* T_Case *)
    intros n0 γ0 Γ0 q1 q2 V M1 M2 γ1 γ2 A1 A2 B B1 B2 v IHv c IHc1 c0 IHc2 e e0 e1. unfold SemCWt. intros ρ Hρ.
    destruct (IHv ρ Hρ) as (W & HE & HL). cbn [LR] in HL.
    destruct HL as (W' & [[HW H1]|[HW H1]]).
    + set (Hok := rho_ok_cons n0 A1 Γ0 W' ρ Hρ (LR_up_val n0 A1 W' H1)).
      destruct (IHc1 (scons W' ρ) Hok) as (T' & HE' & HL').
      rewrite e0.
      exists (down_comp n0 T'). split.
      * rewrite HW in HE. eapply E_Casel; [exact HE | exact HE' | exact e | reflexivity].
      * exact (proj1 (LR_down_bwd (S n0) CompFlag B1) n0 (Nat.le_succ_diag_r n0) n0 T' (le_n n0) HL').
    + set (Hok := rho_ok_cons n0 A2 Γ0 W' ρ Hρ (LR_up_val n0 A2 W' H1)).
      destruct (IHc2 (scons W' ρ) Hok) as (T' & HE' & HL').
      rewrite e1.
      exists (down_comp n0 T'). split.
      * rewrite HW in HE. eapply E_Caser; [exact HE | exact HE' | exact e | reflexivity].
      * exact (proj1 (LR_down_bwd (S n0) CompFlag B2) n0 (Nat.le_succ_diag_r n0) n0 T' (le_n n0) HL').
  - (* T_Abs *)
    intros n0 γ0 Γ0 q M A B B' c IHc e. unfold SemCWt. intros ρ Hρ.
    exists (Closure n0 n0 γ0 ρ M). split.
    + apply E_Abs.
    + cbn [LR]. exists n0, n0, γ0, γ0, ρ, M, (le_n n0), (le_n n0).
      split; [apply down_env_until_id | split; [reflexivity |]].
      intros W HLRW.
      assert (Hok : ρ_ok (scons (down_value n0 W) ρ) (ctx_insert A Γ0)).
      { apply rho_ok_cons.
        - exact Hρ.
        - apply LR_down_value with (k:=ValFlag).
          apply LR_up_val. exact HLRW. }
      destruct (IHc (scons (down_value n0 W) ρ) Hok) as (T & HE & HL').
      exists T. split; [exact HE |].
      rewrite e.
      exact (proj1 (LR_down_bwd (S n0) CompFlag B') n0 (Nat.le_succ_diag_r n0) n0 T (le_n n0) HL').
  - (* T_App *)
    intros n0 γ0 Γ0 M q V γ1 γ2 A B c IHc v IHv e. unfold SemCWt. intros ρ Hρ.
    destruct (IHc ρ Hρ) as (Tf & HE & HL). cbn [LR] in HL.
    destruct HL as (mo & mi & gs & gi & r & M' & Hn & Hi & Heq & HC & HB). subst Tf.
    destruct (IHv ρ Hρ) as (W & HEV & HLW).
    destruct (HB W HLW) as (T' & HE' & HL').
    exists (down_comp mo T'). split.
    + eapply E_AppAbs with (γ' := gs) (γUp := gi) (H := Hi) (ρ' := r) (M' := M') (T' := T') (W := W);
        [exact HE | exact HEV | symmetry; exact Heq | exact HE' | exact e | reflexivity].
    + exact HL'.
  - (* T_CSub *)
    intros n0 γ0 Γ0 M γ' B c IHc a. unfold SemCWt. intros ρ Hρ.
    destruct (IHc ρ Hρ) as (T & HE & HL).
    exists T. split.
    + eapply E_CSub; [exact HE | exact a].
    + exact HL.
Qed.

Theorem CWt_sound : forall n (γ : attrs n) (Γ : context n) (M : Comp n) (B : CompTy n),
  CWt γ Γ M B -> SemCWt γ Γ M B.
Proof.
  intros n γ Γ M B H. exact (proj2 (Wt_sound_mutual n γ Γ) M B H).
Qed.

Theorem function_soundness : forall n (γ : attrs n) (Γ : context n) (ρ : env n) M A B q,
  semtyping.ρ_ok ρ Γ ->
  CWt γ Γ M (CAbs q A B) ->
  exists mOuter mInner γInner ρ' M' HInner,
  EvalComp γ ρ M (Closure mOuter mInner (down_env_until γInner mOuter HInner) ρ' M') /\
  forall W, semtyping.LR A W ->
  exists T, EvalComp (q .: γInner) ((mOuter W↓ W) .: ρ') M' T.
Proof.
  intros n γ Γ ρ M A B q Hρ HW.
  destruct (CWt_sound n γ Γ M (CAbs q A B) HW ρ Hρ) as (T & HE & HL).
  cbn [LR] in HL.
  destruct HL as (mo & mi & gs & gi & r & M' & Hn & Hi & Heq & HC & HB).
  exists mo, mi, gi, r, M', Hi.
  split.
  - rewrite HC in HE. rewrite <- Heq in HE. exact HE.
  - intros W HLW. destruct (HB W HLW) as (T' & HE' & HL'). exists T'. exact HE'.
Qed.
