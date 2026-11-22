Set Implicit Arguments.

Require Import Definitions.

Require Import Step.

Require Import Misc.

From Stdlib Require Import Lia.

Reserved Notation "[ L ] G ⊢k S <⦂ U" (at level 70).

Inductive subtykn : vars -> env -> typ -> typ -> Prop :=

| snf_vrefl : forall L G x,
    [ L ] G ⊢k typ_sel x <⦂ typ_sel x

| snf_top : forall L G T,
    [ L ] G ⊢k T <⦂ typ_top

| snf_bot : forall L G T,
    [ L ] G ⊢k typ_bot <⦂ T

| snf_bnd : forall L G S T1 T2 U,
    [ L ] G ⊢k S <⦂ T1 ->
    [ L ] G ⊢k T2 <⦂ U ->
    [ L ] G ⊢k typ_bnd T1 T2 <⦂ typ_bnd S U

| snf_all : forall L G T U1 U2 x,
    x `notin` union (fv G)
      (union (fv T) (union (fv U1) (union (fv U2) L))) ->
    [ union L (union (singleton x) (fv T)) ]
      x ~ T ++ G ⊢k open x U1 <⦂ open x U2 ->
    [ L ] G ⊢k typ_all T U1 <⦂ typ_all T U2

| snf_sel1 : forall L G x T S,
    binds x T G ->
    [ L ] G ⊢k T <⦂ typ_bnd S typ_top ->
    [ L ] G ⊢k S <⦂ (typ_sel $ avar_f x)

| snf_sel2 : forall L G x T U,
    binds x T G ->
    [ L ] G ⊢k T <⦂ typ_bnd typ_bot U ->
    [ L ] G ⊢k typ_sel $ avar_f x <⦂ U
where "[ L ] G ⊢k S <⦂ U" := (subtykn L G S U).

(* ------------------------------------------------------------------ *)
(* Basic environment lemmas                                            *)
(* ------------------------------------------------------------------ *)

Lemma dom_in_fv : forall (G : env) (x : atom), x `in` dom G -> x `in` fv G.
Proof. intros. simpl. fsetdec. Qed.

Lemma notin_fv_dom : forall (G : env) (x : atom), x `notin` fv G -> x `notin` dom G.
Proof. intros x G H. simpl in H. fsetdec. Qed.

Lemma wf_cons_inv_wf : forall (x : atom) (a : typ) (G : env),
    wf_env ((x,a)::G) -> wf_env G.
Proof. intros. inversion H. assumption. Qed.

Lemma wf_cons_inv_lc : forall (x : atom) (a : typ) (G : env),
    wf_env ((x,a)::G) -> lc a.
Proof. intros. inversion H. assumption. Qed.

Lemma wf_cons_inv_fv : forall (x : atom) (a : typ) (G : env),
    wf_env ((x,a)::G) -> fv a [<=] dom G.
Proof. intros. inversion H. assumption. Qed.

Lemma wf_cons_inv_notin : forall (x : atom) (a : typ) (G : env),
    wf_env ((x,a)::G) -> x `notin` dom G.
Proof. intros. assert (H1 : x `notin` fv G) by (inversion H; fsetdec).
  apply notin_fv_dom; assumption. Qed.

Lemma wf_env_uniq : forall G, wf_env G -> uniq G.
Proof.
  intros G H. induction H.
  - apply uniq_nil.
  - apply uniq_push.
    + assumption.
    + apply notin_fv_dom. fsetdec.
Qed.

Lemma binds_in_dom : forall (x : atom) (a : typ) (E : env), binds x a E -> x `in` dom E.
Proof.
  intros x a E H. induction E as [| [y c] E'].
  - inversion H.
  - simpl. simpl in H. destruct H as [Heq | Hin].
    + inversion Heq; subst; fsetdec.
    + apply IHE' in Hin; fsetdec.
Qed.

Lemma binds_decomp : forall (x : atom) (a : typ) (G : env),
    binds x a G -> exists G1 G2, G = G2 ++ (x,a) :: G1.
Proof.
  intros x a G H. induction G as [| [y c] G'].
  - inversion H.
  - simpl in H. destruct H as [Heq | Hin].
    + inversion Heq; subst. exists G', nil. reflexivity.
    + destruct (IHG' Hin) as [G1 [G2 Heq2]]. exists G1, ((y,c)::G2). simpl. rewrite Heq2. reflexivity.
Qed.

Lemma uniq_head_notin : forall (E : env) (x : atom) (a : typ), uniq ((x,a)::E) -> x `notin` dom E.
Proof. intros. inversion H. assumption. Qed.

Lemma decomp_unique : forall (G2 G1 : env) (x : atom) (a : typ),
  uniq (G2 ++ (x,a) :: G1) ->
  forall (G2' G1' : env) (b : typ),
  G2 ++ (x,a) :: G1 = G2' ++ (x,b) :: G1' -> a = b /\ G1 = G1'.
Proof.
  intros G2. induction G2 as [| [y c] G2'']; intros G1 x a Hu G2' G1' b Heq.
  - destruct G2' as [| [z d] G2'].
    + simpl in Heq.
      assert (Hpair : (x,a) = (x,b)) by
        (apply (f_equal (fun l => match l with nil => (x,a) | p::_ => p end)) in Heq; simpl in Heq; exact Heq).
      assert (Htail : G1 = G1') by
        (apply (f_equal (fun l => match l with nil => nil | _::t => t end)) in Heq; simpl in Heq; exact Heq).
      split.
      * apply (f_equal (@snd atom typ)) in Hpair. simpl in Hpair. exact Hpair.
      * exact Htail.
    + simpl in Heq.
      assert (Htail : G1 = G2' ++ (x,b) :: G1') by
        (apply (f_equal (fun l => match l with nil => nil | _::t => t end)) in Heq; simpl in Heq; exact Heq).
      exfalso.
      assert (Hin : binds x b (G2' ++ (x,b) :: G1')) by apply in_elt.
      apply binds_in_dom in Hin. rewrite <- Htail in Hin.
      assert (Hnot : x `notin` dom G1) by (apply (@uniq_head_notin G1 x a); simpl in Hu; assumption).
      fsetdec.
  - destruct G2' as [| [z d] G2'].
    + simpl in Heq.
      assert (Hpair : (y,c) = (x,b)) by
        (apply (f_equal (fun l => match l with nil => (y,c) | p::_ => p end)) in Heq; simpl in Heq; exact Heq).
      assert (Htail : G2'' ++ (x,a) :: G1 = G1') by
        (apply (f_equal (fun l => match l with nil => nil | _::t => t end)) in Heq; simpl in Heq; exact Heq).
      assert (Hyx : y = x) by (apply (f_equal (@fst atom typ)) in Hpair; simpl in Hpair; exact Hpair).
      exfalso.
      assert (Hin : binds x a (G2'' ++ (x,a) :: G1)) by apply in_elt.
      apply binds_in_dom in Hin.
      assert (Hnot : y `notin` dom (G2'' ++ (x,a) :: G1))
        by (apply (@uniq_head_notin (G2'' ++ (x,a) :: G1) y c); simpl in Hu; assumption).
      rewrite Hyx in Hnot.
      fsetdec.
    + simpl in Heq.
      assert (Htail : G2'' ++ (x,a) :: G1 = G2' ++ (x,b) :: G1') by
        (apply (f_equal (fun l => match l with nil => nil | _::t => t end)) in Heq; simpl in Heq; exact Heq).
      simpl in Hu.
      assert (Hu' : uniq (G2'' ++ (x,a) :: G1)) by (inversion Hu; assumption).
      eapply IHG2''; eauto.
Qed.

(* uniqueness of the bound type for a given key *)
Lemma binds_func : forall (G : env) (x : atom) (a b : typ),
    uniq G -> binds x a G -> binds x b G -> a = b.
Proof.
  intros G x a b Hu Ha Hb.
  destruct (@binds_decomp x b G Hb) as [G1 [G2 Heq]].
  subst G.
  apply (@binds_mid_eq typ x a b G1 G2); assumption.
Qed.

Lemma wf_env_tail : forall (G2 G1 : env) (x : atom) (a : typ),
    wf_env (G2 ++ (x,a) :: G1) -> wf_env G1.
Proof.
  intros G2. induction G2 as [| [y c] G2'']; intros G1 x a H.
  - simpl in H. inversion H. assumption.
  - simpl in H. apply IHG2'' with (x:=x) (a:=a). inversion H. assumption.
Qed.

Lemma wf_binds_lc : forall (G : env) (x : atom) (a : typ),
    wf_env G -> binds x a G -> lc a.
Proof.
  intros G. induction G as [| [y c] G']; intros x a Hwf Hb.
  - inversion Hb.
  - simpl in Hb. assert (Hwf' := wf_cons_inv_wf Hwf). destruct Hb as [Heq | Hin].
    + inversion Heq. subst. apply wf_cons_inv_lc in Hwf. assumption.
    + eapply IHG'; eauto.
Qed.

Lemma wf_binds_fv : forall (G : env) (x : atom) (a : typ),
    wf_env G -> binds x a G -> fv a [<=] dom G.
Proof.
  intros G. induction G as [| [y c] G']; intros x a Hwf Hb.
  - inversion Hb.
  - simpl in Hb. assert (Hwf' := wf_cons_inv_wf Hwf). destruct Hb as [Heq | Hin].
    + inversion Heq; subst. apply wf_cons_inv_fv in Hwf. intros z Hz. apply Hwf in Hz. simpl. fsetdec.
    + intros z Hz. apply (IHG' x a Hwf' Hin) in Hz. simpl. fsetdec.
Qed.

Lemma wf_decomp_fv : forall (G2 G1 : env) (x : atom) (a : typ),
    wf_env (G2 ++ (x,a) :: G1) -> fv a [<=] dom G1.
Proof.
  intros G2. induction G2 as [| [y c] G2'']; intros G1 x a H.
  - simpl in H. inversion H. assumption.
  - simpl in H. inversion H. eapply IHG2''. eassumption.
Qed.

Lemma wf_decomp_lc : forall (G2 G1 : env) (x : atom) (a : typ),
    wf_env (G2 ++ (x,a) :: G1) -> lc a.
Proof.
  intros. apply (@wf_binds_lc (G2 ++ (x,a) :: G1) x a).
  - assumption.
  - apply in_elt.
Qed.

(* ------------------------------------------------------------------ *)
(* Local closure and free variables of opening                         *)
(* ------------------------------------------------------------------ *)

Lemma fv_typ_top : fv typ_top [=] empty.
Proof. simpl. reflexivity. Qed.
Lemma fv_typ_bot : fv typ_bot [=] empty.
Proof. simpl. reflexivity. Qed.
Lemma fv_typ_sel_f : forall (x : atom), fv (typ_sel (avar_f x)) [=] singleton x.
Proof. simpl. reflexivity. Qed.
Lemma fv_typ_sel_b : forall (i : nat), fv (typ_sel (avar_b i)) [=] empty.
Proof. simpl. reflexivity. Qed.
Lemma fv_typ_bnd : forall (S U : typ), fv (typ_bnd S U) [=] fv S \u fv U.
Proof. simpl. reflexivity. Qed.
Lemma fv_typ_all : forall (S U : typ), fv (typ_all S U) [=] fv S \u fv U.
Proof. simpl. reflexivity. Qed.

Lemma lc_typ_bnd_inv : forall (S U : typ), lc (typ_bnd S U) -> lc S /\ lc U.
Proof. intros. inversion H. auto. Qed.

Lemma lc_typ_all_inv : forall (S U : typ), lc (typ_all S U) -> lc S /\ lc_at 1 U.
Proof. intros. inversion H. auto. Qed.

Lemma lc_open_avar : forall (n : nat) (v : avar) (x : atom),
    lc_at (S n) v -> lc_at n (open_rec_avar n x v).
Proof.
  intros n v x H. destruct v.
  - simpl. destruct (n == n0).
    + constructor.
    + inversion H. constructor. lia.
  - simpl. constructor.
Qed.

Lemma fv_open_avar : forall (k : nat) (v : avar) (x : atom),
    fv (open_rec_avar k x v) [<=] fv v \u singleton x.
Proof.
  intros k v x. destruct v.
  - simpl. destruct (k == n); simpl; fsetdec.
  - simpl. fsetdec.
Qed.

Lemma fv_open_rec_typ : forall (T : typ) (k : nat) (x : atom),
    fv (open_rec_typ k x T) [<=] fv T \u singleton x.
Proof.
  induction T; intros k x; simpl.
  - fsetdec.
  - fsetdec.
  - pose proof (@fv_open_avar k a x). simpl in H. fsetdec.
  - pose proof (IHT1 k x). pose proof (IHT2 (S k) x). fsetdec.
  - pose proof (IHT1 k x). pose proof (IHT2 k x). fsetdec.
Qed.

Lemma fv_open : forall (T : typ) (x : atom),
    fv (open x T) [<=] fv T \u singleton x.
Proof. intros. apply fv_open_rec_typ. Qed.

Lemma lc_open_rec : forall (T : typ) (n : nat) (x : atom),
    lc_at (S n) T -> lc_at n (open_rec_typ n x T).
Proof.
  induction T; intros n x H; simpl.
  - constructor.
  - constructor.
  - inversion H. apply lc_typ_sel. apply (@lc_open_avar n a x). assumption.
  - inversion H; subst.
    apply lc_typ_all.
    + apply IHT1. assumption.
    + apply IHT2. assumption.
  - inversion H; subst.
    apply lc_typ_bnd.
    + apply IHT1. assumption.
    + apply IHT2. assumption.
Qed.

Lemma lc_open : forall (T : typ) (x : atom),
    lc_at 1 T -> lc (open x T).
Proof. intros. apply lc_open_rec with (n:=0). assumption. Qed.

(* ------------------------------------------------------------------ *)
(* Exposure: preservation and restriction                              *)
(* ------------------------------------------------------------------ *)

Lemma in_dom_app_r : forall (G0 G : env) (x : atom),
    x `in` dom G -> x `in` dom (G0 ++ G).
Proof.
  intros G0. induction G0 as [| [y c] G0']; intros G x H.
  - simpl. assumption.
  - simpl. apply AtomSetImpl.add_2. apply IHG0'. assumption.
Qed.

Lemma exposure_lc : forall (G : env) (S V : typ),
    G ⊢ S ⇑ V -> wf_env G -> lc S -> lc V.
Proof.
  intros G S V Hexp. induction Hexp; intros Hwf Hlc.
  - assumption.
  - constructor.
  - constructor.
  - (* exp_bnd: G = G2 ++ x ~ T ++ G1, premises in G1 *)
    assert (Hwf1 : wf_env G1) by (apply (@wf_env_tail G2 G1 x T); assumption).
    assert (HlcT : lc T).
    { apply (@wf_decomp_lc G2 G1 x T); assumption. }
    assert (HlcU : lc U) by (destruct (lc_typ_bnd_inv (IHHexp1 Hwf1 HlcT)) as [Hl Hr]; exact Hr).
    apply (IHHexp2 Hwf1 HlcU).
Qed.

Lemma exposure_fv : forall (G : env) (S V : typ),
    G ⊢ S ⇑ V -> wf_env G -> fv S [<=] dom G -> fv V [<=] dom G.
Proof.
  intros G S V Hexp. induction Hexp; intros Hwf Hfv.
  - assumption.
  - rewrite fv_typ_top. fsetdec.
  - rewrite fv_typ_bot. fsetdec.
  - assert (Hwf1 : wf_env G1) by (apply (@wf_env_tail G2 G1 x T); assumption).
    assert (HfvT : fv T [<=] dom G1) by (apply (@wf_decomp_fv G2 G1 x T); assumption).
    assert (HfvU : fv U [<=] dom G1).
    { pose proof (IHHexp1 Hwf1 HfvT) as H. rewrite fv_typ_bnd in H. fsetdec. }
    intros z Hz. apply (IHHexp2 Hwf1 HfvU) in Hz.
    assert (Hz' : z `in` dom ((x,T) :: G1)) by (simpl; fsetdec).
    apply (@in_dom_app_r G2 ((x,T) :: G1) z). assumption.
Qed.

Lemma in_dom_decomp : forall (G : env) (x : atom),
    x `in` dom G -> exists A B T, G = A ++ (x,T) :: B.
Proof.
  intros G. induction G as [| [y c] G']; intros x Hin.
  - simpl in Hin. fsetdec.
  - simpl in Hin. assert (Hdec : x = y \/ x `in` dom G') by fsetdec.
    destruct Hdec as [-> | Hin'].
    + exists nil, G', c. reflexivity.
    + destruct (IHG' x Hin') as [A [B [T Heq]]]. exists ((y,c)::A), B, T. simpl. rewrite Heq. reflexivity.
Qed.

Lemma exp_restrict : forall (Gk G1 P : env) (S V : typ),
    Gk = P ++ G1 -> uniq Gk -> fv S [<=] dom G1 ->
    Gk ⊢ S ⇑ V -> G1 ⊢ S ⇑ V.
Proof.
  intros Gk G1 P S V Heq Hu Hfv Hexp.
  remember (P ++ G1) as Gs eqn:Hs.
  subst Gk.
  destruct Hexp as [G0 T0 Hns | G0 T0 | G1c G2c Tzc xc Hp | G1c G2c Tzc xc Lc Uc Uc' Hp1 Hp2].
  - apply exp_stop. assumption.
  - apply exp_top.
  - (* exp_bot *)
    assert (Hx : xc `in` dom G1).
    { apply Hfv. rewrite fv_typ_sel_f. fsetdec. }
    destruct (@in_dom_decomp G1 xc Hx) as [A [B [Tz1 HG1]]].
    assert (Hdec : G2c ++ (xc,Tzc) :: G1c = (P++A) ++ (xc,Tz1) :: B).
    { transitivity (P ++ (A ++ (xc,Tz1) :: B)).
      - rewrite <- HG1. exact Hs.
      - symmetry. apply app_assoc. }
    destruct (@decomp_unique G2c G1c xc Tzc Hu (P++A) B Tz1 Hdec) as [HT HB].
    rewrite <- HT in HG1. rewrite <- HB in HG1.
    rewrite HG1. apply exp_bot. assumption.
  - (* exp_bnd *)
    assert (Hx : xc `in` dom G1).
    { apply Hfv. rewrite fv_typ_sel_f. fsetdec. }
    destruct (@in_dom_decomp G1 xc Hx) as [A [B [Tz1 HG1]]].
    assert (Hdec : G2c ++ (xc,Tzc) :: G1c = (P++A) ++ (xc,Tz1) :: B).
    { transitivity (P ++ (A ++ (xc,Tz1) :: B)).
      - rewrite <- HG1. exact Hs.
      - symmetry. apply app_assoc. }
    destruct (@decomp_unique G2c G1c xc Tzc Hu (P++A) B Tz1 Hdec) as [HT HB].
    rewrite <- HT in HG1. rewrite <- HB in HG1.
    rewrite HG1. eapply exp_bnd; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Upcast / downcast targets                                           *)
(* ------------------------------------------------------------------ *)

Lemma upcast_lc : forall (G : env) (x : avar) (V : typ),
    G ⊢ x ↗! V -> wf_env G -> lc V.
Proof.
  intros G x V Hup. induction Hup; intros Hwf.
  - constructor.
  - constructor.
  - assert (Hwf1 : wf_env G1) by (apply (@wf_env_tail G2 G1 x T); assumption).
    assert (HlcT : lc T) by (apply (@wf_decomp_lc G2 G1 x T); assumption).
    pose proof (exposure_lc H Hwf1 HlcT) as Hlc.
    destruct (lc_typ_bnd_inv Hlc) as [Hl Hr]. exact Hr.
Qed.

Lemma upcast_fv : forall (G : env) (x : avar) (V : typ),
    G ⊢ x ↗! V -> wf_env G -> fv V [<=] dom G.
Proof.
  intros G x V Hup. induction Hup; intros Hwf.
  - rewrite fv_typ_top. fsetdec.
  - rewrite fv_typ_bot. fsetdec.
  - assert (Hwf1 : wf_env G1) by (apply (@wf_env_tail G2 G1 x T); assumption).
    assert (HfvT : fv T [<=] dom G1) by (apply (@wf_decomp_fv G2 G1 x T); assumption).
    pose proof (exposure_fv H Hwf1 HfvT) as Hfv.
    rewrite fv_typ_bnd in Hfv.
    intros z Hz.
    assert (Hz1 : z `in` dom G1) by (apply Hfv; fsetdec).
    assert (Hz2 : z `in` dom ((x,T) :: G1)) by (simpl; fsetdec).
    apply (@in_dom_app_r G2 ((x,T) :: G1) z). assumption.
Qed.

Lemma downcast_lc : forall (G : env) (x : avar) (V : typ),
    G ⊢ x ↘! V -> wf_env G -> lc V.
Proof.
  intros G x V Hdc. induction Hdc; intros Hwf.
  - constructor.
  - constructor.
  - assert (Hwf1 : wf_env G1) by (apply (@wf_env_tail G2 G1 x T); assumption).
    assert (HlcT : lc T) by (apply (@wf_decomp_lc G2 G1 x T); assumption).
    pose proof (exposure_lc H Hwf1 HlcT) as Hlc.
    destruct (lc_typ_bnd_inv Hlc) as [Hl Hr]. exact Hl.
Qed.

Lemma downcast_fv : forall (G : env) (x : avar) (V : typ),
    G ⊢ x ↘! V -> wf_env G -> fv V [<=] dom G.
Proof.
  intros G x V Hdc. induction Hdc; intros Hwf.
  - rewrite fv_typ_bot. fsetdec.
  - rewrite fv_typ_top. fsetdec.
  - assert (Hwf1 : wf_env G1) by (apply (@wf_env_tail G2 G1 x T); assumption).
    assert (HfvT : fv T [<=] dom G1) by (apply (@wf_decomp_fv G2 G1 x T); assumption).
    pose proof (exposure_fv H Hwf1 HfvT) as Hfv.
    rewrite fv_typ_bnd in Hfv.
    intros z Hz.
    assert (Hz1 : z `in` dom G1) by (apply Hfv; fsetdec).
    assert (Hz2 : z `in` dom ((x,T) :: G1)) by (simpl; fsetdec).
    apply (@in_dom_app_r G2 ((x,T) :: G1) z). assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Exposure to bounds, translated into kernel subtyping                *)
(* ------------------------------------------------------------------ *)

Lemma exp_subst : forall (Gk Gexp P : env),
    Gk = P ++ Gexp ->
    forall (T V : typ), Gexp ⊢ T ⇑ V ->
    forall (Lo Wb : typ), V = typ_bnd Lo Wb ->
    forall (Lab : atoms) (Ures : typ), [Lab]Gk ⊢k Wb <⦂ Ures ->
    [Lab]Gk ⊢k T <⦂ typ_bnd typ_bot Ures.
Proof.
  intros Gk Gexp P Heq T V Hexp.
  revert Gk P Heq.
  induction Hexp; intros Gk P Heq Lo Wb HV Lab Ures Hk.
  - rewrite HV. apply snf_bnd.
    + apply snf_bot.
    + exact Hk.
  - discriminate HV.
  - discriminate HV.
  - assert (Heq1 : Gk = (P ++ G2 ++ x ~ T) ++ G1).
    { rewrite Heq.
      rewrite (app_assoc (atom * typ) P (G2 ++ x ~ T) G1).
      rewrite (app_assoc (atom * typ) G2 (x ~ T) G1).
      reflexivity. }
    assert (Hb : binds x T Gk).
    { rewrite Heq. apply binds_app_3. unfold binds. apply in_elt. }
    eapply snf_sel2.
    + exact Hb.
    + assert (HU0 : [Lab]Gk ⊢k U <⦂ typ_bnd typ_bot Ures).
      { eapply IHHexp2. apply Heq1. exact HV. exact Hk. }
      eapply IHHexp1.
      * apply Heq1.
      * reflexivity.
      * exact HU0.
Qed.

Lemma exp_ctr : forall (Gk Gexp P : env),
    Gk = P ++ Gexp ->
    forall (T V : typ), Gexp ⊢ T ⇑ V ->
    forall (Lo Wb : typ), V = typ_bnd Lo Wb ->
    forall (Lab : atoms) (Sres : typ), [Lab]Gk ⊢k Sres <⦂ Lo ->
    [Lab]Gk ⊢k T <⦂ typ_bnd Sres typ_top.
Proof.
  intros Gk Gexp P Heq T V Hexp.
  revert Gk P Heq.
  induction Hexp; intros Gk P Heq Lo Wb HV Lab Sres Hs.
  - rewrite HV. apply snf_bnd.
    + exact Hs.
    + apply snf_top.
  - discriminate HV.
  - discriminate HV.
  - assert (Heq1 : Gk = (P ++ G2 ++ x ~ T) ++ G1).
    { rewrite Heq.
      rewrite (app_assoc (atom * typ) P (G2 ++ x ~ T) G1).
      rewrite (app_assoc (atom * typ) G2 (x ~ T) G1).
      reflexivity. }
    assert (Hb : binds x T Gk).
    { rewrite Heq. apply binds_app_3. unfold binds. apply in_elt. }
    eapply snf_sel2.
    + exact Hb.
    + assert (HU : [Lab]Gk ⊢k U <⦂ typ_bnd Sres typ_top).
      { eapply IHHexp2. apply Heq1. exact HV. exact Hs. }
      eapply (@exp_subst Gk G1 (P ++ G2 ++ x ~ T) Heq1 T (typ_bnd L U) Hexp1 L U eq_refl Lab (typ_bnd Sres typ_top)).
      exact HU.
Qed.

Lemma exp_bot_kn : forall (Gk Gexp P : env),
    Gk = P ++ Gexp ->
    forall (T V : typ), Gexp ⊢ T ⇑ V -> V = typ_bot ->
    forall (Lab : atoms) (Ures : typ), [Lab]Gk ⊢k T <⦂ typ_bnd typ_bot Ures.
Proof.
  intros Gk Gexp P Heq T V Hexp.
  revert Gk P Heq.
  induction Hexp; intros Gk P Heq HV Lab Ures.
  - rewrite HV. apply snf_bot.
  - discriminate HV.
  - assert (Heq1 : Gk = (P ++ G2 ++ x ~ T) ++ G1).
    { rewrite Heq.
      rewrite (app_assoc (atom * typ) P (G2 ++ x ~ T) G1).
      rewrite (app_assoc (atom * typ) G2 (x ~ T) G1).
      reflexivity. }
    assert (Hb : binds x T Gk).
    { rewrite Heq. apply binds_app_3. unfold binds. apply in_elt. }
    eapply snf_sel2.
    + exact Hb.
    + eapply IHHexp. apply Heq1. reflexivity.
  - assert (Heq1 : Gk = (P ++ G2 ++ x ~ T) ++ G1).
    { rewrite Heq.
      rewrite (app_assoc (atom * typ) P (G2 ++ x ~ T) G1).
      rewrite (app_assoc (atom * typ) G2 (x ~ T) G1).
      reflexivity. }
    assert (Hb : binds x T Gk).
    { rewrite Heq. apply binds_app_3. unfold binds. apply in_elt. }
    eapply snf_sel2.
    + exact Hb.
    + assert (HU : [Lab]Gk ⊢k U <⦂ typ_bnd typ_bot Ures).
      { eapply IHHexp2. apply Heq1. exact HV. }
      eapply (@exp_subst Gk G1 (P ++ G2 ++ x ~ T) Heq1 T (typ_bnd L U) Hexp1 L U eq_refl Lab (typ_bnd typ_bot Ures)).
      exact HU.
Qed.

Lemma exp_bot_ctr : forall (Gk Gexp P : env),
    Gk = P ++ Gexp ->
    forall (T V : typ), Gexp ⊢ T ⇑ V -> V = typ_bot ->
    forall (Lab : atoms) (Sres : typ), [Lab]Gk ⊢k T <⦂ typ_bnd Sres typ_top.
Proof.
  intros Gk Gexp P Heq T V Hexp.
  revert Gk P Heq.
  induction Hexp; intros Gk P Heq HV Lab Sres.
  - rewrite HV. apply snf_bot.
  - discriminate HV.
  - assert (Heq1 : Gk = (P ++ G2 ++ x ~ T) ++ G1).
    { rewrite Heq.
      rewrite (app_assoc (atom * typ) P (G2 ++ x ~ T) G1).
      rewrite (app_assoc (atom * typ) G2 (x ~ T) G1).
      reflexivity. }
    assert (Hb : binds x T Gk).
    { rewrite Heq. apply binds_app_3. unfold binds. apply in_elt. }
    eapply snf_sel2.
    + exact Hb.
    + eapply (@exp_bot_kn Gk G1 (P ++ G2 ++ x ~ T) Heq1 T typ_bot Hexp eq_refl Lab (typ_bnd Sres typ_top)).
  - assert (Heq1 : Gk = (P ++ G2 ++ x ~ T) ++ G1).
    { rewrite Heq.
      rewrite (app_assoc (atom * typ) P (G2 ++ x ~ T) G1).
      rewrite (app_assoc (atom * typ) G2 (x ~ T) G1).
      reflexivity. }
    assert (Hb : binds x T Gk).
    { rewrite Heq. apply binds_app_3. unfold binds. apply in_elt. }
    eapply snf_sel2.
    + exact Hb.
    + assert (HU : [Lab]Gk ⊢k U <⦂ typ_bnd Sres typ_top).
      { eapply IHHexp2. apply Heq1. exact HV. }
      eapply (@exp_subst Gk G1 (P ++ G2 ++ x ~ T) Heq1 T (typ_bnd L U) Hexp1 L U eq_refl Lab (typ_bnd Sres typ_top)).
      exact HU.
Qed.

(* ------------------------------------------------------------------ *)
(* Step subtyping with a top/bot source                                *)
(* ------------------------------------------------------------------ *)

Lemma ss_top_bot_absurd : forall (Lab : atoms) (G : env),
    [Lab]G ⊢s typ_top <⦂ typ_bot -> False.
Proof. intros Lab G H. inversion H. Qed.

Lemma ss_top_bnd_absurd : forall (Lab : atoms) (G : env) (S U : typ),
    [Lab]G ⊢s typ_top <⦂ typ_bnd S U -> False.
Proof. intros Lab G S U H. inversion H. Qed.


(* ------------------------------------------------------------------ *)
(* Step subtyping implies kernel subtyping                             *)
(* ------------------------------------------------------------------ *)

Lemma decomp_mid_eq : forall (G2 G1 : env) (x : atom) (T : typ),
    G2 ++ x ~ T ++ G1 = (G2 ++ x ~ T) ++ G1.
Proof. intros. rewrite (app_assoc (atom * typ) G2 (x ~ T) G1). reflexivity. Qed.

Lemma bot_neq_top : typ_bot <> typ_top.
Proof. discriminate. Qed.
Lemma top_neq_bot : typ_top <> typ_bot.
Proof. discriminate. Qed.
Lemma sel_neq_top : forall a : avar, typ_sel a <> typ_top.
Proof. discriminate. Qed.
Lemma sel_neq_bot : forall a : avar, typ_sel a <> typ_bot.
Proof. discriminate. Qed.
Lemma bnd_neq_top : forall S U : typ, typ_bnd S U <> typ_top.
Proof. discriminate. Qed.
Lemma bnd_neq_bot : forall S U : typ, typ_bnd S U <> typ_bot.
Proof. discriminate. Qed.
Lemma all_neq_top : forall S U : typ, typ_all S U <> typ_top.
Proof. discriminate. Qed.
Lemma all_neq_bot : forall S U : typ, typ_all S U <> typ_bot.
Proof. discriminate. Qed.

Lemma ss_to_kn_aux : forall (Lab : atoms) (G : env) (S U : typ),
    [Lab]G ⊢s S <⦂ U ->
    (wf_env G -> fv S [<=] dom G -> lc S -> fv U [<=] dom G -> lc U -> [Lab]G ⊢k S <⦂ U)
    /\ (S = typ_top -> forall z : avar, [Lab]G ⊢k typ_sel z <⦂ U)
    /\ (U = typ_bot -> forall z : avar, [Lab]G ⊢k S <⦂ typ_sel z)
    /\ (S = typ_top -> U = typ_bot -> False).
Proof.
  intros Lab G S U Hstp.
  induction Hstp as [L0 G0 T0 | L0 G0 T0 | L0 G0 x0
                   | L0 G0 x0 T0 U0 Hup Dsub IHDsub | L0 G0 x0 T0 U0 Hdc Dsub IHDsub
                   | L0 G0 S1 U1 S2 U2 D1 IH1 D2 IH2 | L0 G0 T0 U1 U2 x0 Hfresh Dsub IHDsub].
  - (* ss_top *)
    split.
    + intros _ _ _ _ _. apply (@snf_top L0 G0 T0).
    + split.
      * intros _ z. apply (@snf_top L0 G0 (typ_sel z)).
      * split.
        -- intros HU. exact (False_ind _ (top_neq_bot HU)).
        -- intros _ HU. exact (top_neq_bot HU).
  - (* ss_bot *)
    split.
    + intros _ _ _ _ _. apply (@snf_bot L0 G0 T0).
    + split.
      * intros HS. exact (False_ind _ (bot_neq_top HS)).
      * split.
        -- intros _ z. apply (@snf_bot L0 G0 (typ_sel z)).
        -- intros HS _. exact (bot_neq_top HS).
  - (* ss_sel_refl *)
    split.
    + intros _ _ _ _ _. apply (@snf_vrefl L0 G0 x0).
    + split.
      * intros HS. exact (False_ind _ (@sel_neq_top x0 HS)).
      * split.
        -- intros HU. exact (False_ind _ (@sel_neq_bot x0 HU)).
        -- intros HS _. exact (@sel_neq_top x0 HS).
  - (* ss_sel_left *)
    destruct IHDsub as [IHA [IHB [IHC IHD]]].
    split.
    + intros Hwf HSfv HSlc HUfv HUl.
      assert (HlcT : lc T0) by (apply (@upcast_lc G0 x0 T0); assumption).
      assert (HfvT : fv T0 [<=] dom G0) by (apply (@upcast_fv G0 x0 T0); assumption).
      assert (Hk : [L0]G0 ⊢k T0 <⦂ U0) by (apply IHA; assumption).
      destruct Hup as [G1 x1 | G1c G2c xa Ta Hp | G1c G2c xa Ta La Ua Hp].
      * apply (IHB eq_refl _).
      * eapply snf_sel2.
        -- unfold binds. apply in_elt.
        -- eapply exp_bot_kn; [apply decomp_mid_eq | exact Hp | reflexivity].
      * eapply snf_sel2.
        -- unfold binds. apply in_elt.
        -- eapply exp_subst; [apply decomp_mid_eq | exact Hp | reflexivity | exact Hk].
    + split.
      * intros HS. exact (False_ind _ (@sel_neq_top x0 HS)).
      * split.
        -- intros HU z.
           destruct Hup as [G1 x1 | G1c G2c xa Ta Hp | G1c G2c xa Ta La Ua Hp].
           ++ exact (False_ind _ (IHD eq_refl HU)).
           ++ eapply snf_sel2.
              ** unfold binds. apply in_elt.
              ** eapply exp_bot_kn; [apply decomp_mid_eq | exact Hp | reflexivity].
           ++ eapply snf_sel2.
              ** unfold binds. apply in_elt.
              ** eapply exp_subst; [apply decomp_mid_eq | exact Hp | reflexivity | apply (IHC HU z)].
        -- intros HS _. exact (@sel_neq_top x0 HS).
  - (* ss_sel_right *)
    destruct IHDsub as [IHA [IHB [IHC IHD]]].
    split.
    + intros Hwf USfv USlc HUfv HUl.
      assert (HlcT : lc T0) by (apply (@downcast_lc G0 x0 T0); assumption).
      assert (HfvT : fv T0 [<=] dom G0) by (apply (@downcast_fv G0 x0 T0); assumption).
      assert (Hk : [L0]G0 ⊢k U0 <⦂ T0) by (apply IHA; assumption).
      destruct Hdc as [G1 x1 | G1c G2c xa Ta Hp | G1c G2c xa Ta La Ua Hp].
      * apply (IHC eq_refl _).
      * eapply snf_sel1.
        -- unfold binds. apply in_elt.
        -- eapply exp_bot_ctr; [apply decomp_mid_eq | exact Hp | reflexivity].
      * eapply snf_sel1.
        -- unfold binds. apply in_elt.
        -- eapply exp_ctr; [apply decomp_mid_eq | exact Hp | reflexivity | exact Hk].
    + split.
      * intros HS z.
        destruct Hdc as [G1 x1 | G1c G2c xa Ta Hp | G1c G2c xa Ta La Ua Hp].
        -- exact (False_ind _ (IHD HS eq_refl)).
        -- eapply snf_sel1.
           ++ unfold binds. apply in_elt.
           ++ eapply exp_bot_ctr; [apply decomp_mid_eq | exact Hp | reflexivity].
        -- eapply snf_sel1.
           ++ unfold binds. apply in_elt.
           ++ eapply exp_ctr; [apply decomp_mid_eq | exact Hp | reflexivity | apply (IHB HS z)].
      * split.
        -- intros HU. exact (False_ind _ (@sel_neq_bot x0 HU)).
        -- intros _ HU. exact (@sel_neq_bot x0 HU).
  - (* ss_bnd *)
    destruct IH1 as [IH1A [IH1B [IH1C IH1D]]].
    destruct IH2 as [IH2A [IH2B [IH2C IH2D]]].
    split.
    + intros Hwf Sfv Slc Ufv Ulc.
      destruct (lc_typ_bnd_inv Slc) as [S1lc U1lc].
      destruct (lc_typ_bnd_inv Ulc) as [S2lc U2lc].
      rewrite fv_typ_bnd in Sfv. rewrite fv_typ_bnd in Ufv.
      apply (@snf_bnd L0 G0 S2 S1 U1 U2).
      * apply IH1A.
        -- exact Hwf.
        -- intros z Hz. apply Ufv. fsetdec.
        -- exact S2lc.
        -- intros z Hz. apply Sfv. fsetdec.
        -- exact S1lc.
      * apply IH2A.
        -- exact Hwf.
        -- intros z Hz. apply Sfv. fsetdec.
        -- exact U1lc.
        -- intros z Hz. apply Ufv. fsetdec.
        -- exact U2lc.
    + split.
      * intros HS. exact (False_ind _ (@bnd_neq_top S1 U1 HS)).
      * split.
        -- intros HU. exact (False_ind _ (@bnd_neq_bot S2 U2 HU)).
        -- intros HS _. exact (@bnd_neq_top S1 U1 HS).
  - (* ss_all *)
    destruct IHDsub as [IHA [IHB [IHC IHD]]].
    split.
    + intros Hwf Sfv Slc Ufv Ulc.
      destruct (lc_typ_all_inv Slc) as [Tlc U1lc].
      destruct (lc_typ_all_inv Ulc) as [_ U2lc].
      rewrite fv_typ_all in Sfv. rewrite fv_typ_all in Ufv.
      assert (Hfresh' : x0 `notin` union (fv G0)
                (union (fv T0) (union (fv U1) (union (fv U2) L0)))) by fsetdec.
      apply (@snf_all L0 G0 T0 U1 U2 x0 Hfresh').
      assert (Hwf' : wf_env (x0 ~ T0 ++ G0)).
      { apply wf_cons.
        - fsetdec.
        - intros z Hz. apply Sfv. fsetdec.
        - exact Hwf.
        - exact Tlc. }
      apply IHA.
      * exact Hwf'.
      * intros z Hz. apply (@fv_open U1 x0) in Hz. simpl. fsetdec.
      * apply lc_open. exact U1lc.
      * intros z Hz. apply (@fv_open U2 x0) in Hz. simpl. fsetdec.
      * apply lc_open. exact U2lc.
    + split.
      * intros HS. exact (False_ind _ (@all_neq_top T0 U1 HS)).
      * split.
        -- intros HU. exact (False_ind _ (@all_neq_bot T0 U2 HU)).
        -- intros HS _. exact (@all_neq_top T0 U1 HS).
Qed.

Lemma ss_to_kn : forall (Lab : atoms) (G : env) (S U : typ),
    wf_env G -> fv S [<=] dom G -> lc S -> fv U [<=] dom G -> lc U ->
    [Lab]G ⊢s S <⦂ U -> [Lab]G ⊢k S <⦂ U.
Proof.
  intros Lab G S U Hwf HSfv HSlc HUfv HUl Hstp.
  destruct (@ss_to_kn_aux Lab G S U Hstp) as [HA _].
  apply HA; assumption.
Qed.

Lemma exp_top_only : forall (G : env) (V : typ), G ⊢ typ_top ⇑ V -> V = typ_top.
Proof.
  intros G V H. inversion H; subst.
  - reflexivity.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* More constructor inequalities and exposure facts                    *)
(* ------------------------------------------------------------------ *)
Lemma top_neq_bnd : forall S U : typ, typ_top <> typ_bnd S U.
Proof. discriminate. Qed.
Lemma sel_neq_bnd : forall a : avar, forall S U : typ, typ_sel a <> typ_bnd S U.
Proof. discriminate. Qed.
Lemma all_neq_bnd : forall S U W V : typ, typ_all S U <> typ_bnd W V.
Proof. discriminate. Qed.

Lemma not_sel_bot : ~ is_sel typ_bot.
Proof. intros H. unfold is_sel in H. simpl in H. exact H. Qed.
Lemma not_sel_bnd : forall S U : typ, ~ is_sel (typ_bnd S U).
Proof. intros S U H. unfold is_sel in H. simpl in H. exact H. Qed.
Lemma not_sel_top : ~ is_sel typ_top.
Proof. intros H. unfold is_sel in H. simpl in H. exact H. Qed.

Lemma exp_restrict_tail : forall (G2 G1 : env) (x : atom) (T W : typ),
    wf_env (G2 ++ x ~ T ++ G1) -> fv T [<=] dom G1 ->
    (G2 ++ x ~ T ++ G1) ⊢ T ⇑ W -> G1 ⊢ T ⇑ W.
Proof.
  intros G2 G1 x T W Hwf Hfv Hexp.
  apply (@exp_restrict (G2 ++ x ~ T ++ G1) G1 (G2 ++ x ~ T) T W).
  - apply decomp_mid_eq.
  - apply wf_env_uniq; exact Hwf.
  - exact Hfv.
  - exact Hexp.
Qed.

(* ------------------------------------------------------------------ *)
(* Shapes of step subtypings with bound targets                        *)
(* ------------------------------------------------------------------ *)

Lemma ss_bound_cov : forall (Lab : atoms) (G : env) (T V : typ),
    wf_env G -> lc T -> fv T [<=] dom G ->
    [Lab]G ⊢s T <⦂ V ->
    forall U, V = typ_bnd typ_bot U ->
    exists W, (G ⊢ T ⇑ W) /\
      (W = typ_bot \/ (exists Lo Wo, W = typ_bnd Lo Wo /\ [Lab]G ⊢s Wo <⦂ U)).
Proof.
  intros Lab G T V Hwf Hlc Hfv D.
  revert Hwf Hlc Hfv.
  refine ((fix f (L0 : atoms) (G0 : env) (T0 V0 : typ)
                 (D0 : [L0]G0 ⊢s T0 <⦂ V0) {struct D0}
               : wf_env G0 -> lc T0 -> fv T0 [<=] dom G0 ->
                 forall U, V0 = typ_bnd typ_bot U ->
                 exists W, (G0 ⊢ T0 ⇑ W) /\
                   (W = typ_bot \/ (exists Lo Wo, W = typ_bnd Lo Wo /\ [L0]G0 ⊢s Wo <⦂ U))
             := match D0 as Dd in stp_subty Lb Gb Tb Vb
                      return (wf_env Gb -> lc Tb -> fv Tb [<=] dom Gb ->
                              forall U, Vb = typ_bnd typ_bot U ->
                              exists W, (Gb ⊢ Tb ⇑ W) /\
                                (W = typ_bot \/ (exists Lo Wo, W = typ_bnd Lo Wo /\ [Lb]Gb ⊢s Wo <⦂ U)))
                with
                | @ss_top Lb Gb Tc => _
                | @ss_bot Lb Gb Tc => _
                | @ss_sel_refl Lb Gb x0 => _
                | @ss_sel_left Lb Gb x0 T0 U0 Hup Dsub => _
                | @ss_sel_right Lb Gb x0 T0 U0 Hdc Dsub => _
                | @ss_bnd Lb Gb S1 U1 S2 U2 D1 D2 => _
                | @ss_all Lb Gb T0 U1 U2 x0 Hfresh Dsub => _
                end) Lab G T V D).
  - (* ss_top *) intros Hw Hl Hf U HV. exfalso.
    exact (@bnd_neq_top typ_bot U (eq_sym HV)).
  - (* ss_bot *) intros Hw Hl Hf U HV. exists typ_bot. split.
    + apply exp_stop. exact not_sel_bot.
    + left. reflexivity.
  - (* ss_sel_refl *) intros Hw Hl Hf U HV. exfalso.
    exact (@sel_neq_bnd x0 typ_bot U HV).
  - (* ss_sel_left *) intros Hw Hl Hf U HV.
    assert (HlcT : lc T0) by (apply (@upcast_lc Gb x0 T0); [exact Hup | exact Hw]).
    assert (HfvT : fv T0 [<=] dom Gb) by (apply (@upcast_fv Gb x0 T0); [exact Hup | exact Hw]).
    destruct (f Lb Gb T0 U0 Dsub Hw HlcT HfvT U HV) as [W [Hexp Hdisj]].
    destruct Hup as [G1 x1 | G1c G2c xa Ta Hp | G1c G2c xa Ta La Ua Hp].
    + (* uce_top *) exfalso.
      destruct Hdisj as [Hb | [Lo [Wo [Heq _]]]].
      * exact (top_neq_bot (eq_trans (eq_sym (@exp_top_only _ W Hexp)) Hb)).
      * exact (@top_neq_bnd Lo Wo (eq_trans (eq_sym (@exp_top_only _ W Hexp)) Heq)).
    + (* uce_bot *) exists typ_bot. split.
      * eapply exp_bot. exact Hp.
      * left. reflexivity.
    + (* uce_bnd *)
      assert (HwfG1 : wf_env G1c) by (apply (@wf_env_tail G2c G1c xa Ta); exact Hw).
      assert (HlcTa : lc Ta) by (apply (@wf_decomp_lc G2c G1c xa Ta); exact Hw).
      assert (HfvTa : fv Ta [<=] dom G1c) by (apply (@wf_decomp_fv G2c G1c xa Ta); exact Hw).
      assert (HlcUa : lc Ua).
      { pose proof (exposure_lc Hp HwfG1 HlcTa) as Hx.
        destruct (lc_typ_bnd_inv Hx) as [_ Hr]. exact Hr. }
      assert (HfvUa : fv Ua [<=] dom G1c).
      { pose proof (exposure_fv Hp HwfG1 HfvTa) as Hx.
        rewrite fv_typ_bnd in Hx.
        intros z Hz. apply Hx. fsetdec. }
      assert (HfvUaG : fv Ua [<=] dom (G2c ++ xa ~ Ta ++ G1c)).
      { intros z Hz. apply HfvUa in Hz.
        assert (Hz2 : z `in` dom ((xa,Ta) :: G1c)) by (simpl; fsetdec).
        apply (@in_dom_app_r G2c ((xa,Ta) :: G1c) z). assumption. }
      destruct (f Lb _ Ua U0 Dsub Hw HlcUa HfvUaG U HV) as [W2 [HexpW HdisjW]].
      assert (HexpWr : G1c ⊢ Ua ⇑ W2).
      { apply (@exp_restrict (G2c ++ xa ~ Ta ++ G1c) G1c (G2c ++ xa ~ Ta) Ua W2).
        - apply decomp_mid_eq.
        - apply wf_env_uniq. exact Hw.
        - exact HfvUa.
        - exact HexpW. }
      destruct HdisjW as [Hb | [Lo [Wo [Heq Hst]]]].
      * exists typ_bot. split.
        -- rewrite Hb in HexpWr. eapply exp_bnd; [exact Hp | exact HexpWr].
        -- left. reflexivity.
      * exists (typ_bnd Lo Wo). split.
        -- rewrite Heq in HexpWr. eapply exp_bnd; [exact Hp | exact HexpWr].
        -- right. exists Lo, Wo. split; [reflexivity | exact Hst].
  - (* ss_sel_right *) intros Hw Hl Hf U HV. exfalso.
    exact (@sel_neq_bnd x0 typ_bot U HV).
  - (* ss_bnd *) intros Hw Hl Hf U HV.
    injection HV as HS2 HU2.
    exists (typ_bnd S1 U1). split.
    + apply exp_stop. apply not_sel_bnd.
    + right. exists S1, U1. split; [reflexivity | rewrite <- HU2; exact D2].
  - (* ss_all *) intros Hw Hl Hf U HV. exfalso.
    exact (@all_neq_bnd T0 U2 typ_bot U HV).
Qed.

Lemma ss_bound_ctr : forall (Lab : atoms) (G : env) (T V : typ),
    wf_env G -> lc T -> fv T [<=] dom G ->
    [Lab]G ⊢s T <⦂ V ->
    forall S, V = typ_bnd S typ_top ->
    exists W, (G ⊢ T ⇑ W) /\
      (W = typ_bot \/ (exists Lo Wo, W = typ_bnd Lo Wo /\ [Lab]G ⊢s S <⦂ Lo)).
Proof.
  intros Lab G T V Hwf Hlc Hfv D.
  revert Hwf Hlc Hfv.
  refine ((fix f (L0 : atoms) (G0 : env) (T0 V0 : typ)
                 (D0 : [L0]G0 ⊢s T0 <⦂ V0) {struct D0}
               : wf_env G0 -> lc T0 -> fv T0 [<=] dom G0 ->
                 forall S, V0 = typ_bnd S typ_top ->
                 exists W, (G0 ⊢ T0 ⇑ W) /\
                   (W = typ_bot \/ (exists Lo Wo, W = typ_bnd Lo Wo /\ [L0]G0 ⊢s S <⦂ Lo))
             := match D0 as Dd in stp_subty Lb Gb Tb Vb
                      return (wf_env Gb -> lc Tb -> fv Tb [<=] dom Gb ->
                              forall S, Vb = typ_bnd S typ_top ->
                              exists W, (Gb ⊢ Tb ⇑ W) /\
                                (W = typ_bot \/ (exists Lo Wo, W = typ_bnd Lo Wo /\ [Lb]Gb ⊢s S <⦂ Lo)))
                with
                | @ss_top Lb Gb Tc => _
                | @ss_bot Lb Gb Tc => _
                | @ss_sel_refl Lb Gb x0 => _
                | @ss_sel_left Lb Gb x0 T0 U0 Hup Dsub => _
                | @ss_sel_right Lb Gb x0 T0 U0 Hdc Dsub => _
                | @ss_bnd Lb Gb S1 U1 S2 U2 D1 D2 => _
                | @ss_all Lb Gb T0 U1 U2 x0 Hfresh Dsub => _
                end) Lab G T V D).
  - (* ss_top *) intros Hw Hl Hf S0 HV. exfalso.
    exact (@top_neq_bnd S0 typ_top (HV)).
  - (* ss_bot *) intros Hw Hl Hf S0 HV. exists typ_bot. split.
    + apply exp_stop. exact not_sel_bot.
    + left. reflexivity.
  - (* ss_sel_refl *) intros Hw Hl Hf S0 HV. exfalso.
    exact (@sel_neq_bnd x0 S0 typ_top HV).
  - (* ss_sel_left *) intros Hw Hl Hf S0 HV.
    assert (HlcT : lc T0) by (apply (@upcast_lc Gb x0 T0); [exact Hup | exact Hw]).
    assert (HfvT : fv T0 [<=] dom Gb) by (apply (@upcast_fv Gb x0 T0); [exact Hup | exact Hw]).
    destruct (f Lb Gb T0 U0 Dsub Hw HlcT HfvT S0 HV) as [W [Hexp Hdisj]].
    destruct Hup as [G1 x1 | G1c G2c xa Ta Hp | G1c G2c xa Ta La Ua Hp].
    + (* uce_top *) exfalso.
      destruct Hdisj as [Hb | [Lo [Wo [Heq _]]]].
      * exact (top_neq_bot (eq_trans (eq_sym (@exp_top_only _ W Hexp)) Hb)).
      * exact (@top_neq_bnd Lo Wo (eq_trans (eq_sym (@exp_top_only _ W Hexp)) Heq)).
    + (* uce_bot *) exists typ_bot. split.
      * eapply exp_bot. exact Hp.
      * left. reflexivity.
    + (* uce_bnd *)
      assert (HwfG1 : wf_env G1c) by (apply (@wf_env_tail G2c G1c xa Ta); exact Hw).
      assert (HlcTa : lc Ta) by (apply (@wf_decomp_lc G2c G1c xa Ta); exact Hw).
      assert (HfvTa : fv Ta [<=] dom G1c) by (apply (@wf_decomp_fv G2c G1c xa Ta); exact Hw).
      assert (HlcUa : lc Ua).
      { pose proof (exposure_lc Hp HwfG1 HlcTa) as Hx.
        destruct (lc_typ_bnd_inv Hx) as [_ Hr]. exact Hr. }
      assert (HfvUa : fv Ua [<=] dom G1c).
      { pose proof (exposure_fv Hp HwfG1 HfvTa) as Hx.
        rewrite fv_typ_bnd in Hx.
        intros z Hz. apply Hx. fsetdec. }
      assert (HfvUaG : fv Ua [<=] dom (G2c ++ xa ~ Ta ++ G1c)).
      { intros z Hz. apply HfvUa in Hz.
        assert (Hz2 : z `in` dom ((xa,Ta) :: G1c)) by (simpl; fsetdec).
        apply (@in_dom_app_r G2c ((xa,Ta) :: G1c) z). assumption. }
      destruct (f Lb _ Ua U0 Dsub Hw HlcUa HfvUaG S0 HV) as [W2 [HexpW HdisjW]].
      assert (HexpWr : G1c ⊢ Ua ⇑ W2).
      { apply (@exp_restrict (G2c ++ xa ~ Ta ++ G1c) G1c (G2c ++ xa ~ Ta) Ua W2).
        - apply decomp_mid_eq.
        - apply wf_env_uniq. exact Hw.
        - exact HfvUa.
        - exact HexpW. }
      destruct HdisjW as [Hb | [Lo [Wo [Heq Hst]]]].
      * exists typ_bot. split.
        -- rewrite Hb in HexpWr. eapply exp_bnd; [exact Hp | exact HexpWr].
        -- left. reflexivity.
      * exists (typ_bnd Lo Wo). split.
        -- rewrite Heq in HexpWr. eapply exp_bnd; [exact Hp | exact HexpWr].
        -- right. exists Lo, Wo. split; [reflexivity | exact Hst].
  - (* ss_sel_right *) intros Hw Hl Hf S0 HV. exfalso.
    exact (@sel_neq_bnd x0 S0 typ_top HV).
  - (* ss_bnd *) intros Hw Hl Hf S0 HV.
    injection HV as HS2 HU2.
    exists (typ_bnd S1 U1). split.
    + apply exp_stop. apply not_sel_bnd.
    + right. exists S1, U1. split; [reflexivity | rewrite HS2 in D1; exact D1].
  - (* ss_all *) intros Hw Hl Hf S0 HV. exfalso.
    exact (@all_neq_bnd T0 U2 S0 typ_top HV).
Qed.

(* ------------------------------------------------------------------ *)
(* Kernel subtyping implies step subtyping                             *)
(* ------------------------------------------------------------------ *)

Lemma kn_to_ss : forall (Lab : atoms) (G : env) (S U : typ),
    wf_env G -> fv S [<=] dom G -> lc S -> fv U [<=] dom G -> lc U ->
    [Lab]G ⊢k S <⦂ U -> [Lab]G ⊢s S <⦂ U.
Proof.
  intros Lab G S U Hwf HSfv HSlc HUfv HUl Hkn.
  revert Hwf HSfv HSlc HUfv HUl.
  induction Hkn as [L0 G0 x0 | L0 G0 T0 | L0 G0 T0
                   | L0 G0 S0 T1 T2 U0 D1 IH1 D2 IH2
                   | L0 G0 T0 U1 U2 x0 Hfresh Dsub IHDsub
                   | L0 G0 x0 T0 S0 Hb Dsub IHDsub
                   | L0 G0 x0 T0 U0 Hb Dsub IHDsub];
  intros Hwf HSfv HSlc HUfv HUl.
  - (* snf_vrefl *) apply ss_sel_refl.
  - (* snf_top *) apply ss_top.
  - (* snf_bot *) apply ss_bot.
  - (* snf_bnd *)
    rewrite fv_typ_bnd in HSfv. rewrite fv_typ_bnd in HUfv.
    destruct (lc_typ_bnd_inv HSlc) as [T1lc T2lc].
    destruct (lc_typ_bnd_inv HUl) as [S0lc U0lc].
    eapply ss_bnd.
    + apply IH1.
      * exact Hwf.
      * intros z Hz. apply HUfv. fsetdec.
      * exact S0lc.
      * intros z Hz. apply HSfv. fsetdec.
      * exact T1lc.
    + apply IH2.
      * exact Hwf.
      * intros z Hz. apply HSfv. fsetdec.
      * exact T2lc.
      * intros z Hz. apply HUfv. fsetdec.
      * exact U0lc.
  - (* snf_all *)
    rewrite fv_typ_all in HSfv. rewrite fv_typ_all in HUfv.
    destruct (lc_typ_all_inv HSlc) as [T0lc U1lc].
    destruct (lc_typ_all_inv HUl) as [_ U2lc].
    eapply (@ss_all L0 G0 T0 U1 U2 x0).
    + fsetdec.
    + assert (Hwf' : wf_env (x0 ~ T0 ++ G0)).
      { apply wf_cons.
        - fsetdec.
        - intros z Hz. apply HSfv. fsetdec.
        - exact Hwf.
        - exact T0lc. }
      apply IHDsub.
      * exact Hwf'.
      * intros z Hz. apply (@fv_open U1 x0) in Hz. simpl. fsetdec.
      * apply lc_open. exact U1lc.
      * intros z Hz. apply (@fv_open U2 x0) in Hz. simpl. fsetdec.
      * apply lc_open. exact U2lc.
  - (* snf_sel1 *)
    assert (HlcT : lc T0) by (apply (@wf_binds_lc G0 x0 T0); assumption).
    assert (HfvT : fv T0 [<=] dom G0) by (apply (@wf_binds_fv G0 x0 T0); assumption).
    assert (HlcB : lc (typ_bnd S0 typ_top)) by (apply lc_typ_bnd; [exact HSlc | constructor]).
    assert (HfvB : fv (typ_bnd S0 typ_top) [<=] dom G0).
    { intros z Hz. rewrite fv_typ_bnd in Hz. apply HSfv. fsetdec. }
    assert (Dstep : [L0]G0 ⊢s T0 <⦂ typ_bnd S0 typ_top)
      by (apply IHDsub; [exact Hwf | exact HfvT | exact HlcT | exact HfvB | exact HlcB]).
    destruct (@ss_bound_ctr L0 G0 T0 (typ_bnd S0 typ_top) Hwf HlcT HfvT Dstep S0 eq_refl)
      as [W [Hexp Hdisj]].
    destruct (@binds_decomp x0 T0 G0 Hb) as [G1 [G2 Heq]].
    subst G0.
    assert (HfvTG1 : fv T0 [<=] dom G1) by (apply (@wf_decomp_fv G2 G1 x0 T0); exact Hwf).
    destruct Hdisj as [Hb' | [Lo [Wo [HeqW Hst]]]].
    + assert (Hexr : G1 ⊢ T0 ⇑ typ_bot).
      { apply (@exp_restrict (G2 ++ x0 ~ T0 ++ G1) G1 (G2 ++ x0 ~ T0) T0 typ_bot).
        - apply decomp_mid_eq.
        - apply wf_env_uniq. exact Hwf.
        - exact HfvTG1.
        - rewrite Hb' in Hexp. exact Hexp. }
      assert (Hdown : (G2 ++ x0 ~ T0 ++ G1) ⊢ avar_f x0 ↘! typ_top)
        by (eapply dce_top; exact Hexr).
      eapply ss_sel_right.
      * exact Hdown.
      * apply ss_top.
    + assert (Hexr : G1 ⊢ T0 ⇑ typ_bnd Lo Wo).
      { apply (@exp_restrict (G2 ++ x0 ~ T0 ++ G1) G1 (G2 ++ x0 ~ T0) T0 (typ_bnd Lo Wo)).
        - apply decomp_mid_eq.
        - apply wf_env_uniq. exact Hwf.
        - exact HfvTG1.
        - rewrite HeqW in Hexp. exact Hexp. }
      assert (Hdown : (G2 ++ x0 ~ T0 ++ G1) ⊢ avar_f x0 ↘! Lo)
        by (eapply dce_bnd; exact Hexr).
      eapply ss_sel_right.
      * exact Hdown.
      * exact Hst.
  - (* snf_sel2 *)
    assert (HlcT : lc T0) by (apply (@wf_binds_lc G0 x0 T0); assumption).
    assert (HfvT : fv T0 [<=] dom G0) by (apply (@wf_binds_fv G0 x0 T0); assumption).
    assert (HlcB : lc (typ_bnd typ_bot U0)) by (apply lc_typ_bnd; [constructor | exact HUl]).
    assert (HfvB : fv (typ_bnd typ_bot U0) [<=] dom G0).
    { intros z Hz. rewrite fv_typ_bnd in Hz. apply HUfv. fsetdec. }
    assert (Dstep : [L0]G0 ⊢s T0 <⦂ typ_bnd typ_bot U0)
      by (apply IHDsub; [exact Hwf | exact HfvT | exact HlcT | exact HfvB | exact HlcB]).
    destruct (@ss_bound_cov L0 G0 T0 (typ_bnd typ_bot U0) Hwf HlcT HfvT Dstep U0 eq_refl)
      as [W [Hexp Hdisj]].
    destruct (@binds_decomp x0 T0 G0 Hb) as [G1 [G2 Heq]].
    subst G0.
    assert (HfvTG1 : fv T0 [<=] dom G1) by (apply (@wf_decomp_fv G2 G1 x0 T0); exact Hwf).
    destruct Hdisj as [Hb' | [Lo [Wo [HeqW Hst]]]].
    + assert (Hexr : G1 ⊢ T0 ⇑ typ_bot).
      { apply (@exp_restrict (G2 ++ x0 ~ T0 ++ G1) G1 (G2 ++ x0 ~ T0) T0 typ_bot).
        - apply decomp_mid_eq.
        - apply wf_env_uniq. exact Hwf.
        - exact HfvTG1.
        - rewrite Hb' in Hexp. exact Hexp. }
      assert (Hup : (G2 ++ x0 ~ T0 ++ G1) ⊢ avar_f x0 ↗! typ_bot)
        by (eapply uce_bot; exact Hexr).
      eapply ss_sel_left.
      * exact Hup.
      * apply ss_bot.
    + assert (Hexr : G1 ⊢ T0 ⇑ typ_bnd Lo Wo).
      { apply (@exp_restrict (G2 ++ x0 ~ T0 ++ G1) G1 (G2 ++ x0 ~ T0) T0 (typ_bnd Lo Wo)).
        - apply decomp_mid_eq.
        - apply wf_env_uniq. exact Hwf.
        - exact HfvTG1.
        - rewrite HeqW in Hexp. exact Hexp. }
      assert (Hup : (G2 ++ x0 ~ T0 ++ G1) ⊢ avar_f x0 ↗! Wo)
        by (eapply uce_bnd; exact Hexr).
      eapply ss_sel_left.
      * exact Hup.
      * exact Hst.
Qed.

Theorem subtykn_equiv_stp_subty : forall L G S U,
    wf_env G ->
    fv S [<=] dom G -> lc S ->
    fv U [<=] dom G -> lc U ->
    [ L ] G ⊢k S <⦂ U <->
    [ L ] G ⊢s S <⦂ U.

Proof.
  intros L G S U Hwf HSfv HSlc HUfv HUl. split.
  - apply (@kn_to_ss L G S U); assumption.
  - apply (@ss_to_kn L G S U); assumption.
Qed.
