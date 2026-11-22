Set Implicit Arguments.

Require Import Definitions.

Require Import Stareat.

Require Import Misc.

Reserved Notation "[ L ] G1 ⊢k S <⦂ U k⊣ G2" (at level 70).

Inductive subtysk : vars -> env -> typ -> typ -> env -> Prop :=

| ssk_refl : forall L G1 G2 x,
    [ L ] G1 ⊢k typ_sel x <⦂ typ_sel x k⊣ G2

| ssk_top : forall L G1 G2 T,
    [ L ] G1 ⊢k T <⦂ typ_top k⊣ G2

| ssk_bot : forall L G1 G2 T,
    [ L ] G1 ⊢k typ_bot <⦂ T k⊣ G2

| ssk_bnd : forall L G1 G2 S T1 T2 U,
    [ L ] G2 ⊢k S <⦂ T1 k⊣ G1 ->
    [ L ] G1 ⊢k T2 <⦂ U k⊣ G2 ->
    [ L ] G1 ⊢k typ_bnd T1 T2 <⦂ typ_bnd S U k⊣ G2

| ssk_all : forall L G1 G2 T1 T2 U1 U2 x,
    x `notin` fv G1 `union` fv T1 `union` fv T2
      `union` fv U1 `union` fv U2 `union` fv G2 `union` L ->
    [ L ] G2 ⊢k T2 <⦂ T1 k⊣ G1 ->
    [ union L (union (singleton x) (fv T2)) ]
      x ~ T1 ++ G1 ⊢k open x U1 <⦂ open x U2 k⊣ x ~ T2 ++ G2 ->
    [ L ] G1 ⊢k typ_all T1 U1 <⦂ typ_all T2 U2 k⊣ G2

| ssk_sel1 : forall L G1 G2 x T S,
    binds x T G2 ->
    [ L ] G2 ⊢k T <⦂ typ_bnd S typ_top k⊣ G1 ->
    [ L ] G1 ⊢k S <⦂ typ_sel $ avar_f x k⊣ G2

| ssk_sel2 : forall L G1 G2 x T U,
    binds x T G1 ->
    [ L ] G1 ⊢k T <⦂ typ_bnd typ_bot U k⊣ G2 ->
    [ L ] G1 ⊢k typ_sel $ avar_f x <⦂ U k⊣ G2
where "[ L ] G1 ⊢k S <⦂ U k⊣ G2" := (subtysk L G1 S U G2).

Reserved Notation "[ L ] G1 >> T '<⦂p' U << G2" (at level 70).

Inductive subtysk' : vars -> env -> typ -> typ -> env -> nat -> Prop :=
| ssk'_refl : forall L G1 G2 x, subtysk' L G1 (typ_sel x) (typ_sel x) G2 1
| ssk'_top : forall L G1 G2 T, subtysk' L G1 T typ_top G2 1
| ssk'_bot : forall L G1 G2 T, subtysk' L G1 typ_bot T G2 1
| ssk'_bnd : forall L G1 G2 S T1 T2 U n1 n2,
    subtysk' L G2 S T1 G1 n1 -> subtysk' L G1 T2 U G2 n2 ->
    subtysk' L G1 (typ_bnd T1 T2) (typ_bnd S U) G2 (1 + n1 + n2)
| ssk'_all : forall L G1 G2 T1 T2 U1 U2 x n1 n2,
    x `notin` fv G1 `union` fv T1 `union` fv T2
      `union` fv U1 `union` fv U2 `union` fv G2 `union` L ->
    subtysk' L G2 T2 T1 G1 n1 ->
    subtysk' (union L (union (singleton x) (fv T2)))
            (x ~ T1 ++ G1) (open x U1) (open x U2) (x ~ T2 ++ G2) n2 ->
    subtysk' L G1 (typ_all T1 U1) (typ_all T2 U2) G2 (1 + n1 + n2)
| ssk'_sel1 : forall L G1 G2 x T S n,
    binds x T G2 ->
    subtysk' L G2 T (typ_bnd S typ_top) G1 n ->
    subtysk' L G1 S (typ_sel $ avar_f x) G2 (1 + n)
| ssk'_sel2 : forall L G1 G2 x T U n,
    binds x T G1 ->
    subtysk' L G1 T (typ_bnd typ_bot U) G2 n ->
    subtysk' L G1 (typ_sel $ avar_f x) U G2 (1 + n).

Require Import Lia.

(* ============================================================ *)
(* Basic metatheory                                             *)
(* ============================================================ *)

Lemma fv_open_rec_upper : forall k u T,
    fv_typ (open_rec_typ k u T) [<=] fv_typ T \u {{u}}.
Proof.
  intros k u T. revert k. induction T as [| |v|T1 IH1 T2 IH2|T1 IH1 T2 IH2];
    simpl; intros k.
  - fsetdec.
  - fsetdec.
  - destruct v; simpl.
    + destruct (k == n); simpl; fsetdec.
    + fsetdec.
  - specialize (IH1 k). specialize (IH2 (S k)). fsetdec.
  - specialize (IH1 k). specialize (IH2 k). fsetdec.
Qed.

Lemma fv_open_upper : forall u T,
    fv_typ (open_rec_typ 0 u T) [<=] fv_typ T \u {{u}}.
Proof. intros. apply fv_open_rec_upper. Qed.

Lemma fv_open_rec_in : forall k u T z,
    z `in` fv_typ (open_rec_typ k u T) -> z `in` fv_typ T \/ z = u.
Proof.
  intros k u T z H. pose proof (fv_open_rec_upper k u T) as Hs.
  pose proof (Hs z H) as H1. clear Hs. fsetdec.
Qed.

Lemma lc_at_mono : forall T n m, lc_at n T -> n <= m -> lc_at m T.
Proof.
  intros T. induction T as [| |v|T1 IH1 T2 IH2|T1 IH1 T2 IH2];
    intros n m H Hle; simpl in *.
  - constructor.
  - constructor.
  - destruct v.
    + change (lc_typ_at n (typ_sel (avar_b n0))) in H.
      inversion H. change (lc_avar_at n (avar_b n0)) in H2. inversion H2.
      apply lc_typ_sel. constructor. lia.
    + apply lc_typ_sel. apply lc_af.
  - change (lc_typ_at n (typ_all T1 T2)) in H. inversion H; subst.
    change (lc_typ_at m (typ_all T1 T2)).
    apply lc_typ_all.
    + apply IH1 with (n := n) (m := m); auto.
    + apply IH2 with (n := S n) (m := S m); auto. lia.
  - change (lc_typ_at n (typ_bnd T1 T2)) in H. inversion H; subst.
    change (lc_typ_at m (typ_bnd T1 T2)).
    apply lc_typ_bnd.
    + apply IH1 with (n := n) (m := m); auto.
    + apply IH2 with (n := n) (m := m); auto.
Qed.

Lemma lc_typ_open_rec : forall k u T,
    lc_at (S k) T -> lc_at k (open_rec_typ k u T).
Proof.
  intros k u T. revert k. induction T as [| |v|T1 IH1 T2 IH2|T1 IH1 T2 IH2];
    simpl; intros k H.
  - constructor.
  - constructor.
  - destruct v; simpl.
    + destruct (k == n) as [Heq | Hneq].
      * apply lc_typ_sel. apply lc_af.
      * apply lc_typ_sel. constructor.
        change (lc_typ_at (S k) (typ_sel (avar_b n))) in H.
        inversion H. change (lc_avar_at (S k) (avar_b n)) in H2. inversion H2.
        lia.
    + apply lc_typ_sel. apply lc_af.
  - change (lc_typ_at (S k) (typ_all T1 T2)) in H. inversion H; subst.
    change (lc_typ_at k (typ_all (open_rec_typ k u T1) (open_rec_typ (S k) u T2))).
    apply lc_typ_all.
    + apply IH1 with (k := k). assumption.
    + apply IH2 with (k := S k). assumption.
  - change (lc_typ_at (S k) (typ_bnd T1 T2)) in H. inversion H; subst.
    change (lc_typ_at k (typ_bnd (open_rec_typ k u T1) (open_rec_typ k u T2))).
    apply lc_typ_bnd.
    + apply IH1 with (k := k). assumption.
    + apply IH2 with (k := k). assumption.
Qed.

Lemma lc_open : forall u T, lc_at 1 T -> lc (open_rec_typ 0 u T).
Proof.
  intros u T H. unfold lc. change (lc_at 0 (open_rec_typ 0 u T)).
  apply lc_typ_open_rec. assumption.
Qed.

Lemma lc_bnd_inv : forall n T1 T2, lc_at n (typ_bnd T1 T2) ->
                                 lc_at n T1 /\ lc_at n T2.
Proof.
  intros. change (lc_typ_at n (typ_bnd T1 T2)) in H. inversion H. auto.
Qed.

Lemma lc_all_inv : forall n T1 T2, lc_at n (typ_all T1 T2) ->
                                 lc_at n T1 /\ lc_at (S n) T2.
Proof.
  intros. change (lc_typ_at n (typ_all T1 T2)) in H. inversion H. auto.
Qed.

Lemma fv_bnd_subset_l : forall T1 T2, fv T1 [<=] fv (typ_bnd T1 T2).
Proof. intros. simpl. fsetdec. Qed.
Lemma fv_bnd_subset_r : forall T1 T2, fv T2 [<=] fv (typ_bnd T1 T2).
Proof. intros. simpl. fsetdec. Qed.
Lemma fv_all_subset_l : forall T1 T2, fv T1 [<=] fv (typ_all T1 T2).
Proof. intros. simpl. fsetdec. Qed.
Lemma fv_all_subset_r : forall T1 T2, fv T2 [<=] fv (typ_all T1 T2).
Proof. intros. simpl. fsetdec. Qed.

Lemma wf_env_suffix : forall A G, wf_env (A ++ G) -> wf_env G.
Proof.
  intros A. induction A as [| [y Ty] A IH]; intros G H.
  - simpl in H. exact H.
  - simpl in H. inversion H; subst. apply IH. assumption.
Qed.

Lemma dom_subset_fv : forall (G:env), dom G [<=] fv G.
Proof. intro G. simpl. fsetdec. Qed.

Lemma fv_subset_dom_cons : forall (G:env) (y:atom) (Ty:typ),
    dom G [<=] dom ((y,Ty) :: G).
Proof. intros. rewrite dom_cons. fsetdec. Qed.

Lemma wf_env_binds_notin_fv : forall G x T,
    wf_env G -> binds x T G -> x `notin` fv T.
Proof.
  intros G. induction G as [| [y Ty] G IH]; intros x T Hwf Hb.
  - inversion Hb.
  - simpl in Hwf. inversion Hwf; subst.
    apply binds_cons_1 in Hb. destruct Hb as [[Heq HTeq] | Hb].
    + subst. simpl in *. fsetdec.
    + apply IH with (x := x); auto.
Qed.

Lemma wf_env_binds_lc : forall G x T,
    wf_env G -> binds x T G -> lc T.
Proof.
  intros G. induction G as [| [y Ty] G IH]; intros x T Hwf Hb.
  - inversion Hb.
  - inversion Hwf; subst.
    apply binds_cons_1 in Hb. destruct Hb as [[Heq HTeq] | Hb].
    + subst. assumption.
    + apply IH with (x := x); auto.
Qed.

Lemma wf_env_binds_fv_dom : forall G x T,
    wf_env G -> binds x T G -> fv T [<=] dom G.
Proof.
  intros G. induction G as [| [y Ty] G IH]; intros x T Hwf Hb.
  - inversion Hb.
  - inversion Hwf; subst.
    apply binds_cons_1 in Hb. destruct Hb as [[Heq HTeq] | Hb].
    + subst. simpl. apply Subset_trans with (s' := dom G).
      * assumption.
      * fsetdec.
    + simpl. apply Subset_trans with (s' := dom G).
      * apply IH with (x := x); auto.
      * fsetdec.
Qed.

Lemma wf_env_uniq : forall G, wf_env G -> uniq G.
Proof.
  intros G H. induction H.
  - apply uniq_nil.
  - apply uniq_cons_3.
    + assumption.
    + pose proof (dom_subset_fv G). fsetdec.
Qed.

Lemma wf_env_binds_split : forall (G:env) x T,
    wf_env G -> binds x T G ->
    exists A B, G = A ++ x ~ T ++ B /\ fv T [<=] dom B /\ lc T.
Proof.
  intros G. induction G as [| [y Ty] G IH]; intros x T Hwf Hb.
  - inversion Hb.
  - inversion Hwf; subst.
    apply binds_cons_1 in Hb. destruct Hb as [[Heq HTeq] | Hb].
    + subst. exists nil, G. simpl. split; [ reflexivity | split; assumption ].
    + destruct (IH x T H4 Hb) as [A [B [Heq [Hfv Hlc]]]].
      exists ((y,Ty)::A), B. simpl. rewrite Heq. split; [ reflexivity | split; assumption ].
Qed.

Lemma binds_mid_self : forall (A B:env) (x:atom) (T:typ),
    binds x T (A ++ x ~ T ++ B).
Proof. intros. apply binds_app_3. apply binds_app_2. apply binds_one_3; auto. Qed.

Lemma app_decomp_uniq : forall (A:env) (B:env) (x:atom) (T:typ),
    uniq (A ++ x ~ T ++ B) ->
    forall A' B', A ++ x ~ T ++ B = A' ++ x ~ T ++ B' -> A = A' /\ B = B'.
Proof.
  intros A. induction A as [| [y U] A IH]; intros B x T Huniq A' B' Heq.
  - destruct A' as [| [z V] A'].
    + simpl in *. inversion Heq; subst. auto.
    + simpl in *.
      injection Heq as Hxz HTV HB.
      assert (Hin : x `in` dom B).
      { apply binds_In with (a := T). rewrite HB. apply binds_mid_self. }
      exfalso. apply uniq_cons_2 in Huniq. fsetdec.
  - destruct A' as [| [z V] A'].
    + simpl in *.
      injection Heq as Hyx HU HB.
      assert (Hin : x `in` dom (A ++ (x,T)::B)).
      { apply binds_In with (a := T). apply binds_mid_self. }
      exfalso. subst y. subst U. apply uniq_cons_2 in Huniq. fsetdec.
    + simpl in *. injection Heq as Hy HU Htail. subst.
      assert (A = A' /\ B = B').
      { apply IH with (B := B) (x := x) (T := T); auto.
        apply uniq_cons_1 in Huniq. exact Huniq. }
      destruct H; subst. auto.
Qed.

Lemma binds_decomp_uniq : forall (G:env) x T1 T2 A1 B1 A2 B2,
    uniq G ->
    G = A1 ++ x ~ T1 ++ B1 ->
    G = A2 ++ x ~ T2 ++ B2 ->
    T1 = T2 /\ B1 = B2.
Proof.
  intros G x T1 T2 A1 B1 A2 B2 Huniq E1 E2.
  assert (Hb1 : binds x T1 G) by (rewrite E1; apply binds_mid_self).
  assert (Hb2 : binds x T2 G) by (rewrite E2; apply binds_mid_self).
  assert (Heq : T1 = T2).
  { apply binds_unique with (x := x) (a := T1) (b := T2) (E := G); auto. }
  subst T2.
  assert (AB : A1 = A2 /\ B1 = B2).
  { apply (app_decomp_uniq A1 B1 x T1).
    - rewrite <- E1. exact Huniq.
    - rewrite <- E1. rewrite E2. reflexivity. }
  tauto.
Qed.

(* ============================================================ *)
(* Environment insertion                                        *)
(* ============================================================ *)

Inductive env_insert (A G G' : env) : Prop :=
| ei_intro : forall P Q, G = P ++ Q -> G' = P ++ A ++ Q -> env_insert A G G'.

Lemma env_insert_refl : forall G, env_insert nil G G.
Proof. intros. apply ei_intro with (P := nil) (Q := G); simpl; auto. Qed.

Lemma env_insert_cons : forall A G G' (y:atom) (T:typ),
    env_insert A G G' -> env_insert A (y ~ T ++ G) (y ~ T ++ G').
Proof.
  intros A G G' y T [P Q HG HG'].
  apply ei_intro with (P := (y,T)::P) (Q := Q).
  - simpl. rewrite HG. reflexivity.
  - simpl. rewrite HG'. reflexivity.
Qed.

Lemma env_insert_dom : forall A G G', env_insert A G G' ->
    dom G' [=] dom G \u dom A.
Proof.
  intros A G G' [P Q HG HG']. rewrite HG'. rewrite HG.
  repeat rewrite dom_app. fsetdec.
Qed.

Lemma fv_values_app : forall (f:typ -> atoms) (E F:env),
    fv_values f (E ++ F) [=] fv_values f E \u fv_values f F.
Proof.
  intros f E. induction E as [| [y Ty] E IH]; intros F; simpl.
  - fsetdec.
  - rewrite IH. fsetdec.
Qed.

Lemma env_insert_fv : forall A G G', env_insert A G G' ->
    fv G' [=] fv G \u fv A.
Proof.
  intros A G G' [P Q HG HG']. rewrite HG'. rewrite HG.
  change (dom (P ++ A ++ Q) \u fv_values fv_typ (P ++ A ++ Q)
          [=] (dom (P ++ Q) \u fv_values fv_typ (P ++ Q))
              \u (dom A \u fv_values fv_typ A)).
  repeat rewrite dom_app. repeat rewrite fv_values_app. fsetdec.
Qed.

Lemma env_insert_binds : forall A G G' x T,
    env_insert A G G' -> binds x T G -> binds x T G'.
Proof.
  intros A G G' x T [P Q HG HG'] Hb. rewrite HG' in *. rewrite HG in Hb.
  apply binds_app_1 in Hb. destruct Hb as [Hb | Hb].
  - apply binds_app_2 with (F := A ++ Q) in Hb. exact Hb.
  - apply binds_app_3 with (E := P ++ A) in Hb.
    rewrite app_assoc in Hb. exact Hb.
Qed.

Lemma env_insert_dom_sub : forall A G G', env_insert A G G' ->
    dom G [<=] dom G'.
Proof. intros. pose proof (env_insert_dom H). fsetdec. Qed.

Lemma env_insert_fv_sub : forall A G G', env_insert A G G' ->
    fv G [<=] fv G'.
Proof. intros. pose proof (env_insert_fv H). fsetdec. Qed.

(* ============================================================ *)
(* Kernel insertion                                             *)
(* ============================================================ *)

Lemma fv_open_dom_cons : forall (x:atom) (T U:typ) (G:env),
    fv U [<=] dom G -> fv (open x U) [<=] dom (x ~ T ++ G).
Proof.
  intros. apply Subset_trans with (s' := fv U \u {{x}}).
  - apply fv_open_upper.
  - simpl. fsetdec.
Qed.

Lemma subtysk_insert : forall L (A1 A2 G1 G1' G2 G2' : env) S U,
    fv A1 [<=] L -> fv A2 [<=] L ->
    env_insert A1 G1 G1' -> env_insert A2 G2 G2' ->
    wf_env G1 -> wf_env G2 -> wf_env G1' -> wf_env G2' ->
    fv S [<=] dom G1 -> lc S ->
    fv U [<=] dom G2 -> lc U ->
    [ L ] G1 ⊢k S <⦂ U k⊣ G2 ->
    [ L ] G1' ⊢k S <⦂ U k⊣ G2'.
Proof.
  intros L A1 A2 G1 G1' G2 G2' S U HA1 HA2 EI1 EI2 W1 W2 W1' W2' HS HlcS HU HlcU H.
  revert A1 A2 G1' G2' HA1 HA2 EI1 EI2 W1 W2 W1' W2' HS HlcS HU HlcU.
  induction H as [| | | L0 G1_0 G2_0 Sb T1 T2 Ub H1 IHH1 H2 IHH2
                  | L0 G1_0 G2_0 T1 T2 U1 U2 x0 Hx H1 IHH1 H2 IHH2
                  | L0 G1_0 G2_0 x0 T0 S0 Hb H1 IHH1
                  | L0 G1_0 G2_0 x0 T0 U0 Hb H1 IHH1];
    intros A1 A2 G1' G2' HA1 HA2 EI1 EI2 W1 W2 W1' W2' HS HlcS HU HlcU.
  - apply ssk_refl.
  - apply ssk_top.
  - apply ssk_bot.
  - (* ssk_bnd *)
    apply ssk_bnd.
    + apply (IHH1 A2 A1 G2' G1'); auto.
      * apply Subset_trans with (s' := fv (typ_bnd Sb Ub)).
        -- apply fv_bnd_subset_l.
        -- exact HU.
      * apply lc_bnd_inv in HlcU. tauto.
      * apply Subset_trans with (s' := fv (typ_bnd T1 T2)).
        -- apply fv_bnd_subset_l.
        -- exact HS.
      * apply lc_bnd_inv in HlcS. tauto.
    + apply (IHH2 A1 A2 G1' G2'); auto.
      * apply Subset_trans with (s' := fv (typ_bnd T1 T2)).
        -- apply fv_bnd_subset_r.
        -- exact HS.
      * apply lc_bnd_inv in HlcS. tauto.
      * apply Subset_trans with (s' := fv (typ_bnd Sb Ub)).
        -- apply fv_bnd_subset_r.
        -- exact HU.
      * apply lc_bnd_inv in HlcU. tauto.
  - (* ssk_all *)
    apply ssk_all with (x := x0).
    + pose proof (env_insert_fv EI1) as Efv1.
      pose proof (env_insert_fv EI2) as Efv2.
      fsetdec.
    + apply (IHH1 A2 A1 G2' G1'); auto.
      * apply Subset_trans with (s' := fv (typ_all T2 U2)).
        -- apply fv_all_subset_l.
        -- exact HU.
      * apply lc_all_inv in HlcU. tauto.
      * apply Subset_trans with (s' := fv (typ_all T1 U1)).
        -- apply fv_all_subset_l.
        -- exact HS.
      * apply lc_all_inv in HlcS. tauto.
    + apply (IHH2 A1 A2 ((x0, T1) :: G1') ((x0, T2) :: G2')).
      * fsetdec.
      * fsetdec.
      * apply env_insert_cons. exact EI1.
      * apply env_insert_cons. exact EI2.
      * apply wf_cons.
        -- fsetdec.
        -- apply Subset_trans with (s' := fv (typ_all T1 U1)).
           ++ apply fv_all_subset_l.
           ++ exact HS.
        -- exact W1.
        -- apply lc_all_inv in HlcS. tauto.
      * apply wf_cons.
        -- fsetdec.
        -- apply Subset_trans with (s' := fv (typ_all T2 U2)).
           ++ apply fv_all_subset_l.
           ++ exact HU.
        -- exact W2.
        -- apply lc_all_inv in HlcU. tauto.
      * apply wf_cons.
        -- pose proof (env_insert_fv EI1) as Efv1. fsetdec.
        -- apply Subset_trans with (s' := dom G1_0).
           ++ apply Subset_trans with (s' := fv (typ_all T1 U1)).
              ** apply fv_all_subset_l.
              ** exact HS.
           ++ exact (env_insert_dom_sub EI1).
        -- exact W1'.
        -- apply lc_all_inv in HlcS. tauto.
      * apply wf_cons.
        -- pose proof (env_insert_fv EI2) as Efv2. fsetdec.
        -- apply Subset_trans with (s' := dom G2_0).
           ++ apply Subset_trans with (s' := fv (typ_all T2 U2)).
              ** apply fv_all_subset_l.
              ** exact HU.
           ++ exact (env_insert_dom_sub EI2).
        -- exact W2'.
        -- apply lc_all_inv in HlcU. tauto.
      * apply fv_open_dom_cons.
        apply Subset_trans with (s' := fv (typ_all T1 U1)).
        -- apply fv_all_subset_r.
        -- exact HS.
      * apply lc_open. apply lc_all_inv in HlcS. tauto.
      * apply fv_open_dom_cons.
        apply Subset_trans with (s' := fv (typ_all T2 U2)).
        -- apply fv_all_subset_r.
        -- exact HU.
      * apply lc_open. apply lc_all_inv in HlcU. tauto.
  - (* ssk_sel1 *)
    apply ssk_sel1 with (x := x0) (T := T0).
    + apply env_insert_binds with (A := A2) (G := G2_0); auto.
    + apply (IHH1 A2 A1 G2' G1'); auto.
      * apply wf_env_binds_fv_dom with (x := x0); auto.
      * apply wf_env_binds_lc with (x := x0) (G := G2_0); auto.
      * simpl. fsetdec.
      * apply lc_typ_bnd; [ exact HlcS | apply lc_typ_top ].
  - (* ssk_sel2 *)
    apply ssk_sel2 with (x := x0) (T := T0).
    + apply env_insert_binds with (A := A1) (G := G1_0); auto.
    + apply (IHH1 A1 A2 G1' G2'); auto.
      * apply wf_env_binds_fv_dom with (x := x0); auto.
      * apply wf_env_binds_lc with (x := x0) (G := G1_0); auto.
      * simpl. fsetdec.
      * apply lc_typ_bnd; [ apply lc_typ_bot | exact HlcU ].
Qed.


(* ============================================================ *)
(* Reflexivity of the kernel relation                           *)
(* ============================================================ *)

Fixpoint size_typ (T:typ) : nat :=
  match T with
  | typ_top => 1
  | typ_bot => 1
  | typ_sel _ => 1
  | typ_all T1 T2 => 1 + size_typ T1 + size_typ T2
  | typ_bnd T1 T2 => 1 + size_typ T1 + size_typ T2
  end.

Lemma size_open_rec : forall k u T,
    size_typ (open_rec_typ k u T) = size_typ T.
Proof.
  intros k u T. revert k. induction T as [| |v|T1 IH1 T2 IH2|T1 IH1 T2 IH2];
    simpl; intros k.
  - reflexivity.
  - reflexivity.
  - destruct v; simpl. destruct (k == n); reflexivity. reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
  - rewrite IH1. rewrite IH2. reflexivity.
Qed.

Lemma kernel_refl : forall (T:typ) L G1 G2,
    [ L ] G1 ⊢k T <⦂ T k⊣ G2.
Proof.
  assert (H : forall n (T:typ), size_typ T <= n ->
              forall L G1 G2, [ L ] G1 ⊢k T <⦂ T k⊣ G2).
  { intros n. induction n as [|n IH]; intros T Hn L G1 G2.
    - destruct T; simpl in Hn; lia.
    - destruct T as [| |v|T1 U1|T1 U1]; simpl in Hn.
      + apply ssk_top.
      + apply ssk_bot.
      + apply ssk_refl.
      + destruct (atom_fresh (fv G1 \u fv T1 \u fv U1 \u fv G2 \u L)) as [x Hx].
        apply ssk_all with (x := x).
        * fsetdec.
        * apply IH; lia.
        * apply IH. rewrite size_open_rec. lia.
      + apply ssk_bnd.
        * apply IH; lia.
        * apply IH; lia. }
  intros. apply (H (size_typ T) T); lia.
Qed.

(* ============================================================ *)
(* Invariants of revealing                                      *)
(* ============================================================ *)

Lemma wf_env_cons_inv : forall (x:atom) (T:typ) (G:env),
    wf_env (x ~ T ++ G) ->
    x `notin` fv T \u fv G /\ fv T [<=] dom G /\ wf_env G /\ lc T.
Proof.
  intros x T G H. inversion H. auto.
Qed.

Lemma revealing_wf : forall G T G' U,
    wf_env G -> revealing G T G' U -> wf_env G'.
Proof.
  intros G T G' U Hwf H.
  induction H as [G0 T0 Hns | G0 T0 | G1 G2 G1' T0 x H1 IH1
                  | G1 G2 T0 G1' G1'' x Lb V U' H1 IH1 H2 IH2].
  - exact Hwf.
  - apply wf_nil.
  - apply wf_nil.
  - apply IH2. apply IH1.
    apply wf_env_suffix with (A := x ~ T0).
    apply wf_env_suffix with (A := G2).
    exact Hwf.
Qed.

Lemma revealing_fv : forall G T G' U,
    wf_env G -> fv T [<=] dom G -> revealing G T G' U -> fv U [<=] dom G'.
Proof.
  intros G T G' U Hwf Hfv H.
  induction H as [G0 T0 Hns | G0 T0 | G1 G2 G1' T0 x H1 IH1
                  | G1 G2 T0 G1' G1'' x Lb V U' H1 IH1 H2 IH2].
  - exact Hfv.
  - simpl. fsetdec.
  - simpl. fsetdec.
  - assert (HwfX : wf_env (x ~ T0 ++ G1)).
    { apply wf_env_suffix with (A := G2). exact Hwf. }
    destruct (wf_env_cons_inv HwfX) as [_ [HfvT [Hwf1 HlcT]]].
    assert (HfvB : fv (typ_bnd Lb V) [<=] dom G1') by (apply IH1; assumption).
    assert (HfvV : fv V [<=] dom G1').
    { apply Subset_trans with (s' := fv (typ_bnd Lb V)).
      - apply fv_bnd_subset_r.
      - exact HfvB. }
    apply IH2.
    + exact (revealing_wf Hwf1 H1).
    + exact HfvV.
Qed.

Lemma revealing_lc : forall G T G' U,
    wf_env G -> lc T -> revealing G T G' U -> lc U.
Proof.
  intros G T G' U Hwf Hlc H.
  induction H as [G0 T0 Hns | G0 T0 | G1 G2 G1' T0 x H1 IH1
                  | G1 G2 T0 G1' G1'' x Lb V U' H1 IH1 H2 IH2].
  - exact Hlc.
  - apply lc_typ_top.
  - apply lc_typ_bot.
  - assert (HwfX : wf_env (x ~ T0 ++ G1)).
    { apply wf_env_suffix with (A := G2). exact Hwf. }
    destruct (wf_env_cons_inv HwfX) as [_ [_ [Hwf1 HlcT]]].
    assert (HlcB : lc (typ_bnd Lb V)) by (apply IH1; assumption).
    destruct (lc_bnd_inv HlcB) as [HLb HV].
    apply IH2.
    + exact (revealing_wf Hwf1 H1).
    + exact HV.
Qed.

(* ============================================================ *)
(* More environment facts                                        *)
(* ============================================================ *)

Lemma fv_app_sub_l : forall (A B:env), fv A [<=] fv (A ++ B).
Proof.
  intros A B.
  change (dom A \u fv_values fv_typ A [<=]
          dom (A ++ B) \u fv_values fv_typ (A ++ B)).
  rewrite dom_app. rewrite fv_values_app. fsetdec.
Qed.

Lemma fv_app_sub_r : forall (A B:env), fv B [<=] fv (A ++ B).
Proof.
  intros A B.
  change (dom B \u fv_values fv_typ B [<=]
          dom (A ++ B) \u fv_values fv_typ (A ++ B)).
  rewrite dom_app. rewrite fv_values_app. fsetdec.
Qed.

Lemma dom_app_sub_l : forall (A B:env), dom A [<=] dom (A ++ B).
Proof. intros. rewrite dom_app. fsetdec. Qed.

Lemma dom_app_sub_r : forall (A B:env), dom B [<=] dom (A ++ B).
Proof. intros. rewrite dom_app. fsetdec. Qed.

Lemma env_insert_here : forall (A G:env), env_insert A G (A ++ G).
Proof.
  intros. apply ei_intro with (P := nil) (Q := G); simpl; auto.
Qed.

Lemma revealing_suffix : forall G T G' U,
    revealing G T G' U -> exists P, G = P ++ G'.
Proof.
  intros G T G' U H.
  induction H as [G0 T0 Hns | G0 T0 | G1 G2 G1' T0 x H1 IH1
                  | G1 G2 T0 G1' G1'' x Lb V U' H1 IH1 H2 IH2].
  - exists nil. simpl. reflexivity.
  - exists G0. simpl. rewrite app_nil_r. reflexivity.
  - exists (G2 ++ x ~ T0 ++ G1). simpl. rewrite app_nil_r. reflexivity.
  - destruct IH1 as [P1 E1]. destruct IH2 as [P2 E2].
    exists (G2 ++ x ~ T0 ++ P1 ++ P2).
    rewrite E1. rewrite E2.
    repeat rewrite app_assoc. reflexivity.
Qed.

(* ============================================================ *)
(* Selector-bound correspondence: revealing a bnd to the bottom *)
(* ============================================================ *)

Lemma app_cons_assoc : forall (A G:env) (x:atom) (T:typ) (G1:env),
    A ++ G ++ x ~ T ++ G1 = (A ++ G ++ x ~ T) ++ G1.
Proof. intros. repeat rewrite app_assoc. reflexivity. Qed.

Require Import Arith Wf_nat.

(* ============================================================ *)
(* Size-indexed revealing (for well-founded induction)          *)
(* ============================================================ *)

Inductive revealing_sz : nat -> env -> typ -> env -> typ -> Prop :=
| rsz_stop : forall G T, ~is_sel T -> revealing_sz 1 G T G T
| rsz_top : forall G T, revealing_sz 1 G T nil typ_top
| rsz_bot : forall G1 G2 G1' T x n,
    revealing_sz n G1 T G1' typ_bot ->
    revealing_sz (S n) (G2 ++ x ~ T ++ G1) (typ_sel (avar_f x)) nil typ_bot
| rsz_bnd : forall G1 G2 T G1' G1'' x L U U' n1 n2,
    revealing_sz n1 G1 T G1' (typ_bnd L U) ->
    revealing_sz n2 G1' U G1'' U' ->
    revealing_sz (S (n1 + n2)) (G2 ++ x ~ T ++ G1) (typ_sel (avar_f x)) G1'' U'.

Lemma revealing_sz_revealing : forall n G T G' U,
    revealing_sz n G T G' U -> revealing G T G' U.
Proof.
  intros n G T G' U H.
  induction H as [G0 T0 Hns | G0 T0 | G1 G2 G1' T0 x m Hm IHm
                  | G1 G2 T0 G1' G1'' x Lb V U' n1 n2 Hm1 IHm1 Hm2 IHm2].
  - apply rv_stop; auto.
  - apply rv_top.
  - eapply rv_bot with (G1' := G1'); eauto.
  - eapply rv_bnd with (G1' := G1'); eauto.
Qed.

Lemma revealing_revealing_sz : forall G T G' U,
    revealing G T G' U -> exists n, revealing_sz n G T G' U.
Proof.
  intros G T G' U H.
  induction H as [G0 T0 Hns | G0 T0 | G1 G2 G1' T0 x H1 IH1
                  | G1 G2 T0 G1' G1'' x Lb V U' H1 IH1 H2 IH2].
  - exists 1. apply rsz_stop; auto.
  - exists 1. apply rsz_top.
  - destruct IH1 as [n Hn]. exists (S n). eapply rsz_bot with (G1' := G1'); eauto.
  - destruct IH1 as [n1 Hn1]. destruct IH2 as [n2 Hn2].
    exists (S (n1 + n2)). eapply rsz_bnd; eauto.
Qed.

(* ============================================================ *)
(* Selector-bound correspondence: revealing a bnd to the bottom *)
(* ============================================================ *)

Lemma revealing_bnd_bot_sz : forall (n:nat) L (A G0 G':env) (Tx:typ) (W:typ)
    (Lb V:typ) U (H:env),
    revealing_sz n G0 Tx G' W ->
    W = typ_bnd Lb V ->
    [ L ] G' ⊢k V <⦂ U k⊣ H ->
    wf_env G0 -> wf_env (A ++ G0) -> wf_env H ->
    fv (A ++ G0) [<=] L ->
    fv V [<=] dom G' -> lc V ->
    fv U [<=] dom H -> lc U ->
    [ L ] A ++ G0 ⊢k Tx <⦂ typ_bnd typ_bot U k⊣ H.
Proof.
  intros n. induction n using lt_wf_ind.
  rename H into IHn.
  intros L A G0 G' Tx W Lb V U H Hsz Heq HE WG0 WAG WH HfvL HfvV HlcV HfvU HlcU.
  destruct Hsz as [G T Hns | G T | G1 G2 G1' T x m Hm
                   | G1 G2 T G1' G1'' x Lb0 V0 U' m1 m2 Hm1 Hm2].
  - (* rsz_stop *)
    subst T.
    assert (HE' : [ L ] A ++ G ⊢k V <⦂ U k⊣ H).
    { eapply (@subtysk_insert L A nil G (A ++ G) H H V U).
      - apply Subset_trans with (s' := fv (A ++ G)).
        + apply fv_app_sub_l.
        + exact HfvL.
      - simpl. intros a Ha. fsetdec.
      - apply env_insert_here.
      - apply env_insert_refl.
      - exact WG0.
      - exact WH.
      - exact WAG.
      - exact WH.
      - exact HfvV.
      - exact HlcV.
      - exact HfvU.
      - exact HlcU.
      - exact HE. }
    apply ssk_bnd.
    + apply ssk_bot.
    + exact HE'.
  - (* rsz_top *) discriminate.
  - (* rsz_bot *) discriminate.
  - (* rsz_bnd *)
    subst U'.
    apply ssk_sel2 with (x := x) (T := T).
    + apply binds_app_3. apply binds_app_3.
      apply binds_app_2. apply binds_one_3; auto.
    + assert (HwfX : wf_env (x ~ T ++ G1)).
      { apply wf_env_suffix with (A := G2). exact WG0. }
      destruct (wf_env_cons_inv HwfX) as [_ [HfvT [HwfG1 HlcT]]].
      assert (HwfG1' : wf_env G1').
      { exact (revealing_wf HwfG1 (revealing_sz_revealing Hm1)). }
      assert (HfvB : fv (typ_bnd Lb0 V0) [<=] dom G1').
      { exact (revealing_fv HwfG1 HfvT (revealing_sz_revealing Hm1)). }
      assert (HfvV0 : fv V0 [<=] dom G1').
      { apply Subset_trans with (s' := fv (typ_bnd Lb0 V0)).
        - apply fv_bnd_subset_r.
        - exact HfvB. }
      assert (HlcV0 : lc V0).
      { destruct (lc_bnd_inv (revealing_lc HwfG1 HlcT (revealing_sz_revealing Hm1))) as [_ HV0]. exact HV0. }
      assert (HfvVr : fv V [<=] dom G1'').
      { apply Subset_trans with (s' := fv (typ_bnd Lb V)).
        - apply fv_bnd_subset_r.
        - exact (revealing_fv HwfG1' HfvV0 (revealing_sz_revealing Hm2)). }
      assert (HlcVr : lc V).
      { destruct (lc_bnd_inv (revealing_lc HwfG1' HlcV0 (revealing_sz_revealing Hm2))) as [_ HV]. exact HV. }
      assert (HfvG1 : fv G1 [<=] fv (G2 ++ x ~ T ++ G1)).
      { apply Subset_trans with (s' := fv (x ~ T ++ G1)).
        - apply fv_app_sub_r with (A := x ~ T).
        - apply fv_app_sub_r with (A := G2). }
      assert (HfvG1' : fv G1' [<=] L).
      { destruct (revealing_suffix (revealing_sz_revealing Hm1)) as [P1 E1].
        apply Subset_trans with (s' := fv G1).
        - rewrite E1. apply fv_app_sub_r.
        - apply Subset_trans with (s' := fv (A ++ (G2 ++ x ~ T ++ G1))).
          + apply Subset_trans with (s' := fv (G2 ++ x ~ T ++ G1)).
            * exact HfvG1.
            * apply fv_app_sub_r with (A := A).
          + exact HfvL. }
      assert (Hlt1 : m1 < S (m1 + m2)) by lia.
      assert (Hlt2 : m2 < S (m1 + m2)) by lia.
      assert (HE2 : [ L ] G1' ⊢k V0 <⦂ typ_bnd typ_bot U k⊣ H).
      { eapply (@IHn m2 Hlt2 L nil G1' G1'' V0 (typ_bnd Lb V) Lb V U H).
        - exact Hm2.
        - reflexivity.
        - exact HE.
        - exact HwfG1'.
        - simpl. exact HwfG1'.
        - exact WH.
        - simpl. exact HfvG1'.
        - exact HfvVr.
        - exact HlcVr.
        - exact HfvU.
        - exact HlcU. }
      assert (HF : [ L ] (A ++ G2 ++ x ~ T) ++ G1 ⊢k T <⦂
                    typ_bnd typ_bot (typ_bnd typ_bot U) k⊣ H).
      { eapply (@IHn m1 Hlt1 L (A ++ G2 ++ x ~ T) G1 G1' T (typ_bnd Lb0 V0) Lb0 V0
                  (typ_bnd typ_bot U) H).
        - exact Hm1.
        - reflexivity.
        - exact HE2.
        - exact HwfG1.
        - rewrite <- app_cons_assoc. exact WAG.
        - exact WH.
        - rewrite <- app_cons_assoc. exact HfvL.
        - exact HfvV0.
        - exact HlcV0.
        - simpl. fsetdec.
        - simpl. apply lc_typ_bnd; [ apply lc_typ_bot | exact HlcU ]. }
      rewrite app_cons_assoc. exact HF.
Qed.

Lemma revealing_bnd_bot : forall L (A G0 G':env) (Tx:typ) (Lb V:typ) U (H:env),
    revealing G0 Tx G' (typ_bnd Lb V) ->
    [ L ] G' ⊢k V <⦂ U k⊣ H ->
    wf_env G0 -> wf_env (A ++ G0) -> wf_env H ->
    fv (A ++ G0) [<=] L ->
    fv V [<=] dom G' -> lc V ->
    fv U [<=] dom H -> lc U ->
    [ L ] A ++ G0 ⊢k Tx <⦂ typ_bnd typ_bot U k⊣ H.
Proof.
  intros L A G0 G' Tx Lb V U H Hrev HE WG0 WAG WH HfvL HfvV HlcV HfvU HlcU.
  destruct (revealing_revealing_sz Hrev) as [n Hn].
  eapply revealing_bnd_bot_sz; eauto.
Qed.

(* ============================================================ *)
(* Selector-bound correspondence: revealing a bnd to the top    *)
(* ============================================================ *)

Lemma revealing_bnd_low_sz : forall (n:nat) L (A G0 G':env) (Tx:typ) (W:typ)
    (Lb V:typ) (Gw:env) (Sw Up':typ),
    revealing_sz n G0 Tx G' W ->
    W = typ_bnd Lb V ->
    [ L ] Gw ⊢k Sw <⦂ Lb k⊣ G' ->
    [ L ] G' ⊢k V <⦂ Up' k⊣ Gw ->
    wf_env G0 -> wf_env (A ++ G0) -> wf_env Gw -> wf_env G' ->
    fv (A ++ G0) [<=] L ->
    fv Sw [<=] dom Gw -> lc Sw ->
    fv Lb [<=] dom G' -> lc Lb -> fv V [<=] dom G' -> lc V ->
    fv Up' [<=] dom Gw -> lc Up' ->
    [ L ] A ++ G0 ⊢k Tx <⦂ typ_bnd Sw Up' k⊣ Gw.
Proof.
  intros n. induction n using lt_wf_ind.
  rename H into IHn.
  intros L A G0 G' Tx W Lb V Gw Sw Up' Hsz Heq HE HV WG0 WAG WGw WG' HfvL
         HfvSw HlcSw HfvLb HlcLb HfvV HlcV HfvUp HlcUp.
  destruct Hsz as [G T Hns | G T | G1 G2 G1' T x m Hm
                   | G1 G2 T G1' G1'' x Lb0 V0 U' m1 m2 Hm1 Hm2].
  - (* rsz_stop *)
    subst T.
    assert (HVE : [ L ] A ++ G ⊢k V <⦂ Up' k⊣ Gw).
    { eapply (@subtysk_insert L A nil G (A ++ G) Gw Gw V Up').
      - apply Subset_trans with (s' := fv (A ++ G)).
        + apply fv_app_sub_l.
        + exact HfvL.
      - simpl. intros a Ha. fsetdec.
      - apply env_insert_here.
      - apply env_insert_refl.
      - exact WG0.
      - exact WGw.
      - exact WAG.
      - exact WGw.
      - exact HfvV.
      - exact HlcV.
      - exact HfvUp.
      - exact HlcUp.
      - exact HV. }
    assert (HE' : [ L ] Gw ⊢k Sw <⦂ Lb k⊣ A ++ G).
    { eapply (@subtysk_insert L nil A Gw Gw G (A ++ G) Sw Lb).
      - simpl. intros a Ha. fsetdec.
      - apply Subset_trans with (s' := fv (A ++ G)).
        + apply fv_app_sub_l.
        + exact HfvL.
      - apply env_insert_refl.
      - apply env_insert_here.
      - exact WGw.
      - exact WG0.
      - exact WGw.
      - exact WAG.
      - exact HfvSw.
      - exact HlcSw.
      - exact HfvLb.
      - exact HlcLb.
      - exact HE. }
    apply ssk_bnd.
    + exact HE'.
    + exact HVE.
  - (* rsz_top *) discriminate.
  - (* rsz_bot *) discriminate.
  - (* rsz_bnd *)
    subst U'.
    apply ssk_sel2 with (x := x) (T := T).
    + apply binds_app_3. apply binds_app_3.
      apply binds_app_2. apply binds_one_3; auto.
    + assert (HwfX : wf_env (x ~ T ++ G1)).
      { apply wf_env_suffix with (A := G2). exact WG0. }
      destruct (wf_env_cons_inv HwfX) as [_ [HfvT [HwfG1 HlcT]]].
      assert (HwfG1' : wf_env G1').
      { exact (revealing_wf HwfG1 (revealing_sz_revealing Hm1)). }
      assert (HwfG1'' : wf_env G1'').
      { exact (revealing_wf HwfG1' (revealing_sz_revealing Hm2)). }
      assert (HfvB : fv (typ_bnd Lb0 V0) [<=] dom G1').
      { exact (revealing_fv HwfG1 HfvT (revealing_sz_revealing Hm1)). }
      assert (HfvV0 : fv V0 [<=] dom G1').
      { apply Subset_trans with (s' := fv (typ_bnd Lb0 V0)).
        - apply fv_bnd_subset_r.
        - exact HfvB. }
      assert (HlcV0 : lc V0).
      { destruct (lc_bnd_inv (revealing_lc HwfG1 HlcT (revealing_sz_revealing Hm1))) as [_ HV0]. exact HV0. }
      assert (HfvLb0 : fv Lb0 [<=] dom G1').
      { apply Subset_trans with (s' := fv (typ_bnd Lb0 V0)).
        - apply fv_bnd_subset_l.
        - exact HfvB. }
      assert (HlcLb0 : lc Lb0).
      { destruct (lc_bnd_inv (revealing_lc HwfG1 HlcT (revealing_sz_revealing Hm1))) as [HL0 _]. exact HL0. }
      assert (HfvB2 : fv (typ_bnd Lb V) [<=] dom G1'').
      { exact (revealing_fv HwfG1' HfvV0 (revealing_sz_revealing Hm2)). }
      assert (HfvLb' : fv Lb [<=] dom G1'').
      { apply Subset_trans with (s' := fv (typ_bnd Lb V)).
        - apply fv_bnd_subset_l.
        - exact HfvB2. }
      assert (HlcLb' : lc Lb).
      { destruct (lc_bnd_inv (revealing_lc HwfG1' HlcV0 (revealing_sz_revealing Hm2))) as [HL _]. exact HL. }
      assert (HfvVr : fv V [<=] dom G1'').
      { apply Subset_trans with (s' := fv (typ_bnd Lb V)).
        - apply fv_bnd_subset_r.
        - exact HfvB2. }
      assert (HlcVr : lc V).
      { destruct (lc_bnd_inv (revealing_lc HwfG1' HlcV0 (revealing_sz_revealing Hm2))) as [_ HVr]. exact HVr. }
      assert (HfvG1 : fv G1 [<=] fv (G2 ++ x ~ T ++ G1)).
      { apply Subset_trans with (s' := fv (x ~ T ++ G1)).
        - apply fv_app_sub_r with (A := x ~ T).
        - apply fv_app_sub_r with (A := G2). }
      assert (HfvG1' : fv G1' [<=] L).
      { destruct (revealing_suffix (revealing_sz_revealing Hm1)) as [P1 E1].
        apply Subset_trans with (s' := fv G1).
        - rewrite E1. apply fv_app_sub_r.
        - apply Subset_trans with (s' := fv (A ++ (G2 ++ x ~ T ++ G1))).
          + apply Subset_trans with (s' := fv (G2 ++ x ~ T ++ G1)).
            * exact HfvG1.
            * apply fv_app_sub_r with (A := A).
          + exact HfvL. }
      assert (Hlt1 : m1 < S (m1 + m2)) by lia.
      assert (Hlt2 : m2 < S (m1 + m2)) by lia.
      (* IH on Hm2: V0 <: bnd Sw Up' at G1' *)
      assert (HUP : [ L ] G1' ⊢k V0 <⦂ typ_bnd Sw Up' k⊣ Gw).
      { eapply (@IHn m2 Hlt2 L nil G1' G1'' V0 (typ_bnd Lb V) Lb V Gw Sw Up').
        - exact Hm2.
        - reflexivity.
        - exact HE.
        - exact HV.
        - exact HwfG1'.
        - simpl. exact HwfG1'.
        - exact WGw.
        - exact HwfG1''.
        - simpl. exact HfvG1'.
        - exact HfvSw.
        - exact HlcSw.
        - exact HfvLb'.
        - exact HlcLb'.
        - exact HfvVr.
        - exact HlcVr.
        - exact HfvUp.
        - exact HlcUp. }
      (* IH on Hm1 with lower step ssk_bot and upper step HUP *)
      assert (HLO : [ L ] Gw ⊢k typ_bot <⦂ Lb0 k⊣ G1').
      { apply ssk_bot. }
      assert (HLO2 : [ L ] (A ++ G2 ++ x ~ T) ++ G1 ⊢k T <⦂
                     typ_bnd typ_bot (typ_bnd Sw Up') k⊣ Gw).
      { eapply (@IHn m1 Hlt1 L (A ++ G2 ++ x ~ T) G1 G1' T (typ_bnd Lb0 V0) Lb0 V0
                  Gw typ_bot (typ_bnd Sw Up')).
        - exact Hm1.
        - reflexivity.
        - exact HLO.
        - exact HUP.
        - exact HwfG1.
        - rewrite <- app_cons_assoc. exact WAG.
        - exact WGw.
        - exact HwfG1'.
        - rewrite <- app_cons_assoc. exact HfvL.
        - simpl. fsetdec.
        - simpl. apply lc_typ_bot.
        - exact HfvLb0.
        - exact HlcLb0.
        - exact HfvV0.
        - exact HlcV0.
        - simpl. fsetdec.
        - simpl. apply lc_typ_bnd; [ exact HlcSw | exact HlcUp ]. }
      rewrite app_cons_assoc. exact HLO2.
Qed.

Lemma revealing_bnd_low : forall L (A G0 G':env) (Tx:typ) (Lb V:typ) (Gw:env) (Sw Up':typ),
    revealing G0 Tx G' (typ_bnd Lb V) ->
    [ L ] Gw ⊢k Sw <⦂ Lb k⊣ G' ->
    [ L ] G' ⊢k V <⦂ Up' k⊣ Gw ->
    wf_env G0 -> wf_env (A ++ G0) -> wf_env Gw -> wf_env G' ->
    fv (A ++ G0) [<=] L ->
    fv Sw [<=] dom Gw -> lc Sw ->
    fv Lb [<=] dom G' -> lc Lb -> fv V [<=] dom G' -> lc V ->
    fv Up' [<=] dom Gw -> lc Up' ->
    [ L ] A ++ G0 ⊢k Tx <⦂ typ_bnd Sw Up' k⊣ Gw.
Proof.
  intros L A G0 G' Tx Lb V Gw Sw Up' Hrev HE HV WG0 WAG WGw WG' HfvL
         HfvSw HlcSw HfvLb HlcLb HfvV HlcV HfvUp HlcUp.
  destruct (revealing_revealing_sz Hrev) as [n Hn].
  eapply revealing_bnd_low_sz; eauto.
Qed.
(* ============================================================ *)
(* Boundary elimination for the strong kernel relation.         *)
(* Proved jointly on the size-indexed relation subtysk' by      *)
(* well-founded induction:                                      *)
(*   A. S <: bot  =>  S <: U                                    *)
(*   B. S <: bnd bot X, X ->step Y  =>  S <: bnd bot Y          *)
(*   C. S <: bnd top top  =>  S <: bnd B top                    *)
(*   D. top <: U  =>  B <: U                                    *)
(* ============================================================ *)

Inductive bot_to : typ -> typ -> Prop :=
| bt_bot : forall U, bot_to typ_bot U
| bt_top : forall X, bot_to X typ_top
| bt_bnd : forall X Y, bot_to X Y -> bot_to (typ_bnd typ_bot X) (typ_bnd typ_bot Y)
| bt_low : forall B, bot_to (typ_bnd typ_top typ_top) (typ_bnd B typ_top).

Lemma bot_quad : forall (n:nat),
  (forall L (G1 G2:env) S, subtysk' L G1 S typ_bot G2 n ->
     forall U G3, exists m, subtysk' L G1 S U G3 m)
  /\
  (forall L (Gx:env) S (Gy:env) X, subtysk' L Gx S (typ_bnd typ_bot X) Gy n ->
     forall Y, bot_to X Y -> forall Gz, exists m, subtysk' L Gx S (typ_bnd typ_bot Y) Gz m)
  /\
  (forall L (Gx:env) S (Gy:env), subtysk' L Gx S (typ_bnd typ_top typ_top) Gy n ->
     forall B Gz, exists m, subtysk' L Gx S (typ_bnd B typ_top) Gz m)
  /\
  (forall L (Gx:env) (Gy:env) U, subtysk' L Gx typ_top U Gy n ->
     forall B Gz, exists m, subtysk' L Gz B U Gy m).
Proof.
  intros n. induction n using lt_wf_ind. rename H into IHn.
  repeat split.
  - (* A : bottom elimination *)
    intros L G1 G2 S Hely U G3.
    inversion Hely; subst.
    + exists 1. apply ssk'_bot.
    + destruct (IHn n0 ltac:(lia)) as [IHA [IHB [IHC IHD]]].
      destruct (IHB L G1 T G2 typ_bot H0 U (bt_bot U) G3) as [m Hm].
      exists (S m). apply ssk'_sel2 with (x := x) (T := T); auto.
  - (* B : bottom covariance *)
    intros L Gx S Gy X Hely Y Hbt Gz.
    inversion Hely; subst.
    + exists 1. apply ssk'_bot.
    + destruct (IHn n2 ltac:(lia)) as [IHA [IHB [IHC IHD]]].
      assert (H7' : exists m2, subtysk' L Gx T2 Y Gz m2).
      { destruct Hbt as [U0 | X0b | X0b Y0 Hbt0 | B0].
        - destruct (IHA L Gx Gy T2 H7 U0 Gz) as [m2 Hm2]. exists m2. exact Hm2.
        - exists 1. apply ssk'_top.
        - destruct (IHB L Gx T2 Gy X0b H7 Y0 Hbt0 Gz) as [m2 Hm2].
          exists m2. exact Hm2.
        - destruct (IHC L Gx T2 Gy H7 B0 Gz) as [m2 Hm2]. exists m2. exact Hm2. }
      destruct H7' as [m2 Hm2].
      exists (1 + 1 + m2). eapply ssk'_bnd; [ apply ssk'_bot | exact Hm2 ].
    + destruct (IHn n0 ltac:(lia)) as [IHA [IHB [IHC IHD]]].
      destruct (IHB L Gx T Gy (typ_bnd typ_bot X) H0
                  (typ_bnd typ_bot Y) (bt_bnd Hbt) Gz) as [m Hm].
      exists (S m). apply ssk'_sel2 with (x := x) (T := T); auto.
  - (* C : top-lower covariance *)
    intros L Gx S Gy Hely B Gz.
    inversion Hely; subst.
    + exists 1. apply ssk'_bot.
    + destruct (IHn n1 ltac:(lia)) as [IHA [IHB [IHC IHD]]].
      destruct (IHD L Gy Gx T1 H4 B Gz) as [m1 Hm1].
      exists (1 + m1 + 1). eapply ssk'_bnd; [ exact Hm1 | apply ssk'_top ].
    + destruct (IHn n0 ltac:(lia)) as [IHA [IHB [IHC IHD]]].
      destruct (IHB L Gx T Gy (typ_bnd typ_top typ_top) H0
                  (typ_bnd B typ_top) (bt_low B) Gz) as [m Hm].
      exists (S m). apply ssk'_sel2 with (x := x) (T := T); auto.
  - (* D : top elimination *)
    intros L Gx Gy U Hely B Gz.
    inversion Hely; subst.
    + exists 1. apply ssk'_top.
    + destruct (IHn n0 ltac:(lia)) as [IHA [IHB [IHC IHD]]].
      destruct (IHC L Gy T Gx H0 B Gz) as [m Hm].
      exists (S m). apply ssk'_sel1 with (x := x) (T := T); auto.
Qed.

Lemma subtysk'_subtysk : forall (n:nat) L (G1:env) S U (G2:env),
    subtysk' L G1 S U G2 n -> subtysk L G1 S U G2.
Proof.
  intros n L G1 S U G2 H. induction H.
  - apply ssk_refl.
  - apply ssk_top.
  - apply ssk_bot.
  - eapply ssk_bnd; eauto.
  - eapply ssk_all; eauto.
  - eapply ssk_sel1; eauto.
  - eapply ssk_sel2; eauto.
Qed.

Lemma subtysk_subtysk' : forall L (G1:env) S U (G2:env),
    subtysk L G1 S U G2 -> exists n, subtysk' L G1 S U G2 n.
Proof.
  intros L G1 S U G2 H.
  induction H as [L0 G1_0 G2_0 x0 | L0 G1_0 G2_0 T0 | L0 G1_0 G2_0 T0
    | L0 G1_0 G2_0 Sb T1 T2 Ub H1 IH1 H2 IH2
    | L0 G1_0 G2_0 T1 T2 U1 U2 x0 Hx H1 IH1 H2 IH2
    | L0 G1_0 G2_0 x0 T0 S0 Hb H1 IH1
    | L0 G1_0 G2_0 x0 T0 U0 Hb H1 IH1].
  - exists 1. apply ssk'_refl.
  - exists 1. apply ssk'_top.
  - exists 1. apply ssk'_bot.
  - destruct IH1 as [n1 H1']. destruct IH2 as [n2 H2'].
    exists (1 + n1 + n2). eapply ssk'_bnd; eauto.
  - destruct IH1 as [n1 H1']. destruct IH2 as [n2 H2'].
    exists (1 + n1 + n2). eapply ssk'_all; eauto.
  - destruct IH1 as [n Hn]. exists (1 + n). eapply ssk'_sel1; eauto.
  - destruct IH1 as [n Hn]. exists (1 + n). eapply ssk'_sel2; eauto.
Qed.

Lemma bot_elim : forall L (G1:env) (G2:env) S,
    [ L ] G1 ⊢k S <⦂ typ_bot k⊣ G2 ->
    forall U (G3:env), [ L ] G1 ⊢k S <⦂ U k⊣ G3.
Proof.
  intros L G1 G2 S D.
  destruct (subtysk_subtysk' D) as [n Hn].
  intros U G3.
  destruct (proj1 (bot_quad n) L G1 G2 S Hn U G3) as [m Hm].
  apply subtysk'_subtysk in Hm. exact Hm.
Qed.

Lemma bnd_bot_cov : forall L (Gx:env) S (Gy:env) X,
    [ L ] Gx ⊢k S <⦂ typ_bnd typ_bot X k⊣ Gy ->
    forall Y, bot_to X Y ->
      forall Gz, [ L ] Gx ⊢k S <⦂ typ_bnd typ_bot Y k⊣ Gz.
Proof.
  intros L Gx S Gy X D Y Hbt Gz.
  destruct (subtysk_subtysk' D) as [n Hn].
  destruct (proj1 (proj2 (bot_quad n)) L Gx S Gy X Hn Y Hbt Gz) as [m Hm].
  apply subtysk'_subtysk in Hm. exact Hm.
Qed.

Lemma bnd_top_cov : forall L (Gx:env) S (Gy:env),
    [ L ] Gx ⊢k S <⦂ typ_bnd typ_top typ_top k⊣ Gy ->
    forall B Gz, [ L ] Gx ⊢k S <⦂ typ_bnd B typ_top k⊣ Gz.
Proof.
  intros L Gx S Gy D B Gz.
  destruct (subtysk_subtysk' D) as [n Hn].
  destruct (proj1 (proj2 (proj2 (bot_quad n))) L Gx S Gy Hn B Gz) as [m Hm].
  apply subtysk'_subtysk in Hm. exact Hm.
Qed.

Lemma top_elim : forall L (Gx:env) (Gy:env) U,
    [ L ] Gx ⊢k typ_top <⦂ U k⊣ Gy ->
    forall B Gz, [ L ] Gz ⊢k B <⦂ U k⊣ Gy.
Proof.
  intros L Gx Gy U D B Gz.
  destruct (subtysk_subtysk' D) as [n Hn].
  destruct (proj2 (proj2 (proj2 (bot_quad n))) L Gx Gy U Hn B Gz) as [m Hm].
  apply subtysk'_subtysk in Hm. exact Hm.
Qed.

(* ============================================================ *)
(* Revealing to the bottom gives a kernel judgement at bottom.  *)
(* ============================================================ *)

(* ============================================================ *)
(* Revealing to the bottom gives a kernel judgement at bottom.  *)
(* ============================================================ *)

(* ============================================================ *)
(* Revealing to the bottom gives a kernel judgement at bottom.  *)
(* ============================================================ *)

Lemma binds_mid_self2 : forall (A G B:env) (x:atom) (T:typ),
    binds x T (A ++ G ++ x ~ T ++ B).
Proof.
  intros. apply binds_app_3. apply binds_app_3. apply binds_app_2.
  apply binds_one_3; auto.
Qed.

Lemma revealing_bot_kernel_sz : forall (n:nat) L (A G0 G':env) (Tx W:typ),
    revealing_sz n G0 Tx G' W ->
    W = typ_bot ->
    wf_env G0 -> wf_env (A ++ G0) -> fv (A ++ G0) [<=] L ->
    fv Tx [<=] dom G0 -> lc Tx ->
    [ L ] A ++ G0 ⊢k Tx <⦂ typ_bot k⊣ G'.
Proof.
  intros n. induction n using lt_wf_ind. rename H into IHn.
  intros L A G0 G' Tx W Hsz Heq WG0 WAG HfvL HfvTx HlcTx.
  subst W.
  inversion Hsz; subst.
  - (* rsz_stop : Tx = bot *)
    apply ssk_bot.
  - (* rsz_bot : Tx = sel x *)
    assert (HwfX : wf_env (x ~ T ++ G1)).
    { apply wf_env_suffix with (A := G2). exact WG0. }
    destruct (wf_env_cons_inv HwfX) as [_ [HfvT [HwfG1 HlcT]]].
    assert (IHr : [ L ] (A ++ G2 ++ x ~ T) ++ G1 ⊢k T <⦂ typ_bot k⊣ G1').
    { eapply (@IHn n0); [ lia | exact H | reflexivity
        | exact HwfG1 | rewrite <- app_cons_assoc; exact WAG
        | rewrite <- app_cons_assoc; exact HfvL
        | exact HfvT | exact HlcT ]. }
    assert (Hbe : [ L ] (A ++ G2 ++ x ~ T) ++ G1 ⊢k T <⦂ typ_bnd typ_bot typ_bot k⊣ nil).
    { eapply bot_elim. exact IHr. }
    apply ssk_sel2 with (x := x) (T := T).
    + apply binds_mid_self2.
    + replace (A ++ G2 ++ x ~ T ++ G1) with ((A ++ G2 ++ x ~ T) ++ G1).
      * exact Hbe.
      * symmetry. apply app_cons_assoc.
  - (* rsz_bnd : Tx = sel x *)
    assert (HwfX : wf_env (x ~ T ++ G1)).
    { apply wf_env_suffix with (A := G2). exact WG0. }
    destruct (wf_env_cons_inv HwfX) as [_ [HfvT [HwfG1 HlcT]]].
    assert (HwfG1' : wf_env G1').
    { exact (revealing_wf HwfG1 (revealing_sz_revealing H)). }
    assert (HwfGr : wf_env G').
    { exact (revealing_wf HwfG1' (revealing_sz_revealing H0)). }
    assert (HfvB : fv (typ_bnd L0 U) [<=] dom G1').
    { exact (revealing_fv HwfG1 HfvT (revealing_sz_revealing H)). }
    assert (HfvV0 : fv U [<=] dom G1').
    { apply Subset_trans with (s' := fv (typ_bnd L0 U)).
      - apply fv_bnd_subset_r.
      - exact HfvB. }
    assert (HlcV0 : lc U).
    { destruct (lc_bnd_inv (revealing_lc HwfG1 HlcT (revealing_sz_revealing H))) as [_ HV0]. exact HV0. }
    assert (HfvG1 : fv G1 [<=] fv (G2 ++ x ~ T ++ G1)).
    { apply Subset_trans with (s' := fv (x ~ T ++ G1)).
      - apply fv_app_sub_r with (A := x ~ T).
      - apply fv_app_sub_r with (A := G2). }
    assert (HfvG1' : fv G1' [<=] L).
    { destruct (revealing_suffix (revealing_sz_revealing H)) as [P1 E1].
      apply Subset_trans with (s' := fv G1).
      - rewrite E1. apply fv_app_sub_r.
      - apply Subset_trans with (s' := fv (A ++ (G2 ++ x ~ T ++ G1))).
        + apply Subset_trans with (s' := fv (G2 ++ x ~ T ++ G1)).
          * exact HfvG1.
          * apply fv_app_sub_r with (A := A).
        + exact HfvL. }
    assert (HE : [ L ] G1' ⊢k U <⦂ typ_bot k⊣ G').
    { eapply (@IHn n2 ltac:(lia) L nil G1' G' U typ_bot);
        [ exact H0 | reflexivity
        | exact HwfG1' | simpl; exact HwfG1'
        | simpl; exact HfvG1' | exact HfvV0 | exact HlcV0 ]. }
    assert (Hrb : [ L ] (A ++ G2 ++ x ~ T) ++ G1 ⊢k T <⦂ typ_bnd typ_bot typ_bot k⊣ G').
    { eapply revealing_bnd_bot; [ exact (revealing_sz_revealing H) | exact HE
        | exact HwfG1 | rewrite <- app_cons_assoc; exact WAG
        | exact HwfGr | rewrite <- app_cons_assoc; exact HfvL
        | exact HfvV0 | exact HlcV0
        | simpl; fsetdec | simpl; apply lc_typ_bot ]. }
    apply ssk_sel2 with (x := x) (T := T).
    + apply binds_mid_self2.
    + replace (A ++ G2 ++ x ~ T ++ G1) with ((A ++ G2 ++ x ~ T) ++ G1).
      * exact Hrb.
      * symmetry. apply app_cons_assoc.
Qed.

Lemma revealing_bot_kernel : forall L (A G0 G':env) (Tx:typ),
    revealing G0 Tx G' typ_bot ->
    wf_env G0 -> wf_env (A ++ G0) -> fv (A ++ G0) [<=] L ->
    fv Tx [<=] dom G0 -> lc Tx ->
    [ L ] A ++ G0 ⊢k Tx <⦂ typ_bot k⊣ G'.
Proof.
  intros L A G0 G' Tx Hrev WG0 WAG HfvL HfvTx HlcTx.
  destruct (revealing_revealing_sz Hrev) as [n Hn].
  eapply revealing_bot_kernel_sz; eauto.
Qed.

Lemma app_x_cons_assoc : forall (A B:env) (x:atom) (T:typ),
    (A ++ x ~ T) ++ B = A ++ x ~ T ++ B.
Proof. intros. rewrite app_assoc. reflexivity. Qed.

(* ============================================================ *)
(* Upcast followed by a kernel judgement                       *)
(* ============================================================ *)

Lemma upcast_kernel_cont : forall (G:env) (x:avar) (G':env) T,
    upcast G x G' T ->
    forall L U (H:env),
      [ L ] G' ⊢k T <⦂ U k⊣ H ->
      wf_env G -> wf_env G' -> wf_env H ->
      fv G [<=] L -> fv T [<=] dom G' -> lc T ->
      fv U [<=] dom H -> lc U ->
      [ L ] G ⊢k typ_sel x <⦂ U k⊣ H.
Proof.
  intros G x G' T Hup.
  induction Hup as [G0 x0 | G1 G2 x0 T0 G1' Hrev | G1 G2 x0 T0 G1' Lb V0 Hrev];
    intros L U H HE WG WG' WH HfvG HfvT HlcT HfvU HlcU.
  - (* uc_top *)
    eapply top_elim. exact HE.
  - (* uc_bot *)
    assert (HwfX : wf_env (x0 ~ T0 ++ G1)).
    { apply wf_env_suffix with (A := G2). exact WG. }
    destruct (wf_env_cons_inv HwfX) as [_ [HfvT0 [HwfG1 HlcT0]]].
    assert (HR : [ L ] (G2 ++ x0 ~ T0) ++ G1 ⊢k T0 <⦂ typ_bot k⊣ G1').
    { eapply revealing_bot_kernel; [ exact Hrev
        | exact HwfG1 | rewrite app_x_cons_assoc; exact WG
        | rewrite app_x_cons_assoc; exact HfvG
        | exact HfvT0 | exact HlcT0 ]. }
    assert (Hbe : [ L ] (G2 ++ x0 ~ T0) ++ G1 ⊢k T0 <⦂ typ_bnd typ_bot U k⊣ H).
    { eapply bot_elim. exact HR. }
    apply ssk_sel2 with (x := x0) (T := T0).
    + apply binds_mid_self.
    + rewrite <- app_x_cons_assoc. exact Hbe.
  - (* uc_bnd *)
    assert (HwfX : wf_env (x0 ~ T0 ++ G1)).
    { apply wf_env_suffix with (A := G2). exact WG. }
    destruct (wf_env_cons_inv HwfX) as [_ [HfvT0 [HwfG1 HlcT0]]].
    assert (HfvB : fv (typ_bnd Lb V0) [<=] dom G1').
    { exact (revealing_fv HwfG1 HfvT0 Hrev). }
    assert (HfvV : fv V0 [<=] dom G1').
    { apply Subset_trans with (s' := fv (typ_bnd Lb V0)).
      - apply fv_bnd_subset_r.
      - exact HfvB. }
    assert (HlcV : lc V0).
    { destruct (lc_bnd_inv (revealing_lc HwfG1 HlcT0 Hrev)) as [_ HV]. exact HV. }
    assert (Hrb : [ L ] (G2 ++ x0 ~ T0) ++ G1 ⊢k T0 <⦂ typ_bnd typ_bot U k⊣ H).
    { eapply revealing_bnd_bot; [ exact Hrev | exact HE
        | exact HwfG1 | rewrite app_x_cons_assoc; exact WG
        | exact WH | rewrite app_x_cons_assoc; exact HfvG
        | exact HfvV | exact HlcV | exact HfvU | exact HlcU ]. }
    apply ssk_sel2 with (x := x0) (T := T0).
    + apply binds_mid_self.
    + rewrite <- app_x_cons_assoc. exact Hrb.
Qed.

(* ============================================================ *)
(* Downcast preceded by a kernel judgement                     *)
(* ============================================================ *)

Lemma downcast_kernel_cont : forall (G:env) (x:avar) (G':env) T,
    downcast G x G' T ->
    forall L (Gw:env) S,
      [ L ] Gw ⊢k S <⦂ T k⊣ G' ->
      wf_env G -> wf_env G' -> wf_env Gw ->
      fv S [<=] dom Gw -> lc S -> fv G [<=] L ->
      [ L ] Gw ⊢k S <⦂ typ_sel x k⊣ G.
Proof.
  intros G x G' T Hdc.
  induction Hdc as [G0 x0 | G1 G2 x0 T0 G1' Hrev | G1 G2 x0 T0 G1' Lb V0 Hrev];
    intros L Gw S HE WG WG' WGw HfvS HlcS HfvG.
  - (* dc_bot *)
    eapply bot_elim. exact HE.
  - (* dc_top *)
    assert (HwfX : wf_env (x0 ~ T0 ++ G1)).
    { apply wf_env_suffix with (A := G2). exact WG. }
    destruct (wf_env_cons_inv HwfX) as [_ [HfvT0 [HwfG1 HlcT0]]].
    assert (HR : [ L ] (G2 ++ x0 ~ T0) ++ G1 ⊢k T0 <⦂ typ_bot k⊣ G1').
    { eapply revealing_bot_kernel; [ exact Hrev
        | exact HwfG1 | rewrite app_x_cons_assoc; exact WG
        | rewrite app_x_cons_assoc; exact HfvG
        | exact HfvT0 | exact HlcT0 ]. }
    assert (Hbe : [ L ] (G2 ++ x0 ~ T0) ++ G1 ⊢k T0 <⦂ typ_bnd S typ_top k⊣ Gw).
    { eapply bot_elim. exact HR. }
    apply ssk_sel1 with (x := x0) (T := T0).
    + apply binds_mid_self.
    + rewrite <- app_x_cons_assoc. exact Hbe.
  - (* dc_bnd *)
    assert (HwfX : wf_env (x0 ~ T0 ++ G1)).
    { apply wf_env_suffix with (A := G2). exact WG. }
    destruct (wf_env_cons_inv HwfX) as [_ [HfvT0 [HwfG1 HlcT0]]].
    assert (HwfG1' : wf_env G1').
    { exact (revealing_wf HwfG1 Hrev). }
    assert (HfvB : fv (typ_bnd Lb V0) [<=] dom G1').
    { exact (revealing_fv HwfG1 HfvT0 Hrev). }
    assert (HfvLb : fv Lb [<=] dom G1').
    { apply Subset_trans with (s' := fv (typ_bnd Lb V0)).
      - apply fv_bnd_subset_l.
      - exact HfvB. }
    assert (HlcLb : lc Lb).
    { destruct (lc_bnd_inv (revealing_lc HwfG1 HlcT0 Hrev)) as [HL _]. exact HL. }
    assert (HfvV : fv V0 [<=] dom G1').
    { apply Subset_trans with (s' := fv (typ_bnd Lb V0)).
      - apply fv_bnd_subset_r.
      - exact HfvB. }
    assert (HlcV : lc V0).
    { destruct (lc_bnd_inv (revealing_lc HwfG1 HlcT0 Hrev)) as [_ HV]. exact HV. }
    assert (Htop : [ L ] G1' ⊢k V0 <⦂ typ_top k⊣ Gw).
    { apply ssk_top. }
    assert (Hrb : [ L ] (G2 ++ x0 ~ T0) ++ G1 ⊢k T0 <⦂ typ_bnd S typ_top k⊣ Gw).
    { eapply revealing_bnd_low; [ exact Hrev | exact HE | exact Htop
        | exact HwfG1 | rewrite app_x_cons_assoc; exact WG
        | exact WGw | exact HwfG1'
        | rewrite app_x_cons_assoc; exact HfvG
        | exact HfvS | exact HlcS | exact HfvLb | exact HlcLb
        | exact HfvV | exact HlcV | simpl; fsetdec | simpl; apply lc_typ_top ]. }
    apply ssk_sel1 with (x := x0) (T := T0).
    + apply binds_mid_self.
    + rewrite <- app_x_cons_assoc. exact Hrb.
Qed.

(* ============================================================ *)
(* Well-formedness of upcast / downcast results                 *)
(* ============================================================ *)

Lemma upcast_wf : forall (G:env) (x:avar) (G':env) T,
    upcast G x G' T -> wf_env G -> wf_env G'.
Proof.
  intros G x G' T Hup. induction Hup as [G0 x0 | G1 G2 x0 T0 G1' Hrev
                                         | G1 G2 x0 T0 G1' Lb V0 Hrev];
    intros WG.
  - simpl. apply wf_nil.
  - simpl. apply wf_nil.
  - assert (HwfG1 : wf_env G1).
    { apply wf_env_suffix with (A := x0 ~ T0).
      apply wf_env_suffix with (A := G2). exact WG. }
    exact (revealing_wf HwfG1 Hrev).
Qed.

Lemma upcast_fv_lc : forall (G:env) (x:avar) (G':env) T,
    upcast G x G' T -> wf_env G -> fv T [<=] dom G' /\ lc T.
Proof.
  intros G x G' T Hup. induction Hup as [G0 x0 | G1 G2 x0 T0 G1' Hrev
                                         | G1 G2 x0 T0 G1' Lb V0 Hrev];
    intros WG.
  - simpl. split; [ fsetdec | apply lc_typ_top ].
  - simpl. split; [ fsetdec | apply lc_typ_bot ].
  - assert (HwfX : wf_env (x0 ~ T0 ++ G1)).
    { apply wf_env_suffix with (A := G2). exact WG. }
    destruct (wf_env_cons_inv HwfX) as [_ [HfvT [HwfG1 HlcT]]].
    assert (HfvB : fv (typ_bnd Lb V0) [<=] dom G1').
    { exact (revealing_fv HwfG1 HfvT Hrev). }
    assert (HlcB : lc (typ_bnd Lb V0)).
    { exact (revealing_lc HwfG1 HlcT Hrev). }
    split.
    + apply Subset_trans with (s' := fv (typ_bnd Lb V0)).
      * apply fv_bnd_subset_r.
      * exact HfvB.
    + destruct (lc_bnd_inv HlcB) as [_ HV]. exact HV.
Qed.

Lemma downcast_wf : forall (G:env) (x:avar) (G':env) T,
    downcast G x G' T -> wf_env G -> wf_env G'.
Proof.
  intros G x G' T Hdc. induction Hdc as [G0 x0 | G1 G2 x0 T0 G1' Hrev
                                          | G1 G2 x0 T0 G1' Lb V0 Hrev];
    intros WG.
  - simpl. apply wf_nil.
  - simpl. apply wf_nil.
  - assert (HwfG1 : wf_env G1).
    { apply wf_env_suffix with (A := x0 ~ T0).
      apply wf_env_suffix with (A := G2). exact WG. }
    exact (revealing_wf HwfG1 Hrev).
Qed.

Lemma downcast_fv_lc : forall (G:env) (x:avar) (G':env) T,
    downcast G x G' T -> wf_env G -> fv T [<=] dom G' /\ lc T.
Proof.
  intros G x G' T Hdc. induction Hdc as [G0 x0 | G1 G2 x0 T0 G1' Hrev
                                          | G1 G2 x0 T0 G1' Lb V0 Hrev];
    intros WG.
  - simpl. split; [ fsetdec | apply lc_typ_bot ].
  - simpl. split; [ fsetdec | apply lc_typ_top ].
  - assert (HwfX : wf_env (x0 ~ T0 ++ G1)).
    { apply wf_env_suffix with (A := G2). exact WG. }
    destruct (wf_env_cons_inv HwfX) as [_ [HfvT [HwfG1 HlcT]]].
    assert (HfvB : fv (typ_bnd Lb V0) [<=] dom G1').
    { exact (revealing_fv HwfG1 HfvT Hrev). }
    assert (HlcB : lc (typ_bnd Lb V0)).
    { exact (revealing_lc HwfG1 HlcT Hrev). }
    split.
    + apply Subset_trans with (s' := fv (typ_bnd Lb V0)).
      * apply fv_bnd_subset_l.
      * exact HfvB.
    + destruct (lc_bnd_inv HlcB) as [HL _]. exact HL.
Qed.

(* ============================================================ *)
(* Filtering environments by a set of variables                 *)
(* ============================================================ *)

Definition env_filter (X:atoms) (G:env) : env :=
  filter (fun p => AtomSetImpl.mem (fst p) X) G.

Lemma env_filter_app : forall X (A B:env),
    env_filter X (A ++ B) = env_filter X A ++ env_filter X B.
Proof. intros. apply filter_app. Qed.

Lemma env_filter_nil : forall X, env_filter X nil = nil.
Proof. reflexivity. Qed.

Lemma env_filter_cons_mem : forall X (x:atom) (T:typ) (G:env),
    x `in` X -> env_filter X (x ~ T ++ G) = x ~ T ++ env_filter X G.
Proof.
  intros X x T G Hin. unfold env_filter. simpl.
  assert (Hm : AtomSetImpl.mem x X = true).
  { apply AtomSetImpl.mem_1. exact Hin. }
  rewrite Hm. reflexivity.
Qed.

Lemma env_filter_cons_notmem : forall X (x:atom) (T:typ) (G:env),
    x `notin` X -> env_filter X (x ~ T ++ G) = env_filter X G.
Proof.
  intros X x T G Hin. unfold env_filter. simpl.
  assert (Hm : AtomSetImpl.mem x X = false).
  { destruct (AtomSetImpl.mem x X) eqn:E; auto. exfalso. apply Hin.
    apply AtomSetImpl.mem_2. exact E. }
  rewrite Hm. reflexivity.
Qed.

Lemma env_filter_binds : forall X (G:env) x T,
    binds x T (env_filter X G) <-> binds x T G /\ x `in` X.
Proof.
  intros. unfold env_filter, binds. rewrite filter_In. simpl. split.
  - intros [Hin Hm]. split; auto. apply AtomSetImpl.mem_2. exact Hm.
  - intros [Hin Hx]. split; auto. apply AtomSetImpl.mem_1. exact Hx.
Qed.

Lemma env_filter_binds_2 : forall X (G:env) x T,
    binds x T (env_filter X G) -> binds x T G.
Proof. intros. apply env_filter_binds in H. tauto. Qed.

Lemma env_filter_binds_in : forall X (G:env) x T,
    binds x T (env_filter X G) -> x `in` X.
Proof. intros. apply env_filter_binds in H. tauto. Qed.

Lemma env_filter_binds_1 : forall X (G:env) x T,
    binds x T G -> x `in` X -> binds x T (env_filter X G).
Proof. intros. apply env_filter_binds. auto. Qed.

Lemma dom_env_filter_sub : forall X (G:env),
    dom (env_filter X G) [<=] dom G.
Proof.
  intros X G. unfold env_filter.
  induction G as [| [y U] G IH]; simpl.
  - fsetdec.
  - destruct (AtomSetImpl.mem y X); simpl; fsetdec.
Qed.

Lemma fv_values_env_filter_sub : forall X (G:env),
    fv_values fv_typ (env_filter X G) [<=] fv_values fv_typ G.
Proof.
  intros X G. unfold env_filter.
  induction G as [| [y U] G IH]; simpl.
  - fsetdec.
  - destruct (AtomSetImpl.mem y X); simpl; fsetdec.
Qed.

Lemma env_filter_fv_sub : forall X (G:env), fv (env_filter X G) [<=] fv G.
Proof.
  intros X G.
  change (dom (env_filter X G) \u fv_values fv_typ (env_filter X G)
          [<=] dom G \u fv_values fv_typ G).
  pose proof (dom_env_filter_sub X G).
  pose proof (fv_values_env_filter_sub X G). fsetdec.
Qed.

Lemma env_filter_dom_sub : forall X (G:env),
    dom G [<=] X -> env_filter X G = G.
Proof.
  intros X G H. unfold env_filter.
  induction G as [| [y U] G IH]; simpl.
  - reflexivity.
  - assert (Hy : y `in` X) by (apply H; simpl; fsetdec).
    rewrite (AtomSetImpl.mem_1 Hy). rewrite IH.
    + reflexivity.
    + intros z Hz. apply H. simpl. fsetdec.
Qed.

Lemma mem_union_singleton_not : forall (X:atoms) x y, y <> x ->
    AtomSetImpl.mem y (X \u {{x}}) = AtomSetImpl.mem y X.
Proof.
  intros X x y Hyx.
  destruct (AtomSetImpl.mem y (X \u {{x}})) eqn:E1;
    destruct (AtomSetImpl.mem y X) eqn:E2; auto; exfalso.
  - assert (Hin : y \in X \u {{x}}) by (apply AtomSetImpl.mem_2; exact E1).
    assert (Hnot : y \notin X).
    { intro HX. rewrite (AtomSetImpl.mem_1 HX) in E2. discriminate. }
    fsetdec.
  - assert (Hin : y \in X) by (apply AtomSetImpl.mem_2; exact E2).
    assert (Hin2 : y \in X \u {{x}}) by fsetdec.
    rewrite (AtomSetImpl.mem_1 Hin2) in E1. discriminate.
Qed.

Lemma env_filter_union_notin : forall X (x:atom) (G:env),
    x `notin` dom G -> env_filter (X \u {{x}}) G = env_filter X G.
Proof.
  intros X x G Hx. unfold env_filter.
  apply filter_ext_in. intros [y U] Hin. simpl.
  apply mem_union_singleton_not.
  intro Heq. subst. apply Hx. apply binds_In with (a := U). exact Hin.
Qed.

Lemma env_filter_mid : forall X (A:env) (x:atom) (T:typ) (B:env),
    x `in` X ->
    env_filter X (A ++ x ~ T ++ B) = env_filter X A ++ x ~ T ++ env_filter X B.
Proof.
  intros. rewrite env_filter_app.
  rewrite (env_filter_cons_mem (X := X) (x := x) T B H).
  reflexivity.
Qed.

Lemma mem_false : forall (X:atoms) x, x `notin` X -> AtomSetImpl.mem x X = false.
Proof.
  intros X x H. destruct (AtomSetImpl.mem x X) eqn:E; auto. exfalso.
  apply H. apply AtomSetImpl.mem_2. exact E.
Qed.

Lemma env_filter_notin_all : forall X (G:env),
    (forall y, y `in` dom G -> y `notin` X) -> env_filter X G = nil.
Proof.
  intros X G H. unfold env_filter.
  induction G as [| [y U] G IH]; simpl.
  - reflexivity.
  - assert (Hy : y `notin` X) by (apply H; simpl; fsetdec).
    rewrite (mem_false Hy). simpl.
    apply IH. intros z Hz. apply H. simpl; fsetdec.
Qed.

Lemma env_filter_suffix : forall (A:env) (x:atom) (T:typ) (B:env),
    wf_env (A ++ x ~ T ++ B) -> env_filter (dom B) (A ++ x ~ T ++ B) = B.
Proof.
  intros A x T B W.
  assert (Huniq : uniq (A ++ x ~ T ++ B)) by (apply wf_env_uniq; exact W).
  assert (HxB : x `notin` dom B).
  { assert (W1 : wf_env (x ~ T ++ B)).
    { apply wf_env_suffix with (A := A). exact W. }
    destruct (wf_env_cons_inv W1) as [Hfr _].
    intro Hin. apply Hfr. pose proof (dom_subset_fv B). fsetdec. }
  assert (HA : forall y, y `in` dom A -> y `notin` dom B).
  { intros y Hy HyB.
    assert (Hd : disjoint A (x ~ T ++ B)) by (apply uniq_app_3; exact Huniq).
    unfold disjoint in Hd.
    assert (Hin : y \in AtomSetImpl.inter (dom A) (dom (x ~ T ++ B))).
    { simpl. fsetdec. }
    apply (Hd y) in Hin. fsetdec. }
  rewrite env_filter_app.
  rewrite (env_filter_cons_notmem (X := dom B) (x := x) T B HxB).
  assert (HB : env_filter (dom B) B = B).
  { apply env_filter_dom_sub. fsetdec. }
  assert (HAnil : env_filter (dom B) A = nil).
  { apply env_filter_notin_all. exact HA. }
  rewrite HAnil, HB. reflexivity.
Qed.

Lemma revealing_filter : forall (G:env) T (G':env) U,
    revealing G T G' U ->
    forall X, wf_env G -> wf_env (env_filter X G) ->
      fv T [<=] dom (env_filter X G) ->
      exists G'', revealing (env_filter X G) T G'' U /\ G'' = env_filter X G'.
Proof.
  intros G T G' U Hrev.
  induction Hrev as [G0 T0 Hns | G0 T0
                  | G1 G2 G1' T0 x Rev1 IH1
                  | G1 G2 T0 G1' G1'' x Lb V U' Rev1 IH1 Rev2 IH2];
    intros X W WF HfvT.
  - exists (env_filter X G0). split.
    + apply rv_stop. exact Hns.
    + reflexivity.
  - exists nil. split.
    + apply rv_top.
    + rewrite env_filter_nil. reflexivity.
  - (* rv_bot *)
    assert (HxF : x \in dom (env_filter X (G2 ++ x ~ T0 ++ G1))).
    { simpl in HfvT. fsetdec. }
    destruct (@binds_In_inv typ x _ HxF) as [Tz Hbz].
    assert (HxX : x `in` X) by (apply env_filter_binds_in with (G := G2 ++ x ~ T0 ++ G1) (T := Tz); exact Hbz).
    assert (HbzG : binds x Tz (G2 ++ x ~ T0 ++ G1))
      by (apply env_filter_binds_2 with (X := X); exact Hbz).
    assert (Huniq : uniq (G2 ++ x ~ T0 ++ G1)) by (apply wf_env_uniq; exact W).
    assert (HTz : Tz = T0) by (eapply binds_mid_eq; eauto).
    subst Tz.
    assert (Hdec : env_filter X (G2 ++ x ~ T0 ++ G1)
                   = env_filter X G2 ++ x ~ T0 ++ env_filter X G1)
      by (apply env_filter_mid; exact HxX).
    assert (WF1 : wf_env (env_filter X G1)).
    { rewrite Hdec in WF.
      apply wf_env_suffix with (A := x ~ T0).
      apply wf_env_suffix with (A := env_filter X G2). exact WF. }
    assert (HfvT0 : fv T0 [<=] dom (env_filter X G1)).
    { rewrite Hdec in WF.
      assert (Wsplit : wf_env (x ~ T0 ++ env_filter X G1)).
      { apply wf_env_suffix with (A := env_filter X G2). exact WF. }
      destruct (wf_env_cons_inv Wsplit) as [_ [Hfv [_ _]]]. exact Hfv. }
    assert (W1 : wf_env G1).
    { apply wf_env_suffix with (A := x ~ T0).
      apply wf_env_suffix with (A := G2). exact W. }
    destruct (IH1 X W1 WF1 HfvT0) as [G1a [Hrev1a HG1a]].
    exists nil. split.
    + rewrite Hdec. eapply rv_bot. exact Hrev1a.
    + rewrite env_filter_nil. reflexivity.
  - (* rv_bnd *)
    assert (HxF : x \in dom (env_filter X (G2 ++ x ~ T0 ++ G1))).
    { simpl in HfvT. fsetdec. }
    destruct (@binds_In_inv typ x _ HxF) as [Tz Hbz].
    assert (HxX : x `in` X) by (apply env_filter_binds_in with (G := G2 ++ x ~ T0 ++ G1) (T := Tz); exact Hbz).
    assert (HbzG : binds x Tz (G2 ++ x ~ T0 ++ G1))
      by (apply env_filter_binds_2 with (X := X); exact Hbz).
    assert (Huniq : uniq (G2 ++ x ~ T0 ++ G1)) by (apply wf_env_uniq; exact W).
    assert (HTz : Tz = T0) by (eapply binds_mid_eq; eauto).
    subst Tz.
    assert (Hdec : env_filter X (G2 ++ x ~ T0 ++ G1)
                   = env_filter X G2 ++ x ~ T0 ++ env_filter X G1)
      by (apply env_filter_mid; exact HxX).
    assert (W1 : wf_env G1).
    { apply wf_env_suffix with (A := x ~ T0).
      apply wf_env_suffix with (A := G2). exact W. }
    assert (WF1 : wf_env (env_filter X G1)).
    { rewrite Hdec in WF.
      apply wf_env_suffix with (A := x ~ T0).
      apply wf_env_suffix with (A := env_filter X G2). exact WF. }
    assert (HfvT0 : fv T0 [<=] dom (env_filter X G1)).
    { rewrite Hdec in WF.
      assert (Wsplit : wf_env (x ~ T0 ++ env_filter X G1)).
      { apply wf_env_suffix with (A := env_filter X G2). exact WF. }
      destruct (wf_env_cons_inv Wsplit) as [_ [Hfv [_ _]]]. exact Hfv. }
    destruct (IH1 X W1 WF1 HfvT0) as [G1a [Hrev1a HG1a]].
    assert (W1' : wf_env G1') by (apply revealing_wf with (G := G1) (T := T0) (G' := G1') (U := typ_bnd Lb V); auto).
    assert (WF1' : wf_env (env_filter X G1')).
    { rewrite <- HG1a. apply revealing_wf with (G := env_filter X G1) (T := T0) (G' := G1a) (U := typ_bnd Lb V); auto. }
    assert (HfvV : fv V [<=] dom (env_filter X G1')).
    { rewrite <- HG1a.
      assert (HfvB : fv (typ_bnd Lb V) [<=] dom G1a).
      { apply revealing_fv with (G := env_filter X G1) (T := T0); auto. }
      apply Subset_trans with (s' := fv (typ_bnd Lb V)); [ apply fv_bnd_subset_r | exact HfvB ]. }
    destruct (IH2 X W1' WF1' HfvV) as [G1b [Hrev2b HG1b]].
    exists G1b. split.
    + rewrite Hdec. eapply rv_bnd.
      * exact Hrev1a.
      * rewrite HG1a. exact Hrev2b.
    + rewrite HG1b. reflexivity.
Qed.

Lemma env_filter_binding_split : forall X (G2:env) (x:atom) (T0:typ) (G1:env),
    wf_env (G2 ++ x ~ T0 ++ G1) ->
    wf_env (env_filter X (G2 ++ x ~ T0 ++ G1)) ->
    x `in` dom (env_filter X (G2 ++ x ~ T0 ++ G1)) ->
    x `in` X /\
    env_filter X (G2 ++ x ~ T0 ++ G1)
      = env_filter X G2 ++ x ~ T0 ++ env_filter X G1 /\
    wf_env G1 /\ wf_env (env_filter X G1) /\ fv T0 [<=] dom (env_filter X G1).
Proof.
  intros X G2 x T0 G1 W WF HxF.
  destruct (@binds_In_inv typ x _ HxF) as [Tz Hbz].
  assert (HxX : x `in` X)
    by (apply env_filter_binds_in with (G := G2 ++ x ~ T0 ++ G1) (T := Tz); exact Hbz).
  assert (HbzG : binds x Tz (G2 ++ x ~ T0 ++ G1))
    by (apply env_filter_binds_2 with (X := X); exact Hbz).
  assert (Huniq : uniq (G2 ++ x ~ T0 ++ G1)) by (apply wf_env_uniq; exact W).
  assert (HTz : Tz = T0) by (eapply binds_mid_eq; eauto). subst Tz.
  assert (Hdec : env_filter X (G2 ++ x ~ T0 ++ G1)
                 = env_filter X G2 ++ x ~ T0 ++ env_filter X G1)
    by (apply env_filter_mid; exact HxX).
  assert (W1 : wf_env G1).
  { apply wf_env_suffix with (A := x ~ T0).
    apply wf_env_suffix with (A := G2). exact W. }
  assert (WF1 : wf_env (env_filter X G1)).
  { rewrite Hdec in WF.
    apply wf_env_suffix with (A := x ~ T0).
    apply wf_env_suffix with (A := env_filter X G2). exact WF. }
  assert (HfvT0 : fv T0 [<=] dom (env_filter X G1)).
  { rewrite Hdec in WF.
    assert (Wsplit : wf_env (x ~ T0 ++ env_filter X G1)).
    { apply wf_env_suffix with (A := env_filter X G2). exact WF. }
    destruct (wf_env_cons_inv Wsplit) as [_ [Hfv [_ _]]]. exact Hfv. }
  auto.
Qed.

Lemma upcast_filter_avar : forall (G:env) (v:avar) (G':env) T,
    upcast G v G' T ->
    forall X a, v = avar_f a -> wf_env G -> wf_env (env_filter X G) ->
      a `in` dom (env_filter X G) ->
      exists G'', upcast (env_filter X G) v G'' T /\ G'' = env_filter X G'.
Proof.
  intros G v G' T Hup.
  induction Hup as [G0 x | G1 G2 x T0 G1' Rev1 | G1 G2 x T0 G1' Lb U Rev1];
    intros X a Hv W WF Ha.
  - exists nil. split.
    + apply uc_top.
    + rewrite env_filter_nil. reflexivity.
  - injection Hv as Hxa. subst a.
    destruct (@env_filter_binding_split X G2 x T0 G1 W WF Ha)
      as [HxX [Hdec [W1 [WF1 HfvT0]]]].
    destruct (revealing_filter Rev1 X W1 WF1 HfvT0) as [G1a [Hrev1a HG1a]].
    exists nil. split.
    + rewrite Hdec.
      eapply uc_bot. exact Hrev1a.
    + rewrite env_filter_nil. reflexivity.
  - injection Hv as Hxa. subst a.
    destruct (@env_filter_binding_split X G2 x T0 G1 W WF Ha)
      as [HxX [Hdec [W1 [WF1 HfvT0]]]].
    destruct (revealing_filter Rev1 X W1 WF1 HfvT0) as [G1a [Hrev1a HG1a]].
    exists G1a. split.
    + rewrite Hdec.
      eapply uc_bnd. exact Hrev1a.
    + exact HG1a.
Qed.

Lemma downcast_filter_avar : forall (G:env) (v:avar) (G':env) T,
    downcast G v G' T ->
    forall X a, v = avar_f a -> wf_env G -> wf_env (env_filter X G) ->
      a `in` dom (env_filter X G) ->
      exists G'', downcast (env_filter X G) v G'' T /\ G'' = env_filter X G'.
Proof.
  intros G v G' T Hdc.
  induction Hdc as [G0 x | G1 G2 x T0 G1' Rev1 | G1 G2 x T0 G1' Lb U Rev1];
    intros X a Hv W WF Ha.
  - exists nil. split.
    + apply dc_bot.
    + rewrite env_filter_nil. reflexivity.
  - injection Hv as Hxa. subst a.
    destruct (@env_filter_binding_split X G2 x T0 G1 W WF Ha)
      as [HxX [Hdec [W1 [WF1 HfvT0]]]].
    destruct (revealing_filter Rev1 X W1 WF1 HfvT0) as [G1a [Hrev1a HG1a]].
    exists nil. split.
    + rewrite Hdec.
      eapply dc_top. exact Hrev1a.
    + rewrite env_filter_nil. reflexivity.
  - injection Hv as Hxa. subst a.
    destruct (@env_filter_binding_split X G2 x T0 G1 W WF Ha)
      as [HxX [Hdec [W1 [WF1 HfvT0]]]].
    destruct (revealing_filter Rev1 X W1 WF1 HfvT0) as [G1a [Hrev1a HG1a]].
    exists G1a. split.
    + rewrite Hdec.
      eapply dc_bnd. exact Hrev1a.
    + exact HG1a.
Qed.

Lemma upcast_avar_b : forall (G:env) n (G':env) T,
    upcast G (avar_b n) G' T -> G' = nil /\ T = typ_top.
Proof.
  intros G n G' T H. inversion H; subst; auto.
Qed.

Lemma downcast_avar_b : forall (G:env) n (G':env) T,
    downcast G (avar_b n) G' T -> G' = nil /\ T = typ_bot.
Proof.
  intros G n G' T H. inversion H; subst; auto.
Qed.

Lemma env_filter_cons_union : forall X (x:atom) (T:typ) (G:env),
    x `notin` dom G ->
    env_filter (X \u {{x}}) (x ~ T ++ G) = x ~ T ++ env_filter X G.
Proof.
  intros X x T G Hx. unfold env_filter. simpl.
  assert (Hm : AtomSetImpl.mem x (X \u {{x}}) = true)
    by (apply AtomSetImpl.mem_1; fsetdec).
  rewrite Hm.
  assert (Hpred : forall p, In p G ->
    (fun p0 : atom * typ => AtomSetImpl.mem (fst p0) (X \u {{x}})) p =
    (fun p0 : atom * typ => AtomSetImpl.mem (fst p0) X) p).
  { intros [y U] Hin. simpl. apply mem_union_singleton_not.
    intro Heq. subst. apply Hx. apply binds_In with (a := U). exact Hin. }
  rewrite (filter_ext_in _ _ G Hpred). reflexivity.
Qed.

Lemma stareat_filter : forall M (G1:env) (G2:env) S U,
    [ M ] G1 >> S <⦂ U << G2 ->
    forall X1 X2,
      wf_env G1 -> wf_env G2 ->
      wf_env (env_filter X1 G1) -> wf_env (env_filter X2 G2) ->
      fv S [<=] dom G1 -> lc S -> fv U [<=] dom G2 -> lc U ->
      fv S [<=] dom (env_filter X1 G1) ->
      fv U [<=] dom (env_filter X2 G2) ->
      [ M ] env_filter X1 G1 >> S <⦂ U << env_filter X2 G2.
Proof.
  intros M G1 G2 S U Hsa.
  induction Hsa as [L G1 G2 T | L G1 G2 T | L G1 G2 x
                  | L G1 x G2 T U G1' Hup Hsub IHsub
                  | L G1 x G2 T U G2' Hdc Hsub IHsub
                  | L G1 T1 U1 G2 T2 U2 x Hx Hp IHp Hb IHb
                  | L G1 S1 U1 S2 U2 G2 H1 IH1 H2 IH2];
    intros X1 X2 W1 W2 WF1 WF2 HS LS HU LU HS' HU'.
  - (* sa_bot *) apply sa_bot.
  - (* sa_top *) apply sa_top.
  - (* sa_sel_refl *) apply sa_sel_refl.
  - (* sa_sel_left *)
    destruct x as [n | a].
    + destruct (@upcast_avar_b G1 n G1' T Hup) as [HG' HT]. subst G1'. subst T.
      assert (Hst : [ L ] env_filter X1 nil >> typ_top <⦂ U << env_filter X2 G2).
      { apply IHsub.
        - apply wf_nil.
        - exact W2.
        - rewrite env_filter_nil. apply wf_nil.
        - exact WF2.
        - simpl. fsetdec.
        - apply lc_typ_top.
        - exact HU.
        - exact LU.
        - simpl. fsetdec.
        - exact HU'. }
      rewrite env_filter_nil in Hst.
      eapply sa_sel_left; [ apply uc_top | exact Hst ].
    + assert (Ha : a `in` dom (env_filter X1 G1)) by (simpl in HS'; fsetdec).
      destruct (@upcast_filter_avar G1 (avar_f a) G1' T Hup X1 a eq_refl W1 WF1 Ha)
        as [G'' [Hup' HG'']].
      assert (Hst : [ L ] env_filter X1 G1' >> T <⦂ U << env_filter X2 G2).
      { apply IHsub.
        - apply (upcast_wf Hup W1).
        - exact W2.
        - rewrite <- HG''. apply (upcast_wf Hup' WF1).
        - exact WF2.
        - apply (proj1 (upcast_fv_lc Hup W1)).
        - apply (proj2 (upcast_fv_lc Hup W1)).
        - exact HU.
        - exact LU.
        - rewrite <- HG''. apply (proj1 (upcast_fv_lc Hup' WF1)).
        - exact HU'. }
      rewrite <- HG'' in Hst.
      eapply sa_sel_left; [ exact Hup' | exact Hst ].
  - (* sa_sel_right *)
    destruct x as [n | a].
    + destruct (@downcast_avar_b G2 n G2' U Hdc) as [HG' HT]. subst G2'. subst U.
      assert (Hst : [ L ] env_filter X1 G1 >> T <⦂ typ_bot << env_filter X2 nil).
      { apply IHsub.
        - exact W1.
        - apply wf_nil.
        - exact WF1.
        - rewrite env_filter_nil. apply wf_nil.
        - exact HS.
        - exact LS.
        - simpl. fsetdec.
        - apply lc_typ_bot.
        - exact HS'.
        - simpl. fsetdec. }
      rewrite env_filter_nil in Hst.
      eapply sa_sel_right; [ apply dc_bot | exact Hst ].
    + assert (Ha : a `in` dom (env_filter X2 G2)) by (simpl in HU'; fsetdec).
      destruct (@downcast_filter_avar G2 (avar_f a) G2' U Hdc X2 a eq_refl W2 WF2 Ha)
        as [G'' [Hdc' HG'']].
      assert (Hst : [ L ] env_filter X1 G1 >> T <⦂ U << env_filter X2 G2').
      { apply IHsub.
        - exact W1.
        - apply (downcast_wf Hdc W2).
        - exact WF1.
        - rewrite <- HG''. apply (downcast_wf Hdc' WF2).
        - exact HS.
        - exact LS.
        - apply (proj1 (downcast_fv_lc Hdc W2)).
        - apply (proj2 (downcast_fv_lc Hdc W2)).
        - exact HS'.
        - rewrite <- HG''. apply (proj1 (downcast_fv_lc Hdc' WF2)). }
      rewrite <- HG'' in Hst.
      eapply sa_sel_right; [ exact Hdc' | exact Hst ].
  - (* sa_all *)
    assert (HxdG1 : x `notin` dom G1) by (pose proof (dom_subset_fv G1); fsetdec).
    assert (HxdG2 : x `notin` dom G2) by (pose proof (dom_subset_fv G2); fsetdec).
    destruct (@lc_all_inv 0 T1 U1 LS) as [HlcT1 HlcU1].
    destruct (@lc_all_inv 0 T2 U2 LU) as [HlcT2 HlcU2].
    apply sa_all with (x := x).
    + pose proof (env_filter_fv_sub X1 G1). pose proof (env_filter_fv_sub X2 G2).
      fsetdec.
    + apply IHp.
      * exact W2.
      * exact W1.
      * exact WF2.
      * exact WF1.
      * apply Subset_trans with (s' := fv (typ_all T2 U2));
          [ apply fv_all_subset_l | exact HU ].
      * exact HlcT2.
      * apply Subset_trans with (s' := fv (typ_all T1 U1));
          [ apply fv_all_subset_l | exact HS ].
      * exact HlcT1.
      * apply Subset_trans with (s' := fv (typ_all T2 U2));
          [ apply fv_all_subset_l | exact HU' ].
      * apply Subset_trans with (s' := fv (typ_all T1 U1));
          [ apply fv_all_subset_l | exact HS' ].
    + rewrite <- (@env_filter_cons_union X1 x T1 G1 HxdG1),
                <- (@env_filter_cons_union X2 x T2 G2 HxdG2).
      apply IHb.
      * apply wf_cons.
        -- fsetdec.
        -- apply Subset_trans with (s' := fv (typ_all T1 U1));
             [ apply fv_all_subset_l | exact HS ].
        -- exact W1.
        -- exact HlcT1.
      * apply wf_cons.
        -- fsetdec.
        -- apply Subset_trans with (s' := fv (typ_all T2 U2));
             [ apply fv_all_subset_l | exact HU ].
        -- exact W2.
        -- exact HlcT2.
      * rewrite (@env_filter_cons_union X1 x T1 G1 HxdG1).
        apply wf_cons.
        -- pose proof (env_filter_fv_sub X1 G1). fsetdec.
        -- apply Subset_trans with (s' := fv (typ_all T1 U1));
             [ apply fv_all_subset_l | exact HS' ].
        -- exact WF1.
        -- exact HlcT1.
      * rewrite (@env_filter_cons_union X2 x T2 G2 HxdG2).
        apply wf_cons.
        -- pose proof (env_filter_fv_sub X2 G2). fsetdec.
        -- apply Subset_trans with (s' := fv (typ_all T2 U2));
             [ apply fv_all_subset_l | exact HU' ].
        -- exact WF2.
        -- exact HlcT2.
      * pose proof (fv_open_upper x U1).
        pose proof (fv_all_subset_r T1 U1). simpl. fsetdec.
      * apply lc_open. exact HlcU1.
      * pose proof (fv_open_upper x U2).
        pose proof (fv_all_subset_r T2 U2). simpl. fsetdec.
      * apply lc_open. exact HlcU2.
      * pose proof (fv_open_upper x U1).
        rewrite (@env_filter_cons_union X1 x T1 G1 HxdG1).
        pose proof (fv_all_subset_r T1 U1). simpl. fsetdec.
      * pose proof (fv_open_upper x U2).
        rewrite (@env_filter_cons_union X2 x T2 G2 HxdG2).
        pose proof (fv_all_subset_r T2 U2). simpl. fsetdec.
  - (* sa_bnd *)
    destruct (@lc_bnd_inv 0 S1 U1 LS) as [HlcS1 HlcU1].
    destruct (@lc_bnd_inv 0 S2 U2 LU) as [HlcS2 HlcU2].
    apply sa_bnd.
    + apply IH1.
      * exact W2.
      * exact W1.
      * exact WF2.
      * exact WF1.
      * apply Subset_trans with (s' := fv (typ_bnd S2 U2));
          [ apply fv_bnd_subset_l | exact HU ].
      * exact HlcS2.
      * apply Subset_trans with (s' := fv (typ_bnd S1 U1));
          [ apply fv_bnd_subset_l | exact HS ].
      * exact HlcS1.
      * apply Subset_trans with (s' := fv (typ_bnd S2 U2));
          [ apply fv_bnd_subset_l | exact HU' ].
      * apply Subset_trans with (s' := fv (typ_bnd S1 U1));
          [ apply fv_bnd_subset_l | exact HS' ].
    + apply IH2.
      * exact W1.
      * exact W2.
      * exact WF1.
      * exact WF2.
      * apply Subset_trans with (s' := fv (typ_bnd S1 U1));
          [ apply fv_bnd_subset_r | exact HS ].
      * exact HlcU1.
      * apply Subset_trans with (s' := fv (typ_bnd S2 U2));
          [ apply fv_bnd_subset_r | exact HU ].
      * exact HlcU2.
      * apply Subset_trans with (s' := fv (typ_bnd S1 U1));
          [ apply fv_bnd_subset_r | exact HS' ].
      * apply Subset_trans with (s' := fv (typ_bnd S2 U2));
          [ apply fv_bnd_subset_r | exact HU' ].
Qed.

Lemma revealing_top_inv : forall (G:env) (G':env) U,
    revealing G typ_top G' U -> U = typ_top.
Proof.
  intros G G' U H. inversion H; subst; auto.
Qed.

Lemma revealing_bot_inv : forall (G:env) (G':env) U,
    revealing G typ_bot G' U -> U = typ_bot \/ U = typ_top.
Proof.
  intros G G' U H. inversion H; subst; auto.
Qed.

Lemma stareat_bnd_split : forall M (GL:env) (GR:env) P U,
    [ M ] GL >> P <⦂ U << GR ->
    wf_env GL -> wf_env GR ->
    fv P [<=] dom GL -> lc P -> lc U -> fv U [<=] dom GR ->
    forall S0 U0, U = typ_bnd S0 U0 ->
      fv S0 [<=] dom GR -> lc S0 -> fv U0 [<=] dom GR -> lc U0 ->
      ((exists GL' L U', revealing GL P GL' (typ_bnd L U') /\
          [ M ] GR >> S0 <⦂ L << GL' /\ [ M ] GL' >> U' <⦂ U0 << GR)
       \/ (exists GL', revealing GL P GL' typ_bot)).
Proof.
  intros M GL GR P U Hsa.
  induction Hsa as [L GL T GR | L GL T GR | L GL x GR
                  | L GL x GR T U GL1 Hup Hsub IHsub
                  | L GL x GR T U GR1 Hdc Hsub IHsub
                  | L GL T1 U1 GR T2 U2 x Hx Hp Hb IHp IHb
                  | L GL S1 U1 S2 U2 GR H1 IH1 H2 IH2];
    intros WGL WGR HfvP HlcP HlcU HfvU S0 U0 Heq HfvS HlcS HfvU0 HlcU0.
  - (* sa_bot *)
    subst T. right. exists GL. apply rv_stop. simpl. intro H; exact H.
  - (* sa_top *) discriminate Heq.
  - (* sa_sel_refl *) discriminate Heq.
  - (* sa_sel_left *)
    subst U.
    assert (HlcB : lc (typ_bnd S0 U0)) by (apply lc_typ_bnd; auto).
    assert (HfvB : fv (typ_bnd S0 U0) [<=] dom GR) by fsetdec.
    destruct Hup as [G0 x0 | G1 G2 x0 T0 G1p RevU | G1 G2 x0 T0 G1p Lb Ub RevU].
    + (* uc_top *)
      assert (HfvTop : fv typ_top [<=] dom (nil:env)) by (simpl; fsetdec).
      destruct (IHsub wf_nil WGR HfvTop lc_typ_top
                      HlcB HfvB S0 U0 eq_refl HfvS HlcS HfvU0 HlcU0)
        as [[GLp [Lp [Up [Hrev _]]]] | [GLp Hrev]].
      * apply revealing_top_inv in Hrev. discriminate Hrev.
      * apply revealing_top_inv in Hrev. discriminate Hrev.
    + (* uc_bot *)
      right. exists nil. eapply rv_bot. exact RevU.
    + (* uc_bnd *)
      assert (WGL1 : wf_env G1p).
      { assert (W1 : wf_env G1).
        { apply wf_env_suffix with (A := x0 ~ T0).
          apply wf_env_suffix with (A := G2). exact WGL. }
        apply revealing_wf with (G := G1) (T := T0) (G' := G1p) (U := typ_bnd Lb Ub);
          auto. }
      assert (HfvUb : fv Ub [<=] dom G1p).
      { assert (HfvBb : fv (typ_bnd Lb Ub) [<=] dom G1p).
        { assert (W1 : wf_env G1).
          { apply wf_env_suffix with (A := x0 ~ T0).
            apply wf_env_suffix with (A := G2). exact WGL. }
          assert (HfvT0 : fv T0 [<=] dom G1).
          { assert (WX : wf_env (x0 ~ T0 ++ G1)).
            { apply wf_env_suffix with (A := G2). exact WGL. }
            destruct (wf_env_cons_inv WX) as [_ [Hf [_ _]]]. exact Hf. }
          apply revealing_fv with (G := G1) (T := T0); auto. }
        apply Subset_trans with (s' := fv (typ_bnd Lb Ub));
          [ apply fv_bnd_subset_r | exact HfvBb ]. }
      assert (HlcUb : lc Ub).
      { assert (W1 : wf_env G1).
        { apply wf_env_suffix with (A := x0 ~ T0).
          apply wf_env_suffix with (A := G2). exact WGL. }
        assert (HlcT0 : lc T0).
        { assert (WX : wf_env (x0 ~ T0 ++ G1)).
          { apply wf_env_suffix with (A := G2). exact WGL. }
          destruct (wf_env_cons_inv WX) as [_ [_ [_ Hl]]]. exact Hl. }
        assert (HlcB0 : lc (typ_bnd Lb Ub)).
        { apply revealing_lc with (G := G1) (T := T0) (G' := G1p) (U := typ_bnd Lb Ub); auto. }
        destruct (@lc_bnd_inv 0 Lb Ub HlcB0) as [_ HU]. exact HU. }
      destruct (IHsub WGL1 WGR HfvUb HlcUb HlcB HfvB
                      S0 U0 eq_refl HfvS HlcS HfvU0 HlcU0)
        as [[GLp [Lp [Up [Hrev [Hlo Hhi]]]]] | [GLp Hrev]].
      * left. exists GLp, Lp, Up. split.
        -- eapply rv_bnd; [ exact RevU | exact Hrev ].
        -- split; assumption.
      * right. exists GLp. eapply rv_bnd; [ exact RevU | exact Hrev ].
  - (* sa_sel_right *) discriminate Heq.
  - (* sa_all *) discriminate Heq.
  - (* sa_bnd *)
    injection Heq as HS0 HU0. subst S0. subst U0.
    left. exists GL, S1, U1. split.
    + apply rv_stop. simpl. intro H; exact H.
    + split; assumption.
Qed.

Lemma kernel_stareat : forall n M (G1:env) S U (G2:env),
    subtysk' M G1 S U G2 n ->
    wf_env G1 -> wf_env G2 ->
    fv S [<=] dom G1 -> lc S -> fv U [<=] dom G2 -> lc U ->
    [ M ] G1 >> S <⦂ U << G2.
Proof.
  intros n. induction n using lt_wf_ind.
  rename H into IH.
  intros M G1 S U G2 D.
  destruct D as [L G1 G2 x
                | L G1 G2 T
                | L G1 G2 T
                | L G1 G2 S0 T1 T2 U0 n1 n2 D1 D2
                | L G1 G2 T1 T2 U1 U2 x n1 n2 Hx D1 D2
                | L G1 G2 x T S0 n1 Hb D1
                | L G1 G2 x T U0 n1 Hb D1];
    intros W1 W2 HS LS HU LU.
  - (* ssk'_refl *) apply sa_sel_refl.
  - (* ssk'_top *) apply sa_top.
  - (* ssk'_bot *) apply sa_bot.
  - (* ssk'_bnd *)
    assert (H1 : [ L ] G2 >> S0 <⦂ T1 << G1).
    { apply (IH n1); [ lia | exact D1 | exact W2 | exact W1
        | apply Subset_trans with (s' := fv (typ_bnd S0 U0));
            [ apply fv_bnd_subset_l | exact HU ]
        | apply lc_bnd_inv in LU; tauto
        | apply Subset_trans with (s' := fv (typ_bnd T1 T2));
            [ apply fv_bnd_subset_l | exact HS ]
        | apply lc_bnd_inv in LS; tauto ]. }
    assert (H2 : [ L ] G1 >> T2 <⦂ U0 << G2).
    { apply (IH n2); [ lia | exact D2 | exact W1 | exact W2
        | apply Subset_trans with (s' := fv (typ_bnd T1 T2));
            [ apply fv_bnd_subset_r | exact HS ]
        | apply lc_bnd_inv in LS; tauto
        | apply Subset_trans with (s' := fv (typ_bnd S0 U0));
            [ apply fv_bnd_subset_r | exact HU ]
        | apply lc_bnd_inv in LU; tauto ]. }
    eapply sa_bnd; [ exact H1 | exact H2 ].
  - (* ssk'_all *)
    assert (HxdG1 : x `notin` dom G1) by (pose proof (dom_subset_fv G1); fsetdec).
    assert (HxdG2 : x `notin` dom G2) by (pose proof (dom_subset_fv G2); fsetdec).
    destruct (@lc_all_inv 0 T1 U1 LS) as [HlcT1 HlcU1].
    destruct (@lc_all_inv 0 T2 U2 LU) as [HlcT2 HlcU2].
    assert (H1 : [ L ] G2 >> T2 <⦂ T1 << G1).
    { apply (IH n1); [ lia | exact D1 | exact W2 | exact W1
        | apply Subset_trans with (s' := fv (typ_all T2 U2));
            [ apply fv_all_subset_l | exact HU ]
        | exact HlcT2
        | apply Subset_trans with (s' := fv (typ_all T1 U1));
            [ apply fv_all_subset_l | exact HS ]
        | exact HlcT1 ]. }
    assert (H2 : [ union L (union (singleton x) (fv T2)) ]
                 x ~ T1 ++ G1 >> open x U1 <⦂ open x U2 << x ~ T2 ++ G2).
    { apply (IH n2); [ lia | exact D2
        | apply wf_cons; [ fsetdec
            | apply Subset_trans with (s' := fv (typ_all T1 U1));
                [ apply fv_all_subset_l | exact HS ]
            | exact W1 | exact HlcT1 ]
        | apply wf_cons; [ fsetdec
            | apply Subset_trans with (s' := fv (typ_all T2 U2));
                [ apply fv_all_subset_l | exact HU ]
            | exact W2 | exact HlcT2 ]
        | pose proof (fv_open_upper x U1); pose proof (fv_all_subset_r T1 U1); simpl; fsetdec
        | apply lc_open; exact HlcU1
        | pose proof (fv_open_upper x U2); pose proof (fv_all_subset_r T2 U2); simpl; fsetdec
        | apply lc_open; exact HlcU2 ]. }
    eapply sa_all; [ exact Hx | exact H1 | exact H2 ].
  - (* ssk'_sel1 *)
    assert (Hst : [ L ] G2 >> T <⦂ typ_bnd S0 typ_top << G1).
    { apply (IH n1); [ lia | exact D1 | exact W2 | exact W1
        | apply wf_env_binds_fv_dom with (x := x); auto
        | apply wf_env_binds_lc with (x := x) (G := G2); auto
        | simpl; fsetdec
        | apply lc_typ_bnd; [ exact LS | apply lc_typ_top ] ]. }
    destruct (@wf_env_binds_split G2 x T W2 Hb) as [A [B [HG2 [HfvT HlcT]]]].
    subst G2.
    assert (HWFB : wf_env B).
    { apply wf_env_suffix with (A := x ~ T).
      apply wf_env_suffix with (A := A). exact W2. }
    assert (HEQB : env_filter (dom B) (A ++ x ~ T ++ B) = B).
    { apply (@env_filter_suffix A x T B). exact W2. }
    assert (HEQG1 : env_filter (dom G1) G1 = G1).
    { apply env_filter_dom_sub. fsetdec. }
    assert (HWFfB : wf_env (env_filter (dom B) (A ++ x ~ T ++ B))).
    { rewrite HEQB. exact HWFB. }
    assert (HWFG1 : wf_env (env_filter (dom G1) G1)).
    { rewrite HEQG1. exact W1. }
    assert (HstB : [ L ] env_filter (dom B) (A ++ x ~ T ++ B)
                              >> T <⦂ typ_bnd S0 typ_top << env_filter (dom G1) G1).
    { apply (@stareat_filter L (A ++ x ~ T ++ B) G1 T (typ_bnd S0 typ_top) Hst
               (dom B) (dom G1)).
      - exact W2.
      - exact W1.
      - exact HWFfB.
      - exact HWFG1.
      - apply wf_env_binds_fv_dom with (x := x); auto.
      - exact HlcT.
      - simpl; fsetdec.
      - apply lc_typ_bnd; [ exact LS | apply lc_typ_top ].
      - rewrite HEQB. exact HfvT.
      - rewrite HEQG1. simpl; fsetdec. }
    rewrite HEQB, HEQG1 in HstB.
    assert (Hsplit := @stareat_bnd_split L B G1 T (typ_bnd S0 typ_top) HstB
                        HWFB W1 HfvT HlcT
                        (ltac:(apply lc_typ_bnd; [ exact LS | apply lc_typ_top ]))
                        (ltac:(simpl; fsetdec))
                        S0 typ_top eq_refl HS LS (ltac:(simpl; fsetdec)) lc_typ_top).
    destruct Hsplit as [[B' [Lb [Ub [Hrev [Hlo _]]]]] | [B' Hrev]].
    + eapply sa_sel_right.
      * eapply dc_bnd. exact Hrev.
      * exact Hlo.
    + eapply sa_sel_right.
      * eapply dc_top. exact Hrev.
      * apply sa_top.
  - (* ssk'_sel2 *)
    assert (Hst : [ L ] G1 >> T <⦂ typ_bnd typ_bot U0 << G2).
    { apply (IH n1); [ lia | exact D1 | exact W1 | exact W2
        | apply wf_env_binds_fv_dom with (x := x); auto
        | apply wf_env_binds_lc with (x := x) (G := G1); auto
        | simpl; fsetdec
        | apply lc_typ_bnd; [ apply lc_typ_bot | exact LU ] ]. }
    destruct (@wf_env_binds_split G1 x T W1 Hb) as [A [B [HG1 [HfvT HlcT]]]].
    subst G1.
    assert (HWFB : wf_env B).
    { apply wf_env_suffix with (A := x ~ T).
      apply wf_env_suffix with (A := A). exact W1. }
    assert (HEQB : env_filter (dom B) (A ++ x ~ T ++ B) = B).
    { apply (@env_filter_suffix A x T B). exact W1. }
    assert (HEG2 : env_filter (dom G2) G2 = G2).
    { apply env_filter_dom_sub. fsetdec. }
    assert (HWFfB : wf_env (env_filter (dom B) (A ++ x ~ T ++ B))).
    { rewrite HEQB. exact HWFB. }
    assert (HWFG2 : wf_env (env_filter (dom G2) G2)).
    { rewrite HEG2. exact W2. }
    assert (HstB : [ L ] env_filter (dom B) (A ++ x ~ T ++ B)
                              >> T <⦂ typ_bnd typ_bot U0 << env_filter (dom G2) G2).
    { apply (@stareat_filter L (A ++ x ~ T ++ B) G2 T (typ_bnd typ_bot U0) Hst
               (dom B) (dom G2)).
      - exact W1.
      - exact W2.
      - exact HWFfB.
      - exact HWFG2.
      - apply wf_env_binds_fv_dom with (x := x); auto.
      - exact HlcT.
      - simpl; fsetdec.
      - apply lc_typ_bnd; [ apply lc_typ_bot | exact LU ].
      - rewrite HEQB. exact HfvT.
      - rewrite HEG2. simpl; fsetdec. }
    rewrite HEQB, HEG2 in HstB.
    assert (Hsplit := @stareat_bnd_split L B G2 T (typ_bnd typ_bot U0) HstB
                        HWFB W2 HfvT HlcT
                        (ltac:(apply lc_typ_bnd; [ apply lc_typ_bot | exact LU ]))
                        (ltac:(simpl; fsetdec))
                        typ_bot U0 eq_refl (ltac:(simpl; fsetdec)) lc_typ_bot HU LU).
    destruct Hsplit as [[B' [Lb [Ub [Hrev [_ Hhi]]]]] | [B' Hrev]].
    + eapply sa_sel_left.
      * eapply uc_bnd. exact Hrev.
      * exact Hhi.
    + eapply sa_sel_left.
      * eapply uc_bot. exact Hrev.
      * apply sa_bot.
Qed.

Lemma fv_cons_sub : forall (x:atom) (T:typ) (G:env),
    fv (x ~ T ++ G) [<=] {{x}} \u fv T \u fv G.
Proof.
  intros.
  change (dom ((x,T) :: G) \u fv_values fv_typ ((x,T) :: G)
          [<=] {{x}} \u fv T \u (dom G \u fv_values fv_typ G)).
  rewrite dom_cons. simpl.
  pose proof (dom_subset_fv G). fsetdec.
Qed.

Lemma revealing_env_fv : forall (G:env) T (G':env) U,
    revealing G T G' U -> fv G' [<=] fv G.
Proof.
  intros G T G' U H. destruct (revealing_suffix H) as [P HP].
  rewrite HP. apply fv_app_sub_r.
Qed.

Lemma upcast_env_fv : forall (G:env) (x:avar) (G':env) T,
    upcast G x G' T -> fv G' [<=] fv G.
Proof.
  intros G x G' T H. induction H as [G0 x0 | G1 G2 x0 T0 G1' Rev1
                                  | G1 G2 x0 T0 G1' Lb U Rev1].
  - simpl. fsetdec.
  - simpl. fsetdec.
  - apply Subset_trans with (s' := fv G1).
    + apply (@revealing_env_fv G1 T0 G1' (typ_bnd Lb U)). exact Rev1.
    + apply Subset_trans with (s' := fv (x0 ~ T0 ++ G1)).
      * apply fv_app_sub_r.
      * apply fv_app_sub_r.
Qed.

Lemma downcast_env_fv : forall (G:env) (x:avar) (G':env) T,
    downcast G x G' T -> fv G' [<=] fv G.
Proof.
  intros G x G' T H. induction H as [G0 x0 | G1 G2 x0 T0 G1' Rev1
                                    | G1 G2 x0 T0 G1' Lb U Rev1].
  - simpl. fsetdec.
  - simpl. fsetdec.
  - apply Subset_trans with (s' := fv G1).
    + apply (@revealing_env_fv G1 T0 G1' (typ_bnd Lb U)). exact Rev1.
    + apply Subset_trans with (s' := fv (x0 ~ T0 ++ G1)).
      * apply fv_app_sub_r.
      * apply fv_app_sub_r.
Qed.

Lemma upcast_type_fv : forall (G:env) (x:avar) (G':env) T,
    upcast G x G' T -> wf_env G -> fv T [<=] fv G.
Proof.
  intros G x G' T H W.
  pose proof (upcast_fv_lc H W) as [HT _].
  pose proof (upcast_env_fv H).
  pose proof (dom_subset_fv G').
  fsetdec.
Qed.

Lemma downcast_type_fv : forall (G:env) (x:avar) (G':env) T,
    downcast G x G' T -> wf_env G -> fv T [<=] fv G.
Proof.
  intros G x G' T H W.
  pose proof (downcast_fv_lc H W) as [HT _].
  pose proof (downcast_env_fv H).
  pose proof (dom_subset_fv G').
  fsetdec.
Qed.

Lemma stareat_kernel : forall L (G1:env) S U (G2:env),
    [ L ] G1 >> S <⦂ U << G2 ->
    wf_env G1 -> wf_env G2 ->
    fv S [<=] dom G1 -> lc S -> fv U [<=] dom G2 -> lc U ->
    fv G1 \u fv G2 \u fv S \u fv U [<=] L ->
    [ L ] G1 ⊢k S <⦂ U k⊣ G2.
Proof.
  intros L G1 S U G2 Hsa.
  induction Hsa as [L G1 T G2 | L G1 T G2 | L G1 x G2
                  | L G1 x G2 T U G1' Hup Hsub IHsub
                  | L G1 x G2 T U G2' Hdc Hsub IHsub
                  | L G1 T1 U1 G2 T2 U2 x Hx Hp IHp Hb IHb
                  | L G1 S1 U1 S2 U2 G2 H1 IH1 H2 IH2];
    intros W1 W2 HS LS HU LU HL.
  - (* sa_bot *) apply ssk_bot.
  - (* sa_top *) apply ssk_top.
  - (* sa_sel_refl *) apply ssk_refl.
  - (* sa_sel_left *)
    assert (W1' : wf_env G1') by (exact (@upcast_wf G1 x G1' T Hup W1)).
    assert (HfvT : fv T [<=] dom G1') by (apply (proj1 (upcast_fv_lc Hup W1))).
    assert (HlcT : lc T) by (apply (proj2 (upcast_fv_lc Hup W1))).
    assert (HL' : fv G1' \u fv G2 \u fv T \u fv U [<=] L).
    { pose proof (upcast_env_fv Hup). pose proof (upcast_type_fv Hup W1). fsetdec. }
    assert (Hk : [ L ] G1' ⊢k T <⦂ U k⊣ G2).
    { apply (IHsub W1' W2 HfvT HlcT HU LU HL'). }
    eapply upcast_kernel_cont; [ exact Hup | exact Hk | exact W1 | exact W1'
      | exact W2 | fsetdec | exact HfvT | exact HlcT | exact HU | exact LU ].
  - (* sa_sel_right *)
    assert (W2' : wf_env G2') by (exact (@downcast_wf G2 x G2' U Hdc W2)).
    assert (HfvU : fv U [<=] dom G2') by (apply (proj1 (downcast_fv_lc Hdc W2))).
    assert (HlcU : lc U) by (apply (proj2 (downcast_fv_lc Hdc W2))).
    assert (HL' : fv G1 \u fv G2' \u fv T \u fv U [<=] L).
    { pose proof (downcast_env_fv Hdc). pose proof (downcast_type_fv Hdc W2). fsetdec. }
    assert (Hk : [ L ] G1 ⊢k T <⦂ U k⊣ G2').
    { apply (IHsub W1 W2' HS LS HfvU HlcU HL'). }
    eapply downcast_kernel_cont; [ exact Hdc | exact Hk | exact W2 | exact W2'
      | exact W1 | exact HS | exact LS | fsetdec ].
  - (* sa_all *)
    destruct (@lc_all_inv 0 T1 U1 LS) as [HlcT1 HlcU1].
    destruct (@lc_all_inv 0 T2 U2 LU) as [HlcT2 HlcU2].
    assert (HL1 : fv G2 \u fv G1 \u fv T2 \u fv T1 [<=] L).
    { pose proof (fv_all_subset_l T1 U1). pose proof (fv_all_subset_r T1 U1).
      pose proof (fv_all_subset_l T2 U2). pose proof (fv_all_subset_r T2 U2).
      fsetdec. }
    assert (H1 : [ L ] G2 ⊢k T2 <⦂ T1 k⊣ G1).
    { apply (IHp W2 W1
        (ltac:(apply Subset_trans with (s' := fv (typ_all T2 U2));
               [ apply fv_all_subset_l | exact HU ]))
        HlcT2
        (ltac:(apply Subset_trans with (s' := fv (typ_all T1 U1));
               [ apply fv_all_subset_l | exact HS ]))
        HlcT1 HL1). }
    assert (HLb : fv (x ~ T1 ++ G1) \u fv (x ~ T2 ++ G2)
                  \u fv (open x U1) \u fv (open x U2)
                  [<=] L \u {{x}} \u fv T2).
    { pose proof (fv_open_upper x U1). pose proof (fv_open_upper x U2).
      pose proof (fv_all_subset_l T1 U1). pose proof (fv_all_subset_r T1 U1).
      pose proof (fv_all_subset_l T2 U2). pose proof (fv_all_subset_r T2 U2).
      pose proof (dom_subset_fv G1). pose proof (dom_subset_fv G2).
      pose proof (@fv_cons_sub x T1 G1). pose proof (@fv_cons_sub x T2 G2).
      fsetdec. }
    assert (H2 : [ L \u {{x}} \u fv T2 ]
                 (x ~ T1 ++ G1) ⊢k open x U1 <⦂ open x U2 k⊣ (x ~ T2 ++ G2)).
    { apply (IHb
        (ltac:(apply wf_cons; [ fsetdec
          | apply Subset_trans with (s' := fv (typ_all T1 U1));
              [ apply fv_all_subset_l | exact HS ] | exact W1 | exact HlcT1 ]))
        (ltac:(apply wf_cons; [ fsetdec
          | apply Subset_trans with (s' := fv (typ_all T2 U2));
              [ apply fv_all_subset_l | exact HU ] | exact W2 | exact HlcT2 ]))
        (ltac:(pose proof (fv_open_upper x U1); pose proof (fv_all_subset_r T1 U1);
               simpl; fsetdec))
        (ltac:(apply lc_open; exact HlcU1))
        (ltac:(pose proof (fv_open_upper x U2); pose proof (fv_all_subset_r T2 U2);
               simpl; fsetdec))
        (ltac:(apply lc_open; exact HlcU2))
        HLb). }
    eapply ssk_all; [ exact Hx | exact H1 | exact H2 ].
  - (* sa_bnd *)
    destruct (@lc_bnd_inv 0 S1 U1 LS) as [HlcS1 HlcU1].
    destruct (@lc_bnd_inv 0 S2 U2 LU) as [HlcS2 HlcU2].
    assert (HL1 : fv G2 \u fv G1 \u fv S2 \u fv S1 [<=] L).
    { pose proof (fv_bnd_subset_l S1 U1). pose proof (fv_bnd_subset_r S1 U1).
      pose proof (fv_bnd_subset_l S2 U2). pose proof (fv_bnd_subset_r S2 U2).
      fsetdec. }
    assert (H1' : [ L ] G2 ⊢k S2 <⦂ S1 k⊣ G1).
    { apply (IH1 W2 W1
        (ltac:(apply Subset_trans with (s' := fv (typ_bnd S2 U2));
               [ apply fv_bnd_subset_l | exact HU ]))
        HlcS2
        (ltac:(apply Subset_trans with (s' := fv (typ_bnd S1 U1));
               [ apply fv_bnd_subset_l | exact HS ]))
        HlcS1 HL1). }
    assert (HL2 : fv G1 \u fv G2 \u fv U1 \u fv U2 [<=] L).
    { pose proof (fv_bnd_subset_l S1 U1). pose proof (fv_bnd_subset_r S1 U1).
      pose proof (fv_bnd_subset_l S2 U2). pose proof (fv_bnd_subset_r S2 U2).
      fsetdec. }
    assert (H2' : [ L ] G1 ⊢k U1 <⦂ U2 k⊣ G2).
    { apply (IH2 W1 W2
        (ltac:(apply Subset_trans with (s' := fv (typ_bnd S1 U1));
               [ apply fv_bnd_subset_r | exact HS ]))
        HlcU1
        (ltac:(apply Subset_trans with (s' := fv (typ_bnd S2 U2));
               [ apply fv_bnd_subset_r | exact HU ]))
        HlcU2 HL2). }
    eapply ssk_bnd; [ exact H1' | exact H2' ].
Qed.

Theorem subtysk_equiv_stareat : forall L G1 S U G2,
    wf_env G1 -> wf_env G2 ->
    fv S [<=] dom G1 -> lc S ->
    fv U [<=] dom G2 -> lc U ->
    [ L `union` fv G1 `union` fv G2 `union` fv S `union` fv U ]
      G1 ⊢k S <⦂ U k⊣ G2 <->
    [ L `union` fv G1 `union` fv G2 `union` fv S `union` fv U ]
      G1 >> S <⦂ U << G2.
Proof.
  intros L G1 S U G2 W1 W2 HS LS HU LU. split.
  - intros D. destruct (subtysk_subtysk' D) as [n Hn].
    exact (@kernel_stareat n
             (L `union` fv G1 `union` fv G2 `union` fv S `union` fv U)
             G1 S U G2 Hn W1 W2 HS LS HU LU).
  - intros Hsa.
    exact (@stareat_kernel
             (L `union` fv G1 `union` fv G2 `union` fv S `union` fv U)
             G1 S U G2 Hsa W1 W2 HS LS HU LU (ltac:(fsetdec))).
Qed.
