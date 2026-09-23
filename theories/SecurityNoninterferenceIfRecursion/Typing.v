From AutoProof.SecurityNoninterferenceIfRecursion Require Export Semantics.
Import ListNotations.

Inductive subtype : ty -> ty -> Prop :=
  | S_Unit : forall kappa1 kappa2,
      wf_security kappa1 -> wf_security kappa2 -> security_le kappa1 kappa2 ->
      subtype (Ty_Unit kappa1) (Ty_Unit kappa2)
  | S_Sum : forall T1 T2 U1 U2 kappa1 kappa2,
      subtype T1 U1 -> subtype T2 U2 ->
      wf_security kappa1 -> wf_security kappa2 -> security_le kappa1 kappa2 ->
      subtype (Ty_Sum T1 T2 kappa1) (Ty_Sum U1 U2 kappa2)
  | S_Prod : forall T1 T2 U1 U2 kappa1 kappa2,
      subtype T1 U1 -> subtype T2 U2 ->
      wf_security kappa1 -> wf_security kappa2 -> security_le kappa1 kappa2 ->
      subtype (Ty_Prod T1 T2 kappa1) (Ty_Prod U1 U2 kappa2)
  | S_Arrow : forall T1 T2 U1 U2 kappa1 kappa2,
      subtype U1 T1 -> subtype T2 U2 ->
      wf_security kappa1 -> wf_security kappa2 -> security_le kappa1 kappa2 ->
      subtype (Ty_Arrow T1 T2 kappa1) (Ty_Arrow U1 U2 kappa2)
  | S_Trans : forall T U V, subtype T U -> subtype U V -> subtype T V
  | S_Nat : forall k1 k2, wf_security k1 -> wf_security k2 -> security_le k1 k2 ->
      subtype (Ty_Nat k1) (Ty_Nat k2).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      lookup_context x Gamma = Some T -> wf_ty T ->
      has_type Gamma (tm_fvar x) T
  | T_Unit : forall Gamma kappa,
      wf_security kappa -> has_type Gamma (tm_unit kappa) (Ty_Unit kappa)
  | T_Abs : forall (L : list atom) Gamma T1 body T2 kappa,
      wf_ty T1 -> wf_security kappa ->
      (forall x : atom, ~ In x L ->
        has_type (update Gamma x T1) (open body (tm_fvar x)) T2) ->
      has_type Gamma (tm_abs T1 body kappa) (Ty_Arrow T1 T2 kappa)
  | T_App : forall Gamma t1 t2 T1 T2 kappa r,
      has_type Gamma t1 (Ty_Arrow T1 T2 kappa) ->
      has_type Gamma t2 T1 -> flows_to kappa.(reader) r ->
      has_type Gamma (tm_app t1 t2 r) (ty_protect kappa.(indirect_reader) T2)
  | T_Pair : forall Gamma t1 t2 T1 T2 kappa,
      has_type Gamma t1 T1 -> has_type Gamma t2 T2 -> wf_security kappa ->
      has_type Gamma (tm_pair t1 t2 kappa) (Ty_Prod T1 T2 kappa)
  | T_Fst : forall Gamma t T1 T2 kappa r,
      has_type Gamma t (Ty_Prod T1 T2 kappa) -> flows_to kappa.(reader) r ->
      has_type Gamma (tm_fst t r) (ty_protect kappa.(indirect_reader) T1)
  | T_Snd : forall Gamma t T1 T2 kappa r,
      has_type Gamma t (Ty_Prod T1 T2 kappa) -> flows_to kappa.(reader) r ->
      has_type Gamma (tm_snd t r) (ty_protect kappa.(indirect_reader) T2)
  | T_Inl : forall Gamma t T1 T2 kappa,
      has_type Gamma t T1 -> wf_ty T2 -> wf_security kappa ->
      has_type Gamma (tm_inl t kappa) (Ty_Sum T1 T2 kappa)
  | T_Inr : forall Gamma t T1 T2 kappa,
      wf_ty T1 -> has_type Gamma t T2 -> wf_security kappa ->
      has_type Gamma (tm_inr t kappa) (Ty_Sum T1 T2 kappa)
  | T_Case : forall (L : list atom) Gamma t body1 body2 T1 T2 T kappa r,
      has_type Gamma t (Ty_Sum T1 T2 kappa) -> flows_to kappa.(reader) r ->
      (forall x : atom, ~ In x L ->
        has_type (update Gamma x T1) (open body1 (tm_fvar x)) T) ->
      (forall x : atom, ~ In x L ->
        has_type (update Gamma x T2) (open body2 (tm_fvar x)) T) ->
      has_type Gamma (tm_case t body1 body2 r)
        (ty_protect kappa.(indirect_reader) T)
  | T_Protect : forall Gamma t T l,
      has_type Gamma t T -> has_type Gamma (tm_protect l t) (ty_protect l T)
  | T_Sub : forall Gamma t T U,
      has_type Gamma t T -> subtype T U -> has_type Gamma t U
  | T_Nat : forall Gamma n k, wf_security k -> has_type Gamma (tm_nat n k) (Ty_Nat k)
  | T_Succ : forall Gamma t k r,
      has_type Gamma t (Ty_Nat k) -> flows_to k.(reader) r ->
      has_type Gamma (tm_succ t r) (ty_protect k.(indirect_reader) (Ty_Nat public))
  | T_NatRec : forall Gamma n b s k T r,
      has_type Gamma n (Ty_Nat k) -> has_type Gamma b T ->
      has_type Gamma s (Ty_Arrow (Ty_Nat public) (Ty_Arrow T T public) public) ->
      flows_to k.(reader) r ->
      has_type Gamma (tm_natrec n b s r) (ty_protect k.(indirect_reader) T)
  | T_If : forall Gamma c yes no k T r,
      has_type Gamma c (Ty_Sum (Ty_Unit public) (Ty_Unit public) k) ->
      has_type Gamma yes T -> has_type Gamma no T -> flows_to k.(reader) r ->
      has_type Gamma (tm_if c yes no r) (ty_protect k.(indirect_reader) T).

Lemma ty_protect_wf : forall T l,
  wf_ty T -> wf_ty (ty_protect l T).
Proof.
  assert (forall k l, wf_security k -> wf_security (protect_security k l)) as Hprotect.
  { intros [r ir] l. destruct r, ir, l;
      unfold wf_security, protect_security; simpl; tauto. }
  destruct T; simpl; intros l H; intuition.
Qed.

Lemma subtype_regular : forall T U,
  subtype T U -> wf_ty T /\ wf_ty U.
Proof. intros T U H. induction H; simpl in *; tauto. Qed.

Lemma subtype_erasure : forall T U,
  subtype T U -> erase_type T = erase_type U.
Proof. intros T U H. induction H; simpl; congruence. Qed.

Lemma security_le_refl : forall k, security_le k k.
Proof. intros [r ir]. split; apply flows_to_refl. Qed.

Lemma security_le_trans : forall k1 k2 k3,
  security_le k1 k2 -> security_le k2 k3 -> security_le k1 k3.
Proof.
  intros k1 k2 k3 [Hr1 Hi1] [Hr2 Hi2]. split; eapply flows_to_trans; eassumption.
Qed.

Lemma subtype_refl : forall T, wf_ty T -> subtype T T.
Proof.
  induction T; simpl; intros Hwf.
  - apply S_Unit; try assumption; apply security_le_refl.
  - destruct Hwf as [H1 [H2 Hk]]. apply S_Sum; auto using security_le_refl.
  - destruct Hwf as [H1 [H2 Hk]]. apply S_Prod; auto using security_le_refl.
  - destruct Hwf as [H1 [H2 Hk]]. apply S_Arrow; auto using security_le_refl.
  - apply S_Nat; try assumption; apply security_le_refl.
Qed.

Lemma security_protect_mono : forall k1 k2 l1 l2,
  security_le k1 k2 -> flows_to l1 l2 ->
  security_le (protect_security k1 l1) (protect_security k2 l2).
Proof.
  intros [r1 ir1] [r2 ir2] l1 l2.
  destruct r1, ir1, r2, ir2, l1, l2;
    unfold security_le, protect_security; simpl; tauto.
Qed.

Lemma protect_security_wf : forall k l,
  wf_security k -> wf_security (protect_security k l).
Proof.
  intros [r ir] l; destruct r, ir, l;
    unfold wf_security, protect_security; simpl; tauto.
Qed.

Lemma ty_protect_low : forall T, ty_protect Low T = T.
Proof.
  destruct T; destruct s as [r ir]; destruct r, ir; reflexivity.
Qed.

Lemma subtype_protect : forall T U, subtype T U -> forall l1 l2,
  flows_to l1 l2 -> subtype (ty_protect l1 T) (ty_protect l2 U).
Proof.
  intros T U Hsub. induction Hsub; intros l1 l2 Hl; simpl.
  - apply S_Unit; auto using protect_security_wf, security_protect_mono.
  - apply S_Sum; auto using protect_security_wf, security_protect_mono.
  - apply S_Prod; auto using protect_security_wf, security_protect_mono.
  - apply S_Arrow; auto using protect_security_wf, security_protect_mono.
  - eapply S_Trans; [apply IHHsub1; exact Hl | apply IHHsub2; apply flows_to_refl].
  - apply S_Nat; auto using protect_security_wf, security_protect_mono.
Qed.

Lemma subtype_arrow_inv : forall T U,
  subtype T U -> forall A B k,
  T = Ty_Arrow A B k ->
  exists A' B' k', U = Ty_Arrow A' B' k' /\
    subtype A' A /\ subtype B B' /\ security_le k k'.
Proof.
  intros T U Hsub. induction Hsub; intros A B k Heq; inversion Heq; subst.
  - exists U1, U2, kappa2. auto.
  - destruct (IHHsub1 _ _ _ eq_refl) as [Am [Bm [km [-> [Ha [Hb Hk]]]]]].
    destruct (IHHsub2 _ _ _ eq_refl) as [Ac [Bc [kc [-> [Ha' [Hb' Hk']]]]]].
    exists Ac, Bc, kc. split; [reflexivity | ]. repeat split.
    + eapply S_Trans; eassumption.
    + eapply S_Trans; eassumption.
    + eapply flows_to_trans; [exact (proj1 Hk) | exact (proj1 Hk')].
    + eapply flows_to_trans; [exact (proj2 Hk) | exact (proj2 Hk')].
Qed.

Lemma subtype_prod_inv : forall T U,
  subtype T U -> forall A B k,
  T = Ty_Prod A B k ->
  exists A' B' k', U = Ty_Prod A' B' k' /\
    subtype A A' /\ subtype B B' /\ security_le k k'.
Proof.
  intros T U Hsub. induction Hsub; intros A B k Heq; inversion Heq; subst.
  - exists U1, U2, kappa2. auto.
  - destruct (IHHsub1 _ _ _ eq_refl) as [Am [Bm [km [-> [Ha [Hb Hk]]]]]].
    destruct (IHHsub2 _ _ _ eq_refl) as [Ac [Bc [kc [-> [Ha' [Hb' Hk']]]]]].
    exists Ac, Bc, kc. split; [reflexivity | ]. repeat split.
    + eapply S_Trans; eassumption.
    + eapply S_Trans; eassumption.
    + eapply flows_to_trans; [exact (proj1 Hk) | exact (proj1 Hk')].
    + eapply flows_to_trans; [exact (proj2 Hk) | exact (proj2 Hk')].
Qed.

Lemma subtype_sum_inv : forall T U,
  subtype T U -> forall A B k,
  T = Ty_Sum A B k ->
  exists A' B' k', U = Ty_Sum A' B' k' /\
    subtype A A' /\ subtype B B' /\ security_le k k'.
Proof.
  intros T U Hsub. induction Hsub; intros A B k Heq; inversion Heq; subst.
  - exists U1, U2, kappa2. auto.
  - destruct (IHHsub1 _ _ _ eq_refl) as [Am [Bm [km [-> [Ha [Hb Hk]]]]]].
    destruct (IHHsub2 _ _ _ eq_refl) as [Ac [Bc [kc [-> [Ha' [Hb' Hk']]]]]].
    exists Ac, Bc, kc. split; [reflexivity | ]. repeat split.
    + eapply S_Trans; eassumption.
    + eapply S_Trans; eassumption.
    + eapply flows_to_trans; [exact (proj1 Hk) | exact (proj1 Hk')].
    + eapply flows_to_trans; [exact (proj2 Hk) | exact (proj2 Hk')].
Qed.

Lemma subtype_nat_inv : forall T U, subtype T U -> forall k,
  T = Ty_Nat k -> exists k', U = Ty_Nat k' /\ security_le k k'.
Proof.
  intros T U H. induction H; intros k E; inversion E; subst.
  - destruct (IHsubtype1 _ eq_refl) as [km [-> Hm]].
    destruct (IHsubtype2 _ eq_refl) as [ku [-> Hu]].
    exists ku. split; [reflexivity | eapply security_le_trans; eassumption].
  - exists k2. auto.
Qed.

Lemma typing_regular : forall Gamma t T,
  has_type Gamma t T -> locally_closed t /\ wf_ty T.
Proof.
  intros Gamma t T H. induction H; unfold locally_closed, open in *; simpl in *.
  - tauto.
  - tauto.
  - destruct (fresh_atom L) as [x Hfresh].
    destruct (H2 x Hfresh) as [Hlc Hwf].
    split; [eapply lc_at_open_inv; exact Hlc | tauto].
  - destruct IHhas_type1 as [Hlc1 [Hwf1 [Hwf2 Hk]]].
    destruct IHhas_type2 as [Hlc2 _]. split; [tauto | apply ty_protect_wf; exact Hwf2].
  - tauto.
  - destruct IHhas_type as [Hlc [Hwf1 [Hwf2 Hk]]].
    split; [exact Hlc | apply ty_protect_wf; exact Hwf1].
  - destruct IHhas_type as [Hlc [Hwf1 [Hwf2 Hk]]].
    split; [exact Hlc | apply ty_protect_wf; exact Hwf2].
  - tauto.
  - tauto.
  - destruct (fresh_atom L) as [x Hfresh].
    destruct (H2 x Hfresh) as [Hlc1 Hwf1].
    destruct (H4 x Hfresh) as [Hlc2 Hwf2].
    split.
    + split; [tauto | ]. split; eapply lc_at_open_inv; eassumption.
    + apply ty_protect_wf; exact Hwf1.
  - split; [tauto | apply ty_protect_wf; tauto].
  - split; [tauto | exact (proj2 (subtype_regular _ _ H0))].
  - tauto.
  - split; [tauto | destruct k as [r0 ir]; destruct r0, ir; exact I].
  - split; [tauto | apply ty_protect_wf; tauto].
  - split; [tauto | apply ty_protect_wf; tauto].
Qed.
