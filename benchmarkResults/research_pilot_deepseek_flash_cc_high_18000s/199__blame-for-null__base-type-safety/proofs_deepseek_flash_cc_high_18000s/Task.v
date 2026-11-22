From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Require Import Metalib.Metatheory.
Require Import Definitions.

Open Scope list_scope.

(* ------------------------- free variables ------------------------- *)

Fixpoint fv_trm (t:trm) : atoms :=
  match t with
  | t_var_b _ => empty
  | t_var_f x => singleton x
  | t_null => empty
  | t_abs _ s => fv_trm s
  | t_app s t => union (fv_trm s) (fv_trm t)
  | t_app_safe f s t => union (fv_trm f) (union (fv_trm s) (fv_trm t))
  | t_cast s _ _ _ => fv_trm s
  end.

(* ------------------------- substitution ------------------------- *)

Fixpoint subst_trm (x:var) (u:trm) (t:trm) : trm :=
  match t with
  | t_var_b n => t_var_b n
  | t_var_f y => if eq_dec x y then u else t_var_f y
  | t_null => t_null
  | t_abs T s => t_abs T (subst_trm x u s)
  | t_app s t => t_app (subst_trm x u s) (subst_trm x u t)
  | t_app_safe f s t => t_app_safe (subst_trm x u f) (subst_trm x u s) (subst_trm x u t)
  | t_cast s V p T => t_cast (subst_trm x u s) V p T
  end.

Lemma subst_trm_fresh : forall t xz u,
  xz `notin` fv_trm t ->
  subst_trm xz u t = t.
Proof.
  induction t; simpl; intros xz u Hf; auto.
  - destruct (eq_dec xz x) as [e|ne].
    + exfalso. apply Hf. rewrite e. apply AtomSetImpl.singleton_2; reflexivity.
    + reflexivity.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma subst_open_fresh_rec : forall k s xz v,
  xz `notin` fv_trm s ->
  subst_trm xz v (open_trm_wrt_trm_rec k (t_var_f xz) s)
  = open_trm_wrt_trm_rec k v s.
Proof.
  intros k s. revert k. induction s; intros k xz v Hf; simpl.
  - (* var_b *) destruct (lt_eq_lt_dec n k) as [[lt|eq]|gt]; simpl.
    + reflexivity.
    + subst n. destruct (eq_dec xz xz) as [e|ne]; [reflexivity|exfalso; apply ne; reflexivity].
    + reflexivity.
  - (* var_f *) destruct (eq_dec xz x) as [e|ne].
    + exfalso. apply Hf. rewrite e. apply AtomSetImpl.singleton_2. reflexivity.
    + reflexivity.
  - (* null *) reflexivity.
  - (* abs *) f_equal. apply (IHs (S k) xz v). simpl in Hf. exact Hf.
  - (* app *)
    assert (H1 : xz `notin` fv_trm s1) by exact (notin_union_1 xz _ _ Hf).
    assert (H2 : xz `notin` fv_trm s2) by exact (notin_union_2 xz _ _ Hf).
    rewrite (IHs1 k xz v H1), (IHs2 k xz v H2). reflexivity.
  - (* app_safe *)
    assert (H1 : xz `notin` fv_trm s1) by exact (notin_union_1 xz _ _ Hf).
    assert (H23 : xz `notin` union (fv_trm s2) (fv_trm s3)) by exact (notin_union_2 xz _ _ Hf).
    assert (H2 : xz `notin` fv_trm s2) by exact (notin_union_1 xz _ _ H23).
    assert (H3 : xz `notin` fv_trm s3) by exact (notin_union_2 xz _ _ H23).
    rewrite (IHs1 k xz v H1), (IHs2 k xz v H2), (IHs3 k xz v H3). reflexivity.
  - (* cast *) rewrite (IHs k xz v). reflexivity. exact Hf.
Qed.

Lemma subst_open_fresh : forall s xz v,
  xz `notin` fv_trm s ->
  subst_trm xz v (open_trm_wrt_trm s (t_var_f xz))
  = open_trm_wrt_trm s v.
Proof.
  intros. unfold open_trm_wrt_trm. apply subst_open_fresh_rec. exact H.
Qed.

(* ------------------------- binding structure ------------------------- *)

Fixpoint lc_at (d:nat) (t:trm) : Prop :=
  match t with
  | t_var_b n => n < d
  | t_var_f _ => True
  | t_null => True
  | t_abs _ s => lc_at (S d) s
  | t_app s t => lc_at d s /\ lc_at d t
  | t_app_safe f s t => lc_at d f /\ lc_at d s /\ lc_at d t
  | t_cast s _ _ _ => lc_at d s
  end.

Lemma lc_at_open_ignore : forall d k s xa ya,
  lc_at d (open_trm_wrt_trm_rec k (t_var_f xa) s) <->
  lc_at d (open_trm_wrt_trm_rec k (t_var_f ya) s).
Proof.
  intros d k s. revert d k. induction s; intros d k xa ya; simpl.
  - destruct (lt_eq_lt_dec n k) as [[l|e]|g]; simpl; reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. apply IHs.
  - simpl. rewrite IHs1, IHs2. reflexivity.
  - simpl. rewrite IHs1, IHs2, IHs3. reflexivity.
  - simpl. apply IHs.
Qed.

Lemma lc_at_iff_open : forall d s,
  lc_at (S d) s <->
  (forall x, lc_at d (open_trm_wrt_trm_rec d (t_var_f x) s)).
Proof.
  intros d s. revert d. induction s; intros d; simpl.
  - (* var_b *) split.
    + intros H x. destruct (lt_eq_lt_dec n d) as [[l|e]|g]; simpl.
      * exact l.
      * subst n. exact I.
      * exfalso; lia.
    + intros H. destruct (atom_fresh empty) as [a Ha]. specialize (H a).
      destruct (lt_eq_lt_dec n d) as [[l|e]|g]; simpl in H.
      * lia.
      * subst n. lia.
      * lia.
  - (* var_f *) split; intros; exact I.
  - (* null *) split; intros; exact I.
  - (* abs *) apply (IHs (S d)).
  - (* app *) split.
    + intros [H1 H2] x. split.
      * apply (proj1 (IHs1 d)); exact H1.
      * apply (proj1 (IHs2 d)); exact H2.
    + intros H. split.
      * apply (proj2 (IHs1 d)). intro x. exact (proj1 (H x)).
      * apply (proj2 (IHs2 d)). intro x. exact (proj2 (H x)).
  - (* app_safe *) split.
    + intros [H1 [H2 H3]] x. split; [|split].
      * apply (proj1 (IHs1 d)); exact H1.
      * apply (proj1 (IHs2 d)); exact H2.
      * apply (proj1 (IHs3 d)); exact H3.
    + intros H. split; [|split].
      * apply (proj2 (IHs1 d)). intro x. exact (proj1 (H x)).
      * apply (proj2 (IHs2 d)). intro x. exact (proj1 (proj2 (H x))).
      * apply (proj2 (IHs3 d)). intro x. exact (proj2 (proj2 (H x))).
  - (* cast *) apply IHs.
Qed.

(* ------------------------- size of terms ------------------------- *)

Fixpoint size_trm (t:trm) : nat :=
  match t with
  | t_var_b _ => 1
  | t_var_f _ => 1
  | t_null => 1
  | t_abs _ s => S (size_trm s)
  | t_app s t => S (size_trm s + size_trm t)
  | t_app_safe f s t => S (size_trm f + size_trm s + size_trm t)
  | t_cast s _ _ _ => S (size_trm s)
  end.

Lemma size_open_rec : forall k s xa,
  size_trm (open_trm_wrt_trm_rec k (t_var_f xa) s) = size_trm s.
Proof.
  intros k s. revert k. induction s; intros k xa; simpl.
  - destruct (lt_eq_lt_dec n k) as [[l|e]|g]; reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHs. reflexivity.
  - rewrite IHs1, IHs2. reflexivity.
  - rewrite IHs1, IHs2, IHs3. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

Lemma lc_at_0_lc_aux : forall n t, size_trm t <= n -> lc_at 0 t -> lc_trm t.
Proof.
  induction n as [|n IH]; intros t Hsz Hlc.
  - destruct t; simpl in *; lia.
  - destruct t; simpl in *.
    + exfalso; lia.
    + constructor.
    + constructor.
    + apply lc_t_abs. intro xa.
      apply IH.
      * change (size_trm (open_trm_wrt_trm_rec 0 (t_var_f xa) t) <= n).
        rewrite size_open_rec. lia.
      * change (lc_at 0 (open_trm_wrt_trm_rec 0 (t_var_f xa) t)).
        exact (proj1 (lc_at_iff_open 0 t) Hlc xa).
    + apply lc_t_app.
      * apply IH; [lia | exact (proj1 Hlc)].
      * apply IH; [lia | exact (proj2 Hlc)].
    + apply lc_t_app_safe.
      * apply IH; [lia | exact (proj1 Hlc)].
      * apply IH; [lia | exact (proj1 (proj2 Hlc))].
      * apply IH; [lia | exact (proj2 (proj2 Hlc))].
    + apply lc_t_cast. apply IH; [lia | exact Hlc].
Qed.

Lemma lc_at_0_lc : forall t, lc_at 0 t -> lc_trm t.
Proof.
  intro t. apply (lc_at_0_lc_aux (size_trm t) t); lia.
Qed.

Lemma typing_lc_at : forall G t T, typing G t T -> lc_at 0 t.
Proof.
  intros G t T Hty. induction Hty; simpl.
  - exact I.
  - exact I.
  - apply (proj2 (lc_at_iff_open 0 s)).
    intro x.
    destruct (atom_fresh L) as [a Ha].
    specialize (H0 a Ha).
    apply (proj1 (lc_at_open_ignore 0 0 s a x)).
    exact H0.
  - split; [exact IHHty1 | exact IHHty2].
  - split; [|split]; [exact IHHty1 | exact IHHty2 | exact IHHty3].
  - exact IHHty.
Qed.

Lemma typing_lc : forall G t T, typing G t T -> lc_trm t.
Proof.
  intros G t T H. apply lc_at_0_lc. exact (typing_lc_at G t T H).
Qed.

Lemma notin_dom_app_1 : forall {A : Type} (G1 G2:list (atom*A)) (x:atom),
  x `notin` dom (G1++G2) -> x `notin` dom G1.
Proof.
  intros. rewrite dom_app in H. apply notin_union_1 in H. exact H.
Qed.

Lemma notin_dom_app_2 : forall {A : Type} (G1 G2:list (atom*A)) (x:atom),
  x `notin` dom (G1++G2) -> x `notin` dom G2.
Proof.
  intros. rewrite dom_app in H. apply notin_union_2 in H. exact H.
Qed.

(* list / dom helpers *)

Lemma in_insert_mid : forall {A : Type} (l1 l2:list A) (a b:A),
  In a (l1++l2) -> In a (l1++b::l2).
Proof.
  intros. apply in_app_iff in H. apply in_app_iff.
  destruct H as [H|H]; [left; exact H | right]. simpl. right. exact H.
Qed.

Lemma notin_singleton_neq : forall (x y:atom), x `notin` singleton y -> x <> y.
Proof.
  intros x y H E. apply H. subst y. apply AtomSetImpl.singleton_2. reflexivity.
Qed.

Lemma notin_dom_cons : forall {A : Type} (G:list (atom*A)) (y z:atom) (a:A),
  y <> z -> y `notin` dom G -> y `notin` dom ((z,a)::G).
Proof.
  intros. rewrite dom_cons. apply notin_union_3.
  - apply notin_singleton. intro E. apply H. symmetry. exact E.
  - exact H0.
Qed.

Lemma uniq_remove_mid_helper : forall {A : Type} (G1 G2:list (atom*A)) (x:atom) (V:A),
  uniq (G1 ++ (x,V) :: G2) -> uniq (G1 ++ G2).
Proof.
  intros. exact (@uniq_remove_mid A G1 [(x,V)] G2 H).
Qed.

Lemma typing_insert : forall G t T, typing G t T ->
  forall G1 G2 (y:atom) (U:typ),
    G = G1 ++ G2 ->
    y `notin` dom (G1++G2) ->
    typing (G1 ++ (y,U) :: G2) t T.
Proof.
  intros G t T Hty. induction Hty; intros G1 G2 y U Heq Hy; subst G.
  - (* var *) apply typing_var.
    + apply (@uniq_insert_mid typ y U G2 G1 H).
      * apply notin_dom_app_1 in Hy. exact Hy.
      * apply notin_dom_app_2 in Hy. exact Hy.
    + apply in_insert_mid. exact H0.
  - (* null *) apply typing_null.
    apply (@uniq_insert_mid typ y U G2 G1 H).
    + apply notin_dom_app_1 in Hy. exact Hy.
    + apply notin_dom_app_2 in Hy. exact Hy.
  - (* abs *)
    apply typing_abs with (L := union L (union (singleton y) (dom (G1++G2)))).
    intros z Hz.
    assert (HzL : z `notin` L) by (apply notin_union_1 in Hz; exact Hz).
    assert (Hz2 : z `notin` union (singleton y) (dom (G1++G2)))
      by (apply notin_union_2 in Hz; exact Hz).
    assert (Hzy : z <> y) by (apply notin_singleton_neq; apply notin_union_1 in Hz2; exact Hz2).
    assert (Hd : y `notin` dom (G1++G2)) by exact Hy.
    refine (H0 z HzL (z~V ++ G1) G2 y U _ _).
    + (* Heq' *) simpl. reflexivity.
    + (* freshness *)
      change (y `notin` dom ((z,V)::(G1++G2))).
      apply notin_dom_cons.
      * intro E. apply Hzy. symmetry. exact E.
      * exact Hd.
  - (* app *)
    apply typing_app with (M:=M) (V:=V).
    + apply IHHty1; auto.
    + exact H.
    + apply IHHty2; auto.
  - (* safe app *)
    apply typing_safe_app with (M:=M) (V:=V).
    + apply IHHty1; auto.
    + exact H.
    + apply IHHty2; auto.
    + apply IHHty3; auto.
  - (* cast *)
    apply typing_cast with (V:=V).
    + apply IHHty; auto.
    + exact H.
Qed.

Lemma in_mid_remove : forall {A : Type} (l1 l2:list A) (a b:A),
  In a (l1++b::l2) -> a <> b -> In a (l1++l2).
Proof.
  intros A l1 l2 a b H Hne. apply in_app_iff. apply in_app_iff in H.
  destruct H as [H|H]; [left; exact H|right].
  simpl in H. destruct H as [E|H]; [exfalso; apply Hne; symmetry; exact E|exact H].
Qed.

Lemma lc_trm_to_lc_at : forall t, lc_trm t -> lc_at 0 t.
Proof.
  intros t H. induction H; simpl.
  - exact I.
  - exact I.
  - apply (proj2 (lc_at_iff_open 0 t)). intro x. apply H0.
  - split; [exact IHlc_trm1 | exact IHlc_trm2].
  - split; [|split]; [exact IHlc_trm1 | exact IHlc_trm2 | exact IHlc_trm3].
  - exact IHlc_trm.
Qed.

Lemma lc_at_open_id : forall d u, lc_at d u -> forall k v, d <= k -> open_trm_wrt_trm_rec k v u = u.
Proof.
  intros d u. revert d. induction u; intros d Hlc k v Hdk; simpl in *.
  - destruct (lt_eq_lt_dec n k) as [[l|e]|g]; simpl.
    + reflexivity.
    + exfalso; lia.
    + exfalso; lia.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal. apply IHu with (d:=S d) (k:=S k); [exact Hlc | lia].
  - simpl. rewrite (IHu1 d (proj1 Hlc) k v Hdk). rewrite (IHu2 d (proj2 Hlc) k v Hdk). reflexivity.
  - simpl. rewrite (IHu1 d (proj1 Hlc) k v Hdk).
    rewrite (IHu2 d (proj1 (proj2 Hlc)) k v Hdk).
    rewrite (IHu3 d (proj2 (proj2 Hlc)) k v Hdk). reflexivity.
  - simpl. rewrite (IHu d Hlc k v Hdk). reflexivity.
Qed.

Lemma lc_open_id : forall u, lc_trm u -> forall k v, open_trm_wrt_trm_rec k v u = u.
Proof.
  intros u H k v. apply (lc_at_open_id 0 u). apply lc_trm_to_lc_at. exact H. lia.
Qed.

Lemma subst_open_comm_lc_rec : forall k s xz u zz,
  lc_trm u -> zz <> xz ->
  subst_trm xz u (open_trm_wrt_trm_rec k (t_var_f zz) s)
  = open_trm_wrt_trm_rec k (t_var_f zz) (subst_trm xz u s).
Proof.
  intros k s. revert k. induction s; intros k xz u zz Hlc Hzx; simpl.
  - (* var_b *) destruct (lt_eq_lt_dec n k) as [[l|e]|g]; simpl.
    + reflexivity.
    + subst n. destruct (eq_dec xz zz) as [E|N].
      * exfalso; apply Hzx; symmetry; exact E.
      * reflexivity.
    + reflexivity.
  - (* var_f *) destruct (eq_dec xz x) as [E|N]; simpl.
    + rewrite lc_open_id; [reflexivity|exact Hlc].
    + reflexivity.
  - (* null *) reflexivity.
  - (* abs *) f_equal. apply (IHs (S k) xz u zz Hlc Hzx).
  - (* app *) rewrite (IHs1 k xz u zz Hlc Hzx), (IHs2 k xz u zz Hlc Hzx). reflexivity.
  - (* app_safe *) rewrite (IHs1 k xz u zz Hlc Hzx), (IHs2 k xz u zz Hlc Hzx), (IHs3 k xz u zz Hlc Hzx). reflexivity.
  - (* cast *) rewrite (IHs k xz u zz Hlc Hzx). reflexivity.
Qed.

Lemma subst_open_comm_lc : forall s x u z,
  lc_trm u -> z <> x ->
  subst_trm x u (open_trm_wrt_trm s (t_var_f z))
  = open_trm_wrt_trm (subst_trm x u s) (t_var_f z).
Proof.
  intros. unfold open_trm_wrt_trm. apply subst_open_comm_lc_rec; auto.
Qed.

Lemma typing_subst_sandwich : forall G t T, typing G t T ->
  forall G1 G2 (xz:atom) (Vz:typ) (u:trm),
    G = G1 ++ (xz,Vz) :: G2 ->
    lc_trm u ->
    typing (G1++G2) u Vz ->
    typing (G1++G2) (subst_trm xz u t) T.
Proof.
  intros G t T Hty. induction Hty; intros G1 G2 xz Vz u Heq Hlcu Hu; subst G.
  - (* var *)
    destruct (eq_dec xz x) as [E|N].
    + subst x.
      assert (T = Vz) by (exact (@binds_mid_eq typ xz T Vz G2 G1 H0 H)).
      subst T.
      simpl. destruct (eq_dec xz xz) as [E2|N2]; [exact Hu | exfalso; apply N2; reflexivity].
    + simpl. destruct (eq_dec xz x) as [E|N2].
      * exfalso; apply N; exact E.
      * apply typing_var.
        -- exact (@uniq_remove_mid_helper typ G1 G2 xz Vz H).
        -- apply (in_mid_remove _ _ _ _ H0). intro E. apply N. injection E. auto.
  - (* null *) apply typing_null. exact (@uniq_remove_mid_helper typ G1 G2 xz Vz H).
  - (* abs *)
    apply typing_abs with (L := union L (union (singleton xz) (dom (G1++G2)))).
    intros z Hz.
    assert (HzL : z `notin` L) by (apply notin_union_1 in Hz; exact Hz).
    assert (Hz2 : z `notin` union (singleton xz) (dom (G1++G2)))
      by (apply notin_union_2 in Hz; exact Hz).
    assert (Hzx : z <> xz) by (apply notin_singleton_neq; apply notin_union_1 in Hz2; exact Hz2).
    assert (Hzd : z `notin` dom (G1++G2)) by (apply notin_union_2 in Hz2; exact Hz2).
    assert (Hu' : typing ((z~V ++ G1)++G2) u Vz).
    { exact (typing_insert (G1++G2) u Vz Hu nil (G1++G2) z V eq_refl Hzd). }
    change (typing (z ~ V ++ G1 ++ G2)
      (open_trm_wrt_trm (subst_trm xz u s) (t_var_f z)) T).
    rewrite <- (subst_open_comm_lc s xz u z Hlcu Hzx).
    refine (H0 z HzL (z~V ++ G1) G2 xz Vz u _ Hlcu _).
    + simpl. reflexivity.
    + exact Hu'.
  - (* app *)
    simpl. apply typing_app with (M:=M) (V:=V).
    + eapply IHHty1; eauto.
    + exact H.
    + eapply IHHty2; eauto.
  - (* safe app *)
    simpl. apply typing_safe_app with (M:=M) (V:=V).
    + eapply IHHty1; eauto.
    + exact H.
    + eapply IHHty2; eauto.
    + eapply IHHty3; eauto.
  - (* cast *)
    simpl. apply typing_cast with (V:=V).
    + eapply IHHty; eauto.
    + exact H.
Qed.

(* ------------------------- inversion lemmas ------------------------- *)

Lemma inv_typing_var : forall G x T, typing G (t_var_f x) T -> uniq G /\ binds x T G.
Proof. intros. inversion H; subst; auto. Qed.

Lemma inv_typing_null : forall G T, typing G t_null T -> T = typ_null.
Proof. intros. inversion H; subst; auto. Qed.

Lemma inv_typing_abs : forall G V0 body T,
  typing G (t_abs V0 body) T ->
  exists Tbody L, T = typ_mod_arrow mod_non_nullable V0 Tbody /\
    (forall x, x \notin L -> typing ((x,V0)::G) (open_trm_wrt_trm body (t_var_f x)) Tbody).
Proof. intros. inversion H; subst; eauto. Qed.

Lemma inv_typing_app : forall G s t T,
  typing G (t_app s t) T ->
  exists M V, typing G s (typ_mod_arrow M V T) /\ M <> mod_safe /\ typing G t V.
Proof. intros. inversion H; subst; eauto. Qed.

Lemma inv_typing_safe_app : forall G f s t T,
  typing G (t_app_safe f s t) T ->
  exists M V, typing G f (typ_mod_arrow M V T) /\ M <> mod_non_nullable /\
    typing G s V /\ typing G t T.
Proof. intros. inversion H; subst. eexists; eexists; repeat split; eauto. Qed.

Lemma inv_typing_cast : forall G s V p T U,
  typing G (t_cast s V p T) U -> U = T /\ typing G s V /\ compat V T.
Proof. intros. inversion H; subst; auto. Qed.

Lemma inv_compat_arrow : forall M1 V1 V2 M2 T1 T2,
  compat (typ_mod_arrow M1 V1 V2) (typ_mod_arrow M2 T1 T2) ->
  compat T1 V1 /\ compat V2 T2.
Proof. intros. inversion H; subst; auto. Qed.

Lemma inv_compat_null_arrow : forall M V T,
  compat typ_null (typ_mod_arrow M V T) -> M <> mod_non_nullable.
Proof. intros. inversion H; subst; auto. Qed.

Lemma norm_typing : forall v v', norm v v' ->
  forall G M V T, typing G v (typ_mod_arrow M V T) ->
  typing G v' (typ_mod_arrow mod_non_nullable V T).
Proof.
  intros v v' Hnorm. induction Hnorm; intros G Mz Vz Tz Hty.
  - (* norm_abs *) inversion Hty; subst; assumption.
  - (* norm_cast *)
    destruct (inv_typing_cast G v (typ_mod_arrow M1 V1 V2) p
                (typ_mod_arrow M2 T1 T2) (typ_mod_arrow Mz Vz Tz) Hty)
      as [EU [Hv0 Hc]].
    injection EU as EM EV ET. subst.
    refine (typing_cast G v' (typ_mod_arrow mod_non_nullable V1 V2) p
              (typ_mod_arrow mod_non_nullable T1 T2) _ _).
    + apply (IHHnorm G M1 V1 V2). exact Hv0.
    + destruct (inv_compat_arrow M1 V1 V2 M2 T1 T2 Hc) as [Hd Hcod].
      apply compat_arrow; assumption.
Qed.

Lemma neglabel_exists : forall p:label, exists p', neglabel p p'.
Proof.
  intros [l|l]; [exists (label_not_label l); apply nl_l | exists (label_name l); apply nl_nl].
Qed.

Lemma mod_unsafe_neq_safe : mod_unsafe <> mod_safe. Proof. discriminate. Qed.
Lemma mod_nonnull_neq_safe : mod_non_nullable <> mod_safe. Proof. discriminate. Qed.

Lemma unwrap_null_value : forall G v U,
  typing G v U ->
  forall M V T, U = typ_mod_arrow M V T ->
  M <> mod_safe -> Is_true (is_val_of_trm v) -> isnull v ->
  exists p, unwrap v p.
Proof.
  intros G v U Hty. induction Hty; intros Mz Vz Tz EU Hsafe Hval Hnull.
  - (* var *) simpl in Hval; inversion Hval.
  - (* null *) simpl in EU; inversion EU.
  - (* abs *) simpl in Hnull; inversion Hnull.
  - (* app *) simpl in Hval; inversion Hval.
  - (* safe_app *) simpl in Hval; inversion Hval.
  - (* cast *)
    simpl in Hval. inversion Hnull; subst; clear Hnull.
    pose proof (typing_lc G s V Hty) as Hlc.
    destruct V as [| M1 V1 V2].
    + (* source null *)
      assert (HMn : Mz <> mod_non_nullable) by (exact (inv_compat_null_arrow Mz Vz Tz H)).
      destruct Mz as [| |].
      * destruct (neglabel_exists p) as [p' Hp'].
        exists p'. apply unwrap_null_bang; auto.
      * exfalso; apply Hsafe; reflexivity.
      * exfalso; apply HMn; reflexivity.
    + (* source arrow *)
      destruct Mz as [| |].
      * (* target unsafe *)
        destruct M1 as [| |].
           destruct (IHHty mod_unsafe V1 V2 eq_refl mod_unsafe_neq_safe Hval H1) as [p' Hp'].
           exists p'. apply unwrap_bang_bang. exact Hp'.
        -- destruct (neglabel_exists p) as [p' Hp'].
           exists p'. apply unwrap_question_bang; auto.
        -- destruct (IHHty mod_non_nullable V1 V2 eq_refl mod_nonnull_neq_safe Hval H1) as [p' Hp'].
           exists p'. apply unwrap_hash. exact Hp'.
      * exfalso; apply Hsafe; reflexivity.
      * (* target non_nullable *)
        destruct M1 as [| |].
        -- exists p. apply unwrap_bang_hash. exact Hlc.
        -- exists p. apply unwrap_question_hash. exact Hlc.
        -- destruct (IHHty mod_non_nullable V1 V2 eq_refl mod_nonnull_neq_safe Hval H1) as [p' Hp'].
           exists p'. apply unwrap_hash. exact Hp'.
Qed.

Lemma isabs_typed_arrow : forall G v V, typing G v V -> isabs v ->
  exists M V1 V2, V = typ_mod_arrow M V1 V2.
Proof.
  intros G v V Hty Hisabs. revert G V Hty.
  induction Hisabs; intros G Vz Hty.
  - (* abs *) destruct (inv_typing_abs G T t Vz Hty) as [Tb [L [EV _]]].
    exists mod_non_nullable, T, Tb. exact EV.
  - (* cast *) destruct (inv_typing_cast G v V p T Vz Hty) as [EV [Ht0 Hc]].
    subst Vz.
    destruct (IHHisabs G V Ht0) as [M1 [V1 [V2 EV0]]]. subst V.
    inversion Hc; subst. eauto.
Qed.

Lemma val_not_null_isabs : forall v,
  Is_true (is_val_of_trm v) -> lc_trm v -> ~ isnull v -> isabs v.
Proof.
  intros v. induction v; simpl; intros Hval Hlc Hn; try (inversion Hval).
  - (* null *) exfalso; apply Hn; constructor.
  - (* abs *) apply isabs_abs; exact Hlc.
  - (* cast *) apply isabs_cast. apply IHv.
    + exact Hval.
    + inversion Hlc; subst; assumption.
    + intro H; apply Hn; apply isnull_cast; exact H.
Qed.

Lemma isnull_dec : forall t, {isnull t} + {~ isnull t}.
Proof.
  induction t.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - left; constructor.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - right; intro H; inversion H.
  - destruct IHt as [H|H].
    + left; apply isnull_cast; exact H.
    + right; intro Hn; inversion Hn; subst; apply H; assumption.
Qed.

Lemma isabs_norm : forall G v V, typing G v V -> isabs v ->
  exists v', norm v v' /\ Is_true (is_val_of_trm v') /\ lc_trm v'.
Proof.
  intros G v V Hty Hisabs. revert G V Hty.
  induction Hisabs; intros G Vz Hty.
  - (* abs *)
    exists (t_abs T t). split.
    + apply norm_abs; assumption.
    + split; [reflexivity | assumption].
  - (* cast *)
    destruct (inv_typing_cast G v V p T Vz Hty) as [EV [Ht0 Hc]].
    subst Vz.
    destruct (IHHisabs G V Ht0) as [v' [Hnrm [Hval Hlc]]].
    destruct (isabs_typed_arrow G v V Ht0 Hisabs) as [M1 [V1 [V2 EV0]]]. subst V.
    destruct (isabs_typed_arrow G (t_cast v (typ_mod_arrow M1 V1 V2) p T) T Hty
                (isabs_cast v (typ_mod_arrow M1 V1 V2) p T Hisabs)) as [M2 [T1 [T2 EVT]]].
    subst T.
    exists (t_cast v' (typ_mod_arrow mod_non_nullable V1 V2) p
              (typ_mod_arrow mod_non_nullable T1 T2)).
    split.
    + apply norm_cast; exact Hnrm.
    + split.
      * simpl. exact Hval.
      * apply lc_t_cast; exact Hlc.
Qed.

Theorem preservation : forall G t r T,
  typing G t T ->
  step t r ->
  (exists p, r = r_blame p) \/
  (exists u, r = r_term u /\ typing G u T).
Proof.
  intros G t r T Hty Hstep. revert G T Hty.
  induction Hstep; intros G Tz Hty.
  - (* step_cast_ctx *)
    destruct (inv_typing_cast G t V p V' Tz Hty) as [EU [Ht Hc]]. subst Tz.
    destruct (IHHstep G V Ht) as [[q EQ]|[u [EQ Htu]]].
    + discriminate EQ.
    + inversion EQ; subst u. right. exists (t_cast t' V p V'). split; [reflexivity|].
      apply typing_cast with (V:=V); assumption.
  - (* step_cast_err *) left. exists q. reflexivity.
  - (* step_app *)
    destruct (inv_typing_app G (t_abs T t) v Tz Hty) as [M [V [Hs [HMsafe Hv]]]].
    destruct (inv_typing_abs G T t (typ_mod_arrow M V Tz) Hs) as [Tb [L [EU Hbody]]].
    injection EU as EM EV ET. subst.
    destruct (atom_fresh (union L (fv_trm t))) as [x Hx].
    assert (HxL : x `notin` L) by (apply notin_union_1 in Hx; exact Hx).
    assert (Hxt : x `notin` fv_trm t) by (apply notin_union_2 in Hx; exact Hx).
    pose proof (typing_lc G v T Hv) as Hlcv.
    pose proof (typing_subst_sandwich ((x,T)::G) (open_trm_wrt_trm t (t_var_f x)) Tb
                 (Hbody x HxL) nil G x T v eq_refl Hlcv Hv) as Hsub.
    right. exists (open_trm_wrt_trm t v). split; [reflexivity|].
    rewrite <- (subst_open_fresh t x v Hxt). exact Hsub.
  - (* step_app_ctxL *)
    destruct (inv_typing_app G s t Tz Hty) as [M [V [Hs [HMsafe Ht]]]].
    destruct (IHHstep G (typ_mod_arrow M V Tz) Hs) as [[q EQ]|[u [EQ Htu]]].
    + discriminate EQ.
    + inversion EQ; subst u. right. exists (t_app s' t). split; [reflexivity|].
      apply typing_app with (M:=M) (V:=V); assumption.
  - (* step_app_ctxR *)
    destruct (inv_typing_app G v t Tz Hty) as [M [V [Hv [HMsafe Ht]]]].
    destruct (IHHstep G V Ht) as [[q EQ]|[u [EQ Htu]]].
    + discriminate EQ.
    + inversion EQ; subst u. right. exists (t_app v t'). split; [reflexivity|].
      apply typing_app with (M:=M) (V:=V); assumption.
  - (* step_app_errL *) left. exists p. reflexivity.
  - (* step_app_errR *) left. exists p. reflexivity.
  - (* step_app_fail *) left. exists p. reflexivity.
  - (* step_app_norm *)
    destruct (inv_typing_app G v u Tz Hty) as [M [V [Hv [HMsafe Hu]]]].
    pose proof (norm_typing v v' H4 G M V Tz Hv) as Hv'.
    right. exists (t_app v' u). split; [reflexivity|].
    apply typing_app with (M:=mod_non_nullable) (V:=V).
    + exact Hv'.
    + discriminate.
    + exact Hu.
  - (* step_app_cast *)
    destruct (inv_typing_app G
                (t_cast v (typ_mod_arrow mod_non_nullable V1 V2) p
                   (typ_mod_arrow mod_non_nullable T1 T2)) v' Tz Hty)
      as [M [V [Hfun [HMsafe Hvv']]]].
    destruct (inv_typing_cast G v (typ_mod_arrow mod_non_nullable V1 V2) p
                (typ_mod_arrow mod_non_nullable T1 T2) (typ_mod_arrow M V Tz) Hfun)
      as [EU [Hv Hc]].
    injection EU as EM EV ET. subst.
    destruct (inv_compat_arrow mod_non_nullable V1 V2 mod_non_nullable T1 T2 Hc)
      as [Hd Hcod].
    pose proof (typing_cast G v' T1 p' V1 Hvv' Hd) as Harg.
    pose proof (typing_app G v (t_cast v' T1 p' V1) V2 mod_non_nullable V1
                  Hv (mod_nonnull_neq_safe) Harg) as Happ.
    right. exists (t_cast (t_app v (t_cast v' T1 p' V1)) V2 p T2).
    split; [reflexivity|].
    exact (typing_cast G (t_app v (t_cast v' T1 p' V1)) V2 p T2 Happ Hcod).
  - (* step_safe_app_null *)
    destruct (inv_typing_safe_app G v t1 t2 Tz Hty) as [M [V [Hf [HMn [Ht1 Ht2]]]]].
    right. exists t2. split; [reflexivity| exact Ht2].
  - (* step_safe_app_norm *)
    destruct (inv_typing_safe_app G v t1 t2 Tz Hty) as [M [V [Hf [HMn [Ht1 Ht2]]]]].
    pose proof (norm_typing v v' H4 G M V Tz Hf) as Hf'.
    right. exists (t_app v' t1). split; [reflexivity|].
    apply typing_app with (M:=mod_non_nullable) (V:=V).
    + exact Hf'.
    + discriminate.
    + exact Ht1.
  - (* step_safe_app_ctxL *)
    destruct (inv_typing_safe_app G t t1 t2 Tz Hty) as [M [V [Hf [HMn [Ht1 Ht2]]]]].
    destruct (IHHstep G (typ_mod_arrow M V Tz) Hf) as [[q EQ]|[u [EQ Hu]]].
    + discriminate EQ.
    + inversion EQ; subst u. right. exists (t_app_safe t' t1 t2). split; [reflexivity|].
      apply typing_safe_app with (M:=M) (V:=V); assumption.
  - (* step_safe_app_errL *) left. exists p. reflexivity.
Qed.

Lemma progress_aux : forall G tr T, G = nil -> typing G tr T ->
  (exists u, step tr u) \/ Is_true (is_val_of_trm tr).
Proof.
  intros G tr T Heq Hty. revert Heq. induction Hty; intros Heq.
  - (* var *) exfalso. subst G. unfold binds in H0. simpl in H0. inversion H0.
  - (* null *) right. reflexivity.
  - (* abs *) right. reflexivity.
  - (* app *)
    destruct (IHHty1 Heq) as [[u Hu]|Hval_s].
    + destruct u as [s'|q].
      * left. exists (r_term (t_app s' t)). apply step_app_ctxL.
        -- exact (typing_lc G t V Hty2).
        -- exact Hu.
      * left. exists (r_blame q). apply step_app_errL.
        -- exact (typing_lc G t V Hty2).
        -- exact Hu.
    + destruct (IHHty2 Heq) as [[u Hu]|Hval_t].
      * destruct u as [t'|q].
        -- left. exists (r_term (t_app s t')). apply step_app_ctxR.
           ++ exact Hval_s.
           ++ exact (typing_lc G s (typ_mod_arrow M V T) Hty1).
           ++ exact Hu.
        -- left. exists (r_blame q). apply step_app_errR.
           ++ exact Hval_s.
           ++ exact (typing_lc G s (typ_mod_arrow M V T) Hty1).
           ++ exact Hu.
      * destruct (isnull_dec s) as [Hn|Hn].
        -- destruct (unwrap_null_value G s (typ_mod_arrow M V T) Hty1 M V T eq_refl H Hval_s Hn) as [pp Hup].
           left. exists (r_blame pp). apply step_app_fail.
           ++ exact Hval_s.
           ++ exact Hval_t.
           ++ exact (typing_lc G t V Hty2).
           ++ exact Hn.
           ++ exact Hup.
        -- assert (Hab : isabs s).
           { apply val_not_null_isabs; [exact Hval_s | exact (typing_lc G s (typ_mod_arrow M V T) Hty1) | exact Hn]. }
           destruct (isabs_norm G s (typ_mod_arrow M V T) Hty1 Hab) as [s' [Hnorm [Hvals' Hlcs']]].
           left. exists (r_term (t_app s' t)). apply step_app_norm.
           ++ exact Hval_s.
           ++ exact Hval_t.
           ++ exact Hvals'.
           ++ exact (typing_lc G t V Hty2).
           ++ exact Hab.
           ++ exact Hnorm.
  - (* safe app *)

    destruct (IHHty1 Heq) as [[u Hu]|Hval_f].
    + destruct u as [f'|q].
      * left. exists (r_term (t_app_safe f' s t)). apply step_safe_app_ctxL.
        -- exact (typing_lc G s V Hty2).
        -- exact (typing_lc G t T Hty3).
        -- exact Hu.
      * left. exists (r_blame q). apply step_safe_app_errL.
        -- exact (typing_lc G s V Hty2).
        -- exact (typing_lc G t T Hty3).
        -- exact Hu.
    + destruct (isnull_dec f) as [Hn|Hn].
      * left. exists (r_term t). apply step_safe_app_null.
        -- exact Hval_f.
        -- exact (typing_lc G s V Hty2).
        -- exact (typing_lc G t T Hty3).
        -- exact Hn.
      * assert (Hab : isabs f).
        { apply val_not_null_isabs; [exact Hval_f | exact (typing_lc G f (typ_mod_arrow M V T) Hty1) | exact Hn]. }
        destruct (isabs_norm G f (typ_mod_arrow M V T) Hty1 Hab) as [f' [Hnorm [Hvals' Hlcs']]].
        left. exists (r_term (t_app f' s)). apply step_safe_app_norm.
        -- exact Hval_f.
        -- exact Hvals'.
        -- exact (typing_lc G t T Hty3).
        -- exact (typing_lc G s V Hty2).
        -- exact Hab.
        -- exact Hnorm.
  - (* cast *)
    destruct (IHHty Heq) as [[u Hu]|Hval].
    + destruct u as [s'|q].
      * left. exists (r_term (t_cast s' V p T)). apply step_cast_ctx. exact Hu.
      * left. exists (r_blame q). apply step_cast_err. exact Hu.
    + right. simpl. exact Hval.
Qed.

Theorem progress : forall t T,
  typing nil t T ->
  (exists u, step t u) \/ Is_true (is_val_of_trm t).
Proof.
  intros t T H. exact (progress_aux nil t T eq_refl H).
Qed.
