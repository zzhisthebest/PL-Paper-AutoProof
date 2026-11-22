Set Implicit Arguments.

Require Import STLC_Ref_Soundness_Common.
From Stdlib Require Import Lia.

Implicit Types Y : phi.

Implicit Types P : conf->Prop.

CoInductive coomnibig : conf -> (conf->Prop) -> Prop :=
  | coomnibig_val : forall c P,
      value (fst c) ->
      P c ->
      coomnibig c P
  | coomnibig_beta : forall mu t1 t2 P,
      sto_ok mu ->
      term (trm_abs t1) ->
      value t2 ->
      coomnibig (t1 ^^ t2, mu) P ->
      coomnibig (trm_app (trm_abs t1) t2, mu) P
  | coomnibig_rand : forall mu n P,
      (forall m, 0 <= m < max n 1 -> P ((trm_int m), mu)) ->
      coomnibig (trm_rand (trm_int n), mu) P
  | coomnibig_ref : forall mu t1 P,
      sto_ok mu ->
      value t1 ->
      (forall l, l # mu ->
        P (trm_loc l, (mu & l ~ t1))) ->
      coomnibig (trm_ref t1, mu) P
  | coomnibig_get : forall mu l t P,
      sto_ok mu ->
      binds l t mu ->
      P (t, mu) ->
      coomnibig (trm_get (trm_loc l), mu) P
  | coomnibig_set : forall mu l t2 P,
      sto_ok mu ->
      value t2 ->
      P (trm_unit, mu & l ~ t2) ->
      coomnibig (trm_set (trm_loc l) t2, mu) P

  | coomnibig_app_1 : forall mu t1 t2 P1 P,
      ~ value t1 ->
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_app t1' t2, mu') P) ->
      coomnibig (trm_app t1 t2, mu) P
  | coomnibig_app_2 : forall mu t1 t2 P1 P,
      value t1 ->
      ~ value t2 ->
      coomnibig (t2, mu) P1 ->
      (forall t2' mu', P1 (t2',mu') -> coomnibig (trm_app t1 t2', mu') P) ->
      coomnibig (trm_app t1 t2, mu) P
  | coomnibig_ref_1 : forall mu t1 P1 P,
      ~ value t1 ->
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_ref t1', mu') P) ->
      coomnibig (trm_ref t1, mu) P
  | coomnibig_get_1 : forall mu t1 P1 P,
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_get t1', mu') P) ->
      coomnibig (trm_get t1, mu) P
  | coomnibig_set_1 : forall mu t1 t2 P1 P,
      ~ value t1 ->
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_set t1' t2, mu') P) ->
      coomnibig (trm_set t1 t2, mu) P
  | coomnibig_set_2 : forall mu t1 t2 P1 P,
      value t1 ->
      ~ value t2 ->
      coomnibig (t2, mu) P1 ->
      (forall t2' mu', P1 (t2',mu') -> coomnibig (trm_set t1 t2', mu') P) ->
      coomnibig (trm_set t1 t2, mu) P
  | coomnibig_rand_1 : forall mu t1 P1 P,
      ~ value t1 ->
      coomnibig (t1, mu) P1 ->
      (forall t1' mu', P1 (t1',mu') -> coomnibig (trm_rand t1', mu') P) ->
      coomnibig (trm_rand t1, mu) P.

Definition post (Y:phi) (T:typ) : conf->Prop :=
  fun '(t,mu) =>
    exists Y', extends Y Y'
             /\ Y' |== mu
             /\ value t
             /\ empty ! Y' |= t ~: T.

Definition coomnibig_soundness := forall mu t Y T,
  Y |== mu ->
  empty ! Y |= t ~: T ->
  coomnibig (t,mu) (post Y T).

Definition himpl (H1 H2:conf->Prop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).




(* ============ basic facts about terms and values ============ *)

Lemma typing_term : forall E Y t T, typing E Y t T -> term t.
Proof.
  intros E Y t T H. induction H.
  - apply term_var.
  - apply (term_abs (L:=L)). intros x Hx. apply H0. exact Hx.
  - apply term_app; assumption.
  - apply term_trm_unit.
  - apply term_int.
  - apply term_loc.
  - apply term_ref; assumption.
  - apply term_get; assumption.
  - apply term_set; assumption.
  - apply term_rand; assumption.
Qed.

Lemma value_term : forall t, value t -> term t.
Proof.
  intros t H. induction H.
  - assumption.
  - apply term_trm_unit.
  - apply term_int.
  - apply term_loc.
Qed.

Lemma value_dec : forall t, term t -> value t \/ ~ value t.
Proof.
  intros t Ht. destruct t.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - left. apply value_abs. exact Ht.
  - right. intro H. inversion H.
  - left. apply value_unit.
  - left. apply value_int.
  - left. apply value_loc.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
Qed.

Lemma value_arrow_inv : forall E Y (v:trm) T1 T2,
  value v -> typing E Y v (typ_arrow T1 T2) -> exists t0, v = trm_abs t0.
Proof.
  introv Hv Ht. inductions Hv.
  - exists t1. reflexivity.
  - inverts Ht.
  - inverts Ht.
  - inverts Ht.
Qed.

Lemma value_ref_inv : forall E Y (v:trm) T,
  value v -> typing E Y v (typ_ref T) -> exists l, v = trm_loc l.
Proof.
  introv Hv Ht. inductions Hv.
  - inverts Ht.
  - inverts Ht.
  - inverts Ht.
  - exists l. reflexivity.
Qed.

Lemma value_int_inv : forall E Y (v:trm) ,
  value v -> typing E Y v typ_int -> exists n, v = trm_int n.
Proof.
  introv Hv Ht. inductions Hv.
  - inverts Ht.
  - inverts Ht.
  - exists n. reflexivity.
  - inverts Ht.
Qed.

(* ============ store typing helpers ============ *)

Lemma sto_typing_ok : forall Y mu, Y |== mu -> sto_ok mu.
Proof. introv H. destruct H as [H _]. exact H. Qed.

Lemma sto_typing_dom : forall Y mu, Y |== mu -> forall l, l # mu -> l # Y.
Proof. introv H. destruct H as [_ [H _]]. apply H. Qed.

Lemma sto_typing_binds : forall Y mu, Y |== mu ->
  forall l T, binds l T Y -> exists t, value t /\ binds l t mu /\ empty ! Y |= t ~: T.
Proof. introv H. destruct H as [_ [_ H]]. apply H. Qed.

(* ============ de Bruijn closedness of terms ============ *)

Fixpoint bclosed_rec (k:nat) (t:trm) : Prop :=
  match t with
  | trm_bvar i     => Nat.lt i k
  | trm_fvar _     => True
  | trm_abs t1     => bclosed_rec (S k) t1
  | trm_app t1 t2  => bclosed_rec k t1 /\ bclosed_rec k t2
  | trm_unit       => True
  | trm_int _      => True
  | trm_loc _      => True
  | trm_ref t1     => bclosed_rec k t1
  | trm_get t1     => bclosed_rec k t1
  | trm_set t1 t2  => bclosed_rec k t1 /\ bclosed_rec k t2
  | trm_rand t1    => bclosed_rec k t1
  end.

Definition closed_trm (t:trm) : Prop := forall j v, open_rec j v t = t.

Lemma open_bclosed_iff : forall t k x,
  bclosed_rec k (open_rec k (trm_fvar x) t) <-> bclosed_rec (S k) t.
Proof.
  induction t; intros k x; simpl.
  - case_if; simpl; split; intros H; try lia; auto.
  - tauto.
  - apply (IHt (S k) x).
  - split; intro H; destruct H as [H1 H2]; split;
      [ apply (proj1 (IHt1 k x)) | apply (proj1 (IHt2 k x)) | apply (proj2 (IHt1 k x)) | apply (proj2 (IHt2 k x)) ]; assumption.
  - tauto.
  - tauto.
  - tauto.
  - apply (IHt k x).
  - apply (IHt k x).
  - split; intro H; destruct H as [H1 H2]; split;
      [ apply (proj1 (IHt1 k x)) | apply (proj1 (IHt2 k x)) | apply (proj2 (IHt1 k x)) | apply (proj2 (IHt2 k x)) ]; assumption.
  - apply (IHt k x).
Qed.

Lemma term_bclosed : forall t, term t -> bclosed_rec 0 t.
Proof.
  intros t H. induction H.
  - simpl. tauto.
  - simpl. apply (proj1 (open_bclosed_iff t1 0 (var_gen L))).
    apply H0. apply var_gen_spec.
  - simpl. split; assumption.
  - simpl. tauto.
  - simpl. tauto.
  - simpl. tauto.
  - simpl. assumption.
  - simpl. assumption.
  - simpl. split; assumption.
  - simpl. assumption.
Qed.

Lemma open_rec_bclosed : forall t k,
  bclosed_rec k t -> forall j w, Nat.le k j -> open_rec j w t = t.
Proof.
  induction t; intros k Hb j w Hkj; simpl in *.
  - case_if; [lia|reflexivity].
  - reflexivity.
  - f_equal. apply (IHt (S k) Hb (S j) w). lia.
  - destruct Hb as [H1 H2]. rewrite (IHt1 k H1 j w); [|lia]. rewrite (IHt2 k H2 j w); [|lia]. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IHt k Hb j w); [reflexivity|lia].
  - rewrite (IHt k Hb j w); [reflexivity|lia].
  - destruct Hb as [H1 H2]. rewrite (IHt1 k H1 j w); [|lia]. rewrite (IHt2 k H2 j w); [|lia]. reflexivity.
  - rewrite (IHt k Hb j w); [reflexivity|lia].
Qed.

Lemma term_closed : forall t, term t -> closed_trm t.
Proof.
  intros t Ht j v. unfold closed_trm.
  exact (@open_rec_bclosed t 0 (term_bclosed Ht) j v (Nat.le_0_l j)).
Qed.



(* ============ substitution and opening ============ *)

Lemma subst_open_fvar : forall t u z k,
  z \notin fv t ->
  subst z u (open_rec k (trm_fvar z) t) = open_rec k u t.
Proof.
  induction t; intros u z k Hfv; simpl in *.
  - case_if; simpl; [case_if; reflexivity | reflexivity].
  - case_if; simpl; [subst v; exfalso; apply Hfv; apply in_singleton_self | reflexivity].
  - simpl. f_equal. apply IHt. assumption.
  - simpl. destruct (notin_union_r Hfv) as [H1 H2].
    rewrite IHt1; [|exact H1]. rewrite IHt2; [|exact H2]. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHt; [|assumption]. reflexivity.
  - simpl. rewrite IHt; [|assumption]. reflexivity.
  - simpl. destruct (notin_union_r Hfv) as [H1 H2].
    rewrite IHt1; [|exact H1]. rewrite IHt2; [|exact H2]. reflexivity.
  - simpl. rewrite IHt; [|assumption]. reflexivity.
Qed.

Lemma subst_open_comm : forall a u z y k,
  z <> y -> closed_trm u ->
  open_rec k (trm_fvar y) (subst z u a) = subst z u (open_rec k (trm_fvar y) a).
Proof.
  induction a; intros u z y k Hzy Hu; simpl in *.
  - case_if; simpl.
    + case_if; reflexivity.
    + reflexivity.
  - case_if; simpl.
    + subst v. rewrite (Hu k (trm_fvar y)). reflexivity.
    + reflexivity.
  - f_equal. apply IHa; assumption.
  - rewrite IHa1; [|assumption|assumption]. rewrite IHa2; [|assumption|assumption]. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHa; [|assumption|assumption]. reflexivity.
  - rewrite IHa; [|assumption|assumption]. reflexivity.
  - rewrite IHa1; [|assumption|assumption]. rewrite IHa2; [|assumption|assumption]. reflexivity.
  - rewrite IHa; [|assumption|assumption]. reflexivity.
Qed.

Lemma subst_open_comm_open : forall a u z y,
  z <> y -> closed_trm u ->
  open (subst z u a) (trm_fvar y) = subst z u (open a (trm_fvar y)).
Proof. intros. apply (@subst_open_comm a u z y 0); assumption. Qed.

(* ============ environment weakening ============ *)

Lemma extends_push_same : forall (E1 E2:env) x v,
  extends E1 E2 -> extends (E1 & x ~ v) (E2 & x ~ v).
Proof.
  intros E1 E2 x v Hext y w Hy.
  destruct (binds_push_inv Hy) as [[Hxy Hwv]|[Hxy Hy']].
  - subst. apply binds_push_eq.
  - apply binds_push_neq; [apply Hext; assumption | exact Hxy].
Qed.

Lemma typing_weaken_env : forall E1 E2 Y t T,
  typing E1 Y t T -> ok E1 -> ok E2 -> extends E1 E2 -> typing E2 Y t T.
Proof.
  intros E1 E2 Y t T H Hok1. revert E2.
  induction H; intros E2 Hok2 Hext.
  - apply typing_var; [exact Hok2 | apply Hext; assumption].
  - apply (typing_abs (L := L \u dom E \u dom E2)).
    intros x Hx.
    destruct (notin_union_r Hx) as [HxL HxE2'].
    destruct (notin_union_r HxE2') as [HxE HxE2].
    apply (H0 x HxL).
    + apply ok_push; assumption.
    + apply ok_push; assumption.
    + apply extends_push_same; assumption.
  - eapply typing_app; [apply IHtyping1; assumption|apply IHtyping2; assumption].
  - apply typing_unit; assumption.
  - apply typing_int; assumption.
  - apply typing_loc; [assumption|assumption].
  - apply typing_ref; apply IHtyping; assumption.
  - apply typing_get; apply IHtyping; assumption.
  - eapply typing_set; [apply IHtyping1; assumption|apply IHtyping2; assumption].
  - apply typing_rand; apply IHtyping; assumption.
Qed.

(* ============ substitution for typing ============ *)

Lemma typing_subst_gen : forall (E:env) Y (t:trm) T,
  typing E Y t T ->
  ok E ->
  forall E1 E2 z U,
  E = E1 & z ~ U & E2 ->
  forall u, closed_trm u ->
  typing (E1 & E2) Y u U ->
  typing (E1 & E2) Y (subst z u t) T.
Proof.
  intros E Y t T Hty.
  induction Hty; intros Hok E1 E2 z Us HE u Hcl Hu.
  - (* var *) subst E. simpl. case_if.
    + subst x. assert (T = Us) as HTU by (eapply binds_middle_eq_inv; eassumption).
      subst T. exact Hu.
    + apply typing_var.
      * eapply (ok_remove (F:=z ~ Us)); eassumption.
      * eapply (binds_subst (x2:=z) (v2:=Us)); [ exact H0 | assumption ].
  - (* abs *)
    apply (typing_abs (L := L \u dom E \u dom (E1 & E2) \u \{z})).
    intros x Hx.
    destruct (notin_union_r Hx) as [HxL Hx1].
    destruct (notin_union_r Hx1) as [HxE Hx2].
    destruct (notin_union_r Hx2) as [HxEE Hxz].
    change (E1 & E2 & x ~ U ! Y |= (subst z u t1) ^ x ~: T).
    rewrite (@subst_open_comm_open t1 u z x (fun Hc => notin_singleton_r Hxz (eq_sym Hc)) Hcl).
    rewrite <- (concat_assoc E1 E2 (x ~ U)).
    assert (Hokx : ok (E & x ~ U)) by (apply ok_push; assumption).
    assert (HEq : E & x ~ U = E1 & z ~ Us & (E2 & x ~ U)).
    { rewrite HE. symmetry. apply concat_assoc. }
    assert (HokR : ok (E1 & E2)).
    { eapply (ok_remove (F:=z~Us)). rewrite <- HE. exact Hok. }
    assert (Hu' : E1 & (E2 & x ~ U) ! Y |= u ~: Us).
    { eapply typing_weaken_env.
      - exact Hu.
      - exact HokR.
      - rewrite (concat_assoc E1 E2 (x ~ U)).
        apply ok_push; [ exact HokR | exact HxEE ].
      - rewrite (concat_assoc E1 E2 (x ~ U)). apply extends_push. exact HxEE. }
    apply (H0 x HxL Hokx E1 (E2 & x ~ U) z Us HEq u Hcl Hu').
  - (* app *) eapply typing_app.
    + apply (IHHty1 Hok E1 E2 z Us HE u Hcl Hu).
    + apply (IHHty2 Hok E1 E2 z Us HE u Hcl Hu).
  - (* unit *) simpl. apply typing_unit.
    eapply (ok_remove (F:=z~Us)). rewrite <- HE. exact Hok.
  - (* int *) simpl. apply typing_int.
    eapply (ok_remove (F:=z~Us)). rewrite <- HE. exact Hok.
  - (* loc *) simpl. apply typing_loc.
    + eapply (ok_remove (F:=z~Us)). rewrite <- HE. exact Hok.
    + assumption.
  - (* ref *) simpl. apply typing_ref.
    apply (IHHty Hok E1 E2 z Us HE u Hcl Hu).
  - (* get *) simpl. apply typing_get.
    apply (IHHty Hok E1 E2 z Us HE u Hcl Hu).
  - (* set *) simpl. eapply typing_set.
    + apply (IHHty1 Hok E1 E2 z Us HE u Hcl Hu).
    + apply (IHHty2 Hok E1 E2 z Us HE u Hcl Hu).
  - (* rand *) simpl. apply typing_rand.
    apply (IHHty Hok E1 E2 z Us HE u Hcl Hu).
Qed.


(* ============ beta typing ============ *)

Lemma typing_beta : forall Y T1 T2 t0 t2,
  empty ! Y |= trm_abs t0 ~: typ_arrow T1 T2 ->
  empty ! Y |= t2 ~: T1 ->
  empty ! Y |= t0 ^^ t2 ~: T2.
Proof.
  intros Y T1 T2 t0 t2 H1 H2.
  inversion H1; subst.
  pose (x := var_gen (L \u fv t0)).
  assert (HxL : x \notin L) by (unfold x; apply (notin_union_r1 (F:=fv t0)); apply var_gen_spec).
  assert (Hxfv : x \notin fv t0) by (unfold x; apply (notin_union_r2 (E:=L)); apply var_gen_spec).
  assert (Hprem : empty & x ~ T1 ! Y |= t0 ^ x ~: T2) by (apply (H5 x HxL)).
  assert (Hokx : ok (empty & x ~ T1)).
  { apply ok_push. apply ok_empty. rewrite dom_empty. apply notin_empty. }
  assert (Hcl : closed_trm t2) by (apply term_closed; exact (@typing_term empty Y t2 T1 H2)).
  assert (Heq : empty & x ~ T1 = empty & x ~ T1 & empty) by (rewrite concat_empty_r; reflexivity).
  assert (Hu : empty & empty ! Y |= t2 ~: T1) by (rewrite concat_empty_l; exact H2).
  pose proof (@typing_subst_gen (empty & x ~ T1) Y (t0 ^ x) T2 Hprem Hokx empty empty x T1 Heq t2 Hcl Hu) as Hres.
  rewrite concat_empty_l in Hres.
  change (empty ! Y |= subst x t2 (open_rec 0 (trm_fvar x) t0) ~: T2) in Hres.
  rewrite (@subst_open_fvar t0 t2 x 0 Hxfv) in Hres.
  change (empty ! Y |= open_rec 0 t2 t0 ~: T2).
  exact Hres.
Qed.

(* ============ phi weakening and store typing lemmas ============ *)

Lemma extends_refl_phi : forall (Y:phi), extends Y Y.
Proof. intros Y x v H. exact H. Qed.

Lemma extends_trans_phi : forall (X Y Z:phi), extends X Y -> extends Y Z -> extends X Z.
Proof. intros X Y Z H1 H2 x v H. apply H2, H1, H. Qed.

Lemma typing_extend_phi : forall E Y Y' t T,
  typing E Y t T -> extends Y Y' -> typing E Y' t T.
Proof.
  intros E Y Y' t T H. revert Y'.
  induction H; intros Y'' Hext.
  - apply typing_var; assumption.
  - apply (typing_abs (L:=L)). intros x Hx.
    apply (H0 x Hx Y'' Hext).
  - eapply typing_app; [apply IHtyping1; assumption|apply IHtyping2; assumption].
  - apply typing_unit; assumption.
  - apply typing_int; assumption.
  - apply typing_loc; [assumption|apply Hext; assumption].
  - apply typing_ref; apply IHtyping; assumption.
  - apply typing_get; apply IHtyping; assumption.
  - eapply typing_set; [apply IHtyping1; assumption|apply IHtyping2; assumption].
  - apply typing_rand; apply IHtyping; assumption.
Qed.

(* ============ store typing update lemmas ============ *)

Lemma sto_typing_push : forall Y mu l T (t:trm),
  Y |== mu -> l # mu -> value t -> empty ! Y |= t ~: T ->
  (Y & l ~ T) |== (mu & l ~ t).
Proof.
  intros Y mu l T t Hsto Hl Hv Htyt.
  destruct Hsto as [Hok [Hdom Hbind]].
  assert (Hterm : term t) by (apply value_term; exact Hv).
  assert (HlY : l # Y) by (apply Hdom; exact Hl).
  split.
  - apply sto_ok_push; assumption.
  - split.
    + intros l' Hl'.
      rewrite (dom_concat mu (l ~ t)) in Hl'.
      apply notin_union_r in Hl'. destruct Hl' as [Hl'mu Hl'l].
      rewrite (dom_single l t) in Hl'l.
      rewrite (dom_concat Y (l ~ T)).
      apply notin_union_l.
      * apply Hdom; exact Hl'mu.
      * rewrite (dom_single l T). apply notin_singleton_l. apply notin_singleton_r in Hl'l. auto.
    + intros l' T' Hb.
      destruct (binds_push_inv Hb) as [[Hl' Heq] | [Hl' Hb']].
      * subst l'. subst T'. exists t. split; [exact Hv|]. split.
        -- apply binds_push_eq.
        -- apply typing_extend_phi with (Y:=Y); [exact Htyt | apply extends_push; exact HlY].
      * destruct (Hbind l' T' Hb') as [t0 [Hv0 [Hb0 Hty0]]].
        exists t0. split; [exact Hv0|]. split.
        -- apply binds_push_neq; [exact Hb0 | exact Hl'].
        -- apply typing_extend_phi with (Y:=Y); [exact Hty0 | apply extends_push; exact HlY].
Qed.

Lemma sto_typing_set : forall Y mu l T (t:trm),
  Y |== mu -> binds l T Y -> value t -> empty ! Y |= t ~: T ->
  Y |== (mu & l ~ t).
Proof.
  intros Y mu l T t Hsto Hbl Hv Htyt.
  destruct Hsto as [Hok [Hdom Hbind]].
  assert (Hterm : term t) by (apply value_term; exact Hv).
  split.
  - apply sto_ok_push; assumption.
  - split.
    + intros l' Hl'.
      rewrite (dom_concat mu (l ~ t)) in Hl'.
      apply notin_union_r in Hl'. destruct Hl' as [Hl'mu Hl'l].
      apply Hdom; exact Hl'mu.
    + intros l' T' Hb.
      destruct (classicT (l' = l)) as [Heq | Hneq].
      * subst l'. 
        assert (T' = T) by (apply binds_functional with (x:=l) (E:=Y); assumption).
        subst T'. exists t. split; [exact Hv|]. split.
        -- apply binds_push_eq.
        -- exact Htyt.
      * destruct (Hbind l' T' Hb) as [t0 [Hv0 [Hb0 Hty0]]].
        exists t0. split; [exact Hv0|]. split.
        -- apply binds_push_neq; [exact Hb0 | exact Hneq].
        -- exact Hty0.
Qed.

(* ============ monotonicity ============ *)

Lemma post_mono : forall Y Y' T, extends Y Y' -> (post Y' T) ==> (post Y T).
Proof.
  intros Y Y' T Hext [t mu] H. unfold post in *.
  destruct H as [Y'' [H1 [H2 [H3 H4]]]].
  exists Y''. split; [|split; [|split]]; auto. apply extends_trans_phi with Y'; assumption.
Qed.

Lemma coomnibig_mono : forall c P1 P2, coomnibig c P1 -> (P1 ==> P2) -> coomnibig c P2.
Proof.
  cofix CIH. intros c P1 P2 H HP.
  destruct H.
  - apply coomnibig_val; [assumption|apply HP; assumption].
  - eapply coomnibig_beta.
    + eassumption.
    + eassumption.
    + eassumption.
    + exact (CIH _ P P2 H2 HP).
  - apply coomnibig_rand. intros m Hm. apply HP. apply H. exact Hm.
  - apply coomnibig_ref.
    + eassumption.
    + eassumption.
    + intros l Hl. apply HP. apply H1. exact Hl.
  - eapply coomnibig_get.
    + eassumption.
    + eassumption.
    + apply HP. exact H1.
  - apply coomnibig_set.
    + eassumption.
    + eassumption.
    + apply HP. exact H1.
  - eapply coomnibig_app_1.
    + eassumption.
    + exact H0.
    + intros t1' mu' Hp. exact (CIH _ P P2 (H1 t1' mu' Hp) HP).
  - eapply coomnibig_app_2.
    + eassumption.
    + eassumption.
    + exact H1.
    + intros t1' mu' Hp. exact (CIH _ P P2 (H2 t1' mu' Hp) HP).
  - eapply coomnibig_ref_1.
    + eassumption.
    + exact H0.
    + intros t1' mu' Hp. exact (CIH _ P P2 (H1 t1' mu' Hp) HP).
  - eapply coomnibig_get_1.
    + exact H.
    + intros t1' mu' Hp. exact (CIH _ P P2 (H0 t1' mu' Hp) HP).
  - eapply coomnibig_set_1.
    + eassumption.
    + exact H0.
    + intros t1' mu' Hp. exact (CIH _ P P2 (H1 t1' mu' Hp) HP).
  - eapply coomnibig_set_2.
    + eassumption.
    + eassumption.
    + exact H1.
    + intros t1' mu' Hp. exact (CIH _ P P2 (H2 t1' mu' Hp) HP).
  - eapply coomnibig_rand_1.
    + eassumption.
    + exact H0.
    + intros t1' mu' Hp. exact (CIH _ P P2 (H1 t1' mu' Hp) HP).
Qed.


(* ============ post intro ============ *)

Lemma post_intro : forall Y T t mu,
  Y |== mu -> value t -> empty ! Y |= t ~: T -> post Y T (t,mu).
Proof.
  intros. unfold post. exists Y. split; [apply extends_refl_phi|split; [assumption|split; assumption]].
Qed.

Lemma post_intro_ext : forall Y Y' T t mu,
  extends Y Y' -> Y' |== mu -> value t -> empty ! Y' |= t ~: T -> post Y T (t,mu).
Proof.
  intros. unfold post. exists Y'. tauto.
Qed.

(* ============ main theorem ============ *)

(* main generalized soundness lemma *)
Lemma typed_coomnibig : forall mu t Y T Y0,
  extends Y0 Y -> Y |== mu -> empty ! Y |= t ~: T ->
  coomnibig (t,mu) (post Y0 T).
Proof.
  cofix CIH. intros mu t Y T Y0 Hext Hsto Hty.
  destruct t as [n | v | t1 | t1 t2 | | n | l | t1 | t1 | t1 t2 | t1].
  - (* bvar *) inversion Hty.
  - (* fvar *) inversion Hty; subst. destruct (binds_empty_inv H3).
  - (* abs *) pose proof (@typing_term empty Y (trm_abs t1) T Hty) as Hterm.
    inversion Hty; subst.
    apply coomnibig_val.
    + apply value_abs. exact Hterm.
    + apply post_intro_ext with (Y':=Y); [exact Hext | exact Hsto | apply value_abs; exact Hterm | assumption].
  - (* app *) inversion Hty; subst.
    destruct (@value_dec t1 (@typing_term empty Y t1 (typ_arrow T1 T) H3)) as [Hv1 | Hnv1].
    + destruct (@value_dec t2 (@typing_term empty Y t2 T1 H5)) as [Hv2 | Hnv2].
      * destruct (@value_arrow_inv empty Y t1 T1 T Hv1 H3) as [t0 Heq]. subst t1.
        eapply coomnibig_beta.
        -- eapply sto_typing_ok; exact Hsto.
        -- apply value_term; exact Hv1.
        -- exact Hv2.
        -- refine (@CIH mu (t0 ^^ t2) Y T Y0 Hext Hsto _).
           apply typing_beta with (T1:=T1); assumption.
      * eapply coomnibig_app_2 with (P1 := post Y T1).
        -- exact Hv1.
        -- exact Hnv2.
        -- refine (@CIH mu t2 Y T1 Y (@extends_refl_phi Y) Hsto H5).
        -- intros t2' mu' Hp.
           unfold post in Hp. destruct Hp as [Y' [Hext' [Hsto' [Hv2' Hty2']]]].
           refine (@CIH mu' (trm_app t1 t2') Y' T Y0 _ Hsto' _).
           ++ eapply extends_trans_phi; [exact Hext | exact Hext'].
           ++ eapply typing_app.
              ** eapply typing_extend_phi; [exact H3 | exact Hext'].
              ** exact Hty2'.
    + eapply coomnibig_app_1 with (P1 := post Y (typ_arrow T1 T)).
      * exact Hnv1.
      * refine (@CIH mu t1 Y (typ_arrow T1 T) Y (@extends_refl_phi Y) Hsto H3).
      * intros t1' mu' Hp.
        unfold post in Hp. destruct Hp as [Y' [Hext' [Hsto' [Hv1' Hty1']]]].
        refine (@CIH mu' (trm_app t1' t2) Y' T Y0 _ Hsto' _).
        -- eapply extends_trans_phi; [exact Hext | exact Hext'].
        -- eapply typing_app.
           ++ exact Hty1'.
           ++ eapply typing_extend_phi; [exact H5 | exact Hext'].
  - (* unit *) inversion Hty; subst.
    apply coomnibig_val.
    + apply value_unit.
    + apply post_intro_ext with (Y':=Y); [exact Hext | exact Hsto | apply value_unit | apply typing_unit; assumption].
  - (* int *) inversion Hty; subst.
    apply coomnibig_val.
    + apply value_int.
    + apply post_intro_ext with (Y':=Y); [exact Hext | exact Hsto | apply value_int | apply typing_int; assumption].
  - (* loc *) inversion Hty; subst.
    apply coomnibig_val.
    + apply value_loc.
    + apply post_intro_ext with (Y':=Y); [exact Hext | exact Hsto | apply value_loc | apply typing_loc; assumption].
  - (* ref *) inversion Hty; subst.
    destruct (@value_dec t1 (@typing_term empty Y t1 T0 H2)) as [Hv1 | Hnv1].
    + eapply coomnibig_ref.
      * eapply sto_typing_ok; exact Hsto.
      * exact Hv1.
      * intros l0 Hl0.
        unfold post. exists (Y & l0 ~ T0). split.
        -- eapply extends_trans_phi; [exact Hext | apply extends_push; eapply sto_typing_dom; eassumption].
        -- split.
           ++ apply sto_typing_push; assumption.
           ++ split; [apply value_loc | apply typing_loc; [apply ok_empty | apply binds_push_eq]].
    + eapply coomnibig_ref_1 with (P1 := post Y T0).
      * exact Hnv1.
      * refine (@CIH mu t1 Y T0 Y (@extends_refl_phi Y) Hsto H2).
      * intros t1' mu' Hp.
        unfold post in Hp. destruct Hp as [Y' [Hext' [Hsto' [Hv1' Hty1']]]].
        refine (@CIH mu' (trm_ref t1') Y' (typ_ref T0) Y0 _ Hsto' _).
        -- eapply extends_trans_phi; [exact Hext | exact Hext'].
        -- apply typing_ref; exact Hty1'.
  - (* get *) inversion Hty; subst.
    destruct (@value_dec t1 (@typing_term empty Y t1 (typ_ref T) H2)) as [Hv1 | Hnv1].
    + destruct (@value_ref_inv empty Y t1 T Hv1 H2) as [l0 Heq]. subst t1.
      inversion H2; subst.
      destruct (sto_typing_binds Hsto H5) as [t0 [Hvt [Hbt Htyt]]].
      refine (@coomnibig_get mu l0 t0 (post Y0 T) _ Hbt _).
      * eapply sto_typing_ok; exact Hsto.
      * apply post_intro_ext with (Y':=Y); [exact Hext | exact Hsto | exact Hvt | exact Htyt].
    + eapply coomnibig_get_1 with (P1 := post Y (typ_ref T)).
      * refine (@CIH mu t1 Y (typ_ref T) Y (@extends_refl_phi Y) Hsto H2).
      * intros t1' mu' Hp.
        unfold post in Hp. destruct Hp as [Y' [Hext' [Hsto' [Hv1' Hty1']]]].
        refine (@CIH mu' (trm_get t1') Y' T Y0 _ Hsto' _).
        -- eapply extends_trans_phi; [exact Hext | exact Hext'].
        -- apply typing_get; exact Hty1'.
  - (* set *) inversion Hty; subst.
    destruct (@value_dec t1 (@typing_term empty Y t1 (typ_ref T0) H3)) as [Hv1 | Hnv1].
    + destruct (@value_ref_inv empty Y t1 T0 Hv1 H3) as [l0 Heq]. subst t1.
      inversion H3; subst.
      destruct (@value_dec t2 (@typing_term empty Y t2 T0 H5)) as [Hv2 | Hnv2].
      * refine (@coomnibig_set mu l0 t2 (post Y0 typ_unit) _ _ _).
        -- eapply sto_typing_ok; exact Hsto.
        -- exact Hv2.
        -- apply post_intro_ext with (Y':=Y).
           ++ exact Hext.
           ++ eapply sto_typing_set; [exact Hsto | exact H6 | exact Hv2 | exact H5].
           ++ apply value_unit.
           ++ apply typing_unit; apply ok_empty.
      * eapply coomnibig_set_2 with (P1 := post Y T0).
        -- exact Hv1.
        -- exact Hnv2.
        -- refine (@CIH mu t2 Y T0 Y (@extends_refl_phi Y) Hsto H5).
        -- intros t2' mu' Hp.
           unfold post in Hp. destruct Hp as [Y' [Hext' [Hsto' [Hv2' Hty2']]]].
           refine (@coomnibig_set mu' l0 t2' (post Y0 typ_unit) _ _ _).
           ++ eapply sto_typing_ok; exact Hsto'.
           ++ exact Hv2'.
           ++ apply post_intro_ext with (Y':=Y').
              ** eapply extends_trans_phi; [exact Hext | exact Hext'].
              ** eapply sto_typing_set; [exact Hsto' | exact (Hext' l0 T0 H6) | exact Hv2' | exact Hty2'].
              ** apply value_unit.
              ** apply typing_unit; apply ok_empty.
    + eapply coomnibig_set_1 with (P1 := post Y (typ_ref T0)).
      * exact Hnv1.
      * refine (@CIH mu t1 Y (typ_ref T0) Y (@extends_refl_phi Y) Hsto H3).
      * intros t1' mu' Hp.
        unfold post in Hp. destruct Hp as [Y' [Hext' [Hsto' [Hv1' Hty1']]]].
        refine (@CIH mu' (trm_set t1' t2) Y' typ_unit Y0 _ Hsto' _).
        -- eapply extends_trans_phi; [exact Hext | exact Hext'].
        -- eapply typing_set.
           ++ exact Hty1'.
           ++ eapply typing_extend_phi; [exact H5 | exact Hext'].
  - (* rand *) inversion Hty; subst.
    destruct (@value_dec t1 (@typing_term empty Y t1 typ_int H2)) as [Hv1 | Hnv1].
    + destruct (@value_int_inv empty Y t1 Hv1 H2) as [n0 Heq]. subst t1.
      eapply coomnibig_rand.
      intros m Hm.
      apply post_intro_ext with (Y':=Y).
      * exact Hext.
      * exact Hsto.
      * apply value_int.
      * apply typing_int; apply ok_empty.
    + eapply coomnibig_rand_1 with (P1 := post Y typ_int).
      * exact Hnv1.
      * refine (@CIH mu t1 Y typ_int Y (@extends_refl_phi Y) Hsto H2).
      * intros t1' mu' Hp.
        unfold post in Hp. destruct Hp as [Y' [Hext' [Hsto' [Hv1' Hty1']]]].
        refine (@CIH mu' (trm_rand t1') Y' typ_int Y0 _ Hsto' _).
        -- eapply extends_trans_phi; [exact Hext | exact Hext'].
        -- apply typing_rand; exact Hty1'.
Qed.


Theorem coomnibig_soundness_result : coomnibig_soundness.
Proof.
  unfold coomnibig_soundness. intros mu t Y T Hsto Hty.
  exact (@typed_coomnibig mu t Y T Y (@extends_refl_phi Y) Hsto Hty).
Qed.


