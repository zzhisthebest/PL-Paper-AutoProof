Set Implicit Arguments.

Require Import STLC_Ref_Soundness_Common.

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

Local Lemma omni_typing_term E Y t T :
  E ! Y |= t ~: T -> term t.
Proof.
  intro H. induction H; eauto using term_var, term_abs, term_app,
    term_trm_unit, term_int, term_loc, term_ref, term_get, term_set, term_rand.
Qed.

Local Lemma omni_value_term t : value t -> term t.
Proof.
  intro H. destruct H; auto using term_trm_unit, term_int, term_loc.
Qed.

Local Lemma omni_typing_weaken E Y t T :
  E ! Y |= t ~: T ->
  forall F Z, ok F -> extends E F -> extends Y Z -> F ! Z |= t ~: T.
Proof.
  intro HT. induction HT; intros F Z HF HE HY;
    eauto using typing_var, typing_app, typing_unit, typing_int, typing_loc,
      typing_ref, typing_get, typing_set, typing_rand.
  apply typing_abs with (L := L \u dom F).
  intros x Hx. apply notin_union in Hx as [HxL HxF].
  apply H0; auto using ok_push.
  intros y V Hy.
  apply binds_push_inv in Hy as [[-> ->] | [Hneq Hy]].
  - apply binds_push_eq.
  - apply binds_push_neq; auto.
Qed.

Local Lemma omni_open_rec_other t :
  forall i j u v, i <> j ->
  {j ~> v} t = {i ~> u} ({j ~> v} t) ->
  t = {i ~> u} t.
Proof.
  induction t; intros i j u w Hneq Hopen; simpl in *; try reflexivity.
  - destruct (classicT (j = n)) as [-> | Hjn].
    + destruct (classicT (i = n)); congruence.
    + exact Hopen.
  - injection Hopen as Hopen. f_equal.
    apply IHt with (j := S j) (v := w); [congruence | exact Hopen].
  - injection Hopen as H1 H2. f_equal; eauto.
  - injection Hopen as Hopen. f_equal. eauto.
  - injection Hopen as Hopen. f_equal. eauto.
  - injection Hopen as H1 H2. f_equal; eauto.
  - injection Hopen as Hopen. f_equal. eauto.
Qed.

Local Lemma omni_open_rec_term t :
  term t -> forall k u, {k ~> u} t = t.
Proof.
  intro H. induction H; intros k u; simpl; try solve [f_equal; auto].
  destruct (var_fresh L) as [x Hx].
  f_equal. symmetry.
  eapply omni_open_rec_other with (j := 0) (v := trm_fvar x).
  - discriminate.
  - symmetry. apply H0. exact Hx.
Qed.

Local Lemma omni_subst_open_rec t :
  forall k z u v, term u ->
  [z ~> u] ({k ~> v} t) = {k ~> ([z ~> u] v)} ([z ~> u] t).
Proof.
  induction t; intros k z u w Hu; simpl; try solve [f_equal; auto].
  - destruct (classicT (k = n)); reflexivity.
  - destruct (classicT (v = z)); [symmetry; auto using omni_open_rec_term | reflexivity].
Qed.

Local Lemma omni_subst_intro t :
  forall k x u, x \notin fv t ->
  [x ~> u] ({k ~> trm_fvar x} t) = {k ~> u} t.
Proof.
  induction t; intros k x u Hx; simpl in *;
    try solve [apply notin_union in Hx as [Hx1 Hx2]; f_equal; auto];
    try solve [f_equal; auto].
  - destruct (classicT (k = n)); simpl; [|reflexivity].
    destruct (classicT (x = x)); congruence.
  - apply notin_singleton in Hx.
    destruct (classicT (v = x)); congruence.
Qed.

Local Lemma omni_typing_subst E Y t T :
  E ! Y |= t ~: T ->
  forall F z u U, ok F -> empty ! Y |= u ~: U ->
    (forall x V, binds x V E -> (x = z /\ V = U) \/
                                (x <> z /\ binds x V F)) ->
    F ! Y |= ([z ~> u] t) ~: T.
Proof.
  intro HT. induction HT; intros F z u V HF Hu Hbind; simpl;
    eauto using typing_app, typing_unit, typing_int, typing_loc, typing_ref,
      typing_get, typing_set, typing_rand.
  - destruct (Hbind _ _ H0) as [[-> ->] | [Hx HxF]].
    + destruct (classicT (z = z)); [|contradiction].
      eapply omni_typing_weaken; eauto using extends_refl.
      intros y W Hy. exfalso. eapply binds_empty_inv; eauto.
    + destruct (classicT (x = z)); [contradiction | auto using typing_var].
  - apply typing_abs with (L := L \u (dom F \u \{z})).
    intros x Hx. apply notin_union in Hx as [HxL Hx].
    apply notin_union in Hx as [HxF Hxz].
    apply notin_singleton in Hxz.
    change (F & x ~ U ! Y |= {0 ~> trm_fvar x} ([z ~> u] t1) ~: T).
    assert (Hvar : [z ~> u] (trm_fvar x) = trm_fvar x).
    { simpl. destruct (classicT (x = z)); congruence. }
    rewrite <- Hvar at 1.
    rewrite <- omni_subst_open_rec by eauto using omni_typing_term.
    eapply H0; eauto using ok_push.
    intros y W Hy.
    apply binds_push_inv in Hy as [[-> ->] | [Hyx Hy]].
    + right. auto using binds_push_eq.
    + destruct (Hbind _ _ Hy) as [Hmatch | [Hyz HyF]].
      * left. exact Hmatch.
      * right. auto using binds_push_neq.
Qed.

Local Lemma omni_typing_beta Y t u U T :
  empty ! Y |= trm_abs t ~: typ_arrow U T ->
  empty ! Y |= u ~: U ->
  empty ! Y |= t ^^ u ~: T.
Proof.
  intros Habs Hu.
  inversion Habs as [|L E Z U' T' t' Hbody| | | | | | | |]; subst.
  destruct (var_fresh (L \u fv t)) as [x Hx].
  apply notin_union in Hx as [HxL Hxt].
  unfold open. rewrite <- omni_subst_intro with (x := x) by exact Hxt.
  eapply omni_typing_subst; eauto using ok_empty.
  intros y V Hy. apply binds_push_inv in Hy as [Hmatch | [_ Hy]].
  - left. exact Hmatch.
  - exfalso. eapply binds_empty_inv; eauto.
Qed.

Local Lemma omni_typing_store_weaken Y Z t T :
  extends Y Z -> empty ! Y |= t ~: T -> empty ! Z |= t ~: T.
Proof.
  intros HE HT.
  eapply omni_typing_weaken; eauto using ok_empty, extends_refl.
Qed.

Local Lemma omni_extends_trans (X Y Z : phi) :
  extends X Y -> extends Y Z -> extends X Z.
Proof.
  intros HXY HYZ l U Hl. apply HYZ, HXY, Hl.
Qed.

Local Lemma omni_store_alloc mu Y l t U :
  Y |== mu -> l # mu -> value t -> empty ! Y |= t ~: U ->
  (Y & l ~ U) |== (mu & l ~ t).
Proof.
  intros (Hok & Hfresh & Hlookup) Hl Hv HT.
  assert (HE : extends Y (Y & l ~ U)) by auto using extends_push.
  split; [constructor; auto using omni_value_term |].
  split.
  - intros k Hk. rewrite dom_concat, dom_single in Hk |- *.
    apply notin_union in Hk as [Hk Hkl].
    apply notin_union. auto.
  - intros k V Hk.
    apply binds_push_inv in Hk as [[-> ->] | [Hkl Hk]].
    + exists t. repeat split; eauto using binds_push_eq, omni_typing_store_weaken.
    + destruct (Hlookup _ _ Hk) as (v & Hval & Hbind & Htyp).
      exists v. repeat split; eauto using binds_push_neq, omni_typing_store_weaken.
Qed.

Local Lemma omni_store_update mu Y l t U :
  Y |== mu -> binds l U Y -> value t -> empty ! Y |= t ~: U ->
  Y |== (mu & l ~ t).
Proof.
  intros (Hok & Hfresh & Hlookup) Hl Hv HT.
  split; [constructor; auto using omni_value_term |].
  split.
  - intros k Hk. rewrite dom_concat in Hk.
    apply notin_union in Hk as [Hk _]. auto.
  - intros k V Hk.
    destruct (classic (k = l)) as [-> | Hneq].
    + assert (V = U) by (eapply binds_functional; eauto). subst.
      exists t. repeat split; auto using binds_push_eq.
    + destruct (Hlookup _ _ Hk) as (v & Hval & Hbind & Htyp).
      exists v. repeat split; auto using binds_push_neq.
Qed.

Local Lemma omni_arrow_value Y t U T :
  empty ! Y |= t ~: typ_arrow U T -> value t ->
  exists b, t = trm_abs b /\ term (trm_abs b).
Proof.
  intros HT Hv. inversion Hv; subst; inversion HT; eauto.
Qed.

Local Lemma omni_ref_value Y t U :
  empty ! Y |= t ~: typ_ref U -> value t ->
  exists l, t = trm_loc l /\ binds l U Y.
Proof.
  intros HT Hv. inversion Hv; subst; inversion HT; eauto.
Qed.

Local Lemma omni_int_value Y t :
  empty ! Y |= t ~: typ_int -> value t ->
  exists n, t = trm_int n.
Proof.
  intros HT Hv. inversion Hv; subst; inversion HT; eauto.
Qed.

Local Lemma omni_post (Y0 Y : phi) t mu T :
  extends Y0 Y -> Y |== mu -> value t -> empty ! Y |= t ~: T ->
  post Y0 T (t, mu).
Proof.
  intros HE Hstore Hv HT. exists Y. split; [exact HE |].
  split; [exact Hstore |]. split; assumption.
Qed.

(* Continuations keep the original postcondition even when allocation
   grows the store typing used to type their next configuration. *)
Local Lemma omni_soundness_extends :
  forall mu t Y T Y0, extends Y0 Y ->
  Y |== mu -> empty ! Y |= t ~: T ->
  coomnibig (t, mu) (post Y0 T).
Proof.
  cofix CIH.
  intros mu t Y T Y0 Hext Hstore HT.
  assert (Hok : sto_ok mu) by exact (proj1 Hstore).
  inversion HT as
    [E Z x U _ Hx
    |L E Z U V b Hbody
    |U V E Z t1 t2 H1 H2
    |E Z _
    |E Z n _
    |E Z l U _ Hl
    |E Z t1 U H1
    |E Z t1 U H1
    |E Z t1 t2 U H1 H2
    |E Z t1 H1]; subst.
  - exfalso. eapply binds_empty_inv; eauto.
  - apply coomnibig_val.
    + simpl. eauto using value_abs, omni_typing_term.
    + eapply omni_post; eauto using value_abs, omni_typing_term.
  - destruct (classic (value t1)) as [Hv1 | Hnv1].
    + destruct (classic (value t2)) as [Hv2 | Hnv2].
      * destruct (omni_arrow_value H1 Hv1) as (b & -> & Hb).
        apply coomnibig_beta; try assumption.
        eapply CIH with (Y := Y); eauto using omni_typing_beta.
      * apply coomnibig_app_2 with (P1 := post Y U); try assumption.
        -- eapply CIH with (Y := Y); eauto using extends_refl.
        -- intros t2' mu' (Z & HYZ & Hstore' & _ & H2').
           eapply CIH with (Y := Z); eauto using omni_extends_trans.
           eapply typing_app; eauto using omni_typing_store_weaken.
    + apply coomnibig_app_1 with (P1 := post Y (typ_arrow U T)); try assumption.
      * eapply CIH with (Y := Y); eauto using extends_refl.
      * intros t1' mu' (Z & HYZ & Hstore' & _ & H1').
        eapply CIH with (Y := Z); eauto using omni_extends_trans.
        eapply typing_app; eauto using omni_typing_store_weaken.
  - apply coomnibig_val; simpl; eauto using value_unit, omni_post.
  - apply coomnibig_val; simpl; eauto using value_int, omni_post.
  - apply coomnibig_val; simpl; eauto using value_loc, omni_post.
  - destruct (classic (value t1)) as [Hv | Hnv].
    + apply coomnibig_ref; try assumption.
      intros l Hl.
      assert (HlY : l # Y) by exact (proj1 (proj2 Hstore) l Hl).
      apply omni_post with (Y := Y & l ~ U).
      * eapply omni_extends_trans; eauto using extends_push.
      * eauto using omni_store_alloc.
      * apply value_loc.
      * auto using typing_loc, binds_push_eq, ok_empty.
    + apply coomnibig_ref_1 with (P1 := post Y U); try assumption.
      * eapply CIH with (Y := Y); eauto using extends_refl.
      * intros t1' mu' (Z & HYZ & Hstore' & _ & H1').
        eapply CIH with (Y := Z); eauto using omni_extends_trans, typing_ref.
  - destruct (classic (value t1)) as [Hv | Hnv].
    + destruct (omni_ref_value H1 Hv) as (l & -> & Hl).
      destruct (proj2 (proj2 Hstore) _ _ Hl) as (v & Hval & Hbind & Htyp).
      eapply coomnibig_get; eauto using omni_post.
    + apply coomnibig_get_1 with (P1 := post Y (typ_ref T)).
      * eapply CIH with (Y := Y); eauto using extends_refl.
      * intros t1' mu' (Z & HYZ & Hstore' & _ & H1').
        eapply CIH with (Y := Z); eauto using omni_extends_trans, typing_get.
  - destruct (classic (value t1)) as [Hv1 | Hnv1].
    + destruct (classic (value t2)) as [Hv2 | Hnv2].
      * destruct (omni_ref_value H1 Hv1) as (l & -> & Hl).
        apply coomnibig_set; try assumption.
        eapply omni_post; eauto using omni_store_update, value_unit,
          typing_unit, ok_empty.
      * apply coomnibig_set_2 with (P1 := post Y U); try assumption.
        -- eapply CIH with (Y := Y); eauto using extends_refl.
        -- intros t2' mu' (Z & HYZ & Hstore' & _ & H2').
           eapply CIH with (Y := Z); eauto using omni_extends_trans.
           eapply typing_set; eauto using omni_typing_store_weaken.
    + apply coomnibig_set_1 with (P1 := post Y (typ_ref U)); try assumption.
      * eapply CIH with (Y := Y); eauto using extends_refl.
      * intros t1' mu' (Z & HYZ & Hstore' & _ & H1').
        eapply CIH with (Y := Z); eauto using omni_extends_trans.
        eapply typing_set; eauto using omni_typing_store_weaken.
  - destruct (classic (value t1)) as [Hv | Hnv].
    + destruct (omni_int_value H1 Hv) as [n ->].
      apply coomnibig_rand. intros m Hm.
      eapply omni_post; eauto using value_int, typing_int, ok_empty.
    + apply coomnibig_rand_1 with (P1 := post Y typ_int); try assumption.
      * eapply CIH with (Y := Y); eauto using extends_refl.
      * intros t1' mu' (Z & HYZ & Hstore' & _ & H1').
        eapply CIH with (Y := Z); eauto using omni_extends_trans, typing_rand.
Qed.

Theorem coomnibig_soundness_result : coomnibig_soundness.
Proof.
  intros mu t Y T Hstore HT.
  eapply omni_soundness_extends; eauto using extends_refl.
Qed.
