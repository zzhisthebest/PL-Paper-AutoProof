From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
From AutoProof Require Import Smallstep.
From AutoProof.STLCRecursion Require Import Syntax StlcProp Infrastructure.
Import ListNotations.
Module STLCRecNorm.
Import STLCRec STLCRecProp STLCRecInfrastructure.

Definition halts (t : tm) : Prop :=
  exists v, t -->* v /\ value v.

Lemma multi_trans : forall t u v,
  t -->* u ->
  u -->* v ->
  t -->* v.
Proof.
  intros t u v Htu Huv.
  induction Htu.
  - exact Huv.
  - eapply multi_step; eauto.
Qed.

Lemma multi_app1 : forall t1 t1' t2,
  t1 -->* t1' ->
  locally_closed t2 ->
  tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 Hs Ht2.
  induction Hs.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App1; eauto.
    + exact IHHs.
Qed.

Lemma multi_app2 : forall v1 t2 t2',
  value v1 ->
  t2 -->* t2' ->
  tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros v1 t2 t2' Hv Hs.
  induction Hs.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2; eauto.
    + exact IHHs.
Qed.

Fixpoint value_relation (T : ty) (v : tm) : Prop :=
  value v /\
  match T with
  | Ty_Nat => numeric_value v
  | Ty_Bool =>
      v = tm_true \/ v = tm_false
  | Ty_Arrow T1 T2 =>
      exists body,
        v = tm_abs T1 body /\
        forall arg,
          value_relation T1 arg ->
          locally_closed (open body arg) /\
          exists v',
            open body arg -->* v' /\
            value_relation T2 v'
  end.

Definition expression_relation (T : ty) (t : tm) : Prop :=
  locally_closed t /\
  exists v,
    t -->* v /\
    value_relation T v.

Definition related_substitution
    (Gamma : context) (rho : term_substitution) : Prop :=
  forall x T, Gamma x = Some T -> value_relation T (rho x).

Lemma value_relation_value : forall T v,
  value_relation T v -> value v.
Proof.
  intros T v H. destruct T; simpl in H; tauto.
Qed.

Lemma value_relation_term : forall T v,
  value_relation T v -> locally_closed v.
Proof.
  intros T v H.
  apply value_regular.
  apply value_relation_value with (T := T).
  exact H.
Qed.

Lemma expression_relation_halts : forall T t,
  expression_relation T t ->
  halts t.
Proof.
  intros T t [_ [v [Hs HV]]].
  exists v. split.
  - exact Hs.
  - apply value_relation_value with (T := T). exact HV.
Qed.

Lemma related_update : forall Gamma rho x T v,
  related_substitution Gamma rho ->
  value_relation T v ->
  related_substitution (update Gamma x T) (subst_update rho x v).
Proof.
  unfold related_substitution, subst_update, update.
  intros Gamma rho x T v Hrel HV y U Hy.
  destruct (Nat.eqb x y) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst y.
    injection Hy as ->. exact HV.
  - apply Hrel. exact Hy.
Qed.

Lemma empty_related :
  related_substitution empty id_substitution.
Proof.
  unfold related_substitution, empty.
  intros. discriminate H.
Qed.

Lemma value_is_expression : forall T v,
  value_relation T v -> expression_relation T v.
Proof.
  intros T v HV. split.
  - eapply value_relation_term. exact HV.
  - exists v. split.
    + apply multi_refl.
    + exact HV.
Qed.

Lemma expression_expansion : forall T t u,
  locally_closed t ->
  t -->* u ->
  expression_relation T u ->
  expression_relation T t.
Proof.
  intros T t u Hlc Hsteps [_ [v [Hs HV]]].
  split. exact Hlc.
  exists v. split.
  - eapply multi_trans; eauto.
  - exact HV.
Qed.

Lemma expression_app : forall T1 T2 t1 t2,
  expression_relation (Ty_Arrow T1 T2) t1 ->
  expression_relation T1 t2 ->
  expression_relation T2 (tm_app t1 t2).
Proof.
  intros T1 T2 t1 t2 [Ht1 [vf [Hs1 HVf]]] [Ht2 [va [Hs2 HVa]]].
  destruct HVf as [HVf_value [body [Heq Hbody]]]. subst vf.
  assert (Hfun_lc : locally_closed (tm_abs T1 body)).
  { apply value_regular. exact HVf_value. }
  destruct (Hbody va HVa) as [Hbody_lc [vr [Hsbody HVr]]].
  split.
  - apply lc_app; assumption.
  - exists vr. split.
    + eapply multi_trans.
      * apply multi_app1; eauto.
      * eapply multi_trans.
        -- apply multi_app2; eauto.
        -- eapply multi_step.
           ++ apply ST_AppAbs. exact Hfun_lc.
              eapply value_relation_value. exact HVa.
           ++ exact Hsbody.
    + exact HVr.
Qed.

Lemma numeral_relation : forall n,
  value_relation Ty_Nat (numeral n).
Proof.
  intros n. simpl. split.
  - apply v_nat. apply numeral_numeric.
  - apply numeral_numeric.
Qed.

Lemma multi_succ : forall t u,
  t -->* u -> tm_succ t -->* tm_succ u.
Proof.
  intros t u H. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_Succ. exact H.
    + exact IHmulti.
Qed.

Lemma expression_succ : forall t,
  expression_relation Ty_Nat t ->
  expression_relation Ty_Nat (tm_succ t).
Proof.
  intros t [Hlc [v [Hs [Hv Hnum]]]].
  split. apply lc_succ. exact Hlc.
  exists (tm_succ v). split.
  - apply multi_succ. exact Hs.
  - simpl. split.
    + apply v_nat. apply nv_succ. exact Hnum.
    + apply nv_succ. exact Hnum.
Qed.

Lemma multi_rec_arg : forall n n' b s,
  n -->* n' -> locally_closed b -> locally_closed s ->
  tm_natrec n b s -->* tm_natrec n' b s.
Proof.
  intros n n' b s H Hb Hs. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_RecArg; eassumption.
    + exact IHmulti.
Qed.

Lemma multi_rec_base : forall n b b' s,
  numeric_value n -> b -->* b' -> locally_closed s ->
  tm_natrec n b s -->* tm_natrec n b' s.
Proof.
  intros n b b' s Hn H Hs. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_RecBase; eassumption.
    + exact IHmulti.
Qed.

Lemma multi_rec_step : forall n b s s',
  numeric_value n -> value b -> s -->* s' ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof.
  intros n b s s' Hn Hb H. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_RecStep; eassumption.
    + exact IHmulti.
Qed.

(* 如果 n 是 Ty_Nat 类型的好值，b 是 T 类型的好值，s 是 Nat -> T -> T 类型的好值，
   那么 tm_natrec n b s 就是 T 类型的好程序。 *)
Lemma expression_rec_numeral : forall T n b s,
  value_relation Ty_Nat n ->
  value_relation T b ->
  value_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s [_ Hnum] Hb Hs.
  destruct (numeric_numeral n Hnum) as [k ->].
  clear Hnum.
  revert T b s Hb Hs.
  induction k as [|n IH]; intros T b s Hb Hs.
  - eapply expression_expansion with (u := b).
    + apply lc_rec.
      * apply lc_zero.
      * eapply value_relation_term. exact Hb.
      * eapply value_relation_term. exact Hs.
    + eapply multi_step.
      * apply ST_RecZero; eapply value_relation_value; eassumption.
      * apply multi_refl.
    + apply value_is_expression. exact Hb.
  - eapply expression_expansion with
      (u := tm_app (tm_app s (numeral n)) (tm_natrec (numeral n) b s)).
    + apply lc_rec.
      * apply numeric_value_lc. apply numeral_numeric.
      * eapply value_relation_term. exact Hb.
      * eapply value_relation_term. exact Hs.
    + eapply multi_step.
      * apply ST_RecSucc.
        -- apply numeral_numeric.
        -- eapply value_relation_value. exact Hb.
        -- eapply value_relation_value. exact Hs.
      * apply multi_refl.
    + apply expression_app with (T1 := T).
      * apply expression_app with (T1 := Ty_Nat).
        -- apply value_is_expression. exact Hs.
        -- apply value_is_expression. apply numeral_relation.
      * apply IH; assumption.
Qed.
(* 如果 n 是 Ty_Nat 类型的好程序，b 是 T 类型的好程序，s 是 Nat -> T -> T 类型的好程序，
   那么 tm_natrec n b s 就是 T 类型的好程序。 *)
Lemma expression_rec : forall T n b s,
  expression_relation Ty_Nat n ->
  expression_relation T b ->
  expression_relation (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  expression_relation T (tm_natrec n b s).
Proof.
  intros T n b s [Hn [vn [Hsn [Hvn Hnum]]]]
    [Hb [vb [Hsb HVb]]] [Hs [vs [Hss HVs]]].
  eapply expression_expansion with (u := tm_natrec vn vb vs).
  - apply lc_rec; assumption.
  - eapply multi_trans.
    + apply multi_rec_arg; eassumption.
    + eapply multi_trans.
      * apply multi_rec_base; eassumption.
      * apply multi_rec_step.
        -- exact Hnum.
        -- eapply value_relation_value. exact HVb.
        -- exact Hss.
  - apply expression_rec_numeral.
    + split; assumption.
    + exact HVb.
    + exact HVs.
Qed.

Theorem fundamental : forall Gamma t T,
  <{ Gamma |-- t \in T }> ->
  forall rho,
    proper_substitution rho ->
    related_substitution Gamma rho ->
    expression_relation T (msubst rho t).
Proof.
  intros Gamma t T Htyping.
  induction Htyping; intros rho Hproper Hrel.
  - apply value_is_expression.
    apply Hrel with (x := x). exact H.
  - assert (Habs_lc : locally_closed (msubst rho (tm_abs T1 t1))).
    {
      apply msubst_preserves_term.
      - exact Hproper.
      - apply typing_regular with (Gamma := Gamma) (T := Ty_Arrow T1 T2).
        apply T_Abs with (L := L). exact H.
    }
    apply value_is_expression. simpl. split.
    + apply v_abs. exact Habs_lc.
    + exists (msubst rho t1). split.
      * reflexivity.
      * intros arg HVarg.
        pose (x := fresh (L ++ free_vars t1)).
        assert (HxL : ~ In x L).
        {
          intro Hin. unfold x in Hin.
          apply (fresh_notin (L ++ free_vars t1)).
          apply in_or_app. left. exact Hin.
        }
        assert (Hxfv : ~ In x (free_vars t1)).
        {
          intro Hin. unfold x in Hin.
          apply (fresh_notin (L ++ free_vars t1)).
          apply in_or_app. right. exact Hin.
        }
        assert (Harg_lc : locally_closed arg).
        { eapply value_relation_term. exact HVarg. }
        specialize (H0 x HxL (subst_update rho x arg)).
        specialize (H0 (proper_update rho x arg Hproper Harg_lc)).
        specialize (H0 (related_update Gamma rho x T1 arg Hrel HVarg)).
        rewrite (msubst_open_update t1 rho x arg Hxfv Hproper Harg_lc) in H0.
        exact H0.
  - apply expression_app with (T1 := T1).
    + apply IHHtyping1; assumption.
    + apply IHHtyping2; assumption.
  - apply value_is_expression. simpl. split.
    + apply v_true.
    + left. reflexivity.
  - apply value_is_expression. simpl. split.
    + apply v_false.
    + right. reflexivity.
  - apply value_is_expression. apply (numeral_relation 0).
  - apply expression_succ. apply IHHtyping; assumption.
  - apply expression_rec.
    + apply IHHtyping1; assumption.
    + apply IHHtyping2; assumption.
    + apply IHHtyping3; assumption.
Qed.

Theorem evaluation_terminates : forall t T,
  <{ empty |-- t \in T }> -> halts t.
Proof.
  intros t T HT.
  pose proof (fundamental empty t T HT id_substitution
    id_substitution_proper empty_related) as Hrel.
  rewrite msubst_id in Hrel.
  apply expression_relation_halts with (T := T). exact Hrel.
Qed.

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall t', t --> t' -> strongly_normalizing t') ->
      strongly_normalizing t.

Lemma halts_strongly_normalizing : forall t,
  halts t -> strongly_normalizing t.
Proof.
  intros t [v [Hsteps Hv]].
  induction Hsteps as [v | t u v Htu Huv IH].
  - apply SN_intro. intros t' Hstep.
    exfalso. exact (value_no_step v Hv t' Hstep).
  - apply SN_intro. intros t' Hstep.
    assert (Heq : t' = u).
    { eapply step_deterministic; eassumption. }
    subst t'. apply IH. exact Hv.
Qed.

Theorem normalization : forall t T,
  <{ empty |-- t \in T }> -> strongly_normalizing t.
Proof.
  intros t T HT.
  apply halts_strongly_normalizing.
  apply evaluation_terminates with (T := T). exact HT.
Qed.

End STLCRecNorm.
