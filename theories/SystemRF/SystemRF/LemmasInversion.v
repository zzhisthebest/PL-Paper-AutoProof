Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.SystemRF.LemmasTyping.
Require Import AutoProof.SystemRF.SystemRF.LemmasNarrowing.
Require Import AutoProof.SystemRF.SystemRF.LemmasTransitive. 

(* -- A collection of Lemmas about inverting typing judgements for abstraction types. In our
   --   system this is not trivial because T_Sub could be used finitely many times to produce
   --   the judgment. The key point is to use transitivity of subtyping to collapse a chain
   --   of applications of T-Sub to a single use of T-Sub *)

Lemma lem_invert_lambda : forall (g:env) (le:expr) (t:type),
  Hastype g le t -> (forall (e : expr) (s_x s : type),
    le = Lambda e -> WFEnv g -> Subtype g t (TFunc s_x s)
                  -> WFtype g (TFunc s_x s) Star
                  -> exists nms, forall (y:var_name), (~ In y nms 
                      -> Hastype (Cons y s_x g) (unbind y e) (unbindT y s))).
Proof. apply ( Hastype_ind
    ( fun (g:env) (le:expr) (t:type) => forall (e : expr) (s_x s : type),
        le = Lambda e -> WFEnv g -> Subtype g t (TFunc s_x s) 
                      -> WFtype g (TFunc s_x s) Star
                      -> exists nms, forall (y:var_name), (~ In y nms 
                          -> Hastype (Cons y s_x g) (unbind y e) (unbindT y s)))
  ); try discriminate; intros.
  - (* isTAbs *) inversion H4; injection H2 as H2; subst;   (* invert SFunc *)
    inversion H5; try inversion H2;                             (* invert WFFunc *)
    exists (union (union (union nms nms0) nms1) (binds g)); intros.
    apply not_elem_union_elim in H13 as [Hfresh012 Hfresh_g].
    apply not_elem_union_elim in Hfresh012 as [Hfresh01 Hfresh_1].
    apply not_elem_union_elim in Hfresh01 as [Hfresh Hfresh_0].
    eapply T_Sub with (T1 := unbindT y T2) (k := k0).
    + eapply lem_narrow_typ_top with
        (t_x := T1) (k_sx := k_x) (k_tx := k).
      * apply H0. exact Hfresh.
      * apply wfenv_unique. exact H3.
      * exact Hfresh_g.
      * exact H8.
      * exact H.
      * exact H10.
      * exact H3.
    + apply H9. exact Hfresh_1.
    + apply H12. exact Hfresh_0.
  - (* isTSub *)
    apply H0; try assumption.
    eapply lem_sub_trans with
      (t' := T2) (k := Star) (k' := k) (k'' := Star).
    + exact H4.
    + eapply lem_typing_wf; eassumption.
    + exact H1.
    + exact H6.
    + exact H2.
    + exact H5.
  Qed.

Lemma lem_invert_tabs : forall (g:env) (e:expr) (t_x t:type),
    Hastype g (Lambda e) (TFunc t_x t) 
                  -> WFEnv g -> WFtype g (TFunc t_x t) Star
                  -> exists nms, forall (y:var_name), (~ In y nms 
                          -> Hastype (Cons y t_x g) (unbind y e) (unbindT y t)).
Proof. intros; inversion H.
  - (* isTAbs *) exists nms; apply H7.
  - (* isTSub *)
    eapply (lem_invert_lambda g (Lambda e) T1 H2 e t_x t).
    + reflexivity.
    + exact H0.
    + exact H4.
    + exact H1.
  Qed.

Lemma lem_invert_lambdat : forall (g:env) (lke:expr) (t:type),
    Hastype g lke t -> ( forall (k:kind) (e:expr) (s:type),
        lke = LambdaT k e -> WFEnv g -> Subtype g t (TPoly k s)
                          -> WFtype g (TPoly k s) Star
                          -> exists nms, forall (a:var_name), ( ~ In a nms 
                                -> Hastype (ConsT a k g) (unbind_tv a e) (unbind_tvT a s))).
Proof. apply ( Hastype_ind
    ( fun (g:env) (lke:expr) (t:type) => forall (k:kind) (e:expr) (s:type),
        lke = LambdaT k e -> WFEnv g -> Subtype g t (TPoly k s)
                          -> WFtype g (TPoly k s) Star
                          -> exists nms, forall (a:var_name), ( ~ In a nms 
                               -> Hastype (ConsT a k g) (unbind_tv a e) (unbind_tvT a s)))  
  ); try discriminate; intros.
  - (* isTAbsT *) inversion (* of SPoly *) H3; injection H1 as H1 H1'; subst;
    inversion (* of WFPoly *) H4; try inversion H1; subst;
    exists (union (union (union nms nms0) nms1) (binds g));
    intros a Hfresh_all.
    apply not_elem_union_elim in Hfresh_all as [Hfresh012 Hfresh_g].
    apply not_elem_union_elim in Hfresh012 as [Hfresh01 Hfresh_1].
    apply not_elem_union_elim in Hfresh01 as [Hfresh Hfresh_0].
    eapply T_Sub with (T1 := unbind_tvT a T) (k := k_t).
    + apply H. exact Hfresh.
    + apply H6. exact Hfresh_1.
    + apply H7. exact Hfresh_0.
  - (* isTSub *)
    apply H0; try assumption.
    eapply lem_sub_trans with
      (t' := T2) (k := Star) (k' := k) (k'' := Star).
    + exact H4.
    + eapply lem_typing_wf; eassumption.
    + exact H1.
    + exact H6.
    + exact H2.
    + exact H5.
  Qed.

Lemma lem_invert_tabst : forall (g:env) (k:kind) (e:expr) (t:type),
    Hastype g (LambdaT k e) (TPoly k t) 
                  -> WFEnv g -> WFtype g (TPoly k t) Star
                  -> exists nms, forall (a:var_name), (~ In a nms 
                          -> Hastype (ConsT a k g) (unbind_tv a e) (unbind_tvT a t)).
Proof. intros; inversion H.
  - (* isTAbs *) exists nms; assumption.
  - (* isTSub *)
    eapply (lem_invert_lambdat g (LambdaT k e) T1 H2 k e t).
    + reflexivity.
    + exact H0.
    + exact H4.
    + exact H1.
  Qed.

Lemma lem_lambdaT_tpoly_same_kind' : forall (g:env) (lke:expr) (t:type),
    Hastype g lke t -> ( forall (k k':kind) (e:expr) (s:type),
        lke = LambdaT k e -> WFEnv g -> Subtype g t (TPoly k' s)
                          -> WFtype g (TPoly k' s) Star
                          -> k = k').
Proof. apply ( Hastype_ind
    ( fun (g:env) (lke:expr) (t:type) => forall (k k':kind) (e:expr) (s:type),
        lke = LambdaT k e -> WFEnv g -> Subtype g t (TPoly k' s)
                          -> WFtype g (TPoly k' s) Star
                          -> k = k') 
  ); try discriminate; intros.
  - (* isTAbsT *) inversion H3; injection H1 as Hk0 He0; subst k0; assumption.
  - (* isTSub *)
    eapply H0 with (e := e) (s := s).
    + exact H3.
    + exact H4.
    + eapply lem_sub_trans with
        (t' := T2) (k := Star) (k' := k) (k'' := Star).
      * exact H4.
      * eapply lem_typing_wf; eassumption.
      * exact H1.
      * exact H6.
      * exact H2.
      * exact H5.
    + exact H6.
  Qed.

Lemma lem_lambdaT_tpoly_same_kind : forall (g:env) (k k':kind) (e:expr) (t:type),
    Hastype g (LambdaT k e) (TPoly k' t) -> WFEnv g -> WFtype g (TPoly k' t) Star  
                                        -> k = k'.
Proof. intros; inversion H.
  - (* isTAbsT *) reflexivity.
  - (* isTSub  *)
    eapply (lem_lambdaT_tpoly_same_kind'
      g (LambdaT k e) T1 H2 k k' e t).
    + reflexivity.
    + exact H0.
    + exact H4.
    + exact H1.
  Qed.
