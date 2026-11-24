Set Implicit Arguments.

Require Import Definitions.

Require Import Stareat.

Require Import Misc.

From Stdlib Require Import Lia.

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

Local Lemma sk_fv_env_cons : forall x T (G : env),
    fv ((x,T) :: G) [=] singleton x `union` fv T `union` fv G.
Proof.
  intros. change
    (AtomSetImpl.add x (dom G) `union` (fv_values fv G `union` fv T)
      [=] singleton x `union` fv T `union` (dom G `union` fv_values fv G)).
  fsetdec.
Qed.

Local Lemma sk_dom_fv : forall (G : env), dom G [<=] fv G.
Proof.
  intros. change (dom G [<=] dom G `union` fv_values fv G). fsetdec.
Qed.

Local Lemma sk_fv_env_incl : forall (E G : env),
    incl E G -> fv E [<=] fv G.
Proof.
  assert (entry : forall x T (G : env), In (x,T) G ->
      singleton x `union` fv T [<=] fv G).
  { intros x T G. induction G as [|[y V] G IH]; simpl In; intros H.
    - contradiction.
    - pose proof (sk_fv_env_cons y V G).
      destruct H as [H | H].
      + inversion H; subst. fsetdec.
      + specialize (IH H). fsetdec. }
  induction E as [|[x T] E IH]; intros G H.
  - change (empty `union` empty [<=] fv G). fsetdec.
  - assert (tail : incl E G) by (intros b Hb; apply H; now right).
    pose proof (IH G tail).
    pose proof (entry x T G (H (x,T) (or_introl eq_refl))).
    pose proof (sk_fv_env_cons x T E). fsetdec.
Qed.

Local Lemma sk_incl_push : forall x T (E G : env),
    incl E G -> incl (x ~ T ++ E) (x ~ T ++ G).
Proof.
  intros x T E G H b [<- | Hb].
  - now left.
  - right. now apply H.
Qed.

Local Lemma sk_wf_uniq : forall (G : env), wf_env G -> uniq G.
Proof.
  intros G H. induction H.
  - constructor.
  - apply uniq_push; auto. pose proof (sk_dom_fv G). fsetdec.
Qed.

Local Definition sk_scoped (G : env) (T : typ) :=
  fv T [<=] dom G /\ lc T.

Local Lemma sk_wf_split : forall (P G : env) x T,
    wf_env (P ++ x ~ T ++ G) -> wf_env G /\ sk_scoped G T.
Proof.
  induction P as [|[y V] P IH]; simpl; intros G x T H; inversion H; subst.
  - split; auto. split; assumption.
  - apply (IH G x T). assumption.
Qed.

Local Lemma sk_scoped_bnd : forall G A B,
    sk_scoped G (typ_bnd A B) -> sk_scoped G A /\ sk_scoped G B.
Proof.
  intros G A B [Hfv Hlc]. change (fv A `union` fv B [<=] dom G) in Hfv.
  change (lc_typ_at 0 (typ_bnd A B)) in Hlc. inversion Hlc; subst.
  repeat split; try assumption; fsetdec.
Qed.

Local Lemma sk_scoped_all_arg : forall G A B,
    sk_scoped G (typ_all A B) -> sk_scoped G A.
Proof.
  intros G A B [Hfv Hlc]. change (fv A `union` fv B [<=] dom G) in Hfv.
  change (lc_typ_at 0 (typ_all A B)) in Hlc. inversion Hlc; subst.
  split; [fsetdec | assumption].
Qed.

Local Lemma sk_fv_open : forall T k x,
    fv (open_rec k x T) [<=] singleton x `union` fv T.
Proof.
  change (forall T k x, fv_typ (open_rec_typ k x T) [<=] singleton x `union` fv_typ T).
  induction T as [| |[i|y]|A IHA B IHB|A IHA B IHB]; intros k x; simpl.
  - fsetdec.
  - fsetdec.
  - destruct (k == i); simpl; fsetdec.
  - fsetdec.
  - specialize (IHA k x). specialize (IHB (S k) x).
    fsetdec.
  - specialize (IHA k x). specialize (IHB k x).
    fsetdec.
Qed.

Local Lemma sk_lc_open : forall T k x,
    lc_typ_at (S k) T -> lc_typ_at k (open_rec_typ k x T).
Proof.
  induction T as [| |[i|y]|A IHA B IHB|A IHA B IHB]; intros k x H;
    inversion H; subst; simpl.
  - constructor.
  - constructor.
  - unfold open_rec_avar. destruct (k == i) as [<- | Hneq];
      constructor; [constructor |].
    match goal with
    | H : lc_at _ (avar_b _) |- _ => inversion H; subst
    end.
    constructor. lia.
  - repeat constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Local Lemma sk_scoped_all_body : forall G A B x,
    sk_scoped G (typ_all A B) ->
    sk_scoped (x ~ A ++ G) (open x B).
Proof.
  intros G A B x [Hfv Hlc].
  change (fv A `union` fv B [<=] dom G) in Hfv.
  change (lc_typ_at 0 (typ_all A B)) in Hlc. inversion Hlc; subst.
  split.
  - pose proof (sk_fv_open B 0 x).
    pose proof (dom_cons typ x A G).
    change (fv (open x B) [<=] dom ((x,A) :: G)). fsetdec.
  - apply sk_lc_open. assumption.
Qed.

Local Lemma sk_scoped_bot : forall G, sk_scoped G typ_bot.
Proof.
  intros. split; [change (empty [<=] dom G); fsetdec | constructor].
Qed.

Local Lemma sk_scoped_top : forall G, sk_scoped G typ_top.
Proof.
  intros. split; [change (empty [<=] dom G); fsetdec | constructor].
Qed.

Local Lemma sk_scoped_bnd_intro : forall G A B,
    sk_scoped G A -> sk_scoped G B -> sk_scoped G (typ_bnd A B).
Proof.
  intros G A B [HA HAlc] [HB HBlc]. split.
  - change (fv A `union` fv B [<=] dom G). fsetdec.
  - constructor; assumption.
Qed.

Local Lemma sk_scoped_lookup : forall G x,
    sk_scoped G (typ_sel (avar_f x)) -> exists T, binds x T G.
Proof.
  intros G x [Hfv _]. change (singleton x [<=] dom G) in Hfv.
  assert (Hin : x `in` dom G) by fsetdec.
  clear Hfv. induction G as [|[y T] G IH].
  - simpl in Hin. fsetdec.
  - pose proof (dom_cons typ y T G).
    destruct (x == y) as [-> | Hneq].
    + exists T. now left.
    + assert (x `in` dom G) by fsetdec.
      destruct (IH H0) as [U HU]. exists U. now right.
Qed.

Local Lemma sk_binds_split : forall (G : env) x T,
    binds x T G -> exists P D, G = P ++ x ~ T ++ D.
Proof.
  intros G x T H. exact (in_split _ _ H).
Qed.

Local Lemma sk_binds_middle : forall (P D : env) x T,
    binds x T (P ++ x ~ T ++ D).
Proof.
  intros. apply binds_app_iff. right. now left.
Qed.

Local Lemma sk_incl_suffix : forall (P D : env), incl D (P ++ D).
Proof.
  intros. apply incl_appr, incl_refl.
Qed.

Local Lemma sk_wf_push : forall (G : env) x T,
    wf_env G -> sk_scoped G T ->
    x `notin` fv T `union` fv G -> wf_env (x ~ T ++ G).
Proof.
  intros G x T H [Hfv Hlc] Hfresh. now constructor.
Qed.

(* An extension can keep the original binder choices if its added names
   are covered by the freshness set. *)
Local Lemma sk_weaken : forall L G S U F, subtysk L G S U F ->
    forall E D, incl G E -> incl F D ->
    fv E [<=] fv G `union` L -> fv D [<=] fv F `union` L ->
    subtysk L E S U D.
Proof.
  intros L G S U F H.
  induction H as
      [L G F x | L G F T | L G F T
      | L G F S A B U Hlo IHlo Hhi IHhi
      | L G F A B U V x Hfresh Harg IHarg Hbody IHbody
      | L G F x T S Hbind Hbound IHbound
      | L G F x T U Hbind Hbound IHbound];
    intros E D Hleft Hright Hfvleft Hfvright.
  - apply ssk_refl.
  - apply ssk_top.
  - apply ssk_bot.
  - apply ssk_bnd; auto.
  - eapply ssk_all with (x := x).
    + fsetdec.
    + now apply IHarg.
    + apply IHbody; try (apply sk_incl_push; assumption).
      * change (fv ((x,A) :: E) [<=]
          fv ((x,A) :: G) `union` (L `union` (singleton x `union` fv B))).
        pose proof (sk_fv_env_cons x A E) as HconsE.
        pose proof (sk_fv_env_cons x A G) as HconsG.
        clear - HconsE HconsG Hfvleft. fsetdec.
      * change (fv ((x,B) :: D) [<=]
          fv ((x,B) :: F) `union` (L `union` (singleton x `union` fv B))).
        pose proof (sk_fv_env_cons x B D) as HconsD.
        pose proof (sk_fv_env_cons x B F) as HconsF.
        clear - HconsD HconsF Hfvright. fsetdec.
  - eapply ssk_sel1 with (T := T).
    + now apply Hright.
    + now apply IHbound.
  - eapply ssk_sel2 with (T := T).
    + now apply Hleft.
    + now apply IHbound.
Qed.

Local Lemma sk_weaken_left : forall L G S U F E,
    subtysk L G S U F -> incl G E -> fv E [<=] L ->
    subtysk L E S U F.
Proof.
  intros. eapply sk_weaken; try eassumption; try apply incl_refl; fsetdec.
Qed.

Local Lemma sk_weaken_right : forall L G S U F D,
    subtysk L G S U F -> incl F D -> fv D [<=] L ->
    subtysk L G S U D.
Proof.
  intros. eapply sk_weaken; try eassumption; try apply incl_refl; fsetdec.
Qed.

(* In a cast that returns top or bottom, the subsequent comparison
   may be reused after replacing that extreme by an arbitrary type. *)
Inductive sk_shape_sub : typ -> typ -> Prop :=
| sk_shape_refl : forall T, sk_shape_sub T T
| sk_shape_bot : forall T, sk_shape_sub typ_bot T
| sk_shape_top : forall T, sk_shape_sub T typ_top
| sk_shape_bnd : forall A B C D,
    sk_shape_sub C A -> sk_shape_sub B D ->
    sk_shape_sub (typ_bnd A B) (typ_bnd C D).

Local Lemma sk_shape_compat : forall L G S U F, subtysk L G S U F ->
    forall S' U', sk_shape_sub S' S -> sk_shape_sub U U' ->
    subtysk L G S' U' F.
Proof.
  intros L G S U F H.
  induction H as
      [L G F x | L G F T | L G F T
      | L G F S A B U Hlo IHlo Hhi IHhi
      | L G F A B U V x Hfresh Harg IHarg Hbody IHbody
      | L G F x T S Hbind Hbound IHbound
      | L G F x T U Hbind Hbound IHbound];
    intros S' U' Hleft Hright.
  - inversion Hleft; inversion Hright; subst;
      solve [apply ssk_bot | apply ssk_top | apply ssk_refl].
  - inversion Hright; subst; apply ssk_top.
  - inversion Hleft; subst; apply ssk_bot.
  - inversion Hleft; inversion Hright; subst; try apply ssk_top;
      try apply ssk_bot; apply ssk_bnd;
      (apply IHlo || apply IHhi); try assumption; apply sk_shape_refl.
  - inversion Hleft; inversion Hright; subst; try apply ssk_top;
      try apply ssk_bot; eapply ssk_all; eassumption.
  - inversion Hright; subst; [| apply ssk_top].
    eapply ssk_sel1; [eassumption |].
    apply IHbound; [apply sk_shape_refl |].
    apply sk_shape_bnd; [assumption | apply sk_shape_refl].
  - inversion Hleft; subst; [| apply ssk_bot].
    eapply ssk_sel2; [eassumption |].
    apply IHbound; [apply sk_shape_refl |].
    apply sk_shape_bnd; [apply sk_shape_refl | assumption].
Qed.

Local Lemma sk_revealing_incl : forall G T D V,
    revealing G T D V -> incl D G.
Proof.
  intros G T D V H. induction H.
  - apply incl_refl.
  - apply incl_nil_l.
  - apply incl_nil_l.
  - eapply incl_tran; [exact IHrevealing2 |].
    eapply incl_tran; [exact IHrevealing1 |].
    apply incl_appr, sk_incl_suffix.
Qed.

Local Lemma sk_revealing_scoped : forall G T D V,
    revealing G T D V -> wf_env G -> sk_scoped G T ->
    wf_env D /\ sk_scoped D V.
Proof.
  intros G T D V H. induction H; intros Hwf Hscope.
  - auto.
  - split; [constructor | apply sk_scoped_top].
  - split; [constructor | apply sk_scoped_bot].
  - destruct (sk_wf_split G2 G1 x T Hwf) as [Hw HT].
    destruct (IHrevealing1 Hw HT) as [Hw' HB].
    destruct (sk_scoped_bnd HB) as [_ HU].
    now apply IHrevealing2.
Qed.

Local Lemma sk_reveal_bnd : forall L G T A B F,
    stareat L G T (typ_bnd A B) F ->
    (exists D, revealing G T D typ_bot) \/
    (exists D C E, revealing G T D (typ_bnd C E) /\
       stareat L F A C D /\ stareat L D E B F).
Proof.
  intros L G T A B F H. remember (typ_bnd A B) as V eqn:HV.
  induction H as
      [L G T F | L G T F | L G x F
      | L G x F T V D Hcast Hsub IH
      | L G x F T U D Hcast Hsub IH
      | L G A' B' F C E x Hfresh Harg IHarg Hbody IHbody
      | L G A' B' C E F Hlo IHlo Hhi IHhi];
    try discriminate HV.
  - left. exists G. apply rv_stop. simpl. tauto.
  - specialize (IH HV). inversion Hcast; subst.
    + inversion Hsub.
    + left. exists nil. eapply rv_bot. eassumption.
    + destruct IH as [[D' Hr] | [D' [C [E [Hr [Hlo Hhi]]]]]].
      * left. exists D'. eapply rv_bnd; eassumption.
      * right. exists D', C, E. repeat split; try assumption.
        eapply rv_bnd; eassumption.
  - inversion HV; subst. right. exists G, A', B'. repeat split; try assumption.
    apply rv_stop. simpl. tauto.
Qed.

Local Lemma sk_binding_scope : forall (E G : env) x T,
    incl E G -> uniq G -> wf_env E ->
    sk_scoped E (typ_sel (avar_f x)) -> binds x T G ->
    exists P D, E = P ++ x ~ T ++ D /\
      incl D G /\ wf_env D /\ sk_scoped D T.
Proof.
  intros E G x T Hincl Huniq Hwf Hscope Hbind.
  destruct (sk_scoped_lookup Hscope) as [V HV].
  assert (V = T) by (eapply binds_unique; [exact (Hincl _ HV) | exact Hbind | exact Huniq]).
  subst V.
  destruct (sk_binds_split E x T HV) as [P [D ->]].
  exists P, D. split; [reflexivity |]. split.
  - eapply incl_tran; [apply incl_appr, sk_incl_suffix | exact Hincl].
  - exact (sk_wf_split P D x T Hwf).
Qed.

(* Selection is checked in the suffix defining the selected variable.
   The smaller environments let the induction hypothesis make that move. *)
Local Lemma sk_complete : forall L G S U F, subtysk L G S U F ->
    forall K E D, K [<=] L -> incl E G -> incl D F ->
    uniq G -> uniq F -> wf_env E -> wf_env D ->
    sk_scoped E S -> sk_scoped D U ->
    stareat K E S U D.
Proof.
  intros L G S U F H.
  induction H as
      [L G F x | L G F T | L G F T
      | L G F S A B U Hlo IHlo Hhi IHhi
      | L G F A B U V x Hfresh Harg IHarg Hbody IHbody
      | L G F x T S Hbind Hbound IHbound
      | L G F x T U Hbind Hbound IHbound];
    intros K E D HK HE HD HuniqG HuniqF HwfE HwfD HscopeE HscopeD.
  - apply sa_sel_refl.
  - apply sa_top.
  - apply sa_bot.
  - destruct (sk_scoped_bnd HscopeE) as [HA HB].
    destruct (sk_scoped_bnd HscopeD) as [HS HU].
    apply sa_bnd; auto.
  - pose proof (sk_fv_env_incl HE) as HfvE.
    pose proof (sk_fv_env_incl HD) as HfvD.
    pose proof (sk_dom_fv G) as HG.
    pose proof (sk_dom_fv F) as HF.
    pose proof (sk_scoped_all_arg HscopeE) as HA.
    pose proof (sk_scoped_all_arg HscopeD) as HB.
    eapply sa_all with (x := x).
    + fsetdec.
    + now apply IHarg.
    + apply IHbody.
      * clear - HK. fsetdec.
      * now apply sk_incl_push.
      * now apply sk_incl_push.
      * apply uniq_push; [assumption |]. clear - Hfresh HG. fsetdec.
      * apply uniq_push; [assumption |]. clear - Hfresh HF. fsetdec.
      * apply sk_wf_push; try assumption. clear - Hfresh HfvE. fsetdec.
      * apply sk_wf_push; try assumption. clear - Hfresh HfvD. fsetdec.
      * now apply sk_scoped_all_body.
      * now apply sk_scoped_all_body.
  - destruct (@sk_binding_scope D F x T HD HuniqF HwfD HscopeD Hbind)
      as [P [D' [-> [HD' [HwfD' HT]]]]].
    assert (Hsub : stareat K D' T (typ_bnd S typ_top) E).
    { apply IHbound; eauto using sk_scoped_bnd_intro, sk_scoped_top. }
    destruct (sk_reveal_bnd Hsub) as [[J Hr] | [J [A [B [Hr [Hlo Hhi]]]]]].
    + eapply sa_sel_right; [eapply dc_top; exact Hr | apply sa_top].
    + eapply sa_sel_right; [eapply dc_bnd; exact Hr | exact Hlo].
  - destruct (@sk_binding_scope E G x T HE HuniqG HwfE HscopeE Hbind)
      as [P [E' [-> [HE' [HwfE' HT]]]]].
    assert (Hsub : stareat K E' T (typ_bnd typ_bot U) D).
    { apply IHbound; eauto using sk_scoped_bnd_intro, sk_scoped_bot. }
    destruct (sk_reveal_bnd Hsub) as [[J Hr] | [J [A [B [Hr [Hlo Hhi]]]]]].
    + eapply sa_sel_left; [eapply uc_bot; exact Hr | apply sa_bot].
    + eapply sa_sel_left; [eapply uc_bnd; exact Hr | exact Hhi].
Qed.

Local Lemma sk_upcast_scope : forall G x D V,
    upcast G x D V -> wf_env G -> wf_env D /\ sk_scoped D V.
Proof.
  intros G x D V Hcast Hwf. destruct Hcast.
  - split; [constructor | apply sk_scoped_top].
  - split; [constructor | apply sk_scoped_bot].
  - destruct (sk_wf_split G2 G1 x T Hwf) as [Hw HT].
    destruct (sk_revealing_scoped H Hw HT) as [Hw' HB].
    split; [exact Hw' | exact (proj2 (sk_scoped_bnd HB))].
Qed.

Local Lemma sk_downcast_scope : forall G x D V,
    downcast G x D V -> wf_env G -> wf_env D /\ sk_scoped D V.
Proof.
  intros G x D V Hcast Hwf. destruct Hcast.
  - split; [constructor | apply sk_scoped_bot].
  - split; [constructor | apply sk_scoped_top].
  - destruct (sk_wf_split G2 G1 x T Hwf) as [Hw HT].
    destruct (sk_revealing_scoped H Hw HT) as [Hw' HB].
    split; [exact Hw' | exact (proj1 (sk_scoped_bnd HB))].
Qed.

Local Lemma sk_upcast_incl : forall G x D V, upcast G x D V -> incl D G.
Proof.
  intros G x D V H. destruct H.
  - apply incl_nil_l.
  - apply incl_nil_l.
  - eapply incl_tran; [eapply sk_revealing_incl; eassumption |].
    apply incl_appr, sk_incl_suffix.
Qed.

Local Lemma sk_downcast_incl : forall G x D V, downcast G x D V -> incl D G.
Proof.
  intros G x D V H. destruct H.
  - apply incl_nil_l.
  - apply incl_nil_l.
  - eapply incl_tran; [eapply sk_revealing_incl; eassumption |].
    apply incl_appr, sk_incl_suffix.
Qed.

(* Lift the comparison from the revealed type back to its original type. *)
Local Lemma sk_revealing_left : forall G T D V, revealing G T D V ->
    forall L E F U, incl G E -> fv E [<=] L ->
    subtysk L D V U F -> subtysk L E T U F.
Proof.
  intros G T D V H.
  induction H as
      [G T Hstop | G T
      | G P D T x Hr IHr
      | G P T D J x A B V Hr IHr Hv IHv];
    intros L E F U HE Hfv Hsub.
  - eapply sk_weaken_left; eassumption.
  - eapply sk_weaken_left; [| apply incl_nil_l | exact Hfv].
    eapply sk_shape_compat; [exact Hsub | apply sk_shape_top | apply sk_shape_refl].
  - eapply ssk_sel2 with (T := T).
    + apply HE. apply sk_binds_middle.
    + apply IHr; [| exact Hfv | apply ssk_bot].
      eapply incl_tran; [apply incl_appr, sk_incl_suffix | exact HE].
  - assert (HG : incl G E).
    { eapply incl_tran; [apply incl_appr, sk_incl_suffix | exact HE]. }
    assert (HD : fv D [<=] L).
    { pose proof (sk_fv_env_incl (sk_revealing_incl Hr)).
      pose proof (sk_fv_env_incl HG). fsetdec. }
    eapply ssk_sel2 with (T := T).
    + apply HE. apply sk_binds_middle.
    + apply IHr; [exact HG | exact Hfv |].
      apply ssk_bnd.
      * apply ssk_bot.
      * apply IHv; [apply incl_refl | exact HD | exact Hsub].
Qed.

Local Lemma sk_upcast_left : forall G x D V, upcast G x D V ->
    forall L U F, fv G [<=] L ->
    subtysk L D V U F -> subtysk L G (typ_sel x) U F.
Proof.
  intros G x D V H. destruct H; intros K U' F Hfv Hsub.
  - eapply sk_weaken_left; [| apply incl_nil_l | exact Hfv].
    eapply sk_shape_compat; [exact Hsub | apply sk_shape_top | apply sk_shape_refl].
  - eapply ssk_sel2 with (T := T); [apply sk_binds_middle |].
    eapply sk_revealing_left; [eassumption | apply incl_appr, sk_incl_suffix
                            | exact Hfv | apply ssk_bot].
  - eapply ssk_sel2 with (T := T); [apply sk_binds_middle |].
    eapply sk_revealing_left; [eassumption | apply incl_appr, sk_incl_suffix
                            | exact Hfv |].
    apply ssk_bnd; [apply ssk_bot | exact Hsub].
Qed.

Local Lemma sk_downcast_right : forall G x D V, downcast G x D V ->
    forall L S E, fv G [<=] L ->
    subtysk L E S V D -> subtysk L E S (typ_sel x) G.
Proof.
  intros G x D V H. destruct H; intros K S E Hfv Hsub.
  - eapply sk_weaken_right; [| apply incl_nil_l | exact Hfv].
    eapply sk_shape_compat; [exact Hsub | apply sk_shape_refl | apply sk_shape_bot].
  - eapply ssk_sel1 with (T := T); [apply sk_binds_middle |].
    eapply sk_revealing_left; [eassumption | apply incl_appr, sk_incl_suffix
                            | exact Hfv | apply ssk_bot].
  - eapply ssk_sel1 with (T := T); [apply sk_binds_middle |].
    eapply sk_revealing_left; [eassumption | apply incl_appr, sk_incl_suffix
                            | exact Hfv |].
    apply ssk_bnd; [exact Hsub | apply ssk_top].
Qed.

Local Lemma sk_sound : forall L G S U F, stareat L G S U F ->
    forall K, K [<=] L -> fv G [<=] K -> fv F [<=] K ->
    wf_env G -> wf_env F -> sk_scoped G S -> sk_scoped F U ->
    subtysk K G S U F.
Proof.
  intros L G S U F H.
  induction H as
      [L G T F | L G T F | L G x F
      | L G x F T U D Hcast Hsub IH
      | L G x F T U D Hcast Hsub IH
      | L G A U F B V x Hfresh Harg IHarg Hbody IHbody
      | L G A B C E F Hlo IHlo Hhi IHhi];
    intros K HK HfvG HfvF HwfG HwfF HscopeG HscopeF.
  - apply ssk_bot.
  - apply ssk_top.
  - apply ssk_refl.
  - destruct (sk_upcast_scope Hcast HwfG) as [Hw HT].
    pose proof (sk_fv_env_incl (sk_upcast_incl Hcast)) as HfvD.
    eapply sk_upcast_left; [exact Hcast | exact HfvG |].
    apply IH; try assumption. fsetdec.
  - destruct (sk_downcast_scope Hcast HwfF) as [Hw HU].
    pose proof (sk_fv_env_incl (sk_downcast_incl Hcast)) as HfvD.
    eapply sk_downcast_right; [exact Hcast | exact HfvF |].
    apply IH; try assumption. fsetdec.
  - pose proof (sk_scoped_all_arg HscopeG) as HA.
    pose proof (sk_scoped_all_arg HscopeF) as HB.
    pose proof (proj1 HA) as HfvA.
    pose proof (sk_dom_fv G) as HG.
    eapply ssk_all with (x := x).
    + fsetdec.
    + now apply IHarg.
    + apply IHbody.
      * clear - HK. fsetdec.
      * pose proof (sk_fv_env_cons x A G) as Hcons.
        change (fv ((x,A) :: G) [<=] K `union` (singleton x `union` fv B)).
        clear - HfvG HfvA HG Hcons. fsetdec.
      * pose proof (sk_fv_env_cons x B F) as Hcons.
        change (fv ((x,B) :: F) [<=] K `union` (singleton x `union` fv B)).
        clear - HfvF Hcons. fsetdec.
      * apply sk_wf_push; try assumption. clear - Hfresh. fsetdec.
      * apply sk_wf_push; try assumption. clear - Hfresh. fsetdec.
      * now apply sk_scoped_all_body.
      * now apply sk_scoped_all_body.
  - destruct (sk_scoped_bnd HscopeG) as [HA HB].
    destruct (sk_scoped_bnd HscopeF) as [HC HE].
    apply ssk_bnd; auto.
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
  intros L G1 S U G2 Hw1 Hw2 HfvS HlcS HfvU HlcU.
  split; intro H.
  - eapply sk_complete; [exact H | fsetdec | apply incl_refl | apply incl_refl
                        | now apply sk_wf_uniq | now apply sk_wf_uniq
                        | exact Hw1 | exact Hw2 | now split | now split].
  - eapply sk_sound; [exact H | fsetdec | fsetdec | fsetdec
                     | exact Hw1 | exact Hw2 | now split | now split].
Qed.
