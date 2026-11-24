Require Import Metalib.Metatheory.

Require Import syntax_ott rules_inf Infrastructure rules_inf2.

Require Import Coq.Strings.String.

Fixpoint erase_anno (e:exp) : dexp :=
  match e with
  | (e_var_b nat) => de_var_b nat
  | (e_var_f x) => de_var_f x
  | e_top => de_top
  | (e_lit i5) => de_lit i5
  | (e_abs A e B) => de_abs (erase_anno e)
  | (e_fixpoint e A) => de_fixpoint (erase_anno e)
  | (e_app e1 e2) => de_app (erase_anno e1) (erase_anno e2)
  | (e_merge e1 e2) => de_merge (erase_anno e1) (erase_anno e2)
  | (e_anno e A) => erase_anno e
  end.

Notation "| e |" := (erase_anno e) (at level 30, e at level 39).

From Stdlib Require Import Lia.

Local Lemma erase_anno_open_rec : forall e k u,
    erase_anno (open_exp_wrt_exp_rec k u e) =
    open_dexp_wrt_dexp_rec k (erase_anno u) (erase_anno e).
Proof.
  induction e as [n | x | | i | A e IH B | e IH A |
                  e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH A];
    intros k u; simpl; try now rewrite ?IH, ?IH1, ?IH2.
  destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt]; reflexivity.
Qed.

Local Lemma erase_anno_open : forall e u,
    erase_anno (open_exp_wrt_exp e u) =
    open_dexp_wrt_dexp (erase_anno e) (erase_anno u).
Proof.
  intros e u. apply erase_anno_open_rec.
Qed.

Local Lemma erase_anno_lc : forall e,
    lc_exp e -> lc_dexp (erase_anno e).
Proof.
  intros e Hlc.
  induction Hlc as [x | | i | A e B Hbody IH | e A Hbody IH |
                    e1 e2 H1 IH1 H2 IH2 | e1 e2 H1 IH1 H2 IH2 | e A H IH];
    simpl; eauto using lc_dexp.
  - apply lc_de_abs. intro x.
    specialize (IH x). now rewrite erase_anno_open in IH.
  - apply lc_de_fixpoint. intro x.
    specialize (IH x). now rewrite erase_anno_open in IH.
Qed.

Local Lemma erase_anno_value : forall v,
    value v -> DValue (erase_anno v).
Proof.
  intros v Hv. induction Hv; simpl; eauto using DValue, erase_anno_lc.
  apply DVal_abs. exact (erase_anno_lc _ H).
Qed.

Local Lemma dstep_star_trans : forall e1 e2 e3,
    e1 ->>* e2 -> e2 ->>* e3 -> e1 ->>* e3.
Proof.
  intros e1 e2 e3 H12 H23.
  induction H12; eauto using star_step.
Qed.

Local Lemma dstep_star_context : forall (C : dexp -> dexp),
    (forall e e', DunfieldStep e e' -> DunfieldStep (C e) (C e')) ->
    forall e e', e ->>* e' -> C e ->>* C e'.
Proof.
  intros C HC e e' Hsteps.
  induction Hsteps; eauto using star_refl, star_step.
Qed.

Local Lemma typed_reduce_source_lc : forall v A v',
    TypedReduce v A v' -> lc_dexp (erase_anno v).
Proof.
  intros v A v' H. induction H; simpl in *; eauto using lc_dexp, erase_anno_lc.
  exact (erase_anno_lc _ H).
Qed.

Local Lemma typed_reduce_result_value : forall v A v',
    TypedReduce v A v' -> DValue (erase_anno v').
Proof.
  intros v A v' H. induction H; simpl; eauto using DValue, lc_dexp.
  apply DVal_abs. exact (erase_anno_lc _ H).
Qed.

Local Lemma typed_reduce_erasure : forall v A v',
    TypedReduce v A v' -> erase_anno v ->>* erase_anno v'.
Proof.
  intros v A v' H.
  induction H as [i | v Hlc | v A B Hlc Htop | A e B C D Hlc Htop Hdom Hcod |
                  v1 v2 A v1' Hlc Hred IH Hord | v1 v2 A v2' Hlc Hred IH Hord |
                  v A B v1 v2 Hleft IHleft Hright IHright]; simpl.
  - apply star_refl.
  - eapply star_step; [apply DStep_top; now apply erase_anno_lc | apply star_refl].
  - eapply star_step; [apply DStep_top; now apply erase_anno_lc |].
    eapply star_step; [apply DStep_toparr | apply star_refl].
  - apply star_refl.
  - eapply star_step; [apply DStep_unmergel | exact IH].
    + now apply erase_anno_lc.
    + exact (typed_reduce_source_lc _ _ _ Hred).
  - eapply star_step; [apply DStep_unmerger | exact IH].
    + now apply erase_anno_lc.
    + exact (typed_reduce_source_lc _ _ _ Hred).
  - eapply star_step.
    { apply DStep_split. exact (typed_reduce_source_lc _ _ _ Hleft). }
    eapply dstep_star_trans.
    + apply (dstep_star_context (fun e => de_merge e (erase_anno v)));
        [| exact IHleft].
      intros e e' Hstep. apply DStep_mergel; [| exact Hstep].
      exact (typed_reduce_source_lc _ _ _ Hleft).
    + apply (dstep_star_context (de_merge (erase_anno v1))); [| exact IHright].
      intros e e' Hstep. apply DStep_merger; [| exact Hstep].
      exact (typed_reduce_result_value _ _ _ Hleft).
Qed.

Theorem reduction_soundness : forall e e',
    step e e' -> (erase_anno e) ->>* (erase_anno e').
Proof.
  intros e e' Hstep.
  induction Hstep as [A e D v v' Hlc Hv Hred | v A v' Hv Hred |
                      e1 e2 e1' Hlc Hstep IH | v1 e2 e2' Hv Hstep IH |
                      e1 e2 e1' Hlc Hstep IH | v1 e2 e2' Hv Hstep IH |
                      e A e' Hstep IH | e A Hlc]; simpl.
  - rewrite erase_anno_open.
    pose proof (erase_anno_lc _ Hlc) as Habs.
    eapply dstep_star_trans.
    + apply (dstep_star_context (de_app (de_abs (erase_anno e)))).
      * intros u u' Hu. apply DStep_appr; [now apply DVal_abs | exact Hu].
      * exact (typed_reduce_erasure _ _ _ Hred).
    + eapply star_step; [apply DStep_beta | apply star_refl].
      * exact Habs.
      * exact (typed_reduce_result_value _ _ _ Hred).
  - exact (typed_reduce_erasure _ _ _ Hred).
  - apply (dstep_star_context (fun e => de_app e (erase_anno e2))); [| exact IH].
    eauto using DStep_appl, erase_anno_lc.
  - apply (dstep_star_context (de_app (erase_anno v1))); [| exact IH].
    eauto using DStep_appr, erase_anno_value.
  - apply (dstep_star_context (fun e => de_merge e (erase_anno e2))); [| exact IH].
    eauto using DStep_mergel, erase_anno_lc.
  - apply (dstep_star_context (de_merge (erase_anno v1))); [| exact IH].
    eauto using DStep_merger, erase_anno_value.
  - exact IH.
  - rewrite erase_anno_open.
    eapply star_step; [apply DStep_fix | apply star_refl].
    exact (erase_anno_lc _ Hlc).
Qed.
