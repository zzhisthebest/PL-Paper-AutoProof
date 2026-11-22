Require Import Definitions.Syntax Definitions.Semantics Definitions.Typing
  Definitions.CTSanity Definitions.SubDenotation.
From Stdlib Require Import ListSet.
From Stdlib Require Import List Arith Lia ZArith Bool Arith.Wf_nat.
Require Import RFJ.Lists.
Require Import RFJ.Utils.Referable.
From Stdlib Require Import Program.Equality.
Require Import Definitions.FJTyping.


(* ===== module devtest8 ===== *)
(* ============ generic list lemmas ============ *)
Lemma Forall2_nth_error_some : forall {A B} (P:A->B->Prop) l1 l2 i x,
  Forall2 P l1 l2 -> nth_error l1 i = Some x -> exists y, nth_error l2 i = Some y /\ P x y.
Proof.
  intros A B P l1. induction l1 as [|a l1 IH]; intros l2 i x HF HN.
  - destruct i; simpl in HN; discriminate.
  - destruct l2 as [|b l2]; simpl in HF; [inversion HF|].
    inversion HF as [|? ? ? ? HP HF']; subst.
    destruct i as [|i]; simpl in *.
    + injection HN as ->. exists b. auto.
    + specialize (IH l2 i x HF' HN). destruct IH as [y [Hy HPy]]. exists y. auto.
Qed.

Lemma Forall2_nth_error_Some : forall {A B} (P:A->B->Prop) l1 l2 i x y,
  Forall2 P l1 l2 -> nth_error l1 i = Some x -> nth_error l2 i = Some y -> P x y.
Proof.
  intros A B P l1 l2 i x y HF HN1 HN2.
  destruct (Forall2_nth_error_some P l1 l2 i x HF HN1) as [y' [Hy' HP]].
  rewrite Hy' in HN2. injection HN2 as ->. auto.
Qed.

Lemma Forall2_length : forall {A B} (P:A->B->Prop) l1 l2, Forall2 P l1 l2 -> length l1 = length l2.
Proof. intros. induction H; simpl; auto. Qed.

Lemma nth_error_map_Some : forall {A B} (f:A->B) l i y,
  nth_error (map f l) i = Some y -> exists x, nth_error l i = Some x /\ f x = y.
Proof.
  intros A B f l. induction l as [|a l IH]; intros i y H.
  - destruct i; simpl in H; discriminate.
  - destruct i as [|i]; simpl in *.
    + injection H as Hy. exists a. simpl. auto.
    + apply IH in H. destruct H as [x [Hx Hxy]]. exists x; auto.
Qed.

(* ============ isLC monotonicity ============ *)
Lemma isLC_mono_gen :
  (forall e j k, j <= k -> isLC_at j e -> isLC_at k e) /\
  (forall t j k, j <= k -> isLCT_at j t -> isLCT_at k t) /\
  (forall ps j k, j <= k -> isLCP_at j ps -> isLCP_at k ps).
Proof.
  apply syntax_mutind'.
  - simpl; auto.
  - simpl; auto.
  - simpl; intros i j k Hjk Hi; lia.
  - simpl; auto.
  - simpl; intros o e IH j k Hjk H; eapply IH; eauto.
  - simpl; intros o e1 IH1 e2 IH2 j k Hjk [H1 H2]; split; eauto.
  - simpl; intros e IH m e0 IH0 j k Hjk [H1 H2]; split; eauto.
  - simpl; intros e IH f j k Hjk H; eapply IH; eauto.
  - simpl. intros c l HF j k Hjk Hv.
    revert HF Hv. induction l as [|a l IHs]; simpl; intros HF Hv; auto.
    simpl in Hv. destruct Hv as [Ha Hl].
    inversion HF as [|? ? Ha' HF']; subst. split.
    + eapply Ha'; eauto. + apply IHs; auto.
  - simpl. intros e1 IH1 e2 IH2 j k Hjk [H1 H2]; split. eapply IH1; eauto. apply IH2 with (j:=j+1) (k:=k+1); auto; lia.
  - simpl. intros b ps IH j k Hjk H. apply IH with (j:=j+1) (k:=k+1); auto; lia.
  - simpl; auto.
  - simpl. intros p IHp ps IHps j k Hjk [H1 H2]; split; eauto.
Qed.

Lemma isLC_at_mono : forall e j k, j <= k -> isLC_at j e -> isLC_at k e.
Proof. intros; eapply (proj1 isLC_mono_gen); eauto. Qed.
Lemma isLCT_at_mono : forall t j k, j <= k -> isLCT_at j t -> isLCT_at k t.
Proof. intros; eapply (proj1 (proj2 isLC_mono_gen)); eauto. Qed.
Lemma isLCP_at_mono : forall ps j k, j <= k -> isLCP_at j ps -> isLCP_at k ps.
Proof. intros; eapply (proj2 (proj2 isLC_mono_gen)); eauto. Qed.

(* ============ list-level predicates ============ *)
Definition isValueL (l:[expr]) : Prop :=
  (fix f (es':[expr]) := match es' with | nil => True | e::es'' => isValue e /\ f es'' end) l.

Definition isLCL_at (j:nat) (l:[expr]) : Prop :=
  (fix f (es':[expr]) := match es' with | nil => True | e::es'' => isLC_at j e /\ f es'' end) l.

Fixpoint fvfree (e:expr) : Prop :=
  match e with
  | Bc _ => True
  | Ic _ => True
  | BV _ => True
  | FV _ => False
  | ExpUnOp _ e1 => fvfree e1
  | ExpBinOp _ e1 e2 => fvfree e1 /\ fvfree e2
  | ExpFieldAccess e1 _ => fvfree e1
  | ExpMethodInvoc e1 _ e2 => fvfree e1 /\ fvfree e2
  | ExpNew c l => (fix f (es':[expr]) := match es' with | nil => True | e::es'' => fvfree e /\ f es'' end) l
  | ExpLet e1 e2 => fvfree e1 /\ fvfree e2
  end.

Definition fvfreeL (l:[expr]) : Prop :=
  (fix f (es':[expr]) := match es' with | nil => True | e::es'' => fvfree e /\ f es'' end) l.

Lemma isValueL_Forall : forall l, isValueL l <-> Forall isValue l.
Proof.
  induction l as [|a l IH]; simpl.
  - split; intros; constructor.
  - split; intros H; [destruct H as [Ha Hl]|inversion H as [|? ? Ha Hl]; subst].
    + constructor; auto. apply IH; auto.
    + split; auto. apply IH; auto.
Qed.

Lemma fvfreeL_Forall : forall l, fvfreeL l <-> Forall fvfree l.
Proof.
  induction l as [|a l IH]; simpl.
  - split; intros; constructor.
  - split; intros H; [destruct H as [Ha Hl]|inversion H as [|? ? Ha Hl]; subst].
    + constructor; auto. apply IH; auto.
    + split; auto. apply IH; auto.
Qed.

(* isValue implies isLC *)
Lemma isValue_isLC : forall e, isValue e -> isLC e.
Proof.
  refine (proj1 (syntax_mutind'
    (fun e => isValue e -> isLC_at 0 e) (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - cbn; auto.
  - cbn; auto.
  - cbn; intros i H; destruct H.
  - cbn; intros x H; destruct H.
  - cbn; intros o e IH H; destruct H.
  - cbn; intros o e1 IH1 e2 IH2 H; destruct H.
  - cbn; intros e1 IH1 m e2 IH2 H; destruct H.
  - cbn; intros e IH f H; destruct H.
  - cbn. intros c l HF H.
    revert HF. apply isValueL_Forall in H.
    induction H as [|a l Ha Hl IHs]; cbn; intros HF.
    + exact I.
    + inversion HF as [|? ? Ha' HF']; subst. split.
      * apply Ha'; auto.
      * apply IHs; auto.
  - cbn; intros e1 IH1 e2 IH2 H; destruct H.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma isValue_isLC' : forall e j, isValue e -> isLC_at j e.
Proof.
  intros e j H. apply isLC_at_mono with (j:=0).
  - lia.
  - apply isValue_isLC; auto.
Qed.

Lemma isValueL_isLCL : forall l j, isValueL l -> isLCL_at j l.
Proof.
  intros l j H. apply isValueL_Forall in H.
  induction H as [|a l Ha Hl IHs]; simpl; auto.
  split; auto. apply isValue_isLC'; auto.
Qed.

(* isValue implies fvfree *)
Lemma isValue_fvfree : forall e, isValue e -> fvfree e.
Proof.
  refine (proj1 (syntax_mutind'
    (fun e => isValue e -> fvfree e) (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - simpl; auto.
  - simpl; auto.
  - simpl; intros i H; destruct H.
  - simpl; intros x H; destruct H.
  - simpl; intros o e IH H; destruct H.
  - simpl; intros o e1 IH1 e2 IH2 H; destruct H.
  - simpl; intros e1 IH1 m e2 IH2 H; destruct H.
  - simpl; intros e IH f H; destruct H.
  - simpl. intros c l HF H.
    revert HF. apply isValueL_Forall in H.
    induction H as [|a l Ha Hl IHs]; simpl; intros HF.
    + exact I.
    + inversion HF as [|? ? Ha' HF']; subst. split.
      * apply Ha'; auto.
      * apply IHs; auto.
  - simpl; intros e1 IH1 e2 IH2 H; destruct H.
  - simpl; auto.
  - simpl; auto.
  - simpl; auto.
Qed.

(* ============ substitution: values are closed ============ *)
Lemma fvfree_subFV : forall e, fvfree e -> forall x v, subFV x v e = e.
Proof.
  refine (proj1 (syntax_mutind'
    (fun e => fvfree e -> forall x v, subFV x v e = e)
    (fun (_:type) => True) (fun (_:preds) => True) _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - simpl; auto.
  - simpl; auto.
  - simpl; auto.
  - simpl; intros x H; destruct H.
  - simpl; intros o e IH H x v; simpl. rewrite IH; auto.
  - simpl; intros o e1 IH1 e2 IH2 H x v; simpl. destruct H as [H1 H2]; rewrite IH1, IH2; auto.
  - simpl; intros e1 IH1 m e2 IH2 H x v; simpl. destruct H as [H1 H2]; rewrite IH1, IH2; auto.
  - simpl; intros e IH f H x v; simpl. rewrite IH; auto.
  - simpl. intros c l HF H x v. simpl. f_equal.
    revert HF H. induction l as [|a l IHs]; simpl; intros HF H.
    + reflexivity.
    + destruct H as [Ha Hl]. inversion HF as [|? ? Ha' HF']; subst.
      rewrite (Ha' Ha). rewrite (IHs HF' Hl). reflexivity.
  - simpl; intros e1 IH1 e2 IH2 H x v; simpl. destruct H as [H1 H2]; rewrite IH1, IH2; auto.
  - simpl; intros; auto.
  - simpl; intros; auto.
  - simpl; intros; auto.
Qed.

Lemma fvfreeL_map : forall l, fvfreeL l -> forall x v, map (subFV x v) l = l.
Proof.
  intros l H. apply fvfreeL_Forall in H.
  induction H as [|a l Ha Hl IHs]; simpl; intros x v.
  - reflexivity.
  - rewrite fvfree_subFV; auto. rewrite IHs; auto.
Qed.

Lemma isValue_subFV : forall v, isValue v -> forall x w, subFV x w v = v.
Proof. intros. apply fvfree_subFV. apply isValue_fvfree; auto. Qed.

(* ============ fvfree preserved by subBV ============ *)
Lemma fvfree_subBV_gen :
  (forall (e:expr) (j:nat) (w:expr), fvfree w -> (fvfree (subBV_at j w e) <-> fvfree e)) /\
  (type -> True) /\ (preds -> True).
Proof.
  refine (syntax_mutind' (fun e => forall j w, fvfree w -> (fvfree (subBV_at j w e) <-> fvfree e))
    (fun (_:type) => True) (fun (_:preds) => True) _ _ _ _ _ _ _ _ _ _ _ _ _).
  - simpl; tauto.
  - simpl; tauto.
  - simpl. intros i j w Hw. destruct (j =? i) eqn:E; simpl; tauto.
  - simpl; tauto.
  - simpl; intros o e IH j w Hw; simpl. apply IH; auto.
  - simpl; intros o e1 IH1 e2 IH2 j w Hw; simpl. specialize (IH1 j w Hw). specialize (IH2 j w Hw). rewrite IH1, IH2; tauto.
  - simpl; intros e1 IH1 m e2 IH2 j w Hw; simpl. specialize (IH1 j w Hw). specialize (IH2 j w Hw). rewrite IH1, IH2; tauto.
  - simpl; intros e IH f j w Hw; simpl. apply IH; auto.
  - simpl. intros c l HF j w Hw. simpl.
    revert HF. induction l as [|a l IHs]; simpl; intros HF.
    + tauto.
    + inversion HF as [|? ? Ha' HF']; subst.
      specialize (Ha' j w Hw). apply IHs in HF'. rewrite Ha', HF'. tauto.
  - simpl; intros e1 IH1 e2 IH2 j w Hw; simpl. specialize (IH1 j w Hw). specialize (IH2 (j+1) w Hw). rewrite IH1, IH2. tauto.
  - simpl; tauto.
  - simpl; tauto.
  - simpl; tauto.
Qed.

Lemma fvfree_subBV : forall e j w, fvfree w -> fvfree (subBV_at j w e) -> fvfree e.
Proof. intros. apply (proj1 fvfree_subBV_gen e j w H). auto. Qed.

(* ============ subBV identity when locally closed ============ *)
Lemma subBV_at_LC_gen :
  (forall (e:expr) (j:nat), isLC_at j e -> forall w, subBV_at j w e = e) /\
  (forall (t:type) (j:nat), isLCT_at j t -> forall w, tsubBV_at j w t = t) /\
  (forall (ps:preds) (j:nat), isLCP_at j ps -> forall w, psubBV_at j w ps = ps).
Proof.
  refine (syntax_mutind'
    (fun (e:expr) => forall j, isLC_at j e -> forall w, subBV_at j w e = e)
    (fun (t:type) => forall j, isLCT_at j t -> forall w, tsubBV_at j w t = t)
    (fun (ps:preds) => forall j, isLCP_at j ps -> forall w, psubBV_at j w ps = ps)
    _ _ _ _ _ _ _ _ _ _ _ _ _).
  - simpl; auto.
  - simpl; auto.
  - simpl. intros i j Hj w. simpl. destruct (j =? i) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso; lia.
    + reflexivity.
  - simpl; auto.
  - simpl; intros o e IH j Hj w; simpl. rewrite IH; auto.
  - simpl; intros o e1 IH1 e2 IH2 j Hj w; simpl. destruct Hj as [H1 H2]. rewrite IH1, IH2; auto.
  - simpl; intros e1 IH1 m e2 IH2 j Hj w; simpl. destruct Hj as [H1 H2]. rewrite IH1, IH2; auto.
  - simpl; intros e IH f j Hj w; simpl. rewrite IH; auto.
  - simpl. intros c l HF j Hj w. simpl. f_equal.
    revert HF. induction l as [|a l IHs]; simpl; intros HF.
    + reflexivity.
    + destruct Hj as [Ha Hl]. inversion HF as [|? ? Ha' HF']; subst.
      rewrite (Ha' j Ha). rewrite (IHs Hl HF'). reflexivity.
  - simpl; intros e1 IH1 e2 IH2 j Hj w; simpl. destruct Hj as [H1 H2]. rewrite IH1 with (j:=j), IH2 with (j:=j+1); auto.
  - simpl; intros b ps IHp j Hj w. simpl. rewrite IHp with (j:=j+1); auto.
  - simpl; auto.
  - simpl; intros p IHp ps IHps j Hj w; simpl. destruct Hj as [H1 H2]. rewrite IHp, IHps; auto.
Qed.

Lemma subBV_at_LC : forall e j, isLC_at j e -> forall w, subBV_at j w e = e.
Proof. intros; apply (proj1 subBV_at_LC_gen); auto. Qed.

Lemma psubBV_at_lc : forall ps j, isLCP_at j ps -> forall w, psubBV_at j w ps = ps.
Proof. intros; apply (proj2 (proj2 subBV_at_LC_gen)); auto. Qed.

Lemma isValue_subBV_at : forall v, isValue v -> forall j w, subBV_at j w v = v.
Proof. intros. apply subBV_at_LC. apply isValue_isLC'; auto. Qed.

(* ============ free variable membership ============ *)
Definition fvL (l:[expr]) : names :=
  (fix f (es':[expr]) := match es' with | nil => empty | e::es'' => union (fv e) (f es'') end) l.

Lemma In_union_iff : forall (s t:names) y, In y (union s t) <-> In y s \/ In y t.
Proof. intros. apply set_union_iff. Qed.

Lemma not_or : forall A B:Prop, ~(A \/ B) -> ~A /\ ~B.
Proof. intros A B H; split; intro; apply H; auto. Qed.

Lemma In_singleton_iff : forall x y, In y (singleton x) <-> y = x.
Proof.
  intros. unfold singleton, names_add, empty, empty_set. rewrite set_add_iff.
  split.
  - intros [H|H]; auto. unfold empty_set in H; destruct H.
  - intros ->. left; reflexivity.
Qed.

Lemma In_empty_iff : forall y, ~ In y (empty).
Proof. intros. unfold empty, empty_set. simpl. auto. Qed.

Lemma fvL_mem : forall l y, In y (fvL l) <-> exists a, In a l /\ In y (fv a).
Proof.
  induction l as [|a l IH]; simpl; intros y.
  - split; intros H. + apply In_empty_iff in H; tauto.
    + destruct H as [a [Ha _]]; inversion Ha.
  - rewrite In_union_iff. split.
    + intros [H|H]. * exists a; auto. * apply IH in H; destruct H as [b [Hb Hy]]; exists b; auto.
    + intros [b [Hb Hy]]. destruct Hb as [->|Hb].
      * left; auto. * right; apply IH; eauto.
Qed.

Lemma fv_New_notin : forall c l y a, ~ In y (fv (ExpNew c l)) -> In a l -> ~ In y (fv a).
Proof.
  intros c l y a H Ha Hy. apply H. change (In y (fvL l)). rewrite fvL_mem.
  exists a; auto.
Qed.

(* ============ definitional unfolding lemmas ============ *)
Lemma sFV_New : forall x v c l, subFV x v (ExpNew c l) = ExpNew c (map (subFV x v) l).
Proof. intros. reflexivity. Qed.
Lemma sBV_New : forall j w c l, subBV_at j w (ExpNew c l) = ExpNew c (map (subBV_at j w) l).
Proof. intros. reflexivity. Qed.
Lemma open_New : forall j y c l, open_at j y (ExpNew c l) = ExpNew c (map (open_at j y) l).
Proof. intros. reflexivity. Qed.
Lemma sFV_Let : forall x v a b, subFV x v (ExpLet a b) = ExpLet (subFV x v a) (subFV x v b).
Proof. intros. reflexivity. Qed.
Lemma sBV_Let : forall j w a b, subBV_at j w (ExpLet a b) = ExpLet (subBV_at j w a) (subBV_at (j+1) w b).
Proof. intros. reflexivity. Qed.
Lemma open_Let : forall j y a b, open_at j y (ExpLet a b) = ExpLet (open_at j y a) (open_at (j+1) y b).
Proof. intros. reflexivity. Qed.
Lemma tsubFV_TRefn : forall x v b ps, tsubFV x v (TRefn b ps) = TRefn b (psubFV x v ps).
Proof. intros. reflexivity. Qed.
Lemma tsubBV_TRefn : forall j w b ps, tsubBV_at j w (TRefn b ps) = TRefn b (psubBV_at (j+1) w ps).
Proof. intros. reflexivity. Qed.
Lemma openT_TRefn : forall j y b ps, openT_at j y (TRefn b ps) = TRefn b (openP_at (j+1) y ps).
Proof. intros. reflexivity. Qed.
Lemma psubFV_PCons : forall x v p ps, psubFV x v (PCons p ps) = PCons (subFV x v p) (psubFV x v ps).
Proof. intros. reflexivity. Qed.
Lemma psubBV_PCons : forall j w p ps, psubBV_at j w (PCons p ps) = PCons (subBV_at j w p) (psubBV_at j w ps).
Proof. intros. reflexivity. Qed.
Lemma psubBV_PEmpty : forall j w, psubBV_at j w PEmpty = PEmpty.
Proof. intros. reflexivity. Qed.
Lemma psubBV_at_PEmpty : forall j w, psubBV_at j w PEmpty = PEmpty.
Proof. intros. reflexivity. Qed.
Lemma tsubBV_at_TRefn : forall j w b ps, tsubBV_at j w (TRefn b ps) = TRefn b (psubBV_at (j+1) w ps).
Proof. intros. reflexivity. Qed.
Lemma psubFV_PEmpty : forall x v, psubFV x v PEmpty = PEmpty.
Proof. intros. reflexivity. Qed.
Lemma psubBV_at_PCons : forall j w p ps, psubBV_at j w (PCons p ps) = PCons (subBV_at j w p) (psubBV_at j w ps).
Proof. intros. reflexivity. Qed.
Lemma openP_PCons : forall j y p ps, openP_at j y (PCons p ps) = PCons (open_at j y p) (openP_at j y ps).
Proof. intros. reflexivity. Qed.

(* ============ substitution on an opened term ============ *)
Lemma subFV_open_gen :
  (forall (e:expr) (j:nat) (y:vname), ~ In y (fv e) ->
      forall v, subFV y v (open_at j y e) = subBV_at j v e) /\
  (forall (t:type) (j:nat) (y:vname), ~ In y (free t) ->
      forall v, tsubFV y v (openT_at j y t) = tsubBV_at j v t) /\
  (forall (ps:preds) (j:nat) (y:vname), ~ In y (fvP ps) ->
      forall v, psubFV y v (openP_at j y ps) = psubBV_at j v ps).
Proof.
  refine (syntax_mutind'
    (fun e => forall j y, ~ In y (fv e) -> forall v, subFV y v (open_at j y e) = subBV_at j v e)
    (fun t => forall j y, ~ In y (free t) -> forall v, tsubFV y v (openT_at j y t) = tsubBV_at j v t)
    (fun ps => forall j y, ~ In y (fvP ps) -> forall v, psubFV y v (openP_at j y ps) = psubBV_at j v ps)
    _ _ _ _ _ _ _ _ _ _ _ _ _).
  - simpl; auto.
  - simpl; auto.
  - simpl. intros i j y Hy v. destruct (j =? i) eqn:E; simpl.
    + apply Nat.eqb_eq in E; subst. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - simpl. intros x j y Hy v. simpl. destruct (y =? x) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hy. left; reflexivity.
    + reflexivity.
  - simpl. intros o e IH j y Hy v. simpl. rewrite IH; auto.
  - simpl. intros o e1 IH1 e2 IH2 j y Hy v. simpl.
    rewrite In_union_iff in Hy. apply not_or in Hy. destruct Hy as [H1 H2]. rewrite IH1, IH2; auto.
  - simpl. intros e1 IH1 m e2 IH2 j y Hy v. simpl.
    rewrite In_union_iff in Hy. apply not_or in Hy. destruct Hy as [H1 H2]. rewrite IH1, IH2; auto.
  - simpl. intros e IH f j y Hy v. simpl. rewrite IH; auto.
  - intros c l HF j y Hy v.
    rewrite open_New, sFV_New, sBV_New, map_map.
    rewrite Forall_forall in HF.
    apply f_equal. apply map_ext_in. intros a Ha.
    assert (Hfa : ~ In y (fv a)) by (apply fv_New_notin with (c:=c) (l:=l) (y:=y); auto).
    apply HF; auto.
  - simpl. intros e1 IH1 e2 IH2 j y Hy v. simpl.
    rewrite In_union_iff in Hy. apply not_or in Hy. destruct Hy as [H1 H2].
    rewrite IH1; auto. rewrite IH2; auto.
  - simpl. intros b ps IH j y Hy v. simpl. rewrite IH with (j:=j+1); auto.
  - simpl; auto.
  - simpl. intros p IHp ps IHps j y Hy v. simpl.
    rewrite In_union_iff in Hy. apply not_or in Hy. destruct Hy as [H1 H2].
    rewrite IHp; auto. rewrite IHps; auto.
Qed.

Lemma subFV_open : forall e j y, ~ In y (fv e) -> forall v, subFV y v (open_at j y e) = subBV_at j v e.
Proof. intros; apply (proj1 subFV_open_gen); auto. Qed.

Lemma subFV_notin_gen :
  (forall (e:expr) (y:vname), ~ In y (fv e) -> forall v, subFV y v e = e) /\
  (forall (t:type) (y:vname), ~ In y (free t) -> forall v, tsubFV y v t = t) /\
  (forall (ps:preds) (y:vname), ~ In y (fvP ps) -> forall v, psubFV y v ps = ps).
Proof.
  refine (syntax_mutind'
    (fun e => forall y, ~ In y (fv e) -> forall v, subFV y v e = e)
    (fun t => forall y, ~ In y (free t) -> forall v, tsubFV y v t = t)
    (fun ps => forall y, ~ In y (fvP ps) -> forall v, psubFV y v ps = ps)
    _ _ _ _ _ _ _ _ _ _ _ _ _).
  - simpl; auto.
  - simpl; auto.
  - simpl; auto.
  - simpl. intros x y Hy v. simpl. destruct (y =? x) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hy. left; reflexivity.
    + reflexivity.
  - simpl. intros o e IH y Hy v. simpl. rewrite IH; auto.
  - simpl. intros o e1 IH1 e2 IH2 y Hy v. simpl.
    rewrite In_union_iff in Hy. apply not_or in Hy. destruct Hy as [H1 H2]; rewrite IH1, IH2; auto.
  - simpl. intros e1 IH1 m e2 IH2 y Hy v. simpl.
    rewrite In_union_iff in Hy. apply not_or in Hy. destruct Hy as [H1 H2]; rewrite IH1, IH2; auto.
  - simpl. intros e IH f y Hy v. simpl. rewrite IH; auto.
  - intros c l HF y Hy v.
    rewrite sFV_New.
    rewrite Forall_forall in HF.
    apply f_equal.
    transitivity (map (fun x => x) l).
    + apply map_ext_in. intros a Ha.
      assert (Hfa : ~ In y (fv a)) by (apply fv_New_notin with (c:=c) (l:=l) (y:=y); auto).
      apply HF; auto.
    + apply map_id.
  - simpl. intros e1 IH1 e2 IH2 y Hy v. simpl.
    rewrite In_union_iff in Hy. apply not_or in Hy. destruct Hy as [H1 H2]; rewrite IH1, IH2; auto.
  - simpl. intros b ps IH y Hy v. simpl. rewrite IH; auto.
  - simpl; auto.
  - simpl. intros p IHp ps IHps y Hy v. simpl.
    rewrite In_union_iff in Hy. apply not_or in Hy. destruct Hy as [H1 H2]; rewrite IHp, IHps; auto.
Qed.

Lemma subFV_notin : forall e y, ~ In y (fv e) -> forall v, subFV y v e = e.
Proof. intros; apply (proj1 subFV_notin_gen); auto. Qed.
Lemma tsubFV_notin : forall t y, ~ In y (free t) -> forall v, tsubFV y v t = t.
Proof. intros; apply (proj1 (proj2 subFV_notin_gen)); auto. Qed.
Lemma psubFV_notin : forall ps y, ~ In y (fvP ps) -> forall v, psubFV y v ps = ps.
Proof. intros; apply (proj2 (proj2 subFV_notin_gen)); auto. Qed.

(* ============ subFV commutes with subBV ============ *)
Lemma subFV_subBV_gen :
  (forall (e:expr) (x:vname) (v:expr), isLC v ->
     forall (j:nat) (w:expr), subFV x v (subBV_at j w e) = subBV_at j (subFV x v w) (subFV x v e)) /\
  (forall (t:type) (x:vname) (v:expr), isLC v ->
     forall (j:nat) (w:expr), tsubFV x v (tsubBV_at j w t) = tsubBV_at j (subFV x v w) (tsubFV x v t)) /\
  (forall (ps:preds) (x:vname) (v:expr), isLC v ->
     forall (j:nat) (w:expr), psubFV x v (psubBV_at j w ps) = psubBV_at j (subFV x v w) (psubFV x v ps)).
Proof.
  refine (syntax_mutind'
    (fun e => forall x v, isLC v -> forall j w, subFV x v (subBV_at j w e) = subBV_at j (subFV x v w) (subFV x v e))
    (fun t => forall x v, isLC v -> forall j w, tsubFV x v (tsubBV_at j w t) = tsubBV_at j (subFV x v w) (tsubFV x v t))
    (fun ps => forall x v, isLC v -> forall j w, psubFV x v (psubBV_at j w ps) = psubBV_at j (subFV x v w) (psubFV x v ps))
    _ _ _ _ _ _ _ _ _ _ _ _ _).
  - simpl; auto.
  - simpl; auto.
  - simpl. intros i x v Hv j w. simpl. destruct (j =? i); reflexivity.
  - simpl. intros y x v Hv j w. simpl.
    destruct (x =? y) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      assert (Hlc : isLC_at j v) by (apply isLC_at_mono with (j:=0); [lia|auto]).
      rewrite (subBV_at_LC v j Hlc (subFV y v w)).
      simpl. reflexivity.
    + reflexivity.
  - simpl. intros o e IH x v Hv j w. simpl. rewrite IH; auto.
  - simpl. intros o e1 IH1 e2 IH2 x v Hv j w. simpl. rewrite IH1, IH2; auto.
  - simpl. intros e1 IH1 m e2 IH2 x v Hv j w. simpl. rewrite IH1, IH2; auto.
  - simpl. intros e IH f x v Hv j w. simpl. rewrite IH; auto.
  - intros c l HF x v Hv j w.
    rewrite sBV_New, sFV_New, sFV_New, sBV_New, map_map, map_map.
    f_equal. rewrite Forall_forall in HF.
    apply map_ext_in. intros a Ha.
    apply HF; auto.
  - simpl. intros e1 IH1 e2 IH2 x v Hv j w. simpl. rewrite IH1, IH2; auto.
  - simpl. intros b ps IH x v Hv j w. simpl. rewrite IH with (j:=j+1); auto.
  - simpl; auto.
  - simpl. intros p IHp ps IHps x v Hv j w. simpl. rewrite IHp, IHps; auto.
Qed.

Lemma subFV_subBV : forall e x v, isLC v -> forall j w,
  subFV x v (subBV_at j w e) = subBV_at j (subFV x v w) (subFV x v e).
Proof. intros; apply (proj1 subFV_subBV_gen); auto. Qed.
Lemma psubFV_psubBV : forall ps x v, isLC v -> forall j w,
  psubFV x v (psubBV_at j w ps) = psubBV_at j (subFV x v w) (psubFV x v ps).
Proof. intros; apply (proj2 (proj2 subFV_subBV_gen)); auto. Qed.
Lemma tsubFV_tsubBV : forall t x v, isLC v -> forall j w,
  tsubFV x v (tsubBV_at j w t) = tsubBV_at j (subFV x v w) (tsubFV x v t).
Proof. intros; apply (proj1 (proj2 subFV_subBV_gen)); auto. Qed.

(* ============ csubst algebra ============ *)
Definition LCsubst (th:csub) : Prop :=
  (fix f (th':csub) := match th' with
    | CEmpty => True
    | CCons x v th'' => isLC v /\ f th''
    end) th.

Lemma LCsubst_empty : LCsubst CEmpty.
Proof. simpl. auto. Qed.

Lemma LCsubst_cons : forall x v th, LCsubst (CCons x v th) <-> isLC v /\ LCsubst th.
Proof. intros. simpl. tauto. Qed.

Lemma LCsubst_tail : forall x v th, LCsubst (CCons x v th) -> LCsubst th.
Proof. intros x v th H. unfold LCsubst in H. simpl in H. destruct H as [_ H]; auto. Qed.

Lemma LCsubst_head : forall x v th, LCsubst (CCons x v th) -> isLC v.
Proof. intros x v th H. unfold LCsubst in H. simpl in H. destruct H as [H _]; auto. Qed.

Lemma csubst_Bc : forall th b, csubst th (Bc b) = Bc b.
Proof. intros th. induction th; simpl; auto. Qed.
Lemma csubst_Ic : forall th n, csubst th (Ic n) = Ic n.
Proof. intros th. induction th; simpl; auto. Qed.
Lemma csubst_BV : forall th i, csubst th (BV i) = BV i.
Proof. intros th. induction th; simpl; auto. Qed.

Lemma csubst_UnOp : forall th o e, csubst th (ExpUnOp o e) = ExpUnOp o (csubst th e).
Proof.
  intros th. induction th as [|x v th IH]; intros o e; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma csubst_BinOp : forall th o e1 e2,
  csubst th (ExpBinOp o e1 e2) = ExpBinOp o (csubst th e1) (csubst th e2).
Proof.
  intros th. induction th as [|x v th IH]; intros o e1 e2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma csubst_Invok : forall th e1 m e2,
  csubst th (ExpMethodInvoc e1 m e2) = ExpMethodInvoc (csubst th e1) m (csubst th e2).
Proof.
  intros th. induction th as [|x v th IH]; intros e1 m e2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma csubst_Field : forall th e f,
  csubst th (ExpFieldAccess e f) = ExpFieldAccess (csubst th e) f.
Proof.
  intros th. induction th as [|x v th IH]; intros e f; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma csubst_Let : forall th e1 e2,
  csubst th (ExpLet e1 e2) = ExpLet (csubst th e1) (csubst th e2).
Proof.
  intros th. induction th as [|x v th IH]; intros e1 e2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma csubst_New : forall th c l,
  csubst th (ExpNew c l) = ExpNew c (map (csubst th) l).
Proof.
  intros th. induction th as [|x v th IH]; intros c l.
  - simpl. f_equal. symmetry. exact (map_id l).
  - change (csubst th (subFV x v (ExpNew c l)) = ExpNew c (map (csubst (CCons x v th)) l)).
    rewrite sFV_New, IH, map_map. reflexivity.
Qed.

Lemma csubst_fvfree : forall e, fvfree e -> forall th, csubst th e = e.
Proof.
  intros e Hf. induction th as [|x v th IH]; simpl.
  - reflexivity.
  - rewrite fvfree_subFV; auto.
Qed.

Lemma csubst_value : forall v, isValue v -> forall th, csubst th v = v.
Proof. intros. apply csubst_fvfree. apply isValue_fvfree; auto. Qed.

Lemma cpsubst_PEmpty : forall th, cpsubst th PEmpty = PEmpty.
Proof. intros th. induction th; simpl; auto. Qed.
Lemma cpsubst_PCons : forall th p ps, cpsubst th (PCons p ps) = PCons (csubst th p) (cpsubst th ps).
Proof.
  intros th. induction th as [|x v th IH]; intros p ps; simpl.
  - reflexivity.
  - change (cpsubst th (psubFV x v (PCons p ps)) = PCons (csubst (CCons x v th) p) (cpsubst (CCons x v th) ps)).
    rewrite psubFV_PCons, IH. reflexivity.
Qed.
Lemma ctsubst_TRefn : forall th b ps, ctsubst th (TRefn b ps) = TRefn b (cpsubst th ps).
Proof.
  intros th. induction th as [|x v th IH]; intros b ps; simpl.
  - reflexivity.
  - change (ctsubst th (tsubFV x v (TRefn b ps)) = TRefn b (cpsubst (CCons x v th) ps)).
    rewrite tsubFV_TRefn, IH. reflexivity.
Qed.

Lemma eqlPred_unfold : forall e, eqlPred e = ExpBinOp Eq e (BV 0).
Proof. reflexivity. Qed.

Lemma subFV_eqlPred : forall x v e, subFV x v (eqlPred e) = eqlPred (subFV x v e).
Proof. intros. simpl. reflexivity. Qed.

Lemma tsubFV_self : forall x v t e, tsubFV x v (self t e) = self (tsubFV x v t) (subFV x v e).
Proof.
  intros x v t e. destruct t as [b ps]. simpl.
  unfold eqlPred. simpl. reflexivity.
Qed.

Lemma ctsubst_self : forall th t e, ctsubst th (self t e) = self (ctsubst th t) (csubst th e).
Proof.
  intros th. induction th as [|x v th IH]; intros t e; simpl.
  - reflexivity.
  - rewrite tsubFV_self. apply IH.
Qed.

Lemma csubst_subBV_gen :
  (forall (e:expr) (th:csub), LCsubst th -> forall j w,
      csubst th (subBV_at j w e) = subBV_at j (csubst th w) (csubst th e)) /\
  (forall (t:type) (th:csub), LCsubst th -> forall j w,
      ctsubst th (tsubBV_at j w t) = tsubBV_at j (csubst th w) (ctsubst th t)) /\
  (forall (ps:preds) (th:csub), LCsubst th -> forall j w,
      cpsubst th (psubBV_at j w ps) = psubBV_at j (csubst th w) (cpsubst th ps)).
Proof.
  split.
  - intros e th. revert e. induction th as [|x v th' IH]; intros e Hlc j w.
    + reflexivity.
    + simpl. unfold LCsubst in Hlc. simpl in Hlc. destruct Hlc as [Hv Hlc].
      rewrite subFV_subBV; auto.
  - split.
    + intros t th. revert t. induction th as [|x v th' IH]; intros t Hlc j w.
      * reflexivity.
      * simpl. unfold LCsubst in Hlc. simpl in Hlc. destruct Hlc as [Hv Hlc].
        rewrite tsubFV_tsubBV; auto.
    + intros ps th. revert ps. induction th as [|x v th' IH]; intros ps Hlc j w.
      * reflexivity.
      * simpl. unfold LCsubst in Hlc. simpl in Hlc. destruct Hlc as [Hv Hlc].
        rewrite psubFV_psubBV; auto.
Qed.

Lemma csubst_subBV : forall e th, LCsubst th -> forall j w,
  csubst th (subBV_at j w e) = subBV_at j (csubst th w) (csubst th e).
Proof. intros; apply (proj1 csubst_subBV_gen); auto. Qed.
Lemma ctsubst_tsubBV : forall t th, LCsubst th -> forall j w,
  ctsubst th (tsubBV_at j w t) = tsubBV_at j (csubst th w) (ctsubst th t).
Proof. intros; apply (proj1 (proj2 csubst_subBV_gen)); auto. Qed.
Lemma cpsubst_psubBV : forall ps th, LCsubst th -> forall j w,
  cpsubst th (psubBV_at j w ps) = psubBV_at j (csubst th w) (cpsubst th ps).
Proof. intros; apply (proj2 (proj2 csubst_subBV_gen)); auto. Qed.

Lemma cpsubst_psubBV0 : forall ps th, LCsubst th -> forall w,
  cpsubst th (psubBV w ps) = psubBV (csubst th w) (cpsubst th ps).
Proof. intros. apply cpsubst_psubBV; auto. Qed.

Lemma ctsubst_tsubBV0 : forall t th, LCsubst th -> forall w,
  ctsubst th (tsubBV w t) = tsubBV (csubst th w) (ctsubst th t).
Proof. intros. apply ctsubst_tsubBV; auto. Qed.

Lemma isLCL_at_In : forall l j a, isLCL_at j l -> In a l -> isLC_at j a.
Proof.
  intros l. induction l as [|b l IH]; simpl; intros j a H Ha; [destruct Ha|].
  destruct H as [Hb Hl]. destruct Ha as [->|Ha]; auto.
Qed.

Lemma isLCL_map_gen : forall (f:expr->expr) l j,
  (forall a, In a l -> isLC_at j (f a)) -> isLCL_at j (map f l).
Proof.
  intros f l. induction l as [|a l IH]; intros j Hf; simpl.
  - exact I.
  - split.
    + apply Hf. left; auto.
    + apply IH. intros b Hb. apply Hf. right; auto.
Qed.

Lemma isLCL_map : forall (f:expr->expr) l j, isLCL_at j l ->
  (forall a, In a l -> isLC_at j (f a)) -> isLCL_at j (map f l).
Proof. intros; apply isLCL_map_gen; auto. Qed.

(* ============ LC under substitution ============ *)
Lemma isLC_subFV_gen :
  (forall (e:expr) (j:nat), isLC_at j e -> forall x v, isLC v -> isLC_at j (subFV x v e)) /\
  (forall (t:type) (j:nat), isLCT_at j t -> forall x v, isLC v -> isLCT_at j (tsubFV x v t)) /\
  (forall (ps:preds) (j:nat), isLCP_at j ps -> forall x v, isLC v -> isLCP_at j (psubFV x v ps)).
Proof.
  refine (syntax_mutind'
    (fun e => forall j, isLC_at j e -> forall x v, isLC v -> isLC_at j (subFV x v e))
    (fun t => forall j, isLCT_at j t -> forall x v, isLC v -> isLCT_at j (tsubFV x v t))
    (fun ps => forall j, isLCP_at j ps -> forall x v, isLC v -> isLCP_at j (psubFV x v ps))
    _ _ _ _ _ _ _ _ _ _ _ _ _).
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn. intros y j Ht x v Hv. cbn. destruct (x =? y) eqn:E.
    + apply isLC_at_mono with (j:=0); [lia|auto].
    + exact I.
  - cbn; intros o e IH j H x v Hv. cbn. apply IH; auto.
  - cbn; intros o e1 IH1 e2 IH2 j H x v Hv. cbn. destruct H as [H1 H2]; split; auto.
  - cbn; intros e1 IH1 m e2 IH2 j H x v Hv. cbn. destruct H as [H1 H2]; split; auto.
  - cbn; intros e IH f j H x v Hv. cbn. apply IH; auto.
  - intros c l HF j H x v Hv.
    change (isLCL_at j l) in H.
    rewrite sFV_New. rewrite Forall_forall in HF.
    apply isLCL_map_gen. intros a Ha. exact (HF a Ha j (isLCL_at_In l j a H Ha) x v Hv).
  - cbn; intros e1 IH1 e2 IH2 j H x v Hv. cbn. destruct H as [H1 H2]; split; auto.
  - cbn. intros b ps IH j H x v Hv. cbn. apply IH; auto.
  - cbn; auto.
  - cbn. intros p IHp ps IHps j H x v Hv. cbn. destruct H as [H1 H2]; split; auto.
Qed.

Lemma isLC_subFV : forall e j, isLC_at j e -> forall x v, isLC v -> isLC_at j (subFV x v e).
Proof. intros; apply (proj1 isLC_subFV_gen); auto. Qed.
Lemma isLCP_subFV : forall ps j, isLCP_at j ps -> forall x v, isLC v -> isLCP_at j (psubFV x v ps).
Proof. intros; apply (proj2 (proj2 isLC_subFV_gen)); auto. Qed.
Lemma isLCT_subFV : forall t j, isLCT_at j t -> forall x v, isLC v -> isLCT_at j (tsubFV x v t).
Proof. intros; apply (proj1 (proj2 isLC_subFV_gen)); auto. Qed.

Lemma isLC_subBV_at_gen :
  (forall (e:expr) (j:nat), isLC_at (S j) e -> forall w, isLC w -> isLC_at j (subBV_at j w e)) /\
  (forall (t:type) (j:nat), isLCT_at (S j) t -> forall w, isLC w -> isLCT_at j (tsubBV_at j w t)) /\
  (forall (ps:preds) (j:nat), isLCP_at (S j) ps -> forall w, isLC w -> isLCP_at j (psubBV_at j w ps)).
Proof.
  refine (syntax_mutind'
    (fun e => forall j, isLC_at (S j) e -> forall w, isLC w -> isLC_at j (subBV_at j w e))
    (fun t => forall j, isLCT_at (S j) t -> forall w, isLC w -> isLCT_at j (tsubBV_at j w t))
    (fun ps => forall j, isLCP_at (S j) ps -> forall w, isLC w -> isLCP_at j (psubBV_at j w ps))
    _ _ _ _ _ _ _ _ _ _ _ _ _).
  - cbn; auto.
  - cbn; auto.
  - cbn. intros i j H w Hw. destruct (j =? i) eqn:E.
    + apply Nat.eqb_eq in E; subst. exact (isLC_at_mono w 0 i (Nat.le_0_l i) Hw).
    + apply Nat.eqb_neq in E. simpl. lia.
  - cbn; auto.
  - cbn; intros o e IH j H w Hw. cbn. apply IH; auto.
  - cbn; intros o e1 IH1 e2 IH2 j H w Hw. cbn. destruct H as [H1 H2]; split; auto.
  - cbn; intros e1 IH1 m e2 IH2 j H w Hw. cbn. destruct H as [H1 H2]; split; auto.
  - cbn; intros e IH f j H w Hw. cbn. apply IH; auto.
  - intros c l HF j H w Hw.
    change (isLCL_at (S j) l) in H.
    rewrite sBV_New. rewrite Forall_forall in HF.
    apply isLCL_map_gen. intros a Ha. exact (HF a Ha j (isLCL_at_In l (S j) a H Ha) w Hw).
  - cbn. intros e1 IH1 e2 IH2 j H w Hw. cbn. destruct H as [H1 H2]; split.
    + apply IH1; auto. + apply IH2; auto.
  - cbn. intros b ps IH j H w Hw. cbn. apply IH; auto.
  - cbn; auto.
  - cbn. intros p IHp ps IHps j H w Hw. cbn. destruct H as [H1 H2]; split; auto.
Qed.

Lemma isLC_subBV_at : forall e j, isLC_at (S j) e -> forall w, isLC w -> isLC_at j (subBV_at j w e).
Proof. intros; apply (proj1 isLC_subBV_at_gen); auto. Qed.

Lemma isLC_psubBV : forall ps, isLCP_at 1 ps -> forall w, isLC w -> isLCP (psubBV w ps).
Proof.
  intros ps H w Hw. unfold isLCP, psubBV.
  apply (proj2 (proj2 isLC_subBV_at_gen)); auto.
Qed.

Lemma isLC_csubst_gen :
  (forall (e:expr) (th:csub), LCsubst th -> isLC e -> isLC (csubst th e)) /\
  (forall (t:type) (th:csub), LCsubst th -> isLCT t -> isLCT (ctsubst th t)) /\
  (forall (ps:preds) (th:csub), LCsubst th -> isLCP ps -> isLCP (cpsubst th ps)).
Proof.
  split.
  - intros e th. revert e. induction th as [|x v th IH]; intros e Hlc He.
    + simpl; auto.
    + unfold LCsubst in Hlc; simpl in Hlc. destruct Hlc as [Hv Hlc].
      simpl. apply IH; auto. apply isLC_subFV; auto.
  - split.
    + intros t th. revert t. induction th as [|x v th IH]; intros t Hlc Ht.
      * simpl; auto.
      * unfold LCsubst in Hlc; simpl in Hlc. destruct Hlc as [Hv Hlc].
        destruct t as [b ps]. unfold isLCT in Ht. simpl in Ht.
        simpl. apply IH; auto.
        unfold isLCT. simpl. apply isLCP_subFV; auto.
    + intros ps th. revert ps. induction th as [|x v th IH]; intros ps Hlc Hp.
      * simpl; auto.
      * unfold LCsubst in Hlc; simpl in Hlc. destruct Hlc as [Hv Hlc].
        unfold isLCP in Hp. simpl. apply IH; auto.
        unfold isLCP. apply isLCP_subFV; auto.
Qed.

(* ============ evaluation: basic closure properties ============ *)
Lemma EvalsTo_trans : forall a b c, EvalsTo a b -> EvalsTo b c -> EvalsTo a c.
Proof.
  intros a b c H. induction H as [|e1 e2 e3 Hstep _ IH]; intros Hbc.
  - exact Hbc.
  - eapply AddStep; eauto.
Qed.

Lemma EvalsTo_unop : forall o a b, EvalsTo a b -> EvalsTo (ExpUnOp o a) (ExpUnOp o b).
Proof.
  intros o a b H. induction H as [|e1 e2 e3 Hstep _ IH].
  - apply Refl.
  - eapply AddStep with (e2 := ExpUnOp o e2).
    + apply EUnOp1; exact Hstep.
    + exact IH.
Qed.

Lemma EvalsTo_binop_l : forall o a b c, EvalsTo a b -> EvalsTo (ExpBinOp o a c) (ExpBinOp o b c).
Proof.
  intros o a b c H. induction H as [|e1 e2 e3 Hstep _ IH].
  - apply Refl.
  - eapply AddStep with (e2 := ExpBinOp o e2 c).
    + apply EBinOp1; exact Hstep.
    + exact IH.
Qed.

Lemma EvalsTo_binop_r : forall o a b c, isValue a -> EvalsTo b c -> EvalsTo (ExpBinOp o a b) (ExpBinOp o a c).
Proof.
  intros o a b c Hv H. induction H as [|e1 e2 e3 Hstep _ IH].
  - apply Refl.
  - eapply AddStep with (e2 := ExpBinOp o a e2).
    + apply EBinOp2 with (v:=a); auto.
    + exact IH.
Qed.

Lemma EvalsTo_field : forall a b f, EvalsTo a b -> EvalsTo (ExpFieldAccess a f) (ExpFieldAccess b f).
Proof.
  intros a b f H. induction H as [|e1 e2 e3 Hstep _ IH].
  - apply Refl.
  - eapply AddStep with (e2 := ExpFieldAccess e2 f).
    + apply RefRC_Field; exact Hstep.
    + exact IH.
Qed.

Lemma EvalsTo_invok_l : forall a b m c, EvalsTo a b -> EvalsTo (ExpMethodInvoc a m c) (ExpMethodInvoc b m c).
Proof.
  intros a b m c H. induction H as [|e1 e2 e3 Hstep _ IH].
  - apply Refl.
  - eapply AddStep with (e2 := ExpMethodInvoc e2 m c).
    + apply Refc_Invok1; exact Hstep.
    + exact IH.
Qed.

Lemma EvalsTo_invok_r : forall a b m c, isValue a -> EvalsTo b c -> EvalsTo (ExpMethodInvoc a m b) (ExpMethodInvoc a m c).
Proof.
  intros a b m c Hv H. induction H as [|e1 e2 e3 Hstep _ IH].
  - apply Refl.
  - eapply AddStep with (e2 := ExpMethodInvoc a m e2).
    + apply Refc_Invok2 with (v:=a); auto.
    + exact IH.
Qed.

Lemma EvalsTo_let_l : forall a b e, EvalsTo a b -> EvalsTo (ExpLet a e) (ExpLet b e).
Proof.
  intros a b e H. induction H as [|e1 e2 e3 Hstep _ IH].
  - apply Refl.
  - eapply AddStep with (e2 := ExpLet e2 e).
    + apply ELet; exact Hstep.
    + exact IH.
Qed.

(* ============ list replacement & extensionality ============ *)
Lemma length_replace : forall {A} (l:list A) i v, length (replace l i v) = length l.
Proof. induction l as [|a l IH]; intros i v; destruct i as [|i]; simpl; auto. Qed.

Lemma nth_error_replace_eq : forall {A} (l:list A) i v, i < length l ->
  nth_error (replace l i v) i = Some v.
Proof.
  induction l as [|a l IH]; intros i v Hi; destruct i as [|i]; simpl in *.
  - lia.
  - lia.
  - reflexivity.
  - apply IH; lia.
Qed.

Lemma nth_error_replace_neq : forall {A} (l:list A) i j v, i <> j ->
  nth_error (replace l i v) j = nth_error l j.
Proof.
  induction l as [|a l IH]; intros i j v Hij.
  - destruct i, j; simpl; auto.
  - destruct i as [|i], j as [|j]; simpl in *.
    + exfalso; apply Hij; reflexivity.
    + reflexivity.
    + reflexivity.
    + apply IH; auto.
Qed.

Lemma nth_error_ext : forall {A} (l1 l2:list A), length l1 = length l2 ->
  (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  induction l1 as [|a1 l1 IH]; intros l2 Hlen Hn.
  - destruct l2; simpl in *; auto; discriminate.
  - destruct l2 as [|a2 l2]; simpl in *; [discriminate|]. f_equal.
    + specialize (Hn 0); simpl in Hn. injection Hn as ->. reflexivity.
    + apply IH; [lia|]. intro i. specialize (Hn (S i)); simpl in Hn. exact Hn.
Qed.

Lemma Forall2_nth_Some_all : forall {A B} (P:A->B->Prop) l1 l2,
  length l1 = length l2 ->
  (forall i a, nth_error l1 i = Some a -> exists b, nth_error l2 i = Some b /\ P a b) ->
  Forall2 P l1 l2.
Proof.
  induction l1 as [|a1 l1 IH]; intros l2 Hlen H.
  - destruct l2; simpl in *; auto; discriminate.
  - destruct l2 as [|a2 l2]; simpl in *; [discriminate|].
    constructor.
    + destruct (H 0 a1) as [b0 [Hb HP]]; auto. simpl in Hb. injection Hb as ->. auto.
    + apply IH; [lia|]. intros i a Ha.
      destruct (H (S i) a) as [b0 [Hb HP]]; auto. simpl in Hb. exact (ex_intro _ b0 (conj Hb HP)).
Qed.

(* ============ evaluation of new arguments ============ *)
Lemma EvalsTo_new_arg : forall c es es' i a b,
  length es = length es' ->
  (forall j, j <> i -> nth_error es j = nth_error es' j) ->
  nth_error es i = Some a -> nth_error es' i = Some b ->
  EvalsTo a b -> EvalsTo (ExpNew c es) (ExpNew c es').
Proof.
  intros c es es' i a b Hlen Hoth Ha Hb H.
  revert es es' i Hlen Hoth Ha Hb.
  induction H as [|x y z Hstep Htail IH].
  - intros es es' i Hlen Hoth Ha Hb.
    assert (es = es') as ->.
    { apply nth_error_ext; auto. intro j. destruct (Nat.eq_dec j i) as [->|Hne].
      - rewrite Ha, Hb. reflexivity.
      - rewrite Hoth; auto. }
    apply Refl.
  - intros es es' i Hlen Hoth Ha Hb.
    assert (Hi : i < length es) by (apply nth_error_Some; rewrite Ha; discriminate).
    assert (Hib : i < length es') by lia.
    eapply AddStep with (e2 := ExpNew c (replace es' i y)).
    + apply RefRC_New_Arg with (ei := x) (ei' := y) (i := i) (es := es) (es' := replace es' i y).
      * exact Hstep.
      * exact Ha.
      * apply nth_error_replace_eq; lia.
      * intros j Hj. rewrite (nth_error_replace_neq es' i j y (fun H => Hj (eq_sym H))). apply Hoth; auto.
      * rewrite length_replace. lia.
    + eapply IH.
      * rewrite length_replace. auto.
      * intros j Hj. apply nth_error_replace_neq. intro H; apply Hj; symmetry; exact H.
      * apply nth_error_replace_eq; lia.
      * exact Hb.
Qed.

Lemma EvalsTo_new_head : forall c a a' l, EvalsTo a a' ->
  EvalsTo (ExpNew c (a::l)) (ExpNew c (a'::l)).
Proof.
  intros c a a' l H.
  induction H as [|x y z Hstep Htail IH].
  - apply Refl.
  - eapply AddStep with (e2 := ExpNew c (y::l)).
    + apply RefRC_New_Arg with (ei := x) (ei' := y) (i := 0) (es := x::l) (es' := y::l).
      * exact Hstep.
      * reflexivity.
      * reflexivity.
      * intros j Hj. destruct j; [contradiction|reflexivity].
      * reflexivity.
    + exact IH.
Qed.

Lemma EvalsTo_new_prefix : forall c pre l l',
  (forall i a, nth_error l i = Some a -> exists b, nth_error l' i = Some b /\ EvalsTo a b) ->
  length l = length l' ->
  EvalsTo (ExpNew c (pre ++ l)) (ExpNew c (pre ++ l')).
Proof.
  intros c pre l. revert pre. induction l as [|a l IH]; intros pre l' Hpt Hlen.
  - destruct l' as [|b l']; simpl in *; [apply Refl|discriminate].
  - destruct l' as [|b l']; simpl in *; [discriminate|].
    assert (Hab : EvalsTo a b).
    { destruct (Hpt 0 a) as [b' [Hb' HP]]; auto. simpl in Hb'. injection Hb' as ->. auto. }
    assert (Hpt' : forall i a0, nth_error l i = Some a0 -> exists b0, nth_error l' i = Some b0 /\ EvalsTo a0 b0).
    { intros i a0 Ha0. destruct (Hpt (S i) a0) as [b0 [Hb0 HP]]; auto. simpl in Hb0. exact (ex_intro _ b0 (conj Hb0 HP)). }
    assert (Hlen' : length l = length l') by lia.
    eapply EvalsTo_trans with (b := ExpNew c (pre ++ b :: l)).
    + apply EvalsTo_new_arg with (i := length pre) (a := a) (b := b).
      * rewrite length_app, length_app. simpl. lia.
      * intros j Hj. destruct (Nat.lt_ge_cases j (length pre)) as [Hlt|Hge].
        -- rewrite nth_error_app1 by lia. rewrite nth_error_app1 by lia. reflexivity.
        -- rewrite nth_error_app2 by lia. rewrite nth_error_app2 by lia.
           assert (Heq : j - length pre = S (j - length pre - 1)) by lia. rewrite Heq. reflexivity.
      * rewrite nth_error_app2 by lia. assert (Heq : length pre - length pre = 0) by lia. rewrite Heq. reflexivity.
      * rewrite nth_error_app2 by lia. assert (Heq : length pre - length pre = 0) by lia. rewrite Heq. reflexivity.
      * exact Hab.
    + assert (Hass : pre ++ b :: l = (pre ++ (b :: nil)) ++ l) by (rewrite <- app_assoc; reflexivity).
      assert (Hass' : pre ++ b :: l' = (pre ++ (b :: nil)) ++ l') by (rewrite <- app_assoc; reflexivity).
      rewrite Hass, Hass'. apply IH; auto.
Qed.

Lemma EvalsTo_new_Forall2 : forall c l l', Forall2 EvalsTo l l' ->
  EvalsTo (ExpNew c l) (ExpNew c l').
Proof.
  intros c l l' H. induction H as [|a a' l l' Ha Hl IH].
  - apply Refl.
  - change (EvalsTo (ExpNew c (nil ++ a :: l)) (ExpNew c (nil ++ a' :: l'))).
    eapply EvalsTo_new_prefix.
    + intros i a0 Ha0. destruct i as [|i]; simpl in *.
      * injection Ha0 as ->. exists a'. split; [reflexivity|exact Ha].
      * destruct (Forall2_nth_error_some EvalsTo l l' i a0 Hl Ha0) as [b [Hb HP]]. exists b; auto.
    + simpl. f_equal. apply Forall2_length with (P:=EvalsTo); exact Hl.
Qed.


Lemma Step_New_inv : forall c es e', Step (ExpNew c es) e' ->
  exists es', e' = ExpNew c es' /\ length es = length es' /\
    exists i ei ei', Step ei ei' /\ nth_error es i = Some ei /\ nth_error es' i = Some ei' /\
      (forall j, j <> i -> nth_error es j = nth_error es' j).
Proof.
  intros c es e' H.
  inversion H as [| | | | | | | | C Fs fi ei i HF HnthF HnthE Hval | e0 e0' f Hst | C ei' es1 es1' ei i Hsti HnE HnE' Hoth Hlen | | ]; subst.
  eauto 14.
Qed.

Lemma EvalsTo_new_inv : forall c es z,
  EvalsTo (ExpNew c es) z ->
  exists es', z = ExpNew c es' /\ length es = length es' /\
    (forall i a, nth_error es i = Some a -> exists b, nth_error es' i = Some b /\ EvalsTo a b).
Proof.
  intros c es z H.
  remember (ExpNew c es) as X eqn:EX.
  revert es EX.
  induction H as [|x y z0 Hstep Htail IH]; intros es EX.
  - subst e. exists es; split; [reflexivity|split; [reflexivity|]].
    intros i a Ha; exists a; split; [exact Ha|apply Refl].
  - subst x.
    destruct (Step_New_inv c es y Hstep) as [ys [-> [Hlen [i [ei [ei' [Hsti [HnE [HnE' Hoth]]]]]]]]].
    destruct (IH ys eq_refl) as [zs [-> [Hlen2 Hpt]]].
    exists zs; split; [reflexivity|split; [lia|]].
    intros j a Ha.
    destruct (Nat.eq_dec j i) as [->|Hne].
    + rewrite HnE in Ha; injection Ha as ->.
      destruct (Hpt i ei') as [b0 [Hb HP]]; auto.
      exists b0; split; auto.
      eapply EvalsTo_trans; [|exact HP].
      eapply AddStep; [exact Hsti|apply Refl].
    + rewrite (Hoth j Hne) in Ha.
      destruct (Hpt j a) as [b0 [Hb HP]]; auto.
Qed.

Lemma subBV_unfold : forall v e, subBV v e = subBV_at 0 v e.
Proof. reflexivity. Qed.

(* ============ properties of Denotes ============ *)
Lemma Drefn_gen : forall t v, Denotes t v -> forall b ps, t = TRefn b ps -> PEvalsTrue (psubBV v ps).
Proof.
  intros t v Hd.
  refine (Denotes_ind
    (fun t v => forall b ps, t = TRefn b ps -> PEvalsTrue (psubBV v ps))
    _ _ _ _ t v Hd).
  - intros psc i HP b0 ps0 Heq. injection Heq as Hb Hp. subst. exact HP.
  - intros psc bol HP b0 ps0 Heq. injection Heq as Hb Hp. subst. exact HP.
  - intros psc c es Fs Hval HP HFs HF b0 ps0 Heq. injection Heq as Hb Hp. subst. exact HP.
  - intros b1 b2 psc v0 Hrec IH FJ b0 ps0 Heq. injection Heq as Hb Hp.
    apply IH with (b:=b1) (ps:=ps0). rewrite Hp. reflexivity.
Qed.

Lemma Denotes_refn : forall b ps v, Denotes (TRefn b ps) v -> PEvalsTrue (psubBV v ps).
Proof. intros. eapply Drefn_gen; eauto. Qed.

Lemma Denotes_isValue : forall t v, Denotes t v -> isValue v.
Proof.
  intros t v Hd.
  refine (Denotes_ind (fun t v => isValue v) _ _ _ _ t v Hd); simpl; eauto.
Qed.

Lemma Dimpl_gen : forall t v, Denotes t v -> forall b ps qs, t = TRefn b ps ->
  (PEvalsTrue (psubBV v ps) -> PEvalsTrue (psubBV v qs)) -> Denotes (TRefn b qs) v.
Proof.
  intros t v Hd.
  refine (Denotes_ind
    (fun t v => forall b ps qs, t = TRefn b ps ->
       (PEvalsTrue (psubBV v ps) -> PEvalsTrue (psubBV v qs)) -> Denotes (TRefn b qs) v)
    _ _ _ _ t v Hd).
  - intros psc i HP b0 ps0 qs Heq Himp. injection Heq as Hb Hp. subst.
    apply DenotesInt. apply Himp. exact HP.
  - intros psc bol HP b0 ps0 qs Heq Himp. injection Heq as Hb Hp. subst.
    apply DenotesBool. apply Himp. exact HP.
  - intros psc c es Fs Hval HP HFs HF b0 ps0 qs Heq Himp. injection Heq as Hb Hp. subst.
    eapply DenotesClass; eauto.
  - intros b1 b2 psc v0 Hrec IH FJ b0 ps0 qs Heq Himp. injection Heq as Hb Hp.
    eapply DenotesUpcast.
    + apply IH with (b:=b1) (ps:=ps0) (qs:=qs).
      * rewrite Hp. reflexivity.
      * exact Himp.
    + rewrite <- Hb. exact FJ.
Qed.

Lemma Denotes_impl : forall b ps qs v,
  (PEvalsTrue (psubBV v ps) -> PEvalsTrue (psubBV v qs)) ->
  Denotes (TRefn b ps) v -> Denotes (TRefn b qs) v.
Proof. intros. eapply Dimpl_gen; eauto. Qed.

Lemma Denotes_drop : forall b ps v, Denotes (TRefn b ps) v -> Denotes (TRefn b PEmpty) v.
Proof. intros. apply Denotes_impl with (ps:=ps). intros _. apply PEEmp. exact H. Qed.

(* veq is reflexive on values *)
Lemma veqL_self_gen : forall l,
  (forall a, In a l -> isValue a -> veq a a = true) -> isValueL l ->
  (fix ff (es1' es2':[expr]) :=
     match es1' with
     | nil => (match es2' with nil => true | _ => false end)
     | e1 :: es1'' => (match es2' with nil => false | e2 :: es2'' => andb (veq e1 e2) (ff es1'' es2'') end)
     end) l l = true.
Proof.
  induction l as [|a l IH]; simpl; intros Hpt H.
  - reflexivity.
  - destruct H as [Ha Hl]. rewrite (IH (fun b Hb => Hpt b (or_intror Hb)) Hl).
    rewrite andb_true_iff. split; [apply Hpt; auto | reflexivity].
Qed.

Lemma veq_self : forall v, isValue v -> veq v v = true.
Proof.
  refine (proj1 (syntax_mutind' (fun e => isValue e -> veq e e = true)
    (fun (_:type) => True) (fun (_:preds) => True) _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - cbn. intros b H. destruct b; reflexivity.
  - cbn. intros n H. apply Z.eqb_refl.
  - cbn; intros i H; destruct H.
  - cbn; intros x H; destruct H.
  - cbn; intros o e IH H; destruct H.
  - cbn; intros o e1 IH1 e2 IH2 H; destruct H.
  - cbn; intros e1 IH1 m e2 IH2 H; destruct H.
  - cbn; intros e IH f H; destruct H.
  - cbn. intros c l HF H. rewrite Nat.eqb_refl. simpl.
    rewrite Forall_forall in HF.
    apply veqL_self_gen.
    + intros a Ha Ha'. apply HF; auto.
    + auto.
  - cbn; intros e1 IH1 e2 IH2 H; destruct H.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma EvalsTo_Eq_self : forall v, isValue v -> EvalsTo (ExpBinOp Eq v v) (Bc true).
Proof.
  intros v Hv.
  assert (Hstep : Step (ExpBinOp Eq v v) (Bc true)).
  { assert (Hb : bdelta Eq v v (isCpt_Eq v v Hv Hv) = Bc true).
    { change (Bc (veq v v) = Bc true). apply f_equal. apply veq_self; auto. }
    rewrite <- Hb. apply EBinOp3 with (pf := isCpt_Eq v v Hv Hv); auto. }
  eapply AddStep; [exact Hstep | apply Refl].
Qed.

Lemma EvalsTo_Eq_true : forall E v, EvalsTo E v -> isValue v -> EvalsTo (ExpBinOp Eq E v) (Bc true).
Proof.
  intros E v HE Hv.
  eapply EvalsTo_trans with (b := ExpBinOp Eq v v).
  - apply EvalsTo_binop_l. exact HE.
  - apply EvalsTo_Eq_self; auto.
Qed.

Lemma subBV_eqlPred_LC : forall E v, isLC E -> subBV_at 0 v (eqlPred E) = ExpBinOp Eq E v.
Proof.
  intros E v Hlc. unfold eqlPred. simpl.
  rewrite subBV_at_LC; auto.
Qed.

Lemma Denotes_self_eq : forall b ps v E,
  isLC E -> Denotes (TRefn b ps) v -> EvalsTo E v ->
  Denotes (TRefn b (PCons (eqlPred E) ps)) v.
Proof.
  intros b ps v E Hlc Hd HE.
  apply Denotes_impl with (ps := ps).
  - intro HP. apply PECons.
    + rewrite subBV_eqlPred_LC; auto.
      apply EvalsTo_Eq_true; auto. apply Denotes_isValue in Hd; auto.
    + exact HP.
  - exact Hd.
Qed.

(* ============ freshness utilities ============ *)
Lemma list_max_ub : forall (s:names) x, In x s -> x <= list_max s.
Proof.
  intros s. induction s as [|a l IH]; intros x H; [destruct H|].
  simpl in *. destruct H as [->|H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; auto|apply Nat.le_max_r].
Qed.

Definition freshv (s:names) : vname := S (list_max s).

Lemma freshv_notin : forall s, ~ In (freshv s) s.
Proof. intros s H. pose proof (list_max_ub s (freshv s) H). unfold freshv in H0. lia. Qed.

Lemma notin_app_l : forall (a b:names) x, ~ In x (a ++ b) -> ~ In x a.
Proof. intros a b x H Hx. apply H. apply in_app_iff; auto. Qed.
Lemma notin_app_r : forall (a b:names) x, ~ In x (a ++ b) -> ~ In x b.
Proof. intros a b x H Hx. apply H. apply in_app_iff; auto. Qed.

(* ============ opening and csubst ============ *)
Lemma psubFV_openP : forall ps j y, ~ In y (fvP ps) ->
  forall v, psubFV y v (openP_at j y ps) = psubBV_at j v ps.
Proof. intros; apply (proj2 (proj2 subFV_open_gen)); auto. Qed.

Lemma tsubFV_openT : forall t j y, ~ In y (free t) ->
  forall v, tsubFV y v (openT_at j y t) = tsubBV_at j v t.
Proof. intros; apply (proj1 (proj2 subFV_open_gen)); auto. Qed.

Lemma csubst_open_at : forall e th y v j, LCsubst th -> isValue v -> ~ In y (fv e) ->
  csubst (CCons y v th) (open_at j y e) = subBV_at j v (csubst th e).
Proof.
  intros e th y v j Hlc Hv Hy.
  change (csubst th (subFV y v (open_at j y e)) = subBV_at j v (csubst th e)).
  rewrite subFV_open; auto.
  rewrite csubst_subBV; auto.
  rewrite csubst_value; auto.
Qed.

Lemma cpsubst_openP : forall ps th y v, LCsubst th -> isValue v -> ~ In y (fvP ps) ->
  cpsubst (CCons y v th) (openP_at 0 y ps) = psubBV v (cpsubst th ps).
Proof.
  intros ps th y v Hlc Hv Hy.
  change (cpsubst th (psubFV y v (openP_at 0 y ps)) = psubBV v (cpsubst th ps)).
  rewrite psubFV_openP; auto.
  rewrite cpsubst_psubBV; auto.
  rewrite csubst_value; auto.
Qed.

Lemma ctsubst_openT : forall t th y v, LCsubst th -> isValue v -> ~ In y (free t) -> isLCT t ->
  ctsubst (CCons y v th) (openT_at 0 y t) = ctsubst th t.
Proof.
  intros t th y v Hlc Hv Hy Ht. destruct t as [b ps].
  unfold isLCT in Ht. simpl in Ht.
  change (ctsubst th (tsubFV y v (openT_at 0 y (TRefn b ps))) = ctsubst th (TRefn b ps)).
  rewrite tsubFV_openT; auto.
  change (ctsubst th (TRefn b (psubBV_at 1 v ps)) = ctsubst th (TRefn b ps)).
  rewrite ctsubst_TRefn. rewrite ctsubst_TRefn.
  assert (Hps : psubBV_at 1 v ps = ps).
  { apply psubBV_at_lc. unfold isLCP_at. exact Ht. }
  rewrite Hps. reflexivity.
Qed.

(* ============ DenotesEnv facts ============ *)
Lemma DenotesEnv_LCsubst : forall g th, DenotesEnv g th -> LCsubst th.
Proof.
  intros g th H. induction H as [|g th x t v Hd IH Hnin HD].
  - exact I.
  - apply LCsubst_cons. split; auto.
    apply Denotes_isValue in HD. apply isValue_isLC; auto.
Qed.

(* ============ free variables survive substitution of unbound names ============ *)
Lemma In_subFV_gen :
  (forall (e:expr) (y x:vname) (v:expr), x <> y -> In x (fv e) -> In x (fv (subFV y v e))) /\
  (forall (t:type) (y x:vname) (v:expr), x <> y -> In x (free t) -> In x (free (tsubFV y v t))) /\
  (forall (ps:preds) (y x:vname) (v:expr), x <> y -> In x (fvP ps) -> In x (fvP (psubFV y v ps))).
Proof.
  refine (syntax_mutind'
    (fun e => forall y x v, x <> y -> In x (fv e) -> In x (fv (subFV y v e)))
    (fun t => forall y x v, x <> y -> In x (free t) -> In x (free (tsubFV y v t)))
    (fun ps => forall y x v, x <> y -> In x (fvP ps) -> In x (fvP (psubFV y v ps)))
    _ _ _ _ _ _ _ _ _ _ _ _ _).
  - cbn; intros; contradiction.
  - cbn; intros; contradiction.
  - cbn; intros; contradiction.
  - simpl. intros z y x v Hxy Hx.
    destruct (y =? z) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      apply In_singleton_iff in Hx. subst. exfalso; apply Hxy; auto.
    + simpl. apply In_singleton_iff in Hx. subst. apply In_singleton_iff; auto.
  - simpl. intros o e IH y x v Hxy Hx. simpl. apply IH; auto.
  - simpl. intros o e1 IH1 e2 IH2 y x v Hxy Hx. simpl.
    rewrite In_union_iff in Hx. destruct Hx as [Hx|Hx]; apply In_union_iff; [left|right]; auto.
  - simpl. intros e1 IH1 m e2 IH2 y x v Hxy Hx. simpl.
    rewrite In_union_iff in Hx. destruct Hx as [Hx|Hx]; apply In_union_iff; [left|right]; auto.
  - simpl. intros e IH f y x v Hxy Hx. simpl. apply IH; auto.
  - intros c l HF y x v Hxy Hx.
    rewrite sFV_New. change (In x (fvL (map (subFV y v) l))).
    change (In x (fvL l)) in Hx.
    rewrite fvL_mem in Hx. destruct Hx as [a [Ha Hxa]].
    rewrite fvL_mem. exists (subFV y v a). split.
    + clear HF. revert Ha. induction l as [|b l IHl]; simpl; intros Ha; auto.
      destruct Ha as [->|Ha]; [left|right]; auto.
    + rewrite Forall_forall in HF. apply HF; auto.
  - simpl. intros e1 IH1 e2 IH2 y x v Hxy Hx. simpl.
    rewrite In_union_iff in Hx. destruct Hx as [Hx|Hx]; apply In_union_iff; [left|right]; auto.
  - simpl. intros b ps IH y x v Hxy Hx. simpl. apply IH; auto.
  - simpl; intros; contradiction.
  - simpl. intros p IHp ps IHps y x v Hxy Hx. simpl.
    rewrite In_union_iff in Hx. destruct Hx as [Hx|Hx]; apply In_union_iff; [left|right]; auto.
Qed.

Lemma In_subFV : forall e y x v, x <> y -> In x (fv e) -> In x (fv (subFV y v e)).
Proof. intros; apply (proj1 In_subFV_gen); auto. Qed.
Lemma In_psubFV : forall ps y x v, x <> y -> In x (fvP ps) -> In x (fvP (psubFV y v ps)).
Proof. intros; apply (proj2 (proj2 In_subFV_gen)); auto. Qed.

Lemma fv_csubst_unbound : forall e th x,
  In x (fv e) -> ~ In x (bindsC th) -> In x (fv (csubst th e)).
Proof.
  intros e th. revert e. induction th as [|y v th IH]; intros e x Hx Hnin.
  - simpl. exact Hx.
  - change (In x (fv (csubst th (subFV y v e)))).
    assert (Hxne : x <> y).
    { intro Heq. apply Hnin. subst. unfold bindsC. apply set_add_iff. left; reflexivity. }
    assert (Htail : ~ In x (bindsC th)).
    { intro Hc. apply Hnin. unfold bindsC. apply set_add_iff. right; exact Hc. }
    apply IH.
    + apply In_subFV; auto.
    + exact Htail.
Qed.

Lemma fvL_empty_of_pt : forall l,
  (forall a, In a l -> fvfree a -> fv a = empty) -> fvfreeL l -> fvL l = empty.
Proof.
  intros l. induction l as [|a l IH]; intros Hpt H; simpl.
  - reflexivity.
  - destruct H as [Ha Hl]. rewrite (IH (fun b Hb => Hpt b (or_intror Hb)) Hl). simpl.
    apply Hpt; [left; reflexivity | exact Ha].
Qed.

Lemma fvL_map_subBV : forall l j w, isValue w ->
  (forall a, In a l -> isValue w -> fv (subBV_at j w a) = fv a) -> fvL (map (subBV_at j w) l) = fvL l.
Proof.
  intros l. induction l as [|a l IH]; intros j w Hw Hpt; simpl.
  - reflexivity.
  - rewrite (Hpt a (or_introl eq_refl) Hw), (IH j w Hw (fun b Hb => Hpt b (or_intror Hb))). reflexivity.
Qed.

(* ============ fvfree implies empty free variables ============ *)
Lemma fvfree_fv_empty_gen :
  (forall (e:expr), fvfree e -> fv e = empty) /\
  (forall (t:type), True) /\ (forall (ps:preds), True).
Proof.
  refine (syntax_mutind' (fun e => fvfree e -> fv e = empty)
    (fun (_:type) => True) (fun (_:preds) => True) _ _ _ _ _ _ _ _ _ _ _ _ _).
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn; intros x H; destruct H.
  - cbn; intros o e IH H; simpl. apply IH; auto.
  - cbn; intros o e1 IH1 e2 IH2 H; simpl. destruct H as [H1 H2].
    rewrite (IH1 H1), (IH2 H2). reflexivity.
  - cbn; intros e1 IH1 m e2 IH2 H; simpl. destruct H as [H1 H2].
    rewrite (IH1 H1), (IH2 H2). reflexivity.
  - cbn; intros e IH f H; simpl. apply IH; auto.
  - cbn; intros c l HF H. simpl.
    change (fvL l = empty).
    rewrite Forall_forall in HF.
    apply fvL_empty_of_pt; auto.
  - cbn; intros e1 IH1 e2 IH2 H; simpl. destruct H as [H1 H2].
    rewrite (IH1 H1), (IH2 H2). reflexivity.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma fvfree_fv_empty : forall e, fvfree e -> fv e = empty.
Proof. intros; apply (proj1 fvfree_fv_empty_gen); auto. Qed.

Lemma isValue_fv_empty : forall e, isValue e -> fv e = empty.
Proof. intros. apply fvfree_fv_empty. apply isValue_fvfree; auto. Qed.

(* ============ fv is unchanged by substituting values for bound variables ============ *)
Lemma fv_subBV_gen :
  (forall (e:expr) (j:nat) (w:expr), isValue w -> fv (subBV_at j w e) = fv e) /\
  (forall (t:type) (j:nat) (w:expr), isValue w -> free (tsubBV_at j w t) = free t) /\
  (forall (ps:preds) (j:nat) (w:expr), isValue w -> fvP (psubBV_at j w ps) = fvP ps).
Proof.
  refine (syntax_mutind'
    (fun e => forall j w, isValue w -> fv (subBV_at j w e) = fv e)
    (fun t => forall j w, isValue w -> free (tsubBV_at j w t) = free t)
    (fun ps => forall j w, isValue w -> fvP (psubBV_at j w ps) = fvP ps)
    _ _ _ _ _ _ _ _ _ _ _ _ _).
  - cbn; auto.
  - cbn; auto.
  - cbn. intros i j w Hw. destruct (j =? i) eqn:E.
    + simpl. apply isValue_fv_empty; auto.
    + reflexivity.
  - cbn; auto.
  - cbn; intros o e IH j w Hw; simpl. apply IH; auto.
  - cbn; intros o e1 IH1 e2 IH2 j w Hw; simpl. rewrite (IH1 j w Hw), (IH2 j w Hw). reflexivity.
  - cbn; intros e1 IH1 m e2 IH2 j w Hw; simpl. rewrite (IH1 j w Hw), (IH2 j w Hw). reflexivity.
  - cbn; intros e IH f j w Hw; simpl. apply IH; auto.
  - intros c l HF j w Hw.
    rewrite sBV_New. change (fvL (map (subBV_at j w) l) = fvL l).
    rewrite Forall_forall in HF.
    apply fvL_map_subBV; auto.
  - cbn; intros e1 IH1 e2 IH2 j w Hw; simpl. rewrite (IH1 j w Hw), (IH2 (j+1) w Hw). reflexivity.
  - cbn; intros b ps IH j w Hw; simpl. apply IH with (j:=j+1); auto.
  - cbn; auto.
  - cbn; intros p IHp ps IHps j w Hw; simpl. rewrite (IHp j w Hw), (IHps j w Hw). reflexivity.
Qed.

Lemma fv_subBV_at : forall e j w, isValue w -> fv (subBV_at j w e) = fv e.
Proof. intros; apply (proj1 fv_subBV_gen); auto. Qed.

Lemma fvP_psubBV : forall ps j w, isValue w -> fvP (psubBV_at j w ps) = fvP ps.
Proof. intros; apply (proj2 (proj2 fv_subBV_gen)); auto. Qed.

(* ============ free variables are preserved along evaluation ============ *)
Lemma isValueL_nth : forall l i a, isValueL l -> nth_error l i = Some a -> isValue a.
Proof.
  intros l i a Hl. apply isValueL_Forall in Hl. rewrite Forall_forall in Hl.
  intros Ha. apply Hl. eapply nth_error_In; eauto.
Qed.

Lemma fvL_empty_of_all : forall l, (forall a, In a l -> fv a = empty) -> fvL l = empty.
Proof.
  intros l H. induction l as [|a l IH]; simpl.
  - reflexivity.
  - rewrite (H a (or_introl eq_refl)), (IH (fun b Hb => H b (or_intror Hb))). reflexivity.
Qed.

Lemma isValueL_fv_empty : forall l, isValueL l -> fvL l = empty.
Proof.
  intros l H. apply fvL_empty_of_all. intros a Ha.
  apply isValue_fv_empty. apply isValueL_Forall in H. rewrite Forall_forall in H. apply H; auto.
Qed.

Lemma Step_fv_subset : forall e e', Step e e' -> forall x, In x (fv e) -> In x (fv e').
Proof.
  intros e e' H.
  induction H as
    [ c e0 e0' Hst
    | c w pf Hv
    | c e0 e0' e1 Hst
    | c e0 e0' v Hv Hst
    | c v1 v2 pf Hv1 Hv2
    | m e1 e2 e1' Hst
    | m v e0 e0' Hv Hst
    | C e0 m v es Hbody Hv HvalNew
    | C Fs es fi ei i HFs HnthF HnthE Hval
    | e0 e0' f Hst
    | C ei' es es' ei i Hst IHn HnE HnE' Hoth Hlen
    | e_x e_x' e0 Hst
    | v e0 Hv ].
  all: intros x Hx.
  - simpl in *. apply IHHst; auto.
  - simpl in *. apply isValue_fv_empty in Hv. rewrite Hv in Hx. destruct Hx.
  - simpl in *. rewrite In_union_iff in Hx. destruct Hx as [Hx|Hx].
    + rewrite In_union_iff. left. apply IHHst; auto.
    + rewrite In_union_iff. right; auto.
  - simpl in *. rewrite In_union_iff in Hx. destruct Hx as [Hx|Hx].
    + rewrite In_union_iff. left; auto.
    + rewrite In_union_iff. right. apply IHHst; auto.
  - simpl in *. rewrite In_union_iff in Hx. destruct Hx as [Hx|Hx].
    + apply isValue_fv_empty in Hv1. rewrite Hv1 in Hx. destruct Hx.
    + apply isValue_fv_empty in Hv2. rewrite Hv2 in Hx. destruct Hx.
  - simpl in *. rewrite In_union_iff in Hx. destruct Hx as [Hx|Hx].
    + rewrite In_union_iff. left. apply IHHst; auto.
    + rewrite In_union_iff. right; auto.
  - simpl in *. rewrite In_union_iff in Hx. destruct Hx as [Hx|Hx].
    + rewrite In_union_iff. left; auto.
    + rewrite In_union_iff. right. apply IHHst; auto.
  - simpl in *. rewrite In_union_iff in Hx. destruct Hx as [Hx|Hx].
    + change (In x (fvL es)) in Hx. apply isValueL_fv_empty in HvalNew. rewrite HvalNew in Hx. destruct Hx.
    + apply isValue_fv_empty in Hv. rewrite Hv in Hx. destruct Hx.
  - simpl in *. change (In x (fvL es)) in Hx. apply isValueL_fv_empty in Hval. rewrite Hval in Hx. destruct Hx.
  - simpl in *. apply IHHst; auto.
  - simpl in *. rewrite fvL_mem in Hx. destruct Hx as [a0 [Ha0 Hx0]].
    apply In_nth_error in Ha0. destruct Ha0 as [j Hj].
    change (In x (fvL es')). apply fvL_mem. destruct (Nat.eq_dec j i) as [->|Hne].
    + rewrite HnE in Hj. injection Hj as ->.
      exists ei'. split; [apply nth_error_In with (n:=i); exact HnE'|]. apply IHn; auto.
    + exists a0. split.
      * apply nth_error_In with (n:=j). rewrite <- (Hoth j Hne). exact Hj.
      * exact Hx0.
  - simpl in *. rewrite In_union_iff in Hx. destruct Hx as [Hx|Hx].
    + rewrite In_union_iff. left. apply IHHst; auto.
    + rewrite In_union_iff. right; auto.
  - simpl in *. rewrite In_union_iff in Hx. destruct Hx as [Hx|Hx].
    + apply isValue_fv_empty in Hv. rewrite Hv in Hx. destruct Hx.
    + change (In x (fv (subBV_at 0 v e0))). rewrite (fv_subBV_at e0 0 v Hv). exact Hx.
Qed.

Lemma names_eq_nil : forall (s:names), (forall x, ~ In x s) -> s = nil.
Proof.
  intros s H. destruct s as [|a l].
  - reflexivity.
  - exfalso. apply (H a). left; reflexivity.
Qed.

Lemma EvalsTo_fv_empty : forall e v, EvalsTo e v -> isValue v -> fv e = empty.
Proof.
  intros e v H. induction H as [|e1 e2 e3 Hst Htail IH]; intros Hv.
  - apply isValue_fv_empty; auto.
  - assert (H3 : fv e2 = empty) by (apply IH; auto).
    assert (H4 : forall x, ~ In x (fv e1)).
    { intros x Hx. apply (Step_fv_subset e1 e2 Hst) in Hx. rewrite H3 in Hx.
      unfold empty, empty_set in Hx. simpl in Hx. exact Hx. }
    apply names_eq_nil. auto.
Qed.

(* ============ predicates with no free variables ============ *)
Lemma PEvalsTrue_fvP_empty : forall ps, PEvalsTrue ps -> fvP ps = empty.
Proof.
  intros ps H. induction H as [|p ps HE HP IH].
  - reflexivity.
  - simpl. rewrite (EvalsTo_fv_empty p (Bc true) HE); [|simpl; auto].
    rewrite IH. reflexivity.
Qed.

Lemma Denotes_fvP_empty : forall b ps v, Denotes (TRefn b ps) v -> fvP ps = empty.
Proof.
  intros b ps v Hd.
  assert (Hv : isValue v) by (apply Denotes_isValue in Hd; auto).
  assert (Hfv : fvP ps = empty).
  { rewrite <- (fvP_psubBV ps 0 v Hv). apply PEvalsTrue_fvP_empty.
    apply Denotes_refn in Hd; auto. }
  exact Hfv.
Qed.

Lemma DenotesEnv_bindsC_fwd : forall g th, DenotesEnv g th -> forall x, In x (bindsC th) -> in_env x g.
Proof.
  intros g th H. induction H as [|g th y t v Hd IH Hnin HD]; intros x Hx.
  - destruct Hx.
  - unfold in_env, binds. fold binds. unfold names_add. apply set_add_iff.
    unfold bindsC in Hx. fold bindsC in Hx. unfold names_add in Hx. rewrite set_add_iff in Hx.
    destruct Hx as [->|Hx]; [left; reflexivity|right; apply IH; auto].
Qed.

Lemma DenotesEnv_bindsC_bwd : forall g th, DenotesEnv g th -> forall x, in_env x g -> In x (bindsC th).
Proof.
  intros g th H. induction H as [|g th y t v Hd IH Hnin HD]; intros x Hx.
  - destruct Hx.
  - unfold in_env, Elem, binds in Hx. fold binds in Hx. unfold names_add in Hx. rewrite set_add_iff in Hx.
    destruct Hx as [->|Hx].
    + unfold bindsC. fold bindsC. unfold names_add. apply set_add_iff. left; reflexivity.
    + unfold bindsC. fold bindsC. unfold names_add. apply set_add_iff. right. apply IH; auto.
Qed.

Lemma fvP_csubst_unbound : forall ps th x,
  In x (fvP ps) -> ~ In x (bindsC th) -> In x (fvP (cpsubst th ps)).
Proof.
  intros ps. induction ps as [|p ps IH]; intros th x Hx Hnin.
  - unfold fvP in Hx. simpl in Hx. rewrite cpsubst_PEmpty. unfold fvP. simpl. exact Hx.
  - rewrite cpsubst_PCons. unfold fvP. fold fvP. rewrite In_union_iff.
    unfold fvP in Hx. fold fvP in Hx. rewrite In_union_iff in Hx.
    destruct Hx as [Hx|Hx].
    + left. apply fv_csubst_unbound; auto.
    + right. apply IH; auto.
Qed.

(* ============ environment / substitution correspondence ============ *)
Lemma DenotesEnv_bindsC : forall g th, DenotesEnv g th -> forall x, In x (bindsC th) <-> in_env x g.
Proof.
  intros g th H. induction H as [|g th x t v Hd IH Hnin HD].
  - intro y. unfold in_env. simpl. split; intros H; [destruct H|destruct H].
  - intro y. unfold in_env, Elem. unfold bindsC. fold bindsC. unfold binds. fold binds. unfold names_add.
    rewrite !set_add_iff. split; intros [H|H]; [left|right|left|right]; auto; apply IH in H; auto.
Qed.

(* ============ bound_in implies membership ============ *)
Lemma bound_in_in_env : forall x t g, bound_in x t g -> in_env x g.
Proof.
  intros x t g. induction g as [|y t_y g IH]; intros Hb.
  - destruct Hb.
  - destruct Hb as [[-> ->]|Hb].
    + unfold in_env, binds. fold binds. unfold names_add. apply set_add_iff. left; reflexivity.
    + unfold in_env, binds. fold binds. unfold names_add. apply set_add_iff. right. apply IH; auto.
Qed.

Lemma psubFV_empty_notin : forall ps, fvP ps = empty -> forall y, ~ In y (fvP ps).
Proof. intros ps H y Hy. rewrite H in Hy. unfold empty, empty_set in Hy. simpl in Hy. exact Hy. Qed.

Lemma tsubFV_notin_of_denotes : forall t th y v v',
  ~ In y (bindsC th) -> Denotes (ctsubst th t) v' -> tsubFV y v t = t.
Proof.
  intros t th y v v' Hnin HD. destruct t as [b ps]. rewrite ctsubst_TRefn in HD.
  assert (Hfv : fvP (cpsubst th ps) = empty).
  { exact (Denotes_fvP_empty b (cpsubst th ps) v' HD). }
  assert (Hy : ~ In y (fvP ps)).
  { intro Hyin.
    assert (Hcontra : In y (fvP (cpsubst th ps))) by (apply fvP_csubst_unbound; auto).
    rewrite Hfv in Hcontra. unfold empty, empty_set in Hcontra. simpl in Hcontra. exact Hcontra. }
  exact (tsubFV_notin (TRefn b ps) y Hy v).
Qed.

Lemma csubst_FV_self : forall y v th, isValue v -> csubst (CCons y v th) (FV y) = v.
Proof.
  intros y v th Hv. change (csubst th (subFV y v (FV y)) = v).
  simpl. rewrite Nat.eqb_refl. apply csubst_value; auto.
Qed.

Lemma csubst_FV_other : forall x y v th, x <> y -> csubst (CCons y v th) (FV x) = csubst th (FV x).
Proof.
  intros x y v th Hne. change (csubst th (subFV y v (FV x)) = csubst th (FV x)).
  simpl. destruct (y =? x) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply Hne; auto.
  - reflexivity.
Qed.

Lemma notin_bindsC_of_notin_env : forall g th y, DenotesEnv g th -> ~ in_env y g -> ~ In y (bindsC th).
Proof.
  intros g th y Hd Hnin Hc. apply Hnin. exact (DenotesEnv_bindsC_fwd g th Hd y Hc).
Qed.

Lemma DenotesEnv_lookup : forall g th, DenotesEnv g th ->
  forall x t, bound_in x t g ->
  exists v, Denotes (ctsubst th t) v /\ csubst th (FV x) = v.
Proof.
  intros g th H. induction H as [|g th y t_y v_y Hd IH Hnin HD].
  - intros x t Hb. destruct Hb.
  - intros x t Hb. destruct Hb as [[-> ->]|Hb].
    + exists v_y. split.
      * assert (Hnotin : ~ In y (bindsC th))
          by (exact (notin_bindsC_of_notin_env g th y Hd Hnin)).
        assert (Hteq : tsubFV y v_y t_y = t_y)
          by (exact (tsubFV_notin_of_denotes t_y th y v_y v_y Hnotin HD)).
        change (Denotes (ctsubst th (tsubFV y v_y t_y)) v_y).
        rewrite Hteq. exact HD.
      * apply csubst_FV_self. apply Denotes_isValue in HD; auto.
    + destruct (IH x t Hb) as [v [Hden Hxval]].
      exists v. split.
      * assert (Hnotin : ~ In y (bindsC th))
          by (exact (notin_bindsC_of_notin_env g th y Hd Hnin)).
        assert (Hteq : tsubFV y v_y t = t)
          by (exact (tsubFV_notin_of_denotes t th y v_y v Hnotin Hden)).
        change (Denotes (ctsubst th (tsubFV y v_y t)) v).
        rewrite Hteq. exact Hden.
      * assert (Hne : x <> y).
        { intro Heq. apply Hnin. rewrite <- Heq. exact (bound_in_in_env x t g Hb). }
        rewrite (csubst_FV_other x y v_y th Hne).
        exact Hxval.
Qed.

(* ============ fresh variable outside four sets ============ *)
Lemma fresh4_notin : forall (a b c d:names),
  let y := freshv (a ++ b ++ c ++ d) in
  ~ In y a /\ ~ In y b /\ ~ In y c /\ ~ In y d.
Proof.
  intros a b c d. simpl.
  assert (H : ~ In (freshv (a ++ b ++ c ++ d)) (a ++ b ++ c ++ d)) by apply freshv_notin.
  assert (H1 : ~ In (freshv (a ++ b ++ c ++ d)) (b ++ (c ++ d)))
    by (apply notin_app_r with (a:=a); exact H).
  assert (H2 : ~ In (freshv (a ++ b ++ c ++ d)) (c ++ d))
    by (apply notin_app_r with (a:=b); exact H1).
  assert (H3 : ~ In (freshv (a ++ b ++ c ++ d)) b)
    by (apply notin_app_l with (b:=c ++ d); exact H1).
  assert (H4 : ~ In (freshv (a ++ b ++ c ++ d)) a)
    by (apply notin_app_l with (b:=b ++ (c ++ d)); exact H).
  split; [exact H4|split; [exact H3|split]].
  - apply notin_app_l with (b:=d); exact H2.
  - apply notin_app_r with (a:=c); exact H2.
Qed.

Lemma LImplies_apply : forall g p q, LImplies g p q ->
  forall th, DenotesEnv g th -> PEvalsTrue (cpsubst th p) -> PEvalsTrue (cpsubst th q).
Proof. intros g p q H. destruct H as [g' p' q' Hf]. exact Hf. Qed.

Lemma Subtype_sound : forall g s t, Subtype g s t ->
  forall th, DenotesEnv g th -> forall v, Denotes (ctsubst th s) v -> Denotes (ctsubst th t) v.
Proof.
  intros g s t HS. dependent destruction HS.
  intros th Hd v HD.
  rewrite ctsubst_TRefn in HD. rewrite ctsubst_TRefn.
  set (y := freshv (nms ++ fvP p1 ++ fvP p2 ++ binds g)).
  assert (Hyres := fresh4_notin nms (fvP p1) (fvP p2) (binds g)).
  fold y in Hyres. destruct Hyres as [Hnms [Hfv1 [Hfv2 Hbinds]]].
  assert (HLC := DenotesEnv_LCsubst g th Hd).
  assert (Hv : isValue v) by (apply Denotes_isValue in HD; auto).
  assert (Heq1 : cpsubst (CCons y v th) (unbindP y p1) = psubBV v (cpsubst th p1))
    by (apply cpsubst_openP; auto).
  assert (Heq2 : cpsubst (CCons y v th) (unbindP y p2) = psubBV v (cpsubst th p2))
    by (apply cpsubst_openP; auto).
  assert (Hth : DenotesEnv (Cons y (TRefn b1 PEmpty) g) (CCons y v th)).
  { apply DExt.
    - exact Hd.
    - unfold in_env. exact Hbinds.
    - rewrite ctsubst_TRefn, cpsubst_PEmpty.
      apply Denotes_drop with (ps:=cpsubst th p1). exact HD. }
  assert (Himp : forall th', DenotesEnv (Cons y (TRefn b1 PEmpty) g) th' ->
      PEvalsTrue (cpsubst th' (unbindP y p1)) -> PEvalsTrue (cpsubst th' (unbindP y p2))).
  { exact (LImplies_apply _ _ _ (H0 y Hnms)). }
  assert (Hpre : PEvalsTrue (cpsubst (CCons y v th) (unbindP y p1))).
  { rewrite Heq1. apply Denotes_refn in HD. exact HD. }
  assert (Hpost : PEvalsTrue (psubBV v (cpsubst th p2))).
  { assert (Ht := Himp _ Hth Hpre). rewrite Heq2 in Ht. exact Ht. }
  apply DenotesUpcast with (b1:=b1).
  - apply Denotes_impl with (ps:=cpsubst th p1).
    + intros _. exact Hpost.
    + exact HD.
  - exact H.
Qed.

(* ============ step inversion lemmas ============ *)
Lemma Step_UnOp_inv : forall o e e', Step (ExpUnOp o e) e' ->
  (exists e0, Step e e0 /\ e' = ExpUnOp o e0) \/
  (exists (w:expr) (pf:isCompat o w), e = w /\ isValue w /\ e' = udelta o w pf).
Proof.
  intros o e e' H. remember (ExpUnOp o e) as X eqn:EX. revert o e EX.
  induction H as
    [ c e1 e1' Hst IH1 | c w pf Hval
    | c e1 e1' e2 Hst IH1 | c e1 e1' v Hval Hst IH1
    | c v1 v2 pf Hv1 Hv2
    | m e1 e2 e1' Hst IH1 | m v e1 e1' Hval Hst IH1
    | C e0 m v es Hbody Hvalv HvalNew
    | C Fs es fi ei i HFs HnF HnE Hval
    | e0 e0' f Hst IH1
    | C ei' es es' ei i Hst IH1 HnE HnE' Hoth Hlen
    | e_x e_x' e0 Hst IH1 | v e0 Hval ];
  intros ox ee EX.
  - injection EX as H; subst. left. exists e1'. split; [exact Hst|].
    destruct ox, c; reflexivity.
  - injection EX as H; subst. right. destruct ox, c.
    eexists. eexists. split; [reflexivity|split; auto].
  - discriminate EX. - discriminate EX. - discriminate EX. - discriminate EX.
  - discriminate EX. - discriminate EX. - discriminate EX. - discriminate EX.
  - discriminate EX. - discriminate EX. - discriminate EX.
Qed.

Lemma Step_BinOp_inv : forall o e1 e2 e',
  Step (ExpBinOp o e1 e2) e' ->
  (exists e0, Step e1 e0 /\ e' = ExpBinOp o e0 e2) \/
  (exists e0, isValue e1 /\ Step e2 e0 /\ e' = ExpBinOp o e1 e0) \/
  (exists (pf:isCompat2 o e1 e2), isValue e1 /\ isValue e2 /\ e' = bdelta o e1 e2 pf).
Proof.
  intros o e1 e2 e' H. remember (ExpBinOp o e1 e2) as X eqn:EX. revert o e1 e2 EX.
  induction H as
    [ c a a' Hst IH1 | c w pf Hval
    | c a a' a2 Hst IH1 | c a a' v Hval Hst IH1
    | c v1 v2 pf Hv1 Hv2
    | m a b a' Hst IH1 | m v a b Hval Hst IH1
    | C e0 m v es Hbody Hvalv HvalNew
    | C Fs es fi ei i HFs HnF HnE Hval
    | e0 e0' f Hst IH1
    | C ei' es es' ei i Hst IH1 HnE HnE' Hoth Hlen
    | e_x e_x' e0 Hst IH1 | v e0 Hval ];
  intros ox ax bx EX.
  - discriminate EX. - discriminate EX.
  - injection EX as Ho Ha Hb. subst. left. eauto.
  - injection EX as Ho Ha Hb. subst. right. left. eauto.
  - injection EX as Ho Ha Hb. subst. right. right. eauto.
  - discriminate EX. - discriminate EX. - discriminate EX. - discriminate EX.
  - discriminate EX. - discriminate EX. - discriminate EX. - discriminate EX.
Qed.

Lemma Step_Field_inv : forall e f e', Step (ExpFieldAccess e f) e' ->
  (exists e0, Step e e0 /\ e' = ExpFieldAccess e0 f) \/
  (exists C Fs es fi ei i, e = ExpNew C es /\ Reffields C Fs /\
     nth_error Fs i = Some fi /\ ref fi = f /\ nth_error es i = Some ei /\
     isValue (ExpNew C es) /\ e' = ei).
Proof.
  intros e f e' H. remember (ExpFieldAccess e f) as X eqn:EX. revert e f EX.
  induction H as
    [ c a a' Hst IH1 | c w pf Hval
    | c a a' a2 Hst IH1 | c a a' v Hval Hst IH1
    | c v1 v2 pf Hv1 Hv2
    | m a b a' Hst IH1 | m v a b Hval Hst IH1
    | C e0 m v es Hbody Hvalv HvalNew
    | C Fs es fi ei i HFs HnF HnE Hval
    | e0 e0' f0 Hst IH1
    | C ei' es es' ei i Hst IH1 HnE HnE' Hoth Hlen
    | e_x e_x' e0 Hst IH1 | v e0 Hval ];
  intros ee ff EX.
  - discriminate EX. - discriminate EX. - discriminate EX. - discriminate EX.
  - discriminate EX. - discriminate EX. - discriminate EX. - discriminate EX.
  - injection EX as He Hf. subst. right. eauto 14.
  - injection EX as He Hf. subst. left. eauto.
  - discriminate EX. - discriminate EX. - discriminate EX.
Qed.

Lemma Step_Invok_inv : forall e1 m e2 e', Step (ExpMethodInvoc e1 m e2) e' ->
  (exists e0, Step e1 e0 /\ e' = ExpMethodInvoc e0 m e2) \/
  (exists e0, isValue e1 /\ Step e2 e0 /\ e' = ExpMethodInvoc e1 m e0) \/
  (exists C es body, e1 = ExpNew C es /\ m_body m C body /\ isValue e2 /\ isValue (ExpNew C es) /\
     e' = subBV_at 1 (ExpNew C es) (subBV e2 body)).
Proof.
  intros e1 m e2 e' H. remember (ExpMethodInvoc e1 m e2) as X eqn:EX. revert e1 m e2 EX.
  induction H as
    [ c a a' Hst IH1 | c w pf Hval
    | c a a' a2 Hst IH1 | c a a' v Hval Hst IH1
    | c v1 v2 pf Hv1 Hv2
    | m0 a b a' Hst IH1 | m0 v a b Hval Hst IH1
    | C e0 m0 v es Hbody Hvalv HvalNew
    | C Fs es fi ei i HFs HnF HnE Hval
    | e0 e0' f Hst IH1
    | C ei' es es' ei i Hst IH1 HnE HnE' Hoth Hlen
    | e_x e_x' e0 Hst IH1 | v e0 Hval ];
  intros ea mm eb EX.
  - discriminate EX. - discriminate EX. - discriminate EX. - discriminate EX.
  - discriminate EX.
  - injection EX as Ha Hm Hb. subst. left. eauto.
  - injection EX as Ha Hm Hb. subst. right. left. eauto.
  - injection EX as Ha Hm Hb. subst. right. right. eauto 12.
  - discriminate EX. - discriminate EX. - discriminate EX.
  - discriminate EX. - discriminate EX.
Qed.

Lemma Step_Let_inv : forall e1 e2 e', Step (ExpLet e1 e2) e' ->
  (exists e0, Step e1 e0 /\ e' = ExpLet e0 e2) \/
  (isValue e1 /\ e' = subBV e1 e2).
Proof.
  intros e1 e2 e' H. remember (ExpLet e1 e2) as X eqn:EX. revert e1 e2 EX.
  induction H as
    [ c a a' Hst IH1 | c w pf Hval
    | c a a' a2 Hst IH1 | c a a' v Hval Hst IH1
    | c v1 v2 pf Hv1 Hv2
    | m a b a' Hst IH1 | m v a b Hval Hst IH1
    | C e0 m v es Hbody Hvalv HvalNew
    | C Fs es fi ei i HFs HnF HnE Hval
    | e0 e0' f Hst IH1
    | C ei' es es' ei i Hst IH1 HnE HnE' Hoth Hlen
    | e_x e_x' e0 Hst IH1 | v e0 Hval ];
  intros ea eb EX.
  - discriminate EX. - discriminate EX. - discriminate EX. - discriminate EX.
  - discriminate EX. - discriminate EX. - discriminate EX. - discriminate EX.
  - discriminate EX. - discriminate EX. - discriminate EX.
  - injection EX as Ha Hb. subst. left. eauto.
  - injection EX as Ha Hb. subst. right. eauto.
Qed.

Lemma isValue_not_step : forall a b, isValue a -> Step a b -> False.
Proof.
  intros a b Hv H.
  induction H as
    [ c e1 e1' Hst IH1 | c w pf Hval
    | c e1 e1' e2 Hst IH1 | c e1 e1' v Hval Hst IH1
    | c v1 v2 pf Hv1 Hv2
    | m e1 e2 e1' Hst IH1 | m v e1 e1' Hval Hst IH1
    | C e0 m v es Hbody Hvalv HvalNew
    | C Fs es fi ei i HFs HnF HnE Hval
    | e0 e0' f Hst IH1
    | C ei' es es' ei i Hst IH1 HnE HnE' Hoth Hlen
    | e_x e_x' e0 Hst IH1 | v e0 Hval ].
  all: try (cbn in Hv; contradiction).
  exfalso. eapply IH1. eapply isValueL_nth; eauto.
Qed.

Lemma EvalsTo_value : forall a b, isValue a -> EvalsTo a b -> a = b.
Proof.
  intros a b Hv H. induction H as [|x y z Hst Htail IH].
  - reflexivity.
  - exfalso. exact (isValue_not_step _ _ Hv Hst).
Qed.

(* ============ evaluation decomposition ============ *)
Lemma EvalsTo_unop_inv : forall o e z, EvalsTo (ExpUnOp o e) z -> isValue z ->
  exists z1, EvalsTo e z1 /\ isValue z1 /\ EvalsTo (ExpUnOp o z1) z.
Proof.
  intros o e z H. remember (ExpUnOp o e) as X eqn:EX. revert o e EX.
  induction H as [|e1 e2 e3 Hst Htail IH]; intros ox ex EX Hv.
  - subst e. cbn in Hv. destruct Hv.
  - subst e1.
    destruct (Step_UnOp_inv _ _ _ Hst) as [[e0 [Hstep Heq]] | [w [pf [He [Hval Heq]]]]].
    + destruct (IH ox e0 Heq Hv) as [z1 [Hz1 [Hv1 Hfin]]].
      exists z1. split.
      * eapply AddStep; [exact Hstep|exact Hz1].
      * split; [exact Hv1|exact Hfin].
    + subst ex. eexists. split.
      * apply Refl.
      * split; [exact Hval|].
        eapply AddStep.
        -- apply EUnOp2 with (pf:=pf). exact Hval.
        -- rewrite <- Heq. exact Htail.
Qed.

Lemma EvalsTo_binop_inv : forall o e1 e2 z, EvalsTo (ExpBinOp o e1 e2) z -> isValue z ->
  exists z1 z2, EvalsTo e1 z1 /\ isValue z1 /\ EvalsTo e2 z2 /\ isValue z2 /\
     EvalsTo (ExpBinOp o z1 z2) z.
Proof.
  intros o e1 e2 z H. remember (ExpBinOp o e1 e2) as X eqn:EX. revert o e1 e2 EX.
  induction H as [|a b c Hst Htail IH]; intros ox ex1 ex2 EX Hv.
  - subst e. cbn in Hv. destruct Hv.
  - subst a.
    destruct (Step_BinOp_inv _ _ _ _ Hst) as
      [[e0 [Hstep Heq]] | [[e0 [Hval1 [Hstep Heq]]] | [pf [Hval1 [Hval2 Heq]]]]].
    + assert (Hrec := IH ox e0 ex2 Heq Hv).
      destruct Hrec as [z1 [z2 [H1 [Hv1 [H2 [Hv2 Hfin]]]]]].
      exists z1, z2. split.
      * eapply AddStep; [exact Hstep|exact H1].
      * split; [exact Hv1|]. split; [exact H2|]. split; [exact Hv2|exact Hfin].
    + destruct (IH ox ex1 e0 Heq Hv) as [z1 [z2 [H1 [Hv1 [H2 [Hv2 Hfin]]]]]].
      exists z1, z2. split.
      * exact H1.
      * split; [exact Hv1|]. split.
        -- eapply AddStep; [exact Hstep|exact H2].
        -- split; [exact Hv2|exact Hfin].
    + subst b. exists ex1, ex2. split.
      * apply Refl.
      * split; [exact Hval1|]. split; [apply Refl|]. split; [exact Hval2|].
        eapply AddStep.
        -- apply EBinOp3 with (pf:=pf); auto.
        -- exact Htail.
Qed.

Lemma EvalsTo_field_inv : forall e f z, EvalsTo (ExpFieldAccess e f) z -> isValue z ->
  exists C Fs es fi ei i, EvalsTo e (ExpNew C es) /\ Reffields C Fs /\
     nth_error Fs i = Some fi /\ ref fi = f /\ nth_error es i = Some ei /\
     isValue (ExpNew C es) /\ z = ei.
Proof.
  intros e f z H. remember (ExpFieldAccess e f) as X eqn:EX. revert e f EX.
  induction H as [|a b c Hst Htail IH]; intros ex ff EX Hv.
  - subst e. cbn in Hv. destruct Hv.
  - subst a.
    destruct (Step_Field_inv _ _ _ Hst) as
      [[e0 [Hstep Heq]] | [C [Fs [es [fi [ei [i [Heq [HFs [HnF [Hrf [HnE [Hval Hz]]]]]]]]]]]]].
    + destruct (IH e0 ff Heq Hv) as
        [C [Fs [es [fi [ei [i [H1 [HFs [HnF [Hrf [HnE [HvN Hz]]]]]]]]]]]].
      exists C, Fs, es, fi, ei, i. split.
      * eapply AddStep; [exact Hstep|exact H1].
      * split; [exact HFs|]. split; [exact HnF|]. split; [exact Hrf|]. split; [exact HnE|].
        split; [exact HvN|exact Hz].
    + exists C, Fs, es, fi, ei, i. split.
      * rewrite Heq. apply Refl.
      * split; [exact HFs|]. split; [exact HnF|]. split; [exact Hrf|]. split; [exact HnE|].
        split; [exact Hval|].
        change (isValueL es) in Hval.
        assert (Hvb : isValue b) by (rewrite Hz; eapply isValueL_nth; eauto).
        assert (Hbc : b = c) by (apply EvalsTo_value; auto).
        rewrite <- Hbc. exact Hz.
Qed.

Lemma EvalsTo_invok_inv : forall e1 m e2 z, EvalsTo (ExpMethodInvoc e1 m e2) z -> isValue z ->
  exists C es vb body, EvalsTo e1 (ExpNew C es) /\ isValue (ExpNew C es) /\
     EvalsTo e2 vb /\ isValue vb /\ m_body m C body /\
     EvalsTo (subBV_at 1 (ExpNew C es) (subBV vb body)) z.
Proof.
  intros e1 m e2 z H. remember (ExpMethodInvoc e1 m e2) as X eqn:EX. revert e1 m e2 EX.
  induction H as [|a b c Hst Htail IH]; intros ex1 mm ex2 EX Hv.
  - subst e. cbn in Hv. destruct Hv.
  - subst a.
    destruct (Step_Invok_inv _ _ _ _ Hst) as
      [[e0 [Hstep Heq]] | [[e0 [Hval1 [Hstep Heq]]] | [C [es [body [Heq [Hbody [Hval2 [HvalNew Heq2]]]]]]]]].
    + destruct (IH e0 mm ex2 Heq Hv) as [C [es [vb [body [H1 [HvN [H2 [Hv2 [Hbody Hfin]]]]]]]]].
      exists C, es, vb, body. split.
      * eapply AddStep; [exact Hstep|exact H1].
      * split; [exact HvN|]. split; [exact H2|]. split; [exact Hv2|]. split; [exact Hbody|exact Hfin].
    + destruct (IH ex1 mm e0 Heq Hv) as [C [es [vb [body [H1 [HvN [H2 [Hv2 [Hbody Hfin]]]]]]]]].
      exists C, es, vb, body. split.
      * exact H1.
      * split; [exact HvN|]. split.
        -- eapply AddStep; [exact Hstep|exact H2].
        -- split; [exact Hv2|]. split; [exact Hbody|exact Hfin].
    + exists C, es, ex2, body. split.
      * rewrite Heq. apply Refl.
      * split; [exact HvalNew|]. split; [apply Refl|]. split; [exact Hval2|]. split; [exact Hbody|].
        rewrite <- Heq2. exact Htail.
Qed.

Lemma EvalsTo_let_inv : forall e1 e2 z, EvalsTo (ExpLet e1 e2) z -> isValue z ->
  exists z1, EvalsTo e1 z1 /\ isValue z1 /\ EvalsTo (subBV_at 0 z1 e2) z.
Proof.
  intros e1 e2 z H. remember (ExpLet e1 e2) as X eqn:EX. revert e1 e2 EX.
  induction H as [|a b c Hst Htail IH]; intros ex1 ex2 EX Hv.
  - subst e. cbn in Hv. destruct Hv.
  - subst a.
    destruct (Step_Let_inv _ _ _ Hst) as [[e0 [Hstep Heq]] | [Hval Heq]].
    + destruct (IH e0 ex2 Heq Hv) as [z1 [H1 [Hv1 Hfin]]].
      exists z1. split.
      * eapply AddStep; [exact Hstep|exact H1].
      * split; [exact Hv1|exact Hfin].
    + exists ex1. split.
      * apply Refl.
      * split; [exact Hval|]. change (EvalsTo (subBV ex1 ex2) c). rewrite <- Heq. exact Htail.
Qed.

(* ============ bounded free-variable covers ============ *)
Fixpoint bvCover (j:nat) (e:expr) : Prop :=
  match e with
  | Bc _ => True
  | Ic _ => True
  | BV i => i = j
  | FV _ => True
  | ExpUnOp _ e1 => bvCover j e1
  | ExpBinOp _ e1 e2 => bvCover j e1 /\ bvCover j e2
  | ExpMethodInvoc e1 _ e2 => bvCover j e1 /\ bvCover j e2
  | ExpFieldAccess e1 _ => bvCover j e1
  | ExpNew _ l => (fix f (es':[expr]) := match es' with
                  | nil => True | e::es'' => bvCover j e /\ f es'' end) l
  | ExpLet e1 e2 => bvCover j e1 /\ bvCover (j+1) e2
  end.

Lemma bvCover_subBV_id : forall e j k w, bvCover j e -> k <> j -> subBV_at k w e = e.
Proof.
  refine (proj1 (syntax_mutind'
    (fun e => forall j k w, bvCover j e -> k <> j -> subBV_at k w e = e)
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - cbn; intros; reflexivity.
  - cbn; intros; reflexivity.
  - cbn; intros i j k w Hc Hneq.
    simpl. destruct (k =? i) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hneq. transitivity i; auto.
    + reflexivity.
  - cbn; intros; reflexivity.
  - cbn; intros o e1 IH j k w Hc Hneq. simpl. f_equal. exact (IH j k w Hc Hneq).
  - cbn; intros o e1 IH1 e2 IH2 j k w Hc Hneq. simpl.
    destruct Hc as [H1 H2]. rewrite (IH1 j k w H1 Hneq), (IH2 j k w H2 Hneq). reflexivity.
  - cbn; intros e1 IH1 m e2 IH2 j k w Hc Hneq. simpl.
    destruct Hc as [H1 H2]. rewrite (IH1 j k w H1 Hneq), (IH2 j k w H2 Hneq). reflexivity.
  - cbn; intros e1 IH f j k w Hc Hneq. simpl. f_equal. exact (IH j k w Hc Hneq).
  - intros c l HF j k w Hc Hneq.
    rewrite sBV_New. f_equal. change (map (subBV_at k w) l = l).
    rewrite Forall_forall in HF.
    revert Hc. induction l as [|a l IHs]; simpl; intros Hc.
    + reflexivity.
    + destruct Hc as [Ha Hl].
      rewrite (HF a (or_introl eq_refl) j k w Ha Hneq).
      rewrite (IHs (fun b Hb => HF b (or_intror Hb)) Hl). reflexivity.
  - cbn; intros e1 IH1 e2 IH2 j k w Hc Hneq. simpl.
    destruct Hc as [H1 H2]. rewrite (IH1 j k w H1 Hneq).
    rewrite (IH2 (j+1) (k+1) w H2). reflexivity. lia.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma bvCover_new_nth : forall l j i a,
  (fix f (es':[expr]) := match es' with nil => True | e::es'' => bvCover j e /\ f es'' end) l ->
  nth_error l i = Some a -> bvCover j a.
Proof.
  induction l as [|b l IH]; intros j i a Hc Hn; simpl in *.
  - destruct i; discriminate.
  - destruct Hc as [Hb Hl]. destruct i as [|i]; simpl in *.
    + injection Hn as ->. exact Hb.
    + apply (IH j i a); auto.
Qed.

Lemma bvCover_Forall : forall l j,
  (fix f (es':[expr]) := match es' with nil => True | e::es'' => bvCover j e /\ f es'' end) l ->
  Forall (bvCover j) l.
Proof.
  induction l as [|a l IH]; intros j H; simpl in *.
  - constructor.
  - destruct H as [Ha Hl]. constructor; auto.
Qed.

Lemma isLC_subBV_cover : forall e j w, bvCover j e -> isLC w -> isLC (subBV_at j w e).
Proof.
  refine (proj1 (syntax_mutind'
    (fun e => forall j w, bvCover j e -> isLC w -> isLC (subBV_at j w e))
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - cbn; auto.
  - cbn; auto.
  - cbn. intros i j w Hc Hw. subst. simpl. rewrite Nat.eqb_refl. exact Hw.
  - cbn; auto.
  - cbn; intros o e1 IH j w Hc Hw. simpl. apply IH; auto.
  - cbn; intros o e1 IH1 e2 IH2 j w Hc Hw. simpl.
    destruct Hc as [H1 H2]. split.
    + apply IH1; auto.
    + apply IH2; auto.
  - cbn; intros e1 IH1 m e2 IH2 j w Hc Hw. simpl.
    destruct Hc as [H1 H2]. split.
    + apply IH1; auto.
    + apply IH2; auto.
  - cbn; intros e1 IH f j w Hc Hw. simpl. apply IH; auto.
  - intros c l HF j w Hc Hw.
    rewrite sBV_New. change (isLCL_at 0 (map (subBV_at j w) l)).
    rewrite Forall_forall in HF.
    apply isLCL_map_gen. intros a Ha.
    assert (Hin : In a l) by auto.
    apply In_nth_error in Hin. destruct Hin as [i Hi].
    assert (Ha' : bvCover j a) by (eapply bvCover_new_nth; eauto).
    apply HF; auto.
  - cbn; intros e1 IH1 e2 IH2 j w Hc Hw. simpl.
    destruct Hc as [H1 H2]. split.
    + apply IH1; auto.
    + apply isLC_at_mono with (j:=0); [lia|exact (IH2 (j+1) w H2 Hw)].
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma EvalsTo_field_iv : forall e f z, EvalsTo (ExpFieldAccess e f) z -> isValue z ->
  exists C es, EvalsTo e (ExpNew C es) /\ isValue (ExpNew C es).
Proof.
  intros e f z H. remember (ExpFieldAccess e f) as X eqn:EX. revert e f EX.
  induction H as [|a b c Hst Htail IH]; intros ex ff EX Hv.
  - subst e. cbn in Hv. destruct Hv.
  - subst a.
    destruct (Step_Field_inv _ _ _ Hst) as
      [[e0 [Hstep Heq]] | [C [Fs [es [fi [ei [i [Heq [HFs [HnF [Hrf [HnE [Hval Hz]]]]]]]]]]]]].
    + subst b. destruct (IH e0 ff eq_refl Hv) as [C [es [H1 HvN]]].
      exists C, es. split; [|exact HvN]. eapply AddStep; [exact Hstep|exact H1].
    + subst b. exists C, es. split; [|exact Hval]. rewrite Heq. apply Refl.
Qed.

(* ============ simulation: replacing a closed evaluated expression ============ *)
Lemma sim_subBV : forall p j E v, bvCover j p -> isLC E -> EvalsTo E v -> isValue v ->
  forall z, isValue z -> EvalsTo (subBV_at j v p) z -> EvalsTo (subBV_at j E p) z.
Proof.
  refine (proj1 (syntax_mutind'
    (fun p => forall j E v, bvCover j p -> isLC E -> EvalsTo E v -> isValue v ->
        forall z, isValue z -> EvalsTo (subBV_at j v p) z -> EvalsTo (subBV_at j E p) z)
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - intros b j E v Hc HE HEv Hv z Hz H. simpl. exact H.
  - intros n j E v Hc HE HEv Hv z Hz H. simpl. exact H.
  - intros i j E v Hc HE HEv Hv z Hz H. simpl in Hc. subst i.
    change (EvalsTo (if j =? j then v else BV j) z) in H.
    rewrite Nat.eqb_refl in H. simpl in H.
    assert (Hres : EvalsTo E z).
    { eapply EvalsTo_trans with (b := v). exact HEv. exact H. }
    change (EvalsTo (if j =? j then E else BV j) z).
    rewrite Nat.eqb_refl. simpl. exact Hres.
  - intros x j E v Hc HE HEv Hv z Hz H. simpl. exact H.
  - intros o p1 IH j E v Hc HE HEv Hv z Hz H.
    change (EvalsTo (ExpUnOp o (subBV_at j v p1)) z) in H.
    destruct (EvalsTo_unop_inv o _ z H Hz) as [z1 [H1 [Hv1 Hfin]]].
    assert (R : EvalsTo (subBV_at j E p1) z1) by (apply IH with (j:=j) (E:=E) (v:=v); auto).
    change (EvalsTo (ExpUnOp o (subBV_at j E p1)) z).
    eapply EvalsTo_trans with (b := ExpUnOp o z1).
    + apply EvalsTo_unop; exact R.
    + exact Hfin.
  - intros o p1 IH1 p2 IH2 j E v Hc HE HEv Hv z Hz H.
    change (EvalsTo (ExpBinOp o (subBV_at j v p1) (subBV_at j v p2)) z) in H.
    destruct Hc as [Hc1 Hc2].
    destruct (EvalsTo_binop_inv o _ _ z H Hz) as [z1 [z2 [H1 [Hv1 [H2 [Hv2 Hfin]]]]]].
    assert (R1 : EvalsTo (subBV_at j E p1) z1) by (apply IH1 with (j:=j) (E:=E) (v:=v); auto).
    assert (R2 : EvalsTo (subBV_at j E p2) z2) by (apply IH2 with (j:=j) (E:=E) (v:=v); auto).
    change (EvalsTo (ExpBinOp o (subBV_at j E p1) (subBV_at j E p2)) z).
    eapply EvalsTo_trans with (b := ExpBinOp o z1 z2).
    + eapply EvalsTo_trans with (b := ExpBinOp o z1 (subBV_at j E p2)).
      * apply EvalsTo_binop_l. exact R1.
      * apply EvalsTo_binop_r; auto.
    + exact Hfin.
  - intros p1 IH1 m p2 IH2 j E v Hc HE HEv Hv z Hz H.
    change (EvalsTo (ExpMethodInvoc (subBV_at j v p1) m (subBV_at j v p2)) z) in H.
    destruct Hc as [Hc1 Hc2].
    destruct (EvalsTo_invok_inv _ _ _ z H Hz) as
      [C [es [vb [body [H1 [HvN [H2 [Hv2 [Hbody Hfin]]]]]]]]].
    assert (R1 : EvalsTo (subBV_at j E p1) (ExpNew C es)) by (apply IH1 with (j:=j) (E:=E) (v:=v); auto).
    assert (R2 : EvalsTo (subBV_at j E p2) vb) by (apply IH2 with (j:=j) (E:=E) (v:=v); auto).
    change (EvalsTo (ExpMethodInvoc (subBV_at j E p1) m (subBV_at j E p2)) z).
    eapply EvalsTo_trans with
      (b := ExpMethodInvoc (ExpNew C es) m (subBV_at j E p2)).
    + apply EvalsTo_invok_l; exact R1.
    + eapply EvalsTo_trans with (b := ExpMethodInvoc (ExpNew C es) m vb).
      * apply EvalsTo_invok_r; auto.
      * eapply EvalsTo_trans with
          (b := subBV_at 1 (ExpNew C es) (subBV vb body)).
        -- eapply AddStep.
           ++ exact (Refc_Invok3 C body m vb es Hbody Hv2 HvN).
           ++ apply Refl.
        -- exact Hfin.
  - intros p1 IH f j E v Hc HE HEv Hv z Hz H.
    change (EvalsTo (ExpFieldAccess (subBV_at j v p1) f) z) in H.
    destruct (EvalsTo_field_inv _ _ _ H Hz) as
      [C [Fs [es [fi [ei [i [H1 [HFs [HnF [Hrf [HnE [HvN Hz']]]]]]]]]]]].
    assert (R : EvalsTo (subBV_at j E p1) (ExpNew C es)) by (apply IH with (j:=j) (E:=E) (v:=v); auto).
    change (EvalsTo (ExpFieldAccess (subBV_at j E p1) f) z).
    eapply EvalsTo_trans with (b := ExpFieldAccess (ExpNew C es) f).
    + apply EvalsTo_field; exact R.
    + eapply EvalsTo_trans with (b := ei).
      * eapply AddStep.
         -- rewrite <- Hrf. exact (Refc_Field C Fs es fi ei i HFs HnF HnE HvN).
        -- apply Refl.
      * rewrite Hz'. apply Refl.
  - intros c l HF j E v Hc HE HEv Hv z Hz H.
    rewrite sBV_New in H.
    change (EvalsTo (ExpNew c (map (subBV_at j v) l)) z) in H.
    destruct (EvalsTo_new_inv c (map (subBV_at j v) l) z H) as
      [es' [Hz' [Hlen Hpt]]].
    rewrite Hz'.
    change (EvalsTo (ExpNew c (map (subBV_at j E) l)) (ExpNew c es')).
    eapply EvalsTo_new_prefix with (pre := nil) (l := map (subBV_at j E) l) (l' := es').
    + intros i a0 Ha0.
      apply nth_error_map_Some in Ha0. destruct Ha0 as [a [Ha Haeq]]. subst a0.
      assert (Hnthv : nth_error (map (subBV_at j v) l) i = Some (subBV_at j v a)).
      { rewrite nth_error_map. rewrite Ha. reflexivity. }
      destruct (Hpt i (subBV_at j v a) Hnthv) as [b0 [Hb0 Hev0]].
      assert (Hb0v : isValue b0).
      { assert (Hvs : isValue (ExpNew c es')) by (rewrite <- Hz'; exact Hz).
        apply isValueL_Forall in Hvs. rewrite Forall_forall in Hvs.
        apply Hvs. eapply nth_error_In; eauto. }
      assert (Hcova : bvCover j a) by (exact (bvCover_new_nth l j i a Hc Ha)).
      exists b0. split; [exact Hb0|].
      rewrite Forall_forall in HF.
      assert (Hin : In a l) by (eapply nth_error_In; eauto).
      eapply HF; eauto.
    + rewrite length_map. rewrite length_map in Hlen. exact Hlen.
  - intros p1 IH1 p2 IH2 j E v Hc HE HEv Hv z Hz H.
    change (EvalsTo (ExpLet (subBV_at j v p1) (subBV_at (j+1) v p2)) z) in H.
    destruct Hc as [Hc1 Hc2].
    destruct (EvalsTo_let_inv _ _ z H Hz) as [z1 [H1 [Hv1 Hfin]]].
    assert (R1 : EvalsTo (subBV_at j E p1) z1) by (apply IH1 with (j:=j) (E:=E) (v:=v); auto).
    assert (Hlcv : isLC (subBV_at (j+1) v p2)).
    { apply isLC_subBV_cover with (j:=j+1) (w:=v); auto. apply isValue_isLC; auto. }
    assert (Hfin' : EvalsTo (subBV_at (j+1) v p2) z).
    { rewrite <- (subBV_at_LC (subBV_at (j+1) v p2) 0 Hlcv z1). exact Hfin. }
    assert (R2 : EvalsTo (subBV_at (j+1) E p2) z) by (apply IH2 with (j:=j+1) (E:=E) (v:=v); auto).
    assert (HlcE : isLC (subBV_at (j+1) E p2)).
    { apply isLC_subBV_cover with (j:=j+1) (w:=E); auto. }
    change (EvalsTo (ExpLet (subBV_at j E p1) (subBV_at (j+1) E p2)) z).
    eapply EvalsTo_trans with (b := ExpLet z1 (subBV_at (j+1) E p2)).
    + apply EvalsTo_let_l; exact R1.
    + eapply EvalsTo_trans with (b := subBV z1 (subBV_at (j+1) E p2)).
      * eapply AddStep.
        -- apply ELetV; auto.
        -- apply Refl.
      * assert (Heq : subBV z1 (subBV_at (j+1) E p2) = subBV_at (j+1) E p2).
        { rewrite subBV_unfold. exact (subBV_at_LC (subBV_at (j+1) E p2) 0 HlcE z1). }
        rewrite Heq. exact R2.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

(* ============ normal forms of typing-rule result types ============ *)
Lemma ctsubst_tybc : forall th b,
  ctsubst th (tybc b) = TRefn TBool (PCons (ExpBinOp Eq (Bc b) (BV 0)) PEmpty).
Proof.
  intros. unfold tybc. rewrite ctsubst_TRefn, cpsubst_PCons, cpsubst_PEmpty.
  rewrite csubst_BinOp, csubst_Bc, csubst_BV. reflexivity.
Qed.

Lemma ctsubst_tyic : forall th n,
  ctsubst th (tyic n) = TRefn TInt (PCons (ExpBinOp Eq (Ic n) (BV 0)) PEmpty).
Proof.
  intros. unfold tyic. rewrite ctsubst_TRefn, cpsubst_PCons, cpsubst_PEmpty.
  rewrite csubst_BinOp, csubst_Ic, csubst_BV. reflexivity.
Qed.

Lemma tsubBV_unfold : forall e t, tsubBV e t = tsubBV_at 0 e t.
Proof. reflexivity. Qed.

Lemma ctsubst_tyNot : forall th e, LCsubst th ->
  ctsubst th (tsubBV e (ty' Not)) =
  TRefn TBool (PCons (ExpBinOp Eq (ExpUnOp Not (csubst th e)) (BV 0)) PEmpty).
Proof.
  intros th e Hlc. unfold ty', refn_pred. rewrite tsubBV_unfold. rewrite tsubBV_TRefn.
  rewrite ctsubst_TRefn.
  rewrite psubBV_at_PCons. rewrite psubBV_at_PEmpty.
  rewrite cpsubst_PCons. rewrite cpsubst_PEmpty.
  rewrite csubst_subBV; auto.
  rewrite csubst_BinOp. rewrite csubst_UnOp. repeat rewrite csubst_BV. cbn. reflexivity.
Qed.

Lemma ctsubst_tyBinOp : forall th op e1 e2, LCsubst th -> isLC e1 -> isLC e2 ->
  ctsubst th (tsubBV_at 1 e1 (tsubBV e2 (ty'2 op))) =
  TRefn TBool (PCons (ExpBinOp Eq (ExpBinOp op (csubst th e1) (csubst th e2)) (BV 0)) PEmpty).
Proof.
  intros th op e1 e2 Hlc Hl1 Hl2. destruct op; unfold ty'2, refn_pred2;
  rewrite tsubBV_unfold; rewrite tsubBV_TRefn; rewrite tsubBV_at_TRefn;
  rewrite ctsubst_TRefn;
  rewrite psubBV_at_PCons; rewrite psubBV_at_PCons; rewrite psubBV_at_PEmpty;
  rewrite cpsubst_PCons; rewrite cpsubst_PEmpty;
  rewrite csubst_subBV; auto;
  rewrite csubst_subBV; auto;
  repeat rewrite csubst_BinOp; repeat rewrite csubst_BV; cbn.
  all: assert (Hlc2 : isLC (csubst th e2)) by (apply (proj1 isLC_csubst_gen); auto).
  all: change (isLC_at 0 (csubst th e2)) in Hlc2.
  all: assert (Hlc2' : isLC_at 2 (csubst th e2)) by (apply isLC_at_mono with (j:=0); [lia|exact Hlc2]).
  all: rewrite (subBV_at_LC (csubst th e2) 2 Hlc2' (csubst th e1)).
  all: reflexivity.
Qed.

(* ============ semantic typing ============ *)
(* ============ opening inversions for LC at a fixed index ============ *)
Lemma isLC_open_at_inv : forall e j k y,
  isLC_at j (open_at k y e) -> k <= j -> isLC_at (j+1) e.
Proof.
  refine (proj1 (syntax_mutind'
    (fun e => forall j k y, isLC_at j (open_at k y e) -> k <= j -> isLC_at (j+1) e)
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - cbn; auto.
  - cbn; auto.
  - cbn. intros i j k y H Hk. destruct (k =? i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. simpl. lia.
    + simpl in H. simpl. lia.
  - cbn; auto.
  - cbn. intros o e IH j k y H Hk. apply (IH j k y); auto.
  - cbn. intros o e1 IH1 e2 IH2 j k y [H1 H2] Hk. split; [apply (IH1 j k y)|apply (IH2 j k y)]; auto.
  - cbn. intros e1 IH1 m e2 IH2 j k y [H1 H2] Hk. split; [apply (IH1 j k y)|apply (IH2 j k y)]; auto.
  - cbn. intros e IH f j k y H Hk. apply (IH j k y); auto.
  - cbn. intros c l HF j k y H Hk.
    induction HF as [|a l Pa Pl IHl]; simpl in *.
    + exact I.
    + destruct H as [Ha Hl]. split.
      * apply (Pa j k y); auto.
      * apply IHl; auto.
  - cbn. intros e1 IH1 e2 IH2 j k y [H1 H2] Hk. split.
    + apply (IH1 j k y); auto.
    + apply (IH2 (j+1) (k+1) y); auto. lia.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma isLCP_open_inv : forall ps j k y,
  isLCP_at j (openP_at k y ps) -> k <= j -> isLCP_at (j+1) ps.
Proof.
  refine (proj2 (proj2 (syntax_mutind'
    (fun (_:expr) => True) (fun (_:type) => True)
    (fun ps => forall j k y, isLCP_at j (openP_at k y ps) -> k <= j -> isLCP_at (j+1) ps)
    _ _ _ _ _ _ _ _ _ _ _ _ _))).
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn. intros p IHp ps IHps j k y [Hp Hps] Hk. split.
    + apply (isLC_open_at_inv p j k y); auto.
    + apply (IHps j k y); auto.
Qed.

Lemma Forall_isLCL_at : forall l j, Forall (isLC_at j) l ->
  (fix f (es':[expr]) := match es' with nil => True | e::es'' => isLC_at j e /\ f es'' end) l.
Proof.
  intros l j H. induction H as [|a l Ha Hl IH]; simpl.
  - exact I.
  - split; auto.
Qed.

Lemma isLC_csubst_at : forall e th, LCsubst th -> forall j,
  isLC_at j e -> isLC_at j (csubst th e).
Proof.
  intros e th. revert e. induction th as [|x v th IH]; intros e Hlc j He; simpl.
  - exact He.
  - apply IH.
    + apply LCsubst_tail in Hlc; exact Hlc.
    + apply (proj1 isLC_subFV_gen); auto.
      apply LCsubst_head in Hlc; exact Hlc.
Qed.

(* ============ expression size ============ *)
Fixpoint esize (e:expr) : nat :=
  match e with
  | Bc _ | Ic _ | BV _ | FV _ => 1
  | ExpUnOp _ e1 => S (esize e1)
  | ExpBinOp _ e1 e2 => S (esize e1 + esize e2)
  | ExpMethodInvoc e1 _ e2 => S (esize e1 + esize e2)
  | ExpFieldAccess e1 _ => S (esize e1)
  | ExpNew _ l => S ((fix go (l0:[expr]) : nat :=
                        match l0 with
                        | nil => 0
                        | a :: l' => esize a + go l'
                        end) l)
  | ExpLet e1 e2 => S (esize e1 + esize e2)
  end.

Definition esizeL (l:[expr]) : nat :=
  (fix go (l0:[expr]) : nat :=
     match l0 with
     | nil => 0
     | a :: l' => esize a + go l'
     end) l.

Lemma esize_pos : forall e, 1 <= esize e.
Proof. intros e. destruct e; simpl; lia. Qed.

Lemma esizeL_nth_le : forall l i a, nth_error l i = Some a -> esize a <= esizeL l.
Proof.
  intros l. induction l as [|b l IH]; intros i a H.
  - destruct i; simpl in H; discriminate.
  - destruct i as [|i]; simpl in *.
    + injection H as ->. lia.
    + apply IH in H. lia.
Qed.

Lemma esize_open_at : forall e k y, esize (open_at k y e) = esize e.
Proof.
  refine (proj1 (syntax_mutind'
    (fun e => forall k y, esize (open_at k y e) = esize e)
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - cbn; auto.
  - cbn; auto.
  - cbn. intros i k y. destruct (k =? i); reflexivity.
  - cbn; auto.
  - cbn. intros o e IH k y. simpl. rewrite IH. reflexivity.
  - cbn. intros o e1 IH1 e2 IH2 k y. simpl. rewrite IH1, IH2. reflexivity.
  - cbn. intros e1 IH1 m e2 IH2 k y. simpl. rewrite IH1, IH2. reflexivity.
  - cbn. intros e IH f k y. simpl. rewrite IH. reflexivity.
  - cbn. intros c l HF k y.
    assert (Hmap : esizeL (map (open_at k y) l) = esizeL l).
    { induction HF as [|a l Pa Pl IHl]; simpl.
      - reflexivity.
      - rewrite Pa, IHl. reflexivity. }
    change (S (esizeL (map (open_at k y) l)) = S (esizeL l)).
    rewrite Hmap. reflexivity.
  - cbn. intros e1 IH1 e2 IH2 k y. simpl. rewrite IH1, IH2. reflexivity.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

(* ============ HasFJtype without the subsumption rule ============ *)
Inductive HasFJtypeD : fjenv -> expr -> fjtype -> Prop :=
| DBC   : forall (g:fjenv) (b:bool), HasFJtypeD g (Bc b) TBool
| DIC   : forall (g:fjenv) (n:Z), HasFJtypeD g (Ic n) TInt
| DVar  : forall (g:fjenv) (x:vname) (b:fjtype), bound_inF x b g -> HasFJtypeD g (FV x) b
| DUnOP : forall (g:fjenv) (e:expr) (op:UnOp),
    HasFJtype g e (erase (intype op)) ->
    HasFJtypeD g (ExpUnOp op e) (erase (ty' op))
| DBinOP : forall (g:fjenv) (e1 e2:expr) (op:BinOp),
    HasFJtype g e1 (erase (fst (intype2 op))) ->
    HasFJtype g e2 (erase (snd (intype2 op))) ->
    HasFJtypeD g (ExpBinOp op e1 e2) (erase (ty'2 op))
| DInvok : forall (g:fjenv) (e1 e2:expr) (m:MethodName) t rt C ps,
    HasFJtype g e1 (TNom (TClass C)) ->
    mtype(m, C) = ps ~> t ~> rt ->
    HasFJtype g e2 (erase t) ->
    HasFJtypeD g (ExpMethodInvoc e1 m e2) (erase rt)
| DInvokI : forall (g:fjenv) (e1 e2:expr) (m:MethodName) t rt C ps,
    HasFJtype g e1 (TNom (TInterface C)) ->
    mtypei(m, C) = ps ~> t ~> rt ->
    HasFJtype g e2 (erase t) ->
    HasFJtypeD g (ExpMethodInvoc e1 m e2) (erase rt)
| DField : forall g e f T C F i ff,
    HasFJtype g e (TNom (TClass C)) ->
    Reffields C F ->
    nth_error F i = Some ff ->
    ref ff = f ->
    ReffieldType ff = T ->
    HasFJtypeD g (ExpFieldAccess e f) (erase T)
| DNew : forall g es C Fs Us fs,
    Us = map erase (map ReffieldType Fs) ->
    fs = map ReffieldName Fs ->
    Reffields C Fs ->
    Forall2 (HasFJtype g) es Us ->
    HasFJtypeD g (ExpNew C es) (TNom (TClass C))
| DLet : forall (g:fjenv) (e_x:expr) (b:fjtype) (e:expr) (b':fjtype) (nms:names),
    HasFJtype g e_x b ->
    (forall (y:vname), ~ Elem y nms -> HasFJtype (FCons y b g) (unbind y e) b') ->
    HasFJtypeD g (ExpLet e_x e) b'.

Lemma HasFJtype_to_D : forall g e t, HasFJtype g e t -> exists s, HasFJtypeD g e s.
Proof.
  intros g e t H.
  induction H as
   [ g b | g n | g x b Hb
   | g e op H1 IH1
   | g e1 e2 op H1 IH1 H2 IH2
   | g e1 e2 m t rt C ps H1 IH1 Hm H2 IH2
   | g e1 e2 m t rt C ps H1 IH1 Hm H2 IH2
   | g e f T C F i ff H1 IH1 HFs Hnth Href HT
   | g es C Fs Us fs HUs Hfs HFs HF2
   | g e_x b e b' nms Hwf Hx IHx Hbody
   | g e s t H1 IH1 Hsub ].
  - eexists; eapply DBC.
  - eexists; eapply DIC.
  - eexists; eapply DVar; eauto.
  - eexists; eapply DUnOP; eauto.
  - eexists; eapply DBinOP; eauto.
  - eexists; eapply DInvok; eauto.
  - eexists; eapply DInvokI; eauto.
  - eexists; eapply DField; eauto.
  - eexists; eapply DNew; eauto.
  - eexists; eapply DLet; eauto.
  - destruct IH1 as [s0 Hs0]; eexists; exact Hs0.
Qed.

Lemma HasFJtypeD_let_inv : forall g e1 e2 s,
  HasFJtypeD g (ExpLet e1 e2) s ->
  exists b b' nms, HasFJtype g e1 b /\
    (forall y, ~ Elem y nms -> HasFJtype (FCons y b g) (unbind y e2) b').
Proof.
  intros g e1 e2 s HD. dependent destruction HD.
  eexists; eexists; eexists; split; eauto.
Qed.

Lemma Forall2_isLC_bound : forall g es Us m,
  esizeL es <= m ->
  Forall2 (HasFJtype g) es Us ->
  (forall e, esize e <= m -> forall g' t, HasFJtype g' e t -> forall j, isLC_at j e) ->
  forall j, Forall (isLC_at j) es.
Proof.
  intros g es Us m Hm HF2 Hrec j. revert Hm j.
  induction HF2 as [|e U es Us He Htail IHtail]; intros Hm j.
  - constructor.
  - simpl in Hm. constructor.
    + assert (Hle : esize e <= m) by lia. exact (Hrec e Hle g U He j).
    + apply IHtail. lia.
Qed.

Lemma HasFJtype_isLC : forall n e, esize e <= n -> forall g t, HasFJtype g e t -> forall j, isLC_at j e.
Proof.
  intros n. induction n as [|n IH]; intros e Hn g t HF j.
  - exfalso. pose proof (esize_pos e). lia.
  - destruct e as [b|z|i|x|op e1|op e1 e2|e1 f|e1 m e2|c l|e1 e2].
    + cbn; auto.
    + cbn; auto.
    + destruct (HasFJtype_to_D g (BV i) t HF) as [s HD]. dependent destruction HD.
    + cbn; auto.
    + destruct (HasFJtype_to_D g (ExpUnOp op e1) t HF) as [s HD]. dependent destruction HD.
      simpl. eapply IH; [simpl in Hn; lia | eassumption].
    + destruct (HasFJtype_to_D g (ExpBinOp op e1 e2) t HF) as [s HD]. dependent destruction HD.
      simpl. split.
      * eapply IH; [simpl in Hn; lia | eassumption].
      * eapply IH; [simpl in Hn; lia | eassumption].
    + destruct (HasFJtype_to_D g (ExpFieldAccess e1 f) t HF) as [s HD]. dependent destruction HD.
      simpl. eapply IH; [simpl in Hn; lia | eassumption].
    + destruct (HasFJtype_to_D g (ExpMethodInvoc e1 m e2) t HF) as [s HD]. dependent destruction HD.
      all: simpl; split.
      all: eapply IH; [simpl in Hn; lia | eassumption].
    + destruct (HasFJtype_to_D g (ExpNew c l) t HF) as [s HD]. dependent destruction HD.
      simpl. apply Forall_isLCL_at.
      assert (Hle : esizeL l <= n).
      { change (S (esizeL l) <= S n) in Hn. lia. }
      eapply Forall2_isLC_bound; [exact Hle | eassumption | exact IH].
    + destruct (HasFJtype_to_D g (ExpLet e1 e2) t HF) as [s HD].
      destruct (HasFJtypeD_let_inv g e1 e2 s HD) as [b [b' [nms [Hx Hbody]]]].
      simpl. split.
      * eapply IH; [simpl in Hn; lia | eassumption].
      * assert (Hsize2 : esize e2 <= n) by (simpl in Hn; lia).
        pose (y := freshv nms).
        assert (Hy : ~ Elem y nms) by (apply freshv_notin).
        assert (HB : HasFJtype (FCons y b g) (unbind y e2) b') by (apply Hbody; exact Hy).
        assert (HL : isLC_at 0 (open_at 0 y e2)).
        { eapply IH; [| exact HB].
          unfold unbind. rewrite esize_open_at. exact Hsize2. }
        assert (HL1 : isLC_at 1 e2).
        { apply (isLC_open_at_inv e2 0 0 y); auto. }
        apply isLC_at_mono with (j:=1); [lia | exact HL1].
Qed.

Lemma Hastype_isLC : forall g e t, Hastype g e t -> isLC e.
Proof.
  intros g e t H.
  refine (Hastype_ind (fun g e t => isLC e)
    _ _ _ _ _ _ _ _ _ _ _ g e t H).
  - intros gg b. cbn; auto.
  - intros gg n. cbn; auto.
  - intros gg e0 op tt Hte IH Hsub Hlc. cbn. exact Hlc.
  - intros gg e1 e2 op tt tt' Ht1 IH1 Hsub1 Ht2 IH2 Hsub2 Hlc1 Hlc2. cbn. split; auto.
  - intros gg x tt Hb Hwf. cbn; auto.
  - intros gg e1 e2 m tt tt' rt C ps ps' Hte1 IH1 Hmty Hsub Hte2 IH2 Hsub2 Hlc2 Hlc1. cbn. split; auto.
  - intros gg e1 e2 m tt tt' rt I ps ps' Hte1 IH1 Hmty Hsub Hte2 IH2 Hsub2 Hlc2 Hlc1. cbn. split; auto.
  - intros gg e0 f C Fs i fi ps Hlc Hte IH HFs Hnth Hreff. cbn. exact Hlc.
  - intros gg es Ts C Fs Us fs HUs Hfs HLC HFs HF2 HSub2. cbn.
    apply Forall_isLCL_at. exact HLC.
  - intros gg e_x b e0 b' nms Hwfb' Hte IHx Hbody IHb. cbn. split.
    + exact IHx.
    + pose (y := freshv nms).
      assert (Hy : ~ Elem y nms) by (apply freshv_notin).
      apply (isLC_open_at_inv e0 0 0 y).
      * unfold unbind, isLC. apply IHb; exact Hy.
      * lia.
  - intros gg e0 s tt Hte IH Hwft Hsub. exact IH.
Qed.

Lemma PIsBool_isLCP : forall g ps, PIsBool g ps -> forall j, isLCP_at j ps.
Proof.
  intros g ps H. induction H as [gg | gg p ps Hop Hps IH].
  - intro j. cbn; auto.
  - intro j. cbn. split.
    + exact (HasFJtype_isLC (esize p) p (le_n (esize p)) gg TBool Hop j).
    + exact (IH j).
Qed.

Lemma WFtype_isLCT : forall g t, WFtype g t -> isLCT t.
Proof.
  intros g t H. induction H as [g b | g b ps nms Hbase IHbase Hne Hbody].
  - cbn; auto.
  - cbn.
    pose (y := freshv nms).
    assert (Hy : ~ Elem y nms) by (apply freshv_notin).
    assert (HB : PIsBool (FCons y b (erase_env g)) (openP_at 0 y ps)) by (apply Hbody; exact Hy).
    assert (HL : isLCP_at 0 (openP_at 0 y ps)).
    { apply (PIsBool_isLCP _ _ HB 0). }
    apply (isLCP_open_inv ps 0 0 y); auto.
Qed.

(* ============ canonicity of operator results ============ *)
Lemma EvalsTo_unop_result : forall op E v, EvalsTo (ExpUnOp op E) v -> isValue v -> exists b, v = Bc b.
Proof.
  intros op E v HE Hv.
  destruct (EvalsTo_unop_inv op E v HE Hv) as [z1 [H1 [Hv1 Hfin]]].
  inversion Hfin as [ee | x y z Hstep Htail]; subst.
  - destruct Hv.
  - destruct (Step_UnOp_inv op z1 y Hstep) as [[e0 [Hst Heq]] | [w [pf [He [Hval Heq]]]]].
    + exfalso. exact (isValue_not_step z1 e0 Hv1 Hst).
    + destruct pf. subst. simpl in Htail. destruct b; simpl in Htail.
      * exists false. symmetry. eapply EvalsTo_value; [simpl; exact I|exact Htail].
      * exists true. symmetry. eapply EvalsTo_value; [simpl; exact I|exact Htail].
Qed.

Lemma EvalsTo_binop_result : forall op E1 E2 v, EvalsTo (ExpBinOp op E1 E2) v -> isValue v -> exists b, v = Bc b.
Proof.
  intros op E1 E2 v HE Hv.
  destruct (EvalsTo_binop_inv op E1 E2 v HE Hv) as
    [z1 [z2 [H1 [Hv1 [H2 [Hv2 Hfin]]]]]].
  inversion Hfin as [ee | x y z Hstep Htail]; subst.
  - destruct Hv.
  - destruct (Step_BinOp_inv op z1 z2 y Hstep) as
      [[e0 [Hst Heq]] | [[e0 [Hval1 [Hst Heq]]] | [pf [Hval1 [Hval2 Heq]]]]].
    + exfalso. exact (isValue_not_step z1 e0 Hv1 Hst).
    + exfalso. exact (isValue_not_step z2 e0 Hv2 Hst).
    + destruct pf as [b1 b2 | b1 b2 | v1 v2 Hvv1 Hvv2]; subst y; simpl in Htail.
      * exists (andb b1 b2). symmetry. eapply EvalsTo_value; [simpl; exact I|exact Htail].
      * exists (orb b1 b2). symmetry. eapply EvalsTo_value; [simpl; exact I|exact Htail].
      * exists (veq v1 v2). symmetry. eapply EvalsTo_value; [simpl; exact I|exact Htail].
Qed.




(* ===== module fuel ===== *)
Inductive EvalsToN : nat -> expr -> expr -> Prop :=
| EvN_refl : forall e, EvalsToN 0 e e
| EvN_step : forall n e1 e2 e3, Step e1 e2 -> EvalsToN n e2 e3 -> EvalsToN (S n) e1 e3.

Lemma EvN_EvalsTo : forall n e v, EvalsToN n e v -> EvalsTo e v.
Proof.
  intros n e v H. induction H as [e | n e1 e2 e3 Hstep Htail IH].
  - apply Refl.
  - eapply AddStep; eauto.
Qed.

Lemma EvalsTo_EvN : forall e v, EvalsTo e v -> exists n, EvalsToN n e v.
Proof.
  intros e v H. induction H as [e | e1 e2 e3 Hstep Htail IH].
  - exists 0. apply EvN_refl.
  - destruct IH as [n Hn]. exists (S n). eapply EvN_step; eauto.
Qed.

Lemma EvN_value_eq : forall n e v, EvalsToN n e v -> isValue e -> v = e.
Proof.
  intros n e v H. induction H as [e | n e1 e2 e3 Hstep Htail IH]; intros Hv.
  - reflexivity.
  - exfalso. eapply isValue_not_step; eauto.
Qed.

Lemma EvN_trans : forall n a b, EvalsToN n a b -> forall m c, EvalsToN m b c -> EvalsToN (n+m) a c.
Proof.
  intros n a b H. induction H as [a | n a b c Hstep Htail IH]; intros m d Hmd.
  - simpl. exact Hmd.
  - simpl. eapply EvN_step; [exact Hstep | apply IH; exact Hmd].
Qed.

Lemma EvN_unop_decomp : forall n op e v, EvalsToN n (ExpUnOp op e) v -> isValue v ->
  exists n1 n2 w r, EvalsToN n1 e w /\ isValue w /\
    Step (ExpUnOp op w) r /\ EvalsToN n2 r v /\ n = n1 + S n2.
Proof.
  intros n op e v H. remember (ExpUnOp op e) as X eqn:EX. revert op e EX.
  induction H as [a | n' a b c Hstep Htail IH]; intros op0 e0 EX Hv.
  - subst a. cbn in Hv. destruct Hv.
  - subst a.
    destruct (Step_UnOp_inv op0 e0 b Hstep) as [[e1 [Hst Heq]] | [w [pf [He [Hval Heq]]]]].
    + subst b.
      destruct (IH op0 e1 eq_refl Hv) as [n1 [n2 [w [r [Hev [Hw [Hstep2 [Hrv Hn]]]]]]]].
      exists (S n1), n2, w, r.
      split; [|split; [exact Hw|split; [exact Hstep2|split; [exact Hrv|lia]]]].
      eapply EvN_step; eauto.
    + subst b. subst e0.
      exists 0, n', w, (udelta op0 w pf).
      split; [apply EvN_refl|split; [exact Hval|split; [apply EUnOp2; exact Hval|split; [exact Htail|lia]]]].
Qed.

Lemma EvN_value_steps : forall n e v, EvalsToN n e v -> isValue e -> n = 0.
Proof.
  intros n e v H. induction H as [e | n e1 e2 e3 Hstep Htail IH]; intros Hv.
  - reflexivity.
  - exfalso. eapply isValue_not_step; eauto.
Qed.

Lemma EvN_binop_decomp : forall n op e1 e2 v,
  EvalsToN n (ExpBinOp op e1 e2) v -> isValue v ->
  exists n1 n2 n3 w1 w2 r, EvalsToN n1 e1 w1 /\ isValue w1 /\
    EvalsToN n2 e2 w2 /\ isValue w2 /\
    Step (ExpBinOp op w1 w2) r /\ EvalsToN n3 r v /\ n = n1 + n2 + 1 + n3.
Proof.
  intros n op e1 e2 v H. remember (ExpBinOp op e1 e2) as X eqn:EX.
  revert op e1 e2 EX.
  induction H as [a | n' a b c Hstep Htail IH]; intros op0 e0 e2' EX Hv.
  - subst a. cbn in Hv. destruct Hv.
  - subst a.
    destruct (Step_BinOp_inv op0 e0 e2' b Hstep) as
      [[e1' [Hst Heq]] | [[e2'' [Hval [Hst Heq]]] | [pf [Hval1 [Hval2 Heq]]]]].
    + subst b.
      destruct (IH op0 e1' e2' eq_refl Hv) as
        [n1 [n2 [n3 [w1 [w2 [r [H1 [Hw1 [H2 [Hw2 [Hstep2 [Hrv Hn]]]]]]]]]]]].
      exists (S n1), n2, n3, w1, w2, r.
      repeat split.
      * eapply EvN_step; eauto.
      * exact Hw1.
      * exact H2.
      * exact Hw2.
      * exact Hstep2.
      * exact Hrv.
      * lia.
    + subst b.
      destruct (IH op0 e0 e2'' eq_refl Hv) as
        [n1 [n2 [n3 [w1 [w2 [r [H1 [Hw1 [H2 [Hw2 [Hstep2 [Hrv Hn]]]]]]]]]]]].
      assert (Hn1 : n1 = 0) by (eapply EvN_value_steps; eauto).
      assert (Hw1eq : w1 = e0) by (eapply EvN_value_eq; eauto).
      subst n1. subst w1.
      exists 0, (S n2), n3, e0, w2, r.
      repeat split.
      * apply EvN_refl.
      * exact Hval.
      * eapply EvN_step; eauto.
      * exact Hw2.
      * exact Hstep2.
      * exact Hrv.
      * lia.
    + subst b.
      exists 0, 0, n', e0, e2', (bdelta op0 e0 e2' pf).
      repeat split; try (apply EvN_refl); try assumption;
        try (apply EBinOp3 with (pf := pf)); try lia.
Qed.

Lemma EvN_let_decomp : forall n e1 e2 v,
  EvalsToN n (ExpLet e1 e2) v -> isValue v ->
  exists nx n2 vx, EvalsToN nx e1 vx /\ isValue vx /\
    EvalsToN n2 (subBV_at 0 vx e2) v /\ n = nx + 1 + n2.
Proof.
  intros n e1 e2 v H. remember (ExpLet e1 e2) as X eqn:EX.
  revert e1 e2 EX.
  induction H as [a | n' a b c Hstep Htail IH]; intros e1' e2' EX Hv.
  - subst a. cbn in Hv. destruct Hv.
  - subst a.
    destruct (Step_Let_inv e1' e2' b Hstep) as [[e0 [Hst Heq]] | [Hval Heq]].
    + subst b.
      destruct (IH e0 e2' eq_refl Hv) as [nx [n2 [vx [H1 [Hvx [H2 Hn]]]]]].
      exists (S nx), n2, vx.
      repeat split; try (eapply EvN_step; eauto); try assumption; try lia.
    + subst b.
      exists 0, n', e1'.
      repeat split; try (apply EvN_refl); try assumption; try lia.
Qed.

Lemma EvN_field_decomp : forall n e f v,
  EvalsToN n (ExpFieldAccess e f) v -> isValue v ->
  exists n1 C Fs es fi ei i,
    EvalsToN n1 e (ExpNew C es) /\ isValue (ExpNew C es) /\
    Reffields C Fs /\ nth_error Fs i = Some fi /\ ref fi = f /\
    nth_error es i = Some ei /\ v = ei /\ n = n1 + 1.
Proof.
  intros n e f v H. remember (ExpFieldAccess e f) as X eqn:EX. revert e f EX.
  induction H as [a | n' a b c Hstep Htail IH]; intros e0 f0 EX Hv.
  - subst a. cbn in Hv. destruct Hv.
  - subst a.
    destruct (Step_Field_inv e0 f0 b Hstep) as
      [[e1 [Hst Heq]] |
       [C [Fs [es [fi [ei [i [Heq [HFs [HnF [Hrf [HnE [HvalNew Hz]]]]]]]]]]]]].
    + subst b.
      destruct (IH e1 f0 eq_refl Hv) as
        [n1 [C [Fs [es [fi [ei [i [H1 [Hval [HFs [HnF [Hrf [HnE [Hvz Hn]]]]]]]]]]]]]].
      exists (S n1), C, Fs, es, fi, ei, i.
      repeat split; try assumption; try lia.
      eapply EvN_step; eauto.
    + subst b. subst e0.
      assert (Hvei : isValue ei) by (exact (isValueL_nth es i ei HvalNew HnE)).
      assert (Hveq : c = ei) by (apply (EvN_value_eq n' ei c Htail Hvei)).
      assert (Hn' : n' = 0) by (apply (EvN_value_steps n' ei c Htail Hvei)).
      subst c. subst n'.
      exists 0, C, Fs, es, fi, ei, i.
      repeat split; try assumption; try lia.
      apply EvN_refl.
Qed.

Lemma EvN_invok_decomp : forall n e1 m e2 v,
  EvalsToN n (ExpMethodInvoc e1 m e2) v -> isValue v ->
  exists n1 n2 nb C es vb body,
    EvalsToN n1 e1 (ExpNew C es) /\ isValue (ExpNew C es) /\
    EvalsToN n2 e2 vb /\ isValue vb /\ m_body m C body /\
    EvalsToN nb (subBV_at 1 (ExpNew C es) (subBV vb body)) v /\
    n = n1 + n2 + 1 + nb.
Proof.
  intros n e1 m e2 v H. remember (ExpMethodInvoc e1 m e2) as X eqn:EX.
  revert e1 m e2 EX.
  induction H as [a | n' a b c Hstep Htail IH]; intros e1' m0 e2' EX Hv.
  - subst a. cbn in Hv. destruct Hv.
  - subst a.
    destruct (Step_Invok_inv e1' m0 e2' b Hstep) as [Hrecv | [Harg | Hcall]].
    + destruct Hrecv as [e0 [Hst Heq]]. subst b.
destruct (IH e0 m0 e2' eq_refl Hv) as [n1 [n2 [nb [C [es [vb [body Hconj]]]]]]].
      destruct Hconj as [H1 Hrest].
      destruct Hrest as [HvalNew Hrest].
      destruct Hrest as [H2 Hrest].
      destruct Hrest as [Hvb Hrest].
      destruct Hrest as [Hbody Hrest].
      destruct Hrest as [Hb Hn].
      exists (S n1), n2, nb, C, es, vb, body.
      repeat split; try assumption; try lia.
      eapply EvN_step; eauto.
    + destruct Harg as [e0 [Hval [Hst Heq]]]. subst b.
destruct (IH e1' m0 e0 eq_refl Hv) as [n1 [n2 [nb [C [es [vb [body Hconj]]]]]]].
      destruct Hconj as [H1 Hrest].
      destruct Hrest as [HvalNew Hrest].
      destruct Hrest as [H2 Hrest].
      destruct Hrest as [Hvb Hrest].
      destruct Hrest as [Hbody Hrest].
      destruct Hrest as [Hb Hn].
      assert (Hn1 : n1 = 0) by (apply (EvN_value_steps n1 e1' (ExpNew C es) H1 Hval)).
      assert (Hveq : ExpNew C es = e1') by (apply (EvN_value_eq n1 e1' (ExpNew C es) H1 Hval)).
      subst n1. subst e1'.
      exists 0, (S n2), nb, C, es, vb, body.
      repeat split; try assumption; try (apply EvN_refl); try lia.
      eapply EvN_step; eauto.
    + destruct Hcall as [C [es [body [Heq [Hbody [Hval [HvalNew Heq']]]]]]].
      subst b. subst e1'.
      exists 0, 0, n', C, es, e2', body.
      repeat split; try assumption; try (apply EvN_refl); try lia.
Qed.

Lemma EvN_new_decomp : forall n C es v,
  EvalsToN n (ExpNew C es) v -> isValue v ->
  exists vs, v = ExpNew C vs /\ length es = length vs /\
    (forall i a, nth_error es i = Some a ->
       exists b nb, nth_error vs i = Some b /\ EvalsToN nb a b /\ nb <= n).
Proof.
  intros n C es v H. remember (ExpNew C es) as X eqn:EX. revert C es EX.
  induction H as [a | n' a b c Hstep Htail IH]; intros C0 es0 EX Hv.
  - subst a.
    exists es0. split; [reflexivity|split; [reflexivity|]].
    intros i a Ha. exists a, 0. split; [exact Ha|split; [apply EvN_refl|lia]].
  - subst a.
    destruct (Step_New_inv C0 es0 b Hstep) as
      [ys [Hb [Hlen [i0 [ei [ei' [Hsti [HnE [HnE' Hoth]]]]]]]]].
    subst b.
    destruct (IH C0 ys eq_refl Hv) as [vs [Hveq [Hlen2 Hpt]]].
    exists vs. split; [exact Hveq|split; [lia|]].
    intros j a Ha.
    destruct (Nat.eq_dec j i0) as [->|Hne].
    + rewrite HnE in Ha. injection Ha as ->.
      destruct (Hpt i0 ei' HnE') as [b0 [nb [Hb0 [HP Hle]]]].
      exists b0, (S nb). split; [exact Hb0|split; [eapply EvN_step; eauto|lia]].
    + rewrite (Hoth j Hne) in Ha.
      destruct (Hpt j a Ha) as [b0 [nb [Hb0 [HP Hle]]]].
      exists b0, nb. split; [exact Hb0|split; [exact HP|lia]].
Qed.



(* ============ direct typing (without subsumption) ============ *)
Inductive HastypeD : env -> expr -> type -> Prop :=
| D_TBC : forall g b, HastypeD g (Bc b) (tybc b)
| D_TIC : forall g n, HastypeD g (Ic n) (tyic n)
| D_TUnOP : forall g e t, Hastype g e t -> Subtype g t (intype Not) -> isLC e ->
    HastypeD g (ExpUnOp Not e) (tsubBV e (ty' Not))
| D_TBinOP_And : forall g e1 e2 t t', Hastype g e1 t -> Subtype g t (fst (intype2 And)) ->
    Hastype g e2 t' -> Subtype g t' (tsubBV e1 (snd (intype2 And))) ->
    isLC e1 -> isLC e2 -> HastypeD g (ExpBinOp And e1 e2) (tsubBV_at 1 e1 (tsubBV e2 (ty'2 And)))
| D_TBinOP_Or : forall g e1 e2 t t', Hastype g e1 t -> Subtype g t (fst (intype2 Or)) ->
    Hastype g e2 t' -> Subtype g t' (tsubBV e1 (snd (intype2 Or))) ->
    isLC e1 -> isLC e2 -> HastypeD g (ExpBinOp Or e1 e2) (tsubBV_at 1 e1 (tsubBV e2 (ty'2 Or)))
| D_TBinOP_Eq : forall g e1 e2 t t', Hastype g e1 t -> Subtype g t (fst (intype2 Eq)) ->
    Hastype g e2 t' -> Subtype g t' (tsubBV e1 (snd (intype2 Eq))) ->
    isLC e1 -> isLC e2 -> HastypeD g (ExpBinOp Eq e1 e2) (tsubBV_at 1 e1 (tsubBV e2 (ty'2 Eq)))
| D_TVar : forall g x t, bound_in x t g -> WFtype g t -> HastypeD g (FV x) (self t (FV x))
| D_TInvok : forall g e1 e2 m t t' rt C ps ps',
    Hastype g e1 (TRefn (TNom (TClass C)) ps') -> mtype(m, C) = ps ~> t ~> rt ->
    Subtype g (TRefn (TNom (TClass C)) ps') (TRefn (TNom (TClass C)) ps) ->
    Hastype g e2 t' -> Subtype g t' (tsubBV e1 t) -> isLC e2 -> isLC e1 ->
    HastypeD g (ExpMethodInvoc e1 m e2) (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2))
| D_TInvokI : forall g e1 e2 m t t' rt I ps ps',
    Hastype g e1 (TRefn (TNom (TInterface I)) ps') -> mtypei(m, I) = ps ~> t ~> rt ->
    Subtype g (TRefn (TNom (TInterface I)) ps') (TRefn (TNom (TInterface I)) ps) ->
    Hastype g e2 t' -> Subtype g t' (tsubBV e1 t) -> isLC e2 -> isLC e1 ->
    HastypeD g (ExpMethodInvoc e1 m e2) (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2))
| D_TField : forall g e f C Fs i fi ps, isLC e ->
    Hastype g e (TRefn (TNom (TClass C)) ps) -> Reffields C Fs -> nth_error Fs i = Some fi ->
    ref fi = f -> HastypeD g (ExpFieldAccess e f) (self (tsubBV e (ReffieldType fi)) (ExpFieldAccess e f))
| D_TNew : forall g es Ts C Fs Us fs, Us = map ReffieldType Fs -> fs = map ref Fs ->
    Forall isLC es -> Reffields C Fs -> Forall2 (Hastype g) es Ts ->
    Forall2 (Subtype g) Ts (map (tsubBV (ExpNew C es)) Us) ->
    HastypeD g (ExpNew C es) (self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es))
| D_TLet : forall g e_x b e b' nms, WFtype g b' -> Hastype g e_x b ->
    (forall y, ~ Elem y nms -> Hastype (Cons y b g) (unbind y e) (unbindT y b')) ->
    HastypeD g (ExpLet e_x e) (self b' (ExpLet e_x e)).

Lemma Hastype_to_D_sem : forall g e t, Hastype g e t ->
  exists s, HastypeD g e s /\
    (forall th, DenotesEnv g th -> forall v,
       Denotes (ctsubst th s) v -> Denotes (ctsubst th t) v).
Proof.
  intros g e t H.
  induction H as
   [ g b | g m | g e op t H1 IH1 Hsub Hlc
   | g e1 e2 op t t' H1 IH1 Hsub1 H2 IH2 Hsub2 Hlc1 Hlc2
   | g x t Hb Hwf
   | g e1 e2 m t t' rt C ps ps' H1 IH1 Hm Hsub H2 IH2 Hsub2 Hlc2 Hlc1
   | g e1 e2 m t t' rt I ps ps' H1 IH1 Hm Hsub H2 IH2 Hsub2 Hlc2 Hlc1
   | g e f C Fs i fi ps Hlc H1 IH1 HFs Hnth Hreff
   | g es Ts C Fs Us fs HUs Hfs HLC HFs HF2 HSub2
   | g e_x b e b' nms Hwf Hx IHx Hbody IHbody
   | g e0 s t H1 IH1 Hwf Hsub ].
  - exists (tybc b). split; [apply D_TBC | intros th Hd v HD; exact HD].
  - exists (tyic m). split; [apply D_TIC | intros th Hd v HD; exact HD].
  - destruct op.
    exists (tsubBV e (ty' Not)).
    split; [apply (D_TUnOP g e t H1 Hsub Hlc) | intros th Hd v HD; exact HD].
  - destruct op.
    + exists (tsubBV_at 1 e1 (tsubBV e2 (ty'2 And))).
      split; [apply (D_TBinOP_And g e1 e2 t t' H1 Hsub1 H2 Hsub2 Hlc1 Hlc2) | intros th Hd v HD; exact HD].
    + exists (tsubBV_at 1 e1 (tsubBV e2 (ty'2 Or))).
      split; [apply (D_TBinOP_Or g e1 e2 t t' H1 Hsub1 H2 Hsub2 Hlc1 Hlc2) | intros th Hd v HD; exact HD].
    + exists (tsubBV_at 1 e1 (tsubBV e2 (ty'2 Eq))).
      split; [apply (D_TBinOP_Eq g e1 e2 t t' H1 Hsub1 H2 Hsub2 Hlc1 Hlc2) | intros th Hd v HD; exact HD].
  - exists (self t (FV x)). split; [apply (D_TVar g x t Hb Hwf) | intros th Hd v HD; exact HD].
  - exists (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2)).
    split; [apply (D_TInvok g e1 e2 m t t' rt C ps ps' H1 Hm Hsub H2 Hsub2 Hlc2 Hlc1) | intros th Hd v HD; exact HD].
  - exists (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2)).
    split; [apply (D_TInvokI g e1 e2 m t t' rt I ps ps' H1 Hm Hsub H2 Hsub2 Hlc2 Hlc1) | intros th Hd v HD; exact HD].
  - exists (self (tsubBV e (ReffieldType fi)) (ExpFieldAccess e f)).
    split; [apply (D_TField g e f C Fs i fi ps Hlc H1 HFs Hnth Hreff) | intros th Hd v HD; exact HD].
  - exists (self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es)).
    split; [apply (D_TNew g es Ts C Fs Us fs HUs Hfs HLC HFs HF2 HSub2) | intros th Hd v HD; exact HD].
  - exists (self b' (ExpLet e_x e)).
    split; [apply (D_TLet g e_x b e b' nms Hwf Hx Hbody) | intros th Hd v HD; exact HD].
  - destruct IH1 as [s0 [HD Htr]].
    exists s0. split; [exact HD |].
    intros th Hd v HDv.
    exact (Subtype_sound g s t Hsub th Hd v (Htr th Hd v HDv)).
Qed.

(* ============ inversion of direct typing ============ *)
Lemma HastypeD_bc_inv : forall g b s, HastypeD g (Bc b) s -> s = tybc b.
Proof. intros. dependent destruction H. reflexivity. Qed.

Lemma HastypeD_ic_inv : forall g n s, HastypeD g (Ic n) s -> s = tyic n.
Proof. intros. dependent destruction H. reflexivity. Qed.

Lemma HastypeD_bv_inv : forall g i s, HastypeD g (BV i) s -> False.
Proof. intros. dependent destruction H. Qed.

Lemma HastypeD_var_inv : forall g x s, HastypeD g (FV x) s ->
  exists t, s = self t (FV x) /\ bound_in x t g /\ WFtype g t.
Proof. intros. dependent destruction H. eexists. split; [reflexivity|]. repeat split; try assumption. Qed.

Lemma HastypeD_unop_inv : forall g op e s, HastypeD g (ExpUnOp op e) s ->
  s = tsubBV e (ty' op) /\ exists t, Hastype g e t /\ Subtype g t (intype op) /\ isLC e.
Proof. intros g op e s HD. destruct op. dependent destruction HD.
  split; [reflexivity|]. eexists t. auto. Qed.

Lemma HastypeD_binop_inv : forall g op e1 e2 s, HastypeD g (ExpBinOp op e1 e2) s ->
  s = tsubBV_at 1 e1 (tsubBV e2 (ty'2 op)) /\
  exists t t', Hastype g e1 t /\ Subtype g t (fst (intype2 op)) /\
    Hastype g e2 t' /\ Subtype g t' (tsubBV e1 (snd (intype2 op))) /\ isLC e1 /\ isLC e2.
Proof.
  intros g op e1 e2 s HD. destruct op.
  - dependent destruction HD.
    split.
    + reflexivity.
    + eexists t. eexists t'. repeat split; assumption.
  - dependent destruction HD.
    split.
    + reflexivity.
    + eexists t. eexists t'. repeat split; assumption.
  - dependent destruction HD.
    split.
    + reflexivity.
    + eexists t. eexists t'. repeat split; assumption.
Qed.

Lemma HastypeD_field_inv : forall g e f s, HastypeD g (ExpFieldAccess e f) s ->
  exists C Fs i fi ps, s = self (tsubBV e (ReffieldType fi)) (ExpFieldAccess e f) /\
    isLC e /\ Hastype g e (TRefn (TNom (TClass C)) ps) /\ Reffields C Fs /\
    nth_error Fs i = Some fi /\ ref fi = f.
Proof. intros. dependent destruction H.
  eexists C. eexists Fs. eexists i. eexists fi. eexists ps.
  split; [reflexivity|]. repeat split; try assumption. Qed.

Lemma HastypeD_new_inv : forall g C es s, HastypeD g (ExpNew C es) s ->
  exists Ts Fs Us fs, s = self (TRefn (TNom (TClass C)) PEmpty) (ExpNew C es) /\
    Us = map ReffieldType Fs /\ fs = map ref Fs /\ Forall isLC es /\
    Reffields C Fs /\ Forall2 (Hastype g) es Ts /\
    Forall2 (Subtype g) Ts (map (tsubBV (ExpNew C es)) Us).
Proof. intros. dependent destruction H.
  eexists Ts. eexists Fs. eexists (map ReffieldType Fs). eexists (map ref Fs).
  split; [reflexivity|]. repeat split; try reflexivity; try assumption. Qed.

Lemma HastypeD_let_inv : forall g e_x e s, HastypeD g (ExpLet e_x e) s ->
  exists b b' nms, s = self b' (ExpLet e_x e) /\ WFtype g b' /\ Hastype g e_x b /\
    (forall y, ~ Elem y nms -> Hastype (Cons y b g) (unbind y e) (unbindT y b')).
Proof. intros. dependent destruction H.
  eexists b. eexists b'. eexists nms.
  split; [reflexivity|]. repeat split; try assumption. Qed.

Lemma Denotes_self_any : forall t E v,
  isLC E -> Denotes t v -> EvalsTo E v -> Denotes (self t E) v.
Proof.
  intros [b ps] E v Hlc Hd HE. simpl. apply Denotes_self_eq; auto.
Qed.

(* ============ closedness of class-table field types ============ *)
Lemma ctsubst_free : forall th t, free t = empty -> ctsubst th t = t.
Proof.
  intros th. induction th as [|x v th IH]; intros t Hfree.
  - reflexivity.
  - destruct t as [b ps].
    assert (Hfp : fvP ps = empty) by (exact Hfree).
    assert (Hx : ~ In x (fvP ps)).
    { intro Hx. rewrite Hfp in Hx. apply In_empty_iff in Hx. exact Hx. }
    assert (Hsub : psubFV x v ps = ps) by (apply psubFV_notin; exact Hx).
    simpl. rewrite Hsub. apply IH. exact Hfree.
Qed.

Lemma FType_OK_free : forall C fi, FType_OK C fi -> free (ReffieldType fi) = empty.
Proof.
  intros C fi H. inversion H as [C0 t f Hfree Hwf]; subst. simpl. exact Hfree.
Qed.

Lemma Forall_FType_OK_free : forall C fs, Forall (FType_OK C) fs ->
  Forall (fun fi => free (ReffieldType fi) = empty) fs.
Proof.
  intros C fs H. induction H as [|fi fs Hfi Hfs IH].
  - constructor.
  - constructor.
    + apply (FType_OK_free C fi Hfi).
    + exact IH.
Qed.

Lemma Reffields_free : forall C Fs, Reffields C Fs ->
  Forall (fun fi => free (ReffieldType fi) = empty) Fs.
Proof.
  intros C Fs H. induction H as
    [|C D Is fs noDupfs K mds noDupMds fs' Hfind HRfs IH Hnd].
  - constructor.
  - apply Forall_app. split.
    + exact IH.
    + apply (Forall_FType_OK_free C fs).
      assert (HC := cok C D fs noDupfs K Is mds noDupMds Hfind).
      inversion HC.
      assumption.
Qed.

(* ============ determinism of the class table relations ============ *)
Lemma m_body_det : forall m C e1, m_body m C e1 -> forall e2, m_body m C e2 -> e1 = e2.
Proof.
  intros m C e1 H. induction H as
    [C D Is m0 ps rt t e Fs K Ms noDupfs noDupMds Hfind Hmfind
    | C D Is m0 e Fs K Ms noDupfs noDupMds Hfind Hnone Hbody IH].
  - intros e2 H2.
    inversion H2 as
      [C2 D2 Is2 m2 ps2 rt2 t2 e2' Fs2 K2 Ms2 nd1 nd2 Hfind2 Hmfind2
      | C2 D2 Is2 m2 e2' Fs2 K2 Ms2 nd1 nd2 Hfind2 Hnone2 Hbody2].
    + rewrite Hfind in Hfind2. injection Hfind2; intros; subst.
      rewrite Hmfind in Hmfind2. injection Hmfind2; intros; subst.
      reflexivity.
    + rewrite Hfind in Hfind2. injection Hfind2; intros; subst.
      rewrite Hnone2 in Hmfind. discriminate.
  - intros e2 H2.
    inversion H2 as
      [C2 D2 Is2 m2 ps2 rt2 t2 e2' Fs2 K2 Ms2 nd1 nd2 Hfind2 Hmfind2
      | C2 D2 Is2 m2 e2' Fs2 K2 Ms2 nd1 nd2 Hfind2 Hnone2 Hbody2].
    + rewrite Hfind in Hfind2. injection Hfind2; intros; subst.
      rewrite Hmfind2 in Hnone. discriminate.
    + rewrite Hfind in Hfind2. injection Hfind2; intros; subst.
      apply IH. exact Hbody2.
Qed.

Lemma Reffields_det : forall C Fs1, Reffields C Fs1 -> forall Fs2, Reffields C Fs2 -> Fs1 = Fs2.
Proof.
  intros C Fs1 H. induction H as
    [|C D Is fs noDupfs K mds noDupMds fs' Hfind HRfs IH];
    intros Fs2 H2.
  - inversion H2 as
      [|C2 D2 Is2 fs2 nd1 K2 mds2 nd2 fs2' Hfind2 HRfs2 Hnd2]; subst.
    + reflexivity.
    + rewrite obj_notin_dom in Hfind2. discriminate.
  - inversion H2 as
      [|C2 D2 Is2 fs2 nd1 K2 mds2 nd2 fs2' Hfind2 HRfs2 Hnd2]; subst.
    + rewrite obj_notin_dom in Hfind. discriminate.
    + rewrite Hfind in Hfind2. injection Hfind2; intros; subst.
      rewrite (IH fs2' HRfs2). reflexivity.
Qed.

Lemma Reffields_NoDup : forall C Fs, Reffields C Fs -> NoDup (refs Fs).
Proof.
  intros C Fs H. induction H as
    [|C D Is fs noDupfs K mds noDupMds fs' Hfind HRfs IH Hnd].
  - constructor.
  - exact Hnd.
Qed.

Lemma nth_error_ref_unique : forall (Fs:[RefFieldDecl]) i fi j fj,
  NoDup (refs Fs) ->
  nth_error Fs i = Some fi -> nth_error Fs j = Some fj ->
  ref fi = ref fj -> i = j /\ fi = fj.
Proof.
  intros Fs. induction Fs as [|a l IH]; intros i fi j fj Hnd Hi Hj Href.
  - destruct i; simpl in Hi; discriminate.
  - simpl in Hnd. inversion Hnd as [|x l' Hnot Hnd']; subst.
    simpl in Hi, Hj.
    destruct i as [|i], j as [|j]; simpl in *.
    + injection Hi as ->. injection Hj as ->. split; reflexivity.
    + injection Hi as ->.
      exfalso. apply Hnot. rewrite Href. unfold refs.
      apply in_map with (f := @ref RefFieldDecl RefFieldRef) (x := fj).
      eapply nth_error_In; eauto.
    + injection Hj as ->.
      exfalso. apply Hnot. rewrite <- Href. unfold refs.
      apply in_map with (f := @ref RefFieldDecl RefFieldRef) (x := fi).
      eapply nth_error_In; eauto.
    + destruct (IH i fi j fj Hnd' Hi Hj Href) as [Hij Hfij].
      split; [lia | exact Hfij].
Qed.

(* ===== module uniq ===== *)
Lemma Step_BV : forall i e, Step (BV i) e -> False.
Proof. intros. inversion H. Qed.
Lemma Step_FV : forall x e, Step (FV x) e -> False.
Proof. intros. inversion H. Qed.

Lemma udelta_irrel : forall op w (pf1 pf2: isCompat op w),
  udelta op w pf1 = udelta op w pf2.
Proof. intros. dependent destruction pf1. dependent destruction pf2. reflexivity. Qed.

Lemma bdelta_irrel : forall op w1 w2 (pf1 pf2: isCompat2 op w1 w2),
  bdelta op w1 w2 pf1 = bdelta op w1 w2 pf2.
Proof. intros. dependent destruction pf1; dependent destruction pf2; simpl; auto. Qed.

Lemma unique_inner : forall F,
  (forall n, n < F -> forall e v1, EvalsToN n e v1 ->
     forall m v2, EvalsToN m e v2 -> isValue v1 -> isValue v2 -> v1 = v2) ->
  forall e v1, EvalsToN F e v1 ->
  forall m v2, EvalsToN m e v2 -> isValue v1 -> isValue v2 -> v1 = v2.
Proof.
  intros F Hsmall e.
  refine (proj1 (syntax_mutind'
    (fun ep => forall v1, EvalsToN F ep v1 ->
       forall m v2, EvalsToN m ep v2 -> isValue v1 -> isValue v2 -> v1 = v2)
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _) e).
  - (* Bc *) intros b v1 H1 m v2 H2 Hv1 Hv2.
    assert (E1 : v1 = Bc b) by (apply (EvN_value_eq F (Bc b) v1 H1); simpl; exact I).
    assert (E2 : v2 = Bc b) by (apply (EvN_value_eq m (Bc b) v2 H2); simpl; exact I).
    rewrite E1, E2. reflexivity.
  - (* Ic *) intros n v1 H1 m v2 H2 Hv1 Hv2.
    assert (E1 : v1 = Ic n) by (apply (EvN_value_eq F (Ic n) v1 H1); simpl; exact I).
    assert (E2 : v2 = Ic n) by (apply (EvN_value_eq m (Ic n) v2 H2); simpl; exact I).
    rewrite E1, E2. reflexivity.
  - (* BV *) intros i v1 H1 m v2 H2 Hv1 Hv2.
    inversion H1 as [e0 | n' a b c Hstep Htail]; subst.
    + simpl in Hv1. destruct Hv1.
    + exfalso. exact (Step_BV i b Hstep).
  - (* FV *) intros x v1 H1 m v2 H2 Hv1 Hv2.
    inversion H1 as [e0 | n' a b c Hstep Htail]; subst.
    + simpl in Hv1. destruct Hv1.
    + exfalso. exact (Step_FV x b Hstep).
  - (* UnOp *) intros op e1 IH v1 H1 m v2 H2 Hv1 Hv2.
    destruct (EvN_unop_decomp F op e1 v1 H1 Hv1) as
      [n1 [n2 [w1 [r1 [He1 [Hw1 [Hs1 [Ht1 Hn1]]]]]]]].
    destruct (EvN_unop_decomp m op e1 v2 H2 Hv2) as
      [n1' [n2' [w2 [r2 [He2 [Hw2 [Hs2 [Ht2 Hn2]]]]]]]].
    assert (Hw : w1 = w2).
    { destruct (lt_eq_lt_dec n1 F) as [[Hlt|Heq]|Hgt].
      - exact (Hsmall n1 Hlt e1 w1 He1 n1' w2 He2 Hw1 Hw2).
      - subst n1. exact (IH w1 He1 n1' w2 He2 Hw1 Hw2).
      - exfalso; lia. }
    subst w2.
    destruct (Step_UnOp_inv op w1 r1 Hs1) as [[e0 [Hst Heq]] | [w0 [pf1 [He [Hval Heq]]]]].
    + exfalso. exact (isValue_not_step w1 e0 Hw1 Hst).
    + subst w0. subst r1.
      destruct (Step_UnOp_inv op w1 r2 Hs2) as [[e0' [Hst' Heq']] | [w0' [pf2 [He' [Hval' Heq']]]]].
      * exfalso. exact (isValue_not_step w1 e0' Hw1 Hst').
      * subst w0'. subst r2.
        assert (Hr : udelta op w1 pf1 = udelta op w1 pf2) by (apply udelta_irrel).
        rewrite <- Hr in Ht2.
        exact (Hsmall n2 ltac:(lia) (udelta op w1 pf1) v1 Ht1 n2' v2 Ht2 Hv1 Hv2).
  - (* BinOp *) intros op e1 IH1 e2 IH2 v1 H1 m v2 H2 Hv1 Hv2.
    destruct (EvN_binop_decomp F op e1 e2 v1 H1 Hv1) as
      [n1 [n2 [n3 [w1 [w2 [r1 [He1 [Hw1 [He2 [Hw2 [Hs1 [Ht1 Hn1]]]]]]]]]]]].
    destruct (EvN_binop_decomp m op e1 e2 v2 H2 Hv2) as
      [n1' [n2' [n3' [w1' [w2' [r2 [He1' [Hw1' [He2' [Hw2' [Hs2 [Ht2 Hn2]]]]]]]]]]]].
    assert (Hw1eq : w1 = w1').
    { destruct (lt_eq_lt_dec n1 F) as [[Hlt|Heq]|Hgt].
      - exact (Hsmall n1 Hlt e1 w1 He1 n1' w1' He1' Hw1 Hw1').
      - subst n1. exact (IH1 w1 He1 n1' w1' He1' Hw1 Hw1').
      - exfalso; lia. }
    assert (Hw2eq : w2 = w2').
    { destruct (lt_eq_lt_dec n2 F) as [[Hlt|Heq]|Hgt].
      - exact (Hsmall n2 Hlt e2 w2 He2 n2' w2' He2' Hw2 Hw2').
      - subst n2. exact (IH2 w2 He2 n2' w2' He2' Hw2 Hw2').
      - exfalso; lia. }
    subst w1'. subst w2'.
    destruct (Step_BinOp_inv op w1 w2 r1 Hs1) as
      [[e0 [Hst Heq]] | [[e0 [Hval [Hst Heq]]] | [pf1 [Hval1 [Hval2 Heq]]]]].
    + exfalso. exact (isValue_not_step w1 e0 Hw1 Hst).
    + exfalso. exact (isValue_not_step w2 e0 Hw2 Hst).
    + subst r1.
      destruct (Step_BinOp_inv op w1 w2 r2 Hs2) as
        [[e0' [Hst' Heq']] | [[e0' [Hval' [Hst' Heq']]] | [pf2 [Hval1' [Hval2' Heq']]]]].
      * exfalso. exact (isValue_not_step w1 e0' Hw1 Hst').
      * exfalso. exact (isValue_not_step w2 e0' Hw2 Hst').
      * subst r2.
        assert (Hr : bdelta op w1 w2 pf1 = bdelta op w1 w2 pf2) by (apply bdelta_irrel).
        rewrite <- Hr in Ht2.
        exact (Hsmall n3 ltac:(lia) (bdelta op w1 w2 pf1) v1 Ht1 n3' v2 Ht2 Hv1 Hv2).
  - (* Invok *) intros e1 IH1 mname e2 IH2 v1 H1 m v2 H2 Hv1 Hv2.
    destruct (EvN_invok_decomp F e1 mname e2 v1 H1 Hv1) as
      [na1 [na2 [nb1 [C1 [es1 [vb1 [body1 Hconj1]]]]]]].
    destruct Hconj1 as [Hrec1 Hrest1].
    destruct Hrest1 as [HvalN1 Hrest1].
    destruct Hrest1 as [Harg1 Hrest1].
    destruct Hrest1 as [Hvb1 Hrest1].
    destruct Hrest1 as [Hbodyrel1 Hrest1].
    destruct Hrest1 as [Hbodyev1 Hn1].
    destruct (EvN_invok_decomp m e1 mname e2 v2 H2 Hv2) as
      [na1' [na2' [nb1' [C2 [es2 [vb2 [body2 Hconj2]]]]]]].
    destruct Hconj2 as [Hrec2 Hrest2].
    destruct Hrest2 as [HvalN2 Hrest2].
    destruct Hrest2 as [Harg2 Hrest2].
    destruct Hrest2 as [Hvb2 Hrest2].
    destruct Hrest2 as [Hbodyrel2 Hrest2].
    destruct Hrest2 as [Hbodyev2 Hn2].
    assert (Hreq : ExpNew C1 es1 = ExpNew C2 es2).
    { exact (Hsmall na1 ltac:(lia) e1 (ExpNew C1 es1) Hrec1 na1' (ExpNew C2 es2) Hrec2 HvalN1 HvalN2). }
    injection Hreq as HC Hes. subst C2. subst es2.
    assert (Hvbeq : vb1 = vb2).
    { exact (Hsmall na2 ltac:(lia) e2 vb1 Harg1 na2' vb2 Harg2 Hvb1 Hvb2). }
    subst vb2.
    assert (Hbeq : body1 = body2) by (eapply m_body_det; eauto).
    subst body2.
    exact (Hsmall nb1 ltac:(lia)
             (subBV_at 1 (ExpNew C1 es1) (subBV vb1 body1)) v1 Hbodyev1
             nb1' v2 Hbodyev2 Hv1 Hv2).
  - (* Field *) intros e1 IH f v1 H1 m v2 H2 Hv1 Hv2.
    destruct (EvN_field_decomp F e1 f v1 H1 Hv1) as
      [n1 [C1 [Fs1 [es1 [fi1 [ei1 [i1 Hconj1]]]]]]].
    destruct Hconj1 as [Hrec1 Hrest1].
    destruct Hrest1 as [Hval1 Hrest1].
    destruct Hrest1 as [HFs1 Hrest1].
    destruct Hrest1 as [HnF1 Hrest1].
    destruct Hrest1 as [Href1 Hrest1].
    destruct Hrest1 as [HnE1 Hrest1].
    destruct Hrest1 as [Hv1eq Hn1].
    destruct (EvN_field_decomp m e1 f v2 H2 Hv2) as
      [n1' [C2 [Fs2 [es2 [fi2 [ei2 [i2 Hconj2]]]]]]].
    destruct Hconj2 as [Hrec2 Hrest2].
    destruct Hrest2 as [Hval2 Hrest2].
    destruct Hrest2 as [HFs2 Hrest2].
    destruct Hrest2 as [HnF2 Hrest2].
    destruct Hrest2 as [Href2 Hrest2].
    destruct Hrest2 as [HnE2 Hrest2].
    destruct Hrest2 as [Hv2eq Hn2].
    assert (Hreq : ExpNew C1 es1 = ExpNew C2 es2).
    { exact (Hsmall n1 ltac:(lia) e1 (ExpNew C1 es1) Hrec1 n1' (ExpNew C2 es2) Hrec2 Hval1 Hval2). }
    injection Hreq as HC Hes. subst C2. subst es2.
    subst v1. subst v2.
    assert (HFs : Fs1 = Fs2) by (eapply Reffields_det; eauto).
    subst Fs2.
    assert (Hrefeq : ref fi1 = ref fi2) by (rewrite Href1; symmetry; exact Href2).
    destruct (nth_error_ref_unique Fs1 i1 fi1 i2 fi2
                (Reffields_NoDup C1 Fs1 HFs1) HnF1 HnF2 Hrefeq) as [Hi Hfi].
    subst i2. subst fi2.
    rewrite HnE1 in HnE2. injection HnE2 as Hei. subst ei2.
    reflexivity.
  - (* New *) intros C l HF v1 H1 m v2 H2 Hv1 Hv2.
    rewrite Forall_forall in HF.
    destruct (EvN_new_decomp F C l v1 H1 Hv1) as [vs1 [E1 [Len1 Hpt1]]].
    destruct (EvN_new_decomp m C l v2 H2 Hv2) as [vs2 [E2 [Len2 Hpt2]]].
    subst v1. subst v2.
    assert (Hlen : length vs1 = length vs2) by lia.
    assert (Hnth : forall i, nth_error vs1 i = nth_error vs2 i).
    { intro i.
      destruct (nth_error vs1 i) as [b1|] eqn:Eb1.
      - assert (Hilt : i < length l).
        { rewrite Len1. apply nth_error_Some. rewrite Eb1. discriminate. }
        destruct (nth_error l i) as [a|] eqn:Ea.
        + destruct (Hpt1 i a Ea) as [b1' [nb1 [Hb1' [Hev1 Hle1]]]].
          rewrite Eb1 in Hb1'. injection Hb1' as Hb1eq. subst b1'.
          destruct (Hpt2 i a Ea) as [b2 [nb2 [Hb2' [Hev2 Hle2]]]].
          assert (Hvb1 : isValue b1).
          { change (isValueL vs1) in Hv1.
            exact (isValueL_nth vs1 i b1 Hv1 Eb1). }
          assert (Hvb2 : isValue b2).
          { change (isValueL vs2) in Hv2.
            exact (isValueL_nth vs2 i b2 Hv2 Hb2'). }
          assert (Hb12 : b1 = b2).
          { destruct (lt_eq_lt_dec nb1 F) as [[Hlt|Heq]|Hgt].
            - exact (Hsmall nb1 Hlt a b1 Hev1 nb2 b2 Hev2 Hvb1 Hvb2).
            - subst nb1. exact (HF a (nth_error_In l i Ea) b1 Hev1 nb2 b2 Hev2 Hvb1 Hvb2).
            - exfalso; lia. }
          rewrite Hb2', Hb12. reflexivity.
        + apply nth_error_None in Ea. lia.
      - destruct (nth_error vs2 i) as [b2|] eqn:Eb2; [|reflexivity].
        exfalso.
        assert (Hilt : i < length l).
        { rewrite Len2. apply nth_error_Some. rewrite Eb2. discriminate. }
        destruct (nth_error l i) as [a|] eqn:Ea.
        + destruct (Hpt1 i a Ea) as [b1 [nb1 [Hb1 [Hev1 Hle1]]]].
          rewrite Eb1 in Hb1. discriminate.
        + apply nth_error_None in Ea. lia. }
    rewrite (nth_error_ext vs1 vs2 Hlen Hnth). reflexivity.
  - (* Let *) intros e1 IH1 e2 IH2 v1 H1 m v2 H2 Hv1 Hv2.
    destruct (EvN_let_decomp F e1 e2 v1 H1 Hv1) as
      [nx [n2 [vx Hconj1]]].
    destruct Hconj1 as [Hx Hrest1].
    destruct Hrest1 as [Hvx Hrest1].
    destruct Hrest1 as [Hbody Hn1].
    destruct (EvN_let_decomp m e1 e2 v2 H2 Hv2) as
      [nx' [n2' [vx' Hconj2]]].
    destruct Hconj2 as [Hx' Hrest2].
    destruct Hrest2 as [Hvx' Hrest2].
    destruct Hrest2 as [Hbody' Hn2].
    assert (Hvxeq : vx = vx').
    { exact (Hsmall nx ltac:(lia) e1 vx Hx nx' vx' Hx' Hvx Hvx'). }
    subst vx'.
    exact (Hsmall n2 ltac:(lia) (subBV_at 0 vx e2) v1 Hbody n2' v2 Hbody' Hv1 Hv2).
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma unique_all : forall n e v1, EvalsToN n e v1 ->
  forall m v2, EvalsToN m e v2 -> isValue v1 -> isValue v2 -> v1 = v2.
Proof.
  intros n.
  apply (lt_wf_rect n (fun n => forall e v1, EvalsToN n e v1 ->
    forall m v2, EvalsToN m e v2 -> isValue v1 -> isValue v2 -> v1 = v2)).
  intros n' Hrec e v1 H1 m v2 H2 Hv1 Hv2.
  exact (unique_inner n' (fun n0 Hlt => Hrec n0 Hlt) e v1 H1 m v2 H2 Hv1 Hv2).
Qed.

Lemma EvalsTo_unique : forall e v1 v2,
  EvalsTo e v1 -> EvalsTo e v2 -> isValue v1 -> isValue v2 -> v1 = v2.
Proof.
  intros e v1 v2 HE1 HE2 Hv1 Hv2.
  destruct (EvalsTo_EvN e v1 HE1) as [n Hn].
  destruct (EvalsTo_EvN e v2 HE2) as [m Hm].
  exact (unique_all n e v1 Hn m v2 Hm Hv1 Hv2).
Qed.

(* ===== module fwd ===== *)
Lemma subBV_New_map : forall j w C l,
  subBV_at j w (ExpNew C l) = ExpNew C (map (subBV_at j w) l).
Proof. intros. simpl. reflexivity. Qed.

Lemma sim_subBV_fwd : forall p j E V z,
  bvCover j p -> isLC E -> EvalsTo E V -> isValue V -> isValue z ->
  EvalsTo (subBV_at j E p) z -> EvalsTo (subBV_at j V p) z.
Proof.
  refine (proj1 (syntax_mutind'
    (fun p => forall j E V z, bvCover j p -> isLC E -> EvalsTo E V -> isValue V ->
       isValue z -> EvalsTo (subBV_at j E p) z -> EvalsTo (subBV_at j V p) z)
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - (* Bc *) intros b j E V z Hbv HE HEV HV Hz H. simpl. simpl in H. exact H.
  - (* Ic *) intros n j E V z Hbv HE HEV HV Hz H. simpl. simpl in H. exact H.
  - (* BV *) intros i j E V z Hbv HE HEV HV Hz H.
    simpl in Hbv. subst i.
    assert (HjE : subBV_at j E (BV j) = E)
      by (simpl; rewrite Nat.eqb_refl; reflexivity).
    assert (HjV : subBV_at j V (BV j) = V)
      by (simpl; rewrite Nat.eqb_refl; reflexivity).
    rewrite HjE in H. rewrite HjV.
    assert (HzV : z = V) by (apply (EvalsTo_unique E z V H HEV Hz HV)).
    subst z. apply Refl.
  - (* FV *) intros x j E V z Hbv HE HEV HV Hz H. simpl. simpl in H. exact H.
  - (* UnOp *) intros op p IH j E V z Hbv HE HEV HV Hz H.
    simpl in H. simpl.
    destruct (EvalsTo_unop_inv op (subBV_at j E p) z H Hz) as [w [H1 [Hw Hfin]]].
    assert (Hbvp : bvCover j p) by (simpl in Hbv; exact Hbv).
    assert (H1' : EvalsTo (subBV_at j V p) w) by
      (apply (IH j E V w Hbvp HE HEV HV Hw H1)).
    eapply EvalsTo_trans with (b := ExpUnOp op w).
    + apply EvalsTo_unop. exact H1'.
    + exact Hfin.
  - (* BinOp *) intros op p1 IH1 p2 IH2 j E V z Hbv HE HEV HV Hz H.
    simpl in H. simpl.
    destruct (EvalsTo_binop_inv op (subBV_at j E p1) (subBV_at j E p2) z H Hz) as
      [w1 [w2 [H1 [Hw1 [H2 [Hw2 Hfin]]]]]].
    destruct Hbv as [Hbv1 Hbv2].
    assert (H1' : EvalsTo (subBV_at j V p1) w1) by
      (apply (IH1 j E V w1 Hbv1 HE HEV HV Hw1 H1)).
    assert (H2' : EvalsTo (subBV_at j V p2) w2) by
      (apply (IH2 j E V w2 Hbv2 HE HEV HV Hw2 H2)).
    eapply EvalsTo_trans with (b := ExpBinOp op w1 (subBV_at j V p2)).
    + apply EvalsTo_binop_l. exact H1'.
    + eapply EvalsTo_trans with (b := ExpBinOp op w1 w2).
      * apply EvalsTo_binop_r; auto.
      * exact Hfin.
  - (* Invok *) intros p1 IH1 mname p2 IH2 j E V z Hbv HE HEV HV Hz H.
    simpl in H. simpl.
    destruct Hbv as [Hbv1 Hbv2].
    destruct (EvalsTo_invok_inv (subBV_at j E p1) mname (subBV_at j E p2) z H Hz) as
      [C [es [vb [body [Hrec [HvalN [Harg [Hvb [Hbodyrel Ht]]]]]]]]].
    assert (Hrec' : EvalsTo (subBV_at j V p1) (ExpNew C es)) by
      (apply (IH1 j E V (ExpNew C es) Hbv1 HE HEV HV HvalN Hrec)).
    assert (Harg' : EvalsTo (subBV_at j V p2) vb) by
      (apply (IH2 j E V vb Hbv2 HE HEV HV Hvb Harg)).
    eapply EvalsTo_trans with (b := ExpMethodInvoc (ExpNew C es) mname (subBV_at j V p2)).
    + apply EvalsTo_invok_l. exact Hrec'.
    + eapply EvalsTo_trans with (b := ExpMethodInvoc (ExpNew C es) mname vb).
      * apply EvalsTo_invok_r; auto.
      * eapply EvalsTo_trans with (b := subBV_at 1 (ExpNew C es) (subBV vb body)).
        -- eapply AddStep; [|apply Refl]. eapply Refc_Invok3; eauto.
        -- exact Ht.
  - (* Field *) intros p IH f j E V z Hbv HE HEV HV Hz H.
    simpl in H. simpl.
    destruct (EvalsTo_field_inv (subBV_at j E p) f z H Hz) as
      [C [Fs [es [fi [ei [i [Hrec [HFs [HnF [Hrf [HnE [HvalNew Hz_eq]]]]]]]]]]]].
    subst z.
    assert (Hrec' : EvalsTo (subBV_at j V p) (ExpNew C es)) by
      (apply (IH j E V (ExpNew C es) Hbv HE HEV HV HvalNew Hrec)).
    eapply EvalsTo_trans with (b := ExpFieldAccess (ExpNew C es) f).
    + apply EvalsTo_field. exact Hrec'.
    + eapply AddStep; [|apply Refl]. rewrite <- Hrf. eapply Refc_Field; eauto.
  - (* New *) intros C l HF j E V z Hbv HE HEV HV Hz H.
    rewrite Forall_forall in HF.
    assert (HbvL : Forall (bvCover j) l).
    { apply bvCover_Forall. simpl in Hbv. exact Hbv. }
    rewrite Forall_forall in HbvL.
    rewrite subBV_New_map in H.
    rewrite subBV_New_map.
    destruct (EvalsTo_new_inv C (map (subBV_at j E) l) z H) as
      [zs [Hz_eq [Hlen Hpt]]].
    subst z.
    apply EvalsTo_new_Forall2.
    eapply Forall2_nth_Some_all.
    + rewrite !length_map. rewrite length_map in Hlen. exact Hlen.
    + intros i a' Ha'.
      destruct (nth_error_map_Some (subBV_at j V) l i a' Ha') as [a [Ha Haeq]].
      subst a'.
      assert (HEa : nth_error (map (subBV_at j E) l) i = Some (subBV_at j E a)).
      { rewrite nth_error_map. rewrite Ha. simpl. reflexivity. }
      destruct (Hpt i (subBV_at j E a) HEa) as [b [Hb Hev]].
      exists b. split; [exact Hb|].
      assert (Hvb : isValue b).
      { change (isValueL zs) in Hz.
        exact (isValueL_nth zs i b Hz Hb). }
      exact (HF a (nth_error_In l i Ha) j E V b
               (HbvL a (nth_error_In l i Ha)) HE HEV HV Hvb Hev).
  - (* Let *) intros p1 IH1 p2 IH2 j E V z Hbv HE HEV HV Hz H.
    simpl in H. simpl.
    destruct Hbv as [Hbv1 Hbv2].
    destruct (EvalsTo_let_inv (subBV_at j E p1) (subBV_at (j+1) E p2) z H Hz) as
      [vx [H1 [Hvx Hbody]]].
    assert (H1' : EvalsTo (subBV_at j V p1) vx) by
      (apply (IH1 j E V vx Hbv1 HE HEV HV Hvx H1)).
    assert (HbodyE : subBV_at 0 vx (subBV_at (j+1) E p2) = subBV_at (j+1) E p2).
    { apply subBV_at_LC. apply (isLC_subBV_cover p2 (j+1) E Hbv2 HE). }
    assert (HbodyV : subBV_at 0 vx (subBV_at (j+1) V p2) = subBV_at (j+1) V p2).
    { apply subBV_at_LC. apply (isLC_subBV_cover p2 (j+1) V Hbv2).
      apply isValue_isLC; exact HV. }
    rewrite HbodyE in Hbody.
    assert (Hbody' : EvalsTo (subBV_at (j+1) V p2) z) by
      (apply (IH2 (j+1) E V z Hbv2 HE HEV HV Hz Hbody)).
    eapply EvalsTo_trans with (b := ExpLet vx (subBV_at (j+1) V p2)).
    + apply EvalsTo_let_l. exact H1'.
    + eapply EvalsTo_trans with (b := subBV_at 0 vx (subBV_at (j+1) V p2)).
      * eapply AddStep; [|apply Refl]. apply ELetV. exact Hvx.
      * rewrite HbodyV. exact Hbody'.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

(* ===== module imp ===== *)
Fixpoint bvCover2 (j:nat) (e:expr) {struct e} : Prop :=
  match e with
  | Bc _ | Ic _ | FV _ => True
  | BV i => i = j \/ i = j + 1
  | ExpUnOp _ e1 => bvCover2 j e1
  | ExpFieldAccess e1 _ => bvCover2 j e1
  | ExpBinOp _ e1 e2 => bvCover2 j e1 /\ bvCover2 j e2
  | ExpMethodInvoc e1 _ e2 => bvCover2 j e1 /\ bvCover2 j e2
  | ExpNew _ l => (fix g (l0:[expr]) := match l0 with nil => True | a::l' => bvCover2 j a /\ g l' end) l
  | ExpLet a b => bvCover2 j a /\ bvCover2 (j+1) b
  end.

Lemma isValue_bvCover : forall w, isValue w -> forall j, bvCover j w.
Proof.
  refine (proj1 (syntax_mutind'
    (fun w => isValue w -> forall j, bvCover j w)
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - simpl; auto.
  - simpl; auto.
  - simpl; intros i H; destruct H.
  - simpl; intros x H; destruct H.
  - simpl; intros o e IH H; destruct H.
  - simpl; intros o e1 IH1 e2 IH2 H; destruct H.
  - simpl; intros e1 IH1 m e2 IH2 H; destruct H.
  - simpl; intros e IH f H; destruct H.
  - simpl. intros c l HF H. revert HF H.
    induction l as [|a l IHs]; simpl; intros HF H.
    + intro j; exact I.
    + destruct H as [Ha Hl]. inversion HF as [|? ? Pa Pl]; subst. intro j. split.
      * apply (Pa Ha j).
      * apply (IHs Pl Hl j).
  - simpl; intros e1 IH1 e2 IH2 H; destruct H.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma bvCover2_subBV : forall p j w,
  bvCover2 j p -> isValue w -> bvCover (j+1) (subBV_at j w p).
Proof.
  refine (proj1 (syntax_mutind'
    (fun p => forall j w, bvCover2 j p -> isValue w ->
       bvCover (j+1) (subBV_at j w p))
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - simpl; auto.
  - simpl; auto.
  - simpl. intros i j w Hbv Hw. simpl in Hbv.
    destruct Hbv as [Heq|Heq]; subst i.
    + rewrite Nat.eqb_refl. simpl. apply isValue_bvCover; exact Hw.
    + destruct (j =? j+1) eqn:E.
      * apply Nat.eqb_eq in E. exfalso. lia.
      * simpl; auto.
  - simpl; auto.
  - simpl; intros o e IH j w Hbv Hw. apply IH; auto.
  - simpl; intros o e1 IH1 e2 IH2 j w [H1 H2] Hw. split; auto.
  - simpl; intros e1 IH1 m e2 IH2 j w [H1 H2] Hw. split; auto.
  - simpl; intros e IH f j w Hbv Hw. apply IH; auto.
  - simpl. intros C l HF j w Hbv Hw. simpl. simpl in Hbv.
    revert HF Hbv. induction l as [|a l IHs]; simpl; intros HF Hbv.
    + exact I.
    + destruct Hbv as [Ha Hl]. inversion HF as [|? ? Pa Pl]; subst. split.
      * apply (Pa j w Ha Hw).
      * apply (IHs Pl Hl).
  - simpl; intros e1 IH1 e2 IH2 j w [H1 H2] Hw. split.
    + exact (IH1 j w H1 Hw).
    + exact (IH2 (j+1) w H2 Hw).
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma comm_subBV : forall p j k E w,
  j <> k -> isLC E -> isValue w ->
  subBV_at k w (subBV_at j E p) = subBV_at j E (subBV_at k w p).
Proof.
  refine (proj1 (syntax_mutind'
    (fun p => forall j k E w, j <> k -> isLC E -> isValue w ->
       subBV_at k w (subBV_at j E p) = subBV_at j E (subBV_at k w p))
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - simpl; auto.
  - simpl; auto.
  - simpl. intros i j k E w Hjk HE Hw.
    destruct (j =? i) eqn:Ej; destruct (k =? i) eqn:Ek; simpl.
    + exfalso. apply Nat.eqb_eq in Ej. apply Nat.eqb_eq in Ek. lia.
    + try rewrite Ej. try rewrite Ek. simpl. apply (subBV_at_LC E k).
      apply isLC_at_mono with (j:=0); [lia|exact HE].
    + try rewrite Ej. try rewrite Ek. simpl. symmetry. apply (subBV_at_LC w j).
      apply isValue_isLC'; exact Hw.
    + try rewrite Ej. try rewrite Ek. simpl. reflexivity.
  - simpl; auto.
  - simpl; intros o e IH j k E w Hjk HE Hw. rewrite (IH j k E w); auto.
  - simpl; intros o e1 IH1 e2 IH2 j k E w Hjk HE Hw.
    rewrite (IH1 j k E w); auto. rewrite (IH2 j k E w); auto.
  - simpl; intros e1 IH1 m e2 IH2 j k E w Hjk HE Hw.
    rewrite (IH1 j k E w); auto. rewrite (IH2 j k E w); auto.
  - simpl; intros e IH f j k E w Hjk HE Hw. rewrite (IH j k E w); auto.
  - intros C l HF j k E w Hjk HE Hw.
    rewrite subBV_New_map. rewrite subBV_New_map.
    rewrite subBV_New_map. rewrite subBV_New_map.
    f_equal.
    revert HF. induction l as [|a l IHs]; simpl; intros HF.
    + reflexivity.
    + inversion HF as [|? ? Pa Pl]; subst. simpl.
      rewrite (Pa j k E w Hjk HE Hw).
      f_equal. apply IHs; exact Pl.
  - simpl; intros e1 IH1 e2 IH2 j k E w Hjk HE Hw.
    simpl.
    rewrite (IH1 j k E w); auto.
    rewrite (IH2 (j+1) (k+1) E w); auto. lia.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Fixpoint InP (p:expr) (ps:preds) : Prop :=
  match ps with
  | PEmpty => False
  | PCons q qs => p = q \/ InP p qs
  end.

Lemma PEvals_subst_fwd : forall (ps:preds) E V w,
  (forall p, InP p ps -> bvCover2 0 p) ->
  isLC E -> isValue V -> EvalsTo E V -> isValue w ->
  PEvalsTrue (psubBV w (psubBV_at 1 E ps)) ->
  PEvalsTrue (psubBV w (psubBV_at 1 V ps)).
Proof.
  induction ps as [|p ps IH]; intros E V w Hc HE HVv HEV Hw HP; simpl in HP.
  - exact HP.
  - inversion HP as [|p0 ps0 Hhead Htail]; subst.
    apply PECons.
    + change (EvalsTo (subBV_at 0 w (subBV_at 1 V p)) (Bc true)).
      change (EvalsTo (subBV_at 0 w (subBV_at 1 E p)) (Bc true)) in Hhead.
      rewrite (comm_subBV p 1 0 V w); [|lia|apply isValue_isLC; exact HVv|exact Hw].
      rewrite (comm_subBV p 1 0 E w) in Hhead; [|lia|exact HE|exact Hw].
      apply (sim_subBV_fwd (subBV_at 0 w p) 1 E V (Bc true)).
      * apply (bvCover2_subBV p 0 w (Hc p (or_introl eq_refl)) Hw).
      * exact HE.
      * exact HEV.
      * exact HVv.
      * simpl; exact I.
      * exact Hhead.
    + apply (IH E V w).
      * intros q Hq. apply Hc. right. exact Hq.
      * exact HE.
      * exact HVv.
      * exact HEV.
      * exact Hw.
      * exact Htail.
Qed.

Lemma Denotes_tsubBV_fwd : forall b (ps:preds) v E V,
  (forall p, InP p ps -> bvCover2 0 p) ->
  isLC E -> isLC V -> EvalsTo E V -> isValue V -> isValue v ->
  Denotes (TRefn b (psubBV_at 1 E ps)) v ->
  Denotes (TRefn b (psubBV_at 1 V ps)) v.
Proof.
  intros b ps v E V Hc HE HLV HEV HVv Hv HD.
  apply (Denotes_impl b (psubBV_at 1 E ps) (psubBV_at 1 V ps) v).
  - intro HP. apply (PEvals_subst_fwd ps E V v Hc HE HVv HEV Hv HP).
  - exact HD.
Qed.

(* ===== module ctx ===== *)
Lemma subBV_many_LC : forall ws e, isLC e -> subBV_many ws e = e.
Proof.
  intros ws. induction ws as [|w ws IH]; intros e He.
  - reflexivity.
  - simpl.
    assert (Hid : subBV_at (length ws - 0) w e = e).
    { apply subBV_at_LC. apply isLC_at_mono with (j:=0); [lia|exact He]. }
    rewrite Hid. apply IH; exact He.
Qed.

Lemma subBV_many_cons : forall w ws e,
  subBV_many (w::ws) e = subBV_many ws (subBV_at (length ws) w e).
Proof.
  intros. cbn [subBV_many].
  replace (length (w::ws) - 1) with (length ws) by (simpl; lia).
  reflexivity.
Qed.

Lemma subBV_many_let : forall ws A B,
  exists B', subBV_many ws (ExpLet A B) = ExpLet (subBV_many ws A) B' /\
    (forall vx, subBV_at 0 vx B' = subBV_many (ws ++ (vx :: nil)) B).
Proof.
  induction ws as [|w ws IH]; intros A B.
  - exists B. split; [reflexivity|]. intro vx. reflexivity.
  - destruct (IH (subBV_at (length ws) w A) (subBV_at (length ws + 1) w B))
      as [B' [Heq Hprop]].
    exists B'. split.
    + rewrite (subBV_many_cons w ws (ExpLet A B)).
      rewrite (subBV_many_cons w ws A).
      assert (Hsplit : subBV_at (length ws) w (ExpLet A B)
                       = ExpLet (subBV_at (length ws) w A)
                                (subBV_at (length ws + 1) w B)) by reflexivity.
      rewrite Hsplit.
      rewrite Heq. reflexivity.
    + intro vx.
      rewrite Hprop.
      change (subBV_many (ws ++ (vx :: nil)) (subBV_at (length ws + 1) w B)
              = subBV_many (w :: (ws ++ (vx :: nil))) B).
      rewrite (subBV_many_cons w (ws ++ (vx :: nil)) B).
      replace (length (ws ++ (vx :: nil))) with (length ws + 1)
        by (rewrite length_app; simpl; lia).
      reflexivity.
Qed.

Lemma subBV_many_UnOp : forall ws o e,
  subBV_many ws (ExpUnOp o e) = ExpUnOp o (subBV_many ws e).
Proof.
  induction ws as [|w ws IH]; intros o e.
  - reflexivity.
  - rewrite (subBV_many_cons w ws (ExpUnOp o e)).
    rewrite (subBV_many_cons w ws e).
    change (subBV_many ws (ExpUnOp o (subBV_at (length ws) w e))
            = ExpUnOp o (subBV_many ws (subBV_at (length ws) w e))).
    rewrite (IH o (subBV_at (length ws) w e)). reflexivity.
Qed.

Lemma subBV_many_BinOp : forall ws o e1 e2,
  subBV_many ws (ExpBinOp o e1 e2) = ExpBinOp o (subBV_many ws e1) (subBV_many ws e2).
Proof.
  induction ws as [|w ws IH]; intros o e1 e2.
  - reflexivity.
  - rewrite (subBV_many_cons w ws (ExpBinOp o e1 e2)).
    rewrite (subBV_many_cons w ws e1).
    rewrite (subBV_many_cons w ws e2).
    change (subBV_many ws
       (ExpBinOp o (subBV_at (length ws) w e1) (subBV_at (length ws) w e2))
       = ExpBinOp o (subBV_many ws (subBV_at (length ws) w e1))
                    (subBV_many ws (subBV_at (length ws) w e2))).
    rewrite (IH o (subBV_at (length ws) w e1) (subBV_at (length ws) w e2)).
    reflexivity.
Qed.

Lemma subBV_many_Invok : forall ws e1 m e2,
  subBV_many ws (ExpMethodInvoc e1 m e2)
  = ExpMethodInvoc (subBV_many ws e1) m (subBV_many ws e2).
Proof.
  induction ws as [|w ws IH]; intros e1 m e2.
  - reflexivity.
  - rewrite (subBV_many_cons w ws (ExpMethodInvoc e1 m e2)).
    rewrite (subBV_many_cons w ws e1).
    rewrite (subBV_many_cons w ws e2).
    change (subBV_many ws
       (ExpMethodInvoc (subBV_at (length ws) w e1) m (subBV_at (length ws) w e2))
       = ExpMethodInvoc (subBV_many ws (subBV_at (length ws) w e1)) m
                        (subBV_many ws (subBV_at (length ws) w e2))).
    rewrite (IH (subBV_at (length ws) w e1) m (subBV_at (length ws) w e2)).
    reflexivity.
Qed.

Lemma subBV_many_Field : forall ws e f,
  subBV_many ws (ExpFieldAccess e f) = ExpFieldAccess (subBV_many ws e) f.
Proof.
  induction ws as [|w ws IH]; intros e f.
  - reflexivity.
  - rewrite (subBV_many_cons w ws (ExpFieldAccess e f)).
    rewrite (subBV_many_cons w ws e).
    change (subBV_many ws (ExpFieldAccess (subBV_at (length ws) w e) f)
            = ExpFieldAccess (subBV_many ws (subBV_at (length ws) w e)) f).
    rewrite (IH (subBV_at (length ws) w e) f). reflexivity.
Qed.

Lemma subBV_many_New : forall ws C l,
  subBV_many ws (ExpNew C l) = ExpNew C (map (subBV_many ws) l).
Proof.
  induction ws as [|w ws IH]; intros C l.
  - simpl. f_equal. symmetry. apply map_id.
  - rewrite (subBV_many_cons w ws (ExpNew C l)).
    change (subBV_many ws (ExpNew C (map (subBV_at (length ws) w) l))
            = ExpNew C (map (subBV_many (w::ws)) l)).
    rewrite (IH C (map (subBV_at (length ws) w) l)).
    f_equal. rewrite map_map. apply map_ext. intro x.
    symmetry. apply subBV_many_cons.
Qed.

Lemma sim_ctx : forall p ws j E V z,
  isLC E -> EvalsTo E V -> isValue V -> isValue z ->
  EvalsTo (subBV_many ws (subBV_at j E p)) z ->
  EvalsTo (subBV_many ws (subBV_at j V p)) z.
Proof.
  refine (proj1 (syntax_mutind'
    (fun p => forall ws j E V z, isLC E -> EvalsTo E V -> isValue V -> isValue z ->
       EvalsTo (subBV_many ws (subBV_at j E p)) z ->
       EvalsTo (subBV_many ws (subBV_at j V p)) z)
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - intros b ws j E V z HE HEV HV Hz H. exact H.
  - intros n ws j E V z HE HEV HV Hz H. exact H.
  - intros i ws j E V z HE HEV HV Hz H. simpl in H.
    destruct (j =? i) eqn:Ej.
    + apply Nat.eqb_eq in Ej. subst i.
      rewrite subBV_many_LC in H; [|exact HE].
      assert (HzV : z = V) by (apply (EvalsTo_unique E z V H HEV Hz HV)).
      subst z. simpl. rewrite Nat.eqb_refl. simpl.
      rewrite subBV_many_LC; [apply Refl|apply isValue_isLC; exact HV].
    + simpl. rewrite Ej. simpl. exact H.
  - intros x ws j E V z HE HEV HV Hz H. exact H.
  - intros o p IH ws j E V z HE HEV HV Hz H.
    change (EvalsTo (subBV_many ws (ExpUnOp o (subBV_at j E p))) z) in H.
    change (EvalsTo (subBV_many ws (ExpUnOp o (subBV_at j V p))) z).
    rewrite subBV_many_UnOp in H. rewrite subBV_many_UnOp.
    destruct (EvalsTo_unop_inv o (subBV_many ws (subBV_at j E p)) z H Hz) as
      [w [H1 [Hw Hfin]]].
    assert (H1' : EvalsTo (subBV_many ws (subBV_at j V p)) w) by
      (apply (IH ws j E V w HE HEV HV Hw H1)).
    eapply EvalsTo_trans with (b := ExpUnOp o w).
    + apply EvalsTo_unop. exact H1'.
    + exact Hfin.
  - intros o p1 IH1 p2 IH2 ws j E V z HE HEV HV Hz H.
    change (EvalsTo (subBV_many ws (ExpBinOp o (subBV_at j E p1) (subBV_at j E p2))) z) in H.
    change (EvalsTo (subBV_many ws (ExpBinOp o (subBV_at j V p1) (subBV_at j V p2))) z).
    rewrite subBV_many_BinOp in H. rewrite subBV_many_BinOp.
    destruct (EvalsTo_binop_inv o (subBV_many ws (subBV_at j E p1))
                (subBV_many ws (subBV_at j E p2)) z H Hz) as
      [w1 [w2 [H1 [Hw1 [H2 [Hw2 Hfin]]]]]].
    assert (H1' : EvalsTo (subBV_many ws (subBV_at j V p1)) w1) by
      (apply (IH1 ws j E V w1 HE HEV HV Hw1 H1)).
    assert (H2' : EvalsTo (subBV_many ws (subBV_at j V p2)) w2) by
      (apply (IH2 ws j E V w2 HE HEV HV Hw2 H2)).
    eapply EvalsTo_trans with (b := ExpBinOp o w1 (subBV_many ws (subBV_at j V p2))).
    + apply EvalsTo_binop_l. exact H1'.
    + eapply EvalsTo_trans with (b := ExpBinOp o w1 w2).
      * apply EvalsTo_binop_r; auto.
      * exact Hfin.
  - intros p1 IH1 m p2 IH2 ws j E V z HE HEV HV Hz H.
    change (EvalsTo (subBV_many ws
      (ExpMethodInvoc (subBV_at j E p1) m (subBV_at j E p2))) z) in H.
    change (EvalsTo (subBV_many ws
      (ExpMethodInvoc (subBV_at j V p1) m (subBV_at j V p2))) z).
    rewrite subBV_many_Invok in H. rewrite subBV_many_Invok.
    destruct (EvalsTo_invok_inv (subBV_many ws (subBV_at j E p1)) m
                (subBV_many ws (subBV_at j E p2)) z H Hz) as
      [C [es [vb [body [Hrec [HvalN [Harg [Hvb [Hbodyrel Ht]]]]]]]]].
    assert (Hrec' : EvalsTo (subBV_many ws (subBV_at j V p1)) (ExpNew C es)) by
      (apply (IH1 ws j E V (ExpNew C es) HE HEV HV HvalN Hrec)).
    assert (Harg' : EvalsTo (subBV_many ws (subBV_at j V p2)) vb) by
      (apply (IH2 ws j E V vb HE HEV HV Hvb Harg)).
    eapply EvalsTo_trans with
      (b := ExpMethodInvoc (ExpNew C es) m (subBV_many ws (subBV_at j V p2))).
    + apply EvalsTo_invok_l. exact Hrec'.
    + eapply EvalsTo_trans with (b := ExpMethodInvoc (ExpNew C es) m vb).
      * apply EvalsTo_invok_r; auto.
      * eapply EvalsTo_trans with
          (b := subBV_at 1 (ExpNew C es) (subBV vb body)).
        -- eapply AddStep; [|apply Refl]. eapply Refc_Invok3; eauto.
        -- exact Ht.
  - intros p IH f ws j E V z HE HEV HV Hz H.
    change (EvalsTo (subBV_many ws (ExpFieldAccess (subBV_at j E p) f)) z) in H.
    change (EvalsTo (subBV_many ws (ExpFieldAccess (subBV_at j V p) f)) z).
    rewrite subBV_many_Field in H. rewrite subBV_many_Field.
    destruct (EvalsTo_field_inv (subBV_many ws (subBV_at j E p)) f z H Hz) as
      [C [Fs [es [fi [ei [i [Hrec [HFs [HnF [Hrf [HnE [HvalNew Hz_eq]]]]]]]]]]]].
    subst z.
    assert (Hrec' : EvalsTo (subBV_many ws (subBV_at j V p)) (ExpNew C es)) by
      (apply (IH ws j E V (ExpNew C es) HE HEV HV HvalNew Hrec)).
    eapply EvalsTo_trans with (b := ExpFieldAccess (ExpNew C es) f).
    + apply EvalsTo_field. exact Hrec'.
    + eapply AddStep; [|apply Refl]. rewrite <- Hrf. eapply Refc_Field; eauto.
  - intros C l HF ws j E V z HE HEV HV Hz H.
    rewrite Forall_forall in HF.
    change (EvalsTo (subBV_many ws (ExpNew C (map (subBV_at j E) l))) z) in H.
    change (EvalsTo (subBV_many ws (ExpNew C (map (subBV_at j V) l))) z).
    rewrite subBV_many_New in H. rewrite subBV_many_New.
    destruct (EvalsTo_new_inv C (map (subBV_many ws) (map (subBV_at j E) l)) z H)
      as [zs [Hz_eq [Hlen Hpt]]].
    subst z.
    apply EvalsTo_new_Forall2.
    eapply Forall2_nth_Some_all.
    + rewrite !length_map. rewrite !length_map in Hlen. exact Hlen.
    + intros i a' Ha'.
      destruct (nth_error_map_Some (subBV_many ws) (map (subBV_at j V) l) i a' Ha')
        as [x [Hx Hxeq]].
      subst a'.
      destruct (nth_error_map_Some (subBV_at j V) l i x Hx) as [a [Ha Haeq]].
      subst x.
      assert (HEa : nth_error (map (subBV_many ws) (map (subBV_at j E) l)) i
                   = Some (subBV_many ws (subBV_at j E a))).
      { rewrite !nth_error_map. rewrite Ha. simpl. reflexivity. }
      destruct (Hpt i (subBV_many ws (subBV_at j E a)) HEa) as [b [Hb Hev]].
      exists b. split; [exact Hb|].
      assert (Hvb : isValue b).
      { change (isValueL zs) in Hz. exact (isValueL_nth zs i b Hz Hb). }
      exact (HF a (nth_error_In l i Ha) ws j E V b HE HEV HV Hvb Hev).
  - intros a IH1 b IH2 ws j E V z HE HEV HV Hz H.
    change (EvalsTo (subBV_many ws (ExpLet (subBV_at j E a) (subBV_at (j+1) E b))) z) in H.
    destruct (subBV_many_let ws (subBV_at j E a) (subBV_at (j+1) E b))
      as [BE [HeqE HpropE]].
    rewrite HeqE in H.
    destruct (EvalsTo_let_inv _ _ _ H Hz) as [vx [Hx [Hvx Hbody]]].
    rewrite (HpropE vx) in Hbody.
    assert (Hx' : EvalsTo (subBV_many ws (subBV_at j V a)) vx) by
      (apply (IH1 ws j E V vx HE HEV HV Hvx Hx)).
    assert (Hbody' : EvalsTo (subBV_many (ws ++ (vx :: nil)) (subBV_at (j+1) V b)) z) by
      (apply (IH2 (ws ++ (vx :: nil)) (j+1) E V z HE HEV HV Hz Hbody)).
    change (EvalsTo (subBV_many ws (ExpLet (subBV_at j V a) (subBV_at (j+1) V b))) z).
    destruct (subBV_many_let ws (subBV_at j V a) (subBV_at (j+1) V b))
      as [BV [HeqV HpropV]].
    rewrite HeqV.
    eapply EvalsTo_trans with (b := ExpLet vx BV).
    + apply EvalsTo_let_l. exact Hx'.
    + eapply EvalsTo_trans with (b := subBV_at 0 vx BV).
      * eapply AddStep; [|apply Refl]. apply ELetV. exact Hvx.
      * rewrite HpropV. exact Hbody'.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma sim_ctx_rev : forall p ws j E V z,
  isLC E -> EvalsTo E V -> isValue V -> isValue z ->
  EvalsTo (subBV_many ws (subBV_at j V p)) z ->
  EvalsTo (subBV_many ws (subBV_at j E p)) z.
Proof.
  refine (proj1 (syntax_mutind'
    (fun p => forall ws j E V z, isLC E -> EvalsTo E V -> isValue V -> isValue z ->
       EvalsTo (subBV_many ws (subBV_at j V p)) z ->
       EvalsTo (subBV_many ws (subBV_at j E p)) z)
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - intros b ws j E V z HE HEV HV Hz H. exact H.
  - intros n ws j E V z HE HEV HV Hz H. exact H.
  - intros i ws j E V z HE HEV HV Hz H. simpl in H.
    destruct (j =? i) eqn:Ej.
    + apply Nat.eqb_eq in Ej. subst i.
      rewrite subBV_many_LC in H; [|apply isValue_isLC; exact HV].
      assert (HVe : V = z) by (apply (EvalsTo_value V z HV H)).
      subst z. simpl. rewrite Nat.eqb_refl. simpl.
      rewrite subBV_many_LC; [exact HEV|exact HE].
    + simpl. rewrite Ej. simpl. exact H.
  - intros x ws j E V z HE HEV HV Hz H. exact H.
  - intros o p IH ws j E V z HE HEV HV Hz H.
    change (EvalsTo (subBV_many ws (ExpUnOp o (subBV_at j V p))) z) in H.
    change (EvalsTo (subBV_many ws (ExpUnOp o (subBV_at j E p))) z).
    rewrite subBV_many_UnOp in H. rewrite subBV_many_UnOp.
    destruct (EvalsTo_unop_inv o (subBV_many ws (subBV_at j V p)) z H Hz) as
      [w [H1 [Hw Hfin]]].
    assert (H1' : EvalsTo (subBV_many ws (subBV_at j E p)) w) by
      (apply (IH ws j E V w HE HEV HV Hw H1)).
    eapply EvalsTo_trans with (b := ExpUnOp o w).
    + apply EvalsTo_unop. exact H1'.
    + exact Hfin.
  - intros o p1 IH1 p2 IH2 ws j E V z HE HEV HV Hz H.
    change (EvalsTo (subBV_many ws (ExpBinOp o (subBV_at j V p1) (subBV_at j V p2))) z) in H.
    change (EvalsTo (subBV_many ws (ExpBinOp o (subBV_at j E p1) (subBV_at j E p2))) z).
    rewrite subBV_many_BinOp in H. rewrite subBV_many_BinOp.
    destruct (EvalsTo_binop_inv o (subBV_many ws (subBV_at j V p1))
                (subBV_many ws (subBV_at j V p2)) z H Hz) as
      [w1 [w2 [H1 [Hw1 [H2 [Hw2 Hfin]]]]]].
    assert (H1' : EvalsTo (subBV_many ws (subBV_at j E p1)) w1) by
      (apply (IH1 ws j E V w1 HE HEV HV Hw1 H1)).
    assert (H2' : EvalsTo (subBV_many ws (subBV_at j E p2)) w2) by
      (apply (IH2 ws j E V w2 HE HEV HV Hw2 H2)).
    eapply EvalsTo_trans with (b := ExpBinOp o w1 (subBV_many ws (subBV_at j E p2))).
    + apply EvalsTo_binop_l. exact H1'.
    + eapply EvalsTo_trans with (b := ExpBinOp o w1 w2).
      * apply EvalsTo_binop_r; auto.
      * exact Hfin.
  - intros p1 IH1 m p2 IH2 ws j E V z HE HEV HV Hz H.
    change (EvalsTo (subBV_many ws
      (ExpMethodInvoc (subBV_at j V p1) m (subBV_at j V p2))) z) in H.
    change (EvalsTo (subBV_many ws
      (ExpMethodInvoc (subBV_at j E p1) m (subBV_at j E p2))) z).
    rewrite subBV_many_Invok in H. rewrite subBV_many_Invok.
    destruct (EvalsTo_invok_inv (subBV_many ws (subBV_at j V p1)) m
                (subBV_many ws (subBV_at j V p2)) z H Hz) as
      [C [es [vb [body [Hrec [HvalN [Harg [Hvb [Hbodyrel Ht]]]]]]]]].
    assert (Hrec' : EvalsTo (subBV_many ws (subBV_at j E p1)) (ExpNew C es)) by
      (apply (IH1 ws j E V (ExpNew C es) HE HEV HV HvalN Hrec)).
    assert (Harg' : EvalsTo (subBV_many ws (subBV_at j E p2)) vb) by
      (apply (IH2 ws j E V vb HE HEV HV Hvb Harg)).
    eapply EvalsTo_trans with
      (b := ExpMethodInvoc (ExpNew C es) m (subBV_many ws (subBV_at j E p2))).
    + apply EvalsTo_invok_l. exact Hrec'.
    + eapply EvalsTo_trans with (b := ExpMethodInvoc (ExpNew C es) m vb).
      * apply EvalsTo_invok_r; auto.
      * eapply EvalsTo_trans with
          (b := subBV_at 1 (ExpNew C es) (subBV vb body)).
        -- eapply AddStep; [|apply Refl]. eapply Refc_Invok3; eauto.
        -- exact Ht.
  - intros p IH f ws j E V z HE HEV HV Hz H.
    change (EvalsTo (subBV_many ws (ExpFieldAccess (subBV_at j V p) f)) z) in H.
    change (EvalsTo (subBV_many ws (ExpFieldAccess (subBV_at j E p) f)) z).
    rewrite subBV_many_Field in H. rewrite subBV_many_Field.
    destruct (EvalsTo_field_inv (subBV_many ws (subBV_at j V p)) f z H Hz) as
      [C [Fs [es [fi [ei [i [Hrec [HFs [HnF [Hrf [HnE [HvalNew Hz_eq]]]]]]]]]]]].
    subst z.
    assert (Hrec' : EvalsTo (subBV_many ws (subBV_at j E p)) (ExpNew C es)) by
      (apply (IH ws j E V (ExpNew C es) HE HEV HV HvalNew Hrec)).
    eapply EvalsTo_trans with (b := ExpFieldAccess (ExpNew C es) f).
    + apply EvalsTo_field. exact Hrec'.
    + eapply AddStep; [|apply Refl]. rewrite <- Hrf. eapply Refc_Field; eauto.
  - intros C l HF ws j E V z HE HEV HV Hz H.
    rewrite Forall_forall in HF.
    change (EvalsTo (subBV_many ws (ExpNew C (map (subBV_at j V) l))) z) in H.
    change (EvalsTo (subBV_many ws (ExpNew C (map (subBV_at j E) l))) z).
    rewrite subBV_many_New in H. rewrite subBV_many_New.
    destruct (EvalsTo_new_inv C (map (subBV_many ws) (map (subBV_at j V) l)) z H)
      as [zs [Hz_eq [Hlen Hpt]]].
    subst z.
    apply EvalsTo_new_Forall2.
    eapply Forall2_nth_Some_all.
    + rewrite !length_map. rewrite !length_map in Hlen. exact Hlen.
    + intros i a' Ha'.
      destruct (nth_error_map_Some (subBV_many ws) (map (subBV_at j E) l) i a' Ha')
        as [x [Hx Hxeq]].
      subst a'.
      destruct (nth_error_map_Some (subBV_at j E) l i x Hx) as [a [Ha Haeq]].
      subst x.
      assert (HVa : nth_error (map (subBV_many ws) (map (subBV_at j V) l)) i
                   = Some (subBV_many ws (subBV_at j V a))).
      { rewrite !nth_error_map. rewrite Ha. simpl. reflexivity. }
      destruct (Hpt i (subBV_many ws (subBV_at j V a)) HVa) as [b [Hb Hev]].
      exists b. split; [exact Hb|].
      assert (Hvb : isValue b).
      { change (isValueL zs) in Hz. exact (isValueL_nth zs i b Hz Hb). }
      exact (HF a (nth_error_In l i Ha) ws j E V b HE HEV HV Hvb Hev).
  - intros a IH1 b IH2 ws j E V z HE HEV HV Hz H.
    change (EvalsTo (subBV_many ws (ExpLet (subBV_at j V a) (subBV_at (j+1) V b))) z) in H.
    destruct (subBV_many_let ws (subBV_at j V a) (subBV_at (j+1) V b))
      as [BV [HeqV HpropV]].
    rewrite HeqV in H.
    destruct (EvalsTo_let_inv _ _ _ H Hz) as [vx [Hx [Hvx Hbody]]].
    rewrite (HpropV vx) in Hbody.
    assert (Hx' : EvalsTo (subBV_many ws (subBV_at j E a)) vx) by
      (apply (IH1 ws j E V vx HE HEV HV Hvx Hx)).
    assert (Hbody' : EvalsTo (subBV_many (ws ++ (vx :: nil)) (subBV_at (j+1) E b)) z) by
      (apply (IH2 (ws ++ (vx :: nil)) (j+1) E V z HE HEV HV Hz Hbody)).
    change (EvalsTo (subBV_many ws (ExpLet (subBV_at j E a) (subBV_at (j+1) E b))) z).
    destruct (subBV_many_let ws (subBV_at j E a) (subBV_at (j+1) E b))
      as [BE [HeqE HpropE]].
    rewrite HeqE.
    eapply EvalsTo_trans with (b := ExpLet vx BE).
    + apply EvalsTo_let_l. exact Hx'.
    + eapply EvalsTo_trans with (b := subBV_at 0 vx BE).
      * eapply AddStep; [|apply Refl]. apply ELetV. exact Hvx.
      * rewrite HpropE. exact Hbody'.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma sim_ctx_nil : forall p j E V z,
  isLC E -> EvalsTo E V -> isValue V -> isValue z ->
  EvalsTo (subBV_at j E p) z -> EvalsTo (subBV_at j V p) z.
Proof.
  intros p j E V z HE HEV HV Hz H.
  apply (sim_ctx p nil j E V z HE HEV HV Hz).
  simpl. exact H.
Qed.

Lemma sim_ctx_rev_nil : forall p j E V z,
  isLC E -> EvalsTo E V -> isValue V -> isValue z ->
  EvalsTo (subBV_at j V p) z -> EvalsTo (subBV_at j E p) z.
Proof.
  intros p j E V z HE HEV HV Hz H.
  apply (sim_ctx_rev p nil j E V z HE HEV HV Hz).
  simpl. exact H.
Qed.

Lemma PEvals_subst_fwd_nc : forall (ps:preds) E V w,
  isLC E -> isValue V -> EvalsTo E V -> isValue w ->
  PEvalsTrue (psubBV w (psubBV_at 1 E ps)) ->
  PEvalsTrue (psubBV w (psubBV_at 1 V ps)).
Proof.
  induction ps as [|p ps IH]; intros E V w HE HVv HEV Hw HP; simpl in HP.
  - exact HP.
  - inversion HP as [|p0 ps0 Hhead Htail]; subst.
    apply PECons.
    + change (EvalsTo (subBV_at 0 w (subBV_at 1 V p)) (Bc true)).
      change (EvalsTo (subBV_at 0 w (subBV_at 1 E p)) (Bc true)) in Hhead.
      rewrite (comm_subBV p 1 0 V w); [|lia|apply isValue_isLC; exact HVv|exact Hw].
      rewrite (comm_subBV p 1 0 E w) in Hhead; [|lia|exact HE|exact Hw].
      apply (sim_ctx_nil (subBV_at 0 w p) 1 E V (Bc true)).
      * exact HE.
      * exact HEV.
      * exact HVv.
      * simpl; exact I.
      * exact Hhead.
    + apply (IH E V w); auto.
Qed.

Lemma PEvals_subst_rev_nc : forall (ps:preds) E V w,
  isLC E -> isValue V -> EvalsTo E V -> isValue w ->
  PEvalsTrue (psubBV w (psubBV_at 1 V ps)) ->
  PEvalsTrue (psubBV w (psubBV_at 1 E ps)).
Proof.
  induction ps as [|p ps IH]; intros E V w HE HVv HEV Hw HP; simpl in HP.
  - exact HP.
  - inversion HP as [|p0 ps0 Hhead Htail]; subst.
    apply PECons.
    + change (EvalsTo (subBV_at 0 w (subBV_at 1 E p)) (Bc true)).
      change (EvalsTo (subBV_at 0 w (subBV_at 1 V p)) (Bc true)) in Hhead.
      rewrite (comm_subBV p 1 0 E w); [|lia|exact HE|exact Hw].
      rewrite (comm_subBV p 1 0 V w) in Hhead; [|lia|apply isValue_isLC; exact HVv|exact Hw].
      apply (sim_ctx_rev_nil (subBV_at 0 w p) 1 E V (Bc true)).
      * exact HE.
      * exact HEV.
      * exact HVv.
      * simpl; exact I.
      * exact Hhead.
    + apply (IH E V w); auto.
Qed.

Lemma Denotes_tsubBV_fwd_nc : forall b (ps:preds) v E V,
  isLC E -> EvalsTo E V -> isValue V -> isValue v ->
  Denotes (TRefn b (psubBV_at 1 E ps)) v ->
  Denotes (TRefn b (psubBV_at 1 V ps)) v.
Proof.
  intros b ps v E V HE HEV HVv Hv HD.
  apply (Denotes_impl b (psubBV_at 1 E ps) (psubBV_at 1 V ps) v).
  - intro HP. apply (PEvals_subst_fwd_nc ps E V v HE HVv HEV Hv HP).
  - exact HD.
Qed.

Lemma Denotes_tsubBV_rev_nc : forall b (ps:preds) v E V,
  isLC E -> EvalsTo E V -> isValue V -> isValue v ->
  Denotes (TRefn b (psubBV_at 1 V ps)) v ->
  Denotes (TRefn b (psubBV_at 1 E ps)) v.
Proof.
  intros b ps v E V HE HEV HVv Hv HD.
  apply (Denotes_impl b (psubBV_at 1 V ps) (psubBV_at 1 E ps) v).
  - intro HP. apply (PEvals_subst_rev_nc ps E V v HE HVv HEV Hv HP).
  - exact HD.
Qed.

(* ===== module helpers ===== *)
Lemma FJSubtype_trans : forall s t u, FJSubtype s t -> FJSubtype t u -> FJSubtype s u.
Proof.
  intros s t u H1. revert u. induction H1; intros u H2.
  - inversion H2; subst; apply SubBAny.
  - inversion H2; subst; [apply SubBAny|apply SubBInt].
  - inversion H2; subst; [apply SubBAny|apply SubBBool].
  - inversion H2; subst.
    + apply SubBAny.
    + apply SubBClass. eapply SubCTrans; eauto.
Qed.

Lemma Denotes_new_class_inv : forall t v, Denotes t v ->
  forall b ps C es, t = TRefn b ps -> v = ExpNew C es ->
  exists Fs, Reffields C Fs /\
    PEvalsTrue (psubBV (ExpNew C es) ps) /\
    Forall2 Denotes (map (tsubBV (ExpNew C es)) (map ReffieldType Fs)) es /\
    FJSubtype (TNom (TClass C)) b.
Proof.
  intros t v HD.
  induction HD; intros xb xps xC xes Ht Hv.
  - simpl in Hv. discriminate Hv.
  - simpl in Hv. discriminate Hv.
  - injection Ht as Hb Hps. injection Hv as Hc Hes. subst.
    exists Fs. split; [exact H1|]. split; [exact H0|]. split; [exact H2|].
    apply SubBClass, SubCRefl.
  - injection Ht as Hb Hps. subst.
    destruct (IHHD b1 xps xC xes eq_refl eq_refl) as [Fs [HRF [HPE [HF2 HSub]]]].
    exists Fs. split; [exact HRF|]. split; [exact HPE|]. split; [exact HF2|].
    eapply FJSubtype_trans; eauto.
Qed.

Lemma Denotes_rebase : forall C1 D ps es E,
  Denotes (TRefn (TNom E) ps) (ExpNew C1 es) ->
  SubClass (TClass C1) (TClass D) ->
  Denotes (TRefn (TNom (TClass D)) ps) (ExpNew C1 es).
Proof.
  intros C1 D ps es E HD Hsub.
  destruct (Denotes_new_class_inv (TRefn (TNom E) ps) (ExpNew C1 es) HD
              (TNom E) ps C1 es eq_refl eq_refl) as [Fs [HRF [HPE [HF2 _]]]].
  apply DenotesUpcast with (b1 := TNom (TClass C1)).
  - apply DenotesClass with (Fs := Fs).
    + apply Denotes_isValue in HD. exact HD.
    + exact HPE.
    + exact HRF.
    + exact HF2.
  - apply SubBClass. exact Hsub.
Qed.

Lemma CType_OK_parts : forall C D Is fs noDupfs K mds noDupMds,
  CType_OK (RefCDecl C D Is fs noDupfs K mds noDupMds) ->
  exists fdecl, Reffields D fdecl /\ NoDup (refs (fdecl ++ fs)) /\
    Forall (FType_OK C) fs.
Proof.
  intros. dependent destruction H.
  eexists. split; [exact H0|]. split; [exact H1|exact H3].
Qed.

Lemma SubClass_src_class : forall b1 b2, SubClass b1 b2 ->
  forall C, b2 = TClass C -> exists C1, b1 = TClass C1.
Proof.
  intros b1 b2 H. induction H; intros C0 HC.
  - subst. exists C0. reflexivity.
  - destruct (IHSubClass2 C0 HC) as [C2 HC2]. subst b2.
    apply (IHSubClass1 C2 eq_refl).
  - exists C. reflexivity.
  - subst. discriminate.
Qed.

Lemma SubClass_reffields_prefix : forall b1 b2, SubClass b1 b2 ->
  forall C1 C Fs, b1 = TClass C1 -> b2 = TClass C -> Reffields C Fs ->
  exists Fs1 suf, Reffields C1 Fs1 /\ Fs1 = Fs ++ suf.
Proof.
  intros b1 b2 H. induction H; intros C1 C0 Fs Hb1 Hb2 HR.
  - subst b. injection Hb2 as Hc2. subst.
    exists Fs, nil. split; [exact HR|rewrite app_nil_r; reflexivity].
  - rename H into H12. rename H0 into H23.
    rename IHSubClass1 into IH12. rename IHSubClass2 into IH23.
    assert (Hb2c : exists C2, b2 = TClass C2) by
      (eapply SubClass_src_class; [exact H23|exact Hb2]).
    destruct Hb2c as [C2 Hb2'].
    destruct (IH23 C2 C0 Fs Hb2' Hb2 HR) as [Fs2 [s2 [HR2 Hseq2]]].
    destruct (IH12 C1 C2 Fs2 Hb1 Hb2' HR2) as [Fs1 [s1 [HR1 Hseq1]]].
    exists Fs1, (s2 ++ s1). split; [exact HR1|].
    rewrite Hseq1, Hseq2, app_assoc. reflexivity.
  - injection Hb1 as Hc1. injection Hb2 as Hc2. subst C1. subst C0.
    destruct (CType_OK_parts C D Is fs noDupfs K mds noDupMds
                (cok C D fs noDupfs K Is mds noDupMds H))
      as [fdecl [HRf [Hnd HFT]]].
    assert (Hfdec : fdecl = Fs) by (eapply Reffields_det; [exact HRf|exact HR]).
    subst fdecl.
    exists (Fs ++ fs), fs. split.
    + eapply RefF_Decl; [exact H|exact HR|exact Hnd].
    + reflexivity.
  - discriminate Hb2.
Qed.

Lemma Forall_isLCL : forall l, Forall isLC l -> isLCL_at 0 l.
Proof.
  intros l H. induction H as [|a l Ha Hl IH].
  - simpl. exact I.
  - simpl. split; [exact Ha|exact IH].
Qed.

Lemma isLC_New_of_Forall : forall c l, Forall isLC l -> isLC (ExpNew c l).
Proof. intros. change (isLCL_at 0 l). apply Forall_isLCL. exact H. Qed.

Lemma nth_error_exists : forall {A} (l:[A]) i, i < length l -> exists a, nth_error l i = Some a.
Proof.
  intros A l i Hlt. destruct (nth_error l i) eqn:E.
  - exists a. reflexivity.
  - apply nth_error_None in E. lia.
Qed.

Lemma in_map_inv : forall {A B} (f:A->B) l y, In y (map f l) -> exists x, In x l /\ f x = y.
Proof.
  intros A B f l. induction l as [|a l IH]; intros y H; simpl in H.
  - destruct H.
  - destruct H as [Heq|H].
    + subst y. exists a. split; [left; reflexivity|reflexivity].
    + destruct (IH y H) as [x [Hx Hfx]]. exists x. split; [right; exact Hx|exact Hfx].
Qed.

Lemma FJSubtype_class_inv : forall C D,
  FJSubtype (TNom (TClass C)) (TNom (TClass D)) -> SubClass (TClass C) (TClass D).
Proof. intros. inversion H. assumption. Qed.

(* ===== module newcase ===== *)
Lemma sem_new_case : forall F,
  (forall m, m < F -> forall g e t, Hastype g e t -> forall th, DenotesEnv g th ->
     forall v, EvalsToN m (csubst th e) v -> isValue v -> Denotes (ctsubst th t) v) ->
  forall es,
  (forall a, In a es -> forall g t, Hastype g a t -> forall th, DenotesEnv g th ->
     forall v, EvalsToN F (csubst th a) v -> isValue v -> Denotes (ctsubst th t) v) ->
  forall g C t, Hastype g (ExpNew C es) t -> forall th, DenotesEnv g th ->
  forall v, EvalsToN F (csubst th (ExpNew C es)) v -> isValue v ->
  Denotes (ctsubst th t) v.
Proof.
  intros F Hsmall es IHl g C t Hty th Hd v HN Hv.
  destruct (Hastype_to_D_sem g (ExpNew C es) t Hty) as [s [HD Htr]].
  destruct (HastypeD_new_inv g C es s HD) as
    [Ts [Fs [Us [fs [Heqs [HUs [Hfs [HLC [HRF [HTs HSub2]]]]]]]]]].
  subst s. subst Us.
  apply (Htr th Hd v).
  rewrite csubst_New in HN.
  destruct (EvN_new_decomp F C (map (csubst th) es) v HN Hv)
    as [vs [Hveq [Hlen Hpt]]].
  subst v.
  rewrite ctsubst_self. rewrite ctsubst_TRefn. rewrite cpsubst_PEmpty.
  rewrite csubst_New.
  apply Denotes_self_eq.
  - assert (Hlc_th : LCsubst th) by (exact (DenotesEnv_LCsubst g th Hd)).
    apply isLC_New_of_Forall. rewrite Forall_forall. intros a Ha.
    rewrite Forall_forall in HLC.
    apply in_map_inv in Ha. destruct Ha as [a0 [Ha0 Haeq]]. subst a.
    exact (proj1 isLC_csubst_gen a0 th Hlc_th (HLC a0 Ha0)).
  - apply DenotesClass with (Fs := Fs).
    + exact Hv.
    + apply PEEmp.
    + exact HRF.
    + eapply Forall2_nth_Some_all.
      * rewrite !length_map.
        assert (Hl1 : length es = length Ts) by (exact (Forall2_length (Hastype g) es Ts HTs)).
        assert (Hl2 : length Ts = length Fs).
        { rewrite (Forall2_length (Subtype g) Ts (map (tsubBV (ExpNew C es)) (map ReffieldType Fs)) HSub2).
          rewrite !length_map. reflexivity. }
        rewrite length_map in Hlen. lia.
      * intros i a Ha.
        destruct (nth_error_map_Some (tsubBV (ExpNew C vs)) (map ReffieldType Fs) i a Ha)
          as [x [Hx Haeq]]. subst a.
        destruct (nth_error_map_Some ReffieldType Fs i x Hx) as [fi [Hfi Hxeq]].
        subst x.
        assert (HiFs : i < length Fs) by
          (apply nth_error_Some; rewrite Hfi; discriminate).
        assert (Hl1 : length es = length Ts) by (exact (Forall2_length (Hastype g) es Ts HTs)).
        assert (Hl2 : length Ts = length Fs).
        { rewrite (Forall2_length (Subtype g) Ts (map (tsubBV (ExpNew C es)) (map ReffieldType Fs)) HSub2).
          rewrite !length_map. reflexivity. }
        assert (HiEs : i < length es) by (rewrite Hl1, Hl2; exact HiFs).
        destruct (nth_error_exists es i HiEs) as [ei Hei].
        destruct (Forall2_nth_error_some (Hastype g) es Ts i ei HTs Hei)
          as [Ti [HTi Hty_ei]].
        destruct (Forall2_nth_error_some (Subtype g) Ts
                    (map (tsubBV (ExpNew C es)) (map ReffieldType Fs)) i Ti HSub2 HTi)
          as [Ui [HUi Hsub_i]].
        destruct (nth_error_map_Some (tsubBV (ExpNew C es)) (map ReffieldType Fs)
                    i Ui HUi) as [y [Hy HyEq]].
        destruct (nth_error_map_Some ReffieldType Fs i y Hy) as [fi' [Hfi' Hy']].
        assert (Hfieq : fi = fi') by (rewrite Hfi in Hfi'; injection Hfi' as H; exact H).
        subst fi'. subst y. subst Ui.
        assert (HiMap : nth_error (map (csubst th) es) i = Some (csubst th ei)).
        { rewrite nth_error_map. rewrite Hei. reflexivity. }
        destruct (Hpt i (csubst th ei) HiMap) as [b [nb [Hb [HevNb Hle]]]].
        assert (Hvb : isValue b).
        { change (isValueL vs) in Hv.
          exact (isValueL_nth vs i b Hv Hb). }
        assert (HDb : Denotes (ctsubst th Ti) b).
        { destruct (lt_eq_lt_dec nb F) as [[Hlt|Heq]|Hgt].
          - exact (Hsmall nb Hlt g ei Ti Hty_ei th Hd b HevNb Hvb).
          - subst nb. exact (IHl ei (nth_error_In es i Hei) g Ti Hty_ei th Hd b HevNb Hvb).
          - lia. }
        assert (HDU : Denotes (ctsubst th (tsubBV (ExpNew C es) (ReffieldType fi))) b)
          by (eapply Subtype_sound; [exact Hsub_i|exact Hd|exact HDb]).
        assert (Hfreefi : free (ReffieldType fi) = empty).
        { apply Reffields_free in HRF. rewrite Forall_forall in HRF.
          exact (HRF fi (nth_error_In Fs i Hfi)). }
        assert (Hlc_th : LCsubst th) by (exact (DenotesEnv_LCsubst g th Hd)).
        rewrite ctsubst_tsubBV0 in HDU; [|exact Hlc_th].
        rewrite csubst_New in HDU.
        rewrite (ctsubst_free th (ReffieldType fi) Hfreefi) in HDU.
        destruct (ReffieldType fi) as [bf psf] eqn:Hft.
        change (Denotes (tsubBV_at 0 (ExpNew C (map (csubst th) es)) (TRefn bf psf)) b) in HDU.
        rewrite tsubBV_TRefn in HDU.
        exists b. split; [exact Hb|].
        change (Denotes (tsubBV_at 0 (ExpNew C vs) (TRefn bf psf)) b).
        rewrite tsubBV_TRefn.
        assert (HLCmap : isLC (ExpNew C (map (csubst th) es))).
        { apply isLC_New_of_Forall. rewrite Forall_forall. intros a0 Ha0.
          rewrite Forall_forall in HLC.
          apply in_map_inv in Ha0. destruct Ha0 as [a1 [Ha1 Haeq]]. subst a0.
          exact (proj1 isLC_csubst_gen a1 th Hlc_th (HLC a1 Ha1)). }
        assert (Hev : EvalsTo (ExpNew C (map (csubst th) es)) (ExpNew C vs)).
        { change (EvalsTo (ExpNew C (nil ++ map (csubst th) es)) (ExpNew C (nil ++ vs))).
          eapply EvalsTo_new_prefix.
          - intros i0 a0 Ha0.
            destruct (Hpt i0 a0 Ha0) as [b0 [nb0 [Hb0 [HevNb0 _]]]].
            exists b0. split; [exact Hb0|exact (EvN_EvalsTo nb0 a0 b0 HevNb0)].
          - exact Hlen. }
        eapply Denotes_tsubBV_fwd_nc; [exact HLCmap|exact Hev|exact Hv|exact Hvb|exact HDU].
  - assert (Hlc_th : LCsubst th) by (exact (DenotesEnv_LCsubst g th Hd)).
    assert (HLCmap : isLC (ExpNew C (map (csubst th) es))).
    { apply isLC_New_of_Forall. rewrite Forall_forall. intros a0 Ha0.
      rewrite Forall_forall in HLC.
      apply in_map_inv in Ha0. destruct Ha0 as [a1 [Ha1 Haeq]]. subst a0.
      exact (proj1 isLC_csubst_gen a1 th Hlc_th (HLC a1 Ha1)). }
    change (EvalsTo (ExpNew C (nil ++ map (csubst th) es)) (ExpNew C (nil ++ vs))).
    eapply EvalsTo_new_prefix.
    + intros i0 a0 Ha0.
      destruct (Hpt i0 a0 Ha0) as [b0 [nb0 [Hb0 [HevNb0 _]]]].
      exists b0. split; [exact Hb0|exact (EvN_EvalsTo nb0 a0 b0 HevNb0)].
    + exact Hlen.
Qed.

(* ===== module fieldcase ===== *)
Lemma sem_field_case : forall F,
  (forall m, m < F -> forall g e t, Hastype g e t -> forall th, DenotesEnv g th ->
     forall v, EvalsToN m (csubst th e) v -> isValue v -> Denotes (ctsubst th t) v) ->
  forall g e f t, Hastype g (ExpFieldAccess e f) t -> forall th, DenotesEnv g th ->
  forall v, EvalsToN F (csubst th (ExpFieldAccess e f)) v -> isValue v ->
  Denotes (ctsubst th t) v.
Proof.
  intros F Hsmall g e f t Hty th Hd v HN Hv.
  destruct (Hastype_to_D_sem g (ExpFieldAccess e f) t Hty) as [s [HD Htr]].
  destruct (HastypeD_field_inv g e f s HD) as
    [C [Fs [i [fi [ps [Heqs [Hlce [Hte [HRF [Hnth Href]]]]]]]]]].
  subst s.
  apply (Htr th Hd v).
  rewrite csubst_Field in HN.
  destruct (EvN_field_decomp F (csubst th e) f v HN Hv) as
    [n1 [C1 [Fs1 [es [fi1 [ei [i1 [H1 [HvalNew [HRF1 [Hnth1 [Href1 [HnthE1 [Hveq Hn]]]]]]]]]]]]]].
  subst v.
  assert (Hn1lt : n1 < F) by lia.
  rewrite ctsubst_self.
  pose (HDrec := Hsmall n1 Hn1lt g e (TRefn (TNom (TClass C)) ps) Hte th Hd
                    (ExpNew C1 es) H1 HvalNew).
  rewrite ctsubst_TRefn in HDrec.
  destruct (Denotes_new_class_inv (TRefn (TNom (TClass C)) (cpsubst th ps))
              (ExpNew C1 es) HDrec (TNom (TClass C)) (cpsubst th ps) C1 es
              eq_refl eq_refl)
    as [Fsd [HRFd [HPE [HF2d Hsubj]]]].
  assert (HFsd : Fsd = Fs1) by (eapply Reffields_det; [exact HRFd|exact HRF1]).
  subst Fsd.
  assert (HsubC : SubClass (TClass C1) (TClass C))
    by (apply (FJSubtype_class_inv C1 C); exact Hsubj).
  destruct (SubClass_reffields_prefix (TClass C1) (TClass C) HsubC C1 C Fs
              eq_refl eq_refl HRF) as [Fs1' [suf [HRF1' Hseq]]].
  assert (HFs1' : Fs1' = Fs1) by (eapply Reffields_det; [exact HRF1'|exact HRF1]).
  rewrite HFs1' in Hseq.
  assert (HiFs : i < length Fs) by (apply nth_error_Some; rewrite Hnth; discriminate).
  assert (Hnth1i : nth_error Fs1 i = Some fi).
  { rewrite Hseq. rewrite nth_error_app1; [exact Hnth|exact HiFs]. }
  assert (Hrefeq : ref fi = ref fi1) by (rewrite Href, Href1; reflexivity).
  destruct (nth_error_ref_unique Fs1 i fi i1 fi1
              (Reffields_NoDup C1 Fs1 HRF1) Hnth1i Hnth1 Hrefeq)
    as [Hii Hfifi].
  subst i1. subst fi1.
  assert (HiEs : i < length es) by (apply nth_error_Some; rewrite HnthE1; discriminate).
  assert (HlenT : length (map (tsubBV (ExpNew C1 es)) (map ReffieldType Fs1)) = length es)
    by (exact (Forall2_length Denotes (map (tsubBV (ExpNew C1 es)) (map ReffieldType Fs1)) es HF2d)).
  assert (HiT : i < length (map (tsubBV (ExpNew C1 es)) (map ReffieldType Fs1)))
    by (rewrite HlenT; exact HiEs).
  destruct (nth_error_exists (map (tsubBV (ExpNew C1 es)) (map ReffieldType Fs1)) i HiT)
    as [td Htd].
  assert (Hden_td : Denotes td ei) by
    (eapply Forall2_nth_error_Some; [exact HF2d|exact Htd|exact HnthE1]).
  destruct (nth_error_map_Some (tsubBV (ExpNew C1 es)) (map ReffieldType Fs1) i td Htd)
    as [y [Hy HyEq]]. subst td.
  destruct (nth_error_map_Some ReffieldType Fs1 i y Hy) as [fi' [Hfi' Hy']].
  assert (Hfieq : fi = fi') by (rewrite Hnth1i in Hfi'; injection Hfi' as H; exact H).
  subst fi'. subst y.
  assert (Hfreefi : free (ReffieldType fi) = empty).
  { apply Reffields_free in HRF. rewrite Forall_forall in HRF.
    exact (HRF fi (nth_error_In Fs i Hnth)). }
  assert (Hlc_th : LCsubst th) by (exact (DenotesEnv_LCsubst g th Hd)).
  assert (Hct : ctsubst th (tsubBV e (ReffieldType fi)) =
                tsubBV (csubst th e) (ReffieldType fi)).
  { rewrite ctsubst_tsubBV0; [|exact Hlc_th].
    rewrite (ctsubst_free th (ReffieldType fi) Hfreefi). reflexivity. }
  destruct fi as [ft ff] eqn:Hfi.
  destruct ft as [bf psf] eqn:Hft.
  simpl in Hden_td. simpl in Hct. simpl.
  rewrite Hct.
  cbn [self].
  apply Denotes_self_eq.
  - exact (proj1 isLC_csubst_gen (ExpFieldAccess e f) th Hlc_th Hlce).
  - assert (HlceE : isLC (csubst th e))
      by (exact (proj1 isLC_csubst_gen e th Hlc_th Hlce)).
    assert (HevE : EvalsTo (csubst th e) (ExpNew C1 es)) by (apply EvN_EvalsTo with (n:=n1); exact H1).
    assert (Hvei : isValue ei) by (exact (isValueL_nth es i ei HvalNew HnthE1)).
    exact (Denotes_tsubBV_rev_nc bf psf ei (csubst th e) (ExpNew C1 es)
             HlceE HevE HvalNew Hvei Hden_td).
  - rewrite csubst_Field.
    exact (EvN_EvalsTo F (ExpFieldAccess (csubst th e) f) ei HN).
Qed.

(* ===== module invsupp ===== *)
Lemma comm_subBV_lc : forall p j k E w,
  j <> k -> isLC E -> isLC w ->
  subBV_at k w (subBV_at j E p) = subBV_at j E (subBV_at k w p).
Proof.
  refine (proj1 (syntax_mutind'
    (fun p => forall j k E w, j <> k -> isLC E -> isLC w ->
       subBV_at k w (subBV_at j E p) = subBV_at j E (subBV_at k w p))
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - simpl; auto.
  - simpl; auto.
  - simpl. intros i j k E w Hjk HE Hw.
    destruct (j =? i) eqn:Ej; destruct (k =? i) eqn:Ek; simpl.
    + exfalso. apply Nat.eqb_eq in Ej. apply Nat.eqb_eq in Ek. lia.
    + try rewrite Ej. try rewrite Ek. simpl. apply (subBV_at_LC E k).
      apply isLC_at_mono with (j:=0); [lia|exact HE].
    + try rewrite Ej. try rewrite Ek. simpl. symmetry. apply (subBV_at_LC w j).
      apply isLC_at_mono with (j:=0); [lia|exact Hw].
    + try rewrite Ej. try rewrite Ek. simpl. reflexivity.
  - simpl; auto.
  - simpl; intros o e0 IH j k E w Hjk HE Hw. rewrite (IH j k E w); auto.
  - simpl; intros o e1 IH1 e2 IH2 j k E w Hjk HE Hw.
    rewrite (IH1 j k E w); auto. rewrite (IH2 j k E w); auto.
  - simpl; intros e1 IH1 m e2 IH2 j k E w Hjk HE Hw.
    rewrite (IH1 j k E w); auto. rewrite (IH2 j k E w); auto.
  - simpl; intros e0 IH f j k E w Hjk HE Hw. rewrite (IH j k E w); auto.
  - intros C l HF j k E w Hjk HE Hw.
    rewrite subBV_New_map. rewrite subBV_New_map.
    rewrite subBV_New_map. rewrite subBV_New_map.
    f_equal.
    revert HF. induction l as [|a l IHs]; simpl; intros HF.
    + reflexivity.
    + inversion HF as [|? ? Pa Pl]; subst. simpl.
      rewrite (Pa j k E w Hjk HE Hw).
      f_equal. apply IHs; exact Pl.
  - simpl; intros e1 IH1 e2 IH2 j k E w Hjk HE Hw.
    simpl.
    rewrite (IH1 j k E w); auto.
    rewrite (IH2 (j+1) (k+1) E w); auto. lia.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma PEvals_subBV_at_rev : forall ps j E V v,
  j <> 0 -> isLC E -> EvalsTo E V -> isValue V -> isValue v ->
  PEvalsTrue (psubBV v (psubBV_at j V ps)) ->
  PEvalsTrue (psubBV v (psubBV_at j E ps)).
Proof.
  induction ps as [|p ps IH]; intros j E V v Hj HE HEV HV Hv HP; simpl in HP.
  - exact HP.
  - inversion HP as [|p0 ps0 Hhead Htail]; subst.
    apply PECons.
    + change (EvalsTo (subBV_at 0 v (subBV_at j E p)) (Bc true)).
      change (EvalsTo (subBV_at 0 v (subBV_at j V p)) (Bc true)) in Hhead.
      rewrite (comm_subBV_lc p j 0 E v); [|lia|exact HE|apply isValue_isLC; exact Hv].
      rewrite (comm_subBV_lc p j 0 V v) in Hhead; [|lia|apply isValue_isLC; exact HV|apply isValue_isLC; exact Hv].
      apply (sim_ctx_rev_nil (subBV_at 0 v p) j E V (Bc true));
        [exact HE|exact HEV|exact HV|simpl; exact I|exact Hhead].
    + apply (IH j E V v); auto.
Qed.

Lemma Denotes_subBV_at_rev : forall b ps j E V v,
  j <> 0 -> isLC E -> EvalsTo E V -> isValue V -> isValue v ->
  Denotes (TRefn b (psubBV_at j V ps)) v ->
  Denotes (TRefn b (psubBV_at j E ps)) v.
Proof.
  intros b ps j E V v Hj HE HEV HV Hv HD.
  eapply Denotes_impl; [|exact HD].
  intro HP. exact (PEvals_subBV_at_rev ps j E V v Hj HE HEV HV Hv HP).
Qed.

(* ===== module closure ===== *)
Lemma fv_New_eq : forall c l, fv (ExpNew c l) = fvL l.
Proof. intros. cbn. reflexivity. Qed.

Lemma fvL_map_subset : forall l (f:expr->expr),
  (forall a, In a l -> forall x, In x (fv a) -> In x (fv (f a))) ->
  forall x, In x (fvL l) -> In x (fvL (map f l)).
Proof.
  induction l as [|a l IH]; intros f Hf x Hx; cbn in *.
  - destruct Hx.
  - unfold union in Hx. unfold union. rewrite set_union_iff in Hx. rewrite set_union_iff.
    destruct Hx as [Hx|Hx].
    + left. exact (Hf a (or_introl eq_refl) x Hx).
    + right. apply IH; [intros b Hb; apply Hf; right; exact Hb|exact Hx].
Qed.

Lemma fv_open_at_subset : forall e j y x, In x (fv e) -> In x (fv (open_at j y e)).
Proof.
  refine (proj1 (syntax_mutind'
    (fun e => forall j y x, In x (fv e) -> In x (fv (open_at j y e)))
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - simpl. intros b j y x Hx. change (In x empty) in Hx. destruct Hx.
  - simpl. intros n j y x Hx. change (In x empty) in Hx. destruct Hx.
  - simpl. intros i j y x Hx. change (In x empty) in Hx. destruct Hx.
  - simpl. intros x0 j y x Hx. exact Hx.
  - simpl. intros o e IH j y x Hx. apply (IH j y x). exact Hx.
  - simpl. intros o e1 IH1 e2 IH2 j y x Hx.
    unfold union in Hx. unfold union. rewrite set_union_iff in Hx. rewrite set_union_iff.
    destruct Hx as [Hx|Hx]; [left; apply IH1; exact Hx|right; apply IH2; exact Hx].
  - simpl. intros e1 IH1 m e2 IH2 j y x Hx.
    unfold union in Hx. unfold union. rewrite set_union_iff in Hx. rewrite set_union_iff.
    destruct Hx as [Hx|Hx]; [left; apply IH1; exact Hx|right; apply IH2; exact Hx].
  - simpl. intros e IH f j y x Hx. apply IH. exact Hx.
  - intros C l HF j y x Hx.
    rewrite Forall_forall in HF.
    change (In x (fvL (map (open_at j y) l))).
    change (In x (fvL l)) in Hx.
    apply fvL_map_subset with (f := open_at j y).
    + intros a Ha x0 Hx0. exact (HF a Ha j y x0 Hx0).
    + exact Hx.
  - simpl. intros e1 IH1 e2 IH2 j y x Hx.
    unfold union in Hx. unfold union. rewrite set_union_iff in Hx. rewrite set_union_iff.
    destruct Hx as [Hx|Hx]; [left; apply IH1; exact Hx|right; apply IH2; exact Hx].
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma fvP_openP_subset : forall ps j y x, In x (fvP ps) -> In x (fvP (openP_at j y ps)).
Proof.
  induction ps as [|p ps IH]; intros j y x Hx; simpl in *.
  - destruct Hx.
  - unfold union in Hx. unfold union. rewrite set_union_iff in Hx. rewrite set_union_iff.
    destruct Hx as [Hx|Hx]; [left; apply fv_open_at_subset; exact Hx|right; apply IH; exact Hx].
Qed.

Lemma names_empty_of_noelem : forall s:names, (forall x, ~ In x s) -> s = empty.
Proof.
  intros s H. destruct s as [|a s].
  - reflexivity.
  - exfalso. apply (H a). left. reflexivity.
Qed.

(* ===== module closure4 ===== *)
Lemma bound_inF_bindsFJ0 : forall g x b, bound_inF x b g -> In x (bindsFJ g).
Proof.
  induction g as [|y ty g IH]; simpl; intros x b Hb; [destruct Hb|].
  destruct Hb as [[-> ->]|Hb].
  - unfold names_add. rewrite set_add_iff. left. reflexivity.
  - unfold names_add. rewrite set_add_iff. right. apply (IH x b); exact Hb.
Qed.

Lemma Forall2_fv_bound : forall g es Us m,
  esizeL es <= m ->
  Forall2 (HasFJtype g) es Us ->
  (forall e, esize e <= m -> forall g' t, HasFJtype g' e t ->
     forall x, In x (fv e) -> In x (bindsFJ g')) ->
  forall x, In x (fvL es) -> In x (bindsFJ g).
Proof.
  intros g es Us m Hm HF2 Hrec x Hx. revert Hm Hx.
  induction HF2 as [|e U es Us He Htail IHtail]; intros Hm Hx.
  - cbn in Hx. destruct Hx.
  - simpl in Hm. change (In x (union (fv e) (fvL es))) in Hx.
    unfold union in Hx. rewrite set_union_iff in Hx. destruct Hx as [Hx|Hx].
    + assert (Hle : esize e <= m) by lia.
      exact (Hrec e Hle g U He x Hx).
    + apply IHtail; [lia|exact Hx].
Qed.

Lemma HasFJtype_fv : forall n e, esize e <= n -> forall g t, HasFJtype g e t ->
  forall x, In x (fv e) -> In x (bindsFJ g).
Proof.
  intros n. induction n as [|n IH]; intros e Hn g t HF x Hx.
  - exfalso. pose proof (esize_pos e). lia.
  - destruct e as [b|z|i|vv|op e1|op e1 e2|e1 f|e1 m e2|c l|e1 e2].
    + (* Bc *) simpl in Hx. destruct Hx.
    + (* Ic *) simpl in Hx. destruct Hx.
    + (* BV *) destruct (HasFJtype_to_D g (BV i) t HF) as [s HD].
      dependent destruction HD.
    + (* FV *) destruct (HasFJtype_to_D g (FV vv) t HF) as [s HD].
      dependent destruction HD.
      simpl in Hx. destruct Hx as [Heq|Hx]; [|destruct Hx]. subst x.
      eapply bound_inF_bindsFJ0. exact H.
    + (* UnOp *) destruct (HasFJtype_to_D g (ExpUnOp op e1) t HF) as [s HD].
      dependent destruction HD.
      simpl in Hx.
      assert (Hle : esize e1 <= n) by (simpl in Hn; lia).
      exact (IH e1 Hle g _ H x Hx).
    + (* BinOp *) destruct (HasFJtype_to_D g (ExpBinOp op e1 e2) t HF) as [s HD].
      dependent destruction HD.
      simpl in Hx. unfold union in Hx. rewrite set_union_iff in Hx.
      destruct Hx as [Hx|Hx].
      * assert (Hle : esize e1 <= n) by (simpl in Hn; lia).
        exact (IH e1 Hle g _ H x Hx).
      * assert (Hle : esize e2 <= n) by (simpl in Hn; lia).
        exact (IH e2 Hle g _ H0 x Hx).
    + (* Field *) destruct (HasFJtype_to_D g (ExpFieldAccess e1 f) t HF) as [s HD].
      dependent destruction HD.
      simpl in Hx.
      assert (Hle : esize e1 <= n) by (simpl in Hn; lia).
      exact (IH e1 Hle g _ H x Hx).
    + (* Invok *) destruct (HasFJtype_to_D g (ExpMethodInvoc e1 m e2) t HF) as [s HD].
      dependent destruction HD.
      all: assert (Hle1 : esize e1 <= n) by (simpl in Hn; lia).
      all: assert (Hle2 : esize e2 <= n) by (simpl in Hn; lia).
      all: simpl in Hx; unfold union in Hx; rewrite set_union_iff in Hx;
           destruct Hx as [Hx|Hx];
           [ exact (IH e1 Hle1 g _ H x Hx)
           | exact (IH e2 Hle2 g _ H1 x Hx) ].
    + (* New *) destruct (HasFJtype_to_D g (ExpNew c l) t HF) as [s HD].
      dependent destruction HD.
      change (In x (fvL l)) in Hx.
      assert (Hle : esizeL l <= n) by (change (S (esizeL l) <= S n) in Hn; lia).
      eapply Forall2_fv_bound; [exact Hle|exact H2| |exact Hx].
      intros e0 Hle0 g0 t0 He0 x0 Hx0. exact (IH e0 Hle0 g0 t0 He0 x0 Hx0).
    + (* Let *) destruct (HasFJtype_to_D g (ExpLet e1 e2) t HF) as [s HD].
      destruct (HasFJtypeD_let_inv g e1 e2 s HD) as [b [b' [nms [Hx1 Hbody]]]].
      simpl in Hx. unfold union in Hx. rewrite set_union_iff in Hx.
      destruct Hx as [Hx|Hx].
      * assert (Hle1 : esize e1 <= n) by (simpl in Hn; lia).
        exact (IH e1 Hle1 g _ Hx1 x Hx).
      * assert (Hsize2 : esize e2 <= n) by (simpl in Hn; lia).
        pose (y := freshv (nms ++ fv e2)).
        assert (Hyn : ~ In y nms) by (apply notin_app_l with (b:=fv e2); apply freshv_notin).
        assert (Hyf : ~ In y (fv e2)) by (apply notin_app_r with (a:=nms); apply freshv_notin).
        assert (HB : HasFJtype (FCons y b g) (unbind y e2) b').
        { unfold unbind. apply Hbody; exact Hyn. }
        assert (Hxin : In x (fv (unbind y e2))).
        { unfold unbind. apply fv_open_at_subset. exact Hx. }
        assert (Hs2size : esize (unbind y e2) <= n).
        { unfold unbind. rewrite esize_open_at. exact Hsize2. }
        pose proof (IH (unbind y e2) Hs2size (FCons y b g) b' HB x Hxin) as Hmem.
        simpl in Hmem. unfold names_add in Hmem. rewrite set_add_iff in Hmem.
        destruct Hmem as [Hxy|Hxg]; [subst x; contradiction|exact Hxg].
Qed.

(* ===== module closure5 ===== *)
Lemma HasFJtype_fv_all : forall g e t, HasFJtype g e t ->
  forall x, In x (fv e) -> In x (bindsFJ g).
Proof.
  intros g e t H x Hx.
  exact (HasFJtype_fv (esize e) e (le_n (esize e)) g t H x Hx).
Qed.

Lemma PIsBool_fv_cons_empty : forall y b ps,
  ~ In y (fvP ps) ->
  PIsBool (FCons y b FEmpty) (unbindP y ps) ->
  fvP ps = empty.
Proof.
  induction ps as [|p ps IH]; intros Hy HP.
  - simpl. reflexivity.
  - simpl in HP. inversion HP as [|g0 p0 ps0 Hty HPi]; subst.
    assert (Hyps : ~ In y (fvP ps)).
    { intro H. apply Hy. simpl. unfold union. rewrite set_union_iff. right; exact H. }
    assert (Hfvps : fvP ps = empty) by (exact (IH Hyps HPi)).
    assert (Hfvp : fv p = empty).
    { apply names_empty_of_noelem. intros x Hx.
      assert (Hxopen : In x (fv (open_at 0 y p))) by (apply fv_open_at_subset; exact Hx).
      assert (Hmem := HasFJtype_fv_all (FCons y b FEmpty) (open_at 0 y p) TBool Hty x Hxopen).
      simpl in Hmem. destruct Hmem as [Hxy|Hemp].
      - apply Hy. simpl. unfold union. rewrite set_union_iff. left. subst x. exact Hx.
      - destruct Hemp. }
    simpl. rewrite Hfvp, Hfvps. reflexivity.
Qed.

Lemma WFtype_empty_free_gen : forall g t, WFtype g t -> g = Empty -> free t = empty.
Proof.
  intros g t H. induction H; intros Hg; subst g.
  - simpl. reflexivity.
  - simpl.
    pose (y := freshv (nms ++ fvP ps)).
    assert (Hyn : ~ Elem y nms) by (apply notin_app_l with (b:=fvP ps); apply freshv_notin).
    assert (Hy : ~ In y (fvP ps)) by (apply notin_app_r with (a:=nms); apply freshv_notin).
    exact (PIsBool_fv_cons_empty y b ps Hy (H1 y Hyn)).
Qed.

Lemma WFtype_empty_free : forall t, WFtype Empty t -> free t = empty.
Proof. intros t H. exact (WFtype_empty_free_gen Empty t H eq_refl). Qed.

(* ===== module invfacts ===== *)
Lemma find_in_MDefn : forall (m:MethodName) (Ms:[MethodDefn]) d,
  find m Ms = Some d -> In d Ms.
Proof.
  intros m Ms. induction Ms as [|a l IH]; intros d H; simpl in H.
  - discriminate.
  - destruct (m =? (match a with MDefn (MDecl _ x _ _) _ => x end)) eqn:E; simpl in H.
    + change ((if (m =? (match a with MDefn (MDecl _ x _ _) _ => x end))
               then Some a else find m l) = Some d) in H.
      rewrite E in H. simpl in H. injection H as ->. left. reflexivity.
    + change ((if (m =? (match a with MDefn (MDecl _ x _ _) _ => x end))
               then Some a else find m l) = Some d) in H.
      rewrite E in H. simpl in H. right. apply IH. exact H.
Qed.

Lemma find_in_MDecl : forall (m:MethodName) (Ms:[MethodDecl]) d,
  find m Ms = Some d -> In d Ms.
Proof.
  intros m Ms. induction Ms as [|a l IH]; intros d H; simpl in H.
  - discriminate.
  - destruct (m =? (match a with MDecl _ x _ _ => x end)) eqn:E; simpl in H.
    + change ((if (m =? (match a with MDecl _ x _ _ => x end))
               then Some a else find m l) = Some d) in H.
      rewrite E in H. simpl in H. injection H as ->. left. reflexivity.
    + change ((if (m =? (match a with MDecl _ x _ _ => x end))
               then Some a else find m l) = Some d) in H.
      rewrite E in H. simpl in H. right. apply IH. exact H.
Qed.

Lemma CType_OK_MType : forall C D Is fs noDupfs K mds noDupMds,
  CType_OK (RefCDecl C D Is fs noDupfs K mds noDupMds) -> Forall (MType_OK C) mds.
Proof. intros. dependent destruction H. assumption. Qed.

Lemma MType_OK_decl : forall C rt m ps t e,
  MType_OK C (MDefn (MDecl rt m ps t) e) ->
  fvP ps = empty /\ free t = empty /\ free rt = empty.
Proof.
  intros C rt m ps t e H. dependent destruction H.
  split; [|split].
  - pose proof (WFtype_empty_free _ H2) as Hfr.
    simpl in Hfr. exact Hfr.
  - exact H7.
  - exact H8.
Qed.

Lemma mtype_facts : forall m C ps t rt, mtype(m,C) = ps ~> t ~> rt ->
  fvP ps = empty /\ free t = empty /\ free rt = empty.
Proof.
  intros m C ps t rt H. induction H.
  - assert (HMT : Forall (MType_OK C) Ms).
    { apply (CType_OK_MType C D Is Fs noDupfs K Ms noDupMds).
      apply (cok C D Fs noDupfs K Is Ms noDupMds). exact H. }
    rewrite Forall_forall in HMT.
    assert (Hin : In (MDefn (MDecl rt m ps t) e) Ms) by
      (apply (find_in_MDefn m Ms (MDefn (MDecl rt m ps t) e)); exact H0).
    exact (MType_OK_decl C rt m ps t e (HMT _ Hin)).
  - assumption.
Qed.

Lemma IType_OK_MTypeI : forall I iMs noDupiMds,
  IType_OK (RefIDecl I iMs noDupiMds) -> Forall (MType_OK_I I) iMs.
Proof. intros. dependent destruction H. assumption. Qed.

Lemma MType_OK_I_decl : forall I rt m ps t,
  MType_OK_I I (MDecl rt m ps t) ->
  fvP ps = empty /\ free t = empty /\ free rt = empty.
Proof.
  intros I rt m ps t H. dependent destruction H.
  split; [|split].
  - pose proof (WFtype_empty_free _ H) as Hfr.
    simpl in Hfr. exact Hfr.
  - exact H2.
  - exact H3.
Qed.

Lemma mtypei_facts : forall m I ps t rt, mtypei(m,I) = ps ~> t ~> rt ->
  fvP ps = empty /\ free t = empty /\ free rt = empty.
Proof.
  intros m I ps t rt H. induction H.
  - assert (HMT : Forall (MType_OK_I I) Ms).
    { apply (IType_OK_MTypeI I Ms noDupMds).
      apply (iok I Ms noDupMds). exact H. }
    rewrite Forall_forall in HMT.
    assert (Hin : In (MDecl rt m ps t) Ms) by
      (apply (find_in_MDecl m Ms (MDecl rt m ps t)); exact H0).
    exact (MType_OK_I_decl I rt m ps t (HMT _ Hin)).
Qed.

(* ===== module chain ===== *)
Definition DirectParent (C D:ClassName) : Prop :=
  exists Is Fs noDupfs K Ms noDupMds,
    find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds).

Lemma SubClass_step : forall b1 b2, SubClass b1 b2 ->
  forall C1 C, b1 = TClass C1 -> b2 = TClass C -> 
    C1 = C \/ exists D, DirectParent C1 D /\ SubClass (TClass D) (TClass C).
Proof.
  intros b1 b2 H.
  induction H as [ b | b1 b2 b3 H12 IH12 H23 IH23
                 | C D Is fs noDupfs K mds noDupMds Hfind
                 | C D Is I fs noDupfs K mds noDupMds i Hfind Hnth ];
    intros C1 C0 E1 E2.
  - subst b. injection E2 as ->. subst. left. reflexivity.
  - assert (Hb2 : exists C2, b2 = TClass C2) by (eapply SubClass_src_class; [exact H23|exact E2]).
    destruct Hb2 as [C2 Hb2].
    destruct (IH23 C2 C0 Hb2 E2) as [Heq|[D2 [Hpar2 Hsub2]]].
    + subst C2.
      destruct (IH12 C1 C0 E1 Hb2) as [Heq2|[D [Hpar Hsub]]].
      * left. exact Heq2.
      * right. exists D. split; [exact Hpar|exact Hsub].
    + destruct (IH12 C1 C2 E1 Hb2) as [Heq1|[D1 [Hpar1 Hsub1]]].
      * subst C1. right. exists D2. split; [exact Hpar2|exact Hsub2].
      * right. exists D1. split; [exact Hpar1|].
        eapply SubCTrans; [exact Hsub1|].
        destruct Hpar2 as [Is [Fs [noDupfs [K [Ms [noDupMds Hfind]]]]]].
        eapply SubCTrans.
        -- eapply SubCInh; exact Hfind.
        -- exact Hsub2.
  - injection E1 as Hc1. injection E2 as Hc2. subst C1. subst C0.
    right. exists D. split; [|apply SubCRefl].
    exists Is, fs, noDupfs, K, mds, noDupMds. exact Hfind.
  - subst. discriminate E2.
Qed.

Lemma m_body_decl : forall m C body, m_body m C body ->
  exists D ps t rt e, mtype(m,C) = ps ~> t ~> rt /\
    mtype(m,D) = ps ~> t ~> rt /\
    MType_OK D (MDefn (MDecl rt m ps t) e) /\ body = e.
Proof.
  intros m C body H.
  induction H as
    [C D Is m0 ps rt t e Fs K Ms noDupfs noDupMds Hfind Hmfind
    |C D Is m0 e Fs K Ms noDupfs noDupMds Hfind Hnone Hbody IH].
  - exists C, ps, t, rt, e. split; [|split; [|split]].
    + eapply mty_ok; eauto.
    + eapply mty_ok; eauto.
    + assert (HMT := CType_OK_MType C D Is Fs noDupfs K Ms noDupMds
                    (cok C D Fs noDupfs K Is Ms noDupMds Hfind)).
      rewrite Forall_forall in HMT.
      apply HMT.
      apply (find_in_MDefn m0 Ms (MDefn (MDecl rt m0 ps t) e)). exact Hmfind.
    + reflexivity.
  - destruct IH as [D0 [ps0 [t0 [rt0 [e2 [Hm1 [Hm2 [Hok Hb]]]]]]]].
    exists D0, ps0, t0, rt0, e2. split; [|split; [|split]].
    + eapply mty_no_override; [exact Hfind|exact Hnone|exact Hm1].
    + exact Hm2.
    + exact Hok.
    + exact Hb.
Qed.

Lemma RefCDecl_inv : forall C D1 Is1 F1 n1 K1 M1 nm1 D2 Is2 F2 n2 K2 M2 nm2,
  RefCDecl C D1 Is1 F1 n1 K1 M1 nm1 = RefCDecl C D2 Is2 F2 n2 K2 M2 nm2 ->
  D1 = D2 /\ Is1 = Is2 /\ F1 = F2 /\ K1 = K2 /\ M1 = M2.
Proof.
  intros. dependent destruction H. auto.
Qed.

Lemma find_some_det : forall {A} `{Referable A} (l:[A]) k (a b:A),
  find k l = Some a -> find k l = Some b -> a = b.
Proof.
  intros A RA l k a b H1 H2. rewrite H1 in H2. injection H2 as ->. reflexivity.
Qed.

Lemma RefCDecl_inv2 : forall C D1 Is1 F1 n1 K1 M1 nm1 D2 Is2 F2 n2 K2 M2 nm2,
  RefCDecl C D1 Is1 F1 n1 K1 M1 nm1 = RefCDecl C D2 Is2 F2 n2 K2 M2 nm2 ->
  D1 = D2 /\ M1 = M2.
Proof. intros. dependent destruction H. auto. Qed.

Lemma m_type_det : forall m C ps t rt ps' t' rt',
  mtype(m,C) = ps ~> t ~> rt -> mtype(m,C) = ps' ~> t' ~> rt' ->
  ps = ps' /\ t = t' /\ rt = rt'.
Proof.
  intros m C ps t rt ps' t' rt' H1 H2.
  induction H1.
  - dependent destruction H2.
    + match goal with
      | HC1 : find ?C0 RefCT = Some ?d1, HC2 : find ?C0 RefCT = Some ?d2 |- _ =>
          pose proof (find_some_det _ _ d1 d2 HC1 HC2) as Hdecl
      end.
      apply RefCDecl_inv2 in Hdecl. destruct Hdecl as [HD HMs].
      rewrite HD in *. rewrite HMs in *.
      match goal with
      | Hs1 : find ?m ?Ms = Some ?a, Hs2 : find ?m ?Ms = Some ?b |- _ =>
          pose proof (find_some_det Ms m a b Hs1 Hs2) as Hmdeq
      end.
      dependent destruction Hmdeq. auto.
    + match goal with
      | HC1 : find ?C0 RefCT = Some ?d1, HC2 : find ?C0 RefCT = Some ?d2 |- _ =>
          pose proof (find_some_det _ _ d1 d2 HC1 HC2) as Hdecl
      end.
      apply RefCDecl_inv2 in Hdecl. destruct Hdecl as [HD HMs].
      rewrite HD in *. rewrite HMs in *.
      exfalso.
      match goal with
      | Hs : find ?m ?Ms = Some _, Hn : find ?m ?Ms = None |- _ =>
          rewrite Hs in Hn; discriminate Hn
      end.
  - dependent destruction H2.
    + match goal with
      | HC1 : find ?C0 RefCT = Some ?d1, HC2 : find ?C0 RefCT = Some ?d2 |- _ =>
          pose proof (find_some_det _ _ d1 d2 HC1 HC2) as Hdecl
      end.
      apply RefCDecl_inv2 in Hdecl. destruct Hdecl as [HD HMs].
      rewrite HD in *. rewrite HMs in *.
      exfalso.
      match goal with
      | Hs : find ?m ?Ms = Some _, Hn : find ?m ?Ms = None |- _ =>
          rewrite Hs in Hn; discriminate Hn
      end.
    + match goal with
      | HC1 : find ?C0 RefCT = Some ?d1, HC2 : find ?C0 RefCT = Some ?d2 |- _ =>
          pose proof (find_some_det _ _ d1 d2 HC1 HC2) as Hdecl
      end.
      apply RefCDecl_inv2 in Hdecl. destruct Hdecl as [HD HMs].
      rewrite HD in *. rewrite HMs in *.
      apply IHm_type. assumption.
Qed.

Lemma m_type_decomp : forall m C ps t rt, mtype(m,C) = ps ~> t ~> rt ->
  (exists D Is Fs noDupfs K Ms noDupMds e,
     find C RefCT = Some (RefCDecl C D Is Fs noDupfs K Ms noDupMds) /\
     find m Ms = Some (MDefn (MDecl rt m ps t) e) /\ DirectParent C D) \/
  (exists D, DirectParent C D /\ mtype(m,D) = ps ~> t ~> rt).
Proof.
  intros m C ps t rt H. dependent destruction H.
  - left. exists D, Is, Fs, noDupfs, K, Ms, noDupMds, e.
    split; [exact H|split; [exact H0|]].
    exists Is, Fs, noDupfs, K, Ms, noDupMds. exact H.
  - right. exists D. split; [|exact H1].
    exists Is, Fs, noDupfs, K, Ms, noDupMds. exact H.
Qed.

Lemma m_body_decl_sub : forall m C body, m_body m C body ->
  exists D ps t rt e, mtype(m,C) = ps ~> t ~> rt /\
    mtype(m,D) = ps ~> t ~> rt /\
    MType_OK D (MDefn (MDecl rt m ps t) e) /\ body = e /\
    SubClass (TClass C) (TClass D).
Proof.
  intros m C body H.
  induction H as
    [C D Is m0 ps rt t e Fs K Ms noDupfs noDupMds Hfind Hmfind
    |C D Is m0 e Fs K Ms noDupfs noDupMds Hfind Hnone Hbody IH].
  - exists C, ps, t, rt, e. split; [|split; [|split; [|split]]].
    + eapply mty_ok; eauto.
    + eapply mty_ok; eauto.
    + assert (HMT := CType_OK_MType C D Is Fs noDupfs K Ms noDupMds
                    (cok C D Fs noDupfs K Is Ms noDupMds Hfind)).
      rewrite Forall_forall in HMT.
      apply HMT.
      apply (find_in_MDefn m0 Ms (MDefn (MDecl rt m0 ps t) e)). exact Hmfind.
    + reflexivity.
    + apply SubCRefl.
  - destruct IH as [D0 [ps0 [t0 [rt0 [e2 [Hm1 [Hm2 [Hok [Hb Hsub]]]]]]]]].
    exists D0, ps0, t0, rt0, e2. split; [|split; [|split; [|split]]].
    + eapply mty_no_override; [exact Hfind|exact Hnone|exact Hm1].
    + exact Hm2.
    + exact Hok.
    + exact Hb.
    + eapply SubCTrans.
      * eapply SubCInh; exact Hfind.
      * exact Hsub.
Qed.

Lemma ctsubst_openT_at : forall t th y v j, LCsubst th -> isValue v ->
  ~ In y (free t) ->
  ctsubst (CCons y v th) (openT_at j y t) = tsubBV_at j v (ctsubst th t).
Proof.
  intros t th y v j Hlc Hv Hy. destruct t as [b ps].
  change (ctsubst th (tsubFV y v (openT_at j y (TRefn b ps))) =
          tsubBV_at j v (ctsubst th (TRefn b ps))).
  rewrite tsubFV_openT; auto.
  rewrite tsubBV_at_TRefn. rewrite ctsubst_TRefn.
  rewrite ctsubst_TRefn. rewrite tsubBV_at_TRefn.
  rewrite cpsubst_psubBV; auto.
  rewrite (csubst_value v Hv).
  reflexivity.
Qed.

Lemma cpsubst_openP_at : forall ps th y v j, LCsubst th -> isValue v ->
  ~ In y (fvP ps) ->
  cpsubst (CCons y v th) (openP_at j y ps) = psubBV_at j v (cpsubst th ps).
Proof.
  intros ps th y v j Hlc Hv Hy.
  change (cpsubst th (psubFV y v (openP_at j y ps)) = psubBV_at j v (cpsubst th ps)).
  rewrite psubFV_openP; [|exact Hy].
  rewrite cpsubst_psubBV; [|exact Hlc].
  rewrite (csubst_value v Hv).
  reflexivity.
Qed.

Lemma Denotes_head_drop : forall b p ps v,
  Denotes (TRefn b (PCons p ps)) v -> Denotes (TRefn b ps) v.
Proof.
  intros b p ps v H.
  eapply Denotes_impl; [|exact H].
  intro HP. inversion HP as [|p0 ps0 Hh Ht]; subst. exact Ht.
Qed.

Lemma isLCL_at_map_id : forall (l:[expr]) (j:index) (f:expr->expr),
  (forall a, In a l -> isLC_at j a -> f a = a) ->
  isLCL_at j l -> map f l = l.
Proof.
  induction l as [|a l IH]; simpl; intros j f Hf Hl.
  - reflexivity.
  - destruct Hl as [Ha Hl]. f_equal.
    + apply Hf; [left; reflexivity|exact Ha].
    + apply (IH j f); [intros b Hb; apply Hf; right; exact Hb|exact Hl].
Qed.

Lemma open_at_LC : forall e j y, isLC_at j e -> open_at j y e = e.
Proof.
  refine (proj1 (syntax_mutind'
    (fun e => forall j y, isLC_at j e -> open_at j y e = e)
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. intros i j y H. destruct (j =? i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - simpl. reflexivity.
  - simpl. intros o e0 IH j y H. simpl. rewrite IH; auto.
  - simpl. intros o e1 IH1 e2 IH2 j y H. simpl.
    destruct H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
  - simpl. intros e1 IH1 m e2 IH2 j y H. simpl.
    destruct H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
  - simpl. intros e0 IH f j y H. simpl. rewrite IH; auto.
  - intros c l HF j y H. rewrite Forall_forall in HF. simpl. f_equal.
    apply isLCL_at_map_id with (j := j) (f := open_at j y).
    + intros a Ha. apply HF; exact Ha.
    + exact H.
  - simpl. intros e1 IH1 e2 IH2 j y H. simpl.
    destruct H as [H1 H2]. rewrite IH1; auto. rewrite IH2; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma subFV_open_at_other : forall e j y y' v,
  y <> y' -> isLC v ->
  subFV y' v (open_at j y e) = open_at j y (subFV y' v e).
Proof.
  refine (proj1 (syntax_mutind'
    (fun e => forall j y y' v, y <> y' -> isLC v ->
       subFV y' v (open_at j y e) = open_at j y (subFV y' v e))
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. intros i j y y' v Hne Hfv.
    destruct (j =? i) eqn:E; simpl.
    + destruct (y' =? y) eqn:E2; simpl; [|reflexivity].
      apply Nat.eqb_eq in E2. exfalso. apply Hne. symmetry. exact E2.
    + reflexivity.
  - simpl. intros x j y y' v Hne Hlc. simpl.
    destruct (y' =? x) eqn:E.
    + apply Nat.eqb_eq in E. subst y'.
      assert (Hvc : isLC_at j v) by (apply isLC_at_mono with (j:=0); [lia|exact Hlc]).
      rewrite (open_at_LC v j y Hvc). reflexivity.
    + reflexivity.
  - simpl. intros o e0 IH j y y' v Hne Hfv. simpl. rewrite IH; auto.
  - simpl. intros o e1 IH1 e2 IH2 j y y' v Hne Hfv. simpl.
    rewrite IH1; auto. rewrite IH2; auto.
  - simpl. intros e1 IH1 m e2 IH2 j y y' v Hne Hfv. simpl.
    rewrite IH1; auto. rewrite IH2; auto.
  - simpl. intros e0 IH f j y y' v Hne Hfv. simpl. rewrite IH; auto.
  - intros c l HF j y y' v Hne Hfv.
    rewrite Forall_forall in HF.
    rewrite sFV_New, open_New, sFV_New, open_New.
    rewrite map_map, map_map.
    f_equal. apply map_ext_in. intros a Ha.
    apply HF; auto.
  - simpl. intros e1 IH1 e2 IH2 j y y' v Hne Hfv. simpl.
    rewrite IH1; auto. rewrite IH2; auto.
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma psubFV_openP_other : forall ps j y y' v,
  y <> y' -> isLC v ->
  psubFV y' v (openP_at j y ps) = openP_at j y (psubFV y' v ps).
Proof.
  induction ps as [|p ps IH]; intros j y y' v Hne Hlc; simpl.
  - reflexivity.
  - rewrite IH; auto. rewrite subFV_open_at_other; auto.
Qed.

Lemma tsubFV_openT_other : forall t j y y' v,
  y <> y' -> isLC v ->
  tsubFV y' v (openT_at j y t) = openT_at j y (tsubFV y' v t).
Proof.
  intros [b ps] j y y' v Hne Hlc. simpl.
  rewrite psubFV_openP_other; auto.
Qed.

Lemma fvL_map_open_inv : forall (l:[expr]) j y x,
  (forall a, In a l -> forall x, In x (fv (open_at j y a)) -> In x (fv a) \/ x = y) ->
  In x (fvL (map (open_at j y) l)) -> In x (fvL l) \/ x = y.
Proof.
  induction l as [|a l IH]; intros j y x Hf Hx; simpl in *.
  - destruct Hx.
  - unfold union in Hx. rewrite set_union_iff in Hx. destruct Hx as [Hx|Hx].
    + destruct (Hf a (or_introl eq_refl) x Hx) as [Ha|Hy].
      * left. unfold union. rewrite set_union_iff. left. exact Ha.
      * right. exact Hy.
    + destruct (IH j y x (fun b Hb => Hf b (or_intror Hb)) Hx) as [Hl|Hy].
      * left. unfold union. rewrite set_union_iff. right. exact Hl.
      * right. exact Hy.
Qed.

Lemma fv_open_at_inv : forall e j y x,
  In x (fv (open_at j y e)) -> In x (fv e) \/ x = y.
Proof.
  refine (proj1 (syntax_mutind'
    (fun e => forall j y x, In x (fv (open_at j y e)) -> In x (fv e) \/ x = y)
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _)).
  - simpl. intros b j y x Hx. change (In x empty) in Hx. destruct Hx.
  - simpl. intros n j y x Hx. change (In x empty) in Hx. destruct Hx.
  - simpl. intros i j y x Hx. destruct (j =? i) eqn:E; simpl in Hx.
    + right. destruct Hx as [->|[]]. reflexivity.
    + left. exact Hx.
  - simpl. intros x0 j y x Hx. left. exact Hx.
  - simpl. intros o e0 IH j y x Hx. apply IH in Hx. exact Hx.
  - simpl. intros o e1 IH1 e2 IH2 j y x Hx.
    unfold union in Hx. rewrite set_union_iff in Hx. destruct Hx as [Hx|Hx].
    + destruct (IH1 j y x Hx) as [H|H]; [left; unfold union; rewrite set_union_iff; left; exact H|right; exact H].
    + destruct (IH2 j y x Hx) as [H|H]; [left; unfold union; rewrite set_union_iff; right; exact H|right; exact H].
  - simpl. intros e1 IH1 m e2 IH2 j y x Hx.
    unfold union in Hx. rewrite set_union_iff in Hx. destruct Hx as [Hx|Hx].
    + destruct (IH1 j y x Hx) as [H|H]; [left; unfold union; rewrite set_union_iff; left; exact H|right; exact H].
    + destruct (IH2 j y x Hx) as [H|H]; [left; unfold union; rewrite set_union_iff; right; exact H|right; exact H].
  - simpl. intros e0 IH f j y x Hx. apply IH in Hx. exact Hx.
  - intros c l HF j y x Hx.
    change (In x (fvL (map (open_at j y) l))) in Hx.
    rewrite Forall_forall in HF.
    apply fvL_map_open_inv with (j:=j) (y:=y) in Hx.
    + destruct Hx as [Hl|Hy]; [left; change (In x (fvL l)); exact Hl|right; exact Hy].
    + intros a Ha. exact (HF a Ha j y).
  - simpl. intros e1 IH1 e2 IH2 j y x Hx.
    unfold union in Hx. rewrite set_union_iff in Hx. destruct Hx as [Hx|Hx].
    + destruct (IH1 j y x Hx) as [H|H]; [left; unfold union; rewrite set_union_iff; left; exact H|right; exact H].
    + destruct (IH2 (j+1) y x Hx) as [H|H]; [left; unfold union; rewrite set_union_iff; right; exact H|right; exact H].
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.

Lemma fvP_openP_inv : forall ps j y x,
  In x (fvP (openP_at j y ps)) -> In x (fvP ps) \/ x = y.
Proof.
  induction ps as [|p ps IH]; intros j y x Hx; simpl in *.
  - destruct Hx.
  - unfold union in Hx. rewrite set_union_iff in Hx. destruct Hx as [Hx|Hx].
    + destruct (fv_open_at_inv p j y x Hx) as [H|H].
      * left; unfold union; rewrite set_union_iff; left; exact H.
      * right; exact H.
    + destruct (IH j y x Hx) as [H|H].
      * left; unfold union; rewrite set_union_iff; right; exact H.
      * right; exact H.
Qed.

Lemma free_openT_inv : forall t j y x,
  In x (free (openT_at j y t)) -> In x (free t) \/ x = y.
Proof. intros [b ps] j y x Hx. simpl in *. exact (fvP_openP_inv ps (j+1) y x Hx). Qed.
Lemma ctsubst_openT2 : forall t y y' w vb,
  y <> y' -> isValue w -> isValue vb ->
  ~ In y (free t) -> ~ In y' (free t) ->
  ctsubst (CCons y w (CCons y' vb CEmpty)) (openT_at 1 y (openT_at 0 y' t))
    = tsubBV_at 1 w (tsubBV vb t).
Proof.
  intros t y y' w vb Hne Hw Hvb Hy Hy'.
  change (ctsubst (CCons y' vb CEmpty)
            (tsubFV y w (openT_at 1 y (openT_at 0 y' t)))
          = tsubBV_at 1 w (tsubBV vb t)).
  assert (Hyopen : ~ In y (free (openT_at 0 y' t))).
  { intro H. destruct (free_openT_inv t 0 y' y H) as [H1|H1].
    - exact (Hy H1).
    - exact (Hne H1). }
  rewrite tsubFV_openT; [|exact Hyopen].
  change (tsubFV y' vb (tsubBV_at 1 w (openT_at 0 y' t))
          = tsubBV_at 1 w (tsubBV vb t)).
  rewrite tsubFV_tsubBV; [|apply isValue_isLC; exact Hvb].
  rewrite isValue_subFV; [|exact Hw].
  rewrite tsubFV_openT; [|exact Hy'].
  reflexivity.
Qed.


(* ===== module mtrans ===== *)
Lemma find_some_ref : forall {A} `{Referable A} (l:[A]) k d,
  find k l = Some d -> ref d = k.
Proof.
  intros A RA l. induction l as [|a l IH]; simpl; intros k d H.
  - discriminate.
  - destruct (k =? ref a) eqn:E.
    + injection H as ->. apply Nat.eqb_eq in E. symmetry. exact E.
    + apply IH; exact H.
Qed.

Lemma MType_OK_override : forall C rt m ps t e,
  MType_OK C (MDefn (MDecl rt m ps t) e) ->
  exists D, DirectParent C D /\ override m C D ps t rt.
Proof.
  intros. dependent destruction H.
  exists D. split.
  - exists Is, Fs, noDupfs, K, Ms, noDupMds. exact H.
  - exact H1.
Qed.

Lemma DirectParent_det : forall C D1 D2,
  DirectParent C D1 -> DirectParent C D2 -> D1 = D2.
Proof.
  intros C D1 D2 [Is1 [Fs1 [n1 [K1 [M1 [nm1 H1]]]]]]
                   [Is2 [Fs2 [n2 [K2 [M2 [nm2 H2]]]]]].
  pose proof (find_some_det _ C _ _ H1 H2) as Heq.
  apply RefCDecl_inv2 in Heq. tauto.
Qed.

Lemma ctsubst_openT2' : forall t y y' w vb,
  y <> y' -> isValue w -> isValue vb ->
  ~ In y (free t) -> ~ In y' (free t) ->
  ctsubst (CCons y' vb (CCons y w CEmpty)) (openT_at 1 y (openT_at 0 y' t))
    = tsubBV_at 1 w (tsubBV vb t).
Proof.
  intros t y y' w vb Hne Hw Hvb Hy Hy'.
  change (ctsubst (CCons y w CEmpty)
            (tsubFV y' vb (openT_at 1 y (openT_at 0 y' t)))
          = tsubBV_at 1 w (tsubBV vb t)).
  rewrite tsubFV_openT_other; [|exact Hne|apply isValue_isLC; exact Hvb].
  rewrite tsubFV_openT; [|exact Hy'].
  change (ctsubst (CCons y w CEmpty) (openT_at 1 y (tsubBV vb t))
          = tsubBV_at 1 w (tsubBV vb t)).
  assert (Hfvt : ~ In y (free (tsubBV vb t))).
  { change (~ In y (free (tsubBV_at 0 vb t))).
    rewrite (proj1 (proj2 fv_subBV_gen) t 0 vb Hvb). exact Hy. }
  rewrite ctsubst_openT_at; [|apply LCsubst_empty|exact Hw|exact Hfvt].
  reflexivity.
Qed.

Lemma mtype_transfer_cur : forall b1 b2, SubClass b1 b2 ->
  forall C1 X C, b1 = TClass X -> b2 = TClass C ->
  SubClass (TClass C1) (TClass X) ->
  forall m ps_s t_s rt_s, mtype(m,C) = ps_s ~> t_s ~> rt_s ->
  forall es vb,
    Denotes (TRefn (TNom (TClass C)) ps_s) (ExpNew C1 es) ->
    Denotes (tsubBV (ExpNew C1 es) t_s) vb ->
    exists ps_x t_x rt_x,
      mtype(m,X) = ps_x ~> t_x ~> rt_x /\
      fvP ps_x = empty /\ free t_x = empty /\ free rt_x = empty /\
      Denotes (TRefn (TNom (TClass X)) ps_x) (ExpNew C1 es) /\
      Denotes (tsubBV (ExpNew C1 es) t_x) vb /\
      (forall v, Denotes (tsubBV_at 1 (ExpNew C1 es) (tsubBV vb rt_x)) v ->
                 Denotes (tsubBV_at 1 (ExpNew C1 es) (tsubBV vb rt_s)) v).
Proof.
  intros b1 b2 H2.
  induction H2; intros C1 Xt Ct E1 E2 H1 m ps_s t_s rt_s Hstat es vb Hself Harg.
  - (* Refl *) subst b. injection E2 as ->.
    exists ps_s, t_s, rt_s. split; [exact Hstat|].
    destruct (mtype_facts m _ ps_s t_s rt_s Hstat) as [Hps [Ht Hrt]].
    split; [exact Hps|]. split; [exact Ht|]. split; [exact Hrt|].
    split; [exact Hself|]. split; [exact Harg|].
    intros v Hv. exact Hv.
  - (* Trans *)
    assert (Hb2 : exists C2, b2 = TClass C2) by (eapply SubClass_src_class; [exact H2_0|exact E2]).
    destruct Hb2 as [C2 Hb2].
    assert (H12c : SubClass (TClass Xt) (TClass C2)).
    { rewrite E1 in H2_. rewrite Hb2 in H2_. exact H2_. }
    assert (H1c : SubClass (TClass C1) (TClass C2)).
    { eapply SubCTrans; [exact H1|exact H12c]. }
    destruct (IHSubClass2 C1 C2 Ct Hb2 E2 H1c m ps_s t_s rt_s Hstat es vb Hself Harg)
      as [ps_m [t_m [rt_m [Hm_mid [Hps_m [Ht_m [Hrt_m [Hself_m [Harg_m Hres_m]]]]]]]]].
    destruct (IHSubClass1 C1 Xt C2 E1 Hb2 H1 m ps_m t_m rt_m Hm_mid es vb Hself_m Harg_m)
      as [ps_x [t_x [rt_x [Hm_x [Hps_x [Ht_x [Hrt_x [Hself_x [Harg_x Hres_x]]]]]]]]].
    exists ps_x, t_x, rt_x. split; [exact Hm_x|].
    split; [exact Hps_x|]. split; [exact Ht_x|]. split; [exact Hrt_x|].
    split; [exact Hself_x|]. split; [exact Harg_x|].
    intros v Hv. apply Hres_m. apply Hres_x. exact Hv.
  - (* Inh *)
    injection E1 as ->. injection E2 as ->.
    destruct (find m mds) as [d|] eqn:Hfm.
    + (* declared at C *)
      destruct d as [md e0]. destruct md as [rt0 m0 ps0 t0].
      assert (Hm0 : m0 = m).
      { change (ref (MDefn (MDecl rt0 m0 ps0 t0) e0) = m).
        apply (find_some_ref mds m (MDefn (MDecl rt0 m0 ps0 t0) e0)). exact Hfm. }
      subst m0.
      assert (HMT : Forall (MType_OK Xt) mds).
      { apply (CType_OK_MType Xt Ct Is fs noDupfs K mds noDupMds).
        apply (cok Xt Ct fs noDupfs K Is mds noDupMds). exact H. }
      rewrite Forall_forall in HMT.
      assert (Hok : MType_OK Xt (MDefn (MDecl rt0 m ps0 t0) e0)).
      { apply HMT. apply (find_in_MDefn m mds (MDefn (MDecl rt0 m ps0 t0) e0)). exact Hfm. }
      destruct (MType_OK_override Xt rt0 m ps0 t0 e0 Hok) as [D' [Hpar Hov]].
      assert (HD' : D' = Ct).
      { eapply DirectParent_det; [exact Hpar|].
        exists Is, fs, noDupfs, K, mds, noDupMds. exact H. }
      subst D'.
      destruct (MType_OK_decl Xt rt0 m ps0 t0 e0 Hok) as [Hps0 [Ht0 Hrt0]].
      destruct (mtype_facts m Ct ps_s t_s rt_s Hstat) as [Hps_s [Ht_s Hrt_s]].
      destruct (Hov t_s rt_s ps_s Hstat) as [Hself_sub [Harg_sub Hres_sub]].
      pose proof (Denotes_isValue _ _ Hself) as Hw.
      assert (Hself_C : Denotes (TRefn (TNom (TClass Xt)) ps_s) (ExpNew C1 es)).
      { eapply Denotes_rebase; [exact Hself|exact H1]. }
      assert (Hself_new : Denotes (TRefn (TNom (TClass Xt)) ps0) (ExpNew C1 es)).
      { exact (Subtype_sound Empty (TRefn (TNom (TClass Xt)) ps_s)
                 (TRefn (TNom (TClass Xt)) ps0) Hself_sub CEmpty DEmp
                 (ExpNew C1 es) Hself_C). }
      pose (y := freshv (free t_s ++ (free t0 ++ (free rt0 ++ free rt_s)))).
      assert (Hy_all : ~ In y (free t_s ++ (free t0 ++ (free rt0 ++ free rt_s))))
        by (apply freshv_notin).
      assert (Hy_ts : ~ In y (free t_s))
        by (apply (notin_app_l (free t_s) (free t0 ++ (free rt0 ++ free rt_s)) y); exact Hy_all).
      assert (Hy_rest : ~ In y (free t0 ++ (free rt0 ++ free rt_s)))
        by (apply (notin_app_r (free t_s) (free t0 ++ (free rt0 ++ free rt_s)) y); exact Hy_all).
      assert (Hy_t0 : ~ In y (free t0))
        by (apply (notin_app_l (free t0) (free rt0 ++ free rt_s) y); exact Hy_rest).
      assert (Hy_rest2 : ~ In y (free rt0 ++ free rt_s))
        by (apply (notin_app_r (free t0) (free rt0 ++ free rt_s) y); exact Hy_rest).
      assert (Hy_r0 : ~ In y (free rt0))
        by (apply (notin_app_l (free rt0) (free rt_s) y); exact Hy_rest2).
      assert (Hy_rs : ~ In y (free rt_s))
        by (apply (notin_app_r (free rt0) (free rt_s) y); exact Hy_rest2).
      assert (Henv1 : DenotesEnv (Cons y (TRefn (TNom (TClass Xt)) ps_s) Empty)
                (CCons y (ExpNew C1 es) CEmpty)).
      { apply DExt.
        - apply DEmp.
        - unfold in_env. simpl. auto.
        - simpl. exact Hself_C. }
      assert (Harg_ct : Denotes (ctsubst (CCons y (ExpNew C1 es) CEmpty)
                           (openT_at 0 y t_s)) vb).
      { rewrite ctsubst_openT_at; [|apply LCsubst_empty|exact Hw|exact Hy_ts].
        change (Denotes (tsubBV (ExpNew C1 es) t_s) vb). exact Harg. }
      assert (Hct0 : ctsubst (CCons y (ExpNew C1 es) CEmpty) (openT_at 0 y t0)
                     = tsubBV (ExpNew C1 es) t0).
      { rewrite ctsubst_openT_at; [|apply LCsubst_empty|exact Hw|exact Hy_t0].
        change (tsubBV (ExpNew C1 es) t0 = tsubBV (ExpNew C1 es) t0). reflexivity. }
      assert (Harg_new : Denotes (tsubBV (ExpNew C1 es) t0) vb).
      { rewrite <- Hct0.
        eapply (Subtype_sound (Cons y (TRefn (TNom (TClass Xt)) ps_s) Empty)
                  (openT_at 0 y t_s) (openT_at 0 y t0)).
        - apply Harg_sub.
        - exact Henv1.
        - exact Harg_ct. }
      pose (y' := freshv (free rt0 ++ (free rt_s ++ (y :: nil)))).
      assert (Hy'_all : ~ In y' (free rt0 ++ (free rt_s ++ (y :: nil))))
        by (apply freshv_notin).
      assert (Hy'_r0 : ~ In y' (free rt0))
        by (apply (notin_app_l (free rt0) (free rt_s ++ (y :: nil)) y'); exact Hy'_all).
      assert (Hy'_rest : ~ In y' (free rt_s ++ (y :: nil)))
        by (apply (notin_app_r (free rt0) (free rt_s ++ (y :: nil)) y'); exact Hy'_all).
      assert (Hy'_rs : ~ In y' (free rt_s))
        by (apply (notin_app_l (free rt_s) (y :: nil) y'); exact Hy'_rest).
      assert (Hy'_list : ~ In y' (y :: nil))
        by (apply (notin_app_r (free rt_s) (y :: nil) y'); exact Hy'_rest).
      assert (Hy'ne : y' <> y).
      { intro Hneq. apply Hy'_list. rewrite Hneq. left. reflexivity. }
      assert (Hne' : y <> y') by (intro Hneq; apply Hy'ne; symmetry; exact Hneq).
      assert (Henv2 : DenotesEnv
                (Cons y' (openT_at 0 y t_s)
                   (Cons y (TRefn (TNom (TClass Xt)) ps_s) Empty))
                (CCons y' vb (CCons y (ExpNew C1 es) CEmpty))).
      { apply DExt.
        - exact Henv1.
        - unfold in_env. simpl. exact Hy'_list.
        - exact Harg_ct. }
      assert (Hct_rt0 : ctsubst (CCons y' vb (CCons y (ExpNew C1 es) CEmpty))
                         (openT_at 1 y (openT_at 0 y' rt0))
                       = tsubBV_at 1 (ExpNew C1 es) (tsubBV vb rt0)).
      { rewrite ctsubst_openT2'; [reflexivity|exact Hne'|exact Hw|exact (Denotes_isValue _ _ Harg)|exact Hy_r0|exact Hy'_r0]. }
      assert (Hct_rs : ctsubst (CCons y' vb (CCons y (ExpNew C1 es) CEmpty))
                        (openT_at 1 y (openT_at 0 y' rt_s))
                      = tsubBV_at 1 (ExpNew C1 es) (tsubBV vb rt_s)).
      { rewrite ctsubst_openT2'; [reflexivity|exact Hne'|exact Hw|exact (Denotes_isValue _ _ Harg)|exact Hy_rs|exact Hy'_rs]. }
      assert (Hres_new : forall v,
        Denotes (tsubBV_at 1 (ExpNew C1 es) (tsubBV vb rt0)) v ->
        Denotes (tsubBV_at 1 (ExpNew C1 es) (tsubBV vb rt_s)) v).
      { intros v Hv. rewrite <- Hct_rt0 in Hv. rewrite <- Hct_rs.
        eapply (Subtype_sound
                  (Cons y' (openT_at 0 y t_s)
                     (Cons y (TRefn (TNom (TClass Xt)) ps_s) Empty))
                  (openT_at 1 y (openT_at 0 y' rt0))
                  (openT_at 1 y (openT_at 0 y' rt_s))).
        - apply Hres_sub. exact Hne'.
        - exact Henv2.
        - exact Hv. }
      exists ps0, t0, rt0. split; [eapply mty_ok; eauto|].
      split; [exact Hps0|]. split; [exact Ht0|]. split; [exact Hrt0|].
      split; [exact Hself_new|]. split; [exact Harg_new|].
      exact Hres_new.
    + (* inherited *)
      destruct (mtype_facts m Ct ps_s t_s rt_s Hstat) as [Hps_s [Ht_s Hrt_s]].
      exists ps_s, t_s, rt_s. split.
      * eapply mty_no_override; [exact H|exact Hfm|exact Hstat].
      * split; [exact Hps_s|]. split; [exact Ht_s|]. split; [exact Hrt_s|].
        split.
        -- eapply Denotes_rebase; [exact Hself|exact H1].
        -- split; [exact Harg|].
           intros v Hv. exact Hv.

  - (* IInh *) discriminate E2.
Qed.

Lemma cpsubst_free_of_fvP : forall ps th, fvP ps = empty -> cpsubst th ps = ps.
Proof.
  intros ps th Hfv.
  assert (Ht : ctsubst th (TRefn (TNom (TClass Object)) ps) = TRefn (TNom (TClass Object)) ps).
  { apply ctsubst_free. simpl. exact Hfv. }
  rewrite ctsubst_TRefn in Ht. injection Ht as Heq. exact Heq.
Qed.

Lemma MType_OK_body : forall C rt m ps t e,
  MType_OK C (MDefn (MDecl rt m ps t) e) ->
  fv e = empty /\ free t = empty /\ free rt = empty /\ fvP ps = empty /\
  (forall y y', y <> y' ->
     Hastype (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C)) ps) Empty))
       (open_at 1 y (open_at 0 y' e))
       (openT_at 1 y (openT_at 0 y' rt))).
Proof.
  intros C rt m ps t e H. dependent destruction H.
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split.
  - pose proof (WFtype_empty_free _ H2) as Hfr. simpl in Hfr. exact Hfr.
  - exact H5.
Qed.

Lemma csubst_open_at2 : forall e y y' w vb,
  y <> y' -> isValue w -> isValue vb ->
  ~ In y (fv e) -> ~ In y' (fv e) ->
  csubst (CCons y' vb (CCons y w CEmpty)) (open_at 1 y (open_at 0 y' e))
    = subBV_at 1 w (subBV vb e).
Proof.
  intros e y y' w vb Hne Hw Hvb Hy Hy'.
  change (csubst (CCons y w CEmpty)
            (subFV y' vb (open_at 1 y (open_at 0 y' e)))
          = subBV_at 1 w (subBV vb e)).
  rewrite subFV_open_at_other; [|exact Hne|apply isValue_isLC; exact Hvb].
  rewrite subFV_open; [|exact Hy'].
  change (csubst (CCons y w CEmpty) (open_at 1 y (subBV vb e)) = subBV_at 1 w (subBV vb e)).
  assert (Hfv : ~ In y (fv (subBV vb e))).
  { change (~ In y (fv (subBV_at 0 vb e))).
    rewrite (fv_subBV_at e 0 vb Hvb). exact Hy. }
  rewrite csubst_open_at; [|apply LCsubst_empty|exact Hw|exact Hfv].
  reflexivity.
Qed.

Lemma comm_psubBV_lc : forall ps j k E w,
  j <> k -> isLC E -> isLC w ->
  psubBV_at k w (psubBV_at j E ps) = psubBV_at j E (psubBV_at k w ps).
Proof.
  induction ps as [|p ps IH]; intros j k E w Hjk HE Hw; simpl.
  - reflexivity.
  - rewrite IH; auto. rewrite (comm_subBV_lc p j k E w); auto.
Qed.

(* ===== module iface ===== *)
Lemma CType_OK_ClassImpl : forall C D Is fs noDupfs K mds noDupMds,
  CType_OK (RefCDecl C D Is fs noDupfs K mds noDupMds) ->
  forall i I, nth_error Is i = Some I -> Class_implemented C I.
Proof. intros. dependent destruction H. exact (H5 i I H6). Qed.

Lemma FJSubtype_iface_inv : forall C I,
  FJSubtype (TNom (TClass C)) (TNom (TInterface I)) ->
  SubClass (TClass C) (TInterface I).
Proof. intros. inversion H. assumption. Qed.

Lemma SubClass_from_iface : forall b1 b2, SubClass b1 b2 ->
  forall J, b1 = TInterface J -> b2 = TInterface J.
Proof.
  intros b1 b2 H. induction H; intros J E.
  - subst b. reflexivity.
  - apply (IHSubClass2 J). apply (IHSubClass1 J). exact E.
  - subst. discriminate E.
  - subst. discriminate E.
Qed.

Lemma SubClass_iface_eq : forall J I, SubClass (TInterface J) (TInterface I) -> J = I.
Proof.
  intros J I H.
  pose proof (SubClass_from_iface (TInterface J) (TInterface I) H J eq_refl) as Heq.
  injection Heq as ->. reflexivity.
Qed.

Lemma SubClass_to_interface : forall b1 b2, SubClass b1 b2 ->
  forall C1 It, b1 = TClass C1 -> b2 = TInterface It ->
  exists X, SubClass (TClass C1) (TClass X) /\
    exists D Is fs noDupfs K mds noDupMds i,
      find X RefCT = Some (RefCDecl X D Is fs noDupfs K mds noDupMds) /\
      nth_error Is i = Some It.
Proof.
  intros b1 b2 H. induction H; intros C1 It E1 E2.
  - subst b. discriminate E2.
  - destruct b2 as [C2|J].
    + destruct (IHSubClass2 C2 It eq_refl E2) as
        [X [HsubX [D [Is [fs [nd [K [mds [nmd [i [Hfind Hnth]]]]]]]]]]].
      exists X. split; [|exists D, Is, fs, nd, K, mds, nmd, i; split; assumption].
      eapply SubCTrans.
      * rewrite E1 in H. exact H.
      * exact HsubX.
    + assert (H23' : SubClass (TInterface J) (TInterface It)) by (rewrite E2 in H0; exact H0).
      assert (HJI : J = It) by (apply SubClass_iface_eq; exact H23').
      subst J. exact (IHSubClass1 C1 It E1 eq_refl).
  - subst. discriminate E2.
  - injection E1 as ->. injection E2 as ->.
    exists C1. split; [apply SubCRefl|].
    exists D, Is, fs, noDupfs, K, mds, noDupMds, i. split; assumption.
Qed.

Lemma RefIDecl_inv : forall I iMs nm iMs' nm',
  RefIDecl I iMs nm = RefIDecl I iMs' nm' -> iMs = iMs'.
Proof. intros. dependent destruction H. reflexivity. Qed.

Lemma mtypei_implement : forall C I m ps t rt,
  Class_implemented C I ->
  mtypei(m,I) = ps ~> t ~> rt ->
  exists ps' Ds D0,
    mtype(m,C) = ps' ~> Ds ~> D0 /\
    Subtype Empty (TRefn (TNom (TClass C)) ps) (TRefn (TNom (TClass C)) ps') /\
    subtype_under (TRefn (TNom (TClass C)) ps) t Ds /\
    subtype_under2 (TRefn (TNom (TClass C)) ps) t D0 rt.
Proof.
  intros C I m ps t rt HCI Hmti.
  dependent destruction HCI.
  dependent destruction Hmti.
  pose proof (find_some_det _ I _ _ H H1) as Hidecl.
  apply RefIDecl_inv in Hidecl. subst iMs.
  destruct (H0 m rt ps t H2) as [Ds [D0 [ps' [Hmtype [Hsub [Hargu Hresu]]]]]].
  exists ps', Ds, D0. split; [exact Hmtype|]. split; [exact Hsub|]. split; assumption.
Qed.

Lemma mtypei_transfer_impl : forall C I m ps t rt,
  Class_implemented C I ->
  mtypei(m,I) = ps ~> t ~> rt ->
  forall C1 es vb,
    SubClass (TClass C1) (TClass C) ->
    Denotes (TRefn (TNom (TInterface I)) ps) (ExpNew C1 es) ->
    Denotes (tsubBV (ExpNew C1 es) t) vb ->
    exists ps' Ds D0,
      mtype(m,C) = ps' ~> Ds ~> D0 /\
      fvP ps' = empty /\ free Ds = empty /\ free D0 = empty /\
      Denotes (TRefn (TNom (TClass C)) ps') (ExpNew C1 es) /\
      Denotes (tsubBV (ExpNew C1 es) Ds) vb /\
      (forall v, Denotes (tsubBV_at 1 (ExpNew C1 es) (tsubBV vb D0)) v ->
                 Denotes (tsubBV_at 1 (ExpNew C1 es) (tsubBV vb rt)) v).
Proof.
  intros C I m ps t rt HCI Hmti C1 es vb HsubC1C HselfI HargI.
  destruct (mtypei_facts m I ps t rt Hmti) as [Hps [Ht Hrt]].
  destruct (mtypei_implement C I m ps t rt HCI Hmti)
    as [ps' [Ds [D0 [Hmtype [Hsub [Hargu Hresu]]]]]].
  destruct (mtype_facts m C ps' Ds D0 Hmtype) as [Hps' [HDs HD0]].
  assert (Hw : isValue (ExpNew C1 es)) by (apply Denotes_isValue in HselfI; exact HselfI).
  assert (Hself_C : Denotes (TRefn (TNom (TClass C)) ps) (ExpNew C1 es)).
  { eapply Denotes_rebase; [exact HselfI|exact HsubC1C]. }
  assert (Hself_new : Denotes (TRefn (TNom (TClass C)) ps') (ExpNew C1 es)).
  { exact (Subtype_sound Empty (TRefn (TNom (TClass C)) ps)
             (TRefn (TNom (TClass C)) ps') Hsub CEmpty DEmp
             (ExpNew C1 es) Hself_C). }
  pose (y := 0).
  assert (Hy_t : ~ In y (free t)) by (rewrite Ht; intro H; exact H).
  assert (Hy_Ds : ~ In y (free Ds)) by (rewrite HDs; intro H; exact H).
  assert (Henv1 : DenotesEnv (Cons y (TRefn (TNom (TClass C)) ps) Empty)
            (CCons y (ExpNew C1 es) CEmpty)).
  { apply DExt.
    - apply DEmp.
    - unfold in_env. simpl. intro H. exact H.
    - simpl. exact Hself_C. }
  assert (Harg_ct : Denotes (ctsubst (CCons y (ExpNew C1 es) CEmpty)
                       (openT_at 0 y t)) vb).
  { rewrite ctsubst_openT_at; [|apply LCsubst_empty|exact Hw|exact Hy_t].
    change (Denotes (tsubBV (ExpNew C1 es) t) vb). exact HargI. }
  assert (Hct_Ds : ctsubst (CCons y (ExpNew C1 es) CEmpty) (openT_at 0 y Ds)
                   = tsubBV (ExpNew C1 es) Ds).
  { rewrite ctsubst_openT_at; [|apply LCsubst_empty|exact Hw|exact Hy_Ds].
    change (tsubBV (ExpNew C1 es) Ds = tsubBV (ExpNew C1 es) Ds). reflexivity. }
  assert (Harg_new : Denotes (tsubBV (ExpNew C1 es) Ds) vb).
  { rewrite <- Hct_Ds.
    eapply (Subtype_sound (Cons y (TRefn (TNom (TClass C)) ps) Empty)
              (openT_at 0 y t) (openT_at 0 y Ds)).
    - apply Hargu.
    - exact Henv1.
    - exact Harg_ct. }
  pose (y' := 1).
  assert (Hyy' : y <> y') by (unfold y, y'; lia).
  assert (Hy'_t : ~ In y' (free t)) by (rewrite Ht; intro H; exact H).
  assert (Hy'_D0 : ~ In y' (free D0)) by (rewrite HD0; intro H; exact H).
  assert (Hy_D0 : ~ In y (free D0)) by (rewrite HD0; intro H; exact H).
  assert (Hy_rt : ~ In y (free rt)) by (rewrite Hrt; intro H; exact H).
  assert (Hy'_rt : ~ In y' (free rt)) by (rewrite Hrt; intro H; exact H).
  assert (Henv2 : DenotesEnv
            (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C)) ps) Empty))
            (CCons y' vb (CCons y (ExpNew C1 es) CEmpty))).
  { apply DExt.
    - exact Henv1.
    - unfold in_env. simpl. intro H.
      destruct H as [Hxy|Hnil]; [unfold y, y' in Hxy; lia|exact Hnil].
    - exact Harg_ct. }
  assert (Hct_D0 : ctsubst (CCons y' vb (CCons y (ExpNew C1 es) CEmpty))
                     (openT_at 1 y (openT_at 0 y' D0))
                   = tsubBV_at 1 (ExpNew C1 es) (tsubBV vb D0)).
  { rewrite ctsubst_openT2'; [reflexivity|exact Hyy'|exact Hw|exact (Denotes_isValue _ _ HargI)|exact Hy_D0|exact Hy'_D0]. }
  assert (Hct_rt : ctsubst (CCons y' vb (CCons y (ExpNew C1 es) CEmpty))
                    (openT_at 1 y (openT_at 0 y' rt))
                  = tsubBV_at 1 (ExpNew C1 es) (tsubBV vb rt)).
  { rewrite ctsubst_openT2'; [reflexivity|exact Hyy'|exact Hw|exact (Denotes_isValue _ _ HargI)|exact Hy_rt|exact Hy'_rt]. }
  assert (Hres_new : forall v,
    Denotes (tsubBV_at 1 (ExpNew C1 es) (tsubBV vb D0)) v ->
    Denotes (tsubBV_at 1 (ExpNew C1 es) (tsubBV vb rt)) v).
  { intros v Hv. rewrite <- Hct_D0 in Hv. rewrite <- Hct_rt.
    eapply (Subtype_sound
              (Cons y' (openT_at 0 y t)
                 (Cons y (TRefn (TNom (TClass C)) ps) Empty))
              (openT_at 1 y (openT_at 0 y' D0))
              (openT_at 1 y (openT_at 0 y' rt))).
    - apply Hresu. exact Hyy'.
    - exact Henv2.
    - exact Hv. }
  exists ps', Ds, D0. split; [exact Hmtype|].
  split; [exact Hps'|]. split; [exact HDs|]. split; [exact HD0|].
  split; [exact Hself_new|]. split; [exact Harg_new|].
  exact Hres_new.
Qed.

(* ===== module invokcase ===== *)
Lemma sem_invok_class_case : forall F,
  (forall m, m < F -> forall g e t, Hastype g e t -> forall th, DenotesEnv g th ->
     forall v, EvalsToN m (csubst th e) v -> isValue v -> Denotes (ctsubst th t) v) ->
  forall g e1 e2 m t C ps ps' t' rt,
    Hastype g e1 (TRefn (TNom (TClass C)) ps') ->
    mtype(m, C) = ps ~> t ~> rt ->
    Subtype g (TRefn (TNom (TClass C)) ps') (TRefn (TNom (TClass C)) ps) ->
    Hastype g e2 t' ->
    Subtype g t' (tsubBV e1 t) ->
    isLC e2 -> isLC e1 ->
  forall th, DenotesEnv g th ->
  forall v, EvalsToN F (csubst th (ExpMethodInvoc e1 m e2)) v -> isValue v ->
    Denotes (ctsubst th (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2))) v.
Proof.
  intros F Hsmall g e1 e2 m t C ps ps' t' rt Hte1 Hm Hsub Hte2 Hsub2 Hlc2 Hlc1 th Hd v HN Hv.
  pose (Hlc_th := DenotesEnv_LCsubst g th Hd).
  rewrite csubst_Invok in HN.
  destruct (EvN_invok_decomp F (csubst th e1) m (csubst th e2) v HN Hv)
    as [n1 [n2 [nb [C1 [es [vb [body [Hrec [HvalNew [HargEv [Hvb [Hmbody [HbodyEv Hn]]]]]]]]]]]]].
  assert (Hn1 : n1 < F) by lia.
  assert (Hn2 : n2 < F) by lia.
  assert (Hnb : nb < F) by lia.
  (* receiver denotation at static declaration predicates *)
  pose proof (Hsmall n1 Hn1 g e1 (TRefn (TNom (TClass C)) ps') Hte1 th Hd
                (ExpNew C1 es) Hrec HvalNew) as HDrec.
  pose proof (Subtype_sound g (TRefn (TNom (TClass C)) ps') (TRefn (TNom (TClass C)) ps)
                Hsub th Hd (ExpNew C1 es) HDrec) as HDrec2.
  rewrite ctsubst_TRefn in HDrec2.
  destruct (mtype_facts m C ps t rt Hm) as [Hps_e [Ht_e Hrt_e]].
  rewrite (cpsubst_free_of_fvP ps th Hps_e) in HDrec2.
  destruct (Denotes_new_class_inv (TRefn (TNom (TClass C)) ps) (ExpNew C1 es) HDrec2
              (TNom (TClass C)) ps C1 es eq_refl eq_refl) as [Fs [HRF [HPE [HF2 Hsubj]]]].
  assert (HsubC : SubClass (TClass C1) (TClass C))
    by (apply (FJSubtype_class_inv C1 C); exact Hsubj).
  (* argument denotation at static argument type *)
  pose proof (Hsmall n2 Hn2 g e2 t' Hte2 th Hd vb HargEv Hvb) as HDarg.
  pose proof (Subtype_sound g t' (tsubBV e1 t) Hsub2 th Hd vb HDarg) as HDarg2.
  rewrite ctsubst_tsubBV0 in HDarg2; [|exact Hlc_th].
  rewrite (ctsubst_free th t Ht_e) in HDarg2.
  destruct t as [bt pst] eqn:Ht_eq.
  change (Denotes (tsubBV_at 0 (csubst th e1) (TRefn bt pst)) vb) in HDarg2.
  rewrite tsubBV_TRefn in HDarg2.
  assert (Hev1 : EvalsTo (csubst th e1) (ExpNew C1 es))
    by (apply EvN_EvalsTo with (n:=n1); exact Hrec).
  assert (HlcE1 : isLC (csubst th e1))
    by (exact (proj1 isLC_csubst_gen e1 th Hlc_th Hlc1)).
  assert (HDarg_w : Denotes (tsubBV_at 0 (ExpNew C1 es) (TRefn bt pst)) vb).
  { rewrite tsubBV_TRefn.
    eapply Denotes_tsubBV_fwd_nc;
      [exact HlcE1|exact Hev1|exact HvalNew|exact Hvb|exact HDarg2]. }
  (* transfer static mtype at C to dynamic mtype at C1 *)
  destruct (mtype_transfer_cur (TClass C1) (TClass C) HsubC C1 C1 C eq_refl eq_refl
              (SubCRefl (TClass C1)) m ps (TRefn bt pst) rt Hm es vb HDrec2 HDarg_w)
    as [ps_x [t_x [rt_x [Hm_x [Hps_x [Ht_x [Hrt_x [Hself_x [Harg_x Hres_x]]]]]]]]].
  (* body declaration *)
  destruct (m_body_decl_sub m C1 body Hmbody)
    as [D [ps_d [t_d [rt_d [e2b [Hm_d1 [Hm_d2 [Hok [Hb_eq HsubCd]]]]]]]]].
  destruct (m_type_det m C1 ps_x t_x rt_x ps_d t_d rt_d Hm_x Hm_d1)
    as [Hpsd [Htd Hrtd]].
  subst ps_d. subst t_d. subst rt_d.
  destruct (MType_OK_body D rt_x m ps_x t_x e2b Hok)
    as [Hfv_e [Hfree_td [Hfree_rtd [Hfv_psd HbodyTy]]]].
  rewrite Hb_eq in HbodyEv.
  (* choose fresh variable names *)
  pose (y := 0). pose (y' := 1).
  assert (Hyy' : y <> y') by (unfold y, y'; lia).
  assert (Hy_td : ~ In y (free t_x)) by (rewrite Hfree_td; intro H; exact H).
  assert (Hy_rtd : ~ In y (free rt_x)) by (rewrite Hfree_rtd; intro H; exact H).
  assert (Hy'_td : ~ In y' (free t_x)) by (rewrite Hfree_td; intro H; exact H).
  assert (Hy'_rtd : ~ In y' (free rt_x)) by (rewrite Hfree_rtd; intro H; exact H).
  assert (Hy_e : ~ In y (fv e2b)) by (rewrite Hfv_e; intro H; exact H).
  assert (Hy'_e : ~ In y' (fv e2b)) by (rewrite Hfv_e; intro H; exact H).
  (* body environment *)
  assert (Hself_D : Denotes (TRefn (TNom (TClass D)) ps_x) (ExpNew C1 es)).
  { eapply Denotes_rebase; [exact Hself_x|exact HsubCd]. }
  assert (Hpar : Denotes (ctsubst (CCons y (ExpNew C1 es) CEmpty) (openT_at 0 y t_x)) vb).
  { rewrite ctsubst_openT_at; [|apply LCsubst_empty|exact HvalNew|exact Hy_td].
    change (Denotes (tsubBV (ExpNew C1 es) t_x) vb). exact Harg_x. }
  assert (Henv_inner : DenotesEnv (Cons y (TRefn (TNom (TClass D)) ps_x) Empty)
                (CCons y (ExpNew C1 es) CEmpty)).
  { apply DExt.
    - apply DEmp.
    - unfold in_env. simpl. intro H. exact H.
    - simpl. exact Hself_D. }
  assert (Henv : DenotesEnv (Cons y' (openT_at 0 y t_x)
                (Cons y (TRefn (TNom (TClass D)) ps_x) Empty))
                (CCons y' vb (CCons y (ExpNew C1 es) CEmpty))).
  { apply DExt.
    - exact Henv_inner.
    - unfold in_env. simpl. intro H.
      destruct H as [Hxy|Hnil]; [unfold y, y' in Hxy; lia|exact Hnil].
    - exact Hpar. }
  (* body evaluation *)
  assert (HevB : EvalsToN nb (csubst (CCons y' vb (CCons y (ExpNew C1 es) CEmpty))
                        (open_at 1 y (open_at 0 y' e2b))) v).
  { rewrite (csubst_open_at2 e2b y y' (ExpNew C1 es) vb Hyy' HvalNew Hvb Hy_e Hy'_e).
    exact HbodyEv. }
  assert (HDb : Denotes (ctsubst (CCons y' vb (CCons y (ExpNew C1 es) CEmpty))
                    (openT_at 1 y (openT_at 0 y' rt_x))) v).
  { exact (Hsmall nb Hnb (Cons y' (openT_at 0 y t_x)
             (Cons y (TRefn (TNom (TClass D)) ps_x) Empty))
             (open_at 1 y (open_at 0 y' e2b))
             (openT_at 1 y (openT_at 0 y' rt_x))
             (HbodyTy y y' Hyy')
             (CCons y' vb (CCons y (ExpNew C1 es) CEmpty)) Henv v HevB Hv). }
  rewrite (ctsubst_openT2' rt_x y y' (ExpNew C1 es) vb Hyy' HvalNew Hvb Hy_rtd Hy'_rtd) in HDb.
  pose proof (Hres_x v HDb) as Hres_static.
  (* reduce the goal self type *)
  rewrite ctsubst_self.
  rewrite ctsubst_tsubBV; [|exact Hlc_th].
  rewrite ctsubst_tsubBV0; [|exact Hlc_th].
  rewrite (ctsubst_free th rt Hrt_e).
  destruct rt as [br prt] eqn:Hrt_eq.
  change (Denotes (self (tsubBV_at 1 (csubst th e1)
            (tsubBV_at 0 (csubst th e2) (TRefn br prt)))
            (csubst th (ExpMethodInvoc e1 m e2))) v).
  rewrite tsubBV_TRefn.
  rewrite tsubBV_at_TRefn.
  cbn [self].
  apply Denotes_self_eq.
  - assert (Hlcinv : isLC (ExpMethodInvoc e1 m e2)) by (simpl; split; assumption).
    exact (proj1 isLC_csubst_gen (ExpMethodInvoc e1 m e2) th Hlc_th Hlcinv).
  - (* two-hole transfer from values w, vb to expressions E1, E2 *)
    assert (HlcE2 : isLC (csubst th e2)).
    { exact (proj1 isLC_csubst_gen e2 th Hlc_th Hlc2). }
    assert (Hev2 : EvalsTo (csubst th e2) vb)
      by (apply EvN_EvalsTo with (n:=n2); exact HargEv).
    pose proof HvalNew as Hvalw.
    (* step 1: self value -> expression E1 at index 2 *)
    assert (Hs1 : Denotes (TRefn br (psubBV_at 2 (csubst th e1) (psubBV_at 1 vb prt))) v).
    { eapply Denotes_subBV_at_rev; [lia|exact HlcE1|exact Hev1|exact Hvalw|exact Hv|].
      change (Denotes (TRefn br (psubBV_at 2 (ExpNew C1 es) (psubBV_at 1 vb prt))) v)
        in Hres_static.
      exact Hres_static. }
    assert (Hs2 : Denotes (TRefn br (psubBV_at 1 vb (psubBV_at 2 (csubst th e1) prt))) v).
    { rewrite <- (comm_psubBV_lc prt 2 1 (csubst th e1) vb) in Hs1;
        [|lia|exact HlcE1|apply isValue_isLC; exact Hvb].
      exact Hs1. }
    assert (Hs3 : Denotes (TRefn br (psubBV_at 1 (csubst th e2) (psubBV_at 2 (csubst th e1) prt))) v).
    { eapply Denotes_subBV_at_rev; [lia|exact HlcE2|exact Hev2|exact Hvb|exact Hv|exact Hs2]. }
    assert (Hs4 : Denotes (TRefn br (psubBV_at 2 (csubst th e1) (psubBV_at 1 (csubst th e2) prt))) v).
    { rewrite <- (comm_psubBV_lc prt 1 2 (csubst th e2) (csubst th e1)) in Hs3;
        [|lia|exact HlcE2|exact HlcE1].
      exact Hs3. }
    exact Hs4.
  - rewrite csubst_Invok.
    exact (EvN_EvalsTo F (ExpMethodInvoc (csubst th e1) m (csubst th e2)) v HN).
Qed.

(* ===== module invokiface ===== *)
Lemma sem_invok_iface_case : forall F,
  (forall m, m < F -> forall g e t, Hastype g e t -> forall th, DenotesEnv g th ->
     forall v, EvalsToN m (csubst th e) v -> isValue v -> Denotes (ctsubst th t) v) ->
  forall g e1 e2 m t I ps ps' t' rt,
    Hastype g e1 (TRefn (TNom (TInterface I)) ps') ->
    mtypei(m, I) = ps ~> t ~> rt ->
    Subtype g (TRefn (TNom (TInterface I)) ps') (TRefn (TNom (TInterface I)) ps) ->
    Hastype g e2 t' ->
    Subtype g t' (tsubBV e1 t) ->
    isLC e2 -> isLC e1 ->
  forall th, DenotesEnv g th ->
  forall v, EvalsToN F (csubst th (ExpMethodInvoc e1 m e2)) v -> isValue v ->
    Denotes (ctsubst th (self (tsubBV_at 1 e1 (tsubBV e2 rt)) (ExpMethodInvoc e1 m e2))) v.
Proof.
  intros F Hsmall g e1 e2 m t I ps ps' t' rt Hte1 Hmti Hsub Hte2 Hsub2 Hlc2 Hlc1 th Hd v HN Hv.
  pose (Hlc_th := DenotesEnv_LCsubst g th Hd).
  rewrite csubst_Invok in HN.
  destruct (EvN_invok_decomp F (csubst th e1) m (csubst th e2) v HN Hv)
    as [n1 [n2 [nb [C1 [es [vb [body [Hrec [HvalNew [HargEv [Hvb [Hmbody [HbodyEv Hn]]]]]]]]]]]]].
  assert (Hn1 : n1 < F) by lia.
  assert (Hn2 : n2 < F) by lia.
  assert (Hnb : nb < F) by lia.
  pose proof (Hsmall n1 Hn1 g e1 (TRefn (TNom (TInterface I)) ps') Hte1 th Hd
                (ExpNew C1 es) Hrec HvalNew) as HDrec.
  pose proof (Subtype_sound g (TRefn (TNom (TInterface I)) ps') (TRefn (TNom (TInterface I)) ps)
                Hsub th Hd (ExpNew C1 es) HDrec) as HDrec2.
  rewrite ctsubst_TRefn in HDrec2.
  destruct (mtypei_facts m I ps t rt Hmti) as [Hps_e [Ht_e Hrt_e]].
  rewrite (cpsubst_free_of_fvP ps th Hps_e) in HDrec2.
  destruct (Denotes_new_class_inv (TRefn (TNom (TInterface I)) ps) (ExpNew C1 es) HDrec2
              (TNom (TInterface I)) ps C1 es eq_refl eq_refl) as [Fs [HRF [HPE [HF2 Hsubj]]]].
  assert (HsubI : SubClass (TClass C1) (TInterface I))
    by (apply (FJSubtype_iface_inv C1 I); exact Hsubj).
  destruct (SubClass_to_interface (TClass C1) (TInterface I) HsubI C1 I eq_refl eq_refl)
    as [X [HsubC1X [Dx [Isx [fsx [ndx [Kx [mdsx [nmdx [ix [HfindX HnthX]]]]]]]]]]].
  assert (HCI_X : Class_implemented X I).
  { eapply CType_OK_ClassImpl; [|exact HnthX].
    apply (cok X Dx fsx ndx Kx Isx mdsx nmdx). exact HfindX. }
  pose proof (Hsmall n2 Hn2 g e2 t' Hte2 th Hd vb HargEv Hvb) as HDarg.
  pose proof (Subtype_sound g t' (tsubBV e1 t) Hsub2 th Hd vb HDarg) as HDarg2.
  rewrite ctsubst_tsubBV0 in HDarg2; [|exact Hlc_th].
  rewrite (ctsubst_free th t Ht_e) in HDarg2.
  destruct t as [bt pst] eqn:Ht_eq.
  change (Denotes (tsubBV_at 0 (csubst th e1) (TRefn bt pst)) vb) in HDarg2.
  rewrite tsubBV_TRefn in HDarg2.
  assert (Hev1 : EvalsTo (csubst th e1) (ExpNew C1 es))
    by (apply EvN_EvalsTo with (n:=n1); exact Hrec).
  assert (HlcE1 : isLC (csubst th e1))
    by (exact (proj1 isLC_csubst_gen e1 th Hlc_th Hlc1)).
  assert (HDarg_w : Denotes (tsubBV_at 0 (ExpNew C1 es) (TRefn bt pst)) vb).
  { rewrite tsubBV_TRefn.
    eapply Denotes_tsubBV_fwd_nc;
      [exact HlcE1|exact Hev1|exact HvalNew|exact Hvb|exact HDarg2]. }
  destruct (mtypei_transfer_impl X I m ps (TRefn bt pst) rt HCI_X Hmti C1 es vb
              HsubC1X HDrec2 HDarg_w)
    as [psi [Ds [D0 [Hm_X [Hps_i [HDs [HD0 [Hself_X [Harg_X Hres_impl]]]]]]]]].
  destruct (mtype_transfer_cur (TClass C1) (TClass X) HsubC1X C1 C1 X eq_refl eq_refl
              (SubCRefl (TClass C1)) m psi Ds D0 Hm_X es vb Hself_X Harg_X)
    as [ps_x [t_x [rt_x [Hm_x [Hps_x [Ht_x [Hrt_x [Hself_x [Harg_x Hres_y]]]]]]]]].
  destruct (m_body_decl_sub m C1 body Hmbody)
    as [D [ps_d [t_d [rt_d [e2b [Hm_d1 [Hm_d2 [Hok [Hb_eq HsubCd]]]]]]]]].
  destruct (m_type_det m C1 ps_x t_x rt_x ps_d t_d rt_d Hm_x Hm_d1)
    as [Hpsd [Htd Hrtd]].
  subst ps_d. subst t_d. subst rt_d.
  assert (Hres_x : forall v,
    Denotes (tsubBV_at 1 (ExpNew C1 es) (tsubBV vb rt_x)) v ->
    Denotes (tsubBV_at 1 (ExpNew C1 es) (tsubBV vb rt)) v).
  { intros v0 Hv0. exact (Hres_impl v0 (Hres_y v0 Hv0)). }
  destruct (MType_OK_body D rt_x m ps_x t_x e2b Hok)
    as [Hfv_e [Hfree_td [Hfree_rtd [Hfv_psd HbodyTy]]]].
  rewrite Hb_eq in HbodyEv.
  (* choose fresh variable names *)
  pose (y := 0). pose (y' := 1).
  assert (Hyy' : y <> y') by (unfold y, y'; lia).
  assert (Hy_td : ~ In y (free t_x)) by (rewrite Hfree_td; intro H; exact H).
  assert (Hy_rtd : ~ In y (free rt_x)) by (rewrite Hfree_rtd; intro H; exact H).
  assert (Hy'_td : ~ In y' (free t_x)) by (rewrite Hfree_td; intro H; exact H).
  assert (Hy'_rtd : ~ In y' (free rt_x)) by (rewrite Hfree_rtd; intro H; exact H).
  assert (Hy_e : ~ In y (fv e2b)) by (rewrite Hfv_e; intro H; exact H).
  assert (Hy'_e : ~ In y' (fv e2b)) by (rewrite Hfv_e; intro H; exact H).
  (* body environment *)
  assert (Hself_D : Denotes (TRefn (TNom (TClass D)) ps_x) (ExpNew C1 es)).
  { eapply Denotes_rebase; [exact Hself_x|exact HsubCd]. }
  assert (Hpar : Denotes (ctsubst (CCons y (ExpNew C1 es) CEmpty) (openT_at 0 y t_x)) vb).
  { rewrite ctsubst_openT_at; [|apply LCsubst_empty|exact HvalNew|exact Hy_td].
    change (Denotes (tsubBV (ExpNew C1 es) t_x) vb). exact Harg_x. }
  assert (Henv_inner : DenotesEnv (Cons y (TRefn (TNom (TClass D)) ps_x) Empty)
                (CCons y (ExpNew C1 es) CEmpty)).
  { apply DExt.
    - apply DEmp.
    - unfold in_env. simpl. intro H. exact H.
    - simpl. exact Hself_D. }
  assert (Henv : DenotesEnv (Cons y' (openT_at 0 y t_x)
                (Cons y (TRefn (TNom (TClass D)) ps_x) Empty))
                (CCons y' vb (CCons y (ExpNew C1 es) CEmpty))).
  { apply DExt.
    - exact Henv_inner.
    - unfold in_env. simpl. intro H.
      destruct H as [Hxy|Hnil]; [unfold y, y' in Hxy; lia|exact Hnil].
    - exact Hpar. }
  (* body evaluation *)
  assert (HevB : EvalsToN nb (csubst (CCons y' vb (CCons y (ExpNew C1 es) CEmpty))
                        (open_at 1 y (open_at 0 y' e2b))) v).
  { rewrite (csubst_open_at2 e2b y y' (ExpNew C1 es) vb Hyy' HvalNew Hvb Hy_e Hy'_e).
    exact HbodyEv. }
  assert (HDb : Denotes (ctsubst (CCons y' vb (CCons y (ExpNew C1 es) CEmpty))
                    (openT_at 1 y (openT_at 0 y' rt_x))) v).
  { exact (Hsmall nb Hnb (Cons y' (openT_at 0 y t_x)
             (Cons y (TRefn (TNom (TClass D)) ps_x) Empty))
             (open_at 1 y (open_at 0 y' e2b))
             (openT_at 1 y (openT_at 0 y' rt_x))
             (HbodyTy y y' Hyy')
             (CCons y' vb (CCons y (ExpNew C1 es) CEmpty)) Henv v HevB Hv). }
  rewrite (ctsubst_openT2' rt_x y y' (ExpNew C1 es) vb Hyy' HvalNew Hvb Hy_rtd Hy'_rtd) in HDb.
  pose proof (Hres_x v HDb) as Hres_static.
  (* reduce the goal self type *)
  rewrite ctsubst_self.
  rewrite ctsubst_tsubBV; [|exact Hlc_th].
  rewrite ctsubst_tsubBV0; [|exact Hlc_th].
  rewrite (ctsubst_free th rt Hrt_e).
  destruct rt as [br prt] eqn:Hrt_eq.
  change (Denotes (self (tsubBV_at 1 (csubst th e1)
            (tsubBV_at 0 (csubst th e2) (TRefn br prt)))
            (csubst th (ExpMethodInvoc e1 m e2))) v).
  rewrite tsubBV_TRefn.
  rewrite tsubBV_at_TRefn.
  cbn [self].
  apply Denotes_self_eq.
  - assert (Hlcinv : isLC (ExpMethodInvoc e1 m e2)) by (simpl; split; assumption).
    exact (proj1 isLC_csubst_gen (ExpMethodInvoc e1 m e2) th Hlc_th Hlcinv).
  - (* two-hole transfer from values w, vb to expressions E1, E2 *)
    assert (HlcE2 : isLC (csubst th e2)).
    { exact (proj1 isLC_csubst_gen e2 th Hlc_th Hlc2). }
    assert (Hev2 : EvalsTo (csubst th e2) vb)
      by (apply EvN_EvalsTo with (n:=n2); exact HargEv).
    pose proof HvalNew as Hvalw.
    (* step 1: self value -> expression E1 at index 2 *)
    assert (Hs1 : Denotes (TRefn br (psubBV_at 2 (csubst th e1) (psubBV_at 1 vb prt))) v).
    { eapply Denotes_subBV_at_rev; [lia|exact HlcE1|exact Hev1|exact Hvalw|exact Hv|].
      change (Denotes (TRefn br (psubBV_at 2 (ExpNew C1 es) (psubBV_at 1 vb prt))) v)
        in Hres_static.
      exact Hres_static. }
    assert (Hs2 : Denotes (TRefn br (psubBV_at 1 vb (psubBV_at 2 (csubst th e1) prt))) v).
    { rewrite <- (comm_psubBV_lc prt 2 1 (csubst th e1) vb) in Hs1;
        [|lia|exact HlcE1|apply isValue_isLC; exact Hvb].
      exact Hs1. }
    assert (Hs3 : Denotes (TRefn br (psubBV_at 1 (csubst th e2) (psubBV_at 2 (csubst th e1) prt))) v).
    { eapply Denotes_subBV_at_rev; [lia|exact HlcE2|exact Hev2|exact Hvb|exact Hv|exact Hs2]. }
    assert (Hs4 : Denotes (TRefn br (psubBV_at 2 (csubst th e1) (psubBV_at 1 (csubst th e2) prt))) v).
    { rewrite <- (comm_psubBV_lc prt 1 2 (csubst th e2) (csubst th e1)) in Hs3;
        [|lia|exact HlcE2|exact HlcE1].
      exact Hs3. }
    exact Hs4.
  - rewrite csubst_Invok.
    exact (EvN_EvalsTo F (ExpMethodInvoc (csubst th e1) m (csubst th e2)) v HN).

Qed.

(* ===== module semfinal ===== *)
Lemma sem_inner_full : forall F,
  (forall m, m < F -> forall g e t, Hastype g e t -> forall th, DenotesEnv g th ->
     forall v, EvalsToN m (csubst th e) v -> isValue v -> Denotes (ctsubst th t) v) ->
  forall g e t, Hastype g e t -> forall th, DenotesEnv g th ->
  forall v, EvalsToN F (csubst th e) v -> isValue v -> Denotes (ctsubst th t) v.
Proof.
  intros F Hsmall g e t Hty th Hd v HN Hv.
  revert g t Hty th Hd v HN Hv.
  refine (proj1 (syntax_mutind'
    (fun e => forall g t, Hastype g e t -> forall th, DenotesEnv g th ->
        forall v, EvalsToN F (csubst th e) v -> isValue v -> Denotes (ctsubst th t) v)
    (fun (_:type) => True) (fun (_:preds) => True)
    _ _ _ _ _ _ _ _ _ _ _ _ _) e).
  - (* Bc *) intros b g t Hty th Hd v HN Hv.
    destruct (Hastype_to_D_sem g (Bc b) t Hty) as [s [HD Htr]].
    dependent destruction HD.
    apply (Htr th Hd v).
    rewrite csubst_Bc in HN.
    assert (Hveq : v = Bc b) by (apply (EvN_value_eq F (Bc b) v HN); simpl; exact I).
    subst v. rewrite ctsubst_tybc.
    change (Denotes (self (TRefn TBool PEmpty) (Bc b)) (Bc b)).
    apply Denotes_self_eq.
    + change (isLC_at 0 (Bc b)). exact (isValue_isLC' (Bc b) 0 I).
    + apply DenotesBool. apply PEEmp.
    + apply Refl.
  - (* Ic *) intros n g t Hty th Hd v HN Hv.
    destruct (Hastype_to_D_sem g (Ic n) t Hty) as [s [HD Htr]].
    dependent destruction HD.
    apply (Htr th Hd v).
    rewrite csubst_Ic in HN.
    assert (Hveq : v = Ic n) by (apply (EvN_value_eq F (Ic n) v HN); simpl; exact I).
    subst v. rewrite ctsubst_tyic.
    change (Denotes (self (TRefn TInt PEmpty) (Ic n)) (Ic n)).
    apply Denotes_self_eq.
    + change (isLC_at 0 (Ic n)). exact (isValue_isLC' (Ic n) 0 I).
    + apply DenotesInt. apply PEEmp.
    + apply Refl.
  - (* BV *) intros i g t Hty th Hd v HN Hv.
    destruct (Hastype_to_D_sem g (BV i) t Hty) as [s [HD Htr]].
    dependent destruction HD.
  - (* FV *) intros x g t Hty th Hd v HN Hv.
    destruct (Hastype_to_D_sem g (FV x) t Hty) as [s [HD Htr]].
    dependent destruction HD.
    destruct (DenotesEnv_lookup g th Hd x t0 H) as [vx [Hden Hxval]].
    rewrite Hxval in HN.
    assert (Hveq : v = vx) by
      (apply (EvN_value_eq F vx v HN); apply Denotes_isValue in Hden; exact Hden).
    subst v.
    apply (Htr th Hd vx).
    rewrite ctsubst_self. rewrite Hxval.
    apply Denotes_self_any.
    + apply Denotes_isValue in Hden. apply isValue_isLC; exact Hden.
    + exact Hden.
    + apply Refl.
  - (* UnOp *) intros op e1 IH g t Hty th Hd v HN Hv.
    destruct (Hastype_to_D_sem g (ExpUnOp op e1) t Hty) as [s [HD Htr]].
    destruct (HastypeD_unop_inv g op e1 s HD) as [Heqs [t0 [Hte [Hsub Hlce1]]]].
    subst s.
    rewrite csubst_UnOp in HN.
    destruct (EvN_unop_decomp F op (csubst th e1) v HN Hv)
      as [n1 [n2 [w [r [H1 [Hw [Hstep [H2 Hn]]]]]]]].
    destruct (Step_UnOp_inv op w r Hstep) as [[e0 [Hst Heq]] | [w0 [pf [He [Hval0 Heq]]]]].
    + exfalso. exact (isValue_not_step w e0 Hw Hst).
    + subst w0. subst r.
      assert (Hvr : isValue (udelta op w pf)).
      { destruct pf. simpl. destruct b; simpl; exact I. }
      assert (Hveq : v = udelta op w pf) by
        (apply (EvN_value_eq n2 (udelta op w pf) v H2 Hvr)).
      subst v.
      apply (Htr th Hd (udelta op w pf)).
      destruct pf.
      rewrite ctsubst_tyNot; [|apply (DenotesEnv_LCsubst g th Hd)].
      apply Denotes_self_eq.
      * cbn. apply (proj1 isLC_csubst_gen);
          [apply (DenotesEnv_LCsubst g th Hd) | exact Hlce1].
      * destruct b; simpl; apply DenotesBool; apply PEEmp.
      * eapply EvalsTo_trans with (b := ExpUnOp Not (Bc b)).
        -- apply EvalsTo_unop. eapply EvN_EvalsTo. exact H1.
        -- eapply AddStep; [exact Hstep | apply Refl].
  - (* BinOp *) intros op e1 IH1 e2 IH2 g t Hty th Hd v HN Hv.
    destruct (Hastype_to_D_sem g (ExpBinOp op e1 e2) t Hty) as [s [HD Htr]].
    destruct (HastypeD_binop_inv g op e1 e2 s HD) as
      [Heqs [t0 [t0' [Hte1 [Hsub1 [Hte2 [Hsub2 [Hlce1 Hlce2]]]]]]]].
    subst s.
    rewrite csubst_BinOp in HN.
    destruct (EvN_binop_decomp F op (csubst th e1) (csubst th e2) v HN Hv)
      as [n1 [n2 [n3 [w1 [w2 [r [H1 [Hw1 [H2 [Hw2 [Hstep [H3 Hn]]]]]]]]]]]].
    destruct (Step_BinOp_inv op w1 w2 r Hstep) as
      [[e0 [Hst Heq]] | [[e0 [Hval [Hst Heq]]] | [pf [Hval1 [Hval2 Heq]]]]].
    + exfalso. exact (isValue_not_step w1 e0 Hw1 Hst).
    + exfalso. exact (isValue_not_step w2 e0 Hw2 Hst).
    + subst r.
      assert (Hvr : isValue (bdelta op w1 w2 pf)).
      { destruct pf as [b1 b2 | b1 b2 | v1 v2 p1 p2]; simpl.
        - destruct b1, b2; simpl; exact I.
        - destruct b1, b2; simpl; exact I.
        - exact I. }
      assert (Hveq : v = bdelta op w1 w2 pf) by
        (apply (EvN_value_eq n3 (bdelta op w1 w2 pf) v H3 Hvr)).
      subst v.
      apply (Htr th Hd (bdelta op w1 w2 pf)).
      destruct pf as [b1 b2 | b1 b2 | v1 v2 p1 p2].
      * rewrite ctsubst_tyBinOp;
          [|apply (DenotesEnv_LCsubst g th Hd)|exact Hlce1|exact Hlce2].
        apply Denotes_self_eq.
        -- cbn. split; apply (proj1 isLC_csubst_gen);
             [apply (DenotesEnv_LCsubst g th Hd) | exact Hlce1
             |apply (DenotesEnv_LCsubst g th Hd) | exact Hlce2].
        -- destruct b1, b2; simpl; apply DenotesBool; apply PEEmp.
        -- eapply EvalsTo_trans with (b := ExpBinOp And (Bc b1) (Bc b2)).
           ++ eapply EvalsTo_trans with (b := ExpBinOp And (Bc b1) (csubst th e2)).
              ** apply EvalsTo_binop_l. eapply EvN_EvalsTo. exact H1.
              ** apply EvalsTo_binop_r; [exact Hw1 | eapply EvN_EvalsTo; exact H2].
           ++ eapply AddStep; [exact Hstep | apply Refl].
      * rewrite ctsubst_tyBinOp;
          [|apply (DenotesEnv_LCsubst g th Hd)|exact Hlce1|exact Hlce2].
        apply Denotes_self_eq.
        -- cbn. split; apply (proj1 isLC_csubst_gen);
             [apply (DenotesEnv_LCsubst g th Hd) | exact Hlce1
             |apply (DenotesEnv_LCsubst g th Hd) | exact Hlce2].
        -- destruct b1, b2; simpl; apply DenotesBool; apply PEEmp.
        -- eapply EvalsTo_trans with (b := ExpBinOp Or (Bc b1) (Bc b2)).
           ++ eapply EvalsTo_trans with (b := ExpBinOp Or (Bc b1) (csubst th e2)).
              ** apply EvalsTo_binop_l. eapply EvN_EvalsTo. exact H1.
              ** apply EvalsTo_binop_r; [exact Hw1 | eapply EvN_EvalsTo; exact H2].
           ++ eapply AddStep; [exact Hstep | apply Refl].
      * rewrite ctsubst_tyBinOp;
          [|apply (DenotesEnv_LCsubst g th Hd)|exact Hlce1|exact Hlce2].
        apply Denotes_self_eq.
        -- cbn. split; apply (proj1 isLC_csubst_gen);
             [apply (DenotesEnv_LCsubst g th Hd) | exact Hlce1
             |apply (DenotesEnv_LCsubst g th Hd) | exact Hlce2].
        -- apply DenotesBool. apply PEEmp.
        -- eapply EvalsTo_trans with (b := ExpBinOp Eq v1 v2).
           ++ eapply EvalsTo_trans with (b := ExpBinOp Eq v1 (csubst th e2)).
              ** apply EvalsTo_binop_l. eapply EvN_EvalsTo. exact H1.
              ** apply EvalsTo_binop_r; [exact Hw1 | eapply EvN_EvalsTo; exact H2].
           ++ eapply AddStep; [exact Hstep | apply Refl].
  - (* Invok *) intros e1 IH1 m e2 IH2 g0 t0 Hty0 th0 Hd0 v0 HN0 Hv0.
    destruct (Hastype_to_D_sem g0 (ExpMethodInvoc e1 m e2) t0 Hty0) as [s [HD Htr]].
    dependent destruction HD.
    + eapply Htr; [exact Hd0|].
      eapply (sem_invok_class_case F Hsmall); eauto.
    + eapply Htr; [exact Hd0|].
      eapply (sem_invok_iface_case F Hsmall); eauto.
  - (* Field *) intros e0 IH0 f g0 t0 Hty0 th0 Hd0 v0 HN0 Hv0.
    exact (sem_field_case F Hsmall g0 e0 f t0 Hty0 th0 Hd0 v0 HN0 Hv0).
  - (* New *) intros c l HF g0 t0 Hty0 th0 Hd0 v0 HN0 Hv0.
    rewrite Forall_forall in HF.
    exact (sem_new_case F Hsmall l (fun a Ha => HF a Ha) g0 c t0 Hty0 th0 Hd0 v0 HN0 Hv0).

  - (* Let *) intros e_x IHe_x e0 IHe0 g t Hty th Hd v HN Hv.
    destruct (Hastype_to_D_sem g (ExpLet e_x e0) t Hty) as [s [HD Htr]].
    destruct (HastypeD_let_inv g e_x e0 s HD) as
      [b [b' [nms [Heqs [Hwfb' [Hte Hbody]]]]]].
    subst s.
    rewrite csubst_Let in HN.
    pose (Hlcth := DenotesEnv_LCsubst g th Hd).
    destruct (EvN_let_decomp F (csubst th e_x) (csubst th e0) v HN Hv)
      as [nx [n2 [vx [Hx [Hvx [Hbev Hn]]]]]].
    assert (Hnx : nx < F) by lia.
    assert (Hn2 : n2 < F) by lia.
    assert (HDx : Denotes (ctsubst th b) vx) by
      (apply (Hsmall nx Hnx g e_x b Hte th Hd vx Hx Hvx)).
    assert (Hlcex0 : isLC e_x) by (exact (Hastype_isLC g e_x b Hte)).
    assert (Hle0 : isLC_at 1 e0).
    { pose (y0 := freshv nms).
      assert (Hy0 : ~ Elem y0 nms) by (apply freshv_notin).
      apply (isLC_open_at_inv e0 0 0 y0); [|lia].
      assert (HB0 : Hastype (Cons y0 b g) (unbind y0 e0) (unbindT y0 b'))
        by (apply Hbody; exact Hy0).
      change (isLC (unbind y0 e0)).
      exact (Hastype_isLC _ _ _ HB0). }
    assert (Hlcex : isLC (csubst th e_x)).
    { apply (proj1 isLC_csubst_gen); [exact Hlcth | exact Hlcex0]. }
    assert (Hlce0 : isLC_at 1 (csubst th e0)).
    { apply (isLC_csubst_at e0 th Hlcth 1 Hle0). }
    pose (y := freshv (nms ++ (fv e0 ++ (free b' ++ binds g)))).
    assert (Hyn : ~ In y (nms ++ (fv e0 ++ (free b' ++ binds g)))) by (apply freshv_notin).
    assert (Hy_nms : ~ Elem y nms) by (apply notin_app_l in Hyn; exact Hyn).
    assert (Hy_rest : ~ In y (fv e0 ++ (free b' ++ binds g))) by (apply notin_app_r in Hyn; exact Hyn).
    assert (Hy_fv : ~ In y (fv e0)) by (apply notin_app_l in Hy_rest; exact Hy_rest).
    assert (Hy_rest2 : ~ In y (free b' ++ binds g)) by (apply notin_app_r in Hy_rest; exact Hy_rest).
    assert (Hy_free : ~ In y (free b')) by (apply notin_app_l in Hy_rest2; exact Hy_rest2).
    assert (Hy_binds : ~ In y (binds g)) by (apply notin_app_r in Hy_rest2; exact Hy_rest2).
    assert (HlctB : isLCT b') by (apply (WFtype_isLCT g b' Hwfb')).
    pose (th' := CCons y vx th).
    assert (HDE : DenotesEnv (Cons y b g) th').
    { unfold th'. apply DExt; [exact Hd | unfold in_env; exact Hy_binds | exact HDx]. }
    assert (HEsubN : EvalsToN n2 (csubst th' (unbind y e0)) v).
    { unfold th', unbind.
      rewrite csubst_open_at; [|exact Hlcth|exact Hvx|exact Hy_fv].
      exact Hbev. }
    assert (HB : Hastype (Cons y b g) (unbind y e0) (unbindT y b'))
      by (apply Hbody; exact Hy_nms).
    assert (HDb : Denotes (ctsubst th' (unbindT y b')) v).
    { exact (Hsmall n2 Hn2 (Cons y b g) (unbind y e0) (unbindT y b') HB th' HDE v HEsubN Hv). }
    assert (HDb' : Denotes (ctsubst th b') v).
    { unfold th' in HDb. unfold unbindT in HDb.
      erewrite ctsubst_openT in HDb; [|exact Hlcth|exact Hvx|exact Hy_free|exact HlctB].
      exact HDb. }
    apply (Htr th Hd v).
    rewrite ctsubst_self. rewrite csubst_Let.
    apply Denotes_self_any.
    + cbn. split; [exact Hlcex | exact Hlce0].
    + exact HDb'.
    + exact (EvN_EvalsTo F _ v HN).
  - cbn; auto.
  - cbn; auto.
  - cbn; auto.
Qed.



Lemma sem_all_full : forall m,
  forall g e t, Hastype g e t -> forall th, DenotesEnv g th ->
  forall v, EvalsToN m (csubst th e) v -> isValue v -> Denotes (ctsubst th t) v.
Proof.
  intros m.
  apply (lt_wf_rect m (fun m => forall g e t, Hastype g e t ->
    forall th, DenotesEnv g th ->
    forall v, EvalsToN m (csubst th e) v -> isValue v -> Denotes (ctsubst th t) v)).
  intros m0 Hrec g e t Hty th Hd v HN Hv.
  exact (sem_inner_full m0 (fun m1 Hlt => Hrec m1 Hlt) g e t Hty th Hd v HN Hv).
Qed.

Lemma sem_evals_full : forall g e t, Hastype g e t ->
  forall th, DenotesEnv g th -> forall v,
  EvalsTo (csubst th e) v -> isValue v -> Denotes (ctsubst th t) v.
Proof.
  intros g e t Hty th Hd v HE Hv.
  destruct (EvalsTo_EvN (csubst th e) v HE) as [m Hm].
  exact (sem_all_full m g e t Hty th Hd v Hm Hv).
Qed.


Lemma PEvals_subst_rev0_nc : forall ps E V,
  isLC E -> EvalsTo E V -> isValue V ->
  PEvalsTrue (psubBV V ps) -> PEvalsTrue (psubBV E ps).
Proof.
  induction ps as [|p ps IH]; intros E V HE HEV HV HP; simpl in HP.
  - exact HP.
  - inversion HP as [|p0 ps0 Hhead Htail]; subst.
    apply PECons.
    + change (EvalsTo (subBV_at 0 E p) (Bc true)).
      change (EvalsTo (subBV_at 0 V p) (Bc true)) in Hhead.
      apply (sim_ctx_rev_nil p 0 E V (Bc true));
        [exact HE|exact HEV|exact HV|simpl; exact I|exact Hhead].
    + apply (IH E V); auto.
Qed.

Theorem logical_soundness : forall (e e':expr) (t:type) g b ps,
  Hastype g e (TRefn b ps) -> WFEnv g -> Terminating g e -> LEntails g (psubBV e ps).
Proof.
  intros e e' t g b ps Hty Hwf Hterm.
  unfold LEntails. intros th Hd.
  unfold Terminating in Hterm.
  destruct (Hterm th Hd) as [v [HEv Hv]].
  pose proof (sem_evals_full g e (TRefn b ps) Hty th Hd v HEv Hv) as HD.
  rewrite ctsubst_TRefn in HD.
  apply Denotes_refn in HD.
  rewrite cpsubst_psubBV0; [|exact (DenotesEnv_LCsubst g th Hd)].
  assert (Hlc_th : LCsubst th) by (exact (DenotesEnv_LCsubst g th Hd)).
  assert (Hlce : isLC e) by (apply (Hastype_isLC g e (TRefn b ps)); exact Hty).
  eapply PEvals_subst_rev0_nc;
    [|exact HEv|exact Hv|exact HD].
  exact (proj1 isLC_csubst_gen e th Hlc_th Hlce).
Qed.
