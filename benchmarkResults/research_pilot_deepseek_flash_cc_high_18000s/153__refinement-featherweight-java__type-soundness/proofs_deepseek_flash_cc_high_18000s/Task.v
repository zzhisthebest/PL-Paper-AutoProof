Require Import Definitions.Syntax Definitions.Semantics Definitions.Typing
  Definitions.CTSanity.

Require Import List.
Require Import Forall2.
Require Import ZArith.
Require Import Lia.
Require Import Lists.ListSet.
From Stdlib Require Import Program.Equality.
Require Import RFJ.Utils.Referable.
Require Import RFJ.Lists.replace.
Require Import Definitions.SubDenotation Definitions.FJTyping.

(* ============================================================ *)
(* Basic list and set helpers                                    *)
(* ============================================================ *)

Lemma list_max_ub : forall (l : [nat]) (x : nat), In x l -> x <= list_max l.
Proof.
  intros l x Hin.
  pose proof (proj1 (list_max_le l (list_max l)) (le_n (list_max l))) as H.
  apply (Forall_forall (fun k => k <= list_max l) l).
  - auto.
  - auto.
Qed.

Lemma fresh_not_in : forall (l : [nat]), ~ In (fresh l) l.
Proof.
  intros l Hin.
  pose proof (list_max_ub l (fresh l) Hin).
  unfold fresh in H. lia.
Qed.

Lemma fresh_not_in_add : forall (l : names) (x : vname),
    ~ Elem (fresh (names_add x l)) (names_add x l).
Proof.
  intros l x. apply fresh_not_in.
Qed.

Lemma fresh_not_in_add_l : forall (l : names) (x : vname),
    ~ Elem (fresh (names_add x l)) l.
Proof.
  intros l x H. apply (fresh_not_in_add l x).
  apply set_add_intro1. auto.
Qed.

Lemma fresh_not_in_add_ne : forall (l : names) (x y : vname),
    y = fresh (names_add x l) -> y <> x.
Proof.
  intros l x y ->. intro Hxy.
  apply (fresh_not_in_add l x).
  rewrite Hxy. apply set_add_intro2. auto.
Qed.

Lemma set_add_inv : forall (x y : vname) (s : names),
    Elem y (names_add x s) -> y = x \/ Elem y s.
Proof.
  intros. apply set_add_elim in H. auto.
Qed.

Lemma not_in_union_l : forall (x : vname) (a b : names),
    ~ Elem x (union a b) -> ~ Elem x a.
Proof.
  intros x a b H Ha. apply H. apply set_union_iff. left; auto.
Qed.

Lemma not_in_union_r : forall (x : vname) (a b : names),
    ~ Elem x (union a b) -> ~ Elem x b.
Proof.
  intros x a b H Hb. apply H. apply set_union_iff. right; auto.
Qed.

Lemma not_in_union : forall (x : vname) (a b : names),
    ~ Elem x a -> ~ Elem x b -> ~ Elem x (union a b).
Proof.
  intros x a b Ha Hb H. apply set_union_iff in H. destruct H; auto.
Qed.

Lemma in_union_l : forall (x : vname) (a b : names), Elem x a -> Elem x (union a b).
Proof. intros. apply set_union_iff. left; auto. Qed.

Lemma in_union_r : forall (x : vname) (a b : names), Elem x b -> Elem x (union a b).
Proof. intros. apply set_union_iff. right; auto. Qed.

Lemma not_in_singleton : forall (x y : vname), ~ Elem x (singleton y) -> x <> y.
Proof.
  intros x y H ->. apply H. unfold singleton.
  apply set_add_intro2. auto.
Qed.

Lemma in_singleton : forall (x y : vname), x = y -> Elem x (singleton y).
Proof.
  intros x y ->. unfold singleton. apply set_add_intro2. auto.
Qed.

Lemma not_in_empty : forall (x : vname), ~ Elem x (empty : names).
Proof.
  intros x H. unfold empty, empty_set, Elem in H. auto.
Qed.

(* ============================================================ *)
(* Erasure commutes with opening                                *)
(* ============================================================ *)

Lemma erase_openT : forall j y t, erase (openT_at j y t) = erase t.
Proof.
  intros j y t. destruct t as [b ps]. simpl. destruct b; reflexivity.
Qed.

Lemma erase_tsubFV : forall x v t, erase (tsubFV x v t) = erase t.
Proof. intros. destruct t as [b ps]. reflexivity. Qed.

Lemma erase_tsubBV : forall v t, erase (tsubBV v t) = erase t.
Proof. intros. destruct t as [b ps]. reflexivity. Qed.

Lemma erase_tsubBV_at : forall j v t, erase (tsubBV_at j v t) = erase t.
Proof. intros. destruct t as [b ps]. reflexivity. Qed.

Lemma erase_tsubBV_many : forall vs t, erase (tsubBV_many vs t) = erase t.
Proof.
  intros vs. induction vs as [|v vs IH]; intros t; simpl.
  - reflexivity.
  - rewrite IH. apply erase_tsubBV_at.
Qed.

Lemma erase_self : forall t e, erase (self t e) = erase t.
Proof. intros. destruct t as [b ps]. reflexivity. Qed.

(* ============================================================ *)
(* isValue and isLC list characterisations                       *)
(* ============================================================ *)

Lemma isValue_new_iff : forall c es, isValue (ExpNew c es) <-> Forall isValue es.
Proof.
  intros c es. revert c.
  induction es as [|e es IH]; intro c; simpl.
  - split; intros; constructor.
  - split.
    + intros [H1 H2]. constructor; auto. apply (proj1 (IH c)). exact H2.
    + intros H. split.
      * inversion H. auto.
      * apply (proj2 (IH c)). inversion H. auto.
Qed.

Lemma isLC_new_iff : forall j c es, isLC_at j (ExpNew c es) <-> Forall (isLC_at j) es.
Proof.
  intros j c es. revert j c.
  induction es as [|e es IH]; intros j c; simpl.
  - split; intros; constructor.
  - split.
    + intros [H1 H2]. constructor; auto. apply (proj1 (IH j c)). exact H2.
    + intros H. split.
      * inversion H. auto.
      * apply (proj2 (IH j c)). inversion H. auto.
Qed.

Lemma isValue_new_intro : forall c es, Forall isValue es -> isValue (ExpNew c es).
Proof. intros. apply isValue_new_iff. auto. Qed.

Lemma isLC_new_intro : forall j c es, Forall (isLC_at j) es -> isLC_at j (ExpNew c es).
Proof. intros. apply isLC_new_iff. auto. Qed.

Lemma isValue_not_Var : forall i, ~ isValue (BV i).
Proof. intros. simpl. auto. Qed.

Lemma isValue_not_FV : forall x, ~ isValue (FV x).
Proof. intros. simpl. auto. Qed.

Lemma isValue_not_UnOp : forall o e, ~ isValue (ExpUnOp o e).
Proof. intros. simpl. auto. Qed.

Lemma isValue_not_BinOp : forall o e1 e2, ~ isValue (ExpBinOp o e1 e2).
Proof. intros. simpl. auto. Qed.

Lemma isValue_not_Field : forall e f, ~ isValue (ExpFieldAccess e f).
Proof. intros. simpl. auto. Qed.

Lemma isValue_not_Invoc : forall e m e2, ~ isValue (ExpMethodInvoc e m e2).
Proof. intros. simpl. auto. Qed.

Lemma isValue_not_Let : forall e1 e2, ~ isValue (ExpLet e1 e2).
Proof. intros. simpl. auto. Qed.

Lemma isLC_subterm_UnOp : forall j o e, isLC_at j (ExpUnOp o e) -> isLC_at j e.
Proof. intros. simpl in H. auto. Qed.

Lemma isLC_subterm_BinOp_l : forall j o e1 e2, isLC_at j (ExpBinOp o e1 e2) -> isLC_at j e1.
Proof. intros. simpl in H. tauto. Qed.

Lemma isLC_subterm_BinOp_r : forall j o e1 e2, isLC_at j (ExpBinOp o e1 e2) -> isLC_at j e2.
Proof. intros. simpl in H. tauto. Qed.

Lemma isLC_subterm_Invoc_l : forall j e1 m e2, isLC_at j (ExpMethodInvoc e1 m e2) -> isLC_at j e1.
Proof. intros. simpl in H. tauto. Qed.

Lemma isLC_subterm_Invoc_r : forall j e1 m e2, isLC_at j (ExpMethodInvoc e1 m e2) -> isLC_at j e2.
Proof. intros. simpl in H. tauto. Qed.

Lemma isLC_subterm_Field : forall j e f, isLC_at j (ExpFieldAccess e f) -> isLC_at j e.
Proof. intros. simpl in H. auto. Qed.

Lemma isLC_subterm_Let_l : forall j e1 e2, isLC_at j (ExpLet e1 e2) -> isLC_at j e1.
Proof. intros. simpl in H. tauto. Qed.

Lemma isLC_subterm_Let_r : forall j e1 e2, isLC_at j (ExpLet e1 e2) -> isLC_at (j+1) e2.
Proof. intros. simpl in H. tauto. Qed.

Lemma isLC_subterm_New_in : forall j c es e, isLC_at j (ExpNew c es) -> In e es -> isLC_at j e.
Proof.
  intros j c es e H Hin.
  apply isLC_new_iff in H.
  apply Forall_forall with (x:=e) in H; auto.
Qed.

(* ============================================================ *)
(* nth_error and replace                                         *)
(* ============================================================ *)

Lemma nth_error_app_prefix : forall (A : Type) (l l' : [A]) i x,
    nth_error l i = Some x -> nth_error (l ++ l') i = Some x.
Proof.
  intros A l l' i x H.
  rewrite nth_error_app1; auto.
  apply nth_error_Some. rewrite H. discriminate.
Qed.

Lemma length_replace : forall (A : Type) (l : [A]) i (v : A),
    length (replace l i v) = length l.
Proof.
  intros A l. induction l as [|a l IH]; intros i v; destruct i; simpl; auto.
Qed.

Lemma nth_error_replace_same : forall (A : Type) (l : [A]) i (v : A),
    i < length l -> nth_error (replace l i v) i = Some v.
Proof.
  intros A l. induction l as [|a l IH]; intros i v Hlt; destruct i; simpl in *.
  - lia.
  - lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma nth_error_replace_other : forall (A : Type) (l : [A]) i j (v : A),
    j <> i -> nth_error (replace l i v) j = nth_error l j.
Proof.
  intros A l. induction l as [|a l IH]; intros i j v Hne.
  - destruct i, j; reflexivity.
  - destruct i as [|i], j as [|j]; simpl in *.
    + exfalso. apply Hne. reflexivity.
    + reflexivity.
    + reflexivity.
    + apply IH. lia.
Qed.

Lemma In_nth_error : forall (A : Type) (l : [A]) (x : A),
    In x l -> exists i, nth_error l i = Some x.
Proof.
  intros A l. induction l as [|a l IH]; intros x Hin.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + exists 0. simpl. reflexivity.
    + destruct (IH x Hin) as [i Hi]. exists (S i). simpl. auto.
Qed.

(* ============================================================ *)
(* Forall2 lemmas                                                *)
(* ============================================================ *)

Lemma Forall2_nth_error_l : forall (A B : Type) (R : A -> B -> Prop) l1 l2 i x,
    Forall2 R l1 l2 -> nth_error l1 i = Some x ->
    exists y, nth_error l2 i = Some y /\ R x y.
Proof.
  intros A B R l1. induction l1 as [|a l1 IH]; intros l2 i x HF Hn.
  - destruct l2 as [|b l2]; [destruct i; simpl in Hn; discriminate | dependent destruction HF].
  - destruct l2 as [|b l2]; [dependent destruction HF |].
    destruct i; simpl in *.
    + injection Hn as ->. dependent destruction HF. exists b. split; auto.
    + dependent destruction HF. eapply IH; eauto.
Qed.

Lemma Forall2_nth_error_r : forall (A B : Type) (R : A -> B -> Prop) l1 l2 i y,
    Forall2 R l1 l2 -> nth_error l2 i = Some y ->
    exists x, nth_error l1 i = Some x /\ R x y.
Proof.
  intros A B R l1. induction l1 as [|a l1 IH]; intros l2 i y HF Hn.
  - destruct l2 as [|b l2]; [destruct i; simpl in Hn; discriminate | dependent destruction HF].
  - destruct l2 as [|b l2]; [dependent destruction HF |].
    destruct i; simpl in *.
    + injection Hn as ->. dependent destruction HF. exists a. split; auto.
    + dependent destruction HF. eapply IH; eauto.
Qed.

Lemma Forall2_nth : forall (A B : Type) (R : A -> B -> Prop) l1 l2,
    Forall2 R l1 l2 ->
    forall i x y, nth_error l1 i = Some x -> nth_error l2 i = Some y -> R x y.
Proof.
  intros A B R l1. induction l1 as [|a l1 IH]; intros l2 HF i x y H1 H2.
  - destruct l2 as [|b l2]; [destruct i; simpl in H1; discriminate | dependent destruction HF].
  - destruct l2 as [|b l2]; [dependent destruction HF |].
    destruct i; simpl in *.
    + injection H1 as ->. injection H2 as ->. dependent destruction HF. auto.
    + dependent destruction HF. eapply IH; eauto.
Qed.

Lemma Forall2_Forall_l : forall (A B : Type) (R : A -> B -> Prop) (P : A -> Prop) l1 l2,
    Forall2 R l1 l2 -> (forall x y, R x y -> P x) -> Forall P l1.
Proof.
  intros A B R P l1. induction l1 as [|a l1 IH]; intros l2 HF HP.
  - destruct l2 as [|b l2]; [constructor | dependent destruction HF].
  - destruct l2 as [|b l2]; [dependent destruction HF |].
    dependent destruction HF. constructor.
    + apply HP with (y:=b). auto.
    + eapply IH; eauto.
Qed.

Lemma Forall2_Forall_r : forall (A B : Type) (R : A -> B -> Prop) (P : B -> Prop) l1 l2,
    Forall2 R l1 l2 -> (forall x y, R x y -> P y) -> Forall P l2.
Proof.
  intros A B R P l1. induction l1 as [|a l1 IH]; intros l2 HF HP.
  - destruct l2 as [|b l2]; [constructor | dependent destruction HF].
  - destruct l2 as [|b l2]; [dependent destruction HF |].
    dependent destruction HF. constructor.
    + apply HP with (x:=a). auto.
    + eapply IH; eauto.
Qed.

Lemma Forall2_map_l : forall (A A' B : Type) (R : A -> B -> Prop) (R' : A' -> B -> Prop)
    (f : A -> A') l1 l2,
    Forall2 R l1 l2 ->
    (forall x y, R x y -> R' (f x) y) ->
    Forall2 R' (map f l1) l2.
Proof.
  intros A A' B R R' f l1. induction l1 as [|a l1 IH]; intros l2 HF Himp.
  - destruct l2 as [|b l2]; [simpl; constructor | dependent destruction HF].
  - destruct l2 as [|b l2]; [dependent destruction HF |].
    dependent destruction HF. simpl. constructor.
    + apply Himp; auto.
    + eapply IH; eauto.
Qed.

Lemma Forall2_replace_l : forall (A B : Type) (R : A -> B -> Prop) l1 l2 i x y x',
    Forall2 R l1 l2 -> nth_error l1 i = Some x -> nth_error l2 i = Some y ->
    R x' y -> Forall2 R (replace l1 i x') l2.
Proof.
  intros A B R l1. induction l1 as [|a l1 IH]; intros l2 i x y x' HF H1 H2 HR.
  - destruct i; simpl in H1; discriminate.
  - destruct l2 as [|b l2]; [dependent destruction HF |].
    destruct i; simpl in *.
    + injection H1 as ->. injection H2 as ->. dependent destruction HF.
      simpl. constructor; auto.
    + dependent destruction HF. simpl. constructor; auto. eapply IH; eauto.
Qed.

Lemma Forall2_map_subst_l : forall (A B : Type) (R : A -> B -> Prop) (R' : A -> B -> Prop)
    (f : A -> A) l1 l2,
    Forall2 R l1 l2 ->
    (forall x y, R x y -> R' (f x) y) ->
    Forall2 R' (map f l1) l2.
Proof. intros. eapply Forall2_map_l; eauto. Qed.

(* ============================================================ *)
(* find lemmas                                                   *)
(* ============================================================ *)

Lemma find_nil : forall (A : Type) (R : Referable A) k, @find A R k nil = None.
Proof. intros. simpl. reflexivity. Qed.

Lemma find_cons : forall (A : Type) (R : Referable A) k x xs,
    @find A R k (x :: xs) = if PeanoNat.Nat.eqb k (ref x) then Some x else @find A R k xs.
Proof. intros. simpl. reflexivity. Qed.

Lemma find_some_in : forall (A : Type) (R : Referable A) k l x,
    @find A R k l = Some x -> In x l.
Proof.
  intros A R k l. induction l as [|a l IH]; intros x H.
  - simpl in H. discriminate.
  - rewrite find_cons in H.
    destruct (PeanoNat.Nat.eqb k (ref a)) eqn:E.
    + injection H as ->. left; auto.
    + right. eapply IH; eauto.
Qed.

Lemma find_ref_eq : forall (A : Type) (R : Referable A) k l x,
    @find A R k l = Some x -> ref x = k.
Proof.
  intros A R k l. induction l as [|a l IH]; intros x H.
  - simpl in H. discriminate.
  - rewrite find_cons in H.
    destruct (PeanoNat.Nat.eqb k (ref a)) eqn:E.
    + injection H as Hax. subst x. apply PeanoNat.Nat.eqb_eq in E. rewrite E. reflexivity.
    + eapply IH; eauto.
Qed.

Lemma find_not_found : forall (A : Type) (R : Referable A) k l,
    @find A R k l = None -> forall x, In x l -> ref x <> k.
Proof.
  intros A R k l. induction l as [|a l IH]; intros H x Hin.
  - destruct Hin.
  - rewrite find_cons in H.
    destruct (PeanoNat.Nat.eqb k (ref a)) eqn:E.
    + discriminate.
    + destruct Hin as [-> | Hin].
      * intro Hk. apply PeanoNat.Nat.eqb_neq in E. apply E. auto.
      * eapply IH; eauto.
Qed.

Lemma find_det : forall (A : Type) (R : Referable A) k l x y,
    NoDup (refs l) -> @find A R k l = Some x -> @find A R k l = Some y -> x = y.
Proof.
  intros A R k l. induction l as [|a l IH]; intros x y Hnd H1 H2.
  - simpl in H1. discriminate.
  - rewrite find_cons in H1, H2.
    destruct (PeanoNat.Nat.eqb k (ref a)) eqn:E.
    + injection H1 as ->. injection H2 as ->. reflexivity.
    + apply IH; auto.
      unfold refs in Hnd. simpl in Hnd. inversion Hnd; auto.
Qed.

Lemma Forall_find : forall (A : Type) (R : Referable A) (P : A -> Prop) k l x,
    Forall P l -> @find A R k l = Some x -> P x.
Proof.
  intros A R P k l. induction l as [|a l IH]; intros x HF H.
  - simpl in H. discriminate.
  - rewrite find_cons in H.
    inversion HF; subst.
    destruct (PeanoNat.Nat.eqb k (ref a)) eqn:E.
    + injection H as ->. auto.
    + eapply IH; eauto.
Qed.

Lemma find_In_iff : forall (A : Type) (R : Referable A) k l x,
    @find A R k l = Some x -> In x l.
Proof. intros. eapply find_some_in; eauto. Qed.

(* ============================================================ *)
(* FJ subtype basics                                             *)
(* ============================================================ *)

Lemma SubClass_refl : forall b, SubClass b b.
Proof. intro b. apply SubCRefl. Qed.

Lemma SubClass_trans : forall b1 b2 b3, SubClass b1 b2 -> SubClass b2 b3 -> SubClass b1 b3.
Proof. intros. eapply SubCTrans; eauto. Qed.

Lemma FJSubtype_refl : forall t, FJSubtype t t.
Proof.
  intro t. destruct t as [| | | n].
  - apply SubBAny.
  - apply SubBBool.
  - apply SubBInt.
  - destruct n; apply SubBClass; apply SubCRefl.
Qed.

Lemma FJSubtype_trans : forall s t u, FJSubtype s t -> FJSubtype t u -> FJSubtype s u.
Proof.
  intros s t u H1. revert u. induction H1; intros u H2.
  - dependent destruction H2. apply SubBAny.
  - dependent destruction H2; [apply SubBAny | apply SubBInt].
  - dependent destruction H2; [apply SubBAny | apply SubBBool].
  - dependent destruction H2.
    + apply SubBAny.
    + eapply SubBClass. eapply SubCTrans; eauto.
Qed.

Lemma FJSubtype_bool_inv : forall t, FJSubtype t TBool -> t = TBool.
Proof.
  intros t H. dependent destruction H; auto.
Qed.

Lemma FJSubtype_int_inv : forall t, FJSubtype t TInt -> t = TInt.
Proof.
  intros t H. dependent destruction H; auto.
Qed.

Lemma FJSubtype_nom_inv : forall t (X : nomtype),
    FJSubtype t (TNom X) -> exists Y, t = TNom Y /\ SubClass Y X.
Proof.
  intros t X H. dependent destruction H.
  exists C. split; auto.
Qed.

Lemma SubClass_class_target : forall (Y : nomtype) (C : ClassName),
    SubClass Y (TClass C) -> exists C', Y = TClass C'.
Proof.
  intros Y C H. remember (TClass C) as T eqn:E. revert C E.
  induction H as [b | b1 b2 b3 H12 IH12 H23 IH23 | C0 D Is fs n1 K ms n2 Hf | C0 D Is I fs n1 K ms n2 i Hf Hi]; intros C0' E.
  - inversion E; subst. exists C0'; reflexivity.
  - inversion E; subst.
    destruct (IH23 C0' eq_refl) as [C' HC']. subst b2.
    destruct (IH12 C' eq_refl) as [C'' HC'']. subst b1. exists C''; reflexivity.
  - inversion E; subst. exists C0; reflexivity.
  - inversion E.
Qed.

Lemma FJSubtype_class_inv : forall t C,
    FJSubtype t (TNom (TClass C)) -> exists C', t = TNom (TClass C') /\ SubClass (TClass C') (TClass C).
Proof.
  intros t C H. apply FJSubtype_nom_inv in H.
  destruct H as [Y [HY Hc]]. subst t.
  destruct (SubClass_class_target Y C Hc) as [C' E]. subst Y.
  exists C'. split; auto.
Qed.

(* ============================================================ *)
(* Erasure of typing                                             *)
(* ============================================================ *)

Lemma bound_in_erase : forall x t g, bound_in x t g -> bound_inF x (erase t) (erase_env g).
Proof.
  intros x t g H. induction g as [|y ty g IH]; simpl in *.
  - destruct H.
  - destruct H as [[-> ->] | H].
    + left. split; auto.
    + right. auto.
Qed.

Lemma Subtype_erase : forall g s t, Subtype g s t -> FJSubtype (erase s) (erase t).
Proof.
  intros g s t H. induction H.
  - simpl. auto.
Qed.

Lemma Forall2_Subtype_erase : forall g Ts Us,
    Forall2 (Subtype g) Ts Us ->
    Forall2 (fun t u => FJSubtype (erase t) (erase u)) Ts Us.
Proof.
  intros g Ts Us H. induction H as [|t u Ts Us Hs Hrest IH].
  - constructor.
  - constructor.
    + apply Subtype_erase with (g:=g). exact Hs.
    + exact IH.
Qed.

Lemma Forall2_map_inv : forall (A B C : Type) (R : A -> C -> Prop) (f : B -> C) l1 l2,
    Forall2 (fun a c => R a c) l1 (map f l2) ->
    Forall2 (fun a b => R a (f b)) l1 l2.
Proof.
  intros A B C R f l1. induction l1 as [|a l1 IH]; intros l2 H.
  - destruct l2; simpl in H; dependent destruction H. constructor.
  - destruct l2 as [|b l2]; simpl in H; [dependent destruction H |].
    dependent destruction H. constructor; auto.
Qed.

Lemma Forall2_hasFJ_aux : forall g es Ts,
    Forall (fun ei => forall Ti, Hastype g ei Ti -> HasFJtype (erase_env g) ei (erase Ti)) es ->
    Forall2 (Hastype g) es Ts ->
    forall Us, Forall2 (fun t u => FJSubtype (erase t) (erase u)) Ts Us ->
    Forall2 (HasFJtype (erase_env g)) es (map erase Us).
Proof.
  intros g es Ts Hf H2 Us. revert Us.
  induction H2 as [|e t es Ts He Hrest IH]; intros Us H2.
  - destruct Us as [|u Us]; simpl in H2; dependent destruction H2. constructor.
  - destruct Us as [|u Us]; simpl in H2; [dependent destruction H2 |].
    dependent destruction H2.
    inversion Hf as [|? ? Hhead Htail]; subst.
    simpl. constructor.
    + eapply FTSub.
      * apply Hhead. exact He.
      * exact H.
    + eapply IH; eauto.
Qed.


(* ============================================================ *)
(* Expression size                                               *)
(* ============================================================ *)

Fixpoint expr_size (e : expr) : nat :=
  match e with
  | Bc _ => 1
  | Ic _ => 1
  | BV _ => 1
  | FV _ => 1
  | ExpUnOp _ e1 => S (expr_size e1)
  | ExpBinOp _ e1 e2 => S (expr_size e1 + expr_size e2)
  | ExpMethodInvoc e1 _ e2 => S (expr_size e1 + expr_size e2)
  | ExpFieldAccess e1 _ => S (expr_size e1)
  | ExpNew _ es => S ((fix f (es : [expr]) : nat :=
                         match es with
                         | nil => 0
                         | e :: l => expr_size e + f l
                         end) es)
  | ExpLet e1 e2 => S (expr_size e1 + expr_size e2)
  end.

Definition list_expr_size (es : [expr]) : nat :=
  (fix f (es : [expr]) : nat :=
     match es with
     | nil => 0
     | e :: l => expr_size e + f l
     end) es.

Lemma list_expr_size_nil : list_expr_size nil = 0.
Proof. reflexivity. Qed.

Lemma list_expr_size_cons : forall (a : expr) es,
    list_expr_size (a :: es) = expr_size a + list_expr_size es.
Proof. intros. unfold list_expr_size. simpl. reflexivity. Qed.

Lemma list_expr_size_eq : forall es,
    (fix f (es : [expr]) : nat :=
       match es with
       | nil => 0
       | e :: l => expr_size e + f l
       end) es = list_expr_size es.
Proof.
  intros es. induction es as [|e es IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma expr_size_new : forall c es, expr_size (ExpNew c es) = S (list_expr_size es).
Proof. intros. simpl. rewrite list_expr_size_eq. reflexivity. Qed.

Lemma expr_size_pos : forall e, 0 < expr_size e.
Proof. intros e. destruct e; simpl; lia. Qed.

Lemma list_expr_size_pos_le : forall es e, In e es -> expr_size e <= list_expr_size es.
Proof.
  intros es. induction es as [|a es IH]; intros e Hin.
  - destruct Hin.
  - destruct Hin as [-> | Hin]; simpl.
    + lia.
    + pose proof (IH e Hin). lia.
Qed.

Lemma expr_size_new_In : forall (c : ClassName) (es : [expr]) e,
    In e es -> expr_size e < expr_size (ExpNew c es).
Proof.
  intros. rewrite expr_size_new. pose proof (list_expr_size_pos_le es e H). lia.
Qed.

Lemma expr_size_UnOp : forall o e, expr_size e < expr_size (ExpUnOp o e).
Proof. intros. simpl. lia. Qed.

Lemma expr_size_BinOp_l : forall o e1 e2, expr_size e1 < expr_size (ExpBinOp o e1 e2).
Proof. intros. simpl. lia. Qed.

Lemma expr_size_BinOp_r : forall o e1 e2, expr_size e2 < expr_size (ExpBinOp o e1 e2).
Proof. intros. simpl. lia. Qed.

Lemma expr_size_Invoc_l : forall e1 m e2, expr_size e1 < expr_size (ExpMethodInvoc e1 m e2).
Proof. intros. simpl. lia. Qed.

Lemma expr_size_Invoc_r : forall e1 m e2, expr_size e2 < expr_size (ExpMethodInvoc e1 m e2).
Proof. intros. simpl. lia. Qed.

Lemma expr_size_Field : forall e f, expr_size e < expr_size (ExpFieldAccess e f).
Proof. intros. simpl. lia. Qed.

Lemma expr_size_Let_l : forall e1 e2, expr_size e1 < expr_size (ExpLet e1 e2).
Proof. intros. simpl. lia. Qed.

Lemma expr_size_Let_r : forall e1 e2, expr_size e2 < expr_size (ExpLet e1 e2).
Proof. intros. simpl. lia. Qed.

(* named list-opening function matching the internal fix *)
Fixpoint open_list_at (j : index) (y : vname) (es : [expr]) : [expr] :=
  match es with
  | nil => nil
  | e :: es' => open_at j y e :: open_list_at j y es'
  end.

Lemma open_list_at_eq : forall j y es,
    (fix f (es : [expr]) : [expr] :=
       match es with
       | nil => nil
       | e :: l => open_at j y e :: f l
       end) es = open_list_at j y es.
Proof.
  intros j y es. induction es as [|e es IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma open_at_new : forall j y c es,
    open_at j y (ExpNew c es) = ExpNew c (open_list_at j y es).
Proof.
  intros. simpl. rewrite open_list_at_eq. reflexivity.
Qed.

Lemma size_open_both : forall n,
    (forall e, expr_size e <= n -> forall j y, expr_size (open_at j y e) = expr_size e) /\
    (forall es, list_expr_size es <= n -> forall j y,
        list_expr_size (open_list_at j y es) = list_expr_size es).
Proof.
  induction n as [|n IH].
  - split.
    + intros e Hn j y. pose proof (expr_size_pos e); lia.
    + intros es Hn j y. destruct es as [|a es].
      * simpl. reflexivity.
      * pose proof (expr_size_pos a). rewrite list_expr_size_cons in Hn. lia.
  - destruct IH as [IHe IHl].
    assert (Hexp : forall e, expr_size e <= S n -> forall j y,
               expr_size (open_at j y e) = expr_size e).
    { intros e He j y. destruct e as [b | z | iv | x | o e0 | o e0 e1 | e0 f | e0 m e1 | c es | e0 e1].
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. destruct (PeanoNat.Nat.eqb j iv); reflexivity.
      * simpl. reflexivity.
      * simpl in *. f_equal. apply IHe. lia.
      * simpl in *. f_equal. rewrite (IHe e0); [| lia]. rewrite (IHe e1); [| lia]. reflexivity.
      * simpl in *. f_equal. apply IHe. lia.
      * simpl in *. f_equal. rewrite (IHe e0); [| lia]. rewrite (IHe e1); [| lia]. reflexivity.
      * (* ExpNew *)
        rewrite open_at_new, expr_size_new.
        assert (Hl : list_expr_size es <= n) by (rewrite expr_size_new in He; lia).
        rewrite (IHl es Hl). reflexivity.
      * simpl in *. f_equal. rewrite (IHe e0); [| lia]. rewrite (IHe e1); [| lia]. reflexivity. }
    assert (Hlist : forall es, list_expr_size es <= S n -> forall j y,
               list_expr_size (open_list_at j y es) = list_expr_size es).
    { intros es Hle j y. destruct es as [|a es].
      * simpl. reflexivity.
      * assert (Htail : list_expr_size es <= n) by (rewrite list_expr_size_cons in Hle; pose proof (expr_size_pos a); lia).
        simpl. rewrite (IHl es Htail). f_equal.
        apply Hexp.
        pose proof (list_expr_size_pos_le (a::es) a (or_introl eq_refl)).
        rewrite list_expr_size_cons in Hle. lia. }
    split; auto.
Qed.

Lemma expr_size_open_at : forall e j y, expr_size (open_at j y e) = expr_size e.
Proof. intros. apply (proj1 (size_open_both (expr_size e))); lia. Qed.

Lemma list_expr_size_open_list : forall n j y es,
    list_expr_size es <= n ->
    list_expr_size (open_list_at j y es) = list_expr_size es.
Proof. intros. apply (proj2 (size_open_both n)); auto. Qed.

(* ============================================================ *)
(* Erasure of typing (using size induction)                      *)
(* ============================================================ *)

Lemma Forall2_subst_subtype_erase : forall g Ts Us v,
    Forall2 (Subtype g) Ts (map (tsubBV v) Us) ->
    Forall2 (fun t u => FJSubtype (erase t) (erase u)) Ts Us.
Proof.
  intros g Ts Us v H. apply Forall2_map_inv with (f := tsubBV v) in H.
  induction H as [|t u Ts Us Hs Hrest IH].
  - constructor.
  - constructor.
    + apply Subtype_erase with (g:=g) in Hs. rewrite erase_tsubBV in Hs. exact Hs.
    + exact IH.
Qed.

Lemma Hastype_erase_aux : forall n e, expr_size e <= n ->
    forall g t, Hastype g e t -> HasFJtype (erase_env g) e (erase t).
Proof.
  induction n as [|n IH]; intros e Hn g t Hty.
  - pose proof (expr_size_pos e); lia.
  - induction Hty as
      [g b
      | g z
      | g e0 op t0 Ht0 IHt0 St0 lc0
      | g e1 e2 op t1 t2 H1 IH1 S1 H2 IH2 S2 lc1 lc2
      | g x t0 Hb Hwf
      | g e1 e2 m t1 t2 rt C ps ps0 H1 IH1 mt S1 H2 IH2 S2 lc2 lc1
      | g e1 e2 m t1 t2 rt I ps ps0 H1 IH1 mt S1 H2 IH2 S2 lc2 lc1
      | g e0 f C Fs i fi ps0 lc0 H0 IH0 Rf nth refeq
      | g es Ts C Fs Us fs Usmap fsmap Flc Rf HF2 HS2
      | g ex b e0 b' nms Hwf Hx IHx Hbody
      | g e0 s t0 H0 IH0 Hwf St
      ].
    + (* TBC *) simpl. apply FTBC.
    + (* TIC *) simpl. apply FTIC.
    + (* TUnOP *)
      rewrite erase_tsubBV.
      eapply FTUnOP.
      eapply FTSub with (s := erase t0).
      * eapply IH with (e := e0) (g := g) (t := t0); [| exact Ht0].
        pose proof (expr_size_UnOp op e0). lia.
      * exact (Subtype_erase g _ _ St0).
    + (* TBinOP *)
      rewrite erase_tsubBV_at, erase_tsubBV.
      eapply FTBinOP.
      * eapply FTSub with (s := erase t1).
        -- eapply IH with (e := e1) (g := g) (t := t1); [| exact H1].
           pose proof (expr_size_BinOp_l op e1 e2). lia.
        -- exact (Subtype_erase g _ _ S1).
      * eapply FTSub with (s := erase t2).
        -- eapply IH with (e := e2) (g := g) (t := t2); [| exact H2].
           pose proof (expr_size_BinOp_r op e1 e2). lia.
        -- apply Subtype_erase with (g:=g) in S2. rewrite erase_tsubBV in S2. exact S2.
    + (* TVar *)
      rewrite erase_self.
      apply FTVar. apply bound_in_erase. exact Hb.
    + (* TInvok *)
      rewrite erase_self, erase_tsubBV_at, erase_tsubBV.
      eapply FTInvok.
      * eapply IH with (e := e1) (g := g) (t := TRefn (TNom (TClass C)) ps0); [| exact H1].
        pose proof (expr_size_Invoc_l e1 m e2). lia.
      * exact mt.
      * eapply FTSub with (s := erase t2).
        -- eapply IH with (e := e2) (g := g) (t := t2); [| exact H2].
           pose proof (expr_size_Invoc_r e1 m e2). lia.
        -- apply Subtype_erase with (g:=g) in S2. rewrite erase_tsubBV in S2. exact S2.
    + (* TInvokI *)
      rewrite erase_self, erase_tsubBV_at, erase_tsubBV.
      eapply FTInvokI.
      * eapply IH with (e := e1) (g := g) (t := TRefn (TNom (TInterface I)) ps0); [| exact H1].
        pose proof (expr_size_Invoc_l e1 m e2). lia.
      * exact mt.
      * eapply FTSub.
        -- eapply IH; [| exact H2].
           pose proof (expr_size_Invoc_r e1 m e2). lia.
        -- apply Subtype_erase with (g:=g) in S2. rewrite erase_tsubBV in S2. exact S2.
    + (* TField *)
      rewrite erase_self, erase_tsubBV.
      eapply FTField.
      * eapply IH with (e := e0) (g := g) (t := TRefn (TNom (TClass C)) ps0); [| exact H0].
        pose proof (expr_size_Field e0 f). lia.
      * exact Rf.
      * exact nth.
      * exact refeq.
      * reflexivity.
    + (* TNew *)
      rewrite erase_self.
      eapply FTNew with (Fs := Fs) (Us := map erase Us) (fs := fs).
      * rewrite Usmap. reflexivity.
      * rewrite fsmap. reflexivity.
      * exact Rf.
      * eapply Forall2_hasFJ_aux with (Us := Us).
        -- apply Forall_forall. intros ei Hin Ti Hi.
           eapply IH with (e := ei) (g := g) (t := Ti); [| exact Hi].
           pose proof (expr_size_new_In C es ei Hin).
           assert (Hpos : 0 < expr_size (ExpNew C es)) by apply expr_size_pos.
           lia.
        -- exact HF2.
        -- eapply Forall2_subst_subtype_erase. exact HS2.
    + (* TLet *)
      rewrite erase_self.
      eapply FTLet.
      * eapply IH with (e := ex) (g := g) (t := b); [| exact Hx].
        pose proof (expr_size_Let_l ex e0). lia.
      * intros y Hy.
        specialize (Hbody y Hy).
        assert (Hsz : expr_size (unbind y e0) <= n).
        { change (expr_size (open_at 0 y e0) <= n). rewrite expr_size_open_at.
          pose proof (expr_size_Let_r ex e0). lia. }
        pose proof (IH (unbind y e0) Hsz (Cons y b g) (unbindT y b') Hbody) as Hr.
        change (HasFJtype (erase_env (Cons y b g)) (unbind y e0) (erase (openT_at 0 y b'))) in Hr.
        rewrite erase_openT in Hr.
        change (HasFJtype (FCons y (erase b) (erase_env g)) (unbind y e0) (erase b')).
        exact Hr.
    + (* TSub *)
      eapply FTSub with (s := erase s).
      * apply IH0. exact Hn.
      * exact (Subtype_erase g _ _ St).
Qed.

Lemma Hastype_erase : forall g e t, Hastype g e t -> HasFJtype (erase_env g) e (erase t).
Proof. intros. eapply Hastype_erase_aux. - apply le_n. - exact H. Qed.

(* ============================================================ *)
(* Substitution / opening commutation                            *)
(* ============================================================ *)

Fixpoint subFV_list (x : vname) (v : expr) (es : [expr]) : [expr] :=
  match es with
  | nil => nil
  | e :: es' => subFV x v e :: subFV_list x v es'
  end.

Fixpoint subBV_list_at (j : index) (v : expr) (es : [expr]) : [expr] :=
  match es with
  | nil => nil
  | e :: es' => subBV_at j v e :: subBV_list_at j v es'
  end.

Lemma subFV_list_eq : forall x v es,
    (fix f (es : [expr]) : [expr] :=
       match es with
       | nil => nil
       | e :: l => subFV x v e :: f l
       end) es = subFV_list x v es.
Proof.
  intros x v es. induction es as [|e es IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma subFV_new : forall x v c es,
    subFV x v (ExpNew c es) = ExpNew c (subFV_list x v es).
Proof. intros. simpl. rewrite subFV_list_eq. reflexivity. Qed.

Lemma subBV_list_eq : forall j v es,
    (fix f (es : [expr]) : [expr] :=
       match es with
       | nil => nil
       | e :: l => subBV_at j v e :: f l
       end) es = subBV_list_at j v es.
Proof.
  intros j v es. induction es as [|e es IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma subBV_new : forall j v c es,
    subBV_at j v (ExpNew c es) = ExpNew c (subBV_list_at j v es).
Proof. intros. simpl. rewrite subBV_list_eq. reflexivity. Qed.

Lemma subFV_list_map : forall x v es, subFV_list x v es = map (subFV x v) es.
Proof.
  intros x v es. induction es as [|e es IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma subFV_open_comm_both : forall n,
    (forall e, expr_size e <= n -> forall x y v j, x <> y ->
        (forall j y, open_at j y v = v) ->
        subFV x v (open_at j y e) = open_at j y (subFV x v e)) /\
    (forall es, list_expr_size es <= n -> forall x y v j, x <> y ->
        (forall j y, open_at j y v = v) ->
        subFV_list x v (open_list_at j y es) = open_list_at j y (subFV_list x v es)).
Proof.
  induction n as [|n IH].
  - split.
    + intros e He. pose proof (expr_size_pos e); lia.
    + intros es He x y v j Hxy Hv. destruct es as [|a es].
      * simpl. reflexivity.
      * pose proof (expr_size_pos a). rewrite list_expr_size_cons in He. lia.
  - destruct IH as [IHe IHl].
    assert (Hexp : forall e, expr_size e <= S n -> forall x y v j, x <> y ->
               (forall j y, open_at j y v = v) ->
               subFV x v (open_at j y e) = open_at j y (subFV x v e)).
    { intros e He x y v j Hxy Hv.
      destruct e as [b | z | iv | xx | o e0 | o e0 e1 | e0 f | e0 m e1 | c es | e0 e1].
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. destruct (PeanoNat.Nat.eqb j iv) eqn:Ej.
        -- destruct (PeanoNat.Nat.eqb x y) eqn:Ex; simpl.
           ++ exfalso. apply Hxy. apply PeanoNat.Nat.eqb_eq in Ex. auto.
           ++ rewrite Ex. reflexivity.
        -- destruct (PeanoNat.Nat.eqb x y) eqn:Ex; simpl; reflexivity.
      * simpl. destruct (PeanoNat.Nat.eqb x xx); simpl.
        -- symmetry. apply Hv.
        -- reflexivity.
      * simpl. f_equal. apply IHe; auto. pose proof (expr_size_UnOp o e0). lia.
      * simpl. f_equal.
        -- apply IHe; auto. pose proof (expr_size_BinOp_l o e0 e1). lia.
        -- apply IHe; auto. pose proof (expr_size_BinOp_r o e0 e1). lia.
      * simpl. f_equal. apply IHe; auto. pose proof (expr_size_Field e0 f). lia.
      * simpl. f_equal.
        -- apply IHe; auto. pose proof (expr_size_Invoc_l e0 m e1). lia.
        -- apply IHe; auto. pose proof (expr_size_Invoc_r e0 m e1). lia.
      * (* ExpNew *)
        rewrite open_at_new, subFV_new, subFV_new, open_at_new.
        f_equal. apply IHl; auto.
        rewrite expr_size_new in He. lia.
      * simpl. f_equal.
        -- apply IHe; auto. pose proof (expr_size_Let_l e0 e1). lia.
        -- apply IHe; auto. pose proof (expr_size_Let_r e0 e1). lia. }
    assert (Hlist : forall es, list_expr_size es <= S n -> forall x y v j, x <> y ->
               (forall j y, open_at j y v = v) ->
               subFV_list x v (open_list_at j y es) = open_list_at j y (subFV_list x v es)).
    { intros es He x y v j Hxy Hv. destruct es as [|a es].
      * simpl. reflexivity.
      * assert (Ha : expr_size a <= S n)
          by (pose proof (list_expr_size_pos_le (a::es) a (or_introl eq_refl)); rewrite list_expr_size_cons in He; lia).
        assert (Htail : list_expr_size es <= n)
          by (rewrite list_expr_size_cons in He; pose proof (expr_size_pos a); lia).
        simpl. rewrite (Hexp a Ha x y v j Hxy Hv). rewrite (IHl es Htail x y v j Hxy Hv). reflexivity. }
    split; auto.
Qed.

Lemma subFV_open_comm : forall x y v j e, x <> y ->
    (forall j y, open_at j y v = v) ->
    subFV x v (open_at j y e) = open_at j y (subFV x v e).
Proof. intros. apply (proj1 (subFV_open_comm_both (expr_size e))); auto; lia. Qed.

Lemma isValue_open_at_both : forall n,
    (forall e, expr_size e <= n -> isValue e -> forall j y, open_at j y e = e) /\
    (forall es, list_expr_size es <= n -> Forall isValue es -> forall j y,
        open_list_at j y es = es).
Proof.
  induction n as [|n IH].
  - split.
    + intros e He Hv. pose proof (expr_size_pos e); lia.
    + intros es He Hf. destruct es as [|a es].
      * simpl. reflexivity.
      * inversion Hf. pose proof (expr_size_pos a).
        simpl in He. lia.
  - destruct IH as [IHe IHl].
    assert (Hexp : forall e, expr_size e <= S n -> isValue e -> forall j y, open_at j y e = e).
    { intros e He Hv j y. destruct e as [b | z | iv | xx | o e0 | o e0 e1 | e0 f | e0 m e1 | c es | e0 e1].
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl in Hv. contradiction.
      * simpl in Hv. contradiction.
      * simpl in Hv. contradiction.
      * simpl in Hv. contradiction.
      * simpl in Hv. contradiction.
      * simpl in Hv. contradiction.
      * rewrite open_at_new. f_equal. apply IHl.
        -- rewrite expr_size_new in He. lia.
        -- apply (proj1 (isValue_new_iff c es)). exact Hv.
      * simpl in Hv. contradiction. }
    assert (Hlist : forall es, list_expr_size es <= S n -> Forall isValue es -> forall j y,
               open_list_at j y es = es).
    { intros es He Hf j y. destruct es as [|a es].
      * simpl. reflexivity.
      * inversion Hf as [|? ? Ha Hrest]; subst.
        assert (Ha' : expr_size a <= S n)
          by (pose proof (list_expr_size_pos_le (a::es) a (or_introl eq_refl)); rewrite list_expr_size_cons in He; lia).
        assert (Htail : list_expr_size es <= n)
          by (rewrite list_expr_size_cons in He; pose proof (expr_size_pos a); lia).
        simpl. rewrite (Hexp a Ha' Ha j y). rewrite (IHl es Htail Hrest j y). reflexivity. }
    split; auto.
Qed.

Lemma isValue_open_at_inv : forall v, isValue v -> forall j y, open_at j y v = v.
Proof. intros v Hv j y. apply (proj1 (isValue_open_at_both (expr_size v))); auto; lia. Qed.

Lemma open_list_at_lc_val : forall es, Forall isValue es -> forall j y,
    open_list_at j y es = es.
Proof. intros es Hf j y. apply (proj2 (isValue_open_at_both (list_expr_size es))); auto; lia. Qed.

(* ============================================================ *)
(* Free variables of lists and closing commutation               *)
(* ============================================================ *)

Fixpoint fv_list (es : [expr]) : names :=
  match es with
  | nil => empty
  | e :: es' => union (fv e) (fv_list es')
  end.

Lemma fv_list_eq : forall es,
    (fix f (es : [expr]) : names :=
       match es with
       | nil => empty
       | e :: l => union (fv e) (f l)
       end) es = fv_list es.
Proof.
  intros es. induction es as [|e es IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma fv_new : forall c es, fv (ExpNew c es) = fv_list es.
Proof. intros. simpl. rewrite fv_list_eq. reflexivity. Qed.

Lemma fv_list_not_in : forall es x, ~ Elem x (fv_list es) ->
    forall a, In a es -> ~ Elem x (fv a).
Proof.
  intros es. induction es as [|e es IH]; intros x H a Hin.
  - destruct Hin.
  - simpl in H. destruct Hin as [-> | Hin].
    + apply not_in_union_l in H. auto.
    + eapply IH; eauto. apply not_in_union_r in H. auto.
Qed.

Lemma fv_list_in : forall es x a, In a es -> Elem x (fv a) -> Elem x (fv_list es).
Proof.
  intros es. induction es as [|e es IH]; intros x a Hin Hx.
  - destruct Hin.
  - simpl. destruct Hin as [-> | Hin].
    + apply in_union_l. auto.
    + apply in_union_r. eapply IH; eauto.
Qed.

Lemma fv_list_not_in_cons_l : forall a es x,
    ~ Elem x (fv_list (a :: es)) -> ~ Elem x (fv a).
Proof.
  intros. simpl in H. apply not_in_union_l in H. auto.
Qed.

Lemma fv_list_not_in_cons_r : forall a es x,
    ~ Elem x (fv_list (a :: es)) -> ~ Elem x (fv_list es).
Proof.
  intros. simpl in H. apply not_in_union_r in H. auto.
Qed.

Lemma subFV_open_self_both : forall n,
    (forall e, expr_size e <= n -> forall x v j, ~ Elem x (fv e) ->
        subFV x v (open_at j x e) = subBV_at j v e) /\
    (forall es, list_expr_size es <= n -> forall x v j,
        (forall a, In a es -> ~ Elem x (fv a)) ->
        subFV_list x v (open_list_at j x es) = subBV_list_at j v es).
Proof.
  induction n as [|n IH].
  - split.
    + intros e He. pose proof (expr_size_pos e); lia.
    + intros es He x v j Hf. destruct es as [|a es].
      * simpl. reflexivity.
      * pose proof (expr_size_pos a). rewrite list_expr_size_cons in He. lia.
  - destruct IH as [IHe IHl].
    assert (Hexp : forall e, expr_size e <= S n -> forall x v j, ~ Elem x (fv e) ->
               subFV x v (open_at j x e) = subBV_at j v e).
    { intros e He x v j Hfresh.
      destruct e as [b | z | iv | xx | o e0 | o e0 e1 | e0 f | e0 m e1 | c es | e0 e1].
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. destruct (PeanoNat.Nat.eqb j iv); simpl; try (rewrite PeanoNat.Nat.eqb_refl); reflexivity.
      * (* FV *)
        assert (Hne : x <> xx) by (intro E; subst; apply Hfresh; apply in_singleton; auto).
        simpl. destruct (PeanoNat.Nat.eqb x xx) eqn:Ex.
        -- apply PeanoNat.Nat.eqb_eq in Ex. exfalso. auto.
        -- reflexivity.
      * (* UnOp *) simpl in Hfresh. simpl. f_equal.
        apply IHe; [pose proof (expr_size_UnOp o e0); lia | auto].
      * (* BinOp *) simpl in Hfresh. simpl. f_equal.
        -- apply IHe; [pose proof (expr_size_BinOp_l o e0 e1); lia | apply not_in_union_l in Hfresh; auto].
        -- apply IHe; [pose proof (expr_size_BinOp_r o e0 e1); lia | apply not_in_union_r in Hfresh; auto].
      * (* Field *) simpl in Hfresh. simpl. f_equal.
        apply IHe; [pose proof (expr_size_Field e0 f); lia | auto].
      * (* Invoc *) simpl in Hfresh. simpl. f_equal.
        -- apply IHe; [pose proof (expr_size_Invoc_l e0 m e1); lia | apply not_in_union_l in Hfresh; auto].
        -- apply IHe; [pose proof (expr_size_Invoc_r e0 m e1); lia | apply not_in_union_r in Hfresh; auto].
      * (* ExpNew *)
        rewrite open_at_new, subFV_new, subBV_new. f_equal.
        apply IHl.
        -- rewrite expr_size_new in He. lia.
        -- rewrite fv_new in Hfresh. intros b Hb. eapply fv_list_not_in; eauto.
      * (* Let *) simpl in Hfresh. simpl. f_equal.
        -- apply IHe; [pose proof (expr_size_Let_l e0 e1); lia | apply not_in_union_l in Hfresh; auto].
        -- apply IHe; [pose proof (expr_size_Let_r e0 e1); lia | apply not_in_union_r in Hfresh; auto]. }
    assert (Hlist : forall es, list_expr_size es <= S n -> forall x v j,
               (forall a, In a es -> ~ Elem x (fv a)) ->
               subFV_list x v (open_list_at j x es) = subBV_list_at j v es).
    { intros es He x v j Hf. destruct es as [|a es].
      * simpl. reflexivity.
      * assert (Ha : expr_size a <= S n)
          by (pose proof (list_expr_size_pos_le (a::es) a (or_introl eq_refl)); rewrite list_expr_size_cons in He; lia).
        assert (Htail : list_expr_size es <= n)
          by (rewrite list_expr_size_cons in He; pose proof (expr_size_pos a); lia).
        simpl. rewrite (Hexp a Ha x v j).
        -- rewrite (IHl es Htail x v j).
           ++ reflexivity.
           ++ intros b Hb. apply Hf. right. auto.
        -- apply Hf. left. auto. }
    split; auto.
Qed.

Lemma subFV_open_self : forall x v j e, ~ Elem x (fv e) ->
    subFV x v (open_at j x e) = subBV_at j v e.
Proof. intros. apply (proj1 (subFV_open_self_both (expr_size e))); auto; lia. Qed.

(* ============================================================ *)
(* FJ context permutation, weakening, and head substitution      *)
(* ============================================================ *)

Definition permF (g g' : fjenv) : Prop :=
  forall x t, bound_inF x t g <-> bound_inF x t g'.

Lemma bound_inF_cons : forall x t y ty g,
    bound_inF x t (FCons y ty g) <-> ((x = y /\ t = ty) \/ bound_inF x t g).
Proof. intros. simpl. tauto. Qed.

Lemma permF_cons : forall g g' y ty, permF g g' -> permF (FCons y ty g) (FCons y ty g').
Proof.
  intros g g' y ty H x t. do 2 rewrite bound_inF_cons.
  specialize (H x t). tauto.
Qed.

Lemma permF_cons_swap : forall a ta b tb g,
    permF (FCons a ta (FCons b tb g)) (FCons b tb (FCons a ta g)).
Proof.
  intros a ta b tb g x t.
  repeat rewrite bound_inF_cons. tauto.
Qed.

Lemma permF_refl : forall g, permF g g.
Proof. intros g x t. tauto. Qed.

Lemma permF_sym : forall g g', permF g g' -> permF g' g.
Proof. intros g g' H x t. specialize (H x t). tauto. Qed.

Lemma permF_trans : forall g g' g'', permF g g' -> permF g' g'' -> permF g g''.
Proof. intros g g' g'' H1 H2 x t. specialize (H1 x t). specialize (H2 x t). tauto. Qed.

Lemma not_in_envFJ_cons : forall x y ty g,
    x <> y -> ~ in_envFJ x g -> ~ in_envFJ x (FCons y ty g).
Proof.
  intros x y ty g Hne Hg. unfold in_envFJ in *. simpl.
  intro H. apply set_add_elim in H. destruct H; auto.
Qed.

Lemma Forall2_HasFJ_perm_in : forall (gg g' : fjenv) es Us,
    (forall a u, In a es -> HasFJtype gg a u -> HasFJtype g' a u) ->
    Forall2 (HasFJtype gg) es Us -> Forall2 (HasFJtype g') es Us.
Proof.
  intros gg g' es Us Hper Hf.
  induction Hf as [|a u es' Us' Ha Hrest IH].
  - constructor.
  - constructor.
    + apply Hper with (u:=u); auto. left; auto.
    + apply IH. intros b v Hin Hb. apply Hper with (u:=v); auto. right; auto.
Qed.

Lemma HasFJtype_perm_aux : forall n e, expr_size e <= n ->
    forall g g' t, permF g g' -> HasFJtype g e t -> HasFJtype g' e t.
Proof.
  induction n as [|n IH]; intros e He g g' t Hp Hty.
  - pose proof (expr_size_pos e); lia.
  - induction Hty as
      [gg b | gg z
      | gg x0 t0 Hb
      | gg e0 op Ht0 IH0
      | gg e1 e2 op H1 IH1 H2 IH2
      | gg e1 e2 m t1 rt C ps H1 IH1 mt H2 IH2
      | gg e1 e2 m t1 rt I ps H1 IH1 mt H2 IH2
      | gg e0 f T C F i ff H0 IH0 Rf nth refeq Req
      | gg es C Fs Us fs Usmap fsmap Rf HF2
      | gg ex b e0 b' nms Hx IHx Hbody
      | gg e0 s t0 H0 IH0 St
      ].
    + apply FTBC.
    + apply FTIC.
    + apply FTVar. apply (proj1 (Hp x0 t0)); auto.
    + eapply FTUnOP. apply IH0; [pose proof (expr_size_UnOp op e0); lia | auto].
    + eapply FTBinOP.
      * apply IH1; [pose proof (expr_size_BinOp_l op e1 e2); lia | auto].
      * apply IH2; [pose proof (expr_size_BinOp_r op e1 e2); lia | auto].
    + eapply FTInvok.
      * apply IH1; [pose proof (expr_size_Invoc_l e1 m e2); lia | auto].
      * exact mt.
      * apply IH2; [pose proof (expr_size_Invoc_r e1 m e2); lia | auto].
    + eapply FTInvokI.
      * apply IH1; [pose proof (expr_size_Invoc_l e1 m e2); lia | auto].
      * exact mt.
      * apply IH2; [pose proof (expr_size_Invoc_r e1 m e2); lia | auto].
    + eapply FTField.
      * apply IH0; [pose proof (expr_size_Field e0 f); lia | auto].
      * exact Rf. * exact nth. * exact refeq. * exact Req.
    + eapply FTNew.
      * exact Usmap. * exact fsmap. * exact Rf.
      * eapply Forall2_HasFJ_perm_in; [ | exact HF2].
        intros a u Hin Ha. apply IH with (g:=gg) (t:=u); auto.
        pose proof (expr_size_new_In C es a Hin).
        pose proof (expr_size_pos (ExpNew C es)). lia.
    + eapply FTLet.
      * apply IHx; [pose proof (expr_size_Let_l ex e0); lia | auto].
      * intros y Hy. apply IH with (g:=FCons y b gg) (t:=b').
        -- change (expr_size (open_at 0 y e0) <= n). rewrite expr_size_open_at.
           pose proof (expr_size_Let_r ex e0). lia.
        -- apply permF_cons; auto.
        -- exact (Hbody y Hy).
    + eapply FTSub.
      * apply IH0; auto.
      * exact St.
Qed.

Lemma HasFJtype_perm : forall g g' e t, permF g g' -> HasFJtype g e t -> HasFJtype g' e t.
Proof. intros. eapply HasFJtype_perm_aux; eauto. Qed.

Lemma HasFJtype_weak_aux : forall n e, expr_size e <= n ->
    forall g y ty t, HasFJtype g e t -> HasFJtype (FCons y ty g) e t.
Proof.
  induction n as [|n IH]; intros e He g y ty t Hty.
  - pose proof (expr_size_pos e); lia.
  - induction Hty as
      [gg b | gg z
      | gg x0 t0 Hb
      | gg e0 op Ht0 IH0
      | gg e1 e2 op H1 IH1 H2 IH2
      | gg e1 e2 m t1 rt C ps H1 IH1 mt H2 IH2
      | gg e1 e2 m t1 rt I ps H1 IH1 mt H2 IH2
      | gg e0 f T C F i ff H0 IH0 Rf nth refeq Req
      | gg es C Fs Us fs Usmap fsmap Rf HF2
      | gg ex b e0 b' nms Hx IHx Hbody
      | gg e0 s t0 H0 IH0 St
      ].
    + apply FTBC.
    + apply FTIC.
    + apply FTVar. apply bound_inF_cons. right. auto.
    + eapply FTUnOP. apply IH with (g:=gg) (y:=y) (ty:=ty) (t:=erase (intype op)); auto.
      pose proof (expr_size_UnOp op e0). lia.
    + eapply FTBinOP.
      * apply IH with (g:=gg) (y:=y) (ty:=ty) (t:=erase (fst (intype2 op))); auto.
        pose proof (expr_size_BinOp_l op e1 e2). lia.
      * apply IH with (g:=gg) (y:=y) (ty:=ty) (t:=erase (snd (intype2 op))); auto.
        pose proof (expr_size_BinOp_r op e1 e2). lia.
    + eapply FTInvok.
      * apply IH with (g:=gg) (y:=y) (ty:=ty) (t:=TNom (TClass C)); auto.
        pose proof (expr_size_Invoc_l e1 m e2). lia.
      * exact mt.
      * apply IH with (g:=gg) (y:=y) (ty:=ty) (t:=erase t1); auto.
        pose proof (expr_size_Invoc_r e1 m e2). lia.
    + eapply FTInvokI.
      * apply IH with (g:=gg) (y:=y) (ty:=ty) (t:=TNom (TInterface I)); auto.
        pose proof (expr_size_Invoc_l e1 m e2). lia.
      * exact mt.
      * apply IH with (g:=gg) (y:=y) (ty:=ty) (t:=erase t1); auto.
        pose proof (expr_size_Invoc_r e1 m e2). lia.
    + eapply FTField.
      * apply IH with (g:=gg) (y:=y) (ty:=ty) (t:=TNom (TClass C)); auto.
        pose proof (expr_size_Field e0 f). lia.
      * exact Rf. * exact nth. * exact refeq. * exact Req.
    + eapply FTNew.
      * exact Usmap. * exact fsmap. * exact Rf.
      * eapply Forall2_HasFJ_perm_in with (g' := FCons y ty gg).
        -- intros a u Hin Ha. apply IH with (g:=gg) (y:=y) (ty:=ty) (t:=u).
           ++ pose proof (expr_size_new_In C es a Hin).
              pose proof (expr_size_pos (ExpNew C es)). lia.
           ++ exact Ha.
        -- exact HF2.
    + eapply FTLet.
      * apply IH with (g:=gg) (y:=y) (ty:=ty) (t:=b).
        -- pose proof (expr_size_Let_l ex e0). lia.
        -- exact Hx.
      * intros y0 Hy0.
        eapply HasFJtype_perm with (g := FCons y ty (FCons y0 b gg))
                                      (g' := FCons y0 b (FCons y ty gg)).
        -- apply permF_cons_swap.
        -- apply IH with (g:=FCons y0 b gg) (y:=y) (ty:=ty) (t:=b').
           ++ change (expr_size (open_at 0 y0 e0) <= n). rewrite expr_size_open_at.
              pose proof (expr_size_Let_r ex e0). lia.
           ++ exact (Hbody y0 Hy0).
    + eapply FTSub.
      * apply IH0; auto.
      * exact St.
Qed.

Lemma HasFJtype_weak : forall g y ty e t,
    HasFJtype g e t -> HasFJtype (FCons y ty g) e t.
Proof. intros. eapply HasFJtype_weak_aux; eauto. Qed.

Lemma bound_inF_in_envFJ : forall x t g, bound_inF x t g -> in_envFJ x g.
Proof.
  intros x t g. induction g as [|y ty g IH]; simpl; intros H.
  - destruct H.
  - destruct H as [[-> ->] | H].
    + unfold in_envFJ. simpl. apply set_add_intro2. auto.
    + unfold in_envFJ. simpl. apply set_add_intro1. apply IH. auto.
Qed.

Lemma not_in_big_decomp : forall y (nms : names) x (g : fjenv),
    ~ Elem y (union nms (union (singleton x) (bindsFJ g))) ->
    ~ Elem y nms /\ y <> x /\ ~ in_envFJ y g.
Proof.
  intros y nms x g H.
  pose proof (not_in_union_l y nms (union (singleton x) (bindsFJ g)) H) as Hl.
  pose proof (not_in_union_r y nms (union (singleton x) (bindsFJ g)) H) as Hr.
  pose proof (not_in_union_l y (singleton x) (bindsFJ g) Hr) as Hs.
  pose proof (not_in_union_r y (singleton x) (bindsFJ g) Hr) as Hb.
  split; [auto|]. split.
  - apply not_in_singleton. auto.
  - unfold in_envFJ. auto.
Qed.

Lemma Forall2_HasFJ_subst_gen : forall (GG g : fjenv) x (vv : expr) es Us,
    (forall a u, In a es -> HasFJtype GG a u -> HasFJtype g (subFV x vv a) u) ->
    Forall2 (HasFJtype GG) es Us ->
    Forall2 (HasFJtype g) (map (subFV x vv) es) Us.
Proof.
  intros GG g x vv es Us Hper Hf.
  induction Hf as [|a u es0 Us0 Ha Hrest IH].
  - simpl. constructor.
  - simpl. constructor.
    + apply Hper with (u:=u); auto. left; auto.
    + apply IH. intros b w Hin Hb. apply Hper with (u:=w); auto. right; auto.
Qed.

Lemma HasFJtype_subst_gen : forall (v : expr),
    (forall j y, open_at j y v = v) ->
    forall n e, expr_size e <= n ->
    forall (GG : fjenv) t, HasFJtype GG e t ->
    forall x tx (g : fjenv), GG = FCons x tx g -> ~ in_envFJ x g ->
    HasFJtype g v tx ->
    HasFJtype g (subFV x v e) t.
Proof.
  intros v Hv n. induction n as [|n IHn]; intros e He GG t Hty x tx g EG Hxin Hvty.
  - pose proof (expr_size_pos e); lia.
  - revert x tx g EG Hxin Hvty.
    induction Hty as
      [GG0 b | GG0 m
      | GG0 z t0 Hb
      | GG0 e0 op Ht0 IH0
      | GG0 e1 e2 op H1 IH1 H2 IH2
      | GG0 e1 e2 m1 t1 rt C ps H1 IH1 mt H2 IH2
      | GG0 e1 e2 m1 t1 rt I ps H1 IH1 mt H2 IH2
      | GG0 e0 f T C F i ff H0 IH0 Rf nth refeq Req
      | GG0 es C Fs Us fs Usmap fsmap Rf HF2
      | GG0 ex b e0 b' nms Hx IHx Hbody
      | GG0 e0 s t0 H0 IH0 St
      ]; intros x tx g EG Hxin Hvty.
    + apply FTBC.
    + apply FTIC.
    + (* FTVar *) rewrite EG in Hb. simpl in Hb. destruct Hb as [[Hz Ht] | Hg].
      * subst z. subst t0. simpl. rewrite PeanoNat.Nat.eqb_refl. simpl. exact Hvty.
      * destruct (PeanoNat.Nat.eqb x z) eqn:E.
        -- apply PeanoNat.Nat.eqb_eq in E. subst z. exfalso. apply Hxin.
           eapply bound_inF_in_envFJ; eauto.
        -- simpl. rewrite E. simpl. apply FTVar. exact Hg.
    + eapply FTUnOP. apply IH0 with (x:=x) (tx:=tx) (g:=g);
      try (pose proof (expr_size_UnOp op e0); lia); auto.
    + eapply FTBinOP.
      * apply IH1 with (x:=x) (tx:=tx) (g:=g);
        try (pose proof (expr_size_BinOp_l op e1 e2); lia); auto.
      * apply IH2 with (x:=x) (tx:=tx) (g:=g);
        try (pose proof (expr_size_BinOp_r op e1 e2); lia); auto.
    + eapply FTInvok.
      * apply IH1 with (x:=x) (tx:=tx) (g:=g);
        try (pose proof (expr_size_Invoc_l e1 m1 e2); lia); auto.
      * exact mt.
      * apply IH2 with (x:=x) (tx:=tx) (g:=g);
        try (pose proof (expr_size_Invoc_r e1 m1 e2); lia); auto.
    + eapply FTInvokI.
      * apply IH1 with (x:=x) (tx:=tx) (g:=g);
        try (pose proof (expr_size_Invoc_l e1 m1 e2); lia); auto.
      * exact mt.
      * apply IH2 with (x:=x) (tx:=tx) (g:=g);
        try (pose proof (expr_size_Invoc_r e1 m1 e2); lia); auto.
    + eapply FTField.
      * apply IH0 with (x:=x) (tx:=tx) (g:=g);
        try (pose proof (expr_size_Field e0 f); lia); auto.
      * exact Rf. * exact nth. * exact refeq. * exact Req.
    + (* FTNew *)
      rewrite subFV_new, subFV_list_map.
      eapply FTNew.
      * exact Usmap. * exact fsmap. * exact Rf.
      * eapply Forall2_HasFJ_subst_gen with (vv:=v).
        -- intros a u Hin Ha. apply IHn with (e:=a) (GG:=GG0) (x:=x) (tx:=tx) (g:=g).
           ++ pose proof (expr_size_new_In C es a Hin).
              pose proof (expr_size_pos (ExpNew C es)). lia.
           ++ exact Ha.
           ++ exact EG.
           ++ exact Hxin.
           ++ exact Hvty.
        -- exact HF2.
    + (* FTLet *)
      eapply FTLet with (nms := union nms (union (singleton x) (bindsFJ g))).
      * apply IHx with (x:=x) (tx:=tx) (g:=g);
        try (pose proof (expr_size_Let_l ex e0); lia); auto.
      * intros y Hy. apply not_in_big_decomp in Hy.
        destruct Hy as [Hy_nms [Hyx Hyg]].
        assert (Hperm : permF (FCons y b GG0) (FCons x tx (FCons y b g))).
        { rewrite EG. apply permF_cons_swap. }
        assert (Hsz : expr_size (open_at 0 y e0) <= n).
        { rewrite expr_size_open_at. pose proof (expr_size_Let_r ex e0). lia. }
        assert (Hxnot : ~ in_envFJ x (FCons y b g)).
        { intros Hc. unfold in_envFJ in *. simpl in Hc.
          apply set_add_elim in Hc. destruct Hc as [Hxy | Hc].
          - apply Hyx. symmetry. exact Hxy.
          - apply Hxin. exact Hc. }
        assert (Hvweak : HasFJtype (FCons y b g) v tx).
        { apply HasFJtype_weak. exact Hvty. }
        assert (Htyperm : HasFJtype (FCons x tx (FCons y b g)) (open_at 0 y e0) b').
        { eapply HasFJtype_perm; [exact Hperm | exact (Hbody y Hy_nms)]. }
        change (HasFJtype (FCons y b g) (open_at 0 y (subFV x v e0)) b').
        rewrite <- (subFV_open_comm x y v 0 e0); auto.
        apply IHn with (e := open_at 0 y e0) (GG := FCons x tx (FCons y b g))
                       (x := x) (tx := tx) (g := FCons y b g).
        -- exact Hsz.
        -- exact Htyperm.
        -- reflexivity.
        -- exact Hxnot.
        -- exact Hvweak.
    + eapply FTSub.
      * apply IH0 with (x:=x) (tx:=tx) (g:=g); try exact He; auto.
      * exact St.
Qed.

Lemma HasFJtype_subst_head : forall g x tx e t v,
    ~ in_envFJ x g ->
    HasFJtype (FCons x tx g) e t ->
    HasFJtype g v tx ->
    (forall j y, open_at j y v = v) ->
    HasFJtype g (subFV x v e) t.
Proof. intros. eapply HasFJtype_subst_gen; eauto. Qed.

(* ============================================================ *)
(* Structural inversion lemmas for HasFJtype (peeling FTSub)     *)
(* ============================================================ *)

Lemma H_Bc_inv : forall G b t, HasFJtype G (Bc b) t -> FJSubtype TBool t.
Proof.
  intros G b t H. remember (Bc b) as E eqn:EE. revert b EE.
  induction H as
    [gg b0 | gg n | gg x b0 Hb | gg e op Ht IHt
    | gg e1 e2 op H1 IH1 H2 IH2
    | gg e1 e2 m t1 rt C ps H1 IH1 mt H2 IH2
    | gg e1 e2 m t1 rt I ps H1 IH1 mt H2 IH2
    | gg e f T C F i ff H0 IH0 Rf nth refeq Req
    | gg es C Fs Us fs Usmap fsmap Rf HF2
    | gg ex b0 e b' nms Hx IHx Hbody
    | gg e s t0 H0 IH0 St]; intros b1 EE.
  - injection EE; intros; subst. apply FJSubtype_refl.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - pose proof (IH0 b1 EE) as Hs. eapply FJSubtype_trans; eauto.
Qed.

Lemma H_Ic_inv : forall G z t, HasFJtype G (Ic z) t -> FJSubtype TInt t.
Proof.
  intros G z t H. remember (Ic z) as E eqn:EE. revert z EE.
  induction H as
    [gg b0 | gg n | gg x b0 Hb | gg e op Ht IHt
    | gg e1 e2 op H1 IH1 H2 IH2
    | gg e1 e2 m t1 rt C ps H1 IH1 mt H2 IH2
    | gg e1 e2 m t1 rt I ps H1 IH1 mt H2 IH2
    | gg e f T C F i ff H0 IH0 Rf nth refeq Req
    | gg es C Fs Us fs Usmap fsmap Rf HF2
    | gg ex b0 e b' nms Hx IHx Hbody
    | gg e s t0 H0 IH0 St]; intros z0 EE.
  - discriminate EE.
  - injection EE; intros; subst. apply FJSubtype_refl.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - pose proof (IH0 z0 EE) as Hs. eapply FJSubtype_trans; eauto.
Qed.

Lemma H_FV_inv : forall G x t,
    HasFJtype G (FV x) t -> exists b, bound_inF x b G /\ FJSubtype b t.
Proof.
  intros G x t H. remember (FV x) as E eqn:EE. revert x EE.
  induction H as
    [gg b0 | gg n | gg x0 b0 Hb | gg e op Ht IHt
    | gg e1 e2 op H1 IH1 H2 IH2
    | gg e1 e2 m t1 rt C ps H1 IH1 mt H2 IH2
    | gg e1 e2 m t1 rt I ps H1 IH1 mt H2 IH2
    | gg e f T C F i ff H0 IH0 Rf nth refeq Req
    | gg es C Fs Us fs Usmap fsmap Rf HF2
    | gg ex b0 e b' nms Hx IHx Hbody
    | gg e s t0 H0 IH0 St]; intros x1 EE.
  - discriminate EE.
  - discriminate EE.
  - injection EE; intros; subst. exists b0. split; auto. apply FJSubtype_refl.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - destruct (IH0 x1 EE) as [b [Hb Hs]]. exists b. split; auto.
    eapply FJSubtype_trans; eauto.
Qed.

Lemma H_UnOp_inv : forall G c e0 t,
    HasFJtype G (ExpUnOp c e0) t ->
    HasFJtype G e0 (erase (intype c)) /\ FJSubtype (erase (ty' c)) t.
Proof.
  intros G c e0 t H. remember (ExpUnOp c e0) as E eqn:EE. revert c e0 EE.
  induction H as
    [gg b0 | gg n | gg x b0 Hb | gg e op Ht IHt
    | gg e1 e2 op H1 IH1 H2 IH2
    | gg e1 e2 m t1 rt C ps H1 IH1 mt H2 IH2
    | gg e1 e2 m t1 rt I ps H1 IH1 mt H2 IH2
    | gg e f T C F i ff H0 IH0 Rf nth refeq Req
    | gg es C Fs Us fs Usmap fsmap Rf HF2
    | gg ex b0 e b' nms Hx IHx Hbody
    | gg e s t0 H0 IH0 St]; intros cu eu EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - injection EE; intros; subst. destruct op, cu. split; [exact Ht | apply FJSubtype_refl].
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - destruct (IH0 cu eu EE) as [Hp Hs]. split; auto.
    eapply FJSubtype_trans; eauto.
Qed.

Lemma H_BinOp_inv : forall G c e1 e2 t,
    HasFJtype G (ExpBinOp c e1 e2) t ->
    HasFJtype G e1 (erase (fst (intype2 c))) /\
    HasFJtype G e2 (erase (snd (intype2 c))) /\
    FJSubtype (erase (ty'2 c)) t.
Proof.
  intros G c e1 e2 t H. remember (ExpBinOp c e1 e2) as E eqn:EE. revert c e1 e2 EE.
  induction H as
    [gg b0 | gg n | gg x b0 Hb | gg e op Ht IHt
    | gg e1' e2' op H1 IH1 H2 IH2
    | gg e1' e2' m t1 rt C ps H1 IH1 mt H2 IH2
    | gg e1' e2' m t1 rt I ps H1 IH1 mt H2 IH2
    | gg e f T C F i ff H0 IH0 Rf nth refeq Req
    | gg es C Fs Us fs Usmap fsmap Rf HF2
    | gg ex b0 e b' nms Hx IHx Hbody
    | gg e s t0 H0 IH0 St]; intros cb e1b e2b EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - injection EE; intros; subst. repeat split; auto; apply FJSubtype_refl.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - destruct (IH0 cb e1b e2b EE) as [H1b [H2b Hs]]. repeat split; auto.
    eapply FJSubtype_trans; eauto.
Qed.

Lemma H_Field_inv : forall G e f t,
    HasFJtype G (ExpFieldAccess e f) t ->
    exists C Fs i ff,
      Reffields C Fs /\ nth_error Fs i = Some ff /\ ref ff = f /\
      HasFJtype G e (TNom (TClass C)) /\ FJSubtype (erase (ReffieldType ff)) t.
Proof.
  intros G e f t H. remember (ExpFieldAccess e f) as E eqn:EE. revert e f EE.
  induction H as
    [gg b0 | gg n | gg x b0 Hb | gg e0 op Ht IHt
    | gg e1 e2 op H1 IH1 H2 IH2
    | gg e1 e2 m t1 rt C ps H1 IH1 mt H2 IH2
    | gg e1 e2 m t1 rt I ps H1 IH1 mt H2 IH2
    | gg e0 f0 T C F i ff H0 IH0 Rf nth refeq Req
    | gg es C Fs Us fs Usmap fsmap Rf HF2
    | gg ex b0 e0 b' nms Hx IHx Hbody
    | gg e0 s t0 H0 IH0 St]; intros eF fF EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - injection EE; intros; subst. exists C, F, i, ff.
    split; [|split; [|split; [|split]]]; auto. apply FJSubtype_refl.
  - discriminate EE.
  - discriminate EE.
  - destruct (IH0 eF fF EE) as [C [Fs [i [ffi [HR [Hn [Hr [Hty Hs]]]]]]]].
    exists C, Fs, i, ffi. split; [|split; [|split; [|split]]]; auto.
    eapply FJSubtype_trans; eauto.
Qed.

Lemma H_Invok_inv : forall G e1 m e2 t,
    HasFJtype G (ExpMethodInvoc e1 m e2) t ->
    (exists C ps t1 rt, mtype(m, C) = ps ~> t1 ~> rt /\
        HasFJtype G e1 (TNom (TClass C)) /\ HasFJtype G e2 (erase t1) /\
        FJSubtype (erase rt) t) \/
    (exists I ps t1 rt, mtypei(m, I) = ps ~> t1 ~> rt /\
        HasFJtype G e1 (TNom (TInterface I)) /\ HasFJtype G e2 (erase t1) /\
        FJSubtype (erase rt) t).
Proof.
  intros G e1 m e2 t H. remember (ExpMethodInvoc e1 m e2) as E eqn:EE.
  revert e1 m e2 EE.
  induction H as
    [gg b0 | gg n | gg x b0 Hb | gg e0 op Ht IHt
    | gg e1' e2' op H1 IH1 H2 IH2
    | gg e1' e2' m0 t1 rt C ps H1 IH1 mt H2 IH2
    | gg e1' e2' m0 t1 rt I ps H1 IH1 mt H2 IH2
    | gg e0 f T C F i ff H0 IH0 Rf nth refeq Req
    | gg es C Fs Us fs Usmap fsmap Rf HF2
    | gg ex b0 e0 b' nms Hx IHx Hbody
    | gg e0 s t0 H0 IH0 St]; intros ei mi e2i EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - injection EE; intros; subst.
    left. exists C, ps, t1, rt. split; [|split; [|split]]; auto. apply FJSubtype_refl.
  - injection EE; intros; subst.
    right. exists I, ps, t1, rt. split; [|split; [|split]]; auto. apply FJSubtype_refl.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - destruct (IH0 ei mi e2i EE)
      as [[C [ps [t1 [rt [Hmt [H1 [H2 Hs]]]]]]] |
          [I [ps [t1 [rt [Hmt [H1 [H2 Hs]]]]]]]].
    + left. exists C, ps, t1, rt. split; [|split; [|split]]; auto.
      eapply FJSubtype_trans; eauto.
    + right. exists I, ps, t1, rt. split; [|split; [|split]]; auto.
      eapply FJSubtype_trans; eauto.
Qed.

Lemma H_New_inv : forall G C es t,
    HasFJtype G (ExpNew C es) t ->
    exists Fs, Reffields C Fs /\
      Forall2 (HasFJtype G) es (map erase (map ReffieldType Fs)) /\
      FJSubtype (TNom (TClass C)) t.
Proof.
  intros G C es t H. remember (ExpNew C es) as E eqn:EE. revert C es EE.
  induction H as
    [gg b0 | gg n | gg x b0 Hb | gg e0 op Ht IHt
    | gg e1 e2 op H1 IH1 H2 IH2
    | gg e1 e2 m t1 rt C0 ps H1 IH1 mt H2 IH2
    | gg e1 e2 m t1 rt I ps H1 IH1 mt H2 IH2
    | gg e0 f T C0 F i ff H0 IH0 Rf nth refeq Req
    | gg es0 C0 Fs Us fs Usmap fsmap Rf HF2
    | gg ex b0 e0 b' nms Hx IHx Hbody
    | gg e0 s t0 H0 IH0 St]; intros Cn esn EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - injection EE; intros; subst. exists Fs. split; [|split]; auto.
    apply FJSubtype_refl.
  - discriminate EE.
  - destruct (IH0 Cn esn EE) as [Fs [HR [Hf Hs]]]. exists Fs.
    split; [|split]; auto. eapply FJSubtype_trans; eauto.
Qed.

Lemma H_Let_inv : forall G ex e t,
    HasFJtype G (ExpLet ex e) t ->
    exists b b' nms, HasFJtype G ex b /\
      (forall y, ~ Elem y nms -> HasFJtype (FCons y b G) (unbind y e) b') /\
      FJSubtype b' t.
Proof.
  intros G ex e t H. remember (ExpLet ex e) as E eqn:EE. revert ex e EE.
  induction H as
    [gg b0 | gg n | gg x b0 Hb | gg e0 op Ht IHt
    | gg e1 e2 op H1 IH1 H2 IH2
    | gg e1 e2 m t1 rt C ps H1 IH1 mt H2 IH2
    | gg e1 e2 m t1 rt I ps H1 IH1 mt H2 IH2
    | gg e0 f T C F i ff H0 IH0 Rf nth refeq Req
    | gg es C Fs Us fs Usmap fsmap Rf HF2
    | gg ex0 b0 e0 b' nms Hx IHx Hbody
    | gg e0 s t0 H0 IH0 St]; intros exl el EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - discriminate EE.
  - injection EE; intros; subst. exists b0, b', nms.
    split; [|split]; auto. apply FJSubtype_refl.
  - destruct (IH0 exl el EE) as [b [b' [nms [Hx [Hb Hs]]]]].
    exists b, b', nms. split; [|split]; auto. eapply FJSubtype_trans; eauto.
Qed.

(* ============================================================ *)
(* Superclass reachability                                       *)
(* ============================================================ *)

Inductive Reach : ClassName -> ClassName -> Prop :=
| Reach_refl : forall C, Reach C C
| Reach_step : forall C D E Is Fs nd1 K Ms nd2,
    find C RefCT = Some (RefCDecl C D Is Fs nd1 K Ms nd2) ->
    Reach D E -> Reach C E.

Lemma Reach_trans : forall C D E, Reach C D -> Reach D E -> Reach C E.
Proof.
  intros C D E H. induction H as [C0 | C0 D0 E0 Is Fs nd1 K Ms nd2 Hf HR IH].
  - intros HDE. exact HDE.
  - intros HDE. eapply Reach_step; [exact Hf | eapply IH; exact HDE].
Qed.

Lemma subclass_iface_source : forall (I : InterfaceName) Y,
    SubClass (TInterface I) Y -> exists J, Y = TInterface J.
Proof.
  intros I Y H. dependent induction H.
  - exists I. reflexivity.
  - destruct (IHSubClass1 I eq_refl) as [J HJ]. subst b2.
    exact (IHSubClass2 J eq_refl).
Qed.

Lemma SubClass_iface_class_false : forall (I : InterfaceName) C,
    SubClass (TInterface I) (TClass C) -> False.
Proof.
  intros I C H. destruct (subclass_iface_source I (TClass C) H) as [J HJ].
  inversion HJ.
Qed.

Lemma SubClass_iface_eq : forall (I J : InterfaceName),
    SubClass (TInterface I) (TInterface J) -> I = J.
Proof.
  intros I J H. dependent induction H.
  - reflexivity.
  - destruct (subclass_iface_source I b2 H) as [J1 HJ1]. subst b2.
    pose proof (IHSubClass1 I J1 eq_refl eq_refl) as H1.
    pose proof (IHSubClass2 J1 J eq_refl eq_refl) as H2.
    congruence.
Qed.

Lemma subclass_reach : forall C D, SubClass (TClass C) (TClass D) -> Reach C D.
Proof.
  intros C D H. dependent induction H.
  - apply Reach_refl.
  - destruct b2 as [E | I].
    + eapply Reach_trans.
      * apply (IHSubClass1 C E eq_refl eq_refl).
      * apply (IHSubClass2 E D eq_refl eq_refl).
    + exfalso. eapply SubClass_iface_class_false; eauto.
  - eapply Reach_step; [exact H | apply Reach_refl].
Qed.

Lemma reach_subclass : forall C D, Reach C D -> SubClass (TClass C) (TClass D).
Proof.
  intros C D H. induction H as [C0 | C0 D0 E0 Is Fs nd1 K Ms nd2 Hf HR IH].
  - apply SubCRefl.
  - eapply SubCTrans.
    + eapply SubCInh; exact Hf.
    + exact IH.
Qed.

(* ============================================================ *)
(* Method / body resolution                                      *)
(* ============================================================ *)

Lemma mtype_decl : forall m C ps t rt,
    mtype(m, C) = ps ~> t ~> rt ->
    exists X D Is Fs K Ms nd1 nd2 e,
      Reach C X /\
      find X RefCT = Some (RefCDecl X D Is Fs nd1 K Ms nd2) /\
      find m Ms = Some (MDefn (MDecl rt m ps t) e).
Proof.
  intros m C ps t rt H. dependent induction H.
  - exists C, D, Is, Fs, K, Ms, noDupfs, noDupMds, e.
    split; [apply Reach_refl | split; auto].
  - destruct IHm_type as [X1 [D1 [Is1 [Fs1 [K1 [Ms1 [nd11 [nd21 [e1 [HR [Hf Hm]]]]]]]]]]].
    exists X1, D1, Is1, Fs1, K1, Ms1, nd11, nd21, e1.
    split; [|split]; auto.
    eapply Reach_step; eauto.
Qed.

Lemma m_body_decl : forall m C e,
    m_body m C e ->
    exists X D Is Fs K Ms nd1 nd2 ps t rt,
      Reach C X /\
      find X RefCT = Some (RefCDecl X D Is Fs nd1 K Ms nd2) /\
      find m Ms = Some (MDefn (MDecl rt m ps t) e).
Proof.
  intros m C e H. induction H as
    [C D Is m0 ps rt t e0 Fs K Ms nd1 nd2 Hf Hm
    | C D Is m0 e0 Fs K Ms nd1 nd2 Hf Hnot Hbody IH].
  - exists C, D, Is, Fs, K, Ms, nd1, nd2, ps, t, rt.
    split; [apply Reach_refl | split; auto].
  - destruct IH as [X1 [D1 [Is1 [Fs1 [K1 [Ms1 [nd11 [nd21 [ps1 [t1 [rt1 [HR [Hf' Hm]]]]]]]]]]]]].
    exists X1, D1, Is1, Fs1, K1, Ms1, nd11, nd21, ps1, t1, rt1.
    split; [|split]; auto. eapply Reach_step; eauto.
Qed.


Lemma MDefn_inj : forall d1 d2 e1 e2, MDefn d1 e1 = MDefn d2 e2 -> d1 = d2 /\ e1 = e2.
Proof. intros. injection H. auto. Qed.

Lemma MDecl_inj : forall rt1 m1 ps1 t1 rt2 m2 ps2 t2,
    MDecl rt1 m1 ps1 t1 = MDecl rt2 m2 ps2 t2 ->
    rt1 = rt2 /\ m1 = m2 /\ ps1 = ps2 /\ t1 = t2.
Proof. intros. injection H. auto. Qed.

Lemma mtype_det : forall m C ps1 t1 rt1,
    mtype(m, C) = ps1 ~> t1 ~> rt1 ->
    forall ps2 t2 rt2, mtype(m, C) = ps2 ~> t2 ~> rt2 ->
    ps1 = ps2 /\ t1 = t2 /\ rt1 = rt2.
Proof.
  intros m C ps1 t1 rt1 H1. induction H1 as
    [C0 D0 Is0 m0 ps0 rt0 t0 e0 Fs0 K0 Ms0 nd1 nd2 Hf0 Hm0
    | ps0 C0 D0 Is0 m0 rt0 t0 Fs0 K0 Ms0 nd1 nd2 Hf0 Hnot0 Hmt0 IH0];
    intros ps2 t2 rt2 H2.
  - dependent destruction H2.
    + assert (HMs : Ms0 = Ms) by (rewrite Hf0 in H; congruence).
      subst Ms0.
      assert (Hdef : MDefn (MDecl rt0 m ps0 t0) e0 = MDefn (MDecl rt m ps t) e).
      { eapply find_det; eauto. }
      destruct (MDefn_inj _ _ _ _ Hdef) as [Hmd He].
      destruct (MDecl_inj _ _ _ _ _ _ _ _ Hmd) as [Hrt [Hm [Hps Ht]]].
      subst. auto.
    + assert (HMs : Ms0 = Ms) by (rewrite Hf0 in H; congruence).
      subst Ms0. rewrite Hm0 in H0. discriminate.
  - dependent destruction H2.
    + assert (HMs : Ms0 = Ms) by (rewrite Hf0 in H; congruence).
      subst Ms0. rewrite H0 in Hnot0. discriminate.
    + assert (HD : D0 = D) by (rewrite Hf0 in H; congruence).
      subst D0. exact (IH0 ps t rt H2).
Qed.

Lemma Reach_mtype_exists : forall C D m,
    Reach C D ->
    (exists ps t rt, mtype(m, D) = ps ~> t ~> rt) ->
    exists ps t rt, mtype(m, C) = ps ~> t ~> rt.
Proof.
  intros C D m H. induction H as [C0 | C0 D0 E0 Is Fs nd1 K Ms nd2 Hf HR IH].
  - intros Hm. exact Hm.
  - intros [ps [t [rt Hm]]].
    destruct (find m Ms) as [d|] eqn:E.
    + destruct d as [[rt' m' ps' t'] e'].
      assert (Href : ref (MDefn (MDecl rt' m' ps' t') e') = m)
        by (eapply find_ref_eq; eauto).
      simpl in Href. subst m'.
      exists ps', t', rt'.
      eapply mty_ok; eauto.
    + destruct (IH (ex_intro _ ps (ex_intro _ t (ex_intro _ rt Hm))))
        as [ps' [t' [rt' Hm']]].
      exists ps', t', rt'.
      eapply mty_no_override; eauto.
Qed.

Lemma m_body_decl_mtype : forall m C e,
    m_body m C e ->
    exists X D Is Fs K Ms nd1 nd2 ps t rt,
      Reach C X /\
      find X RefCT = Some (RefCDecl X D Is Fs nd1 K Ms nd2) /\
      find m Ms = Some (MDefn (MDecl rt m ps t) e) /\
      mtype(m, C) = ps ~> t ~> rt.
Proof.
  intros m C e H. induction H as
    [C D Is m0 ps rt t e0 Fs K Ms nd1 nd2 Hf Hm
    | C D Is m0 e0 Fs K Ms nd1 nd2 Hf Hnot Hbody IH].
  - exists C, D, Is, Fs, K, Ms, nd1, nd2, ps, t, rt.
    split; [apply Reach_refl | split; [|split]]; auto.
    eapply mty_ok; eauto.
  - destruct IH as (X & D1 & Is1 & Fs1 & K1 & Ms1 & nd11 & nd21 & ps & t & rt & HR & Hf' & Hm' & Hmt).
    exists X, D1, Is1, Fs1, K1, Ms1, nd11, nd21, ps, t, rt.
    split; [|split; [|split]]; auto.
    + eapply Reach_step; eauto.
    + eapply mty_no_override; eauto.
Qed.

Lemma reach_mbody : forall m C X e,
    Reach C X -> m_body m X e -> exists e', m_body m C e'.
Proof.
  intros m C X e HR. induction HR as [C0 | C0 D0 E0 Is Fs nd1 K Ms nd2 Hf HR0 IH].
  - intros Hm. exists e. exact Hm.
  - intros Hm. destruct (find m Ms) as [d|] eqn:E.
    + destruct d as [[rt m' ps t] e'].
      assert (Href : ref (MDefn (MDecl rt m' ps t) e') = m)
        by (eapply find_ref_eq; eauto).
      simpl in Href. subst m'.
      exists e'. eapply mbdy_ok; eauto.
    + destruct (IH Hm) as [e' He'].
      exists e'. eapply mbdy_no_override; eauto.
Qed.


Lemma mtype_exists_mbody : forall m C ps t rt,
    mtype(m, C) = ps ~> t ~> rt -> exists e, m_body m C e.
Proof.
  intros m C ps t rt Hm.
  destruct (mtype_decl m C ps t rt Hm) as
    (X & D & Is & Fs & K & Ms & nd1 & nd2 & e & HR & Hf & Hfind).
  assert (HmX : m_body m X e) by (eapply mbdy_ok; eauto).
  destruct (reach_mbody m C X e HR HmX) as [e' He'].
  exists e'. exact He'.
Qed.


Lemma cok_methods : forall X D Is Fs nd1 K Ms nd2,
    find X RefCT = Some (RefCDecl X D Is Fs nd1 K Ms nd2) ->
    Forall (MType_OK X) Ms.
Proof.
  intros X D Is Fs nd1 K Ms nd2 Hf.
  pose proof (cok X D Fs nd1 K Is Ms nd2 Hf) as HC.
  inversion HC. assumption.
Qed.

Lemma MType_OK_override : forall C rt m ps t e D Is Fs nd1 K Ms nd2,
    find C RefCT = Some (RefCDecl C D Is Fs nd1 K Ms nd2) ->
    MType_OK C (MDefn (MDecl rt m ps t) e) ->
    override m C D ps t rt.
Proof.
  intros. inversion H0; subst.
  assert (HD : D0 = D) by (rewrite H in H6; congruence).
  subst D0. exact H8.
Qed.

Lemma MType_OK_body : forall C rt m ps t e,
    MType_OK C (MDefn (MDecl rt m ps t) e) ->
    (forall y y', y <> y' ->
      Hastype (Cons y' (openT_at 0 y t) (Cons y (TRefn (TNom (TClass C)) ps) Empty))
              (open_at 1 y (open_at 0 y' e))
              (openT_at 1 y (openT_at 0 y' rt))) /\
    fv e = empty /\ free t = empty /\ free rt = empty.
Proof.
  intros. inversion H; subst. auto.
Qed.

Lemma override_subtypes_erase : forall m C D ps t rt Ds D0 ps',
    override m C D ps t rt -> mtype(m, D) = ps' ~> Ds ~> D0 ->
    FJSubtype (erase Ds) (erase t) /\ FJSubtype (erase rt) (erase D0).
Proof.
  intros m C D ps t rt Ds D0 ps' Hov Hm.
  destruct (Hov Ds D0 ps' Hm) as [Hpred [Hpar Hret]].
  - (* param *)
    split.
    + unfold subtype_under in Hpar. specialize (Hpar 0).
      apply Subtype_erase in Hpar. rewrite !erase_openT in Hpar. exact Hpar.
    + unfold subtype_under2 in Hret. specialize (Hret 0 1).
      assert (H01 : 0 <> 1) by lia. specialize (Hret H01).
      apply Subtype_erase in Hret. rewrite !erase_openT in Hret. exact Hret.
Qed.

Lemma mtype_chain_sub : forall Cdyn Cstat m ps1 t1 rt1,
    Reach Cdyn Cstat ->
    mtype(m, Cdyn) = ps1 ~> t1 ~> rt1 ->
    forall ps2 t2 rt2, mtype(m, Cstat) = ps2 ~> t2 ~> rt2 ->
    FJSubtype (erase t2) (erase t1) /\
    (FJSubtype (erase rt1) (erase rt2)).
Proof.
  intros Cdyn Cstat m ps1 t1 rt1 HR. revert ps1 t1 rt1.
  induction HR as [C0 | C0 D0 E0 Is Fs nd1 K Ms nd2 Hf HR0 IH];
    intros ps1 t1 rt1 Hm1 ps2 t2 rt2 Hm2.
  - destruct (mtype_det _ _ _ _ _ Hm1 _ _ _ Hm2) as [Hps [Ht Hrt]].
    subst. split; apply FJSubtype_refl.
  - dependent destruction Hm1.
    + (* mty_ok *)
      assert (HD : D0 = D) by (rewrite Hf in H; congruence).
      subst D0.
      assert (HForall : Forall (MType_OK C) Ms0)
        by (eapply cok_methods with (D:=D) (Is:=Is0) (Fs:=Fs0) (nd1:=noDupfs) (K:=K0) (nd2:=noDupMds); exact H).
      pose proof (Forall_find MethodDefn MDefnRef (MType_OK C) m Ms0 _ HForall H0) as Hmok.
      pose proof (MType_OK_override C rt m ps t e D Is0 Fs0 noDupfs K0 Ms0 noDupMds H Hmok) as Hov.
      destruct (Reach_mtype_exists D E0 m HR0
                  (ex_intro _ ps2 (ex_intro _ t2 (ex_intro _ rt2 Hm2))))
        as [ps' [Ds [D0' HmD]]].
      destruct (IH ps' Ds D0' HmD ps2 t2 rt2 Hm2) as [Hpar_d Hret_d].
      destruct (override_subtypes_erase m C D ps t rt Ds D0' ps' Hov HmD)
        as [Hpar_o Hret_o].
      split.
      * eapply FJSubtype_trans; eauto.
      * eapply FJSubtype_trans; eauto.
    + (* mty_no_override *)
      assert (HD : D = D0) by (rewrite Hf in H; congruence).
      subst D. exact (IH ps t rt Hm1 ps2 t2 rt2 Hm2).
Qed.

(* ============================================================ *)
(* Reffields functionality and prefix                           *)
(* ============================================================ *)

Lemma Reffields_fun : forall C Fs1 Fs2, Reffields C Fs1 -> Reffields C Fs2 -> Fs1 = Fs2.
Proof.
  intros C Fs1 Fs2 H1. revert Fs2. induction H1 as [| C0 D Is fs nd1 K Ms nd2 fs' Hf HR IH Hnd]; intros Fs2 H2.
  - (* Object *) dependent destruction H2.
    + reflexivity.
    + (* find Object = Some ... contradicts obj_notin_dom *)
      rewrite obj_notin_dom in H. discriminate.
  - inversion H2; subst.
    + rewrite obj_notin_dom in Hf. discriminate.
    + assert (HD : D0 = D) by (rewrite Hf in H; congruence).
      assert (Hfs : fs0 = fs) by (rewrite Hf in H; congruence).
      subst D0. subst fs0.
      assert (Hsuper : fs' = fs'0) by (exact (IH fs'0 H0)).
      subst fs'0. reflexivity.
Qed.

Lemma Reffields_prefix : forall Cdyn Cstat Fdyn Fstat,
    Reach Cdyn Cstat ->
    Reffields Cdyn Fdyn -> Reffields Cstat Fstat ->
    exists extra, Fdyn = Fstat ++ extra.
Proof.
  intros Cdyn Cstat Fdyn Fstat HR. revert Fdyn Fstat.
  induction HR as [C0 | C0 D0 E0 Is Fs nd1 K Ms nd2 Hf HR0 IH];
    intros Fdyn Fstat Hdyn Hstat.
  - exists nil. rewrite (Reffields_fun _ _ _ Hdyn Hstat). rewrite app_nil_r. reflexivity.
  - dependent destruction Hdyn.
    + rewrite obj_notin_dom in Hf. discriminate.
    + assert (HD : D0 = D) by (rewrite Hf in H; congruence).
      assert (Hfs : Fs = fs) by (rewrite Hf in H; congruence).
      subst D0. subst Fs.
      destruct (IH fs' Fstat Hdyn Hstat) as [extra Hextra].
      exists (extra ++ fs). rewrite Hextra. rewrite app_assoc. reflexivity.
Qed.

(* ============================================================ *)
(* Interface implementation discovery                            *)
(* ============================================================ *)

Lemma SubClass_iface_target : forall C I,
    SubClass (TClass C) (TInterface I) ->
    exists E D Is Fs nd1 K Ms nd2 i,
      Reach C E /\
      find E RefCT = Some (RefCDecl E D Is Fs nd1 K Ms nd2) /\
      nth_error Is i = Some I.
Proof.
  intros C I H. dependent induction H.
  - destruct b2 as [E | J].
    + destruct (IHSubClass2 E I eq_refl eq_refl) as
        (E2 & D2 & Is2 & Fs2 & nd12 & K2 & Ms2 & nd22 & i2 & HR2 & Hf2 & Hn2).
      exists E2, D2, Is2, Fs2, nd12, K2, Ms2, nd22, i2.
      split; [|split]; auto.
      eapply Reach_trans; [apply subclass_reach; exact H | exact HR2].
    + destruct (IHSubClass1 C J eq_refl eq_refl) as
        (E & D & Is & Fs & nd1 & K & Ms & nd2 & i & HR & Hf & Hn).
      pose proof (SubClass_iface_eq J I H0) as ->.
      exists E, D, Is, Fs, nd1, K, Ms, nd2, i. split; [|split]; auto.
  - exists C, D, Is, fs, noDupfs, K, mds, noDupMds, i.
    split; [apply Reach_refl | split; auto].
Qed.

Lemma H_BV_inv : forall g i t, HasFJtype g (BV i) t -> False.
Proof.
  intros g i t H. remember (BV i) as E eqn:EE. revert i EE.
  induction H as
    [gg b0 | gg n | gg x b0 Hb | gg e op Ht IHt
    | gg e1 e2 op H1 IH1 H2 IH2
    | gg e1 e2 m t1 rt C ps H1 IH1 mt H2 IH2
    | gg e1 e2 m t1 rt I ps H1 IH1 mt H2 IH2
    | gg e f T C F i ff H0 IH0 Rf nth refeq Req
    | gg es C Fs Us fs Usmap fsmap Rf HF2
    | gg ex b0 e b' nms Hx IHx Hbody
    | gg e0 s t0 H0 IH0 St]; intros i0 EE.
  - discriminate EE. - discriminate EE. - discriminate EE. - discriminate EE.
  - discriminate EE. - discriminate EE. - discriminate EE. - discriminate EE.
  - discriminate EE. - discriminate EE.
  - exact (IH0 i0 EE).
Qed.

Lemma HasFJtype_value_bool : forall g v,
    isValue v -> HasFJtype g v TBool -> exists b, v = Bc b.
Proof.
  intros g v Hv Hty. destruct v as [b | z | iv | x | o e0 | o e0 e1 | e0 f | e0 m e1 | c es | e0 e1];
    simpl in Hv; try contradiction.
  - exists b. reflexivity.
  - exfalso. apply H_Ic_inv in Hty. dependent destruction Hty.
  - exfalso. destruct (H_New_inv g c es TBool Hty) as [Fs [HR [Hf Hsub]]].
    dependent destruction Hsub.
Qed.

Lemma HasFJtype_value_class : forall g v C,
    isValue v -> HasFJtype g v (TNom (TClass C)) ->
    exists C' es, v = ExpNew C' es /\ SubClass (TClass C') (TClass C).
Proof.
  intros g v C Hv Hty. destruct v as [b | z | iv | x | o e0 | o e0 e1 | e0 f | e0 m e1 | c es | e0 e1];
    simpl in Hv; try contradiction.
  - exfalso. apply H_Bc_inv in Hty. dependent destruction Hty.
  - exfalso. apply H_Ic_inv in Hty. dependent destruction Hty.
  - (* ExpNew *) exists c, es. split; [reflexivity|].
    destruct (H_New_inv g c es (TNom (TClass C)) Hty) as [Fs [HR [Hf Hsub]]].
    destruct (FJSubtype_class_inv (TNom (TClass c)) C Hsub) as [C' [HC' Hsc]].
    inversion HC'. subst. exact Hsc.
Qed.

Lemma HasFJtype_value_iface : forall g v I,
    isValue v -> HasFJtype g v (TNom (TInterface I)) ->
    exists C es, v = ExpNew C es /\ SubClass (TClass C) (TInterface I).
Proof.
  intros g v I Hv Hty. destruct v as [b | z | iv | x | o e0 | o e0 e1 | e0 f | e0 m e1 | c es | e0 e1];
    simpl in Hv; try contradiction.
  - exfalso. apply H_Bc_inv in Hty. dependent destruction Hty.
  - exfalso. apply H_Ic_inv in Hty. dependent destruction Hty.
  - (* ExpNew *) exists c, es. split; [reflexivity|].
    destruct (H_New_inv g c es (TNom (TInterface I)) Hty) as [Fs [HR [Hf Hsub]]].
    destruct (FJSubtype_nom_inv (TNom (TClass c)) (TInterface I) Hsub) as [Y [HY Hsc]].
    inversion HY. subst. exact Hsc.
Qed.

Lemma iface_implement : forall E D Is Fs nd1 K Ms nd2 i I,
    find E RefCT = Some (RefCDecl E D Is Fs nd1 K Ms nd2) ->
    nth_error Is i = Some I ->
    forall m irt ips it,
      mtypei(m, I) = ips ~> it ~> irt ->
      exists Ds D0 ps', mtype(m, E) = ps' ~> Ds ~> D0.
Proof.
  intros E D Is Fs nd1 K Ms nd2 i I Hf Hn m irt ips it Hmti.
  pose proof (cok E D Fs nd1 K Is Ms nd2 Hf) as HC.
  inversion HC as [E0 D0 Fs0 ndf Is0 K0 Ms0 ndm fdecl HK HRf Hnd HForall HF Hfind HCI]; subst.
  assert (Himpl : Class_implemented E I) by (exact (HCI i I Hn)).
  inversion Himpl as [E1 I1 iMs ndi HfindI Hforall]; subst.
  inversion Hmti as [I2 Ms2 m2 rt2 t2 ps2 nd2' HfindI2 HfindM]; subst.
  assert (HMsi : Ms2 = iMs) by (rewrite HfindI in HfindI2; congruence).
  subst Ms2.
  destruct (Hforall m irt ips it HfindM) as (Ds & D0' & ps' & Hmt & Hrest).
  exists Ds, D0', ps'. exact Hmt.
Qed.

Lemma nth_error_map_Some : forall (A B : Type) (f : A -> B) l i x,
    nth_error l i = Some x -> nth_error (map f l) i = Some (f x).
Proof.
  intros A B f l. induction l as [|a l IH]; intros i x H.
  - destruct i; simpl in H; discriminate.
  - destruct i; simpl in *.
    + injection H as ->. reflexivity.
    + apply IH; auto.
Qed.

(* ============================================================ *)
(* Progress                                                      *)
(* ============================================================ *)

Lemma progress_args : forall es,
    Forall (fun e => isValue e \/ exists e', Step e e') es ->
    (forall e, In e es -> isValue e) \/
    exists i ei ei', nth_error es i = Some ei /\ Step ei ei'.
Proof.
  intros es. induction es as [|a es IH]; intros Hall.
  - left. intros e Hin. destruct Hin.
  - inversion Hall as [|? ? Ha Hrest]; subst.
    destruct Ha as [Hva | [a' Hsa]].
    + destruct (IH Hrest) as [Hval | (i & ei & ei' & Hnth & Hstep)].
      * left. intros e [-> | Hin]; auto.
      * right. exists (S i), ei, ei'. split; auto.
    + right. exists 0, a, a'. split; auto.
Qed.

Lemma fj_progress_aux : forall n e, expr_size e <= n ->
    forall t, HasFJtype FEmpty e t -> isValue e \/ exists e', Step e e'.
Proof.
  induction n as [|n IH]; intros e He t Hty.
  - pose proof (expr_size_pos e); lia.
  - destruct e as [b | z | iv | x | o e0 | o e0 e1 | e0 f | e0 m e1 | c es | e0 e1].
    + left. simpl. auto.
    + left. simpl. auto.
    + exfalso. exact (H_BV_inv FEmpty iv t Hty).
    + exfalso. destruct (H_FV_inv FEmpty x t Hty) as [b0 [Hb Hs]].
      simpl in Hb. destruct Hb.
    + (* UnOp *)
      destruct (H_UnOp_inv FEmpty o e0 t Hty) as [Hp Hs].
      destruct (IH e0 ltac:(pose proof (expr_size_UnOp o e0); lia) (erase (intype o)) Hp)
        as [Hv | [e0' Hs0]].
      * destruct o. (* Not *)
        destruct (HasFJtype_value_bool FEmpty e0 Hv Hp) as [b0 Hb]. subst e0.
        right. exists (udelta Not (Bc b0) (isCpt_Not b0)).
        eapply EUnOp2 with (pf := isCpt_Not b0). exact Hv.
      * right. exists (ExpUnOp o e0'). eapply EUnOp1; eauto.
    + (* BinOp *)
      destruct (H_BinOp_inv FEmpty o e0 e1 t Hty) as [H1 [H2 Hs]].
      destruct (IH e0 ltac:(pose proof (expr_size_BinOp_l o e0 e1); lia)
                  (erase (fst (intype2 o))) H1) as [Hv1 | [e0' Hs1]].
      * destruct (IH e1 ltac:(pose proof (expr_size_BinOp_r o e0 e1); lia)
                    (erase (snd (intype2 o))) H2) as [Hv2 | [e1' Hs2]].
        -- (* both values *)
           destruct o.
           ++ destruct (HasFJtype_value_bool FEmpty e0 Hv1 H1) as [b1 Hb1]. subst e0.
              destruct (HasFJtype_value_bool FEmpty e1 Hv2 H2) as [b2 Hb2]. subst e1.
              right. exists (bdelta And (Bc b1) (Bc b2) (isCpt_And b1 b2)).
              eapply EBinOp3 with (pf := isCpt_And b1 b2); auto.
           ++ destruct (HasFJtype_value_bool FEmpty e0 Hv1 H1) as [b1 Hb1]. subst e0.
              destruct (HasFJtype_value_bool FEmpty e1 Hv2 H2) as [b2 Hb2]. subst e1.
              right. exists (bdelta Or (Bc b1) (Bc b2) (isCpt_Or b1 b2)).
              eapply EBinOp3 with (pf := isCpt_Or b1 b2); auto.
           ++ right. exists (bdelta Eq e0 e1 (isCpt_Eq e0 e1 Hv1 Hv2)).
              eapply EBinOp3 with (pf := isCpt_Eq e0 e1 Hv1 Hv2); auto.
        -- right. exists (ExpBinOp o e0 e1'). eapply EBinOp2; eauto.
      * right. exists (ExpBinOp o e0' e1). eapply EBinOp1; eauto.
    + (* Field *)
      destruct (H_Field_inv FEmpty e0 f t Hty) as (C & Fs & i & ff & HR & Hnth & Href & Htye & Hsub).
      destruct (IH e0 ltac:(pose proof (expr_size_Field e0 f); lia) (TNom (TClass C)) Htye)
        as [Hv | [e0' Hs]].
      * (* receiver is a value *)
        destruct (HasFJtype_value_class FEmpty e0 C Hv Htye) as [Cdyn [es [Heq HsubC]]].
        subst e0.
        destruct (H_New_inv FEmpty Cdyn es (TNom (TClass C)) Htye) as [Fdyn [HRdyn [Hf2 Hsub2]]].
        destruct (Reffields_prefix Cdyn C Fdyn Fs (subclass_reach _ _ HsubC) HRdyn HR)
          as [extra Hextra].
        subst Fdyn.
        assert (Hnthd : nth_error (Fs ++ extra) i = Some ff)
          by (eapply nth_error_app_prefix; eauto).
        assert (Hnf : nth_error (map erase (map ReffieldType (Fs ++ extra))) i
                      = Some (erase (ReffieldType ff))).
        { apply nth_error_map_Some. apply nth_error_map_Some. exact Hnthd. }
        assert (Hlt : i < length (map erase (map ReffieldType (Fs ++ extra))))
          by (apply nth_error_Some; rewrite Hnf; discriminate).
        assert (Hlen : length es = length (map erase (map ReffieldType (Fs ++ extra))))
          by (eapply Forall2_length; eauto).
        assert (Hlt' : i < length es) by lia.
        destruct (nth_error es i) as [ei|] eqn:Enth; [|apply nth_error_Some in Hlt'; rewrite Enth in Hlt'; exfalso; apply Hlt'; reflexivity].
        right. exists ei. rewrite <- Href.
        eapply Refc_Field with (Fs := Fs ++ extra) (fi := ff) (i := i).
        -- exact HRdyn.
        -- exact Hnthd.
        -- exact Enth.
        -- exact Hv.
      * right. exists (ExpFieldAccess e0' f). eapply RefRC_Field; eauto.
    + (* Invok *)
      destruct (H_Invok_inv FEmpty e0 m e1 t Hty) as
        [[C [ps [t1 [rt [Hmt [H1 [H2 Hs]]]]]]] |
         [I [ps [t1 [rt [Hmt [H1 [H2 Hs]]]]]]]].
      * destruct (IH e0 ltac:(pose proof (expr_size_Invoc_l e0 m e1); lia) (TNom (TClass C)) H1)
          as [Hv1 | [e0' Hs1]].
        -- destruct (IH e1 ltac:(pose proof (expr_size_Invoc_r e0 m e1); lia) (erase t1) H2)
             as [Hv2 | [e1' Hs2]].
           ++ (* call *)
              destruct (HasFJtype_value_class FEmpty e0 C Hv1 H1) as [Cdyn [es [Heq HsubC]]].
              subst e0.
              destruct (mtype_exists_mbody m C ps t1 rt Hmt) as [ebody Hbody].
              destruct (reach_mbody m Cdyn C ebody (subclass_reach _ _ HsubC) Hbody) as [eb' Hebody].
              right. exists (subBV_at 1 (ExpNew Cdyn es) (subBV e1 eb')).
              eapply Refc_Invok3; eauto.
           ++ right. exists (ExpMethodInvoc e0 m e1'). eapply Refc_Invok2; eauto.
        -- right. exists (ExpMethodInvoc e0' m e1). eapply Refc_Invok1; eauto.
      * destruct (IH e0 ltac:(pose proof (expr_size_Invoc_l e0 m e1); lia) (TNom (TInterface I)) H1)
          as [Hv1 | [e0' Hs1]].
        -- destruct (IH e1 ltac:(pose proof (expr_size_Invoc_r e0 m e1); lia) (erase t1) H2)
             as [Hv2 | [e1' Hs2]].
           ++ destruct (HasFJtype_value_iface FEmpty e0 I Hv1 H1) as [Cdyn [es [Heq HsubC]]].
              subst e0.
              destruct (SubClass_iface_target Cdyn I HsubC) as
                (E & Dd & Is & Fs & nd1 & Kd & Ms & nd2 & ii & HRc & HfE & HnthE).
              destruct (iface_implement E Dd Is Fs nd1 Kd Ms nd2 ii I HfE HnthE m rt ps t1 Hmt)
                as [Ds [D0 [ps' HmtE]]].
              destruct (mtype_exists_mbody m E ps' Ds D0 HmtE) as [ebody Hbody].
              destruct (reach_mbody m Cdyn E ebody HRc Hbody) as [eb' Hebody].
              right. exists (subBV_at 1 (ExpNew Cdyn es) (subBV e1 eb')).
              eapply Refc_Invok3; eauto.
           ++ right. exists (ExpMethodInvoc e0 m e1'). eapply Refc_Invok2; eauto.
        -- right. exists (ExpMethodInvoc e0' m e1). eapply Refc_Invok1; eauto.
    + (* New *)
      destruct (H_New_inv FEmpty c es t Hty) as [Fs [HR [Hf2 Hsub]]].
      assert (Hall : Forall (fun e => isValue e \/ exists e', Step e e') es).
      { apply Forall_forall. intros a Hin.
        destruct (In_nth_error _ _ _ Hin) as [i Hnth].
        destruct (Forall2_nth_error_l _ _ _ _ _ _ _ Hf2 Hnth) as [u [Hu Htya]].
        apply IH with (t:=u); auto.
        pose proof (expr_size_new_In c es a Hin).
        pose proof (expr_size_pos (ExpNew c es)). lia. }
      destruct (progress_args es Hall) as [Hval | (i & ei & ei' & Hnth & Hstep)].
      * left. apply isValue_new_intro. apply Forall_forall. auto.
      * right. exists (ExpNew c (replace es i ei')).
        assert (Hlt : i < length es) by (apply nth_error_Some; rewrite Hnth; discriminate).
        eapply RefRC_New_Arg with (ei := ei); eauto.
        -- apply nth_error_replace_same; auto.
        -- intros j Hj. symmetry. apply nth_error_replace_other; auto.
        -- symmetry. apply length_replace.
    + (* Let *)
      destruct (H_Let_inv FEmpty e0 e1 t Hty) as [b0 [b' [nms [Hx [Hb Hs]]]]].
      destruct (IH e0 ltac:(pose proof (expr_size_Let_l e0 e1); lia) b0 Hx)
        as [Hv | [e0' Hs0]].
      * right. exists (subBV e0 e1). eapply ELetV; exact Hv.
      * right. exists (ExpLet e0' e1). eapply ELet; eauto.
Qed.

Lemma fj_progress : forall e t, HasFJtype FEmpty e t -> isValue e \/ exists e', Step e e'.
Proof. intros. eapply fj_progress_aux; eauto. Qed.

Lemma implement_subtypes_erase : forall C m irt ips it Ds D0 ps',
    implement C m irt ips it -> mtype(m, C) = ps' ~> Ds ~> D0 ->
    FJSubtype (erase it) (erase Ds) /\ FJSubtype (erase D0) (erase irt).
Proof.
  intros C m irt ips it Ds D0 ps' Himp Hmt.
  destruct Himp as (Ds0 & D00 & ps0 & Hm0 & Hpre & Hpar & Hret).
  (* mtype determinism gives the types match *)
  destruct (mtype_det _ _ _ _ _ Hmt _ _ _ Hm0) as [Hps [Ht Hrt]].
  subst Ds0. subst D00.
  split.
  - unfold subtype_under in Hpar. specialize (Hpar 0).
    apply Subtype_erase in Hpar. rewrite !erase_openT in Hpar. exact Hpar.
  - unfold subtype_under2 in Hret. specialize (Hret 0 1).
    assert (H01 : 0 <> 1) by lia. specialize (Hret H01).
    apply Subtype_erase in Hret. rewrite !erase_openT in Hret. exact Hret.
Qed.



Lemma iface_implement_full : forall E D Is Fs nd1 K Ms nd2 i I,
    find E RefCT = Some (RefCDecl E D Is Fs nd1 K Ms nd2) ->
    nth_error Is i = Some I ->
    forall m irt ips it,
      mtypei(m, I) = ips ~> it ~> irt ->
      implement E m irt ips it.
Proof.
  intros E D Is Fs nd1 K Ms nd2 i I Hf Hn m irt ips it Hmti.
  pose proof (cok E D Fs nd1 K Is Ms nd2 Hf) as HC.
  inversion HC as [E0 D0 Fs0 ndf Is0 K0 Ms0 ndm fdecl HK HRf Hnd HForall HF Hfind HCI]; subst.
  assert (Himpl : Class_implemented E I) by (exact (HCI i I Hn)).
  inversion Himpl as [E1 I1 iMs ndi HfindI Hforall]; subst.
  inversion Hmti as [I2 Ms2 m2 rt2 t2 ps2 nd2' HfindI2 HfindM]; subst.
  assert (HMsi : Ms2 = iMs) by (rewrite HfindI in HfindI2; congruence).
  subst Ms2.
  exact (Hforall m irt ips it HfindM).
Qed.

Lemma substituted_body_typing : forall X D Is Fs nd1 K Ms nd2 rtd m psd td ebody,
    find X RefCT = Some (RefCDecl X D Is Fs nd1 K Ms nd2) ->
    find m Ms = Some (MDefn (MDecl rtd m psd td) ebody) ->
    forall v recv,
      isValue v -> isValue recv ->
      HasFJtype FEmpty v (erase td) ->
      HasFJtype FEmpty recv (TNom (TClass X)) ->
      HasFJtype FEmpty (subBV_at 1 recv (subBV v ebody)) (erase rtd).
Proof.
  intros X D Is Fs nd1 K Ms nd2 rtd m psd td ebody HfX HfindM v recv Hv Hvrecv Hvarg Hrecv.
  assert (HForall : Forall (MType_OK X) Ms)
    by (eapply cok_methods with (D:=D) (Is:=Is) (Fs:=Fs) (nd1:=nd1) (K:=K) (nd2:=nd2); exact HfX).
  pose proof (Forall_find MethodDefn MDefnRef (MType_OK X) m Ms _ HForall HfindM) as Hmok.
  destruct (MType_OK_body X rtd m psd td ebody Hmok) as [Hbodyty [Hfve _]].
  set (bad := fv (subBV_at 0 v ebody)).
  set (y := fresh bad). set (y' := S y).
  assert (Hyy' : y <> y') by lia.
  assert (Hybad : ~ Elem y bad) by (apply fresh_not_in).
  specialize (Hbodyty y y' Hyy').
  pose proof (Hastype_erase _ _ _ Hbodyty) as HbodyF.
  cbn [erase_env] in HbodyF.
  rewrite !erase_openT in HbodyF.
  assert (HargW : HasFJtype (FCons y (TNom (TClass X)) FEmpty) v (erase td))
    by (apply HasFJtype_weak; exact Hvarg).
  assert (Hnotin : ~ in_envFJ y' (FCons y (TNom (TClass X)) FEmpty)).
  { intros Hc. unfold in_envFJ in *. simpl in Hc.
    destruct Hc as [Hyy | Hc]; [exfalso; apply Hyy'; exact Hyy | destruct Hc]. }
  pose proof (HasFJtype_subst_head (FCons y (TNom (TClass X)) FEmpty)
                y' (erase td) (open_at 1 y (open_at 0 y' ebody)) (erase rtd) v
                Hnotin HbodyF HargW (isValue_open_at_inv v Hv)) as Hsubst1.
  assert (HrecvW : HasFJtype (FCons y (TNom (TClass X)) FEmpty) recv (TNom (TClass X)))
    by (apply HasFJtype_weak; exact Hrecv).
  pose proof (HasFJtype_subst_head FEmpty y (TNom (TClass X))
                (subFV y' v (open_at 1 y (open_at 0 y' ebody))) (erase rtd) recv
                (not_in_empty y) Hsubst1 Hrecv
                (isValue_open_at_inv recv Hvrecv)) as Hsubst2.
  assert (Heq : subFV y recv (subFV y' v (open_at 1 y (open_at 0 y' ebody)))
              = subBV_at 1 recv (subBV v ebody)).
  { rewrite (subFV_open_comm y' y v 1 (open_at 0 y' ebody)); auto.
    - rewrite (subFV_open_self y' v 0 ebody).
      2: { rewrite Hfve. apply not_in_empty. }
      rewrite (subFV_open_self y recv 1 (subBV_at 0 v ebody)).
      2: { intro Hc. apply Hybad. unfold bad. exact Hc. }
      reflexivity.
    - apply isValue_open_at_inv. exact Hv. }
  rewrite <- Heq. exact Hsubst2.
Qed.


Lemma Reffields_NoDup : forall C Fs, Reffields C Fs -> NoDup (refs Fs).
Proof.
  intros C Fs H. induction H as [| C0 D Is fs nd1 K Ms nd2 fs' Hf HR IH Hnd].
  - constructor.
  - exact Hnd.
Qed.

Lemma NoDup_refs_In : forall (l : [RefFieldDecl]) x y,
    NoDup (refs l) -> In x l -> In y l -> ref x = ref y -> x = y.
Proof.
  intros l. induction l as [|a l IH]; intros x y Hnd Hx Hy Href.
  - destruct Hx.
  - destruct Hx as [-> | Hx]; destruct Hy as [-> | Hy].
    + reflexivity.
    + exfalso. inversion Hnd as [|? ? Hnot Hnd']. subst.
      apply Hnot.
      assert (Hin : In (ref y) (refs l)) by (apply in_map; exact Hy).
      rewrite <- Href in Hin. exact Hin.
    + exfalso. inversion Hnd as [|? ? Hnot Hnd']. subst.
      apply Hnot.
      assert (Hin : In (ref x) (refs l)) by (apply in_map; exact Hx).
      rewrite Href in Hin. exact Hin.
    + apply IH with (y:=y); auto.
      inversion Hnd as [|? ? Hnot Hnd']. subst. exact Hnd'.
Qed.

Lemma nth_error_ext : forall (A : Type) (l1 l2 : [A]),
    length l1 = length l2 ->
    (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 Hlen Hn.
  - destruct l2; [reflexivity | simpl in Hlen; discriminate].
  - destruct l2 as [|b l2]; [simpl in Hlen; discriminate |].
    assert (Ha : a = b). { specialize (Hn 0). simpl in Hn. injection Hn. auto. }
    subst b. f_equal. apply IH.
    + simpl in Hlen. lia.
    + intros i. specialize (Hn (S i)). simpl in Hn. exact Hn.
Qed.

(* ============================================================ *)
(* Type preservation                                             *)
(* ============================================================ *)

Lemma fj_preservation : forall e e' t,
    Step e e' -> HasFJtype FEmpty e t -> HasFJtype FEmpty e' t.
Proof.
  intros e e' t Hs. revert t. induction Hs as
    [ c e0 e0' Hs0 IH0
    | c w pf Hv
    | c e0 e0' e1 Hs0 IH0
    | c e0 e0' v Hv Hs0 IH0
    | c v1 v2 pf Hv1 Hv2
    | m e1 e2 e1' Hs0 IH0
    | m v e0 e0' Hv Hs0 IH0
    | C ebody m v es Hbody Hv Hvnew
    | C Fs es fi ei i HR HnthF HnthE Hv
    | e0 e0' f Hs0 IH0
    | C ei' es es' ei i Hs0 IH0 HnthA HnthB Hsame Hlen
    | e_x e_x' e Hs0 IH0
    | v e Hv ]; intros t Hty.
  - (* EUnOp1 *)
    destruct (H_UnOp_inv FEmpty c e0 t Hty) as [Hprem Hsub].
    eapply FTSub with (s := erase (ty' c)).
    + eapply FTUnOP. apply IH0. exact Hprem.
    + exact Hsub.
  - (* EUnOp2 *)
    destruct (H_UnOp_inv FEmpty c w t Hty) as [Hprem Hsub].
    destruct pf; destruct b;
      (eapply FTSub with (s := TBool); [simpl; apply FTBC | exact Hsub]).
  - (* EBinOp1 *)
    destruct (H_BinOp_inv FEmpty c e0 e1 t Hty) as [H1 [H2 Hsub]].
    eapply FTSub with (s := erase (ty'2 c)).
    + eapply FTBinOP. apply IH0; exact H1. exact H2.
    + exact Hsub.
  - (* EBinOp2 *)
    destruct (H_BinOp_inv FEmpty c v e0 t Hty) as [H1 [H2 Hsub]].
    eapply FTSub with (s := erase (ty'2 c)).
    + eapply FTBinOP. exact H1. apply IH0; exact H2.
    + exact Hsub.
  - (* EBinOp3 *)
    destruct (H_BinOp_inv FEmpty c v1 v2 t Hty) as [H1 [H2 Hsub]].
    destruct c; destruct pf; simpl;
      (eapply FTSub with (s := TBool); [apply FTBC | exact Hsub]).
  - (* Refc_Invok1 *)
    destruct (H_Invok_inv FEmpty e1 m e2 t Hty) as
      [[Cst [pst [tt [rtt [Hmt [H1 [H2 Hsub]]]]]]] |
       [Ist [pst [tt [rtt [Hmt [H1 [H2 Hsub]]]]]]]].
    + eapply FTSub with (s := erase rtt).
      * eapply FTInvok; [ apply IH0; exact H1 | exact Hmt | exact H2 ].
      * exact Hsub.
    + eapply FTSub with (s := erase rtt).
      * eapply FTInvokI; [ apply IH0; exact H1 | exact Hmt | exact H2 ].
      * exact Hsub.
  - (* Refc_Invok2 *)
    destruct (H_Invok_inv FEmpty v m e0 t Hty) as
      [[Cst [pst [tt [rtt [Hmt [H1 [H2 Hsub]]]]]]] |
       [Ist [pst [tt [rtt [Hmt [H1 [H2 Hsub]]]]]]]].
    + eapply FTSub with (s := erase rtt).
      * eapply FTInvok; [ exact H1 | exact Hmt | apply IH0; exact H2 ].
      * exact Hsub.
    + eapply FTSub with (s := erase rtt).
      * eapply FTInvokI; [ exact H1 | exact Hmt | apply IH0; exact H2 ].
      * exact Hsub.
  - (* Refc_Invok3 *)
    destruct (H_Invok_inv FEmpty (ExpNew C es) m v t Hty) as
      [[Cst [pst [tt [rtt [Hmt [H1 [H2 Hsub]]]]]]] |
       [Ist [pst [tt [rtt [Hmt [H1 [H2 Hsub]]]]]]]].
    + (* class invocation *)
      destruct (H_New_inv FEmpty C es (TNom (TClass Cst)) H1) as
        [Fdyn [HRdyn [Hfargs Hsubrecv]]].
      destruct (FJSubtype_class_inv (TNom (TClass C)) Cst Hsubrecv) as [C' [HC' Hsc]].
      inversion HC'; subst C'.
      destruct (m_body_decl_mtype m C ebody Hbody) as
        (X & Dd & Isd & Fsd & Kd & Ms & nd1 & nd2 & psd & td & rtd & HRC & HfX & HfindM & HmtC).
      destruct (mtype_chain_sub C Cst m psd td rtd (subclass_reach _ _ Hsc) HmtC pst tt rtt Hmt)
        as [Hpar Hret].
      assert (Harg : HasFJtype FEmpty v (erase td))
        by (eapply FTSub with (s := erase tt); [exact H2 | exact Hpar]).
      assert (HrecvC : HasFJtype FEmpty (ExpNew C es) (TNom (TClass C))).
      { eapply FTNew with (Fs:=Fdyn) (Us:=map erase (map ReffieldType Fdyn))
                            (fs:=map ReffieldName Fdyn).
        - reflexivity. - reflexivity. - exact HRdyn. - exact Hfargs. }
      assert (Hrecv : HasFJtype FEmpty (ExpNew C es) (TNom (TClass X))).
      { eapply FTSub with (s := TNom (TClass C));
          [exact HrecvC | apply SubBClass; apply reach_subclass; exact HRC]. }
      eapply FTSub with (s := erase rtd).
      * eapply substituted_body_typing
          with (X:=X) (D:=Dd) (Is:=Isd) (Fs:=Fsd) (nd1:=nd1) (K:=Kd) (Ms:=Ms) (nd2:=nd2)
               (rtd:=rtd) (m:=m) (psd:=psd) (td:=td) (ebody:=ebody).
        -- exact HfX.
        -- exact HfindM.
        -- exact Hv.
        -- exact Hvnew.
        -- exact Harg.
        -- exact Hrecv.
      * eapply FJSubtype_trans; [exact Hret | exact Hsub].
    + (* interface invocation *)
      destruct (H_New_inv FEmpty C es (TNom (TInterface Ist)) H1) as
        [Fdyn [HRdyn [Hfargs Hsubrecv]]].
      destruct (FJSubtype_nom_inv (TNom (TClass C)) (TInterface Ist) Hsubrecv) as [Y [HY Hsc]].
      inversion HY; subst Y.
      destruct (SubClass_iface_target C Ist Hsc) as
        (E & Dd & Isd & Fsd & nd1 & Kd & Ms & nd2 & ii & HRC & HfE & HnthE).
      destruct (iface_implement_full E Dd Isd Fsd nd1 Kd Ms nd2 ii Ist HfE HnthE m rtt pst tt Hmt)
        as (Ds & D0 & ps' & HmtE & Hpred & HparSub & HretSub).
      assert (HparI : FJSubtype (erase tt) (erase Ds)).
      { unfold subtype_under in HparSub. specialize (HparSub 0).
        apply Subtype_erase in HparSub. rewrite !erase_openT in HparSub. exact HparSub. }
      assert (HretI : FJSubtype (erase D0) (erase rtt)).
      { unfold subtype_under2 in HretSub. specialize (HretSub 0 1).
        assert (H01 : 0 <> 1) by lia. specialize (HretSub H01).
        apply Subtype_erase in HretSub. rewrite !erase_openT in HretSub. exact HretSub. }
      destruct (m_body_decl_mtype m C ebody Hbody) as
        (X & Dd2 & Isd2 & Fsd2 & Kd2 & Ms2 & nd12 & nd22 & psd & td & rtd & HRC2 & HfX & HfindM & HmtC).
      destruct (mtype_chain_sub C E m psd td rtd HRC HmtC ps' Ds D0 HmtE) as [Hpar2 Hret2].
      assert (Harg : HasFJtype FEmpty v (erase td)).
      { eapply FTSub with (s := erase Ds);
          [eapply FTSub with (s := erase tt); [exact H2 | exact HparI] | exact Hpar2]. }
      assert (HrecvC : HasFJtype FEmpty (ExpNew C es) (TNom (TClass C))).
      { eapply FTNew with (Fs:=Fdyn) (Us:=map erase (map ReffieldType Fdyn))
                            (fs:=map ReffieldName Fdyn).
        - reflexivity. - reflexivity. - exact HRdyn. - exact Hfargs. }
      assert (Hrecv : HasFJtype FEmpty (ExpNew C es) (TNom (TClass X))).
      { eapply FTSub with (s := TNom (TClass C));
          [exact HrecvC | apply SubBClass; apply reach_subclass; exact HRC2]. }
      assert (Hsubtot : FJSubtype (erase rtd) t).
      { eapply FJSubtype_trans;
          [exact Hret2 | eapply FJSubtype_trans; [exact HretI | exact Hsub]]. }
      eapply FTSub with (s := erase rtd).
      * eapply substituted_body_typing
          with (X:=X) (D:=Dd2) (Is:=Isd2) (Fs:=Fsd2) (nd1:=nd12) (K:=Kd2) (Ms:=Ms2) (nd2:=nd22)
               (rtd:=rtd) (m:=m) (psd:=psd) (td:=td) (ebody:=ebody).
        -- exact HfX.
        -- exact HfindM.
        -- exact Hv.
        -- exact Hvnew.
        -- exact Harg.
        -- exact Hrecv.
      * exact Hsubtot.
  - (* Refc_Field *)
    destruct (H_Field_inv FEmpty (ExpNew C es) (ref fi) t Hty) as
      (Cst & Fs0 & ii & ff & HR0 & Hnth0 & Href0 & Htye & Hsub).
    destruct (H_New_inv FEmpty C es (TNom (TClass Cst)) Htye) as
      [Fdyn [HRdyn [Hfargs Hsubrecv]]].
    destruct (FJSubtype_class_inv (TNom (TClass C)) Cst Hsubrecv) as [C' [HC' Hsc]].
    inversion HC'; subst C'.
    assert (HFdyn : Fdyn = Fs) by (eapply Reffields_fun; eauto).
    subst Fdyn.
    destruct (Reffields_prefix C Cst Fs Fs0 (subclass_reach _ _ Hsc) HR HR0) as [extra Hextra].
    subst Fs.
    assert (Hinff : In ff (Fs0 ++ extra)).
    { apply in_or_app. left. eapply nth_error_In. exact Hnth0. }
    assert (HinFi : In fi (Fs0 ++ extra)).
    { eapply nth_error_In. exact HnthF. }
    assert (HrefFi : ref fi = ref ff) by (symmetry; exact Href0).
    assert (HNoDup : NoDup (refs (Fs0 ++ extra))) by (exact (Reffields_NoDup C (Fs0 ++ extra) HR)).
    assert (Hfieq : fi = ff)
      by (eapply NoDup_refs_In; [exact HNoDup | exact HinFi | exact Hinff | exact HrefFi]).
    subst fi.
    assert (Hnf : nth_error (map erase (map ReffieldType (Fs0 ++ extra))) i
                 = Some (erase (ReffieldType ff))).
    { apply nth_error_map_Some. apply nth_error_map_Some. exact HnthF. }
    assert (Htyei : HasFJtype FEmpty ei (erase (ReffieldType ff)))
      by (eapply Forall2_nth; eauto).
    eapply FTSub with (s := erase (ReffieldType ff)).
    + exact Htyei.
    + exact Hsub.
  - (* RefRC_Field *)
    destruct (H_Field_inv FEmpty e0 f t Hty) as
      (Cst & Fs0 & ii & ff & HR & HnthF & Href & Htye & Hsub).
    eapply FTSub with (s := erase (ReffieldType ff)).
    + eapply FTField; [ apply IH0; exact Htye | exact HR | exact HnthF | exact Href | reflexivity ].
    + exact Hsub.
  - (* RefRC_New_Arg *)
    destruct (H_New_inv FEmpty C es t Hty) as [Fs0 [HR [Hfargs Hsub]]].
    destruct (Forall2_nth_error_l _ _ _ _ _ _ _ Hfargs HnthA) as [u [Hu Htyei]].
    assert (Htyei' : HasFJtype FEmpty ei' u) by (apply IH0; exact Htyei).
    assert (Hfargs' : Forall2 (HasFJtype FEmpty) (replace es i ei')
                     (map erase (map ReffieldType Fs0)))
      by (eapply Forall2_replace_l; eauto).
    assert (Hes' : es' = replace es i ei').
    { apply nth_error_ext.
      - rewrite length_replace. symmetry. exact Hlen.
      - intros j. destruct (PeanoNat.Nat.eqb j i) eqn:Ej.
        + apply PeanoNat.Nat.eqb_eq in Ej. subst j.
          rewrite HnthB. symmetry. apply nth_error_replace_same.
          apply nth_error_Some. rewrite HnthA. discriminate.
        + apply PeanoNat.Nat.eqb_neq in Ej.
          rewrite (nth_error_replace_other _ _ _ _ _ Ej).
          symmetry. apply Hsame. auto. }
    subst es'.
    eapply FTSub with (s := TNom (TClass C)).
    + eapply FTNew with (Fs:=Fs0) (Us:=map erase (map ReffieldType Fs0))
                          (fs:=map ReffieldName Fs0).
      * reflexivity. * reflexivity. * exact HR. * exact Hfargs'.
    + exact Hsub.
  - (* ELet *)
    destruct (H_Let_inv FEmpty e_x e t Hty) as [b [b' [nms [Hx [Hbody Hsub]]]]].
    eapply FTSub with (s := b').
    + eapply FTLet with (nms := nms).
      * apply IH0. exact Hx.
      * exact Hbody.
    + exact Hsub.
  - (* ELetV *)
    destruct (H_Let_inv FEmpty v e t Hty) as [b [b' [nms [Hvty [Hbody Hsub]]]]].
    set (y := fresh (union nms (fv e))).
    assert (Hy : ~ Elem y (union nms (fv e))) by (apply fresh_not_in).
    assert (Hy_nms : ~ Elem y nms) by (apply not_in_union_l in Hy; auto).
    assert (Hy_fv : ~ Elem y (fv e)) by (apply not_in_union_r in Hy; auto).
    pose proof (HasFJtype_subst_head FEmpty y b (unbind y e) b' v
                  (not_in_empty y) (Hbody y Hy_nms) Hvty
                  (isValue_open_at_inv v Hv)) as Hsubst.
    change (HasFJtype FEmpty (subFV y v (open_at 0 y e)) b') in Hsubst.
    rewrite (subFV_open_self y v 0 e Hy_fv) in Hsubst.
    eapply FTSub with (s := b').
    + exact Hsubst.
    + exact Hsub.
Qed.

Lemma fj_soundness : forall e e' t,
    EvalsTo e e' -> HasFJtype FEmpty e t ->
    isValue e' \/ exists e'', Step e' e''.
Proof.
  intros e e' t Hev. induction Hev as [e0 | e1 e2 e3 Hs Hev IH]; intros Hty.
  - eapply fj_progress; exact Hty.
  - apply IH. apply fj_preservation with (e := e1); auto.
Qed.

Theorem type_soundness : forall (e e':expr) (t:type),
    EvalsTo e e' -> Hastype Empty e t -> isValue e' \/  exists e'', Step e' e''.
Proof.
  intros e e' t Hev Hty.
  eapply fj_soundness with (e := e) (e' := e') (t := erase t).
  - exact Hev.
  - change (HasFJtype FEmpty e (erase t)).
    exact (Hastype_erase Empty e t Hty).
Qed.
