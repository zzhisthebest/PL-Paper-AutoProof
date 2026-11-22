From Qual Require Import Qualitative_ott.
From mathcomp Require Import ssreflect ssrbool.
From Stdlib Require Import Arith Lia Compare_dec.
Require Import Metalib.Metatheory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope order_scope.
Local Close Scope bool_scope.

Fixpoint wf (k:nat) (t:tm) : Prop :=
  match t with
  | a_TyUnit => True
  | a_TmUnit => True
  | a_Pi _ A B => wf k A /\ wf (S k) B
  | a_Abs _ A b => wf k A /\ wf (S k) b
  | a_App a _ b => wf k a /\ wf k b
  | a_Type _ => True
  | a_Var_b n => Nat.lt n k
  | a_Var_f _ => True
  | a_CEq _ a b _ A => wf k a /\ wf k b /\ wf k A
  | a_Refl => True
  | a_Transp a b => wf k a /\ wf k b
  | a_T _ A => wf k A
  | a_Box _ a => wf k a
  | a_Unbox _ a => wf k a
  | a_SSigma _ A B => wf k A /\ wf (S k) B
  | a_SPair a _ b => wf k a /\ wf k b
  | a_Proj1 _ a => wf k a
  | a_Proj2 _ a => wf k a
  | a_Bool => True
  | a_True => True
  | a_False => True
  | a_If a b0 b1 => wf k a /\ wf k b0 /\ wf k b1
  end.

(* replace index k of t by a variable *)
Lemma wf_open_var : forall t k x,
  wf (S k) t <-> wf k (open_tm_wrt_tm_rec k (a_Var_f x) t).
Proof.
  intros t. induction t; intros k vv; simpl.
  - tauto. - tauto.
  - rewrite (IHt1 k vv) (IHt2 (S k) vv); tauto.
  - rewrite (IHt1 k vv) (IHt2 (S k) vv); tauto.
  - rewrite (IHt1 k vv) (IHt2 k vv); tauto.
  - tauto.
  - cbn [open_tm_wrt_tm_rec].
  destruct (lt_eq_lt_dec n k) as [[H|H]|H].
  + cbn [wf]. split; intros _; lia.
  + cbn [wf]. split; intros _; lia.
  + cbn [wf]. split.
    * intros H1. exfalso. lia.
    * intros H1. exfalso. lia.
  - tauto.
  - rewrite (IHt1 k vv) (IHt2 k vv) (IHt3 k vv); tauto.
  - tauto.
  - rewrite (IHt1 k vv) (IHt2 k vv); tauto.
  - rewrite (IHt k vv); tauto.
  - rewrite (IHt k vv); tauto.
  - rewrite (IHt k vv); tauto.
  - rewrite (IHt1 k vv) (IHt2 (S k) vv); tauto.
  - rewrite (IHt1 k vv) (IHt2 k vv); tauto.
  - rewrite (IHt k vv); tauto.
  - rewrite (IHt k vv); tauto.
  - tauto. - tauto. - tauto.
  - rewrite (IHt1 k vv) (IHt2 k vv) (IHt3 k vv); tauto.
Qed.

Fixpoint tm_size (t:tm) : nat :=
  match t with
  | a_TyUnit | a_TmUnit | a_Type _ | a_Var_b _ | a_Var_f _ | a_Refl
  | a_Bool | a_True | a_False => 1
  | a_Pi _ A B => S (tm_size A + tm_size B)
  | a_Abs _ A b => S (tm_size A + tm_size b)
  | a_App a _ b => S (tm_size a + tm_size b)
  | a_CEq _ a b _ A => S (tm_size a + tm_size b + tm_size A)
  | a_Transp a b => S (tm_size a + tm_size b)
  | a_T _ A => S (tm_size A)
  | a_Box _ a => S (tm_size a)
  | a_Unbox _ a => S (tm_size a)
  | a_SSigma _ A B => S (tm_size A + tm_size B)
  | a_SPair a _ b => S (tm_size a + tm_size b)
  | a_Proj1 _ a => S (tm_size a)
  | a_Proj2 _ a => S (tm_size a)
  | a_If a b0 b1 => S (tm_size a + tm_size b0 + tm_size b1)
  end.

Lemma tm_size_open_var : forall t k x,
  tm_size (open_tm_wrt_tm_rec k (a_Var_f x) t) = tm_size t.
Proof.
  intros t. induction t; intros k vv; simpl.
  - reflexivity. - reflexivity.
  - rewrite (IHt1 k vv) (IHt2 (S k) vv); reflexivity.
  - rewrite (IHt1 k vv) (IHt2 (S k) vv); reflexivity.
  - rewrite (IHt1 k vv) (IHt2 k vv); reflexivity.
  - reflexivity.
  - cbn [open_tm_wrt_tm_rec]. destruct (lt_eq_lt_dec n k) as [[H|H]|H]; cbn [tm_size]; reflexivity.
  - reflexivity.
  - rewrite (IHt1 k vv) (IHt2 k vv) (IHt3 k vv); reflexivity.
  - reflexivity.
  - rewrite (IHt1 k vv) (IHt2 k vv); reflexivity.
  - rewrite (IHt k vv); reflexivity.
  - rewrite (IHt k vv); reflexivity.
  - rewrite (IHt k vv); reflexivity.
  - rewrite (IHt1 k vv) (IHt2 (S k) vv); reflexivity.
  - rewrite (IHt1 k vv) (IHt2 k vv); reflexivity.
  - rewrite (IHt k vv); reflexivity.
  - rewrite (IHt k vv); reflexivity.
  - reflexivity. - reflexivity. - reflexivity.
  - rewrite (IHt1 k vv) (IHt2 k vv) (IHt3 k vv); reflexivity.
Qed.

Lemma wf_lc_aux : forall n t, Nat.le (tm_size t) n -> wf 0 t -> lc_tm t.
Proof.
  intros n. induction n as [| n IH]; intros t Hle Hwf.
  - destruct t; simpl in Hle; lia.
  - destruct t; simpl in *.
    + constructor. + constructor.
    + (* Pi *)
      destruct Hwf as [HA HB]. apply lc_a_Pi.
      * apply IH; [ simpl in Hle; lia | exact HA ].
      * intro x. apply (IH (open_tm_wrt_tm t2 (a_Var_f x))).
        -- rewrite tm_size_open_var. simpl in Hle. lia.
        -- apply (proj1 (wf_open_var t2 0 x)). exact HB.
    + (* Abs *)
      destruct Hwf as [HA HB]. apply lc_a_Abs.
      * apply IH; [ simpl in Hle; lia | exact HA ].
      * intro x. apply (IH (open_tm_wrt_tm t2 (a_Var_f x))).
        -- rewrite tm_size_open_var. simpl in Hle. lia.
        -- apply (proj1 (wf_open_var t2 0 x)). exact HB.
    + (* App *) destruct Hwf as [Ha Hb]. constructor.
      * apply IH; [ simpl in Hle; lia | exact Ha ].
      * apply IH; [ simpl in Hle; lia | exact Hb ].
    + constructor.
    + (* Var_b *) simpl in Hwf. lia.
    + constructor.
    + (* CEq *) destruct Hwf as [Ha [Hb Hc]]. econstructor.
      * apply IH; [ simpl in Hle; lia | exact Ha ].
      * apply IH; [ simpl in Hle; lia | exact Hb ].
      * apply IH; [ simpl in Hle; lia | exact Hc ].
    + constructor.
    + (* Transp *) destruct Hwf as [Ha Hb]. constructor.
      * apply IH; [ simpl in Hle; lia | exact Ha ].
      * apply IH; [ simpl in Hle; lia | exact Hb ].
    + (* T *) constructor.
      apply IH; [ simpl in Hle; lia | exact Hwf ].
    + (* Box *) constructor.
      apply IH; [ simpl in Hle; lia | exact Hwf ].
    + (* Unbox *) constructor.
      apply IH; [ simpl in Hle; lia | exact Hwf ].
    + (* SSigma *)
      destruct Hwf as [HA HB]. apply lc_a_SSigma.
      * apply IH; [ simpl in Hle; lia | exact HA ].
      * intro x. apply (IH (open_tm_wrt_tm t2 (a_Var_f x))).
        -- rewrite tm_size_open_var. simpl in Hle. lia.
        -- apply (proj1 (wf_open_var t2 0 x)). exact HB.
    + (* SPair *) destruct Hwf as [Ha Hb]. constructor.
      * apply IH; [ simpl in Hle; lia | exact Ha ].
      * apply IH; [ simpl in Hle; lia | exact Hb ].
    + (* Proj1 *) constructor.
      apply IH; [ simpl in Hle; lia | exact Hwf ].
    + (* Proj2 *) constructor.
      apply IH; [ simpl in Hle; lia | exact Hwf ].
    + constructor. + constructor. + constructor.
    + (* If *) destruct Hwf as [Ha [Hb Hc]]. econstructor.
      * apply IH; [ simpl in Hle; lia | exact Ha ].
      * apply IH; [ simpl in Hle; lia | exact Hb ].
      * apply IH; [ simpl in Hle; lia | exact Hc ].
Qed.

Lemma wf_lc : forall t, wf 0 t -> lc_tm t.
Proof. intros t H. apply wf_lc_aux with (n := tm_size t). apply Nat.le_refl. exact H. Qed.

Lemma lc_wf : forall t, lc_tm t -> wf 0 t.
Proof.
  intros t H. induction H using lc_tm_ind; simpl; try tauto.
  - (* Pi *) split; [ exact IHlc_tm | ].
    apply (proj2 (wf_open_var B 0 (Atom.fresh nil))).
    apply (H1 (Atom.fresh nil)).
  - (* Abs *) split; [ exact IHlc_tm | ].
    apply (proj2 (wf_open_var a 0 (Atom.fresh nil))).
    apply (H1 (Atom.fresh nil)).
  - (* SSigma *) split; [ exact IHlc_tm | ].
    apply (proj2 (wf_open_var B 0 (Atom.fresh nil))).
    apply (H1 (Atom.fresh nil)).
Qed.

Lemma lc_wf_iff : forall t, lc_tm t <-> wf 0 t.
Proof. intro t; split; [apply lc_wf | apply wf_lc]. Qed.

(* ============  Regularity: well-typed terms are locally closed  ============ *)

Lemma typing_wf : forall W psi a A, Typing W psi a A -> wf 0 a.
Proof.
  intros W psi a A H. induction H; simpl; try tauto.
  - (* T_Pi *) split; [ exact IHTyping | ].
    destruct (atom_fresh L) as [x Hx].
    apply (proj2 (wf_open_var B 0 x)). apply (H1 x Hx).
  - (* T_Abs *) split.
    + simpl in IHTyping. exact (proj1 IHTyping).
    + destruct (atom_fresh L) as [x Hx].
      apply (proj2 (wf_open_var b 0 x)). apply (H0 x Hx).
  - (* T_SSigma *) split; [ exact IHTyping | ].
    destruct (atom_fresh L) as [x Hx].
    apply (proj2 (wf_open_var B 0 x)). apply (H1 x Hx).
Qed.

Lemma typing_lc : forall W psi a A, Typing W psi a A -> lc_tm a.
Proof.
  intros W psi a A H. apply wf_lc.
  exact (typing_wf (W:=W) (psi:=psi) (a:=a) (A:=A) H).
Qed.


Lemma wf_mono : forall t k k', Nat.le k k' -> wf k t -> wf k' t.
Proof.
  intros t. induction t as [| |psi A IHA Btx IHB|psi A IHA b IHb|a0 IHa psi b IHb
                 |s|n|xx|psi a0 IHa b IHb psi0 A IHA| |a0 IHa b IHb|psi A IHA
                 |psi a0 IHa|psi a0 IHa|psi A IHA Btx IHB|a0 IHa psi b IHb|psi a0 IHa
                 |psi a0 IHa| | | |a0 IHa b0 IHb0 b1 IHb1];
  intros k k' Hle HB; simpl in *.
  - exact I. - exact I.
  - split. exact (IHA k k' Hle (proj1 HB)).
    exact (IHB (S k) (S k') (ltac:(lia)) (proj2 HB)).
  - split. exact (IHA k k' Hle (proj1 HB)).
    exact (IHb (S k) (S k') (ltac:(lia)) (proj2 HB)).
  - split. exact (IHa k k' Hle (proj1 HB)).
    exact (IHb k k' Hle (proj2 HB)).
  - exact I.
  - lia.
  - exact I.
  - split. exact (IHa k k' Hle (proj1 HB)).
    split. exact (IHb k k' Hle (proj1 (proj2 HB))).
    exact (IHA k k' Hle (proj2 (proj2 HB))).
  - exact I.
  - split. exact (IHa k k' Hle (proj1 HB)).
    exact (IHb k k' Hle (proj2 HB)).
  - exact (IHA k k' Hle HB).
  - exact (IHa k k' Hle HB).
  - exact (IHa k k' Hle HB).
  - split. exact (IHA k k' Hle (proj1 HB)).
    exact (IHB (S k) (S k') (ltac:(lia)) (proj2 HB)).
  - split. exact (IHa k k' Hle (proj1 HB)).
    exact (IHb k k' Hle (proj2 HB)).
  - exact (IHa k k' Hle HB).
  - exact (IHa k k' Hle HB).
  - exact I. - exact I. - exact I.
  - split. exact (IHa k k' Hle (proj1 HB)).
    split. exact (IHb0 k k' Hle (proj1 (proj2 HB))).
    exact (IHb1 k k' Hle (proj2 (proj2 HB))).
Qed.

Lemma le_Sn : forall n, Nat.le n (S n).
Proof. intros. lia. Qed.

(* opening a well-scoped term with a well-scoped term *)
Lemma wf_open_term : forall B k a,
  wf (S k) B -> wf k a -> wf k (open_tm_wrt_tm_rec k a B).
Proof.
  intros B.
  induction B as [| |psi A IHA Btx IHB|psi A IHA b IHb|a0 IHa psi b IHb
                 |s|n|xx|psi a0 IHa b IHb psi0 A IHA| |a0 IHa b IHb|psi A IHA
                 |psi a0 IHa|psi a0 IHa|psi A IHA Btx IHB|a0 IHa psi b IHb|psi a0 IHa
                 |psi a0 IHa| | | |a0 IHa b0 IHb0 b1 IHb1];
  intros k av HB Ha; simpl in *.
  - exact I. - exact I.
  - split. exact (@IHA k av (proj1 HB) Ha).
    exact (@IHB (S k) av (proj2 HB) (@wf_mono av k (S k) (le_Sn k) Ha)).
  - split. exact (@IHA k av (proj1 HB) Ha).
    exact (@IHb (S k) av (proj2 HB) (@wf_mono av k (S k) (le_Sn k) Ha)).
  - split. exact (@IHa k av (proj1 HB) Ha).
    exact (@IHb k av (proj2 HB) Ha).
  - exact I.
  - cbn [open_tm_wrt_tm_rec]. destruct (lt_eq_lt_dec n k) as [[H|H]|H]; cbn [wf].
    + exact H.
    + exact Ha.
    + exfalso. lia.
  - exact I.
  - split. exact (@IHa k av (proj1 HB) Ha).
    split. exact (@IHb k av (proj1 (proj2 HB)) Ha).
    exact (@IHA k av (proj2 (proj2 HB)) Ha).
  - exact I.
  - split. exact (@IHa k av (proj1 HB) Ha).
    exact (@IHb k av (proj2 HB) Ha).
  - exact (@IHA k av HB Ha).
  - exact (@IHa k av HB Ha).
  - exact (@IHa k av HB Ha).
  - split. exact (@IHA k av (proj1 HB) Ha).
    exact (@IHB (S k) av (proj2 HB) (@wf_mono av k (S k) (le_Sn k) Ha)).
  - split. exact (@IHa k av (proj1 HB) Ha).
    exact (@IHb k av (proj2 HB) Ha).
  - exact (@IHa k av HB Ha).
  - exact (@IHa k av HB Ha).
  - exact I. - exact I. - exact I.
  - split. exact (@IHa k av (proj1 HB) Ha).
    split. exact (@IHb0 k av (proj1 (proj2 HB)) Ha).
    exact (@IHb1 k av (proj2 (proj2 HB)) Ha).
Qed.


Lemma Ctx_uniq : forall W, Ctx W -> uniq W.
Proof.
  intros W H. induction H.
  - apply EnvImpl.uniq_nil.
  - apply EnvImpl.uniq_push; assumption.
Qed.

Lemma Ctx_wf_types : forall W, Ctx W -> forall x g A, binds x (g,A) W -> wf 0 A.
Proof.
  intros W H. induction H; intros y g B Hb.
  - inversion Hb.
  - change (binds y (g,B) ((x, (psi0,A)) :: W)) in Hb.
    simpl in Hb. destruct Hb as [E|Hb].
    + inversion E; subst. apply typing_wf in H0. exact H0.
    + exact (@IHCtx y g B Hb).
Qed.

Lemma typing_wf_type : forall W psi a A, Typing W psi a A -> wf 0 A.
Proof.
  intros W psi a A H. induction H; simpl in *.
  - exact I.                                              (* T_Type *)
  - exact (@Ctx_wf_types W H x psi0 A H1).                (* T_Var *)
  - exact I.                                              (* T_Pi *)
  - (* T_Abs *)
    have HP := typing_wf H1. simpl in HP. split.
    + exact (proj1 HP).
    + destruct (atom_fresh L) as [y Hy].
      apply (proj2 (wf_open_var B 0 y)). apply (H0 y Hy).
  - exact (@wf_open_term B 0 a (proj2 IHTyping1) (typing_wf H0)).  (* T_App *)
  - exact (typing_wf H0).                                 (* T_Conv *)
  - exact (typing_wf H).                                  (* T_Refl *)
  - exact I.                                              (* T_CEq *)
  - (* T_Transp *)
    have HB1 : wf 1 B.
    { destruct (atom_fresh L) as [y Hy].
      apply (proj2 (wf_open_var B 0 y)). apply (typing_wf (H y Hy)). }
    exact (@wf_open_term B 0 a1 HB1 (proj1 (proj2 IHTyping1))).
  - exact I.                                              (* T_T *)
  - exact IHTyping1.                                      (* T_Box *)
  - exact IHTyping.                                       (* T_Unbox *)
  - exact I.                                              (* T_SSigma *)
  - exact (typing_wf H).                                  (* T_SPair *)
  - exact (proj1 IHTyping).                               (* T_Proj1 *)
  - exact (@wf_open_term B 0 (a_Proj1 psi0 a) (proj2 IHTyping1) (typing_wf H0)). (* T_Proj2 *)
  - exact I.                                              (* T_TyUnit *)
  - exact I.                                              (* T_TmUnit *)
  - exact I.                                              (* T_Bool *)
  - exact I.                                              (* T_True *)
  - exact I.                                              (* T_False *)
  - exact IHTyping2.                                      (* T_If *)
Qed.

(* ============  Opening and substitution at the raw term level  ============ *)

Lemma open_rec_identity : forall t k, wf k t ->
  forall k' v, Nat.le k k' -> open_tm_wrt_tm_rec k' v t = t.
Proof.
  intros t. induction t as [| |psi A IHA Btx IHB|psi A IHA b IHb|a0 IHa psi b IHb
                 |s|n|xx|psi a0 IHa b IHb psi0 A IHA| |a0 IHa b IHb|psi A IHA
                 |psi a0 IHa|psi a0 IHa|psi A IHA Btx IHB|a0 IHa psi b IHb|psi a0 IHa
                 |psi a0 IHa| | | |a0 IHa b0 IHb0 b1 IHb1];
  intros k Hk k' v Hle; simpl in *.
  - reflexivity. - reflexivity.
  - rewrite (IHA k (proj1 Hk) k' v Hle).
    rewrite (IHB (S k) (proj2 Hk) (S k') v ltac:(lia)). reflexivity.
  - rewrite (IHA k (proj1 Hk) k' v Hle).
    rewrite (IHb (S k) (proj2 Hk) (S k') v ltac:(lia)). reflexivity.
  - rewrite (IHa k (proj1 Hk) k' v Hle).
    rewrite (IHb k (proj2 Hk) k' v Hle). reflexivity.
  - reflexivity.
  - cbn [open_tm_wrt_tm_rec].
    destruct (lt_eq_lt_dec n k') as [[H|H]|H].
    + reflexivity.
    + exfalso. lia.
    + exfalso. lia.
  - reflexivity.
  - rewrite (IHa k (proj1 Hk) k' v Hle).
    rewrite (IHb k (proj1 (proj2 Hk)) k' v Hle).
    rewrite (IHA k (proj2 (proj2 Hk)) k' v Hle). reflexivity.
  - reflexivity.
  - rewrite (IHa k (proj1 Hk) k' v Hle).
    rewrite (IHb k (proj2 Hk) k' v Hle). reflexivity.
  - rewrite (IHA k Hk k' v Hle). reflexivity.
  - rewrite (IHa k Hk k' v Hle). reflexivity.
  - rewrite (IHa k Hk k' v Hle). reflexivity.
  - rewrite (IHA k (proj1 Hk) k' v Hle).
    rewrite (IHB (S k) (proj2 Hk) (S k') v ltac:(lia)). reflexivity.
  - rewrite (IHa k (proj1 Hk) k' v Hle).
    rewrite (IHb k (proj2 Hk) k' v Hle). reflexivity.
  - rewrite (IHa k Hk k' v Hle). reflexivity.
  - rewrite (IHa k Hk k' v Hle). reflexivity.
  - reflexivity. - reflexivity. - reflexivity.
  - rewrite (IHa k (proj1 Hk) k' v Hle).
    rewrite (IHb0 k (proj1 (proj2 Hk)) k' v Hle).
    rewrite (IHb1 k (proj2 (proj2 Hk)) k' v Hle). reflexivity.
Qed.

Lemma lc_open_identity : forall t, lc_tm t -> forall k v, open_tm_wrt_tm_rec k v t = t.
Proof.
  intros t H k v. exact (@open_rec_identity t 0 (lc_wf H) k v (Nat.le_0_l k)).
Qed.

Lemma wf_subst : forall t k, wf k t -> forall c x, wf 0 c -> wf k (subst_tm c x t).
Proof.
  intros t. induction t as [| |psi A IHA Btx IHB|psi A IHA b IHb|a0 IHa psi b IHb
                 |s|n|xx|psi a0 IHa b IHb psi0 A IHA| |a0 IHa b IHb|psi A IHA
                 |psi a0 IHa|psi a0 IHa|psi A IHA Btx IHB|a0 IHa psi b IHb|psi a0 IHa
                 |psi a0 IHa| | | |a0 IHa b0 IHb0 b1 IHb1];
  intros k Hk c y Hc; simpl in *.
  - exact I. - exact I.
  - split. exact (IHA k (proj1 Hk) c y Hc).
    exact (IHB (S k) (proj2 Hk) c y Hc).
  - split. exact (IHA k (proj1 Hk) c y Hc).
    exact (IHb (S k) (proj2 Hk) c y Hc).
  - split. exact (IHa k (proj1 Hk) c y Hc).
    exact (IHb k (proj2 Hk) c y Hc).
  - exact I.
  - exact Hk.
  - case: (eq_var xx y) => [E|NE].
    + exact (@wf_mono c 0 k (Nat.le_0_l k) Hc).
    + exact I.
  - split. exact (IHa k (proj1 Hk) c y Hc).
    split. exact (IHb k (proj1 (proj2 Hk)) c y Hc).
    exact (IHA k (proj2 (proj2 Hk)) c y Hc).
  - exact I.
  - split. exact (IHa k (proj1 Hk) c y Hc).
    exact (IHb k (proj2 Hk) c y Hc).
  - exact (IHA k Hk c y Hc).
  - exact (IHa k Hk c y Hc).
  - exact (IHa k Hk c y Hc).
  - split. exact (IHA k (proj1 Hk) c y Hc).
    exact (IHB (S k) (proj2 Hk) c y Hc).
  - split. exact (IHa k (proj1 Hk) c y Hc).
    exact (IHb k (proj2 Hk) c y Hc).
  - exact (IHa k Hk c y Hc).
  - exact (IHa k Hk c y Hc).
  - exact I. - exact I. - exact I.
  - split. exact (IHa k (proj1 Hk) c y Hc).
    split. exact (IHb0 k (proj1 (proj2 Hk)) c y Hc).
    exact (IHb1 k (proj2 (proj2 Hk)) c y Hc).
Qed.

Lemma lc_subst : forall t, lc_tm t -> forall c x, lc_tm c -> lc_tm (subst_tm c x t).
Proof.
  intros t Ht c x Hc. apply wf_lc. apply (@wf_subst t 0).
  - apply lc_wf, Ht.
  - apply lc_wf, Hc.
Qed.

Lemma subst_open_rec : forall t k u c x, lc_tm c ->
  subst_tm c x (open_tm_wrt_tm_rec k u t)
  = open_tm_wrt_tm_rec k (subst_tm c x u) (subst_tm c x t).
Proof.
  intros t. induction t as [| |psi A IHA Btx IHB|psi A IHA b IHb|a0 IHa psi b IHb
                 |s|n|xx|psi a0 IHa b IHb psi0 A IHA| |a0 IHa b IHb|psi A IHA
                 |psi a0 IHa|psi a0 IHa|psi A IHA Btx IHB|a0 IHa psi b IHb|psi a0 IHa
                 |psi a0 IHa| | | |a0 IHa b0 IHb0 b1 IHb1];
  intros k u c y Hc; simpl in *.
  - reflexivity. - reflexivity.
  - rewrite (IHA k u c y Hc). rewrite (IHB (S k) u c y Hc). reflexivity.
  - rewrite (IHA k u c y Hc). rewrite (IHb (S k) u c y Hc). reflexivity.
  - rewrite (IHa k u c y Hc). rewrite (IHb k u c y Hc). reflexivity.
  - reflexivity.
  - cbn [open_tm_wrt_tm_rec].
    destruct (lt_eq_lt_dec n k) as [[H|H]|H]; reflexivity.
  - case: (eq_var xx y) => [E|NE]; simpl.
    + rewrite (@lc_open_identity c Hc k (subst_tm c y u)). reflexivity.
    + reflexivity.
  - rewrite (IHa k u c y Hc). rewrite (IHb k u c y Hc). rewrite (IHA k u c y Hc).
    reflexivity.
  - reflexivity.
  - rewrite (IHa k u c y Hc). rewrite (IHb k u c y Hc). reflexivity.
  - rewrite (IHA k u c y Hc). reflexivity.
  - rewrite (IHa k u c y Hc). reflexivity.
  - rewrite (IHa k u c y Hc). reflexivity.
  - rewrite (IHA k u c y Hc). rewrite (IHB (S k) u c y Hc). reflexivity.
  - rewrite (IHa k u c y Hc). rewrite (IHb k u c y Hc). reflexivity.
  - rewrite (IHa k u c y Hc). reflexivity.
  - rewrite (IHa k u c y Hc). reflexivity.
  - reflexivity. - reflexivity. - reflexivity.
  - rewrite (IHa k u c y Hc). rewrite (IHb0 k u c y Hc). rewrite (IHb1 k u c y Hc).
    reflexivity.
Qed.

Lemma subst_open : forall t u c x, lc_tm c ->
  subst_tm c x (open_tm_wrt_tm t u)
  = open_tm_wrt_tm (subst_tm c x t) (subst_tm c x u).
Proof. intros. unfold open_tm_wrt_tm. apply subst_open_rec. assumption. Qed.

(* ============  econtext insertion plumbing  ============ *)

Lemma binds_insert : forall (P1 P2:econtext) (y:atom) (g:grade) (x:atom) (a:grade),
  binds x a (P1++P2) -> binds x a (P1 ++ (y,g)::P2).
Proof.
  intros P1. induction P1 as [|(b,h) P1' IH]; intros P2 y g x a H; simpl in *.
  - right; assumption.
  - destruct H as [E|Hin]; [left; exact E | right; apply (IH P2 y g x a); exact Hin].
Qed.

Lemma notin_dom_insert : forall (P1 P2:econtext) (y:atom) (g:grade) (a:atom),
  a \notin dom (P1++P2) -> a <> y -> a \notin dom (P1 ++ (y,g)::P2).
Proof.
  intros P1. induction P1 as [|(b,h) P1' IH]; intros P2 y g a H Ha; simpl in *.
  - apply notin_add_3; [ symmetry; assumption | assumption ].
  - apply notin_add_1 in H as Hb. apply notin_add_2 in H as Hd.
    apply notin_add_3; [ exact Hb | apply (IH P2 y g a); assumption ].
Qed.

Lemma uniq_insert : forall (P1 P2:econtext) (y:atom) (g:grade),
  uniq (P1++P2) -> y \notin dom (P1++P2) -> uniq (P1 ++ (y,g)::P2).
Proof.
  intros P1. induction P1 as [|(b,h) P1' IH]; intros P2 y g Hu Hy; simpl in *.
  - apply EnvImpl.uniq_push; assumption.
  - change (uniq (one ((b,h)) ++ (P1'++P2))) in Hu.
    inversion Hu as [| ? ? ? Hu' Hb]; subst.
    apply notin_add_1 in Hy as Hyb. apply notin_add_2 in Hy as Hyd.
    change (uniq (one (b,h) ++ (P1' ++ (y,g)::P2))).
    apply EnvImpl.uniq_push.
    + apply (IH P2 y g); assumption.
    + exact (@notin_dom_insert P1' P2 y g b Hb Hyb).
Qed.


Scheme GDefEq_mutP := Induction for GDefEq Sort Prop
  with CGDefEq_mutP := Induction for CGDefEq Sort Prop.

Lemma gdefeq_insert : forall (P:econtext) (psi:grade) (a b:tm), GDefEq P psi a b ->
  forall (Q1 Q2:econtext) (yy:atom) (gg:grade), P = Q1++Q2 -> yy \notin dom P ->
    GDefEq (Q1++(yy,gg)::Q2) psi a b.
Proof.
  refine (@GDefEq_mutP
    (fun (e:econtext) (s:grade) (t t0:tm) (_:GDefEq e s t t0) =>
       forall (Q1 Q2:econtext) (yy:atom) (gg:grade), e = Q1++Q2 -> yy \notin dom e ->
         GDefEq (Q1++(yy,gg)::Q2) s t t0)
    (fun (e:econtext) (s s0:grade) (t t0:tm) (_:CGDefEq e s s0 t t0) =>
       forall (Q1 Q2:econtext) (yy:atom) (gg:grade), e = Q1++Q2 -> yy \notin dom e ->
         CGDefEq (Q1++(yy,gg)::Q2) s s0 t t0)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* GE_Var *) intros P1 psi x psi0 u i bd Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@GE_Var (Q1++(yy,gg)::Q2) psi x psi0).
    + apply uniq_insert; assumption.
    + assumption.
    + apply binds_insert; assumption.
  - (* GE_Type *) intros P1 psi s u Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_Type. apply uniq_insert; assumption.
  - (* GE_Sym *) intros P1 psi bb aa gx IHx Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_Sym. apply (IHx Q1 Q2 yy gg eq_refl Hy).
  - (* GE_Trans *) intros P1 psi a b cc gx IHx gy IHy Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_Trans.
    + apply (IHx Q1 Q2 yy gg eq_refl Hy).
    + apply (IHy Q1 Q2 yy gg eq_refl Hy).
  - (* GE_App *) intros P1 psi b0 psi0 a0 b1 a1 gx IHx cc IHc Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_App.
    + apply (IHx Q1 Q2 yy gg eq_refl Hy).
    + apply (IHc Q1 Q2 yy gg eq_refl Hy).
  - (* GE_Abs *) intros L P1 psi psi0 A0 b0 A1 b1 l0 l1 gpt IHpt Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@GE_Abs (L \u {{yy}}) (Q1++(yy,gg)::Q2) psi psi0 A0 b0 A1 b1).
    + exact l0. + exact l1.
    +
    intros z Hz.
    have HzL : z \notin L. { exact (@notin_union_1 z L ({{yy}}) Hz). }
    have Hzs : z \notin {{yy}}. { exact (@notin_union_2 z L ({{yy}}) Hz). }
    have Hyz : yy <> z. { exact (@notin_singleton_1 yy z Hzs). }
    have Hzy : z <> yy. { intro E; apply Hyz; symmetry; exact E. }
    have Hfr : yy \notin dom ((z, psi0) :: (Q1++Q2)).
    { simpl. apply notin_add_3; [ exact Hzy | exact Hy ]. }
    exact (IHpt z HzL ((z,psi0)::Q1) Q2 yy gg eq_refl Hfr).
  - (* GE_Pi *) intros L P1 psi psi0 A0 B0 A1 B1 gd IHd gpt IHpt Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@GE_Pi (L \u {{yy}}) (Q1++(yy,gg)::Q2) psi psi0 A0 B0 A1 B1).
    +
    + apply (IHd Q1 Q2 yy gg eq_refl Hy).
    + intros z Hz.
      have HzL : z \notin L. { exact (@notin_union_1 z L ({{yy}}) Hz). }
      have Hzs : z \notin {{yy}}. { exact (@notin_union_2 z L ({{yy}}) Hz). }
      have Hyz : yy <> z. { exact (@notin_singleton_1 yy z Hzs). }
      have Hzy : z <> yy. { intro E; apply Hyz; symmetry; exact E. }
      have Hfr : yy \notin dom ((z, psi0) :: (Q1++Q2)).
      { simpl. apply notin_add_3; [ exact Hzy | exact Hy ]. }
      exact (IHpt z HzL ((z,psi0)::Q1) Q2 yy gg eq_refl Hfr).
  - (* GE_AppAbs *) intros P1 psi aa psi0 b0 a0 b1 A gx IHx cc IHc Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_AppAbs.
    + apply (IHx Q1 Q2 yy gg eq_refl Hy).
    + apply (IHc Q1 Q2 yy gg eq_refl Hy).
  - (* GE_Refl *) intros P1 psi u Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_Refl. apply uniq_insert; assumption.
  - (* GE_Transp *) intros P1 psi a0 b0 a1 b1 gx IHx gy IHy Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_Transp.
    + apply (IHx Q1 Q2 yy gg eq_refl Hy).
    + apply (IHy Q1 Q2 yy gg eq_refl Hy).
  - (* GE_CEq *) intros P1 psi psi0 a0 b0 psi1 A0 a1 b1 A1 l0 l1 gx IHx gy IHy hle Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@GE_CEq (Q1++(yy,gg)::Q2) psi psi0 a0 b0 psi1 A0 a1 b1 A1); [ exact l0 | exact l1 | | | exact hle ].
    + apply (IHx Q1 Q2 yy gg eq_refl Hy).
    + apply (IHy Q1 Q2 yy gg eq_refl Hy).
  - (* GE_TranspRefl *) intros P1 psi a0 b0 b1 gx IHx gy IHy Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_TranspRefl.
    + apply (IHx Q1 Q2 yy gg eq_refl Hy).
    + apply (IHy Q1 Q2 yy gg eq_refl Hy).
  - (* GE_T *) intros P1 psi psi0 A B gx IHx Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_T. apply (IHx Q1 Q2 yy gg eq_refl Hy).
  - (* GE_Box *) intros P1 psi psi0 a b cc IHc Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_Box. apply (IHc Q1 Q2 yy gg eq_refl Hy).
  - (* GE_Unbox *) intros P1 psi psi0 a b gx IHx hle Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_Unbox; [ apply (IHx Q1 Q2 yy gg eq_refl Hy) | exact hle ].
  - (* GE_UnboxBox *) intros P1 psi psi0 a b gx IHx hle Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_UnboxBox; [ apply (IHx Q1 Q2 yy gg eq_refl Hy) | exact hle ].
  - (* GE_Proj1Cong *) intros P1 psi psi0 a0 a1 gx IHx hle Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_Proj1Cong; [ apply (IHx Q1 Q2 yy gg eq_refl Hy) | exact hle ].
  - (* GE_Proj2Cong *) intros P1 psi psi0 a0 a1 gx IHx Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_Proj2Cong; apply (IHx Q1 Q2 yy gg eq_refl Hy).
  - (* GE_Proj1Beta *) intros P1 psi psi0 b a1 a2 gx IHx hle Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_Proj1Beta; [ apply (IHx Q1 Q2 yy gg eq_refl Hy) | exact hle ].
  - (* GE_Proj2Beta *) intros P1 psi psi0 b a2 a1 gx IHx Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_Proj2Beta; apply (IHx Q1 Q2 yy gg eq_refl Hy).
  - (* GE_SPair *) intros P1 psi a0 psi0 b0 a1 b1 cc IHc gx IHx Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_SPair.
    + apply (IHc Q1 Q2 yy gg eq_refl Hy).
    + apply (IHx Q1 Q2 yy gg eq_refl Hy).
  - (* GE_SSigma *) intros L P1 psi psi0 A0 B0 A1 B1 gd IHd gpt IHpt Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@GE_SSigma (L \u {{yy}}) (Q1++(yy,gg)::Q2) psi psi0 A0 B0 A1 B1).
    +
    + apply (IHd Q1 Q2 yy gg eq_refl Hy).
    + intros z Hz.
      have HzL : z \notin L. { exact (@notin_union_1 z L ({{yy}}) Hz). }
      have Hzs : z \notin {{yy}}. { exact (@notin_union_2 z L ({{yy}}) Hz). }
      have Hyz : yy <> z. { exact (@notin_singleton_1 yy z Hzs). }
      have Hzy : z <> yy. { intro E; apply Hyz; symmetry; exact E. }
      have Hfr : yy \notin dom ((z, psi0) :: (Q1++Q2)).
      { simpl. apply notin_add_3; [ exact Hzy | exact Hy ]. }
      exact (IHpt z HzL ((z,psi0)::Q1) Q2 yy gg eq_refl Hfr).
  - (* GE_TyUnit *) intros P1 psi u Q1 Q2 yy gg Heq Hy. subst P1. eapply GE_TyUnit. apply uniq_insert; assumption.
  - (* GE_TmUnit *) intros P1 psi u Q1 Q2 yy gg Heq Hy. subst P1. eapply GE_TmUnit. apply uniq_insert; assumption.
  - (* GE_Bool *) intros P1 psi u Q1 Q2 yy gg Heq Hy. subst P1. eapply GE_Bool. apply uniq_insert; assumption.
  - (* GE_True *) intros P1 psi u Q1 Q2 yy gg Heq Hy. subst P1. eapply GE_True. apply uniq_insert; assumption.
  - (* GE_False *) intros P1 psi u Q1 Q2 yy gg Heq Hy. subst P1. eapply GE_False. apply uniq_insert; assumption.
  - (* GE_If *) intros P1 psi a0 b0 b1 a1 b2 b3 gx IHx gy IHy gz IHz Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_If.
    + apply (IHx Q1 Q2 yy gg eq_refl Hy).
    + apply (IHy Q1 Q2 yy gg eq_refl Hy).
    + apply (IHz Q1 Q2 yy gg eq_refl Hy).
  - (* GE_IfTrue *) intros P1 psi a0 b0 b1 b2 b3 gx IHx gy IHy gz IHz Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_IfTrue.
    + apply (IHx Q1 Q2 yy gg eq_refl Hy).
    + apply (IHy Q1 Q2 yy gg eq_refl Hy).
    + apply (IHz Q1 Q2 yy gg eq_refl Hy).
  - (* GE_IfFalse *) intros P1 psi a0 b0 b1 b3 b2 gx IHx gy IHy gz IHz Q1 Q2 yy gg Heq Hy. subst P1.
    eapply GE_IfFalse.
    + apply (IHx Q1 Q2 yy gg eq_refl Hy).
    + apply (IHy Q1 Q2 yy gg eq_refl Hy).
    + apply (IHz Q1 Q2 yy gg eq_refl Hy).
  - (* CGE_Leq *) intros P1 psi psi0 a b hle gx IHx Q1 Q2 yy gg Heq Hy. subst P1.
    eapply CGE_Leq; [ exact hle | apply (IHx Q1 Q2 yy gg eq_refl Hy) ].
  - (* CGE_NLeq *) intros P1 psi psi0 a b la lb hnle u Q1 Q2 yy gg Heq Hy. subst P1.
    eapply CGE_NLeq; [ exact la | exact lb | exact hnle | apply uniq_insert; assumption ].
Qed.

Lemma subst_var_eq : forall (c:tm) (x:atom), subst_tm c x (a_Var_f x) = c.
Proof.
  intros. cbn [subst_tm].
  destruct (@eq_dec tmvar EqDec_eq_of_X x x) as [E|NE]; cbn [is_left];
    [ reflexivity | exfalso; apply NE; reflexivity ].
Qed.

Lemma subst_var_neq : forall (c:tm) (x y:atom), x <> y -> subst_tm c x (a_Var_f y) = a_Var_f y.
Proof.
  intros. cbn [subst_tm].
  destruct (@eq_dec tmvar EqDec_eq_of_X y x) as [E|NE]; cbn [is_left];
    [ exfalso; apply H; symmetry; exact E | reflexivity ].
Qed.

Lemma cond_extend : forall (P:econtext) (psi:grade) (xv:atom) (cv:tm) (z:atom) (psi0:grade),
  z <> xv -> z \notin dom P ->
  (GDefEq P psi cv cv \/ (forall g:grade, binds xv g P -> ~ (g <= psi))) ->
  (GDefEq ((z,psi0)::P) psi cv cv \/
   (forall g:grade, binds xv g ((z,psi0)::P) -> ~ (g <= psi))).
Proof.
  intros P psi xv cv z psi0 Hzx HzP [Hr|Hn].
  - left. exact (@gdefeq_insert P psi cv cv Hr nil P z psi0 eq_refl HzP).
  - right. intros g Hb.
    apply (Hn g). apply EnvImpl.binds_cons_1 in Hb.
    destruct Hb as [[E1 E2]|Hb]; [ exfalso; apply Hzx; symmetry; exact E1 | exact Hb ].
Qed.

Lemma gdefeq_subst : forall (P:econtext) (psi:grade) (a b:tm), GDefEq P psi a b ->
  forall (xv:atom) (cv:tm), lc_tm cv ->
  (GDefEq P psi cv cv \/ (forall g:grade, binds xv g P -> ~ (g <= psi))) ->
  GDefEq P psi (subst_tm cv xv a) (subst_tm cv xv b).
Proof.
  refine (@GDefEq_mutP
    (fun (e:econtext) (s:grade) (t t0:tm) (_:GDefEq e s t t0) =>
       forall (xv:atom) (cv:tm), lc_tm cv ->
       (GDefEq e s cv cv \/ (forall g:grade, binds xv g e -> ~ (g <= s))) ->
       GDefEq e s (subst_tm cv xv t) (subst_tm cv xv t0))
    (fun (e:econtext) (s s0:grade) (t t0:tm) (_:CGDefEq e s s0 t t0) =>
       forall (xv:atom) (cv:tm), lc_tm cv ->
       (GDefEq e s cv cv \/ (forall g:grade, binds xv g e -> ~ (g <= s))) ->
       CGDefEq e s s0 (subst_tm cv xv t) (subst_tm cv xv t0))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* GE_Var *) intros P1 psi x psi0 u i bd xv cv Hlc Hcond.
    destruct (@eq_dec tmvar EqDec_eq_of_X x xv) as [E|NE].
    + subst x. rewrite (@subst_var_eq cv xv).
      destruct Hcond as [Hr|Hn]; [ exact Hr | exfalso; exact (Hn psi0 bd i) ].
    + have Hne : xv <> x. { symmetry; exact NE. }
      rewrite (@subst_var_neq cv xv x Hne).
      eapply (@GE_Var P1 psi x psi0); [ exact u | exact i | exact bd ].
  - (* GE_Type *) intros P1 psi s u xv cv Hlc Hcond. simpl.
    eapply GE_Type; exact u.
  - (* GE_Sym *) intros P1 psi bb aa gx IHx xv cv Hlc Hcond. simpl.
    eapply GE_Sym. exact (IHx xv cv Hlc Hcond).
  - (* GE_Trans *) intros P1 psi a b cc gx IHx gy IHy xv cv Hlc Hcond. simpl.
    eapply GE_Trans; [ exact (IHx xv cv Hlc Hcond) | exact (IHy xv cv Hlc Hcond) ].
  - (* GE_App *) intros P1 psi b0 psi0 a0 b1 a1 gx IHx cc IHc xv cv Hlc Hcond. simpl.
    eapply GE_App; [ exact (IHx xv cv Hlc Hcond) | exact (IHc xv cv Hlc Hcond) ].
  - (* GE_Abs *) intros L P1 psi psi0 A0 b0 A1 b1 l0 l1 gpt IHpt xv cv Hlc Hcond. simpl.
    eapply (@GE_Abs ((((L \u dom P1) \u {{xv}}))) P1 psi psi0
              (subst_tm cv xv A0) (subst_tm cv xv b0) (subst_tm cv xv A1) (subst_tm cv xv b1)).
    + exact (@lc_subst A0 l0 cv xv Hlc).
    + exact (@lc_subst A1 l1 cv xv Hlc).
    + intros z Hz.
      have Hz1 : z \notin (L \u dom P1). { exact (@notin_union_1 z (L \u dom P1) {{xv}} Hz). }
      have Hz2 : z \notin {{xv}}. { exact (@notin_union_2 z (L \u dom P1) {{xv}} Hz). }
      have HzL : z \notin L. { exact (@notin_union_1 z L (dom P1) Hz1). }
      have Hzd : z \notin dom P1. { exact (@notin_union_2 z L (dom P1) Hz1). }
      have Hxvz : xv <> z. { exact (@notin_singleton_1 xv z Hz2). }
      have Hzxv : z <> xv. { intro E; apply Hxvz; symmetry; exact E. }
      have Hcond' := @cond_extend P1 psi xv cv z psi0 Hzxv Hzd Hcond.
      pose proof (IHpt z HzL xv cv Hlc Hcond') as Hres.
      rewrite (@subst_open b0 (a_Var_f z) cv xv Hlc) (@subst_var_neq cv xv z Hxvz) in Hres.
      rewrite (@subst_open b1 (a_Var_f z) cv xv Hlc) (@subst_var_neq cv xv z Hxvz) in Hres.
      exact Hres.
  - (* GE_Pi *) intros L P1 psi psi0 A0 B0 A1 B1 gd IHd gpt IHpt xv cv Hlc Hcond. simpl.
    eapply (@GE_Pi (((L \u dom P1) \u {{xv}})) P1 psi psi0
              (subst_tm cv xv A0) (subst_tm cv xv B0) (subst_tm cv xv A1) (subst_tm cv xv B1)).
    + exact (IHd xv cv Hlc Hcond).
    + intros z Hz.
      have Hz1 : z \notin (L \u dom P1). { exact (@notin_union_1 z (L \u dom P1) {{xv}} Hz). }
      have Hz2 : z \notin {{xv}}. { exact (@notin_union_2 z (L \u dom P1) {{xv}} Hz). }
      have HzL : z \notin L. { exact (@notin_union_1 z L (dom P1) Hz1). }
      have Hzd : z \notin dom P1. { exact (@notin_union_2 z L (dom P1) Hz1). }
      have Hxvz : xv <> z. { exact (@notin_singleton_1 xv z Hz2). }
      have Hzxv : z <> xv. { intro E; apply Hxvz; symmetry; exact E. }
      have Hcond' := @cond_extend P1 psi xv cv z psi0 Hzxv Hzd Hcond.
      pose proof (IHpt z HzL xv cv Hlc Hcond') as Hres.
      rewrite (@subst_open B0 (a_Var_f z) cv xv Hlc) (@subst_var_neq cv xv z Hxvz) in Hres.
      rewrite (@subst_open B1 (a_Var_f z) cv xv Hlc) (@subst_var_neq cv xv z Hxvz) in Hres.
      exact Hres.
  - (* GE_AppAbs *) intros P1 psi aa psi0 b0 a0 b1 A gx IHx cc IHc xv cv Hlc Hcond. simpl.
    rewrite (@subst_open a0 b1 cv xv Hlc).
    eapply GE_AppAbs; [ exact (IHx xv cv Hlc Hcond) | exact (IHc xv cv Hlc Hcond) ].
  - (* GE_Refl *) intros P1 psi u xv cv Hlc Hcond. simpl. eapply GE_Refl; exact u.
  - (* GE_Transp *) intros P1 psi a0 b0 a1 b1 gx IHx gy IHy xv cv Hlc Hcond. simpl.
    eapply GE_Transp; [ exact (IHx xv cv Hlc Hcond) | exact (IHy xv cv Hlc Hcond) ].
  - (* GE_CEq *) intros P1 psi psi0 a0 b0 psi1 A0 a1 b1 A1 l0 l1 gx IHx gy IHy hle xv cv Hlc Hcond. simpl.
    eapply (@GE_CEq P1 psi psi0 (subst_tm cv xv a0) (subst_tm cv xv b0) psi1
              (subst_tm cv xv A0) (subst_tm cv xv a1) (subst_tm cv xv b1) (subst_tm cv xv A1)).
    + exact (@lc_subst A0 l0 cv xv Hlc).
    + exact (@lc_subst A1 l1 cv xv Hlc).
    + exact (IHx xv cv Hlc Hcond).
    + exact (IHy xv cv Hlc Hcond).
    + exact hle.
  - (* GE_TranspRefl *) intros P1 psi a0 b0 b1 gx IHx gy IHy xv cv Hlc Hcond. simpl.
    eapply GE_TranspRefl; [ exact (IHx xv cv Hlc Hcond) | exact (IHy xv cv Hlc Hcond) ].
  - (* GE_T *) intros P1 psi psi0 A B gx IHx xv cv Hlc Hcond. simpl.
    eapply GE_T; exact (IHx xv cv Hlc Hcond).
  - (* GE_Box *) intros P1 psi psi0 a b cc IHc xv cv Hlc Hcond. simpl.
    eapply GE_Box; exact (IHc xv cv Hlc Hcond).
  - (* GE_Unbox *) intros P1 psi psi0 a b gx IHx hle xv cv Hlc Hcond. simpl.
    eapply GE_Unbox; [ exact (IHx xv cv Hlc Hcond) | exact hle ].
  - (* GE_UnboxBox *) intros P1 psi psi0 a b gx IHx hle xv cv Hlc Hcond. simpl.
    eapply GE_UnboxBox; [ exact (IHx xv cv Hlc Hcond) | exact hle ].
  - (* GE_Proj1Cong *) intros P1 psi psi0 a0 a1 gx IHx hle xv cv Hlc Hcond. simpl.
    eapply GE_Proj1Cong; [ exact (IHx xv cv Hlc Hcond) | exact hle ].
  - (* GE_Proj2Cong *) intros P1 psi psi0 a0 a1 gx IHx xv cv Hlc Hcond. simpl.
    eapply GE_Proj2Cong; exact (IHx xv cv Hlc Hcond).
  - (* GE_Proj1Beta *) intros P1 psi psi0 b a1 a2 gx IHx hle xv cv Hlc Hcond. simpl.
    eapply GE_Proj1Beta; [ exact (IHx xv cv Hlc Hcond) | exact hle ].
  - (* GE_Proj2Beta *) intros P1 psi psi0 b a2 a1 gx IHx xv cv Hlc Hcond. simpl.
    eapply GE_Proj2Beta; exact (IHx xv cv Hlc Hcond).
  - (* GE_SPair *) intros P1 psi a0 psi0 b0 a1 b1 cc IHc gx IHx xv cv Hlc Hcond. simpl.
    eapply GE_SPair; [ exact (IHc xv cv Hlc Hcond) | exact (IHx xv cv Hlc Hcond) ].
  - (* GE_SSigma *) intros L P1 psi psi0 A0 B0 A1 B1 gd IHd gpt IHpt xv cv Hlc Hcond. simpl.
    eapply (@GE_SSigma (((L \u dom P1) \u {{xv}})) P1 psi psi0
              (subst_tm cv xv A0) (subst_tm cv xv B0) (subst_tm cv xv A1) (subst_tm cv xv B1)).
    + exact (IHd xv cv Hlc Hcond).
    + intros z Hz.
      have Hz1 : z \notin (L \u dom P1). { exact (@notin_union_1 z (L \u dom P1) {{xv}} Hz). }
      have Hz2 : z \notin {{xv}}. { exact (@notin_union_2 z (L \u dom P1) {{xv}} Hz). }
      have HzL : z \notin L. { exact (@notin_union_1 z L (dom P1) Hz1). }
      have Hzd : z \notin dom P1. { exact (@notin_union_2 z L (dom P1) Hz1). }
      have Hxvz : xv <> z. { exact (@notin_singleton_1 xv z Hz2). }
      have Hzxv : z <> xv. { intro E; apply Hxvz; symmetry; exact E. }
      have Hcond' := @cond_extend P1 psi xv cv z psi0 Hzxv Hzd Hcond.
      pose proof (IHpt z HzL xv cv Hlc Hcond') as Hres.
      rewrite (@subst_open B0 (a_Var_f z) cv xv Hlc) (@subst_var_neq cv xv z Hxvz) in Hres.
      rewrite (@subst_open B1 (a_Var_f z) cv xv Hlc) (@subst_var_neq cv xv z Hxvz) in Hres.
      exact Hres.
  - (* GE_TyUnit *) intros P1 psi u xv cv Hlc Hcond. simpl. eapply GE_TyUnit; exact u.
  - (* GE_TmUnit *) intros P1 psi u xv cv Hlc Hcond. simpl. eapply GE_TmUnit; exact u.
  - (* GE_Bool *) intros P1 psi u xv cv Hlc Hcond. simpl. eapply GE_Bool; exact u.
  - (* GE_True *) intros P1 psi u xv cv Hlc Hcond. simpl. eapply GE_True; exact u.
  - (* GE_False *) intros P1 psi u xv cv Hlc Hcond. simpl. eapply GE_False; exact u.
  - (* GE_If *) intros P1 psi a0 b0 b1 a1 b2 b3 gx IHx gy IHy gz IHz xv cv Hlc Hcond. simpl.
    eapply GE_If; [ exact (IHx xv cv Hlc Hcond) | exact (IHy xv cv Hlc Hcond) | exact (IHz xv cv Hlc Hcond) ].
  - (* GE_IfTrue *) intros P1 psi a0 b0 b1 b2 b3 gx IHx gy IHy gz IHz xv cv Hlc Hcond. simpl.
    eapply GE_IfTrue; [ exact (IHx xv cv Hlc Hcond) | exact (IHy xv cv Hlc Hcond) | exact (IHz xv cv Hlc Hcond) ].
  - (* GE_IfFalse *) intros P1 psi a0 b0 b1 b3 b2 gx IHx gy IHy gz IHz xv cv Hlc Hcond. simpl.
    eapply GE_IfFalse; [ exact (IHx xv cv Hlc Hcond) | exact (IHy xv cv Hlc Hcond) | exact (IHz xv cv Hlc Hcond) ].
  - (* CGE_Leq *) intros P1 psi psi0 a b hle gx IHx xv cv Hlc Hcond. simpl.
    eapply CGE_Leq; [ exact hle | exact (IHx xv cv Hlc Hcond) ].
  - (* CGE_NLeq *) intros P1 psi psi0 a b la lb hnle u xv cv Hlc Hcond. simpl.
    eapply CGE_NLeq; [ exact (@lc_subst a la cv xv Hlc) | exact (@lc_subst b lb cv xv Hlc) | exact hnle | exact u ].
Qed.

(* ============  Labels facts  ============ *)

Lemma labels_nil : labels nil = nil. Proof. reflexivity. Qed.
Lemma labels_cons : forall W x g A, labels ((x,(g,A))::W) = (x,g)::labels W.
Proof. reflexivity. Qed.
Lemma labels_app : forall (E F:context), labels (E++F) = labels E ++ labels F.
Proof. intros. unfold labels. rewrite EnvImpl.map_app. reflexivity. Qed.
Lemma uniq_labels : forall W, uniq W -> uniq (labels W).
Proof. intros W H. apply EnvImpl.uniq_map_2. exact H. Qed.
Lemma binds_labels : forall W x g A, binds x (g,A) W -> binds x g (labels W).
Proof.
  intros W x g A H. unfold labels.
  exact (@EnvImpl.binds_map_2 (grade*tm) grade (fun p:grade*tm => fst p) x (g,A) W H).
Qed.

(* any typing derivation gives a well-formed context *)
Lemma typing_ctx : forall W psi a A, Typing W psi a A -> Ctx W.
Proof.
  intros W psi a A H. induction H; try assumption.
Qed.

(* uniq of labels from any typing derivation *)
Lemma uniq_labels_typing : forall W psi a A, Typing W psi a A -> uniq (labels W).
Proof.
  intros. apply uniq_labels. apply Ctx_uniq. exact (typing_ctx H).
Qed.

Lemma typing_gdefeq_refl : forall W psi a A, Typing W psi a A ->
  forall psi', psi <= psi' -> GDefEq (labels W) psi' a a.
Proof.
  intros W psi a A H. induction H; intros psi' Hle.
  - (* T_Type *) eapply GE_Type. apply uniq_labels. apply Ctx_uniq. assumption.
  - (* T_Var *) eapply (@GE_Var (labels W) psi' x psi0).
    + apply uniq_labels. apply Ctx_uniq. assumption.
    + exact (Order.POrderTheory.le_trans H0 Hle).
    + exact (binds_labels H1).
  - (* T_Pi *) eapply GE_Pi.
    + apply (IHTyping psi' Hle).
    + intros x Hx. apply (H1 x Hx psi' Hle).
  - (* T_Abs *)
    have HA : lc_tm A. { apply wf_lc. have HP := typing_wf H1. simpl in HP. exact (proj1 HP). }
    eapply GE_Abs; [ exact HA | exact HA | ].
    intros x Hx. apply (H0 x Hx psi' Hle).
  - (* T_App *) eapply GE_App.
    + apply (IHTyping1 psi' Hle).
    + case: (boolP (psi0 <= psi')) => [Hle0|Hnle0].
      * apply CGE_Leq; [ exact Hle0 | apply (IHTyping2 psi' Hle0) ].
      * move/negP: Hnle0 => Hnle0. apply CGE_NLeq; [ exact (typing_lc H0) | exact (typing_lc H0)
                         | exact Hnle0 | exact (uniq_labels_typing H0) ].
  - (* T_Conv *) apply (IHTyping1 psi' Hle).
  - (* T_Refl *) eapply GE_Refl. exact (uniq_labels_typing H).
  - (* T_CEq *) eapply GE_CEq.
    + exact (typing_lc H1).
    + exact (typing_lc H1).
    + apply (IHTyping1 psi' (Order.POrderTheory.le_trans H3 (Order.POrderTheory.le_trans H4 Hle))).
    + apply (IHTyping2 psi' (Order.POrderTheory.le_trans H3 (Order.POrderTheory.le_trans H4 Hle))).
    + exact (Order.POrderTheory.le_trans H4 Hle).
  - (* T_Transp *) eapply GE_Transp.
    + apply (IHTyping1 psi' Hle).
    + apply (IHTyping2 psi' Hle).
  - (* T_T *) eapply GE_T. apply (IHTyping psi' Hle).
  - (* T_Box *)
    eapply GE_Box.
    case: (boolP (psi0 <= psi')) => [Hle0|Hnle0].
    + apply CGE_Leq; [ exact Hle0 | apply (IHTyping1 psi' Hle0) ].
    + move/negP: Hnle0 => Hnle0. apply CGE_NLeq; [ exact (typing_lc H) | exact (typing_lc H)
                       | exact Hnle0 | exact (uniq_labels_typing H0) ].
  - (* T_Unbox *) eapply GE_Unbox.
    + apply (IHTyping psi' Hle).
    + exact (Order.POrderTheory.le_trans H0 Hle).
  - (* T_SSigma *) eapply GE_SSigma.
    + apply (IHTyping psi' Hle).
    + intros x Hx. apply (H1 x Hx psi' Hle).
  - (* T_SPair *) eapply GE_SPair.
    + case: (boolP (psi0 <= psi')) => [Hle0|Hnle0].
      * apply CGE_Leq; [ exact Hle0 | apply (IHTyping2 psi' Hle0) ].
      * move/negP: Hnle0 => Hnle0. apply CGE_NLeq; [ exact (typing_lc H0) | exact (typing_lc H0)
                         | exact Hnle0 | exact (uniq_labels_typing H0) ].
    + apply (IHTyping3 psi' Hle).
  - (* T_Proj1 *) eapply GE_Proj1Cong.
    + apply (IHTyping psi' Hle).
    + exact (Order.POrderTheory.le_trans H0 Hle).
  - (* T_Proj2 *) eapply GE_Proj2Cong. apply (IHTyping1 psi' Hle).
  - (* T_TyUnit *) eapply GE_TyUnit. apply uniq_labels. apply Ctx_uniq. assumption.
  - (* T_TmUnit *) eapply GE_TmUnit. exact (uniq_labels_typing H).
  - (* T_Bool *) eapply GE_Bool. apply uniq_labels. apply Ctx_uniq. assumption.
  - (* T_True *) eapply GE_True. exact (uniq_labels_typing H).
  - (* T_False *) eapply GE_False. exact (uniq_labels_typing H).
  - (* T_If *) eapply GE_If.
    + apply (IHTyping1 psi' Hle).
    + apply (IHTyping2 psi' Hle).
    + apply (IHTyping3 psi' Hle).
Qed.

(* ============  Parallel reduction preserves headforms  ============ *)

Lemma par_headform : forall (P:econtext) (psi:grade) (a b:tm),
  Par P psi a b -> forall h, tm_to_headform a = Some h -> tm_to_headform b = Some h.
Proof.
  intros P psi a b H. induction H; intros h Hh; simpl in Hh;
    try discriminate Hh; try assumption.
Qed.

Lemma epar_headform : forall (P:econtext) (a b:tm),
  EPar P a b -> forall h, tm_to_headform a = Some h -> tm_to_headform b = Some h.
Proof.
  intros P a b H. induction H. intros h Hh. exact (@par_headform P psi a b H h Hh).
Qed.

Lemma empar_headform : forall (P:econtext) (a b:tm),
  EMPar P a b -> forall h, tm_to_headform a = Some h -> tm_to_headform b = Some h.
Proof.
  intros P a b H. induction H; intros h Hh.
  - exact (@epar_headform P a b H h Hh).
  - apply IHEMPar. exact (@epar_headform P a b H h Hh).
Qed.

Lemma ejoins_consistent : forall (P:econtext) (a b:tm),
  EJoins P a b ->
  forall h1 h2, tm_to_headform a = Some h1 -> tm_to_headform b = Some h2 -> h1 = h2.
Proof.
  intros P a b H h1 h2 Ha Hb. destruct H as [P' a1 a2 c Hac Hbc].
  assert (Hc1 : tm_to_headform c = Some h1) by exact (@empar_headform _ _ _ Hac h1 Ha).
  assert (Hc2 : tm_to_headform c = Some h2) by exact (@empar_headform _ _ _ Hbc h2 Hb).
  rewrite Hc1 in Hc2. injection Hc2. auto.
Qed.

(* ============  GDefEq endpoints are locally closed  ============ *)

Lemma gdefeq_wf : forall (P:econtext) (psi:grade) (a b:tm),
  GDefEq P psi a b -> wf 0 a /\ wf 0 b.
Proof.
  refine (@GDefEq_mutP
    (fun (e:econtext) (s:grade) (t t0:tm) (_:GDefEq e s t t0) =>
       wf 0 t /\ wf 0 t0)
    (fun (e:econtext) (s s0:grade) (t t0:tm) (_:CGDefEq e s s0 t t0) =>
       wf 0 t /\ wf 0 t0)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - (* GE_Var *) intros P1 psi x psi0 u i bd. simpl. tauto.
  - (* GE_Type *) intros P1 psi s u. simpl. tauto.
  - (* GE_Sym *) intros P1 psi bb aa gx IHx. tauto.
  - (* GE_Trans *) intros P1 psi a b cc gx IHx gy IHy. tauto.
  - (* GE_App *) intros P1 psi b0 psi0 a0 b1 a1 gx IHx cc IHc. simpl. tauto.
  - (* GE_Abs *) intros L P1 psi psi0 A0 b0 A1 b1 l0 l1 gpt IHpt.
    destruct (atom_fresh L) as [x Hx].
    simpl. split; [ split | split ].
    + exact (@lc_wf A0 l0).
    + apply (proj2 (wf_open_var b0 0 x)). exact (proj1 (IHpt x Hx)).
    + exact (@lc_wf A1 l1).
    + apply (proj2 (wf_open_var b1 0 x)). exact (proj2 (IHpt x Hx)).
  - (* GE_Pi *) intros L P1 psi psi0 A0 B0 A1 B1 gd IHd gpt IHpt.
    destruct (atom_fresh L) as [x Hx].
    simpl. split; [ split | split ].
    + exact (proj1 IHd).
    + apply (proj2 (wf_open_var B0 0 x)). exact (proj1 (IHpt x Hx)).
    + exact (proj2 IHd).
    + apply (proj2 (wf_open_var B1 0 x)). exact (proj2 (IHpt x Hx)).
  - (* GE_AppAbs *) intros P1 psi aa psi0 b0 a0 b1 A gx IHx cc IHc.
    simpl in *. split; [ tauto | ].
    apply (@wf_open_term a0 0 b1).
    + exact (proj2 (proj2 IHx)).
    + exact (proj2 IHc).
  - (* GE_Refl *) intros P1 psi u. simpl. tauto.
  - (* GE_Transp *) intros P1 psi a0 b0 a1 b1 gx IHx gy IHy. simpl. tauto.
  - (* GE_CEq *) intros P1 psi psi0 a0 b0 psi1 A0 a1 b1 A1 l0 l1 gx IHx gy IHy hle.
    simpl. split; [ split | split ].
    + exact (proj1 IHx).
    + split; [ exact (proj1 IHy) | exact (@lc_wf A0 l0) ].
    + exact (proj2 IHx).
    + split; [ exact (proj2 IHy) | exact (@lc_wf A1 l1) ].
  - (* GE_TranspRefl *) intros P1 psi a0 b0 b1 gx IHx gy IHy. simpl in *. tauto.
  - (* GE_T *) intros P1 psi psi0 A B gx IHx. simpl. tauto.
  - (* GE_Box *) intros P1 psi psi0 a b cc IHc. simpl. tauto.
  - (* GE_Unbox *) intros P1 psi psi0 a b gx IHx hle. simpl. tauto.
  - (* GE_UnboxBox *) intros P1 psi psi0 a b gx IHx hle. simpl in *. tauto.
  - (* GE_Proj1Cong *) intros P1 psi psi0 a0 a1 gx IHx hle. simpl. tauto.
  - (* GE_Proj2Cong *) intros P1 psi psi0 a0 a1 gx IHx. simpl. tauto.
  - (* GE_Proj1Beta *) intros P1 psi psi0 b a1 a2 gx IHx hle. simpl in *. tauto.
  - (* GE_Proj2Beta *) intros P1 psi psi0 b a2 a1 gx IHx. simpl in *. tauto.
  - (* GE_SPair *) intros P1 psi a0 psi0 b0 a1 b1 cc IHc gx IHx. simpl. tauto.
  - (* GE_SSigma *) intros L P1 psi psi0 A0 B0 A1 B1 gd IHd gpt IHpt.
    destruct (atom_fresh L) as [x Hx].
    simpl. split; [ split | split ].
    + exact (proj1 IHd).
    + apply (proj2 (wf_open_var B0 0 x)). exact (proj1 (IHpt x Hx)).
    + exact (proj2 IHd).
    + apply (proj2 (wf_open_var B1 0 x)). exact (proj2 (IHpt x Hx)).
  - (* GE_TyUnit *) intros P1 psi u. simpl. tauto.
  - (* GE_TmUnit *) intros P1 psi u. simpl. tauto.
  - (* GE_Bool *) intros P1 psi u. simpl. tauto.
  - (* GE_True *) intros P1 psi u. simpl. tauto.
  - (* GE_False *) intros P1 psi u. simpl. tauto.
  - (* GE_If *) intros P1 psi a0 b0 b1 a1 b2 b3 gx IHx gy IHy gz IHz. simpl in *. tauto.
  - (* GE_IfTrue *) intros P1 psi a0 b0 b1 b2 b3 gx IHx gy IHy gz IHz. simpl in *.
    destruct IHx as [Ha _]. destruct IHy as [Hb0 Hb2]. destruct IHz as [Hb1 _].
    repeat split; assumption.
  - (* GE_IfFalse *) intros P1 psi a0 b0 b1 b3 b2 gx IHx gy IHy gz IHz. simpl in *.
    destruct IHx as [Ha _]. destruct IHy as [Hb0 _]. destruct IHz as [Hb1 Hb3].
    repeat split; assumption.
  - (* CGE_Leq *) intros P1 psi psi0 a b hle gx IHx. exact IHx.
  - (* CGE_NLeq *) intros P1 psi psi0 a b la lb hnle u. simpl.
    split; [ apply lc_wf; exact la | apply lc_wf; exact lb ].
Qed.

Lemma cgdefeq_wf : forall (P:econtext) (psi psi0:grade) (a b:tm),
  CGDefEq P psi psi0 a b -> wf 0 a /\ wf 0 b.
Proof.
  intros P psi psi0 a b H. destruct H as [P psi psi0 a b hle Hg | P psi psi0 a b la lb hnle u].
  - exact (gdefeq_wf Hg).
  - split; [ apply lc_wf; exact la | apply lc_wf; exact lb ].
Qed.

Lemma gdefeq_lc : forall (P:econtext) (psi:grade) (a b:tm),
  GDefEq P psi a b -> lc_tm a /\ lc_tm b.
Proof.
  intros P psi a b H. destruct (gdefeq_wf H) as [Ha Hb]. split; apply wf_lc; assumption.
Qed.

(* ============  Grade-respecting (parallel-reduction reflexive) terms  ============ *)

Inductive OKPar : econtext -> grade -> tm -> Prop :=
 | OK_Var : forall (P:econtext) (psi:grade) (x:tmvar) (g:grade),
     uniq P -> g <= psi -> binds x g P -> OKPar P psi (a_Var_f x)
 | OK_Type : forall (P:econtext) (psi:grade) s,
     uniq P -> OKPar P psi (a_Type s)
 | OK_Pi : forall (L:vars) (P:econtext) (psi psi0:grade) (A B:tm),
     OKPar P psi A ->
     (forall x, x \notin L -> OKPar ((x,psi0)::P) psi (open_tm_wrt_tm B (a_Var_f x))) ->
     OKPar P psi (a_Pi psi0 A B)
 | OK_Abs : forall (L:vars) (P:econtext) (psi psi0:grade) (A b:tm),
     lc_tm A ->
     (forall x, x \notin L -> OKPar ((x,psi0)::P) psi (open_tm_wrt_tm b (a_Var_f x))) ->
     OKPar P psi (a_Abs psi0 A b)
 | OK_App : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b:tm),
     OKPar P psi a -> OKCPar P psi psi0 b ->
     OKPar P psi (a_App a psi0 b)
 | OK_Refl : forall (P:econtext) (psi:grade), uniq P -> OKPar P psi a_Refl
 | OK_Transp : forall (P:econtext) (psi:grade) (a b:tm),
     OKPar P psi a -> OKPar P psi b -> OKPar P psi (a_Transp a b)
 | OK_CEq : forall (P:econtext) (psi psi0:grade) (a b:tm) (psi1:grade) (A:tm),
     lc_tm A -> OKPar P psi a -> OKPar P psi b -> psi0 <= psi ->
     OKPar P psi (a_CEq psi0 a b psi1 A)
 | OK_T : forall (P:econtext) (psi psi0:grade) (A:tm),
     OKPar P psi A -> OKPar P psi (a_T psi0 A)
 | OK_Box : forall (P:econtext) (psi psi0:grade) (a:tm),
     OKCPar P psi psi0 a -> OKPar P psi (a_Box psi0 a)
 | OK_Unbox : forall (P:econtext) (psi psi0:grade) (a:tm),
     OKPar P psi a -> psi0 <= psi -> OKPar P psi (a_Unbox psi0 a)
 | OK_SSigma : forall (L:vars) (P:econtext) (psi psi0:grade) (A B:tm),
     OKPar P psi A ->
     (forall x, x \notin L -> OKPar ((x,psi0)::P) psi (open_tm_wrt_tm B (a_Var_f x))) ->
     OKPar P psi (a_SSigma psi0 A B)
 | OK_SPair : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b:tm),
     OKCPar P psi psi0 a -> OKPar P psi b -> OKPar P psi (a_SPair a psi0 b)
 | OK_Proj1 : forall (P:econtext) (psi psi0:grade) (a:tm),
     OKPar P psi a -> psi0 <= psi -> OKPar P psi (a_Proj1 psi0 a)
 | OK_Proj2 : forall (P:econtext) (psi psi0:grade) (a:tm),
     OKPar P psi a -> OKPar P psi (a_Proj2 psi0 a)
 | OK_TyUnit : forall (P:econtext) (psi:grade), uniq P -> OKPar P psi a_TyUnit
 | OK_TmUnit : forall (P:econtext) (psi:grade), uniq P -> OKPar P psi a_TmUnit
 | OK_Bool : forall (P:econtext) (psi:grade), uniq P -> OKPar P psi a_Bool
 | OK_True : forall (P:econtext) (psi:grade), uniq P -> OKPar P psi a_True
 | OK_False : forall (P:econtext) (psi:grade), uniq P -> OKPar P psi a_False
 | OK_If : forall (P:econtext) (psi:grade) (a b0 b1:tm),
     OKPar P psi a -> OKPar P psi b0 -> OKPar P psi b1 -> OKPar P psi (a_If a b0 b1)
with OKCPar : econtext -> grade -> grade -> tm -> Prop :=
 | OKC_Leq : forall (P:econtext) (psi psi0:grade) (a:tm),
     psi0 <= psi -> OKPar P psi a -> OKCPar P psi psi0 a
 | OKC_NLeq : forall (P:econtext) (psi psi0:grade) (a:tm),
     not (psi0 <= psi) -> lc_tm a -> uniq P -> OKCPar P psi psi0 a.

Fixpoint okpar_par (P:econtext) (psi:grade) (t:tm) (o:OKPar P psi t) {struct o}
  : uniq P -> Par P psi t t :=
  match o as o0 in OKPar e s t0 return (uniq e -> Par e s t0 t0) with
  | OK_Var P1 psi1 x g u i bd => fun Hu => @Par_Var P1 psi1 x g u i bd
  | OK_Type P1 psi1 s u => fun Hu => @Par_Type P1 psi1 s u
  | OK_Pi L P1 psi1 psi0 A B ga gb => fun Hu =>
      ltac:(apply (@Par_Pi (L \u dom P1) P1 psi1 psi0 A B A B);
            [ exact (@okpar_par P1 psi1 A ga Hu)
            | intros x Hx;
              apply (@okpar_par ((x,psi0)::P1) psi1 (open_tm_wrt_tm B (a_Var_f x))
                               (gb x (@notin_union_1 x L (dom P1) Hx)));
              apply (@uniq_insert nil P1 x psi0);
              [ exact Hu | exact (@notin_union_2 x L (dom P1) Hx) ] ])
  | OK_Abs L P1 psi1 psi0 A b lA gb => fun Hu =>
      ltac:(apply (@Par_Abs (L \u dom P1) P1 psi1 psi0 A b A b);
            [ exact lA | exact lA
            | intros x Hx;
              apply (@okpar_par ((x,psi0)::P1) psi1 (open_tm_wrt_tm b (a_Var_f x))
                               (gb x (@notin_union_1 x L (dom P1) Hx)));
              apply (@uniq_insert nil P1 x psi0);
              [ exact Hu | exact (@notin_union_2 x L (dom P1) Hx) ] ])
  | OK_App P1 psi1 a psi0 b ga cb => fun Hu =>
      @Par_App P1 psi1 a psi0 b a b (@okpar_par P1 psi1 a ga Hu) (@okcpar_cpar P1 psi1 psi0 b cb Hu)
  | OK_Refl P1 psi1 u => fun Hu => @Par_Refl P1 psi1 u
  | OK_Transp P1 psi1 a b ga gb => fun Hu =>
      @Par_Transp P1 psi1 a b a b (@okpar_par P1 psi1 a ga Hu) (@okpar_par P1 psi1 b gb Hu)
  | OK_CEq P1 psi1 psi0 a b psig A lA ga gb hle => fun Hu =>
      @Par_CEq P1 psi1 psi0 a b psig A a b A lA lA
        (@okpar_par P1 psi1 a ga Hu) (@okpar_par P1 psi1 b gb Hu) hle
  | OK_T P1 psi1 psi0 A gA => fun Hu =>
      @Par_T P1 psi1 psi0 A A (@okpar_par P1 psi1 A gA Hu)
  | OK_Box P1 psi1 psi0 a ca => fun Hu =>
      @Par_Box P1 psi1 psi0 a a (@okcpar_cpar P1 psi1 psi0 a ca Hu)
  | OK_Unbox P1 psi1 psi0 a ga hle => fun Hu =>
      @Par_Unbox P1 psi1 psi0 a a (@okpar_par P1 psi1 a ga Hu) hle
  | OK_SSigma L P1 psi1 psi0 A B gA gB => fun Hu =>
      ltac:(apply (@Par_SSigma (L \u dom P1) P1 psi1 psi0 A B A B);
            [ exact (@okpar_par P1 psi1 A gA Hu)
            | intros x Hx;
              apply (@okpar_par ((x,psi0)::P1) psi1 (open_tm_wrt_tm B (a_Var_f x))
                               (gB x (@notin_union_1 x L (dom P1) Hx)));
              apply (@uniq_insert nil P1 x psi0);
              [ exact Hu | exact (@notin_union_2 x L (dom P1) Hx) ] ])
  | OK_SPair P1 psi1 a psi0 b ca gb => fun Hu =>
      @Par_SPair P1 psi1 a psi0 b a b (@okcpar_cpar P1 psi1 psi0 a ca Hu) (@okpar_par P1 psi1 b gb Hu)
  | OK_Proj1 P1 psi1 psi0 a ga hle => fun Hu =>
      @Par_Proj1Cong P1 psi1 psi0 a a (@okpar_par P1 psi1 a ga Hu) hle
  | OK_Proj2 P1 psi1 psi0 a ga => fun Hu =>
      @Par_Proj2Cong P1 psi1 psi0 a a (@okpar_par P1 psi1 a ga Hu)
  | OK_TyUnit P1 psi1 u => fun Hu => @Par_TyUnit P1 psi1 u
  | OK_TmUnit P1 psi1 u => fun Hu => @Par_TmUnit P1 psi1 u
  | OK_Bool P1 psi1 u => fun Hu => @Par_Bool P1 psi1 u
  | OK_True P1 psi1 u => fun Hu => @Par_True P1 psi1 u
  | OK_False P1 psi1 u => fun Hu => @Par_False P1 psi1 u
  | OK_If P1 psi1 a b0 b1 ga gb0 gb1 => fun Hu =>
      @Par_If P1 psi1 a b0 b1 a b0 b1
        (@okpar_par P1 psi1 a ga Hu) (@okpar_par P1 psi1 b0 gb0 Hu) (@okpar_par P1 psi1 b1 gb1 Hu)
  end
with okcpar_cpar (P:econtext) (psi psi0:grade) (t:tm) (o:OKCPar P psi psi0 t) {struct o}
  : uniq P -> CPar P psi psi0 t t :=
  match o as o0 in OKCPar e s s0 t0 return (uniq e -> CPar e s s0 t0 t0) with
  | OKC_Leq P1 psi1 psi0 a hle ga => fun Hu =>
      @CPar_Leq P1 psi1 psi0 a a hle (@okpar_par P1 psi1 a ga Hu)
  | OKC_NLeq P1 psi1 psi0 a hnle la u => fun Hu =>
      @CPar_Nleq P1 psi1 psi0 a a la la hnle u
  end.

(* ============  Substitution of a fresh variable is the identity  ============ *)

Lemma subst_fv_id : forall (t:tm) (c:tm) (x:atom),
  x \notin fv_tm t -> subst_tm c x t = t.
Proof.
  intros t. induction t as [| |psi A IHA Btx IHB|psi A IHA b IHb|a0 IHa psi b IHb
                 |s|n|y|psi a0 IHa b IHb psi0 A IHA| |a0 IHa b IHb|psi A IHA
                 |psi a0 IHa|psi a0 IHa|psi A IHA Btx IHB|a0 IHa psi b IHb|psi a0 IHa
                 |psi a0 IHa| | | |a0 IHa b0 IHb0 b1 IHb1];
  intros c x Hx; simpl in *; try reflexivity.
  - (* Pi *) apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    rewrite (IHA c x HA) (IHB c x HB). reflexivity.
  - (* Abs *) apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    rewrite (IHA c x HA) (IHb c x HB). reflexivity.
  - (* App *) apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    rewrite (IHa c x HA) (IHb c x HB). reflexivity.
  - (* Var_f *) have Hyx : y <> x := @notin_singleton_1 y x Hx.
    destruct (@eq_dec tmvar EqDec_eq_of_X y x) as [E|NE]; cbn [is_left].
    + exfalso; exact (Hyx E).
    + reflexivity.
  - (* CEq *) apply notin_union_1 in Hx as Ha. apply notin_union_2 in Hx as Hbc.
    apply notin_union_1 in Hbc as Hb. apply notin_union_2 in Hbc as HA.
    rewrite (IHa c x Ha) (IHb c x Hb) (IHA c x HA). reflexivity.
  - (* Transp *) apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    rewrite (IHa c x HA) (IHb c x HB). reflexivity.
  - (* T *) rewrite (IHA c x Hx). reflexivity.
  - (* Box *) rewrite (IHa c x Hx). reflexivity.
  - (* Unbox *) rewrite (IHa c x Hx). reflexivity.
  - (* SSigma *) apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    rewrite (IHA c x HA) (IHB c x HB). reflexivity.
  - (* SPair *) apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    rewrite (IHa c x HA) (IHb c x HB). reflexivity.
  - (* Proj1 *) rewrite (IHa c x Hx). reflexivity.
  - (* Proj2 *) rewrite (IHa c x Hx). reflexivity.
  - (* If *) apply notin_union_1 in Hx as Ha. apply notin_union_2 in Hx as Hbc.
    apply notin_union_1 in Hbc as Hb0. apply notin_union_2 in Hbc as Hb1.
    rewrite (IHa c x Ha) (IHb0 c x Hb0) (IHb1 c x Hb1). reflexivity.
Qed.

(* ============  Weakening of the OK predicates  ============ *)

Unset Implicit Arguments.
Scheme OKPar_mutP := Induction for OKPar Sort Prop
  with OKCPar_mutP := Induction for OKCPar Sort Prop.
Set Implicit Arguments.

Lemma okpar_insert : forall (P:econtext) (psi:grade) (t:tm), OKPar P psi t ->
  forall (Q1 Q2:econtext) (yy:atom) (gg:grade), P = Q1++Q2 -> yy \notin dom P ->
    OKPar (Q1++(yy,gg)::Q2) psi t.
Proof.
  intros P psig t H.
  refine (OKPar_mutP
    (fun (e:econtext) (s:grade) (t:tm) (_:OKPar e s t) =>
       forall (Q1 Q2:econtext) (yy:atom) (gg:grade), e = Q1++Q2 -> yy \notin dom e ->
         OKPar (Q1++(yy,gg)::Q2) s t)
    (fun (e:econtext) (s s0:grade) (t:tm) (_:OKCPar e s s0 t) =>
       forall (Q1 Q2:econtext) (yy:atom) (gg:grade), e = Q1++Q2 -> yy \notin dom e ->
         OKCPar (Q1++(yy,gg)::Q2) s s0 t)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P psig t H).
  - (* OK_Var *) intros P1 psi x g u i bd Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_Var (Q1++(yy,gg)::Q2) psi x g).
    + apply uniq_insert; assumption.
    + exact i.
    + apply binds_insert; assumption.
  - (* OK_Type *) intros P1 psi s u Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_Type (Q1++(yy,gg)::Q2) psi s). apply uniq_insert; assumption.
  - (* OK_Pi *) intros L P1 psi psi0 A B ga IHa gb IHb Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_Pi (L \u {{yy}}) (Q1++(yy,gg)::Q2) psi psi0 A B).
    + apply (IHa Q1 Q2 yy gg eq_refl Hy).
    + intros x Hx.
      have HxL : x \notin L := @notin_union_1 x L {{yy}} Hx.
      have Hxs : x \notin {{yy}} := @notin_union_2 x L {{yy}} Hx.
      have Hyx : yy <> x := @notin_singleton_1 yy x Hxs.
      have Hxy : x <> yy := fun E => Hyx (eq_sym E).
      have Hfr : yy \notin dom ((x,psi0)::(Q1++Q2)) by
        (simpl; apply notin_add; [ exact Hxy | exact Hy ]).
      exact (IHb x HxL ((x,psi0)::Q1) Q2 yy gg eq_refl Hfr).
  - (* OK_Abs *) intros L P1 psi psi0 A b lA gb IHb Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_Abs (L \u {{yy}}) (Q1++(yy,gg)::Q2) psi psi0 A b lA).
    intros x Hx.
    have HxL : x \notin L := @notin_union_1 x L {{yy}} Hx.
    have Hxs : x \notin {{yy}} := @notin_union_2 x L {{yy}} Hx.
    have Hyx : yy <> x := @notin_singleton_1 yy x Hxs.
    have Hxy : x <> yy := fun E => Hyx (eq_sym E).
    have Hfr : yy \notin dom ((x,psi0)::(Q1++Q2)) by
      (simpl; apply notin_add; [ exact Hxy | exact Hy ]).
    exact (IHb x HxL ((x,psi0)::Q1) Q2 yy gg eq_refl Hfr).
  - (* OK_App *) intros P1 psi a psi0 b ga IHa cb IHcb Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_App (Q1++(yy,gg)::Q2) psi a psi0 b).
    + apply (IHa Q1 Q2 yy gg eq_refl Hy).
    + apply (IHcb Q1 Q2 yy gg eq_refl Hy).
  - (* OK_Refl *) intros P1 psi u Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_Refl (Q1++(yy,gg)::Q2) psi). apply uniq_insert; assumption.
  - (* OK_Transp *) intros P1 psi a b ga IHa gb IHb Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_Transp (Q1++(yy,gg)::Q2) psi a b).
    + apply (IHa Q1 Q2 yy gg eq_refl Hy).
    + apply (IHb Q1 Q2 yy gg eq_refl Hy).
  - (* OK_CEq *) intros P1 psi psi0 a b psiq A lA ga IHa gb IHb hle Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_CEq (Q1++(yy,gg)::Q2) psi psi0 a b psiq A lA).
    + apply (IHa Q1 Q2 yy gg eq_refl Hy).
    + apply (IHb Q1 Q2 yy gg eq_refl Hy).
    + exact hle.
  - (* OK_T *) intros P1 psi psi0 A ga IHa Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_T (Q1++(yy,gg)::Q2) psi psi0 A).
    apply (IHa Q1 Q2 yy gg eq_refl Hy).
  - (* OK_Box *) intros P1 psi psi0 a ca IHca Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_Box (Q1++(yy,gg)::Q2) psi psi0 a).
    apply (IHca Q1 Q2 yy gg eq_refl Hy).
  - (* OK_Unbox *) intros P1 psi psi0 a ga IHa hle Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_Unbox (Q1++(yy,gg)::Q2) psi psi0 a).
    + apply (IHa Q1 Q2 yy gg eq_refl Hy).
    + exact hle.
  - (* OK_SSigma *) intros L P1 psi psi0 A B ga IHa gb IHb Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_SSigma (L \u {{yy}}) (Q1++(yy,gg)::Q2) psi psi0 A B).
    + apply (IHa Q1 Q2 yy gg eq_refl Hy).
    + intros x Hx.
      have HxL : x \notin L := @notin_union_1 x L {{yy}} Hx.
      have Hxs : x \notin {{yy}} := @notin_union_2 x L {{yy}} Hx.
      have Hyx : yy <> x := @notin_singleton_1 yy x Hxs.
      have Hxy : x <> yy := fun E => Hyx (eq_sym E).
      have Hfr : yy \notin dom ((x,psi0)::(Q1++Q2)) by
        (simpl; apply notin_add; [ exact Hxy | exact Hy ]).
      exact (IHb x HxL ((x,psi0)::Q1) Q2 yy gg eq_refl Hfr).
  - (* OK_SPair *) intros P1 psi a psi0 b ca IHca gb IHb Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_SPair (Q1++(yy,gg)::Q2) psi a psi0 b).
    + apply (IHca Q1 Q2 yy gg eq_refl Hy).
    + apply (IHb Q1 Q2 yy gg eq_refl Hy).
  - (* OK_Proj1 *) intros P1 psi psi0 a ga IHa hle Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_Proj1 (Q1++(yy,gg)::Q2) psi psi0 a).
    + apply (IHa Q1 Q2 yy gg eq_refl Hy).
    + exact hle.
  - (* OK_Proj2 *) intros P1 psi psi0 a ga IHa Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_Proj2 (Q1++(yy,gg)::Q2) psi psi0 a).
    apply (IHa Q1 Q2 yy gg eq_refl Hy).
  - (* OK_TyUnit *) intros P1 psi u Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_TyUnit (Q1++(yy,gg)::Q2) psi). apply uniq_insert; assumption.
  - (* OK_TmUnit *) intros P1 psi u Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_TmUnit (Q1++(yy,gg)::Q2) psi). apply uniq_insert; assumption.
  - (* OK_Bool *) intros P1 psi u Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_Bool (Q1++(yy,gg)::Q2) psi). apply uniq_insert; assumption.
  - (* OK_True *) intros P1 psi u Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_True (Q1++(yy,gg)::Q2) psi). apply uniq_insert; assumption.
  - (* OK_False *) intros P1 psi u Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_False (Q1++(yy,gg)::Q2) psi). apply uniq_insert; assumption.
  - (* OK_If *) intros P1 psi a b0 b1 ga IHa gb0 IHb0 gb1 IHb1 Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OK_If (Q1++(yy,gg)::Q2) psi a b0 b1).
    + apply (IHa Q1 Q2 yy gg eq_refl Hy).
    + apply (IHb0 Q1 Q2 yy gg eq_refl Hy).
    + apply (IHb1 Q1 Q2 yy gg eq_refl Hy).
  - (* OKC_Leq *) intros P1 psi psi0 a hle ga IHa Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OKC_Leq (Q1++(yy,gg)::Q2) psi psi0 a hle).
    apply (IHa Q1 Q2 yy gg eq_refl Hy).
  - (* OKC_NLeq *) intros P1 psi psi0 a hnle la u Q1 Q2 yy gg Heq Hy. subst P1.
    eapply (@OKC_NLeq (Q1++(yy,gg)::Q2) psi psi0 a hnle la).
    apply uniq_insert; assumption.
Qed.

(* ============  OK predicates are stable under substitution  ============ *)

Lemma ok_cond_extend : forall (P:econtext) (psi:grade) (xv:atom) (cv:tm) (z:atom) (psi0:grade),
  z <> xv -> z \notin dom P ->
  (OKPar P psi cv \/ (forall g:grade, binds xv g P -> ~ (g <= psi))) ->
  (OKPar ((z,psi0)::P) psi cv \/
   (forall g:grade, binds xv g ((z,psi0)::P) -> ~ (g <= psi))).
Proof.
  intros P psi xv cv z psi0 Hzx HzP [Hr|Hn].
  - left. exact (@okpar_insert P psi cv Hr nil P z psi0 eq_refl HzP).
  - right. intros g Hb.
    apply (Hn g). apply EnvImpl.binds_cons_1 in Hb.
    destruct Hb as [[E1 E2]|Hb]; [ exfalso; apply Hzx; symmetry; exact E1 | exact Hb ].
Qed.

Lemma okpar_subst_gen : forall (P:econtext) (psi:grade) (t:tm), OKPar P psi t ->
  forall (xv:atom) (cv:tm), lc_tm cv ->
  (OKPar P psi cv \/ (forall g:grade, binds xv g P -> ~ (g <= psi))) ->
  OKPar P psi (subst_tm cv xv t).
Proof.
  intros P psig t H.
  refine (OKPar_mutP
    (fun (e:econtext) (s:grade) (t:tm) (_:OKPar e s t) =>
       forall (xv:atom) (cv:tm), lc_tm cv ->
       (OKPar e s cv \/ (forall g:grade, binds xv g e -> ~ (g <= s))) ->
       OKPar e s (subst_tm cv xv t))
    (fun (e:econtext) (s s0:grade) (t:tm) (_:OKCPar e s s0 t) =>
       forall (xv:atom) (cv:tm), lc_tm cv ->
       (OKPar e s cv \/ (forall g:grade, binds xv g e -> ~ (g <= s))) ->
       OKCPar e s s0 (subst_tm cv xv t))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P psig t H).
  - (* OK_Var *) intros P1 psi x g u i bd xv cv Hlc Hcond.
    destruct (@eq_dec tmvar EqDec_eq_of_X x xv) as [E|NE].
    + subst x. rewrite (@subst_var_eq cv xv).
      destruct Hcond as [Hr|Hn]; [ exact Hr | exfalso; exact (Hn g bd i) ].
    + have Hne : xv <> x. { symmetry; exact NE. }
      rewrite (@subst_var_neq cv xv x Hne).
      eapply (@OK_Var P1 psi x g); [ exact u | exact i | exact bd ].
  - (* OK_Type *) intros P1 psi s u xv cv Hlc Hcond. simpl.
    eapply (@OK_Type P1 psi s); exact u.
  - (* OK_Pi *) intros L P1 psi psi0 A B ga IHa gb IHb xv cv Hlc Hcond. simpl.
    eapply (@OK_Pi ((((L \u dom P1) \u {{xv}}))) P1 psi psi0
              (subst_tm cv xv A) (subst_tm cv xv B)).
    + exact (IHa xv cv Hlc Hcond).
    + intros z Hz.
      have Hz1 : z \notin (L \u dom P1). { exact (@notin_union_1 z (L \u dom P1) {{xv}} Hz). }
      have Hz2 : z \notin {{xv}}. { exact (@notin_union_2 z (L \u dom P1) {{xv}} Hz). }
      have HzL : z \notin L. { exact (@notin_union_1 z L (dom P1) Hz1). }
      have Hzd : z \notin dom P1. { exact (@notin_union_2 z L (dom P1) Hz1). }
      have Hxvz : xv <> z. { exact (@notin_singleton_1 xv z Hz2). }
      have Hzxv : z <> xv. { intro E; apply Hxvz; symmetry; exact E. }
      have Hcond' := @ok_cond_extend P1 psi xv cv z psi0 Hzxv Hzd Hcond.
      pose proof (IHb z HzL xv cv Hlc Hcond') as Hres.
      rewrite (@subst_open B (a_Var_f z) cv xv Hlc) (@subst_var_neq cv xv z Hxvz) in Hres.
      exact Hres.
  - (* OK_Abs *) intros L P1 psi psi0 A b lA gb IHb xv cv Hlc Hcond. simpl.
    eapply (@OK_Abs ((((L \u dom P1) \u {{xv}}))) P1 psi psi0
              (subst_tm cv xv A) (subst_tm cv xv b)).
    + exact (@lc_subst A lA cv xv Hlc).
    + intros z Hz.
      have Hz1 : z \notin (L \u dom P1). { exact (@notin_union_1 z (L \u dom P1) {{xv}} Hz). }
      have Hz2 : z \notin {{xv}}. { exact (@notin_union_2 z (L \u dom P1) {{xv}} Hz). }
      have HzL : z \notin L. { exact (@notin_union_1 z L (dom P1) Hz1). }
      have Hzd : z \notin dom P1. { exact (@notin_union_2 z L (dom P1) Hz1). }
      have Hxvz : xv <> z. { exact (@notin_singleton_1 xv z Hz2). }
      have Hzxv : z <> xv. { intro E; apply Hxvz; symmetry; exact E. }
      have Hcond' := @ok_cond_extend P1 psi xv cv z psi0 Hzxv Hzd Hcond.
      pose proof (IHb z HzL xv cv Hlc Hcond') as Hres.
      rewrite (@subst_open b (a_Var_f z) cv xv Hlc) (@subst_var_neq cv xv z Hxvz) in Hres.
      exact Hres.
  - (* OK_App *) intros P1 psi a psi0 b ga IHa cb IHcb xv cv Hlc Hcond. simpl.
    eapply (@OK_App P1 psi (subst_tm cv xv a) psi0 (subst_tm cv xv b)).
    + exact (IHa xv cv Hlc Hcond).
    + exact (IHcb xv cv Hlc Hcond).
  - (* OK_Refl *) intros P1 psi u xv cv Hlc Hcond. simpl. eapply (@OK_Refl P1 psi); exact u.
  - (* OK_Transp *) intros P1 psi a b ga IHa gb IHb xv cv Hlc Hcond. simpl.
    eapply (@OK_Transp P1 psi (subst_tm cv xv a) (subst_tm cv xv b)).
    + exact (IHa xv cv Hlc Hcond).
    + exact (IHb xv cv Hlc Hcond).
  - (* OK_CEq *) intros P1 psi psi0 a b psiq A lA ga IHa gb IHb hle xv cv Hlc Hcond. simpl.
    eapply (@OK_CEq P1 psi psi0 (subst_tm cv xv a) (subst_tm cv xv b) psiq
              (subst_tm cv xv A)).
    + exact (@lc_subst A lA cv xv Hlc).
    + exact (IHa xv cv Hlc Hcond).
    + exact (IHb xv cv Hlc Hcond).
    + exact hle.
  - (* OK_T *) intros P1 psi psi0 A ga IHa xv cv Hlc Hcond. simpl.
    eapply (@OK_T P1 psi psi0 (subst_tm cv xv A)); exact (IHa xv cv Hlc Hcond).
  - (* OK_Box *) intros P1 psi psi0 a ca IHca xv cv Hlc Hcond. simpl.
    eapply (@OK_Box P1 psi psi0 (subst_tm cv xv a)); exact (IHca xv cv Hlc Hcond).
  - (* OK_Unbox *) intros P1 psi psi0 a ga IHa hle xv cv Hlc Hcond. simpl.
    eapply (@OK_Unbox P1 psi psi0 (subst_tm cv xv a)).
    + exact (IHa xv cv Hlc Hcond).
    + exact hle.
  - (* OK_SSigma *) intros L P1 psi psi0 A B ga IHa gb IHb xv cv Hlc Hcond. simpl.
    eapply (@OK_SSigma ((((L \u dom P1) \u {{xv}}))) P1 psi psi0
              (subst_tm cv xv A) (subst_tm cv xv B)).
    + exact (IHa xv cv Hlc Hcond).
    + intros z Hz.
      have Hz1 : z \notin (L \u dom P1). { exact (@notin_union_1 z (L \u dom P1) {{xv}} Hz). }
      have Hz2 : z \notin {{xv}}. { exact (@notin_union_2 z (L \u dom P1) {{xv}} Hz). }
      have HzL : z \notin L. { exact (@notin_union_1 z L (dom P1) Hz1). }
      have Hzd : z \notin dom P1. { exact (@notin_union_2 z L (dom P1) Hz1). }
      have Hxvz : xv <> z. { exact (@notin_singleton_1 xv z Hz2). }
      have Hzxv : z <> xv. { intro E; apply Hxvz; symmetry; exact E. }
      have Hcond' := @ok_cond_extend P1 psi xv cv z psi0 Hzxv Hzd Hcond.
      pose proof (IHb z HzL xv cv Hlc Hcond') as Hres.
      rewrite (@subst_open B (a_Var_f z) cv xv Hlc) (@subst_var_neq cv xv z Hxvz) in Hres.
      exact Hres.
  - (* OK_SPair *) intros P1 psi a psi0 b ca IHca gb IHb xv cv Hlc Hcond. simpl.
    eapply (@OK_SPair P1 psi (subst_tm cv xv a) psi0 (subst_tm cv xv b)).
    + exact (IHca xv cv Hlc Hcond).
    + exact (IHb xv cv Hlc Hcond).
  - (* OK_Proj1 *) intros P1 psi psi0 a ga IHa hle xv cv Hlc Hcond. simpl.
    eapply (@OK_Proj1 P1 psi psi0 (subst_tm cv xv a)).
    + exact (IHa xv cv Hlc Hcond).
    + exact hle.
  - (* OK_Proj2 *) intros P1 psi psi0 a ga IHa xv cv Hlc Hcond. simpl.
    eapply (@OK_Proj2 P1 psi psi0 (subst_tm cv xv a)); exact (IHa xv cv Hlc Hcond).
  - (* OK_TyUnit *) intros P1 psi u xv cv Hlc Hcond. simpl. eapply (@OK_TyUnit P1 psi); exact u.
  - (* OK_TmUnit *) intros P1 psi u xv cv Hlc Hcond. simpl. eapply (@OK_TmUnit P1 psi); exact u.
  - (* OK_Bool *) intros P1 psi u xv cv Hlc Hcond. simpl. eapply (@OK_Bool P1 psi); exact u.
  - (* OK_True *) intros P1 psi u xv cv Hlc Hcond. simpl. eapply (@OK_True P1 psi); exact u.
  - (* OK_False *) intros P1 psi u xv cv Hlc Hcond. simpl. eapply (@OK_False P1 psi); exact u.
  - (* OK_If *) intros P1 psi a b0 b1 ga IHa gb0 IHb0 gb1 IHb1 xv cv Hlc Hcond. simpl.
    eapply (@OK_If P1 psi (subst_tm cv xv a) (subst_tm cv xv b0) (subst_tm cv xv b1)).
    + exact (IHa xv cv Hlc Hcond).
    + exact (IHb0 xv cv Hlc Hcond).
    + exact (IHb1 xv cv Hlc Hcond).
  - (* OKC_Leq *) intros P1 psi psi0 a hle ga IHa xv cv Hlc Hcond. simpl.
    eapply (@OKC_Leq P1 psi psi0 (subst_tm cv xv a) hle).
    exact (IHa xv cv Hlc Hcond).
  - (* OKC_NLeq *) intros P1 psi psi0 a hnle la u xv cv Hlc Hcond. simpl.
    eapply (@OKC_NLeq P1 psi psi0 (subst_tm cv xv a) hnle
              (@lc_subst a la cv xv Hlc) u).
Qed.

Lemma okcpar_subst_gen : forall (P:econtext) (psi psi0:grade) (t:tm), OKCPar P psi psi0 t ->
  forall (xv:atom) (cv:tm), lc_tm cv ->
  (OKPar P psi cv \/ (forall g:grade, binds xv g P -> ~ (g <= psi))) ->
  OKCPar P psi psi0 (subst_tm cv xv t).
Proof.
  intros P psi psi0 t H xv cv Hlc Hcond.
  destruct H as [P1 psib psia a hle ga | P1 psib psia a hnle la u].
  - eapply (@OKC_Leq P1 psib psia (subst_tm cv xv a) hle).
    exact (@okpar_subst_gen P1 psib a ga xv cv Hlc Hcond).
  - eapply (@OKC_NLeq P1 psib psia (subst_tm cv xv a) hnle).
    + exact (@lc_subst a la cv xv Hlc).
    + exact u.
Qed.
(* ============  OK terms are well-scoped  ============ *)

Lemma okpar_lc : forall (P:econtext) (psi:grade) (t:tm),
  OKPar P psi t -> wf 0 t.
Proof.
  intros P psig t H.
  refine (OKPar_mutP
    (fun (e:econtext) (s:grade) (t:tm) (_:OKPar e s t) => wf 0 t)
    (fun (e:econtext) (s s0:grade) (t:tm) (_:OKCPar e s s0 t) => wf 0 t)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P psig t H).
  - (* OK_Var *) intros P1 psi x g u i bd. simpl. exact I.
  - (* OK_Type *) intros P1 psi s u. simpl. exact I.
  - (* OK_Pi *) intros L P1 psi psi0 A B ga IHa gb IHb. simpl. split.
    + exact IHa.
    + destruct (atom_fresh L) as [x Hx].
      apply (proj2 (wf_open_var B 0 x)). exact (IHb x Hx).
  - (* OK_Abs *) intros L P1 psi psi0 A b lA gb IHb. simpl. split.
    + exact (@lc_wf A lA).
    + destruct (atom_fresh L) as [x Hx].
      apply (proj2 (wf_open_var b 0 x)). exact (IHb x Hx).
  - (* OK_App *) intros P1 psi a psi0 b ga IHa cb IHcb. simpl. split; assumption.
  - (* OK_Refl *) intros P1 psi u. simpl. exact I.
  - (* OK_Transp *) intros P1 psi a b ga IHa gb IHb. simpl. split; assumption.
  - (* OK_CEq *) intros P1 psi psi0 a b psiq A lA ga IHa gb IHb hle. simpl.
    split; [ exact IHa | split; [ exact IHb | exact (@lc_wf A lA) ] ].
  - (* OK_T *) intros P1 psi psi0 A ga IHa. simpl. exact IHa.
  - (* OK_Box *) intros P1 psi psi0 a ca IHca. simpl. exact IHca.
  - (* OK_Unbox *) intros P1 psi psi0 a ga IHa hle. simpl. exact IHa.
  - (* OK_SSigma *) intros L P1 psi psi0 A B ga IHa gb IHb. simpl. split.
    + exact IHa.
    + destruct (atom_fresh L) as [x Hx].
      apply (proj2 (wf_open_var B 0 x)). exact (IHb x Hx).
  - (* OK_SPair *) intros P1 psi a psi0 b ca IHca gb IHb. simpl. split; assumption.
  - (* OK_Proj1 *) intros P1 psi psi0 a ga IHa hle. simpl. exact IHa.
  - (* OK_Proj2 *) intros P1 psi psi0 a ga IHa. simpl. exact IHa.
  - (* OK_TyUnit *) intros P1 psi u. simpl. exact I.
  - (* OK_TmUnit *) intros P1 psi u. simpl. exact I.
  - (* OK_Bool *) intros P1 psi u. simpl. exact I.
  - (* OK_True *) intros P1 psi u. simpl. exact I.
  - (* OK_False *) intros P1 psi u. simpl. exact I.
  - (* OK_If *) intros P1 psi a b0 b1 ga IHa gb0 IHb0 gb1 IHb1. simpl.
    split; [ exact IHa | split; assumption ].
  - (* OKC_Leq *) intros P1 psi psi0 a hle ga IHa. simpl. exact IHa.
  - (* OKC_NLeq *) intros P1 psi psi0 a hnle la u. simpl. exact (@lc_wf a la).
Qed.

Lemma okcpar_lc : forall (P:econtext) (psi psi0:grade) (t:tm),
  OKCPar P psi psi0 t -> wf 0 t.
Proof.
  intros P psi psi0 t H. destruct H as [P1 psib psia a hle ga | P1 psib psia a hnle la u].
  - exact (@okpar_lc P1 psib a ga).
  - exact (@lc_wf a la).
Qed.

Lemma okpar_lc_tm : forall (P:econtext) (psi:grade) (t:tm),
  OKPar P psi t -> lc_tm t.
Proof. intros P psi t H. apply wf_lc. exact (@okpar_lc P psi t H). Qed.

Lemma okcpar_lc_tm : forall (P:econtext) (psi psi0:grade) (t:tm),
  OKCPar P psi psi0 t -> lc_tm t.
Proof. intros P psi psi0 t H. apply wf_lc. exact (@okcpar_lc P psi psi0 t H). Qed.

(* ============  Removing an unused context binding  ============ *)

Lemma binds_drop : forall (Q1 Q2:econtext) (xx:atom) (gg:grade) (x':atom) (g':grade),
  binds x' g' (Q1++(xx,gg)::Q2) -> x' <> xx -> binds x' g' (Q1++Q2).
Proof.
  intros Q1. induction Q1 as [|(a,h) Q1' IH]; intros Q2 xx gg x' g' H Hne; simpl in *.
  - destruct H as [E|Hin].
    + injection E as Ex Eg. exfalso; apply Hne; symmetry; exact Ex.
    + exact Hin.
  - destruct H as [E|Hin].
    + left; exact E.
    + right; apply (IH Q2 xx gg x' g'); assumption.
Qed.

Lemma notin_dom_drop : forall (Q1 Q2:econtext) (xx:atom) (gg:grade) (a:atom),
  a \notin dom (Q1++(xx,gg)::Q2) -> a \notin dom (Q1++Q2).
Proof.
  intros Q1. induction Q1 as [|(b,h) Q1' IH]; intros Q2 xx gg a H; simpl in *.
  - apply notin_add_2 in H. exact H.
  - have Hba : b <> a. { apply notin_add_1 in H. exact H. }
    have Hd : a \notin dom (Q1'++(xx,gg)::Q2). { apply notin_add_2 in H. exact H. }
    apply IH in Hd.
    apply notin_add; [ exact Hba | exact Hd ].
Qed.

Lemma uniq_drop : forall (Q1 Q2:econtext) (xx:atom) (gg:grade),
  uniq (Q1++(xx,gg)::Q2) -> uniq (Q1++Q2).
Proof.
  intros Q1. induction Q1 as [|(a,h) Q1' IH]; intros Q2 xx gg u; simpl in *.
  - change (uniq (one (xx,gg) ++ Q2)) in u.
    inversion u as [| ? ? ? Hu Hb]; subst. exact Hu.
  - change (uniq (one (a,h) ++ (Q1'++(xx,gg)::Q2))) in u.
    inversion u as [| ? ? ? Hu Hb]; subst.
    have IH' : uniq (Q1'++Q2) := IH Q2 xx gg Hu.
    change (uniq (one (a,h) ++ (Q1'++Q2))).
    apply EnvImpl.uniq_push.
    + exact IH'.
    + apply (@notin_dom_drop Q1' Q2 xx gg a). exact Hb.
Qed.

Lemma fv_open_rec : forall (t:tm) (k:nat) (y:atom) (x:atom),
  x \notin fv_tm t -> x <> y ->
  x \notin fv_tm (open_tm_wrt_tm_rec k (a_Var_f y) t).
Proof.
  intros t. induction t as [| |psi A IHA Btx IHB|psi A IHA b IHb|a0 IHa psi b IHb
                 |s|n|z|psi a0 IHa b IHb psi0 A IHA| |a0 IHa b IHb|psi A IHA
                 |psi a0 IHa|psi a0 IHa|psi A IHA Btx IHB|a0 IHa psi b IHb|psi a0 IHa
                 |psi a0 IHa| | | |a0 IHa b0 IHb0 b1 IHb1];
  intros k y x Hx Hxy; simpl in *.
  - exact Hx. - exact Hx.
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHA k y x HA Hxy).
    + exact (IHB (S k) y x HB Hxy).
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHA k y x HA Hxy).
    + exact (IHb (S k) y x HB Hxy).
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHa k y x HA Hxy).
    + exact (IHb k y x HB Hxy).
  - exact Hx.
  - cbn [open_tm_wrt_tm_rec]. destruct (lt_eq_lt_dec n k) as [[H|H]|H]; cbn [fv_tm].
    + apply notin_empty.
    + apply notin_singleton. symmetry; exact Hxy.
    + apply notin_empty.
  - exact Hx.
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as Hbc.
    apply notin_union_1 in Hbc as HB. apply notin_union_2 in Hbc as HC.
    apply notin_union.
    + exact (IHa k y x HA Hxy).
    + apply notin_union.
      * exact (IHb k y x HB Hxy).
      * exact (IHA k y x HC Hxy).
  - exact Hx.
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHa k y x HA Hxy).
    + exact (IHb k y x HB Hxy).
  - exact (IHA k y x Hx Hxy).
  - exact (IHa k y x Hx Hxy).
  - exact (IHa k y x Hx Hxy).
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHA k y x HA Hxy).
    + exact (IHB (S k) y x HB Hxy).
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHa k y x HA Hxy).
    + exact (IHb k y x HB Hxy).
  - exact (IHa k y x Hx Hxy).
  - exact (IHa k y x Hx Hxy).
  - exact Hx. - exact Hx. - exact Hx.
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as Hbc.
    apply notin_union_1 in Hbc as HB. apply notin_union_2 in Hbc as HC.
    apply notin_union.
    + exact (IHa k y x HA Hxy).
    + apply notin_union.
      * exact (IHb0 k y x HB Hxy).
      * exact (IHb1 k y x HC Hxy).
Qed.

Lemma okpar_drop : forall (P:econtext) (psi:grade) (t:tm), OKPar P psi t ->
  forall (Q1 Q2:econtext) (xx:atom) (gg:grade),
    P = Q1++(xx,gg)::Q2 -> xx \notin fv_tm t -> OKPar (Q1++Q2) psi t.
Proof.
  intros P psig t H.
  refine (OKPar_mutP
    (fun (e:econtext) (s:grade) (t:tm) (_:OKPar e s t) =>
       forall (Q1 Q2:econtext) (xx:atom) (gg:grade),
         e = Q1++(xx,gg)::Q2 -> xx \notin fv_tm t -> OKPar (Q1++Q2) s t)
    (fun (e:econtext) (s s0:grade) (t:tm) (_:OKCPar e s s0 t) =>
       forall (Q1 Q2:econtext) (xx:atom) (gg:grade),
         e = Q1++(xx,gg)::Q2 -> xx \notin fv_tm t -> OKCPar (Q1++Q2) s s0 t)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P psig t H).
  - (* OK_Var *) intros P1 psi x g u i bd Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    have Hxne : x <> xx := @notin_singleton_1 x xx Hfv.
    eapply (@OK_Var (Q1++Q2) psi x g).
    + apply (@uniq_drop Q1 Q2 xx gg); exact u.
    + exact i.
    + apply (@binds_drop Q1 Q2 xx gg x g); assumption.
  - (* OK_Type *) intros P1 psi s u Q1 Q2 xx gg Heq Hfv. subst P1.
    eapply (@OK_Type (Q1++Q2) psi s). apply (@uniq_drop Q1 Q2 xx gg); exact u.
  - (* OK_Pi *) intros L P1 psi psi0 A B ga IHa gb IHb Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    apply notin_union_1 in Hfv as HA. apply notin_union_2 in Hfv as HB.
    eapply (@OK_Pi (L \u {{xx}}) (Q1++Q2) psi psi0 A B).
    + exact (IHa Q1 Q2 xx gg eq_refl HA).
    + intros y Hy.
      have HyL : y \notin L := @notin_union_1 y L {{xx}} Hy.
      have Hys : y \notin {{xx}} := @notin_union_2 y L {{xx}} Hy.
      have Hxy : xx <> y := @notin_singleton_1 xx y Hys.
      exact (IHb y HyL ((y,psi0)::Q1) Q2 xx gg eq_refl
               (@fv_open_rec B 0 y xx HB Hxy)).
  - (* OK_Abs *) intros L P1 psi psi0 A b lA gb IHb Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    apply notin_union_2 in Hfv as HB.
    eapply (@OK_Abs (L \u {{xx}}) (Q1++Q2) psi psi0 A b lA).
    intros y Hy.
    have HyL : y \notin L := @notin_union_1 y L {{xx}} Hy.
    have Hys : y \notin {{xx}} := @notin_union_2 y L {{xx}} Hy.
    have Hxy : xx <> y := @notin_singleton_1 xx y Hys.
    exact (IHb y HyL ((y,psi0)::Q1) Q2 xx gg eq_refl
             (@fv_open_rec b 0 y xx HB Hxy)).
  - (* OK_App *) intros P1 psi a psi0 b ga IHa cb IHcb Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    apply notin_union_1 in Hfv as HA. apply notin_union_2 in Hfv as HB.
    eapply (@OK_App (Q1++Q2) psi a psi0 b).
    + exact (IHa Q1 Q2 xx gg eq_refl HA).
    + exact (IHcb Q1 Q2 xx gg eq_refl HB).
  - (* OK_Refl *) intros P1 psi u Q1 Q2 xx gg Heq Hfv. subst P1.
    eapply (@OK_Refl (Q1++Q2) psi). apply (@uniq_drop Q1 Q2 xx gg); exact u.
  - (* OK_Transp *) intros P1 psi a b ga IHa gb IHb Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    apply notin_union_1 in Hfv as HA. apply notin_union_2 in Hfv as HB.
    eapply (@OK_Transp (Q1++Q2) psi a b).
    + exact (IHa Q1 Q2 xx gg eq_refl HA).
    + exact (IHb Q1 Q2 xx gg eq_refl HB).
  - (* OK_CEq *) intros P1 psi psi0 a b psiq A lA ga IHa gb IHb hle Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    apply notin_union_1 in Hfv as HA. apply notin_union_2 in Hfv as Hbc.
    apply notin_union_1 in Hbc as HB. apply notin_union_2 in Hbc as HC.
    eapply (@OK_CEq (Q1++Q2) psi psi0 a b psiq A lA).
    + exact (IHa Q1 Q2 xx gg eq_refl HA).
    + exact (IHb Q1 Q2 xx gg eq_refl HB).
    + exact hle.
  - (* OK_T *) intros P1 psi psi0 A ga IHa Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    eapply (@OK_T (Q1++Q2) psi psi0 A). exact (IHa Q1 Q2 xx gg eq_refl Hfv).
  - (* OK_Box *) intros P1 psi psi0 a ca IHca Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    eapply (@OK_Box (Q1++Q2) psi psi0 a). exact (IHca Q1 Q2 xx gg eq_refl Hfv).
  - (* OK_Unbox *) intros P1 psi psi0 a ga IHa hle Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    eapply (@OK_Unbox (Q1++Q2) psi psi0 a).
    + exact (IHa Q1 Q2 xx gg eq_refl Hfv).
    + exact hle.
  - (* OK_SSigma *) intros L P1 psi psi0 A B ga IHa gb IHb Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    apply notin_union_1 in Hfv as HA. apply notin_union_2 in Hfv as HB.
    eapply (@OK_SSigma (L \u {{xx}}) (Q1++Q2) psi psi0 A B).
    + exact (IHa Q1 Q2 xx gg eq_refl HA).
    + intros y Hy.
      have HyL : y \notin L := @notin_union_1 y L {{xx}} Hy.
      have Hys : y \notin {{xx}} := @notin_union_2 y L {{xx}} Hy.
      have Hxy : xx <> y := @notin_singleton_1 xx y Hys.
      exact (IHb y HyL ((y,psi0)::Q1) Q2 xx gg eq_refl
               (@fv_open_rec B 0 y xx HB Hxy)).
  - (* OK_SPair *) intros P1 psi a psi0 b ca IHca gb IHb Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    apply notin_union_1 in Hfv as HA. apply notin_union_2 in Hfv as HB.
    eapply (@OK_SPair (Q1++Q2) psi a psi0 b).
    + exact (IHca Q1 Q2 xx gg eq_refl HA).
    + exact (IHb Q1 Q2 xx gg eq_refl HB).
  - (* OK_Proj1 *) intros P1 psi psi0 a ga IHa hle Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    eapply (@OK_Proj1 (Q1++Q2) psi psi0 a).
    + exact (IHa Q1 Q2 xx gg eq_refl Hfv).
    + exact hle.
  - (* OK_Proj2 *) intros P1 psi psi0 a ga IHa Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    eapply (@OK_Proj2 (Q1++Q2) psi psi0 a). exact (IHa Q1 Q2 xx gg eq_refl Hfv).
  - (* OK_TyUnit *) intros P1 psi u Q1 Q2 xx gg Heq Hfv. subst P1.
    eapply (@OK_TyUnit (Q1++Q2) psi). apply (@uniq_drop Q1 Q2 xx gg); exact u.
  - (* OK_TmUnit *) intros P1 psi u Q1 Q2 xx gg Heq Hfv. subst P1.
    eapply (@OK_TmUnit (Q1++Q2) psi). apply (@uniq_drop Q1 Q2 xx gg); exact u.
  - (* OK_Bool *) intros P1 psi u Q1 Q2 xx gg Heq Hfv. subst P1.
    eapply (@OK_Bool (Q1++Q2) psi). apply (@uniq_drop Q1 Q2 xx gg); exact u.
  - (* OK_True *) intros P1 psi u Q1 Q2 xx gg Heq Hfv. subst P1.
    eapply (@OK_True (Q1++Q2) psi). apply (@uniq_drop Q1 Q2 xx gg); exact u.
  - (* OK_False *) intros P1 psi u Q1 Q2 xx gg Heq Hfv. subst P1.
    eapply (@OK_False (Q1++Q2) psi). apply (@uniq_drop Q1 Q2 xx gg); exact u.
  - (* OK_If *) intros P1 psi a b0 b1 ga IHa gb0 IHb0 gb1 IHb1 Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    apply notin_union_1 in Hfv as HA. apply notin_union_2 in Hfv as Hbc.
    apply notin_union_1 in Hbc as HB0. apply notin_union_2 in Hbc as HB1.
    eapply (@OK_If (Q1++Q2) psi a b0 b1).
    + exact (IHa Q1 Q2 xx gg eq_refl HA).
    + exact (IHb0 Q1 Q2 xx gg eq_refl HB0).
    + exact (IHb1 Q1 Q2 xx gg eq_refl HB1).
  - (* OKC_Leq *) intros P1 psi psi0 a hle ga IHa Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    eapply (@OKC_Leq (Q1++Q2) psi psi0 a hle).
    exact (IHa Q1 Q2 xx gg eq_refl Hfv).
  - (* OKC_NLeq *) intros P1 psi psi0 a hnle la u Q1 Q2 xx gg Heq Hfv. subst P1. simpl in Hfv.
    eapply (@OKC_NLeq (Q1++Q2) psi psi0 a hnle la).
    apply (@uniq_drop Q1 Q2 xx gg); exact u.
Qed.

Lemma okcpar_drop : forall (P:econtext) (psi psi0:grade) (t:tm), OKCPar P psi psi0 t ->
  forall (Q1 Q2:econtext) (xx:atom) (gg:grade),
    P = Q1++(xx,gg)::Q2 -> xx \notin fv_tm t -> OKCPar (Q1++Q2) psi psi0 t.
Proof.
  intros P psi psi0 t H Q1 Q2 xx gg Heq Hfv.
  destruct H as [P1 psib psia a hle ga | P1 psib psia a hnle la u].
  - subst P1. simpl in Hfv.
    eapply (@OKC_Leq (Q1++Q2) psib psia a hle).
    exact (@okpar_drop (Q1++(xx,gg)::Q2) psib a ga Q1 Q2 xx gg eq_refl Hfv).
  - subst P1.
    eapply (@OKC_NLeq (Q1++Q2) psib psia a hnle la).
    apply (@uniq_drop Q1 Q2 xx gg); exact u.
Qed.

Lemma fv_open_notin : forall (t:tm) (k:nat) (u:tm) (x:atom),
  x \notin fv_tm t -> x \notin fv_tm u ->
  x \notin fv_tm (open_tm_wrt_tm_rec k u t).
Proof.
  intros t. induction t as [| |psi A IHA Btx IHB|psi A IHA b IHb|a0 IHa psi b IHb
                 |s|n|z|psi a0 IHa b IHb psi0 A IHA| |a0 IHa b IHb|psi A IHA
                 |psi a0 IHa|psi a0 IHa|psi A IHA Btx IHB|a0 IHa psi b IHb|psi a0 IHa
                 |psi a0 IHa| | | |a0 IHa b0 IHb0 b1 IHb1];
  intros k u x Hx Hu; simpl in *.
  - exact Hx. - exact Hx.
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHA k u x HA Hu).
    + exact (IHB (S k) u x HB Hu).
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHA k u x HA Hu).
    + exact (IHb (S k) u x HB Hu).
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHa k u x HA Hu).
    + exact (IHb k u x HB Hu).
  - exact Hx.
  - cbn [open_tm_wrt_tm_rec]. destruct (lt_eq_lt_dec n k) as [[H|H]|H]; cbn [fv_tm].
    + apply notin_empty.
    + exact Hu.
    + apply notin_empty.
  - exact Hx.
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as Hbc.
    apply notin_union_1 in Hbc as HB. apply notin_union_2 in Hbc as HC.
    apply notin_union.
    + exact (IHa k u x HA Hu).
    + apply notin_union.
      * exact (IHb k u x HB Hu).
      * exact (IHA k u x HC Hu).
  - exact Hx.
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHa k u x HA Hu).
    + exact (IHb k u x HB Hu).
  - exact (IHA k u x Hx Hu).
  - exact (IHa k u x Hx Hu).
  - exact (IHa k u x Hx Hu).
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHA k u x HA Hu).
    + exact (IHB (S k) u x HB Hu).
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHa k u x HA Hu).
    + exact (IHb k u x HB Hu).
  - exact (IHa k u x Hx Hu).
  - exact (IHa k u x Hx Hu).
  - exact Hx. - exact Hx. - exact Hx.
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as Hbc.
    apply notin_union_1 in Hbc as HB. apply notin_union_2 in Hbc as HC.
    apply notin_union.
    + exact (IHa k u x HA Hu).
    + apply notin_union.
      * exact (IHb0 k u x HB Hu).
      * exact (IHb1 k u x HC Hu).
Qed.

Lemma okpar_open_subst : forall (P:econtext) (psi psi0:grade) (A a0:tm),
  OKPar P psi (a_Abs psi0 A a0) ->
  forall b1:tm, OKCPar P psi psi0 b1 -> OKPar P psi (open_tm_wrt_tm a0 b1).
Proof.
  intros P psi psi0 A a0 H b1 Hb.
  inversion H; subst.
  destruct Hb as [P1 psib psia b hle ga | P1 psib psia b hnle lb].
  - destruct (atom_fresh (L \u (dom P1 \u (fv_tm a0 \u fv_tm b)))) as [x HxS].
    have HxL : x \notin L := @notin_union_1 x L (dom P1 \u (fv_tm a0 \u fv_tm b)) HxS.
    have Hxr : x \notin dom P1 \u (fv_tm a0 \u fv_tm b) :=
      @notin_union_2 x L (dom P1 \u (fv_tm a0 \u fv_tm b)) HxS.
    have Hxdom : x \notin dom P1 := @notin_union_1 x (dom P1) (fv_tm a0 \u fv_tm b) Hxr.
    have Hxr2 : x \notin fv_tm a0 \u fv_tm b :=
      @notin_union_2 x (dom P1) (fv_tm a0 \u fv_tm b) Hxr.
    have Hxfa : x \notin fv_tm a0 := @notin_union_1 x (fv_tm a0) (fv_tm b) Hxr2.
    have Hxfb : x \notin fv_tm b := @notin_union_2 x (fv_tm a0) (fv_tm b) Hxr2.
    have Hbody : OKPar ((x,psia)::P1) psib (open_tm_wrt_tm a0 (a_Var_f x)) := H6 x HxL.
    have Hxfo : x \notin fv_tm (open_tm_wrt_tm a0 b) := @fv_open_notin a0 0 b x Hxfa Hxfb.
    have Hw : OKPar ((x,psia)::P1) psib b :=
      @okpar_insert P1 psib b ga nil P1 x psia eq_refl Hxdom.
    have Hlc : lc_tm b := @okpar_lc_tm P1 psib b ga.
    have Hres := @okpar_subst_gen ((x,psia)::P1) psib
                   (open_tm_wrt_tm a0 (a_Var_f x)) Hbody x b Hlc (or_introl Hw).
    rewrite (@subst_open a0 (a_Var_f x) b x Hlc) (@subst_var_eq b x)
            (@subst_fv_id a0 b x Hxfa) in Hres.
    exact (@okpar_drop ((x,psia)::P1) psib (open_tm_wrt_tm a0 b) Hres
             nil P1 x psia eq_refl Hxfo).
  - destruct (atom_fresh (L \u (dom P1 \u (fv_tm a0 \u fv_tm b)))) as [x HxS].
    have HxL : x \notin L := @notin_union_1 x L (dom P1 \u (fv_tm a0 \u fv_tm b)) HxS.
    have Hxr : x \notin dom P1 \u (fv_tm a0 \u fv_tm b) :=
      @notin_union_2 x L (dom P1 \u (fv_tm a0 \u fv_tm b)) HxS.
    have Hxdom : x \notin dom P1 := @notin_union_1 x (dom P1) (fv_tm a0 \u fv_tm b) Hxr.
    have Hxr2 : x \notin fv_tm a0 \u fv_tm b :=
      @notin_union_2 x (dom P1) (fv_tm a0 \u fv_tm b) Hxr.
    have Hxfa : x \notin fv_tm a0 := @notin_union_1 x (fv_tm a0) (fv_tm b) Hxr2.
    have Hxfb : x \notin fv_tm b := @notin_union_2 x (fv_tm a0) (fv_tm b) Hxr2.
    have Hbody : OKPar ((x,psia)::P1) psib (open_tm_wrt_tm a0 (a_Var_f x)) := H6 x HxL.
    have Hxfo : x \notin fv_tm (open_tm_wrt_tm a0 b) := @fv_open_notin a0 0 b x Hxfa Hxfb.
    have Hcond : OKPar ((x,psia)::P1) psib b \/
                  (forall g:grade, binds x g ((x,psia)::P1) -> ~ (g <= psib)).
    { right. intros g Hbinds.
      apply EnvImpl.binds_cons_1 in Hbinds.
      destruct Hbinds as [[E1 E2]|Hin].
      + subst g. exact hnle.
      + exfalso. exact (@EnvImpl.binds_dom_contradiction grade x g P1 Hin Hxdom). }
    have Hres := @okpar_subst_gen ((x,psia)::P1) psib
                   (open_tm_wrt_tm a0 (a_Var_f x)) Hbody x b lb Hcond.
    rewrite (@subst_open a0 (a_Var_f x) b x lb) (@subst_var_eq b x)
            (@subst_fv_id a0 b x Hxfa) in Hres.
    exact (@okpar_drop ((x,psia)::P1) psib (open_tm_wrt_tm a0 b) Hres
             nil P1 x psia eq_refl Hxfo).
Qed.

(* ============  Inversion helpers for OK predicates  ============ *)

Lemma okcpar_leq_inv : forall (P:econtext) (psi psi0:grade) (b:tm),
  OKCPar P psi psi0 b -> psi0 <= psi -> OKPar P psi b.
Proof.
  intros P psi psi0 b H hle.
  destruct H as [P1 psib psia b' hle' ga | P1 psib psia b' hnle lb].
  - exact ga.
  - exfalso; exact (hnle hle).
Qed.

Lemma okpar_box_inv : forall (P:econtext) (psi psi0:grade) (b:tm),
  OKPar P psi (a_Box psi0 b) -> OKCPar P psi psi0 b.
Proof.
  intros P psi psi0 b H. inversion H; subst; assumption.
Qed.

Lemma okpar_spair_inv : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b:tm),
  OKPar P psi (a_SPair a psi0 b) -> OKCPar P psi psi0 a /\ OKPar P psi b.
Proof.
  intros P psi a psi0 b H. inversion H; subst; split; assumption.
Qed.

(* ============  GDefEq endpoints satisfy the OK predicates  ============ *)

Unset Implicit Arguments.
Scheme GDefEq_okP := Induction for GDefEq Sort Prop
  with CGDefEq_okP := Induction for CGDefEq Sort Prop.
Set Implicit Arguments.

Lemma gdefeq_okpar : forall (P:econtext) (psi:grade) (a b:tm),
  GDefEq P psi a b -> OKPar P psi a /\ OKPar P psi b.
Proof.
  intros P psig ta tb H.
  refine (GDefEq_okP
    (fun (e:econtext) (s:grade) (t0 t1:tm) (_:GDefEq e s t0 t1) =>
       OKPar e s t0 /\ OKPar e s t1)
    (fun (e:econtext) (s s0:grade) (t0 t1:tm) (_:CGDefEq e s s0 t0 t1) =>
       OKCPar e s s0 t0 /\ OKCPar e s s0 t1)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    P psig ta tb H).
  - (* GE_Var *) intros P1 psi x psi0 u i bd. split; apply (@OK_Var P1 psi x psi0); assumption.
  - (* GE_Type *) intros P1 psi s u. split; apply (@OK_Type P1 psi s); exact u.
  - (* GE_Sym *) intros P1 psi bb aa gx IHx. destruct IHx as [HA HB]. split; assumption.
  - (* GE_Trans *) intros P1 psi a b cc gx IHx gy IHy.
    destruct IHx as [HA Hcc]. destruct IHy as [Hcc' HB]. split; assumption.
  - (* GE_App *) intros P1 psi b0 psi0 a0 b1 a1 gx IHx cc IHc.
    destruct IHx as [Hb0 Hb1]. destruct IHc as [Ha0 Ha1]. split.
    + apply (@OK_App P1 psi b0 psi0 a0); assumption.
    + apply (@OK_App P1 psi b1 psi0 a1); assumption.
  - (* GE_Abs *) intros L P1 psi psi0 A0 b0 A1 b1 l0 l1 gpt IHpt. split.
    + apply (@OK_Abs L P1 psi psi0 A0 b0 l0). intros x Hx. exact (proj1 (IHpt x Hx)).
    + apply (@OK_Abs L P1 psi psi0 A1 b1 l1). intros x Hx. exact (proj2 (IHpt x Hx)).
  - (* GE_Pi *) intros L P1 psi psi0 A0 B0 A1 B1 gd IHd gpt IHpt.
    destruct IHd as [HA0 HA1]. split.
    + apply (@OK_Pi L P1 psi psi0 A0 B0 HA0). intros x Hx. exact (proj1 (IHpt x Hx)).
    + apply (@OK_Pi L P1 psi psi0 A1 B1 HA1). intros x Hx. exact (proj2 (IHpt x Hx)).
  - (* GE_AppAbs *) intros P1 psi aa psi0 b0 a0 b1 A gx IHx cc IHc.
    destruct IHx as [Ha Habs]. destruct IHc as [Hb0 Hb1]. split.
    + apply (@OK_App P1 psi aa psi0 b0); assumption.
    + exact (@okpar_open_subst P1 psi psi0 A a0 Habs b1 Hb1).
  - (* GE_Refl *) intros P1 psi u. split; apply (@OK_Refl P1 psi); exact u.
  - (* GE_Transp *) intros P1 psi a0 b0 a1 b1 gx IHx gy IHy.
    destruct IHx as [Ha0 Ha1]. destruct IHy as [Hb0 Hb1]. split.
    + apply (@OK_Transp P1 psi a0 b0); assumption.
    + apply (@OK_Transp P1 psi a1 b1); assumption.
  - (* GE_CEq *) intros P1 psi psi0 a0 b0 psi1 A0 a1 b1 A1 l0 l1 gx IHx gy IHy hle.
    destruct IHx as [Ha0 Ha1]. destruct IHy as [Hb0 Hb1]. split.
    + apply (@OK_CEq P1 psi psi0 a0 b0 psi1 A0 l0); assumption.
    + apply (@OK_CEq P1 psi psi0 a1 b1 psi1 A1 l1); assumption.
  - (* GE_TranspRefl *) intros P1 psi a0 b0 b1 gx IHx gy IHy.
    destruct IHx as [Ha _]. destruct IHy as [Hb0 Hb1]. split.
    + apply (@OK_Transp P1 psi a0 b0); assumption.
    + exact Hb1.
  - (* GE_T *) intros P1 psi psi0 A B gx IHx. destruct IHx as [HA HB]. split.
    + apply (@OK_T P1 psi psi0 A); exact HA.
    + apply (@OK_T P1 psi psi0 B); exact HB.
  - (* GE_Box *) intros P1 psi psi0 a b cc IHc. destruct IHc as [Ha Hb]. split.
    + apply (@OK_Box P1 psi psi0 a); exact Ha.
    + apply (@OK_Box P1 psi psi0 b); exact Hb.
  - (* GE_Unbox *) intros P1 psi psi0 a b gx IHx hle. destruct IHx as [Ha Hb]. split.
    + apply (@OK_Unbox P1 psi psi0 a); assumption.
    + apply (@OK_Unbox P1 psi psi0 b); assumption.
  - (* GE_UnboxBox *) intros P1 psi psi0 a b gx IHx hle. destruct IHx as [Ha Hbox]. split.
    + apply (@OK_Unbox P1 psi psi0 a); assumption.
    + apply (@okcpar_leq_inv P1 psi psi0 b (@okpar_box_inv P1 psi psi0 b Hbox) hle).
  - (* GE_Proj1Cong *) intros P1 psi psi0 a0 a1 gx IHx hle. destruct IHx as [Ha0 Ha1]. split.
    + apply (@OK_Proj1 P1 psi psi0 a0); assumption.
    + apply (@OK_Proj1 P1 psi psi0 a1); assumption.
  - (* GE_Proj2Cong *) intros P1 psi psi0 a0 a1 gx IHx. destruct IHx as [Ha0 Ha1]. split.
    + apply (@OK_Proj2 P1 psi psi0 a0); exact Ha0.
    + apply (@OK_Proj2 P1 psi psi0 a1); exact Ha1.
  - (* GE_Proj1Beta *) intros P1 psi psi0 b a1 a2 gx IHx hle.
    destruct IHx as [Hb Hsp]. destruct (@okpar_spair_inv P1 psi a1 psi0 a2 Hsp) as [Ha1 _]. split.
    + apply (@OK_Proj1 P1 psi psi0 b); assumption.
    + apply (@okcpar_leq_inv P1 psi psi0 a1 Ha1 hle).
  - (* GE_Proj2Beta *) intros P1 psi psi0 b a2 a1 gx IHx.
    destruct IHx as [Hb Hsp]. destruct (@okpar_spair_inv P1 psi a1 psi0 a2 Hsp) as [_ Ha2]. split.
    + apply (@OK_Proj2 P1 psi psi0 b); exact Hb.
    + exact Ha2.
  - (* GE_SPair *) intros P1 psi a0 psi0 b0 a1 b1 cc IHc gx IHx.
    destruct IHc as [Ha0 Ha1]. destruct IHx as [Hb0 Hb1]. split.
    + apply (@OK_SPair P1 psi a0 psi0 b0); assumption.
    + apply (@OK_SPair P1 psi a1 psi0 b1); assumption.
  - (* GE_SSigma *) intros L P1 psi psi0 A0 B0 A1 B1 gd IHd gpt IHpt.
    destruct IHd as [HA0 HA1]. split.
    + apply (@OK_SSigma L P1 psi psi0 A0 B0 HA0). intros x Hx. exact (proj1 (IHpt x Hx)).
    + apply (@OK_SSigma L P1 psi psi0 A1 B1 HA1). intros x Hx. exact (proj2 (IHpt x Hx)).
  - (* GE_TyUnit *) intros P1 psi u. split; apply (@OK_TyUnit P1 psi); exact u.
  - (* GE_TmUnit *) intros P1 psi u. split; apply (@OK_TmUnit P1 psi); exact u.
  - (* GE_Bool *) intros P1 psi u. split; apply (@OK_Bool P1 psi); exact u.
  - (* GE_True *) intros P1 psi u. split; apply (@OK_True P1 psi); exact u.
  - (* GE_False *) intros P1 psi u. split; apply (@OK_False P1 psi); exact u.
  - (* GE_If *) intros P1 psi a0 b0 b1 a1 b2 b3 gx IHx gy IHy gz IHz.
    destruct IHx as [Ha0 Ha1]. destruct IHy as [Hb0 Hb2]. destruct IHz as [Hb1 Hb3]. split.
    + apply (@OK_If P1 psi a0 b0 b1); assumption.
    + apply (@OK_If P1 psi a1 b2 b3); assumption.
  - (* GE_IfTrue *) intros P1 psi a0 b0 b1 b2 b3 gx IHx gy IHy gz IHz.
    destruct IHx as [Ha0 _]. destruct IHy as [Hb0 Hb2]. destruct IHz as [Hb1 _]. split.
    + apply (@OK_If P1 psi a0 b0 b1); assumption.
    + exact Hb2.
  - (* GE_IfFalse *) intros P1 psi a0 b0 b1 b3 b2 gx IHx gy IHy gz IHz.
    destruct IHx as [Ha0 _]. destruct IHy as [Hb0 _]. destruct IHz as [Hb1 Hb3]. split.
    + apply (@OK_If P1 psi a0 b0 b1); assumption.
    + exact Hb3.
  - (* CGE_Leq *) intros P1 psi psi0 a b hle gx IHx. destruct IHx as [Ha Hb]. split.
    + apply (@OKC_Leq P1 psi psi0 a); assumption.
    + apply (@OKC_Leq P1 psi psi0 b); assumption.
  - (* CGE_NLeq *) intros P1 psi psi0 a b la lb hnle u. split.
    + apply (@OKC_NLeq P1 psi psi0 a); assumption.
    + apply (@OKC_NLeq P1 psi psi0 b); assumption.
Qed.

(* ============  Parallel reduction embeds into graded definitional equality  ============ *)

Unset Implicit Arguments.
Scheme Par_mutP := Induction for Par Sort Prop
  with CPar_mutP := Induction for CPar Sort Prop.
Set Implicit Arguments.

Lemma par_gdefeq : forall (P:econtext) (psi:grade) (a b:tm),
  Par P psi a b -> GDefEq P psi a b.
Proof.
  intros P psig ta tb H.
  refine (Par_mutP
    (fun (e:econtext) (s:grade) (t0 t1:tm) (_:Par e s t0 t1) => GDefEq e s t0 t1)
    (fun (e:econtext) (s s0:grade) (t0 t1:tm) (_:CPar e s s0 t0 t1) => CGDefEq e s s0 t0 t1)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P psig ta tb H).
  - (* Par_Var *) intros P1 psi x psi0 u i bd. apply (@GE_Var P1 psi x psi0); assumption.
  - (* Par_Type *) intros P1 psi s u. apply (@GE_Type P1 psi s); exact u.
  - (* Par_Pi *) intros L P1 psi psi1 A1 B1 A2 B2 gA IHA gB IHB.
    apply (@GE_Pi L P1 psi psi1 A1 B1 A2 B2).
    + exact IHA.
    + intros x Hx. exact (IHB x Hx).
  - (* Par_AppBeta *) intros P1 psi a psi0 b a' b' A gA IHA gC IHC.
    apply (@GE_AppAbs P1 psi a psi0 b a' b' A).
    + exact IHA.
    + exact IHC.
  - (* Par_App *) intros P1 psi a psi0 b a' b' gA IHA gC IHC.
    apply (@GE_App P1 psi a psi0 b a' b').
    + exact IHA.
    + exact IHC.
  - (* Par_Abs *) intros L P1 psi psi0 A1 b1 A2 b2 l1 l2 gB IHB.
    apply (@GE_Abs L P1 psi psi0 A1 b1 A2 b2 l1 l2).
    intros x Hx. exact (IHB x Hx).
  - (* Par_Refl *) intros P1 psi u. apply (@GE_Refl P1 psi); exact u.
  - (* Par_Transp *) intros P1 psi a0 b0 a1 b1 gA IHA gB IHB.
    apply (@GE_Transp P1 psi a0 b0 a1 b1); assumption.
  - (* Par_CEq *) intros P1 psi psi0 a0 b0 psi1 A0 a1 b1 A1 l0 l1 gA IHA gB IHB hle.
    apply (@GE_CEq P1 psi psi0 a0 b0 psi1 A0 a1 b1 A1 l0 l1); assumption.
  - (* Par_TranspRefl *) intros P1 psi a0 b0 b1 gA IHA gB IHB.
    apply (@GE_TranspRefl P1 psi a0 b0 b1); assumption.
  - (* Par_T *) intros P1 psi psi0 A B gA IHA. apply (@GE_T P1 psi psi0 A B); exact IHA.
  - (* Par_Box *) intros P1 psi psi0 a b cA IHA. apply (@GE_Box P1 psi psi0 a b); exact IHA.
  - (* Par_Unbox *) intros P1 psi psi0 a b gA IHA hle. apply (@GE_Unbox P1 psi psi0 a b); assumption.
  - (* Par_UnboxBox *) intros P1 psi psi0 a b gA IHA hle. apply (@GE_UnboxBox P1 psi psi0 a b); assumption.
  - (* Par_Proj1Cong *) intros P1 psi psi0 a0 a1 gA IHA hle. apply (@GE_Proj1Cong P1 psi psi0 a0 a1); assumption.
  - (* Par_Proj2Cong *) intros P1 psi psi0 a0 a1 gA IHA. apply (@GE_Proj2Cong P1 psi psi0 a0 a1); exact IHA.
  - (* Par_Proj1Beta *) intros P1 psi psi0 b a1 a2 gA IHA hle. apply (@GE_Proj1Beta P1 psi psi0 b a1 a2); assumption.
  - (* Par_Proj2Beta *) intros P1 psi psi0 b a2 a1 gA IHA. apply (@GE_Proj2Beta P1 psi psi0 b a2 a1); exact IHA.
  - (* Par_SPair *) intros P1 psi a0 psi0 b0 a1 b1 cA IHA gB IHB.
    apply (@GE_SPair P1 psi a0 psi0 b0 a1 b1); assumption.
  - (* Par_SSigma *) intros L P1 psi psi0 A0 B0 A1 B1 gA IHA gB IHB.
    apply (@GE_SSigma L P1 psi psi0 A0 B0 A1 B1).
    + exact IHA.
    + intros x Hx. exact (IHB x Hx).
  - (* Par_TyUnit *) intros P1 psi u. apply (@GE_TyUnit P1 psi); exact u.
  - (* Par_TmUnit *) intros P1 psi u. apply (@GE_TmUnit P1 psi); exact u.
  - (* Par_Bool *) intros P1 psi u. apply (@GE_Bool P1 psi); exact u.
  - (* Par_True *) intros P1 psi u. apply (@GE_True P1 psi); exact u.
  - (* Par_False *) intros P1 psi u. apply (@GE_False P1 psi); exact u.
  - (* Par_If *) intros P1 psi a0 b0 b1 a1 b2 b3 gA IHA gB IHB gC IHC.
    apply (@GE_If P1 psi a0 b0 b1 a1 b2 b3); assumption.
  - (* Par_IfTrue *) intros P1 psi a0 b0 b1 b2 b3 gA IHA gB IHB gC IHC.
    apply (@GE_IfTrue P1 psi a0 b0 b1 b2 b3); assumption.
  - (* Par_IfFalse *) intros P1 psi a0 b0 b1 b3 b2 gA IHA gB IHB gC IHC.
    apply (@GE_IfFalse P1 psi a0 b0 b1 b3 b2); assumption.
  - (* CPar_Leq *) intros P1 psi psi0 a1 a2 hle gA IHA. apply (@CGE_Leq P1 psi psi0 a1 a2); assumption.
  - (* CPar_Nleq *) intros P1 psi psi0 a1 a2 la lb hnle u. apply (@CGE_NLeq P1 psi psi0 a1 a2); assumption.
Qed.

Lemma cpar_gdefeq : forall (P:econtext) (psi psi0:grade) (a b:tm),
  CPar P psi psi0 a b -> CGDefEq P psi psi0 a b.
Proof.
  intros P psi psi0 a b H.
  destruct H as [P1 psib psia a1 a2 hle gpar | P1 psib psia a1 a2 la lb hnle u].
  - apply (@CGE_Leq P1 psib psia a1 a2 hle).
    apply (@par_gdefeq P1 psib a1 a2 gpar).
  - apply (@CGE_NLeq P1 psib psia a1 a2 la lb hnle u).
Qed.
(* ============  OK corollaries  ============ *)

Lemma par_okpar : forall (P:econtext) (psi:grade) (a b:tm),
  Par P psi a b -> OKPar P psi a /\ OKPar P psi b.
Proof.
  intros P psi a b H. apply gdefeq_okpar. apply (@par_gdefeq P psi a b). exact H.
Qed.

Lemma cpar_okcpar : forall (P:econtext) (psi psi0:grade) (a b:tm),
  CPar P psi psi0 a b -> OKCPar P psi psi0 a /\ OKCPar P psi psi0 b.
Proof.
  intros P psi psi0 a b H.
  destruct H as [P1 psib psia a1 a2 hle gpar | P1 psib psia a1 a2 la lb hnle u].
  - destruct (@par_okpar P1 psib a1 a2 gpar) as [HA HB]. split.
    + apply (@OKC_Leq P1 psib psia a1 hle HA).
    + apply (@OKC_Leq P1 psib psia a2 hle HB).
  - split.
    + apply (@OKC_NLeq P1 psib psia a1 hnle la u).
    + apply (@OKC_NLeq P1 psib psia a2 hnle lb u).
Qed.

Lemma gdefeq_par_refl : forall (P:econtext) (psi:grade) (a b:tm),
  GDefEq P psi a b -> uniq P -> Par P psi a a /\ Par P psi b b.
Proof.
  intros P psi a b H Hu. destruct (@gdefeq_okpar P psi a b H) as [HA HB]. split.
  - apply okpar_par; assumption.
  - apply okpar_par; assumption.
Qed.
Lemma par_lc_tm : forall (P:econtext) (psi:grade) (a b:tm),
  Par P psi a b -> lc_tm a /\ lc_tm b.
Proof.
  intros P psi a b H. exact (@gdefeq_lc P psi a b (@par_gdefeq P psi a b H)).
Qed.

Lemma cpar_lc_tm : forall (P:econtext) (psi psi0:grade) (a b:tm),
  CPar P psi psi0 a b -> lc_tm a /\ lc_tm b.
Proof.
  intros P psi psi0 a b H. destruct (@cpar_okcpar P psi psi0 a b H) as [HA HB]. split.
  - exact (@okcpar_lc_tm P psi psi0 a HA).
  - exact (@okcpar_lc_tm P psi psi0 b HB).
Qed.

(* ============  Reflexivity of the parallel/join closures  ============ *)

Lemma multipar_refl : forall (P:econtext) (psi:grade) (t:tm),
  OKPar P psi t -> uniq P -> MultiPar P psi t t.
Proof.
  intros P psi t H Hu. apply MP_One. exact (@okpar_par P psi t H Hu).
Qed.

Lemma cmultipar_refl : forall (P:econtext) (psi psi0:grade) (t:tm),
  OKCPar P psi psi0 t -> uniq P -> CMultiPar P psi psi0 t t.
Proof.
  intros P psi psi0 t H Hu.
  destruct H as [P1 psib psia a hle ga | P1 psib psia a hnle la u].
  - apply (@CMP_Leq P1 psib psia a a hle). apply MP_One. exact (@okpar_par P1 psib a ga Hu).
  - apply (@CMP_Nleq P1 psib psia a a la la hnle u).
Qed.

Lemma epar_refl : forall (P:econtext) (psi:grade) (t:tm),
  OKPar P psi t -> uniq P -> EPar P t t.
Proof.
  intros P psi t H Hu. apply (@EP_One P t t psi). exact (@okpar_par P psi t H Hu).
Qed.

Lemma joins_refl : forall (P:econtext) (psi:grade) (t:tm),
  OKPar P psi t -> uniq P -> Joins P psi t t.
Proof.
  intros P psi t H Hu. apply (@join P psi t t t).
  - exact (@multipar_refl P psi t H Hu).
  - exact (@multipar_refl P psi t H Hu).
Qed.

Lemma ejoins_refl : forall (P:econtext) (psi:grade) (t:tm),
  OKPar P psi t -> uniq P -> EJoins P t t.
Proof.
  intros P psi t H Hu. apply (@EJ_ejoins P t t t).
  - apply (@EMP_One P t t). exact (@epar_refl P psi t H Hu).
  - apply (@EMP_One P t t). exact (@epar_refl P psi t H Hu).
Qed.


(* ============  Bridging to DefEq  ============ *)

Lemma par_defeq : forall (P:econtext) (psi:grade) (a b:tm),
  Par P psi a b -> DefEq P a b.
Proof.
  intros P psi a b H. apply (@E_One P a b psi). apply (@par_gdefeq P psi a b). exact H.
Qed.

Lemma cpar_defeq : forall (P:econtext) (psi psi0:grade) (a b:tm),
  CPar P psi psi0 a b -> CGDefEq P psi psi0 a b.
Proof. intros. apply (@cpar_gdefeq P psi psi0 a b). exact H. Qed.

Lemma okpar_defeq_refl : forall (P:econtext) (psi:grade) (a:tm),
  OKPar P psi a -> uniq P -> DefEq P a a.
Proof.
  intros P psi a H Hu. apply (@E_One P a a psi). apply (@par_gdefeq P psi a a).
  apply okpar_par; assumption.
Qed.




(* ============  Equivalence-closure facts for DefEq  ============ *)

Lemma defeq_sym : forall (P:econtext) (a b:tm), DefEq P a b -> DefEq P b a.
Proof.
  intros P a b H. induction H.
  - apply (@E_One P b a psi). apply GE_Sym. exact H.
  - apply (@E_Trans P b a b0); assumption.
Qed.

Lemma defeq_trans : forall (P:econtext) (a b c:tm),
  DefEq P a b -> DefEq P b c -> DefEq P a c.
Proof. intros P a b c H1 H2. apply (@E_Trans P a c b); assumption. Qed.

Lemma defeq_one_sym : forall (P:econtext) (a b:tm) (psi:grade),
  GDefEq P psi a b -> DefEq P b a.
Proof. intros P a b psi H. apply (@E_One P b a psi). apply GE_Sym. exact H. Qed.

Lemma multipar_trans : forall (P:econtext) (psi:grade) (a b c:tm),
  MultiPar P psi a b -> MultiPar P psi b c -> MultiPar P psi a c.
Proof.
  intros P psi a b c H1. revert c.
  induction H1 as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH];
    intros c H2.
  - apply (@MP_Step P1 psib x c y Hpar H2).
  - apply (@MP_Step P1 psib x c y Hpar (IH c H2)).
Qed.

Lemma joins_sym : forall (P:econtext) (psi:grade) (a b:tm),
  Joins P psi a b -> Joins P psi b a.
Proof.
  intros P psi a b H. destruct H as [P1 psib a1 a2 c Ha Hb].
  apply (@join P1 psib a2 a1 c Hb Ha).
Qed.

Lemma ejoins_sym : forall (P:econtext) (a b:tm),
  EJoins P a b -> EJoins P b a.
Proof.
  intros P a b H. destruct H as [P1 a1 a2 u Ha Hb].
  apply (@EJ_ejoins P1 a2 a1 u Hb Ha).
Qed.

Lemma multipar_headform : forall (P:econtext) (psi:grade) (a b:tm),
  MultiPar P psi a b -> forall h, tm_to_headform a = Some h -> tm_to_headform b = Some h.
Proof.
  intros P psi a b H. induction H as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH];
    intros h Hh.
  - exact (@par_headform P1 psib x y Hpar h Hh).
  - apply IH. exact (@par_headform P1 psib x y Hpar h Hh).
Qed.

Lemma joins_consistent : forall (P:econtext) (psi:grade) (a b:tm),
  Joins P psi a b ->
  forall h1 h2, tm_to_headform a = Some h1 -> tm_to_headform b = Some h2 -> h1 = h2.
Proof.
  intros P psi a b H h1 h2 Ha Hb.
  destruct H as [P1 psib a1 a2 c Hac Hbc].
  assert (Hc1 : tm_to_headform c = Some h1) by exact (@multipar_headform _ _ _ _ Hac h1 Ha).
  assert (Hc2 : tm_to_headform c = Some h2) by exact (@multipar_headform _ _ _ _ Hbc h2 Hb).
  rewrite Hc1 in Hc2. injection Hc2. auto.
Qed.

Lemma okpar_gdefeq_refl : forall (P:econtext) (psi:grade) (t:tm),
  OKPar P psi t -> uniq P -> GDefEq P psi t t.
Proof.
  intros P psi t H Hu. apply (@par_gdefeq P psi t t). apply okpar_par; assumption.
Qed.

Lemma okcpar_cgdefeq_refl : forall (P:econtext) (psi psi0:grade) (t:tm),
  OKCPar P psi psi0 t -> uniq P -> CGDefEq P psi psi0 t t.
Proof.
  intros P psi psi0 t H Hu. apply (@cpar_gdefeq P psi psi0 t t). apply okcpar_cpar; assumption.
Qed.

Lemma multipar_app_congr : forall (P:econtext) (psi:grade) (a a':tm) (psi0:grade) (b:tm),
  MultiPar P psi a a' -> OKCPar P psi psi0 b -> uniq P ->
  MultiPar P psi (a_App a psi0 b) (a_App a' psi0 b).
Proof.
  intros P psi a a' psi0 b H Hb Hu.
  induction H as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH].
  - apply MP_One. apply (@Par_App P1 psib x psi0 b y b Hpar).
    apply okcpar_cpar; assumption.
  - apply (@MP_Step P1 psib (a_App x psi0 b) (a_App x' psi0 b) (a_App y psi0 b)).
    + apply (@Par_App P1 psib x psi0 b y b Hpar). apply okcpar_cpar; assumption.
    + exact (IH Hb Hu).
Qed.

Lemma multipar_app_arg_congr : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b b':tm),
  OKPar P psi a -> CMultiPar P psi psi0 b b' -> uniq P ->
  MultiPar P psi (a_App a psi0 b) (a_App a psi0 b').
Proof.
  intros P psi a psi0 b b' Ha Hc Hu.
  induction Hc as [P1 psib psia b0 b1 hle M | P1 psib psia b0 b1 la lb hnle u].
  - induction M as [P2 ps2 x y Hpar | P2 ps2 x x' y Hpar Hmulti IH].
    + apply MP_One. apply (@Par_App P2 ps2 a psia x a y).
      * apply okpar_par; assumption.
      * apply (@CPar_Leq P2 ps2 psia x y hle Hpar).
    + apply (@MP_Step P2 ps2 (a_App a psia x) (a_App a psia x') (a_App a psia y)).
      * apply (@Par_App P2 ps2 a psia x a y).
        -- apply okpar_par; assumption.
        -- apply (@CPar_Leq P2 ps2 psia x y hle Hpar).
      * exact (IH Ha hle Hu).
  - apply MP_One. apply (@Par_App P1 psib a psia b0 a b1).
    + apply okpar_par; assumption.
    + apply (@CPar_Nleq P1 psib psia b0 b1 la lb hnle u).
Qed.

Lemma multipar_T_congr : forall (P:econtext) (psi:grade) (psi0:grade) (A A':tm),
  MultiPar P psi A A' -> MultiPar P psi (a_T psi0 A) (a_T psi0 A').
Proof.
  intros P psi psi0 A A' H.
  induction H as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH].
  - apply MP_One. apply (@Par_T P1 psib psi0 x y). exact Hpar.
  - apply (@MP_Step P1 psib (a_T psi0 x) (a_T psi0 x') (a_T psi0 y)).
    + apply (@Par_T P1 psib psi0 x y). exact Hpar.
    + exact IH.
Qed.

Lemma multipar_unbox_congr : forall (P:econtext) (psi:grade) (psi0:grade) (a a':tm),
  MultiPar P psi a a' -> psi0 <= psi ->
  MultiPar P psi (a_Unbox psi0 a) (a_Unbox psi0 a').
Proof.
  intros P psi psi0 a a' H hle.
  induction H as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH].
  - apply MP_One. apply (@Par_Unbox P1 psib psi0 x y). exact Hpar. exact hle.
  - apply (@MP_Step P1 psib (a_Unbox psi0 x) (a_Unbox psi0 x') (a_Unbox psi0 y)).
    + apply (@Par_Unbox P1 psib psi0 x y); assumption.
    + exact (IH hle).
Qed.

Lemma multipar_proj2_congr : forall (P:econtext) (psi:grade) (psi0:grade) (a a':tm),
  MultiPar P psi a a' -> MultiPar P psi (a_Proj2 psi0 a) (a_Proj2 psi0 a').
Proof.
  intros P psi psi0 a a' H.
  induction H as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH].
  - apply MP_One. apply (@Par_Proj2Cong P1 psib psi0 x y). exact Hpar.
  - apply (@MP_Step P1 psib (a_Proj2 psi0 x) (a_Proj2 psi0 x') (a_Proj2 psi0 y)).
    + apply (@Par_Proj2Cong P1 psib psi0 x y). exact Hpar.
    + exact IH.
Qed.

Lemma multipar_box_congr : forall (P:econtext) (psi:grade) (psi0:grade) (a a':tm),
  CMultiPar P psi psi0 a a' -> MultiPar P psi (a_Box psi0 a) (a_Box psi0 a').
Proof.
  intros P psi psi0 a a' H.
  induction H as [P1 psib psia b0 b1 hle M | P1 psib psia b0 b1 la lb hnle u].
  - induction M as [P2 ps2 x y Hpar | P2 ps2 x x' y Hpar Hmulti IH].
    + apply MP_One. apply (@Par_Box P2 ps2 psia x y).
      apply (@CPar_Leq P2 ps2 psia x y hle Hpar).
    + apply (@MP_Step P2 ps2 (a_Box psia x) (a_Box psia x') (a_Box psia y)).
      * apply (@Par_Box P2 ps2 psia x y). apply (@CPar_Leq P2 ps2 psia x y hle Hpar).
      * exact (IH hle).
  - apply MP_One. apply (@Par_Box P1 psib psia b0 b1).
    apply (@CPar_Nleq P1 psib psia b0 b1 la lb hnle u).
Qed.

Lemma multipar_transp_congr : forall (P:econtext) (psi:grade) (a a' b:tm),
  MultiPar P psi a a' -> OKPar P psi b -> uniq P ->
  MultiPar P psi (a_Transp a b) (a_Transp a' b).
Proof.
  intros P psi a a' b H Hb Hu.
  induction H as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH].
  - apply MP_One. apply (@Par_Transp P1 psib x b y b); [ exact Hpar | apply okpar_par; assumption ].
  - apply (@MP_Step P1 psib (a_Transp x b) (a_Transp x' b) (a_Transp y b)).
    + apply (@Par_Transp P1 psib x b y b); [ exact Hpar | apply okpar_par; assumption ].
    + exact (IH Hb Hu).
Qed.

Lemma multipar_transp_congr2 : forall (P:econtext) (psi:grade) (a:tm) (b b':tm),
  MultiPar P psi b b' -> OKPar P psi a -> uniq P ->
  MultiPar P psi (a_Transp a b) (a_Transp a b').
Proof.
  intros P psi a b b' H Ha Hu.
  induction H as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH].
  - apply MP_One. apply (@Par_Transp P1 psib a x a y); [ apply okpar_par; assumption | exact Hpar ].
  - apply (@MP_Step P1 psib (a_Transp a x) (a_Transp a x') (a_Transp a y)).
    + apply (@Par_Transp P1 psib a x a y); [ apply okpar_par; assumption | exact Hpar ].
    + exact (IH Ha Hu).
Qed.

Lemma multipar_proj1_congr : forall (P:econtext) (psi:grade) (psi0:grade) (a a':tm),
  MultiPar P psi a a' -> psi0 <= psi ->
  MultiPar P psi (a_Proj1 psi0 a) (a_Proj1 psi0 a').
Proof.
  intros P psi psi0 a a' H hle.
  induction H as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH].
  - apply MP_One. apply (@Par_Proj1Cong P1 psib psi0 x y); assumption.
  - apply (@MP_Step P1 psib (a_Proj1 psi0 x) (a_Proj1 psi0 x') (a_Proj1 psi0 y)).
    + apply (@Par_Proj1Cong P1 psib psi0 x y); assumption.
    + exact (IH hle).
Qed.

Lemma multipar_spair_congr2 : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b b':tm),
  OKCPar P psi psi0 a -> MultiPar P psi b b' -> uniq P ->
  MultiPar P psi (a_SPair a psi0 b) (a_SPair a psi0 b').
Proof.
  intros P psi a psi0 b b' Ha H Hu.
  induction H as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH].
  - apply MP_One. apply (@Par_SPair P1 psib a psi0 x a y).
    + apply okcpar_cpar; assumption.
    + exact Hpar.
  - apply (@MP_Step P1 psib (a_SPair a psi0 x) (a_SPair a psi0 x') (a_SPair a psi0 y)).
    + apply (@Par_SPair P1 psib a psi0 x a y).
      * apply okcpar_cpar; assumption.
      * exact Hpar.
    + exact (IH Ha Hu).
Qed.

Lemma multipar_if_congr1 : forall (P:econtext) (psi:grade) (a a' b0 b1:tm),
  MultiPar P psi a a' -> OKPar P psi b0 -> OKPar P psi b1 -> uniq P ->
  MultiPar P psi (a_If a b0 b1) (a_If a' b0 b1).
Proof.
  intros P psi a a' b0 b1 H Hb0 Hb1 Hu.
  induction H as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH].
  - apply MP_One. apply (@Par_If P1 psib x b0 b1 y b0 b1).
    + exact Hpar.
    + apply okpar_par; assumption.
    + apply okpar_par; assumption.
  - apply (@MP_Step P1 psib (a_If x b0 b1) (a_If x' b0 b1) (a_If y b0 b1)).
    + apply (@Par_If P1 psib x b0 b1 y b0 b1).
      * exact Hpar.
      * apply okpar_par; assumption.
      * apply okpar_par; assumption.
    + exact (IH Hb0 Hb1 Hu).
Qed.

Lemma multipar_ceq_congr1 : forall (P:econtext) (psi:grade) (psi0:grade)
  (a a' b:tm) (psi1:grade) (A0 A1:tm),
  MultiPar P psi a a' -> lc_tm A0 -> lc_tm A1 -> OKPar P psi b -> psi0 <= psi ->
  uniq P -> MultiPar P psi (a_CEq psi0 a b psi1 A0) (a_CEq psi0 a' b psi1 A1).
Proof.
  intros P psi psi0 a a' b psi1 A0 A1 H.
  revert A0 A1.
  induction H as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH];
    intros A0 A1 l0 l1 Hb hle Hu.
  - apply MP_One. apply (@Par_CEq P1 psib psi0 x b psi1 A0 y b A1 l0 l1).
    + exact Hpar.
    + apply okpar_par; assumption.
    + exact hle.
  - apply (@MP_Step P1 psib (a_CEq psi0 x b psi1 A0) (a_CEq psi0 x' b psi1 A1)
               (a_CEq psi0 y b psi1 A1)).
    + apply (@Par_CEq P1 psib psi0 x b psi1 A0 y b A1 l0 l1).
      * exact Hpar.
      * apply okpar_par; assumption.
      * exact hle.
    + exact (IH A1 A1 l1 l1 Hb hle Hu).
Qed.

Lemma multipar_if_congr2 : forall (P:econtext) (psi:grade) (a b0 b0' b1:tm),
  MultiPar P psi b0 b0' -> OKPar P psi a -> OKPar P psi b1 -> uniq P ->
  MultiPar P psi (a_If a b0 b1) (a_If a b0' b1).
Proof.
  intros P psi a b0 b0' b1 H Ha Hb1 Hu.
  induction H as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH].
  - apply MP_One. apply (@Par_If P1 psib a x b1 a y b1).
    + apply okpar_par; assumption.
    + exact Hpar.
    + apply okpar_par; assumption.
  - apply (@MP_Step P1 psib (a_If a x b1) (a_If a x' b1) (a_If a y b1)).
    + apply (@Par_If P1 psib a x b1 a y b1).
      * apply okpar_par; assumption.
      * exact Hpar.
      * apply okpar_par; assumption.
    + exact (IH Ha Hb1 Hu).
Qed.

Lemma multipar_if_congr3 : forall (P:econtext) (psi:grade) (a b0 b1 b1':tm),
  MultiPar P psi b1 b1' -> OKPar P psi a -> OKPar P psi b0 -> uniq P ->
  MultiPar P psi (a_If a b0 b1) (a_If a b0 b1').
Proof.
  intros P psi a b0 b1 b1' H Ha Hb0 Hu.
  induction H as [P1 psib x y Hpar | P1 psib x x' y Hpar Hmulti IH].
  - apply MP_One. apply (@Par_If P1 psib a b0 x a b0 y).
    + apply okpar_par; assumption.
    + apply okpar_par; assumption.
    + exact Hpar.
  - apply (@MP_Step P1 psib (a_If a b0 x) (a_If a b0 x') (a_If a b0 y)).
    + apply (@Par_If P1 psib a b0 x a b0 y).
      * apply okpar_par; assumption.
      * apply okpar_par; assumption.
      * exact Hpar.
    + exact (IH Ha Hb0 Hu).
Qed.

Lemma multipar_spair_congr1 : forall (P:econtext) (psi:grade) (a a':tm) (psi0:grade) (b:tm),
  CMultiPar P psi psi0 a a' -> OKPar P psi b -> uniq P ->
  MultiPar P psi (a_SPair a psi0 b) (a_SPair a' psi0 b).
Proof.
  intros P psi a a' psi0 b H Hb Hu.
  induction H as [P1 psib psia b0 b1 hle M | P1 psib psia b0 b1 la lb hnle u].
  - induction M as [P2 ps2 x y Hpar | P2 ps2 x x' y Hpar Hmulti IH].
    + apply MP_One. apply (@Par_SPair P2 ps2 x psia b y b).
      * apply (@CPar_Leq P2 ps2 psia x y hle Hpar).
      * apply okpar_par; assumption.
    + apply (@MP_Step P2 ps2 (a_SPair x psia b) (a_SPair x' psia b) (a_SPair y psia b)).
      * apply (@Par_SPair P2 ps2 x psia b y b).
        -- apply (@CPar_Leq P2 ps2 psia x y hle Hpar).
        -- apply okpar_par; assumption.
      * exact (IH hle Hb Hu).
  - apply MP_One. apply (@Par_SPair P1 psib b0 psia b b1 b).
    + apply (@CPar_Nleq P1 psib psia b0 b1 la lb hnle u).
    + apply okpar_par; assumption.
Qed.

(* ============  Values vs headforms and irreducibility  ============ *)

Lemma value_headform : forall (t:tm), Value t = true -> exists h, tm_to_headform t = Some h.
Proof.
  intros t. destruct t; simpl; intros H; try discriminate; eexists; reflexivity.
Qed.

Lemma headform_value : forall (t:tm) (h:headform), tm_to_headform t = Some h -> Value t = true.
Proof.
  intros t. destruct t; simpl; intros h H; try discriminate; reflexivity.
Qed.

Lemma value_no_red : forall (t:tm), Value t = true -> ~ (exists u, Red t u).
Proof.
  intros t Hv [u Hu].
  destruct t; simpl in Hv; try discriminate; inversion Hu.
Qed.

Lemma multipar_value : forall (P:econtext) (psi:grade) (a b:tm),
  MultiPar P psi a b -> Value a = true -> Value b = true.
Proof.
  intros P psi a b H Hv. destruct (@value_headform a Hv) as [h Hh].
  apply (@headform_value b h). apply (@multipar_headform P psi a b H h Hh).
Qed.

Lemma epar_value : forall (P:econtext) (a b:tm),
  EPar P a b -> Value a = true -> Value b = true.
Proof.
  intros P a b H Hv. destruct (@value_headform a Hv) as [h Hh].
  apply (@headform_value b h). apply (@epar_headform P a b H h Hh).
Qed.

Lemma empar_value : forall (P:econtext) (a b:tm),
  EMPar P a b -> Value a = true -> Value b = true.
Proof.
  intros P a b H Hv. destruct (@value_headform a Hv) as [h Hh].
  apply (@headform_value b h). apply (@empar_headform P a b H h Hh).
Qed.

(* ============  Red/Reds basic closure facts  ============ *)

Lemma reds_refl : forall (a:tm), lc_tm a -> Reds a a.
Proof. intros a Ha. apply Rs_Refl. exact Ha. Qed.

Lemma reds_trans : forall (a b c:tm), Reds a b -> Reds b c -> Reds a c.
Proof.
  intros a b c H1. induction H1 as [x Hx | a0 a1 b0 Hred Hrest IH]; intros H2.
  - exact H2.
  - apply (@Rs_Step a0 c b0 Hred (IH H2)).
Qed.

Lemma red_reds : forall (a b:tm), Red a b -> lc_tm b -> Reds a b.
Proof.
  intros a b H Hb. apply (@Rs_Step a b b); [ exact H | apply Rs_Refl; exact Hb ].
Qed.

Lemma lc_abs_inv : forall (psi0:grade) (A a:tm),
  lc_tm (a_Abs psi0 A a) -> lc_tm A /\ (forall x, lc_tm (open_tm_wrt_tm a (a_Var_f x))).
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_app_inv : forall (a:tm) (psi:grade) (b:tm),
  lc_tm (a_App a psi b) -> lc_tm a /\ lc_tm b.
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_transp_inv : forall (a b:tm), lc_tm (a_Transp a b) -> lc_tm a /\ lc_tm b.
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_unbox_inv : forall (psi:grade) (a:tm), lc_tm (a_Unbox psi a) -> lc_tm a.
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_unbox_box_inv : forall (psi:grade) (a:tm),
  lc_tm (a_Unbox psi (a_Box psi a)) -> lc_tm a.
Proof. intros. inversion H; subst; inversion H1; subst; auto. Qed.

Lemma lc_proj1_inv : forall (psi:grade) (a:tm), lc_tm (a_Proj1 psi a) -> lc_tm a.
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_proj2_inv : forall (psi:grade) (a:tm), lc_tm (a_Proj2 psi a) -> lc_tm a.
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_spair_inv : forall (a:tm) (psi:grade) (b:tm),
  lc_tm (a_SPair a psi b) -> lc_tm a /\ lc_tm b.
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_proj1_beta_lc : forall (psi:grade) (a1 a2:tm),
  lc_tm (a_Proj1 psi (a_SPair a1 psi a2)) -> lc_tm a1.
Proof. intros. apply (@lc_proj1_inv psi (a_SPair a1 psi a2)) in H.
  destruct (@lc_spair_inv a1 psi a2 H) as [H1 _]. exact H1. Qed.

Lemma lc_proj2_beta_lc : forall (psi:grade) (a1 a2:tm),
  lc_tm (a_Proj2 psi (a_SPair a1 psi a2)) -> lc_tm a2.
Proof. intros. apply (@lc_proj2_inv psi (a_SPair a1 psi a2)) in H.
  destruct (@lc_spair_inv a1 psi a2 H) as [_ H2]. exact H2. Qed.

Lemma lc_if_inv : forall (a b0 b1:tm),
  lc_tm (a_If a b0 b1) -> lc_tm a /\ lc_tm b0 /\ lc_tm b1.
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_if_true_lc : forall (b0 b1:tm), lc_tm (a_If a_True b0 b1) -> lc_tm b0.
Proof. intros. destruct (@lc_if_inv a_True b0 b1 H) as [_ [H0 _]]. exact H0. Qed.

Lemma lc_if_false_lc : forall (b0 b1:tm), lc_tm (a_If a_False b0 b1) -> lc_tm b1.
Proof. intros. destruct (@lc_if_inv a_False b0 b1 H) as [_ [_ H1]]. exact H1. Qed.

Lemma lc_open : forall (A a b:tm) (psi0:grade),
  lc_tm (a_Abs psi0 A a) -> lc_tm b -> lc_tm (open_tm_wrt_tm a b).
Proof.
  intros A a b psi0 Habs Hb.
  destruct (@lc_abs_inv psi0 A a Habs) as [_ Hopen].
  destruct (atom_fresh (fv_tm a)) as [x Hx].
  have Hsub : lc_tm (subst_tm b x (open_tm_wrt_tm a (a_Var_f x))) :=
    @lc_subst (open_tm_wrt_tm a (a_Var_f x)) (Hopen x) b x Hb.
  rewrite (@subst_open a (a_Var_f x) b x Hb) (@subst_var_eq b x)
          (@subst_fv_id a b x Hx) in Hsub.
  exact Hsub.
Qed.

Lemma red_lc : forall (a b:tm), Red a b -> lc_tm a -> lc_tm b.
Proof.
  intros a b H. induction H; intros Ha.
  - match goal with Hl : lc_tm (a_App ?x ?g ?y) |- _ =>
      destruct (@lc_app_inv x g y Hl) as [Hx Hy];
      constructor; [ apply IHRed; exact Hx | exact Hy ] end.
  - eapply lc_open; eassumption.
  - match goal with Hl : lc_tm (a_Transp ?x ?y) |- _ =>
      destruct (@lc_transp_inv x y Hl) as [Hx Hy];
      constructor; [ apply IHRed; exact Hx | exact Hy ] end.
  - match goal with Hl : lc_tm (a_Transp a_Refl ?y) |- _ =>
      destruct (@lc_transp_inv a_Refl y Hl) as [_ Hy]; exact Hy end.
  - match goal with Hl : lc_tm (a_Unbox ?g ?x) |- _ =>
      constructor; exact (IHRed (@lc_unbox_inv g x Hl)) end.
  - match goal with Hl : lc_tm (a_Unbox ?g (a_Box ?g ?x)) |- _ =>
      exact (@lc_unbox_box_inv g x Hl) end.
  - match goal with Hl : lc_tm (a_Proj1 ?g ?x) |- _ =>
      constructor; exact (IHRed (@lc_proj1_inv g x Hl)) end.
  - match goal with Hl : lc_tm (a_Proj2 ?g ?x) |- _ =>
      constructor; exact (IHRed (@lc_proj2_inv g x Hl)) end.
  - match goal with Hl : lc_tm (a_Proj1 ?g (a_SPair ?a1 ?g ?a2)) |- _ =>
      exact (@lc_proj1_beta_lc g a1 a2 Hl) end.
  - match goal with Hl : lc_tm (a_Proj2 ?g (a_SPair ?a1 ?g ?a2)) |- _ =>
      exact (@lc_proj2_beta_lc g a1 a2 Hl) end.
  - match goal with Hl : lc_tm (a_If ?x ?y ?z) |- _ =>
      destruct (@lc_if_inv x y z Hl) as [Hx [Hy Hz]];
      constructor; [ apply IHRed; exact Hx | exact Hy | exact Hz ] end.
  - match goal with Hl : lc_tm (a_If a_True ?y ?z) |- _ =>
      exact (@lc_if_true_lc y z Hl) end.
  - match goal with Hl : lc_tm (a_If a_False ?y ?z) |- _ =>
      exact (@lc_if_false_lc y z Hl) end.
Qed.

Lemma reds_lc : forall (a b:tm), Reds a b -> lc_tm a -> lc_tm b.
Proof.
  intros a b H. induction H as [x Hx | a0 a1 b0 Hred Hrest IH]; intros Hl.
  - exact Hl.
  - apply (IH (@red_lc a0 b0 Hred Hl)).
Qed.

Lemma typing_gdefeq_self : forall (W:context) (psi:grade) (a A:tm),
  Typing W psi a A -> GDefEq (labels W) psi a a.
Proof.
  intros W psi a A H. apply (typing_gdefeq_refl H). apply Order.POrderTheory.le_refl.
Qed.

Lemma reds_red : forall (a b c:tm), Reds a b -> Red b c -> lc_tm c -> Reds a c.
Proof.
  intros a b c Hab Hbc Hlc.
  apply (@reds_trans a b c Hab). apply (@red_reds b c Hbc Hlc).
Qed.

Lemma lc_pi_inv : forall (psi:grade) (A B:tm),
  lc_tm (a_Pi psi A B) -> lc_tm A /\ (forall x, lc_tm (open_tm_wrt_tm B (a_Var_f x))).
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_ssigma_inv : forall (psi:grade) (A B:tm),
  lc_tm (a_SSigma psi A B) -> lc_tm A /\ (forall x, lc_tm (open_tm_wrt_tm B (a_Var_f x))).
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_ceq_inv : forall (psi psi0:grade) (a b:tm) (psi1:grade) (A:tm),
  lc_tm (a_CEq psi0 a b psi1 A) -> lc_tm a /\ lc_tm b /\ lc_tm A.
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_t_inv : forall (psi:grade) (A:tm), lc_tm (a_T psi A) -> lc_tm A.
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_open_term : forall (B:tm) (k:nat) (a:tm),
  lc_tm B -> lc_tm a -> lc_tm (open_tm_wrt_tm_rec k a B).
Proof.
  intros B k a HB Ha.
  rewrite (@open_rec_identity B 0 (lc_wf HB) k a (Nat.le_0_l k)).
  exact HB.
Qed.

Lemma lc_open_any : forall (a b:tm), lc_tm a -> lc_tm b -> lc_tm (open_tm_wrt_tm a b).
Proof.
  intros a b Ha Hb. apply (@lc_open_term a 0 b Ha Hb).
Qed.

Lemma reds_value_eq : forall (a b:tm), Reds a b -> Value a = true -> a = b.
Proof.
  intros a b H Hv. induction H as [x Hx | a0 a1 b0 Hred Hrest IH].
  - reflexivity.
  - exfalso. apply (@value_no_red a0 Hv). exists b0. exact Hred.
Qed.

Lemma red_reds_lc : forall (a b:tm), Red a b -> lc_tm a -> Reds a b.
Proof.
  intros a b H Ha. apply (@red_reds a b H). apply (@red_lc a b H Ha).
Qed.

Lemma red_reds_trans : forall (a b c:tm), Red a b -> Reds b c -> lc_tm a -> Reds a c.
Proof.
  intros a b c Hab Hbc Ha.
  apply (@Rs_Step a c b Hab). exact Hbc.
Qed.


Lemma value_abs : forall (psi:grade) (A b:tm), Value (a_Abs psi A b) = true.
Proof. reflexivity. Qed.
Lemma value_pi : forall (psi:grade) (A B:tm), Value (a_Pi psi A B) = true.
Proof. reflexivity. Qed.
Lemma value_type : forall s, Value (a_Type s) = true.
Proof. reflexivity. Qed.
Lemma value_spair : forall (a:tm) (psi:grade) (b:tm), Value (a_SPair a psi b) = true.
Proof. reflexivity. Qed.
Lemma value_ssigma : forall (psi:grade) (A B:tm), Value (a_SSigma psi A B) = true.
Proof. reflexivity. Qed.
Lemma value_box : forall (psi:grade) (a:tm), Value (a_Box psi a) = true.
Proof. reflexivity. Qed.
Lemma value_t : forall (psi:grade) (A:tm), Value (a_T psi A) = true.
Proof. reflexivity. Qed.
Lemma not_value_app : forall (a:tm) (psi:grade) (b:tm), Value (a_App a psi b) = false.
Proof. reflexivity. Qed.
Lemma not_value_var_f : forall (x:tmvar), Value (a_Var_f x) = false.
Proof. reflexivity. Qed.
Lemma not_value_var_b : forall (n:nat), Value (a_Var_b n) = false.
Proof. reflexivity. Qed.
Lemma not_value_unbox : forall (psi:grade) (a:tm), Value (a_Unbox psi a) = false.
Proof. reflexivity. Qed.
Lemma not_value_proj1 : forall (psi:grade) (a:tm), Value (a_Proj1 psi a) = false.
Proof. reflexivity. Qed.
Lemma not_value_proj2 : forall (psi:grade) (a:tm), Value (a_Proj2 psi a) = false.
Proof. reflexivity. Qed.
Lemma not_value_transp : forall (a b:tm), Value (a_Transp a b) = false.
Proof. reflexivity. Qed.
Lemma not_value_if : forall (a b0 b1:tm), Value (a_If a b0 b1) = false.
Proof. reflexivity. Qed.

Lemma value_refl : Value a_Refl = true. Proof. reflexivity. Qed.
Lemma value_tmunit : Value a_TmUnit = true. Proof. reflexivity. Qed.
Lemma value_tyunit : Value a_TyUnit = true. Proof. reflexivity. Qed.
Lemma value_bool : Value a_Bool = true. Proof. reflexivity. Qed.
Lemma value_true : Value a_True = true. Proof. reflexivity. Qed.
Lemma value_false : Value a_False = true. Proof. reflexivity. Qed.
Lemma value_ceq : forall (psi psi0:grade) (a b:tm) (psi1:grade) (A:tm),
  Value (a_CEq psi0 a b psi1 A) = true.
Proof. reflexivity. Qed.

Ltac solve_value_red :=
  exfalso;
  match goal with
  | Hr : Red ?x _ |- _ =>
      let Hv := constr:(ltac:(vm_compute; reflexivity) : Value x = true) in
      exact (@value_no_red x Hv (ex_intro _ _ Hr))
  end.

Lemma red_det : forall (a b c:tm), Red a b -> Red a c -> b = c.
Proof.
  intros a b c H1. revert c. induction H1; intros c H2;
    inversion H2; subst; try reflexivity;
    try solve_value_red;
    try (f_equal; match goal with IH : forall c, Red ?x c -> _ = c |- _ => apply IH; assumption end).
Qed.

Lemma reds_normal_det : forall (a b c:tm),
  Reds a b -> Reds a c ->
  (forall u, Red b u -> False) -> (forall u, Red c u -> False) -> b = c.
Proof.
  intros a b c H1. revert c. induction H1 as [x Hx | a0 a1 b0 Hred Hrest IH]; intros c H2 Hb Hc.
  - inversion H2 as [y Hy | a0' a1' b1' Hred' Hrest'].
    + reflexivity.
    + exfalso; exact (Hb b1' Hred').
  - inversion H2 as [y Hy | a0' a1' b1' Hred' Hrest'].
    + subst c. exfalso; exact (Hc b0 Hred).
    + have Hb0 : b0 = b1' := @red_det a0 b0 b1' Hred Hred'.
      subst b1'.
      exact (IH c Hrest' Hb Hc).
Qed.

Lemma typing_okpar : forall (W:context) (psi:grade) (a A:tm),
  Typing W psi a A -> forall psi', psi <= psi' -> OKPar (labels W) psi' a.
Proof.
  intros W psi a A H. induction H; intros psi' Hle.
  - (* T_Type *) eapply OK_Type. apply uniq_labels. apply Ctx_uniq. assumption.
  - (* T_Var *) eapply (@OK_Var (labels W) psi' x psi0).
    + apply uniq_labels. apply Ctx_uniq. assumption.
    + exact (Order.POrderTheory.le_trans H0 Hle).
    + exact (binds_labels H1).
  - (* T_Pi *) eapply OK_Pi.
    + apply (IHTyping psi' Hle).
    + intros x Hx. apply (H1 x Hx psi' Hle).
  - (* T_Abs *)
    have HA : lc_tm A. { apply wf_lc. have HP := typing_wf H1. simpl in HP. exact (proj1 HP). }
    eapply OK_Abs; [ exact HA | ].
    intros x Hx. apply (H0 x Hx psi' Hle).
  - (* T_App *) eapply OK_App.
    + apply (IHTyping1 psi' Hle).
    + case: (boolP (psi0 <= psi')) => [Hle0|Hnle0].
      * apply OKC_Leq; [ exact Hle0 | apply (IHTyping2 psi' Hle0) ].
      * move/negP: Hnle0 => Hnle0. apply OKC_NLeq; [ exact Hnle0 | exact (typing_lc H0) | exact (uniq_labels_typing H0) ].
  - (* T_Conv *) apply (IHTyping1 psi' Hle).
  - (* T_Refl *) eapply OK_Refl. exact (uniq_labels_typing H).
  - (* T_CEq *) eapply OK_CEq.
    + exact (typing_lc H1).
    + apply (IHTyping1 psi' (Order.POrderTheory.le_trans H3 (Order.POrderTheory.le_trans H4 Hle))).
    + apply (IHTyping2 psi' (Order.POrderTheory.le_trans H3 (Order.POrderTheory.le_trans H4 Hle))).
    + exact (Order.POrderTheory.le_trans H4 Hle).
  - (* T_Transp *) eapply OK_Transp.
    + apply (IHTyping1 psi' Hle).
    + apply (IHTyping2 psi' Hle).
  - (* T_T *) eapply OK_T. apply (IHTyping psi' Hle).
  - (* T_Box *)
    eapply OK_Box.
    case: (boolP (psi0 <= psi')) => [Hle0|Hnle0].
    + apply OKC_Leq; [ exact Hle0 | apply (IHTyping1 psi' Hle0) ].
    + move/negP: Hnle0 => Hnle0. apply OKC_NLeq; [ exact Hnle0 | exact (typing_lc H) | exact (uniq_labels_typing H0) ].
  - (* T_Unbox *) eapply OK_Unbox.
    + apply (IHTyping psi' Hle).
    + exact (Order.POrderTheory.le_trans H0 Hle).
  - (* T_SSigma *) eapply OK_SSigma.
    + apply (IHTyping psi' Hle).
    + intros x Hx. apply (H1 x Hx psi' Hle).
  - (* T_SPair *) eapply OK_SPair.
    + case: (boolP (psi0 <= psi')) => [Hle0|Hnle0].
      * apply OKC_Leq; [ exact Hle0 | apply (IHTyping2 psi' Hle0) ].
      * move/negP: Hnle0 => Hnle0. apply OKC_NLeq; [ exact Hnle0 | exact (typing_lc H0) | exact (uniq_labels_typing H0) ].
    + apply (IHTyping3 psi' Hle).
  - (* T_Proj1 *) eapply OK_Proj1.
    + apply (IHTyping psi' Hle).
    + exact (Order.POrderTheory.le_trans H0 Hle).
  - (* T_Proj2 *) eapply OK_Proj2. apply (IHTyping1 psi' Hle).
  - (* T_TyUnit *) eapply OK_TyUnit. apply uniq_labels. apply Ctx_uniq. assumption.
  - (* T_TmUnit *) eapply OK_TmUnit. exact (uniq_labels_typing H).
  - (* T_Bool *) eapply OK_Bool. apply uniq_labels. apply Ctx_uniq. assumption.
  - (* T_True *) eapply OK_True. exact (uniq_labels_typing H).
  - (* T_False *) eapply OK_False. exact (uniq_labels_typing H).
  - (* T_If *) eapply OK_If.
    + apply (IHTyping1 psi' Hle).
    + apply (IHTyping2 psi' Hle).
    + apply (IHTyping3 psi' Hle).
Qed.


Lemma typing_par_refl : forall (W:context) (psi:grade) (a A:tm),
  Typing W psi a A -> forall psi', psi <= psi' -> Par (labels W) psi' a a.
Proof.
  intros W psi a A H psi' Hle.
  apply okpar_par.
  - exact (@typing_okpar W psi a A H psi' Hle).
  - exact (@uniq_labels_typing W psi a A H).
Qed.

Lemma typing_par_self : forall (W:context) (psi:grade) (a A:tm),
  Typing W psi a A -> Par (labels W) psi a a.
Proof.
  intros W psi a A H. apply (@typing_par_refl W psi a A H psi).
  apply Order.POrderTheory.le_refl.
Qed.

Lemma typing_abs_pi_defeq : forall (W:context) (psi:grade) (a A:tm),
  Typing W psi a A ->
  forall (psia:grade) (A0 a0:tm), a = a_Abs psia A0 a0 ->
    exists B0, DefEq (labels W) A (a_Pi psia A0 B0).
Proof.
  intros W psi a A H. induction H; intros psia A0 ab Heq; try discriminate Heq.
  - (* T_Abs *) injection Heq as E1 E2 E3. subst.
    exists B. eapply E_One.
    exact (typing_gdefeq_self H1).
  - (* T_Conv *) destruct (IHTyping1 psia A0 ab Heq) as [B0 Hdef].
    exists B0.
    apply (@defeq_trans (labels W) B A (a_Pi psia A0 B0)).
    + apply defeq_sym. exact H1.
    + exact Hdef.
Qed.

Lemma typing_abs_lc : forall (W:context) (psi:grade) (a A:tm),
  Typing W psi a A ->
  forall (psia:grade) (A0 ab:tm), a = a_Abs psia A0 ab -> lc_tm A0.
Proof.
  intros W psi a A H. induction H; intros psia A0 ab Heq; try discriminate Heq.
  - (* T_Abs *) injection Heq as E1 E2 E3. subst.
    apply wf_lc. have HP := typing_wf H1. simpl in HP. exact (proj1 HP).
  - (* T_Conv *) apply (IHTyping1 psia A0 ab Heq).
Qed.

Lemma typing_pi_sort : forall (W:context) (psi:grade) (a T:tm),
  Typing W psi a T ->
  forall (psia:grade) (A B:tm), a = a_Pi psia A B ->
    exists s, DefEq (labels W) T (a_Type s).
Proof.
  intros W psi a T H. induction H; intros psia A0 B0 Heq; try discriminate Heq.
  - (* T_Pi *) injection Heq as E1 E2 E3. subst.
    exists s3. eapply E_One.
    apply (@GE_Type (labels W) psi s3).
    apply uniq_labels. apply Ctx_uniq. apply typing_ctx in H. exact H.
  - (* T_Conv *) destruct (IHTyping1 psia A0 B0 Heq) as [s0 Hs0].
    exists s0.
    apply (@defeq_trans (labels W) B A (a_Type s0)).
    + apply defeq_sym. exact H1.
    + exact Hs0.
Qed.

Fixpoint typing_abs_full (W:context) (psi:grade) (a T:tm) (H:Typing W psi a T) {struct H}
  : forall (psia:grade) (A0 ab:tm), a = a_Abs psia A0 ab ->
    exists B0, DefEq (labels W) T (a_Pi psia A0 B0) /\
      (exists L:vars, forall x, x \notin L ->
        Typing ((x,(psia,A0))::W) psi
          (open_tm_wrt_tm ab (a_Var_f x)) (open_tm_wrt_tm B0 (a_Var_f x))).
Proof.
  intros psia A0 ab Heq.
  destruct H; try discriminate Heq.
  - (* T_Abs *) injection Heq as E1 E2 E3. subst.
    exists B. split.
    + eapply E_One. exact (typing_gdefeq_self H0).
    + exists L. intros x Hx. exact (H x Hx).
  - (* T_Conv *) destruct (typing_abs_full W psi a A H psia A0 ab Heq) as [B0 [Hdef Hbody]].
    exists B0. split.
    + eapply defeq_trans.
      * apply defeq_sym. exact H1.
      * exact Hdef.
    + exact Hbody.
Qed.

Lemma typing_abs_defeq_to_pi : forall (W:context) (psi:grade) (psia:grade) (A0 a0 T:tm),
  Typing W psi (a_Abs psia A0 a0) T ->
  exists B0, DefEq (labels W) T (a_Pi psia A0 B0).
Proof.
  intros W psi psia A0 a0 T H.
  destruct (@typing_abs_full W psi (a_Abs psia A0 a0) T H psia A0 a0 eq_refl)
    as [B0 [Hdef _]]. exists B0. exact Hdef.
Qed.

Lemma typing_abs_body_typing : forall (W:context) (psi:grade) (psia:grade) (A0 a0 T:tm),
  Typing W psi (a_Abs psia A0 a0) T ->
  exists B0 L, forall x, x \notin L ->
    Typing ((x,(psia,A0))::W) psi
      (open_tm_wrt_tm a0 (a_Var_f x)) (open_tm_wrt_tm B0 (a_Var_f x)).
Proof.
  intros W psi psia A0 a0 T H.
  destruct (@typing_abs_full W psi (a_Abs psia A0 a0) T H psia A0 a0 eq_refl)
    as [B0 [_ [L Hb]]]. exists B0, L. exact Hb.
Qed.

Lemma value_iff_headform : forall (t:tm),
  Value t = true <-> exists h, tm_to_headform t = Some h.
Proof.
  intros t. split.
  - apply value_headform.
  - intros [h Hh]. exact (@headform_value t h Hh).
Qed.

Lemma typing_var_binds : forall (W:context) (psi:grade) (a T:tm),
  Typing W psi a T ->
  forall xx, a = a_Var_f xx -> exists g A, binds xx (g,A) W /\ g <= psi.
Proof.
  intros W psi a T H. induction H; intros xx Heq; try discriminate Heq.
  - (* T_Var *) injection Heq as Ex. subst. exists psi0, A. split; assumption.
  - (* T_Conv *) apply (IHTyping1 xx Heq).
Qed.

Fixpoint typing_refl_full (W:context) (psi:grade) (a T:tm) (H:Typing W psi a T) {struct H}
  : a = a_Refl ->
    exists (psi0 psi1:grade) (A a0:tm),
      DefEq (labels W) T (a_CEq psi0 a0 a0 psi1 A).
Proof.
  intros Heq.
  destruct H; try discriminate Heq.
  - (* T_Conv *) destruct (typing_refl_full W psi a A H Heq)
      as [ps0 [ps1 [B0 [c0 Hdef]]]].
    exists ps0; exists ps1; exists B0; exists c0. eapply defeq_trans.
    + apply defeq_sym. exact H1.
    + exact Hdef.
  - (* T_Refl *) eexists. eexists. eexists. eexists.
    eapply E_One. exact (typing_gdefeq_self H).
Qed.

Fixpoint typing_box_full (W:context) (psi:grade) (a T:tm) (H:Typing W psi a T) {struct H}
  : forall (psi0:grade) (b:tm), a = a_Box psi0 b ->
    exists (A:tm) (s:sort_sig.sort),
      DefEq (labels W) T (a_T psi0 A) /\ Typing W psi0 b A.
Proof.
  intros psi0 b Heq.
  destruct H; try discriminate Heq.
  - (* T_Conv *) destruct (typing_box_full W psi a A H psi0 b Heq)
      as [A1 [s1 [Hdef Hcontent]]].
    exists A1, s1. split.
    + eapply defeq_trans. apply defeq_sym; exact H1. exact Hdef.
    + exact Hcontent.
  - (* T_Box *) injection Heq as E1 E2. subst.
    exists A, s. split.
    + eapply E_One. exact (typing_gdefeq_self H0).
    + exact H.
Qed.

Fixpoint typing_spair_full (W:context) (psi:grade) (a T:tm) (H:Typing W psi a T) {struct H}
  : forall (psi0:grade) (a0 b0:tm), a = a_SPair a0 psi0 b0 ->
    exists (A B:tm) (s:sort_sig.sort),
      DefEq (labels W) T (a_SSigma psi0 A B) /\
      Typing W psi0 a0 A /\
      Typing W psi b0 (open_tm_wrt_tm B a0).
Proof.
  intros psi0 a0 b0 Heq.
  destruct H; try discriminate Heq.
  - (* T_Conv *) destruct (typing_spair_full W psi a A H psi0 a0 b0 Heq)
      as [A1 [B1 [s1 [Hdef [Hcont Hbody]]]]].
    exists A1, B1, s1. split; [ | split].
    + eapply defeq_trans. apply defeq_sym; exact H1. exact Hdef.
    + exact Hcont.
    + exact Hbody.
  - (* T_SPair *) injection Heq as E1 E2 E3. subst.
    exists A, B, s. split; [ | split].
    + eapply E_One. exact (typing_gdefeq_self H).
    + exact H0.
    + exact H1.
Qed.

Fixpoint typing_t_full (W:context) (psi:grade) (a T:tm) (H:Typing W psi a T) {struct H}
  : forall (psi0:grade) (A0:tm), a = a_T psi0 A0 ->
    exists (s s1:sort_sig.sort),
      DefEq (labels W) T (a_Type s) /\ Typing W psi A0 (a_Type s1).
Proof.
  intros psi0 A0 Heq.
  destruct H; try discriminate Heq.
  - (* T_Conv *) destruct (typing_t_full W psi a A H psi0 A0 Heq)
      as [s1 [s2 [Hdef Hcont]]].
    exists s1, s2. split.
    + eapply defeq_trans. apply defeq_sym; exact H1. exact Hdef.
    + exact Hcont.
  - (* T_T *) injection Heq as E1 E2. subst.
    exists s2, s1. split.
    + eapply E_One. apply (@GE_Type (labels W) psi s2).
      apply uniq_labels. apply Ctx_uniq. apply typing_ctx in H. exact H.
    + exact H.
Qed.

Fixpoint typing_tmunit_full (W:context) (psi:grade) (a T:tm) (H:Typing W psi a T) {struct H}
  : a = a_TmUnit -> exists (psi0:grade) s, DefEq (labels W) T a_TyUnit /\ Typing W psi0 a_TyUnit (a_Type s).
Proof.
  intros Heq. destruct H; try discriminate Heq.
  - (* T_Conv *) destruct (typing_tmunit_full W psi a A H Heq) as [ps1 [s1 [Hdef Hprem]]].
    exists ps1, s1. split.
    + eapply defeq_trans. apply defeq_sym; exact H1. exact Hdef.
    + exact Hprem.
  - (* T_TmUnit *) clear Heq.
    exists psi0, s. split.
    + eapply E_One. apply (@GE_TyUnit (labels W) psi).
      apply uniq_labels. apply Ctx_uniq. apply typing_ctx in H. exact H.
    + exact H.
Qed.

Fixpoint typing_true_full (W:context) (psi:grade) (a T:tm) (H:Typing W psi a T) {struct H}
  : a = a_True -> exists (psi0:grade) s, DefEq (labels W) T a_Bool /\ Typing W psi0 a_Bool (a_Type s).
Proof.
  intros Heq. destruct H; try discriminate Heq.
  - (* T_Conv *) destruct (typing_true_full W psi a A H Heq) as [ps1 [s1 [Hdef Hprem]]].
    exists ps1, s1. split.
    + eapply defeq_trans. apply defeq_sym; exact H1. exact Hdef.
    + exact Hprem.
  - (* T_True *) clear Heq.
    exists psi0, s. split.
    + eapply E_One. apply (@GE_Bool (labels W) psi).
      apply uniq_labels. apply Ctx_uniq. apply typing_ctx in H. exact H.
    + exact H.
Qed.

Fixpoint typing_false_full (W:context) (psi:grade) (a T:tm) (H:Typing W psi a T) {struct H}
  : a = a_False -> exists (psi0:grade) s, DefEq (labels W) T a_Bool /\ Typing W psi0 a_Bool (a_Type s).
Proof.
  intros Heq. destruct H; try discriminate Heq.
  - (* T_Conv *) destruct (typing_false_full W psi a A H Heq) as [ps1 [s1 [Hdef Hprem]]].
    exists ps1, s1. split.
    + eapply defeq_trans. apply defeq_sym; exact H1. exact Hdef.
    + exact Hprem.
  - (* T_False *) clear Heq.
    exists psi0, s. split.
    + eapply E_One. apply (@GE_Bool (labels W) psi).
      apply uniq_labels. apply Ctx_uniq. apply typing_ctx in H. exact H.
    + exact H.
Qed.

Lemma typing_type_inv : forall (W:context) (psi:grade) (a T:tm),
  Typing W psi a T ->
  forall s0, a = a_Type s0 ->
    exists s1, axiom s0 s1 /\ DefEq (labels W) T (a_Type s1).
Proof.
  intros W psi a T H. induction H; intros s0 Heq; try discriminate Heq.
  - (* T_Type *) injection Heq as E1. subst.
    exists s2. split.
    + exact H0.
    + eapply E_One. apply (@GE_Type (labels W) psi s2).
      apply uniq_labels. apply Ctx_uniq. exact H.
  - (* T_Conv *) destruct (IHTyping1 s0 Heq) as [s1 [Hax Hdef]].
    exists s1. split.
    + exact Hax.
    + eapply defeq_trans. apply defeq_sym; exact H1. exact Hdef.
Qed.

Fixpoint typing_pi_full (W:context) (psi:grade) (a T:tm) (H:Typing W psi a T) {struct H}
  : forall (psia:grade) (A0 B0:tm), a = a_Pi psia A0 B0 ->
    exists (s3:sort_sig.sort) (L:vars) (s1 s2:sort_sig.sort),
      DefEq (labels W) T (a_Type s3) /\
      Typing W psi A0 (a_Type s1) /\
      (forall x, x \notin L ->
        Typing ((x,(psia,A0))::W) psi (open_tm_wrt_tm B0 (a_Var_f x)) (a_Type s2)).
Proof.
  intros psia A0 B0 Heq.
  destruct H; try discriminate Heq.
  - (* T_Pi *) injection Heq as E1 E2 E3. subst.
    exists s3, L, s1, s2. split; [ | split].
    + eapply E_One. apply (@GE_Type (labels W) psi s3).
      apply uniq_labels. apply Ctx_uniq. apply typing_ctx in H. exact H.
    + exact H.
    + exact H0.
  - (* T_Conv *) destruct (typing_pi_full W psi a A H psia A0 B0 Heq)
      as [s3 [L [s1 [s2 [Hdef [Hdom Hbody]]]]]].
    exists s3, L, s1, s2. split; [ | split].
    + eapply defeq_trans. apply defeq_sym; exact H1. exact Hdef.
    + exact Hdom.
    + exact Hbody.
Qed.

Lemma typing_abs_domain_typing : forall (W:context) (psi:grade) (psia:grade) (A0 ab T:tm),
  Typing W psi (a_Abs psia A0 ab) T ->
  exists (psi_A:grade) s, Typing W psi_A A0 (a_Type s).
Proof.
  intros W psi psia A0 ab T H.
  destruct (@typing_abs_full W psi (a_Abs psia A0 ab) T H psia A0 ab eq_refl)
    as [B0 [_ [L Hbody]]].
  destruct (atom_fresh L) as [x Hx].
  pose proof (typing_ctx (Hbody x Hx)) as HC.
  inversion HC as [| W0 xx g0 AA ps0 ss HCtx HTy Hnin]; subst.
  exists ps0, ss. exact HTy.
Qed.

Lemma typing_pi_domain_typing : forall (W:context) (psi:grade) (psia:grade) (A0 B0 T:tm),
  Typing W psi (a_Pi psia A0 B0) T ->
  exists s, Typing W psi A0 (a_Type s).
Proof.
  intros W psi psia A0 B0 T H.
  destruct (@typing_pi_full W psi (a_Pi psia A0 B0) T H psia A0 B0 eq_refl)
    as [s3 [L [s1 [s2 [Hdef [Hdom Hbody]]]]]].
  exists s1. exact Hdom.
Qed.

Lemma typing_pi_body_typing : forall (W:context) (psi:grade) (psia:grade) (A0 B0 T:tm),
  Typing W psi (a_Pi psia A0 B0) T ->
  exists s L, forall x, x \notin L ->
    Typing ((x,(psia,A0))::W) psi (open_tm_wrt_tm B0 (a_Var_f x)) (a_Type s).
Proof.
  intros W psi psia A0 B0 T H.
  destruct (@typing_pi_full W psi (a_Pi psia A0 B0) T H psia A0 B0 eq_refl)
    as [s3 [L [s1 [s2 [Hdef [Hdom Hbody]]]]]].
  exists s2, L. exact Hbody.
Qed.

Lemma fv_subst_notin : forall (t:tm) (c:tm) (x:atom) (y:atom),
  y \notin fv_tm t -> y \notin fv_tm c -> y \notin fv_tm (subst_tm c x t).
Proof.
  intros t. induction t as [| |psi A IHA Btx IHB|psi A IHA b IHb|a0 IHa psi b IHb
                 |s|n|z|psi a0 IHa b IHb psi0 A IHA| |a0 IHa b IHb|psi A IHA
                 |psi a0 IHa|psi a0 IHa|psi A IHA Btx IHB|a0 IHa psi b IHb|psi a0 IHa
                 |psi a0 IHa| | | |a0 IHa b0 IHb0 b1 IHb1];
  intros c x y Hx Hc; simpl in *.
  - exact Hx. - exact Hx.
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHA c x y HA Hc).
    + exact (IHB c x y HB Hc).
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHA c x y HA Hc).
    + exact (IHb c x y HB Hc).
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHa c x y HA Hc).
    + exact (IHb c x y HB Hc).
  - exact Hx.
  - exact Hx.
  - cbn [subst_tm]. destruct (@eq_dec tmvar EqDec_eq_of_X z x) as [E|NE]; cbn [is_left].
    + exact Hc.
    + exact Hx.
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as Hbc.
    apply notin_union_1 in Hbc as HB. apply notin_union_2 in Hbc as HC.
    apply notin_union.
    + exact (IHa c x y HA Hc).
    + apply notin_union.
      * exact (IHb c x y HB Hc).
      * exact (IHA c x y HC Hc).
  - exact Hx.
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHa c x y HA Hc).
    + exact (IHb c x y HB Hc).
  - exact (IHA c x y Hx Hc).
  - exact (IHa c x y Hx Hc).
  - exact (IHa c x y Hx Hc).
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHA c x y HA Hc).
    + exact (IHB c x y HB Hc).
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as HB.
    apply notin_union.
    + exact (IHa c x y HA Hc).
    + exact (IHb c x y HB Hc).
  - exact (IHa c x y Hx Hc).
  - exact (IHa c x y Hx Hc).
  - exact Hx. - exact Hx. - exact Hx.
  - apply notin_union_1 in Hx as HA. apply notin_union_2 in Hx as Hbc.
    apply notin_union_1 in Hbc as HB. apply notin_union_2 in Hbc as HC.
    apply notin_union.
    + exact (IHa c x y HA Hc).
    + apply notin_union.
      * exact (IHb0 c x y HB Hc).
      * exact (IHb1 c x y HC Hc).
Qed.

Fixpoint typing_ceq_full (W:context) (psi:grade) (a T:tm) (H:Typing W psi a T) {struct H}
  : forall (psia psib:grade) (A0 B0 C0:tm), a = a_CEq psia A0 B0 psib C0 ->
    exists (psi2:grade) (s2 s1:sort_sig.sort),
      DefEq (labels W) T (a_Type s2) /\
      Typing W psib A0 C0 /\ Typing W psib B0 C0 /\ Typing W psi2 C0 (a_Type s1).
Proof.
  intros psia psib A0 B0 C0 Heq.
  destruct H; try discriminate Heq.
  - (* T_Conv *) destruct (typing_ceq_full W psi a A H psia psib A0 B0 C0 Heq)
      as [ps2 [s2 [s1 [Hdef [Hta [Htb HtA]]]]]].
    exists ps2, s2, s1. split; [ | split; [ | split]].
    + eapply defeq_trans. apply defeq_sym; exact H1. exact Hdef.
    + exact Hta.
    + exact Htb.
    + exact HtA.
  - (* T_CEq *) injection Heq as E1 E2 E3 E4 E5. subst.
    exists psi2, s2, s1. split; [ | split; [ | split]].
    + eapply E_One. apply (@GE_Type (labels W) psi s2).
      apply uniq_labels. apply Ctx_uniq. apply typing_ctx in H. exact H.
    + exact H.
    + exact H0.
    + exact H1.
Qed.

Theorem preservation :
    forall a b Γ ψ A,
      Typing Γ ψ a A ->
      Red a b ->
      Typing Γ ψ b A.

Theorem progress : forall ψ a A,
  Typing nil ψ a A ->
  Value a \/ exists b, Red a b.
