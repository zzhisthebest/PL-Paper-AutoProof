From diris.lambdabar Require Import definitions.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Lia.
From Stdlib Require Import Classical.

Fixpoint anyb {A : Type} (l : list A) (f : A -> bool) : bool :=
  match l with
  | [] => false
  | x :: l' => if f x then true else anyb l' f
  end.

Lemma anyb_true {A : Type} (l : list A) (f : A -> bool) :
  anyb l f = true <-> exists x, x ∈ l /\ f x = true.
Proof.
  induction l as [|x l' IH]; simpl.
  - split.
    + discriminate.
    + intros (y & Hy & Hfy). apply elem_of_nil in Hy. destruct Hy.
  - destruct (f x) eqn:E.
    + split.
      * intros _. exists x. split; [apply elem_of_cons; left; done|done].
      * intros _. reflexivity.
    + rewrite IH. split.
      * intros (y & Hy & Hfy). exists y. split; [|done].
        apply elem_of_cons. right. exact Hy.
      * intros (y & Hy & Hfy). exists y. split; [|done].
        apply elem_of_cons in Hy as [->|Hy]; [rewrite E in Hfy; discriminate|done].
Qed.

Lemma anyb_false {A : Type} (l : list A) (f : A -> bool) :
  (forall x, x ∈ l -> f x = false) -> anyb l f = false.
Proof.
  induction l as [|x l IH]; intros H; simpl; [done|].
  rewrite H by (left; done). apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma anyb_ext {A : Type} (l : list A) (f g : A -> bool) :
  (forall x, x ∈ l -> f x = g x) -> anyb l f = anyb l g.
Proof.
  induction l as [|x l IH]; intros H; simpl; [done|].
  rewrite H by (left; done). destruct (g x); [done|]. apply IH.
  intros y Hy. apply H. right. exact Hy.
Qed.
From stdpp Require Import base.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Typeclasses Transparent env.

(* ------------------------------------------------------------------ *)
(* Auxiliary definitions                                              *)
(* ------------------------------------------------------------------ *)

Definition dual (t : type) : type :=
  match t with
  | FunT Lin a b => FunT Lin b a
  | _ => t
  end.

Lemma dual_FunT a b : dual (FunT Lin a b) = FunT Lin b a.
Proof. reflexivity. Qed.

Lemma dual_dual a b : dual (dual (FunT Lin a b)) = FunT Lin a b.
Proof. reflexivity. Qed.

Lemma FunT_inj l1 a1 b1 l2 a2 b2 (H : FunT l1 a1 b1 = FunT l2 a2 b2) :
  l1 = l2 /\ a1 = a2 /\ b1 = b2.
Proof. injection H as H1 H2 H3. auto. Qed.

Lemma FunT_neq_UnitT l a b : FunT l a b <> UnitT.
Proof. intros H. discriminate H. Qed.

(* Extensional facts about [unr] (a coinductive predicate). *)
Lemma unr_FunT_inv l a b : unr (FunT l a b) -> l = Unr.
Proof. intros H. dependent destruction H. reflexivity. Qed.

Lemma unr_PairT_inv a b : unr (PairT a b) -> unr a /\ unr b.
Proof. intros H. dependent destruction H. auto. Qed.

Lemma unr_SumT_inv n ts : unr (SumT n ts) -> forall i, unr (ts i).
Proof. intros H. dependent destruction H. auto. Qed.

Lemma unr_UnitT : unr UnitT.
Proof. constructor. Qed.

Lemma unr_FunT_Unr a b : unr (FunT Unr a b).
Proof. constructor. Qed.

Lemma unr_FunT_Lin_false a b : unr (FunT Lin a b) -> False.
Proof. intros H. dependent destruction H. Qed.

(* ------------------------------------------------------------------ *)
(* Runtime typing                                                     *)
(* ------------------------------------------------------------------ *)

Inductive rt : env -> gmap nat type -> expr -> type -> Prop :=
| rt_Var Γ Δ x t :
    env_var Γ x t -> Δ = ∅ -> rt Γ Δ (Var x) t
| rt_Fun Γ Γ' Δ x e t1 t2 l :
    env_bind Γ' x t1 Γ ->
    (l = Unr -> env_unr Γ) ->
    (l = Unr -> Δ = ∅) ->
    rt Γ' Δ e t2 ->
    rt Γ Δ (Fun x e) (FunT l t1 t2)
| rt_App Γ Γ1 Γ2 Δ Δ1 Δ2 e1 e2 t1 t2 l :
    env_split Γ Γ1 Γ2 ->
    Δ = Δ1 ∪ Δ2 -> Δ1 ##ₘ Δ2 ->
    rt Γ1 Δ1 e1 (FunT l t1 t2) ->
    rt Γ2 Δ2 e2 t1 ->
    rt Γ Δ (App e1 e2) t2
| rt_Unit Γ Δ :
    env_unr Γ -> Δ = ∅ -> rt Γ Δ Unit UnitT
| rt_Pair Γ Γ1 Γ2 Δ Δ1 Δ2 e1 e2 t1 t2 :
    env_split Γ Γ1 Γ2 ->
    Δ = Δ1 ∪ Δ2 -> Δ1 ##ₘ Δ2 ->
    rt Γ1 Δ1 e1 t1 -> rt Γ2 Δ2 e2 t2 ->
    rt Γ Δ (Pair e1 e2) (PairT t1 t2)
| rt_LetPair Γ Γ1 Γ2 Δ Δ1 Δ2 e1 e2 t1 t2 t :
    env_split Γ Γ1 Γ2 ->
    Δ = Δ1 ∪ Δ2 -> Δ1 ##ₘ Δ2 ->
    rt Γ1 Δ1 e1 (PairT t1 t2) ->
    rt Γ2 Δ2 e2 (FunT Lin t1 (FunT Lin t2 t)) ->
    rt Γ Δ (LetPair e1 e2) t
| rt_Sum Γ Δ n (ts : fin n -> type) (i : fin n) e :
    rt Γ Δ e (ts i) -> rt Γ Δ (Sum (fin_to_nat i) e) (SumT n ts)
| rt_MatchSum n Γ Γ1 Γ2 Δ Δ1 Δ2 t (ts : fin n -> type) (es : fin n -> expr) e :
    env_split Γ Γ1 Γ2 ->
    Δ = Δ1 ∪ Δ2 -> Δ1 ##ₘ Δ2 ->
    (n = 0 -> env_unr Γ2) ->
    rt Γ1 Δ1 e (SumT n ts) ->
    (forall i, rt Γ2 Δ2 (es i) (FunT Lin (ts i) t)) ->
    rt Γ Δ (MatchSum n e es) t
| rt_Fork Γ Δ e t1 t2 :
    rt Γ Δ e (FunT Lin (FunT Lin t2 t1) UnitT) ->
    rt Γ Δ (Fork e) (FunT Lin t1 t2)
| rt_Val Γ Δ v t :
    env_unr Γ -> rtv Δ v t -> rt Γ Δ (Val v) t
with rtv : gmap nat type -> val -> type -> Prop :=
| rtv_Unit Δ :
    Δ = ∅ -> rtv Δ UnitV UnitT
| rtv_Fun Δ x e t1 t2 l :
    (l = Unr -> Δ = ∅) ->
    rt {[ x := t1 ]} Δ e t2 ->
    rtv Δ (FunV x e) (FunT l t1 t2)
| rtv_Pair Δ Δ1 Δ2 v1 v2 t1 t2 :
    Δ = Δ1 ∪ Δ2 -> Δ1 ##ₘ Δ2 ->
    rtv Δ1 v1 t1 -> rtv Δ2 v2 t2 ->
    rtv Δ (PairV v1 v2) (PairT t1 t2)
| rtv_Sum Δ n (ts : fin n -> type) (i : fin n) v :
    rtv Δ v (ts i) -> rtv Δ (SumV (fin_to_nat i) v) (SumT n ts)
| rtv_Barrier Δ n a b :
    Δ = {[ n := FunT Lin a b ]} ->
    rtv Δ (BarrierV n) (FunT Lin a b).

(* ------------------------------------------------------------------ *)
(* Basic environment and endpoint-context lemmas                      *)
(* ------------------------------------------------------------------ *)

Lemma env_unr_subset Γ Γ' : env_unr Γ' -> Γ ⊆ Γ' -> env_unr Γ.
Proof.
  intros H Hsub x t Hx. apply (H x t).
  destruct (map_subseteq_spec Γ Γ') as [Hf _]. exact (Hf Hsub x t Hx).
Qed.

Lemma env_unr_empty : env_unr (∅ : env).
Proof. intros x t Hx. exfalso. exact (lookup_empty_Some x t Hx). Qed.

Lemma map_subseteq_union_l_str {A} (m1 m2 : gmap string A) : m1 ⊆ m1 ∪ m2.
Proof.
  destruct (map_subseteq_spec m1 (m1 ∪ m2)) as [_ Hg]. apply Hg.
  intros i v Hi. apply (lookup_union_Some_l m1 m2 i v Hi).
Qed.

Lemma map_subseteq_union_l_nat {A} (m1 m2 : gmap nat A) : m1 ⊆ m1 ∪ m2.
Proof.
  destruct (map_subseteq_spec m1 (m1 ∪ m2)) as [_ Hg]. apply Hg.
  intros i v Hi. apply (lookup_union_Some_l m1 m2 i v Hi).
Qed.

Lemma env_split_l_sub Γ Γ1 Γ2 : env_split Γ Γ1 Γ2 -> Γ1 ⊆ Γ.
Proof. intros [Heq _]. rewrite Heq. apply map_subseteq_union_l_str. Qed.

Lemma env_split_r_sub Γ Γ1 Γ2 : env_split Γ Γ1 Γ2 -> Γ2 ⊆ Γ.
Proof.
  intros [Heq Hd]. rewrite Heq.
  destruct (map_subseteq_spec Γ2 (Γ1 ∪ Γ2)) as [_ Hg]. apply Hg.
  intros i v Hi. destruct (Γ1 !! i) as [a|] eqn:E1.
  - rewrite (lookup_union_Some_l Γ1 Γ2 i a E1).
    destruct (Hd i a v E1 Hi) as [-> _]. done.
  - rewrite (lookup_union_r Γ1 Γ2 i E1). done.
Qed.

Lemma env_unr_split_l Γ Γ1 Γ2 : env_split Γ Γ1 Γ2 -> env_unr Γ -> env_unr Γ1.
Proof. intros Hs H. apply (env_unr_subset H). apply env_split_l_sub in Hs. done. Qed.

Lemma env_unr_split_r Γ Γ1 Γ2 : env_split Γ Γ1 Γ2 -> env_unr Γ -> env_unr Γ2.
Proof. intros Hs H. apply (env_unr_subset H). apply env_split_r_sub in Hs. done. Qed.

Lemma env_unr_insert Γ x t : x ∉ dom Γ -> env_unr (<[x:=t]> Γ) -> env_unr Γ.
Proof.
  intros Hdom H. apply (env_unr_subset H).
  destruct (map_subseteq_spec Γ (<[x:=t]> Γ)) as [_ Hg]. apply Hg.
  intros i v Hi. rewrite (lookup_insert Γ x i t).
  destruct (decide (x = i)) as [->|Hne].
  - exfalso. apply Hdom. apply elem_of_dom. rewrite Hi. done.
  - done.
Qed.

Lemma env_unr_insert_ty Γ x t : env_unr (<[x:=t]> Γ) -> unr t.
Proof.
  intros H. apply (H x t). rewrite (lookup_insert_eq Γ x t). done.
Qed.

Lemma env_unr_union_l Γ1 Γ2 : env_unr (Γ1 ∪ Γ2) -> env_unr Γ1.
Proof.
  intros H x t Hx. apply (H x t). apply (lookup_union_Some_l Γ1 Γ2 x t Hx).
Qed.

Lemma env_unr_union Γ1 Γ2 : env_unr Γ1 -> env_unr Γ2 -> env_unr (Γ1 ∪ Γ2).
Proof.
  intros H1 H2 x t Hx. destruct (Γ1 !! x) as [a|] eqn:E1.
  - rewrite (lookup_union_Some_l Γ1 Γ2 x a E1) in Hx.
    injection Hx as Hta. subst a. apply (H1 x t E1).
  - rewrite (lookup_union_r Γ1 Γ2 x E1) in Hx. apply (H2 x t Hx).
Qed.

Lemma disj_sym Γ1 Γ2 : disj Γ1 Γ2 -> disj Γ2 Γ1.
Proof.
  intros Hd i t1 t2 H1 H2. destruct (Hd i t2 t1 H2 H1) as [He Hu].
  split; [symmetry; exact He | rewrite <- He; exact Hu].
Qed.

(* ------------------------------------------------------------------ *)
(* Union helpers for the two key types in use                         *)
(* ------------------------------------------------------------------ *)

Lemma union_empty_l_nat {A} (m : gmap nat A) : (∅ ∪ m) = m.
Proof. apply map_eq. intro i. rewrite (lookup_union (∅ : gmap nat A) m i). destruct (m!!i); done. Qed.
Lemma union_empty_r_nat {A} (m : gmap nat A) : (m ∪ ∅) = m.
Proof. apply map_eq. intro i. rewrite (lookup_union m (∅ : gmap nat A) i). destruct (m!!i); done. Qed.
Lemma union_empty_l_str {A} (m : gmap string A) : (∅ ∪ m) = m.
Proof. apply map_eq. intro i. rewrite (lookup_union (∅ : gmap string A) m i). destruct (m!!i); done. Qed.
Lemma union_empty_r_str {A} (m : gmap string A) : (m ∪ ∅) = m.
Proof. apply map_eq. intro i. rewrite (lookup_union m (∅ : gmap string A) i). destruct (m!!i); done. Qed.

(* ------------------------------------------------------------------ *)
(* Value typing facts                                                 *)
(* ------------------------------------------------------------------ *)

Lemma rtv_unr Δ v t : rtv Δ v t -> unr t -> Δ = ∅.
Proof.
  intros H. induction H; intros Hu.
  - done.
  - apply H. apply unr_FunT_inv in Hu. done.
  - apply unr_PairT_inv in Hu as [Hu1 Hu2].
    rewrite (IHrtv1 Hu1), (IHrtv2 Hu2) in H. rewrite H.
    rewrite union_empty_l_nat. done.
  - apply IHrtv. apply (unr_SumT_inv Hu).
  - exfalso. exact (unr_FunT_Lin_false Hu).
Qed.

Lemma rtv_unit_inv Δ v : rtv Δ v UnitT -> v = UnitV.
Proof. intros H. dependent destruction H. done. Qed.

Lemma rtv_fun_inv Δ v l a b :
  rtv Δ v (FunT l a b) ->
  (exists x e, v = FunV x e) \/ (exists n, v = BarrierV n).
Proof. intros H. dependent destruction H; [left; eauto | right; eauto]. Qed.

Lemma rtv_pair_inv Δ v a b :
  rtv Δ v (PairT a b) -> exists v1 v2, v = PairV v1 v2.
Proof. intros H. dependent destruction H. eauto. Qed.

Lemma rtv_sum_inv Δ v n ts :
  rtv Δ v (SumT n ts) -> exists i w, v = SumV i w.
Proof. intros H. dependent destruction H. eauto. Qed.

(* ------------------------------------------------------------------ *)
(* Embedding of the source typing into the runtime typing             *)
(* ------------------------------------------------------------------ *)

Lemma rt_disjoint_empty_l (Δ : gmap nat type) : (∅ : gmap nat type) ##ₘ Δ.
Proof. apply map_disjoint_empty_l. Qed.
Lemma rt_disjoint_empty_r (Δ : gmap nat type) : Δ ##ₘ (∅ : gmap nat type).
Proof. apply map_disjoint_empty_r. Qed.

Ltac solve_rtprem :=
  first [ eassumption
        | reflexivity
        | rewrite union_empty_l_nat; done
        | apply map_disjoint_empty_l
        | (intros ->; reflexivity) ].

Lemma typed_to_rt Γ e t : typed Γ e t -> rt Γ ∅ e t.
Proof.
  induction 1.
  - apply (rt_Var (Γ := Γ) (Δ := ∅) (x := x) (t := t)). all: solve_rtprem.
  - apply (rt_Fun (Γ := Γ) (Γ' := Γ') (Δ := ∅) (x := x) (e := e)
                  (t1 := t1) (t2 := t2) (l := l)). all: solve_rtprem.
  - apply (rt_App (Γ := Γ) (Γ1 := Γ1) (Γ2 := Γ2) (Δ := ∅) (Δ1 := ∅) (Δ2 := ∅)
                  (e1 := e1) (e2 := e2) (t1 := t1) (t2 := t2) (l := l)). all: solve_rtprem.
  - apply (rt_Unit (Γ := Γ) (Δ := ∅)). all: solve_rtprem.
  - apply (rt_Pair (Γ := Γ) (Γ1 := Γ1) (Γ2 := Γ2) (Δ := ∅) (Δ1 := ∅) (Δ2 := ∅)
                   (e1 := e1) (e2 := e2) (t1 := t1) (t2 := t2)). all: solve_rtprem.
  - apply (rt_LetPair (Γ := Γ) (Γ1 := Γ1) (Γ2 := Γ2) (Δ := ∅) (Δ1 := ∅) (Δ2 := ∅)
                      (e1 := e1) (e2 := e2) (t1 := t1) (t2 := t2) (t := t)). all: solve_rtprem.
  - apply (rt_Sum (Γ := Γ) (Δ := ∅) (n := n) (ts := ts) (i := i) (e := e)). all: solve_rtprem.
  - apply (rt_MatchSum (n := n) (Γ := Γ) (Γ1 := Γ1) (Γ2 := Γ2) (Δ := ∅) (Δ1 := ∅) (Δ2 := ∅)
                       (t := t) (ts := ts) (es := es) (e := e)). all: solve_rtprem.
  - apply (rt_Fork (Γ := Γ) (Δ := ∅) (e := e) (t1 := t1) (t2 := t2)). all: solve_rtprem.
Qed.

Lemma map_empty_of_subseteq_empty_str {A} (m : gmap string A) : m ⊆ ∅ -> m = ∅.
Proof.
  intros H. apply map_eq. intro i. destruct (m !! i) as [v|] eqn:E; [|done].
  exfalso. destruct (map_subseteq_spec m (∅ : gmap string A)) as [Hf _].
  exact (lookup_empty_Some i v (Hf H i v E)).
Qed.

Lemma map_empty_of_subseteq_empty_nat {A} (m : gmap nat A) : m ⊆ ∅ -> m = ∅.
Proof.
  intros H. apply map_eq. intro i. destruct (m !! i) as [v|] eqn:E; [|done].
  exfalso. destruct (map_subseteq_spec m (∅ : gmap nat A)) as [Hf _].
  exact (lookup_empty_Some i v (Hf H i v E)).
Qed.

Lemma env_split_empty Γ Γ1 Γ2 : env_split Γ Γ1 Γ2 -> Γ = ∅ -> Γ1 = ∅ /\ Γ2 = ∅.
Proof.
  intros Hs He. subst Γ. split.
  - apply map_empty_of_subseteq_empty_str. apply env_split_l_sub in Hs. done.
  - apply map_empty_of_subseteq_empty_str. apply env_split_r_sub in Hs. done.
Qed.

Lemma env_split_nil : env_split (∅ : env) ∅ ∅.
Proof.
  split.
  - symmetry. apply (union_empty_l_str (∅ : gmap string type)).
  - intros i t1 t2 H1 H2. exfalso. exact (lookup_empty_Some i t1 H1).
Qed.

(* ------------------------------------------------------------------ *)
(* Decomposition of evaluation contexts                               *)
(* ------------------------------------------------------------------ *)

Record ctx_typing (k : expr -> expr) (Δk Δh : gmap nat type) (s t : type) : Prop := {
  ct_disj : Δk ##ₘ Δh;
  ct_fill_any : forall Δh' e, Δk ##ₘ Δh' -> rt ∅ Δh' e s ->
                  rt ∅ (Δk ∪ Δh') (k e) t;
}.

Lemma ct_fill {k : expr -> expr} {Δk Δh : gmap nat type} {s t : type}
  (C : ctx_typing k Δk Δh s t) (e : expr) (H : rt ∅ Δh e s) :
  rt ∅ (Δk ∪ Δh) (k e) t.
Proof.
  apply (ct_fill_any C). apply (ct_disj C). exact H.
Qed.

Lemma ctx1_decomp_apply_l (v : val) e Δ t :
  rt ∅ Δ (App e (Val v)) t ->
  exists Δk Δh s, Δ = Δk ∪ Δh /\ ctx_typing (fun x => App x (Val v)) Δk Δh s t
                  /\ rt ∅ Δh e s.
Proof.
  intros H. inversion H; subst; clear H.
  destruct (env_split_empty H2 eq_refl) as [E1 E2].
  rewrite E1 in H7. rewrite E2 in H9.
  exists Δ2, Δ1, (FunT l t1 t). split.
  - apply map_union_comm. done.
  - split.
    + split.
      * apply map_disjoint_sym. done.
      * intros Δh' e' Hdisj' He'.
        assert (Hd : Δ2 ##ₘ Δh') by exact Hdisj'.
        rewrite (map_union_comm Δ2 Δh' Hd).
        eapply rt_App with (Γ1:=∅)(Γ2:=∅)(Δ:=Δh'∪Δ2)(Δ1:=Δh')(Δ2:=Δ2)
                           (e1:=e')(e2:=Val v)(t1:=t1)(t2:=t)(l:=l).
        -- apply env_split_nil. -- done. -- apply map_disjoint_sym; exact Hd. -- exact He'. -- exact H9.
    + exact H7.
Qed.

Lemma ctx1_decomp_apply_r (e1 : expr) e Δ t :
  rt ∅ Δ (App e1 e) t ->
  exists Δk Δh s, Δ = Δk ∪ Δh /\ ctx_typing (fun x => App e1 x) Δk Δh s t
                  /\ rt ∅ Δh e s.
Proof.
  intros H. inversion H; subst; clear H.
  destruct (env_split_empty H2 eq_refl) as [E1 E2]. rewrite E1 in H7. rewrite E2 in H9.
  exists Δ1, Δ2, t1. split; [done|]. split.
  - split.
    + exact H4.
    + intros Δh' e' Hdisj' He'.
      eapply rt_App with (Γ1:=∅)(Γ2:=∅)(Δ:=Δ1∪Δh')(Δ1:=Δ1)(Δ2:=Δh')
                         (e1:=e1)(e2:=e')(t1:=t1)(t2:=t)(l:=l).
      * apply env_split_nil. * done. * exact Hdisj'. * exact H7. * exact He'.
  - exact H9.
Qed.

Lemma ctx1_decomp_pair_l (e2 : expr) e Δ t :
  rt ∅ Δ (Pair e e2) t ->
  exists Δk Δh s, Δ = Δk ∪ Δh /\ ctx_typing (fun x => Pair x e2) Δk Δh s t
                  /\ rt ∅ Δh e s.
Proof.
  intros H. inversion H; subst; clear H.
  destruct (env_split_empty H2 eq_refl) as [E1 E2]. rewrite E1 in H7. rewrite E2 in H9.
  exists Δ2, Δ1, t1. split.
  - apply map_union_comm. done.
  - split.
    + split.
      * apply map_disjoint_sym. done.
      * intros Δh' e' Hdisj' He'.
        assert (Hd : Δ2 ##ₘ Δh') by exact Hdisj'.
        rewrite (map_union_comm Δ2 Δh' Hd).
        eapply rt_Pair with (Γ1:=∅)(Γ2:=∅)(Δ:=Δh'∪Δ2)(Δ1:=Δh')(Δ2:=Δ2)
                            (e1:=e')(e2:=e2)(t1:=t1)(t2:=t2).
        -- apply env_split_nil. -- done. -- apply map_disjoint_sym; exact Hd. -- exact He'. -- exact H9.
    + exact H7.
Qed.

Lemma ctx1_decomp_pair_r (e1 : expr) e Δ t :
  rt ∅ Δ (Pair e1 e) t ->
  exists Δk Δh s, Δ = Δk ∪ Δh /\ ctx_typing (fun x => Pair e1 x) Δk Δh s t
                  /\ rt ∅ Δh e s.
Proof.
  intros H. inversion H; subst; clear H.
  destruct (env_split_empty H2 eq_refl) as [E1 E2]. rewrite E1 in H7. rewrite E2 in H9.
  exists Δ1, Δ2, t2. split; [done|]. split.
  - split.
    + exact H4.
    + intros Δh' e' Hdisj' He'.
      eapply rt_Pair with (Γ1:=∅)(Γ2:=∅)(Δ:=Δ1∪Δh')(Δ1:=Δ1)(Δ2:=Δh')
                          (e1:=e1)(e2:=e')(t1:=t1)(t2:=t2).
      * apply env_split_nil. * done. * exact Hdisj'. * exact H7. * exact He'.
  - exact H9.
Qed.

Lemma ctx1_decomp_letpair (e2 : expr) e Δ t :
  rt ∅ Δ (LetPair e e2) t ->
  exists Δk Δh s, Δ = Δk ∪ Δh /\ ctx_typing (fun x => LetPair x e2) Δk Δh s t
                  /\ rt ∅ Δh e s.
Proof.
  intros H. inversion H; subst; clear H.
  destruct (env_split_empty H2 eq_refl) as [E1 E2]. rewrite E1 in H7. rewrite E2 in H9.
  exists Δ2, Δ1, (PairT t1 t2). split.
  - apply map_union_comm. done.
  - split.
    + split.
      * apply map_disjoint_sym. done.
      * intros Δh' e' Hdisj' He'.
        assert (Hd : Δ2 ##ₘ Δh') by exact Hdisj'.
        rewrite (map_union_comm Δ2 Δh' Hd).
        eapply rt_LetPair with (Γ1:=∅)(Γ2:=∅)(Δ:=Δh'∪Δ2)(Δ1:=Δh')(Δ2:=Δ2)
                               (e1:=e')(e2:=e2)(t1:=t1)(t2:=t2)(t:=t).
        -- apply env_split_nil. -- done. -- apply map_disjoint_sym; exact Hd. -- exact He'. -- exact H9.
    + exact H7.
Qed.

Lemma ctx1_decomp_sum (i : nat) e Δ t :
  rt ∅ Δ (Sum i e) t ->
  exists Δk Δh s, Δ = Δk ∪ Δh /\ ctx_typing (fun x => Sum i x) Δk Δh s t
                  /\ rt ∅ Δh e s.
Proof.
  intros H. dependent destruction H.
  exists (∅ : gmap nat type), Δ, (ts i0). split.
  - symmetry. apply union_empty_l_nat.
  - split.
    + split.
      * apply map_disjoint_empty_l.
      * intros Δh' e' Hdisj' He'. rewrite union_empty_l_nat.
        apply (rt_Sum (Γ:=∅)(Δ:=Δh')(n:=n)(ts:=ts)(i:=i0)(e:=e')). exact He'.
    + done.
Qed.

Lemma ctx1_decomp_matchsum (n : nat) (es : fin n -> expr) e Δ t :
  rt ∅ Δ (MatchSum n e es) t ->
  exists Δk Δh s, Δ = Δk ∪ Δh /\ ctx_typing (fun x => MatchSum n x es) Δk Δh s t
                  /\ rt ∅ Δh e s.
Proof.
  intros H. dependent destruction H.
  destruct (env_split_empty H eq_refl) as [E1 E2]. rewrite E1 in H3. rewrite E2 in H4.
  exists Δ2, Δ1, (SumT n ts). split.
  - apply map_union_comm. done.
  - split.
    + split.
      * apply map_disjoint_sym. done.
      * intros Δh' e' Hdisj' He'.
        assert (Hd : Δ2 ##ₘ Δh') by exact Hdisj'.
        rewrite (map_union_comm Δ2 Δh' Hd).
        eapply rt_MatchSum with (n:=n)(Γ1:=∅)(Γ2:=∅)(Δ:=Δh'∪Δ2)(Δ1:=Δh')(Δ2:=Δ2)
                                (t:=t)(ts:=ts)(es:=es)(e:=e').
        -- apply env_split_nil. -- done. -- apply map_disjoint_sym; exact Hd.
        -- intros _; apply env_unr_empty. -- exact He'. -- exact H4.
    + exact H3.
Qed.

Lemma ctx1_decomp_fork e Δ t :
  rt ∅ Δ (Fork e) t ->
  exists Δk Δh s, Δ = Δk ∪ Δh /\ ctx_typing (fun x => Fork x) Δk Δh s t
                  /\ rt ∅ Δh e s.
Proof.
  intros H. inversion H; subst; clear H.
  exists (∅ : gmap nat type), Δ, (FunT Lin (FunT Lin t2 t1) UnitT). split.
  - symmetry. apply union_empty_l_nat.
  - split.
    + split.
      * apply map_disjoint_empty_l.
      * intros Δh' e' Hdisj' He'. rewrite union_empty_l_nat.
        apply (rt_Fork (Γ:=∅)(Δ:=Δh')(e:=e')(t1:=t1)(t2:=t2)). exact He'.
    + done.
Qed.

Lemma ctx1_decomp (k : expr -> expr) : ctx1 k ->
  forall e Δ t, rt ∅ Δ (k e) t ->
  exists Δk Δh s, Δ = Δk ∪ Δh /\ ctx_typing k Δk Δh s t /\ rt ∅ Δh e s.
Proof.
  intros Hk. destruct Hk; intros ex Δ t H; simpl in H.
  - apply ctx1_decomp_apply_l in H. exact H.
  - apply ctx1_decomp_apply_r in H. exact H.
  - apply ctx1_decomp_pair_l in H. exact H.
  - apply ctx1_decomp_pair_r in H. exact H.
  - apply ctx1_decomp_letpair in H. exact H.
  - apply ctx1_decomp_sum in H. exact H.
  - apply ctx1_decomp_matchsum in H. exact H.
  - apply ctx1_decomp_fork in H. exact H.
Qed.

Lemma ctx_decomp (k : expr -> expr) : ctx k ->
  forall e Δ t, rt ∅ Δ (k e) t ->
  exists Δk Δh s, Δ = Δk ∪ Δh /\ ctx_typing k Δk Δh s t /\ rt ∅ Δh e s.
Proof.
  intros Hk. induction Hk; intros e0 Δ0 t0 Hex.
  - exists (∅ : gmap nat type), Δ0, t0. split.
    + symmetry. apply union_empty_l_nat.
    + split.
      * split.
        -- apply map_disjoint_empty_l.
        -- intros Δh' e' Hdisj' He'. rewrite union_empty_l_nat. exact He'.
      * exact Hex.
  - change (rt ∅ Δ0 (k1 (k2 e0)) t0) in Hex.
    destruct (ctx1_decomp (k := k1) H Hex)
      as (Δk1 & Δh1 & s1 & Heq1 & Hct1 & Hh1).
    destruct (IHHk e0 Δh1 s1 Hh1)
      as (Δk2 & Δh2 & s2 & Heq2 & Hct2 & Hh2).
    exists (Δk1 ∪ Δk2), Δh2, s2. split.
    + rewrite Heq1, Heq2. rewrite map_union_assoc. done.
    + split.
      * split.
        -- apply map_disjoint_union_l. split.
           ++ destruct (map_disjoint_union_r Δk1 Δk2 Δh2) as [Hf _].
              assert (Hd : Δk1 ##ₘ (Δk2 ∪ Δh2)) by (rewrite <- Heq2; exact (ct_disj Hct1)).
              destruct (Hf Hd) as [_ Hr]. exact Hr.
           ++ exact (ct_disj Hct2).
        -- intros Δh' e' Hdisj' He'.
           destruct (map_disjoint_union_l Δk1 Δk2 Δh') as [Hf _].
           destruct (Hf Hdisj') as [Hd1 Hd2].
           assert (Hd12 : Δk1 ##ₘ Δk2).
           { destruct (map_disjoint_union_r Δk1 Δk2 Δh2) as [Hg0 _].
             assert (Hdd : Δk1 ##ₘ (Δk2 ∪ Δh2)) by (rewrite <- Heq2; exact (ct_disj Hct1)).
             destruct (Hg0 Hdd) as [Hl _]. exact Hl. }
           assert (Hd1' : Δk1 ##ₘ (Δk2 ∪ Δh')).
           { destruct (map_disjoint_union_r Δk1 Δk2 Δh') as [_ Hg]. apply Hg. split; [exact Hd12|exact Hd1]. }
           pose proof (ct_fill_any Hct2 Hd2 He') as Hk2.
           pose proof (ct_fill_any Hct1 Hd1' Hk2) as Hk1.
           rewrite <- map_union_assoc. exact Hk1.
      * exact Hh2.
Qed.

(* ------------------------------------------------------------------ *)
(* Map plumbing for the substitution lemma                            *)
(* ------------------------------------------------------------------ *)



Lemma delete_union_l_str {A} (m1 m2 : gmap string A) x (H : m2 !! x = None) :
  delete x (m1 ∪ m2) = delete x m1 ∪ m2.
Proof.
  apply map_eq. intro i. rewrite (lookup_delete (m1 ∪ m2) x i).
  destruct (decide (x = i)) as [Heq|Hne].
  - subst i.
    rewrite (lookup_union (delete x m1) m2 x), (lookup_delete_eq m1 x), H. simpl. done.
  - rewrite (lookup_union m1 m2 i), (lookup_union (delete x m1) m2 i).
    rewrite (lookup_delete_ne m1 x i) by done. done.
Qed.

Lemma delete_union_r_str {A} (m1 m2 : gmap string A) x (H : m1 !! x = None) :
  delete x (m1 ∪ m2) = m1 ∪ delete x m2.
Proof.
  apply map_eq. intro i. rewrite (lookup_delete (m1 ∪ m2) x i).
  destruct (decide (x = i)) as [Heq|Hne].
  - subst i.
    rewrite (lookup_union m1 (delete x m2) x), (lookup_delete_eq m2 x), H. simpl. done.
  - rewrite (lookup_union m1 m2 i), (lookup_union m1 (delete x m2) i).
    rewrite (lookup_delete_ne m2 x i) by done. done.
Qed.

Lemma disj_mono_l Γ1 Γ1' Γ2 : disj Γ1 Γ2 -> Γ1' ⊆ Γ1 -> disj Γ1' Γ2.
Proof.
  intros Hd Hsub i t1 t2 H1 H2. apply (Hd i t1 t2).
  - destruct (map_subseteq_spec Γ1' Γ1) as [Hf _]. exact (Hf Hsub i t1 H1).
  - done.
Qed.

Lemma disj_mono_r Γ1 Γ2 Γ2' : disj Γ1 Γ2 -> Γ2' ⊆ Γ2 -> disj Γ1 Γ2'.
Proof.
  intros Hd Hsub i t1 t2 H1 H2. apply (Hd i t1 t2).
  - done.
  - destruct (map_subseteq_spec Γ2' Γ2) as [Hf _]. exact (Hf Hsub i t2 H2).
Qed.

Lemma notin_of_lookup_none (Γ : env) x : Γ !! x = None -> x ∉ dom Γ.
Proof.
  intros H. apply (proj2 (not_elem_of_dom Γ x)). exact H.
Qed.

Lemma lookup_none_of_notin (Γ : env) x : x ∉ dom Γ -> Γ !! x = None.
Proof.
  intros H. destruct (Γ !! x) as [v|] eqn:E; [|done].
  exfalso. apply H. apply elem_of_dom. eexists. exact E.
Qed.

Lemma env_unr_delete Γ x : env_unr Γ -> env_unr (delete x Γ).
Proof. intros H. apply (env_unr_subset H). apply delete_subseteq. Qed.

Lemma delete_union_distr_str {A} (m1 m2 : gmap string A) x :
  delete x (m1 ∪ m2) = delete x m1 ∪ delete x m2.
Proof.
  apply map_eq. intro i. rewrite (lookup_delete (m1 ∪ m2) x i).
  destruct (decide (x = i)) as [Heq|Hne].
  - subst i.
    rewrite (lookup_union (delete x m1) (delete x m2) x).
    rewrite (lookup_delete_eq m1 x), (lookup_delete_eq m2 x). done.
  - rewrite (lookup_union m1 m2 i), (lookup_union (delete x m1) (delete x m2) i).
    rewrite (lookup_delete_ne m1 x i) by done. rewrite (lookup_delete_ne m2 x i) by done.
    done.
Qed.

Lemma disj_delete_l Γ1 Γ2 x : disj Γ1 Γ2 -> disj (delete x Γ1) Γ2.
Proof.
  intros Hd i t1 t2 H1 H2. apply (Hd i t1 t2).
  - destruct (map_subseteq_spec (delete x Γ1) Γ1) as [Hf _].
    exact (Hf (delete_subseteq Γ1 x) i t1 H1).
  - done.
Qed.

Lemma disj_delete_r Γ1 Γ2 x : disj Γ1 Γ2 -> disj Γ1 (delete x Γ2).
Proof.
  intros Hd i t1 t2 H1 H2. apply (Hd i t1 t2).
  - done.
  - destruct (map_subseteq_spec (delete x Γ2) Γ2) as [Hf _].
    exact (Hf (delete_subseteq Γ2 x) i t2 H2).
Qed.

Lemma disj_delete Γ1 Γ2 x : disj Γ1 Γ2 -> disj (delete x Γ1) (delete x Γ2).
Proof. intros Hd. apply disj_delete_r. apply disj_delete_l. done. Qed.

Lemma env_split_ambient Γ Γ1 Γ2 x s :
  env_split (<[x:=s]>Γ) Γ1 Γ2 -> x ∉ dom Γ ->
  (Γ2 !! x = None /\ env_split Γ (delete x Γ1) Γ2) \/
  (Γ1 !! x = None /\ env_split Γ Γ1 (delete x Γ2)) \/
  (Γ1 !! x = Some s /\ Γ2 !! x = Some s /\ unr s /\
   env_split Γ (delete x Γ1) (delete x Γ2)).
Proof.
  intros [Heq Hd] Hx.
  assert (Hdel : delete x (<[x:=s]>Γ) = Γ).
  { apply delete_insert_id. apply lookup_none_of_notin. exact Hx. }
  destruct (Γ1 !! x) as [a|] eqn:E1; destruct (Γ2 !! x) as [b|] eqn:E2.
  - (* both Some *)
    assert (Ha : a = s).
    { assert (Hl : (<[x:=s]>Γ) !! x = Some s) by (rewrite (lookup_insert_eq Γ x s); done).
      rewrite Heq in Hl. rewrite (lookup_union_Some_l Γ1 Γ2 x a E1) in Hl.
      injection Hl as Hl. done. }
    subst a. destruct (Hd x s b E1 E2) as [Hb Hu]. subst b.
    right. right. split.
    { reflexivity. }
    split.
    { reflexivity. }
    split.
    { exact Hu. }
    split.
    { rewrite <- Hdel. rewrite Heq. apply delete_union_distr_str. }
    { intros i t1 t2 H1 H2. apply (Hd i t1 t2).
      - destruct (map_subseteq_spec (delete x Γ1) Γ1) as [Hf _].
        exact (Hf (delete_subseteq Γ1 x) i t1 H1).
      - destruct (map_subseteq_spec (delete x Γ2) Γ2) as [Hf _].
        exact (Hf (delete_subseteq Γ2 x) i t2 H2). }
  - (* Γ1 Some, Γ2 None *)
    left. split.
    { reflexivity. }
    split.
    { rewrite <- Hdel. rewrite Heq. apply delete_union_l_str. exact E2. }
    { intros i t1 t2 H1 H2. apply (Hd i t1 t2).
      - destruct (map_subseteq_spec (delete x Γ1) Γ1) as [Hf _].
        exact (Hf (delete_subseteq Γ1 x) i t1 H1).
      - exact H2. }
  - (* Γ1 None, Γ2 Some *)
    right. left. split.
    { reflexivity. }
    split.
    { rewrite <- Hdel. rewrite Heq. apply delete_union_r_str. exact E1. }
    { intros i t1 t2 H1 H2. apply (Hd i t1 t2).
      - exact H1.
      - destruct (map_subseteq_spec (delete x Γ2) Γ2) as [Hf _].
        exact (Hf (delete_subseteq Γ2 x) i t2 H2). }
  - (* both None: impossible *)
    exfalso.
    assert (Hnone : (Γ1 ∪ Γ2) !! x = None).
    { rewrite (lookup_union_r Γ1 Γ2 x E1). exact E2. }
    rewrite <- Heq in Hnone. rewrite (lookup_insert_eq Γ x s) in Hnone. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Substitution lemma                                                 *)
(* ------------------------------------------------------------------ *)

Lemma notin_dom_of_sub (Γ Γ' : env) (z : string) : Γ ⊆ Γ' -> z ∉ dom Γ' -> z ∉ dom Γ.
Proof.
  intros Hsub Hz Hzin. apply Hz.
  apply elem_of_dom in Hzin. destruct Hzin as (v & Hv).
  apply elem_of_dom. exists v.
  destruct (map_subseteq_spec Γ Γ') as [Hf _]. exact (Hf Hsub z v Hv).
Qed.

Lemma notin_dom_split (Γ Γ1 Γ2 : env) (z : string) :
  env_split Γ Γ1 Γ2 -> z ∉ dom Γ -> z ∉ dom Γ1 /\ z ∉ dom Γ2.
Proof.
  intros Hs Hz. split.
  - apply (notin_dom_of_sub (env_split_l_sub Hs) Hz).
  - apply (notin_dom_of_sub (env_split_r_sub Hs) Hz).
Qed.

Lemma notin_delete_self_str (m : gmap string type) x : x ∉ dom (delete x m).
Proof.
  intros Hc. apply elem_of_dom in Hc. destruct Hc as (v & Hv).
  rewrite (lookup_delete_eq m x) in Hv. discriminate.
Qed.

Lemma delta_disj_l (Δz Δ1 Δ2 : gmap nat type) : Δz ##ₘ (Δ1 ∪ Δ2) -> Δz ##ₘ Δ1.
Proof.
  intros H. destruct (map_disjoint_union_r Δz Δ1 Δ2) as [Hf _].
  destruct (Hf H) as [Hl _]. exact Hl.
Qed.

Lemma delta_disj_r (Δz Δ1 Δ2 : gmap nat type) : Δz ##ₘ (Δ1 ∪ Δ2) -> Δz ##ₘ Δ2.
Proof.
  intros H. destruct (map_disjoint_union_r Δz Δ1 Δ2) as [Hf _].
  destruct (Hf H) as [_ Hr]. exact Hr.
Qed.

Lemma delta_disj_union (Δ1 Δz Δ2 : gmap nat type) :
  Δ1 ##ₘ Δ2 -> Δz ##ₘ Δ2 -> (Δ1 ∪ Δz) ##ₘ Δ2.
Proof.
  intros H1 H2. apply map_disjoint_union_l. split; done.
Qed.

Lemma union_rot (Δ1 Δ2 Δz : gmap nat type) : Δ2 ##ₘ Δz ->
  (Δ1 ∪ Δ2) ∪ Δz = (Δ1 ∪ Δz) ∪ Δ2.
Proof.
  intros H. rewrite <- map_union_assoc. rewrite (map_union_comm Δ2 Δz H).
  rewrite map_union_assoc. done.
Qed.

Lemma rt_subst_absent (e : expr) (t : type) (Γ : env) (Δ : gmap nat type) :
  rt Γ Δ e t -> forall z az, z ∉ dom Γ -> subst z az e = e.
Proof.
  intros H. induction H; intros z az Hz.
  - simpl. destruct (decide (z = x)) as [Heq|Hne].
    + subst z. exfalso. apply Hz. destruct H as (Γ0 & Heq0 & Hunr).
      apply elem_of_dom. rewrite Heq0. rewrite (lookup_insert_eq Γ0 x t). eauto.
    + done.
  - simpl. destruct (decide (z = x)) as [Heq|Hne].
    + done.
    + destruct H as (Hbeq & Hside).
      assert (Hz' : z ∉ dom (<[x:=t1]>Γ)).
      { intros Hc. apply Hz. apply elem_of_dom in Hc. destruct Hc as (v & Hv).
        apply elem_of_dom. exists v.
        rewrite (lookup_insert Γ x z t1) in Hv.
        destruct (decide (x = z)) as [Hxz|Hnez].
        - exfalso. apply Hne. symmetry. exact Hxz.
        - exact Hv. }
      f_equal. apply IHrt. rewrite Hbeq. exact Hz'.
  - simpl. destruct (notin_dom_split H Hz) as [Hz1 Hz2].
    rewrite (IHrt1 z az Hz1), (IHrt2 z az Hz2). done.
  - simpl. done.
  - simpl. destruct (notin_dom_split H Hz) as [Hz1 Hz2].
    rewrite (IHrt1 z az Hz1), (IHrt2 z az Hz2). done.
  - simpl. destruct (notin_dom_split H Hz) as [Hz1 Hz2].
    rewrite (IHrt1 z az Hz1), (IHrt2 z az Hz2). done.
  - simpl. rewrite IHrt. done. exact Hz.
  - simpl. destruct (notin_dom_split H Hz) as [Hz1 Hz2].
    rewrite (IHrt z az Hz1). f_equal. apply functional_extensionality. intro i.
    exact (H5 i z az Hz2).
  - simpl. rewrite IHrt. done. exact Hz.
  - simpl. done.
Qed.

Lemma ins_comm_str {A} (m : gmap string A) x y a b :
  x <> y -> (<[x:=a]>(<[y:=b]>m : gmap string A) : gmap string A) =
            (<[y:=b]>(<[x:=a]>m : gmap string A) : gmap string A).
Proof.
  intros Hne. apply map_eq. intro i.
  rewrite (lookup_insert (<[y:=b]>m) x i a).
  rewrite (lookup_insert m y i b).
  rewrite (lookup_insert (<[x:=a]>m) y i b).
  rewrite (lookup_insert m x i a).
  repeat case_decide; subst; done.
Qed.

Lemma insert_insert_same_str {A} (m : gmap string A) x a b :
  (<[x:=a]>(<[x:=b]>m) : gmap string A) = <[x:=a]>m.
Proof.
  apply map_eq. intro i.
  rewrite (lookup_insert (<[x:=b]>m) x i a).
  rewrite (lookup_insert m x i b).
  rewrite (lookup_insert m x i a).
  repeat case_decide; done.
Qed.

Lemma ins_ins_same_type (m : gmap string type) x a b :
  (<[x:=a]>(<[x:=b]>m) : gmap string type) = <[x:=a]>m.
Proof.
  apply map_eq. intro i.
  rewrite (lookup_insert (<[x:=b]>m) x i a).
  rewrite (lookup_insert m x i b).
  rewrite (lookup_insert m x i a).
  repeat case_decide; done.
Qed.

Lemma ins_comm_type (m : gmap string type) x y a b :
  x <> y -> (<[x:=a]>(<[y:=b]>m) : gmap string type) =
            (<[y:=b]>(<[x:=a]>m) : gmap string type).
Proof.
  intros Hne. apply map_eq. intro i.
  rewrite (lookup_insert (<[y:=b]>m) x i a).
  rewrite (lookup_insert m y i b).
  rewrite (lookup_insert (<[x:=a]>m) y i b).
  rewrite (lookup_insert m x i a).
  repeat case_decide; subst; done.
Qed.

Lemma del_ins_self (m : gmap string type) x s (H : m !! x = Some s) :
  <[x:=s]>(delete x m) = m.
Proof. apply insert_delete_id. exact H. Qed.

Lemma del_ins_none (m : gmap string type) x s (H : m !! x = None) :
  delete x (<[x:=s]>m) = m.
Proof. apply delete_insert_id. exact H. Qed.

Lemma del_ins_ne (m : gmap string type) x y s (H : x <> y) :
  delete x (<[y:=s]>m) = <[y:=s]>(delete x m).
Proof. apply delete_insert_ne. exact H. Qed.



Lemma rt_subst_aux (e : expr) (t : type) (Γ' : env) (Δ : gmap nat type) :
  rt Γ' Δ e t ->
  forall (z : string) (sz : type) (Γs : env) (az : val) (Δz : gmap nat type),
    Γ' = <[z := sz]> Γs ->
    z ∉ dom Γs ->
    Δz ##ₘ Δ ->
    rtv Δz az sz ->
    rt Γs (Δ ∪ Δz) (subst z az e) t.
Proof.
  intros H. induction H; intros z sz Γs az Δz HΓs Hx Hdisj Ha.
  - (* Var *)
    subst Δ. simpl.
    destruct (decide (z = x)) as [Heq|Hne].
    + subst x. rewrite union_empty_l_nat.
      apply rt_Val.
      * (* env_unr Γs *)
        destruct H as (Γ0 & Heq0 & Hunr).
        destruct (map_subseteq_spec Γs Γ0) as [_ Hg].
        apply (env_unr_subset Hunr). apply Hg.
        intros i v Hi. destruct (decide (z = i)) as [Heq2|Hne2].
        -- subst z. exfalso. apply Hx. apply elem_of_dom. eexists. exact Hi.
        -- assert (Hi' : (<[z:=sz]>Γs) !! i = Some v).
           { rewrite (lookup_insert_ne Γs z i sz Hne2). exact Hi. }
           rewrite <- HΓs in Hi'. rewrite Heq0 in Hi'.
           rewrite (lookup_insert_ne Γ0 z i t Hne2) in Hi'. exact Hi'.
      * (* value type equality *)
        assert (Hts : t = sz).
        { destruct H as (Γ0 & Heq0 & Hunr).
          assert (Heq1 : <[z:=t]>Γ0 = <[z:=sz]>Γs).
          { rewrite <- Heq0, <- HΓs. done. }
          assert (Hl : (<[z:=sz]>Γs) !! z = Some sz) by (rewrite (lookup_insert_eq Γs z sz); done).
          rewrite <- Heq1 in Hl. rewrite (lookup_insert_eq Γ0 z t) in Hl.
          injection Hl as Hl. exact Hl. }
        rewrite Hts. exact Ha.
    + (* z <> x *)
      assert (HunrS : unr sz).
      { destruct H as (Γ0 & Heq0 & Hunr).
        assert (Heq1 : <[x:=t]>Γ0 = <[z:=sz]>Γs).
        { rewrite <- Heq0, <- HΓs. done. }
        assert (Hl : (<[z:=sz]>Γs) !! z = Some sz) by (rewrite (lookup_insert_eq Γs z sz); done).
        rewrite <- Heq1 in Hl. rewrite (lookup_insert_ne Γ0 x z t) in Hl by done.
        exact (Hunr z sz Hl). }
      assert (Hae : Δz = ∅) by (apply (rtv_unr Ha HunrS)).
      rewrite union_empty_l_nat, Hae.
      apply rt_Var.
      * destruct H as (Γ0 & Heq0 & Hunr).
        exists (delete z Γ0). split.
        -- assert (Hdel : delete z (<[x:=t]>Γ0) = <[x:=t]>(delete z Γ0)).
           { apply del_ins_ne. exact Hne. }
           rewrite <- Hdel.
           assert (Heq1 : <[x:=t]>Γ0 = <[z:=sz]>Γs) by (rewrite <- Heq0, <- HΓs; done).
           rewrite Heq1.
           symmetry. apply del_ins_none. apply lookup_none_of_notin. exact Hx.
        -- apply env_unr_delete. exact Hunr.
      * done.
  - (* Fun *)
    simpl. destruct (decide (z = x)) as [Heq|Hne].
    + (* binder shadows z: substitution stops *)
      subst z.
      assert (HunrS : unr sz).
      { assert (Hi : Γ !! x = Some sz).
        { rewrite HΓs. rewrite (lookup_insert_eq Γs x sz). done. }
        destruct H as (Hbeq & Hside). exact (Hside sz Hi). }
      assert (Hae : Δz = ∅) by (apply (rtv_unr Ha HunrS)).
      apply (rt_Fun (Γ:=Γs) (Γ':=<[x:=t1]>Γs) (Δ:=Δ∪Δz) (x:=x) (e:=e)
                    (t1:=t1) (t2:=t2) (l:=l)).
      * split.
        -- done.
        -- intros t' Ht. exfalso. apply Hx. apply elem_of_dom. eexists. exact Ht.
      * intros Hl. destruct H as (Hbind & Hside).
        apply (env_unr_insert (Γ:=Γs) (x:=x) (t:=sz)).
        -- exact Hx.
        -- rewrite <- HΓs. exact (H0 Hl).
      * intros Hl. rewrite (H1 Hl), Hae, union_empty_l_nat. done.
      * destruct H as (Hbeq & Hside).
        assert (H2' : rt (<[x:=t1]>(<[x:=sz]>Γs)) Δ e t2).
        { rewrite <- HΓs, <- Hbeq. exact H2. }
        rewrite Hae, union_empty_r_nat.
        replace (<[x:=t1]>Γs) with (<[x:=t1]>(<[x:=sz]>Γs)).
        { exact H2'. }
        { exact (@ins_ins_same_type Γs x t1 sz). }
    + (* binder distinct from z *)
      assert (HΓ' : Γ' = <[z:=sz]>(<[x:=t1]>Γs)).
      { destruct H as (Hbind & Hside). rewrite Hbind.
        rewrite HΓs.
        exact (@ins_comm_type Γs x z t1 sz (fun Hc => Hne (eq_sym Hc))). }
      assert (Hx' : z ∉ dom (<[x:=t1]>Γs)).
      { intros Hc. apply Hx. apply elem_of_dom in Hc. destruct Hc as (v & Hc).
        apply elem_of_dom. exists v.
        rewrite (lookup_insert_ne Γs x z t1 (fun Hc' => Hne (eq_sym Hc'))) in Hc.
        exact Hc. }
      assert (Hbody := IHrt z sz (<[x:=t1]>Γs) az Δz HΓ' Hx' Hdisj Ha).
      apply (rt_Fun (Γ:=Γs) (Γ':=<[x:=t1]>Γs) (Δ:=Δ∪Δz) (x:=x) (e:=subst z az e)
                    (t1:=t1) (t2:=t2) (l:=l)).
      * split.
        -- done.
        -- intros t' Ht. destruct H as (Hbind & Hside).
           assert (Hi : Γ !! x = Some t').
           { rewrite HΓs. rewrite (lookup_insert_ne Γs z x sz) by done. exact Ht. }
           exact (Hside t' Hi).
      * intros Hl. destruct H as (Hbind & Hside).
        apply (env_unr_insert (Γ:=Γs) (x:=z) (t:=sz)).
        -- exact Hx.
        -- rewrite <- HΓs. exact (H0 Hl).
      * intros Hl. rewrite (H1 Hl).
        assert (HunrSz : unr sz).
        { destruct H as (Hbind & Hside).
          assert (Hi : Γ !! z = Some sz) by (rewrite HΓs; rewrite (lookup_insert_eq Γs z sz); done).
          exact ((H0 Hl) z sz Hi). }
        assert (Hae : Δz = ∅) by (apply (rtv_unr Ha HunrSz)).
        rewrite Hae, union_empty_l_nat. done.
      * exact Hbody.
  - (* App *)
    simpl.
    assert (Hsplt : env_split (<[z:=sz]>Γs) Γ1 Γ2) by (rewrite <- HΓs; exact H).
    destruct (env_split_ambient Hsplt Hx)
      as [ (Hz2 & Hs') | [ (Hz1 & Hs') | (Hz1 & Hz2 & Hunr & Hs') ] ].
    + (* z only occurs in Γ1 *)
      assert (Heq : Γ = Γ1 ∪ Γ2) by (destruct H; done).
      assert (E1z : Γ1 !! z = Some sz).
      { assert (Hl : Γ !! z = Some sz) by (rewrite HΓs; rewrite (lookup_insert_eq Γs z sz); done).
        rewrite Heq in Hl. rewrite (lookup_union_l Γ1 Γ2 z Hz2) in Hl. exact Hl. }
      assert (Hins1 : Γ1 = <[z:=sz]>(delete z Γ1)) by (symmetry; apply del_ins_self; exact E1z).
      assert (Hd1 : Δz ##ₘ Δ1) by (apply (delta_disj_l (Δ2 := Δ2)); rewrite <- H0; exact Hdisj).
      assert (Hd2 : Δz ##ₘ Δ2) by (apply (delta_disj_r (Δ1 := Δ1)); rewrite <- H0; exact Hdisj).
      assert (Ht1 := IHrt1 z sz (delete z Γ1) az Δz Hins1
                       (@notin_delete_self_str Γ1 z) Hd1 Ha).
      assert (Ht2 : rt Γ2 Δ2 (subst z az e2) t1).
      { rewrite (@rt_subst_absent e2 t1 Γ2 Δ2 H3 z az (@notin_of_lookup_none Γ2 z Hz2)). exact H3. }
      rewrite H0.
      eapply rt_App with (Γ:=Γs) (Γ1:=delete z Γ1) (Γ2:=Γ2) (Δ:=(Δ1∪Δ2)∪Δz)
                         (Δ1:=Δ1∪Δz) (Δ2:=Δ2) (e1:=subst z az e1) (e2:=subst z az e2)
                         (t1:=t1) (t2:=t2) (l:=l).
      * exact Hs'.
      * apply union_rot. apply map_disjoint_sym. exact Hd2.
      * apply delta_disj_union; [exact H1|exact Hd2].
      * exact Ht1.
      * exact Ht2.
    + (* z only occurs in Γ2 *)
      assert (Heq : Γ = Γ1 ∪ Γ2) by (destruct H; done).
      assert (E2z : Γ2 !! z = Some sz).
      { assert (Hl : Γ !! z = Some sz) by (rewrite HΓs; rewrite (lookup_insert_eq Γs z sz); done).
        rewrite Heq in Hl. rewrite (lookup_union_r Γ1 Γ2 z Hz1) in Hl. exact Hl. }
      assert (Hins2 : Γ2 = <[z:=sz]>(delete z Γ2)) by (symmetry; apply del_ins_self; exact E2z).
      assert (Hd1 : Δz ##ₘ Δ1) by (apply (delta_disj_l (Δ2 := Δ2)); rewrite <- H0; exact Hdisj).
      assert (Hd2 : Δz ##ₘ Δ2) by (apply (delta_disj_r (Δ1 := Δ1)); rewrite <- H0; exact Hdisj).
      assert (Ht2 := IHrt2 z sz (delete z Γ2) az Δz Hins2
                       (@notin_delete_self_str Γ2 z) Hd2 Ha).
      assert (Ht1 : rt Γ1 Δ1 (subst z az e1) (FunT l t1 t2)).
      { rewrite (@rt_subst_absent e1 (FunT l t1 t2) Γ1 Δ1 H2 z az (@notin_of_lookup_none Γ1 z Hz1)). exact H2. }
      rewrite H0.
      eapply rt_App with (Γ:=Γs) (Γ1:=Γ1) (Γ2:=delete z Γ2) (Δ:=(Δ1∪Δ2)∪Δz)
                         (Δ1:=Δ1) (Δ2:=Δ2∪Δz) (e1:=subst z az e1) (e2:=subst z az e2)
                         (t1:=t1) (t2:=t2) (l:=l).
      * exact Hs'.
      * rewrite <- map_union_assoc. done.
      * apply map_disjoint_union_r. split; [exact H1|apply map_disjoint_sym; exact Hd1].
      * exact Ht1.
      * exact Ht2.
    + (* z occurs in both *)
      assert (Hae : Δz = ∅) by (apply (rtv_unr Ha Hunr)).
      assert (E1z : Γ1 !! z = Some sz) by exact Hz1.
      assert (E2z : Γ2 !! z = Some sz) by exact Hz2.
      assert (Hins1 : Γ1 = <[z:=sz]>(delete z Γ1)) by (symmetry; apply del_ins_self; exact E1z).
      assert (Hins2 : Γ2 = <[z:=sz]>(delete z Γ2)) by (symmetry; apply del_ins_self; exact E2z).
      assert (Hd1 : Δz ##ₘ Δ1) by (apply (delta_disj_l (Δ2 := Δ2)); rewrite <- H0; exact Hdisj).
      assert (Hd2 : Δz ##ₘ Δ2) by (apply (delta_disj_r (Δ1 := Δ1)); rewrite <- H0; exact Hdisj).
      assert (Ht1 := IHrt1 z sz (delete z Γ1) az Δz Hins1
                       (@notin_delete_self_str Γ1 z) Hd1 Ha).
      assert (Ht2 := IHrt2 z sz (delete z Γ2) az Δz Hins2
                       (@notin_delete_self_str Γ2 z) Hd2 Ha).
      rewrite Hae, union_empty_r_nat in *.
      eapply rt_App with (Γ:=Γs) (Γ1:=delete z Γ1) (Γ2:=delete z Γ2) (Δ:=Δ)
                         (Δ1:=Δ1) (Δ2:=Δ2) (e1:=subst z az e1) (e2:=subst z az e2)
                         (t1:=t1) (t2:=t2) (l:=l).
      * exact Hs'.
      * exact H0.
      * exact H1.
      * exact Ht1.
      * exact Ht2.

  - (* Unit *)
    subst Δ. simpl. rewrite union_empty_l_nat.
    assert (HunrSz : unr sz).
    { assert (Hi : Γ !! z = Some sz) by (rewrite HΓs; rewrite (lookup_insert_eq Γs z sz); done).
      exact (H z sz Hi). }
    assert (Hae : Δz = ∅) by (apply (rtv_unr Ha HunrSz)).
    rewrite Hae.
    apply rt_Unit.
    + apply (env_unr_insert (Γ:=Γs) (x:=z) (t:=sz)).
      * exact Hx.
      * rewrite <- HΓs. exact H.
    + done.
  - (* Pair *)
    simpl.
    assert (Hsplt : env_split (<[z:=sz]>Γs) Γ1 Γ2) by (rewrite <- HΓs; exact H).
    destruct (env_split_ambient Hsplt Hx)
      as [ (Hz2 & Hs') | [ (Hz1 & Hs') | (Hz1 & Hz2 & Hunr & Hs') ] ].
    + assert (Heq : Γ = Γ1 ∪ Γ2) by (destruct H; done).
      assert (E1z : Γ1 !! z = Some sz).
      { assert (Hl : Γ !! z = Some sz) by (rewrite HΓs; rewrite (lookup_insert_eq Γs z sz); done).
        rewrite Heq in Hl. rewrite (lookup_union_l Γ1 Γ2 z Hz2) in Hl. exact Hl. }
      assert (Hins1 : Γ1 = <[z:=sz]>(delete z Γ1)) by (symmetry; apply del_ins_self; exact E1z).
      assert (Hd1 : Δz ##ₘ Δ1) by (apply (delta_disj_l (Δ2 := Δ2)); rewrite <- H0; exact Hdisj).
      assert (Hd2 : Δz ##ₘ Δ2) by (apply (delta_disj_r (Δ1 := Δ1)); rewrite <- H0; exact Hdisj).
      assert (Ht1 := IHrt1 z sz (delete z Γ1) az Δz Hins1
                       (@notin_delete_self_str Γ1 z) Hd1 Ha).
      assert (Ht2 : rt Γ2 Δ2 (subst z az e2) t2).
      { rewrite (@rt_subst_absent e2 t2 Γ2 Δ2 H3 z az (@notin_of_lookup_none Γ2 z Hz2)). exact H3. }
      rewrite H0.
      eapply rt_Pair with (Γ:=Γs) (Γ1:=delete z Γ1) (Γ2:=Γ2) (Δ:=(Δ1∪Δ2)∪Δz)
                          (Δ1:=Δ1∪Δz) (Δ2:=Δ2) (e1:=subst z az e1) (e2:=subst z az e2)
                          (t1:=t1) (t2:=t2).
      * exact Hs'.
      * apply union_rot. apply map_disjoint_sym. exact Hd2.
      * apply delta_disj_union; [exact H1|exact Hd2].
      * exact Ht1.
      * exact Ht2.
    + assert (Heq : Γ = Γ1 ∪ Γ2) by (destruct H; done).
      assert (E2z : Γ2 !! z = Some sz).
      { assert (Hl : Γ !! z = Some sz) by (rewrite HΓs; rewrite (lookup_insert_eq Γs z sz); done).
        rewrite Heq in Hl. rewrite (lookup_union_r Γ1 Γ2 z Hz1) in Hl. exact Hl. }
      assert (Hins2 : Γ2 = <[z:=sz]>(delete z Γ2)) by (symmetry; apply del_ins_self; exact E2z).
      assert (Hd1 : Δz ##ₘ Δ1) by (apply (delta_disj_l (Δ2 := Δ2)); rewrite <- H0; exact Hdisj).
      assert (Hd2 : Δz ##ₘ Δ2) by (apply (delta_disj_r (Δ1 := Δ1)); rewrite <- H0; exact Hdisj).
      assert (Ht2 := IHrt2 z sz (delete z Γ2) az Δz Hins2
                       (@notin_delete_self_str Γ2 z) Hd2 Ha).
      assert (Ht1 : rt Γ1 Δ1 (subst z az e1) t1).
      { rewrite (@rt_subst_absent e1 t1 Γ1 Δ1 H2 z az (@notin_of_lookup_none Γ1 z Hz1)). exact H2. }
      rewrite H0.
      eapply rt_Pair with (Γ:=Γs) (Γ1:=Γ1) (Γ2:=delete z Γ2) (Δ:=(Δ1∪Δ2)∪Δz)
                          (Δ1:=Δ1) (Δ2:=Δ2∪Δz) (e1:=subst z az e1) (e2:=subst z az e2)
                          (t1:=t1) (t2:=t2).
      * exact Hs'.
      * rewrite <- map_union_assoc. done.
      * apply map_disjoint_union_r. split; [exact H1|apply map_disjoint_sym; exact Hd1].
      * exact Ht1.
      * exact Ht2.
    + assert (Hae : Δz = ∅) by (apply (rtv_unr Ha Hunr)).
      assert (Hins1 : Γ1 = <[z:=sz]>(delete z Γ1)) by (symmetry; apply del_ins_self; exact Hz1).
      assert (Hins2 : Γ2 = <[z:=sz]>(delete z Γ2)) by (symmetry; apply del_ins_self; exact Hz2).
      assert (Hd1 : Δz ##ₘ Δ1) by (apply (delta_disj_l (Δ2 := Δ2)); rewrite <- H0; exact Hdisj).
      assert (Hd2 : Δz ##ₘ Δ2) by (apply (delta_disj_r (Δ1 := Δ1)); rewrite <- H0; exact Hdisj).
      assert (Ht1 := IHrt1 z sz (delete z Γ1) az Δz Hins1
                       (@notin_delete_self_str Γ1 z) Hd1 Ha).
      assert (Ht2 := IHrt2 z sz (delete z Γ2) az Δz Hins2
                       (@notin_delete_self_str Γ2 z) Hd2 Ha).
      rewrite Hae, union_empty_r_nat in *.
      eapply rt_Pair with (Γ:=Γs) (Γ1:=delete z Γ1) (Γ2:=delete z Γ2) (Δ:=Δ)
                          (Δ1:=Δ1) (Δ2:=Δ2) (e1:=subst z az e1) (e2:=subst z az e2)
                          (t1:=t1) (t2:=t2).
      * exact Hs'.
      * exact H0.
      * exact H1.
      * exact Ht1.
      * exact Ht2.

  - (* LetPair *)
    simpl.
    assert (Hsplt : env_split (<[z:=sz]>Γs) Γ1 Γ2) by (rewrite <- HΓs; exact H).
    destruct (env_split_ambient Hsplt Hx)
      as [ (Hz2 & Hs') | [ (Hz1 & Hs') | (Hz1 & Hz2 & Hunr & Hs') ] ].
    + assert (Heq : Γ = Γ1 ∪ Γ2) by (destruct H; done).
      assert (E1z : Γ1 !! z = Some sz).
      { assert (Hl : Γ !! z = Some sz) by (rewrite HΓs; rewrite (lookup_insert_eq Γs z sz); done).
        rewrite Heq in Hl. rewrite (lookup_union_l Γ1 Γ2 z Hz2) in Hl. exact Hl. }
      assert (Hins1 : Γ1 = <[z:=sz]>(delete z Γ1)) by (symmetry; apply del_ins_self; exact E1z).
      assert (Hd1 : Δz ##ₘ Δ1) by (apply (delta_disj_l (Δ2 := Δ2)); rewrite <- H0; exact Hdisj).
      assert (Hd2 : Δz ##ₘ Δ2) by (apply (delta_disj_r (Δ1 := Δ1)); rewrite <- H0; exact Hdisj).
      assert (Ht1 := IHrt1 z sz (delete z Γ1) az Δz Hins1
                       (@notin_delete_self_str Γ1 z) Hd1 Ha).
      assert (Ht2 : rt Γ2 Δ2 (subst z az e2) (FunT Lin t1 (FunT Lin t2 t))).
      { rewrite (@rt_subst_absent e2 (FunT Lin t1 (FunT Lin t2 t)) Γ2 Δ2 H3 z az
                   (@notin_of_lookup_none Γ2 z Hz2)). exact H3. }
      rewrite H0.
      eapply rt_LetPair with (Γ:=Γs) (Γ1:=delete z Γ1) (Γ2:=Γ2) (Δ:=(Δ1∪Δ2)∪Δz)
                             (Δ1:=Δ1∪Δz) (Δ2:=Δ2) (e1:=subst z az e1) (e2:=subst z az e2)
                             (t1:=t1) (t2:=t2) (t:=t).
      * exact Hs'.
      * apply union_rot. apply map_disjoint_sym. exact Hd2.
      * apply delta_disj_union; [exact H1|exact Hd2].
      * exact Ht1.
      * exact Ht2.
    + assert (Heq : Γ = Γ1 ∪ Γ2) by (destruct H; done).
      assert (E2z : Γ2 !! z = Some sz).
      { assert (Hl : Γ !! z = Some sz) by (rewrite HΓs; rewrite (lookup_insert_eq Γs z sz); done).
        rewrite Heq in Hl. rewrite (lookup_union_r Γ1 Γ2 z Hz1) in Hl. exact Hl. }
      assert (Hins2 : Γ2 = <[z:=sz]>(delete z Γ2)) by (symmetry; apply del_ins_self; exact E2z).
      assert (Hd1 : Δz ##ₘ Δ1) by (apply (delta_disj_l (Δ2 := Δ2)); rewrite <- H0; exact Hdisj).
      assert (Hd2 : Δz ##ₘ Δ2) by (apply (delta_disj_r (Δ1 := Δ1)); rewrite <- H0; exact Hdisj).
      assert (Ht2 := IHrt2 z sz (delete z Γ2) az Δz Hins2
                       (@notin_delete_self_str Γ2 z) Hd2 Ha).
      assert (Ht1 : rt Γ1 Δ1 (subst z az e1) (PairT t1 t2)).
      { rewrite (@rt_subst_absent e1 (PairT t1 t2) Γ1 Δ1 H2 z az (@notin_of_lookup_none Γ1 z Hz1)). exact H2. }
      rewrite H0.
      eapply rt_LetPair with (Γ:=Γs) (Γ1:=Γ1) (Γ2:=delete z Γ2) (Δ:=(Δ1∪Δ2)∪Δz)
                             (Δ1:=Δ1) (Δ2:=Δ2∪Δz) (e1:=subst z az e1) (e2:=subst z az e2)
                             (t1:=t1) (t2:=t2) (t:=t).
      * exact Hs'.
      * rewrite <- map_union_assoc. done.
      * apply map_disjoint_union_r. split; [exact H1|apply map_disjoint_sym; exact Hd1].
      * exact Ht1.
      * exact Ht2.
    + assert (Hae : Δz = ∅) by (apply (rtv_unr Ha Hunr)).
      assert (Hins1 : Γ1 = <[z:=sz]>(delete z Γ1)) by (symmetry; apply del_ins_self; exact Hz1).
      assert (Hins2 : Γ2 = <[z:=sz]>(delete z Γ2)) by (symmetry; apply del_ins_self; exact Hz2).
      assert (Hd1 : Δz ##ₘ Δ1) by (apply (delta_disj_l (Δ2 := Δ2)); rewrite <- H0; exact Hdisj).
      assert (Hd2 : Δz ##ₘ Δ2) by (apply (delta_disj_r (Δ1 := Δ1)); rewrite <- H0; exact Hdisj).
      assert (Ht1 := IHrt1 z sz (delete z Γ1) az Δz Hins1
                       (@notin_delete_self_str Γ1 z) Hd1 Ha).
      assert (Ht2 := IHrt2 z sz (delete z Γ2) az Δz Hins2
                       (@notin_delete_self_str Γ2 z) Hd2 Ha).
      rewrite Hae, union_empty_r_nat in *.
      eapply rt_LetPair with (Γ:=Γs) (Γ1:=delete z Γ1) (Γ2:=delete z Γ2) (Δ:=Δ)
                             (Δ1:=Δ1) (Δ2:=Δ2) (e1:=subst z az e1) (e2:=subst z az e2)
                             (t1:=t1) (t2:=t2) (t:=t).
      * exact Hs'.
      * exact H0.
      * exact H1.
      * exact Ht1.
      * exact Ht2.

  - (* Sum *)
    simpl. apply rt_Sum.
    exact (IHrt z sz Γs az Δz HΓs Hx Hdisj Ha).
  - (* MatchSum *)
    simpl.
    assert (Hsplt : env_split (<[z:=sz]>Γs) Γ1 Γ2) by (rewrite <- HΓs; exact H).
    destruct (env_split_ambient Hsplt Hx)
      as [ (Hz2 & Hs') | [ (Hz1 & Hs') | (Hz1 & Hz2 & Hunr & Hs') ] ].
    + assert (Heq : Γ = Γ1 ∪ Γ2) by (destruct H; done).
      assert (E1z : Γ1 !! z = Some sz).
      { assert (Hl : Γ !! z = Some sz) by (rewrite HΓs; rewrite (lookup_insert_eq Γs z sz); done).
        rewrite Heq in Hl. rewrite (lookup_union_l Γ1 Γ2 z Hz2) in Hl. exact Hl. }
      assert (Hins1 : Γ1 = <[z:=sz]>(delete z Γ1)) by (symmetry; apply del_ins_self; exact E1z).
      assert (Hd1 : Δz ##ₘ Δ1) by (apply (delta_disj_l (Δ2 := Δ2)); rewrite <- H0; exact Hdisj).
      assert (Hd2 : Δz ##ₘ Δ2) by (apply (delta_disj_r (Δ1 := Δ1)); rewrite <- H0; exact Hdisj).
      assert (Ht1 := IHrt z sz (delete z Γ1) az Δz Hins1
                       (@notin_delete_self_str Γ1 z) Hd1 Ha).
      assert (Ht2 : forall i, rt Γ2 Δ2 (subst z az (es i)) (FunT Lin (ts i) t)).
      { intros i. rewrite (@rt_subst_absent (es i) (FunT Lin (ts i) t) Γ2 Δ2 (H4 i) z az
                   (@notin_of_lookup_none Γ2 z Hz2)). exact (H4 i). }
      rewrite H0.
      eapply rt_MatchSum with (n:=n) (Γ:=Γs) (Γ1:=delete z Γ1) (Γ2:=Γ2)
                              (Δ:=(Δ1∪Δ2)∪Δz) (Δ1:=Δ1∪Δz) (Δ2:=Δ2)
                              (t:=t) (ts:=ts) (es:=(fun i => subst z az (es i))) (e:=subst z az e).
      * exact Hs'.
      * apply union_rot. apply map_disjoint_sym. exact Hd2.
      * apply delta_disj_union; [exact H1|exact Hd2].
      * exact H2.
      * exact Ht1.
      * exact Ht2.
    + assert (Heq : Γ = Γ1 ∪ Γ2) by (destruct H; done).
      assert (E2z : Γ2 !! z = Some sz).
      { assert (Hl : Γ !! z = Some sz) by (rewrite HΓs; rewrite (lookup_insert_eq Γs z sz); done).
        rewrite Heq in Hl. rewrite (lookup_union_r Γ1 Γ2 z Hz1) in Hl. exact Hl. }
      assert (Hins2 : Γ2 = <[z:=sz]>(delete z Γ2)) by (symmetry; apply del_ins_self; exact E2z).
      assert (Hd1 : Δz ##ₘ Δ1) by (apply (delta_disj_l (Δ2 := Δ2)); rewrite <- H0; exact Hdisj).
      assert (Hd2 : Δz ##ₘ Δ2) by (apply (delta_disj_r (Δ1 := Δ1)); rewrite <- H0; exact Hdisj).
      assert (Ht2 : forall i, rt (delete z Γ2) (Δ2 ∪ Δz) (subst z az (es i)) (FunT Lin (ts i) t)).
      { intros i. exact (H5 i z sz (delete z Γ2) az Δz Hins2 (@notin_delete_self_str Γ2 z) Hd2 Ha). }
      assert (Ht1 : rt Γ1 Δ1 (subst z az e) (SumT n ts)).
      { rewrite (@rt_subst_absent e (SumT n ts) Γ1 Δ1 H3 z az (@notin_of_lookup_none Γ1 z Hz1)). exact H3. }
      assert (Hcond : n = 0 -> env_unr (delete z Γ2)).
      { intros Hn. apply env_unr_delete. exact (H2 Hn). }
      rewrite H0.
      eapply rt_MatchSum with (n:=n) (Γ:=Γs) (Γ1:=Γ1) (Γ2:=delete z Γ2)
                              (Δ:=(Δ1∪Δ2)∪Δz) (Δ1:=Δ1) (Δ2:=Δ2∪Δz)
                              (t:=t) (ts:=ts) (es:=(fun i => subst z az (es i))) (e:=subst z az e).
      * exact Hs'.
      * rewrite <- map_union_assoc. done.
      * apply map_disjoint_union_r. split; [exact H1|apply map_disjoint_sym; exact Hd1].
      * exact Hcond.
      * exact Ht1.
      * exact Ht2.
    + assert (Hae : Δz = ∅) by (apply (rtv_unr Ha Hunr)).
      assert (Hins1 : Γ1 = <[z:=sz]>(delete z Γ1)) by (symmetry; apply del_ins_self; exact Hz1).
      assert (Hins2 : Γ2 = <[z:=sz]>(delete z Γ2)) by (symmetry; apply del_ins_self; exact Hz2).
      assert (Hd1 : Δz ##ₘ Δ1) by (apply (delta_disj_l (Δ2 := Δ2)); rewrite <- H0; exact Hdisj).
      assert (Hd2 : Δz ##ₘ Δ2) by (apply (delta_disj_r (Δ1 := Δ1)); rewrite <- H0; exact Hdisj).
      assert (Ht1 := IHrt z sz (delete z Γ1) az Δz Hins1
                       (@notin_delete_self_str Γ1 z) Hd1 Ha).
      assert (Ht2 : forall i, rt (delete z Γ2) (Δ2 ∪ Δz) (subst z az (es i)) (FunT Lin (ts i) t)).
      { intros i. exact (H5 i z sz (delete z Γ2) az Δz Hins2 (@notin_delete_self_str Γ2 z) Hd2 Ha). }
      assert (Hcond : n = 0 -> env_unr (delete z Γ2)).
      { intros Hn. apply env_unr_delete. exact (H2 Hn). }
      rewrite Hae, union_empty_r_nat in *.
      eapply rt_MatchSum with (n:=n) (Γ:=Γs) (Γ1:=delete z Γ1) (Γ2:=delete z Γ2)
                              (Δ:=Δ) (Δ1:=Δ1) (Δ2:=Δ2)
                              (t:=t) (ts:=ts) (es:=(fun i => subst z az (es i))) (e:=subst z az e).
      * exact Hs'.
      * exact H0.
      * exact H1.
      * exact Hcond.
      * exact Ht1.
      * exact Ht2.

  - (* Fork *)
    simpl. apply rt_Fork.
    exact (IHrt z sz Γs az Δz HΓs Hx Hdisj Ha).
  - (* Val *)
    simpl.
    assert (HunrSz : unr sz).
    { assert (Hi : Γ !! z = Some sz) by (rewrite HΓs; rewrite (lookup_insert_eq Γs z sz); done).
      exact (H z sz Hi). }
    assert (Hae : Δz = ∅) by (apply (rtv_unr Ha HunrSz)).
    rewrite Hae, union_empty_r_nat.
    apply rt_Val.
    + apply (env_unr_insert (Γ:=Γs) (x:=z) (t:=sz)).
      * exact Hx.
      * rewrite <- HΓs. exact H.
    + exact H0.
Qed.

(* ------------------------------------------------------------------ *)
(* Pure step subject reduction                                        *)
(* ------------------------------------------------------------------ *)

Lemma notin_dom_empty_str (x : string) : x ∉ dom (∅ : env).
Proof.
  intros Hc. apply elem_of_dom in Hc. destruct Hc as (v & Hv).
  exact (lookup_empty_Some x v Hv).
Qed.

Lemma rt_pure_step (e e' : expr) (t : type) (Δ : gmap nat type) :
  rt ∅ Δ e t -> pure_step e e' -> rt ∅ Δ e' t.
Proof.
  intros H Hs. induction Hs.
  - (* Fun *)
    inversion H; subst; clear H.
    apply rt_Val.
    + apply env_unr_empty.
    + destruct H2 as (He & _). eapply rtv_Fun.
      * exact H6.
      * assert (Hg : Γ' = {[x:=t1]}) by (rewrite He; apply insert_empty).
        rewrite Hg in H8. exact H8.
  - (* App *)
    inversion H; subst; clear H.
    destruct (env_split_empty H2 eq_refl) as [E1 E2]. rewrite E1 in H7. rewrite E2 in H9.
    inversion H7; subst; clear H7.
    inversion H5; subst; clear H5.
    inversion H9; subst; clear H9.
    eapply (@rt_subst_aux e t {[x:=t1]} Δ1 H11 x t1 ∅ a Δ2).
    + symmetry. apply insert_empty.
    + apply notin_dom_empty_str.
    + apply map_disjoint_sym. exact H4.
    + exact H6.
  - (* Unit *)
    inversion H; subst; clear H. apply rt_Val.
    + apply env_unr_empty.
    + apply rtv_Unit. done.
  - (* Pair *)
    inversion H; subst; clear H.
    destruct (env_split_empty H2 eq_refl) as [E1 E2]. rewrite E1 in H7. rewrite E2 in H9.
    inversion H7; subst; clear H7.
    inversion H9; subst; clear H9.
    apply rt_Val.
    + apply env_unr_empty.
    + eapply rtv_Pair.
      * done.
      * exact H4.
      * exact H5.
      * exact H7.
  - (* LetPair *)
    inversion H; subst; clear H.
    destruct (env_split_empty H2 eq_refl) as [E1 E2]. rewrite E1 in H7. rewrite E2 in H9.
    inversion H7; subst; clear H7.
    inversion H5; subst; clear H5.
    assert (Hd03_2 : (Δ0 ∪ Δ3) ##ₘ Δ2) by exact H4.
    assert (Hd0_2 : Δ0 ##ₘ Δ2).
    { destruct (map_disjoint_union_l Δ0 Δ3 Δ2) as [Hf _].
      destruct (Hf H4) as [Hl _]. exact Hl. }
    assert (Hd3_2 : Δ3 ##ₘ Δ2).
    { destruct (map_disjoint_union_l Δ0 Δ3 Δ2) as [Hf _].
      destruct (Hf H4) as [_ Hr]. exact Hr. }
    assert (Hv1 : rt ∅ Δ0 (Val v1) t1).
    { apply rt_Val; [apply env_unr_empty|exact H11]. }
    assert (Hv2 : rt ∅ Δ3 (Val v2) t2).
    { apply rt_Val; [apply env_unr_empty|exact H12]. }
    assert (Hinner : rt ∅ (Δ2 ∪ Δ0) (App e (Val v1)) (FunT Lin t2 t)).
    { eapply rt_App with (Γ:=∅) (Γ1:=∅) (Γ2:=∅) (Δ:=Δ2∪Δ0)
                        (Δ1:=Δ2) (Δ2:=Δ0) (e1:=e) (e2:=Val v1)
                        (t1:=t1) (t2:=FunT Lin t2 t) (l:=Lin).
      - apply env_split_nil.
      - done.
      - apply map_disjoint_sym. exact Hd0_2.
      - exact H9.
      - exact Hv1. }
    replace ((Δ0 ∪ Δ3) ∪ Δ2) with ((Δ2 ∪ Δ0) ∪ Δ3).
    + eapply rt_App with (Γ:=∅) (Γ1:=∅) (Γ2:=∅) (Δ:=(Δ2∪Δ0)∪Δ3)
                        (Δ1:=Δ2∪Δ0) (Δ2:=Δ3) (e1:=App e (Val v1)) (e2:=Val v2)
                        (t1:=t2) (t2:=t) (l:=Lin).
      * apply env_split_nil.
      * done.
      * apply map_disjoint_union_l. split.
        -- apply map_disjoint_sym. exact Hd3_2.
        -- exact H10.
      * exact Hinner.
      * exact Hv2.
    + rewrite (map_union_comm (Δ0 ∪ Δ3) Δ2 Hd03_2). rewrite map_union_assoc. done.

  - (* Sum *)
    inversion H; subst; clear H.
    inversion H5; subst; clear H5.
    apply rt_Val.
    + apply env_unr_empty.
    + apply rtv_Sum. exact H3.
  - (* MatchSum *)
    dependent destruction H.
    destruct (env_split_empty H eq_refl) as [E1 E2]. rewrite E1 in H3. rewrite E2 in H4.
    inversion H3; subst; clear H3.
    dependent destruction H8.
    assert (Hii : i0 = i) by (apply fin_to_nat_inj; exact x).
    rewrite Hii in H8.
    rewrite (map_union_comm Δ Δ2 H1).
    eapply rt_App with (Γ:=∅) (Γ1:=∅) (Γ2:=∅) (Δ:=Δ2∪Δ)
                       (Δ1:=Δ2) (Δ2:=Δ) (e1:=es i) (e2:=Val v)
                       (t1:=ts i) (t2:=t) (l:=Lin).
    + apply env_split_nil.
    + done.
    + apply map_disjoint_sym. exact H1.
    + apply H4.
    + apply rt_Val; [apply env_unr_empty| exact H8].
Qed.

(* ------------------------------------------------------------------ *)
(* Contexts and local progress                                        *)
(* ------------------------------------------------------------------ *)

Lemma ctx_compose k1 k2 : ctx k1 -> ctx k2 -> ctx (k1 ∘ k2).
Proof.
  intros H1. induction H1; intros H2; simpl.
  - exact H2.
  - exact (@Ctx_comp k1 (k0 ∘ k2) H (IHctx H2)).
Qed.

Lemma ctx1_ctx k : ctx1 k -> ctx k.
Proof. intros H. exact (@Ctx_comp k (fun x => x) H Ctx_id). Qed.

Lemma ctx_id_comp k : ctx k -> ctx (fun x => k x).
Proof. intros H. exact H. Qed.

Lemma ctx_app_l v : ctx (fun x => App x (Val v)).
Proof. apply ctx1_ctx. apply Ctx_App_l. Qed.
Lemma ctx_app_r e : ctx (fun x => App e x).
Proof. apply ctx1_ctx. apply Ctx_App_r. Qed.
Lemma ctx_pair_l e : ctx (fun x => Pair x e).
Proof. apply ctx1_ctx. apply Ctx_Pair_l. Qed.
Lemma ctx_pair_r e : ctx (fun x => Pair e x).
Proof. apply ctx1_ctx. apply Ctx_Pair_r. Qed.
Lemma ctx_letpair e : ctx (fun x => LetPair x e).
Proof. apply ctx1_ctx. apply Ctx_LetPair. Qed.
Lemma ctx_sum i : ctx (fun x => Sum i x).
Proof. apply ctx1_ctx. apply Ctx_Sum. Qed.
Lemma ctx_matchsum n es : ctx (fun x => MatchSum n x es).
Proof. apply ctx1_ctx. apply Ctx_MatchSum. Qed.
Lemma ctx_fork : ctx (fun x => Fork x).
Proof. apply ctx1_ctx. apply Ctx_Fork. Qed.

Definition is_val (e : expr) : Prop := exists v, e = Val v.
Definition reducible (e : expr) : Prop :=
  exists k r r', ctx k /\ e = k r /\ pure_step r r'.
Definition forkable (e : expr) : Prop :=
  exists k v, ctx k /\ e = k (Fork (Val v)).
Definition waiting0 (e : expr) : Prop := exists j, expr_waiting e j.

Lemma rt_progress Γ Δ e t : rt Γ Δ e t -> Γ = ∅ ->
  is_val e \/ reducible e \/ forkable e \/ waiting0 e.
Proof.
  intros H. induction H; intros Hg.
  - (* Var *) exfalso. destruct H as (Γ0 & Heq & _).
    assert (Hc : <[x:=t]>Γ0 = ∅) by (rewrite <- Heq; exact Hg).
    exact (insert_non_empty Γ0 x t Hc).
  - (* Fun *) right. left. exists id, (Fun x e), (Val (FunV x e)).
    split; [apply Ctx_id|]. split; [done| apply Fun_step].
  - (* App *)
    destruct (env_split_empty H Hg) as [Hg1 Hg2].
    destruct (IHrt2 Hg2) as [(v2 & ->) | [(k2 & r2 & r2' & Hk2 & -> & Hps2) | [(k2 & v2 & Hk2 & ->) | (j & Hw2)]]].
    + destruct (IHrt1 Hg1) as [(v1 & ->) | [(k1 & r1 & r1' & Hk1 & -> & Hps1) | [(k1 & v1 & Hk1 & ->) | (j & Hw1)]]].
      * (* both values *) rewrite Hg1 in H2.
        inversion H2; subst; clear H2.
        destruct (rtv_fun_inv H8) as [(x0 & e0 & Hv) | (n0 & Hv)]; subst v1.
        -- right. left. exists id, (App (Val (FunV x0 e0)) (Val v2)), (subst x0 v2 e0).
           split; [apply Ctx_id|]. split; [done|]. apply App_step.
        -- right. right. right. exists n0. exists id, v2. split; [apply Ctx_id|done].
      * right. left. exists ((fun x => App x (Val v2)) ∘ k1), r1, r1'.
        split; [|split; [done|done]].
        apply ctx_compose; [apply ctx_app_l|done].
      * right. right. left. exists ((fun x => App x (Val v2)) ∘ k1), v1.
        split; [|done]. apply ctx_compose; [apply ctx_app_l|done].
      * right. right. right. exists j.
        destruct Hw1 as (k0 & w & Hv & Heq). exists ((fun x => App x (Val v2)) ∘ k0), w.
        split; [apply ctx_compose; [apply ctx_app_l|done]|].
        rewrite Heq. done.
    + right. left. exists ((fun x => App e1 x) ∘ k2), r2, r2'.
      split; [|split; [done|done]]. apply ctx_compose; [apply ctx_app_r|done].
    + right. right. left. exists ((fun x => App e1 x) ∘ k2), v2.
      split; [|done]. apply ctx_compose; [apply ctx_app_r|done].
    + right. right. right. exists j.
      destruct Hw2 as (k0 & w & Hv & Heq). exists ((fun x => App e1 x) ∘ k0), w.
      split; [apply ctx_compose; [apply ctx_app_r|done]|]. rewrite Heq. done.
  - (* Unit *)
    right. left. exists id, Unit, (Val UnitV). split; [apply Ctx_id|]. split; [done|apply Unit_step].
  - (* Pair *)
    destruct (env_split_empty H Hg) as [Hg1 Hg2].
    destruct (IHrt1 Hg1) as [(v1 & ->) | [(k1 & r1 & r1' & Hk1 & -> & Hps1) | [(k1 & v1 & Hk1 & ->) | (j & Hw1)]]].
    + destruct (IHrt2 Hg2) as [(v2 & ->) | [(k2 & r2 & r2' & Hk2 & -> & Hps2) | [(k2 & v2 & Hk2 & ->) | (j & Hw2)]]].
      * right. left. exists id, (Pair (Val v1) (Val v2)), (Val (PairV v1 v2)).
        split; [apply Ctx_id|]. split; [done|apply Pair_step].
      * right. left. exists ((fun x => Pair (Val v1) x) ∘ k2), r2, r2'.
        split; [|split; [done|done]]. apply ctx_compose; [apply ctx_pair_r|done].
      * right. right. left. exists ((fun x => Pair (Val v1) x) ∘ k2), v2.
        split; [|done]. apply ctx_compose; [apply ctx_pair_r|done].
      * right. right. right. exists j.
        destruct Hw2 as (k0 & w & Hv & Heq). exists ((fun x => Pair (Val v1) x) ∘ k0), w.
        split; [apply ctx_compose; [apply ctx_pair_r|done]|]. rewrite Heq. done.
    + right. left. exists ((fun x => Pair x e2) ∘ k1), r1, r1'.
      split; [|split; [done|done]]. apply ctx_compose; [apply ctx_pair_l|done].
    + right. right. left. exists ((fun x => Pair x e2) ∘ k1), v1.
      split; [|done]. apply ctx_compose; [apply ctx_pair_l|done].
    + right. right. right. exists j.
      destruct Hw1 as (k0 & w & Hv & Heq). exists ((fun x => Pair x e2) ∘ k0), w.
      split; [apply ctx_compose; [apply ctx_pair_l|done]|]. rewrite Heq. done.
  - (* LetPair *)
    destruct (env_split_empty H Hg) as [Hg1 Hg2].
    destruct (IHrt1 Hg1) as [(v1 & ->) | [(k1 & r1 & r1' & Hk1 & -> & Hps1) | [(k1 & v1 & Hk1 & ->) | (j & Hw1)]]].
    + rewrite Hg1 in H2. inversion H2; subst; clear H2.
      destruct (rtv_pair_inv H8) as (a & b & Hv). subst v1.
      right. left. exists id, (LetPair (Val (PairV a b)) e2), (App (App e2 (Val a)) (Val b)).
      split; [apply Ctx_id|]. split; [done|apply LetPair_step].
    + right. left. exists ((fun x => LetPair x e2) ∘ k1), r1, r1'.
      split; [|split; [done|done]]. apply ctx_compose; [apply ctx_letpair|done].
    + right. right. left. exists ((fun x => LetPair x e2) ∘ k1), v1.
      split; [|done]. apply ctx_compose; [apply ctx_letpair|done].
    + right. right. right. exists j.
      destruct Hw1 as (k0 & w & Hv & Heq). exists ((fun x => LetPair x e2) ∘ k0), w.
      split; [apply ctx_compose; [apply ctx_letpair|done]|]. rewrite Heq. done.
  - (* Sum *)
    destruct (IHrt Hg) as [(v & ->) | [(k1 & r1 & r1' & Hk1 & -> & Hps1) | [(k1 & v & Hk1 & ->) | (j & Hw)]]].
    + rewrite Hg in H. inversion H; subst; clear H.
      right. left. exists id, (Sum i (Val v)), (Val (SumV (fin_to_nat i) v)).
      split; [apply Ctx_id|]. split; [done|]. apply (Sum_step (fin_to_nat i) v).
    + right. left. exists ((fun x => Sum i x) ∘ k1), r1, r1'.
      split; [|split; [done|done]]. apply ctx_compose; [apply ctx_sum|done].
    + right. right. left. exists ((fun x => Sum i x) ∘ k1), v.
      split; [|done]. apply ctx_compose; [apply ctx_sum|done].
    + right. right. right. exists j.
      destruct Hw as (k0 & w & Hv & Heq). exists ((fun x => Sum i x) ∘ k0), w.
      split; [apply ctx_compose; [apply ctx_sum|done]|]. rewrite Heq. done.
  - (* MatchSum *)
    destruct (env_split_empty H Hg) as [Hg1 Hg2].
    destruct (IHrt Hg1) as [(v & ->) | [(k1 & r1 & r1' & Hk1 & -> & Hps1) | [(k1 & v & Hk1 & ->) | (j & Hw1)]]].
    + rewrite Hg1 in H3. inversion H3; subst; clear H3.
      dependent destruction H10.
      right. left. exists id, (MatchSum n (Val (SumV i v)) es), (App (es i) (Val v)).
      split; [apply Ctx_id|]. split; [done|]. apply MatchSum_step.
    + right. left. exists ((fun x => MatchSum n x es) ∘ k1), r1, r1'.
      split; [|split; [done|done]]. apply ctx_compose; [apply ctx_matchsum|done].
    + right. right. left. exists ((fun x => MatchSum n x es) ∘ k1), v.
      split; [|done]. apply ctx_compose; [apply ctx_matchsum|done].
    + right. right. right. exists j.
      destruct Hw1 as (k0 & w & Hv & Heq). exists ((fun x => MatchSum n x es) ∘ k0), w.
      split; [apply ctx_compose; [apply ctx_matchsum|done]|]. rewrite Heq. done.
  - (* Fork *)
    destruct (IHrt Hg) as [(v & ->) | [(k1 & r1 & r1' & Hk1 & -> & Hps1) | [(k1 & v & Hk1 & ->) | (j & Hw)]]].
    + right. right. left. exists id, v. split; [apply Ctx_id|done].
    + right. left. exists ((fun x => Fork x) ∘ k1), r1, r1'.
      split; [|split; [done|done]]. apply ctx_compose; [apply ctx_fork|done].
    + right. right. left. exists ((fun x => Fork x) ∘ k1), v.
      split; [|done]. apply ctx_compose; [apply ctx_fork|done].
    + right. right. right. exists j.
      destruct Hw as (k0 & w & Hv & Heq). exists ((fun x => Fork x) ∘ k0), w.
      split; [apply ctx_compose; [apply ctx_fork|done]|]. rewrite Heq. done.
  - (* Val *)
    left. exists v. done.
Qed.

(* ------------------------------------------------------------------ *)
(* Configuration invariant                                            *)
(* ------------------------------------------------------------------ *)

Definition live (ρ : cfg) (n : nat) : Prop := ρ !! n = Some Barrier.

Record invP (ρ : cfg) (ID : nat -> gmap nat type) (IOm : gmap nat (type * type))
  (IS : nat -> nat -> bool) (IH1 IH2 : nat -> nat) : Prop := {
  i_thr : forall i e, ρ !! i = Some (Thread e) -> rt ∅ (ID i) e UnitT;
  i_nonthr : forall i, (forall e, ρ !! i <> Some (Thread e)) -> ID i = ∅;
  i_live_iff : forall n, live ρ n <-> IOm !! n <> None;
  i_dual : forall n p q, IOm !! n = Some (p, q) -> q = dual p;
  i_H_neq : forall n, live ρ n -> IH1 n <> IH2 n;
  i_H1 : forall n p q, live ρ n -> IOm !! n = Some (p, q) -> ID (IH1 n) !! n = Some p;
  i_H2 : forall n p q, live ρ n -> IOm !! n = Some (p, q) -> ID (IH2 n) !! n = Some q;
  i_H_exact : forall n k t, live ρ n -> ID k !! n = Some t -> k = IH1 n \/ k = IH2 n;
  i_cut1 : forall n, live ρ n -> IS n (IH1 n) <> IS n (IH2 n);
  i_cut2 : forall n m, live ρ n -> live ρ m -> n <> m -> IS n (IH1 m) = IS n (IH2 m);
  i_dead : forall n k t, IOm !! n = None -> ID k !! n = Some t -> False;
}.

Definition inv (ρ : cfg) : Prop :=
  exists ID IOm IS IH1 IH2, invP ρ ID IOm IS IH1 IH2.

Lemma live_iff_Some (ρ : cfg) n : live ρ n <-> ρ !! n = Some Barrier.
Proof. done. Qed.

(* ------------------------------------------------------------------ *)
(* Basic consequences of the configuration invariant                  *)
(* ------------------------------------------------------------------ *)

Lemma lookup_some_of_neq {A} (m : gmap nat A) n : m !! n <> None -> exists t, m !! n = Some t.
Proof.
  destruct (m !! n) as [t|] eqn:E; [eexists; done| intros H; exfalso; apply H; done].
Qed.

Lemma inv_holder_eq {ρ : cfg} (ID : nat -> gmap nat type) (IOm : gmap nat (type * type)) (IS : nat -> nat -> bool) (IH1 IH2 : nat -> nat) (I : invP ρ ID IOm IS IH1 IH2) n a b k :
  live ρ n -> a <> b ->
  ID a !! n <> None -> ID b !! n <> None -> ID k !! n <> None ->
  k = a \/ k = b.
Proof.
  intros Hl Hab Ha Hb Hk.
  destruct (@lookup_some_of_neq type (ID a) n Ha) as (ta & Ea).
  destruct (@lookup_some_of_neq type (ID b) n Hb) as (tb & Eb).
  destruct (@lookup_some_of_neq type (ID k) n Hk) as (tk & Ek).
  destruct (I.(i_H_exact) Hl Ea) as [Aa|Aa]; subst a;
  destruct (I.(i_H_exact) Hl Eb) as [Bb|Bb]; subst b;
  destruct (I.(i_H_exact) Hl Ek) as [Kk|Kk]; subst k;
  try (left; done); try (right; done); exfalso; apply Hab; done.
Qed.

Lemma inv_pair_types {ρ : cfg} (ID : nat -> gmap nat type) (IOm : gmap nat (type * type)) (IS : nat -> nat -> bool) (IH1 IH2 : nat -> nat) (I : invP ρ ID IOm IS IH1 IH2) n p q a b :
  live ρ n -> IOm !! n = Some (p, q) -> a <> b ->
  ID a !! n <> None -> ID b !! n <> None ->
  (ID a !! n = Some p /\ ID b !! n = Some q) \/
  (ID a !! n = Some q /\ ID b !! n = Some p).
Proof.
  intros Hl Hom Hab Ha Hb.
  pose proof (I.(i_H_neq) Hl) as Hneq.
  pose proof (I.(i_H1) Hl Hom) as E1.
  pose proof (I.(i_H2) Hl Hom) as E2.
  destruct (@lookup_some_of_neq type (ID a) n Ha) as (ta & Ea).
  destruct (@lookup_some_of_neq type (ID b) n Hb) as (tb & Eb).
  destruct (I.(i_H_exact) Hl Ea) as [Aa|Aa]; subst a;
  destruct (I.(i_H_exact) Hl Eb) as [Bb|Bb]; subst b.
  - exfalso. apply Hab. done.
  - left. split; [exact E1|exact E2].
  - right. split; [exact E2|exact E1].
  - exfalso. apply Hab. done.
Qed.

Lemma inv_holder_thread {ρ : cfg} (ID : nat -> gmap nat type) (IOm : gmap nat (type * type)) (IS : nat -> nat -> bool) (IH1 IH2 : nat -> nat) (I : invP ρ ID IOm IS IH1 IH2) n k :
  live ρ n -> ID k !! n <> None -> exists e, ρ !! k = Some (Thread e).
Proof.
  intros Hl Hk. destruct (ρ !! k) as [[e|]|] eqn:E.
  - exists e. done.
  - exfalso. assert (Hnd : forall e0, ρ !! k <> Some (Thread e0)) by (intros e0 Hc; rewrite E in Hc; discriminate).
    pose proof (I.(i_nonthr) Hnd) as HD. rewrite HD in Hk. rewrite lookup_empty in Hk. apply Hk. done.
  - exfalso. assert (Hnd : forall e0, ρ !! k <> Some (Thread e0)) by (intros e0 Hc; rewrite E in Hc; discriminate).
    pose proof (I.(i_nonthr) Hnd) as HD. rewrite HD in Hk. rewrite lookup_empty in Hk. apply Hk. done.
Qed.

Lemma inv_live_of_holder {ρ : cfg} (ID : nat -> gmap nat type) (IOm : gmap nat (type * type)) (IS : nat -> nat -> bool) (IH1 IH2 : nat -> nat) (I : invP ρ ID IOm IS IH1 IH2) n k :
  ID k !! n <> None -> live ρ n.
Proof.
  intros Hk.
  destruct (IOm !! n) as [[p q]|] eqn:E.
  - destruct (I.(i_live_iff) n) as [_ Hg]. apply Hg. rewrite E. discriminate.
  - exfalso. destruct (@lookup_some_of_neq type (ID k) n Hk) as (t & Ht).
    exact (I.(i_dead) E Ht).
Qed.

Lemma inv_holder_partner {ρ : cfg} (ID : nat -> gmap nat type) (IOm : gmap nat (type * type)) (IS : nat -> nat -> bool) (IH1 IH2 : nat -> nat) (I : invP ρ ID IOm IS IH1 IH2) n i :
  live ρ n -> ID i !! n <> None ->
  exists j, j <> i /\ ID j !! n <> None.
Proof.
  intros Hl Hi.
  destruct (@lookup_some_of_neq type (ID i) n Hi) as (ti & Ei).
  destruct (I.(i_live_iff) n) as [Hf _].
  assert (Home : IOm !! n <> None) by (apply Hf; done).
  destruct (@lookup_some_of_neq (type*type) (IOm) n Home) as ((p & q) & Hom).
  pose proof (I.(i_H_neq) Hl) as Hneq.
  pose proof (I.(i_H1) Hl Hom) as E1.
  pose proof (I.(i_H2) Hl Hom) as E2.
  destruct (I.(i_H_exact) Hl Ei) as [Ai|Ai]; subst i.
  - exists (IH2 n). split; [done|]. rewrite E2. discriminate.
  - exists (IH1 n). split; [done|]. rewrite E1. discriminate.
Qed.

Lemma waiting_holds {ρ : cfg} (ID : nat -> gmap nat type) (IOm : gmap nat (type * type)) (IS : nat -> nat -> bool) (IH1 IH2 : nat -> nat) (I : invP ρ ID IOm IS IH1 IH2) i e j :
  ρ !! i = Some (Thread e) -> expr_waiting e j ->
  ID i !! j <> None /\ live ρ j.
Proof.
  intros Hth [k [v [Hk He]]]. subst e.
  pose proof (I.(i_thr) Hth) as Hrt.
  destruct (ctx_decomp Hk Hrt) as (Δk & Δh & s & Heq & Hct & Hh).
  inversion Hh; subst; clear Hh.
  destruct (env_split_empty H1 eq_refl) as [E1 E2]. rewrite E1 in H6. rewrite E2 in H8.
  inversion H6; subst; clear H6.
  dependent destruction H5.
  assert (Hsing2 : Δ2 !! j = None).
  { rewrite map_disjoint_singleton_l in H3. exact H3. }
  assert (Hh_j : ({[j := FunT Lin t1 s]} ∪ Δ2) !! j = Some (FunT Lin t1 s)).
  { apply (lookup_union_Some_l {[j := FunT Lin t1 s]} Δ2 j (FunT Lin t1 s)).
    apply (lookup_insert_eq (∅ : gmap nat type) j (FunT Lin t1 s)). }
  assert (Hk_j : Δk !! j = None).
  { assert (Hkd : Δk ##ₘ ({[j := FunT Lin t1 s]} ∪ Δ2)) by (apply (ct_disj Hct)).
    rewrite map_disjoint_union_r in Hkd. destruct Hkd as [Hks _].
    rewrite map_disjoint_singleton_r in Hks. exact Hks. }
  assert (Hdi : ID i !! j = Some (FunT Lin t1 s)).
  { rewrite Heq. rewrite (lookup_union_r Δk ({[j := FunT Lin t1 s]} ∪ Δ2) j Hk_j).
    exact Hh_j. }
  split.
  - rewrite Hdi. discriminate.
  - apply (@inv_live_of_holder ρ ID IOm IS IH1 IH2 I j i). rewrite Hdi. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Decomposing configurations around a small set of local keys        *)
(* ------------------------------------------------------------------ *)

Lemma lookup_none_of_notin_cfg (γ : cfg) n : n ∉ dom γ -> γ !! n = None.
Proof.
  intros H. destruct (γ !! n) as [v|] eqn:E; [|done].
  exfalso. apply H. apply elem_of_dom. eexists. exact E.
Qed.

Lemma notin_dom_of_sub_cfg (γ γ' : cfg) n : γ ⊆ γ' -> n ∉ dom γ' -> n ∉ dom γ.
Proof.
  intros Hsub Hz Hzin. apply Hz.
  apply elem_of_dom in Hzin. destruct Hzin as (v & Hv).
  apply elem_of_dom. exists v.
  destruct (map_subseteq_spec γ γ') as [Hf _]. exact (Hf Hsub n v Hv).
Qed.

Lemma cfg_decomp1 (ρ : cfg) i (o : obj) : ρ !! i = Some o ->
  ρ = ({[i := o]} : cfg) ∪ delete i ρ.
Proof.
  intros H. apply map_eq. intro k.
  destruct (decide (i = k)) as [Heq|Hne].
  - subst k. symmetry. transitivity (Some o).
    + apply (lookup_union_Some_l ({[i:=o]}:cfg) (delete i ρ) i o).
      assert (Hs : ({[i:=o]}:cfg) = <[i:=o]>(∅:cfg)) by reflexivity.
      rewrite Hs. exact (lookup_insert_eq (∅:cfg) i o).
    + symmetry. exact H.
  - transitivity ((delete i ρ) !! k).
    + symmetry. apply (lookup_delete_ne ρ i k). exact Hne.
    + symmetry. apply (lookup_union_r ({[i:=o]}:cfg) (delete i ρ) k).
      assert (Hs : ({[i:=o]}:cfg) = <[i:=o]>(∅:cfg)) by reflexivity.
      rewrite Hs. apply (lookup_insert_None (∅:cfg) i k o). split; [done|done].
Qed.

Lemma cfg_disj1 (ρ : cfg) i (o : obj) : ({[i := o]} : cfg) ##ₘ delete i ρ.
Proof.
  assert (Hs : ({[i:=o]}:cfg) = <[i:=o]>(∅:cfg)) by reflexivity.
  rewrite Hs. rewrite map_disjoint_insert_l. split.
  - apply (lookup_delete_eq ρ i).
  - apply map_disjoint_empty_l.
Qed.

Lemma cfg_decomp3 (ρ : cfg) i oi j oj n on :
  i <> j -> i <> n -> j <> n ->
  ρ !! i = Some oi -> ρ !! j = Some oj -> ρ !! n = Some on ->
  ρ = ({[i := oi; j := oj; n := on]} : cfg)
      ∪ delete i (delete j (delete n ρ)).
Proof.
  intros Hij Hin Hjn Hi Hj Hn.
  apply map_eq. intro k.
  assert (Hs : ({[i:=oi; j:=oj; n:=on]} : cfg) =
              <[i:=oi]>(<[j:=oj]>(<[n:=on]>(∅:cfg)))) by reflexivity.
  rewrite Hs.
  set (L := <[i:=oi]>(<[j:=oj]>(<[n:=on]>(∅:cfg)))).
  set (F := delete i (delete j (delete n ρ))).
  fold L F.
  destruct (decide (i = k)) as [Heq|Hki].
  - subst k. symmetry. transitivity (Some oi).
    + apply (lookup_union_Some_l L F i oi).
      unfold L. apply (lookup_insert_eq (<[j:=oj]>(<[n:=on]>(∅:cfg))) i oi).
    + symmetry. exact Hi.
  - destruct (decide (j = k)) as [Heq|Hkj].
    + subst k. symmetry. transitivity (Some oj).
      * apply (lookup_union_Some_l L F j oj).
        unfold L. rewrite (lookup_insert_ne (<[j:=oj]>(<[n:=on]>(∅:cfg))) i j oi Hki).
        apply (lookup_insert_eq (<[n:=on]>(∅:cfg)) j oj).
      * symmetry. exact Hj.
    + destruct (decide (n = k)) as [Heq|Hkn].
      * subst k. symmetry. transitivity (Some on).
        -- apply (lookup_union_Some_l L F n on).
           unfold L. rewrite (lookup_insert_ne (<[j:=oj]>(<[n:=on]>(∅:cfg))) i n oi Hki).
           rewrite (lookup_insert_ne (<[n:=on]>(∅:cfg)) j n oj Hkj).
           apply (lookup_insert_eq (∅:cfg) n on).
        -- symmetry. exact Hn.
      * transitivity (F !! k).
        -- symmetry. unfold F.
           rewrite (lookup_delete_ne (delete j (delete n ρ)) i k Hki).
           rewrite (lookup_delete_ne (delete n ρ) j k Hkj).
           rewrite (lookup_delete_ne ρ n k Hkn).
           done.
        -- symmetry. apply (lookup_union_r L F k).
           unfold L.
           rewrite (lookup_insert_ne (<[j:=oj]>(<[n:=on]>(∅:cfg))) i k oi Hki).
           rewrite (lookup_insert_ne (<[n:=on]>(∅:cfg)) j k oj Hkj).
           rewrite (lookup_insert_ne (∅:cfg) n k on Hkn).
           done.
Qed.

Lemma cfg_disj3 (ρ : cfg) i oi j oj n on :
  i <> j -> i <> n -> j <> n ->
  ({[i := oi; j := oj; n := on]} : cfg) ##ₘ delete i (delete j (delete n ρ)).
Proof.
  intros Hij Hin Hjn.
  assert (Hs : ({[i:=oi; j:=oj; n:=on]} : cfg) =
              <[i:=oi]>(<[j:=oj]>(<[n:=on]>(∅:cfg)))) by reflexivity.
  rewrite Hs.
  rewrite map_disjoint_insert_l. split.
  - apply (lookup_delete_eq (delete j (delete n ρ)) i).
  - rewrite map_disjoint_insert_l. split.
    + rewrite (lookup_delete_ne (delete j (delete n ρ)) i j Hij).
      apply (lookup_delete_eq (delete n ρ) j).
    + rewrite map_disjoint_insert_l. split.
      * rewrite (lookup_delete_ne (delete j (delete n ρ)) i n Hin).
        rewrite (lookup_delete_ne (delete n ρ) j n Hjn).
        apply (lookup_delete_eq ρ n).
      * apply map_disjoint_empty_l.
Qed.

(* ------------------------------------------------------------------ *)
(* Building concrete steps                                            *)
(* ------------------------------------------------------------------ *)

Lemma can_step_pure (ρ : cfg) i k r r' :
  ρ !! i = Some (Thread (k r)) -> ctx k -> pure_step r r' -> can_step ρ i.
Proof.
  intros Hlook Hk Hps.
  exists (({[i := Thread (k r')]} : cfg) ∪ delete i ρ).
  assert (Heq : ρ = ({[i := Thread (k r)]} : cfg) ∪ delete i ρ)
    by (apply cfg_decomp1; exact Hlook).
  rewrite Heq at 1.
  eapply Frame_step with (ρ := {[i := Thread (k r)]}) (ρ' := {[i := Thread (k r')]})
                         (ρf := delete i ρ) (i := i).
  - apply cfg_disj1.
  - apply cfg_disj1.
  - apply (Pure_step i k r r' Hk Hps).
Qed.

Lemma can_step_exit (ρ : cfg) i v :
  ρ !! i = Some (Thread (Val v)) -> can_step ρ i.
Proof.
  intros Hlook.
  exists ((∅ : cfg) ∪ delete i ρ).
  assert (Heq : ρ = ({[i := Thread (Val v)]} : cfg) ∪ delete i ρ)
    by (apply cfg_decomp1; exact Hlook).
  rewrite Heq at 1.
  eapply Frame_step with (ρ := {[i := Thread (Val v)]}) (ρ' := (∅ : cfg))
                         (ρf := delete i ρ) (i := i).
  - apply cfg_disj1.
  - apply map_disjoint_empty_l.
  - apply (Exit_step i v).
Qed.

Lemma can_step_fork (ρ : cfg) i k v :
  ρ !! i = Some (Thread (k (Fork (Val v)))) -> ctx k -> can_step ρ i.
Proof.
  intros Hlook Hk.
  pose (j := fresh (dom ρ)).
  pose (n := fresh (dom ρ ∪ {[j]})).
  assert (Hjdom : j ∉ dom ρ) by apply is_fresh.
  assert (Hn : n ∉ dom ρ ∪ {[j]}) by apply is_fresh.
  assert (Hndom : n ∉ dom ρ).
  { intros Hc. apply Hn. apply elem_of_union_l. exact Hc. }
  assert (Hnj : n <> j).
  { intros Hc. apply Hn. rewrite Hc. apply elem_of_union_r. apply elem_of_singleton. done. }
  assert (Hjn : j <> n) by (intros Hc; apply Hnj; symmetry; exact Hc).
  assert (Hij : i <> j) by (intros Hc; apply Hjdom; rewrite <- Hc; apply elem_of_dom; eexists; exact Hlook).
  assert (Hin : i <> n) by (intros Hc; apply Hndom; rewrite <- Hc; apply elem_of_dom; eexists; exact Hlook).
  assert (Hdj : delete i ρ !! j = None).
  { rewrite (lookup_delete_ne ρ i j Hij). apply lookup_none_of_notin_cfg. exact Hjdom. }
  assert (Hdn : delete i ρ !! n = None).
  { rewrite (lookup_delete_ne ρ i n Hin). apply lookup_none_of_notin_cfg. exact Hndom. }
  assert (Hdi : delete i ρ !! i = None) by (apply (lookup_delete_eq ρ i)).
  exists (({[i := Thread (k (Val (BarrierV n)));
             j := Thread (App (Val v) (Val (BarrierV n)));
             n := Barrier]} : cfg) ∪ delete i ρ).
  assert (Heq : ρ = ({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ delete i ρ)
    by (apply cfg_decomp1; exact Hlook).
  rewrite Heq at 1.
  eapply Frame_step with (ρ := {[i := Thread (k (Fork (Val v)))]})
                         (ρ' := {[i := Thread (k (Val (BarrierV n)));
                                   j := Thread (App (Val v) (Val (BarrierV n)));
                                   n := Barrier]})
                         (ρf := delete i ρ) (i := i).
  - apply cfg_disj1.
  - change (map_disjoint (insert i (Thread (k (Val (BarrierV n))))
               (insert j (Thread (App (Val v) (Val (BarrierV n))))
                  (insert n Barrier (∅ : cfg)))) (delete i ρ)).
    rewrite map_disjoint_insert_l. split; [exact Hdi|].
    rewrite map_disjoint_insert_l. split; [exact Hdj|].
    rewrite map_disjoint_insert_l. split; [exact Hdn|]. apply map_disjoint_empty_l.
  - apply (Fork_step i j n k v Hij Hin Hjn Hk).
Qed.

Lemma can_step_sync (ρ : cfg) i j n k1 k2 v1 v2 :
  i <> j -> i <> n -> j <> n ->
  ρ !! i = Some (Thread (k1 (App (Val (BarrierV n)) (Val v1)))) ->
  ρ !! j = Some (Thread (k2 (App (Val (BarrierV n)) (Val v2)))) ->
  ρ !! n = Some Barrier -> ctx k1 -> ctx k2 ->
  can_step ρ n.
Proof.
  intros Hij Hin Hjn Hi Hj Hn Hk1 Hk2.
  exists (({[i := Thread (k1 (Val v2)); j := Thread (k2 (Val v1))]} : cfg)
          ∪ delete i (delete j (delete n ρ))).
  assert (Heq : ρ = ({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                       j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                       n := Barrier]} : cfg)
                    ∪ delete i (delete j (delete n ρ))).
  { exact (@cfg_decomp3 ρ i (Thread (k1 (App (Val (BarrierV n)) (Val v1))))
              j (Thread (k2 (App (Val (BarrierV n)) (Val v2)))) n Barrier
              Hij Hin Hjn Hi Hj Hn). }
  rewrite Heq at 1.
  eapply Frame_step with
    (ρ := {[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
            j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
            n := Barrier]})
    (ρ' := {[i := Thread (k1 (Val v2)); j := Thread (k2 (Val v1))]})
    (ρf := delete i (delete j (delete n ρ))) (i := n).
  - exact (@cfg_disj3 ρ i (Thread (k1 (App (Val (BarrierV n)) (Val v1))))
              j (Thread (k2 (App (Val (BarrierV n)) (Val v2)))) n Barrier
              Hij Hin Hjn).
  - assert (HFi : delete i (delete j (delete n ρ)) !! i = None)
      by (apply (lookup_delete_eq (delete j (delete n ρ)) i)).
    assert (HFj : delete i (delete j (delete n ρ)) !! j = None).
    { rewrite (lookup_delete_ne (delete j (delete n ρ)) i j Hij).
      apply (lookup_delete_eq (delete n ρ) j). }
    change (map_disjoint
              (insert i (Thread (k1 (Val v2)))
                 (insert j (Thread (k2 (Val v1))) (∅ : cfg)))
              (delete i (delete j (delete n ρ)))).
    rewrite map_disjoint_insert_l. split; [exact HFi|].
    rewrite map_disjoint_insert_l. split; [exact HFj|]. apply map_disjoint_empty_l.
  - apply (Sync_step i j n k1 k2 v1 v2 Hij Hin Hjn Hk1 Hk2).
Qed.

(* ------------------------------------------------------------------ *)
(* Threads, closed sets, and deadlock freedom                         *)
(* ------------------------------------------------------------------ *)

Definition is_thread (ρ : cfg) (i : nat) : Prop := exists e, ρ !! i = Some (Thread e).

#[global] Instance is_thread_dec (ρ : cfg) (i : nat) : Decision (is_thread ρ i).
Proof.
  unfold is_thread. destruct (ρ !! i) as [[e|]|]; [left; eauto| right; intros [e H]; discriminate
  | right; intros [e H]; discriminate].
Defined.

Definition threads (ρ : cfg) : gset nat := filter (is_thread ρ) (dom ρ).

Lemma elem_of_threads (ρ : cfg) i : i ∈ threads ρ <-> is_thread ρ i.
Proof.
  unfold threads. rewrite elem_of_filter. split.
  - intros [HP _]. exact HP.
  - intros HP. split; [exact HP|]. apply elem_of_dom. destruct HP as (e & H). eexists. exact H.
Qed.

Definition wclosed {ρ : cfg} (ID : nat -> gmap nat type) (IOm : gmap nat (type * type)) (IS : nat -> nat -> bool) (IH1 IH2 : nat -> nat) (S : gset nat) : Prop :=
  forall x, x ∈ S -> exists e j,
    ρ !! x = Some (Thread e) /\ expr_waiting e j /\
    ID x !! j <> None /\ live ρ j /\ IH1 j ∈ S /\ IH2 j ∈ S.

Lemma gset_size_strong_ind (P : gset nat -> Prop) :
  (forall S, (forall T, size T < size S -> P T) -> P S) -> forall S, P S.
Proof.
  intros H S.
  assert (forall n, forall S0, size S0 <= n -> P S0) as Ha.
  { induction n as [|n IH]; intros S0 Hle.
    - apply H. intros T Hlt. assert (H0 : size S0 = 0) by lia. lia.
    - apply H. intros T Hlt. apply IH. lia. }
  apply (Ha (size S) S). lia.
Qed.

Lemma no_deadlock_aux {ρ : cfg} (ID : nat -> gmap nat type) (IOm : gmap nat (type * type)) (IS : nat -> nat -> bool) (IH1 IH2 : nat -> nat) (I : invP ρ ID IOm IS IH1 IH2) (Hnostep : ~ exists i, can_step ρ i) :
  forall S : gset nat, S <> ∅ -> wclosed (ρ:=ρ) ID IOm IS IH1 IH2 S -> False.
Proof.
  apply (@gset_size_strong_ind (fun S => S <> ∅ -> wclosed (ρ:=ρ) ID IOm IS IH1 IH2 S -> False)).
  intros S IH Hne Hcl.
  destruct (size_pos_elem_of S) as (x & Hx).
  { assert (Hsz : size S <> 0).
    { intro Hc. apply Hne.
      exact (leibniz_equiv S ∅ ((proj1 (size_empty_iff S)) Hc)). }
    lia. }
  destruct (Hcl x Hx) as (e & j & Hth & Hw & Hdj & Hlive & Hh1S & Hh2S).
  destruct Hw as (k1 & v1 & Hk1 & He1).
  (* barrier type data *)
  destruct (I.(i_live_iff) j) as [Hf _].
  assert (Home : IOm !! j <> None) by (apply Hf; done).
  destruct (@lookup_some_of_neq (type*type) (IOm) j Home) as ((p & q) & Hom).
  assert (ED1 : ID (IH1 j) !! j = Some p) by exact (I.(i_H1) Hlive Hom).
  assert (ED2 : ID (IH2 j) !! j = Some q) by exact (I.(i_H2) Hlive Hom).
  assert (Hneq12 : IH1 j <> IH2 j) by exact (I.(i_H_neq) Hlive).
  destruct (@lookup_some_of_neq type (ID x) j Hdj) as (tx & Ex).
  destruct (I.(i_H_exact) Hlive Ex) as [X1|X2].
  - (* x = H1 j, y = H2 j *)
    subst x.
    pose (y := IH2 j).
    assert (HyS : y ∈ S) by (unfold y; exact Hh2S).
    assert (Hy_dj : ID y !! j <> None) by (unfold y; rewrite ED2; discriminate).
    assert (Hxy : IH1 j <> y) by (unfold y; exact Hneq12).
    assert (Hside : IS j (IH1 j) <> IS j y).
    { unfold y. apply (I.(i_cut1) Hlive). }
    destruct (Hcl y HyS) as (ey & jy & Hthy & Hwy & Hdy & Hlivey & Hyy1 & Hyy2).
    destruct Hwy as (k2 & v2 & Hk2 & He2).
    destruct (decide (jy = j)) as [Hjy|Hjy].
    + (* y also waits on j : synchronise *)
      exfalso. apply Hnostep. exists j.
      assert (Hxj : IH1 j <> j).
      { intros Hc. rewrite Hc in Hth. unfold live in Hlive. rewrite Hth in Hlive. discriminate. }
      assert (Hyj : y <> j).
      { intros Hc. rewrite Hc in Hthy. unfold live in Hlive. rewrite Hthy in Hlive. discriminate. }
      rewrite Hjy in He2.
      apply (@can_step_sync ρ (IH1 j) y j k1 k2 v1 v2 Hxy Hxj Hyj).
      * rewrite He1 in Hth. exact Hth.
      * rewrite He2 in Hthy. exact Hthy.
      * exact Hlive.
      * exact Hk1.
      * exact Hk2.
    + (* shrink to the side of y *)
      set (B := filter (fun z => IS j z = IS j y) S).
      assert (HBne : B <> ∅).
      { intro Hc.
        assert (HyB : y ∈ B) by (unfold B; rewrite elem_of_filter; split; [done|exact HyS]).
        assert (Hsubsing : ({[y]} : gset nat) ⊆ B).
        { intros z Hz. rewrite elem_of_singleton in Hz. subst z. exact HyB. }
        assert (Hsz0 : size B = 0).
        { rewrite (f_equal size Hc). apply size_empty. }
        pose proof (subseteq_size ({[y]} : gset nat) B Hsubsing) as Hle.
        assert (Hone : size ({[y]} : gset nat) = 1) by apply size_singleton.
        rewrite Hone in Hle. lia. }
      assert (HxB : IH1 j ∉ B).
      { unfold B. rewrite elem_of_filter. intros [Hc _]. apply Hside. exact Hc. }
      assert (HBsub : B ⊂ S).
      { split.
        - intros z Hz. unfold B in Hz. rewrite elem_of_filter in Hz. exact (proj2 Hz).
        - intros Hc. apply HxB. apply Hc. exact Hx. }
      assert (Hsize : size B < size S) by (apply subset_size; exact HBsub).
      apply (IH B Hsize HBne).
      intros z HzB.
      unfold B in HzB. rewrite elem_of_filter in HzB. destruct HzB as [Hzside HzS].
      destruct (Hcl z HzS) as (ez & jz & Hthz & Hwz & Hdz & Hlivez & Hz1 & Hz2).
      destruct Hwz as (kz & vz & Hkz & Hez).
      destruct (decide (jz = j)) as [Hjz|Hjz].
      * (* z waits on j: z is a holder, hence z = y and we can synchronise *)
        exfalso. apply Hnostep. exists j.
        assert (Hdz' : ID z !! j <> None) by (rewrite <- Hjz; exact Hdz).
        assert (Hhd1 : ID (IH1 j) !! j <> None) by (rewrite ED1; discriminate).
        destruct (@inv_holder_eq ρ ID IOm IS IH1 IH2 I j (IH1 j) y z Hlive Hxy Hhd1 Hy_dj Hdz') as [Zx|Zy].
        -- subst z. exfalso. apply HxB. unfold B. rewrite elem_of_filter. split; [exact Hzside|exact HzS].
        -- subst z.
           assert (Hxj : IH1 j <> j).
           { intros Hc. rewrite Hc in Hth. unfold live in Hlive. rewrite Hth in Hlive. discriminate. }
           assert (Hyj : y <> j).
           { intros Hc. rewrite Hc in Hthy. unfold live in Hlive. rewrite Hthy in Hlive. discriminate. }
           rewrite Hjz in Hez.
           apply (@can_step_sync ρ (IH1 j) y j k1 kz v1 vz Hxy Hxj Hyj).
           ++ rewrite He1 in Hth. exact Hth.
           ++ rewrite Hez in Hthz. exact Hthz.
           ++ exact Hlive. ++ exact Hk1. ++ exact Hkz.
      * assert (Hjne : j <> jz) by (intros Hc; apply Hjz; symmetry; exact Hc).
        assert (Hcut2 := I.(i_cut2) Hlive Hlivez Hjne).
        assert (Hdz_holder := @waiting_holds ρ ID IOm IS IH1 IH2 I z ez jz Hthz (ex_intro _ kz (ex_intro _ vz (conj Hkz Hez)))).
        destruct Hdz_holder as [Hzdj Hlivejz].
        destruct (@lookup_some_of_neq type (ID z) jz Hzdj) as (tz & Ez).
        destruct (I.(i_H_exact) Hlivejz Ez) as [Z1|Z2].
        -- (* z = H1 jz *) subst z.
           exists ez, jz. repeat split.
           ++ exact Hthz.
           ++ exists kz, vz. split; [exact Hkz|exact Hez].
           ++ exact Hzdj.
           ++ exact Hlivejz.
           ++ (* H1 jz ∈ B *) unfold B. rewrite elem_of_filter. split; [exact Hzside|exact HzS].
           ++ (* H2 jz ∈ B *) unfold B. rewrite elem_of_filter. split.
              ** rewrite <- Hcut2. rewrite <- Hzside. done.
              ** exact Hz2.
        -- (* z = H2 jz *) subst z.
           exists ez, jz. repeat split.
           ++ exact Hthz.
           ++ exists kz, vz. split; [exact Hkz|exact Hez].
           ++ exact Hzdj.
           ++ exact Hlivejz.
           ++ (* H1 jz ∈ B *) unfold B. rewrite elem_of_filter. split.
              ** rewrite Hcut2. rewrite Hzside. done.
              ** exact Hz1.
           ++ (* H2 jz ∈ B *) unfold B. rewrite elem_of_filter. split; [exact Hzside|exact HzS].
  - (* x = H2 j, y = H1 j : symmetric *)
    subst x.
    pose (y := IH1 j).
    assert (HyS : y ∈ S) by (unfold y; exact Hh1S).
    assert (Hy_dj : ID y !! j <> None) by (unfold y; rewrite ED1; discriminate).
    assert (Hxy : IH2 j <> y) by (unfold y; intros Hc; apply Hneq12; symmetry; exact Hc).
    assert (Hside : IS j (IH2 j) <> IS j y).
    { unfold y. intros Hc. apply (I.(i_cut1) Hlive). symmetry. exact Hc. }
    destruct (Hcl y HyS) as (ey & jy & Hthy & Hwy & Hdy & Hlivey & Hyy1 & Hyy2).
    destruct Hwy as (k2 & v2 & Hk2 & He2).
    destruct (decide (jy = j)) as [Hjy|Hjy].
    + exfalso. apply Hnostep. exists j.
      assert (Hxj : IH2 j <> j).
      { intros Hc. rewrite Hc in Hth. unfold live in Hlive. rewrite Hth in Hlive. discriminate. }
      assert (Hyj : y <> j).
      { intros Hc. rewrite Hc in Hthy. unfold live in Hlive. rewrite Hthy in Hlive. discriminate. }
      rewrite Hjy in He2.
      apply (@can_step_sync ρ (IH2 j) y j k1 k2 v1 v2 Hxy Hxj Hyj).
      * rewrite He1 in Hth. exact Hth.
      * rewrite He2 in Hthy. exact Hthy.
      * exact Hlive. * exact Hk1. * exact Hk2.
    + set (B := filter (fun z => IS j z = IS j y) S).
      assert (HBne : B <> ∅).
      { intro Hc.
        assert (HyB : y ∈ B) by (unfold B; rewrite elem_of_filter; split; [done|exact HyS]).
        assert (Hsubsing : ({[y]} : gset nat) ⊆ B).
        { intros z Hz. rewrite elem_of_singleton in Hz. subst z. exact HyB. }
        assert (Hsz0 : size B = 0).
        { rewrite (f_equal size Hc). apply size_empty. }
        pose proof (subseteq_size ({[y]} : gset nat) B Hsubsing) as Hle.
        assert (Hone : size ({[y]} : gset nat) = 1) by apply size_singleton.
        rewrite Hone in Hle. lia. }
      assert (HxB : IH2 j ∉ B).
      { unfold B. rewrite elem_of_filter. intros [Hc _]. apply Hside. exact Hc. }
      assert (HBsub : B ⊂ S).
      { split.
        - intros z Hz. unfold B in Hz. rewrite elem_of_filter in Hz. exact (proj2 Hz).
        - intros Hc. apply HxB. apply Hc. exact Hx. }
      assert (Hsize : size B < size S) by (apply subset_size; exact HBsub).
      apply (IH B Hsize HBne).
      intros z HzB.
      unfold B in HzB. rewrite elem_of_filter in HzB. destruct HzB as [Hzside HzS].
      destruct (Hcl z HzS) as (ez & jz & Hthz & Hwz & Hdz & Hlivez & Hz1 & Hz2).
      destruct Hwz as (kz & vz & Hkz & Hez).
      destruct (decide (jz = j)) as [Hjz|Hjz].
      * exfalso. apply Hnostep. exists j.
        assert (Hdz' : ID z !! j <> None) by (rewrite <- Hjz; exact Hdz).
        assert (Hhd2 : ID (IH2 j) !! j <> None) by (rewrite ED2; discriminate).
        destruct (@inv_holder_eq ρ ID IOm IS IH1 IH2 I j (IH2 j) y z Hlive Hxy Hhd2 Hy_dj Hdz') as [Zx|Zy].
        -- subst z. exfalso. apply HxB. unfold B. rewrite elem_of_filter. split; [exact Hzside|exact HzS].
        -- subst z.
           assert (Hxj : IH2 j <> j).
           { intros Hc. rewrite Hc in Hth. unfold live in Hlive. rewrite Hth in Hlive. discriminate. }
           assert (Hyj : y <> j).
           { intros Hc. rewrite Hc in Hthy. unfold live in Hlive. rewrite Hthy in Hlive. discriminate. }
           rewrite Hjz in Hez.
           apply (@can_step_sync ρ (IH2 j) y j k1 kz v1 vz Hxy Hxj Hyj).
           ++ rewrite He1 in Hth. exact Hth.
           ++ rewrite Hez in Hthz. exact Hthz.
           ++ exact Hlive. ++ exact Hk1. ++ exact Hkz.
      * assert (Hjne : j <> jz) by (intros Hc; apply Hjz; symmetry; exact Hc).
        assert (Hcut2 := I.(i_cut2) Hlive Hlivez Hjne).
        assert (Hdz_holder := @waiting_holds ρ ID IOm IS IH1 IH2 I z ez jz Hthz (ex_intro _ kz (ex_intro _ vz (conj Hkz Hez)))).
        destruct Hdz_holder as [Hzdj Hlivejz].
        destruct (@lookup_some_of_neq type (ID z) jz Hzdj) as (tz & Ez).
        destruct (I.(i_H_exact) Hlivejz Ez) as [Z1|Z2].
        -- subst z.
           exists ez, jz. repeat split.
           ++ exact Hthz.
           ++ exists kz, vz. split; [exact Hkz|exact Hez].
           ++ exact Hzdj. ++ exact Hlivejz.
           ++ unfold B. rewrite elem_of_filter. split; [exact Hzside|exact HzS].
           ++ unfold B. rewrite elem_of_filter. split.
              ** rewrite <- Hcut2. rewrite <- Hzside. done.
              ** exact Hz2.
        -- subst z.
           exists ez, jz. repeat split.
           ++ exact Hthz.
           ++ exists kz, vz. split; [exact Hkz|exact Hez].
           ++ exact Hzdj. ++ exact Hlivejz.
           ++ unfold B. rewrite elem_of_filter. split.
              ** rewrite Hcut2. rewrite Hzside. done.
              ** exact Hz1.
           ++ unfold B. rewrite elem_of_filter. split; [exact Hzside|exact HzS].
Qed.

Lemma no_step_all_waiting {ρ : cfg} (ID : nat -> gmap nat type) (IOm : gmap nat (type * type)) (IS : nat -> nat -> bool) (IH1 IH2 : nat -> nat) (I : invP ρ ID IOm IS IH1 IH2)
  (Hnostep : ~ exists i, can_step ρ i) :
  forall i e, ρ !! i = Some (Thread e) -> exists j, expr_waiting e j.
Proof.
  intros i e Hth.
  pose proof (I.(i_thr) Hth) as Hrt.
  destruct (@rt_progress ∅ (ID i) e UnitT Hrt eq_refl)
    as [(v & He) | [(k & r & r' & Hk & He & Hps) | [(k & v & Hk & He) | Hw]]].
  - subst e. exfalso. apply Hnostep. exists i.
    exact (@can_step_exit ρ i v Hth).
  - subst e. exfalso. apply Hnostep. exists i.
    exact (@can_step_pure ρ i k r r' Hth Hk Hps).
  - subst e. exfalso. apply Hnostep. exists i.
    exact (@can_step_fork ρ i k v Hth Hk).
  - exact Hw.
Qed.

Lemma threads_nonempty_of_thread {ρ : cfg} (H : exists i e, ρ !! i = Some (Thread e)) :
  threads ρ <> ∅.
Proof.
  intros Hc. destruct H as (i & e & Hi).
  assert (Hmem : i ∈ threads ρ).
  { destruct (elem_of_threads ρ i) as [_ Hg]. apply Hg. exists e. exact Hi. }
  rewrite Hc in Hmem. exact (not_elem_of_empty i Hmem).
Qed.

Lemma global_progress_of_inv {ρ : cfg} (I : inv ρ) : global_progress ρ.
Proof.
  destruct I as (ID & IOm & IS & IH1 & IH2 & I).
  destruct (classic (ρ = ∅)) as [He|Hne].
  - left. intros i. rewrite He.
    destruct ((∅ : cfg) !! i) as [o|] eqn:E; [discriminate|done].
  - right.
    destruct (classic (exists i e, ρ !! i = Some (Thread e))) as [Hthr|Hnothr].
    + destruct (classic (exists i, can_step ρ i)) as [Hc|Hnostep].
      * exact Hc.
      * exfalso.
        assert (Hwait := @no_step_all_waiting ρ ID IOm IS IH1 IH2 I Hnostep).
        assert (Hcl : wclosed (ρ:=ρ) ID IOm IS IH1 IH2 (threads ρ)).
        { intros x Hx.
          destruct (elem_of_threads ρ x) as [Hf _]. destruct (Hf Hx) as (e & Hth).
          destruct (Hwait x e Hth) as (j & Hw).
          destruct (@waiting_holds ρ ID IOm IS IH1 IH2 I x e j Hth Hw) as (Hdj & Hlive).
          destruct (I.(i_live_iff) j) as [Hf2 _].
          assert (Home : IOm !! j <> None) by (apply Hf2; done).
          destruct (@lookup_some_of_neq (type*type) (IOm) j Home) as ((p & q) & Hom).
          assert (Ep : ID (IH1 j) !! j = Some p) by exact (I.(i_H1) Hlive Hom).
          assert (Eq : ID (IH2 j) !! j = Some q) by exact (I.(i_H2) Hlive Hom).
          exists e, j. repeat split.
          - exact Hth. - exact Hw. - exact Hdj. - exact Hlive.
          - destruct (elem_of_threads ρ (IH1 j)) as [_ Hg].
            apply Hg. destruct (@inv_holder_thread ρ ID IOm IS IH1 IH2 I j (IH1 j) Hlive) as (e1 & He1).
            { rewrite Ep. discriminate. }
            exists e1. exact He1.
          - destruct (elem_of_threads ρ (IH2 j)) as [_ Hg].
            apply Hg. destruct (@inv_holder_thread ρ ID IOm IS IH1 IH2 I j (IH2 j) Hlive) as (e2 & He2).
            { rewrite Eq. discriminate. }
            exists e2. exact He2. }
        exact (@no_deadlock_aux ρ ID IOm IS IH1 IH2 I Hnostep (threads ρ) (threads_nonempty_of_thread Hthr) Hcl).
    + exfalso.
      destruct (@map_choose nat (gmap nat) _ _ _ _ _ _ _ _ _ obj ρ Hne) as (k & o & Hk).
      destruct o as [e|].
      * apply Hnothr. exists k, e. exact Hk.
      * (* a live barrier with no threads is impossible *)
        assert (Hlive : live ρ k) by exact Hk.
        destruct (I.(i_live_iff) k) as [Hf _].
        assert (Home : IOm !! k <> None) by (apply Hf; done).
        destruct (@lookup_some_of_neq (type*type) (IOm) k Home) as ((p & q) & Hom).
        assert (Ep : ID (IH1 k) !! k = Some p) by exact (I.(i_H1) Hlive Hom).
        destruct (@inv_holder_thread ρ ID IOm IS IH1 IH2 I k (IH1 k) Hlive) as (e1 & He1).
        { rewrite Ep. discriminate. }
        apply Hnothr. exists (IH1 k), e1. exact He1.
Qed.

(* ------------------------------------------------------------------ *)
(* Preservation of the invariant                                      *)
(* ------------------------------------------------------------------ *)



Lemma rt_val_unit_ctx (D : gmap nat type) (v : val) :
  rt ∅ D (Val v) UnitT -> D = ∅.
Proof.
  intros H. inversion H; subst; clear H.
  exact (rtv_unr H4 unr_UnitT).
Qed.

Lemma rt_ctx_pure k e e' (Δ : gmap nat type) (t : type) :
  ctx k -> rt ∅ Δ (k e) t -> pure_step e e' -> rt ∅ Δ (k e') t.
Proof.
  intros Hk H Hps.
  destruct (@ctx_decomp k Hk e Δ t H) as (Δk & Δh & s & Heq & Hct & Hh).
  rewrite Heq. apply (ct_fill Hct). apply (rt_pure_step Hh Hps).
Qed.

(* ------------------------------------------------------------------ *)
(* Invariant preservation                                             *)
(* ------------------------------------------------------------------ *)

Lemma fork_decomp (D : gmap nat type) k v :
  ctx k -> rt ∅ D (k (Fork (Val v))) UnitT ->
  exists Δk Δh t1 t2, D = Δk ∪ Δh /\
    ctx_typing k Δk Δh (FunT Lin t1 t2) UnitT /\
    rtv Δh v (FunT Lin (FunT Lin t2 t1) UnitT).
Proof.
  intros Hk Hrt.
  destruct (@ctx_decomp k Hk (Fork (Val v)) D UnitT Hrt) as (Δk & Δh & s & Heq & Hct & Hh).
  inversion Hh; subst; clear Hh.
  inversion H2; subst; clear H2.
  exists Δk, Δh, t1, t2. split; [done|]. split; [exact Hct|exact H4].
Qed.

Lemma sync_decomp (D : gmap nat type) k n v :
  ctx k -> rt ∅ D (k (App (Val (BarrierV n)) (Val v))) UnitT ->
  exists Δk Δn Δv a b, D = Δk ∪ (Δn ∪ Δv) /\ Δn ##ₘ Δv /\
    Δn = {[n := FunT Lin a b]} /\
    ctx_typing k Δk (Δn ∪ Δv) b UnitT /\
    rtv Δv v a.
Proof.
  intros Hk Hrt.
  destruct (@ctx_decomp k Hk (App (Val (BarrierV n)) (Val v)) D UnitT Hrt)
    as (Δk & Δh & s & Heq & Hct & Hh).
  inversion Hh; subst; clear Hh.
  destruct (env_split_empty H1 eq_refl) as [E1 E2]. rewrite E1 in H6. rewrite E2 in H8.
  inversion H6; subst; clear H6.
  dependent destruction H5.
  inversion H8; subst; clear H8.
  exists Δk, {[n := FunT Lin t1 s]}, Δ2, t1, s.
  split; [done|]. split; [exact H3|]. split; [done|]. split; [exact Hct|exact H6].
Qed.

Lemma lookup_cfg3_i (i j n : nat) (o1 o2 o3 : obj) :
  ({[i := o1; j := o2; n := o3]} : cfg) !! i = Some o1.
Proof.
  change ((<[i:=o1]>(<[j:=o2]>(<[n:=o3]>(∅:cfg)))) !! i = Some o1).
  apply lookup_insert_eq.
Qed.

Lemma lookup_cfg3_j (i j n : nat) (o1 o2 o3 : obj) (Hij : i <> j) :
  ({[i := o1; j := o2; n := o3]} : cfg) !! j = Some o2.
Proof.
  change ((<[i:=o1]>(<[j:=o2]>(<[n:=o3]>(∅:cfg)))) !! j = Some o2).
  rewrite (lookup_insert_ne (<[j:=o2]>(<[n:=o3]>(∅:cfg))) i j o1 Hij).
  apply lookup_insert_eq.
Qed.

Lemma lookup_cfg3_n (i j n : nat) (o1 o2 o3 : obj) (Hin : i <> n) (Hjn : j <> n) :
  ({[i := o1; j := o2; n := o3]} : cfg) !! n = Some o3.
Proof.
  change ((<[i:=o1]>(<[j:=o2]>(<[n:=o3]>(∅:cfg)))) !! n = Some o3).
  rewrite (lookup_insert_ne (<[j:=o2]>(<[n:=o3]>(∅:cfg))) i n o1 Hin).
  rewrite (lookup_insert_ne (<[n:=o3]>(∅:cfg)) j n o2 Hjn).
  apply lookup_insert_eq.
Qed.

Lemma lookup_cfg3_other (i j n m : nat) (o1 o2 o3 : obj)
  (Hmi : m <> i) (Hmj : m <> j) (Hmn : m <> n) :
  ({[i := o1; j := o2; n := o3]} : cfg) !! m = None.
Proof.
  change ((<[i:=o1]>(<[j:=o2]>(<[n:=o3]>(∅:cfg)))) !! m = None).
  rewrite (lookup_insert_ne (<[j:=o2]>(<[n:=o3]>(∅:cfg))) i m o1 (fun Hc => Hmi (eq_sym Hc))).
  rewrite (lookup_insert_ne (<[n:=o3]>(∅:cfg)) j m o2 (fun Hc => Hmj (eq_sym Hc))).
  rewrite (lookup_insert_ne (∅:cfg) n m o3 (fun Hc => Hmn (eq_sym Hc))).
  done.
Qed.

Lemma lookup_cfg2_i (i j : nat) (o1 o2 : obj) :
  ({[i := o1; j := o2]} : cfg) !! i = Some o1.
Proof.
  change ((<[i:=o1]>(<[j:=o2]>(∅:cfg))) !! i = Some o1). apply lookup_insert_eq.
Qed.

Lemma lookup_cfg2_j (i j : nat) (o1 o2 : obj) (Hij : i <> j) :
  ({[i := o1; j := o2]} : cfg) !! j = Some o2.
Proof.
  change ((<[i:=o1]>(<[j:=o2]>(∅:cfg))) !! j = Some o2).
  rewrite (lookup_insert_ne (<[j:=o2]>(∅:cfg)) i j o1 Hij). apply lookup_insert_eq.
Qed.

Lemma lookup_cfg2_other (i j m : nat) (o1 o2 : obj) (Hmi : m <> i) (Hmj : m <> j) :
  ({[i := o1; j := o2]} : cfg) !! m = None.
Proof.
  change ((<[i:=o1]>(<[j:=o2]>(∅:cfg))) !! m = None).
  rewrite (lookup_insert_ne (<[j:=o2]>(∅:cfg)) i m o1 (fun Hc => Hmi (eq_sym Hc))).
  rewrite (lookup_insert_ne (∅:cfg) j m o2 (fun Hc => Hmj (eq_sym Hc))). done.
Qed.

Lemma inv_local_pure {ρ0 ρ0' ρf : cfg} {i : nat}
  (ID : nat -> gmap nat type) (IOm : gmap nat (type * type)) (IS : nat -> nat -> bool)
  (IH1 IH2 : nat -> nat) (I : invP (ρ0 ∪ ρf) ID IOm IS IH1 IH2) :
  ρ0 ##ₘ ρf -> ρ0' ##ₘ ρf -> local_step i ρ0 ρ0' -> inv (ρ0' ∪ ρf).
Proof.
  intros Hd Hd' Hls. destruct Hls as [i k e e' Hk Hps | i v | i j n k v Hij Hin Hjn Hk | i j n k1 k2 v1 v2 Hij Hin Hjn Hk1 Hk2].
  assert (Hs_i : ({[i := Thread (k e)]} : cfg) !! i = Some (Thread (k e)))
    by apply lookup_singleton_eq.
  assert (Ht_i : ({[i := Thread (k e')]} : cfg) !! i = Some (Thread (k e')))
    by apply lookup_singleton_eq.
  assert (Hsrc_i : (({[i := Thread (k e)]} : cfg) ∪ ρf) !! i = Some (Thread (k e)))
    by (apply lookup_union_Some_l; exact Hs_i).
  assert (Htgt_i : (({[i := Thread (k e')]} : cfg) ∪ ρf) !! i = Some (Thread (k e')))
    by (apply lookup_union_Some_l; exact Ht_i).
  assert (Hoff : forall m, m <> i ->
            (({[i := Thread (k e')]} : cfg) ∪ ρf) !! m
          = (({[i := Thread (k e)]} : cfg) ∪ ρf) !! m).
  { intros m Hm. rewrite (lookup_union_r ({[i:=Thread (k e')]}:cfg) ρf m).
    - rewrite (lookup_union_r ({[i:=Thread (k e)]}:cfg) ρf m).
      + done.
      + apply lookup_singleton_ne. intros Hc; apply Hm; symmetry; exact Hc.
    - apply lookup_singleton_ne. intros Hc; apply Hm; symmetry; exact Hc. }
  assert (Hlive_eq : forall m, live (({[i := Thread (k e')]} : cfg) ∪ ρf) m <-> live (({[i := Thread (k e)]} : cfg) ∪ ρf) m).
  { intros m. destruct (decide (m = i)) as [->|Hm].
    - unfold live. rewrite Htgt_i, Hsrc_i. split; discriminate.
    - unfold live. rewrite Hoff by exact Hm. done. }
  assert (Hnew : rt ∅ (ID i) (k e') UnitT).
  { exact (@rt_ctx_pure k e e' (ID i) UnitT Hk (I.(i_thr) Hsrc_i) Hps). }
  exists ID, IOm, IS, IH1, IH2.
  constructor.
  - intros m e0 Hm. destruct (decide (m = i)) as [->|Hne].
    + rewrite Htgt_i in Hm. injection Hm as He. subst e0. exact Hnew.
    + rewrite (Hoff m Hne) in Hm. exact (I.(i_thr) Hm).
  - intros m Hnt. apply I.(i_nonthr). intros e0 Hc.
    destruct (decide (m = i)) as [->|Hne].
    + exact (Hnt (k e') Htgt_i).
    + apply (Hnt e0). rewrite (Hoff m Hne). exact Hc.
  - intros n. rewrite (Hlive_eq n). apply I.(i_live_iff).
  - exact I.(i_dual).
  - intros n Hl. exact (I.(i_H_neq) ((proj1 (Hlive_eq n)) Hl)).
  - intros n p q Hl Hom. exact (I.(i_H1) ((proj1 (Hlive_eq n)) Hl) Hom).
  - intros n p q Hl Hom. exact (I.(i_H2) ((proj1 (Hlive_eq n)) Hl) Hom).
  - intros n k0 t Hl Hkk. exact (I.(i_H_exact) ((proj1 (Hlive_eq n)) Hl) Hkk).
  - intros n Hl. exact (I.(i_cut1) ((proj1 (Hlive_eq n)) Hl)).
  - intros n m Hln Hlm Hnm.
    exact (I.(i_cut2) ((proj1 (Hlive_eq n)) Hln) ((proj1 (Hlive_eq m)) Hlm) Hnm).
  - exact I.(i_dead).
  - (* Exit *) 
    assert (Hsrc_i : (({[i := Thread (Val v)]} : cfg) ∪ ρf) !! i = Some (Thread (Val v)))
      by (apply lookup_union_Some_l; apply lookup_singleton_eq).
    assert (Hf_i : ρf !! i = None).
    { rewrite map_disjoint_singleton_l in Hd. exact Hd. }
    assert (HDi : ID i = ∅).
    { exact (@rt_val_unit_ctx (ID i) v (I.(i_thr) Hsrc_i)). }
    assert (Htgt_i : ((∅ : cfg) ∪ ρf) !! i = None).
    { rewrite (lookup_union_r (∅:cfg) ρf i) by apply lookup_empty. exact Hf_i. }
    assert (Hoff : forall m, m <> i ->
              ((∅ : cfg) ∪ ρf) !! m = (({[i := Thread (Val v)]} : cfg) ∪ ρf) !! m).
    { intros m Hm. rewrite (lookup_union_r (∅:cfg) ρf m) by apply lookup_empty.
      rewrite (lookup_union_r ({[i:=Thread (Val v)]}:cfg) ρf m).
      - done.
      - apply lookup_singleton_ne. intros Hc; apply Hm; symmetry; exact Hc. }
    assert (Hlive_eq : forall m, live ((∅:cfg) ∪ ρf) m <-> live (({[i := Thread (Val v)]} : cfg) ∪ ρf) m).
    { intros m. destruct (decide (m = i)) as [->|Hm].
      - unfold live. rewrite Htgt_i, Hsrc_i. split; discriminate.
      - unfold live. rewrite Hoff by exact Hm. done. }
    exists ID, IOm, IS, IH1, IH2. constructor.
    + intros m e0 Hm. destruct (decide (m = i)) as [->|Hne].
      * rewrite Htgt_i in Hm. discriminate.
      * rewrite (Hoff m Hne) in Hm. exact (I.(i_thr) Hm).
    + intros m Hnt. destruct (decide (m = i)) as [->|Hne].
      * exact HDi.
      * apply I.(i_nonthr). intros e0 Hc. apply (Hnt e0). rewrite (Hoff m Hne). exact Hc.
    + intros n. rewrite (Hlive_eq n). apply I.(i_live_iff).
    + exact I.(i_dual).
    + intros n Hl. exact (I.(i_H_neq) ((proj1 (Hlive_eq n)) Hl)).
    + intros n p q Hl Hom. exact (I.(i_H1) ((proj1 (Hlive_eq n)) Hl) Hom).
    + intros n p q Hl Hom. exact (I.(i_H2) ((proj1 (Hlive_eq n)) Hl) Hom).
    + intros n k0 t Hl Hkk. exact (I.(i_H_exact) ((proj1 (Hlive_eq n)) Hl) Hkk).
    + intros n Hl. exact (I.(i_cut1) ((proj1 (Hlive_eq n)) Hl)).
    + intros n m Hln Hlm Hnm.
      exact (I.(i_cut2) ((proj1 (Hlive_eq n)) Hln) ((proj1 (Hlive_eq m)) Hlm) Hnm).
    + exact I.(i_dead).
  - (* Fork *)
    assert (Hsrc_i : (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) !! i
                     = Some (Thread (k (Fork (Val v)))))
      by (apply lookup_union_Some_l; apply lookup_singleton_eq).
    destruct (@fork_decomp (ID i) k v Hk (I.(i_thr) Hsrc_i))
      as (Δk & Δh & t1 & t2 & Heq & Hct & Hval).
    set (p := FunT Lin t1 t2). set (q := FunT Lin t2 t1).
    assert (Hfr_i : ρf !! i = None).
    { rewrite map_disjoint_singleton_l in Hd. exact Hd. }
    assert (Hfr_j : ρf !! j = None).
    { change (map_disjoint
        (insert i (Thread (k (Val (BarrierV n))))
           (insert j (Thread (App (Val v) (Val (BarrierV n))))
              (insert n Barrier (∅ : cfg)))) ρf) in Hd'.
      rewrite map_disjoint_insert_l in Hd'. destruct Hd' as [_ Hd'].
      rewrite map_disjoint_insert_l in Hd'. destruct Hd' as [Hj _]. exact Hj. }
    assert (Hfr_n : ρf !! n = None).
    { change (map_disjoint
        (insert i (Thread (k (Val (BarrierV n))))
           (insert j (Thread (App (Val v) (Val (BarrierV n))))
              (insert n Barrier (∅ : cfg)))) ρf) in Hd'.
      rewrite map_disjoint_insert_l in Hd'. destruct Hd' as [_ Hd'].
      rewrite map_disjoint_insert_l in Hd'. destruct Hd' as [_ Hd'].
      rewrite map_disjoint_insert_l in Hd'. destruct Hd' as [Hn _]. exact Hn. }
    assert (Hsrc_n : (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) !! n = None).
    { rewrite (lookup_union_r ({[i := Thread (k (Fork (Val v)))]} : cfg) ρf n).
      - exact Hfr_n.
      - apply lookup_singleton_ne. exact Hin. }
    assert (Hn_nonlive : ~ live (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) n).
    { unfold live. rewrite Hsrc_n. discriminate. }
    assert (Hom_n : IOm !! n = None).
    { destruct (IOm !! n) as [[p0 q0]|] eqn:E; [|done].
      exfalso. apply Hn_nonlive. destruct (I.(i_live_iff) n) as [_ Hg].
      apply Hg. rewrite E. discriminate. }
    assert (HIDi_n : ID i !! n = None).
    { destruct (ID i !! n) as [t|] eqn:E; [|done].
      exfalso. exact (I.(i_dead) Hom_n E). }
    assert (Hdk_n : Δk !! n = None).
    { destruct (Δk !! n) as [t|] eqn:E; [|done].
      exfalso. rewrite Heq in HIDi_n.
      rewrite (lookup_union_Some_l Δk Δh n t E) in HIDi_n. discriminate. }
    assert (Hdh_n : Δh !! n = None).
    { destruct (Δh !! n) as [t|] eqn:E; [|done].
      exfalso. rewrite Heq in HIDi_n.
      rewrite (lookup_union_r Δk Δh n Hdk_n) in HIDi_n. rewrite E in HIDi_n. discriminate. }
    assert (Hpar : rt ∅ (Δk ∪ {[n := p]}) (k (Val (BarrierV n))) UnitT).
    { apply (ct_fill_any Hct).
      - rewrite map_disjoint_singleton_r. exact Hdk_n.
      - apply rt_Val.
        + apply env_unr_empty.
        + apply rtv_Barrier. unfold p. done. }
    assert (Hchild : rt ∅ (Δh ∪ {[n := q]}) (App (Val v) (Val (BarrierV n))) UnitT).
    { eapply rt_App with (Γ1:=∅)(Γ2:=∅)(Δ:=Δh∪{[n:=q]})(Δ1:=Δh)(Δ2:={[n:=q]})
                         (e1:=Val v)(e2:=Val (BarrierV n))(t1:=q)(t2:=UnitT)(l:=Lin).
      - apply env_split_nil.
      - done.
      - rewrite map_disjoint_singleton_r. exact Hdh_n.
      - apply rt_Val. apply env_unr_empty. exact Hval.
      - apply rt_Val. apply env_unr_empty. apply rtv_Barrier. unfold q. done. }
    assert (Hsrc_j : (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) !! j = None).
    { rewrite (lookup_union_r ({[i := Thread (k (Fork (Val v)))]} : cfg) ρf j).
      - exact Hfr_j.
      - apply lookup_singleton_ne. intros Hc2. exact (Hij Hc2). }
    assert (HIDj : ID j = ∅).
    { apply I.(i_nonthr). intros e0 Hc. rewrite Hsrc_j in Hc. discriminate. }
    assert (HIDj_none : forall m, ID j !! m = None).
    { intros m. rewrite HIDj. apply lookup_empty. }
    assert (HIDn_all : forall k, ID k !! n = None).
    { intros k0. destruct (ID k0 !! n) as [t|] eqn:E; [|done].
      exfalso. exact (I.(i_dead) Hom_n E). }
    assert (HIDk : forall x u, Δk !! x = Some u -> ID i !! x = Some u).
    { intros x u E. rewrite Heq. apply lookup_union_Some_l. exact E. }
    assert (HIDh : forall x u, Δh !! x = Some u -> ID i !! x = Some u).
    { intros x u E. rewrite Heq. apply lookup_union_Some_r.
      - exact (ct_disj Hct).
      - exact E. }
    assert (Hpart : forall x t, ID i !! x = Some t ->
        (Δk !! x = Some t /\ Δh !! x = None) \/
        (Δk !! x = None /\ Δh !! x = Some t)).
    { intros x t HID. rewrite Heq in HID.
      pose proof (proj1 (lookup_union_Some_raw Δk Δh x t) HID) as H.
      destruct H as [Ek|[Ek Eh]].
      - left. split; [exact Ek|].
        exact (map_disjoint_Some_l Δk Δh x t (ct_disj Hct) Ek).
      - right. split; [exact Ek|exact Eh]. }
    assert (Hti : (({[i := Thread (k (Val (BarrierV n)));
                      j := Thread (App (Val v) (Val (BarrierV n)));
                      n := Barrier]} : cfg) ∪ ρf) !! i = Some (Thread (k (Val (BarrierV n))))).
    { apply lookup_union_Some_l. apply lookup_cfg3_i. }
    assert (Htj : (({[i := Thread (k (Val (BarrierV n)));
                      j := Thread (App (Val v) (Val (BarrierV n)));
                      n := Barrier]} : cfg) ∪ ρf) !! j
                = Some (Thread (App (Val v) (Val (BarrierV n))))).
    { apply lookup_union_Some_l. apply lookup_cfg3_j. exact Hij. }
    assert (Htn : (({[i := Thread (k (Val (BarrierV n)));
                      j := Thread (App (Val v) (Val (BarrierV n)));
                      n := Barrier]} : cfg) ∪ ρf) !! n = Some Barrier).
    { apply lookup_union_Some_l. apply lookup_cfg3_n; [exact Hin|exact Hjn]. }
    assert (Hoff : forall m, m <> i -> m <> j -> m <> n ->
              (({[i := Thread (k (Val (BarrierV n)));
                  j := Thread (App (Val v) (Val (BarrierV n)));
                  n := Barrier]} : cfg) ∪ ρf) !! m
            = (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) !! m).
    { intros m0 Hmi Hmj Hmn.
      rewrite (lookup_union_r ({[i := Thread (k (Val (BarrierV n)));
                  j := Thread (App (Val v) (Val (BarrierV n)));
                  n := Barrier]} : cfg) ρf m0)
        by (apply lookup_cfg3_other; assumption).
      rewrite (lookup_union_r ({[i := Thread (k (Fork (Val v)))]} : cfg) ρf m0)
        by (apply lookup_singleton_ne; intros Hc; apply Hmi; symmetry; exact Hc).
      done. }
    assert (Hlive_neqn : forall m, m <> n ->
        live (({[i := Thread (k (Val (BarrierV n)));
                 j := Thread (App (Val v) (Val (BarrierV n)));
                 n := Barrier]} : cfg) ∪ ρf) m ->
        live (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) m).
    { intros m Hmn Hl. destruct (decide (m = i)) as [->|Hmi].
      - unfold live in Hl. rewrite Hti in Hl. discriminate.
      - destruct (decide (m = j)) as [->|Hmj].
        + unfold live in Hl. rewrite Htj in Hl. discriminate.
        + unfold live. rewrite <- (Hoff m Hmi Hmj Hmn). unfold live in Hl. exact Hl. }
    assert (Hsrc_mi : forall m, live (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) m -> m <> i).
    { intros m Hl Hc. rewrite Hc in Hl. unfold live in Hl. rewrite Hsrc_i in Hl. discriminate. }
    assert (Hsrc_mj : forall m, live (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) m -> m <> j).
    { intros m Hl Hc. rewrite Hc in Hl. unfold live in Hl. rewrite Hsrc_j in Hl. discriminate. }
    assert (Hdh_live : forall x, Δh !! x <> None ->
        live (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) x).
    { intros x Hx. destruct (Δh !! x) as [u|] eqn:E; [|done].
      apply (@inv_live_of_holder _ ID IOm IS IH1 IH2 I x i).
      rewrite (HIDh x u E). discriminate. }
    set (D' := fun m => if decide (m = i) then Δk ∪ {[n := p]}
                        else if decide (m = j) then Δh ∪ {[n := q]} else ID m).
    set (Om' := <[n := (p, q)]> IOm).
    set (S' := fun m t => if decide (m = n) then
                            (if decide (t = j) then true else
                             anyb (elements (dom Δh))
                               (fun m0 => if decide (IS m0 t = IS m0 i) then false else true))
                          else if decide (t = j) then IS m i else IS m t).
    set (H1' := fun m => if decide (m = n) then i
                         else if decide (IH1 m = i) then (if decide (Δk !! m = None) then j else IH1 m)
                         else IH1 m).
    set (H2' := fun m => if decide (m = n) then j
                         else if decide (IH2 m = i) then (if decide (Δk !! m = None) then j else IH2 m)
                         else IH2 m).
    assert (Hholders : forall m,
        live (({[i := Thread (k (Val (BarrierV n)));
                 j := Thread (App (Val v) (Val (BarrierV n)));
                 n := Barrier]} : cfg) ∪ ρf) m -> m <> n ->
        (IH1 m = i /\ Δk !! m <> None /\ H1' m = i /\ H2' m = IH2 m) \/
        (IH1 m = i /\ Δk !! m = None /\ H1' m = j /\ H2' m = IH2 m) \/
        (IH2 m = i /\ Δk !! m <> None /\ H2' m = i /\ H1' m = IH1 m) \/
        (IH2 m = i /\ Δk !! m = None /\ H2' m = j /\ H1' m = IH1 m) \/
        (ID i !! m = None /\ H1' m = IH1 m /\ H2' m = IH2 m)).
    { intros m Hl Hmn.
      assert (Hls := Hlive_neqn m Hmn Hl).
      assert (HomS : IOm !! m <> None) by (apply (proj1 (I.(i_live_iff) m) Hls)).
      destruct (IOm !! m) as [[pm qm]|] eqn:HOm; [|exfalso; apply HomS; done].
      assert (E1 := I.(i_H1) Hls HOm).
      assert (E2 := I.(i_H2) Hls HOm).
      assert (Hneq12 := I.(i_H_neq) Hls).
      destruct (ID i !! m) as [tm|] eqn:Ei.
      - destruct (I.(i_H_exact) Hls Ei) as [Ai|Ai].
        + assert (Ais : IH1 m = i) by (symmetry; exact Ai).
          destruct (Δk !! m) as [u|] eqn:Ek.
          * left. split; [exact Ais|]. split; [done|]. split.
            -- unfold H1'. rewrite decide_False by exact Hmn. rewrite decide_True by exact Ais.
               rewrite decide_False by (intro Hc; rewrite Hc in Ek; discriminate Ek). done.
            -- unfold H2'. rewrite decide_False by exact Hmn. rewrite decide_False by (intros Hc; apply Hneq12; rewrite Ais, Hc; done). done.
          * right; left. split; [exact Ais|]. split; [done|]. split.
            -- unfold H1'. rewrite decide_False by exact Hmn. rewrite decide_True by exact Ais.
               rewrite decide_True by done. done.
            -- unfold H2'. rewrite decide_False by exact Hmn. rewrite decide_False by (intros Hc; apply Hneq12; rewrite Ais, Hc; done). done.
        + assert (Ais : IH2 m = i) by (symmetry; exact Ai).
          destruct (Δk !! m) as [u|] eqn:Ek.
          * right; right; left. split; [exact Ais|]. split; [done|]. split.
            -- unfold H2'. rewrite decide_False by exact Hmn. rewrite decide_True by exact Ais.
               rewrite decide_False by (intro Hc; rewrite Hc in Ek; discriminate Ek). done.
            -- unfold H1'. rewrite decide_False by exact Hmn. rewrite decide_False by (intros Hc; apply Hneq12; rewrite Hc, Ais; done). done.
          * right; right; right; left. split; [exact Ais|]. split; [done|]. split.
            -- unfold H2'. rewrite decide_False by exact Hmn. rewrite decide_True by exact Ais.
               rewrite decide_True by done. done.
            -- unfold H1'. rewrite decide_False by exact Hmn. rewrite decide_False by (intros Hc; apply Hneq12; rewrite Hc, Ais; done). done.
      - right; right; right; right. split; [done|]. split.
        + unfold H1'. rewrite decide_False by exact Hmn. rewrite decide_False by (intros Hc; rewrite Hc in E1; rewrite Ei in E1; discriminate E1). done.
        + unfold H2'. rewrite decide_False by exact Hmn. rewrite decide_False by (intros Hc; rewrite Hc in E2; rewrite Ei in E2; discriminate E2). done. }
    assert (HD'i : D' i = Δk ∪ {[n := p]}).
    { unfold D'. rewrite decide_True by done. done. }
    assert (HD'j : D' j = Δh ∪ {[n := q]}).
    { unfold D'. rewrite decide_False by (intros Hc; exact (Hij (eq_sym Hc))).
      rewrite decide_True by done. done. }
    assert (HD'k : forall k, k <> i -> k <> j -> D' k = ID k).
    { intros k0 Hki Hkj. unfold D'.
      rewrite decide_False by exact Hki. rewrite decide_False by exact Hkj. done. }
    exists D', Om', S', H1', H2'. constructor.
    + intros m e0 Hm.
      destruct (decide (m = i)) as [->|Hmi].
      * rewrite Hti in Hm. injection Hm as He. subst e0.
        unfold D'. rewrite decide_True by done. exact Hpar.
      * destruct (decide (m = j)) as [->|Hmj].
        -- rewrite Htj in Hm. injection Hm as He. subst e0.
           unfold D'. rewrite decide_False by done. rewrite decide_True by done. exact Hchild.
        -- destruct (decide (m = n)) as [->|Hmn].
           ++ rewrite Htn in Hm. inversion Hm.
           ++ rewrite (Hoff m Hmi Hmj Hmn) in Hm.
              unfold D'. rewrite decide_False by done. rewrite decide_False by done.
              exact (I.(i_thr) Hm).
    + intros m Hnt.
      destruct (decide (m = i)) as [->|Hmi].
      * exfalso. apply (Hnt (k (Val (BarrierV n)))). exact Hti.
      * destruct (decide (m = j)) as [->|Hmj].
        -- exfalso. apply (Hnt (App (Val v) (Val (BarrierV n)))). exact Htj.
        -- destruct (decide (m = n)) as [->|Hmn].
           ++ unfold D'. rewrite decide_False by done. rewrite decide_False by done.
              apply I.(i_nonthr). intros e0 Hc. rewrite Hsrc_n in Hc. discriminate.
           ++ unfold D'. rewrite decide_False by done. rewrite decide_False by done.
              apply I.(i_nonthr). intros e0 Hc. apply (Hnt e0). rewrite (Hoff m Hmi Hmj Hmn). exact Hc.
    + intros m. unfold live. unfold Om'.
      destruct (decide (m = i)) as [->|Hmi].
      * rewrite Hti. rewrite (lookup_insert_ne IOm n i (p,q)) by (intros Hc; apply Hin; symmetry; exact Hc).
        assert (Hs : ~ live (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) i)
          by (unfold live; rewrite Hsrc_i; intros Hc; discriminate Hc).
        destruct (I.(i_live_iff) i) as [Hf Hg].
        split.
        -- intros Hc. discriminate Hc.
        -- intros Hc. exfalso. apply Hs. apply Hg. exact Hc.
      * destruct (decide (m = j)) as [->|Hmj].
        -- rewrite Htj. rewrite (lookup_insert_ne IOm n j (p,q)) by (intros Hc; apply Hjn; symmetry; exact Hc).
           assert (Hs : ~ live (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) j).
           { intros Hc. unfold live in Hc.
             assert (Hlook : (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) !! j = ρf !! j).
             { apply lookup_union_r. apply lookup_singleton_ne. intros Hc2. exact (Hij Hc2). }
             rewrite Hlook in Hc. rewrite Hfr_j in Hc. discriminate Hc. }
           destruct (I.(i_live_iff) j) as [Hf Hg].
           split.
           ++ intros Hc. discriminate Hc.
           ++ intros Hc. exfalso. apply Hs. apply Hg. exact Hc.
        -- destruct (decide (m = n)) as [->|Hmn].
           ++ rewrite Htn. rewrite (lookup_insert_eq IOm n (p,q)). split; [intros _|intros _]; done.
           ++ rewrite (Hoff m Hmi Hmj Hmn).
              rewrite (lookup_insert_ne IOm n m (p,q)) by (intros Hc; apply Hmn; symmetry; exact Hc).
              apply I.(i_live_iff).
    + intros m p0 q0 Hom. unfold Om' in Hom.
      destruct (decide (m = n)) as [->|Hmn].
      * rewrite (lookup_insert_eq IOm n (p,q)) in Hom. injection Hom as <- <-.
        unfold p. unfold q. rewrite dual_FunT. reflexivity.
      * rewrite (lookup_insert_ne IOm n m (p,q)) in Hom
          by (intros Hc; apply Hmn; symmetry; exact Hc).
        unfold p. unfold q. exact (I.(i_dual) Hom).
    + intros m Hl.
      destruct (decide (m = n)) as [->|Hmn].
      * assert (H1n : H1' n = i) by (unfold H1'; rewrite decide_True by done; done).
        assert (H2n : H2' n = j) by (unfold H2'; rewrite decide_True by done; done).
        rewrite H1n, H2n. exact Hij.
      * assert (Hls := Hlive_neqn m Hmn Hl).
        assert (HomS : IOm !! m <> None) by (apply (proj1 (I.(i_live_iff) m) Hls)).
        destruct (IOm !! m) as [[pm qm]|] eqn:HOm; [|exfalso; apply HomS; done].
        assert (E1 := I.(i_H1) Hls HOm). assert (E2 := I.(i_H2) Hls HOm).
        assert (Hneq12 := I.(i_H_neq) Hls).
        assert (HjE1 : IH1 m <> j) by (intro Hc; rewrite Hc in E1; rewrite HIDj_none in E1; discriminate E1).
        assert (HjE2 : IH2 m <> j) by (intro Hc; rewrite Hc in E2; rewrite HIDj_none in E2; discriminate E2).
        destruct (Hholders m Hl Hmn) as
          [(Ai & _ & H1e & H2e)|[(Ai & _ & H1e & H2e)|[(Ai & _ & H1e & H2e)|[(Ai & _ & H1e & H2e)|(_ & H1e & H2e)]]]].
        -- rewrite H1e, H2e. intro Hc. apply Hneq12. rewrite Ai. exact Hc.
        -- rewrite H1e, H2e. intro Hc. rewrite <- Hc in E2. rewrite HIDj_none in E2. discriminate E2.
        -- rewrite H1e, H2e. intro Hc. apply Hneq12. rewrite Hc, Ai. done.
        -- rewrite H1e, H2e. intro Hc. rewrite Hc in E1. rewrite HIDj_none in E1. discriminate E1.
        -- rewrite H1e, H2e. exact Hneq12.
    + intros m p0 q0 Hl Hom.
      destruct (decide (m = n)) as [->|Hmn].
      * assert (H1n : H1' n = i) by (unfold H1'; rewrite decide_True by done; done).
        rewrite H1n.
        assert (Homn : Om' !! n = Some (p, q)) by (unfold Om'; apply lookup_insert_eq).
        rewrite Homn in Hom. injection Hom as <- <-.
        rewrite HD'i. rewrite (lookup_union_r Δk {[n := p]} n Hdk_n).
        apply lookup_singleton_eq.
      * assert (Hls := Hlive_neqn m Hmn Hl).
        assert (Hom' : Om' !! m = IOm !! m)
          by (unfold Om'; apply lookup_insert_ne; intros Hc; exact (Hmn (eq_sym Hc))).
        rewrite Hom' in Hom.
        assert (E1 := I.(i_H1) Hls Hom). assert (E2 := I.(i_H2) Hls Hom).
        assert (Hneq12 := I.(i_H_neq) Hls).
        assert (HjE1 : IH1 m <> j) by (intro Hc; rewrite Hc in E1; rewrite HIDj_none in E1; discriminate E1).
        assert (Hn_single : ({[n := p]} : gmap nat type) !! m = None)
          by (apply lookup_singleton_ne; intros Hc; apply Hmn; symmetry; exact Hc).
        destruct (Hholders m Hl Hmn) as
          [(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|[(Ai & _ & H1e & H2e)|[(Ai & _ & H1e & H2e)|(Ei & H1e & H2e)]]]].
        -- rewrite H1e. rewrite HD'i.
           rewrite (lookup_union_l Δk {[n := p]} m) by (apply lookup_singleton_ne; intros Hc; apply Hmn; symmetry; exact Hc).
           destruct (Δk !! m) as [u|] eqn:Eku; [|exfalso; apply Ek; done].
           assert (Hu : u = p0) by (rewrite Ai in E1; rewrite (HIDk m u Eku) in E1; injection E1; done).
           subst u. done.
        -- rewrite H1e. rewrite HD'j.
           assert (HdhE : Δh !! m = Some p0).
           { rewrite Ai in E1. rewrite Heq in E1.
             rewrite (lookup_union_r Δk Δh m Ek) in E1. exact E1. }
           rewrite (lookup_union_l Δh {[n := q]} m)
             by (apply lookup_singleton_ne; intros Hc; apply Hmn; symmetry; exact Hc).
           exact HdhE.
        -- rewrite H2e. rewrite (HD'k (IH1 m)).
           ++ exact E1.
           ++ intro Hc. apply Hneq12. rewrite Hc, Ai. done.
           ++ exact HjE1.
        -- rewrite H2e. rewrite (HD'k (IH1 m)).
           ++ exact E1.
           ++ intro Hc. apply Hneq12. rewrite Hc, Ai. done.
           ++ exact HjE1.
        -- rewrite H1e. rewrite (HD'k (IH1 m)).
           ++ exact E1.
           ++ intro Hc. rewrite Hc in E1. rewrite Ei in E1. discriminate E1.
           ++ exact HjE1.
    + intros m p0 q0 Hl Hom.
      destruct (decide (m = n)) as [->|Hmn].
      * assert (H2n : H2' n = j) by (unfold H2'; rewrite decide_True by done; done).
        rewrite H2n.
        assert (Homn : Om' !! n = Some (p, q)) by (unfold Om'; apply lookup_insert_eq).
        rewrite Homn in Hom. injection Hom as <- <-.
        rewrite HD'j. rewrite (lookup_union_r Δh {[n := q]} n Hdh_n).
        apply lookup_singleton_eq.
      * assert (Hls := Hlive_neqn m Hmn Hl).
        assert (Hom' : Om' !! m = IOm !! m)
          by (unfold Om'; apply lookup_insert_ne; intros Hc; exact (Hmn (eq_sym Hc))).
        rewrite Hom' in Hom.
        assert (E1 := I.(i_H1) Hls Hom). assert (E2 := I.(i_H2) Hls Hom).
        assert (Hneq12 := I.(i_H_neq) Hls).
        assert (HjE2 : IH2 m <> j) by (intro Hc; rewrite Hc in E2; rewrite HIDj_none in E2; discriminate E2).
        assert (Hn_single : ({[n := q]} : gmap nat type) !! m = None)
          by (apply lookup_singleton_ne; intros Hc; apply Hmn; symmetry; exact Hc).
        destruct (Hholders m Hl Hmn) as
          [(Ai & _ & H1e & H2e)|[(Ai & _ & H1e & H2e)|[(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|(Ei & H1e & H2e)]]]].
        -- rewrite H2e. rewrite (HD'k (IH2 m)).
           ++ exact E2.
           ++ intro Hc. apply Hneq12. rewrite Ai, Hc. done.
           ++ exact HjE2.
        -- rewrite H2e. rewrite (HD'k (IH2 m)).
           ++ exact E2.
           ++ intro Hc. apply Hneq12. rewrite Ai, Hc. done.
           ++ exact HjE2.
        -- rewrite H1e. rewrite HD'i.
           rewrite (lookup_union_l Δk {[n := p]} m) by (apply lookup_singleton_ne; intros Hc; apply Hmn; symmetry; exact Hc).
           destruct (Δk !! m) as [u|] eqn:Eku; [|exfalso; apply Ek; done].
           assert (Hu : u = q0) by (rewrite Ai in E2; rewrite (HIDk m u Eku) in E2; injection E2; done).
           subst u. done.
        -- rewrite H1e. rewrite HD'j.
           assert (HdhE : Δh !! m = Some q0).
           { rewrite Ai in E2. rewrite Heq in E2.
             rewrite (lookup_union_r Δk Δh m Ek) in E2. exact E2. }
           rewrite (lookup_union_l Δh {[n := q]} m)
             by (apply lookup_singleton_ne; intros Hc; apply Hmn; symmetry; exact Hc).
           exact HdhE.
        -- rewrite H2e. rewrite (HD'k (IH2 m)).
           ++ exact E2.
           ++ intro Hc. rewrite Hc in E2. rewrite Ei in E2. discriminate E2.
           ++ exact HjE2.
    + intros m k0 t Hl Hdk.
      destruct (decide (m = n)) as [->|Hmn].
      * assert (H1n : H1' n = i) by (unfold H1'; rewrite decide_True by done; done).
        assert (H2n : H2' n = j) by (unfold H2'; rewrite decide_True by done; done).
        rewrite H1n, H2n.
        destruct (decide (k0 = i)) as [->|Hki]; [left; done|].
        destruct (decide (k0 = j)) as [->|Hkj]; [right; done|].
        exfalso. rewrite (HD'k k0 Hki Hkj) in Hdk.
        rewrite (HIDn_all k0) in Hdk. discriminate Hdk.
      * assert (Hls := Hlive_neqn m Hmn Hl).
        assert (HomS : IOm !! m <> None) by (apply (proj1 (I.(i_live_iff) m) Hls)).
        destruct (IOm !! m) as [[pm qm]|] eqn:HOm; [|exfalso; apply HomS; done].
        assert (E1 := I.(i_H1) Hls HOm). assert (E2 := I.(i_H2) Hls HOm).
        assert (Hneq12 := I.(i_H_neq) Hls).
        assert (HjE1 : IH1 m <> j) by (intro Hc; rewrite Hc in E1; rewrite HIDj_none in E1; discriminate E1).
        assert (HjE2 : IH2 m <> j) by (intro Hc; rewrite Hc in E2; rewrite HIDj_none in E2; discriminate E2).
        assert (Hn_p : ({[n := p]} : gmap nat type) !! m = None)
          by (apply lookup_singleton_ne; intros Hc; apply Hmn; symmetry; exact Hc).
        assert (Hn_q : ({[n := q]} : gmap nat type) !! m = None)
          by (apply lookup_singleton_ne; intros Hc; apply Hmn; symmetry; exact Hc).
        destruct (Hholders m Hl Hmn) as
          [(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|(Ei & H1e & H2e)]]]].
        -- rewrite H1e, H2e.
           destruct (decide (k0 = i)) as [->|Hki]; [left; done|].
           destruct (decide (k0 = j)) as [->|Hkj]; [exfalso|].
           ++ rewrite HD'j in Hdk. rewrite (lookup_union_l Δh {[n := q]} m Hn_q) in Hdk.
              destruct (Δk !! m) as [u|] eqn:Eku; [|exfalso; apply Ek; done].
              rewrite (map_disjoint_Some_l Δk Δh m u (ct_disj Hct) Eku) in Hdk.
              discriminate Hdk.
           ++ rewrite (HD'k k0 Hki Hkj) in Hdk.
              destruct (I.(i_H_exact) Hls Hdk) as [Hc|Hc]; [left; rewrite Hc, Ai; done|right; exact Hc].
        -- rewrite H1e, H2e.
           destruct (decide (k0 = j)) as [->|Hkj]; [left; done|].
           destruct (decide (k0 = i)) as [->|Hki]; [exfalso|].
           ++ rewrite HD'i in Hdk. rewrite (lookup_union_l Δk {[n := p]} m Hn_p) in Hdk.
              rewrite Ek in Hdk. discriminate Hdk.
           ++ rewrite (HD'k k0 Hki Hkj) in Hdk.
              destruct (I.(i_H_exact) Hls Hdk) as [Hc|Hc].
              ** exfalso. apply Hki. rewrite Hc, Ai. done.
              ** right. exact Hc.
        -- rewrite H1e, H2e.
           destruct (decide (k0 = i)) as [->|Hki]; [right; done|].
           destruct (decide (k0 = j)) as [->|Hkj]; [exfalso|].
           ++ rewrite HD'j in Hdk. rewrite (lookup_union_l Δh {[n := q]} m Hn_q) in Hdk.
              destruct (Δk !! m) as [u|] eqn:Eku; [|exfalso; apply Ek; done].
              rewrite (map_disjoint_Some_l Δk Δh m u (ct_disj Hct) Eku) in Hdk.
              discriminate Hdk.
           ++ rewrite (HD'k k0 Hki Hkj) in Hdk.
              destruct (I.(i_H_exact) Hls Hdk) as [Hc|Hc].
              ** left. exact Hc.
              ** right. rewrite Hc, Ai. done.
        -- rewrite H1e, H2e.
           destruct (decide (k0 = j)) as [->|Hkj]; [right; done|].
           destruct (decide (k0 = i)) as [->|Hki]; [exfalso|].
           ++ rewrite HD'i in Hdk. rewrite (lookup_union_l Δk {[n := p]} m Hn_p) in Hdk.
              rewrite Ek in Hdk. discriminate Hdk.
           ++ rewrite (HD'k k0 Hki Hkj) in Hdk.
              destruct (I.(i_H_exact) Hls Hdk) as [Hc|Hc].
              ** left. exact Hc.
              ** exfalso. apply Hki. rewrite Hc, Ai. done.
        -- rewrite H1e, H2e.
           destruct (decide (k0 = i)) as [->|Hki].
           ++ exfalso. rewrite HD'i in Hdk.
              rewrite (lookup_union_l Δk {[n := p]} m Hn_p) in Hdk.
              assert (HIDi : ID i !! m = Some t)
                by (rewrite Heq; apply lookup_union_Some_l; exact Hdk).
              rewrite Ei in HIDi. discriminate HIDi.
           ++ destruct (decide (k0 = j)) as [->|Hkj].
              ** exfalso. rewrite HD'j in Hdk.
                 rewrite (lookup_union_l Δh {[n := q]} m Hn_q) in Hdk.
                 assert (HIDi : ID i !! m = Some t)
                   by (rewrite Heq; apply lookup_union_Some_r; [exact (ct_disj Hct)|exact Hdk]).
                 rewrite Ei in HIDi. discriminate HIDi.
              ** rewrite (HD'k k0 Hki Hkj) in Hdk.
                 destruct (I.(i_H_exact) Hls Hdk) as [Hc|Hc]; [left; exact Hc|right; exact Hc].
    + intros m Hl.
      destruct (decide (m = n)) as [->|Hmn].
      * assert (H1n : H1' n = i) by (unfold H1'; rewrite decide_True by done; done).
        assert (H2n : H2' n = j) by (unfold H2'; rewrite decide_True by done; done).
        rewrite H1n, H2n.
        assert (HSi : S' n i = false).
        { unfold S'. rewrite decide_True by done. rewrite decide_False by exact Hij.
          apply anyb_false. intros x Hx. rewrite decide_True by done. done. }
        assert (HSj : S' n j = true).
        { unfold S'. rewrite decide_True by done. rewrite decide_True by done. done. }
        rewrite HSi, HSj. intro Hc. discriminate Hc.
      * assert (Hls := Hlive_neqn m Hmn Hl).
        assert (HomS : IOm !! m <> None) by (apply (proj1 (I.(i_live_iff) m) Hls)).
        destruct (IOm !! m) as [[pm qm]|] eqn:HOm; [|exfalso; apply HomS; done].
        assert (E1 := I.(i_H1) Hls HOm). assert (E2 := I.(i_H2) Hls HOm).
        assert (Hneq12 := I.(i_H_neq) Hls).
        assert (HjE1 : IH1 m <> j) by (intro Hc; rewrite Hc in E1; rewrite HIDj_none in E1; discriminate E1).
        assert (HjE2 : IH2 m <> j) by (intro Hc; rewrite Hc in E2; rewrite HIDj_none in E2; discriminate E2).
        destruct (Hholders m Hl Hmn) as
          [(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|(_ & H1e & H2e)]]]].
        -- rewrite H1e, H2e.
           assert (Hsi : S' m i = IS m i)
             by (unfold S'; rewrite decide_False by exact Hmn; rewrite decide_False by exact Hij; done).
           assert (Hsh : S' m (IH2 m) = IS m (IH2 m))
             by (unfold S'; rewrite decide_False by exact Hmn; rewrite decide_False by exact HjE2; done).
           rewrite Hsi, Hsh. intro Hc. apply (I.(i_cut1) Hls). rewrite Ai. exact Hc.
        -- rewrite H1e, H2e.
           assert (Hsj : S' m j = IS m i)
             by (unfold S'; rewrite decide_False by exact Hmn; rewrite decide_True by done; done).
           assert (Hsh : S' m (IH2 m) = IS m (IH2 m))
             by (unfold S'; rewrite decide_False by exact Hmn; rewrite decide_False by exact HjE2; done).
           rewrite Hsj, Hsh. intro Hc. apply (I.(i_cut1) Hls). rewrite Ai. exact Hc.
        -- rewrite H1e, H2e.
           assert (Hsh : S' m (IH1 m) = IS m (IH1 m))
             by (unfold S'; rewrite decide_False by exact Hmn; rewrite decide_False by exact HjE1; done).
           assert (Hsi : S' m i = IS m i)
             by (unfold S'; rewrite decide_False by exact Hmn; rewrite decide_False by exact Hij; done).
           rewrite Hsh, Hsi. intro Hc. apply (I.(i_cut1) Hls). rewrite Ai. exact Hc.
        -- rewrite H1e, H2e.
           assert (Hsh : S' m (IH1 m) = IS m (IH1 m))
             by (unfold S'; rewrite decide_False by exact Hmn; rewrite decide_False by exact HjE1; done).
           assert (Hsj : S' m j = IS m i)
             by (unfold S'; rewrite decide_False by exact Hmn; rewrite decide_True by done; done).
           rewrite Hsh, Hsj. intro Hc. apply (I.(i_cut1) Hls). rewrite Ai. exact Hc.
        -- rewrite H1e, H2e.
           assert (Hsh1 : S' m (IH1 m) = IS m (IH1 m))
             by (unfold S'; rewrite decide_False by exact Hmn; rewrite decide_False by exact HjE1; done).
           assert (Hsh2 : S' m (IH2 m) = IS m (IH2 m))
             by (unfold S'; rewrite decide_False by exact Hmn; rewrite decide_False by exact HjE2; done).
           rewrite Hsh1, Hsh2. exact (I.(i_cut1) Hls).
    + intros n0 m0 Hln0 Hlm0 Hnm0.
      assert (HSni : S' n i = false).
      { unfold S'. rewrite decide_True by done. rewrite decide_False by exact Hij.
        apply anyb_false. intros x Hx. rewrite decide_True by done. done. }
      assert (HSnj : S' n j = true).
      { unfold S'. rewrite decide_True by done. rewrite decide_True by done. done. }
      assert (HSn : forall t, t <> j -> S' n t =
          anyb (elements (dom Δh)) (fun x => if decide (IS x t = IS x i) then false else true)).
      { intros t Htj2. unfold S'. rewrite decide_True by done. rewrite decide_False by exact Htj2. done. }
      assert (HSi0 : forall x, x <> n -> S' x i = IS x i).
      { intros x Hxn. unfold S'. rewrite decide_False by exact Hxn. rewrite decide_False by exact Hij. done. }
      assert (HSj0 : forall x, x <> n -> S' x j = IS x i).
      { intros x Hxn. unfold S'. rewrite decide_False by exact Hxn. rewrite decide_True by done. done. }
      assert (HSt0 : forall x t, x <> n -> t <> j -> S' x t = IS x t).
      { intros x t Hxn Htj3. unfold S'. rewrite decide_False by exact Hxn. rewrite decide_False by exact Htj3. done. }
      assert (Hx_dh : forall x, x ∈ elements (dom Δh) -> exists u, Δh !! x = Some u).
      { intros x Hx. apply elem_of_elements in Hx. apply elem_of_dom in Hx.
        destruct Hx as [u Hu]. exists u. exact Hu. }
      destruct (decide (m0 = n)) as [->|Hm0n].
      * assert (H1n : H1' n = i) by (unfold H1'; rewrite decide_True by done; done).
        assert (H2n : H2' n = j) by (unfold H2'; rewrite decide_True by done; done).
        rewrite H1n, H2n.
        destruct (decide (n0 = n)) as [Hc0|Hn0n].
        -- exfalso. apply Hnm0. exact Hc0.
        -- rewrite (HSi0 n0 Hn0n), (HSj0 n0 Hn0n). done.
      * assert (Hlsm := Hlive_neqn m0 Hm0n Hlm0).
        assert (HomS : IOm !! m0 <> None) by (apply (proj1 (I.(i_live_iff) m0) Hlsm)).
        destruct (IOm !! m0) as [[pm qm]|] eqn:HOm; [|exfalso; apply HomS; done].
        assert (E1 := I.(i_H1) Hlsm HOm). assert (E2 := I.(i_H2) Hlsm HOm).
        assert (Hneq12 := I.(i_H_neq) Hlsm).
        assert (HjE1 : IH1 m0 <> j) by (intro Hc; rewrite Hc in E1; rewrite HIDj_none in E1; discriminate E1).
        assert (HjE2 : IH2 m0 <> j) by (intro Hc; rewrite Hc in E2; rewrite HIDj_none in E2; discriminate E2).
        destruct (decide (n0 = n)) as [->|Hn0n].
        -- assert (Hls0 := Hlsm).
           destruct (Hholders m0 Hlm0 Hm0n) as
             [(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|(Ei & H1e & H2e)]]]].
           ++ rewrite H1e, H2e. rewrite HSni. rewrite (HSn (IH2 m0) HjE2).
              symmetry. apply anyb_false. intros x Hx. destruct (Hx_dh x Hx) as (u & Hxu).
              destruct (Δk !! m0) as [u0|] eqn:Eku; [|exfalso; apply Ek; done].
              assert (Hxne : x <> m0).
              { intro Hc. subst x. rewrite (map_disjoint_Some_l Δk Δh m0 u0 (ct_disj Hct) Eku) in Hxu. discriminate Hxu. }
              assert (Hlsx : live (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) x)
                by (apply Hdh_live; rewrite Hxu; discriminate).
              assert (Hcut2 := @i_cut2 (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I x m0 Hlsx Hlsm Hxne).
              rewrite Ai in Hcut2.
              rewrite decide_True by (symmetry; exact Hcut2). done.
           ++ rewrite H1e, H2e. rewrite HSnj. rewrite (HSn (IH2 m0) HjE2).
              symmetry. apply anyb_true. exists m0. split.
              ** apply elem_of_elements, elem_of_dom. exists pm. 
                 rewrite Ai in E1. rewrite Heq in E1.
                 rewrite (lookup_union_r Δk Δh m0 Ek) in E1. exact E1.
              ** destruct (decide (IS m0 (IH2 m0) = IS m0 i)) as [Hc|_]; [exfalso|done].
                 apply (I.(i_cut1) Hlsm). rewrite Ai. symmetry. exact Hc.
           ++ rewrite H1e, H2e. rewrite (HSn (IH1 m0) HjE1). rewrite HSni.
              apply anyb_false. intros x Hx. destruct (Hx_dh x Hx) as (u & Hxu).
              destruct (Δk !! m0) as [u0|] eqn:Eku; [|exfalso; apply Ek; done].
              assert (Hxne : x <> m0).
              { intro Hc. subst x. rewrite (map_disjoint_Some_l Δk Δh m0 u0 (ct_disj Hct) Eku) in Hxu. discriminate Hxu. }
              assert (Hlsx : live (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) x)
                by (apply Hdh_live; rewrite Hxu; discriminate).
              assert (Hcut2 := @i_cut2 (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I x m0 Hlsx Hlsm Hxne).
              rewrite Ai in Hcut2.
              rewrite decide_True by (exact Hcut2). done.
           ++ rewrite H1e, H2e. rewrite (HSn (IH1 m0) HjE1). rewrite HSnj.
              apply anyb_true. exists m0. split.
              ** apply elem_of_elements, elem_of_dom. exists qm.
                 rewrite Ai in E2. rewrite Heq in E2.
                 rewrite (lookup_union_r Δk Δh m0 Ek) in E2. exact E2.
              ** destruct (decide (IS m0 (IH1 m0) = IS m0 i)) as [Hc|_]; [exfalso|done].
                 apply (I.(i_cut1) Hlsm). rewrite Ai. rewrite Hc. done.
           ++ rewrite H1e, H2e. rewrite (HSn (IH1 m0) HjE1), (HSn (IH2 m0) HjE2).
              apply anyb_ext. intros x Hx. destruct (Hx_dh x Hx) as (u & Hxu).
              assert (Hxne : x <> m0).
              { intro Hc. subst x. assert (Hdi : ID i !! m0 = Some u) by exact (HIDh m0 u Hxu).
                rewrite Ei in Hdi. discriminate Hdi. }
              assert (Hlsx : live (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) x)
                by (apply Hdh_live; rewrite Hxu; discriminate).
              assert (Hcut2 := @i_cut2 (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I x m0 Hlsx Hlsm Hxne).
              rewrite Hcut2. done.
        -- assert (Hls0 := Hlive_neqn n0 Hn0n Hln0).
           destruct (Hholders m0 Hlm0 Hm0n) as
             [(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|[(Ai & Ek & H1e & H2e)|(Ei & H1e & H2e)]]]].
           ++ rewrite H1e, H2e. rewrite (HSi0 n0 Hn0n). rewrite (HSt0 n0 (IH2 m0) Hn0n HjE2).
              rewrite <- Ai. rewrite (@i_cut2 (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I n0 m0 Hls0 Hlsm Hnm0). done.
           ++ rewrite H1e, H2e. rewrite (HSj0 n0 Hn0n). rewrite (HSt0 n0 (IH2 m0) Hn0n HjE2).
              rewrite <- Ai. rewrite (@i_cut2 (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I n0 m0 Hls0 Hlsm Hnm0). done.
           ++ rewrite H1e, H2e. rewrite (HSt0 n0 (IH1 m0) Hn0n HjE1). rewrite (HSi0 n0 Hn0n).
              rewrite <- Ai. rewrite (@i_cut2 (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I n0 m0 Hls0 Hlsm Hnm0). done.
           ++ rewrite H1e, H2e. rewrite (HSt0 n0 (IH1 m0) Hn0n HjE1). rewrite (HSj0 n0 Hn0n).
              rewrite <- Ai. rewrite (@i_cut2 (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I n0 m0 Hls0 Hlsm Hnm0). done.
           ++ rewrite H1e, H2e.
              rewrite (HSt0 n0 (IH1 m0) Hn0n HjE1), (HSt0 n0 (IH2 m0) Hn0n HjE2).
              exact (@i_cut2 (({[i := Thread (k (Fork (Val v)))]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I n0 m0 Hls0 Hlsm Hnm0).
    + intros m k0 t Hom Hdk.
      destruct (decide (m = n)) as [->|Hmn].
      * assert (Homn : Om' !! n = Some (p, q)) by (unfold Om'; apply lookup_insert_eq).
        rewrite Homn in Hom. discriminate Hom.
      * assert (Hom' : Om' !! m = IOm !! m)
          by (unfold Om'; apply lookup_insert_ne; intros Hc; exact (Hmn (eq_sym Hc))).
        rewrite Hom' in Hom.
        destruct (decide (k0 = i)) as [->|Hki].
        -- rewrite HD'i in Hdk.
           rewrite (lookup_union_l Δk {[n := p]} m) in Hdk
             by (apply lookup_singleton_ne; intros Hc; apply Hmn; symmetry; exact Hc).
           exact (I.(i_dead) Hom (HIDk m t Hdk)).
        -- destruct (decide (k0 = j)) as [->|Hkj].
           ++ rewrite HD'j in Hdk.
              rewrite (lookup_union_l Δh {[n := q]} m) in Hdk
                by (apply lookup_singleton_ne; intros Hc; apply Hmn; symmetry; exact Hc).
              assert (HIDi : ID i !! m = Some t)
                by (rewrite Heq; apply lookup_union_Some_r; [exact (ct_disj Hct)|exact Hdk]).
              exact (I.(i_dead) Hom HIDi).
           ++ rewrite (HD'k k0 Hki Hkj) in Hdk. exact (I.(i_dead) Hom Hdk).
  - (* Sync *)
    assert (Hsrc_i : (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
              j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
              n := Barrier]} : cfg) ∪ ρf) !! i
             = Some (Thread (k1 (App (Val (BarrierV n)) (Val v1)))))
      by (apply lookup_union_Some_l; apply lookup_cfg3_i).
    assert (Hsrc_j : (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
              j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
              n := Barrier]} : cfg) ∪ ρf) !! j
             = Some (Thread (k2 (App (Val (BarrierV n)) (Val v2)))))
      by (apply lookup_union_Some_l; apply lookup_cfg3_j; exact Hij).
    assert (Hsrc_n : (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
              j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
              n := Barrier]} : cfg) ∪ ρf) !! n = Some Barrier)
      by (apply lookup_union_Some_l; apply lookup_cfg3_n; [exact Hin|exact Hjn]).
    assert (Htgt_i : (({[i := Thread (k1 (Val v2)); j := Thread (k2 (Val v1))]} : cfg) ∪ ρf) !! i
             = Some (Thread (k1 (Val v2))))
      by (apply lookup_union_Some_l; apply lookup_cfg2_i).
    assert (Htgt_j : (({[i := Thread (k1 (Val v2)); j := Thread (k2 (Val v1))]} : cfg) ∪ ρf) !! j
             = Some (Thread (k2 (Val v1))))
      by (apply lookup_union_Some_l; apply lookup_cfg2_j; exact Hij).
    assert (Hfr_n : ρf !! n = None).
    { change (map_disjoint
        (insert i (Thread (k1 (App (Val (BarrierV n)) (Val v1))))
           (insert j (Thread (k2 (App (Val (BarrierV n)) (Val v2))))
              (insert n Barrier (∅ : cfg)))) ρf) in Hd.
      rewrite map_disjoint_insert_l in Hd. destruct Hd as [_ Hd].
      rewrite map_disjoint_insert_l in Hd. destruct Hd as [_ Hd].
      rewrite map_disjoint_insert_l in Hd. destruct Hd as [Hn _]. exact Hn. }
    assert (Hfr_i : ρf !! i = None).
    { change (map_disjoint
        (insert i (Thread (k1 (Val v2)))
           (insert j (Thread (k2 (Val v1))) (∅ : cfg))) ρf) in Hd'.
      rewrite map_disjoint_insert_l in Hd'. destruct Hd' as [Hi _]. exact Hi. }
    assert (Hfr_j : ρf !! j = None).
    { change (map_disjoint
        (insert i (Thread (k1 (Val v2)))
           (insert j (Thread (k2 (Val v1))) (∅ : cfg))) ρf) in Hd'.
      rewrite map_disjoint_insert_l in Hd'. destruct Hd' as [_ Hd'].
      rewrite map_disjoint_insert_l in Hd'. destruct Hd' as [Hj _]. exact Hj. }
    assert (Hoff : forall m, m <> i -> m <> j -> m <> n ->
              (({[i := Thread (k1 (Val v2)); j := Thread (k2 (Val v1))]} : cfg) ∪ ρf) !! m
            = (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) !! m).
    { intros m Hmi Hmj Hmn0.
      rewrite (lookup_union_r ({[i := Thread (k1 (Val v2)); j := Thread (k2 (Val v1))]} : cfg) ρf m)
        by (apply lookup_cfg2_other; assumption).
      rewrite (lookup_union_r ({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ρf m)
        by (apply lookup_cfg3_other; assumption).
      done. }
    assert (Hlive_eq : forall m, m <> n ->
        live (({[i := Thread (k1 (Val v2)); j := Thread (k2 (Val v1))]} : cfg) ∪ ρf) m
        <-> live (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) m).
    { intros m Hmn0. destruct (decide (m = i)) as [->|Hmi].
      - unfold live. rewrite Htgt_i, Hsrc_i. split; discriminate.
      - destruct (decide (m = j)) as [->|Hmj].
        + unfold live. rewrite Htgt_j, Hsrc_j. split; discriminate.
        + unfold live. rewrite (Hoff m Hmi Hmj Hmn0). done. }
    assert (Htgt_n_none : (({[i := Thread (k1 (Val v2)); j := Thread (k2 (Val v1))]} : cfg) ∪ ρf) !! n = None).
    { rewrite (lookup_union_r ({[i := Thread (k1 (Val v2)); j := Thread (k2 (Val v1))]} : cfg) ρf n)
        by (apply lookup_cfg2_other; [intro Hc; apply Hin; symmetry; exact Hc|intro Hc; apply Hjn; symmetry; exact Hc]).
      exact Hfr_n. }
    assert (Htgt_n_nonlive : ~ live (({[i := Thread (k1 (Val v2)); j := Thread (k2 (Val v1))]} : cfg) ∪ ρf) n)
      by (unfold live; rewrite Htgt_n_none; discriminate).
    destruct (@sync_decomp (ID i) k1 n v1 Hk1 (I.(i_thr) Hsrc_i))
      as (Δk1 & Δn1 & Δv1 & a1 & b1 & Heq1 & Hdv1 & Hn1 & Hct1 & Hv1).
    destruct (@sync_decomp (ID j) k2 n v2 Hk2 (I.(i_thr) Hsrc_j))
      as (Δk2 & Δn2 & Δv2 & a2 & b2 & Heq2 & Hdv2 & Hn2 & Hct2 & Hv2).
    assert (Hdis1 : Δk1 ##ₘ (Δn1 ∪ Δv1)) by exact (ct_disj Hct1).
    assert (Hdis2 : Δk2 ##ₘ (Δn2 ∪ Δv2)) by exact (ct_disj Hct2).
    assert (Hn1_some : Δn1 !! n = Some (FunT Lin a1 b1))
      by (rewrite Hn1; apply lookup_singleton_eq).
    assert (Hn2_some : Δn2 !! n = Some (FunT Lin a2 b2))
      by (rewrite Hn2; apply lookup_singleton_eq).
    assert (Hn1_other : forall x, x <> n -> Δn1 !! x = None)
      by (intros x Hx; rewrite Hn1; apply lookup_singleton_ne; intros Hc; exact (Hx (eq_sym Hc))).
    assert (Hn2_other : forall x, x <> n -> Δn2 !! x = None)
      by (intros x Hx; rewrite Hn2; apply lookup_singleton_ne; intros Hc; exact (Hx (eq_sym Hc))).
    assert (Hk1_n : Δk1 !! n = None)
      by (apply (map_disjoint_Some_r Δk1 (Δn1 ∪ Δv1) n (FunT Lin a1 b1) Hdis1);
          apply lookup_union_Some_l; exact Hn1_some).
    assert (Hk2_n : Δk2 !! n = None)
      by (apply (map_disjoint_Some_r Δk2 (Δn2 ∪ Δv2) n (FunT Lin a2 b2) Hdis2);
          apply lookup_union_Some_l; exact Hn2_some).
    assert (Hv1_n : Δv1 !! n = None)
      by (apply (map_disjoint_Some_l Δn1 Δv1 n (FunT Lin a1 b1) Hdv1); exact Hn1_some).
    assert (Hv2_n : Δv2 !! n = None)
      by (apply (map_disjoint_Some_l Δn2 Δv2 n (FunT Lin a2 b2) Hdv2); exact Hn2_some).
    assert (HIDi_n : ID i !! n = Some (FunT Lin a1 b1)).
    { rewrite Heq1. rewrite (lookup_union_r Δk1 (Δn1 ∪ Δv1) n Hk1_n).
      apply lookup_union_Some_l. exact Hn1_some. }
    assert (HIDj_n : ID j !! n = Some (FunT Lin a2 b2)).
    { rewrite Heq2. rewrite (lookup_union_r Δk2 (Δn2 ∪ Δv2) n Hk2_n).
      apply lookup_union_Some_l. exact Hn2_some. }
    assert (HIDk1 : forall x t, Δk1 !! x = Some t -> ID i !! x = Some t)
      by (intros x t E; rewrite Heq1; apply lookup_union_Some_l; exact E).
    assert (HIDk2 : forall x t, Δk2 !! x = Some t -> ID j !! x = Some t)
      by (intros x t E; rewrite Heq2; apply lookup_union_Some_l; exact E).
    assert (HIDn1 : forall x t, Δn1 !! x = Some t -> ID i !! x = Some t)
      by (intros x t E; rewrite Heq1; apply lookup_union_Some_r; [exact Hdis1|];
          apply lookup_union_Some_l; exact E).
    assert (HIDn2 : forall x t, Δn2 !! x = Some t -> ID j !! x = Some t)
      by (intros x t E; rewrite Heq2; apply lookup_union_Some_r; [exact Hdis2|];
          apply lookup_union_Some_l; exact E).
    assert (HIDv1 : forall x t, Δv1 !! x = Some t -> ID i !! x = Some t)
      by (intros x t E; rewrite Heq1; apply lookup_union_Some_r; [exact Hdis1|];
          apply lookup_union_Some_r; [exact Hdv1|exact E]).
    assert (HIDv2 : forall x t, Δv2 !! x = Some t -> ID j !! x = Some t)
      by (intros x t E; rewrite Heq2; apply lookup_union_Some_r; [exact Hdis2|];
          apply lookup_union_Some_r; [exact Hdv2|exact E]).
    assert (Hlive_n : live (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) n)
      by (unfold live; exact Hsrc_n).
    assert (Homne : IOm !! n <> None) by (apply (proj1 (I.(i_live_iff) n) Hlive_n)).
    destruct (IOm !! n) as [[pn qn]|] eqn:HOmn; [|exfalso; apply Homne; done].
    assert (Hcut_ij : forall q, live (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) q -> q <> n -> IS q i = IS q j).
    { intros q Hlq Hqn.
      assert (Hx_i := I.(i_H_exact) Hlive_n HIDi_n).
      assert (Hx_j := I.(i_H_exact) Hlive_n HIDj_n).
      destruct Hx_i as [Ai|Ai]; destruct Hx_j as [Aj|Aj].
      - exfalso. apply Hij. rewrite Ai, Aj. done.
      - rewrite Ai, Aj. apply (@i_cut2 (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I q n Hlq Hlive_n Hqn).
      - rewrite Ai, Aj. symmetry. apply (@i_cut2 (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I q n Hlq Hlive_n Hqn).
      - exfalso. apply Hij. rewrite Ai, Aj. done. }
    assert (Hno_shared : forall m t u, m <> n ->
        ID i !! m = Some t -> ID j !! m = Some u -> False).
    { intros m t u Hmn0 Hi Hj.
      assert (Hlm : live (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) m)
        by (apply (@inv_live_of_holder _ ID IOm IS IH1 IH2 I m i); rewrite Hi; discriminate).
      assert (Ai := I.(i_H_exact) Hlm Hi).
      assert (Aj := I.(i_H_exact) Hlm Hj).
      assert (Ci := I.(i_H_exact) Hlive_n HIDi_n).
      assert (Cj := I.(i_H_exact) Hlive_n HIDj_n).
      assert (Hneq_ij : IS n i <> IS n j).
      { destruct Ci as [Ci|Ci]; destruct Cj as [Cj|Cj].
        - exfalso. apply Hij. rewrite Ci, Cj. done.
        - rewrite Ci, Cj. apply (I.(i_cut1) Hlive_n).
        - rewrite Ci, Cj. intro Hc. apply (I.(i_cut1) Hlive_n). symmetry. exact Hc.
        - exfalso. apply Hij. rewrite Ci, Cj. done. }
      assert (Hnm0 : n <> m) by (intro Hc; apply Hmn0; symmetry; exact Hc).
      assert (Heq_ij : IS n i = IS n j).
      { destruct Ai as [Ai|Ai]; destruct Aj as [Aj|Aj].
        - exfalso. apply Hij. rewrite Ai, Aj. done.
        - rewrite Ai, Aj. apply (@i_cut2 (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I n m Hlive_n Hlm Hnm0).
        - rewrite Ai, Aj. symmetry. apply (@i_cut2 (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I n m Hlive_n Hlm Hnm0).
        - exfalso. apply Hij. rewrite Ai, Aj. done. }
      exact (Hneq_ij Heq_ij). }
    assert (Hdisk1v2 : Δk1 ##ₘ Δv2).
    { apply map_disjoint_spec. intros m t u Hk Hv.
      assert (Hmn0 : m <> n)
        by (intro Hc; rewrite Hc in Hv; rewrite Hv2_n in Hv; discriminate Hv).
      exact (Hno_shared m t u Hmn0 (HIDk1 m t Hk) (HIDv2 m u Hv)). }
    assert (Hdisk2v1 : Δk2 ##ₘ Δv1).
    { apply map_disjoint_spec. intros m t u Hk Hv.
      assert (Hmn0 : m <> n)
        by (intro Hc; rewrite Hc in Hv; rewrite Hv1_n in Hv; discriminate Hv).
      exact (Hno_shared m u t Hmn0 (HIDv1 m u Hv) (HIDk2 m t Hk)). }
    assert (Hni : ID i !! n <> None) by (rewrite HIDi_n; discriminate).
    assert (Hnj : ID j !! n <> None) by (rewrite HIDj_n; discriminate).
    assert (Hty2 : a2 = b1).
    { assert (Hpair := @inv_pair_types (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I
             n pn qn i j Hlive_n HOmn Hij
             Hni Hnj).
      destruct Hpair as [[Hi_p Hj_q]|[Hi_q Hj_p]].
      - assert (Hp : pn = FunT Lin a1 b1) by (rewrite Hi_p in HIDi_n; injection HIDi_n; done).
        assert (Hq : qn = FunT Lin a2 b2) by (rewrite Hj_q in HIDj_n; injection HIDj_n; done).
        assert (Hdual : FunT Lin a2 b2 = dual (FunT Lin a1 b1)).
        { rewrite <- Hq, <- Hp. exact (I.(i_dual) HOmn). }
        rewrite dual_FunT in Hdual. injection Hdual as Hx Hy. exact Hx.
      - assert (Hq : qn = FunT Lin a1 b1) by (rewrite Hi_q in HIDi_n; injection HIDi_n; done).
        assert (Hp : pn = FunT Lin a2 b2) by (rewrite Hj_p in HIDj_n; injection HIDj_n; done).
        assert (Hdual : FunT Lin a1 b1 = dual (FunT Lin a2 b2)).
        { rewrite <- Hq, <- Hp. exact (I.(i_dual) HOmn). }
        rewrite dual_FunT in Hdual. injection Hdual as Hx Hy. symmetry. exact Hy. }
    assert (Hty1 : a1 = b2).
    { assert (Hpair := @inv_pair_types (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I
             n pn qn i j Hlive_n HOmn Hij
             Hni Hnj).
      destruct Hpair as [[Hi_p Hj_q]|[Hi_q Hj_p]].
      - assert (Hp : pn = FunT Lin a1 b1) by (rewrite Hi_p in HIDi_n; injection HIDi_n; done).
        assert (Hq : qn = FunT Lin a2 b2) by (rewrite Hj_q in HIDj_n; injection HIDj_n; done).
        assert (Hdual : FunT Lin a2 b2 = dual (FunT Lin a1 b1)).
        { rewrite <- Hq, <- Hp. exact (I.(i_dual) HOmn). }
        rewrite dual_FunT in Hdual. injection Hdual as Hx Hy. symmetry. exact Hy.
      - assert (Hq : qn = FunT Lin a1 b1) by (rewrite Hi_q in HIDi_n; injection HIDi_n; done).
        assert (Hp : pn = FunT Lin a2 b2) by (rewrite Hj_p in HIDj_n; injection HIDj_n; done).
        assert (Hdual : FunT Lin a1 b1 = dual (FunT Lin a2 b2)).
        { rewrite <- Hq, <- Hp. exact (I.(i_dual) HOmn). }
        rewrite dual_FunT in Hdual. injection Hdual as Hx Hy. exact Hx. }
    assert (Hpar_i : rt ∅ (Δk1 ∪ Δv2) (k1 (Val v2)) UnitT).
    { apply (ct_fill_any Hct1).
      - exact Hdisk1v2.
      - apply rt_Val. apply env_unr_empty. rewrite <- Hty2. exact Hv2. }
    assert (Hpar_j : rt ∅ (Δk2 ∪ Δv1) (k2 (Val v1)) UnitT).
    { apply (ct_fill_any Hct2).
      - exact Hdisk2v1.
      - apply rt_Val. apply env_unr_empty. rewrite <- Hty1. exact Hv1. }
    set (ID' := fun k => if decide (k = i) then Δk1 ∪ Δv2
                         else if decide (k = j) then Δk2 ∪ Δv1 else ID k).
    set (Om' := delete n IOm).
    set (S' := IS).
    set (H1' := fun q => if decide (IH1 q = i) then (if decide (Δv1 !! q = None) then i else j)
                         else if decide (IH1 q = j) then (if decide (Δv2 !! q = None) then j else i)
                         else IH1 q).
    set (H2' := fun q => if decide (IH2 q = i) then (if decide (Δv1 !! q = None) then i else j)
                         else if decide (IH2 q = j) then (if decide (Δv2 !! q = None) then j else i)
                         else IH2 q).
    assert (HDIDi : ID' i = Δk1 ∪ Δv2) by (unfold ID'; rewrite decide_True by done; done).
    assert (HDIDj : ID' j = Δk2 ∪ Δv1)
      by (unfold ID'; rewrite decide_False by (intros Hc; exact (Hij (eq_sym Hc)));
          rewrite decide_True by done; done).
    assert (HDIDk : forall k, k <> i -> k <> j -> ID' k = ID k)
      by (intros k Hki Hkj; unfold ID'; rewrite decide_False by exact Hki;
          rewrite decide_False by exact Hkj; done).
    assert (HOm_n : Om' !! n = None) by (unfold Om'; apply lookup_delete_eq).
    assert (HOm_o : forall q, q <> n -> Om' !! q = IOm !! q)
      by (intros q Hqn; unfold Om'; apply lookup_delete_ne;
          intros Hc; exact (Hqn (eq_sym Hc))).
    assert (HIDn_other : forall k, k <> i -> k <> j -> ID k !! n = None).
    { intros k Hki Hkj. destruct (ID k !! n) as [t|] eqn:E; [|done].
      assert (Hk := I.(i_H_exact) Hlive_n E).
      assert (Ci := I.(i_H_exact) Hlive_n HIDi_n).
      assert (Cj := I.(i_H_exact) Hlive_n HIDj_n).
      assert (Hpairn : (i = IH1 n /\ j = IH2 n) \/ (i = IH2 n /\ j = IH1 n)).
      { destruct Ci as [Ci|Ci]; destruct Cj as [Cj|Cj].
        - exfalso. apply Hij. rewrite Ci, Cj. done.
        - left. split; done.
        - right. split; done.
        - exfalso. apply Hij. rewrite Ci, Cj. done. }
      destruct Hpairn as [[A1 A2]|[A1 A2]]; destruct Hk as [Hk|Hk].
      - exfalso. apply Hki. rewrite Hk. symmetry. exact A1.
      - exfalso. apply Hkj. rewrite Hk. symmetry. exact A2.
      - exfalso. apply Hkj. rewrite Hk. symmetry. exact A2.
      - exfalso. apply Hki. rewrite Hk. symmetry. exact A1. }
    assert (HIS_phi : forall q t qb, live (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) q -> q <> n ->
        IS q (if decide (t = i) then (if decide (Δv1 !! qb = None) then i else j)
              else if decide (t = j) then (if decide (Δv2 !! qb = None) then j else i) else t)
        = IS q t).
    { intros q t qb Hlq Hqn.
      destruct (decide (t = i)) as [->|Hti].
      - destruct (Δv1 !! qb) as [u|] eqn:E.
        + rewrite decide_False by (intro Hc; discriminate Hc).
          symmetry. apply (Hcut_ij q Hlq Hqn).
        + done.
      - destruct (decide (t = j)) as [->|Htj].
        + destruct (Δv2 !! qb) as [u|] eqn:E.
          * rewrite decide_False by (intro Hc; discriminate Hc).
            apply (Hcut_ij q Hlq Hqn).
          * done.
        + done. }
    assert (Hk1none : forall x t, ID j !! x = Some t -> x <> n -> Δk1 !! x = None).
    { intros x t Hj Hx. destruct (Δk1 !! x) as [u|] eqn:E; [|done].
      exfalso. exact (Hno_shared x u t Hx (HIDk1 x u E) Hj). }
    assert (Hk2none : forall x t, ID i !! x = Some t -> x <> n -> Δk2 !! x = None).
    { intros x t Hi Hx. destruct (Δk2 !! x) as [u|] eqn:E; [|done].
      exfalso. exact (Hno_shared x t u Hx Hi (HIDk2 x u E)). }
    assert (Hv1none : forall x t, ID j !! x = Some t -> x <> n -> Δv1 !! x = None).
    { intros x t Hj Hx. destruct (Δv1 !! x) as [u|] eqn:E; [|done].
      exfalso. exact (Hno_shared x u t Hx (HIDv1 x u E) Hj). }
    assert (Hv2none : forall x t, ID i !! x = Some t -> x <> n -> Δv2 !! x = None).
    { intros x t Hi Hx. destruct (Δv2 !! x) as [u|] eqn:E; [|done].
      exfalso. exact (Hno_shared x t u Hx Hi (HIDv2 x u E)). }
    exists ID', Om', S', H1', H2'. constructor.
    + intros m e0 Hm.
      destruct (decide (m = i)) as [->|Hmi].
      * rewrite Htgt_i in Hm. injection Hm as He. subst e0. rewrite HDIDi. exact Hpar_i.
      * destruct (decide (m = j)) as [->|Hmj].
        -- rewrite Htgt_j in Hm. injection Hm as He. subst e0. rewrite HDIDj. exact Hpar_j.
        -- destruct (decide (m = n)) as [->|Hmn0].
           ++ rewrite Htgt_n_none in Hm. discriminate Hm.
           ++ rewrite (Hoff m Hmi Hmj Hmn0) in Hm.
              rewrite (HDIDk m Hmi Hmj). exact (I.(i_thr) Hm).
    + intros m Hnt.
      destruct (decide (m = i)) as [->|Hmi].
      * exfalso. apply (Hnt (k1 (Val v2))). exact Htgt_i.
      * destruct (decide (m = j)) as [->|Hmj].
        -- exfalso. apply (Hnt (k2 (Val v1))). exact Htgt_j.
        -- destruct (decide (m = n)) as [->|Hmn0].
           ++ rewrite (HDIDk n (fun Hc => Hin (eq_sym Hc)) (fun Hc => Hjn (eq_sym Hc))). apply I.(i_nonthr).
              intros e0 Hc. rewrite Hsrc_n in Hc. discriminate.
           ++ rewrite (HDIDk m Hmi Hmj). apply I.(i_nonthr).
              intros e0 Hc. apply (Hnt e0). rewrite (Hoff m Hmi Hmj Hmn0). exact Hc.
    + intros q. unfold live.
      destruct (decide (q = n)) as [->|Hqn].
      * rewrite Htgt_n_none, HOm_n. split; [intro Hc; discriminate Hc|intro Hc; exfalso; exact (Hc eq_refl)].
      * destruct (decide (q = i)) as [->|Hqi].
        -- assert (Hs : ~ live (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) i)
             by (unfold live; rewrite Hsrc_i; intros Hc; discriminate Hc).
           destruct (I.(i_live_iff) i) as [Hf Hg].
           split.
           ++ intro Hc. rewrite Htgt_i in Hc. discriminate Hc.
           ++ intro Hc. exfalso. apply Hs. apply Hg. rewrite (HOm_o i Hin) in Hc. exact Hc.
        -- destruct (decide (q = j)) as [->|Hqj].
           ++ assert (Hs : ~ live (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) j)
                by (unfold live; rewrite Hsrc_j; intros Hc; discriminate Hc).
              destruct (I.(i_live_iff) j) as [Hf Hg].
              split.
              ** intro Hc. rewrite Htgt_j in Hc. discriminate Hc.
              ** intro Hc. exfalso. apply Hs. apply Hg. rewrite (HOm_o j Hjn) in Hc. exact Hc.
           ++ rewrite (Hoff q Hqi Hqj Hqn). rewrite (HOm_o q Hqn).
              apply I.(i_live_iff).
    + intros q p0 q0 Hom. rewrite (HOm_o q) in Hom.
      * exact (I.(i_dual) Hom).
      * intro Hc. assert (Hnone : Om' !! q = None) by (rewrite Hc; exact HOm_n).
        rewrite Hnone in Hom. discriminate Hom.
    + intros q Hlq.
      assert (Hqn : q <> n) by (intro Hc; unfold live in Hlq; rewrite Hc in Hlq; rewrite Htgt_n_none in Hlq; discriminate Hlq).
      assert (Hls := proj1 (Hlive_eq q Hqn) Hlq).
      assert (HomS : IOm !! q <> None) by (apply (proj1 (I.(i_live_iff) q) Hls)).
      destruct (IOm !! q) as [[p0 q0]|] eqn:HOmq; [|exfalso; apply HomS; done].
      assert (E1 := I.(i_H1) Hls HOmq). assert (E2 := I.(i_H2) Hls HOmq).
      assert (Hneq12 := I.(i_H_neq) Hls).
      destruct (decide (IH1 q = i)) as [A1|A1n].
      { destruct (decide (IH2 q = i)) as [A2|A2n].
        { exfalso. apply Hneq12. rewrite A1, A2. done. }
        { destruct (decide (IH2 q = j)) as [A2j|A2jn].
          { exfalso.
            assert (HHi : ID i !! q = Some p0) by (rewrite A1 in E1; exact E1).
            assert (HHj : ID j !! q = Some q0) by (rewrite A2j in E2; exact E2).
            exact (Hno_shared q p0 q0 Hqn HHi HHj). }
          { unfold H1', H2'. rewrite decide_True by exact A1.
            destruct (Δv1 !! q) as [u|] eqn:Ev.
            { rewrite decide_False by (intro Hc; discriminate Hc).
              rewrite decide_False by exact A2n. rewrite decide_False by exact A2jn.
              intro Hc. apply A2jn. symmetry. exact Hc. }
            { rewrite decide_True by done.
              rewrite decide_False by exact A2n. rewrite decide_False by exact A2jn.
              intro Hc. apply A2n. symmetry. exact Hc. } } } }
      { destruct (decide (IH1 q = j)) as [A1j|A1jn].
        { destruct (decide (IH2 q = i)) as [A2|A2n].
          { exfalso.
            assert (HHi : ID i !! q = Some q0) by (rewrite A2 in E2; exact E2).
            assert (HHj : ID j !! q = Some p0) by (rewrite A1j in E1; exact E1).
            exact (Hno_shared q q0 p0 Hqn HHi HHj). }
          { destruct (decide (IH2 q = j)) as [A2j|A2jn].
            { exfalso. apply Hneq12. rewrite A1j, A2j. done. }
            { unfold H1', H2'. rewrite decide_False by exact A1n.
              rewrite decide_True by exact A1j.
              destruct (Δv2 !! q) as [u|] eqn:Ev.
              { rewrite decide_False by (intro Hc; discriminate Hc).
                rewrite decide_False by exact A2n. rewrite decide_False by exact A2jn.
                intro Hc. apply A2n. symmetry. exact Hc. }
              { rewrite decide_True by done.
                rewrite decide_False by exact A2n. rewrite decide_False by exact A2jn.
                intro Hc. apply A2jn. symmetry. exact Hc. } } } }
        { destruct (decide (IH2 q = i)) as [A2|A2n].
          { unfold H1', H2'. rewrite decide_False by exact A1n.
            rewrite decide_False by exact A1jn.
            rewrite decide_True by exact A2.
            destruct (Δv1 !! q) as [u|] eqn:Ev.
            { rewrite decide_False by (intro Hc; discriminate Hc).
              intro Hc. exact (A1jn Hc). }
            { rewrite decide_True by done.
              intro Hc. exact (A1n Hc). } }
          { destruct (decide (IH2 q = j)) as [A2j|A2jn].
            { unfold H1', H2'. rewrite decide_False by exact A1n.
              rewrite decide_False by exact A1jn.
              rewrite decide_False by exact A2n. rewrite decide_True by exact A2j.
              destruct (Δv2 !! q) as [u|] eqn:Ev.
              { rewrite decide_False by (intro Hc; discriminate Hc).
                intro Hc. exact (A1n Hc). }
              { rewrite decide_True by done.
                intro Hc. exact (A1jn Hc). } }
            { unfold H1', H2'. rewrite decide_False by exact A1n.
              rewrite decide_False by exact A1jn.
              rewrite decide_False by exact A2n. rewrite decide_False by exact A2jn.
              exact Hneq12. } } } }
    + intros q p0 r0 Hlq Hom.
      assert (Hqn : q <> n) by (intro Hc; rewrite Hc in Hlq; unfold live in Hlq; rewrite Htgt_n_none in Hlq; discriminate Hlq).
      assert (Hls := proj1 (Hlive_eq q Hqn) Hlq).
      rewrite (HOm_o q Hqn) in Hom.
      assert (E1 := I.(i_H1) Hls Hom). assert (E2 := I.(i_H2) Hls Hom).
      assert (Hneq12 := I.(i_H_neq) Hls).
      destruct (decide (IH1 q = i)) as [A1|A1n].
      { destruct (Δv1 !! q) as [u|] eqn:Ev.
        { assert (E1a : ID i !! q = Some p0) by (rewrite A1 in E1; exact E1).
          assert (Huv : Δv1 !! q = Some p0).
          { assert (HH := HIDv1 q u Ev). rewrite E1a in HH. injection HH as <-. exact Ev. }
          unfold H1'. rewrite decide_True by exact A1.
          rewrite decide_False by (intro Hc; rewrite Ev in Hc; discriminate Hc).
          rewrite HDIDj. rewrite (lookup_union_r Δk2 Δv1 q (Hk2none q p0 E1a Hqn)).
          exact Huv. }
        { assert (E1a : ID i !! q = Some p0) by (rewrite A1 in E1; exact E1).
          unfold H1'. rewrite decide_True by exact A1. rewrite decide_True by exact Ev.
          assert (HXn : (Δn1 ∪ Δv1) !! q = None).
          { rewrite lookup_union, (Hn1_other q Hqn), Ev. done. }
          assert (Hdk1 : Δk1 !! q = Some p0).
          { rewrite Heq1 in E1a.
            exact (lookup_union_Some_inv_l Δk1 (Δn1 ∪ Δv1) q p0 E1a HXn). }
          rewrite HDIDi. rewrite (lookup_union_l Δk1 Δv2 q (Hv2none q p0 E1a Hqn)).
          exact Hdk1. } }
      { destruct (decide (IH1 q = j)) as [A1j|A1jn].
        { destruct (Δv2 !! q) as [u|] eqn:Ev.
          { assert (E1a : ID j !! q = Some p0) by (rewrite A1j in E1; exact E1).
            assert (Huv : Δv2 !! q = Some p0).
            { assert (HH := HIDv2 q u Ev). rewrite E1a in HH. injection HH as <-. exact Ev. }
            unfold H1'. rewrite decide_False by exact A1n. rewrite decide_True by exact A1j.
            rewrite decide_False by (intro Hc; rewrite Ev in Hc; discriminate Hc).
            rewrite HDIDi. rewrite (lookup_union_r Δk1 Δv2 q (Hk1none q p0 E1a Hqn)).
            exact Huv. }
          { assert (E1a : ID j !! q = Some p0) by (rewrite A1j in E1; exact E1).
            unfold H1'. rewrite decide_False by exact A1n. rewrite decide_True by exact A1j.
            rewrite decide_True by exact Ev.
            assert (HXn : (Δn2 ∪ Δv2) !! q = None).
            { rewrite lookup_union, (Hn2_other q Hqn), Ev. done. }
            assert (Hdk2 : Δk2 !! q = Some p0).
            { rewrite Heq2 in E1a.
              exact (lookup_union_Some_inv_l Δk2 (Δn2 ∪ Δv2) q p0 E1a HXn). }
            rewrite HDIDj. rewrite (lookup_union_l Δk2 Δv1 q (Hv1none q p0 E1a Hqn)).
            exact Hdk2. } }
        { unfold H1'. rewrite decide_False by exact A1n. rewrite decide_False by exact A1jn.
          rewrite (HDIDk (IH1 q) A1n A1jn). exact E1. } }
    + intros q p0 r0 Hlq Hom.
      assert (Hqn : q <> n) by (intro Hc; rewrite Hc in Hlq; unfold live in Hlq; rewrite Htgt_n_none in Hlq; discriminate Hlq).
      assert (Hls := proj1 (Hlive_eq q Hqn) Hlq).
      rewrite (HOm_o q Hqn) in Hom.
      assert (E1 := I.(i_H1) Hls Hom). assert (E2 := I.(i_H2) Hls Hom).
      assert (Hneq12 := I.(i_H_neq) Hls).
      destruct (decide (IH2 q = i)) as [A2|A2n].
      { destruct (Δv1 !! q) as [u|] eqn:Ev.
        { assert (E2a : ID i !! q = Some r0) by (rewrite A2 in E2; exact E2).
          assert (Huv : Δv1 !! q = Some r0).
          { assert (HH := HIDv1 q u Ev). rewrite E2a in HH. injection HH as <-. exact Ev. }
          unfold H2'. rewrite decide_True by exact A2.
          rewrite decide_False by (intro Hc; rewrite Ev in Hc; discriminate Hc).
          rewrite HDIDj. rewrite (lookup_union_r Δk2 Δv1 q (Hk2none q r0 E2a Hqn)).
          exact Huv. }
        { assert (E2a : ID i !! q = Some r0) by (rewrite A2 in E2; exact E2).
          unfold H2'. rewrite decide_True by exact A2. rewrite decide_True by exact Ev.
          assert (HXn : (Δn1 ∪ Δv1) !! q = None).
          { rewrite lookup_union, (Hn1_other q Hqn), Ev. done. }
          assert (Hdk1 : Δk1 !! q = Some r0).
          { rewrite Heq1 in E2a.
            exact (lookup_union_Some_inv_l Δk1 (Δn1 ∪ Δv1) q r0 E2a HXn). }
          rewrite HDIDi. rewrite (lookup_union_l Δk1 Δv2 q (Hv2none q r0 E2a Hqn)).
          exact Hdk1. } }
      { destruct (decide (IH2 q = j)) as [A2j|A2jn].
        { destruct (Δv2 !! q) as [u|] eqn:Ev.
          { assert (E2a : ID j !! q = Some r0) by (rewrite A2j in E2; exact E2).
            assert (Huv : Δv2 !! q = Some r0).
            { assert (HH := HIDv2 q u Ev). rewrite E2a in HH. injection HH as <-. exact Ev. }
            unfold H2'. rewrite decide_False by exact A2n. rewrite decide_True by exact A2j.
            rewrite decide_False by (intro Hc; rewrite Ev in Hc; discriminate Hc).
            rewrite HDIDi. rewrite (lookup_union_r Δk1 Δv2 q (Hk1none q r0 E2a Hqn)).
            exact Huv. }
          { assert (E2a : ID j !! q = Some r0) by (rewrite A2j in E2; exact E2).
            unfold H2'. rewrite decide_False by exact A2n. rewrite decide_True by exact A2j.
            rewrite decide_True by exact Ev.
            assert (HXn : (Δn2 ∪ Δv2) !! q = None).
            { rewrite lookup_union, (Hn2_other q Hqn), Ev. done. }
            assert (Hdk2 : Δk2 !! q = Some r0).
            { rewrite Heq2 in E2a.
              exact (lookup_union_Some_inv_l Δk2 (Δn2 ∪ Δv2) q r0 E2a HXn). }
            rewrite HDIDj. rewrite (lookup_union_l Δk2 Δv1 q (Hv1none q r0 E2a Hqn)).
            exact Hdk2. } }
        { unfold H2'. rewrite decide_False by exact A2n. rewrite decide_False by exact A2jn.
          rewrite (HDIDk (IH2 q) A2n A2jn). exact E2. } }
    + intros q k t Hlq Hk.
      assert (Hqn : q <> n) by (intro Hc; rewrite Hc in Hlq; unfold live in Hlq; rewrite Htgt_n_none in Hlq; discriminate Hlq).
      assert (Hls := proj1 (Hlive_eq q Hqn) Hlq).
      assert (HomS : IOm !! q <> None) by (apply (proj1 (I.(i_live_iff) q) Hls)).
      destruct (IOm !! q) as [[p0 r0]|] eqn:HOmq; [|exfalso; apply HomS; done].
      destruct (decide (k = i)) as [->|Hki].
      { rewrite HDIDi in Hk.
        destruct (Δk1 !! q) as [u|] eqn:E1k.
        { pose proof (map_disjoint_Some_l Δk1 (Δn1 ∪ Δv1) q u Hdis1 E1k) as Hnone.
          apply lookup_union_None_1 in Hnone. destruct Hnone as [_ Hv1n].
          assert (Hlsq : live (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) q)
            by (apply (@inv_live_of_holder _ ID IOm IS IH1 IH2 I q i);
                rewrite (HIDk1 q u E1k); discriminate).
          destruct (I.(i_H_exact) Hlsq (HIDk1 q u E1k)) as [Hc|Hc].
          { left. unfold H1'. rewrite decide_True by (symmetry; exact Hc).
            rewrite decide_True by exact Hv1n. done. }
          { right. unfold H2'. rewrite decide_True by (symmetry; exact Hc).
            rewrite decide_True by exact Hv1n. done. } }
        { destruct (Δv2 !! q) as [u|] eqn:E2v.
          { assert (Hlsq : live (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) q)
              by (apply (@inv_live_of_holder _ ID IOm IS IH1 IH2 I q j);
                  rewrite (HIDv2 q u E2v); discriminate).
            assert (Hv1n : Δv1 !! q = None) by exact (Hv1none q u (HIDv2 q u E2v) Hqn).
            destruct (I.(i_H_exact) Hlsq (HIDv2 q u E2v)) as [Hc|Hc].
            { left. unfold H1'. rewrite decide_False by (intro Hci; apply Hij; symmetry; rewrite Hc; exact Hci).
              rewrite decide_True by (symmetry; exact Hc).
              rewrite decide_False by (intro Hc2; rewrite Hc2 in E2v; discriminate E2v). done. }
            { right. unfold H2'. rewrite decide_False by (intro Hci; apply Hij; symmetry; rewrite Hc; exact Hci).
              rewrite decide_True by (symmetry; exact Hc).
              rewrite decide_False by (intro Hc2; rewrite Hc2 in E2v; discriminate E2v). done. } }
          { rewrite lookup_union_None_2 in Hk; [discriminate Hk|exact E1k|exact E2v]. } } }
      { destruct (decide (k = j)) as [->|Hkj].
        { rewrite HDIDj in Hk.
          destruct (Δk2 !! q) as [u|] eqn:E2k.
          { pose proof (map_disjoint_Some_l Δk2 (Δn2 ∪ Δv2) q u Hdis2 E2k) as Hnone.
            apply lookup_union_None_1 in Hnone. destruct Hnone as [_ Hv2n].
            assert (Hlsq : live (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) q)
              by (apply (@inv_live_of_holder _ ID IOm IS IH1 IH2 I q j);
                  rewrite (HIDk2 q u E2k); discriminate).
            destruct (I.(i_H_exact) Hlsq (HIDk2 q u E2k)) as [Hc|Hc].
            { left. unfold H1'. rewrite decide_False by (intro Hci; rewrite Hci in Hc; apply Hij; symmetry; exact Hc).
              rewrite decide_True by (symmetry; exact Hc).
              rewrite decide_True by exact Hv2n. done. }
            { right. unfold H2'. rewrite decide_False by (intro Hci; rewrite Hci in Hc; apply Hij; symmetry; exact Hc).
              rewrite decide_True by (symmetry; exact Hc).
              rewrite decide_True by exact Hv2n. done. } }
          { destruct (Δv1 !! q) as [u|] eqn:E1v.
            { assert (Hlsq : live (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) q)
                by (apply (@inv_live_of_holder _ ID IOm IS IH1 IH2 I q i);
                    rewrite (HIDv1 q u E1v); discriminate).
              assert (Hv2n : Δv2 !! q = None) by exact (Hv2none q u (HIDv1 q u E1v) Hqn).
              destruct (I.(i_H_exact) Hlsq (HIDv1 q u E1v)) as [Hc|Hc].
              { left. unfold H1'. rewrite decide_True by (symmetry; exact Hc).
                rewrite decide_False by (intro Hc2; rewrite Hc2 in E1v; discriminate E1v). done. }
              { right. unfold H2'. rewrite decide_True by (symmetry; exact Hc).
                rewrite decide_False by (intro Hc2; rewrite Hc2 in E1v; discriminate E1v). done. } }
            { rewrite lookup_union_None_2 in Hk; [discriminate Hk|exact E2k|exact E1v]. } } }
        { rewrite (HDIDk k Hki Hkj) in Hk.
          assert (Hlsq : live (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
                 j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
                 n := Barrier]} : cfg) ∪ ρf) q)
            by (apply (@inv_live_of_holder _ ID IOm IS IH1 IH2 I q k); rewrite Hk; discriminate).
          destruct (I.(i_H_exact) Hlsq Hk) as [Hc|Hc].
          { left. unfold H1'.
            rewrite decide_False by (intro Hci; apply Hki; rewrite Hc; exact Hci).
            rewrite decide_False by (intro Hcj; apply Hkj; rewrite Hc; exact Hcj).
            exact Hc. }
          { right. unfold H2'.
            rewrite decide_False by (intro Hci; apply Hki; rewrite Hc; exact Hci).
            rewrite decide_False by (intro Hcj; apply Hkj; rewrite Hc; exact Hcj).
            exact Hc. } } }
    + intros q Hlq.
      assert (Hqn : q <> n) by (intro Hc; rewrite Hc in Hlq; unfold live in Hlq; rewrite Htgt_n_none in Hlq; discriminate Hlq).
      assert (Hls := proj1 (Hlive_eq q Hqn) Hlq).
      unfold S', H1', H2'.
      rewrite (HIS_phi q (IH1 q) q Hls Hqn).
      rewrite (HIS_phi q (IH2 q) q Hls Hqn).
      apply (I.(i_cut1) Hls).
    + intros q1 q2 Hl1 Hl2 Hq12.
      assert (Hq1n : q1 <> n) by (intro Hc; rewrite Hc in Hl1; unfold live in Hl1; rewrite Htgt_n_none in Hl1; discriminate Hl1).
      assert (Hq2n : q2 <> n) by (intro Hc; rewrite Hc in Hl2; unfold live in Hl2; rewrite Htgt_n_none in Hl2; discriminate Hl2).
      assert (Hls1 := proj1 (Hlive_eq q1 Hq1n) Hl1).
      assert (Hls2 := proj1 (Hlive_eq q2 Hq2n) Hl2).
      unfold S', H1', H2'.
      rewrite (HIS_phi q1 (IH1 q2) q2 Hls1 Hq1n).
      rewrite (HIS_phi q1 (IH2 q2) q2 Hls1 Hq1n).
      exact (@i_cut2 (({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1))); j := Thread (k2 (App (Val (BarrierV n)) (Val v2))); n := Barrier]} : cfg) ∪ ρf) ID IOm IS IH1 IH2 I q1 q2 Hls1 Hls2 Hq12).
    + intros q k t Hom Hk.
      destruct (decide (q = n)) as [->|Hqn].
      { destruct (decide (k = i)) as [->|Hki].
        { rewrite HDIDi in Hk.
          rewrite (lookup_union_None_2 Δk1 Δv2 n Hk1_n Hv2_n) in Hk. discriminate Hk. }
        { destruct (decide (k = j)) as [->|Hkj].
          { rewrite HDIDj in Hk.
            rewrite (lookup_union_None_2 Δk2 Δv1 n Hk2_n Hv1_n) in Hk. discriminate Hk. }
          { rewrite (HDIDk k Hki Hkj) in Hk.
            rewrite (HIDn_other k Hki Hkj) in Hk. discriminate Hk. } } }
      { rewrite (HOm_o q Hqn) in Hom.
        destruct (decide (k = i)) as [->|Hki].
        { rewrite HDIDi in Hk.
          destruct (Δk1 !! q) as [u|] eqn:E1k.
          { exfalso. exact (I.(i_dead) Hom (HIDk1 q u E1k)). }
          destruct (Δv2 !! q) as [u|] eqn:E2v.
          { exfalso. exact (I.(i_dead) Hom (HIDv2 q u E2v)). }
          rewrite (lookup_union_None_2 Δk1 Δv2 q E1k E2v) in Hk. discriminate Hk. }
        { destruct (decide (k = j)) as [->|Hkj].
          { rewrite HDIDj in Hk.
            destruct (Δk2 !! q) as [u|] eqn:E2k.
            { exfalso. exact (I.(i_dead) Hom (HIDk2 q u E2k)). }
            destruct (Δv1 !! q) as [u|] eqn:E1v.
            { exfalso. exact (I.(i_dead) Hom (HIDv1 q u E1v)). }
            rewrite (lookup_union_None_2 Δk2 Δv1 q E2k E1v) in Hk. discriminate Hk. }
          { rewrite (HDIDk k Hki Hkj) in Hk.
            exact (I.(i_dead) Hom Hk). } } }
Qed.


(* ------------------------------------------------------------------ *)
(* Initial invariant and global progress                              *)
(* ------------------------------------------------------------------ *)

Lemma singleton_thread_not_live e n : ~ live ({[0 := Thread e]} : cfg) n.
Proof.
  intro Hl. unfold live in Hl.
  destruct (decide (n = 0)) as [->|Hn].
  - assert (Hs : ({[0 := Thread e]} : cfg) !! 0 = Some (Thread e))
      by apply lookup_singleton_eq.
    rewrite Hs in Hl. discriminate Hl.
  - assert (Hs : ({[0 := Thread e]} : cfg) !! n = None)
      by (apply lookup_singleton_ne; intros Hc; apply Hn; symmetry; exact Hc).
    rewrite Hs in Hl. discriminate Hl.
Qed.

Lemma inv_initial e : typed ∅ e UnitT -> inv ({[0 := Thread e]} : cfg).
Proof.
  intros Ht.
  exists (fun _ => (∅ : gmap nat type)), (∅ : gmap nat (type * type)),
         (fun _ _ => false), (fun _ => 0), (fun _ => 1).
  constructor.
  - intros m e0 Hm. destruct (decide (m = 0)) as [->|Hm0].
    + injection Hm as <-.
      apply typed_to_rt. exact Ht.
    + assert (Hnone : ({[0 := Thread e]} : cfg) !! m = None)
        by (apply lookup_singleton_ne; intros Hc; apply Hm0; symmetry; exact Hc).
      rewrite Hnone in Hm. discriminate Hm.
  - intros m _. done.
  - intros n. unfold live.
    assert (He : (∅ : gmap nat (type * type)) !! n = None) by apply lookup_empty.
    destruct (decide (n = 0)) as [->|Hn].
    + assert (Hs : ({[0 := Thread e]} : cfg) !! 0 = Some (Thread e))
        by apply lookup_singleton_eq.
      rewrite Hs, He. split.
      * intro Hc. discriminate Hc.
      * intro Hc. exfalso. exact (Hc eq_refl).
    + assert (Hs : ({[0 := Thread e]} : cfg) !! n = None)
        by (apply lookup_singleton_ne; intros Hc; apply Hn; symmetry; exact Hc).
      rewrite Hs, He. split.
      * intro Hc. discriminate Hc.
      * intro Hc. exfalso. exact (Hc eq_refl).
  - intros n p q Hom. rewrite lookup_empty in Hom. discriminate Hom.
  - intros n Hl. exfalso.
    exact (@singleton_thread_not_live e n Hl).
  - intros n p q Hl Hom. exfalso.
    exact (@singleton_thread_not_live e n Hl).
  - intros n p q Hl Hom. exfalso.
    exact (@singleton_thread_not_live e n Hl).
  - intros n k t Hl Hk. exfalso.
    exact (@singleton_thread_not_live e n Hl).
  - intros n Hl. exfalso.
    exact (@singleton_thread_not_live e n Hl).
  - intros n m Hln Hlm Hnm. exfalso.
    exact (@singleton_thread_not_live e n Hln).
  - intros n k t Hom Hk. rewrite lookup_empty in Hk. discriminate Hk.
Qed.

Lemma inv_step {ρ ρ' : cfg} : inv ρ -> step' ρ ρ' -> inv ρ'.
Proof.
  intros [ID [IOm [IS [IH1 [IH2 I]]]]] [i Hstep].
  destruct Hstep as [ρ0 ρ0' ρf i Hd Hd' Hls].
  exact (@inv_local_pure ρ0 ρ0' ρf i ID IOm IS IH1 IH2 I Hd Hd' Hls).
Qed.

Lemma inv_steps {ρ ρ' : cfg} : inv ρ -> steps ρ ρ' -> inv ρ'.
Proof.
  intros Hinv Hrt. revert Hinv.
  induction Hrt as [x| x y z Hxy Hyz IH]; intros Hinv.
  - exact Hinv.
  - apply IH. apply (@inv_step x y); [exact Hinv|].
    exact Hxy.
Qed.

Theorem typed_global_progress e ρ :
  typed ∅ e UnitT -> steps {[ 0 := Thread e ]} ρ -> global_progress ρ.
Proof.
  intros Ht Hsteps.
  apply global_progress_of_inv.
  exact (inv_steps (@inv_initial e Ht) Hsteps).
Qed.
