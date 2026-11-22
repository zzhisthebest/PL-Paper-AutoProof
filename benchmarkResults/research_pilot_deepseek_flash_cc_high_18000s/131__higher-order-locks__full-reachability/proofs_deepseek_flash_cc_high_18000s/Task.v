From cgraphs.locks.lambdalock Require Import definitions.

From Stdlib Require Import Classical_Prop Wellfounded Wf_nat Lia.
From Stdlib Require Import Strings.String Eqdep_dec.
From Stdlib Require Import Relation_Operators Arith.
From stdpp Require Import finite.
From Stdlib Require Import FunctionalExtensionality.
Open Scope string_scope.

(* ================================================================== *)
(* Runtime typing for configurations.                                 *)
(*                                                                    *)
(* Source terms are Val-free, so [typed] cannot type configurations   *)
(* produced by reduction.  [wt] extends it with runtime values [cv].  *)
(* Values are environment-independent (they are closed).               *)
(* ================================================================== *)

Inductive wt (L : gmap nat type) : env -> expr -> type -> Prop :=
  | VarW Γ x t :
      env_var Γ x t ->
      wt L Γ (Var x) t
  | FunW Γ Γ' x e t1 t2 l :
      env_bind Γ' x t1 Γ ->
      (l = Unr -> env_unr Γ) ->
      wt L Γ' e t2 ->
      wt L Γ (Fun x e) (FunT l t1 t2)
  | AppW Γ Γ1 Γ2 e1 e2 t1 t2 l :
      env_split Γ Γ1 Γ2 ->
      wt L Γ1 e1 (FunT l t1 t2) ->
      wt L Γ2 e2 t1 ->
      wt L Γ (App e1 e2) t2
  | UnitW Γ :
      env_unr Γ ->
      wt L Γ Unit UnitT
  | PairW Γ Γ1 Γ2 e1 e2 t1 t2 :
      env_split Γ Γ1 Γ2 ->
      wt L Γ1 e1 t1 ->
      wt L Γ2 e2 t2 ->
      wt L Γ (Pair e1 e2) (PairT t1 t2)
  | LetPairW Γ Γ1 Γ2 e1 e2 t1 t2 t :
      env_split Γ Γ1 Γ2 ->
      wt L Γ1 e1 (PairT t1 t2) ->
      wt L Γ2 e2 (FunT Lin t1 (FunT Lin t2 t)) ->
      wt L Γ (LetPair e1 e2) t
  | SumW Γ n (ts : fin n -> type) i e :
      wt L Γ e (ts i) ->
      wt L Γ (Sum i e) (SumT n ts)
  | MatchSumW n Γ Γ1 Γ2 t (ts : fin n -> type) es e :
      env_split Γ Γ1 Γ2 ->
      (n = 0 -> env_unr Γ2) ->
      wt L Γ1 e (SumT n ts) ->
      (forall i, wt L Γ2 (es i) (FunT Lin (ts i) t)) ->
      wt L Γ (MatchSum n e es) t
  | ForkW Γ e t1 t2 :
      wt L Γ e (FunT Lin (FunT Lin t2 t1) UnitT) ->
      wt L Γ (ForkBarrier e) (FunT Lin t1 t2)
  | NewLockW Γ e t :
      wt L Γ e t ->
      wt L Γ (NewLock e) (LockT (Owner,Closed) t)
  | ForkLockW Γ Γ1 Γ2 e1 e2 t l1 l2 l3 :
      env_split Γ Γ1 Γ2 ->
      lockcap_split l1 l2 l3 ->
      wt L Γ1 e1 (LockT l1 t) ->
      wt L Γ2 e2 (FunT Lin (LockT l2 t) UnitT) ->
      wt L Γ (ForkLock e1 e2) (LockT l3 t)
  | AcquireW Γ e t lo :
      wt L Γ e (LockT (lo,Closed) t) ->
      wt L Γ (Acquire e) (PairT (LockT (lo,Opened) t) t)
  | ReleaseW Γ Γ1 Γ2 e1 e2 t lo :
      env_split Γ Γ1 Γ2 ->
      wt L Γ1 e1 (LockT (lo,Opened) t) ->
      wt L Γ2 e2 t ->
      wt L Γ (Release e1 e2) (LockT (lo,Closed) t)
  | WaitW Γ e t :
      wt L Γ e (LockT (Owner,Closed) t) ->
      wt L Γ (Wait e) t
  | DropW Γ e t :
      wt L Γ e (LockT (Client,Closed) t) ->
      wt L Γ (Drop e) UnitT
  | ValW Γ v t :
      env_unr Γ ->
      cv L v t ->
      wt L Γ (Val v) t
with cv (L : gmap nat type) : val -> type -> Prop :=
  | FunVW x e t1 t2 l :
      wt L (<[ x := t1 ]> (∅ : env)) e t2 ->
      cv L (FunV x e) (FunT l t1 t2)
  | UnitVW : cv L UnitV UnitT
  | PairVW v1 v2 t1 t2 :
      cv L v1 t1 -> cv L v2 t2 ->
      cv L (PairV v1 v2) (PairT t1 t2)
  | SumVW n (ts : fin n -> type) i v :
      cv L v (ts i) ->
      cv L (SumV i v) (SumT n ts)
  | BarrierVW n t1 t2 :
      cv L (BarrierV n) (FunT Lin t1 t2)
  | LockVW n lc t :
      L !! n = Some t ->
      cv L (LockV n) (LockT lc t).

(* ---------- gmap / environment helpers ---------- *)

Lemma env_lookup_insert_same x (t : type) : (<[x:=t]>(∅ : env)) !! x = Some t.
Proof. unfold env in *. apply lookup_insert_eq. Qed.

Lemma env_lookup_insert_none x y (t : type) (Γ : env) : x <> y -> Γ !! y = None -> (<[x:=t]>Γ) !! y = None.
Proof.
  unfold env in *. intros Hne Hy.
  rewrite (lookup_insert_ne Γ x y t Hne). done.
Qed.

Lemma env_unr_delete x (Γ : env) : env_unr Γ -> env_unr (delete x Γ).
Proof.
  intros H y t Hy. unfold env_unr in H. unfold env in *.
  destruct (decide (x=y)) as [E|E]; subst.
  - rewrite (lookup_delete_eq Γ y) in Hy. done.
  - rewrite (lookup_delete_ne Γ x y E) in Hy. apply H in Hy. done.
Qed.

Lemma env_unr_insert_lookup x (t : type) (Γ : env) :
  env_unr (<[x:=t]>Γ) -> unr t.
Proof. intros H. unfold env_unr in H. apply (H x t). unfold env. apply lookup_insert_eq. Qed.

Lemma env_union_empty_l (m : env) : ∅ ∪ m = m.
Proof.
  unfold env in *. apply map_eq. intro x. rewrite lookup_union.
  assert (H : (∅ : gmap string type) !! x = None) by apply lookup_empty.
  rewrite H. destruct (m !! x); done.
Qed.

Lemma env_union_empty_r (m : env) : m ∪ ∅ = m.
Proof.
  unfold env in *. apply map_eq. intro x. rewrite lookup_union.
  assert (H : (∅ : gmap string type) !! x = None) by apply lookup_empty.
  rewrite H. destruct (m !! x); done.
Qed.

Lemma env_split_empty (Γ1 Γ2 : env) : env_split ∅ Γ1 Γ2 -> Γ1 = ∅ /\ Γ2 = ∅.
Proof.
  unfold env in *.
  intros [Hun Hdis]. symmetry in Hun.
  apply map_positive_l in Hun as H1. subst Γ1.
  rewrite env_union_empty_l in Hun. subst Γ2. split; reflexivity.
Qed.

Lemma disj_delete x (Γ1 Γ2 : env) : disj Γ1 Γ2 -> disj (delete x Γ1) (delete x Γ2).
Proof.
  unfold env in *.
  intros H i t1 t2 H1 H2.
  destruct (decide (x=i)) as [E|E]; subst.
  - rewrite (lookup_delete_eq Γ1 i) in H1. done.
  - rewrite (lookup_delete_ne Γ1 x i E) in H1. rewrite (lookup_delete_ne Γ2 x i E) in H2. apply (H i t1 t2 H1 H2).
Qed.

Lemma delete_insert_none x (t : type) (Γ : env) : Γ !! x = None -> delete x (<[x:=t]>Γ) = Γ.
Proof.
  unfold env in *. intros Hx. apply map_eq. intro y. destruct (decide (x=y)) as [E|E]; subst.
  - rewrite (lookup_delete_eq (<[y:=t]>Γ) y). done.
  - rewrite (lookup_delete_ne (<[x:=t]>Γ) x y E). rewrite (lookup_insert_ne Γ x y t E). done.
Qed.

Lemma delete_none x (Γ : env) : Γ !! x = None -> delete x Γ = Γ.
Proof.
  unfold env in *. intros Hx. apply map_eq. intro y. destruct (decide (x=y)) as [E|E]; subst.
  - rewrite (lookup_delete_eq Γ y). done.
  - rewrite (lookup_delete_ne Γ x y E). done.
Qed.

Lemma insert_delete_same x (t : type) (Γ : env) : Γ !! x = Some t -> <[x:=t]>(delete x Γ) = Γ.
Proof.
  unfold env in *. intros Hx. apply map_eq. intro y. destruct (decide (x=y)) as [E|E]; subst.
  - rewrite (lookup_insert_eq (delete y Γ) y t). symmetry. done.
  - rewrite (lookup_insert_ne (delete x Γ) x y t E). rewrite (lookup_delete_ne Γ x y E). done.
Qed.

Lemma insert_insert_same x (t1 t2 : type) (Γ : env) :
  <[x:=t2]>(<[x:=t1]>Γ) = <[x:=t2]>Γ.
Proof.
  unfold env in *. apply map_eq. intro y. destruct (decide (x=y)) as [E|E]; subst.
  - rewrite (lookup_insert_eq (<[y:=t1]>Γ) y t2). rewrite (lookup_insert_eq Γ y t2). done.
  - rewrite (lookup_insert_ne (<[x:=t1]>Γ) x y t2 E).
    rewrite (lookup_insert_ne Γ x y t2 E).
    rewrite (lookup_insert_ne Γ x y t1 E). done.
Qed.

Lemma insert_insert_comm x y (t1 t2 : type) (Γ : env) : x <> y ->
  <[x:=t1]>(<[y:=t2]>Γ) = <[y:=t2]>(<[x:=t1]>Γ).
Proof.
  intros Hne. unfold env in *. apply map_eq. intro z.
  destruct (decide (z=x)) as [E1|E1].
  - subst z.
    destruct (decide (x=y)) as [E2|E2].
    + exfalso. apply Hne. done.
    + rewrite (lookup_insert_eq (<[y:=t2]>Γ) x t1).
      rewrite (lookup_insert_ne (<[x:=t1]>Γ) y x t2 (fun H => E2 (eq_sym H))).
      rewrite (lookup_insert_eq Γ x t1). done.
  - destruct (decide (z=y)) as [E2|E2].
    + subst z.
      rewrite (lookup_insert_ne (<[y:=t2]>Γ) x y t1 Hne).
      rewrite (lookup_insert_eq Γ y t2).
      rewrite (lookup_insert_eq (<[x:=t1]>Γ) y t2). done.
    + rewrite (lookup_insert_ne (<[y:=t2]>Γ) x z t1 (fun H => E1 (eq_sym H))).
      rewrite (lookup_insert_ne Γ y z t2 (fun H => E2 (eq_sym H))).
      rewrite (lookup_insert_ne (<[x:=t1]>Γ) y z t2 (fun H => E2 (eq_sym H))).
      rewrite (lookup_insert_ne Γ x z t1 (fun H => E1 (eq_sym H))). done.
Qed.

Lemma env_split_delete x (E E1 E2 : env) :
  env_split E E1 E2 -> env_split (delete x E) (delete x E1) (delete x E2).
Proof.
  unfold env in *. intros [Hun Hdis]. split.
  - rewrite Hun. apply delete_union.
  - apply disj_delete. done.
Qed.

Lemma env_unr_empty : env_unr (∅ : env).
Proof. unfold env in *. intros x t H. assert (H0 : (∅ : gmap string type) !! x = None) by apply lookup_empty. setoid_rewrite H0 in H. done. Qed.

Lemma env_split_nil : env_split (∅ : env) ∅ ∅.
Proof.
  unfold env_split. split.
  - symmetry. apply env_union_empty_l.
  - intros i t1 t2 H1 H2. assert (H0 : (∅ : env) !! i = None) by (unfold env; apply lookup_empty).
    setoid_rewrite H0 in H1. done.
Qed.

(* ---------- Source typing embeds in the runtime typing ---------- *)

Lemma typed_to_wt Γ e t (H : typed Γ e t) : forall L, wt L Γ e t.
Proof.
  induction H as
    [ Γ x t Hvar
    | Γ Γ' x e t1 t2 l Hb Hunr Hty IH
    | Γ Γ1 Γ2 e1 e2 t1 t2 l Hsplit Hty1 IH1 Hty2 IH2
    | Γ Hunr
    | Γ Γ1 Γ2 e1 e2 t1 t2 Hsplit Hty1 IH1 Hty2 IH2
    | Γ Γ1 Γ2 e1 e2 t1 t2 t Hsplit Hty1 IH1 Hty2 IH2
    | Γ n ts i e Hty IH
    | n Γ Γ1 Γ2 t ts es e Hsplit Hn Hty IH Hf IHf
    | Γ e t1 t2 Hty IH
    | Γ e t Hty IH
    | Γ Γ1 Γ2 e1 e2 t l1 l2 l3 Hsplit Hcap Hty1 IH1 Hty2 IH2
    | Γ e t lo Hty IH
    | Γ Γ1 Γ2 e1 e2 t lo Hsplit Hty1 IH1 Hty2 IH2
    | Γ e t Hty IH
    | Γ e t Hty IH ];
    intros L.
  - apply VarW; exact Hvar.
  - eapply FunW; [ exact Hb | exact Hunr | apply IH ].
  - eapply AppW; [ exact Hsplit | apply IH1 | apply IH2 ].
  - apply UnitW; exact Hunr.
  - eapply PairW; [ exact Hsplit | apply IH1 | apply IH2 ].
  - eapply LetPairW; [ exact Hsplit | apply IH1 | apply IH2 ].
  - eapply SumW; apply IH.
  - eapply MatchSumW; [ exact Hsplit | exact Hn | apply IH | intros i; apply (IHf i L) ].
  - eapply ForkW; apply IH.
  - eapply NewLockW; apply IH.
  - eapply ForkLockW; [ exact Hsplit | exact Hcap | apply IH1 | apply IH2 ].
  - eapply AcquireW; apply IH.
  - eapply ReleaseW; [ exact Hsplit | apply IH1 | apply IH2 ].
  - eapply WaitW; apply IH.
  - eapply DropW; apply IH.
Qed.

(* ================================================================== *)
(* Additional environment lemmas needed for substitution.             *)
(* ================================================================== *)

Lemma option_union_none_l {A} (y : option A) : (None : option A) ∪ y = y.
Proof. destruct y; reflexivity. Qed.

Lemma option_union_some_l {A} (a : A) (y : option A) :
  (Some a : option A) ∪ y = Some a.
Proof. destruct y; reflexivity. Qed.

Lemma delete_insert_same_env x (t : type) (Γ : env) :
  delete x (<[x:=t]>Γ) = delete x Γ.
Proof.
  unfold env in *. apply map_eq. intro y.
  destruct (decide (x=y)) as [E|E]; subst.
  - rewrite (lookup_delete_eq (<[y:=t]>Γ) y). rewrite (lookup_delete_eq Γ y). done.
  - rewrite (lookup_delete_ne (<[x:=t]>Γ) x y E).
    rewrite (lookup_insert_ne Γ x y t E).
    rewrite (lookup_delete_ne Γ x y E). done.
Qed.

Lemma insert_delete_same_env x (t : type) (Γ : env) :
  <[x:=t]>(delete x Γ) = <[x:=t]>Γ.
Proof.
  unfold env in *. apply map_eq. intro y.
  destruct (decide (x=y)) as [E|E]; subst.
  - rewrite (lookup_insert_eq (delete y Γ) y t). rewrite (lookup_insert_eq Γ y t). done.
  - rewrite (lookup_insert_ne (delete x Γ) x y t E).
    rewrite (lookup_delete_ne Γ x y E).
    rewrite (lookup_insert_ne Γ x y t E). done.
Qed.

Lemma delete_insert_comm_env x y (t : type) (Γ : env) : x <> y ->
  delete x (<[y:=t]>Γ) = <[y:=t]>(delete x Γ).
Proof.
  intros Hne. unfold env in *. apply map_eq. intro z.
  destruct (decide (x=z)) as [E1|E1]; subst.
  - rewrite (lookup_delete_eq (<[y:=t]>Γ) z).
    rewrite (lookup_insert_ne (delete z Γ) y z t (fun H => Hne (eq_sym H))).
    rewrite (lookup_delete_eq Γ z). done.
  - rewrite (lookup_delete_ne (<[y:=t]>Γ) x z E1).
    destruct (decide (y=z)) as [E2|E2]; subst.
    + rewrite (lookup_insert_eq Γ z t). rewrite (lookup_insert_eq (delete x Γ) z t). done.
    + rewrite (lookup_insert_ne Γ y z t E2).
      rewrite (lookup_insert_ne (delete x Γ) y z t E2).
      rewrite (lookup_delete_ne Γ x z E1). done.
Qed.

Lemma delete_empty_env (x : string) : delete x (∅ : env) = ∅.
Proof.
  unfold env in *. apply map_eq. intro y.
  destruct (decide (x=y)) as [E|E]; subst.
  - rewrite (lookup_delete_eq (∅ : gmap string type) y). symmetry. apply lookup_empty.
  - rewrite (lookup_delete_ne (∅ : gmap string type) x y E). symmetry. apply lookup_empty.
Qed.


Lemma env_var_lookup Γ x t : env_var Γ x t -> Γ !! x = Some t.
Proof.
  intros [Γ' [E _]]. subst Γ. unfold env in *.
  apply lookup_insert_eq.
Qed.

Lemma env_var_unr_delete Γ x t : env_var Γ x t -> env_unr (delete x Γ).
Proof.
  intros [Γ' [E Hu]]. subst Γ.
  rewrite delete_insert_same_env.
  apply env_unr_delete. exact Hu.
Qed.

Lemma env_var_delete Γ x y t : env_var Γ y t -> y <> x -> env_var (delete x Γ) y t.
Proof.
  intros [Γ' [E Hu]] Hne. subst Γ.
  exists (delete x Γ'). split.
  - rewrite delete_insert_comm_env; [done | intros H; exact (Hne (eq_sym H))].
  - apply env_unr_delete. exact Hu.
Qed.

Lemma env_var_empty x t : env_var (∅ : env) x t -> False.
Proof.
  intros [Γ' [E _]].
  assert (Hl : (<[x:=t]>Γ') !! x = Some t) by apply lookup_insert_eq.
  symmetry in E. rewrite E in Hl. cbn in Hl. discriminate Hl.
Qed.

Lemma env_split_lookup_l Γ Γ1 Γ2 x t :
  env_split Γ Γ1 Γ2 -> Γ1 !! x = Some t -> Γ !! x = Some t.
Proof.
  intros [E _] H1. subst Γ.
  apply (lookup_union_Some_l Γ1 Γ2 x t H1).
Qed.

Lemma env_split_lookup_none Γ Γ1 Γ2 x :
  env_split Γ Γ1 Γ2 -> Γ !! x = None -> Γ1 !! x = None /\ Γ2 !! x = None.
Proof.
  intros [E _] H. subst Γ.
  apply (proj1 (lookup_union_None Γ1 Γ2 x)). exact H.
Qed.

Lemma env_split_lookup_r Γ Γ1 Γ2 x t :
  env_split Γ Γ1 Γ2 -> Γ1 !! x = None -> Γ !! x = Some t -> Γ2 !! x = Some t.
Proof.
  intros [E _] Hn Hsome.
  unfold env in *.
  rewrite E in Hsome.
  rewrite lookup_union in Hsome.
  destruct (Γ1 !! x) as [t1|] eqn:E1.
  - discriminate Hn.
  - rewrite option_union_none_l in Hsome. exact Hsome.
Qed.

Lemma env_split_lookup_r_some Γ Γ1 Γ2 x t :
  env_split Γ Γ1 Γ2 -> Γ2 !! x = Some t -> Γ !! x = Some t.
Proof.
  intros [E Hd] H2. unfold env in *. rewrite E. rewrite lookup_union.
  destruct (Γ1 !! x) as [t0|] eqn:E1.
  - destruct (Hd x t0 t E1 H2) as [-> _]. rewrite option_union_some_l. reflexivity.
  - rewrite option_union_none_l. exact H2.
Qed.

(* A variable absent from an environment cannot occur free in a term typed
   under it.  We phrase this via [subst] preservation directly later. *)


(* ===== end of base ===== *)

From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import Strings.String.
Open Scope string_scope.

Section Subst.

Context (L : gmap nat type).

(* ------------------------------------------------------------------ *)
(* Substitution lemma.                                                *)
(*                                                                    *)
(* We substitute a *value* [a] for a variable [x] in a term [e] typed  *)
(* under [Γ].  The result is typed under [delete x Γ].                 *)
(*                                                                    *)
(* The hypothesis [(Γ !! x = Some t1 -> cv L a t1)] is vacuous when    *)
(* [x] is not bound in [Γ]; in that case no value typing is needed.    *)
(* This single uniform statement is what makes the induction go        *)
(* through without extensionality: in the "variable absent" case no    *)
(* rewriting of the substituted term is required.                     *)
(* ------------------------------------------------------------------ *)

Lemma wt_subst_aux :
  forall (Γ : env) (e : expr) (t : type), wt L Γ e t ->
  forall x a, (forall t1, Γ !! x = Some t1 -> cv L a t1) ->
  wt L (delete x Γ) (subst x a e) t.
Proof.
  intros Γ e t H.
  induction H as
    [ Γ x t Hvar
    | Γ Γ' x e t1 t2 l Hb Hunr Hbody IHbody
    | Γ Γ1 Γ2 e1 e2 t1 t2 l Hsplit H1 IH1 H2 IH2
    | Γ Hunr
    | Γ Γ1 Γ2 e1 e2 t1 t2 Hsplit H1 IH1 H2 IH2
    | Γ Γ1 Γ2 e1 e2 t1 t2 t Hsplit H1 IH1 H2 IH2
    | Γ n ts i e H1 IH1
    | n Γ Γ1 Γ2 t ts es e Hsplit Hn H1 IH1 Hf IHf
    | Γ e t1 t2 H1 IH1
    | Γ e t H1 IH1
    | Γ Γ1 Γ2 e1 e2 t l1 l2 l3 Hsplit Hcap H1 IH1 H2 IH2
    | Γ e t lo H1 IH1
    | Γ Γ1 Γ2 e1 e2 t lo Hsplit H1 IH1 H2 IH2
    | Γ e t H1 IH1
    | Γ e t H1 IH1
    | Γ v t Hunr Hcv0 ] using wt_ind.

  (* VarW *)
  - intros y b Hcv. simpl.
    destruct (decide (y = x)) as [E|E].
    + subst y.
      apply ValW.
      * apply env_var_unr_delete with (t := t) in Hvar. exact Hvar.
      * apply (Hcv t). apply env_var_lookup. exact Hvar.
    + apply VarW. apply env_var_delete with (x := y).
      * exact Hvar.
      * intros H; exact (E (eq_sym H)).

  (* FunW *)
  - intros y b Hcv. simpl.
    destruct (decide (y = x)) as [E|E].
    + subst y.
      destruct Hb as [HbEq HbUnr].
      eapply FunW with (Γ' := Γ').
      * split.
        -- rewrite insert_delete_same_env. exact HbEq.
        -- intros t' Ht'. rewrite (lookup_delete_eq Γ x) in Ht'. discriminate Ht'.
      * intros U. apply env_unr_delete. apply Hunr. exact U.
      * exact Hbody.
    + destruct Hb as [HbEq HbUnr].
      eapply FunW with (Γ' := delete y Γ').
      * split.
        -- rewrite HbEq. rewrite (delete_insert_comm_env y x t1 Γ E). reflexivity.
        -- intros t' Ht'. rewrite (lookup_delete_ne Γ y x E) in Ht'. apply HbUnr. exact Ht'.
      * intros U. apply env_unr_delete. apply Hunr. exact U.
      * apply (IHbody y b). intros t1' Hsome.
        apply Hcv.
        rewrite HbEq in Hsome.
        rewrite (lookup_insert_ne Γ x y t1 (fun H => E (eq_sym H))) in Hsome.
        exact Hsome.

  (* AppW *)
  - intros y b Hcv. simpl.
    eapply AppW with (Γ1 := delete y Γ1) (Γ2 := delete y Γ2).
    + apply env_split_delete. exact Hsplit.
    + apply (IH1 y b). intros t1' Hsome. apply Hcv.
      apply (env_split_lookup_l Γ Γ1 Γ2 y t1' Hsplit Hsome).
    + apply (IH2 y b). intros t1' Hsome. apply Hcv.
      apply (env_split_lookup_r_some Γ Γ1 Γ2 y t1' Hsplit Hsome).

  (* UnitW *)
  - intros y b Hcv. simpl. apply UnitW. apply env_unr_delete. exact Hunr.

  (* PairW *)
  - intros y b Hcv. simpl.
    eapply PairW with (Γ1 := delete y Γ1) (Γ2 := delete y Γ2).
    + apply env_split_delete. exact Hsplit.
    + apply (IH1 y b). intros t1' Hsome. apply Hcv.
      apply (env_split_lookup_l Γ Γ1 Γ2 y t1' Hsplit Hsome).
    + apply (IH2 y b). intros t1' Hsome. apply Hcv.
      apply (env_split_lookup_r_some Γ Γ1 Γ2 y t1' Hsplit Hsome).

  (* LetPairW *)
  - intros y b Hcv. simpl.
    eapply LetPairW with (Γ1 := delete y Γ1) (Γ2 := delete y Γ2).
    + apply env_split_delete. exact Hsplit.
    + apply (IH1 y b). intros t1' Hsome. apply Hcv.
      apply (env_split_lookup_l Γ Γ1 Γ2 y t1' Hsplit Hsome).
    + apply (IH2 y b). intros t1' Hsome. apply Hcv.
      apply (env_split_lookup_r_some Γ Γ1 Γ2 y t1' Hsplit Hsome).

  (* SumW *)
  - intros y b Hcv. simpl. apply SumW. apply (IH1 y b). exact Hcv.

  (* MatchSumW *)
  - intros y b Hcv. simpl.
    eapply MatchSumW with (Γ1 := delete y Γ1) (Γ2 := delete y Γ2).
    + apply env_split_delete. exact Hsplit.
    + intros Hn0. apply env_unr_delete. apply Hn. exact Hn0.
    + apply (IH1 y b). intros t1' Hsome. apply Hcv.
      apply (env_split_lookup_l Γ Γ1 Γ2 y t1' Hsplit Hsome).
    + intros i. apply (IHf i y b). intros t1' Hsome. apply Hcv.
      apply (env_split_lookup_r_some Γ Γ1 Γ2 y t1' Hsplit Hsome).

  (* ForkW *)
  - intros y b Hcv. simpl. apply ForkW. apply (IH1 y b). exact Hcv.

  (* NewLockW *)
  - intros y b Hcv. simpl. apply NewLockW. apply (IH1 y b). exact Hcv.

  (* ForkLockW *)
  - intros y b Hcv. simpl.
    eapply ForkLockW with (Γ1 := delete y Γ1) (Γ2 := delete y Γ2).
    + apply env_split_delete. exact Hsplit.
    + exact Hcap.
    + apply (IH1 y b). intros t1' Hsome. apply Hcv.
      apply (env_split_lookup_l Γ Γ1 Γ2 y t1' Hsplit Hsome).
    + apply (IH2 y b). intros t1' Hsome. apply Hcv.
      apply (env_split_lookup_r_some Γ Γ1 Γ2 y t1' Hsplit Hsome).

  (* AcquireW *)
  - intros y b Hcv. simpl. apply AcquireW. apply (IH1 y b). exact Hcv.

  (* ReleaseW *)
  - intros y b Hcv. simpl.
    eapply ReleaseW with (Γ1 := delete y Γ1) (Γ2 := delete y Γ2).
    + apply env_split_delete. exact Hsplit.
    + apply (IH1 y b). intros t1' Hsome. apply Hcv.
      apply (env_split_lookup_l Γ Γ1 Γ2 y t1' Hsplit Hsome).
    + apply (IH2 y b). intros t1' Hsome. apply Hcv.
      apply (env_split_lookup_r_some Γ Γ1 Γ2 y t1' Hsplit Hsome).

  (* WaitW *)
  - intros y b Hcv. simpl. apply WaitW. apply (IH1 y b). exact Hcv.

  (* DropW *)
  - intros y b Hcv. simpl. eapply DropW. apply (IH1 y b). exact Hcv.

  (* ValW *)
  - intros y b Hcv. simpl. apply ValW.
    + apply env_unr_delete. exact Hunr.
    + exact Hcv0.
Qed.

(* The usable form. *)
Lemma wt_subst Γ e t (Hwt : wt L Γ e t) x a t1
    (Hx : Γ !! x = Some t1) (Hcv : cv L a t1) :
  wt L (delete x Γ) (subst x a e) t.
Proof.
  apply (wt_subst_aux Γ e t Hwt x a).
  intros t1' Hx'.
  pose proof Hx as H.
  rewrite Hx' in H. injection H as ->. exact Hcv.
Qed.

(* Closed instantiation: substituting into a singleton environment. *)
Lemma wt_subst_singleton x a t1 e t2
    (Hcv : cv L a t1) (Hwt : wt L (<[x:=t1]>(∅ : env)) e t2) :
  wt L ∅ (subst x a e) t2.
Proof.
  pose proof (wt_subst (<[x:=t1]>(∅ : env)) e t2 Hwt x a t1
                (env_lookup_insert_same x t1) Hcv) as H.
  rewrite delete_insert_same_env in H.
  rewrite delete_empty_env in H.
  exact H.
Qed.

Print Assumptions wt_subst.
Print Assumptions wt_subst_singleton.

End Subst.

(* ===== end of subst ===== *)

From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import Strings.String Eqdep_dec.
Open Scope string_scope.

Section Views.

Context (L : gmap nat type).

(* ---------------- wt views: one per expression constructor ---------- *)

Lemma wt_val_view Γ v t (H : wt L Γ (Val v) t) : env_unr Γ /\ cv L v t.
Proof. inversion H; subst; auto. Qed.

Lemma wt_fun_view Γ x e t (H : wt L Γ (Fun x e) t) :
  exists Γ' t1 t2 l, t = FunT l t1 t2 /\ env_bind Γ' x t1 Γ /\
    (l = Unr -> env_unr Γ) /\ wt L Γ' e t2.
Proof. inversion H; subst; eauto 12. Qed.

Lemma wt_app_view Γ e1 e2 t (H : wt L Γ (App e1 e2) t) :
  exists Γ1 Γ2 t1 l, env_split Γ Γ1 Γ2 /\
    wt L Γ1 e1 (FunT l t1 t) /\ wt L Γ2 e2 t1.
Proof. inversion H; subst; eauto 12. Qed.

Lemma wt_unit_view Γ t (H : wt L Γ Unit t) : t = UnitT /\ env_unr Γ.
Proof. inversion H; subst; auto. Qed.

Lemma wt_pair_view Γ e1 e2 t (H : wt L Γ (Pair e1 e2) t) :
  exists Γ1 Γ2 t1 t2, t = PairT t1 t2 /\ env_split Γ Γ1 Γ2 /\
    wt L Γ1 e1 t1 /\ wt L Γ2 e2 t2.
Proof. inversion H; subst; eauto 12. Qed.

Lemma wt_letpair_view Γ e1 e2 t (H : wt L Γ (LetPair e1 e2) t) :
  exists Γ1 Γ2 t1 t2, env_split Γ Γ1 Γ2 /\
    wt L Γ1 e1 (PairT t1 t2) /\
    wt L Γ2 e2 (FunT Lin t1 (FunT Lin t2 t)).
Proof. inversion H; subst; eauto 12. Qed.

Lemma wt_sum_view Γ n e t (H : wt L Γ (Sum n e) t) :
  exists n' (ts : fin n' -> type) (i : fin n'),
    t = SumT n' ts /\ n = fin_to_nat i /\ wt L Γ e (ts i).
Proof.
  inversion H; subst. eauto 12.
Qed.

Lemma wt_matchsum_view Γ n e es t (H : wt L Γ (MatchSum n e es) t) :
  exists Γ1 Γ2 ts, env_split Γ Γ1 Γ2 /\ (n = 0 -> env_unr Γ2) /\
    wt L Γ1 e (SumT n ts) /\
    (forall i, wt L Γ2 (es i) (FunT Lin (ts i) t)).
Proof.
  remember (MatchSum n e es) as ex eqn:Eex.
  revert n e es Eex.
  destruct H; intros n' e' es' E; try discriminate E.
  injection E as Hn He Hes.
  subst n'. subst e'.
  apply (inj_pair2_eq_dec nat Nat.eq_dec) in Hes.
  subst es'.
  eauto 12.
Qed.

Lemma wt_fork_view Γ e t (H : wt L Γ (ForkBarrier e) t) :
  exists t1 t2, t = FunT Lin t1 t2 /\
    wt L Γ e (FunT Lin (FunT Lin t2 t1) UnitT).
Proof. inversion H; subst; eauto 12. Qed.

Lemma wt_newlock_view Γ e t (H : wt L Γ (NewLock e) t) :
  exists t0, t = LockT (Owner,Closed) t0 /\ wt L Γ e t0.
Proof. inversion H; subst; eauto 12. Qed.

Lemma wt_forklock_view Γ e1 e2 t (H : wt L Γ (ForkLock e1 e2) t) :
  exists Γ1 Γ2 t0 l1 l2 l3, t = LockT l3 t0 /\ env_split Γ Γ1 Γ2 /\
    lockcap_split l1 l2 l3 /\ wt L Γ1 e1 (LockT l1 t0) /\
    wt L Γ2 e2 (FunT Lin (LockT l2 t0) UnitT).
Proof. inversion H; subst; eauto 12. Qed.

Lemma wt_acquire_view Γ e t (H : wt L Γ (Acquire e) t) :
  exists t0 lo, t = PairT (LockT (lo,Opened) t0) t0 /\
    wt L Γ e (LockT (lo,Closed) t0).
Proof. inversion H; subst; eauto 12. Qed.

Lemma wt_release_view Γ e1 e2 t (H : wt L Γ (Release e1 e2) t) :
  exists Γ1 Γ2 t0 lo, t = LockT (lo,Closed) t0 /\ env_split Γ Γ1 Γ2 /\
    wt L Γ1 e1 (LockT (lo,Opened) t0) /\ wt L Γ2 e2 t0.
Proof. inversion H; subst; eauto 12. Qed.

Lemma wt_wait_view Γ e t (H : wt L Γ (Wait e) t) :
  wt L Γ e (LockT (Owner,Closed) t).
Proof. inversion H; subst; auto. Qed.

Lemma wt_drop_view Γ e t (H : wt L Γ (Drop e) t) :
  t = UnitT /\ exists t0, wt L Γ e (LockT (Client,Closed) t0).
Proof. inversion H; subst; eauto 12. Qed.

(* ---------------- cv views: one per value constructor ---------------- *)

Lemma cv_fun_view x e l t1 t2 (H : cv L (FunV x e) (FunT l t1 t2)) :
  wt L (<[x:=t1]>(∅ : env)) e t2.
Proof. inversion H; subst; assumption. Qed.

Lemma cv_barrier_view n l t1 t2 (H : cv L (BarrierV n) (FunT l t1 t2)) :
  l = Lin.
Proof. inversion H; subst; reflexivity. Qed.

Lemma cv_lock_view n lc t (H : cv L (LockV n) (LockT lc t)) :
  L !! n = Some t.
Proof. inversion H; subst; assumption. Qed.

Lemma cv_pair_view v1 v2 t1 t2 (H : cv L (PairV v1 v2) (PairT t1 t2)) :
  cv L v1 t1 /\ cv L v2 t2.
Proof. inversion H; subst; auto. Qed.

Lemma cv_sum_fin_view n ts (i : fin n) v
    (H : cv L (SumV i v) (SumT n ts)) : cv L v (ts i).
Proof.
  remember (SumV i v) as w eqn:Ew.
  remember (SumT n ts) as T eqn:ET.
  revert n ts i v Ew ET.
  destruct H; intros n' ts' i' v' Ew ET; try discriminate Ew; try discriminate ET.
  injection Ew as Hi Hv.
  injection ET as Hn Hts.
  subst n'.
  apply (inj_pair2_eq_dec nat Nat.eq_dec) in Hts.
  subst ts'.
  apply fin_to_nat_inj in Hi.
  pose proof (f_equal (fun j : fin n => ts j) Hi) as Htsi.
  rewrite Htsi in H.
  rewrite Hv in H.
  exact H.
Qed.

(* Value-ranked inversions (for progress): the value is a variable. *)

Lemma cv_unit_inv v (H : cv L v UnitT) : v = UnitV.
Proof. inversion H; reflexivity. Qed.

Lemma cv_fun_inv v l t1 t2 (H : cv L v (FunT l t1 t2)) :
  (exists x e, v = FunV x e) \/ (exists n, v = BarrierV n).
Proof. inversion H; subst; eauto. Qed.

Lemma cv_pair_inv v t1 t2 (H : cv L v (PairT t1 t2)) :
  exists v1 v2, v = PairV v1 v2 /\ cv L v1 t1 /\ cv L v2 t2.
Proof. inversion H; subst; eauto. Qed.

Lemma cv_sum_inv v n ts (H : cv L v (SumT n ts)) :
  exists (i : fin n) v', v = SumV i v' /\ cv L v' (ts i).
Proof.
  remember v as w eqn:Ew.
  remember (SumT n ts) as T eqn:ET.
  revert n ts v Ew ET.
  destruct H; intros n' ts' v' Ew ET; try discriminate Ew; try discriminate ET.
  injection ET as Hn Hts.
  subst n'.
  apply (inj_pair2_eq_dec nat Nat.eq_dec) in Hts.
  subst ts'.
  exists i, v.
  split; [reflexivity | exact H].
Qed.

Lemma cv_lock_inv v lc t (H : cv L v (LockT lc t)) :
  exists n, v = LockV n /\ L !! n = Some t.
Proof. inversion H; subst; eauto. Qed.

End Views.

(* ===== end of views ===== *)

From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import Strings.String.
Open Scope string_scope.

Section Pure.

Context (L : gmap nat type).

(* Closed pure subject reduction: a pure step preserves the type of a
   term typed in the empty environment.  Closedness is essential: the
   runtime value typing [cv] types a function value only when its body is
   typed in the singleton environment of its parameter, which holds for
   terms whose environment is empty at the point of [Fun_step]. *)

Lemma wt_pure_step e e' t :
  wt L ∅ e t -> pure_step e e' -> wt L ∅ e' t.
Proof.
  intros Hwt Hs. revert t Hwt.
  induction Hs; intros t Hwt.

  (* Fun_step *)
  - destruct (wt_fun_view L ∅ _ _ _ Hwt) as (Γ' & t1 & t2 & l & Ht & Hb & Hunr & Hbody).
    subst t. apply ValW.
    + apply env_unr_empty.
    + eapply FunVW.
      destruct Hb as [HbEq _]. rewrite <- HbEq. exact Hbody.

  (* App_step *)
  - destruct (wt_app_view L ∅ _ _ _ Hwt) as (Γ1 & Γ2 & t1 & l & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]. subst Γ1 Γ2.
    destruct (wt_val_view L _ _ _ H1) as [_ Hcv1].
    destruct (wt_val_view L _ _ _ H2) as [_ Hcv2].
    pose proof (cv_fun_view L _ _ _ _ _ Hcv1) as Hbody.
    eapply wt_subst_singleton; [exact Hcv2 | exact Hbody].

  (* Unit_step *)
  - destruct (wt_unit_view L ∅ _ Hwt) as [Ht _]. subst t.
    apply ValW.
    + apply env_unr_empty.
    + apply UnitVW.

  (* Pair_step *)
  - destruct (wt_pair_view L ∅ _ _ _ Hwt) as (Γ1 & Γ2 & t1 & t2 & Ht & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]. subst Γ1 Γ2.
    destruct (wt_val_view L _ _ _ H1) as [_ Hcv1].
    destruct (wt_val_view L _ _ _ H2) as [_ Hcv2].
    subst t. apply ValW.
    + apply env_unr_empty.
    + eapply PairVW; [exact Hcv1 | exact Hcv2].

  (* LetPair_step *)
  - destruct (wt_letpair_view L ∅ _ _ _ Hwt) as (Γ1 & Γ2 & t1 & t2 & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]. subst Γ1 Γ2.
    destruct (wt_val_view L _ _ _ H1) as [_ Hcv1].
    destruct (cv_pair_view L _ _ _ _ Hcv1) as [Hcv1a Hcv1b].
    eapply AppW with (Γ:=∅) (Γ1:=∅) (Γ2:=∅) (t1:=t2) (t2:=t) (l:=Lin).
    + apply env_split_nil.
    + eapply AppW with (Γ:=∅) (Γ1:=∅) (Γ2:=∅) (t1:=t1) (t2:=_) (l:=Lin).
      * apply env_split_nil.
      * exact H2.
      * apply ValW; [apply env_unr_empty | exact Hcv1a].
    + apply ValW; [apply env_unr_empty | exact Hcv1b].

  (* Sum_step *)
  - destruct (wt_sum_view L ∅ _ _ _ Hwt) as (n' & ts & i & Ht & Hn & Hv).
    destruct (wt_val_view L _ _ _ Hv) as [_ Hcv].
    subst t. rewrite Hn.
    apply ValW.
    + apply env_unr_empty.
    + eapply SumVW. exact Hcv.

  (* MatchSum_step *)
  - destruct (wt_matchsum_view L ∅ _ _ _ _ Hwt)
      as (Γ1 & Γ2 & ts & Hsplit & Hn0 & Hscrut & Hf).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]. subst Γ1 Γ2.
    destruct (wt_val_view L _ _ _ Hscrut) as [_ Hcv].
    pose proof (cv_sum_fin_view L _ _ _ _ Hcv) as Hcvv.
    eapply AppW.
    + apply env_split_nil.
    + exact (Hf i).
    + apply ValW; [apply env_unr_empty | exact Hcvv].
Qed.

Print Assumptions wt_pure_step.

End Pure.

(* ===== end of pure ===== *)

From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import Strings.String.
Open Scope string_scope.

Section Progress.

Context (L : gmap nat type).

(* A syntactic classification of the possible heads of an expression.
   Variables are included because progress is proved for arbitrary
   environments; at the empty environment they are ruled out separately. *)

Inductive headkind : expr -> Prop :=
  | hk_var x : headkind (Var x)
  | hk_pure e e' : pure_step e e' -> headkind e
  | hk_barrier n v : headkind (App (Val (BarrierV n)) (Val v))
  | hk_forkbar v : headkind (ForkBarrier (Val v))
  | hk_newlock v : headkind (NewLock (Val v))
  | hk_forklock n v : headkind (ForkLock (Val (LockV n)) (Val v))
  | hk_acquire n : headkind (Acquire (Val (LockV n)))
  | hk_release n v : headkind (Release (Val (LockV n)) (Val v))
  | hk_wait n : headkind (Wait (Val (LockV n)))
  | hk_drop n : headkind (Drop (Val (LockV n))).

Definition progress (e : expr) : Prop :=
  (exists v, e = Val v) \/
  (exists k e0, ctx k /\ e = k e0 /\ headkind e0).

Lemma progress_ctx (k : expr -> expr) (e0 : expr) :
  ctx k -> headkind e0 -> progress (k e0).
Proof.
  intros Hk Hh. right. exists k, e0. auto.
Qed.

Lemma progress_ctx1 (k1 : expr -> expr) (H1 : ctx1 k1)
    (k2 : expr -> expr) (e0 : expr) (H2 : ctx k2) (Hh : headkind e0) :
  progress (k1 (k2 e0)).
Proof.
  apply (progress_ctx (k1 ∘ k2) e0).
  - apply (Ctx_comp k1 k2); assumption.
  - exact Hh.
Qed.

Lemma progress_val v : progress (Val v).
Proof. left. exists v. reflexivity. Qed.

Lemma progress_wt Γ e t (H : wt L Γ e t) : progress e.
Proof.
  induction H as
    [ Γ x t Hvar
    | Γ Γ' x e t1 t2 l Hb Hunr Hbody IHbody
    | Γ Γ1 Γ2 e1 e2 t1 t2 l Hsplit H1 IH1 H2 IH2
    | Γ Hunr
    | Γ Γ1 Γ2 e1 e2 t1 t2 Hsplit H1 IH1 H2 IH2
    | Γ Γ1 Γ2 e1 e2 t1 t2 t Hsplit H1 IH1 H2 IH2
    | Γ n ts i e H1 IH1
    | n Γ Γ1 Γ2 t ts es e Hsplit Hn H1 IH1 Hf IHf
    | Γ e t1 t2 H1 IH1
    | Γ e t H1 IH1
    | Γ Γ1 Γ2 e1 e2 t l1 l2 l3 Hsplit Hcap H1 IH1 H2 IH2
    | Γ e t lo H1 IH1
    | Γ Γ1 Γ2 e1 e2 t lo Hsplit H1 IH1 H2 IH2
    | Γ e t H1 IH1
    | Γ e t H1 IH1
    | Γ v t Hunr Hcv0 ] using wt_ind.

  (* VarW *)
  - right. exists id, (Var x). split; [apply Ctx_id | split; [reflexivity | apply hk_var]].

  (* FunW *)
  - right. exists id, (Fun x e). split; [apply Ctx_id | split; [reflexivity | ]].
    apply (hk_pure (Fun x e) (Val (FunV x e))). apply Fun_step.

  (* AppW *)
  - destruct IH1 as [[v1 Hv1] | [k [e0 [Hk [He0 Hh]]]]].
    + rewrite Hv1 in H1. rewrite Hv1.
      destruct (wt_val_view L _ _ _ H1) as [_ Hcv1].
      destruct (cv_fun_inv L _ _ _ _ Hcv1) as [[x [eb Hveq]] | [bn Hveq]].
      * subst v1.
        destruct IH2 as [[v2 Hv2] | [k [e0 [Hk [He0 Hh]]]]].
        -- rewrite Hv2.
           right. exists id, (App (Val (FunV x eb)) (Val v2)).
           split; [apply Ctx_id | split; [reflexivity | ]].
           apply (hk_pure (App (Val (FunV x eb)) (Val v2))
                          (subst x v2 eb)).
           apply (App_step x eb v2).
        -- rewrite He0.
           apply (progress_ctx1 (λ y, App (Val (FunV x eb)) y) (Ctx_App_r (Val (FunV x eb))) k e0 Hk Hh).
      * subst v1.
        destruct IH2 as [[v2 Hv2] | [k [e0 [Hk [He0 Hh]]]]].
        -- rewrite Hv2.
           right. exists id, (App (Val (BarrierV bn)) (Val v2)).
           split; [apply Ctx_id | split; [reflexivity | apply (hk_barrier bn v2)]].
        -- rewrite He0.
           apply (progress_ctx1 (λ x, App (Val (BarrierV bn)) x) (Ctx_App_r (Val (BarrierV bn))) k e0 Hk Hh).
    + rewrite He0.
      apply (progress_ctx1 (λ x, App x e2) (Ctx_App_l e2) k e0 Hk Hh).

  (* UnitW *)
  - right. exists id, Unit. split; [apply Ctx_id | split; [reflexivity | ]].
    apply (hk_pure Unit (Val UnitV)). apply Unit_step.

  (* PairW *)
  - destruct IH1 as [[v1 Hv1] | [k [e0 [Hk [He0 Hh]]]]].
    + rewrite Hv1.
      destruct IH2 as [[v2 Hv2] | [k [e0 [Hk [He0 Hh]]]]].
      * rewrite Hv2.
        right. exists id, (Pair (Val v1) (Val v2)).
        split; [apply Ctx_id | split; [reflexivity | ]].
        apply (hk_pure (Pair (Val v1) (Val v2)) (Val (PairV v1 v2))).
        apply Pair_step.
      * rewrite He0.
        apply (progress_ctx1 (λ x, Pair (Val v1) x) (Ctx_Pair_r (Val v1)) k e0 Hk Hh).
    + rewrite He0.
      apply (progress_ctx1 (λ x, Pair x e2) (Ctx_Pair_l e2) k e0 Hk Hh).

  (* LetPairW *)
  - destruct IH1 as [[v1 Hv1] | [k [e0 [Hk [He0 Hh]]]]].
    + rewrite Hv1 in H1.
      destruct (wt_val_view L _ _ _ H1) as [_ Hcv1].
      destruct (cv_pair_inv L _ _ _ Hcv1) as [a [b [Hveq _]]].
      subst v1. rewrite Hv1.
      right. exists id, (LetPair (Val (PairV a b)) e2).
      split; [apply Ctx_id | split; [reflexivity | ]].
      apply (hk_pure (LetPair (Val (PairV a b)) e2)
                     (App (App e2 (Val a)) (Val b))).
      apply (LetPair_step a b e2).
    + rewrite He0.
      apply (progress_ctx1 (λ x, LetPair x e2) (Ctx_LetPair e2) k e0 Hk Hh).

  (* SumW *)
  - destruct IH1 as [[v Hv] | [k [e0 [Hk [He0 Hh]]]]].
    + rewrite Hv.
      right. exists id, (Sum i (Val v)).
      split; [apply Ctx_id | split; [reflexivity | ]].
      apply (hk_pure (Sum i (Val v)) (Val (SumV i v))).
      apply (Sum_step (fin_to_nat i) v).
    + rewrite He0.
      apply (progress_ctx1 (λ x, Sum i x) (Ctx_Sum i) k e0 Hk Hh).

  (* MatchSumW *)
  - destruct IH1 as [[v Hv] | [k [e0 [Hk [He0 Hh]]]]].
    + rewrite Hv in H1.
      destruct (wt_val_view L _ _ _ H1) as [_ Hcv].
      destruct (cv_sum_inv L _ _ _ Hcv) as [si [sv [Hveq _]]].
      subst v. rewrite Hv.
      right. exists id, (MatchSum n (Val (SumV si sv)) es).
      split; [apply Ctx_id | split; [reflexivity | ]].
      apply (hk_pure (MatchSum n (Val (SumV si sv)) es)
                     (App (es si) (Val sv))).
      apply (MatchSum_step n si sv es).
    + rewrite He0.
      apply (progress_ctx1 (λ x, MatchSum n x es) (Ctx_MatchSum n es)
                           k e0 Hk Hh).

  (* ForkW *)
  - destruct IH1 as [[v Hv] | [k [e0 [Hk [He0 Hh]]]]].
    + rewrite Hv.
      right. exists id, (ForkBarrier (Val v)).
      split; [apply Ctx_id | split; [reflexivity | apply (hk_forkbar v)]].
    + rewrite He0.
      apply (progress_ctx1 (λ x, ForkBarrier x) Ctx_ForkBarrier k e0 Hk Hh).

  (* NewLockW *)
  - destruct IH1 as [[v Hv] | [k [e0 [Hk [He0 Hh]]]]].
    + rewrite Hv.
      right. exists id, (NewLock (Val v)).
      split; [apply Ctx_id | split; [reflexivity | apply (hk_newlock v)]].
    + rewrite He0.
      apply (progress_ctx1 (λ x, NewLock x) Ctx_NewLock k e0 Hk Hh).

  (* ForkLockW *)
  - destruct IH1 as [[v1 Hv1] | [k [e0 [Hk [He0 Hh]]]]].
    + rewrite Hv1 in H1.
      destruct (wt_val_view L _ _ _ H1) as [_ Hcv1].
      destruct (cv_lock_inv L _ _ _ Hcv1) as [ln [Hveq _]].
      subst v1. rewrite Hv1.
      destruct IH2 as [[v2 Hv2] | [k [e0 [Hk [He0 Hh]]]]].
      * rewrite Hv2.
        right. exists id, (ForkLock (Val (LockV ln)) (Val v2)).
        split; [apply Ctx_id | split; [reflexivity | apply (hk_forklock ln v2)]].
      * rewrite He0.
        apply (progress_ctx1 (λ x, ForkLock (Val (LockV ln)) x)
                             (Ctx_ForkLock_r (Val (LockV ln))) k e0 Hk Hh).
    + rewrite He0.
      apply (progress_ctx1 (λ x, ForkLock x e2) (Ctx_ForkLock_l e2)
                           k e0 Hk Hh).

  (* AcquireW *)
  - destruct IH1 as [[v Hv] | [k [e0 [Hk [He0 Hh]]]]].
    + rewrite Hv in H1.
      destruct (wt_val_view L _ _ _ H1) as [_ Hcv].
      destruct (cv_lock_inv L _ _ _ Hcv) as [ln [Hveq _]].
      subst v. rewrite Hv.
      right. exists id, (Acquire (Val (LockV ln))).
      split; [apply Ctx_id | split; [reflexivity | apply (hk_acquire ln)]].
    + rewrite He0.
      apply (progress_ctx1 (λ x, Acquire x) Ctx_Acquire k e0 Hk Hh).

  (* ReleaseW *)
  - destruct IH1 as [[v1 Hv1] | [k [e0 [Hk [He0 Hh]]]]].
    + rewrite Hv1 in H1.
      destruct (wt_val_view L _ _ _ H1) as [_ Hcv1].
      destruct (cv_lock_inv L _ _ _ Hcv1) as [ln [Hveq _]].
      subst v1. rewrite Hv1.
      destruct IH2 as [[v2 Hv2] | [k [e0 [Hk [He0 Hh]]]]].
      * rewrite Hv2.
        right. exists id, (Release (Val (LockV ln)) (Val v2)).
        split; [apply Ctx_id | split; [reflexivity | apply (hk_release ln v2)]].
      * rewrite He0.
        apply (progress_ctx1 (λ x, Release (Val (LockV ln)) x)
                             (Ctx_Release_r (Val (LockV ln))) k e0 Hk Hh).
    + rewrite He0.
      apply (progress_ctx1 (λ x, Release x e2) (Ctx_Release_l e2)
                           k e0 Hk Hh).

  (* WaitW *)
  - destruct IH1 as [[v Hv] | [k [e0 [Hk [He0 Hh]]]]].
    + rewrite Hv in H1.
      destruct (wt_val_view L _ _ _ H1) as [_ Hcv].
      destruct (cv_lock_inv L _ _ _ Hcv) as [ln [Hveq _]].
      subst v. rewrite Hv.
      right. exists id, (Wait (Val (LockV ln))).
      split; [apply Ctx_id | split; [reflexivity | apply (hk_wait ln)]].
    + rewrite He0.
      apply (progress_ctx1 (λ x, Wait x) Ctx_Wait k e0 Hk Hh).

  (* DropW *)
  - destruct IH1 as [[v Hv] | [k [e0 [Hk [He0 Hh]]]]].
    + rewrite Hv in H1.
      destruct (wt_val_view L _ _ _ H1) as [_ Hcv].
      destruct (cv_lock_inv L _ _ _ Hcv) as [ln [Hveq _]].
      subst v. rewrite Hv.
      right. exists id, (Drop (Val (LockV ln))).
      split; [apply Ctx_id | split; [reflexivity | apply (hk_drop ln)]].
    + rewrite He0.
      apply (progress_ctx1 (λ x, Drop x) Ctx_Drop k e0 Hk Hh).

  (* ValW *)
  - apply progress_val.
Qed.

Print Assumptions progress_wt.

End Progress.

(* ===== end of progress ===== *)

From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import Strings.String.
Open Scope string_scope.

Section Closed.

Context (L : gmap nat type).

Lemma wt_var_empty x t (H : wt L ∅ (Var x) t) : False.
Proof.
  inversion H; subst.
  eapply env_var_empty; eassumption.
Qed.

(* Every evaluation-context hole in a closed well-typed expression is
   itself well typed in the empty environment. *)

Lemma wt_ctx1_hole_empty k E t (Hk : ctx1 k)
    (Hwt : wt L ∅ (k E) t) : exists s, wt L ∅ E s.
Proof.
  destruct Hk; cbn in Hwt.
  - destruct (wt_app_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t1 & l & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eauto.
  - destruct (wt_app_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t1 & l & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eauto.
  - destruct (wt_pair_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t1 & t2 & Ht & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eauto.
  - destruct (wt_pair_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t1 & t2 & Ht & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eauto.
  - destruct (wt_letpair_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t1 & t2 & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eauto.
  - destruct (wt_sum_view L ∅ _ _ _ Hwt)
      as (n' & ts & j & Ht & Hn & Hv).
    eauto.
  - destruct (wt_matchsum_view L ∅ _ _ _ _ Hwt)
      as (Γ1 & Γ2 & ts & Hsplit & Hn & H1 & Hf).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eauto.
  - destruct (wt_fork_view L ∅ _ _ Hwt) as (t1 & t2 & Ht & Hv).
    eauto.
  - destruct (wt_newlock_view L ∅ _ _ Hwt) as (t0 & Ht & Hv).
    eauto.
  - destruct (wt_forklock_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t0 & l1 & l2 & l3 & Ht & Hsplit & Hcap & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eauto.
  - destruct (wt_forklock_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t0 & l1 & l2 & l3 & Ht & Hsplit & Hcap & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eauto.
  - destruct (wt_acquire_view L ∅ _ _ Hwt) as (t0 & lo & Ht & Hv).
    eauto.
  - destruct (wt_release_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t0 & lo & Ht & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eauto.
  - destruct (wt_release_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t0 & lo & Ht & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eauto.
  - pose proof (wt_wait_view L ∅ _ _ Hwt) as Hv. eauto.
  - destruct (wt_drop_view L ∅ _ _ Hwt) as [Ht [t0 Hv]]. eauto.
Qed.

Lemma wt_ctx_hole_empty k E t (Hk : ctx k)
    (Hwt : wt L ∅ (k E) t) : exists s, wt L ∅ E s.
Proof.
  revert E t Hwt.
  induction Hk as [| k1 k2 H1 H2 IH2]; intros E t Hwt.
  - cbn in Hwt. exists t. exact Hwt.
  - cbn in Hwt.
    destruct (wt_ctx1_hole_empty k1 (k2 E) t H1 Hwt) as [s Hs].
    exact (IH2 E s Hs).
Qed.

(* A variable cannot occur at the hole of an evaluation context in a
   closed well-typed expression. *)

Lemma wt_ctx_var_empty k x t (Hk : ctx k)
    (Hwt : wt L ∅ (k (Var x)) t) : False.
Proof.
  destruct (wt_ctx_hole_empty k (Var x) t Hk Hwt) as [s Hs].
  exact (wt_var_empty x s Hs).
Qed.

(* Progress at the empty environment: either a value, or an evaluation
   context containing a pure redex, or a context containing one of the
   lock/barrier head operations. *)

Lemma progress_empty e t (H : wt L ∅ e t) :
  (exists v, e = Val v) \/
  (exists k e0, ctx k /\ e = k e0 /\ headkind e0).
Proof.
  exact (progress_wt L ∅ e t H).
Qed.

(* The exact closed, Unit-typed progress statement. *)

Lemma progress_closed_unit e (H : wt L ∅ e UnitT) :
  e = Val UnitV \/
  (exists k e0 e', ctx k /\ e = k e0 /\ pure_step e0 e') \/
  (exists j, expr_waiting e j) \/
  (exists k v, ctx k /\ e = k (ForkBarrier (Val v))) \/
  (exists k v, ctx k /\ e = k (NewLock (Val v))) \/
  (exists k n v, ctx k /\ e = k (ForkLock (Val (LockV n)) (Val v))).
Proof.
  destruct (progress_empty e UnitT H) as [[v Hv] | [k [e0 [Hk [He Hh]]]]].
  - left. rewrite Hv in H. rewrite Hv.
    destruct (wt_val_view L _ _ _ H) as [_ Hcv].
    pose proof (cv_unit_inv L _ Hcv) as Hvv.
    rewrite Hvv. reflexivity.
  - destruct Hh as [x
                  | eh eh' Hps
                  | bn bv
                  | fbv
                  | nlv
                  | fln flv
                  | an
                  | rn rv
                  | wn
                  | dn].
    + exfalso. eapply (wt_ctx_var_empty k x UnitT Hk). rewrite <- He. exact H.
    + right; left. exists k, eh, eh'. repeat split; assumption.
    + right; right; left. exists bn.
      exists k, (App (Val (BarrierV bn)) (Val bv)).
      split; [exact Hk | split; [exact He | apply Barrier_waiting]].
    + right; right; right; left. exists k, fbv.
      split; [exact Hk | exact He].
    + right; right; right; right; left. exists k, nlv.
      split; [exact Hk | exact He].
    + right; right; right; right; right. exists k, fln, flv.
      split; [exact Hk | exact He].
    + right; right; left. exists an.
      exists k, (Acquire (Val (LockV an))).
      split; [exact Hk | split; [exact He | apply Acquire_waiting]].
    + right; right; left. exists rn.
      exists k, (Release (Val (LockV rn)) (Val rv)).
      split; [exact Hk | split; [exact He | apply Release_waiting]].
    + right; right; left. exists wn.
      exists k, (Wait (Val (LockV wn))).
      split; [exact Hk | split; [exact He | apply Wait_waiting]].
    + right; right; left. exists dn.
      exists k, (Drop (Val (LockV dn))).
      split; [exact Hk | split; [exact He | apply Drop_waiting]].
Qed.

Print Assumptions progress_closed_unit.

End Closed.

(* ===== end of closed ===== *)

From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import Strings.String Eqdep_dec.
Open Scope string_scope.

(* ================================================================== *)
(* Unrestricted types: inversion helpers (also present in Task.v).    *)
(* ================================================================== *)

Lemma unr_LockT l t : unr (LockT l t) -> False.
Proof. intros H. inversion H. Qed.

Lemma unr_fun_lin t1 t2 : unr (FunT Lin t1 t2) -> False.
Proof. intros H. inversion H. Qed.

Lemma unr_pair_l t1 t2 : unr (PairT t1 t2) -> unr t1.
Proof. intros H. inversion H. assumption. Qed.

Lemma unr_pair_r t1 t2 : unr (PairT t1 t2) -> unr t2.
Proof. intros H. inversion H. assumption. Qed.

Lemma unr_sum_inv n ts (H : unr (SumT n ts)) : forall i, unr (ts i).
Proof.
  inversion H.
  subst n0.
  apply (inj_pair2_eq_dec nat Nat.eq_dec) in H2.
  subst ts1.
  assumption.
Qed.

Lemma unr_unit : unr UnitT.
Proof. constructor. Qed.

Lemma unr_fun_unr t1 t2 : unr (FunT Unr t1 t2).
Proof. constructor. Qed.

(* ================================================================== *)
(* The naive claim [cv L v t -> unr t -> val_refs v = empty] is FALSE. *)
(*                                                                    *)
(* A function value at an unrestricted function type may have a       *)
(* reference in its body: [cv] only requires the body to be typed,    *)
(* and there is no well-formedness restriction on the body of a       *)
(* runtime function value.  The counterexample below is a function    *)
(* whose body is [Val (BarrierV 7)]; it is [cv]-typed at               *)
(* [FunT Unr UnitT (FunT Lin UnitT UnitT)], which is unrestricted,    *)
(* yet its [val_refs] is [{7}].                                        *)
(* ================================================================== *)

Lemma env_unr_singleton_unit x : env_unr (<[x := UnitT]> (∅ : env)).
Proof.
  intros y s Hy.
  destruct (decide (y = x)) as [E | E].
  - subst y. unfold env in Hy. rewrite lookup_insert_eq in Hy.
    injection Hy as Heq. subst s. apply unr_unit.
  - unfold env in Hy. rewrite lookup_insert_ne in Hy; [| done].
    rewrite lookup_empty in Hy. discriminate.
Qed.

Definition cv_counterexample_val : val :=
  FunV "x" (Val (BarrierV 7)).

Definition cv_counterexample_type : type :=
  FunT Unr UnitT (FunT Lin UnitT UnitT).

Lemma cv_unr_refs_counterexample :
  exists (L : gmap nat type) (v : val) (t : type),
    cv L v t /\ unr t /\ val_refs v <> ∅.
Proof.
  exists (∅ : gmap nat type), cv_counterexample_val, cv_counterexample_type.
  split.
  - unfold cv_counterexample_val, cv_counterexample_type.
    eapply FunVW.
    eapply ValW.
    + apply env_unr_singleton_unit.
    + eapply BarrierVW.
  - split.
    + apply unr_fun_unr.
    + unfold cv_counterexample_val. simpl.
      (* val_refs (FunV "x" (Val (BarrierV 7))) = expr_refs (Val (BarrierV 7)) = {[7]} *)
      intro H. assert (Hmem : 7 ∈ ({[7]} : gset nat))
        by (apply elem_of_singleton; reflexivity).
      rewrite H in Hmem. apply not_elem_of_empty in Hmem. exact Hmem.
Qed.

(* ================================================================== *)
(* Runtime value typing is linearity-blind.                           *)
(*                                                                    *)
(* [cv] (and [cvS] below) has no disjointness side condition on the    *)
(* [PairV] rule, and [LockV] only requires the lock to be typed in     *)
(* [L].  Consequently the duplicated-capability value below is [wt]    *)
(* typable in the empty environment, although no source term can       *)
(* produce it.  Therefore the lock/refcount capability accounting      *)
(* needed for progress at object locations cannot be derived from      *)
(* runtime typing alone; it must be a separate invariant carried       *)
(* along reachability from the source.                                 *)
(* ================================================================== *)

Lemma cv_dup_lock_value L n t lc :
  L !! n = Some t ->
  cv L (PairV (LockV n) (LockV n)) (PairT (LockT lc t) (LockT lc t)).
Proof.
  intros H. apply PairVW; apply LockVW; exact H.
Qed.

Lemma wt_dup_lock_value L n t lc :
  L !! n = Some t ->
  wt L ∅ (Val (PairV (LockV n) (LockV n)))
         (PairT (LockT lc t) (LockT lc t)).
Proof.
  intros H. apply ValW.
  - apply env_unr_empty.
  - apply cv_dup_lock_value. exact H.
Qed.

Print Assumptions wt_dup_lock_value.

(* ================================================================== *)
(* Refined value typing [cvS] and runtime typing [wtS].                *)
(*                                                                    *)
(* The only change with respect to [cv] is the function-value rule:   *)
(* at an unrestricted function type, the body must be reference-free. *)
(* [wtS] is the corresponding runtime typing, using [cvS] for values. *)
(* ================================================================== *)

Inductive cvS (L : gmap nat type) : val -> type -> Prop :=
  | FunVS x e t1 t2 l :
      wt L (<[x := t1]> (∅ : env)) e t2 ->
      (l = Unr -> expr_refs e = ∅) ->
      cvS L (FunV x e) (FunT l t1 t2)
  | UnitVS : cvS L UnitV UnitT
  | PairVS v1 v2 t1 t2 :
      cvS L v1 t1 -> cvS L v2 t2 ->
      cvS L (PairV v1 v2) (PairT t1 t2)
  | SumVS n (ts : fin n -> type) i v :
      cvS L v (ts i) ->
      cvS L (SumV i v) (SumT n ts)
  | BarrierVS n t1 t2 :
      cvS L (BarrierV n) (FunT Lin t1 t2)
  | LockVS n lc t :
      L !! n = Some t ->
      cvS L (LockV n) (LockT lc t).

Inductive wtS (L : gmap nat type) : env -> expr -> type -> Prop :=
  | VarS Γ x t :
      env_var Γ x t ->
      wtS L Γ (Var x) t
  | FunS Γ Γ' x e t1 t2 l :
      env_bind Γ' x t1 Γ ->
      (l = Unr -> env_unr Γ) ->
      wtS L Γ' e t2 ->
      wtS L Γ (Fun x e) (FunT l t1 t2)
  | AppS Γ Γ1 Γ2 e1 e2 t1 t2 l :
      env_split Γ Γ1 Γ2 ->
      wtS L Γ1 e1 (FunT l t1 t2) ->
      wtS L Γ2 e2 t1 ->
      wtS L Γ (App e1 e2) t2
  | UnitS Γ :
      env_unr Γ ->
      wtS L Γ Unit UnitT
  | PairS Γ Γ1 Γ2 e1 e2 t1 t2 :
      env_split Γ Γ1 Γ2 ->
      wtS L Γ1 e1 t1 ->
      wtS L Γ2 e2 t2 ->
      wtS L Γ (Pair e1 e2) (PairT t1 t2)
  | LetPairS Γ Γ1 Γ2 e1 e2 t1 t2 t :
      env_split Γ Γ1 Γ2 ->
      wtS L Γ1 e1 (PairT t1 t2) ->
      wtS L Γ2 e2 (FunT Lin t1 (FunT Lin t2 t)) ->
      wtS L Γ (LetPair e1 e2) t
  | SumS Γ n (ts : fin n -> type) i e :
      wtS L Γ e (ts i) ->
      wtS L Γ (Sum i e) (SumT n ts)
  | MatchSumS n Γ Γ1 Γ2 t (ts : fin n -> type) es e :
      env_split Γ Γ1 Γ2 ->
      (n = 0 -> env_unr Γ2) ->
      wtS L Γ1 e (SumT n ts) ->
      (forall i, wtS L Γ2 (es i) (FunT Lin (ts i) t)) ->
      wtS L Γ (MatchSum n e es) t
  | ForkS Γ e t1 t2 :
      wtS L Γ e (FunT Lin (FunT Lin t2 t1) UnitT) ->
      wtS L Γ (ForkBarrier e) (FunT Lin t1 t2)
  | NewLockS Γ e t :
      wtS L Γ e t ->
      wtS L Γ (NewLock e) (LockT (Owner,Closed) t)
  | ForkLockS Γ Γ1 Γ2 e1 e2 t l1 l2 l3 :
      env_split Γ Γ1 Γ2 ->
      lockcap_split l1 l2 l3 ->
      wtS L Γ1 e1 (LockT l1 t) ->
      wtS L Γ2 e2 (FunT Lin (LockT l2 t) UnitT) ->
      wtS L Γ (ForkLock e1 e2) (LockT l3 t)
  | AcquireS Γ e t lo :
      wtS L Γ e (LockT (lo,Closed) t) ->
      wtS L Γ (Acquire e) (PairT (LockT (lo,Opened) t) t)
  | ReleaseS Γ Γ1 Γ2 e1 e2 t lo :
      env_split Γ Γ1 Γ2 ->
      wtS L Γ1 e1 (LockT (lo,Opened) t) ->
      wtS L Γ2 e2 t ->
      wtS L Γ (Release e1 e2) (LockT (lo,Closed) t)
  | WaitS Γ e t :
      wtS L Γ e (LockT (Owner,Closed) t) ->
      wtS L Γ (Wait e) t
  | DropS Γ e t :
      wtS L Γ e (LockT (Client,Closed) t) ->
      wtS L Γ (Drop e) UnitT
  | ValS Γ v t :
      env_unr Γ ->
      cvS L v t ->
      wtS L Γ (Val v) t.

(* The refined value typing really does exclude references at
   unrestricted types. *)

Lemma cvS_unr_refs L v t (H : cvS L v t) : unr t -> val_refs v = ∅.
Proof.
  induction H as
    [ x e t1 t2 l Hbody Hrefs
    |
    | v1 v2 t1 t2 H1 IH1 H2 IH2
    | n ts i v H1 IH1
    | n t1 t2
    | n lc t Hlookup ].
  - intro Hty. inversion Hty; subst.
    simpl. apply Hrefs. reflexivity.
  - intro. simpl. reflexivity.
  - intro Hty. simpl.
    rewrite (IH1 (unr_pair_l t1 t2 Hty)).
    rewrite (IH2 (unr_pair_r t1 t2 Hty)).
    apply union_empty_l_L.
  - intro Hty. simpl.
    apply (IH1 (unr_sum_inv n ts Hty i)).
  - intro Hty. exfalso. exact (unr_fun_lin t1 t2 Hty).
  - intro Hty. exfalso. exact (unr_LockT lc t Hty).
Qed.

Print Assumptions cvS_unr_refs.

(* Source terms contain no [Val] constructor, so the refined runtime
   typing [wtS] types every source term.  The [ValS] constructor is
   never needed. *)

Lemma typed_to_wtS Γ e t (H : typed Γ e t) : forall L, wtS L Γ e t.
Proof.
  induction H as
    [ Γ x t Hvar
    | Γ Γ' x e t1 t2 l Hb Hunr Hty IH
    | Γ Γ1 Γ2 e1 e2 t1 t2 l Hsplit Hty1 IH1 Hty2 IH2
    | Γ Hunr
    | Γ Γ1 Γ2 e1 e2 t1 t2 Hsplit Hty1 IH1 Hty2 IH2
    | Γ Γ1 Γ2 e1 e2 t1 t2 t Hsplit Hty1 IH1 Hty2 IH2
    | Γ n ts i e Hty IH
    | n Γ Γ1 Γ2 t ts es e Hsplit Hn Hty IH Hf IHf
    | Γ e t1 t2 Hty IH
    | Γ e t Hty IH
    | Γ Γ1 Γ2 e1 e2 t l1 l2 l3 Hsplit Hcap Hty1 IH1 Hty2 IH2
    | Γ e t lo Hty IH
    | Γ Γ1 Γ2 e1 e2 t lo Hsplit Hty1 IH1 Hty2 IH2
    | Γ e t Hty IH
    | Γ e t Hty IH ];
    intros L.
  - apply VarS; exact Hvar.
  - eapply FunS; [ exact Hb | exact Hunr | apply IH ].
  - eapply AppS; [ exact Hsplit | apply IH1 | apply IH2 ].
  - apply UnitS; exact Hunr.
  - eapply PairS; [ exact Hsplit | apply IH1 | apply IH2 ].
  - eapply LetPairS; [ exact Hsplit | apply IH1 | apply IH2 ].
  - eapply SumS; apply IH.
  - eapply MatchSumS; [ exact Hsplit | exact Hn | apply IH | intros i; apply (IHf i L) ].
  - eapply ForkS; apply IH.
  - eapply NewLockS; apply IH.
  - eapply ForkLockS; [ exact Hsplit | exact Hcap | apply IH1 | apply IH2 ].
  - eapply AcquireS; apply IH.
  - eapply ReleaseS; [ exact Hsplit | apply IH1 | apply IH2 ].
  - eapply WaitS; apply IH.
  - eapply DropS; apply IH.
Qed.

Print Assumptions typed_to_wtS.

(* ===== end of values ===== *)

From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import Strings.String.
Open Scope string_scope.

(* Per-thread progress inside an arbitrary configuration.  The thread
   configuration is split off as a singleton plus a frame; the frame is
   [delete i rho].  The only nontrivial part is choosing fresh names for
   the object/thread spawned by [ForkStep]/[NewLockStep] and proving the
   corresponding disjointness side conditions. *)

Lemma cfg_singleton_delete (ρ : cfg) i e (H : ρ !! i = Some (Thread e)) :
  ({[i := Thread e]} : cfg) ∪ delete i ρ = ρ.
Proof.
  change ((<[i := Thread e]> (∅ : cfg)) ∪ delete i ρ = ρ).
  rewrite (union_insert_delete (∅ : cfg) ρ i (Thread e)).
  - apply map_empty_union.
  - apply lookup_empty.
  - exact H.
Qed.

Lemma disjoint_one_delete (ρ : cfg) i x :
  ({[i := x]} : cfg) ##ₘ delete i ρ.
Proof.
  apply map_disjoint_singleton_l_2.
  apply lookup_delete_eq.
Qed.

Lemma disjoint_two_delete (ρ : cfg) i j x y
    (Hjdom : j ∉ dom ρ) (Hji : j ≠ i) :
  ({[i := x; j := y]} : cfg) ##ₘ delete i ρ.
Proof.
  apply map_disjoint_insert_l. split.
  - apply lookup_delete_eq.
  - apply map_disjoint_singleton_l_2.
    rewrite (lookup_delete_ne ρ i j); [| congruence].
    apply not_elem_of_dom. exact Hjdom.
Qed.

Lemma disjoint_three_delete (ρ : cfg) i j n x y z
    (Hjdom : j ∉ dom ρ) (Hndom : n ∉ dom ρ)
    (Hji : j ≠ i) (Hni : n ≠ i) :
  ({[i := x; j := y; n := z]} : cfg) ##ₘ delete i ρ.
Proof.
  apply map_disjoint_insert_l. split.
  - apply lookup_delete_eq.
  - apply map_disjoint_insert_l. split.
    + rewrite (lookup_delete_ne ρ i j); [| congruence].
      apply not_elem_of_dom. exact Hjdom.
    + apply map_disjoint_singleton_l_2.
      rewrite (lookup_delete_ne ρ i n); [| congruence].
      apply not_elem_of_dom. exact Hndom.
Qed.

Section ThreadProgress.

Context (L : gmap nat type).

Lemma thread_progress ρ i e (Hlive : ρ !! i = Some (Thread e))
    (Hwt : wt L ∅ e UnitT) :
  can_step ρ i \/ exists j, waiting ρ i j.
Proof.
  pose proof (progress_closed_unit L e Hwt) as Hcls.
  destruct Hcls as
    [Hv | [Hpure | [Hwait | [Hfork | [Hnew | Hforklock]]]]].

  (* e = Val UnitV: ExitStep *)
  - left. exists (∅ ∪ delete i ρ).
    rewrite <- (cfg_singleton_delete ρ i e Hlive) at 1. rewrite Hv.
    eapply (Frame_step {[i := Thread (Val UnitV)]} ∅ (delete i ρ) i).
    + apply disjoint_one_delete.
    + apply map_disjoint_empty_l.
    + apply Exit_step.

  (* pure redex under a context: PureStep *)
  - destruct Hpure as (k & e0 & e' & Hk & He & Hps).
    left. exists ({[i := Thread (k e')]} ∪ delete i ρ).
    rewrite <- (cfg_singleton_delete ρ i e Hlive) at 1. rewrite He.
    eapply (Frame_step {[i := Thread (k e0)]}
                       {[i := Thread (k e')]} (delete i ρ) i).
    + apply disjoint_one_delete.
    + apply disjoint_one_delete.
    + apply (Pure_step i k e0 e'); assumption.

  (* syntactic waiting head: waiting clause 1 *)
  - destruct Hwait as [j Hw].
    right. exists j. left. exists e. split; assumption.

  (* ForkBarrier (Val v) under a context: ForkStep with fresh names *)
  - destruct Hfork as (k & v & Hk & He).
    left.
    pose (mn := fresh (dom ρ)).
    assert (Hmndom : mn ∉ dom ρ) by apply is_fresh.
    pose (mj := fresh (dom ρ ∪ {[mn]})).
    assert (Hmjnot : mj ∉ dom ρ ∪ {[mn]}) by apply is_fresh.
    assert (Hmjdom : mj ∉ dom ρ).
    { intro Hc. apply Hmjnot. apply elem_of_union_l. exact Hc. }
    assert (Hmjn : mj ≠ mn).
    { intro Hc. apply Hmjnot. apply elem_of_union_r.
      apply elem_of_singleton. exact Hc. }
    assert (Hidom : i ∈ dom ρ).
    { apply elem_of_dom. exists (Thread e). exact Hlive. }
    assert (Hmni : mn ≠ i).
    { intro Hc. apply Hmndom. rewrite Hc. exact Hidom. }
    assert (Hmji : mj ≠ i).
    { intro Hc. apply Hmjdom. rewrite Hc. exact Hidom. }
    exists ({[i := Thread (k (Val (BarrierV mn)));
              mj := Thread (App (Val v) (Val (BarrierV mn)));
              mn := Barrier]} ∪ delete i ρ).
    rewrite <- (cfg_singleton_delete ρ i e Hlive) at 1. rewrite He.
    eapply (Frame_step
              {[i := Thread (k (ForkBarrier (Val v)))]}
              {[i := Thread (k (Val (BarrierV mn)));
                mj := Thread (App (Val v) (Val (BarrierV mn)));
                mn := Barrier]}
              (delete i ρ) i).
    + apply disjoint_one_delete.
    + apply disjoint_three_delete; assumption.
    + eapply (Fork_step i mj mn k v).
      * intro Hc. exact (Hmji (eq_sym Hc)).
      * intro Hc. exact (Hmni (eq_sym Hc)).
      * exact Hmjn.
      * exact Hk.

  (* NewLock (Val v) under a context: NewLockStep with a fresh name *)
  - destruct Hnew as (k & v & Hk & He).
    left.
    pose (mn := fresh (dom ρ)).
    assert (Hmndom : mn ∉ dom ρ) by apply is_fresh.
    assert (Hidom : i ∈ dom ρ).
    { apply elem_of_dom. exists (Thread e). exact Hlive. }
    assert (Hmni : mn ≠ i).
    { intro Hc. apply Hmndom. rewrite Hc. exact Hidom. }
    exists ({[i := Thread (k (Val (LockV mn)));
              mn := Lock 0 (Some v)]} ∪ delete i ρ).
    rewrite <- (cfg_singleton_delete ρ i e Hlive) at 1. rewrite He.
    eapply (Frame_step
              {[i := Thread (k (NewLock (Val v)))]}
              {[i := Thread (k (Val (LockV mn)));
                mn := Lock 0 (Some v)]}
              (delete i ρ) i).
    + apply disjoint_one_delete.
    + apply disjoint_two_delete; assumption.
    + eapply (NewLock_step v k mn i).
      * intro Hc. exact (Hmni (eq_sym Hc)).
      * exact Hk.

  (* ForkLock head: it is a syntactic waiting head *)
  - destruct Hforklock as (k & ln & v & Hk & He).
    right. exists ln. left. exists e. split; [exact Hlive |].
    unfold expr_waiting.
    exists k, (ForkLock (Val (LockV ln)) (Val v)).
    split; [exact Hk | split; [exact He | apply (ForkLock_waiting ln v)]].
Qed.

Print Assumptions thread_progress.

(* Interface combining the per-thread lemma with the missing object-level
   accounting.  [threads_typed] is the runtime-typing invariant on live
   threads; [obj_progress] is exactly the accounting obligation for live
   objects (locks and barriers) that are not threads.  Note that
   [progress_or_wait] cannot be derived from [thread_progress] alone: a live
   [Barrier] or [Lock] is not a thread, so the per-thread lemma says nothing
   about it, and [can_step] at such an index is only available when a matching
   operation is currently observable in some thread/object. *)

Definition progress_or_wait_obj (ρ : cfg) : Prop :=
  forall i, ρ !! i <> None -> can_step ρ i \/ exists j, waiting ρ i j.

Definition threads_typed (ρ : cfg) : Prop :=
  forall i e, ρ !! i = Some (Thread e) -> wt L ∅ e UnitT.

Definition obj_progress (ρ : cfg) : Prop :=
  forall i y, ρ !! i = Some y -> (forall e, y <> Thread e) ->
    can_step ρ i \/ exists j, waiting ρ i j.

Lemma progress_or_wait_of_typed_obj ρ
    (Hty : threads_typed ρ) (Hobj : obj_progress ρ) :
  progress_or_wait_obj ρ.
Proof.
  intros i Hi.
  destruct (ρ !! i) as [y|] eqn:E.
  - destruct y as [e | | rc o].
    + exact (thread_progress ρ i e E (Hty i e E)).
    + apply Hobj with (y := Barrier); [exact E | discriminate].
    + apply Hobj with (y := Lock rc o); [exact E | discriminate].
  - exfalso. exact (Hi eq_refl).
Qed.

Print Assumptions progress_or_wait_of_typed_obj.

End ThreadProgress.

(* ===== end of thread_progress ===== *)

(* ===== ObjectInv body ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From Stdlib Require Import Classical_Prop.
From stdpp Require Import gmap.
From Stdlib Require Import Strings.String.
Open Scope string_scope.

(* ================================================================== *)
(* Object-level capability inventory.                                 *)
(*                                                                    *)
(* The inventory is deliberately abstract in the maps [caps] and      *)
(* [bend]: a future annotated runtime typing (or a reachability      *)
(* invariant) is expected to provide, for every live configuration,   *)
(* the set of holders of each lock capability state and the set of    *)
(* holders of each barrier endpoint.  The fields below are the        *)
(* accounting facts; the only semantic-looking field is              *)
(* [cap_wait_step], which records that a holder of a capability that  *)
(* is itself blocked on the same lock would exhibit a local step at   *)
(* the lock index.  This is the state/ownership typing fact needed to *)
(* replace per-thread syntax, and it is exactly what avoids the       *)
(* MatchSum branch-duplication problem: capability occurrences are    *)
(* holders in live objects, not raw syntactic occurrences.            *)
(* ================================================================== *)

Definition cap_inventory
    (ρ : cfg)
    (caps : nat -> lockcap -> gset nat)   (* lock n, capability state lc *)
    (bend : nat -> gset nat)              (* barrier n, endpoint holders *)
    : Prop :=
  (* every capability occurrence is in a live object which references n *)
  (forall n lc j, j ∈ caps n lc -> ρ !! j <> None) /\
  (forall n lc j, j ∈ caps n lc ->
     exists y, ρ !! j = Some y /\ n ∈ obj_refs y) /\
  (* a blocked holder of a capability for n exposes a step at n *)
  (forall n lc j e,
     j ∈ caps n lc -> ρ !! j = Some (Thread e) -> expr_waiting e n ->
     can_step ρ n) /\
  (* exactly one Opened capability when the lock content is absent *)
  (forall n rc, ρ !! n = Some (Lock rc None) ->
     exists j, caps n (Owner,Opened) ∪ caps n (Client,Opened) = {[j]}) /\
  (* no Opened capability when the lock has content *)
  (forall n rc v, ρ !! n = Some (Lock rc (Some v)) ->
     caps n (Owner,Opened) ∪ caps n (Client,Opened) = ∅) /\
  (* a lock with content has a capability holder (an owner/referencer) *)
  (forall n rc v, ρ !! n = Some (Lock rc (Some v)) ->
     exists lc j, j ∈ caps n lc) /\
  (* [refcnt] counts Client capabilities *)
  (forall n rc o, ρ !! n = Some (Lock rc o) ->
     (0 < rc <-> exists j, j ∈ caps n (Client,Closed) ∪ caps n (Client,Opened))) /\
  (* a live barrier has exactly two endpoint holders *)
  (forall n, ρ !! n = Some Barrier ->
     exists a b, a <> b /\ bend n = {[a;b]}) /\
  (* endpoints live and reference the barrier *)
  (forall n j, j ∈ bend n -> ρ !! j <> None) /\
  (forall n j, j ∈ bend n ->
     exists y, ρ !! j = Some y /\ n ∈ obj_refs y) /\
  (* at most one endpoint can be a thread blocked on the barrier; two
     blocked endpoints would be a synchronisation redex *)
  (forall n j k e e',
     j ∈ bend n -> k ∈ bend n ->
     ρ !! j = Some (Thread e) -> expr_waiting e n ->
     ρ !! k = Some (Thread e') -> expr_waiting e' n -> j = k).

(* A holder that is not itself blocked on n gives a clause-2 waiting
   edge to n. *)

Lemma waiting_of_inventory_ref ρ n j y
    (Hj : ρ !! j = Some y) (Href : n ∈ obj_refs y)
    (Hnotwait : forall e, y = Thread e -> ~ expr_waiting e n) :
  waiting ρ n j.
Proof.
  right. exists y. split; [exact Hj|split; [exact Href|exact Hnotwait]].
Qed.

Section ObjectProgress.

Context {ρ : cfg} {caps : nat -> lockcap -> gset nat} {bend : nat -> gset nat}
        (Hinv : cap_inventory ρ caps bend).

Lemma inv_cap_live n lc j :
  j ∈ caps n lc -> ρ !! j <> None.
Proof. destruct Hinv as (H & _). exact (H n lc j). Qed.

Lemma inv_cap_ref n lc j :
  j ∈ caps n lc -> exists y, ρ !! j = Some y /\ n ∈ obj_refs y.
Proof. destruct Hinv as (_ & H & _). exact (H n lc j). Qed.

Lemma inv_cap_step n lc j e :
  j ∈ caps n lc -> ρ !! j = Some (Thread e) -> expr_waiting e n ->
  can_step ρ n.
Proof. destruct Hinv as (_ & _ & H & _). exact (H n lc j e). Qed.

Lemma inv_cap_holder_waiting n lc j (Hj : j ∈ caps n lc)
    (Hnc : ~ can_step ρ n) :
  waiting ρ n j.
Proof.
  destruct (inv_cap_ref n lc j Hj) as (y & Hy & Hry).
  apply (waiting_of_inventory_ref ρ n j y Hy Hry).
  intros e He. subst y. intros Hw.
  exact (Hnc (inv_cap_step n lc j e Hj Hy Hw)).
Qed.

Lemma inv_barrier_endpoints n (Hbar : ρ !! n = Some Barrier) :
  exists a b, a <> b /\ bend n = {[a;b]}.
Proof. destruct Hinv as (_ & _ & _ & _ & _ & _ & _ & H & _). exact (H n Hbar). Qed.

Lemma inv_bar_endpoint_live n j : j ∈ bend n -> ρ !! j <> None.
Proof. destruct Hinv as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact (H n j). Qed.

Lemma inv_bar_endpoint_ref n j :
  j ∈ bend n -> exists y, ρ !! j = Some y /\ n ∈ obj_refs y.
Proof. destruct Hinv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact (H n j). Qed.

Lemma inv_bar_one_wait n j k e e' :
  j ∈ bend n -> k ∈ bend n ->
  ρ !! j = Some (Thread e) -> expr_waiting e n ->
  ρ !! k = Some (Thread e') -> expr_waiting e' n -> j = k.
Proof. destruct Hinv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact (H n j k e e'). Qed.

Lemma barrier_endpoint_edge n (Hbar : ρ !! n = Some Barrier)
    (Hnc : ~ can_step ρ n) :
  exists j, waiting ρ n j.
Proof.
  destruct (inv_barrier_endpoints n Hbar) as (a & b & Hne & Hbend).
  assert (Ha : a ∈ bend n) by (rewrite Hbend; set_solver).
  assert (Hb : b ∈ bend n) by (rewrite Hbend; set_solver).
  destruct (classic (exists e, ρ !! a = Some (Thread e) /\
                              expr_waiting e n))
      as [[e [Hea Hwa]] | Hna].
  - exists b.
    destruct (inv_bar_endpoint_ref n b Hb) as (y & Hy & Hry).
    apply (waiting_of_inventory_ref ρ n b y Hy Hry).
    intros e' He'. subst y. intros Hwb.
    apply Hne. eapply (inv_bar_one_wait n a b e e'); eassumption.
  - exists a.
    destruct (inv_bar_endpoint_ref n a Ha) as (y & Hy & Hry).
    apply (waiting_of_inventory_ref ρ n a y Hy Hry).
    intros e He. subst y. intros Hwa.
    exact (Hna (ex_intro _ e (conj Hy Hwa))).
Qed.

Lemma lock_none_edge n rc (Hlock : ρ !! n = Some (Lock rc None))
    (Hnc : ~ can_step ρ n) :
  exists j, waiting ρ n j.
Proof.
  destruct Hinv as (_ & _ & _ & Hnone & _).
  destruct (Hnone n rc Hlock) as (j & Hopened).
  assert (Hj : j ∈ caps n (Owner,Opened) ∪ caps n (Client,Opened)).
  { rewrite Hopened. set_solver. }
  apply elem_of_union in Hj. destruct Hj as [Hj|Hj].
  - exists j. exact (inv_cap_holder_waiting n (Owner,Opened) j Hj Hnc).
  - exists j. exact (inv_cap_holder_waiting n (Client,Opened) j Hj Hnc).
Qed.

Lemma lock_some_edge n rc v (Hlock : ρ !! n = Some (Lock rc (Some v)))
    (Hnc : ~ can_step ρ n) :
  exists j, waiting ρ n j.
Proof.
  destruct Hinv as (_ & _ & _ & _ & _ & Hsome & _).
  destruct (Hsome n rc v Hlock) as (lc & j & Hj).
  exists j. exact (inv_cap_holder_waiting n lc j Hj Hnc).
Qed.

End ObjectProgress.

Theorem object_progress_of_inventory ρ caps bend
    (Hinv : cap_inventory ρ caps bend) :
  forall i y, ρ !! i = Some y -> (forall e, y <> Thread e) ->
    can_step ρ i \/ exists j, waiting ρ i j.
Proof.
  intros i y Hi Hnon.
  destruct y as [e | | rc o].
  - exfalso. exact (Hnon e eq_refl).
  - destruct (classic (can_step ρ i)) as [Hc|Hnc].
    + left. exact Hc.
    + right. eapply (barrier_endpoint_edge Hinv); eassumption.
  - destruct (classic (can_step ρ i)) as [Hc|Hnc].
    + left. exact Hc.
    + right. destruct o as [v|].
      * eapply (lock_some_edge Hinv); eassumption.
      * eapply (lock_none_edge Hinv); eassumption.
Qed.

(* Initial configurations contain no locks or barriers, so the inventory is
   trivially satisfied by empty capability/endpoint maps. *)

Definition init_cfg (e : expr) : cfg := {[0 := Thread e]}.

Lemma init_cfg_lookup e n y (H : (init_cfg e) !! n = Some y) :
  n = 0 /\ y = Thread e.
Proof.
  unfold init_cfg in H.
  destruct (decide (n = 0)) as [E|E].
  - subst n. split; [reflexivity|].
    assert (Heq : ({[0 := Thread e]} : cfg) !! 0 = Some (Thread e)).
    { apply lookup_singleton_eq. }
    rewrite Heq in H. injection H as ->. reflexivity.
  - exfalso.
    assert (Heq : ({[0 := Thread e]} : cfg) !! n = None).
    { apply lookup_singleton_ne. congruence. }
    rewrite Heq in H. discriminate.
Qed.

Lemma init_cap_inventory e :
  cap_inventory (init_cfg e)
                (fun _ _ => (∅ : gset nat)) (fun _ => (∅ : gset nat)).
Proof.
  unfold cap_inventory.
  split.
  { intros n lc j Hj. set_solver. }
  split.
  { intros n lc j Hj. set_solver. }
  split.
  { intros n lc j e0 Hj _ _. set_solver. }
  split.
  { intros n0 rc0 H0.
    destruct (init_cfg_lookup e n0 _ H0) as [_ Hy]. discriminate Hy. }
  split.
  { intros n0 rc0 v0 H0.
    destruct (init_cfg_lookup e n0 _ H0) as [_ Hy]. discriminate Hy. }
  split.
  { intros n0 rc0 v0 H0.
    destruct (init_cfg_lookup e n0 _ H0) as [_ Hy]. discriminate Hy. }
  split.
  { intros n0 rc0 o0 H0.
    destruct (init_cfg_lookup e n0 _ H0) as [_ Hy]. discriminate Hy. }
  split.
  { intros n0 H0.
    destruct (init_cfg_lookup e n0 _ H0) as [_ Hy]. discriminate Hy. }
  split.
  { intros n0 j Hj. set_solver. }
  split.
  { intros n0 j Hj. set_solver. }
  { intros n0 j k e0 e1 Hj. set_solver. }
Qed.

(* Feed the inventory into configuration-level progress, together with the
   runtime typing of every live thread. *)

Theorem progress_or_wait_of_typed_inventory
    (L : gmap nat type) ρ caps bend
    (Hty : forall i e, ρ !! i = Some (Thread e) -> wt L ∅ e UnitT)
    (Hinv : cap_inventory ρ caps bend) :
  progress_or_wait_obj ρ.
Proof.
  apply (progress_or_wait_of_typed_obj L ρ Hty).
  exact (object_progress_of_inventory ρ caps bend Hinv).
Qed.

Print Assumptions object_progress_of_inventory.
Print Assumptions init_cap_inventory.
Print Assumptions progress_or_wait_of_typed_inventory.

(* ===== forest chain ===== *)

(* ===== forest Occ.v ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Strings.String.
Import ListNotations.
Open Scope string_scope.

(* ================================================================== *)
(* Reference-occurrence multiplicities.                               *)
(* ================================================================== *)

Definition fin_sum {n} (f : fin n -> nat) : nat :=
  fold_right (fun i acc => f i + acc) 0 (fin_enum n).

(* Generic fold facts.  Keeping [f] opaque avoids simpl normalising the
   lambda in the induction hypothesis. *)
Lemma fold_right_ext {A} (f g : A -> nat -> nat) (b : nat) (l : list A) :
  (forall x acc, f x acc = g x acc) ->
  fold_right f b l = fold_right g b l.
Proof.
  intros H. induction l as [|a l IH]; simpl.
  - done.
  - rewrite H, IH. done.
Qed.

Lemma fold_right_add_zero {A} (g : A -> nat) (l : list A) :
  fold_right (fun i acc => g i + acc) 0 l = 0 ->
  (forall x, x ∈ l -> g x = 0).
Proof.
  induction l as [|a l IH]; simpl; intros H x Hx.
  - set_solver.
  - apply elem_of_cons in Hx. destruct Hx as [->|Hx].
    + lia.
    + apply IH; [lia|done].
Qed.

Lemma fold_right_add_zero' {A} (g : A -> nat) (l : list A) :
  (forall x, x ∈ l -> g x = 0) ->
  fold_right (fun i acc => g i + acc) 0 l = 0.
Proof.
  induction l as [|a l IH]; simpl; intros H.
  - done.
  - rewrite H by set_solver. apply IH. intros x Hx. apply H. set_solver.
Qed.

Lemma fin_enum_complete n (i : fin n) : i ∈ fin_enum n.
Proof.
  induction i as [n|n i IH]; simpl.
  - left.
  - right. apply list_elem_of_fmap. exists i. split; [done|done].
Qed.

Lemma fin_sum_ext {n} (f g : fin n -> nat) :
  (forall i, f i = g i) -> fin_sum f = fin_sum g.
Proof.
  intros H. unfold fin_sum. apply fold_right_ext. intros i acc. by rewrite H.
Qed.

Lemma fin_sum_add {n} (f g : fin n -> nat) :
  fin_sum (fun i => f i + g i) = fin_sum f + fin_sum g.
Proof.
  unfold fin_sum. induction (fin_enum n) as [|a l IH]; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma fold_right_zero {A} (f : A -> nat -> nat) (l : list A) (b : nat) :
  b = 0 -> (forall x acc, f x acc = acc) -> fold_right f b l = 0.
Proof.
  intros Hb Hf. induction l as [|a l IH]; simpl.
  - done.
  - rewrite Hf. apply IH.
Qed.

Lemma fin_sum_zero {n} : fin_sum (fun _ : fin n => 0) = 0.
Proof.
  unfold fin_sum. apply fold_right_zero; [done|]. intros; lia.
Qed.

Lemma fin_sum_mul {n} (f : fin n -> nat) (c : nat) :
  fin_sum (fun i => f i * c) = fin_sum f * c.
Proof.
  unfold fin_sum. induction (fin_enum n) as [|a l IH]; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma fin_sum_eq_zero {n} (g : fin n -> nat) :
  fin_sum g = 0 <-> (forall i, g i = 0).
Proof.
  unfold fin_sum. split.
  - intros H i. eapply fold_right_add_zero; [exact H|apply fin_enum_complete].
  - intros H. apply fold_right_add_zero'. intros i _. apply H.
Qed.

Lemma length_fin_enum n : List.length (fin_enum n) = n.
Proof.
  induction n as [|n IH]; simpl; [done|]. rewrite length_fmap, IH. done.
Qed.

Lemma fold_right_const {A} (c : nat) (l : list A) :
  fold_right (fun _ acc => c + acc) 0 l = c * List.length l.
Proof.
  induction l as [|a l IH]; simpl; [lia|]. rewrite IH. lia.
Qed.

Lemma fin_sum_const n c : fin_sum (fun _ : fin n => c) = c * n.
Proof.
  unfold fin_sum. rewrite fold_right_const, length_fin_enum. done.
Qed.

(* Count occurrences of a reference index [k]; both locks and barriers. *)
Fixpoint occ_expr (k : nat) (e : expr) : nat :=
  match e with
  | Val v => occ_val k v
  | Var _ => 0
  | Fun _ e => occ_expr k e
  | App e1 e2 => occ_expr k e1 + occ_expr k e2
  | Unit => 0
  | Pair e1 e2 => occ_expr k e1 + occ_expr k e2
  | LetPair e1 e2 => occ_expr k e1 + occ_expr k e2
  | Sum _ e => occ_expr k e
  | MatchSum _ e es => occ_expr k e + fin_sum (fun i => occ_expr k (es i))
  | ForkBarrier e => occ_expr k e
  | NewLock e => occ_expr k e
  | ForkLock e1 e2 => occ_expr k e1 + occ_expr k e2
  | Acquire e => occ_expr k e
  | Release e1 e2 => occ_expr k e1 + occ_expr k e2
  | Wait e => occ_expr k e
  | Drop e => occ_expr k e
  end
with occ_val (k : nat) (v : val) : nat :=
  match v with
  | FunV _ e => occ_expr k e
  | UnitV => 0
  | PairV v1 v2 => occ_val k v1 + occ_val k v2
  | SumV _ v => occ_val k v
  | BarrierV i => if decide (k = i) then 1 else 0
  | LockV i => if decide (k = i) then 1 else 0
  end.

(* Number of [Var x] occurrences replaced by [subst x a]. *)
Fixpoint var_occ (x : string) (e : expr) : nat :=
  match e with
  | Val _ => 0
  | Var y => if decide (x = y) then 1 else 0
  | Fun y e => if decide (x = y) then 0 else var_occ x e
  | App e1 e2 => var_occ x e1 + var_occ x e2
  | Unit => 0
  | Pair e1 e2 => var_occ x e1 + var_occ x e2
  | LetPair e1 e2 => var_occ x e1 + var_occ x e2
  | Sum _ e => var_occ x e
  | MatchSum _ e es => var_occ x e + fin_sum (fun i => var_occ x (es i))
  | ForkBarrier e => var_occ x e
  | NewLock e => var_occ x e
  | ForkLock e1 e2 => var_occ x e1 + var_occ x e2
  | Acquire e => var_occ x e
  | Release e1 e2 => var_occ x e1 + var_occ x e2
  | Wait e => var_occ x e
  | Drop e => var_occ x e
  end.

Lemma subst_occ_expr (x : string) (a : val) (k : nat) (e : expr) :
  occ_expr k (subst x a e) = occ_expr k e + var_occ x e * occ_val k a.
Proof.
  induction e as
    [ v | y | y e IH | e1 IH1 e2 IH2 | | e1 IH1 e2 IH2
    | e1 IH1 e2 IH2 | m e IH | n e IH es IHes | e IH | e IH
    | e1 IH1 e2 IH2 | e IH | e1 IH1 e2 IH2 | e IH | e IH ];
    simpl.
  - simpl. lia.
  - destruct (decide (x = y)); simpl; lia.
  - destruct (decide (x = y)).
    + subst y. simpl. lia.
    + simpl. rewrite IH. done.
  - rewrite IH1, IH2. lia.
  - done.
  - rewrite IH1, IH2. lia.
  - rewrite IH1, IH2. lia.
  - rewrite IH. done.
  - rewrite IH.
    rewrite (@fin_sum_ext n (fun i => occ_expr k (subst x a (es i)))
                           (fun i => occ_expr k (es i) + var_occ x (es i) * occ_val k a)).
    + rewrite fin_sum_add, fin_sum_mul. nia.
    + intro i. apply IHes.
  - rewrite IH. done.
  - rewrite IH. done.
  - rewrite IH1, IH2. lia.
  - rewrite IH. done.
  - rewrite IH1, IH2. lia.
  - rewrite IH. done.
  - rewrite IH. done.
Qed.

Corollary subst_occ_zero x a k e :
  occ_val k a = 0 ->
  occ_expr k (subst x a e) = occ_expr k e.
Proof. intros H. rewrite subst_occ_expr, H. lia. Qed.

(* Object/configuration multiplicity. *)
Definition occ_obj (k : nat) (o : obj) : nat :=
  match o with
  | Thread e => occ_expr k e
  | Barrier => 0
  | Lock _ (Some v) => occ_val k v
  | Lock _ None => 0
  end.

Definition occ_cfg (rho : cfg) (a b : nat) : nat :=
  match rho !! a with
  | Some o => occ_obj b o
  | None => 0
  end.

(* Multiplicity-based no-aliasing (FALSE for this calculus; kept for the
   record and refuted in Counterexample.v). *)
Definition pair_occ_le1 (rho : cfg) : Prop :=
  (forall a, occ_cfg rho a a = 0) /\
  (forall a b, a <> b -> occ_cfg rho a b + occ_cfg rho b a <= 1).

(* ================================================================== *)
(* Typed source expressions have multiplicity zero everywhere.        *)
(* This is the initial condition for the occurrence forest.           *)
(* ================================================================== *)

Lemma typed_occ_zero (Gamma : env) (e : expr) (t : type) :
  typed Gamma e t -> forall k, occ_expr k e = 0.
Proof.
  intros H k. induction H as
    [ Gamma x t Hvar
    | Gamma Gamma' x e t1 t2 l Hb Hunr Hty IH
    | Gamma Gamma1 Gamma2 e1 e2 t1 t2 l Hs H1 IH1 H2 IH2
    | Gamma Hunr
    | Gamma Gamma1 Gamma2 e1 e2 t1 t2 Hs H1 IH1 H2 IH2
    | Gamma Gamma1 Gamma2 e1 e2 t1 t2 t Hs H1 IH1 H2 IH2
    | Gamma n ts i e Hty IH
    | n Gamma Gamma1 Gamma2 t ts es e Hs Hn H1 IH1 Hf IHf
    | Gamma e t1 t2 Hty IH
    | Gamma e t Hty IH
    | Gamma Gamma1 Gamma2 e1 e2 t l1 l2 l3 Hs Hcap H1 IH1 H2 IH2
    | Gamma e t lo Hty IH
    | Gamma Gamma1 Gamma2 e1 e2 t lo Hs H1 IH1 H2 IH2
    | Gamma e t Hty IH
    | Gamma e t Hty IH ]; simpl.
  - done.                                        (* Var *)
  - apply IH.                                    (* Fun *)
  - rewrite IH1, IH2. lia.                       (* App *)
  - done.                                        (* Unit *)
  - rewrite IH1, IH2. lia.                       (* Pair *)
  - rewrite IH1, IH2. lia.                       (* LetPair *)
  - apply IH.                                    (* Sum *)
  - rewrite IH1. simpl.                          (* MatchSum *)
    apply fin_sum_eq_zero. intro i. apply IHf.
  - apply IH.                                    (* ForkBarrier *)
  - apply IH.                                    (* NewLock *)
  - rewrite IH1, IH2. lia.                       (* ForkLock *)
  - apply IH.                                    (* Acquire *)
  - rewrite IH1, IH2. lia.                       (* Release *)
  - apply IH.                                    (* Wait *)
  - apply IH.                                    (* Drop *)
Qed.

Corollary typed_obj_occ_zero (Gamma : env) (e : expr) (t : type) k :
  typed Gamma e t -> occ_obj k (Thread e) = 0.
Proof. intro H. exact (typed_occ_zero Gamma e t H k). Qed.
(* ===== forest Refs.v ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Strings.String.
Import ListNotations.
Open Scope string_scope.


(* ================================================================== *)
(* Set-based reference graph.                                         *)
(* ================================================================== *)

Definition refs_at (ρ : cfg) (a : nat) : gset nat :=
  match ρ !! a with
  | Some o => obj_refs o
  | None => ∅
  end.

Definition socc (ρ : cfg) (a b : nat) : nat :=
  if decide (b ∈ refs_at ρ a) then 1 else 0.

Definition self_ref_free (ρ : cfg) : Prop :=
  forall a, a ∉ refs_at ρ a.

Definition pair_ref_ok (ρ : cfg) : Prop :=
  forall a b, a <> b -> ~ (b ∈ refs_at ρ a /\ a ∈ refs_at ρ b).

Definition ref_pair_ok (ρ : cfg) : Prop :=
  self_ref_free ρ /\ pair_ref_ok ρ.

(* The coordinator's multiplicity=1 formulation at the set level. *)
Definition pair_socc_le1 (ρ : cfg) : Prop :=
  (forall a, socc ρ a a = 0) /\
  (forall a b, a <> b -> socc ρ a b + socc ρ b a <= 1).

Lemma socc_le1 ρ a b : socc ρ a b <= 1.
Proof. unfold socc. destruct (decide (b ∈ refs_at ρ a)); lia. Qed.

Lemma socc_pos ρ a b : 0 < socc ρ a b <-> b ∈ refs_at ρ a.
Proof.
  unfold socc. destruct (decide (b ∈ refs_at ρ a)) as [H|H]; simpl.
  - split; intros; [exact H|lia].
  - split; intros; [lia|exfalso; exact (H H0)].
Qed.

Lemma socc_zero ρ a b : socc ρ a b = 0 <-> b ∉ refs_at ρ a.
Proof.
  unfold socc. destruct (decide (b ∈ refs_at ρ a)) as [H|H]; simpl.
  - split; intros Hx.
    + lia.
    + exfalso. exact (Hx H).
  - split; intros Hx; [exact H|reflexivity].
Qed.

Lemma socc_one_of_mem ρ a b : b ∈ refs_at ρ a -> socc ρ a b = 1.
Proof.
  intros H. unfold socc. destruct (decide (b ∈ refs_at ρ a)); [done|contradiction].
Qed.

Lemma socc_zero_of_not_mem ρ a b : b ∉ refs_at ρ a -> socc ρ a b = 0.
Proof. intros H. apply (proj2 (socc_zero ρ a b)), H. Qed.

Lemma pair_socc_le1_iff ρ : pair_socc_le1 ρ <-> ref_pair_ok ρ.
Proof.
  unfold pair_socc_le1, ref_pair_ok, self_ref_free, pair_ref_ok. split.
  - intros [Hself Hpair]. split.
    + intros a Ha. pose proof (proj2 (socc_pos ρ a a) Ha) as Hpos.
      rewrite Hself in Hpos. lia.
    + intros a b Hne [Hb Ha].
      specialize (Hpair a b Hne).
      rewrite (socc_one_of_mem ρ a b Hb), (socc_one_of_mem ρ b a Ha) in Hpair.
      lia.
  - intros [Hself Hpair]. split.
    + intros a. apply (proj2 (socc_zero ρ a a)), Hself.
    + intros a b Hne.
      destruct (decide (b ∈ refs_at ρ a)) as [Hb|Hb];
      destruct (decide (a ∈ refs_at ρ b)) as [Ha|Ha].
      * exfalso. apply (Hpair a b Hne). done.
      * rewrite (socc_one_of_mem ρ a b Hb).
        rewrite (socc_zero_of_not_mem ρ b a Ha). lia.
      * rewrite (socc_zero_of_not_mem ρ a b Hb).
        rewrite (socc_one_of_mem ρ b a Ha). lia.
      * rewrite (socc_zero_of_not_mem ρ a b Hb).
        rewrite (socc_zero_of_not_mem ρ b a Ha). lia.
Qed.

(* A step that only removes references preserves no-aliasing. *)
Lemma refs_shrink_ref_pair_ok ρ ρ' :
  (forall a, refs_at ρ' a ⊆ refs_at ρ a) ->
  ref_pair_ok ρ -> ref_pair_ok ρ'.
Proof.
  intros Hsub [Hself Hpair]. split.
  - intros a Ha. apply (Hself a), (Hsub a), Ha.
  - intros a b Hne [Hb Ha]. apply (Hpair a b Hne). split.
    + apply (Hsub a), Hb.
    + apply (Hsub b), Ha.
Qed.

(* ================================================================== *)
(* Waiting edges are reference edges.                                 *)
(* ================================================================== *)

Lemma ctx1_expr_refs k (Hk : ctx1 k) e :
  expr_refs e ⊆ expr_refs (k e).
Proof. destruct Hk; simpl; set_solver. Qed.

Lemma ctx_expr_refs k (Hk : ctx k) e :
  expr_refs e ⊆ expr_refs (k e).
Proof.
  induction Hk as [|k1 k2 H1 H2 IH2]; simpl.
  - intros j Hj. exact Hj.
  - intros j Hj. apply (ctx1_expr_refs k1 H1). apply IH2. exact Hj.
Qed.

Lemma expr_head_waiting_ref j e :
  expr_head_waiting e j -> j ∈ expr_refs e.
Proof. intros H. induction H; simpl; set_solver. Qed.

Lemma ctx_head_waiting_ref k e j :
  ctx k -> expr_head_waiting e j -> j ∈ expr_refs (k e).
Proof.
  intros Hk Hh. apply (ctx_expr_refs k Hk e).
  apply expr_head_waiting_ref in Hh. exact Hh.
Qed.

Lemma expr_waiting_ref e j : expr_waiting e j -> j ∈ expr_refs e.
Proof.
  intros [k [e' [Hk [He Hh]]]]. subst e.
  apply ctx_head_waiting_ref; assumption.
Qed.

Definition refs_live (ρ : cfg) : Prop :=
  forall i y, ρ !! i = Some y -> forall j, j ∈ obj_refs y -> ρ !! j <> None.

Lemma thread_waiting_ref ρ i j e :
  ρ !! i = Some (Thread e) -> expr_waiting e j -> j ∈ refs_at ρ i.
Proof.
  intros Hi Hw. unfold refs_at. rewrite Hi. simpl.
  apply expr_waiting_ref in Hw. exact Hw.
Qed.

Lemma obj_refs_at ρ j i y :
  ρ !! j = Some y -> i ∈ obj_refs y -> i ∈ refs_at ρ j.
Proof.
  intros Hj Hi. unfold refs_at. rewrite Hj. exact Hi.
Qed.

Lemma waiting_ref ρ i j :
  waiting ρ i j -> j ∈ refs_at ρ i \/ i ∈ refs_at ρ j.
Proof.
  intros [[e [Hi Hw]]|[y [Hj [Hi _]]]].
  - left. apply (thread_waiting_ref ρ i j e); assumption.
  - right. apply (obj_refs_at ρ j i y); assumption.
Qed.

Lemma waiting_neq ρ i j :
  self_ref_free ρ -> waiting ρ i j -> i <> j.
Proof.
  intros Hsf Hw E. subst j. destruct (waiting_ref ρ i i Hw) as [H|H];
  exact (Hsf i H).
Qed.

(* Two mutual waiting edges force references in both directions, which the
   set-based pair condition forbids. *)
Lemma no_waiting_2cycle ρ i j :
  ref_pair_ok ρ -> waiting ρ i j -> waiting ρ j i -> False.
Proof.
  intros [Hsf Hpair] Hwij Hwji.
  assert (Hne : i <> j) by (apply (waiting_neq ρ i j Hsf Hwij)).
  destruct Hwij as [[e [Hi Hw]]|[y [Hj [Hy Hside]]]];
  destruct Hwji as [[e2 [Hj2 Hw2]]|[y2 [Hi2 [Hy2 Hside2]]]].
  - apply (Hpair i j Hne). split.
    + apply (thread_waiting_ref ρ i j e); assumption.
    + apply (thread_waiting_ref ρ j i e2); assumption.
  - (* the object at i cannot be both a waiting thread and exempt *)
    rewrite Hi in Hi2. injection Hi2 as Ey. subst y2.
    exact (Hside2 e eq_refl Hw).
  - (* dually, the object at j cannot be both a waiting thread and exempt *)
    rewrite Hj2 in Hj. injection Hj as Ey. subst y.
    exact (Hside e2 eq_refl Hw2).
  - apply (Hpair i j Hne). split.
    + apply (obj_refs_at ρ i j y2); assumption.
    + apply (obj_refs_at ρ j i y); assumption.
Qed.

(* A self waiting edge is excluded by self-reference freedom. *)
Lemma no_waiting_self ρ i :
  self_ref_free ρ -> ~ waiting ρ i i.
Proof.
  intros Hsf Hw. destruct (waiting_ref ρ i i Hw) as [H|H]; exact (Hsf i H).
Qed.

(* ================================================================== *)
(* Undirected simple graph and forests.                               *)
(* ================================================================== *)

Definition ref_edge (ρ : cfg) (a b : nat) : Prop :=
  a <> b /\ (b ∈ refs_at ρ a \/ a ∈ refs_at ρ b).

Lemma ref_edge_sym ρ a b : ref_edge ρ a b <-> ref_edge ρ b a.
Proof.
  unfold ref_edge. split; intros [Hne [H|H]]; split; auto; tauto.
Qed.

Inductive path_edges (R : nat -> nat -> Prop) : list nat -> Prop :=
  | pe_nil : path_edges R []
  | pe_one a : path_edges R [a]
  | pe_cons a b l : R a b -> path_edges R (b :: l) -> path_edges R (a :: b :: l).

Definition list_cycle (R : nat -> nat -> Prop) (l : list nat) : Prop :=
  3 <= List.length l /\ NoDup l /\
  path_edges R (l ++ [List.hd 0 l]).

Definition ref_forest (ρ : cfg) : Prop :=
  forall l, ~ list_cycle (ref_edge ρ) l.

Lemma waiting_path_edges_ref ρ l :
  ref_pair_ok ρ ->
  path_edges (waiting ρ) l -> path_edges (ref_edge ρ) l.
Proof.
  intros [Hsf Hpair] Hp. induction Hp as [|a|a b l Hw Hrest IH].
  - constructor.
  - constructor.
  - apply pe_cons.
    + split.
      * apply (waiting_neq ρ a b Hsf Hw).
      * apply (waiting_ref ρ a b Hw).
    + exact IH.
Qed.

(* No directed waiting cycle of length at least three in a forest. *)
Lemma no_waiting_cycle_of_forest ρ l :
  ref_pair_ok ρ -> ref_forest ρ ->
  NoDup l -> 3 <= List.length l ->
  path_edges (waiting ρ) (l ++ [List.hd 0 l]) -> False.
Proof.
  intros Hpair Hforest Hnd Hlen Hpath.
  apply (Hforest l). split; [exact Hlen|]. split; [exact Hnd|].
  apply waiting_path_edges_ref; assumption.
Qed.

(* ================================================================== *)
(* Membership for fin_union and monotonicity.                         *)
(* ================================================================== *)

Lemma elem_of_big_union {A} `{Countable A} (T : gset (gset A)) x :
  x ∈ big_union T <-> exists Y, Y ∈ T /\ x ∈ Y.
Proof.
  unfold big_union.
  eapply (set_fold_ind_L (fun (r : gset A) (Z : gset (gset A)) =>
      x ∈ r <-> exists Y, Y ∈ Z /\ x ∈ Y)).
  - simpl. split; [set_solver|]. intros [Y [HY _]]. set_solver.
  - intros y Z r HyZ IH. simpl.
    rewrite elem_of_union. split.
    + intros [Hxy|Hr].
      * exists y. split; [set_solver|exact Hxy].
      * destruct IH as [Hex _]. destruct (Hex Hr) as [Y [HY HxY]].
        exists Y. split; [set_solver|exact HxY].
    + intros [Y [HY HxY]]. rewrite elem_of_union in HY.
      destruct HY as [HY|HY].
      * apply elem_of_singleton in HY. subst Y. left. exact HxY.
      * right. apply IH. exists Y. split; [exact HY|exact HxY].
Qed.

Lemma fin_list_map {A} n (f : fin n -> A) :
  fin_list n f = List.map f (fin_enum n).
Proof.
  unfold fin_list. induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite (IH (f ∘ FS)).
    rewrite List.map_map. reflexivity.
Qed.

Lemma mem_fin_list_map {A} n (f : fin n -> A) (Y : A) :
  Y ∈ fin_list n f <-> exists i, Y = f i.
Proof.
  rewrite fin_list_map, list_elem_of_fmap. split.
  - intros [i [Hi _]]. exists i. exact Hi.
  - intros [i Hi]. exists i. split; [exact Hi|apply fin_enum_complete].
Qed.

Lemma elem_of_fin_gset {A} `{Countable A} n (f : fin n -> gset A) (Y : gset A) :
  Y ∈ fin_gset n f <-> exists i, Y = f i.
Proof.
  unfold fin_gset. rewrite elem_of_list_to_set. apply mem_fin_list_map.
Qed.

Lemma elem_of_fin_union {A} `{Countable A} n (f : fin n -> gset A) x :
  x ∈ fin_union n f <-> exists i, x ∈ f i.
Proof.
  unfold fin_union. rewrite elem_of_big_union. split.
  - intros [Y [HY HxY]]. apply elem_of_fin_gset in HY.
    destruct HY as [i ->]. exists i. exact HxY.
  - intros [i Hi]. exists (f i). split.
    + apply elem_of_fin_gset. exists i. reflexivity.
    + exact Hi.
Qed.

Lemma fin_union_incl {A} `{Countable A} n (f : fin n -> gset A) i :
  f i ⊆ fin_union n f.
Proof.
  intros x Hx. apply elem_of_fin_union. exists i. exact Hx.
Qed.

Lemma fin_union_mono {A} `{Countable A} n (f g : fin n -> gset A) :
  (forall i, f i ⊆ g i) -> fin_union n f ⊆ fin_union n g.
Proof.
  intros Hsub x Hx. apply elem_of_fin_union in Hx.
  destruct Hx as [i Hi]. apply elem_of_fin_union. exists i. apply Hsub. exact Hi.
Qed.

(* ================================================================== *)
(* Substitution can only shrink / preserve the set of references.     *)
(* ================================================================== *)

Lemma subst_expr_refs_subset x a e :
  expr_refs (subst x a e) ⊆ expr_refs e ∪ val_refs a.
Proof.
  induction e as
    [ v | y | y e IH | e1 IH1 e2 IH2 | | e1 IH1 e2 IH2
    | e1 IH1 e2 IH2 | m e IH | n e IH es IHes | e IH | e IH
    | e1 IH1 e2 IH2 | e IH | e1 IH1 e2 IH2 | e IH | e IH ];
    simpl.
  - set_solver.
  - destruct (decide (x = y)); set_solver.
  - destruct (decide (x = y)); set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - intros z Hz. apply elem_of_union in Hz. destruct Hz as [Hz|Hz].
    + pose proof (IH z Hz) as Hz'. apply elem_of_union in Hz'.
      destruct Hz' as [Hz'|Hz'].
      * apply elem_of_union. left. apply elem_of_union. left. exact Hz'.
      * apply elem_of_union. right. exact Hz'.
    + apply elem_of_fin_union in Hz. destruct Hz as [i Hi].
      pose proof (IHes i z Hi) as Hz'. apply elem_of_union in Hz'.
      destruct Hz' as [Hz'|Hz'].
      * apply elem_of_union. left. apply elem_of_union. right.
        apply elem_of_fin_union. exists i. exact Hz'.
      * apply elem_of_union. right. exact Hz'.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
Qed.

Lemma ctx1_expr_refs_eq k (Hk : ctx1 k) e :
  expr_refs (k e) = expr_refs e ∪ expr_refs (k (Var "ctx_hole")).
Proof. destruct Hk; simpl; set_solver. Qed.

Lemma ctx_expr_refs_eq k (Hk : ctx k) e :
  expr_refs (k e) = expr_refs e ∪ expr_refs (k (Var "ctx_hole")).
Proof.
  induction Hk as [|k1 k2 H1 H2 IH2]; simpl.
  - set_solver.
  - rewrite (ctx1_expr_refs_eq k1 H1 (k2 e)).
    rewrite (ctx1_expr_refs_eq k1 H1 (k2 (Var "ctx_hole"))).
    rewrite IH2. set_solver.
Qed.

Lemma ctx_expr_refs_mono k (Hk : ctx k) e e' :
  expr_refs e' ⊆ expr_refs e -> expr_refs (k e') ⊆ expr_refs (k e).
Proof.
  intros Hsub. rewrite (ctx_expr_refs_eq k Hk e'), (ctx_expr_refs_eq k Hk e).
  set_solver.
Qed.

Lemma pure_step_refs_subset e e' :
  pure_step e e' -> expr_refs e' ⊆ expr_refs e.
Proof.
  intros H. destruct H; simpl.
  - set_solver.
  - etransitivity; [apply subst_expr_refs_subset|]. set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - intros z Hz. apply elem_of_union in Hz. destruct Hz as [Hz|Hz].
    + apply elem_of_union. right.
      apply elem_of_fin_union. exists i. exact Hz.
    + apply elem_of_union. left. exact Hz.
Qed.

(* ================================================================== *)
(* Local shrinking steps.                                             *)
(* ================================================================== *)

Lemma Pure_local_shrink i k e e' :
  ctx k -> pure_step e e' ->
  forall a, refs_at ({[i := Thread (k e')]} : cfg) a ⊆ refs_at ({[i := Thread (k e)]} : cfg) a.
Proof.
  intros Hk Hps a.
  destruct (decide (a = i)) as [->|Hne].
  - assert (E1 : ({[i := Thread (k e')]} : cfg) !! i = Some (Thread (k e'))).
    { change ((<[i := Thread (k e')]> (∅ : cfg)) !! i = Some (Thread (k e'))).
      apply lookup_insert_eq. }
    assert (E2 : ({[i := Thread (k e)]} : cfg) !! i = Some (Thread (k e))).
    { change ((<[i := Thread (k e)]> (∅ : cfg)) !! i = Some (Thread (k e))).
      apply lookup_insert_eq. }
    unfold refs_at. rewrite E1, E2. simpl.
    apply ctx_expr_refs_mono; [exact Hk|apply pure_step_refs_subset; exact Hps].
  - assert (E1 : ({[i := Thread (k e')]} : cfg) !! a = (∅ : cfg) !! a).
    { change ((<[i := Thread (k e')]> (∅ : cfg)) !! a = (∅ : cfg) !! a).
      apply lookup_insert_ne. intro E. apply Hne. symmetry. exact E. }
    assert (E2 : ({[i := Thread (k e)]} : cfg) !! a = (∅ : cfg) !! a).
    { change ((<[i := Thread (k e)]> (∅ : cfg)) !! a = (∅ : cfg) !! a).
      apply lookup_insert_ne. intro E. apply Hne. symmetry. exact E. }
    unfold refs_at. rewrite E1, E2. simpl. set_solver.
Qed.

Lemma Exit_local_shrink i :
  forall a, refs_at (∅ : cfg) a ⊆ refs_at ({[i := Thread (Val UnitV)]} : cfg) a.
Proof. intros a. unfold refs_at. simpl. set_solver. Qed.

Lemma Pure_step_ref_pair_ok i k e e' :
  ctx k -> pure_step e e' ->
  ref_pair_ok ({[i := Thread (k e)]} : cfg) ->
  ref_pair_ok ({[i := Thread (k e')]} : cfg).
Proof.
  intros Hk Hps. apply refs_shrink_ref_pair_ok.
  apply Pure_local_shrink; assumption.
Qed.

Lemma Exit_step_ref_pair_ok i :
  ref_pair_ok ({[i := Thread (Val UnitV)]} : cfg) ->
  ref_pair_ok (∅ : cfg).
Proof.
  intros. apply refs_shrink_ref_pair_ok with (ρ := ({[i := Thread (Val UnitV)]} : cfg)).
  - apply Exit_local_shrink.
  - exact H.
Qed.
(* ===== forest Moves.v ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Strings.String.
Import ListNotations.
Open Scope string_scope.


(* ================================================================== *)
(* Generic reference sets of inserted maps.                           *)
(* ================================================================== *)

Lemma ne_sym {A} {a b : A} : a <> b -> b <> a.
Proof. intros H E. apply H. symmetry. exact E. Qed.

Lemma refs_at_empty a : refs_at (∅ : cfg) a = ∅.
Proof. unfold refs_at. simpl. done. Qed.

Lemma refs_at_insert_same (ρ : cfg) a o :
  refs_at (<[a := o]> ρ) a = obj_refs o.
Proof.
  assert (E : (<[a := o]> ρ) !! a = Some o) by apply lookup_insert_eq.
  unfold refs_at. rewrite E. reflexivity.
Qed.

Lemma refs_at_insert_ne (ρ : cfg) a b o :
  a <> b -> refs_at (<[a := o]> ρ) b = refs_at ρ b.
Proof.
  intros Hne.
  assert (E : (<[a := o]> ρ) !! b = ρ !! b).
  { apply lookup_insert_ne. exact Hne. }
  unfold refs_at. rewrite E. reflexivity.
Qed.

(* Notation-level accessors for 1, 2 and 3 entry map literals. *)
Lemma refs_at_map1 (a : nat) (x : obj) :
  refs_at ({[a := x]} : cfg) a = obj_refs x.
Proof.
  change (refs_at (<[a := x]> (∅ : cfg)) a = obj_refs x).
  apply refs_at_insert_same.
Qed.

Lemma refs_at_map1_other (a b : nat) (x : obj) :
  b <> a -> refs_at ({[a := x]} : cfg) b = ∅.
Proof.
  intros Hba.
  change (refs_at (<[a := x]> (∅ : cfg)) b = ∅).
  rewrite refs_at_insert_ne.
  - rewrite refs_at_empty. reflexivity.
  - apply ne_sym. exact Hba.
Qed.

Lemma refs_at_map2_fst (a b : nat) (x y : obj) :
  a <> b -> refs_at ({[a := x; b := y]} : cfg) a = obj_refs x.
Proof.
  intros Hab.
  change (refs_at (<[a := x]> (<[b := y]> (∅ : cfg))) a = obj_refs x).
  apply refs_at_insert_same.
Qed.

Lemma refs_at_map2_snd (a b : nat) (x y : obj) :
  a <> b -> refs_at ({[a := x; b := y]} : cfg) b = obj_refs y.
Proof.
  intros Hab.
  change (refs_at (<[a := x]> (<[b := y]> (∅ : cfg))) b = obj_refs y).
  rewrite refs_at_insert_ne by exact Hab.
  apply refs_at_insert_same.
Qed.

Lemma refs_at_map2_other (a b c : nat) (x y : obj) :
  c <> a -> c <> b -> refs_at ({[a := x; b := y]} : cfg) c = ∅.
Proof.
  intros Hca Hcb.
  change (refs_at (<[a := x]> (<[b := y]> (∅ : cfg))) c = ∅).
  rewrite refs_at_insert_ne by (apply ne_sym; exact Hca).
  rewrite refs_at_insert_ne by (apply ne_sym; exact Hcb).
  apply refs_at_empty.
Qed.

Lemma refs_at_map3_fst (a b c : nat) (x y z : obj) :
  a <> b -> a <> c ->
  refs_at ({[a := x; b := y; c := z]} : cfg) a = obj_refs x.
Proof.
  intros.
  change (refs_at (<[a := x]> (<[b := y]> (<[c := z]> (∅ : cfg)))) a = obj_refs x).
  apply refs_at_insert_same.
Qed.

Lemma refs_at_map3_snd (a b c : nat) (x y z : obj) :
  b <> a -> b <> c ->
  refs_at ({[a := x; b := y; c := z]} : cfg) b = obj_refs y.
Proof.
  intros Hba Hbc.
  change (refs_at (<[a := x]> (<[b := y]> (<[c := z]> (∅ : cfg)))) b = obj_refs y).
  rewrite refs_at_insert_ne by (apply ne_sym; exact Hba).
  apply refs_at_insert_same.
Qed.

Lemma refs_at_map3_trd (a b c : nat) (x y z : obj) :
  c <> a -> c <> b ->
  refs_at ({[a := x; b := y; c := z]} : cfg) c = obj_refs z.
Proof.
  intros Hca Hcb.
  change (refs_at (<[a := x]> (<[b := y]> (<[c := z]> (∅ : cfg)))) c = obj_refs z).
  rewrite refs_at_insert_ne by (apply ne_sym; exact Hca).
  rewrite refs_at_insert_ne by (apply ne_sym; exact Hcb).
  apply refs_at_insert_same.
Qed.

Lemma refs_at_map3_other (a b c d : nat) (x y z : obj) :
  d <> a -> d <> b -> d <> c ->
  refs_at ({[a := x; b := y; c := z]} : cfg) d = ∅.
Proof.
  intros Hda Hdb Hdc.
  change (refs_at (<[a := x]> (<[b := y]> (<[c := z]> (∅ : cfg)))) d = ∅).
  rewrite refs_at_insert_ne by (apply ne_sym; exact Hda).
  rewrite refs_at_insert_ne by (apply ne_sym; exact Hdb).
  rewrite refs_at_insert_ne by (apply ne_sym; exact Hdc).
  apply refs_at_empty.
Qed.

(* Resolve all decidable key equalities appearing in the goal. *)
Ltac decide_all :=
  repeat match goal with
  | |- context [decide (?a = ?a)] =>
      destruct (decide (a = a)) as [_|H]; [|exfalso; apply H; reflexivity]
  | H : ?a <> ?b |- context [decide (?a = ?b)] =>
      destruct (decide (a = b)) as [E|_]; [exfalso; apply H; exact E|]
  | H : ?a <> ?b |- context [decide (?b = ?a)] =>
      destruct (decide (b = a)) as [E|_]; [exfalso; apply H; symmetry; exact E|]
  end; try reflexivity.

(* ================================================================== *)
(* Exact reference sets for each local rule.                          *)
(* Each lemma fully describes refs_at of the rule's source/target map. *)
(* ================================================================== *)

Lemma Acquire_src_refs v k i n refcnt a :
  i <> n ->
  refs_at ({[i := Thread (k (Acquire (Val (LockV n))));
             n := Lock refcnt (Some v)]} : cfg) a =
  if decide (a = i) then expr_refs (k (Acquire (Val (LockV n))))
  else if decide (a = n) then val_refs v else ∅.
Proof.
  intros Hne. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map2_fst by exact Hne. decide_all.
  - destruct (decide (a = n)) as [->|Han].
    + rewrite refs_at_map2_snd by exact Hne. decide_all.
    + rewrite refs_at_map2_other.
      * decide_all.
      * exact Hai.
      * exact Han.
Qed.

Lemma Acquire_tgt_refs v k i n refcnt a :
  i <> n ->
  refs_at ({[i := Thread (k (Val (PairV (LockV n) v)));
             n := Lock refcnt None]} : cfg) a =
  if decide (a = i) then expr_refs (k (Val (PairV (LockV n) v)))
  else if decide (a = n) then ∅ else ∅.
Proof.
  intros Hne. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map2_fst by exact Hne. decide_all.
  - destruct (decide (a = n)) as [->|Han].
    + rewrite refs_at_map2_snd by exact Hne. decide_all.
    + rewrite refs_at_map2_other.
      * decide_all.
      * exact Hai.
      * exact Han.
Qed.

Lemma Release_src_refs v k i n refcnt a :
  i <> n ->
  refs_at ({[i := Thread (k (Release (Val (LockV n)) (Val v)));
             n := Lock refcnt None]} : cfg) a =
  if decide (a = i) then expr_refs (k (Release (Val (LockV n)) (Val v)))
  else if decide (a = n) then ∅ else ∅.
Proof.
  intros Hne. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map2_fst by exact Hne. decide_all.
  - destruct (decide (a = n)) as [->|Han].
    + rewrite refs_at_map2_snd by exact Hne. decide_all.
    + rewrite refs_at_map2_other.
      * decide_all.
      * exact Hai.
      * exact Han.
Qed.

Lemma Release_tgt_refs v k i n refcnt a :
  i <> n ->
  refs_at ({[i := Thread (k (Val (LockV n)));
             n := Lock refcnt (Some v)]} : cfg) a =
  if decide (a = i) then expr_refs (k (Val (LockV n)))
  else if decide (a = n) then val_refs v else ∅.
Proof.
  intros Hne. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map2_fst by exact Hne. decide_all.
  - destruct (decide (a = n)) as [->|Han].
    + rewrite refs_at_map2_snd by exact Hne. decide_all.
    + rewrite refs_at_map2_other.
      * decide_all.
      * exact Hai.
      * exact Han.
Qed.

Lemma NewLock_src_refs v k i n a :
  i <> n ->
  refs_at ({[i := Thread (k (NewLock (Val v)))]} : cfg) a =
  if decide (a = i) then expr_refs (k (NewLock (Val v))) else ∅.
Proof.
  intros Hne. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map1. decide_all.
  - rewrite refs_at_map1_other by exact Hai. decide_all.
Qed.

Lemma NewLock_tgt_refs v k i n a :
  i <> n ->
  refs_at ({[i := Thread (k (Val (LockV n)));
             n := Lock 0 (Some v)]} : cfg) a =
  if decide (a = i) then expr_refs (k (Val (LockV n)))
  else if decide (a = n) then val_refs v else ∅.
Proof.
  intros Hne. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map2_fst by exact Hne. decide_all.
  - destruct (decide (a = n)) as [->|Han].
    + rewrite refs_at_map2_snd by exact Hne. decide_all.
    + rewrite refs_at_map2_other.
      * decide_all.
      * exact Hai.
      * exact Han.
Qed.

Lemma Drop_src_refs o k i n refcnt a :
  i <> n ->
  refs_at ({[i := Thread (k (Drop (Val (LockV n))));
             n := Lock (S refcnt) o]} : cfg) a =
  if decide (a = i) then expr_refs (k (Drop (Val (LockV n))))
  else if decide (a = n) then obj_refs (Lock (S refcnt) o) else ∅.
Proof.
  intros Hne. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map2_fst by exact Hne. decide_all.
  - destruct (decide (a = n)) as [->|Han].
    + rewrite refs_at_map2_snd by exact Hne. decide_all.
    + rewrite refs_at_map2_other.
      * decide_all.
      * exact Hai.
      * exact Han.
Qed.

Lemma Drop_tgt_refs o k i n refcnt a :
  i <> n ->
  refs_at ({[i := Thread (k (Val UnitV));
             n := Lock refcnt o]} : cfg) a =
  if decide (a = i) then expr_refs (k (Val UnitV))
  else if decide (a = n) then obj_refs (Lock refcnt o) else ∅.
Proof.
  intros Hne. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map2_fst by exact Hne. decide_all.
  - destruct (decide (a = n)) as [->|Han].
    + rewrite refs_at_map2_snd by exact Hne. decide_all.
    + rewrite refs_at_map2_other.
      * decide_all.
      * exact Hai.
      * exact Han.
Qed.

Lemma Wait_src_refs v k i n a :
  i <> n ->
  refs_at ({[i := Thread (k (Wait (Val (LockV n))));
             n := Lock 0 (Some v)]} : cfg) a =
  if decide (a = i) then expr_refs (k (Wait (Val (LockV n))))
  else if decide (a = n) then val_refs v else ∅.
Proof.
  intros Hne. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map2_fst by exact Hne. decide_all.
  - destruct (decide (a = n)) as [->|Han].
    + rewrite refs_at_map2_snd by exact Hne. decide_all.
    + rewrite refs_at_map2_other.
      * decide_all.
      * exact Hai.
      * exact Han.
Qed.

Lemma Wait_tgt_refs v k i n a :
  i <> n ->
  refs_at ({[i := Thread (k (Val v))]} : cfg) a =
  if decide (a = i) then expr_refs (k (Val v)) else ∅.
Proof.
  intros Hne. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map1. decide_all.
  - rewrite refs_at_map1_other by exact Hai. decide_all.
Qed.

Lemma ForkLock_src_refs v o k i n refcnt a :
  i <> n ->
  refs_at ({[i := Thread (k (ForkLock (Val (LockV n)) (Val v)));
             n := Lock refcnt o]} : cfg) a =
  if decide (a = i)
  then expr_refs (k (ForkLock (Val (LockV n)) (Val v)))
  else if decide (a = n) then obj_refs (Lock refcnt o) else ∅.
Proof.
  intros Hne. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map2_fst by exact Hne. decide_all.
  - destruct (decide (a = n)) as [->|Han].
    + rewrite refs_at_map2_snd by exact Hne. decide_all.
    + rewrite refs_at_map2_other.
      * decide_all.
      * exact Hai.
      * exact Han.
Qed.

Lemma ForkLock_tgt_refs v o k i j n refcnt a :
  i <> j -> i <> n -> j <> n ->
  refs_at ({[i := Thread (k (Val (LockV n)));
             j := Thread (App (Val v) (Val (LockV n)));
             n := Lock (S refcnt) o]} : cfg) a =
  if decide (a = i) then expr_refs (k (Val (LockV n)))
  else if decide (a = j) then expr_refs (App (Val v) (Val (LockV n)))
  else if decide (a = n) then obj_refs (Lock (S refcnt) o) else ∅.
Proof.
  intros Hij Hin Hjn. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map3_fst by (exact Hij || exact Hin).
    decide_all.
  - destruct (decide (a = j)) as [->|Haj].
    + rewrite refs_at_map3_snd.
      * decide_all.
      * exact Hai.
      * exact Hjn.
    + destruct (decide (a = n)) as [->|Han].
      * rewrite refs_at_map3_trd.
        -- decide_all.
        -- apply ne_sym; exact Hin.
        -- apply ne_sym; exact Hjn.
      * rewrite refs_at_map3_other.
        -- decide_all.
        -- exact Hai.
        -- exact Haj.
        -- exact Han.
Qed.

Lemma Fork_src_refs v k i a :
  refs_at ({[i := Thread (k (ForkBarrier (Val v)))]} : cfg) a =
  if decide (a = i) then expr_refs (k (ForkBarrier (Val v))) else ∅.
Proof.
  destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map1. decide_all.
  - rewrite refs_at_map1_other by exact Hai. decide_all.
Qed.

Lemma Fork_tgt_refs v k i j n a :
  i <> j -> i <> n -> j <> n ->
  refs_at ({[i := Thread (k (Val (BarrierV n)));
             j := Thread (App (Val v) (Val (BarrierV n)));
             n := Barrier]} : cfg) a =
  if decide (a = i) then expr_refs (k (Val (BarrierV n)))
  else if decide (a = j) then expr_refs (App (Val v) (Val (BarrierV n)))
  else if decide (a = n) then ∅ else ∅.
Proof.
  intros Hij Hin Hjn. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map3_fst by (exact Hij || exact Hin). decide_all.
  - destruct (decide (a = j)) as [->|Haj].
    + rewrite refs_at_map3_snd.
      * decide_all.
      * exact Hai.
      * exact Hjn.
    + destruct (decide (a = n)) as [->|Han].
      * rewrite refs_at_map3_trd.
        -- decide_all.
        -- apply ne_sym; exact Hin.
        -- apply ne_sym; exact Hjn.
      * rewrite refs_at_map3_other.
        -- decide_all.
        -- exact Hai.
        -- exact Haj.
        -- exact Han.
Qed.

Lemma Sync_src_refs v1 v2 k1 k2 i j n a :
  i <> j -> i <> n -> j <> n ->
  refs_at ({[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
             j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
             n := Barrier]} : cfg) a =
  if decide (a = i) then expr_refs (k1 (App (Val (BarrierV n)) (Val v1)))
  else if decide (a = j) then expr_refs (k2 (App (Val (BarrierV n)) (Val v2)))
  else if decide (a = n) then ∅ else ∅.
Proof.
  intros Hij Hin Hjn. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map3_fst by (exact Hij || exact Hin). decide_all.
  - destruct (decide (a = j)) as [->|Haj].
    + rewrite refs_at_map3_snd.
      * decide_all.
      * exact Hai.
      * exact Hjn.
    + destruct (decide (a = n)) as [->|Han].
      * rewrite refs_at_map3_trd.
        -- decide_all.
        -- apply ne_sym; exact Hin.
        -- apply ne_sym; exact Hjn.
      * rewrite refs_at_map3_other.
        -- decide_all.
        -- exact Hai.
        -- exact Haj.
        -- exact Han.
Qed.

Lemma Sync_tgt_refs v1 v2 k1 k2 i j a :
  i <> j ->
  refs_at ({[i := Thread (k1 (Val v2));
             j := Thread (k2 (Val v1))]} : cfg) a =
  if decide (a = i) then expr_refs (k1 (Val v2))
  else if decide (a = j) then expr_refs (k2 (Val v1)) else ∅.
Proof.
  intros Hij. destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map2_fst by exact Hij. decide_all.
  - destruct (decide (a = j)) as [->|Haj].
    + rewrite refs_at_map2_snd by exact Hij. decide_all.
    + rewrite refs_at_map2_other.
      * decide_all.
      * exact Hai.
      * exact Haj.
Qed.

Lemma Exit_tgt_refs a : refs_at (∅ : cfg) a = ∅.
Proof. apply refs_at_empty. Qed.

Lemma Pure_src_refs (k : expr -> expr) (e : expr) (i a : nat) :
  refs_at ({[i := Thread (k e)]} : cfg) a =
  if decide (a = i) then expr_refs (k e) else ∅.
Proof.
  destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map1. decide_all.
  - rewrite refs_at_map1_other by exact Hai. decide_all.
Qed.

Lemma Pure_tgt_refs (k : expr -> expr) (e' : expr) (i a : nat) :
  refs_at ({[i := Thread (k e')]} : cfg) a =
  if decide (a = i) then expr_refs (k e') else ∅.
Proof.
  destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map1. decide_all.
  - rewrite refs_at_map1_other by exact Hai. decide_all.
Qed.
(* ===== forest Forest.v ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Relation_Operators.
Import ListNotations.


(* ================================================================== *)
(* Chains and closed walks of waiting edges.                          *)
(* ================================================================== *)

Inductive walk_path (R : nat -> nat -> Prop) : nat -> list nat -> nat -> Prop :=
  | wp_nil x : walk_path R x [] x
  | wp_cons x y l z : R x y -> walk_path R y l z -> walk_path R x (y :: l) z.

Lemma walk_path_app (R : nat -> nat -> Prop) (x : nat) (l : list nat) (y : nat)
  (l' : list nat) (z : nat) :
  walk_path R x l y -> walk_path R y l' z -> walk_path R x (l ++ l')%list z.
Proof.
  intros H. revert l' z. induction H; intros l0 z0 H'.
  - simpl. exact H'.
  - simpl. eapply wp_cons.
    + exact H.
    + apply IHwalk_path. exact H'.
Qed.

Lemma clos_trans_walk_path (R : nat -> nat -> Prop) x y :
  @clos_trans nat R x y -> exists l, walk_path R x l y.
Proof.
  intros H. induction H.
  - exists [y]. eapply wp_cons.
    + exact H.
    + eapply wp_nil.
  - destruct IHclos_trans1 as [l1 Hl1].
    destruct IHclos_trans2 as [l2 Hl2].
    exists (l1 ++ l2)%list. exact (walk_path_app R x l1 y l2 z Hl1 Hl2).
Qed.

(* Every waiting cycle, as a list of distinct vertices with the wrapping
   edge included, is impossible under the set pair condition + forest. *)
Definition waiting_cycle_list (ρ : cfg) (l : list nat) : Prop :=
  2 <= List.length l /\ NoDup l /\
  path_edges (waiting ρ) (l ++ [List.hd 0 l])%list.

Lemma no_waiting_cycle_list_of_forest_pair ρ l :
  ref_pair_ok ρ -> ref_forest ρ -> waiting_cycle_list ρ l -> False.
Proof.
  intros Hpair Hforest [Hlen [Hnd Hpath]].
  destruct l as [|a [|b l]].
  - simpl in Hlen. lia.
  - (* length one: a self-waiting edge, impossible *)
    cbn in Hpath.
    inversion Hpath as [| |a0 b0 l0 Hw Hrest]; subst.
    exact (no_waiting_self ρ a (proj1 Hpair) Hw).
  - destruct l as [|c l'].
    + (* length two: mutual waiting *)
      cbn in Hpath.
      inversion Hpath as [| |a0 b0 l0 Hw Hrest]; subst.
      inversion Hrest as [| |b0 a0 l0 Hw2 Hrest2]; subst.
      exact (no_waiting_2cycle ρ a b Hpair Hw Hw2).
    + (* length at least three: a genuine simple cycle *)
      apply (no_waiting_cycle_of_forest ρ (a :: b :: c :: l')).
      * exact Hpair.
      * exact Hforest.
      * exact Hnd.
      * simpl. lia.
      * cbn [List.hd]. exact Hpath.
Qed.

(* The remaining graph-theoretic extraction step, stated explicitly as a
   hypothesis: any closed `waiting` walk contains a waiting cycle with
   distinct vertices (of length at least two).  This is exactly the step
   that is not formalised below. *)
Definition no_live_nonstep_cycle (ρ : cfg) : Prop :=
  forall i, i ∈ dom ρ -> ~ can_step ρ i ->
    ~ @clos_trans nat (fun a b => waiting ρ a b) i i.

Definition waiting_cycles_have_simple_form (ρ : cfg) : Prop :=
  forall i, @clos_trans nat (fun a b => waiting ρ a b) i i ->
    exists l, waiting_cycle_list ρ l.

Lemma no_live_nonstep_cycle_of_forest ρ :
  ref_pair_ok ρ -> ref_forest ρ ->
  waiting_cycles_have_simple_form ρ ->
  no_live_nonstep_cycle ρ.
Proof.
  intros Hpair Hforest Hext i _ _ Hcyc.
  destruct (Hext i Hcyc) as [l Hl].
  exact (no_waiting_cycle_list_of_forest_pair ρ l Hpair Hforest Hl).
Qed.
(* ===== forest Extract.v ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap list.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Relation_Operators.
Import ListNotations.
Close Scope string_scope.


(* ================================================================== *)
(* Prefix/suffix closure of [path_edges].                             *)
(* ================================================================== *)

Lemma path_edges_prefix (R : nat -> nat -> Prop) (l1 l2 : list nat) :
  path_edges R (l1 ++ l2) -> path_edges R l1.
Proof.
  revert l2. induction l1 as [|a l1 IH]; intros l2 H.
  - cbn. apply pe_nil.
  - destruct l1 as [|b l1'].
    + cbn in H. destruct l2 as [|c l2].
      * cbn in H. exact H.
      * cbn in H. inversion H as [| |a0 b0 l0 Hw Hrest]; subst.
        apply pe_one.
    + cbn in H. inversion H as [| |a0 b0 l0 Hw Hrest]; subst.
      eapply pe_cons.
      * exact Hw.
      * exact (IH l2 Hrest).
Qed.

Lemma path_edges_suffix (R : nat -> nat -> Prop) (l1 l2 : list nat) :
  path_edges R (l1 ++ l2) -> path_edges R l2.
Proof.
  revert l2. induction l1 as [|a l1 IH]; intros l2 H.
  - cbn in H. exact H.
  - destruct l1 as [|b l1'].
    + cbn in H. destruct l2 as [|c l2'].
      * cbn in H. apply pe_nil.
      * cbn in H. inversion H as [| |a0 b0 l0 Hw Hrest]; subst.
        exact Hrest.
    + cbn in H. inversion H as [| |a0 b0 l0 Hw Hrest]; subst.
      exact (IH l2 Hrest).
Qed.

(* ================================================================== *)
(* Index of an element in a list, as a computable function.           *)
(* ================================================================== *)

Fixpoint index_of (x : nat) (l : list nat) : option nat :=
  match l with
  | [] => None
  | y :: ys =>
      if decide (x = y) then Some 0
      else match index_of x ys with
           | Some i => Some (S i)
           | None => None
           end
  end.

Lemma lookup_nth (l : list nat) (i : nat) : l !! i = nth_error l i.
Proof.
  revert l. induction i as [|i IH]; intros l.
  - destruct l; reflexivity.
  - destruct l as [|a l]; simpl; [reflexivity|apply IH].
Qed.

Lemma hd_nth (A : Type) (d : A) (l : list A) : hd d l = nth 0 l d.
Proof. destruct l; reflexivity. Qed.

Lemma index_of_some (x : nat) (l : list nat) (i : nat) :
  index_of x l = Some i -> l !! i = Some x.
Proof.
  revert i. induction l as [|y ys IH]; intros i H.
  - simpl in H. discriminate.
  - simpl in H. destruct (decide (x = y)) as [E|NE].
    + inversion H as [Ei]. subst i. simpl. rewrite E. reflexivity.
    + destruct (index_of x ys) as [j|] eqn:E; inversion H as [Ei]; subst i.
      simpl. exact (IH j eq_refl).
Qed.

Lemma index_of_none (x : nat) (l : list nat) :
  index_of x l = None -> x ∉ l.
Proof.
  induction l as [|y ys IH]; intros H Hin.
  - simpl in Hin. set_solver.
  - simpl in H. destruct (decide (x = y)) as [E|NE].
    + discriminate.
    + destruct (index_of x ys) as [j|] eqn:E; [discriminate|].
      apply elem_of_cons in Hin as [E'|Hin].
      * exact (NE E').
      * exact (IH eq_refl Hin).
Qed.

Lemma index_of_some_exists (x : nat) (l : list nat) :
  x ∈ l -> exists i, index_of x l = Some i.
Proof.
  induction l as [|y ys IH]; intros Hin.
  - simpl in Hin. set_solver.
  - simpl. destruct (decide (x = y)) as [E|NE].
    + exists 0. reflexivity.
    + destruct (index_of x ys) as [j|] eqn:E.
      * exists (S j). reflexivity.
      * exfalso. apply elem_of_cons in Hin as [E'|Hin].
        -- exact (NE E').
        -- apply (index_of_none x ys E Hin).
Qed.

Lemma index_of_some_lt (x : nat) (l : list nat) (i : nat) :
  index_of x l = Some i -> i < List.length l.
Proof.
  intro H. apply lookup_lt_Some with (x := x). exact (index_of_some x l i H).
Qed.

(* ================================================================== *)
(* Scan for the first repeated vertex.                                *)
(* [pref] is the duplicate-free prefix already scanned, [rest] the     *)
(* unscanned suffix.  On finding [x] already in [pref] at position i,  *)
(* we return the segment of [pref] starting at i.                      *)
(* ================================================================== *)

Fixpoint find_cycle (pref rest : list nat) : option (list nat) :=
  match rest with
  | [] => None
  | x :: xs =>
      match index_of x pref with
      | Some i => Some (drop i pref)
      | None => find_cycle (pref ++ [x])%list xs
      end
  end.

Lemma NoDup_single (x : nat) : NoDup [x].
Proof. constructor; [intros []|constructor]. Qed.

Definition valid_cycle (R : nat -> nat -> Prop) (l : list nat) : Prop :=
  NoDup l /\ 1 <= List.length l /\ path_edges R (l ++ [hd 0 l]).

Lemma find_cycle_some_valid (R : nat -> nat -> Prop) :
  forall (pref rest l : list nat),
    NoDup pref ->
    path_edges R (pref ++ rest) ->
    find_cycle pref rest = Some l ->
    valid_cycle R l.
Proof.
  intros pref rest. revert pref.
  induction rest as [|x xs IH]; intros pref l Hnd Hpath Hres.
  - simpl in Hres. discriminate.
  - simpl in Hres.
    destruct (index_of x pref) as [i|] eqn:E.
    + inversion Hres as [Heq]. subst l.
      pose proof (index_of_some x pref i E) as Hlookup.
      pose proof (lookup_lt_Some pref i x Hlookup) as Hilt.
      assert (Hlookup' : nth_error pref i = Some x).
      { rewrite <- (lookup_nth pref i). exact Hlookup. }
      assert (Hhd : hd 0 (drop i pref) = x).
      { rewrite (@hd_nth nat 0 (drop i pref)).
        rewrite (nth_skipn i pref 0 0). rewrite Nat.add_0_r.
        exact (@nth_error_nth nat pref i x 0 Hlookup'). }
      assert (Hprefx : path_edges R (pref ++ [x])).
      { eapply (path_edges_prefix R (pref ++ [x]) xs).
        rewrite <- app_assoc. exact Hpath. }
      assert (Hseg : path_edges R (drop i pref ++ [x])).
      { eapply (path_edges_suffix R (take i pref) (drop i pref ++ [x])).
        replace ((take i pref ++ (drop i pref ++ [x]))%list)
          with (((take i pref ++ drop i pref) ++ [x])%list) by (symmetry; apply app_assoc).
        rewrite take_drop. exact Hprefx. }
      unfold valid_cycle. split.
      * apply (NoDup_app_remove_l (take i pref) (drop i pref)).
        rewrite take_drop. exact Hnd.
      * split.
        -- rewrite length_drop. lia.
        -- rewrite Hhd. exact Hseg.
    + apply (IH (pref ++ [x])%list l).
      * apply NoDup_app.
        -- exact Hnd.
        -- apply NoDup_single.
        -- intros y Hy Hyx. simpl in Hyx. destruct Hyx as [E'|[]]. subst y.
           exact (index_of_none x pref E (proj2 (@list_elem_of_In nat pref x) Hy)).
      * change (path_edges R (((pref ++ [x])%list) ++ xs)).
        rewrite <- app_assoc. cbn. exact Hpath.
      * exact Hres.
Qed.

Lemma find_cycle_none_nodup (pref rest : list nat) :
  NoDup pref -> find_cycle pref rest = None -> NoDup (pref ++ rest).
Proof.
  revert pref. induction rest as [|x xs IH]; intros pref Hnd Hres.
  - simpl in Hres. rewrite app_nil_r. exact Hnd.
  - simpl in Hres.
    destruct (index_of x pref) as [i|] eqn:E.
    + discriminate.
    + replace ((pref ++ x :: xs)%list) with ((((pref ++ [x])%list) ++ xs)%list).
      2: { rewrite <- app_assoc. cbn. reflexivity. }
      apply IH with (pref := (pref ++ [x])%list).
      * apply NoDup_app.
        -- exact Hnd.
        -- apply NoDup_single.
        -- intros y Hy Hyx. simpl in Hyx. destruct Hyx as [E'|[]]. subst y.
           exact (index_of_none x pref E (proj2 (@list_elem_of_In nat pref x) Hy)).
      * exact Hres.
Qed.

(* ================================================================== *)
(* Closed paths contain simple cycles.                                *)
(* ================================================================== *)

Lemma last_in (l : list nat) (d : nat) :
  l <> [] -> In (List.last l d) l.
Proof.
  induction l as [|a l IH]; intros H.
  - contradiction.
  - destruct l as [|b l'].
    + simpl. left. reflexivity.
    + simpl. right. apply IH. discriminate.
Qed.

Lemma closed_not_nodup (vs : list nat) :
  2 <= List.length vs ->
  hd 0 vs = List.last vs 0 ->
  ~ NoDup vs.
Proof.
  intros Hlen Hclosed Hnd.
  destruct vs as [|a rest].
  - simpl in Hlen. lia.
  - destruct rest as [|b rest'].
    + simpl in Hlen. lia.
    + apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnin _].
      simpl in Hclosed.
      apply Hnin.
      rewrite Hclosed.
      change (In (List.last (b :: rest') 0) (b :: rest')).
      apply last_in. discriminate.
Qed.

Lemma closed_path_simple_cycle (R : nat -> nat -> Prop) (vs : list nat) :
  2 <= List.length vs ->
  path_edges R vs ->
  hd 0 vs = List.last vs 0 ->
  exists l, NoDup l /\ 1 <= List.length l /\
    path_edges R (l ++ [hd 0 l]).
Proof.
  intros Hlen Hpath Hclosed.
  destruct (find_cycle [] vs) as [l|] eqn:E.
  - exists l. apply (find_cycle_some_valid R [] vs l).
    + apply NoDup_nil.
    + change (path_edges R ([] ++ vs)). rewrite app_nil_l. exact Hpath.
    + exact E.
  - exfalso. apply (closed_not_nodup vs); [exact Hlen|exact Hclosed|].
    apply (find_cycle_none_nodup [] vs).
    + apply NoDup_nil.
    + exact E.
Qed.

(* ================================================================== *)
(* From a nonempty [clos_trans] path to a closed [path_edges] list.   *)
(* ================================================================== *)

Lemma clos_trans_walk_nonempty (R : nat -> nat -> Prop) (x y : nat) :
  @clos_trans nat R x y -> exists l, l <> [] /\ walk_path R x l y.
Proof.
  intros H. induction H.
  - exists [y]. split; [discriminate|]. eapply wp_cons.
    + exact H.
    + eapply wp_nil.
  - destruct IHclos_trans1 as [l1 [Hne1 Hw1]].
    destruct IHclos_trans2 as [l2 [_ Hw2]].
    exists (l1 ++ l2)%list. split.
    + destruct l1; [contradiction|discriminate].
    + exact (walk_path_app R x l1 y l2 z Hw1 Hw2).
Qed.

Lemma walk_path_path_edges (R : nat -> nat -> Prop) (x : nat) (l : list nat) (y : nat) :
  walk_path R x l y -> path_edges R (x :: l).
Proof.
  intros H. induction H using walk_path_ind.
  - simpl. apply pe_one.
  - simpl. eapply pe_cons.
    + exact H.
    + assumption.
Qed.

Lemma walk_path_last (R : nat -> nat -> Prop) (x : nat) (l : list nat) (y : nat) :
  walk_path R x l y -> List.last (x :: l) 0 = y.
Proof.
  intros H. induction H using walk_path_ind.
  - reflexivity.
  - simpl. assumption.
Qed.

Lemma clos_trans_simple_cycle (R : nat -> nat -> Prop) (x : nat) :
  @clos_trans nat R x x ->
  exists l, NoDup l /\ 1 <= List.length l /\
    path_edges R (l ++ [hd 0 l]).
Proof.
  intros H.
  destruct (clos_trans_walk_nonempty R x x H) as [l [Hne Hwalk]].
  set (vs := x :: l).
  assert (Hlen : 2 <= List.length vs).
  { unfold vs. simpl. destruct l; [contradiction|simpl; lia]. }
  assert (Hpath : path_edges R vs).
  { unfold vs. apply (walk_path_path_edges R x l x Hwalk). }
  assert (Hclosed : hd 0 vs = List.last vs 0).
  { unfold vs. simpl. symmetry. apply (walk_path_last R x l x Hwalk). }
  exact (closed_path_simple_cycle R vs Hlen Hpath Hclosed).
Qed.

(* ================================================================== *)
(* Waiting cycles have simple form, hence are excluded by the forest. *)
(* ================================================================== *)

Lemma waiting_cycles_have_simple_form_of_no_self (ρ : cfg) :
  (forall i, ~ waiting ρ i i) -> waiting_cycles_have_simple_form ρ.
Proof.
  intros Hns i Hcyc.
  destruct (clos_trans_simple_cycle (fun a b => waiting ρ a b) i Hcyc)
    as [l [Hnd [Hlen1 Hpath]]].
  exists l. unfold waiting_cycle_list. split; [|split].
  - destruct l as [|a [|b l']].
    + simpl in Hlen1. lia.
    + (* length one would be a self-waiting loop *)
      exfalso. apply (Hns a).
      cbn in Hpath.
      inversion Hpath as [| |a0 b0 l0 Hw Hrest]; subst.
      exact Hw.
    + simpl. lia.
  - exact Hnd.
  - exact Hpath.
Qed.

Lemma no_live_nonstep_cycle_of_forest_complete (ρ : cfg) :
  ref_pair_ok ρ -> ref_forest ρ -> no_live_nonstep_cycle ρ.
Proof.
  intros Hpair Hforest.
  apply (no_live_nonstep_cycle_of_forest ρ Hpair Hforest).
  apply waiting_cycles_have_simple_form_of_no_self.
  intros i. exact (no_waiting_self ρ i (proj1 Hpair)).
Qed.

Print Assumptions no_live_nonstep_cycle_of_forest_complete.
(* ===== Task combinatorial section ===== *)
(* A sufficient combinatorial condition for full reachability.        *)
(*                                                                    *)
(* [waiting ρ i j] is the "i depends on j" relation.  If it has a     *)
(* rank that strictly increases along waiting edges, then reachability *)
(* propagates back along those edges from any [can_step] seed.        *)
(* ------------------------------------------------------------------ *)

Definition wait_wf (ρ : cfg) : Prop :=
  well_founded (fun j i => waiting ρ i j).

Definition progress_or_wait (ρ : cfg) : Prop :=
  forall i, ρ !! i <> None -> can_step ρ i \/ exists j, waiting ρ i j.

Definition wait_targets_live (ρ : cfg) : Prop :=
  forall i e j, ρ !! i = Some (Thread e) -> expr_waiting e j -> ρ !! j <> None.

Definition rank_ok (ρ : cfg) (r : nat -> nat) (M : nat) : Prop :=
  (forall i, r i <= M) /\ (forall i j, waiting ρ i j -> r i < r j).

Lemma rank_ok_wait_wf ρ r M :
  rank_ok ρ r M -> wait_wf ρ.
Proof.
  intros [Hb Hr]. unfold wait_wf.
  apply (Wf_nat.well_founded_lt_compat
           nat (fun i => M - r i) (fun j i => waiting ρ i j)).
  intros x y Hxy. pose proof (Hr y x Hxy) as Hlt.
  pose proof (Hb x). pose proof (Hb y). lia.
Qed.

Lemma wait_wf_fully_reachable ρ :
  wait_wf ρ -> progress_or_wait ρ -> wait_targets_live ρ -> fully_reachable ρ.
Proof.
  intros Hwf Hprog Hlive i.
  apply (well_founded_ind Hwf (fun i => inactive ρ i \/ reachable ρ i)).
  intros x IH.
  destruct (ρ !! x) as [y|] eqn:E.
  - right.
    assert (Hact : ρ !! x <> None) by congruence.
    destruct (Hprog x Hact) as [Hstep | [j Hwait]].
    + apply Can_step_reachable; exact Hstep.
    + destruct (IH j Hwait) as [Hinj | Hrj].
      * destruct Hwait as [[e [He Hw]] | [y' [Hy _]]].
        -- exfalso. exact (Hlive x e j He Hw Hinj).
        -- unfold inactive in Hinj. rewrite Hy in Hinj. discriminate.
      * apply Waiting_reachable with j; assumption.
  - left. exact E.
Qed.

Theorem rank_fully_reachable ρ r M :
  rank_ok ρ r M -> progress_or_wait ρ -> wait_targets_live ρ ->
  fully_reachable ρ.
Proof.
  intros Hr Hp Hl.
  apply wait_wf_fully_reachable.
  - apply rank_ok_wait_wf with (r := r) (M := M); exact Hr.
  - exact Hp.
  - exact Hl.
Qed.

(* ------------------------------------------------------------------ *)
(* Seedability: the truly relevant combinatorial condition.           *)
(*                                                                    *)
(* A global rank is too strong: [waiting] may contain cycles that     *)
(* pass through objects which can step.  The correct condition is     *)
(* that every live location reaches, along finitely many waiting      *)
(* edges, some location that can step.                                *)
(* ------------------------------------------------------------------ *)

Definition wait_step (ρ : cfg) : nat -> nat -> Prop :=
  fun a b => waiting ρ a b.

Definition seeded (ρ : cfg) : Prop :=
  forall i, ρ !! i <> None ->
    exists j, rtc (wait_step ρ) i j /\ can_step ρ j.

Lemma reachable_of_wait_rtc ρ a b :
  rtc (wait_step ρ) a b -> reachable ρ b -> reachable ρ a.
Proof.
  intros H. induction H as [| x y z Hxy _ IH]; intros Hb.
  - exact Hb.
  - apply Waiting_reachable with y.
    + exact Hxy.
    + apply IH; exact Hb.
Qed.

Lemma seeded_fully_reachable ρ : seeded ρ -> fully_reachable ρ.
Proof.
  intros Hseed i. destruct (ρ !! i) as [y|] eqn:E.
  - right. destruct (Hseed i ltac:(congruence)) as [j [Hpath Hstep]].
    apply (reachable_of_wait_rtc ρ i j Hpath).
    apply Can_step_reachable; exact Hstep.
  - left. exact E.
Qed.

Lemma reachable_seed ρ i : reachable ρ i ->
  exists j, rtc (wait_step ρ) i j /\ can_step ρ j.
Proof.
  induction 1 as [k Hc | a b Hw Hr IH].
  - exists k. split; [apply rtc_refl | exact Hc].
  - destruct IH as [j [Hpath Hc]].
    exists j. split; [| exact Hc].
    apply (rtc_l (wait_step ρ) a b j Hw Hpath).
Qed.

Lemma fully_reachable_seeded ρ : fully_reachable ρ -> seeded ρ.
Proof.
  intros Hfr i Hi.
  destruct (Hfr i) as [Hin | Hr].
  - exfalso. apply Hi. exact Hin.
  - exact (reachable_seed ρ i Hr).
Qed.

Lemma seeded_iff_fully_reachable ρ : seeded ρ <-> fully_reachable ρ.
Proof.
  split.
  - apply seeded_fully_reachable.
  - apply fully_reachable_seeded.
Qed.

(* A configuration with a live location and no steppable location is
   certainly not fully reachable. *)
Lemma reachable_no_can_step ρ i :
  (forall k, ~ can_step ρ k) -> reachable ρ i -> False.
Proof.
  intros Hns Hr. induction Hr as [k Hc | i j Hw Hr IH].
  - exact (Hns k Hc).
  - exact IH.
Qed.

Lemma no_can_step_not_fully_reachable ρ :
  (forall k, ~ can_step ρ k) ->
  (exists k, ρ !! k <> None) ->
  ~ fully_reachable ρ.
Proof.
  intros Hns [k Hk] Hfr.
  destruct (Hfr k) as [Hin | Hr].
  - unfold inactive in Hin. exact (Hk Hin).
  - exact (reachable_no_can_step ρ k Hns Hr).
Qed.

(* A rank is only needed on the non-steppable locations.  This is the
   exact relaxation needed because waiting cycles through steppable
   locations are harmless. *)

Definition rank_nonstep (ρ : cfg) (r : nat -> nat) (M : nat) : Prop :=
  (forall i, r i <= M) /\
  (forall i j, waiting ρ i j -> ~ can_step ρ i -> r i < r j).

Lemma waiting_target_live ρ (Hlive : wait_targets_live ρ) i j :
  waiting ρ i j -> ρ !! j <> None.
Proof.
  intros [[e [He Hw]] | [y [Hy _]]].
  - exact (Hlive i e j He Hw).
  - rewrite Hy. discriminate.
Qed.

Lemma rank_nonstep_seeded ρ r M
    (Hdec : forall i, {can_step ρ i} + {~ can_step ρ i}) :
  rank_nonstep ρ r M -> progress_or_wait ρ -> wait_targets_live ρ ->
  seeded ρ.
Proof.
  intros [Hb Hr] Hprog Hlive i Hi.
  revert Hi.
  apply (well_founded_ind
    (Wf_nat.well_founded_lt_compat nat (fun i => M - r i)
       (fun y x => M - r y < M - r x)
       (fun x y Hxy => Hxy))
    (fun i => ρ !! i <> None ->
      exists j, rtc (wait_step ρ) i j /\ can_step ρ j)).
  intros x IH Hx.
  destruct (Hdec x) as [Hc | Hnc].
  - exists x. split; [apply rtc_refl | exact Hc].
  - destruct (Hprog x Hx) as [Hc | [y Hw]].
    + exists x. split; [apply rtc_refl | exact Hc].
    + assert (Hlt : M - r y < M - r x).
      { pose proof (Hr x y Hw Hnc). pose proof (Hb x). pose proof (Hb y). lia. }
      assert (Hy : ρ !! y <> None).
      { apply (waiting_target_live ρ Hlive x y Hw). }
      destruct (IH y Hlt Hy) as [z [Hpath Hz]].
      exists z. split; [| exact Hz].
      apply (rtc_l (wait_step ρ) x y z Hw Hpath).
Qed.

Lemma disjoint_env_no_dup_lock Γ1 Γ2 x l t :
  disj Γ1 Γ2 ->
  Γ1 !! x = Some (LockT l t) ->
  Γ2 !! x = Some (LockT l t) ->
  False.
Proof.
  intros Hd H1 H2.
  destruct (Hd x (LockT l t) (LockT l t) H1 H2) as [_ Hunr].
  exact (unr_LockT l t Hunr).
Qed.

(* Every local step has its label live in the source configuration. *)
Lemma local_step_label_live i ρ ρ' : local_step i ρ ρ' -> ρ !! i <> None.
Proof.
  intros H. induction H; simpl; intro E;
    match goal with
    | E : ?M = None |- False =>
        assert (His : is_Some M) by (apply elem_of_dom; set_solver);
        destruct His as [x Hx]; rewrite E in Hx; discriminate
    end.
Qed.

(* ------------------------------------------------------------------ *)
(* A finite total relation contains a directed cycle.                 *)
(*                                                                    *)
(* This is the combinatorial tool turning the fact that every live    *)
(* non-steppable node has an outgoing waiting edge, plus acyclicity,  *)
(* into seedability.  It is constructive (the stdpp finite_choice and *)
(* finite_pigeonhole are closed under the global context).            *)
(* ------------------------------------------------------------------ *)

Lemma iter_positive_clos_trans {A} (R : A -> A -> Prop) (f : A -> A)
    (Hf : forall x, R x (f x)) :
  forall (d:nat) (x:A), 0 < d -> @clos_trans A R x (@Nat.iter d A f x).
Proof.
  intros d. induction d as [|d IH]; intros x Hd.
  - lia.
  - destruct d as [|d'].
    + simpl. apply t_step. apply Hf.
    + rewrite Nat.iter_succ_r.
      eapply t_trans.
      * apply t_step. apply Hf.
      * apply IH. lia.
Qed.

Lemma finite_total_relation_cycle {A} `{EqDecision A} `{Finite A}
    (R : A -> A -> Prop) (a0 : A) :
  (forall x, exists y, R x y) -> exists (x:A), @clos_trans A R x x.
Proof.
  intros Htot.
  destruct (finite_choice (A := A) (B := fun _ => A)
              (fun x (y:A) => R x y) Htot) as [f Hf].
  set (n := card A).
  set (g := fun i : fin (S n) => @Nat.iter (fin_to_nat i) A f a0).
  assert (Hgt : card A < card (fin (S n))).
  { rewrite fin_card. fold n. lia. }
  destruct (finite_pigeonhole (A := fin (S n)) (B := A) g Hgt)
    as [x1 [x2 [Hne Heq]]].
  assert (Hne' : fin_to_nat x1 <> fin_to_nat x2).
  { intro E. apply Hne. apply fin_to_nat_inj. exact E. }
  destruct (lt_eq_lt_dec (fin_to_nat x1) (fin_to_nat x2))
    as [[Hlt|Heqn]|Hgtn].
  - set (d := fin_to_nat x2 - fin_to_nat x1).
    assert (Hd : 0 < d) by lia.
    assert (Hx2 : g x2 = @Nat.iter d A f (g x1)).
    { unfold g.
      replace (fin_to_nat x2) with (d + fin_to_nat x1) by lia.
      rewrite Nat.iter_add. reflexivity. }
    exists (g x1).
    pose proof (iter_positive_clos_trans R f Hf d (g x1) Hd) as Hc.
    rewrite <- Hx2 in Hc. rewrite <- Heq in Hc. exact Hc.
  - exfalso. apply Hne'. exact Heqn.
  - set (d := fin_to_nat x1 - fin_to_nat x2).
    assert (Hd : 0 < d) by lia.
    assert (Hx1 : g x1 = @Nat.iter d A f (g x2)).
    { unfold g.
      replace (fin_to_nat x1) with (d + fin_to_nat x2) by lia.
      rewrite Nat.iter_add. reflexivity. }
    exists (g x2).
    pose proof (iter_positive_clos_trans R f Hf d (g x2) Hd) as Hc.
    rewrite <- Hx1 in Hc. rewrite Heq in Hc. exact Hc.
Qed.

(* ------------------------------------------------------------------ *)
(* Parallel/source reachability is the remaining semantic work.       *)
(* ------------------------------------------------------------------ *)

Lemma finite_orbit_cycle {A} `{EqDecision A} `{Finite A}
    (R : A -> A -> Prop) (a0 : A) :
  (forall x, exists y, R x y) ->
  exists (f:A->A) (k d:nat) (x:A),
    0 < d /\ (forall y, R y (f y)) /\
    x = @Nat.iter k A f a0 /\
    @Nat.iter d A f x = x /\
    @clos_trans A R x x.
Proof.
  intros Htot.
  destruct (finite_choice (A := A) (B := fun _ => A)
              (fun x (y:A) => R x y) Htot) as [f Hf].
  set (n := card A).
  set (g := fun i : fin (S n) => @Nat.iter (fin_to_nat i) A f a0).
  assert (Hgt : card A < card (fin (S n))).
  { rewrite fin_card. fold n. lia. }
  destruct (finite_pigeonhole (A := fin (S n)) (B := A) g Hgt)
    as [x1 [x2 [Hne Heq]]].
  assert (Hne' : fin_to_nat x1 <> fin_to_nat x2).
  { intro E. apply Hne. apply fin_to_nat_inj. exact E. }
  destruct (lt_eq_lt_dec (fin_to_nat x1) (fin_to_nat x2))
    as [[Hlt|Heqn]|Hgtn].
  - set (d := fin_to_nat x2 - fin_to_nat x1).
    assert (Hd : 0 < d) by lia.
    assert (Hx2 : g x2 = @Nat.iter d A f (g x1)).
    { unfold g. replace (fin_to_nat x2) with (d + fin_to_nat x1) by lia.
      rewrite Nat.iter_add. reflexivity. }
    assert (Hiter : @Nat.iter d A f (g x1) = g x1).
    { rewrite <- Hx2. exact (eq_sym Heq). }
    exists f, (fin_to_nat x1), d, (g x1).
    split; [exact Hd|]. split; [exact Hf|]. split; [reflexivity|].
    split; [exact Hiter|].
    pose proof (iter_positive_clos_trans R f Hf d (g x1) Hd) as Hc.
    rewrite Hiter in Hc. exact Hc.
  - exfalso. apply Hne'. exact Heqn.
  - set (d := fin_to_nat x1 - fin_to_nat x2).
    assert (Hd : 0 < d) by lia.
    assert (Hx1 : g x1 = @Nat.iter d A f (g x2)).
    { unfold g. replace (fin_to_nat x1) with (d + fin_to_nat x2) by lia.
      rewrite Nat.iter_add. reflexivity. }
    assert (Hiter : @Nat.iter d A f (g x2) = g x2).
    { rewrite <- Hx1. exact Heq. }
    exists f, (fin_to_nat x2), d, (g x2).
    split; [exact Hd|]. split; [exact Hf|]. split; [reflexivity|].
    split; [exact Hiter|].
    pose proof (iter_positive_clos_trans R f Hf d (g x2) Hd) as Hc.
    rewrite Hiter in Hc. exact Hc.
Qed.

(* max bound of a finite domain *)
Fixpoint list_max (l : list nat) : nat :=
  match l with [] => 0 | x :: xs => Nat.max x (list_max xs) end.

Lemma in_list_max (l:list nat) (x:nat) : x ∈ l -> x <= list_max l.
Proof.
  induction l as [|a l IH]; simpl; intros Hx.
  - set_solver.
  - apply elem_of_cons in Hx as [->|Hx].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (list_max l); [apply IH; exact Hx|apply Nat.le_max_r].
Qed.

Definition dom_max (ρ : cfg) : nat := list_max (elements (dom ρ)).
Definition dom_bound (ρ : cfg) : nat := S (dom_max ρ).

Lemma dom_live_lt (ρ:cfg) (i:nat) : i ∈ dom ρ -> i < dom_bound ρ.
Proof.
  intros Hi. unfold dom_bound, dom_max.
  apply Nat.lt_succ_r.
  apply in_list_max.
  rewrite elem_of_elements. exact Hi.
Qed.

Lemma dom_of_lookup (ρ:cfg) (i:nat) : ρ !! i <> None -> i ∈ dom ρ.
Proof.
  intros Hi. apply elem_of_dom.
  destruct (ρ !! i) as [o|] eqn:E; [eexists; exact E|done].
Qed.

Lemma lookup_of_dom (ρ:cfg) (i:nat) : i ∈ dom ρ -> ρ !! i <> None.
Proof.
  intros Hi E. exact ((proj2 (not_elem_of_dom ρ i) E) Hi).
Qed.

(* waiting-cycle iteration *)
Lemma waiting_iter_clos_trans ρ (h : nat -> nat)
    (Hh : forall j, waiting ρ (h j) (h (S j))) :
  forall j d, 0 < d -> @clos_trans nat (fun a b => waiting ρ a b) (h j) (h (j+d)).
Proof.
  intros j d. revert j. induction d as [|d IH]; intros j Hd.
  - lia.
  - destruct d as [|d'].
    + replace (j + 1) with (S j) by lia.
      apply t_step. apply Hh.
    + eapply t_trans.
      * replace (j + 1) with (S j) by lia. apply t_step. apply Hh.
      * replace (j + 1) with (S j) by lia.
        replace (j + S (S d')) with (S j + S d') by lia.
        apply IH. lia.
Qed.

(* Main reduction: progress + no live waiting cycle => seeded. *)
Lemma seeded_of_progress_acyclic ρ
    (Hprog : progress_or_wait ρ)
    (Hlive : wait_targets_live ρ)
    (Hacyc : forall i, i ∈ dom ρ -> ~ can_step ρ i ->
        ~ @clos_trans nat (fun a b => waiting ρ a b) i i) :
  seeded ρ.
Proof.
  intros i0 Hi0ne.
  pose proof (dom_of_lookup ρ i0 Hi0ne) as Hi0dom.
  set (N := dom_bound ρ).
  pose proof (dom_live_lt ρ i0 Hi0dom) as Hi0lt.
  pose (a0 := nat_to_fin Hi0lt).
  pose (R := fun (a b : fin N) =>
    (fin_to_nat a ∈ dom ρ /\
       (waiting ρ (fin_to_nat a) (fin_to_nat b) \/
        (can_step ρ (fin_to_nat a) /\ fin_to_nat b = fin_to_nat a)))
    \/ (~ fin_to_nat a ∈ dom ρ /\ b = a)).
  assert (Htot : forall a : fin N, exists b, R a b).
  { intros a. destruct (decide (fin_to_nat a ∈ dom ρ)) as [Hla|Hna].
    - destruct (Hprog (fin_to_nat a) (lookup_of_dom ρ (fin_to_nat a) Hla))
        as [Hc|[j Hw]].
      + exists a. left. split; [exact Hla|]. right. split; [exact Hc|reflexivity].
      + assert (Hjne : ρ !! j <> None).
        { destruct Hw as [[e [He Hw']]|[y [Hy _]]].
          - exact (Hlive _ _ _ He Hw').
          - rewrite Hy. discriminate. }
        pose proof (dom_of_lookup ρ j Hjne) as Hjdom.
        pose proof (dom_live_lt ρ j Hjdom) as Hjlt.
        exists (nat_to_fin Hjlt). left. split; [exact Hla|]. left.
        rewrite fin_to_nat_to_fin.
        exact Hw.
    - exists a. right. split; [exact Hna|reflexivity]. }
  destruct (classic (exists j, rtc (wait_step ρ) i0 j /\ can_step ρ j))
    as [Hseed|Hnotseed].
  - exact Hseed.
  - exfalso.
    destruct (finite_orbit_cycle R a0 Htot)
      as [f [k [d [x [Hd [Hf [Hx [Hiter Hc]]]]]]]].
    pose (g := fun j => @Nat.iter j (fin N) f a0).
    assert (Hga0 : g 0 = a0) by reflexivity.
    assert (Ha0 : fin_to_nat a0 = i0).
    { unfold a0. rewrite fin_to_nat_to_fin. reflexivity. }
    assert (Hedge : forall j,
      fin_to_nat (g j) ∈ dom ρ /\
      ~ can_step ρ (fin_to_nat (g j)) /\
      rtc (wait_step ρ) i0 (fin_to_nat (g j)) /\
      waiting ρ (fin_to_nat (g j)) (fin_to_nat (g (S j)))).
    { induction j as [|j IH].
      - split; [|split; [|split]].
        + rewrite Hga0. change (fin_to_nat a0 ∈ dom ρ). rewrite Ha0. exact Hi0dom.
        + intro Hcan. apply Hnotseed. exists i0.
          split; [apply rtc_refl|]. rewrite <- Ha0. exact Hcan.
        + rewrite Hga0. change (rtc (wait_step ρ) i0 (fin_to_nat a0)).
          rewrite Ha0. apply rtc_refl.
        + assert (Hg1 : g 1 = f a0) by reflexivity.
          rewrite Hg1.
          pose proof (Hf a0) as HR. unfold R in HR.
          destruct HR as [[Hla Hrest]|Hna].
          * destruct Hrest as [Hw|Hcan].
            -- rewrite Hga0. change (waiting ρ (fin_to_nat a0) (fin_to_nat (f a0))).
               exact Hw.
            -- exfalso. apply Hnotseed. exists i0.
               split; [apply rtc_refl|]. rewrite <- Ha0. exact (proj1 Hcan).
          * exfalso. apply Hna. change (fin_to_nat a0 ∈ dom ρ). rewrite Ha0. exact Hi0dom.
      - destruct IH as [Hlivej [Hncj [Hrtcj Hwj]]].
        assert (Htarget_ne : ρ !! (fin_to_nat (g (S j))) <> None).
        { destruct Hwj as [[e [He Hw']]|[y [Hy _]]].
          - exact (Hlive _ _ _ He Hw').
          - rewrite Hy. discriminate. }
        pose proof (dom_of_lookup ρ (fin_to_nat (g (S j))) Htarget_ne) as Hlivenext.
        assert (Hncnext : ~ can_step ρ (fin_to_nat (g (S j)))).
        { intro Hcan. apply Hnotseed. exists (fin_to_nat (g (S j))).
          split; [|exact Hcan].
          eapply rtc_r; [exact Hrtcj|exact Hwj]. }
        split; [exact Hlivenext|split; [exact Hncnext|split]].
        + eapply rtc_r; [exact Hrtcj|exact Hwj].
        + assert (HgSS : g (S (S j)) = f (g (S j))) by reflexivity.
          rewrite HgSS.
          pose proof (Hf (g (S j))) as HR. unfold R in HR.
          destruct HR as [[Hla Hrest]|Hna].
          * destruct Hrest as [Hw|Hcan].
            -- exact Hw.
            -- exfalso. apply Hncnext. exact (proj1 Hcan).
          * exfalso. apply Hna. exact Hlivenext. }
    (* the orbit property at k+d closes a waiting cycle *)
    assert (Hgk : x = g k) by exact Hx.
    assert (Hgadd : g (k + d) = g k).
    { unfold g. replace (k + d) with (d + k) by lia.
      rewrite Nat.iter_add.
      rewrite <- Hx. exact Hiter. }
    assert (Hh : forall j, waiting ρ (fin_to_nat (g (k + j)))
                                  (fin_to_nat (g (k + S j)))).
    { intro j. replace (k + S j) with (S (k + j)) by lia.
      exact (proj2 (proj2 (proj2 (Hedge (k + j))))). }
    destruct (Hedge k) as [Hlivek [Hnc_k _]].
    pose proof (waiting_iter_clos_trans ρ
                  (fun j => fin_to_nat (g (k + j))) Hh 0 d Hd) as Hcyc.
    simpl in Hcyc.
    replace (k + 0) with k in Hcyc by lia.
    replace (0 + d) with d in Hcyc by lia.
    assert (Hend : fin_to_nat (g (k + d)) = fin_to_nat (g k)).
    { rewrite Hgadd. reflexivity. }
    rewrite Hend in Hcyc.
    exact (Hacyc (fin_to_nat (g k)) Hlivek Hnc_k Hcyc).
Qed.

(* ------------------------------------------------------------------ *)
(* From the three configuration invariants to full reachability.      *)
(* ------------------------------------------------------------------ *)

Theorem fully_reachable_of_progress_acyclic ρ :
  progress_or_wait ρ -> wait_targets_live ρ ->
  no_live_nonstep_cycle ρ -> fully_reachable ρ.
Proof.
  intros Hprog Hlive Hacyc.
  apply seeded_fully_reachable.
  exact (seeded_of_progress_acyclic ρ Hprog Hlive Hacyc).
Qed.

(* ------------------------------------------------------------------ *)
(* For a configuration rho reached from a typed source, the target     *)
(* follows from the three invariants above:                            *)
(*   1. progress_or_wait rho                                          *)
(*   2. wait_targets_live rho                                         *)
(*   3. no_live_nonstep_cycle rho                                     *)
(* Invariant (1) for live threads is supplied by the runtime typing   *)
(* wt and closed Unit-thread progress.  The remaining obligations are *)
(* object-level capability/refcount accounting for live locks and     *)
(* barriers, kind/liveness of references, and preservation of the     *)
(* provenance/forest invariant along local steps.                     *)
(* ------------------------------------------------------------------ *)

Theorem fully_reachable_of_invariants (L : gmap nat type) ρ caps bend
    (Hty : forall i e, ρ !! i = Some (Thread e) -> wt L ∅ e UnitT)
    (Hinv : cap_inventory ρ caps bend)
    (Hlive : wait_targets_live ρ) (Hpair : ref_pair_ok ρ) (Hforest : ref_forest ρ) :
  fully_reachable ρ.
Proof.
  apply fully_reachable_of_progress_acyclic.
  - change (progress_or_wait_obj ρ). exact (progress_or_wait_of_typed_inventory L ρ caps bend Hty Hinv).
  - exact Hlive.
  - exact (no_live_nonstep_cycle_of_forest_complete ρ Hpair Hforest).
Qed.
Print Assumptions fully_reachable_of_invariants.



(* ===== recovered initial provenance ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap list.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Strings.String.
Import ListNotations.
Close Scope string_scope.


(* ================================================================== *)
(* 1. The initial typed source configuration.                         *)
(* ================================================================== *)

Lemma fin_union_empty {A} `{Countable A} n (f : fin n -> gset A) :
  (forall i, f i = ∅) -> fin_union n f = ∅.
Proof.
  intros Hf. apply set_eq. intros x. split.
  - intros Hx. apply elem_of_fin_union in Hx.
    destruct Hx as [i Hi]. rewrite Hf in Hi. set_solver.
  - intros Hx. set_solver.
Qed.

Lemma typed_expr_refs_empty (Gamma : env) (e : expr) (t : type) :
  typed Gamma e t -> expr_refs e = ∅.
Proof.
  intros H. induction H as
    [ Gamma x t Hvar
    | Gamma Gamma' x e t1 t2 l Hb Hunr Hty IH
    | Gamma Gamma1 Gamma2 e1 e2 t1 t2 l Hs H1 IH1 H2 IH2
    | Gamma Hunr
    | Gamma Gamma1 Gamma2 e1 e2 t1 t2 Hs H1 IH1 H2 IH2
    | Gamma Gamma1 Gamma2 e1 e2 t1 t2 t Hs H1 IH1 H2 IH2
    | Gamma n ts i e Hty IH
    | n Gamma Gamma1 Gamma2 t ts es e Hs Hn H1 IH1 Hf IHf
    | Gamma e t1 t2 Hty IH
    | Gamma e t Hty IH
    | Gamma Gamma1 Gamma2 e1 e2 t l1 l2 l3 Hs Hcap H1 IH1 H2 IH2
    | Gamma e t lo Hty IH
    | Gamma Gamma1 Gamma2 e1 e2 t lo Hs H1 IH1 H2 IH2
    | Gamma e t Hty IH
    | Gamma e t Hty IH ]; simpl.
  - done.
  - exact IH.
  - rewrite IH1, IH2. set_solver.
  - set_solver.
  - rewrite IH1, IH2. set_solver.
  - rewrite IH1, IH2. set_solver.
  - exact IH.
  - rewrite IH1.
    assert (Hfin : fin_union n (expr_refs ∘ es) = ∅).
    { apply fin_union_empty. intro i. apply IHf. }
    rewrite Hfin. set_solver.
  - exact IH.
  - exact IH.
  - rewrite IH1, IH2. set_solver.
  - exact IH.
  - rewrite IH1, IH2. set_solver.
  - exact IH.
  - exact IH.
Qed.

Lemma refs_at_singleton_thread (i : nat) (e : expr) (a : nat) :
  refs_at ({[i := Thread e]} : cfg) a =
  if decide (a = i) then expr_refs e else ∅.
Proof.
  destruct (decide (a = i)) as [->|Hai].
  - rewrite refs_at_map1. reflexivity.
  - rewrite refs_at_map1_other by exact Hai. reflexivity.
Qed.

Lemma typed_singleton_refs_empty (Gamma : env) (e : expr) (t : type) :
  typed Gamma e t ->
  forall a, refs_at ({[0 := Thread e]} : cfg) a = ∅.
Proof.
  intros Hty a.
  rewrite refs_at_singleton_thread.
  destruct (decide (a = 0)) as [_|_]; [|reflexivity].
  exact (typed_expr_refs_empty Gamma e t Hty).
Qed.

Lemma no_refs_ref_pair_ok (ρ : cfg) :
  (forall a, refs_at ρ a = ∅) -> ref_pair_ok ρ.
Proof.
  intros H. split.
  - intros a Ha. rewrite H in Ha. set_solver.
  - intros a b Hne [Hb _]. rewrite H in Hb. set_solver.
Qed.

Lemma no_edges_path_edges (R : nat -> nat -> Prop) :
  (forall a b, ~ R a b) -> forall l, path_edges R l -> List.length l <= 1.
Proof.
  intros Hno l Hp. induction Hp as [|a|a b l Hr Hrest IH].
  - simpl. lia.
  - simpl. lia.
  - exfalso. exact (Hno a b Hr).
Qed.

Lemma no_refs_ref_forest (ρ : cfg) :
  (forall a, refs_at ρ a = ∅) -> ref_forest ρ.
Proof.
  intros H l [Hlen0 [_ Hp]].
  assert (Hno : forall a b, ~ ref_edge ρ a b).
  { intros a b [Hne [Hb|Ha]]; try rewrite H in Hb; try rewrite H in Ha; set_solver. }
  pose proof (no_edges_path_edges (ref_edge ρ) Hno (l ++ [List.hd 0 l]) Hp) as Hlen.
  rewrite List.length_app in Hlen. simpl in Hlen. lia.
Qed.

Lemma typed_singleton_ref_inv (Gamma : env) (e : expr) (t : type) :
  typed Gamma e t ->
  ref_pair_ok ({[0 := Thread e]} : cfg) /\
  ref_forest ({[0 := Thread e]} : cfg).
Proof.
  intro Hty. split.
  - apply no_refs_ref_pair_ok. apply (typed_singleton_refs_empty Gamma e t Hty).
  - apply no_refs_ref_forest. apply (typed_singleton_refs_empty Gamma e t Hty).
Qed.

Print Assumptions typed_singleton_ref_inv.

(* ================================================================== *)
(* 2. Graph helpers for the reattachment argument.                    *)
(* ================================================================== *)

Lemma NoDup_app_not_both (l1 l2 : list nat) :
  NoDup (l1 ++ l2) -> forall x, In x l1 -> In x l2 -> False.
Proof.
  revert l2. induction l1 as [|a l1 IH]; intros l2 H x Hx1 Hx2.
  - simpl in Hx1. contradiction.
  - simpl in H. apply NoDup_cons_iff in H. destruct H as [Hna Hnd].
    simpl in Hx1. destruct Hx1 as [E|Hx1].
    + subst a. apply Hna. apply in_or_app. right. exact Hx2.
    + exact (IH l2 Hnd x Hx1 Hx2).
Qed.

Lemma NoDup_rotate (pre rest : list nat) (x : nat) :
  NoDup (pre ++ x :: rest) -> NoDup (x :: rest ++ pre).
Proof.
  intro H.
  change (NoDup ((x :: rest) ++ pre)).
  pose proof (NoDup_app_remove_l pre (x :: rest) H) as Hxr.
  pose proof (NoDup_app_remove_r pre (x :: rest) H) as Hpre.
  apply NoDup_app.
  - exact Hxr.
  - exact Hpre.
  - intros y Hy Hxpre.
    apply (NoDup_app_not_both pre (x :: rest) H y Hxpre Hy).
Qed.

Lemma path_edges_app_last (R : nat -> nat -> Prop) (l1 : list nat) (x : nat) (l2 : list nat) :
  path_edges R (l1 ++ [x]) -> path_edges R (x :: l2) ->
  path_edges R (l1 ++ x :: l2).
Proof.
  revert x l2. induction l1 as [|a l1 IH]; intros x l2 H1 H2.
  - simpl in H1. simpl. exact H2.
  - destruct l1 as [|b l1'].
    + simpl in H1. inversion H1 as [| |a0 b0 l0 Hr Hrest]; subst.
      simpl. eapply pe_cons.
      * exact Hr.
      * exact H2.
    + simpl in H1. inversion H1 as [| |a0 b0 l0 Hr Hrest]; subst.
      simpl. eapply pe_cons.
      * exact Hr.
      * apply (IH x l2); assumption.
Qed.

Lemma path_edges_snoc (R : nat -> nat -> Prop) (l : list nat) (x : nat) :
  l <> [] -> path_edges R l -> R (List.last l 0) x ->
  path_edges R (l ++ [x]).
Proof.
  revert x. induction l as [|a l IH]; intros x Hne Hp Hlast.
  - contradiction.
  - destruct l as [|b l'].
    + simpl in Hp. inversion Hp as [|a0|a0 b0 l0 Hr Hrest]; subst.
      simpl. eapply pe_cons.
      * exact Hlast.
      * apply pe_one.
    + simpl in Hp. inversion Hp as [| |a0 b0 l0 Hr Hrest]; subst.
      simpl. eapply pe_cons.
      * exact Hr.
      * apply (IH x); [discriminate|exact Hrest|].
        simpl in Hlast. exact Hlast.
Qed.

Lemma path_edges_cons (R : nat -> nat -> Prop) (x : nat) (l : list nat) :
  R x (List.hd 0 l) -> path_edges R l -> path_edges R (x :: l).
Proof.
  intros Hx Hp. destruct l as [|a l'].
  - simpl. apply pe_one.
  - simpl. eapply pe_cons; [exact Hx|exact Hp].
Qed.

Lemma path_edges_last_edge (R : nat -> nat -> Prop) (l : list nat) (x : nat) :
  path_edges R (l ++ [x]) -> l <> [] -> R (List.last l 0) x.
Proof.
  revert x. induction l as [|a l IH]; intros x Hp Hne.
  - contradiction.
  - destruct l as [|b l'].
    + simpl in Hp. inversion Hp as [| |a0 b0 l0 Hr Hrest]; subst.
      exact Hr.
    + simpl in Hp. inversion Hp as [| |a0 b0 l0 Hr Hrest]; subst.
      simpl. apply (IH x Hrest). discriminate.
Qed.

Lemma app_cons_last (rest pre' : list nat) (p z : nat) :
  (rest ++ p :: (pre' ++ [z]))%list = ((rest ++ (p :: pre')) ++ [z])%list.
Proof.
  induction rest as [|a rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(* Rotate a closed path from [pre ++ rest ++ [first pre]] to
   [rest ++ pre ++ [first rest]]. *)
Lemma path_edges_rotate_at (R : nat -> nat -> Prop) (pre rest : list nat) :
  pre <> [] -> rest <> [] ->
  path_edges R (pre ++ rest ++ [List.hd 0 pre]) ->
  path_edges R (rest ++ pre ++ [List.hd 0 rest]).
Proof.
  intros Hpre Hrest Hp.
  assert (Hrest_path : path_edges R (rest ++ [List.hd 0 pre])).
  { apply (path_edges_suffix R pre). exact Hp. }
  assert (Hpre_path : path_edges R (pre ++ [List.hd 0 rest])).
  { destruct rest as [|r rest'].
    - contradiction.
    - cbn [List.hd].
      assert (E : (pre ++ (r :: rest') ++ [List.hd 0 pre])%list
                = ((pre ++ [r]) ++ (rest' ++ [List.hd 0 pre]))%list).
      { rewrite <- app_assoc. cbn. reflexivity. }
      rewrite E in Hp.
      apply (path_edges_prefix R (pre ++ [r]) (rest' ++ [List.hd 0 pre])).
      exact Hp. }
  assert (Hcomb : path_edges R
            (rest ++ List.hd 0 pre :: (List.tl pre ++ [List.hd 0 rest]))).
  { apply (path_edges_app_last R rest (List.hd 0 pre)
             (List.tl pre ++ [List.hd 0 rest])).
    - exact Hrest_path.
    - destruct pre as [|p pre'].
      + contradiction.
      + cbn [List.hd List.tl].
        exact Hpre_path. }
  destruct pre as [|p pre']; [contradiction|].
  cbn [List.hd List.tl] in Hcomb.
  rewrite (app_cons_last rest pre' p (List.hd 0 rest)) in Hcomb.
  rewrite <- app_assoc in Hcomb.
  exact Hcomb.
Qed.

(* If none of the vertices of a path is [i], target edges that are not
   incident to [i] are source edges. *)
Lemma path_edges_mono_avoid_i
  (G H : nat -> nat -> Prop) (i : nat) (R : gset nat) :
  (forall a b, H a b -> G a b \/ (a = i /\ b ∈ R) \/ (b = i /\ a ∈ R)) ->
  forall l, (forall x, x ∈ l -> x <> i) -> path_edges H l -> path_edges G l.
Proof.
  intros Hsub l Hno Hp. induction Hp as [|a|a b l Hr Hrest IH].
  - apply pe_nil.
  - apply pe_one.
  - assert (Ha : a <> i).
    { intros E. apply (Hno a). simpl. left. exact E. }
    assert (Hb : b <> i).
    { intros E. apply (Hno b). simpl. right. left. exact E. }
    assert (Hrest_no : forall x, x ∈ b :: l -> x <> i).
    { intros x Hx. apply (Hno x). simpl. right. exact Hx. }
    destruct (Hsub a b Hr) as [HG|[ [E _] | [E _] ]].
    + eapply pe_cons; [exact HG|apply IH; exact Hrest_no].
    + exfalso. apply Ha. exact E.
    + exfalso. apply Hb. exact E.
Qed.



(* ================================================================== *)
(* Initial configuration satisfies the full invariant package.        *)
(* ================================================================== *)

Lemma init_wait_targets_live e (Hty : typed ∅ e UnitT) :
  wait_targets_live (init_cfg e).
Proof.
  intros i e0 j Hi Hw.
  unfold init_cfg in Hi.
  assert (Hpair : ({[0 := Thread e]} : cfg) !! i = Some (Thread e0)).
  { exact Hi. }
  apply lookup_singleton_Some in Hpair.
  destruct Hpair as [Hi0 Heq].
  injection Heq as ->.
  subst i.
  apply expr_waiting_ref in Hw.
  pose proof (typed_expr_refs_empty ∅ e0 UnitT Hty) as Hemp.
  rewrite Hemp in Hw. exfalso. set_solver.
Qed.

Theorem initial_cfg_invariants e (Hty : typed ∅ e UnitT) :
  exists (caps : nat -> lockcap -> gset nat) (bend : nat -> gset nat),
    (forall i e0, (init_cfg e) !! i = Some (Thread e0) ->
        wt ∅ ∅ e0 UnitT) /\
    cap_inventory (init_cfg e) caps bend /\
    wait_targets_live (init_cfg e) /\
    ref_pair_ok (init_cfg e) /\
    ref_forest (init_cfg e).
Proof.
  exists (fun _ _ => (∅ : gset nat)), (fun _ => (∅ : gset nat)).
  split.
  - intros i e0 Hi.
    unfold init_cfg in Hi.
    apply lookup_singleton_Some in Hi.
    destruct Hi as [Hi0 Heq].
    injection Heq as ->.
    subst i.
    exact (typed_to_wt ∅ e0 UnitT Hty ∅).
  - split.
    + exact (init_cap_inventory e).
    + split.
      * apply init_wait_targets_live. exact Hty.
      * destruct (typed_singleton_ref_inv ∅ e UnitT Hty) as [Hp Hf].
        split; assumption.
Qed.


(* ================================================================== *)
(* Bundled configuration invariant.                                    *)
(* ================================================================== *)

Definition config_invariants (ρ : cfg) : Prop :=
  exists (L : gmap nat type)
         (caps : nat -> lockcap -> gset nat)
         (bend : nat -> gset nat),
    (forall i e, ρ !! i = Some (Thread e) -> wt L ∅ e UnitT) /\
    cap_inventory ρ caps bend /\
    wait_targets_live ρ /\
    ref_pair_ok ρ /\
    ref_forest ρ.

Theorem fully_reachable_of_config_invariants ρ :
  config_invariants ρ -> fully_reachable ρ.
Proof.
  intros (L & caps & bend & Hty & Hinv & Hlive & Hpair & Hforest).
  exact (fully_reachable_of_invariants L ρ caps bend Hty Hinv Hlive Hpair Hforest).
Qed.

Theorem typed_full_reachability_of_step_preservation e ρ
    (Hpres : forall ρ1 ρ2, config_invariants ρ1 -> step' ρ1 ρ2 ->
               config_invariants ρ2)
    (Hty : typed ∅ e UnitT)
    (Hsteps : steps {[0 := Thread e]} ρ) :
  fully_reachable ρ.
Proof.
  apply fully_reachable_of_config_invariants.
  refine (@rtc_ind_r cfg step' config_invariants
            {[0 := Thread e]} _ _ ρ Hsteps).
  - change (config_invariants (init_cfg e)).
    destruct (initial_cfg_invariants e Hty) as
      (caps & bend & Hty' & Hinv & Hlive & Hpair & Hforest).
    exists ∅, caps, bend. tauto.
  - intros y z _ Hyz Hy. exact (Hpres y z Hy Hyz).
Qed.


(* ===== context typing / framed pure thread preservation ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import Strings.String.
Open Scope string_scope.

(* ================================================================== *)
(* Replacing the hole of a closed evaluation context.                 *)
(*                                                                    *)
(* The hole always sits in the empty environment, so the replacement   *)
(* only has to be well typed at the same type as the original hole.    *)
(* This is the context-congruence principle for [wt] used by runtime    *)
(* subject reduction.  It is proved by the constructor views; the      *)
(* [env_split ∅] facts identify the two sub-environments with [∅].     *)
(* ================================================================== *)

Section CtxWtSec.

Context (L : gmap nat type).

Lemma wt_ctx1_replace k E E' t (Hk : ctx1 k) :
  wt L ∅ (k E) t ->
  (forall s, wt L ∅ E s -> wt L ∅ E' s) ->
  wt L ∅ (k E') t.
Proof.
  intros Hwt Hrepl.
  destruct Hk; cbn in Hwt.

  (* App left *)
  - destruct (wt_app_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t1 & l & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eapply AppW; [apply env_split_nil | apply (Hrepl _ H1) | exact H2].

  (* App right *)
  - destruct (wt_app_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t1 & l & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eapply AppW; [apply env_split_nil | exact H1 | apply (Hrepl _ H2)].

  (* Pair left *)
  - destruct (wt_pair_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t1 & t2 & Ht & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    subst t. eapply PairW; [apply env_split_nil | apply (Hrepl _ H1) | exact H2].

  (* Pair right *)
  - destruct (wt_pair_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t1 & t2 & Ht & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    subst t. eapply PairW; [apply env_split_nil | exact H1 | apply (Hrepl _ H2)].

  (* LetPair *)
  - destruct (wt_letpair_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t1 & t2 & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eapply LetPairW; [apply env_split_nil | apply (Hrepl _ H1) | exact H2].

  (* Sum *)
  - destruct (wt_sum_view L ∅ _ _ _ Hwt)
      as (n' & ts & j & Ht & Hn & H1).
    subst t. subst i.
    eapply SumW with (i := j). apply (Hrepl _ H1).

  (* MatchSum *)
  - destruct (wt_matchsum_view L ∅ _ _ _ _ Hwt)
      as (Γ1 & Γ2 & ts & Hsplit & Hn0 & H1 & Hf).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    eapply MatchSumW with (Γ1 := ∅) (Γ2 := ∅) (ts := ts).
    + apply env_split_nil.
    + exact Hn0.
    + apply (Hrepl _ H1).
    + exact Hf.

  (* ForkBarrier *)
  - destruct (wt_fork_view L ∅ _ _ Hwt) as (t1 & t2 & Ht & H1).
    subst t. eapply ForkW. apply (Hrepl _ H1).

  (* NewLock *)
  - destruct (wt_newlock_view L ∅ _ _ Hwt) as (t0 & Ht & H1).
    subst t. eapply NewLockW. apply (Hrepl _ H1).

  (* ForkLock left *)
  - destruct (wt_forklock_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t0 & l1 & l2 & l3 & Ht & Hsplit & Hcap & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    subst t. eapply ForkLockW with (Γ1 := ∅) (Γ2 := ∅)
      (l1 := l1) (l2 := l2) (l3 := l3).
    + apply env_split_nil.
    + exact Hcap.
    + apply (Hrepl _ H1).
    + exact H2.

  (* ForkLock right *)
  - destruct (wt_forklock_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t0 & l1 & l2 & l3 & Ht & Hsplit & Hcap & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    subst t. eapply ForkLockW with (Γ1 := ∅) (Γ2 := ∅)
      (l1 := l1) (l2 := l2) (l3 := l3).
    + apply env_split_nil.
    + exact Hcap.
    + exact H1.
    + apply (Hrepl _ H2).

  (* Acquire *)
  - destruct (wt_acquire_view L ∅ _ _ Hwt) as (t0 & lo & Ht & H1).
    subst t. eapply AcquireW. apply (Hrepl _ H1).

  (* Release left *)
  - destruct (wt_release_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t0 & lo & Ht & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    subst t. eapply ReleaseW with (Γ1 := ∅) (Γ2 := ∅) (lo := lo).
    + apply env_split_nil.
    + apply (Hrepl _ H1).
    + exact H2.

  (* Release right *)
  - destruct (wt_release_view L ∅ _ _ _ Hwt)
      as (Γ1 & Γ2 & t0 & lo & Ht & Hsplit & H1 & H2).
    destruct (env_split_empty Γ1 Γ2 Hsplit) as [E1 E2]; subst Γ1 Γ2.
    subst t. eapply ReleaseW with (Γ1 := ∅) (Γ2 := ∅) (lo := lo).
    + apply env_split_nil.
    + exact H1.
    + apply (Hrepl _ H2).

  (* Wait *)
  - pose proof (wt_wait_view L ∅ _ _ Hwt) as H1.
    eapply WaitW. apply (Hrepl _ H1).

  (* Drop *)
  - destruct (wt_drop_view L ∅ _ _ Hwt) as [Ht [t0 H1]].
    subst t. eapply DropW. apply (Hrepl _ H1).
Qed.

Lemma wt_ctx_replace k E E' t (Hk : ctx k) :
  wt L ∅ (k E) t ->
  (forall s, wt L ∅ E s -> wt L ∅ E' s) ->
  wt L ∅ (k E') t.
Proof.
  revert E E' t.
  induction Hk as [| k1 k2 H1 H2 IH]; intros E E' t Hwt Hrepl.
  - cbn in Hwt |- *. apply Hrepl. exact Hwt.
  - cbn in Hwt |- *.
    apply (wt_ctx1_replace k1 (k2 E) (k2 E') t H1 Hwt).
    intros s Hs.
    exact (IH E E' s Hs Hrepl).
Qed.

(* Specialisation to a pure step at the hole. *)

Lemma wt_ctx_pure_step k e e' t (Hk : ctx k) :
  wt L ∅ (k e) t -> pure_step e e' -> wt L ∅ (k e') t.
Proof.
  intros Hwt Hstep.
  apply (wt_ctx_replace k e e' t Hk Hwt).
  intros s Hs. exact (wt_pure_step L e e' s Hs Hstep).
Qed.

Print Assumptions wt_ctx1_replace.
Print Assumptions wt_ctx_replace.
Print Assumptions wt_ctx_pure_step.

End CtxWtSec.
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import Strings.String.
Open Scope string_scope.

(* ================================================================== *)
(* Thread-typing preservation for a framed Pure step.                 *)
(*                                                                    *)
(* The only changed thread is the one under the evaluation context;    *)
(* all other framed threads keep their typing because the singleton    *)
(* map has no key there.  The changed thread is retyped by            *)
(* [wt_ctx_pure_step].                                                 *)
(* ================================================================== *)

Section ThreadTypedPureSec.

Context (L : gmap nat type).

Lemma threads_typed_pure_frame i k e e' (ρf : cfg) :
  ctx k -> pure_step e e' ->
  threads_typed L (({[i := Thread (k e)]} : cfg) ∪ ρf) ->
  threads_typed L (({[i := Thread (k e')]} : cfg) ∪ ρf).
Proof.
  intros Hk Hps Hty j e0 Hj.
  destruct (decide (j = i)) as [E|E].
  - subst j.
    assert (Hsingle_src :
      ({[i := Thread (k e)]} : cfg) !! i = Some (Thread (k e)))
      by apply lookup_singleton_eq.
    assert (Hsingle_tgt :
      ({[i := Thread (k e')]} : cfg) !! i = Some (Thread (k e')))
      by apply lookup_singleton_eq.
    assert (Htgt :
      (({[i := Thread (k e')]} : cfg) ∪ ρf) !! i = Some (Thread (k e')))
      by (apply (lookup_union_Some_l _ _ _ _ Hsingle_tgt)).
    rewrite Htgt in Hj. inversion Hj; subst e0.
    assert (Hsrc :
      (({[i := Thread (k e)]} : cfg) ∪ ρf) !! i = Some (Thread (k e)))
      by (apply (lookup_union_Some_l _ _ _ _ Hsingle_src)).
    exact (wt_ctx_pure_step L k e e' UnitT Hk (Hty i (k e) Hsrc) Hps).
  - assert (Hleft : ({[i := Thread (k e')]} : cfg) !! j = None)
      by (apply lookup_singleton_ne; congruence).
    assert (Hright : ρf !! j = Some (Thread e0)).
    { exact (lookup_union_Some_inv_r
        ({[i := Thread (k e')]} : cfg) ρf j (Thread e0) Hj Hleft). }
    assert (Hleft_src : ({[i := Thread (k e)]} : cfg) !! j = None)
      by (apply lookup_singleton_ne; congruence).
    assert (Hsrc :
      (({[i := Thread (k e)]} : cfg) ∪ ρf) !! j = Some (Thread e0)).
    { rewrite (lookup_union_r _ _ _ Hleft_src). exact Hright. }
    exact (Hty j e0 Hsrc).
Qed.

Print Assumptions threads_typed_pure_frame.

End ThreadTypedPureSec.

(* ===== ForestMove.v ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap list.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Relation_Operators.
Import ListNotations.
Close Scope string_scope.


(* ================================================================== *)
(* Small list/path helpers for splitting a path at [n].               *)
(* ================================================================== *)

Lemma app_single_cons (p q : list nat) (n : nat) :
  ((p ++ [n]) ++ q)%list = (p ++ n :: q)%list.
Proof.
  induction p as [|a p IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma path_edges_prefix_cons (R : nat -> nat -> Prop) p q n :
  path_edges R (p ++ n :: q) -> path_edges R (p ++ [n]).
Proof.
  intro H. eapply (path_edges_prefix R (p ++ [n]) q).
  rewrite app_single_cons. exact H.
Qed.

Lemma path_edges_suffix_cons (R : nat -> nat -> Prop) p q n :
  path_edges R (p ++ n :: q) -> path_edges R (n :: q).
Proof. intro H. exact (path_edges_suffix R p (n :: q) H). Qed.

Lemma NoDup_prefix_snoc (p q : list nat) (n : nat) :
  NoDup (p ++ n :: q) -> NoDup (p ++ [n]).
Proof.
  intro H.
  pose proof (NoDup_app_remove_r p (n :: q) H) as Hp.
  assert (Hnp : ~ In n p).
  { intro Hin. exact (NoDup_app_not_both p (n :: q) H n Hin (or_introl eq_refl)). }
  apply NoDup_app.
  - exact Hp.
  - apply NoDup_single.
  - intros x Hx Hxn. simpl in Hxn. destruct Hxn as [E|[]].
    subst x. exact (Hnp Hx).
Qed.

Lemma NoDup_suffix_cons (p q : list nat) (n : nat) :
  NoDup (p ++ n :: q) -> NoDup (n :: q).
Proof. intro H. exact (NoDup_app_remove_l p (n :: q) H). Qed.

Lemma hd_in_list (l : list nat) (d : nat) : l <> [] -> In (List.hd d l) l.
Proof.
  destruct l as [|a l]; [contradiction|].
  simpl. left. reflexivity.
Qed.

Lemma last_in_list (l : list nat) (d : nat) : l <> [] -> In (List.last l d) l.
Proof.
  apply last_in.
Qed.

Lemma elem_of_hd (l : list nat) (d : nat) :
  l <> [] -> List.hd d l ∈ l.
Proof.
  intro H. apply (proj2 (@list_elem_of_In nat l (List.hd d l))).
  apply hd_in_list. exact H.
Qed.

Lemma elem_of_last (l : list nat) (d : nat) :
  l <> [] -> List.last l d ∈ l.
Proof.
  intro H. apply (proj2 (@list_elem_of_In nat l (List.last l d))).
  apply last_in_list. exact H.
Qed.

Lemma hd_prefix_cons (p q : list nat) (n : nat) :
  p <> [] -> List.hd 0 (p ++ n :: q) = List.hd 0 p.
Proof.
  destruct p as [|a p]; [contradiction|]. simpl. reflexivity.
Qed.

Lemma last_cons_nil (n x : nat) (l : list nat) :
  List.last (n :: x :: l) 0 = List.last (x :: l) 0.
Proof. simpl. reflexivity. Qed.

Lemma last_snoc (l : list nat) (x d : nat) :
  l <> [] -> List.last (l ++ [x]) d = x.
Proof.
  revert x d. induction l as [|a l IH]; intros x d Hne.
  - contradiction.
  - destruct l as [|b l'].
    + simpl. reflexivity.
    + simpl. apply IH. discriminate.
Qed.

Lemma hd_snoc (l : list nat) (x d : nat) :
  l <> [] -> List.hd d (l ++ [x]) = List.hd d l.
Proof. destruct l; simpl; [contradiction|reflexivity]. Qed.

Lemma last_snoc_any (l : list nat) (x d : nat) :
  List.last (l ++ [x]) d = x.
Proof.
  induction l as [|a l IH]; simpl.
  - reflexivity.
  - destruct l as [|b l'].
    + reflexivity.
    + simpl. apply IH.
Qed.

Lemma last_cons_app_nonempty (p q : list nat) (n d : nat) :
  List.last (p ++ n :: q) d = List.last (n :: q) d.
Proof.
  induction p as [|a p IH]; simpl.
  - reflexivity.
  - destruct p as [|b p'].
    + reflexivity.
    + simpl. apply IH.
Qed.

(* A cycle obtained by taking the prefix of [p ++ n :: q] up to [n],
   and closing it through [n] to the head. *)
Lemma cycle_prefix_n
  (G H : nat -> nat -> Prop) (i n : nat) (R : gset nat) (p q : list nat) :
  (forall a b, H a b -> G a b \/ (a = i /\ b ∈ R) \/ (b = i /\ a ∈ R)) ->
  (forall a b, G a b -> G b a) ->
  (forall a b, H a b -> H b a) ->
  (forall r, r ∈ R -> G n r) ->
  (forall r, r ∈ R -> ~ H n r) ->
  i <> n ->
  n ∉ R ->
  NoDup (i :: p ++ n :: q)%list ->
  2 <= List.length (p ++ n :: q)%list ->
  path_edges H (p ++ n :: q)%list ->
  List.hd 0 (p ++ n :: q)%list ∈ R ->
  list_cycle G (p ++ [n])%list.
Proof.
  intros HtoG Gsym Hsym GnR HnoH Hin HnR Hnd Hrlen Hpath HhdR.
  change (NoDup (i :: (p ++ n :: q)%list)) in Hnd.
  assert (Hir : i ∉ (p ++ n :: q)%list).
  { intro Hmem. pose proof Hnd as Hnd_copy.
    inversion Hnd_copy as [|x l Hnin Htail]; subst.
    apply Hnin.
    exact (proj1 (@list_elem_of_In nat (p ++ n :: q)%list i) Hmem). }
  assert (Hnd_tail : NoDup (p ++ n :: q)%list).
  { exact (NoDup_app_remove_l [i] (p ++ n :: q)%list Hnd). }
  assert (Hnd_pn : NoDup (p ++ [n])%list).
  { apply NoDup_prefix_snoc with (q := q). exact Hnd_tail. }
  assert (Hpath_pn_H : path_edges H (p ++ [n])%list).
  { apply path_edges_prefix_cons with (q := q). exact Hpath. }
  assert (Havoid : forall x, x ∈ (p ++ [n])%list -> x <> i).
  { intros x Hx E. subst x.
    apply (proj1 (@list_elem_of_In nat (p ++ [n]) i)) in Hx.
    apply List.in_app_or in Hx. destruct Hx as [Hxp|Hxn].
    - apply Hir. apply (proj2 (@list_elem_of_In nat (p ++ n :: q) i)).
      apply in_or_app. left. exact Hxp.
    - simpl in Hxn. destruct Hxn as [Ein|[]].
      exact (Hin (eq_sym Ein)). }
  assert (Hpath_pn_G : path_edges G (p ++ [n])%list).
  { apply (path_edges_mono_avoid_i G H i R HtoG); assumption. }
  assert (Hp_ne : p <> []).
  { intro Ep. subst p.
    simpl in HhdR. exact (HnR HhdR). }
  assert (Hlastpn : List.last (p ++ [n])%list 0 = n).
  { apply last_snoc. exact Hp_ne. }
  assert (Hpn_ne : (p ++ [n])%list <> []).
  { destruct p as [|x p']; [contradiction|]. discriminate. }
  assert (Hclosepath : path_edges G ((p ++ [n]) ++ [List.hd 0 (p ++ n :: q)])%list).
  { eapply path_edges_snoc.
    - exact Hpn_ne.
    - exact Hpath_pn_G.
    - rewrite Hlastpn. apply GnR. exact HhdR. }
  assert (Hlenpn : 3 <= List.length (p ++ [n])%list).
  { destruct p as [|x [|y p']].
    - contradiction.
    - exfalso.
      assert (HxR : x ∈ R).
      { simpl in HhdR. exact HhdR. }
      inversion Hpath_pn_H as [| |a b l Hr Hrest]; subst.
      exact (HnoH x HxR (Hsym x n Hr)).
    - simpl. rewrite List.length_app. simpl. lia. }
  unfold list_cycle. split; [exact Hlenpn|]. split; [exact Hnd_pn|].
  assert (Hhd_eq : List.hd 0 (p ++ [n])%list =
                   List.hd 0 (p ++ n :: q)%list).
  { transitivity (List.hd 0 p).
    - apply hd_snoc. exact Hp_ne.
    - symmetry. apply hd_prefix_cons. exact Hp_ne. }
  rewrite Hhd_eq. exact Hclosepath.
Qed.

(* A cycle obtained by taking the suffix of [p ++ n :: q] starting at [n],
   and closing it through [n] to the last vertex. *)
Lemma cycle_suffix_n
  (G H : nat -> nat -> Prop) (i n : nat) (R : gset nat) (p q : list nat) :
  (forall a b, H a b -> G a b \/ (a = i /\ b ∈ R) \/ (b = i /\ a ∈ R)) ->
  (forall a b, G a b -> G b a) ->
  (forall a b, H a b -> H b a) ->
  (forall r, r ∈ R -> G n r) ->
  (forall r, r ∈ R -> ~ H n r) ->
  i <> n ->
  n ∉ R ->
  NoDup (i :: p ++ n :: q)%list ->
  path_edges H (p ++ n :: q)%list ->
  List.last (p ++ n :: q)%list 0 ∈ R ->
  list_cycle G (n :: q)%list.
Proof.
  intros HtoG Gsym Hsym GnR HnoH Hin HnR Hnd Hpath HlastR.
  change (NoDup (i :: (p ++ n :: q)%list)) in Hnd.
  assert (Hir : i ∉ (p ++ n :: q)%list).
  { intro Hmem. pose proof Hnd as Hnd_copy.
    inversion Hnd_copy as [|x l Hnin Htail]; subst.
    apply Hnin.
    exact (proj1 (@list_elem_of_In nat (p ++ n :: q)%list i) Hmem). }
  assert (Hnd_tail : NoDup (p ++ n :: q)%list).
  { exact (NoDup_app_remove_l [i] (p ++ n :: q)%list Hnd). }
  assert (Hnd_nq : NoDup (n :: q)%list).
  { exact (NoDup_suffix_cons p q n Hnd_tail). }
  assert (Hpath_nq_H : path_edges H (n :: q)%list).
  { exact (path_edges_suffix_cons H p q n Hpath). }
  assert (Havoid : forall x, x ∈ (n :: q)%list -> x <> i).
  { intros x Hx E. subst x.
    apply (proj1 (@list_elem_of_In nat (n :: q)%list i)) in Hx.
    simpl in Hx. destruct Hx as [Ein|Hxq].
    - exact (Hin (eq_sym Ein)).
    - apply Hir. apply (proj2 (@list_elem_of_In nat (p ++ n :: q)%list i)).
      apply in_or_app. right. simpl. right. exact Hxq. }
  assert (Hpath_nq_G : path_edges G (n :: q)%list).
  { apply (path_edges_mono_avoid_i G H i R HtoG); assumption. }
  assert (Hq_ne : q <> []).
  { intro Eq. subst q.
    assert (Hl : List.last (p ++ [n])%list 0 = n).
    { apply last_snoc_any. }
    rewrite Hl in HlastR. exact (HnR HlastR). }
  assert (Hnq_ne : (n :: q)%list <> []). { discriminate. }
  assert (Hlast_nq : List.last (n :: q)%list 0 =
                     List.last (p ++ n :: q)%list 0).
  { symmetry. apply last_cons_app_nonempty. }
  assert (Hclosepath : path_edges G ((n :: q) ++ [n])%list).
  { eapply path_edges_snoc.
    - exact Hnq_ne.
    - exact Hpath_nq_G.
    - rewrite Hlast_nq. apply Gsym. apply GnR. exact HlastR. }
  assert (Hlennq : 3 <= List.length (n :: q)%list).
  { destruct q as [|x [|y q']].
    - contradiction.
    - exfalso.
      assert (HxR : x ∈ R).
      { rewrite last_cons_app_nonempty in HlastR. simpl in HlastR. exact HlastR. }
      inversion Hpath_nq_H as [| |a b l Hr Hrest]; subst.
      exact (HnoH x HxR Hr).
    - simpl. lia. }
  unfold list_cycle. split; [exact Hlennq|]. split; [exact Hnd_nq|].
  exact Hclosepath.
Qed.

(* Cycle [n :: r], used when both ends of [r] are in [R]. *)
Lemma cycle_n_r
  (G H : nat -> nat -> Prop) (i n : nat) (R : gset nat) (r : list nat) :
  (forall a b, H a b -> G a b \/ (a = i /\ b ∈ R) \/ (b = i /\ a ∈ R)) ->
  (forall a b, G a b -> G b a) ->
  (forall r, r ∈ R -> G n r) ->
  i <> n ->
  NoDup (i :: r)%list ->
  2 <= List.length r ->
  path_edges H r ->
  List.hd 0 r ∈ R ->
  List.last r 0 ∈ R ->
  n ∉ r ->
  list_cycle G (n :: r)%list.
Proof.
  intros HtoG Gsym GnR Hin Hnd Hrlen Hrpath HhdR HlastR Hnr.
  change (NoDup (i :: r)%list) in Hnd.
  assert (Hnd_r : NoDup r).
  { exact (NoDup_app_remove_l [i] r Hnd). }
  assert (Hir : i ∉ r).
  { intro Hmem. pose proof Hnd as Hnd_copy.
    inversion Hnd_copy as [|x l Hnin Htail]; subst.
    apply Hnin. exact (proj1 (@list_elem_of_In nat r i) Hmem). }
  assert (Havoid : forall x, x ∈ r -> x <> i).
  { intros x Hx E. subst x. exact (Hir Hx). }
  assert (HrG : path_edges G r).
  { apply (path_edges_mono_avoid_i G H i R HtoG r Havoid Hrpath). }
  assert (Hr_ne : r <> []).
  { destruct r; [simpl in Hrlen; lia|discriminate]. }
  assert (Hn_r_ne : (n :: r)%list <> []). { discriminate. }
  assert (Hpath_nr : path_edges G (n :: r)%list).
  { apply path_edges_cons with (l := r).
    - exact (GnR (List.hd 0 r) HhdR).
    - exact HrG. }
  assert (Hlast_nr : List.last (n :: r)%list 0 = List.last r 0).
  { destruct r as [|a r']; [contradiction|]. simpl. reflexivity. }
  assert (Hclosepath : path_edges G ((n :: r) ++ [n])%list).
  { eapply path_edges_snoc.
    - exact Hn_r_ne.
    - exact Hpath_nr.
    - rewrite Hlast_nr. apply Gsym. apply GnR. exact HlastR. }
  assert (Hnd_nr : NoDup (n :: r)%list).
  { apply NoDup_cons_iff. split; [|exact Hnd_r].
    intro Hmem. apply Hnr.
    exact (proj2 (@list_elem_of_In nat r n) Hmem). }
  assert (Hlennr : 3 <= List.length (n :: r)%list).
  { simpl. lia. }
  unfold list_cycle. split; [exact Hlennr|]. split; [exact Hnd_nr|].
  exact Hclosepath.
Qed.

Lemma last_cons_app_single (n : nat) (r : list nat) (i d : nat) :
  List.last (n :: (r ++ [i]))%list d = i.
Proof.
  change (List.last ((n :: r) ++ [i])%list d = i).
  apply last_snoc_any.
Qed.

(* Cycle [n :: r ++ [i]], used when the head of [r] is in [R]
   and its last vertex is not. *)
Lemma cycle_n_r_i
  (G H : nat -> nat -> Prop) (i n : nat) (R : gset nat) (r : list nat) :
  (forall a b, H a b -> G a b \/ (a = i /\ b ∈ R) \/ (b = i /\ a ∈ R)) ->
  (forall a b, G a b -> G b a) ->
  (forall r, r ∈ R -> G n r) ->
  G i n ->
  i <> n ->
  NoDup (i :: r)%list ->
  2 <= List.length r ->
  path_edges H r ->
  List.hd 0 r ∈ R ->
  List.last r 0 ∉ R ->
  H (List.last r 0) i ->
  n ∉ r ->
  list_cycle G (n :: (r ++ [i]))%list.
Proof.
  intros HtoG Gsym GnR Gin Hin Hnd Hrlen Hrpath HhdR HlastNR HlastEdge Hnr.
  change (NoDup (i :: r)%list) in Hnd.
  assert (Hnd_r : NoDup r).
  { exact (NoDup_app_remove_l [i] r Hnd). }
  assert (Hir : i ∉ r).
  { intro Hmem. pose proof Hnd as Hnd_copy.
    inversion Hnd_copy as [|x l Hnin Htail]; subst.
    apply Hnin. exact (proj1 (@list_elem_of_In nat r i) Hmem). }
  assert (Havoid : forall x, x ∈ r -> x <> i).
  { intros x Hx E. subst x. exact (Hir Hx). }
  assert (HrG : path_edges G r).
  { apply (path_edges_mono_avoid_i G H i R HtoG r Havoid Hrpath). }
  assert (Hr_ne : r <> []).
  { destruct r; [simpl in Hrlen; lia|discriminate]. }
  assert (HlastG : G (List.last r 0) i).
  { destruct (HtoG (List.last r 0) i HlastEdge) as [HG|[[E HR]|[E HR]]].
    - exact HG.
    - exfalso. apply HlastNR. rewrite E. exact HR.
    - exfalso. apply HlastNR. exact HR. }
  assert (Hpath_ri_G : path_edges G (r ++ [i])%list).
  { eapply path_edges_snoc.
    - exact Hr_ne.
    - exact HrG.
    - exact HlastG. }
  assert (Hpath_nri_G : path_edges G (n :: (r ++ [i]))%list).
  { apply path_edges_cons with (l := (r ++ [i])%list).
    - change (G n (List.hd 0 (r ++ [i]))).
      rewrite hd_snoc by exact Hr_ne.
      apply GnR. exact HhdR.
    - exact Hpath_ri_G. }
  assert (Hnd_nr : NoDup (n :: r)%list).
  { apply NoDup_cons.
    - intro Hinr. apply Hnr.
      exact (proj2 (@list_elem_of_In nat r n) Hinr).
    - exact Hnd_r. }
  assert (Hin_nr : ~ In i (n :: r)%list).
  { intro Hmem. simpl in Hmem. destruct Hmem as [E|Hinr].
    - exact (Hin (eq_sym E)).
    - apply Hir. exact (proj2 (@list_elem_of_In nat r i) Hinr). }
  assert (Hnd_nri : NoDup (n :: (r ++ [i]))%list).
  { change (NoDup ((n :: r) ++ [i])%list).
    apply NoDup_app.
    - exact Hnd_nr.
    - apply NoDup_single.
    - intros x Hx Hxi. simpl in Hxi. destruct Hxi as [E|[]].
      subst x. exact (Hin_nr Hx). }
  assert (Hnri_ne : (n :: (r ++ [i]))%list <> []). { discriminate. }
  assert (Hlast_nri : List.last (n :: (r ++ [i]))%list 0 = i).
  { apply last_cons_app_single. }
  assert (Hclosepath : path_edges G ((n :: (r ++ [i])) ++ [n])%list).
  { eapply path_edges_snoc.
    - exact Hnri_ne.
    - exact Hpath_nri_G.
    - rewrite Hlast_nri. exact Gin. }
  assert (Hlennri : 3 <= List.length (n :: (r ++ [i]))%list).
  { simpl. rewrite List.length_app. simpl. lia. }
  unfold list_cycle. split; [exact Hlennri|]. split; [exact Hnd_nri|].
  exact Hclosepath.
Qed.

(* Cycle [n :: i :: r], used when the head of [r] is not in [R]
   and its last vertex is in [R]. *)
Lemma cycle_n_i_r
  (G H : nat -> nat -> Prop) (i n : nat) (R : gset nat) (r : list nat) :
  (forall a b, H a b -> G a b \/ (a = i /\ b ∈ R) \/ (b = i /\ a ∈ R)) ->
  (forall a b, G a b -> G b a) ->
  (forall r, r ∈ R -> G n r) ->
  G i n ->
  i <> n ->
  NoDup (i :: r)%list ->
  2 <= List.length r ->
  path_edges H r ->
  List.hd 0 r ∉ R ->
  List.last r 0 ∈ R ->
  H i (List.hd 0 r) ->
  n ∉ r ->
  list_cycle G (n :: i :: r)%list.
Proof.
  intros HtoG Gsym GnR Gin Hin Hnd Hrlen Hrpath HhdNR HlastR Hiedge Hnr.
  assert (Hnd_r : NoDup r).
  { exact (NoDup_app_remove_l [i] r Hnd). }
  assert (Hir : i ∉ r).
  { intro Hmem. pose proof Hnd as Hnd_copy.
    inversion Hnd_copy as [|x l Hnin Htail]; subst.
    apply Hnin. exact (proj1 (@list_elem_of_In nat r i) Hmem). }
  assert (Havoid : forall x, x ∈ r -> x <> i).
  { intros x Hx E. subst x. exact (Hir Hx). }
  assert (HrG : path_edges G r).
  { apply (path_edges_mono_avoid_i G H i R HtoG r Havoid Hrpath). }
  assert (Hr_ne : r <> []).
  { destruct r; [simpl in Hrlen; lia|discriminate]. }
  assert (Hhd_ne_i : List.hd 0 r <> i).
  { intro E. apply Hir. rewrite <- E. apply elem_of_hd. exact Hr_ne. }
  assert (HhdG : G i (List.hd 0 r)).
  { destruct (HtoG i (List.hd 0 r) Hiedge) as [HG|[[E HR]|[E HR]]].
    - exact HG.
    - exfalso. apply HhdNR. exact HR.
    - exfalso. apply Hhd_ne_i. exact E. }
  assert (Hpath_ir_G : path_edges G (i :: r)%list).
  { apply path_edges_cons with (l := r).
    - exact HhdG.
    - exact HrG. }
  assert (Hpath_nir_G : path_edges G (n :: i :: r)%list).
  { apply path_edges_cons with (l := (i :: r)%list).
    - exact (Gsym i n Gin).
    - exact Hpath_ir_G. }
  assert (Hnd_nr : NoDup (n :: r)%list).
  { apply NoDup_cons.
    - intro Hinr. apply Hnr.
      exact (proj2 (@list_elem_of_In nat r n) Hinr).
    - exact Hnd_r. }
  assert (Hn_ir : ~ In n (i :: r)%list).
  { intro Hmem. simpl in Hmem. destruct Hmem as [E|Hinr].
    - exact (Hin E).
    - apply Hnr. exact (proj2 (@list_elem_of_In nat r n) Hinr). }
  assert (Hnd_nir : NoDup (n :: i :: r)%list).
  { apply NoDup_cons.
    - exact Hn_ir.
    - exact Hnd. }
  assert (Hnir_ne : (n :: i :: r)%list <> []). { discriminate. }
  assert (Hlast_nir : List.last (n :: i :: r)%list 0 = List.last r 0).
  { destruct r as [|a r']; [contradiction|]. simpl. reflexivity. }
  assert (Hclosepath : path_edges G ((n :: i :: r) ++ [n])%list).
  { eapply path_edges_snoc.
    - exact Hnir_ne.
    - exact Hpath_nir_G.
    - rewrite Hlast_nir. apply Gsym. apply GnR. exact HlastR. }
  assert (Hlennir : 3 <= List.length (n :: i :: r)%list).
  { simpl. lia. }
  unfold list_cycle. split; [exact Hlennir|]. split; [exact Hnd_nir|].
  exact Hclosepath.
Qed.

(* Split a duplicate-free list at its first occurrence of [i]. *)
Lemma list_split_at (l : list nat) (i : nat) :
  In i l -> exists pre rest, l = (pre ++ i :: rest)%list.
Proof.
  induction l as [|a l IH]; intros Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin. destruct Hin as [E|Hin].
    + subst a. exists [], l. reflexivity.
    + destruct (IH Hin) as [pre [rest E]].
      exists (a :: pre), rest. simpl. rewrite E. reflexivity.
Qed.

Lemma In_nil_nat (x : nat) : ~ In x [].
Proof. intros []. Qed.

Lemma cons_not_nil (a : nat) (l : list nat) : a :: l <> [].
Proof. discriminate. Qed.

(* Head and last edges of a path whose first vertex is [i]. *)
Lemma path_edges_head_edge (R : nat -> nat -> Prop) (i : nat) (l : list nat) :
  l <> [] -> path_edges R (i :: l) -> R i (List.hd 0 l).
Proof.
  intros Hne Hp. destruct l as [|a l'].
  - contradiction.
  - simpl in Hp. inversion Hp as [| |a0 b0 l0 Hr Hrest]; subst.
    exact Hr.
Qed.

Lemma path_edges_last_edge_cons (R : nat -> nat -> Prop) (i : nat) (l : list nat) :
  l <> [] -> path_edges R (i :: (l ++ [i])) -> R (List.last l 0) i.
Proof.
  intros Hne Hp.
  assert (Hpath : path_edges R ((i :: l) ++ [i])%list).
  { simpl. exact Hp. }
  assert (Hlast : List.last (i :: l) 0 = List.last l 0).
  { destruct l as [|a l'].
    - contradiction.
    - simpl. reflexivity. }
  assert (HE : R (List.last (i :: l) 0) i).
  { apply path_edges_last_edge; [exact Hpath|discriminate]. }
  rewrite Hlast in HE. exact HE.
Qed.

(* The internal path [l] of a path [i :: l ++ [i]] is a path. *)
Lemma path_edges_head_edge_closed (R : nat -> nat -> Prop) (i : nat) (r : list nat) :
  r <> [] -> path_edges R (i :: (r ++ [i])) -> R i (List.hd 0 r).
Proof.
  intros Hr_ne Hp.
  assert (Hne : (r ++ [i])%list <> []).
  { destruct r; [contradiction|discriminate]. }
  pose proof (path_edges_head_edge R i (r ++ [i])%list Hne Hp) as Hh.
  rewrite hd_snoc in Hh by exact Hr_ne. exact Hh.
Qed.

Lemma path_edges_internal (R : nat -> nat -> Prop) (i : nat) (l : list nat) :
  path_edges R (i :: (l ++ [i])) -> path_edges R l.
Proof.
  intro Hp.
  change (path_edges R ([i] ++ (l ++ [i]))%list) in Hp.
  pose proof (path_edges_suffix R [i] (l ++ [i])%list Hp) as Hs.
  exact (path_edges_prefix R l [i] Hs).
Qed.

(* A closed path through [i] with distinct vertices can be rotated so that
   it starts at [i]; the remaining vertices form a duplicate-free list [r]
   of length at least two that avoids [i]. *)
Lemma rotate_closed_path_at_i
  (H : nat -> nat -> Prop) (l : list nat) (i : nat) :
  NoDup l -> 3 <= List.length l -> In i l ->
  path_edges H (l ++ [List.hd 0 l]) ->
  exists r, NoDup (i :: r)%list /\ 2 <= List.length r /\
    ~ In i r /\ path_edges H (i :: (r ++ [i]))%list.
Proof.
  intros Hnd Hlen Hin Hpath.
  destruct (list_split_at l i Hin) as [pre [rest E]].
  rewrite E in Hnd, Hlen, Hpath.
  assert (Hnd_ir : NoDup (i :: rest)%list).
  { exact (NoDup_app_remove_l pre (i :: rest)%list Hnd). }
  assert (Hir : ~ In i rest).
  { exact (proj1 (proj1 (NoDup_cons_iff i rest) Hnd_ir)). }
  destruct pre as [|a pre'].
  - simpl in Hpath.
    exists rest. split; [exact Hnd_ir|]. split.
    + simpl in Hlen. lia.
    + split; [exact Hir|].
      change (path_edges H (i :: (rest ++ [i]))%list). exact Hpath.
  - assert (Hhd : List.hd 0 ((a :: pre') ++ i :: rest)%list = List.hd 0 (a :: pre')%list).
    { apply hd_prefix_cons. discriminate. }
    rewrite Hhd in Hpath.
    rewrite <- app_assoc in Hpath.
    pose proof (path_edges_rotate_at H (a :: pre')%list (i :: rest)%list
                  (cons_not_nil a pre') (cons_not_nil i rest) Hpath) as Hrot.
    assert (Hnd_rot : NoDup (i :: (rest ++ (a :: pre')))%list).
    { change (NoDup ((i :: rest) ++ (a :: pre'))%list).
      exact (NoDup_rotate (a :: pre')%list rest i Hnd). }
    exists (rest ++ (a :: pre'))%list. split; [exact Hnd_rot|]. split.
    + rewrite List.length_app. simpl.
      rewrite List.length_app in Hlen. simpl in Hlen. lia.
    + split.
      * exact (proj1 (proj1 (NoDup_cons_iff i (rest ++ (a :: pre'))%list) Hnd_rot)).
      * rewrite <- app_assoc. exact Hrot.
Qed.

Lemma last_cons_nonempty (i : nat) (r : list nat) :
  r <> [] -> List.last (i :: r)%list 0 = List.last r 0.
Proof.
  destruct r as [|a r']; [contradiction|]. simpl. reflexivity.
Qed.

Definition forest_rel (R : nat -> nat -> Prop) : Prop :=
  forall l, ~ list_cycle R l.

(* The abstract bridge/reattachment lemma for forests: target edges are
   source edges except for edges from [i] to [R]; source edges [n-r] for
   [r in R] are removed and reattached at [i], and [i-n] is a source edge.
   Then acyclicity (in the simple cycle sense) is preserved. *)
Lemma forest_rewire_star_at_i
  (G H : nat -> nat -> Prop) (i n : nat) (R : gset nat) :
  (forall a b, H a b -> G a b \/ (a = i /\ b ∈ R) \/ (b = i /\ a ∈ R)) ->
  (forall a b, G a b -> G b a) ->
  (forall a b, H a b -> H b a) ->
  (forall r, r ∈ R -> G n r) ->
  G i n ->
  (forall r, r ∈ R -> ~ H n r) ->
  i <> n -> n ∉ R ->
  forest_rel G -> forest_rel H.
Proof.
  intros HtoG Gsym Hsym GnR Gin HnoH Hin HnR Hforest l Hcyc.
  destruct Hcyc as [Hlen [Hnd Hpath]].
  destruct (In_dec Nat.eq_dec i l) as [Hi|Hi].
  - destruct (rotate_closed_path_at_i H l i Hnd Hlen Hi Hpath)
      as [r [Hnd_ir [Hrlen [Hir Hrot]]]].
    assert (Hr_ne : r <> []).
    { destruct r; [simpl in Hrlen; lia|discriminate]. }
    assert (Hr : path_edges H r).
    { exact (path_edges_internal H i r Hrot). }
    assert (Havoid : forall x, x ∈ r -> x <> i).
    { intros x Hx E. subst x. apply Hir.
      exact (proj1 (@list_elem_of_In nat r i) Hx). }
    assert (Gr : path_edges G r).
    { apply (path_edges_mono_avoid_i G H i R HtoG r Havoid Hr). }
    destruct (decide (List.hd 0 r ∈ R)) as [HhdR|HhdNR].
    + destruct (decide (n ∈ r)) as [Hnin|Hnin].
      * apply (proj1 (@list_elem_of_In nat r n)) in Hnin.
        destruct (list_split_at r n Hnin) as [p [q Er]].
        rewrite Er in HhdR, Hrlen, Hnd_ir, Hr.
        assert (Hp_ne : p <> []).
        { intro Ep. subst p. simpl in HhdR. exact (HnR HhdR). }
        pose proof (cycle_prefix_n G H i n R p q HtoG Gsym Hsym GnR HnoH
                      Hin HnR Hnd_ir Hrlen Hr HhdR) as Hc.
        exact (Hforest _ Hc).
      * destruct (decide (List.last r 0 ∈ R)) as [HlastR|HlastNR].
        -- pose proof (cycle_n_r G H i n R r HtoG Gsym GnR Hin Hnd_ir
                         Hrlen Hr HhdR HlastR Hnin) as Hc.
           exact (Hforest _ Hc).
        -- assert (HlastEdge : H (List.last r 0) i).
           { exact (path_edges_last_edge_cons H i r Hr_ne Hrot). }
           pose proof (cycle_n_r_i G H i n R r HtoG Gsym GnR Gin Hin Hnd_ir
                         Hrlen Hr HhdR HlastNR HlastEdge Hnin) as Hc.
           exact (Hforest _ Hc).
    + destruct (decide (List.last r 0 ∈ R)) as [HlastR|HlastNR].
      * destruct (decide (n ∈ r)) as [Hnin|Hnin].
        -- apply (proj1 (@list_elem_of_In nat r n)) in Hnin.
           destruct (list_split_at r n Hnin) as [p [q Er]].
           rewrite Er in HlastR, Hnd_ir, Hr.
           pose proof (cycle_suffix_n G H i n R p q HtoG Gsym Hsym GnR HnoH
                         Hin HnR Hnd_ir Hr HlastR) as Hc.
           exact (Hforest _ Hc).
        -- assert (Hiedge : H i (List.hd 0 r)).
           { exact (path_edges_head_edge_closed H i r Hr_ne Hrot). }
           pose proof (cycle_n_i_r G H i n R r HtoG Gsym GnR Gin Hin Hnd_ir
                         Hrlen Hr HhdNR HlastR Hiedge Hnin) as Hc.
           exact (Hforest _ Hc).
      * (* neither endpoint is in R: the internal path itself is a source cycle through i *)
        assert (Hiedge : H i (List.hd 0 r)).
        { exact (path_edges_head_edge_closed H i r Hr_ne Hrot). }
        assert (HlastEdge : H (List.last r 0) i).
        { exact (path_edges_last_edge_cons H i r Hr_ne Hrot). }
        assert (Hhd_i : List.hd 0 r <> i).
        { intro E. apply Hir. rewrite <- E. apply hd_in_list. exact Hr_ne. }
        assert (Hlast_i : List.last r 0 <> i).
        { intro E. apply Hir. rewrite <- E. apply last_in_list. exact Hr_ne. }
        assert (HhdG : G i (List.hd 0 r)).
        { destruct (HtoG i (List.hd 0 r) Hiedge) as [HG|[[E HR]|[E HR]]].
          - exact HG.
          - exfalso. apply HhdNR. exact HR.
          - exfalso. apply Hhd_i. exact E. }
        assert (HlastG : G (List.last r 0) i).
        { destruct (HtoG (List.last r 0) i HlastEdge) as [HG|[[E HR]|[E HR]]].
          - exact HG.
          - exfalso. apply Hlast_i. exact E.
          - exfalso. apply HlastNR. exact HR. }
        assert (Gpath_ir : path_edges G (i :: r)%list).
        { apply path_edges_cons with (l := r).
          - exact HhdG.
          - exact Gr. }
        assert (Gclosed : path_edges G ((i :: r) ++ [i])%list).
        { eapply path_edges_snoc.
          - exact (cons_not_nil i r).
          - exact Gpath_ir.
          - rewrite (last_cons_nonempty i r Hr_ne). exact HlastG. }
        assert (HlenG : 3 <= List.length (i :: r)%list).
        { simpl. lia. }
        apply (Hforest (i :: r)%list). split; [exact HlenG|].
        split; [exact Hnd_ir|exact Gclosed].
  - (* [i] does not occur on the cycle: every target edge is a source edge *)
    assert (Havoid : forall x, x ∈ (l ++ [List.hd 0 l])%list -> x <> i).
    { intros x Hx E. subst x.
      apply (proj1 (@list_elem_of_In nat (l ++ [List.hd 0 l]) i)) in Hx.
      apply in_app_or in Hx. destruct Hx as [Hxl|Hxs].
      - exact (Hi Hxl).
      - simpl in Hxs. destruct Hxs as [Ehd|[]].
        apply Hi. rewrite <- Ehd. apply hd_in_list.
        destruct l; [simpl in Hlen; lia|discriminate]. }
    assert (Gpath : path_edges G (l ++ [List.hd 0 l])%list).
    { apply (path_edges_mono_avoid_i G H i R HtoG
               (l ++ [List.hd 0 l]) Havoid Hpath). }
    apply (Hforest l). split; [exact Hlen|]. split; [exact Hnd|exact Gpath].
Qed.

(* ===== ForestStep.v ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap list.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Relation_Operators.
Import ListNotations.
Close Scope string_scope.


(* ================================================================== *)
(* Forest preservation by shrinking the reference relation.           *)
(* ================================================================== *)

Lemma ref_edge_mono (ρ ρ' : cfg) :
  (forall a, refs_at ρ' a ⊆ refs_at ρ a) ->
  forall a b, ref_edge ρ' a b -> ref_edge ρ a b.
Proof.
  intros Hsub a b [Hne [Hb|Ha]].
  - split; [exact Hne|left]. apply (Hsub a). exact Hb.
  - split; [exact Hne|right]. apply (Hsub b). exact Ha.
Qed.

Lemma path_edges_mono (R S : nat -> nat -> Prop) :
  (forall a b, R a b -> S a b) ->
  forall l, path_edges R l -> path_edges S l.
Proof.
  intros Hsub l Hp. induction Hp as [|a|a b l Hr Hrest IH].
  - apply pe_nil.
  - apply pe_one.
  - eapply pe_cons.
    + apply Hsub. exact Hr.
    + exact IH.
Qed.

Lemma ref_forest_shrink (ρ ρ' : cfg) :
  (forall a, refs_at ρ' a ⊆ refs_at ρ a) ->
  ref_forest ρ -> ref_forest ρ'.
Proof.
  intros Hsub Hforest l [Hlen [Hnd Hpath]].
  apply (Hforest l).
  split; [exact Hlen|]. split; [exact Hnd|].
  apply (path_edges_mono (ref_edge ρ') (ref_edge ρ)).
  - apply ref_edge_mono. exact Hsub.
  - exact Hpath.
Qed.

Lemma Pure_step_ref_forest i k e e' :
  ctx k -> pure_step e e' ->
  ref_forest ({[i := Thread (k e)]} : cfg) ->
  ref_forest ({[i := Thread (k e')]} : cfg).
Proof.
  intros Hk Hps. apply ref_forest_shrink.
  apply Pure_local_shrink; assumption.
Qed.

Lemma Exit_step_ref_forest i :
  ref_forest ({[i := Thread (Val UnitV)]} : cfg) ->
  ref_forest (∅ : cfg).
Proof.
  intros. apply ref_forest_shrink with (ρ := ({[i := Thread (Val UnitV)]} : cfg)).
  - apply Exit_local_shrink.
  - exact H.
Qed.

Print Assumptions ref_forest_shrink.
Print Assumptions Pure_step_ref_forest.
Print Assumptions Exit_step_ref_forest.
Print Assumptions forest_rewire_star_at_i.

(* ===== PairMove.v ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap list.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Strings.String.
Import ListNotations.
Close Scope string_scope.


(* ================================================================== *)
(* Pair preservation for a bundle of edges moved from [n] to [i].     *)
(* This is the set-level counterpart of the forest bridge move.       *)
(* ================================================================== *)

Definition self_free_fun (S : nat -> gset nat) : Prop :=
  forall a, a ∉ S a.

Definition pair_ok_fun (S : nat -> gset nat) : Prop :=
  forall a b, a <> b -> ~ (b ∈ S a /\ a ∈ S b).

Definition ref_pair_ok_fun (S : nat -> gset nat) : Prop :=
  self_free_fun S /\ pair_ok_fun S.

Lemma pair_move_add (S T : nat -> gset nat) (i n : nat) (B : gset nat) :
  ref_pair_ok_fun S ->
  T i = S i ∪ B ->
  T n = ∅ ->
  (forall a, a <> i -> a <> n -> T a = S a) ->
  i ∉ B ->
  (forall b, b ∈ B -> i ∉ T b) ->
  ref_pair_ok_fun T.
Proof.
  intros [Hself Hpair] HTi HTn Hother HiB Hrev.
  split.
  - intro a. destruct (decide (a = i)) as [E|Hai].
    + subst a. rewrite HTi. intro Hmem.
      apply elem_of_union in Hmem as [Hin|Hin].
      * exact (Hself i Hin).
      * exact (HiB Hin).
    + destruct (decide (a = n)) as [E|Han].
      * subst a. rewrite HTn. set_solver.
      * rewrite (Hother a Hai Han). apply Hself.
  - intros a b Hne [Hb Ha].
    destruct (decide (a = i)) as [Ea|Hai].
    + subst a. rewrite HTi in Hb.
      apply elem_of_union in Hb as [HbS|HbB].
      * destruct (decide (b = n)) as [Eb|Hbn].
        -- subst b. rewrite HTn in Ha. set_solver.
        -- rewrite (Hother b (ne_sym Hne) Hbn) in Ha.
           exact (Hpair i b Hne (conj HbS Ha)).
      * exact (Hrev b HbB Ha).
    + destruct (decide (a = n)) as [Ea|Han].
      * subst a. rewrite HTn in Hb. set_solver.
      * rewrite (Hother a Hai Han) in Hb.
        destruct (decide (b = i)) as [Eb|Hbi].
        -- subst b. rewrite HTi in Ha.
           apply elem_of_union in Ha as [HaS|HaB].
           ++ exact (Hpair a i Hne (conj Hb HaS)).
           ++ apply (Hrev a HaB). rewrite (Hother a Hai Han). exact Hb.
        -- destruct (decide (b = n)) as [Eb|Hbn].
           ++ subst b. rewrite HTn in Ha. set_solver.
           ++ rewrite (Hother b Hbi Hbn) in Ha.
              exact (Hpair a b Hne (conj Hb Ha)).
Qed.

(* Transfer between the set-function presentation and [cfg]. *)
Lemma ref_pair_ok_fun_iff (ρ : cfg) :
  ref_pair_ok_fun (refs_at ρ) <-> ref_pair_ok ρ.
Proof.
  unfold ref_pair_ok_fun, ref_pair_ok, self_free_fun, pair_ok_fun,
         self_ref_free, pair_ref_ok.
  split; intros [H1 H2]; split; assumption.
Qed.

Print Assumptions pair_move_add.
Print Assumptions ref_pair_ok_fun_iff.

(* ===== KindRefs.v ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.

(* ================================================================== *)
(* Kind-respecting reference sets.                                    *)
(*                                                                    *)
(* [expr_refs] / [val_refs] forget whether a reference came from a    *)
(* [LockV] or a [BarrierV].  These traversals keep the two kinds       *)
(* apart, so a configuration can be required to have every [LockV n]   *)
(* point at a live [Lock] and every [BarrierV n] at a live [Barrier].  *)
(* Counts are still set-based: this is exactly the set of indices      *)
(* occurring with the given constructor, not a multiplicity.           *)
(* ================================================================== *)

Fixpoint expr_lock_refs (e : expr) : gset nat :=
  match e with
  | Val v => val_lock_refs v
  | Var _ => ∅
  | Fun _ e => expr_lock_refs e
  | App e1 e2 => expr_lock_refs e1 ∪ expr_lock_refs e2
  | Unit => ∅
  | Pair e1 e2 => expr_lock_refs e1 ∪ expr_lock_refs e2
  | LetPair e1 e2 => expr_lock_refs e1 ∪ expr_lock_refs e2
  | Sum _ e => expr_lock_refs e
  | MatchSum n e es => expr_lock_refs e ∪ fin_union n (expr_lock_refs ∘ es)
  | ForkBarrier e => expr_lock_refs e
  | NewLock e => expr_lock_refs e
  | ForkLock e1 e2 => expr_lock_refs e1 ∪ expr_lock_refs e2
  | Acquire e => expr_lock_refs e
  | Release e1 e2 => expr_lock_refs e1 ∪ expr_lock_refs e2
  | Wait e => expr_lock_refs e
  | Drop e => expr_lock_refs e
  end
with val_lock_refs (v : val) : gset nat :=
  match v with
  | FunV _ e => expr_lock_refs e
  | UnitV => ∅
  | PairV v1 v2 => val_lock_refs v1 ∪ val_lock_refs v2
  | SumV _ v => val_lock_refs v
  | BarrierV _ => ∅
  | LockV n => {[n]}
  end.

Fixpoint expr_barrier_refs (e : expr) : gset nat :=
  match e with
  | Val v => val_barrier_refs v
  | Var _ => ∅
  | Fun _ e => expr_barrier_refs e
  | App e1 e2 => expr_barrier_refs e1 ∪ expr_barrier_refs e2
  | Unit => ∅
  | Pair e1 e2 => expr_barrier_refs e1 ∪ expr_barrier_refs e2
  | LetPair e1 e2 => expr_barrier_refs e1 ∪ expr_barrier_refs e2
  | Sum _ e => expr_barrier_refs e
  | MatchSum n e es => expr_barrier_refs e ∪ fin_union n (expr_barrier_refs ∘ es)
  | ForkBarrier e => expr_barrier_refs e
  | NewLock e => expr_barrier_refs e
  | ForkLock e1 e2 => expr_barrier_refs e1 ∪ expr_barrier_refs e2
  | Acquire e => expr_barrier_refs e
  | Release e1 e2 => expr_barrier_refs e1 ∪ expr_barrier_refs e2
  | Wait e => expr_barrier_refs e
  | Drop e => expr_barrier_refs e
  end
with val_barrier_refs (v : val) : gset nat :=
  match v with
  | FunV _ e => expr_barrier_refs e
  | UnitV => ∅
  | PairV v1 v2 => val_barrier_refs v1 ∪ val_barrier_refs v2
  | SumV _ v => val_barrier_refs v
  | BarrierV n => {[n]}
  | LockV _ => ∅
  end.

(* Kind liveness: every kind-specific reference in a live object points
   at a live object of that kind. *)

Definition kind_lock_live (ρ : cfg) : Prop :=
  (forall i e n, ρ !! i = Some (Thread e) ->
     n ∈ expr_lock_refs e -> exists rc o, ρ !! n = Some (Lock rc o)) /\
  (forall i rc (o : option val) v n, ρ !! i = Some (Lock rc (Some v)) ->
     n ∈ val_lock_refs v -> exists rc' o', ρ !! n = Some (Lock rc' o')).

Definition kind_barrier_live (ρ : cfg) : Prop :=
  (forall i e n, ρ !! i = Some (Thread e) ->
     n ∈ expr_barrier_refs e -> ρ !! n = Some Barrier) /\
  (forall i rc (o : option val) v n, ρ !! i = Some (Lock rc (Some v)) ->
     n ∈ val_barrier_refs v -> ρ !! n = Some Barrier).

Definition kind_live (ρ : cfg) : Prop :=
  kind_lock_live ρ /\ kind_barrier_live ρ.

(* ===== KindLiveFacts.v ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import List Arith Lia.

(* ================================================================== *)
(* Set-level consequences of kind liveness.                           *)
(* ================================================================== *)

Scheme expr_mut := Induction for expr Sort Prop
with val_mut := Induction for val Sort Prop.

Definition memE (e : expr) : Prop :=
  forall n, n ∈ expr_refs e <-> n ∈ expr_lock_refs e \/ n ∈ expr_barrier_refs e.

Definition memV (v : val) : Prop :=
  forall n, n ∈ val_refs v <-> n ∈ val_lock_refs v \/ n ∈ val_barrier_refs v.

Lemma expr_refs_kind_split : forall e, memE e.
Proof.
  apply (expr_mut memE memV).
  - intros v Hv n. apply Hv.
  - intros s n. simpl. set_solver.
  - intros s e IH n. apply IH.
  - intros e1 IH1 e2 IH2 n. simpl.
    specialize (IH1 n). specialize (IH2 n). set_solver.
  - intros n. simpl. set_solver.
  - intros e1 IH1 e2 IH2 n. simpl.
    specialize (IH1 n). specialize (IH2 n). set_solver.
  - intros e1 IH1 e2 IH2 n. simpl.
    specialize (IH1 n). specialize (IH2 n). set_solver.
  - intros k e IH n. apply IH.
  - intros k e0 IH0 es IHf n. simpl. specialize (IH0 n).
    split.
    + intro H. apply elem_of_union in H as [H|H].
      * destruct (proj1 IH0 H) as [Hl|Hb].
        -- left. apply elem_of_union. left. exact Hl.
        -- right. apply elem_of_union. left. exact Hb.
      * apply elem_of_fin_union in H as [i Hi].
        destruct (proj1 (IHf i n) Hi) as [Hl|Hb].
        -- left. apply elem_of_union. right. apply elem_of_fin_union. exists i. exact Hl.
        -- right. apply elem_of_union. right. apply elem_of_fin_union. exists i. exact Hb.
    + intro H. destruct H as [H|H].
      * apply elem_of_union in H as [Hl|Hl].
        -- apply elem_of_union. left. exact (proj2 IH0 (or_introl Hl)).
        -- apply elem_of_fin_union in Hl. destruct Hl as [i Hi].
           apply elem_of_union. right. apply elem_of_fin_union. exists i.
           exact (proj2 (IHf i n) (or_introl Hi)).
      * apply elem_of_union in H as [Hb|Hb].
        -- apply elem_of_union. left. exact (proj2 IH0 (or_intror Hb)).
        -- apply elem_of_fin_union in Hb. destruct Hb as [i Hi].
           apply elem_of_union. right. apply elem_of_fin_union. exists i.
           exact (proj2 (IHf i n) (or_intror Hi)).
  - intros e IH n. apply IH.
  - intros e IH n. apply IH.
  - intros e1 IH1 e2 IH2 n. simpl.
    specialize (IH1 n). specialize (IH2 n). set_solver.
  - intros e IH n. apply IH.
  - intros e1 IH1 e2 IH2 n. simpl.
    specialize (IH1 n). specialize (IH2 n). set_solver.
  - intros e IH n. apply IH.
  - intros e IH n. apply IH.
  - intros s e IH n. apply IH.
  - intros n. unfold val_refs, val_lock_refs, val_barrier_refs. simpl. set_solver.
  - intros v1 IH1 v2 IH2 n. simpl.
    specialize (IH1 n). specialize (IH2 n). set_solver.
  - intros k v IH n. apply IH.
  - intros n n0. unfold val_refs, val_lock_refs, val_barrier_refs. simpl. set_solver.
  - intros n n0. unfold val_refs, val_lock_refs, val_barrier_refs. simpl. set_solver.
Qed.

Lemma val_refs_kind_split : forall v, memV v.
Proof.
  intros w. apply val_ind.
  - intros s e n. apply (expr_refs_kind_split e n).
  - intros n. unfold val_refs, val_lock_refs, val_barrier_refs. simpl. set_solver.
  - intros v1 IH1 v2 IH2 n. simpl.
    specialize (IH1 n). specialize (IH2 n). set_solver.
  - intros k v IH n. apply IH.
  - intros n n0. unfold val_refs, val_lock_refs, val_barrier_refs. simpl. set_solver.
  - intros n n0. unfold val_refs, val_lock_refs, val_barrier_refs. simpl. set_solver.
Qed.

Lemma mem_expr_refs_kind e n :
  n ∈ expr_refs e <-> n ∈ expr_lock_refs e \/ n ∈ expr_barrier_refs e.
Proof. exact (expr_refs_kind_split e n). Qed.

Lemma mem_val_refs_kind v n :
  n ∈ val_refs v <-> n ∈ val_lock_refs v \/ n ∈ val_barrier_refs v.
Proof. exact (val_refs_kind_split v n). Qed.

(* No live object refers to an index occupied by a live thread. *)

Lemma kind_live_no_thread_in_refs_at (ρ : cfg) i e b
    (Hkind : kind_live ρ) (Hi : ρ !! i = Some (Thread e))
    (Hb : ρ !! b <> None) : i ∉ refs_at ρ b.
Proof.
  destruct Hkind as [[Hlock_thr Hlock_val] [Hbar_thr Hbar_val]].
  unfold refs_at.
  destruct (ρ !! b) as [y|] eqn:Eb; [|set_solver].
  destruct y as [e0| |rc o].
  - simpl. intro Hiin.
    apply mem_expr_refs_kind in Hiin as [Hl|Hbarr].
    + destruct (Hlock_thr b e0 i Eb Hl) as (rc' & o' & Hlock).
      rewrite Hi in Hlock. discriminate.
    + pose proof (Hbar_thr b e0 i Eb Hbarr) as Hbar.
      rewrite Hi in Hbar. discriminate.
  - simpl. set_solver.
  - destruct o as [v|].
    + simpl. intro Hiin.
      apply mem_val_refs_kind in Hiin as [Hl|Hbarr].
      * destruct (Hlock_val b rc (Some v) v i Eb Hl) as (rc' & o' & Hlock).
        rewrite Hi in Hlock. discriminate.
      * pose proof (Hbar_val b rc (Some v) v i Eb Hbarr) as Hbar.
        rewrite Hi in Hbar. discriminate.
    + simpl. set_solver.
Qed.

Lemma lock_content_no_thread_ref (ρ : cfg) n rc v i e
    (Hkind : kind_live ρ) (Hlock : ρ !! n = Some (Lock rc (Some v)))
    (Hi : ρ !! i = Some (Thread e)) : i ∉ val_refs v.
Proof.
  assert (Hri : i ∉ refs_at ρ n).
  { apply (kind_live_no_thread_in_refs_at ρ i e n Hkind Hi).
    rewrite Hlock. discriminate. }
  unfold refs_at in Hri. rewrite Hlock in Hri. simpl in Hri. exact Hri.
Qed.

Print Assumptions expr_refs_kind_split.
Print Assumptions val_refs_kind_split.
Print Assumptions kind_live_no_thread_in_refs_at.
Print Assumptions lock_content_no_thread_ref.

(* ===== ThreadTypedFrame.v ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import Strings.String.

(* ================================================================== *)
(* Framing for [threads_typed].                                        *)
(* ================================================================== *)

Lemma threads_typed_frame L (a a' ρf : cfg) :
  a ##ₘ ρf -> a' ##ₘ ρf ->
  threads_typed L (a ∪ ρf) ->
  threads_typed L a' ->
  threads_typed L (a' ∪ ρf).
Proof.
  intros Ha Haa Hsrc Hloc j e Hj.
  apply (proj1 (lookup_union_Some a' ρf j (Thread e) Haa)) in Hj.
  destruct Hj as [Hj|Hj].
  - exact (Hloc j e Hj).
  - exact (Hsrc j e (proj2 (lookup_union_Some a ρf j (Thread e) Ha) (or_intror Hj))).
Qed.

(* Extract the typing of the non-framed part.  Disjointness is not
   needed: a [Some] lookup in the left component survives the union. *)
Lemma threads_typed_frame_inv L (a ρf : cfg) :
  threads_typed L (a ∪ ρf) ->
  threads_typed L a.
Proof.
  intros Hty j e Hj.
  exact (Hty j e (lookup_union_Some_l a ρf j (Thread e) Hj)).
Qed.

Print Assumptions threads_typed_frame.
Print Assumptions threads_typed_frame_inv.

(* ===== BarrierTyping.v ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Strings.String.
Open Scope string_scope.

(* ================================================================== *)
(* Barrier endpoint typing, and Sync preservation.                     *)
(*                                                                    *)
(* Plain [wt] allows a [BarrierV n] to be used at ANY function type.   *)
(* Therefore two threads can synchronise on n with unrelated endpoint  *)
(* types and the result of Sync is not [wt] (see                   *)
(* ThreadTypedSyncCex.v).  The repair is to record, for every barrier  *)
(* endpoint occurrence, the oriented pair of endpoint types.           *)
(*                                                                    *)
(* [sync_endpoint_typing] below is the exact interface that such an    *)
(* oriented store must provide for one Sync redex:                     *)
(*   - the values carried by the two endpoints have the two endpoint   *)
(*     types;                                                          *)
(*   - the barrier occurrence in thread i has result type [t2];        *)
(*   - the barrier occurrence in thread j has result type [t1].        *)
(* The last two clauses say that the occurrences use the two opposite  *)
(* orientations of the same barrier.  They are precisely what plain    *)
(* [wt] does not determine, and what the Sync counterexample exploits. *)
(* ================================================================== *)

Definition sync_src i j n k1 k2 v1 v2 : cfg :=
  {[ i := Thread (k1 (App (Val (BarrierV n)) (Val v1)));
     j := Thread (k2 (App (Val (BarrierV n)) (Val v2)));
     n := Barrier ]}.

Definition sync_tgt i j k1 k2 v1 v2 : cfg :=
  {[ i := Thread (k1 (Val v2));
     j := Thread (k2 (Val v1)) ]}.

Definition sync_endpoint_typing L n v1 v2 t1 t2 : Prop :=
  wt L ∅ (Val v1) t1 /\
  wt L ∅ (Val v2) t2 /\
  (forall s, wt L ∅ (App (Val (BarrierV n)) (Val v1)) s -> s = t2) /\
  (forall s, wt L ∅ (App (Val (BarrierV n)) (Val v2)) s -> s = t1).

Lemma sync_src_i i j n k1 k2 v1 v2 :
  sync_src i j n k1 k2 v1 v2 !! i =
  Some (Thread (k1 (App (Val (BarrierV n)) (Val v1)))).
Proof. unfold sync_src. apply lookup_insert_eq. Qed.

Lemma sync_src_j i j n k1 k2 v1 v2 (Hji : j <> i) (Hjn : j <> n) :
  sync_src i j n k1 k2 v1 v2 !! j =
  Some (Thread (k2 (App (Val (BarrierV n)) (Val v2)))).
Proof.
  unfold sync_src.
  change ((<[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)))]>
            (<[j := Thread (k2 (App (Val (BarrierV n)) (Val v2)))]>
             (<[n := Barrier]> (∅ : cfg)))) !! j
          = Some (Thread (k2 (App (Val (BarrierV n)) (Val v2))))).
  assert (H : (<[i := Thread (k1 (App (Val (BarrierV n)) (Val v1)))]>
               (<[j := Thread (k2 (App (Val (BarrierV n)) (Val v2)))]>
                (<[n := Barrier]> (∅ : cfg)))) !! j
            = (<[j := Thread (k2 (App (Val (BarrierV n)) (Val v2)))]>
               (<[n := Barrier]> (∅ : cfg))) !! j).
  { apply lookup_insert_ne. congruence. }
  rewrite H. apply lookup_insert_eq.
Qed.

Lemma sync_tgt_i i j k1 k2 v1 v2 :
  sync_tgt i j k1 k2 v1 v2 !! i = Some (Thread (k1 (Val v2))).
Proof. unfold sync_tgt. apply lookup_insert_eq. Qed.

Lemma sync_tgt_j i j k1 k2 v1 v2 (Hji : j <> i) :
  sync_tgt i j k1 k2 v1 v2 !! j = Some (Thread (k2 (Val v1))).
Proof.
  unfold sync_tgt.
  change ((<[i := Thread (k1 (Val v2))]>
            (<[j := Thread (k2 (Val v1))]> (∅ : cfg))) !! j
          = Some (Thread (k2 (Val v1)))).
  assert (H : (<[i := Thread (k1 (Val v2))]>
               (<[j := Thread (k2 (Val v1))]> (∅ : cfg))) !! j
            = (<[j := Thread (k2 (Val v1))]> (∅ : cfg)) !! j).
  { apply lookup_insert_ne. congruence. }
  rewrite H. apply lookup_insert_eq.
Qed.

Lemma sync_tgt_other i j k1 k2 v1 v2 x (Hxi : x <> i) (Hxj : x <> j) :
  sync_tgt i j k1 k2 v1 v2 !! x = None.
Proof.
  unfold sync_tgt.
  change ((<[i := Thread (k1 (Val v2))]>
            (<[j := Thread (k2 (Val v1))]> (∅ : cfg))) !! x = None).
  assert (H : (<[i := Thread (k1 (Val v2))]>
               (<[j := Thread (k2 (Val v1))]> (∅ : cfg))) !! x
            = (<[j := Thread (k2 (Val v1))]> (∅ : cfg)) !! x).
  { apply lookup_insert_ne. congruence. }
  assert (H2 : (<[j := Thread (k2 (Val v1))]> (∅ : cfg)) !! x
             = (∅ : cfg) !! x).
  { apply lookup_insert_ne. congruence. }
  rewrite H, H2. apply lookup_empty.
Qed.

Lemma sync_local_threads_typed L i j n k1 k2 v1 v2 t1 t2
    (Hij : i <> j) (Hin : i <> n) (Hjn : j <> n)
    (Hk1 : ctx k1) (Hk2 : ctx k2)
    (Hend : sync_endpoint_typing L n v1 v2 t1 t2) :
  threads_typed L (sync_src i j n k1 k2 v1 v2) ->
  threads_typed L (sync_tgt i j k1 k2 v1 v2).
Proof.
  intros Hsrc x e Hx.
  destruct Hend as (Hv1 & Hv2 & Hap1 & Hap2).
  destruct (decide (x = i)) as [E|Exi].
  - subst x. rewrite sync_tgt_i in Hx. inversion Hx; subst e.
    apply (wt_ctx_replace L k1
             (App (Val (BarrierV n)) (Val v1)) (Val v2) UnitT Hk1).
    + apply (Hsrc i (k1 (App (Val (BarrierV n)) (Val v1)))).
      apply sync_src_i.
    + intros s Hs. specialize (Hap1 s Hs). subst s. exact Hv2.
  - destruct (decide (x = j)) as [E|Exj].
    + subst x. rewrite sync_tgt_j in Hx; [| congruence].
      inversion Hx; subst e.
      apply (wt_ctx_replace L k2
               (App (Val (BarrierV n)) (Val v2)) (Val v1) UnitT Hk2).
      * apply (Hsrc j (k2 (App (Val (BarrierV n)) (Val v2)))).
        apply sync_src_j; congruence.
      * intros s Hs. specialize (Hap2 s Hs). subst s. exact Hv1.
    + rewrite sync_tgt_other in Hx; [discriminate | exact Exi | exact Exj].
Qed.

(* Framed form, matching the actual Sync_step rule. *)

Lemma sync_threads_typed_frame L i j n k1 k2 v1 v2 t1 t2 ρf
    (Hij : i <> j) (Hin : i <> n) (Hjn : j <> n)
    (Hk1 : ctx k1) (Hk2 : ctx k2)
    (Hend : sync_endpoint_typing L n v1 v2 t1 t2)
    (Hdisj_src : sync_src i j n k1 k2 v1 v2 ##ₘ ρf)
    (Hdisj_tgt : sync_tgt i j k1 k2 v1 v2 ##ₘ ρf) :
  threads_typed L (sync_src i j n k1 k2 v1 v2 ∪ ρf) ->
  threads_typed L (sync_tgt i j k1 k2 v1 v2 ∪ ρf).
Proof.
  intros Hsrc.
  apply (threads_typed_frame L (sync_src i j n k1 k2 v1 v2)
           (sync_tgt i j k1 k2 v1 v2) ρf Hdisj_src Hdisj_tgt Hsrc).
  eapply (sync_local_threads_typed L i j n k1 k2 v1 v2 t1 t2
           Hij Hin Hjn Hk1 Hk2 Hend).
  exact (threads_typed_frame_inv L (sync_src i j n k1 k2 v1 v2) ρf Hsrc).
Qed.

Print Assumptions sync_local_threads_typed.
Print Assumptions sync_threads_typed_frame.

(* ===== ForestSide.v ===== *)
From cgraphs.locks.lambdalock Require Import definitions.
From stdpp Require Import gmap.
From Stdlib Require Import List Arith Lia.
From Stdlib Require Import Strings.String.
Open Scope string_scope.

(* ================================================================== *)
(* Side conditions for the scratch6 pair/forest rewiring lemmas,       *)
(* derived from [kind_live] + [refs_live].                             *)
(*                                                                    *)
(* [PairMove.pair_move_add] needs, for a bundle [B] moved into [i]:    *)
(*     i ∉ B                                                           *)
(*     forall b, b ∈ B -> i ∉ T b                                      *)
(* [ForestMove.forest_rewire_star_at_i] additionally needs [G i n],    *)
(* [i ≠ n], [n ∉ R] and the old-source bundle to be exactly the old    *)
(* out-neighbours of [n].  The two conditions above are the ones that  *)
(* involve references of values and are supplied by kind liveness.     *)
(*                                                                    *)
(* Key fact (KindLiveFacts): under [kind_live], a live thread is never *)
(* referenced by any live object.  Thus whenever the destination of a  *)
(* move is a thread, both pair conditions follow.                      *)
(* ================================================================== *)

(* A live thread does not reference itself. *)
Lemma kind_live_thread_no_self_ref (ρ : cfg) i e
    (Hkind : kind_live ρ) (Hi : ρ !! i = Some (Thread e)) :
  i ∉ refs_at ρ i.
Proof.
  apply (kind_live_no_thread_in_refs_at ρ i e i Hkind Hi).
  rewrite Hi. discriminate.
Qed.

(* The bundle is exactly the out-neighbours of a live old holder [n]
   (Acquire and Wait: the lock content; the pre-state lock's refs are
   precisely [val_refs v]).  If the destination [i] is a live thread,
   both pair conditions hold.  [refs_live] is used to know that every
   node of the bundle is live, so that kind liveness applies to it. *)
Lemma kind_live_bundle_from_object_side
    (ρ : cfg) (i : nat) (e : expr) (n : nat)
    (Hkind : kind_live ρ) (Hrl : refs_live ρ)
    (Hi : ρ !! i = Some (Thread e)) (Hn : ρ !! n <> None) :
  i ∉ refs_at ρ n /\
  (forall b, b ∈ refs_at ρ n -> i ∉ refs_at ρ b).
Proof.
  split.
  - apply (kind_live_no_thread_in_refs_at ρ i e n Hkind Hi Hn).
  - intros b Hb.
    apply (kind_live_no_thread_in_refs_at ρ i e b Hkind Hi).
    destruct (ρ !! n) as [y|] eqn:En; [|done].
    assert (Hb' : b ∈ obj_refs y).
    { unfold refs_at in Hb. rewrite En in Hb. exact Hb. }
    exact (Hrl n y En b Hb').
Qed.

(* The bundle is [val_refs v] for a value [v] occurring in the live
   thread [s] (Sync, and the value argument of Release/NewLock/ForkLock
   when the destination is a fresh or thread object).  If the
   destination [i] is a live thread, both pair conditions hold. *)
Lemma kind_live_bundle_from_thread_side
    (ρ : cfg) (s i : nat) (e : expr) (ed : expr) (v : val)
    (Hkind : kind_live ρ) (Hrl : refs_live ρ)
    (Hs : ρ !! s = Some (Thread e))
    (Hi : ρ !! i = Some (Thread ed))
    (Hsub : forall b, b ∈ val_refs v -> b ∈ expr_refs e) :
  i ∉ val_refs v /\
  (forall b, b ∈ val_refs v -> i ∉ refs_at ρ b).
Proof.
  split.
  - intro Hiv.
    assert (Hin : i ∈ expr_refs e) by (apply Hsub; exact Hiv).
    assert (Hri : i ∈ refs_at ρ s).
    { unfold refs_at. rewrite Hs. exact Hin. }
    assert (Hslive : ρ !! s <> None) by (rewrite Hs; discriminate).
    exact (kind_live_no_thread_in_refs_at ρ i ed s Hkind Hi Hslive Hri).
  - intros b Hb.
    assert (Hin : b ∈ expr_refs e) by (apply Hsub; exact Hb).
    assert (Hb_live : ρ !! b <> None).
    { exact (Hrl s (Thread e) Hs b Hin). }
    exact (kind_live_no_thread_in_refs_at ρ i ed b Hkind Hi Hb_live).
Qed.

(* Fresh destinations (NewLock, Fork, ForkLock) never have incoming
   references: otherwise [refs_live] would make the fresh index live. *)
Lemma fresh_dest_no_backrefs (ρ : cfg) (n : nat)
    (Hrl : refs_live ρ) (Hfresh : ρ !! n = None) :
  (forall b, ρ !! b <> None -> n ∉ refs_at ρ b) /\
  (forall (B : gset nat), (forall b, b ∈ B -> ρ !! b <> None) -> n ∉ B).
Proof.
  split.
  - intros b Hb Hnb.
    destruct (ρ !! b) as [y|] eqn:Eb.
    + assert (Hnref : n ∈ obj_refs y).
      { unfold refs_at in Hnb. rewrite Eb in Hnb. exact Hnb. }
      exact (Hrl b y Eb n Hnref Hfresh).
    + unfold refs_at in Hnb. rewrite Eb in Hnb. done.
  - intros B HB HnB.
    exact (HB n HnB Hfresh).
Qed.

Print Assumptions kind_live_thread_no_self_ref.
Print Assumptions kind_live_bundle_from_object_side.
Print Assumptions kind_live_bundle_from_thread_side.
Print Assumptions fresh_dest_no_backrefs.
Lemma ref_forest_no_triangle_edges (ρ : cfg) a b c
    (Hforest : ref_forest ρ)
    (Hab_ne : a <> b) (Hbc_ne : b <> c) (Hca_ne : c <> a)
    (Hab : ref_edge ρ a b) (Hbc : ref_edge ρ b c) (Hca : ref_edge ρ c a) :
  False.
Proof.
  apply (Hforest [a; b; c]).
  split.
  { simpl. lia. }
  split.
  { repeat constructor; simpl; intuition congruence. }
  change (path_edges (ref_edge ρ) [a; b; c; a]).
  apply (@pe_cons (ref_edge ρ) a b [c; a] Hab).
  apply (@pe_cons (ref_edge ρ) b c [a] Hbc).
  apply (@pe_cons (ref_edge ρ) c a [] Hca).
  apply (@pe_one (ref_edge ρ) a).
Qed.

Lemma release_non_self_backref_conflict
    (ρ : cfg) (i n b : nat) (e : expr) (rc : nat)
    (Hforest : ref_forest ρ)
    (Hi : ρ !! i = Some (Thread e))
    (Hin : n ∈ expr_refs e)
    (Hib : b ∈ expr_refs e)
    (Hbn : n ∈ refs_at ρ b)
    (Hib_ne : i <> b) (Hbn_ne : b <> n) (Hin_ne : i <> n) :
  False.
Proof.
  assert (Hri_n : n ∈ refs_at ρ i).
  { unfold refs_at. rewrite Hi. exact Hin. }
  assert (Hri_b : b ∈ refs_at ρ i).
  { unfold refs_at. rewrite Hi. exact Hib. }
  apply (ref_forest_no_triangle_edges ρ i b n Hforest Hib_ne Hbn_ne
           (fun E => Hin_ne (eq_sym E))).
  - unfold ref_edge. split; [exact Hib_ne|left; exact Hri_b].
  - unfold ref_edge. split; [exact Hbn_ne|left; exact Hbn].
  - unfold ref_edge. split; [exact (fun E => Hin_ne (eq_sym E))|right; exact Hri_n].
Qed.



(* ===== TokenTyping.v ===== *)
Open Scope string_scope.

(* ================================================================== *)
(* Occurrence-complete token contexts.                                *)
(*                                                                    *)
(* A context is a total, finite-support-free multiplicity assignment  *)
(* for lock capabilities and barrier endpoints.  Using total functions *)
(* keeps splitting pointwise and avoids gmap union side conditions.   *)
(* The barrier-endpoint type store [beta] records the oriented pair    *)
(* of endpoint types for each live barrier token.                      *)
(* ================================================================== *)

Instance tt_lockownership_eq_dec : EqDecision lockownership.
Proof. intros x y. unfold Decision. decide equality. Defined.

Instance tt_lockstate_eq_dec : EqDecision lockstate.
Proof. intros x y. unfold Decision. decide equality. Defined.

Record token_ctx := {
  tok_lock : nat -> lockcap -> nat;
  tok_bar  : nat -> nat
}.

Definition tc_zero : token_ctx :=
  {| tok_lock := fun _ _ => 0; tok_bar := fun _ => 0 |}.

Definition tc_add (C1 C2 : token_ctx) : token_ctx :=
  {| tok_lock := fun n lc => tok_lock C1 n lc + tok_lock C2 n lc;
     tok_bar  := fun n => tok_bar C1 n + tok_bar C2 n |}.

Definition tc_lock_one (n : nat) (lc : lockcap) : token_ctx :=
  {| tok_lock := fun n' lc' => if decide (n' = n /\ lc' = lc) then 1 else 0;
     tok_bar  := fun _ => 0 |}.

Definition tc_bar_one (n : nat) : token_ctx :=
  {| tok_lock := fun _ _ => 0;
     tok_bar  := fun n' => if decide (n' = n) then 1 else 0 |}.

Definition lock_count (C : token_ctx) (n : nat) : nat :=
  tok_lock C n (Owner,Opened) +
  tok_lock C n (Owner,Closed) +
  tok_lock C n (Client,Opened) +
  tok_lock C n (Client,Closed).

(* At most one token for an index, counting lock and barrier tokens
   together.  This is the invariant that rules out a Release whose
   payload mentions its own destination lock. *)
Definition index_single (C : token_ctx) : Prop :=
  forall n, lock_count C n + tok_bar C n <= 1.

Definition has_index_token (C : token_ctx) (n : nat) : Prop :=
  (exists lc, 0 < tok_lock C n lc) \/ 0 < tok_bar C n.

Lemma lock_count_nonneg C n lc : 0 <= tok_lock C n lc.
Proof. lia. Qed.

Lemma lock_count_le_sum C n lc :
  tok_lock C n lc <= lock_count C n.
Proof.
  unfold lock_count. destruct lc as [lo st]; destruct lo; destruct st; lia.
Qed.

Lemma tc_add_lock_count C1 C2 n :
  lock_count (tc_add C1 C2) n = lock_count C1 n + lock_count C2 n.
Proof. unfold lock_count, tc_add. simpl. lia. Qed.

Lemma tc_add_bar C1 C2 n :
  tok_bar (tc_add C1 C2) n = tok_bar C1 n + tok_bar C2 n.
Proof. reflexivity. Qed.

Lemma tc_add_lock C1 C2 n lc :
  tok_lock (tc_add C1 C2) n lc = tok_lock C1 n lc + tok_lock C2 n lc.
Proof. reflexivity. Qed.

Lemma tc_add_has_index_l C1 C2 n :
  has_index_token C1 n -> has_index_token (tc_add C1 C2) n.
Proof.
  intros [ [lc H] | H].
  - left. exists lc. rewrite tc_add_lock. lia.
  - right. rewrite tc_add_bar. lia.
Qed.

Lemma tc_add_has_index_r C1 C2 n :
  has_index_token C2 n -> has_index_token (tc_add C1 C2) n.
Proof.
  intros [ [lc H] | H].
  - left. exists lc. rewrite tc_add_lock. lia.
  - right. rewrite tc_add_bar. lia.
Qed.

Lemma tc_lock_one_same n lc :
  tok_lock (tc_lock_one n lc) n lc = 1.
Proof.
  unfold tc_lock_one. simpl.
  destruct (decide (n = n /\ lc = lc)) as [H|H].
  - reflexivity.
  - exfalso. apply H. split; reflexivity.
Qed.

Lemma tc_lock_one_zero n lc n' lc' (H : n' <> n \/ lc' <> lc) :
  tok_lock (tc_lock_one n lc) n' lc' = 0.
Proof.
  unfold tc_lock_one. simpl.
  destruct (decide (n' = n /\ lc' = lc)) as [Hd|Hd].
  - exfalso. destruct H as [Hne|Hne].
    + exact (Hne (proj1 Hd)).
    + exact (Hne (proj2 Hd)).
  - reflexivity.
Qed.

Lemma lock_count_lock_one n lc : lock_count (tc_lock_one n lc) n = 1.
Proof.
  unfold lock_count.
  destruct lc as [lo st]; destruct lo; destruct st.
  - rewrite (tc_lock_one_same n (Owner,Opened)).
    rewrite (tc_lock_one_zero n (Owner,Opened) n (Owner,Closed))
      by (right; discriminate).
    rewrite (tc_lock_one_zero n (Owner,Opened) n (Client,Opened))
      by (right; discriminate).
    rewrite (tc_lock_one_zero n (Owner,Opened) n (Client,Closed))
      by (right; discriminate).
    lia.
  - rewrite (tc_lock_one_same n (Owner,Closed)).
    rewrite (tc_lock_one_zero n (Owner,Closed) n (Owner,Opened))
      by (right; discriminate).
    rewrite (tc_lock_one_zero n (Owner,Closed) n (Client,Opened))
      by (right; discriminate).
    rewrite (tc_lock_one_zero n (Owner,Closed) n (Client,Closed))
      by (right; discriminate).
    lia.
  - rewrite (tc_lock_one_same n (Client,Opened)).
    rewrite (tc_lock_one_zero n (Client,Opened) n (Owner,Opened))
      by (right; discriminate).
    rewrite (tc_lock_one_zero n (Client,Opened) n (Owner,Closed))
      by (right; discriminate).
    rewrite (tc_lock_one_zero n (Client,Opened) n (Client,Closed))
      by (right; discriminate).
    lia.
  - rewrite (tc_lock_one_same n (Client,Closed)).
    rewrite (tc_lock_one_zero n (Client,Closed) n (Owner,Opened))
      by (right; discriminate).
    rewrite (tc_lock_one_zero n (Client,Closed) n (Owner,Closed))
      by (right; discriminate).
    rewrite (tc_lock_one_zero n (Client,Closed) n (Client,Opened))
      by (right; discriminate).
    lia.
Qed.

Lemma tc_lock_one_no_bar n lc m : tok_bar (tc_lock_one n lc) m = 0.
Proof. reflexivity. Qed.

Lemma tc_bar_one_same n : tok_bar (tc_bar_one n) n = 1.
Proof.
  unfold tc_bar_one. simpl.
  destruct (decide (n = n)) as [H|H]; [reflexivity|exfalso; apply H; reflexivity].
Qed.

Lemma tc_bar_one_zero n m (H : m <> n) : tok_bar (tc_bar_one n) m = 0.
Proof.
  unfold tc_bar_one. simpl.
  destruct (decide (m = n)) as [Hd|Hd]; [exfalso; apply H; exact Hd|reflexivity].
Qed.

Lemma tc_bar_one_no_lock n m lc : tok_lock (tc_bar_one n) m lc = 0.
Proof. reflexivity. Qed.

(* Splitting is definitional equality with [tc_add]. *)
Definition tc_split (C C1 C2 : token_ctx) : Prop := C = tc_add C1 C2.

(* ================================================================== *)
(* Token annotation of expressions and values.                        *)
(*                                                                    *)
(* The environment maps variables to the token context of the value   *)
(* that will be substituted for them.  [MatchSum] branches share one  *)
(* branch context: at runtime only one branch is selected, so linear   *)
(* resources are not duplicated across alternatives.  For syntactic  *)
(* safety we take the branch context as an upper bound (the union of  *)
(* all alternatives' tokens).                                         *)
(* ================================================================== *)

Definition tenv := string -> token_ctx.

Definition tenv_zero : tenv := fun _ => tc_zero.

Definition tenv_bind (Delta : tenv) (x : string) : tenv :=
  fun y => if decide (y = x) then tc_zero else Delta y.

Inductive tokE (beta : nat -> option (type * type)) :
    tenv -> expr -> token_ctx -> Prop :=
  | TE_Var Delta x C :
      Delta x = C ->
      tokE beta Delta (Var x) C
  | TE_Val Delta v C :
      tokV beta v C ->
      tokE beta Delta (Val v) C
  | TE_Fun Delta x e C :
      tokE beta (tenv_bind Delta x) e C ->
      tokE beta Delta (Fun x e) C
  | TE_App Delta e1 e2 C1 C2 :
      tokE beta Delta e1 C1 -> tokE beta Delta e2 C2 ->
      tokE beta Delta (App e1 e2) (tc_add C1 C2)
  | TE_Unit Delta :
      tokE beta Delta Unit tc_zero
  | TE_Pair Delta e1 e2 C1 C2 :
      tokE beta Delta e1 C1 -> tokE beta Delta e2 C2 ->
      tokE beta Delta (Pair e1 e2) (tc_add C1 C2)
  | TE_LetPair Delta e1 e2 C1 C2 :
      tokE beta Delta e1 C1 -> tokE beta Delta e2 C2 ->
      tokE beta Delta (LetPair e1 e2) (tc_add C1 C2)
  | TE_Sum Delta n e C :
      tokE beta Delta e C ->
      tokE beta Delta (Sum n e) C
  | TE_MatchSum Delta n e es Cs Cb :
      tokE beta Delta e Cs ->
      (forall i, tokE beta Delta (es i) Cb) ->
      tokE beta Delta (MatchSum n e es) (tc_add Cs Cb)
  | TE_ForkBarrier Delta e C :
      tokE beta Delta e C ->
      tokE beta Delta (ForkBarrier e) C
  | TE_NewLock Delta e C :
      tokE beta Delta e C ->
      tokE beta Delta (NewLock e) C
  | TE_ForkLock Delta e1 e2 C1 C2 :
      tokE beta Delta e1 C1 -> tokE beta Delta e2 C2 ->
      tokE beta Delta (ForkLock e1 e2) (tc_add C1 C2)
  | TE_Acquire Delta e C :
      tokE beta Delta e C ->
      tokE beta Delta (Acquire e) C
  | TE_Release Delta e1 e2 C1 C2 :
      tokE beta Delta e1 C1 -> tokE beta Delta e2 C2 ->
      tokE beta Delta (Release e1 e2) (tc_add C1 C2)
  | TE_Wait Delta e C :
      tokE beta Delta e C ->
      tokE beta Delta (Wait e) C
  | TE_Drop Delta e C :
      tokE beta Delta e C ->
      tokE beta Delta (Drop e) C
with tokV (beta : nat -> option (type * type)) : val -> token_ctx -> Prop :=
  | TV_FunV x e C :
      tokE beta tenv_zero e C ->
      tokV beta (FunV x e) C
  | TV_Unit :
      tokV beta UnitV tc_zero
  | TV_Pair v1 v2 C1 C2 :
      tokV beta v1 C1 -> tokV beta v2 C2 ->
      tokV beta (PairV v1 v2) (tc_add C1 C2)
  | TV_Sum n v C :
      tokV beta v C ->
      tokV beta (SumV n v) C
  | TV_Barrier n t1 t2 :
      beta n = Some (t1, t2) ->
      tokV beta (BarrierV n) (tc_bar_one n)
  | TV_Lock n lc :
      tokV beta (LockV n) (tc_lock_one n lc).

Scheme tokE_mut := Induction for tokE Sort Prop
  with tokV_mut := Induction for tokV Sort Prop.

(* ================================================================== *)
(* Token soundness: every syntactic reference occurrence is covered  *)
(* by a token of the same index.                                      *)
(* ================================================================== *)

Lemma tc_add_has_index_l_rev C1 C2 n :
  has_index_token (tc_add C1 C2) n ->
  has_index_token C1 n \/ has_index_token C2 n.
Proof.
  intros [[lc H]|H].
  - rewrite tc_add_lock in H.
    destruct (Nat.eq_0_gt_0_cases (tok_lock C1 n lc)) as [E|Gt].
    + right. left. exists lc. rewrite E in H. lia.
    + left. left. exists lc. lia.
  - rewrite tc_add_bar in H.
    destruct (Nat.eq_0_gt_0_cases (tok_bar C1 n)) as [E|Gt].
    + right. right. rewrite E in H. lia.
    + left. right. lia.
Qed.

Ltac tok_sound_apply :=
  match goal with
  | IH : (forall m : nat, m ∈ expr_refs _ -> has_index_token _ m)
      |- has_index_token _ _ => eapply IH; eassumption
  | IH : (forall m : nat, m ∈ val_refs _ -> has_index_token _ m)
      |- has_index_token _ _ => eapply IH; eassumption
  end.

Lemma tokE_sound beta Delta e C (H : tokE beta Delta e C) :
  forall n, n ∈ expr_refs e -> has_index_token C n.
Proof.
  induction H using tokE_mut with
    (P0 := fun v C (Hv : tokV beta v C) =>
             forall n, n ∈ val_refs v -> has_index_token C n).
  - (* Var *) intros k Hk. simpl in Hk. set_solver.
  - (* Val *) intros k Hk.
    match goal with
    | IHv : (forall m, m ∈ val_refs _ -> has_index_token _ m) |- _ =>
        exact (IHv k Hk)
    end.
  - (* Fun *) intros k Hk. simpl in Hk. tok_sound_apply.
  - (* App *) intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tok_sound_apply.
    + apply tc_add_has_index_r. tok_sound_apply.
  - (* Unit *) intros k Hk. simpl in Hk. set_solver.
  - (* Pair *) intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tok_sound_apply.
    + apply tc_add_has_index_r. tok_sound_apply.
  - (* LetPair *) intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tok_sound_apply.
    + apply tc_add_has_index_r. tok_sound_apply.
  - (* Sum *) intros k Hk. simpl in Hk. tok_sound_apply.
  - (* MatchSum *) intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tok_sound_apply.
    + apply tc_add_has_index_r.
      apply elem_of_fin_union in Hk. destruct Hk as [i Hi].
      match goal with
      | Hbr : (forall i : fin _, forall m : nat,
                  m ∈ expr_refs _ -> has_index_token _ m) |- _ =>
          exact (Hbr i k Hi)
      end.
  - (* ForkBarrier *) intros k Hk. simpl in Hk. tok_sound_apply.
  - (* NewLock *) intros k Hk. simpl in Hk. tok_sound_apply.
  - (* ForkLock *) intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tok_sound_apply.
    + apply tc_add_has_index_r. tok_sound_apply.
  - (* Acquire *) intros k Hk. simpl in Hk. tok_sound_apply.
  - (* Release *) intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tok_sound_apply.
    + apply tc_add_has_index_r. tok_sound_apply.
  - (* Wait *) intros k Hk. simpl in Hk. tok_sound_apply.
  - (* Drop *) intros k Hk. simpl in Hk. tok_sound_apply.
  - (* FunV *) intros k Hk. simpl in Hk. tok_sound_apply.
  - (* UnitV *) intros k Hk. simpl in Hk. set_solver.
  - (* PairV *) intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tok_sound_apply.
    + apply tc_add_has_index_r. tok_sound_apply.
  - (* SumV *) intros k Hk. simpl in Hk. tok_sound_apply.
  - (* BarrierV *) intros k Hk. simpl in Hk.
    apply elem_of_singleton in Hk. subst k.
    right. rewrite tc_bar_one_same. lia.
  - (* LockV *) intros k Hk. simpl in Hk.
    apply elem_of_singleton in Hk. subst k.
    left. exists lc. rewrite tc_lock_one_same. lia.
Qed.

(* ================================================================== *)
(* Source-initialisation: source terms contain no [Val] nodes, hence  *)
(* their token context is exactly empty.                              *)
(* ================================================================== *)

Inductive val_free : expr -> Prop :=
  | VF_Var x : val_free (Var x)
  | VF_Fun x e : val_free e -> val_free (Fun x e)
  | VF_App e1 e2 : val_free e1 -> val_free e2 -> val_free (App e1 e2)
  | VF_Unit : val_free Unit
  | VF_Pair e1 e2 : val_free e1 -> val_free e2 -> val_free (Pair e1 e2)
  | VF_LetPair e1 e2 : val_free e1 -> val_free e2 -> val_free (LetPair e1 e2)
  | VF_Sum n e : val_free e -> val_free (Sum n e)
  | VF_MatchSum n e es :
      val_free e -> (forall i, val_free (es i)) -> val_free (MatchSum n e es)
  | VF_ForkBarrier e : val_free e -> val_free (ForkBarrier e)
  | VF_NewLock e : val_free e -> val_free (NewLock e)
  | VF_ForkLock e1 e2 : val_free e1 -> val_free e2 -> val_free (ForkLock e1 e2)
  | VF_Acquire e : val_free e -> val_free (Acquire e)
  | VF_Release e1 e2 : val_free e1 -> val_free e2 -> val_free (Release e1 e2)
  | VF_Wait e : val_free e -> val_free (Wait e)
  | VF_Drop e : val_free e -> val_free (Drop e).

Lemma typed_val_free Gamma e t (H : typed Gamma e t) : val_free e.
Proof.
  induction H; try constructor; auto.
Qed.

Definition tenv_zeroish (Delta : tenv) : Prop :=
  forall x, Delta x = tc_zero.

Lemma tenv_bind_zeroish Delta x (H : tenv_zeroish Delta) :
  tenv_zeroish (tenv_bind Delta x).
Proof.
  intro y. unfold tenv_bind, tenv_zeroish in *.
  destruct (decide (y = x)); [reflexivity | apply H].
Qed.

Ltac tok_zero_rec H :=
  match goal with
  | IH : forall D : tenv, tenv_zeroish D -> tokE ?b D _ tc_zero
      |- tokE ?b ?D _ tc_zero => apply IH; exact H
  end.

Lemma tokE_zero_of_val_free beta e (H : val_free e) :
  forall Delta, tenv_zeroish Delta -> tokE beta Delta e tc_zero.
Proof.
  induction H; intros Delta Hzero.
  - apply TE_Var. apply Hzero.
  - apply TE_Fun. apply IHval_free. apply tenv_bind_zeroish. exact Hzero.
  - apply TE_App with (C1 := tc_zero) (C2 := tc_zero); tok_zero_rec Hzero.
  - apply TE_Unit.
  - apply TE_Pair with (C1 := tc_zero) (C2 := tc_zero); tok_zero_rec Hzero.
  - apply TE_LetPair with (C1 := tc_zero) (C2 := tc_zero); tok_zero_rec Hzero.
  - apply TE_Sum. tok_zero_rec Hzero.
  - apply TE_MatchSum with (Cs := tc_zero) (Cb := tc_zero).
    + tok_zero_rec Hzero.
    + intro i.
      match goal with
      | IH : forall i : fin _, forall D : tenv,
                 tenv_zeroish D -> tokE beta D (_ i) tc_zero
          |- tokE beta Delta (_ i) tc_zero =>
          exact (IH i Delta Hzero)
      end.
  - apply TE_ForkBarrier. tok_zero_rec Hzero.
  - apply TE_NewLock. tok_zero_rec Hzero.
  - apply TE_ForkLock with (C1 := tc_zero) (C2 := tc_zero); tok_zero_rec Hzero.
  - apply TE_Acquire. tok_zero_rec Hzero.
  - apply TE_Release with (C1 := tc_zero) (C2 := tc_zero); tok_zero_rec Hzero.
  - apply TE_Wait. tok_zero_rec Hzero.
  - apply TE_Drop. tok_zero_rec Hzero.
Qed.

Definition wtA (L : gmap nat type) (beta : nat -> option (type * type))
    (Gamma : env) (Delta : tenv) (e : expr) (t : type) (C : token_ctx) : Prop :=
  wt L Gamma e t /\ tokE beta Delta e C.

Theorem typed_to_wtA Gamma e t (H : typed Gamma e t)
    (L : gmap nat type) (beta : nat -> option (type * type)) :
  wtA L beta Gamma tenv_zero e t tc_zero.
Proof.
  split.
  - apply typed_to_wt. exact H.
  - apply (tokE_zero_of_val_free beta e (typed_val_free Gamma e t H) tenv_zero).
    intro x. reflexivity.
Qed.

(* ================================================================== *)
(* Release payload safety from token uniqueness.                      *)
(* ================================================================== *)

Lemma index_single_add_left C1 C2 :
  index_single (tc_add C1 C2) -> index_single C1.
Proof.
  intros H n.
  pose proof (H n) as Hle.
  rewrite tc_add_lock_count, tc_add_bar in Hle.
  unfold lock_count in *. lia.
Qed.

Lemma index_single_add_right C1 C2 :
  index_single (tc_add C1 C2) -> index_single C2.
Proof.
  intros H n.
  pose proof (H n) as Hle.
  rewrite tc_add_lock_count, tc_add_bar in Hle.
  unfold lock_count in *. lia.
Qed.

Lemma index_single_split_lock_zero C1 C2 n lc
    (Hsingle : index_single (tc_add C1 C2))
    (Hpos : 0 < tok_lock C1 n lc) :
  (forall lc', tok_lock C2 n lc' = 0) /\ tok_bar C2 n = 0.
Proof.
  assert (Hsum : lock_count (tc_add C1 C2) n + tok_bar (tc_add C1 C2) n
                 = (lock_count C1 n + tok_bar C1 n)
                   + (lock_count C2 n + tok_bar C2 n)).
  { rewrite tc_add_lock_count, tc_add_bar. lia. }
  assert (Hle : lock_count (tc_add C1 C2) n + tok_bar (tc_add C1 C2) n <= 1)
    by apply Hsingle.
  assert (H1le : lock_count C1 n + tok_bar C1 n <= 1).
  { rewrite Hsum in Hle. lia. }
  assert (Hc1pos : 1 <= lock_count C1 n).
  { pose proof (lock_count_le_sum C1 n lc). lia. }
  rewrite Hsum in Hle.
  assert (Hc2 : lock_count C2 n = 0) by lia.
  assert (Hb2 : tok_bar C2 n = 0) by lia.
  split; [|exact Hb2].
  intro lc'. pose proof (lock_count_le_sum C2 n lc'). lia.
Qed.

Lemma tokE_var_inv beta Delta x C
    (H : tokE beta Delta (Var x) C) :
  Delta x = C.
Proof. inversion H; subst; reflexivity. Qed.

Lemma tokE_val_inv beta Delta v C
    (H : tokE beta Delta (Val v) C) :
  tokV beta v C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokE_release_inv beta Delta e1 e2 C
    (H : tokE beta Delta (Release e1 e2) C) :
  exists C1 C2, C = tc_add C1 C2 /\
    tokE beta Delta e1 C1 /\ tokE beta Delta e2 C2.
Proof. inversion H; subst; eauto. Qed.

Lemma tokV_lock_inv beta n C
    (H : tokV beta (LockV n) C) :
  exists lc, C = tc_lock_one n lc.
Proof. inversion H; subst; eauto. Qed.

Lemma tokV_barrier_inv beta n C
    (H : tokV beta (BarrierV n) C) :
  exists t1 t2, beta n = Some (t1, t2) /\ C = tc_bar_one n.
Proof. inversion H; subst; eauto. Qed.

Theorem release_payload_token_free beta Delta n v C1 C2
    (Htok : tokE beta Delta (Release (Val (LockV n)) (Val v)) (tc_add C1 C2))
    (Hsingle : index_single (tc_add C1 C2)) :
  n ∉ val_refs v.
Proof.
  destruct (tokE_release_inv beta Delta (Val (LockV n)) (Val v)
              (tc_add C1 C2) Htok) as (C1' & C2' & HC & H1 & H2).
  pose proof (tokE_val_inv beta Delta (LockV n) C1' H1) as Hv1.
  destruct (tokV_lock_inv beta n C1' Hv1) as (lc & HC1).
  subst C1'.
  assert (Hsingle' : index_single (tc_add (tc_lock_one n lc) C2')).
  { rewrite <- HC. exact Hsingle. }
  assert (Hlock : 0 < tok_lock (tc_lock_one n lc) n lc).
  { rewrite tc_lock_one_same. lia. }
  destruct (index_single_split_lock_zero (tc_lock_one n lc) C2' n lc
              Hsingle' Hlock)
    as [Hzero Hbar].
  intro Hn.
  pose proof (tokE_sound beta Delta (Val v) C2' H2 n) as Hs.
  simpl in Hs. specialize (Hs Hn).
  destruct Hs as [[lc' Hlc']|Hb].
  - rewrite Hzero in Hlc'. lia.
  - rewrite Hbar in Hb. lia.
Qed.

(* ================================================================== *)
(* Annotated runtime typing [wtK]/[cvK]: the store [L] and the plain  *)
(* runtime types are retained, while the token context [C] records    *)
(* every occurrence of a lock capability or barrier endpoint token.   *)
(* Threads are closed, so the token environment is [tenv_zero].       *)
(* ================================================================== *)

Definition wtK (L : gmap nat type) (beta : nat -> option (type * type))
    (Gamma : env) (e : expr) (t : type) (C : token_ctx) : Prop :=
  wt L Gamma e t /\ tokE beta tenv_zero e C.

Definition cvK (L : gmap nat type) (beta : nat -> option (type * type))
    (v : val) (t : type) (C : token_ctx) : Prop :=
  cv L v t /\ tokV beta v C.

Theorem typed_to_wtK Gamma e t (H : typed Gamma e t)
    (L : gmap nat type) (beta : nat -> option (type * type)) :
  wtK L beta Gamma e t tc_zero.
Proof.
  split.
  - apply typed_to_wt. exact H.
  - apply (tokE_zero_of_val_free beta e (typed_val_free Gamma e t H) tenv_zero).
    intro x. reflexivity.
Qed.

Lemma wtK_token_sound L beta Gamma e t C
    (H : wtK L beta Gamma e t C) :
  forall n, n ∈ expr_refs e -> has_index_token C n.
Proof.
  destruct H as [Hwt Htok].
  intros n Hn. exact (tokE_sound beta tenv_zero e C Htok n Hn).
Qed.

Lemma cvK_lock_token L beta n t C (H : cvK L beta (LockV n) t C) :
  exists lc, C = tc_lock_one n lc.
Proof.
  destruct H as [Hcv Htok].
  exact (tokV_lock_inv beta n C Htok).
Qed.

(* Release payload safety stated at the annotated-typing level.  The
   hypothesis [index_single] on the two token contexts of the linear
   split is what prevents the payload from mentioning its own lock. *)
Theorem wtK_release_payload_token_free L beta Gamma n v C1 C2 t lo
    (H : wtK L beta Gamma (Release (Val (LockV n)) (Val v))
           (LockT (lo, Closed) t) (tc_add C1 C2))
    (Hsingle : index_single (tc_add C1 C2)) :
  n ∉ val_refs v.
Proof.
  destruct H as [Hwt Htok].
  exact (release_payload_token_free beta tenv_zero n v C1 C2 Htok Hsingle).
Qed.

Print Assumptions typed_to_wtA.
Print Assumptions typed_to_wtK.
Print Assumptions wtK_token_sound.
Print Assumptions wtK_release_payload_token_free.
Print Assumptions index_single_add_left.
Print Assumptions index_single_add_right.
Print Assumptions release_payload_token_free.

(* ===== TokenCtx.v ===== *)
Open Scope string_scope.

(* ================================================================== *)
(* Token sub-contexts.                                                *)
(*                                                                    *)
(* [tc_le C D] says that [C] has no more lock or barrier tokens than  *)
(* [D] at every index.  It is the order used to state that the token  *)
(* context of a subexpression is contained in the token context of an *)
(* enclosing evaluation context.  No record extensionality (and hence *)
(* no functional extensionality) is needed.                            *)
(* ================================================================== *)

Definition tc_le (C D : token_ctx) : Prop :=
  (forall n lc, tok_lock C n lc <= tok_lock D n lc) /\
  (forall n, tok_bar C n <= tok_bar D n).

Lemma tc_le_refl C : tc_le C C.
Proof. split; intros; lia. Qed.

Lemma tc_le_trans C1 C2 C3 :
  tc_le C1 C2 -> tc_le C2 C3 -> tc_le C1 C3.
Proof.
  intros [Hl1 Hb1] [Hl2 Hb2]. split.
  - intros n lc. pose proof (Hl1 n lc). pose proof (Hl2 n lc). lia.
  - intros n. pose proof (Hb1 n). pose proof (Hb2 n). lia.
Qed.

Lemma tc_le_add_l C1 C2 : tc_le C1 (tc_add C1 C2).
Proof.
  split.
  - intros n lc. rewrite tc_add_lock. lia.
  - intros n. rewrite tc_add_bar. lia.
Qed.

Lemma tc_le_add_r C1 C2 : tc_le C2 (tc_add C1 C2).
Proof.
  split.
  - intros n lc. rewrite tc_add_lock. lia.
  - intros n. rewrite tc_add_bar. lia.
Qed.

Lemma index_single_mono C D
    (Hle : tc_le C D) (Hsingle : index_single D) :
  index_single C.
Proof.
  destruct Hle as [Hlock Hbar].
  intro n.
  pose proof (Hlock n (Owner, Opened)) as H1.
  pose proof (Hlock n (Owner, Closed)) as H2.
  pose proof (Hlock n (Client, Opened)) as H3.
  pose proof (Hlock n (Client, Closed)) as H4.
  pose proof (Hbar n) as H5.
  pose proof (Hsingle n) as H6.
  unfold lock_count in *. lia.
Qed.

(* ================================================================== *)
(* Inversion of one token-typing constructor.  These are the local    *)
(* facts needed to move from a context [k e] to its hole [e].         *)
(* ================================================================== *)

Lemma tokE_app_inv beta Delta e1 e2 C
    (H : tokE beta Delta (App e1 e2) C) :
  exists C1 C2, C = tc_add C1 C2 /\
    tokE beta Delta e1 C1 /\ tokE beta Delta e2 C2.
Proof. inversion H; subst; eauto. Qed.

Lemma tokE_pair_inv beta Delta e1 e2 C
    (H : tokE beta Delta (Pair e1 e2) C) :
  exists C1 C2, C = tc_add C1 C2 /\
    tokE beta Delta e1 C1 /\ tokE beta Delta e2 C2.
Proof. inversion H; subst; eauto. Qed.

Lemma tokE_letpair_inv beta Delta e1 e2 C
    (H : tokE beta Delta (LetPair e1 e2) C) :
  exists C1 C2, C = tc_add C1 C2 /\
    tokE beta Delta e1 C1 /\ tokE beta Delta e2 C2.
Proof. inversion H; subst; eauto. Qed.

Lemma tokE_forklock_inv beta Delta e1 e2 C
    (H : tokE beta Delta (ForkLock e1 e2) C) :
  exists C1 C2, C = tc_add C1 C2 /\
    tokE beta Delta e1 C1 /\ tokE beta Delta e2 C2.
Proof. inversion H; subst; eauto. Qed.

Lemma tokE_sum_inv beta Delta i e C
    (H : tokE beta Delta (Sum i e) C) :
  tokE beta Delta e C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokE_forkbarrier_inv beta Delta e C
    (H : tokE beta Delta (ForkBarrier e) C) :
  tokE beta Delta e C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokE_newlock_inv beta Delta e C
    (H : tokE beta Delta (NewLock e) C) :
  tokE beta Delta e C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokE_acquire_inv beta Delta e C
    (H : tokE beta Delta (Acquire e) C) :
  tokE beta Delta e C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokE_wait_inv beta Delta e C
    (H : tokE beta Delta (Wait e) C) :
  tokE beta Delta e C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokE_drop_inv beta Delta e C
    (H : tokE beta Delta (Drop e) C) :
  tokE beta Delta e C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokE_matchsum_inv beta Delta n e es C
    (H : tokE beta Delta (MatchSum n e es) C) :
  exists Cs Cb, C = tc_add Cs Cb /\
    tokE beta Delta e Cs /\ (forall i, tokE beta Delta (es i) Cb).
Proof.
  inversion H as [ |  |  |  |  |  |  |  | Delta0 n0 e0 es0 Cs0 Cb0 H1 H2 |  |  |  |  |  |  |  ]; subst.
  apply (inj_pair2_eq_dec nat Nat.eq_dec) in H5. subst es0.
  eexists; eexists; split.
  - reflexivity.
  - split; [exact H1 | exact H2].
Qed.

(* ================================================================== *)
(* One evaluation-context frame.                                      *)
(* ================================================================== *)

Lemma tokE_ctx1_sub beta Delta k (Hk : ctx1 k) e C
    (H : tokE beta Delta (k e) C) :
  exists Ce, tokE beta Delta e Ce /\ tc_le Ce C.
Proof.
  revert e C H.
  induction Hk; intros ee C H; simpl in H.
  - (* App left *) destruct (tokE_app_inv beta Delta ee e C H) as
      (C1 & C2 & E & H1 & H2). subst C.
    exists C1. split; [exact H1 | apply tc_le_add_l].
  - (* App right *) destruct (tokE_app_inv beta Delta e ee C H) as
      (C1 & C2 & E & H1 & H2). subst C.
    exists C2. split; [exact H2 | apply tc_le_add_r].
  - (* Pair left *) destruct (tokE_pair_inv beta Delta ee e C H) as
      (C1 & C2 & E & H1 & H2). subst C.
    exists C1. split; [exact H1 | apply tc_le_add_l].
  - (* Pair right *) destruct (tokE_pair_inv beta Delta e ee C H) as
      (C1 & C2 & E & H1 & H2). subst C.
    exists C2. split; [exact H2 | apply tc_le_add_r].
  - (* LetPair *) destruct (tokE_letpair_inv beta Delta ee e C H) as
      (C1 & C2 & E & H1 & H2). subst C.
    exists C1. split; [exact H1 | apply tc_le_add_l].
  - (* Sum *) exists C. split.
    + apply (tokE_sum_inv beta Delta i ee C H).
    + apply tc_le_refl.
  - (* MatchSum scrutinee *) destruct
      (tokE_matchsum_inv beta Delta n ee es C H) as
      (Cs & Cb & E & H1 & H2). subst C.
    exists Cs. split; [exact H1 | apply tc_le_add_l].
  - (* ForkBarrier *) exists C. split.
    + apply (tokE_forkbarrier_inv beta Delta ee C H).
    + apply tc_le_refl.
  - (* NewLock *) exists C. split.
    + apply (tokE_newlock_inv beta Delta ee C H).
    + apply tc_le_refl.
  - (* ForkLock left *) destruct (tokE_forklock_inv beta Delta ee e C H) as
      (C1 & C2 & E & H1 & H2). subst C.
    exists C1. split; [exact H1 | apply tc_le_add_l].
  - (* ForkLock right *) destruct (tokE_forklock_inv beta Delta e ee C H) as
      (C1 & C2 & E & H1 & H2). subst C.
    exists C2. split; [exact H2 | apply tc_le_add_r].
  - (* Acquire *) exists C. split.
    + apply (tokE_acquire_inv beta Delta ee C H).
    + apply tc_le_refl.
  - (* Release left *) destruct (tokE_release_inv beta Delta ee e C H) as
      (C1 & C2 & E & H1 & H2). subst C.
    exists C1. split; [exact H1 | apply tc_le_add_l].
  - (* Release right *) destruct (tokE_release_inv beta Delta e ee C H) as
      (C1 & C2 & E & H1 & H2). subst C.
    exists C2. split; [exact H2 | apply tc_le_add_r].
  - (* Wait *) exists C. split.
    + apply (tokE_wait_inv beta Delta ee C H).
    + apply tc_le_refl.
  - (* Drop *) exists C. split.
    + apply (tokE_drop_inv beta Delta ee C H).
    + apply tc_le_refl.
Qed.

(* ================================================================== *)
(* An arbitrary evaluation context is a composition of frames.        *)
(* ================================================================== *)

Lemma tokE_ctx_sub beta Delta k (Hk : ctx k) e C
    (H : tokE beta Delta (k e) C) :
  exists Ce, tokE beta Delta e Ce /\ tc_le Ce C.
Proof.
  revert e C H.
  induction Hk as [| k1 k2 Hk1 Hk2 IH].
  - (* identity *) intros e C H. simpl in H.
    exists C. split; [exact H | apply tc_le_refl].
  - (* composition *) intros e C H. simpl in H.
    destruct (tokE_ctx1_sub beta Delta k1 Hk1 (k2 e) C H) as
      (CE & HE & HleE).
    destruct (IH e CE HE) as (Ce & He & Hle).
    exists Ce. split; [exact He | eapply tc_le_trans; eauto].
Qed.

Lemma tokE_ctx_index_single beta Delta k (Hk : ctx k) e C
    (H : tokE beta Delta (k e) C) (Hsingle : index_single C) :
  exists Ce, tokE beta Delta e Ce /\ index_single Ce.
Proof.
  destruct (tokE_ctx_sub beta Delta k Hk e C H) as (Ce & He & Hle).
  exists Ce. split; [exact He | apply (index_single_mono Ce C Hle Hsingle)].
Qed.

(* ================================================================== *)
(* Release payload safety for a Release subterm of a token-typed      *)
(* thread expression.  This is the form needed by the Release local   *)
(* step, whose evaluation context is known to be a [ctx].             *)
(* ================================================================== *)

Theorem release_payload_token_free_ctx beta Delta k n v C
    (Hk : ctx k)
    (H : tokE beta Delta (k (Release (Val (LockV n)) (Val v))) C)
    (Hsingle : index_single C) :
  n ∉ val_refs v.
Proof.
  destruct (tokE_ctx_index_single beta Delta k Hk
              (Release (Val (LockV n)) (Val v)) C H Hsingle)
    as (Ce & He & Hsingle_e).
  destruct (tokE_release_inv beta Delta (Val (LockV n)) (Val v) Ce He)
    as (C1 & C2 & E & H1 & H2).
  apply (release_payload_token_free beta Delta n v C1 C2).
  - rewrite E in He. exact He.
  - rewrite E in Hsingle_e. exact Hsingle_e.
Qed.

(* Same statement packaged as a property of one thread, with the
   thread's own token context made explicit. *)

Definition thread_token_single beta (e : expr) : Prop :=
  exists C, tokE beta tenv_zero e C /\ index_single C.

Lemma release_payload_safe_of_thread_token_single beta k n v
    (Hk : ctx k)
    (H : thread_token_single beta (k (Release (Val (LockV n)) (Val v)))) :
  n ∉ val_refs v.
Proof.
  destruct H as (C & Htok & Hsingle).
  exact (release_payload_token_free_ctx beta tenv_zero k n v C Hk Htok Hsingle).
Qed.

Print Assumptions tokE_ctx1_sub.
Print Assumptions tokE_ctx_sub.
Print Assumptions tokE_ctx_index_single.
Print Assumptions release_payload_token_free_ctx.
Print Assumptions release_payload_safe_of_thread_token_single.

(* ===== TokenSub.v ===== *)
Open Scope string_scope.

Lemma tokE_fun_inv beta Delta x e C
    (H : tokE beta Delta (Fun x e) C) :
  tokE beta (tenv_bind Delta x) e C.
Proof. inversion H; subst; assumption. Qed.

(* If [x] has no syntactic occurrence at all, substitution is
   token-context preserving.  Values are not traversed by [subst], so
   the [Val] case is immediate even when the value contains a closure
   whose body mentions [x]. *)

Lemma tokE_subst_unused beta Delta x a e C
    (H : tokE beta Delta e C) (Hocc : var_occ x e = 0) :
  tokE beta Delta (subst x a e) C.
Proof.
  revert Delta C H.
  induction e as
    [ v | y | y e IH | e1 IH1 e2 IH2 | | e1 IH1 e2 IH2
    | e1 IH1 e2 IH2 | n e IH | n e IH es IHes | e IH | e IH
    | e1 IH1 e2 IH2 | e IH | e1 IH1 e2 IH2 | e IH | e IH ];
    intros Delta C H; simpl in Hocc; simpl.
  - (* Val *) exact H.
  - (* Var *) destruct (decide (x = y)) as [E|E]; [simpl in Hocc; discriminate|exact H].
  - (* Fun *) destruct (decide (x = y)) as [E|E].
    + exact H.
    + apply TE_Fun.
      apply (IH Hocc (tenv_bind Delta y) C (tokE_fun_inv beta Delta y e C H)).
  - (* App *)
    assert (Ho1 : var_occ x e1 = 0) by lia.
    assert (Ho2 : var_occ x e2 = 0) by lia.
    destruct (tokE_app_inv beta Delta e1 e2 C H) as (C1 & C2 & E & H1 & H2).
    subst C. apply TE_App with (C1 := C1) (C2 := C2).
    + apply (IH1 Ho1 Delta C1 H1).
    + apply (IH2 Ho2 Delta C2 H2).
  - (* Unit *) exact H.
  - (* Pair *)
    assert (Ho1 : var_occ x e1 = 0) by lia.
    assert (Ho2 : var_occ x e2 = 0) by lia.
    destruct (tokE_pair_inv beta Delta e1 e2 C H) as (C1 & C2 & E & H1 & H2).
    subst C. apply TE_Pair with (C1 := C1) (C2 := C2).
    + apply (IH1 Ho1 Delta C1 H1).
    + apply (IH2 Ho2 Delta C2 H2).
  - (* LetPair *)
    assert (Ho1 : var_occ x e1 = 0) by lia.
    assert (Ho2 : var_occ x e2 = 0) by lia.
    destruct (tokE_letpair_inv beta Delta e1 e2 C H) as (C1 & C2 & E & H1 & H2).
    subst C. apply TE_LetPair with (C1 := C1) (C2 := C2).
    + apply (IH1 Ho1 Delta C1 H1).
    + apply (IH2 Ho2 Delta C2 H2).
  - (* Sum *) apply TE_Sum. apply (IH Hocc Delta C (tokE_sum_inv beta Delta n e C H)).
  - (* MatchSum *)
    assert (Hob : var_occ x e = 0) by lia.
    assert (Hsum : fin_sum (fun i => var_occ x (es i)) = 0) by lia.
    assert (Hoe : forall i, var_occ x (es i) = 0)
      by (intro i; apply (proj1 (fin_sum_eq_zero (fun i => var_occ x (es i))) Hsum)).
    destruct (tokE_matchsum_inv beta Delta n e es C H) as
      (Cs & Cb & E & H1 & H2).
    subst C. apply TE_MatchSum with (Cs := Cs) (Cb := Cb).
    + apply (IH Hob Delta Cs H1).
    + intro i. apply (IHes i (Hoe i) Delta Cb (H2 i)).
  - (* ForkBarrier *) apply TE_ForkBarrier.
    apply (IH Hocc Delta C (tokE_forkbarrier_inv beta Delta e C H)).
  - (* NewLock *) apply TE_NewLock.
    apply (IH Hocc Delta C (tokE_newlock_inv beta Delta e C H)).
  - (* ForkLock *)
    assert (Ho1 : var_occ x e1 = 0) by lia.
    assert (Ho2 : var_occ x e2 = 0) by lia.
    destruct (tokE_forklock_inv beta Delta e1 e2 C H) as (C1 & C2 & E & H1 & H2).
    subst C. apply TE_ForkLock with (C1 := C1) (C2 := C2).
    + apply (IH1 Ho1 Delta C1 H1).
    + apply (IH2 Ho2 Delta C2 H2).
  - (* Acquire *) apply TE_Acquire.
    apply (IH Hocc Delta C (tokE_acquire_inv beta Delta e C H)).
  - (* Release *)
    assert (Ho1 : var_occ x e1 = 0) by lia.
    assert (Ho2 : var_occ x e2 = 0) by lia.
    destruct (tokE_release_inv beta Delta e1 e2 C H) as (C1 & C2 & E & H1 & H2).
    subst C. apply TE_Release with (C1 := C1) (C2 := C2).
    + apply (IH1 Ho1 Delta C1 H1).
    + apply (IH2 Ho2 Delta C2 H2).
  - (* Wait *) apply TE_Wait.
    apply (IH Hocc Delta C (tokE_wait_inv beta Delta e C H)).
  - (* Drop *) apply TE_Drop.
    apply (IH Hocc Delta C (tokE_drop_inv beta Delta e C H)).
Qed.

(* ================================================================== *)
(* Exact obstruction to the naive substitution plan.                  *)
(*                                                                    *)
(* [tokV] is not occurrence-complete: when [MatchSum 0] has no        *)
(* alternatives, [TE_MatchSum] still permits an arbitrary branch      *)
(* context, so a value with no references at all can carry a lock     *)
(* token.  Consequently [val_refs v = ∅ -> C = tc_zero] is false for  *)
(* [tokV], and the proposed replacement [C - Cx + Ca] cannot be       *)
(* derived from reference-freeness of the argument.                   *)
(* ================================================================== *)

Definition gap_beta : nat -> option (type * type) := fun _ => None.

Definition gap_val : val :=
  FunV "zz" (MatchSum 0 Unit (fun _ : fin 0 => Unit)).

Lemma gap_tokV :
  tokV gap_beta gap_val
    (tc_add tc_zero (tc_lock_one 3 (Owner, Opened))).
Proof.
  unfold gap_val. apply TV_FunV.
  apply TE_MatchSum with (Cs := tc_zero) (Cb := tc_lock_one 3 (Owner, Opened)).
  - apply TE_Unit.
  - intro i. inversion i.
Qed.

Lemma gap_val_refs_empty : val_refs gap_val = ∅.
Proof.
  unfold gap_val. simpl. set_solver.
Qed.

Lemma gap_token :
  0 < tok_lock (tc_add tc_zero (tc_lock_one 3 (Owner, Opened)))
              3 (Owner, Opened).
Proof.
  rewrite tc_add_lock.
  rewrite tc_lock_one_same.
  unfold tc_zero. simpl. lia.
Qed.

Theorem tokV_token_occurrence_incomplete :
  exists (v : val) C n,
    tokV gap_beta v C /\ n ∉ val_refs v /\
    (exists lc, 0 < tok_lock C n lc).
Proof.
  exists gap_val, (tc_add tc_zero (tc_lock_one 3 (Owner, Opened))), 3.
  split; [exact gap_tokV|].
  split.
  - rewrite gap_val_refs_empty. set_solver.
  - exists (Owner, Opened). exact gap_token.
Qed.

(* ================================================================== *)
(* Token-context subtraction.                                         *)
(*                                                                    *)
(* [tc_sub C Cx] removes one copy of the tokens of [Cx] from [C].     *)
(* Natural-number subtraction is truncated, so the cancellation        *)
(* lemmas below carry the pointwise order [tc_le Cx C].  We state      *)
(* the results pointwise to avoid needing record extensionality.       *)
(* ================================================================== *)

Definition tc_sub (C Cx : token_ctx) : token_ctx :=
  {| tok_lock := fun n lc => tok_lock C n lc - tok_lock Cx n lc;
     tok_bar  := fun n => tok_bar C n - tok_bar Cx n |}.

Definition tc_eqv (C D : token_ctx) : Prop :=
  (forall n lc, tok_lock C n lc = tok_lock D n lc) /\
  (forall n, tok_bar C n = tok_bar D n).

Lemma tc_eqv_refl C : tc_eqv C C.
Proof. split; reflexivity. Qed.

Lemma tc_eqv_sym C D : tc_eqv C D -> tc_eqv D C.
Proof.
  intros [Hl Hb]. split; [intro n; intro lc; symmetry; apply Hl |
                    intro n; symmetry; apply Hb].
Qed.

Lemma tc_eqv_trans C1 C2 C3 :
  tc_eqv C1 C2 -> tc_eqv C2 C3 -> tc_eqv C1 C3.
Proof.
  intros [Hl1 Hb1] [Hl2 Hb2]. split.
  - intros n lc. transitivity (tok_lock C2 n lc); auto.
  - intro n. transitivity (tok_bar C2 n); auto.
Qed.

Lemma tc_eqv_le_l C1 C2 D :
  tc_eqv C1 C2 -> tc_le C1 D -> tc_le C2 D.
Proof.
  intros [Hl Hb] [Hll Hbb]. split.
  - intros n lc. rewrite <- (Hl n lc). apply Hll.
  - intro n. rewrite <- (Hb n). apply Hbb.
Qed.

Lemma tc_eqv_le_r C D1 D2 :
  tc_eqv D1 D2 -> tc_le C D1 -> tc_le C D2.
Proof.
  intros [Hl Hb] [Hll Hbb]. split.
  - intros n lc. rewrite <- (Hl n lc). apply Hll.
  - intro n. rewrite <- (Hb n). apply Hbb.
Qed.

Lemma tc_eqv_index_single_l C1 C2 :
  tc_eqv C1 C2 -> index_single C1 -> index_single C2.
Proof.
  intros [Hl Hb] H n.
  pose proof (H n) as Hle.
  unfold lock_count, index_single in *.
  rewrite <- (Hl n (Owner, Opened)).
  rewrite <- (Hl n (Owner, Closed)).
  rewrite <- (Hl n (Client, Opened)).
  rewrite <- (Hl n (Client, Closed)).
  rewrite <- (Hb n).
  exact Hle.
Qed.

Lemma tc_eqv_index_single_r C1 C2 :
  tc_eqv C1 C2 -> index_single C2 -> index_single C1.
Proof.
  intros E H2. apply (tc_eqv_index_single_l C2 C1).
  - apply tc_eqv_sym. exact E.
  - exact H2.
Qed.

Lemma tc_sub_le C Cx : tc_le (tc_sub C Cx) C.
Proof.
  split.
  - intros n lc. unfold tc_sub. simpl. lia.
  - intros n. unfold tc_sub. simpl. lia.
Qed.

Lemma index_single_sub C Cx :
  index_single C -> index_single (tc_sub C Cx).
Proof. apply (index_single_mono (tc_sub C Cx) C); apply tc_sub_le. Qed.

(* Pointwise cancellation: if [Cx] is contained in [C], adding it back
   to the difference recovers [C]. *)
Lemma tc_sub_add_cancel C Cx (Hle : tc_le Cx C) :
  tc_eqv C (tc_add (tc_sub C Cx) Cx).
Proof.
  destruct Hle as [Hlock Hbar]. split.
  - intros n lc.
    unfold tc_add, tc_sub. simpl.
    pose proof (Hlock n lc). lia.
  - intro n.
    unfold tc_add, tc_sub. simpl.
    pose proof (Hbar n). lia.
Qed.

(* [tc_disjoint C D] says that at every index, [C] and [D] together
   contain at most one capability or barrier token. *)
Definition tc_disjoint (C D : token_ctx) : Prop :=
  forall n,
    (lock_count C n + tok_bar C n)
    + (lock_count D n + tok_bar D n) <= 1.

Lemma tc_disjoint_sym C D : tc_disjoint C D -> tc_disjoint D C.
Proof. intros H n. pose proof (H n). unfold lock_count in *. lia. Qed.

Lemma index_single_add_of_disjoint C D
    (HsingleC : index_single C) (HsingleD : index_single D)
    (Hdisj : tc_disjoint C D) :
  index_single (tc_add C D).
Proof.
  intro n.
  pose proof (HsingleC n) as Hc.
  pose proof (HsingleD n) as Hd.
  pose proof (Hdisj n) as Hj.
  rewrite tc_add_lock_count, tc_add_bar.
  unfold lock_count in *. lia.
Qed.

Lemma index_single_replace C Cx Ca
    (HsingleC : index_single C)
    (Hdisj : tc_disjoint (tc_sub C Cx) Ca) :
  index_single (tc_add (tc_sub C Cx) Ca).
Proof.
  apply index_single_add_of_disjoint.
  - apply (index_single_sub C Cx HsingleC).
  - (* [tc_disjoint] already bounds both contexts by one at each index. *)
    assert (Hsub : index_single (tc_sub C Cx))
      by apply (index_single_sub C Cx HsingleC).
    intro n.
    pose proof (Hdisj n) as Hj.
    pose proof (Hsub n) as Hl.
    unfold lock_count in *. lia.
  - exact Hdisj.
Qed.

(* If the replacement context is empty, the target context is just the
   difference. *)
Lemma index_single_sub_of_replace C Cx Ca
    (H : index_single (tc_add (tc_sub C Cx) Ca)) :
  index_single (tc_sub C Cx).
Proof. apply (index_single_add_left (tc_sub C Cx) Ca H). Qed.

Print Assumptions tokV_token_occurrence_incomplete.
Print Assumptions tokE_subst_unused.
Print Assumptions index_single_sub.
Print Assumptions tc_sub_add_cancel.
Print Assumptions index_single_add_of_disjoint.
Print Assumptions index_single_replace.
Print Assumptions index_single_sub_of_replace.

(* ===== TokenLinear.v ===== *)
Open Scope string_scope.

(* ================================================================== *)
(* A redesigned token grammar.                                        *)
(*                                                                    *)
(* The original [TE_MatchSum] rule gave every alternative the same     *)
(* branch context [Cb].  In particular, [MatchSum 0] could carry an    *)
(* arbitrary token even though it has no branch at all.  We now use a  *)
(* per-alternative context plus a common upper bound, and force the    *)
(* upper bound to be empty when there are no alternatives.             *)
(* ================================================================== *)

Inductive tokEL (beta : nat -> option (type * type)) :
    tenv -> expr -> token_ctx -> Prop :=
  | TLE_Var Delta x C :
      Delta x = C ->
      tokEL beta Delta (Var x) C
  | TLE_Val Delta v C :
      tokVL beta v C ->
      tokEL beta Delta (Val v) C
  | TLE_Fun Delta x e C :
      tokEL beta (tenv_bind Delta x) e C ->
      tokEL beta Delta (Fun x e) C
  | TLE_App Delta e1 e2 C1 C2 :
      tokEL beta Delta e1 C1 -> tokEL beta Delta e2 C2 ->
      tokEL beta Delta (App e1 e2) (tc_add C1 C2)
  | TLE_Unit Delta :
      tokEL beta Delta Unit tc_zero
  | TLE_Pair Delta e1 e2 C1 C2 :
      tokEL beta Delta e1 C1 -> tokEL beta Delta e2 C2 ->
      tokEL beta Delta (Pair e1 e2) (tc_add C1 C2)
  | TLE_LetPair Delta e1 e2 C1 C2 :
      tokEL beta Delta e1 C1 -> tokEL beta Delta e2 C2 ->
      tokEL beta Delta (LetPair e1 e2) (tc_add C1 C2)
  | TLE_Sum Delta n e C :
      tokEL beta Delta e C ->
      tokEL beta Delta (Sum n e) C
  | TLE_MatchSum Delta n e es Cs Cb Cbs :
      tokEL beta Delta e Cs ->
      (forall i, tokEL beta Delta (es i) (Cbs i)) ->
      (forall i, tc_le (Cbs i) Cb) ->
      (n = 0 -> Cb = tc_zero) ->
      tokEL beta Delta (MatchSum n e es) (tc_add Cs Cb)
  | TLE_ForkBarrier Delta e C :
      tokEL beta Delta e C ->
      tokEL beta Delta (ForkBarrier e) C
  | TLE_NewLock Delta e C :
      tokEL beta Delta e C ->
      tokEL beta Delta (NewLock e) C
  | TLE_ForkLock Delta e1 e2 C1 C2 :
      tokEL beta Delta e1 C1 -> tokEL beta Delta e2 C2 ->
      tokEL beta Delta (ForkLock e1 e2) (tc_add C1 C2)
  | TLE_Acquire Delta e C :
      tokEL beta Delta e C ->
      tokEL beta Delta (Acquire e) C
  | TLE_Release Delta e1 e2 C1 C2 :
      tokEL beta Delta e1 C1 -> tokEL beta Delta e2 C2 ->
      tokEL beta Delta (Release e1 e2) (tc_add C1 C2)
  | TLE_Wait Delta e C :
      tokEL beta Delta e C ->
      tokEL beta Delta (Wait e) C
  | TLE_Drop Delta e C :
      tokEL beta Delta e C ->
      tokEL beta Delta (Drop e) C
with tokVL (beta : nat -> option (type * type)) : val -> token_ctx -> Prop :=
  | TVL_FunV x e C :
      tokEL beta tenv_zero e C ->
      tokVL beta (FunV x e) C
  | TVL_Unit :
      tokVL beta UnitV tc_zero
  | TVL_Pair v1 v2 C1 C2 :
      tokVL beta v1 C1 -> tokVL beta v2 C2 ->
      tokVL beta (PairV v1 v2) (tc_add C1 C2)
  | TVL_Sum n v C :
      tokVL beta v C ->
      tokVL beta (SumV n v) C
  | TVL_Barrier n t1 t2 :
      beta n = Some (t1, t2) ->
      tokVL beta (BarrierV n) (tc_bar_one n)
  | TVL_Lock n lc :
      tokVL beta (LockV n) (tc_lock_one n lc).

Scheme tokEL_mut := Induction for tokEL Sort Prop
  with tokVL_mut := Induction for tokVL Sort Prop.

(* ================================================================== *)
(* Alternative-aware occurrence counting.                             *)
(*                                                                    *)
(* At a [MatchSum], only one alternative is executed.  The amount of   *)
(* token context needed by the alternatives is therefore the maximum   *)
(* over the alternatives, not their sum.                              *)
(* ================================================================== *)

Definition fin_max {n} (f : fin n -> nat) : nat :=
  fold_right (fun i acc => max (f i) acc) 0 (fin_enum n).

Lemma fold_max_ge {A} (g : A -> nat) (l : list A) (b : nat) :
  forall x, x ∈ l -> g x <= fold_right (fun a acc => max (g a) acc) b l.
Proof.
  induction l as [|a l IH]; intros x Hx; simpl.
  - apply not_elem_of_nil in Hx. contradiction.
  - apply elem_of_cons in Hx. destruct Hx as [->|Hx].
    + lia.
    + pose proof (IH x Hx). lia.
Qed.

Lemma fold_max_le {A} (g : A -> nat) (l : list A) (b k : nat) :
  b <= k ->
  (forall x, x ∈ l -> g x <= k) ->
  fold_right (fun a acc => max (g a) acc) b l <= k.
Proof.
  intros Hb Hall. induction l as [|a l IH]; simpl.
  - exact Hb.
  - apply Nat.max_lub.
    + apply Hall. set_solver.
    + apply IH. intros x Hx. apply Hall. set_solver.
Qed.

Lemma fin_max_ge {n} (f : fin n -> nat) (i : fin n) :
  f i <= fin_max f.
Proof.
  unfold fin_max.
  apply (fold_max_ge f (fin_enum n) 0 i). apply fin_enum_complete.
Qed.

Lemma fin_max_empty (f : fin 0 -> nat) : fin_max f = 0.
Proof. reflexivity. Qed.

Lemma fin_max_zero {n} (f : fin n -> nat) :
  fin_max f = 0 -> forall i, f i = 0.
Proof.
  intros H i. pose proof (fin_max_ge f i). lia.
Qed.

Lemma fin_max_le {n} (f : fin n -> nat) (k : nat) :
  (forall i, f i <= k) -> fin_max f <= k.
Proof.
  intros H. unfold fin_max.
  apply (fold_max_le f (fin_enum n) 0 k); [lia|].
  intros x _. apply H.
Qed.

Fixpoint var_budget (x : string) (e : expr) : nat :=
  match e with
  | Val _ => 0
  | Var y => if decide (x = y) then 1 else 0
  | Fun y e => if decide (x = y) then 0 else var_budget x e
  | App e1 e2 => var_budget x e1 + var_budget x e2
  | Unit => 0
  | Pair e1 e2 => var_budget x e1 + var_budget x e2
  | LetPair e1 e2 => var_budget x e1 + var_budget x e2
  | Sum _ e => var_budget x e
  | MatchSum _ e es =>
      var_budget x e + fin_max (fun i => var_budget x (es i))
  | ForkBarrier e => var_budget x e
  | NewLock e => var_budget x e
  | ForkLock e1 e2 => var_budget x e1 + var_budget x e2
  | Acquire e => var_budget x e
  | Release e1 e2 => var_budget x e1 + var_budget x e2
  | Wait e => var_budget x e
  | Drop e => var_budget x e
  end.

Definition tc_nonzero (C : token_ctx) : Prop :=
  exists n, has_index_token C n.

Lemma var_budget_fun_neq x y e (H : x <> y) :
  var_budget x (Fun y e) = var_budget x e.
Proof.
  simpl. destruct (decide (x = y)); [contradiction|reflexivity].
Qed.

Definition tokE_linear (beta : nat -> option (type * type))
    (Delta : tenv) (e : expr) (C : token_ctx) : Prop :=
  tokEL beta Delta e C /\
  forall x, tc_nonzero (Delta x) -> var_budget x e <= 1.

Definition tokV_linear (beta : nat -> option (type * type))
    (v : val) (C : token_ctx) : Prop :=
  tokVL beta v C.

(* ================================================================== *)
(* Environment manipulation.                                          *)
(* ================================================================== *)

Definition tenv_update (Delta : tenv) (x : string) (C : token_ctx) : tenv :=
  fun y => if decide (y = x) then C else Delta y.

Definition tenv_eqv (D1 D2 : tenv) : Prop := forall x, D1 x = D2 x.

Lemma tenv_eqv_refl D : tenv_eqv D D.
Proof. intro x. reflexivity. Qed.

Lemma tenv_eqv_sym D1 D2 : tenv_eqv D1 D2 -> tenv_eqv D2 D1.
Proof. intros H x. symmetry. apply H. Qed.

Lemma tenv_eqv_trans D1 D2 D3 :
  tenv_eqv D1 D2 -> tenv_eqv D2 D3 -> tenv_eqv D1 D3.
Proof. intros H1 H2 x. rewrite H1. apply H2. Qed.

Lemma tenv_update_same Delta x C : tenv_update Delta x C x = C.
Proof. unfold tenv_update. destruct (decide (x = x)); [reflexivity|exfalso; apply n; reflexivity]. Qed.

Lemma tenv_update_neq Delta x y C (H : y <> x) :
  tenv_update Delta x C y = Delta y.
Proof.
  unfold tenv_update. destruct (decide (y = x)); [exfalso; apply H; exact e|reflexivity].
Qed.

Lemma tenv_eqv_bind Delta1 Delta2 x :
  tenv_eqv Delta1 Delta2 -> tenv_eqv (tenv_bind Delta1 x) (tenv_bind Delta2 x).
Proof.
  intros H y. unfold tenv_bind.
  destruct (decide (y = x)); [reflexivity|apply H].
Qed.

Lemma tenv_bind_update_same Delta x C :
  tenv_eqv (tenv_bind (tenv_update Delta x C) x) (tenv_bind Delta x).
Proof.
  intro y. unfold tenv_bind.
  destruct (decide (y = x)) as [->|H].
  - reflexivity.
  - rewrite tenv_update_neq by exact H. reflexivity.
Qed.

Lemma tenv_bind_update_neq Delta x y C (H : y <> x) :
  tenv_eqv (tenv_bind (tenv_update Delta x C) y)
           (tenv_update (tenv_bind Delta y) x C).
Proof.
  intro z. unfold tenv_bind, tenv_update.
  destruct (decide (z = y)) as [->|Hy].
  - destruct (decide (y = x)); [contradiction|reflexivity].
  - destruct (decide (z = x)) as [->|Hx]; reflexivity.
Qed.

Lemma tokEL_tenv_eqv beta D1 D2 e C
    (Heq : tenv_eqv D1 D2) (H : tokEL beta D1 e C) :
  tokEL beta D2 e C.
Proof.
  revert D2 Heq.
  induction H; intros D2 Heq; try (econstructor; eauto; fail).
  - econstructor. rewrite <- Heq. exact H.
  - eapply TLE_Fun. apply IHtokEL. apply tenv_eqv_bind. exact Heq.
Qed.

(* ================================================================== *)
(* Source-initial terms have the empty token context in the new       *)
(* grammar as well.                                                   *)
(* ================================================================== *)

Lemma has_index_token_zero C (H : has_index_token tc_zero C) : False.
Proof.
  destruct H as [[lc Hl]|Hb].
  - unfold tc_zero in Hl. simpl in Hl. lia.
  - unfold tc_zero in Hb. simpl in Hb. lia.
Qed.

Lemma tc_nonzero_zero : ~ tc_nonzero tc_zero.
Proof.
  intros [n Hn]. exact (has_index_token_zero n Hn).
Qed.

Lemma tenv_zero_zeroish : tenv_zeroish tenv_zero.
Proof. intro x. reflexivity. Qed.

Ltac tokL_zero_rec H :=
  match goal with
  | IH : forall D : tenv, tenv_zeroish D -> tokEL ?b D _ tc_zero
      |- tokEL ?b ?D _ tc_zero => apply IH; exact H
  end.

Lemma tokEL_zero_of_val_free beta e (H : val_free e) :
  forall Delta, tenv_zeroish Delta -> tokEL beta Delta e tc_zero.
Proof.
  induction H; intros Delta Hzero.
  - apply TLE_Var. apply Hzero.
  - apply TLE_Fun. apply IHval_free. apply tenv_bind_zeroish. exact Hzero.
  - apply TLE_App with (C1 := tc_zero) (C2 := tc_zero); tokL_zero_rec Hzero.
  - apply TLE_Unit.
  - apply TLE_Pair with (C1 := tc_zero) (C2 := tc_zero); tokL_zero_rec Hzero.
  - apply TLE_LetPair with (C1 := tc_zero) (C2 := tc_zero); tokL_zero_rec Hzero.
  - apply TLE_Sum. tokL_zero_rec Hzero.
  - eapply TLE_MatchSum with (Cs := tc_zero) (Cb := tc_zero)
      (Cbs := fun _ => tc_zero).
    + tokL_zero_rec Hzero.
    + intro i.
      match goal with
      | IH : forall i : fin _, forall D : tenv,
                 tenv_zeroish D -> tokEL beta D (_ i) tc_zero
          |- tokEL beta Delta (_ i) tc_zero =>
          exact (IH i Delta Hzero)
      end.
    + intros i. apply tc_le_refl.
    + intro. reflexivity.
  - apply TLE_ForkBarrier. tokL_zero_rec Hzero.
  - apply TLE_NewLock. tokL_zero_rec Hzero.
  - apply TLE_ForkLock with (C1 := tc_zero) (C2 := tc_zero); tokL_zero_rec Hzero.
  - apply TLE_Acquire. tokL_zero_rec Hzero.
  - apply TLE_Release with (C1 := tc_zero) (C2 := tc_zero); tokL_zero_rec Hzero.
  - apply TLE_Wait. tokL_zero_rec Hzero.
  - apply TLE_Drop. tokL_zero_rec Hzero.
Qed.

Theorem typed_to_tokEL_linear Gamma e t (H : typed Gamma e t)
    (beta : nat -> option (type * type)) :
  tokE_linear beta tenv_zero e tc_zero.
Proof.
  split.
  - apply (tokEL_zero_of_val_free beta e (typed_val_free Gamma e t H)
             tenv_zero tenv_zero_zeroish).
  - intros x Hx. destruct Hx as [n Hn]. exfalso.
    exact (has_index_token_zero n Hn).
Qed.

(* ================================================================== *)
(* Token soundness for the redesigned grammar.                        *)
(* ================================================================== *)

Lemma tc_le_has_index C D n (Hle : tc_le C D) :
  has_index_token C n -> has_index_token D n.
Proof.
  destruct Hle as [Hl Hb]. intros [[lc Hc]|Hc].
  - left. exists lc. pose proof (Hl n lc). lia.
  - right. pose proof (Hb n). lia.
Qed.

Lemma tc_le_add_mono C1 C2 D1 D2 :
  tc_le C1 D1 -> tc_le C2 D2 -> tc_le (tc_add C1 C2) (tc_add D1 D2).
Proof.
  intros [Hl1 Hb1] [Hl2 Hb2]. split.
  - intros n lc. unfold tc_add. simpl.
    pose proof (Hl1 n lc). pose proof (Hl2 n lc). lia.
  - intros n. unfold tc_add. simpl.
    pose proof (Hb1 n). pose proof (Hb2 n). lia.
Qed.

Ltac tokL_sound_apply :=
  match goal with
  | IH : (forall m : nat, m ∈ expr_refs _ -> has_index_token _ m)
      |- has_index_token _ _ => eapply IH; eassumption
  | IH : (forall m : nat, m ∈ val_refs _ -> has_index_token _ m)
      |- has_index_token _ _ => eapply IH; eassumption
  end.

Lemma tokEL_sound beta Delta e C (H : tokEL beta Delta e C) :
  forall n, n ∈ expr_refs e -> has_index_token C n.
Proof.
  induction H using tokEL_mut with
    (P0 := fun v C (Hv : tokVL beta v C) =>
             forall n, n ∈ val_refs v -> has_index_token C n).
  - intros k Hk. simpl in Hk. set_solver.
  - intros k Hk.
    match goal with
    | IHv : (forall m, m ∈ val_refs _ -> has_index_token _ m) |- _ =>
        exact (IHv k Hk)
    end.
  - intros k Hk. simpl in Hk. tokL_sound_apply.
  - intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tokL_sound_apply.
    + apply tc_add_has_index_r. tokL_sound_apply.
  - intros k Hk. simpl in Hk. set_solver.
  - intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tokL_sound_apply.
    + apply tc_add_has_index_r. tokL_sound_apply.
  - intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tokL_sound_apply.
    + apply tc_add_has_index_r. tokL_sound_apply.
  - intros k Hk. simpl in Hk. tokL_sound_apply.
  - intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tokL_sound_apply.
    + apply tc_add_has_index_r.
      apply elem_of_fin_union in Hk. destruct Hk as [i Hi].
      exact (tc_le_has_index _ _ _ (t0 i) (H0 i k Hi)).
  - intros k Hk. simpl in Hk. tokL_sound_apply.
  - intros k Hk. simpl in Hk. tokL_sound_apply.
  - intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tokL_sound_apply.
    + apply tc_add_has_index_r. tokL_sound_apply.
  - intros k Hk. simpl in Hk. tokL_sound_apply.
  - intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tokL_sound_apply.
    + apply tc_add_has_index_r. tokL_sound_apply.
  - intros k Hk. simpl in Hk. tokL_sound_apply.
  - intros k Hk. simpl in Hk. tokL_sound_apply.
  - intros k Hk. simpl in Hk. tokL_sound_apply.
  - intros k Hk. simpl in Hk. set_solver.
  - intros k Hk. simpl in Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. tokL_sound_apply.
    + apply tc_add_has_index_r. tokL_sound_apply.
  - intros k Hk. simpl in Hk. tokL_sound_apply.
  - intros k Hk. simpl in Hk. apply elem_of_singleton in Hk. subst k.
    right. rewrite tc_bar_one_same. lia.
  - intros k Hk. simpl in Hk. apply elem_of_singleton in Hk. subst k.
    left. exists lc. rewrite tc_lock_one_same. lia.
Qed.

(* Inversion helpers. *)
Lemma tokEL_val_inv beta Delta v C (H : tokEL beta Delta (Val v) C) :
  tokVL beta v C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokEL_release_inv beta Delta e1 e2 C
    (H : tokEL beta Delta (Release e1 e2) C) :
  exists C1 C2, C = tc_add C1 C2 /\
    tokEL beta Delta e1 C1 /\ tokEL beta Delta e2 C2.
Proof. inversion H; subst; eauto. Qed.

Lemma tokVL_lock_inv beta n C (H : tokVL beta (LockV n) C) :
  exists lc, C = tc_lock_one n lc.
Proof. inversion H; subst; eauto. Qed.

Lemma index_single_add_left_L C1 C2 :
  index_single (tc_add C1 C2) -> index_single C1.
Proof.
  intros H n. pose proof (H n) as Hle.
  rewrite tc_add_lock_count, tc_add_bar in Hle.
  unfold lock_count in *. lia.
Qed.

Lemma index_single_split_lock_zero_L C1 C2 n lc
    (Hsingle : index_single (tc_add C1 C2))
    (Hpos : 0 < tok_lock C1 n lc) :
  (forall lc', tok_lock C2 n lc' = 0) /\ tok_bar C2 n = 0.
Proof.
  assert (Hsum : lock_count (tc_add C1 C2) n + tok_bar (tc_add C1 C2) n
                 = (lock_count C1 n + tok_bar C1 n)
                   + (lock_count C2 n + tok_bar C2 n)).
  { rewrite tc_add_lock_count, tc_add_bar. lia. }
  assert (Hle : lock_count (tc_add C1 C2) n + tok_bar (tc_add C1 C2) n <= 1)
    by apply Hsingle.
  assert (Hc1pos : 1 <= lock_count C1 n).
  { pose proof (lock_count_le_sum C1 n lc). lia. }
  assert (Hc2 : lock_count C2 n = 0).
  { rewrite Hsum in Hle. lia. }
  split.
  - intro lc'. pose proof (lock_count_le_sum C2 n lc'). lia.
  - rewrite Hsum in Hle. lia.
Qed.

Theorem release_payload_token_free_L beta Delta n v C1 C2
    (Htok : tokEL beta Delta (Release (Val (LockV n)) (Val v))
              (tc_add C1 C2))
    (Hsingle : index_single (tc_add C1 C2)) :
  n ∉ val_refs v.
Proof.
  destruct (tokEL_release_inv beta Delta (Val (LockV n)) (Val v)
              (tc_add C1 C2) Htok) as (C1' & C2' & HC & H1 & H2).
  pose proof (tokEL_val_inv beta Delta (LockV n) C1' H1) as Hv1.
  destruct (tokVL_lock_inv beta n C1' Hv1) as (lc & HC1).
  subst C1'.
  assert (Hsingle' : index_single (tc_add (tc_lock_one n lc) C2')).
  { rewrite <- HC. exact Hsingle. }
  assert (Hlock : 0 < tok_lock (tc_lock_one n lc) n lc).
  { rewrite tc_lock_one_same. lia. }
  destruct (index_single_split_lock_zero_L (tc_lock_one n lc) C2' n lc
              Hsingle' Hlock) as [Hzero Hbar].
  intro Hn.
  pose proof (tokEL_sound beta Delta (Val v) C2' H2 n) as Hs.
  simpl in Hs. specialize (Hs Hn).
  destruct Hs as [[lc' Hlc']|Hb].
  - rewrite Hzero in Hlc'. lia.
  - rewrite Hbar in Hb. lia.
Qed.

Print Assumptions tokEL_zero_of_val_free.
Print Assumptions typed_to_tokEL_linear.
Print Assumptions tokEL_sound.
Print Assumptions release_payload_token_free_L.

(* ================================================================== *)
(* Finite choice for branch contexts.                                 *)
(* ================================================================== *)

Lemma fin_choice {n} (P : fin n -> token_ctx -> Prop) :
  (forall i, exists C, P i C) ->
  exists f, forall i, P i (f i).
Proof.
  revert P. induction n as [|n IH]; intros P H.
  - exists (fun i => Fin.case0 (fun _ => token_ctx) i).
    intro i. exfalso. exact (Fin.case0 (fun _ => False) i).
  - destruct (H 0%fin) as (c0 & Hc0).
    destruct (IH (fun i => P (Fin.FS i))) as (f & Hf).
    + intro i. apply H.
    + exists (fun i => Fin.caseS' i (fun _ => token_ctx) c0 f).
      intro i.
      refine (Fin.caseS' i
                (fun j => P j (Fin.caseS' j (fun _ => token_ctx) c0 f))
                _ _).
      * exact Hc0.
      * intro p. simpl. apply Hf.
Qed.

(* ================================================================== *)
(* Substitution by a token-free value.                                *)
(*                                                                    *)
(* This is the zero-context case: if the argument consumes no token,  *)
(* it can be duplicated arbitrarily often and the surrounding token    *)
(* context does not change at all.                                    *)
(* ================================================================== *)

Lemma tokEL_subst_zero beta x a e :
  tokVL beta a tc_zero ->
  forall Delta C, Delta x = tc_zero -> tokEL beta Delta e C ->
    tokEL beta (tenv_update Delta x tc_zero) (subst x a e) C.
Proof.
  intros Ha.
  induction e; intros Delta C Hx0 Htok; inversion Htok; subst; simpl.
  - (* Val *) econstructor. assumption.
  - (* Var *) destruct (decide (x = s)) as [E|E].
    + subst s. rewrite Hx0. econstructor. exact Ha.
    + econstructor.
      rewrite tenv_update_neq by (intro H; apply E; symmetry; exact H).
      reflexivity.
  - (* Fun *) destruct (decide (x = s)) as [E|E].
    + subst s. econstructor.
      apply (tokEL_tenv_eqv beta (tenv_bind Delta x)
               (tenv_bind (tenv_update Delta x tc_zero) x) e C).
      * apply tenv_eqv_sym. apply tenv_bind_update_same.
      * exact H3.
    + econstructor.
      apply (tokEL_tenv_eqv beta
               (tenv_update (tenv_bind Delta s) x tc_zero)
               (tenv_bind (tenv_update Delta x tc_zero) s)
               (subst x a e) C).
      * apply tenv_eqv_sym. apply tenv_bind_update_neq.
        intro H. exact (E (eq_sym H)).
      * apply IHe.
        -- unfold tenv_bind. destruct (decide (x = s)); [reflexivity|exact Hx0].
        -- exact H3.
  - (* App *) econstructor; [apply IHe1; assumption|apply IHe2; assumption].
  - (* Unit *) econstructor.
  - (* Pair *) econstructor; [apply IHe1; assumption|apply IHe2; assumption].
  - (* LetPair *) econstructor; [apply IHe1; assumption|apply IHe2; assumption].
  - (* Sum *) econstructor. apply IHe; assumption.
  - (* MatchSum *)
    apply (inj_pair2_eq_dec nat Nat.eq_dec) in H2. subst es0.
    eapply TLE_MatchSum with (Cs := Cs) (Cb := Cb) (Cbs := Cbs).
    + exact (IHe Delta Cs Hx0 H3).
    + intro i. exact (H i Delta (Cbs i) Hx0 (H5 i)).
    + exact H7.
    + exact H8.
  - (* ForkBarrier *) econstructor. apply IHe; assumption.
  - (* NewLock *) econstructor. apply IHe; assumption.
  - (* ForkLock *) econstructor; [apply IHe1; assumption|apply IHe2; assumption].
  - (* Acquire *) econstructor. apply IHe; assumption.
  - (* Release *) econstructor; [apply IHe1; assumption|apply IHe2; assumption].
  - (* Wait *) econstructor. apply IHe; assumption.
  - (* Drop *) econstructor. apply IHe; assumption.
Qed.

Lemma tc_le_add_rearrange_l C1 Ca C2 :
  tc_le (tc_add (tc_add C1 Ca) C2) (tc_add (tc_add C1 C2) Ca).
Proof.
  unfold tc_le, tc_add. simpl. split; intros; lia.
Qed.

Lemma tc_le_add_rearrange_r C1 C2 Ca :
  tc_le (tc_add C1 (tc_add C2 Ca)) (tc_add (tc_add C1 C2) Ca).
Proof.
  unfold tc_le, tc_add. simpl. split; intros; lia.
Qed.

(* ================================================================== *)
(* The linear substitution lemma.                                     *)
(*                                                                    *)
(* If the variable occurs at most once (counting alternatives by      *)
(* their maximum), substituting a value [a] with context [Ca] gives a *)
(* term whose token context is bounded by [C + Ca].  We deliberately  *)
(* state an upper bound rather than [C - Cx + Ca]: this is exactly    *)
(* what is needed for the single-index invariant, while avoiding a    *)
(* subtraction that would be wrong for shared branch contexts.        *)
(* ================================================================== *)

Lemma tokEL_subst_linear beta x a Ca (Ha : tokVL beta a Ca) :
  forall e Delta C,
    var_budget x e <= 1 ->
    tokEL beta Delta e C ->
    exists C',
      tokEL beta (tenv_update Delta x Ca) (subst x a e) C' /\
      (var_budget x e = 0 -> tc_le C' C) /\
      (var_budget x e = 1 -> tc_le C' (tc_add C Ca)).
Proof.
  induction e; intros Delta C Hvb Htok; pose (Csrc := C); inversion Htok; subst; simpl.
  - (* Val *)
    exists Csrc. split; [econstructor; assumption|].
    split; [intro; apply tc_le_refl|intro H; simpl in H; lia].
  - (* Var *)
    destruct (decide (x = s)) as [E|E].
    + subst s. exists Ca. split.
      * econstructor. exact Ha.
      * split.
        -- intro H; simpl in H; lia.
        -- intros _. apply tc_le_add_r.
    + exists Csrc. split.
      * econstructor. rewrite tenv_update_neq.
        { reflexivity. }
        { intro H; apply E; symmetry; exact H. }
      * split.
        -- intros _. apply tc_le_refl.
        -- intro H; simpl in H; lia.
  - (* Fun *)
    destruct (decide (x = s)) as [E|E].
    + subst s. exists Csrc. split.
      * econstructor.
        apply (tokEL_tenv_eqv beta (tenv_bind Delta x)
                 (tenv_bind (tenv_update Delta x Ca) x) e C).
        { apply tenv_eqv_sym. apply tenv_bind_update_same. }
        { exact H3. }
      * split.
        -- intros _. apply tc_le_refl.
        -- intro H; simpl in H; lia.
    + destruct (IHe (tenv_bind Delta s) C) as (C' & Hbody & HB0 & HB1).
      { change (var_budget x (Fun s e) <= 1) in Hvb.
        rewrite (var_budget_fun_neq x s e E) in Hvb. exact Hvb. }
      { exact H3. }
      exists C'. split.
      * econstructor.
        apply (tokEL_tenv_eqv beta
                 (tenv_update (tenv_bind Delta s) x Ca)
                 (tenv_bind (tenv_update Delta x Ca) s)
                 (subst x a e) C').
        -- apply tenv_eqv_sym. apply tenv_bind_update_neq.
           intro H; apply E; symmetry; exact H.
        -- exact Hbody.
      * split.
        -- intro H; simpl in H. apply HB0. exact H.
        -- intro H; simpl in H. apply HB1. exact H.
  - (* App *)
    simpl in Hvb.
    destruct (IHe1 Delta C1) as (C1' & Ht1 & HB10 & HB11).
    { lia. }
    { exact H2. }
    destruct (IHe2 Delta C2) as (C2' & Ht2 & HB20 & HB21).
    { lia. }
    { exact H4. }
    exists (tc_add C1' C2'). split.
    + econstructor; assumption.
    + split.
      * intro H0. assert (H1z : var_budget x e1 = 0) by lia.
        assert (H2z : var_budget x e2 = 0) by lia.
        eapply tc_le_trans.
        -- apply tc_le_add_mono; [apply HB10; exact H1z|apply HB20; exact H2z].
        -- apply tc_le_refl.
      * intro Hsum. assert (H1c : var_budget x e1 = 0 \/ var_budget x e1 = 1) by lia.
        destruct H1c as [H1z|H1o].
        -- assert (H2o : var_budget x e2 = 1) by lia.
           eapply tc_le_trans.
           ++ apply tc_le_add_mono; [apply HB10; exact H1z|apply HB21; exact H2o].
           ++ apply tc_le_add_rearrange_r.
        -- assert (H2z : var_budget x e2 = 0) by lia.
           eapply tc_le_trans.
           ++ apply tc_le_add_mono; [apply HB11; exact H1o|apply HB20; exact H2z].
           ++ apply tc_le_add_rearrange_l.
  - (* Unit *)
    exists tc_zero. split; [econstructor|]. split; [intro; apply tc_le_refl|intro H; simpl in H; lia].
  - (* Pair *)
    simpl in Hvb.
    destruct (IHe1 Delta C1) as (C1' & Ht1 & HB10 & HB11).
    { lia. }
    { exact H2. }
    destruct (IHe2 Delta C2) as (C2' & Ht2 & HB20 & HB21).
    { lia. }
    { exact H4. }
    exists (tc_add C1' C2'). split.
    + econstructor; assumption.
    + split.
      * intro H0. assert (H1z : var_budget x e1 = 0) by lia.
        assert (H2z : var_budget x e2 = 0) by lia.
        eapply tc_le_trans.
        -- apply tc_le_add_mono; [apply HB10; exact H1z|apply HB20; exact H2z].
        -- apply tc_le_refl.
      * intro Hsum. assert (H1c : var_budget x e1 = 0 \/ var_budget x e1 = 1) by lia.
        destruct H1c as [H1z|H1o].
        -- assert (H2o : var_budget x e2 = 1) by lia.
           eapply tc_le_trans.
           ++ apply tc_le_add_mono; [apply HB10; exact H1z|apply HB21; exact H2o].
           ++ apply tc_le_add_rearrange_r.
        -- assert (H2z : var_budget x e2 = 0) by lia.
           eapply tc_le_trans.
           ++ apply tc_le_add_mono; [apply HB11; exact H1o|apply HB20; exact H2z].
           ++ apply tc_le_add_rearrange_l.
  - (* LetPair *)
    simpl in Hvb.
    destruct (IHe1 Delta C1) as (C1' & Ht1 & HB10 & HB11).
    { lia. }
    { exact H2. }
    destruct (IHe2 Delta C2) as (C2' & Ht2 & HB20 & HB21).
    { lia. }
    { exact H4. }
    exists (tc_add C1' C2'). split.
    + econstructor; assumption.
    + split.
      * intro H0. assert (H1z : var_budget x e1 = 0) by lia.
        assert (H2z : var_budget x e2 = 0) by lia.
        eapply tc_le_trans.
        -- apply tc_le_add_mono; [apply HB10; exact H1z|apply HB20; exact H2z].
        -- apply tc_le_refl.
      * intro Hsum. assert (H1c : var_budget x e1 = 0 \/ var_budget x e1 = 1) by lia.
        destruct H1c as [H1z|H1o].
        -- assert (H2o : var_budget x e2 = 1) by lia.
           eapply tc_le_trans.
           ++ apply tc_le_add_mono; [apply HB10; exact H1z|apply HB21; exact H2o].
           ++ apply tc_le_add_rearrange_r.
        -- assert (H2z : var_budget x e2 = 0) by lia.
           eapply tc_le_trans.
           ++ apply tc_le_add_mono; [apply HB11; exact H1o|apply HB20; exact H2z].
           ++ apply tc_le_add_rearrange_l.
  - (* Sum *)
    destruct (IHe Delta C Hvb H3) as (C' & Ht & HB0 & HB1).
    exists C'. split; [econstructor; assumption|]. split; assumption.
  - (* MatchSum *)
    simpl in Hvb.
    apply (inj_pair2_eq_dec nat Nat.eq_dec) in H2. subst es0.
    set (vs := var_budget x e).
    set (bm := fin_max (fun i => var_budget x (e0 i))).
    assert (Hvs1 : vs <= 1) by lia.
    assert (Hbm1le : bm <= 1) by (unfold bm; lia).
    destruct (IHe Delta Cs Hvs1 H3) as (Cs' & Hsc & HS0 & HS1).
    assert (Hbranches : forall i, exists Cb',
       tokEL beta (tenv_update Delta x Ca) (subst x a (e0 i)) Cb' /\
       (var_budget x (e0 i) = 0 -> tc_le Cb' (Cbs i)) /\
       (var_budget x (e0 i) = 1 -> tc_le Cb' (tc_add (Cbs i) Ca))).
    { intro i. apply (H i Delta (Cbs i)).
      - unfold bm in Hbm1le. pose proof (fin_max_ge (fun j => var_budget x (e0 j)) i). lia.
      - exact (H5 i). }
    destruct (fin_choice (fun i Cb' =>
       tokEL beta (tenv_update Delta x Ca) (subst x a (e0 i)) Cb' /\
       (var_budget x (e0 i) = 0 -> tc_le Cb' (Cbs i)) /\
       (var_budget x (e0 i) = 1 -> tc_le Cb' (tc_add (Cbs i) Ca))))
      as (Cbs' & HCbs').
    { exact Hbranches. }
    destruct (Nat.eq_0_gt_0_cases bm) as [Hbm0|Hbmpos].
    + (* no branch uses x *)
      assert (Hbm0' : bm = 0) by exact Hbm0.
      exists (tc_add Cs' Cb). split.
      * eapply TLE_MatchSum with (Cs := Cs') (Cb := Cb) (Cbs := Cbs').
        -- exact Hsc.
        -- intro i. exact (proj1 (HCbs' i)).
        -- intro i. apply tc_le_trans with (Cbs i).
           ++ destruct (Nat.eq_0_gt_0_cases (var_budget x (e0 i))) as [Hz|Hp].
              ** apply (proj1 (proj2 (HCbs' i)) Hz).
              ** exfalso. pose proof (fin_max_ge (fun j => var_budget x (e0 j)) i). lia.
           ++ apply H7.
        -- exact H8.
      * split.
        -- intro Hzero. assert (Hvsz : vs = 0) by lia.
           eapply tc_le_trans.
           ++ apply tc_le_add_mono.
              ** apply HS0. exact Hvsz.
              ** apply tc_le_refl.
           ++ apply tc_le_refl.
        -- intro Hone. assert (Hvso : vs = 1) by lia.
           eapply tc_le_trans.
           ++ apply tc_le_add_mono.
              ** apply HS1. exact Hvso.
              ** apply tc_le_refl.
           ++ apply tc_le_add_rearrange_l.
    + (* some branch uses x; all branches use at most once *)
      assert (Hbm1 : bm = 1) by (destruct bm; [lia|destruct bm; [reflexivity|lia]]).
      assert (Hn0 : n <> 0).
      { intro Hn. subst n. simpl in Hbm1. discriminate. }
      exists (tc_add Cs' (tc_add Cb Ca)). split.
      * eapply TLE_MatchSum with (Cs := Cs') (Cb := tc_add Cb Ca) (Cbs := Cbs').
        -- exact Hsc.
        -- intro i. exact (proj1 (HCbs' i)).
        -- intro i.
           assert (Hbi : var_budget x (e0 i) <= 1).
           { unfold bm in Hbm1le.
             pose proof (fin_max_ge (fun j => var_budget x (e0 j)) i). lia. }
           destruct (Nat.eq_0_gt_0_cases (var_budget x (e0 i))) as [Hz|Hp].
           ++ apply (tc_le_trans (Cbs' i) (Cbs i) (tc_add Cb Ca)).
              ** apply (proj1 (proj2 (HCbs' i)) Hz).
              ** apply (tc_le_trans (Cbs i) Cb (tc_add Cb Ca)).
                 --- apply H7.
                 --- apply tc_le_add_l.
           ++ assert (Hoi : var_budget x (e0 i) = 1) by lia.
              apply (tc_le_trans (Cbs' i) (tc_add (Cbs i) Ca) (tc_add Cb Ca)).
              ** apply (proj2 (proj2 (HCbs' i)) Hoi).
              ** apply tc_le_add_mono; [apply H7|apply tc_le_refl].
        -- intro Hn. exfalso. apply Hn0. exact Hn.
      * split.
        -- intro Hzero. assert (vs = 0) by lia. exfalso. lia.
        -- intro Hone. assert (Hvsz : vs = 0) by lia.
           eapply tc_le_trans.
           ++ apply tc_le_add_mono.
              ** apply HS0. exact Hvsz.
              ** apply tc_le_refl.
           ++ apply tc_le_add_rearrange_r.
  - (* ForkBarrier *)
    destruct (IHe Delta C Hvb H1) as (C' & Ht & HB0 & HB1).
    exists C'. split; [econstructor; assumption|]. split; assumption.
  - (* NewLock *)
    destruct (IHe Delta C Hvb H1) as (C' & Ht & HB0 & HB1).
    exists C'. split; [econstructor; assumption|]. split; assumption.
  - (* ForkLock *)
    simpl in Hvb.
    destruct (IHe1 Delta C1) as (C1' & Ht1 & HB10 & HB11).
    { lia. }
    { exact H2. }
    destruct (IHe2 Delta C2) as (C2' & Ht2 & HB20 & HB21).
    { lia. }
    { exact H4. }
    exists (tc_add C1' C2'). split.
    + econstructor; assumption.
    + split.
      * intro H0. assert (H1z : var_budget x e1 = 0) by lia.
        assert (H2z : var_budget x e2 = 0) by lia.
        eapply tc_le_trans.
        -- apply tc_le_add_mono; [apply HB10; exact H1z|apply HB20; exact H2z].
        -- apply tc_le_refl.
      * intro Hsum. assert (H1c : var_budget x e1 = 0 \/ var_budget x e1 = 1) by lia.
        destruct H1c as [H1z|H1o].
        -- assert (H2o : var_budget x e2 = 1) by lia.
           eapply tc_le_trans.
           ++ apply tc_le_add_mono; [apply HB10; exact H1z|apply HB21; exact H2o].
           ++ apply tc_le_add_rearrange_r.
        -- assert (H2z : var_budget x e2 = 0) by lia.
           eapply tc_le_trans.
           ++ apply tc_le_add_mono; [apply HB11; exact H1o|apply HB20; exact H2z].
           ++ apply tc_le_add_rearrange_l.
  - (* Acquire *)
    destruct (IHe Delta C Hvb H1) as (C' & Ht & HB0 & HB1).
    exists C'. split; [econstructor; assumption|]. split; assumption.
  - (* Release *)
    simpl in Hvb.
    destruct (IHe1 Delta C1) as (C1' & Ht1 & HB10 & HB11).
    { lia. }
    { exact H2. }
    destruct (IHe2 Delta C2) as (C2' & Ht2 & HB20 & HB21).
    { lia. }
    { exact H4. }
    exists (tc_add C1' C2'). split.
    + econstructor; assumption.
    + split.
      * intro H0. assert (H1z : var_budget x e1 = 0) by lia.
        assert (H2z : var_budget x e2 = 0) by lia.
        eapply tc_le_trans.
        -- apply tc_le_add_mono; [apply HB10; exact H1z|apply HB20; exact H2z].
        -- apply tc_le_refl.
      * intro Hsum. assert (H1c : var_budget x e1 = 0 \/ var_budget x e1 = 1) by lia.
        destruct H1c as [H1z|H1o].
        -- assert (H2o : var_budget x e2 = 1) by lia.
           eapply tc_le_trans.
           ++ apply tc_le_add_mono; [apply HB10; exact H1z|apply HB21; exact H2o].
           ++ apply tc_le_add_rearrange_r.
        -- assert (H2z : var_budget x e2 = 0) by lia.
           eapply tc_le_trans.
           ++ apply tc_le_add_mono; [apply HB11; exact H1o|apply HB20; exact H2z].
           ++ apply tc_le_add_rearrange_l.
  - (* Wait *)
    destruct (IHe Delta C Hvb H1) as (C' & Ht & HB0 & HB1).
    exists C'. split; [econstructor; assumption|]. split; assumption.
  - (* Drop *)
    destruct (IHe Delta C Hvb H1) as (C' & Ht & HB0 & HB1).
    exists C'. split; [econstructor; assumption|]. split; assumption.
Qed.

Corollary tokEL_subst_linear_bound beta x a Ca e Delta C
    (Ha : tokVL beta a Ca)
    (Hlin : var_budget x e <= 1)
    (H : tokEL beta Delta e C) :
  exists C',
    tokEL beta (tenv_update Delta x Ca) (subst x a e) C' /\
    tc_le C' (tc_add C Ca).
Proof.
  destruct (tokEL_subst_linear beta x a Ca Ha e Delta C Hlin H)
    as (C' & Htok & HB0 & HB1).
  exists C'. split; [exact Htok|].
  destruct (Nat.eq_0_gt_0_cases (var_budget x e)) as [Hz|Hp].
  - apply tc_le_trans with C.
    + apply HB0. exact Hz.
    + apply tc_le_add_l.
  - assert (Ho : var_budget x e = 1) by lia.
    apply HB1. exact Ho.
Qed.

Corollary tokEL_subst_zero_exact beta x a e Delta C
    (Ha : tokVL beta a tc_zero)
    (Hx0 : Delta x = tc_zero)
    (H : tokEL beta Delta e C) :
  tokEL beta (tenv_update Delta x tc_zero) (subst x a e) C.
Proof. exact (tokEL_subst_zero beta x a e Ha Delta C Hx0 H). Qed.

(* Annotated runtime typing for the redesigned grammar. *)
Definition wtKL (L : gmap nat type) (beta : nat -> option (type * type))
    (Gamma : env) (e : expr) (t : type) (C : token_ctx) : Prop :=
  wt L Gamma e t /\ tokEL beta tenv_zero e C.

Definition cvKL (L : gmap nat type) (beta : nat -> option (type * type))
    (v : val) (t : type) (C : token_ctx) : Prop :=
  cv L v t /\ tokVL beta v C.

Theorem typed_to_wtKL Gamma e t (H : typed Gamma e t)
    (L : gmap nat type) (beta : nat -> option (type * type)) :
  wtKL L beta Gamma e t tc_zero.
Proof.
  split.
  - apply typed_to_wt. exact H.
  - apply (tokEL_zero_of_val_free beta e (typed_val_free Gamma e t H)
             tenv_zero tenv_zero_zeroish).
Qed.

Lemma tokVL_val_refs_sound beta v C (H : tokVL beta v C) :
  forall n, n ∈ val_refs v -> has_index_token C n.
Proof.
  induction H as
    [ x0 e0 C0 Hbody
    | 
    | v1 v2 C1 C2 H1 IH1 H2 IH2
    | n v C H IH
    | n t1 t2 Hbeta
    | n lc ].
  - simpl. intros k Hk. apply (tokEL_sound beta tenv_zero e0 C0 Hbody k Hk).
  - simpl. intros k Hk. set_solver.
  - simpl. intros k Hk. apply elem_of_union in Hk.
    destruct Hk as [Hk|Hk].
    + apply tc_add_has_index_l. apply IH1. exact Hk.
    + apply tc_add_has_index_r. apply IH2. exact Hk.
  - simpl. intros k Hk. apply IH. exact Hk.
  - simpl. intros k Hk. apply elem_of_singleton in Hk. subst k.
    right. rewrite tc_bar_one_same. lia.
  - simpl. intros k Hk. apply elem_of_singleton in Hk. subst k.
    left. exists lc. rewrite tc_lock_one_same. lia.
Qed.

Print Assumptions fin_choice.
Print Assumptions tokEL_subst_zero.
Print Assumptions tokEL_subst_linear.
Print Assumptions tokEL_subst_linear_bound.
Print Assumptions typed_to_wtKL.
Print Assumptions tokVL_val_refs_sound.

(* ===== TokenPure.v ===== *)
Open Scope string_scope.

(* ================================================================== *)
(* Pure reduction of the redesigned token grammar.                    *)
(*                                                                    *)
(* This file isolates what can be proved without any extra assumption: *)
(* all non-beta pure steps, and beta steps whose argument is either    *)
(* used at most once or carries no token at all.  The remaining beta   *)
(* case is precisely the obstruction identified in the report.        *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Environment irrelevance for an expression in which [x] does not    *)
(* occur.  This lets a substitution result, which is naturally typed  *)
(* in [tenv_update Delta x Ca], be returned to [Delta] after [x] has  *)
(* been substituted away.                                             *)
(* ------------------------------------------------------------------ *)

Lemma var_budget_subst_same x a e :
  var_budget x (subst x a e) = 0.
Proof.
  induction e; simpl.
  - reflexivity.
  - (* Var *) destruct (decide (x = s)) as [E|E].
    + subst s. destruct (decide (x = x)); [reflexivity|contradiction].
    + simpl. destruct (decide (x = s)); [contradiction|reflexivity].
  - (* Fun *) destruct (decide (x = s)) as [E|E].
    + subst s. destruct (decide (x = x)); [reflexivity|contradiction].
    + simpl. destruct (decide (x = s)); [contradiction|exact IHe].
  - (* App *) rewrite IHe1, IHe2. reflexivity.
  - (* Unit *) reflexivity.
  - (* Pair *) rewrite IHe1, IHe2. reflexivity.
  - (* LetPair *) rewrite IHe1, IHe2. reflexivity.
  - (* Sum *) exact IHe.
  - (* MatchSum *) rewrite IHe.
    assert (Hle : fin_max (fun i => var_budget x (subst x a (e0 i))) <= 0).
    { apply fin_max_le. intro i. rewrite H. lia. }
    lia.
  - (* ForkBarrier *) exact IHe.
  - (* NewLock *) exact IHe.
  - (* ForkLock *) rewrite IHe1, IHe2. reflexivity.
  - (* Acquire *) exact IHe.
  - (* Release *) rewrite IHe1, IHe2. reflexivity.
  - (* Wait *) exact IHe.
  - (* Drop *) exact IHe.
Qed.

Lemma tokEL_matchsum_inv beta Delta n e es C
    (H : tokEL beta Delta (MatchSum n e es) C) :
  exists Cs Cb Cbs,
    C = tc_add Cs Cb /\
    tokEL beta Delta e Cs /\
    (forall i, tokEL beta Delta (es i) (Cbs i)) /\
    (forall i, tc_le (Cbs i) Cb) /\
    (n = 0 -> Cb = tc_zero).
Proof.
  inversion H as
    [ | | | | | | | | Delta0 n0 e0 es0 Cs0 Cb0 Cbs0 H1 H2 H3 H4
    | | | | | | | ]; subst.
  match goal with
  | E : existT _ ?f = existT _ ?g |- _ =>
      apply (inj_pair2_eq_dec nat Nat.eq_dec) in E; subst f
  end.
  eexists Cs0, Cb0, Cbs0. split; [reflexivity|].
  split; [exact H1|].
  split; [exact H2|].
  split; [exact H3| exact H4].
Qed.

Lemma tokEL_app_inv beta Delta e1 e2 C
    (H : tokEL beta Delta (App e1 e2) C) :
  exists C1 C2, C = tc_add C1 C2 /\
    tokEL beta Delta e1 C1 /\ tokEL beta Delta e2 C2.
Proof. inversion H; subst; eauto. Qed.

Lemma tokEL_pair_inv beta Delta e1 e2 C
    (H : tokEL beta Delta (Pair e1 e2) C) :
  exists C1 C2, C = tc_add C1 C2 /\
    tokEL beta Delta e1 C1 /\ tokEL beta Delta e2 C2.
Proof. inversion H; subst; eauto. Qed.

Lemma tokEL_letpair_inv beta Delta e1 e2 C
    (H : tokEL beta Delta (LetPair e1 e2) C) :
  exists C1 C2, C = tc_add C1 C2 /\
    tokEL beta Delta e1 C1 /\ tokEL beta Delta e2 C2.
Proof. inversion H; subst; eauto. Qed.

Lemma tokEL_sum_inv beta Delta n e C
    (H : tokEL beta Delta (Sum n e) C) : tokEL beta Delta e C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokVL_funv_inv beta x e C (H : tokVL beta (FunV x e) C) :
  tokEL beta tenv_zero e C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokVL_pairv_inv beta v1 v2 C (H : tokVL beta (PairV v1 v2) C) :
  exists C1 C2, C = tc_add C1 C2 /\
    tokVL beta v1 C1 /\ tokVL beta v2 C2.
Proof. inversion H; subst; eauto. Qed.

Lemma tokVL_sumv_inv beta n v C (H : tokVL beta (SumV n v) C) :
  tokVL beta v C.
Proof. inversion H; subst; assumption. Qed.

Lemma tc_le_add_comm C1 C2 : tc_le (tc_add C1 C2) (tc_add C2 C1).
Proof. unfold tc_le, tc_add. simpl. split; intros; lia. Qed.

Lemma tc_le_add_rearrange_let Ce C1 C2 :
  tc_le (tc_add (tc_add Ce C1) C2) (tc_add (tc_add C1 C2) Ce).
Proof. unfold tc_le, tc_add. simpl. split; intros; lia. Qed.

Lemma tenv_eqv_bind_zero_zero x :
  tenv_eqv (tenv_bind tenv_zero x) tenv_zero.
Proof.
  intro y. unfold tenv_bind, tenv_zero.
  destruct (decide (y = x)); reflexivity.
Qed.

Lemma tokEL_tenv_update_irrel beta Delta x C e Ctok :
  var_budget x e = 0 ->
  tokEL beta (tenv_update Delta x C) e Ctok ->
  tokEL beta Delta e Ctok.
Proof.
  revert Delta Ctok.
  induction e; intros Delta Ctok Hvb Htok; inversion Htok; subst; simpl in Hvb.
  - (* Val *) econstructor. assumption.
  - (* Var *) destruct (decide (x = s)) as [E|E].
    + subst s. exfalso. revert Hvb. destruct (decide (x = x)); discriminate.
    + econstructor. symmetry.
      rewrite tenv_update_neq.
      * reflexivity.
      * intro Hxs. apply E. symmetry. exact Hxs.
  - (* Fun *) destruct (decide (x = s)) as [E|E].
    + subst s. econstructor.
      apply (tokEL_tenv_eqv beta
               (tenv_bind (tenv_update Delta x C) x)
               (tenv_bind Delta x) e Ctok).
      * apply tenv_bind_update_same.
      * exact H3.
    + econstructor.
      apply IHe with (Delta := tenv_bind Delta s).
      * simpl in Hvb. destruct (decide (x = s)); [contradiction|exact Hvb].
      * apply (tokEL_tenv_eqv beta
                 (tenv_bind (tenv_update Delta x C) s)
                 (tenv_update (tenv_bind Delta s) x C) e Ctok).
        -- apply tenv_bind_update_neq. intro Hxs. apply E. symmetry. exact Hxs.
        -- exact H3.
  - (* App *)
    assert (Hvb1 : var_budget x e1 = 0) by lia.
    assert (Hvb2 : var_budget x e2 = 0) by lia.
    econstructor.
    + apply IHe1; assumption.
    + apply IHe2; assumption.
  - (* Unit *) econstructor.
  - (* Pair *)
    assert (Hvb1 : var_budget x e1 = 0) by lia.
    assert (Hvb2 : var_budget x e2 = 0) by lia.
    econstructor.
    + apply IHe1; assumption.
    + apply IHe2; assumption.
  - (* LetPair *)
    assert (Hvb1 : var_budget x e1 = 0) by lia.
    assert (Hvb2 : var_budget x e2 = 0) by lia.
    econstructor.
    + apply IHe1; assumption.
    + apply IHe2; assumption.
  - (* Sum *) econstructor. apply IHe; assumption.
  - (* MatchSum *)
    apply (inj_pair2_eq_dec nat Nat.eq_dec) in H2. subst es0.
    match goal with
    | H : var_budget x ?escr + fin_max ?f = 0 |- _ =>
        assert (Hvb0 : var_budget x escr = 0) by lia;
        assert (Hvbi : forall i, f i = 0)
          by (intro i; pose proof (fin_max_ge f i); lia)
    end.
    eapply TLE_MatchSum with (Cs := Cs) (Cb := Cb) (Cbs := Cbs).
    + apply IHe; assumption.
    + intro i. eapply H.
      * apply Hvbi.
      * match goal with
        | Hb : forall j, tokEL beta (tenv_update Delta x C) (e0 j) (Cbs j) |- _ =>
            exact (Hb i)
        end.
    + exact H7.
    + exact H8.
  - (* ForkBarrier *) econstructor. apply IHe; assumption.
  - (* NewLock *) econstructor. apply IHe; assumption.
  - (* ForkLock *)
    assert (Hvb1 : var_budget x e1 = 0) by lia.
    assert (Hvb2 : var_budget x e2 = 0) by lia.
    econstructor.
    + apply IHe1; assumption.
    + apply IHe2; assumption.
  - (* Acquire *) econstructor. apply IHe; assumption.
  - (* Release *)
    assert (Hvb1 : var_budget x e1 = 0) by lia.
    assert (Hvb2 : var_budget x e2 = 0) by lia.
    econstructor.
    + apply IHe1; assumption.
    + apply IHe2; assumption.
  - (* Wait *) econstructor. apply IHe; assumption.
  - (* Drop *) econstructor. apply IHe; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Beta substitution under the precisely identified side condition.   *)
(* ------------------------------------------------------------------ *)

Lemma tokEL_beta_subst beta x body a C1 C2
    (Hbody : tokEL beta tenv_zero body C1)
    (Ha : tokVL beta a C2)
    (Hsafe : var_budget x body <= 1 \/ C2 = tc_zero) :
  exists C',
    tokEL beta tenv_zero (subst x a body) C' /\
    tc_le C' (tc_add C1 C2).
Proof.
  destruct Hsafe as [Hlin|Hz].
  - destruct (tokEL_subst_linear_bound beta x a C2 body tenv_zero C1
                Ha Hlin Hbody) as (C' & Ht & Hle).
    exists C'. split; [|exact Hle].
    apply (tokEL_tenv_update_irrel beta tenv_zero x C2
             (subst x a body) C').
    + apply var_budget_subst_same.
    + exact Ht.
  - rewrite Hz in Ha.
    pose proof (tokEL_subst_zero beta x a body Ha tenv_zero C1
                  eq_refl Hbody) as Ht.
    exists C1. split.
    + apply (tokEL_tenv_update_irrel beta tenv_zero x tc_zero
               (subst x a body) C1).
      * apply var_budget_subst_same.
      * exact Ht.
    + apply tc_le_add_l.
Qed.

(* ------------------------------------------------------------------ *)
(* Direct pure steps (at the redex itself).                           *)
(*                                                                    *)
(* [Hbeta] is the only extra condition.  It says that every beta      *)
(* redex hidden in the term has a safe argument: either the function  *)
(* body uses its argument at most once, or the argument carries no    *)
(* token.  This is exactly the condition that the unrefined runtime   *)
(* [cv]/[wt] rules do not provide.                                    *)
(* ------------------------------------------------------------------ *)

Lemma tokEL_pure_step_direct beta e e' C
    (Htok : tokEL beta tenv_zero e C)
    (Hstep : pure_step e e')
    (Hbeta : forall x body a C1 C2,
        e = App (Val (FunV x body)) (Val a) ->
        tokEL beta tenv_zero body C1 ->
        tokVL beta a C2 ->
        var_budget x body <= 1 \/ C2 = tc_zero) :
  exists C', tokEL beta tenv_zero e' C' /\ tc_le C' C.
Proof.
  inversion Hstep; subst.
  - (* Fun *) inversion Htok; subst.
    exists C. split.
    + apply TLE_Val, TVL_FunV.
      apply (tokEL_tenv_eqv beta (tenv_bind tenv_zero x) tenv_zero
               e0 C).
      * apply tenv_eqv_bind_zero_zero.
      * match goal with
        | Hb : tokEL beta (tenv_bind tenv_zero x) e0 C |- _ => exact Hb
        end.
    + apply tc_le_refl.
  - (* beta *) destruct (tokEL_app_inv beta tenv_zero
                  (Val (FunV x e0)) (Val a) C Htok)
      as (C1 & C2 & E & H1 & H2). subst C.
    apply tokEL_val_inv in H1.
    apply tokVL_funv_inv in H1.
    apply tokEL_val_inv in H2.
    destruct (Hbeta x e0 a C1 C2 eq_refl H1 H2) as [Hlin|Hz].
    + destruct (tokEL_beta_subst beta x e0 a C1 C2 H1 H2 (or_introl Hlin))
        as (C' & Ht & Hle).
      exists C'. split; assumption.
    + destruct (tokEL_beta_subst beta x e0 a C1 C2 H1 H2 (or_intror Hz))
        as (C' & Ht & Hle).
      exists C'. split; assumption.
  - (* Unit *) inversion Htok; subst.
    exists tc_zero. split; [apply TLE_Val, TVL_Unit|apply tc_le_refl].
  - (* Pair *) destruct (tokEL_pair_inv beta tenv_zero
                  (Val v1) (Val v2) C Htok)
      as (C1 & C2 & E & H1 & H2). subst C.
    apply tokEL_val_inv in H1. apply tokEL_val_inv in H2.
    exists (tc_add C1 C2). split.
    + apply TLE_Val, TVL_Pair; assumption.
    + apply tc_le_refl.
  - (* LetPair *)
    destruct (tokEL_letpair_inv beta tenv_zero
                (Val (PairV v1 v2)) e0 C Htok)
      as (C12 & Ce & E & H1 & H2). subst C.
    apply tokEL_val_inv in H1.
    destruct (tokVL_pairv_inv beta v1 v2 C12 H1)
      as (C1 & C2 & E12 & Hv1 & Hv2). subst C12.
    exists (tc_add (tc_add Ce C1) C2). split.
    + apply TLE_App.
      * apply TLE_App; [exact H2|apply TLE_Val; exact Hv1].
      * apply TLE_Val; exact Hv2.
    + apply tc_le_add_rearrange_let.
  - (* Sum *) apply tokEL_sum_inv in Htok.
    apply tokEL_val_inv in Htok.
    exists C. split.
    + apply TLE_Val, TVL_Sum. exact Htok.
    + apply tc_le_refl.
  - (* MatchSum *)
    destruct (tokEL_matchsum_inv beta tenv_zero n
                (Val (SumV i v)) es C Htok)
      as (Cs & Cb & Cbs & E & Hs & Hbranches & Hle & Hzero).
    subst C.
    apply tokEL_val_inv in Hs.
    apply tokVL_sumv_inv in Hs.
    exists (tc_add (Cbs i) Cs). split.
    + apply TLE_App.
      * exact (Hbranches i).
      * apply TLE_Val. exact Hs.
    + apply (tc_le_trans (tc_add (Cbs i) Cs) (tc_add Cb Cs)
               (tc_add Cs Cb)).
      * apply tc_le_add_mono; [apply Hle|apply tc_le_refl].
      * apply tc_le_add_comm.
Qed.

(* ------------------------------------------------------------------ *)
(* Context decomposition and contextual replacement.                  *)
(*                                                                    *)
(* The continuation carried by [tokEL_ctx1_hole] is essential: the    *)
(* token grammar is not context-deterministic (the MatchSum upper     *)
(* bound may be enlarged), so we must rebuild against the very hole   *)
(* context that occurs in the given derivation, not an arbitrary one. *)
(* ------------------------------------------------------------------ *)

Lemma tokEL_forklock_inv beta Delta e1 e2 C
    (H : tokEL beta Delta (ForkLock e1 e2) C) :
  exists C1 C2, C = tc_add C1 C2 /\
    tokEL beta Delta e1 C1 /\ tokEL beta Delta e2 C2.
Proof. inversion H; subst; eauto. Qed.

Lemma tokEL_forkbarrier_inv beta Delta e C
    (H : tokEL beta Delta (ForkBarrier e) C) : tokEL beta Delta e C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokEL_newlock_inv beta Delta e C
    (H : tokEL beta Delta (NewLock e) C) : tokEL beta Delta e C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokEL_acquire_inv beta Delta e C
    (H : tokEL beta Delta (Acquire e) C) : tokEL beta Delta e C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokEL_wait_inv beta Delta e C
    (H : tokEL beta Delta (Wait e) C) : tokEL beta Delta e C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokEL_drop_inv beta Delta e C
    (H : tokEL beta Delta (Drop e) C) : tokEL beta Delta e C.
Proof. inversion H; subst; assumption. Qed.

Lemma tokEL_ctx1_hole beta Delta k (Hk : ctx1 k) e C
    (H : tokEL beta Delta (k e) C) :
  exists Ce,
    tokEL beta Delta e Ce /\
    tc_le Ce C /\
    (forall e' Ce', tokEL beta Delta e' Ce' -> tc_le Ce' Ce ->
       exists C', tokEL beta Delta (k e') C' /\ tc_le C' C).
Proof.
  revert e C H.
  induction Hk; intros ee C H; simpl in H.
  - (* App left *)
    destruct (tokEL_app_inv beta Delta ee e C H) as (C1 & C2 & E & H1 & H2).
    subst C. exists C1. split; [exact H1|]. split; [apply tc_le_add_l|].
    intros e' Ce' He' Hle'. exists (tc_add Ce' C2). split.
    + econstructor; [exact He'|exact H2].
    + apply tc_le_add_mono; [exact Hle'|apply tc_le_refl].
  - (* App right *)
    destruct (tokEL_app_inv beta Delta e ee C H) as (C1 & C2 & E & H1 & H2).
    subst C. exists C2. split; [exact H2|]. split; [apply tc_le_add_r|].
    intros e' Ce' He' Hle'. exists (tc_add C1 Ce'). split.
    + econstructor; [exact H1|exact He'].
    + apply tc_le_add_mono; [apply tc_le_refl|exact Hle'].
  - (* Pair left *)
    destruct (tokEL_pair_inv beta Delta ee e C H) as (C1 & C2 & E & H1 & H2).
    subst C. exists C1. split; [exact H1|]. split; [apply tc_le_add_l|].
    intros e' Ce' He' Hle'. exists (tc_add Ce' C2). split.
    + econstructor; [exact He'|exact H2].
    + apply tc_le_add_mono; [exact Hle'|apply tc_le_refl].
  - (* Pair right *)
    destruct (tokEL_pair_inv beta Delta e ee C H) as (C1 & C2 & E & H1 & H2).
    subst C. exists C2. split; [exact H2|]. split; [apply tc_le_add_r|].
    intros e' Ce' He' Hle'. exists (tc_add C1 Ce'). split.
    + econstructor; [exact H1|exact He'].
    + apply tc_le_add_mono; [apply tc_le_refl|exact Hle'].
  - (* LetPair *)
    destruct (tokEL_letpair_inv beta Delta ee e C H) as (C1 & C2 & E & H1 & H2).
    subst C. exists C1. split; [exact H1|]. split; [apply tc_le_add_l|].
    intros e' Ce' He' Hle'. exists (tc_add Ce' C2). split.
    + econstructor; [exact He'|exact H2].
    + apply tc_le_add_mono; [exact Hle'|apply tc_le_refl].
  - (* Sum *) exists C. split.
    + apply (tokEL_sum_inv beta Delta i ee C H).
    + split; [apply tc_le_refl|].
      intros e' Ce' He' Hle'. exists Ce'. split.
      * econstructor. exact He'.
      * exact Hle'.
  - (* MatchSum *)
    destruct (tokEL_matchsum_inv beta Delta n ee es C H)
      as (Cs & Cb & Cbs & E & Hs & Hbranches & Hle & Hzero).
    subst C. exists Cs. split; [exact Hs|]. split; [apply tc_le_add_l|].
    intros e' Ce' He' Hle'. exists (tc_add Ce' Cb). split.
    + eapply TLE_MatchSum with (Cs := Ce') (Cb := Cb) (Cbs := Cbs).
      * exact He'.
      * exact Hbranches.
      * exact Hle.
      * exact Hzero.
    + apply tc_le_add_mono; [exact Hle'|apply tc_le_refl].
  - (* ForkBarrier *) exists C. split.
    + apply (tokEL_forkbarrier_inv beta Delta ee C H).
    + split; [apply tc_le_refl|].
      intros e' Ce' He' Hle'. exists Ce'. split.
      * econstructor. exact He'.
      * exact Hle'.
  - (* NewLock *) exists C. split.
    + apply (tokEL_newlock_inv beta Delta ee C H).
    + split; [apply tc_le_refl|].
      intros e' Ce' He' Hle'. exists Ce'. split.
      * econstructor. exact He'.
      * exact Hle'.
  - (* ForkLock left *)
    destruct (tokEL_forklock_inv beta Delta ee e C H) as (C1 & C2 & E & H1 & H2).
    subst C. exists C1. split; [exact H1|]. split; [apply tc_le_add_l|].
    intros e' Ce' He' Hle'. exists (tc_add Ce' C2). split.
    + econstructor; [exact He'|exact H2].
    + apply tc_le_add_mono; [exact Hle'|apply tc_le_refl].
  - (* ForkLock right *)
    destruct (tokEL_forklock_inv beta Delta e ee C H) as (C1 & C2 & E & H1 & H2).
    subst C. exists C2. split; [exact H2|]. split; [apply tc_le_add_r|].
    intros e' Ce' He' Hle'. exists (tc_add C1 Ce'). split.
    + econstructor; [exact H1|exact He'].
    + apply tc_le_add_mono; [apply tc_le_refl|exact Hle'].
  - (* Acquire *) exists C. split.
    + apply (tokEL_acquire_inv beta Delta ee C H).
    + split; [apply tc_le_refl|].
      intros e' Ce' He' Hle'. exists Ce'. split.
      * econstructor. exact He'.
      * exact Hle'.
  - (* Release left *)
    destruct (tokEL_release_inv beta Delta ee e C H) as (C1 & C2 & E & H1 & H2).
    subst C. exists C1. split; [exact H1|]. split; [apply tc_le_add_l|].
    intros e' Ce' He' Hle'. exists (tc_add Ce' C2). split.
    + econstructor; [exact He'|exact H2].
    + apply tc_le_add_mono; [exact Hle'|apply tc_le_refl].
  - (* Release right *)
    destruct (tokEL_release_inv beta Delta e ee C H) as (C1 & C2 & E & H1 & H2).
    subst C. exists C2. split; [exact H2|]. split; [apply tc_le_add_r|].
    intros e' Ce' He' Hle'. exists (tc_add C1 Ce'). split.
    + econstructor; [exact H1|exact He'].
    + apply tc_le_add_mono; [apply tc_le_refl|exact Hle'].
  - (* Wait *) exists C. split.
    + apply (tokEL_wait_inv beta Delta ee C H).
    + split; [apply tc_le_refl|].
      intros e' Ce' He' Hle'. exists Ce'. split.
      * econstructor. exact He'.
      * exact Hle'.
  - (* Drop *) exists C. split.
    + apply (tokEL_drop_inv beta Delta ee C H).
    + split; [apply tc_le_refl|].
      intros e' Ce' He' Hle'. exists Ce'. split.
      * econstructor. exact He'.
      * exact Hle'.
Qed.

Lemma tokEL_ctx_hole beta Delta k (Hk : ctx k) e C
    (H : tokEL beta Delta (k e) C) :
  exists Ce,
    tokEL beta Delta e Ce /\
    tc_le Ce C /\
    (forall e' Ce', tokEL beta Delta e' Ce' -> tc_le Ce' Ce ->
       exists C', tokEL beta Delta (k e') C' /\ tc_le C' C).
Proof.
  revert e C H.
  induction Hk as [| k1 k2 Hk1 Hk2 IH2].
  - (* id *) intros e C H. exists C. split; [exact H|].
    split; [apply tc_le_refl|].
    intros e' Ce' He' Hle'. exists Ce'. split; assumption.
  - (* composition *) intros e C H. simpl in H.
    destruct (tokEL_ctx1_hole beta Delta k1 Hk1 (k2 e) C H) as
      (Ck2 & Hk2e & Hle1 & Reb1).
    destruct (IH2 e Ck2 Hk2e) as
      (Ce & He & Hle2 & Reb2).
    exists Ce. split; [exact He|]. split.
    + eapply tc_le_trans; [exact Hle2|exact Hle1].
    + intros e' Ce' He' Hle'.
      destruct (Reb2 e' Ce' He' Hle') as (C2' & Hk2e' & Hle2').
      destruct (Reb1 (k2 e') C2' Hk2e' Hle2') as (C' & Hk1e' & Hle1').
      exists C'. split; [exact Hk1e'|exact Hle1'].
Qed.

(* ------------------------------------------------------------------ *)
(* Pure-step preservation through an arbitrary evaluation context.    *)
(* ------------------------------------------------------------------ *)

Lemma tokEL_pure_step_ctx beta k e e' C
    (Hk : ctx k)
    (Htok : tokEL beta tenv_zero (k e) C)
    (Hstep : pure_step e e')
    (Hbeta : forall x body a C1 C2,
        e = App (Val (FunV x body)) (Val a) ->
        tokEL beta tenv_zero body C1 ->
        tokVL beta a C2 ->
        var_budget x body <= 1 \/ C2 = tc_zero) :
  exists C', tokEL beta tenv_zero (k e') C' /\ tc_le C' C.
Proof.
  destruct (tokEL_ctx_hole beta tenv_zero k Hk e C Htok) as
    (Ce & He & HleC & Reb).
  destruct (tokEL_pure_step_direct beta e e' Ce He Hstep Hbeta) as
    (Ce' & He' & Hle).
  destruct (Reb e' Ce' He' Hle) as (C' & Hk' & Hle').
  exists C'. split; [exact Hk'|exact Hle'].
Qed.

Print Assumptions tokEL_tenv_update_irrel.
Print Assumptions tokEL_matchsum_inv.
Print Assumptions tokEL_beta_subst.
Print Assumptions tokEL_pure_step_direct.
Print Assumptions tokEL_ctx1_hole.
Print Assumptions tokEL_ctx_hole.
Print Assumptions tokEL_pure_step_ctx.

(* ------------------------------------------------------------------ *)
(* The per-thread token invariant, and its preservation by a pure     *)
(* step.  The extra [pure_beta_safe] premise is exactly the missing    *)
(* beta condition; see the report.                                    *)
(* ------------------------------------------------------------------ *)

Definition pure_beta_safe beta (e : expr) : Prop :=
  forall x body a C1 C2,
    e = App (Val (FunV x body)) (Val a) ->
    tokEL beta tenv_zero body C1 ->
    tokVL beta a C2 ->
    var_budget x body <= 1 \/ C2 = tc_zero.

Definition token_single_threads_L beta (ρ : cfg) : Prop :=
  forall i e, ρ !! i = Some (Thread e) ->
    exists C, tokEL beta tenv_zero e C /\ index_single C.

Lemma pure_step_token_single_threads_L beta i k e e'
    (Hk : ctx k)
    (Hstep : pure_step e e')
    (Hbeta : pure_beta_safe beta e)
    (Hinv : token_single_threads_L beta {[ i := Thread (k e) ]}) :
  token_single_threads_L beta {[ i := Thread (k e') ]}.
Proof.
  intros j e2 Hlook.
  apply lookup_singleton_Some in Hlook.
  destruct Hlook as [Hij Hbody].
  injection Hbody as Hb. rewrite <- Hb.
  assert (Hsrc : ({[ i := Thread (k e) ]} : cfg) !! i =
                   Some (Thread (k e))).
  { apply lookup_singleton_Some. split; reflexivity. }
  destruct (Hinv i (k e) Hsrc) as (C & Htok & Hsingle).
  destruct (tokEL_pure_step_ctx beta k e e' C Hk Htok Hstep Hbeta)
    as (C' & Htok' & Hle).
  exists C'. split; [exact Htok'|].
  apply (index_single_mono C' C Hle Hsingle).
Qed.

(* ------------------------------------------------------------------ *)
(* Source-initial configurations satisfy the token invariant.         *)
(* ------------------------------------------------------------------ *)

Definition source_typed_threads_L (ρ : cfg) : Prop :=
  forall i e, ρ !! i = Some (Thread e) -> typed (∅ : env) e UnitT.

Lemma index_single_zero_L : index_single tc_zero.
Proof.
  intro n. unfold lock_count, tc_zero. simpl. lia.
Qed.

Theorem token_single_threads_L_of_source_typed beta ρ
    (H : source_typed_threads_L ρ) :
  token_single_threads_L beta ρ.
Proof.
  intros i e Hi.
  destruct (typed_to_wtKL (∅ : env) e UnitT (H i e Hi)
              (∅ : gmap nat type) beta) as [Hwt Htok].
  exists tc_zero. split; [exact Htok | exact index_single_zero_L].
Qed.

(* ------------------------------------------------------------------ *)
(* Release payload safety, now for the redesigned grammar.            *)
(* ------------------------------------------------------------------ *)

Lemma release_payload_safe_of_token_single_L beta k n v C
    (Hk : ctx k)
    (Htok : tokEL beta tenv_zero
              (k (Release (Val (LockV n)) (Val v))) C)
    (Hsingle : index_single C) :
  n ∉ val_refs v.
Proof.
  destruct (tokEL_ctx_hole beta tenv_zero k Hk
              (Release (Val (LockV n)) (Val v)) C Htok)
    as (Ce & He & Hle & Reb).
  assert (Hsingle_e : index_single Ce).
  { apply (index_single_mono Ce C); [apply Hle|exact Hsingle]. }
  destruct (tokEL_release_inv beta tenv_zero
              (Val (LockV n)) (Val v) Ce He)
    as (C1 & C2 & E & H1 & H2).
  apply (release_payload_token_free_L beta tenv_zero n v C1 C2).
  - rewrite <- E. exact He.
  - rewrite E in Hsingle_e. exact Hsingle_e.
Qed.

Print Assumptions pure_step_token_single_threads_L.
Print Assumptions token_single_threads_L_of_source_typed.
Print Assumptions release_payload_safe_of_token_single_L.

(* ------------------------------------------------------------------ *)
(* A machine-checked obstruction to unconditional beta preservation.  *)
(*                                                                    *)
(* The function body is typed under [tenv_zero], so both occurrences *)
(* of [x] carry no token in the source.  The argument nevertheless    *)
(* carries a lock token; beta duplication duplicates it twice.        *)
(* Thus [tokEL] plus [index_single] is not preserved by beta without  *)
(* the [pure_beta_safe] side condition.                               *)
(* ------------------------------------------------------------------ *)

Lemma beta_dup_source_tok beta x n lc :
  tokEL beta tenv_zero
    (App (Val (FunV x (Pair (Var x) (Var x)))) (Val (LockV n)))
    (tc_lock_one n lc).
Proof.
  eapply TLE_App with (C1 := tc_zero) (C2 := tc_lock_one n lc).
  - apply TLE_Val, TVL_FunV.
    eapply TLE_Pair with (C1 := tc_zero) (C2 := tc_zero).
    + apply TLE_Var. reflexivity.
    + apply TLE_Var. reflexivity.
  - apply TLE_Val, TVL_Lock.
Qed.

Lemma tokEL_pair_lockv_lock_count beta Delta n C
    (H : tokEL beta Delta (Pair (Val (LockV n)) (Val (LockV n))) C) :
  2 <= lock_count C n.
Proof.
  destruct (tokEL_pair_inv beta Delta (Val (LockV n))
              (Val (LockV n)) C H)
    as (C1 & C2 & E & H1 & H2). subst C.
  apply tokEL_val_inv in H1. apply tokEL_val_inv in H2.
  destruct (tokVL_lock_inv beta n C1 H1) as (lc1 & E1). subst C1.
  destruct (tokVL_lock_inv beta n C2 H2) as (lc2 & E2). subst C2.
  rewrite tc_add_lock_count, !lock_count_lock_one. lia.
Qed.

Lemma beta_dup_target_not_index_single beta n C
    (H : tokEL beta tenv_zero
           (Pair (Val (LockV n)) (Val (LockV n))) C) :
  ~ index_single C.
Proof.
  intro Hs.
  pose proof (tokEL_pair_lockv_lock_count beta tenv_zero n C H) as Hlow.
  unfold index_single in Hs. specialize (Hs n). lia.
Qed.

Print Assumptions beta_dup_source_tok.
Print Assumptions tokEL_pair_lockv_lock_count.
Print Assumptions beta_dup_target_not_index_single.

Lemma index_single_lock_one n lc : index_single (tc_lock_one n lc).
Proof.
  intro m. rewrite tc_lock_one_no_bar.
  destruct (decide (m = n)) as [->|H].
  - rewrite lock_count_lock_one. lia.
  - assert (Hz : lock_count (tc_lock_one n lc) m = 0).
    { unfold lock_count.
      rewrite (tc_lock_one_zero n lc m (Owner,Opened) (or_introl H)).
      rewrite (tc_lock_one_zero n lc m (Owner,Closed) (or_introl H)).
      rewrite (tc_lock_one_zero n lc m (Client,Opened) (or_introl H)).
      rewrite (tc_lock_one_zero n lc m (Client,Closed) (or_introl H)).
      lia. }
    rewrite Hz. lia.
Qed.

Theorem beta_dup_obstruction beta x n lc :
  tokEL beta tenv_zero
    (App (Val (FunV x (Pair (Var x) (Var x)))) (Val (LockV n)))
    (tc_lock_one n lc) /\
  index_single (tc_lock_one n lc) /\
  (forall C,
      tokEL beta tenv_zero
        (Pair (Val (LockV n)) (Val (LockV n))) C ->
      ~ index_single C).
Proof.
  split; [apply beta_dup_source_tok|].
  split; [apply index_single_lock_one|].
  intros C H. exact (beta_dup_target_not_index_single beta n C H).
Qed.

Print Assumptions index_single_lock_one.
Print Assumptions beta_dup_obstruction.

Lemma empty_token_single_threads_L beta :
  token_single_threads_L beta (∅ : cfg).
Proof.
  intros i e H. simpl in H. discriminate.
Qed.

Print Assumptions empty_token_single_threads_L.
(* ================================================================== *)
(* Target theorem.                                                     *)
(*                                                                    *)
(* It remains to establish, for every configuration rho reached from   *)
(* a typed closed source, the five invariants consumed by             *)
(* [fully_reachable_of_invariants]: threads_typed for some store       *)
(* typing L, cap_inventory, wait_targets_live, ref_pair_ok and         *)
(* ref_forest.                                                         *)
(* ================================================================== *)

Theorem typed_full_reachability e ρ :
  typed ∅ e UnitT -> steps {[ 0 := Thread e ]} ρ -> fully_reachable ρ.

