(** System F parametricity benchmark, Hard variant.
    Features: nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNondeterminismHardTask.

Definition atom := nat.

Declare Scope systemf_scope.
Delimit Scope systemf_scope with systemf.
Open Scope systemf_scope.

Declare Custom Entry systemf_ty.
Declare Custom Entry systemf_tm.

Inductive ty : Type :=
  | Ty_BVar : nat -> ty
  | Ty_FVar : atom -> ty

  | Ty_Arrow : ty -> ty -> ty

  | Ty_All : ty -> ty.

Notation "T" := T
  (in custom systemf_ty at level 0, T constr at level 0) : systemf_scope.
Notation "<{{ T }}>" := T
  (T custom systemf_ty at level 200) : systemf_scope.
Notation "( T )" := T
  (in custom systemf_ty at level 0, T custom systemf_ty) : systemf_scope.
Notation "$( T )" := T
  (in custom systemf_ty at level 0, T constr) : systemf_scope.
Notation "'fvar' X" := (Ty_FVar X)
  (in custom systemf_ty at level 0, X constr at level 0) : systemf_scope.
Notation "T1 '->' T2" := (Ty_Arrow T1 T2)
  (in custom systemf_ty at level 99, right associativity) : systemf_scope.
Notation "'forall' ',' T" := (Ty_All T)
  (in custom systemf_ty at level 200,
   T custom systemf_ty at level 200,
   right associativity) : systemf_scope.

Inductive tm : Type :=
  | tm_bvar : nat -> tm
  | tm_fvar : atom -> tm
  | tm_abs : ty -> tm -> tm
  | tm_app : tm -> tm -> tm

  | tm_tabs : tm -> tm

  | tm_tapp : tm -> ty -> tm
  | tm_choice : tm -> tm -> tm.

Notation "t" := t
  (in custom systemf_tm at level 0, t constr at level 0) : systemf_scope.
Notation "<{ t }>" := t
  (t custom systemf_tm at level 200) : systemf_scope.
Notation "( t )" := t
  (in custom systemf_tm at level 0, t custom systemf_tm) : systemf_scope.
Notation "$( t )" := t
  (in custom systemf_tm at level 0, t constr, only parsing) : systemf_scope.
Notation "'bvar' n" := (tm_bvar n)
  (in custom systemf_tm at level 0, n constr at level 0) : systemf_scope.
Notation "'fvar' x" := (tm_fvar x)
  (in custom systemf_tm at level 0, x constr at level 0) : systemf_scope.
Notation "t1 t2" := (tm_app t1 t2)
  (in custom systemf_tm at level 10, left associativity) : systemf_scope.
Notation "'lambda' ':' T ',' t" := (tm_abs T t)
  (in custom systemf_tm at level 200,
   T custom systemf_ty,
   t custom systemf_tm at level 200,
   left associativity) : systemf_scope.
Notation "'Lambda' ',' t" := (tm_tabs t)
  (in custom systemf_tm at level 200,
   t custom systemf_tm at level 200,
   left associativity) : systemf_scope.
Notation "t '[' T ']'" := (tm_tapp t T)
  (in custom systemf_tm at level 10,
   t custom systemf_tm,
   T custom systemf_ty) : systemf_scope.

Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm at level 200) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  end.

Definition open_ty (T U : ty) : ty := open_ty_rec 0 U T.

Fixpoint open_tm_rec (k : nat) (u t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs T (open_tm_rec (S k) u t1)
  | tm_app t1 t2 => tm_app (open_tm_rec k u t1) (open_tm_rec k u t2)
  | tm_tabs t1 => tm_tabs (open_tm_rec k u t1)
  | tm_tapp t1 T => tm_tapp (open_tm_rec k u t1) T
  | tm_choice t1 t2 => tm_choice (open_tm_rec k u t1) (open_tm_rec k u t2)
  end.

Definition open_tm (t u : tm) : tm := open_tm_rec 0 u t.

Fixpoint open_tm_ty_rec (k : nat) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 =>
      tm_abs (open_ty_rec k U T) (open_tm_ty_rec k U t1)
  | tm_app t1 t2 =>
      tm_app (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  | tm_tabs t1 => tm_tabs (open_tm_ty_rec (S k) U t1)
  | tm_tapp t1 T =>
      tm_tapp (open_tm_ty_rec k U t1) (open_ty_rec k U T)
  | tm_choice t1 t2 => tm_choice (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2)
  end.

Definition open_tm_ty (t : tm) (U : ty) : tm :=
  open_tm_ty_rec 0 U t.

Fixpoint ty_subst (X : atom) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then U else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst X U T1) (ty_subst X U T2)
  | Ty_All T1 => Ty_All (ty_subst X U T1)
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
  | tm_choice t1 t2 => tm_choice (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
  | tm_choice t1 t2 => tm_choice (tm_subst x s t1) (tm_subst x s t2)
  end.

Inductive lc_ty_at : nat -> ty -> Prop :=
  | lc_ty_bvar : forall k i,
      i < k ->
      lc_ty_at k (Ty_BVar i)
  | lc_ty_fvar : forall k X,
      lc_ty_at k (Ty_FVar X)
  | lc_ty_arrow : forall k T1 T2,
      lc_ty_at k T1 ->
      lc_ty_at k T2 ->
      lc_ty_at k (Ty_Arrow T1 T2)
  | lc_ty_all : forall k T,
      lc_ty_at (S k) T ->
      lc_ty_at k (Ty_All T).

Definition locally_closed_ty (T : ty) : Prop := lc_ty_at 0 T.

Inductive lc_tm_at : nat -> nat -> tm -> Prop :=
  | lc_tm_bvar : forall K k i,
      i < k ->
      lc_tm_at K k (tm_bvar i)
  | lc_tm_fvar : forall K k x,
      lc_tm_at K k (tm_fvar x)
  | lc_tm_abs : forall K k T t,
      lc_ty_at K T ->
      lc_tm_at K (S k) t ->
      lc_tm_at K k (tm_abs T t)
  | lc_tm_app : forall K k t1 t2,
      lc_tm_at K k t1 ->
      lc_tm_at K k t2 ->
      lc_tm_at K k (tm_app t1 t2)
  | lc_tm_tabs : forall K k t,
      lc_tm_at (S K) k t ->
      lc_tm_at K k (tm_tabs t)
  | lc_tm_tapp : forall K k t T,
      lc_tm_at K k t ->
      lc_ty_at K T ->
      lc_tm_at K k (tm_tapp t T)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t).

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T t v,
      locally_closed_tm (tm_abs T t) ->
      value v ->

      tm_app (tm_abs T t) v --> open_tm t v
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      locally_closed_tm t2 ->
      tm_app t1 t2 --> tm_app t1' t2

  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      tm_app v1 t2 --> tm_app v1 t2'
  | ST_TAppTabs :

      forall t T,
      locally_closed_tm (tm_tabs t) ->
      locally_closed_ty T ->
      tm_tapp (tm_tabs t) T --> open_tm_ty t T
  | ST_TApp : forall t t' T,
      t --> t' ->
      locally_closed_ty T ->
      tm_tapp t T --> tm_tapp t' T
  | ST_ChoiceLeft : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_choice t1 t2 --> t1
  | ST_ChoiceRight : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_choice t1 t2 --> t2
where "t1 '-->' t2" := (step t1 t2).

Definition ty_context := list atom.

Definition context := list (atom * ty).

Fixpoint lookup_context (x : atom) (Gamma : context) : option ty :=
  match Gamma with
  | [] => None
  | (y, T) :: Gamma' =>
      if Nat.eqb x y then Some T else lookup_context x Gamma'
  end.

Definition empty : context := [].

Definition update (Gamma : context) (x : atom) (T : ty) : context :=
  (x, T) :: Gamma.

Notation "x '|->' v ';' m" := (update m x v)
  (in custom systemf_tm at level 0,
   x constr at level 0,
   v custom systemf_ty,
   right associativity) : systemf_scope.
Notation "x '|->' v" := (update empty x v)
  (in custom systemf_tm at level 0,
   x constr at level 0,
   v custom systemf_ty) : systemf_scope.
Notation "'empty'" := empty
  (in custom systemf_tm) : systemf_scope.

Inductive wf_ty : ty_context -> ty -> Prop :=
  | WF_Var : forall Delta X,
      In X Delta ->
      wf_ty Delta (Ty_FVar X)
  | WF_Arrow : forall Delta T1 T2,
      wf_ty Delta T1 ->
      wf_ty Delta T2 ->
      wf_ty Delta (Ty_Arrow T1 T2)
  | WF_All :

      forall (L : list atom) Delta T,
      (forall X, ~ In X L ->
        wf_ty (X :: Delta) (open_ty T (Ty_FVar X))) ->
      wf_ty Delta (Ty_All T).

Inductive has_type : ty_context -> context -> tm -> ty -> Prop :=
  | T_Var : forall Delta Gamma x T,
      lookup_context x Gamma = Some T ->
      wf_ty Delta T ->
      has_type Delta Gamma (tm_fvar x) T
  | T_Abs : forall (L : list atom) Delta Gamma T1 t2 T2,
      wf_ty Delta T1 ->

      (forall x, ~ In x L ->
        has_type Delta <{ x |-> $(T1); Gamma }>
          (open_tm t2 (tm_fvar x)) T2) ->
      has_type Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)
  | T_App : forall Delta Gamma t1 t2 T1 T2,
      has_type Delta Gamma t1 (Ty_Arrow T1 T2) ->
      has_type Delta Gamma t2 T1 ->
      has_type Delta Gamma (tm_app t1 t2) T2
  | T_TAbs : forall (L : list atom) Delta Gamma t T,
      (forall X, ~ In X L ->
        has_type (X :: Delta) Gamma
          (open_tm_ty t (Ty_FVar X))
          (open_ty T (Ty_FVar X))) ->
      has_type Delta Gamma (tm_tabs t) (Ty_All T)
  | T_TApp : forall Delta Gamma t T U,
      has_type Delta Gamma t (Ty_All T) ->
      wf_ty Delta U ->
      has_type Delta Gamma (tm_tapp t U) (open_ty T U)
  | T_Choice : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma (tm_choice t1 t2) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).


Hint Constructors lc_ty_at lc_tm_at value : core.

(* ============================================================ *)
(* Free type variables of types and terms                       *)
(* ============================================================ *)

Fixpoint fvs_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fvs_ty T1 ++ fvs_ty T2
  | Ty_All T1 => fvs_ty T1
  end.

Fixpoint fvs_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T t1 => fvs_ty T ++ fvs_tm t1
  | tm_app t1 t2 => fvs_tm t1 ++ fvs_tm t2
  | tm_tabs t1 => fvs_tm t1
  | tm_tapp t1 T => fvs_tm t1 ++ fvs_ty T
  | tm_choice t1 t2 => fvs_tm t1 ++ fvs_tm t2
  end.

Fixpoint fvs_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => fvs_ty T ++ fvs_context Gamma'
  end.

Definition fresh_atom (L : list atom) : atom := S (list_max L).

Lemma In_list_max : forall L x, In x L -> x <= list_max L.
Proof.
  intros L x H. induction L as [|a l IH]; simpl in *; [contradiction|].
  unfold list_max in *. simpl in *.
  destruct H as [-> | H].
  - apply Nat.le_max_l.
  - apply Nat.le_trans with (fold_right max 0 l); auto.
    apply Nat.le_max_r.
Qed.

Lemma fresh_atom_notin : forall L, ~ In (fresh_atom L) L.
Proof.
  intros L H. apply In_list_max in H. unfold fresh_atom in H. lia.
Qed.

(* ============================================================ *)
(* Monotonicity of local closedness                             *)
(* ============================================================ *)

Lemma lc_ty_at_mono_S : forall k T, lc_ty_at k T -> lc_ty_at (S k) T.
Proof.
  intros k T H. induction H.
  - constructor. lia.
  - constructor.
  - constructor; assumption.
  - constructor. assumption.
Qed.

Lemma lc_ty_at_mono : forall k k', k <= k' -> forall T, lc_ty_at k T -> lc_ty_at k' T.
Proof.
  intros k k' H. induction H as [|m Hle IH]; intros T HT.
  - assumption.
  - apply lc_ty_at_mono_S. apply IH. assumption.
Qed.

Lemma lc_tm_at_mono_both : forall K K' k k' t,
  K <= K' -> k <= k' -> lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  intros K K' k k' t HK Hk H. revert K K' k k' HK Hk H.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros K K' k k' HK Hk H; inversion H; subst.
  - constructor. lia.
  - constructor.
  - constructor.
    + apply lc_ty_at_mono with (k := K); auto.
    + apply IH1 with (K := K) (k := S k); auto; lia.
  - constructor.
    + apply IH1 with (K := K) (k := k); auto; lia.
    + apply IH2 with (K := K) (k := k); auto; lia.
  - constructor. apply IH1 with (K := S K) (k := k); auto; lia.
  - constructor.
    + apply IH1 with (K := K) (k := k); auto; lia.
    + apply lc_ty_at_mono with (k := K); auto.
  - constructor.
    + apply IH1 with (K := K) (k := k); auto; lia.
    + apply IH2 with (K := K) (k := k); auto; lia.
Qed.

Lemma lc_tm_at_mono_K_S : forall K k t, lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H.
  eapply lc_tm_at_mono_both with (K := K) (K' := S K) (k := k) (k' := k); auto; lia.
Qed.

Lemma lc_tm_at_mono_k_S : forall K k t, lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H.
  eapply lc_tm_at_mono_both with (K := K) (K' := K) (k := k) (k' := S k); auto; lia.
Qed.

Lemma lc_tm_at_mono_K : forall K K', K <= K' -> forall k t, lc_tm_at K k t -> lc_tm_at K' k t.
Proof.
  intros K K' HK k t H.
  eapply lc_tm_at_mono_both with (K := K) (K' := K') (k := k) (k' := k); auto; lia.
Qed.

Lemma lc_tm_at_mono_k : forall k k', k <= k' -> forall K t, lc_tm_at K k t -> lc_tm_at K k' t.
Proof.
  intros k k' Hk K t H.
  eapply lc_tm_at_mono_both with (K := K) (K' := K) (k := k) (k' := k'); auto; lia.
Qed.

(* ============================================================ *)
(* Opening and local closedness of types                        *)
(* ============================================================ *)

Lemma lc_ty_open_rec : forall k U T,
  lc_ty_at 0 U -> lc_ty_at (S k) T -> lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k U T HU. revert k. induction T as [n|X|T1 IH1 T2 IH2|T1 IH1]; intros k HT.
  - simpl. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_at_mono with (k := 0); auto; lia.
    + apply Nat.eqb_neq in E. constructor. inversion HT. lia.
  - simpl. constructor.
  - simpl. inversion HT. constructor; auto.
  - simpl. inversion HT. constructor. apply IH1. assumption.
Qed.

Lemma lc_ty_open_rec_inv : forall k U T,
  lc_ty_at 0 U -> lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  intros k U T HU. revert k. induction T as [n|X|T1 IH1 T2 IH2|T1 IH1]; intros k H.
  - simpl in H. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + apply Nat.eqb_neq in E. inversion H. constructor. lia.
  - simpl in H. inversion H. constructor.
  - simpl in H. inversion H. constructor; auto.
  - simpl in H. inversion H. constructor. apply IH1 with (k := S k). assumption.
Qed.

Lemma open_ty_rec_lc_id : forall k U T,
  lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  intros k U T H. generalize dependent k.
  induction T as [n|X|T1 IH1 T2 IH2|T1 IH1]; intros k HT.
  - simpl. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. inversion HT. lia.
    + reflexivity.
  - reflexivity.
  - simpl. inversion HT. rewrite IH1, IH2; auto.
  - simpl. inversion HT. rewrite IH1 with (k := S k); auto.
Qed.

Lemma open_ty_lc_id : forall U T, lc_ty_at 0 T -> open_ty T U = T.
Proof. intros. apply open_ty_rec_lc_id. assumption. Qed.

(* ============================================================ *)
(* wf_ty and has_type imply local closedness                    *)
(* ============================================================ *)

Lemma wf_ty_lc_ty_at : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H as [Delta X Hin | Delta T1 H1 IH1 T2 H2 IH2 | L Delta T1 Hprem IHprem].
  - constructor.
  - constructor; assumption.
  - constructor.
    specialize (IHprem (fresh_atom L) (fresh_atom_notin L)).
    apply lc_ty_open_rec_inv with (k := 0) (U := Ty_FVar (fresh_atom L)) in IHprem.
    + simpl in IHprem. exact IHprem.
    + constructor.
Qed.

Lemma has_type_lc_ty : forall Delta Gamma t T, has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H. induction H as
    [Delta Gamma x T Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U Ht IHt HU
    | Delta Gamma t1 t2 T Ht1 IH1 Ht2 IH2].
  - eapply wf_ty_lc_ty_at; eassumption.
  - constructor.
    + eapply wf_ty_lc_ty_at; eassumption.
    + apply (IHbody (fresh_atom L) (fresh_atom_notin L)).
  - inversion IH1. assumption.
  - constructor.
    specialize (IHbody (fresh_atom L) (fresh_atom_notin L)).
    apply lc_ty_open_rec_inv with (k := 0) (U := Ty_FVar (fresh_atom L)) in IHbody.
    + simpl in IHbody. exact IHbody.
    + constructor.
  - inversion IHt. apply lc_ty_open_rec.
    + eapply wf_ty_lc_ty_at; eassumption.
    + assumption.
  - assumption.
Qed.

(* ============================================================ *)
(* Opening inversion for terms                                  *)
(* ============================================================ *)

Lemma lc_tm_open_rec_inv : forall K k u t,
  lc_tm_at K 0 u ->
  lc_tm_at K k (open_tm_rec k u t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k u t Hu H. revert Hu H. revert K k.
  induction t as
    [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros K k Hu H.
  - simpl in H. destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + apply Nat.eqb_neq in E. inversion H. constructor. lia.
  - simpl in H. inversion H. constructor.
  - simpl in H. inversion H. constructor.
    + assumption.
    + eapply IH1; eauto.
  - simpl in H. inversion H. constructor.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
  - simpl in H. inversion H. constructor.
    eapply IH1; eauto using lc_tm_at_mono_K.
  - simpl in H. inversion H. constructor.
    + eapply IH1; eauto.
    + assumption.
  - simpl in H. inversion H. constructor.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
Qed.

Lemma lc_tm_open_ty_rec_inv : forall K k U t,
  lc_ty_at 0 U ->
  lc_tm_at K k (open_tm_ty_rec K U t) ->
  lc_tm_at (S K) k t.
Proof.
  intros K k U t HU. revert K k. induction t as
    [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2]; intros K k H.
  - simpl in H. apply lc_tm_at_mono_K_S. assumption.
  - simpl in H. apply lc_tm_at_mono_K_S. assumption.
  - simpl in H. inversion H. constructor.
    + apply lc_ty_open_rec_inv with (k := K) (U := U); assumption.
    + apply IH1 with (K := K) (k := S k); auto.
  - simpl in H. inversion H. constructor.
    + apply IH1 with (K := K) (k := k); auto.
    + apply IH2 with (K := K) (k := k); auto.
  - simpl in H. inversion H. constructor.
    apply IH1 with (K := S K) (k := k); auto.
  - simpl in H. inversion H. constructor.
    + apply IH1 with (K := K) (k := k); auto.
    + apply lc_ty_open_rec_inv with (k := K) (U := U); assumption.
  - simpl in H. inversion H. constructor.
    + apply IH1 with (K := K) (k := k); auto.
    + apply IH2 with (K := K) (k := k); auto.
Qed.

Lemma lc_tm_open_ty_inv : forall U t,
  lc_ty_at 0 U ->
  lc_tm_at 0 0 (open_tm_ty t U) ->
  lc_tm_at 1 0 t.
Proof.
  intros U t HU H. unfold open_tm_ty in H.
  eapply lc_tm_open_ty_rec_inv; eauto.
Qed.

Lemma has_type_lc_tm : forall Delta Gamma t T, has_type Delta Gamma t T -> lc_tm_at 0 0 t.
Proof.
  intros Delta Gamma t T H. induction H as
    [Delta Gamma x T Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U Ht IHt HU
    | Delta Gamma t1 t2 T Ht1 IH1 Ht2 IH2].
  - constructor.
  - constructor.
    + eapply wf_ty_lc_ty_at; eassumption.
    + specialize (IHbody (fresh_atom L) (fresh_atom_notin L)).
      apply lc_tm_open_rec_inv with (k := 0) (u := tm_fvar (fresh_atom L)) in IHbody.
      * exact IHbody.
      * constructor.
  - constructor; assumption.
  - constructor.
    specialize (IHbody (fresh_atom L) (fresh_atom_notin L)).
    apply lc_tm_open_ty_rec_inv with (K := 0) (U := Ty_FVar (fresh_atom L)) in IHbody.
    + simpl in IHbody. exact IHbody.
    + constructor.
  - constructor; [assumption | eapply wf_ty_lc_ty_at; eassumption].
  - constructor; assumption.
Qed.

(* ============================================================ *)
(* Whole-substitution operations and commutation lemmas         *)
(* ============================================================ *)

Fixpoint ty_subst_all (sigma : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sigma X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst_all sigma T1) (ty_subst_all sigma T2)
  | Ty_All T1 => Ty_All (ty_subst_all sigma T1)
  end.

Fixpoint tm_ty_subst_all (sigma : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst_all sigma T) (tm_ty_subst_all sigma t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst_all sigma t1) (tm_ty_subst_all sigma t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst_all sigma t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst_all sigma t1) (ty_subst_all sigma T)
  | tm_choice t1 t2 => tm_choice (tm_ty_subst_all sigma t1) (tm_ty_subst_all sigma t2)
  end.

Fixpoint tm_subst_all (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs T (tm_subst_all sigma t1)
  | tm_app t1 t2 => tm_app (tm_subst_all sigma t1) (tm_subst_all sigma t2)
  | tm_tabs t1 => tm_tabs (tm_subst_all sigma t1)
  | tm_tapp t1 T => tm_tapp (tm_subst_all sigma t1) T
  | tm_choice t1 t2 => tm_choice (tm_subst_all sigma t1) (tm_subst_all sigma t2)
  end.

Lemma lc_ty_subst_all : forall T sigma K,
  (forall X, lc_ty_at 0 (sigma X)) ->
  lc_ty_at K T ->
  lc_ty_at K (ty_subst_all sigma T).
Proof.
  intros T. induction T as [n|X|T1 IH1 T2 IH2|T1 IH1]; intros sigma K Hsig HT.
  - simpl. assumption.
  - simpl. apply lc_ty_at_mono with (k := 0); auto; lia.
  - simpl. inversion HT. constructor; auto.
  - simpl. inversion HT. constructor. apply IH1; auto.
Qed.

Lemma ty_subst_all_open_ty_rec : forall sigma k U T,
  (forall X, lc_ty_at 0 (sigma X)) ->
  ty_subst_all sigma (open_ty_rec k U T) =
  open_ty_rec k (ty_subst_all sigma U) (ty_subst_all sigma T).
Proof.
  intros sigma k U T Hsig. revert k. induction T as [n|X|T1 IH1 T2 IH2|T1 IH1]; intros k.
  - simpl. destruct (Nat.eqb k n); reflexivity.
  - simpl. symmetry. apply open_ty_rec_lc_id.
    apply lc_ty_at_mono with (k := 0); auto; lia.
  - simpl. rewrite IH1, IH2; reflexivity.
  - simpl. rewrite IH1; reflexivity.
Qed.

Lemma tm_ty_subst_all_open_tm_ty_rec : forall sigma k U t,
  (forall X, lc_ty_at 0 (sigma X)) ->
  tm_ty_subst_all sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (ty_subst_all sigma U) (tm_ty_subst_all sigma t).
Proof.
  intros sigma k U t Hsig. revert k. induction t as
    [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2]; intros k.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite ty_subst_all_open_ty_rec, IH1; auto.
  - simpl. rewrite IH1, IH2; reflexivity.
  - simpl. rewrite IH1; reflexivity.
  - simpl. rewrite IH1, ty_subst_all_open_ty_rec; auto.
  - simpl. rewrite IH1, IH2; reflexivity.
Qed.

Lemma ty_subst_all_open_tm_rec : forall sigma k u t,
  tm_ty_subst_all sigma (open_tm_rec k u t) =
  open_tm_rec k (tm_ty_subst_all sigma u) (tm_ty_subst_all sigma t).
Proof.
  intros sigma k u t. revert k. induction t as
    [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2]; intros k.
  - simpl. destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - simpl. rewrite IH1; reflexivity.
  - simpl. rewrite IH1, IH2; reflexivity.
  - simpl. rewrite IH1; reflexivity.
  - simpl. rewrite IH1; reflexivity.
  - simpl. rewrite IH1, IH2; reflexivity.
Qed.

Lemma open_tm_rec_lc_id : forall K k k' u t,
  k <= k' -> lc_tm_at K k t -> open_tm_rec k' u t = t.
Proof.
  intros K k k' u t Hle H. revert H. revert K k k' u Hle.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros K k k' u Hle H; inversion H; subst.
  - simpl. destruct (Nat.eqb k' i) eqn:E. apply Nat.eqb_eq in E. lia. reflexivity.
  - reflexivity.
  - simpl. rewrite IH1 with (K := K) (k := S k) (k' := S k') (u := u); auto. lia.
  - simpl. rewrite IH1 with (K := K) (k := k) (k' := k') (u := u); auto.
    rewrite IH2 with (K := K) (k := k) (k' := k') (u := u); auto.
  - simpl. rewrite IH1 with (K := S K) (k := k) (k' := k') (u := u); auto.
  - simpl. rewrite IH1 with (K := K) (k := k) (k' := k') (u := u); auto.
  - simpl. rewrite IH1 with (K := K) (k := k) (k' := k') (u := u); auto.
    rewrite IH2 with (K := K) (k := k) (k' := k') (u := u); auto.
Qed.

Lemma open_tm_ty_rec_lc_id : forall K k k' U t,
  K <= k' -> lc_tm_at K k t -> open_tm_ty_rec k' U t = t.
Proof.
  intros K k k' U t Hle H. revert H. revert K k k' U Hle.
  induction t as [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros K k k' U Hle H; inversion H; subst.
  - reflexivity.
  - reflexivity.
  - simpl. erewrite open_ty_rec_lc_id.
    + rewrite IH1 with (K := K) (k := S k) (k' := k') (U := U); auto.
    + eapply lc_ty_at_mono; eauto.
  - simpl. rewrite IH1 with (K := K) (k := k) (k' := k') (U := U); auto.
    rewrite IH2 with (K := K) (k := k) (k' := k') (U := U); auto.
  - simpl. rewrite IH1 with (K := S K) (k := k) (k' := S k') (U := U); auto. lia.
  - simpl. erewrite open_ty_rec_lc_id.
    + rewrite IH1 with (K := K) (k := k) (k' := k') (U := U); auto.
    + eapply lc_ty_at_mono; eauto.
  - simpl. rewrite IH1 with (K := K) (k := k) (k' := k') (U := U); auto.
    rewrite IH2 with (K := K) (k := k) (k' := k') (U := U); auto.
Qed.

Lemma tm_subst_all_open_tm_rec : forall sigma k u t,
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  lc_tm_at 0 0 u ->
  tm_subst_all sigma (open_tm_rec k u t) =
  open_tm_rec k (tm_subst_all sigma u) (tm_subst_all sigma t).
Proof.
  intros sigma k u t Hsig Hu. revert k. induction t as
    [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2]; intros k.
  - simpl. destruct (Nat.eqb k i); reflexivity.
  - simpl. erewrite open_tm_rec_lc_id with (K := 0) (k := 0) (k' := k).
    + reflexivity.
    + lia.
    + apply Hsig.
  - simpl. rewrite IH1; auto.
  - simpl. rewrite IH1, IH2; auto.
  - simpl. rewrite IH1; auto.
  - simpl. rewrite IH1; auto.
  - simpl. rewrite IH1, IH2; auto.
Qed.

Lemma tm_subst_all_open_tm_ty_rec : forall sigma k U t,
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  tm_subst_all sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (tm_subst_all sigma t).
Proof.
  intros sigma k U t Hsig. revert k. induction t as
    [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2]; intros k.
  - reflexivity.
  - simpl. erewrite open_tm_ty_rec_lc_id with (K := 0) (k := 0) (k' := k).
    + reflexivity.
    + lia.
    + apply Hsig.
  - simpl. rewrite IH1; reflexivity.
  - simpl. rewrite IH1, IH2; reflexivity.
  - simpl. rewrite IH1; reflexivity.
  - simpl. rewrite IH1; reflexivity.
  - simpl. rewrite IH1, IH2; reflexivity.
Qed.

Lemma tm_subst_all_id : forall t, tm_subst_all (fun x => tm_fvar x) t = t.
Proof.
  intros t. induction t; simpl; auto; rewrite ?IHt, ?IHt1, ?IHt2; auto.
Qed.

Lemma ty_subst_all_id : forall T, ty_subst_all (fun X => Ty_FVar X) T = T.
Proof.
  intros T. induction T; simpl; auto; rewrite ?IHT, ?IHT1, ?IHT2; auto.
Qed.

Lemma tm_ty_subst_all_id : forall t, tm_ty_subst_all (fun X => Ty_FVar X) t = t.
Proof.
  intros t. induction t; simpl; auto; rewrite ?ty_subst_all_id, ?IHt, ?IHt1, ?IHt2; auto.
Qed.

(* ============================================================ *)
(* Semantic types                                           *)
(* ============================================================ *)

Definition pred := tm -> Prop.
Definition semty := (ty * pred)%type.

(* ============================================================ *)
(* Free term variables and typing                            *)
(* ============================================================ *)

Fixpoint fvars_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => fvars_tm t1
  | tm_app t1 t2 => fvars_tm t1 ++ fvars_tm t2
  | tm_tabs t1 => fvars_tm t1
  | tm_tapp t1 _ => fvars_tm t1
  | tm_choice t1 t2 => fvars_tm t1 ++ fvars_tm t2
  end.

Lemma notin_app_l : forall (l1 l2 : list atom) x, ~ In x (l1 ++ l2) -> ~ In x l1.
Proof. intros l1 l2 x H Hin. apply H. apply in_or_app. auto. Qed.

Lemma notin_app_r : forall (l1 l2 : list atom) x, ~ In x (l1 ++ l2) -> ~ In x l2.
Proof. intros l1 l2 x H Hin. apply H. apply in_or_app. auto. Qed.

Lemma in_app_assoc_l : forall (A B U : list atom) z,
  In z (A ++ U) -> In z ((A ++ B) ++ U).
Proof.
  intros A B U z H. apply in_app_or in H. destruct H as [H|H].
  - apply (in_or_app (A ++ B) U z). left. apply (in_or_app A B z). left. exact H.
  - apply (in_or_app (A ++ B) U z). right. exact H.
Qed.

Lemma in_app_assoc_r : forall (A B U : list atom) z,
  In z (B ++ U) -> In z ((A ++ B) ++ U).
Proof.
  intros A B U z H. apply in_app_or in H. destruct H as [H|H].
  - apply (in_or_app (A ++ B) U z). left. apply (in_or_app A B z). right. exact H.
  - apply (in_or_app (A ++ B) U z). right. exact H.
Qed.

Lemma fvars_open_tm_rec_incl : forall k u t z,
  In z (fvars_tm (open_tm_rec k u t)) -> In z (fvars_tm t ++ fvars_tm u).
Proof.
  intros k u t. revert k. induction t as
    [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2]; intros k z H.
  - simpl in H. simpl. destruct (Nat.eqb k i) eqn:E.
    + apply (in_or_app (fvars_tm (tm_bvar i)) (fvars_tm u) z). right. exact H.
    + destruct H.
  - simpl in H. simpl. apply (in_or_app (fvars_tm (tm_fvar x)) (fvars_tm u) z). left. exact H.
  - simpl in H. simpl. apply IH1 with (k := S k). exact H.
  - simpl in H. simpl. apply in_app_or in H. destruct H as [H|H].
    + apply in_app_assoc_l with (B := fvars_tm t2). apply IH1 with (k := k). exact H.
    + apply in_app_assoc_r with (A := fvars_tm t1). apply IH2 with (k := k). exact H.
  - simpl in H. simpl. apply IH1 with (k := k). exact H.
  - simpl in H. simpl. apply IH1 with (k := k). exact H.
  - simpl in H. simpl. apply in_app_or in H. destruct H as [H|H].
    + apply in_app_assoc_l with (B := fvars_tm t2). apply IH1 with (k := k). exact H.
    + apply in_app_assoc_r with (A := fvars_tm t1). apply IH2 with (k := k). exact H.
Qed.

Lemma fvars_open_tm_rec_incl_t : forall k u t z,
  In z (fvars_tm t) -> In z (fvars_tm (open_tm_rec k u t)).
Proof.
  intros k u t. revert k. induction t as
    [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2]; intros k z H; simpl in *.
  - destruct H.
  - exact H.
  - exact (IH1 (S k) z H).
  - apply in_app_or in H. destruct H as [H|H].
    + apply (in_or_app (fvars_tm (open_tm_rec k u t1)) (fvars_tm (open_tm_rec k u t2)) z).
      left. apply IH1 with (k := k). exact H.
    + apply (in_or_app (fvars_tm (open_tm_rec k u t1)) (fvars_tm (open_tm_rec k u t2)) z).
      right. apply IH2 with (k := k). exact H.
  - exact (IH1 k z H).
  - exact (IH1 k z H).
  - apply in_app_or in H. destruct H as [H|H].
    + apply (in_or_app (fvars_tm (open_tm_rec k u t1)) (fvars_tm (open_tm_rec k u t2)) z).
      left. apply IH1 with (k := k). exact H.
    + apply (in_or_app (fvars_tm (open_tm_rec k u t1)) (fvars_tm (open_tm_rec k u t2)) z).
      right. apply IH2 with (k := k). exact H.
Qed.

Lemma fvars_open_tm_ty_rec : forall k U t,
  fvars_tm (open_tm_ty_rec k U t) = fvars_tm t.
Proof.
  intros k U t. revert k. induction t as
    [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2]; intros k; simpl.
  - reflexivity.
  - reflexivity.
  - apply IH1.
  - rewrite IH1, IH2. reflexivity.
  - apply IH1.
  - apply IH1.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma fvars_tm_ty_subst_all : forall sigma t,
  fvars_tm (tm_ty_subst_all sigma t) = fvars_tm t.
Proof.
  intros sigma t. induction t; simpl; auto; rewrite ?IHt, ?IHt1, ?IHt2; auto.
Qed.

Lemma has_type_fv_tm : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall z, In z (fvars_tm t) -> exists Tz, lookup_context z Gamma = Some Tz.
Proof.
  intros Delta Gamma t T H. induction H as
    [Delta Gamma x T Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U Ht IHt HU
    | Delta Gamma t1 t2 T Ht1 IH1 Ht2 IH2];
    intros z Hin.
  - simpl in Hin. destruct Hin as [->|[]]. exists T. assumption.
  - simpl in Hin.
    set (x := fresh_atom (L ++ fvars_tm t2)).
    assert (HxL : ~ In x L) by (apply notin_app_l with (l2 := fvars_tm t2); apply fresh_atom_notin).
    assert (HxT : ~ In x (fvars_tm t2)) by (apply notin_app_r with (l1 := L); apply fresh_atom_notin).
    assert (Hzin : In z (fvars_tm (open_tm t2 (tm_fvar x)))).
    { apply (fvars_open_tm_rec_incl_t 0 (tm_fvar x) t2 z). assumption. }
    destruct (IHbody x HxL z Hzin) as [Tz HTz].
    exists Tz. simpl in HTz.
    destruct (Nat.eqb z x) eqn:E.
    + apply Nat.eqb_eq in E. subst. contradiction.
    + exact HTz.
  - simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + apply IH1; assumption.
    + apply IH2; assumption.
  - simpl in Hin.
    set (X := fresh_atom (L ++ fvars_tm t)).
    assert (HXL : ~ In X L) by (apply notin_app_l with (l2 := fvars_tm t); apply fresh_atom_notin).
    assert (HXin : In z (fvars_tm (open_tm_ty t (Ty_FVar X)))).
    { change (In z (fvars_tm (open_tm_ty_rec 0 (Ty_FVar X) t))).
      rewrite fvars_open_tm_ty_rec. assumption. }
    destruct (IHbody X HXL z HXin) as [Tz HTz]. exists Tz. assumption.
  - simpl in Hin. apply IHt; assumption.
  - simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + apply IH1; assumption.
    + apply IH2; assumption.
Qed.

(* Local closedness of the type/term substituted target term *)

Lemma lc_tm_subst_Wty : forall t (aenv : atom -> semty) (sigma : atom -> tm),
  (forall X, lc_ty_at 0 (fst (aenv X))) ->
  (forall z, In z (fvars_tm t) -> lc_tm_at 0 0 (sigma z)) ->
  lc_tm_at 0 0 t ->
  lc_tm_at 0 0 (tm_subst_all sigma (tm_ty_subst_all (fun X => fst (aenv X)) t)).
Proof.
  intros t. induction t as
    [i|x|T t1 IH1|t1 IH1 t2 IH2|t1 IH1|t1 IH1 T|t1 IH1 t2 IH2];
    intros aenv sigma HW Hsig Hlc; simpl in *.
  - inversion Hlc. lia.
  - apply Hsig. simpl. auto.
  - inversion Hlc. constructor.
    + apply lc_ty_subst_all; auto.
    + apply IH1; auto. intros z Hz. apply Hsig. simpl. auto.
  - inversion Hlc. constructor; [apply IH1|apply IH2]; auto.
  - inversion Hlc. constructor. apply IH1; auto.
  - inversion Hlc. constructor.
    + apply IH1; auto.
    + apply lc_ty_subst_all; auto.
  - inversion Hlc. constructor; [apply IH1|apply IH2]; auto.
Qed.

(* ============================================================ *)
(* Local closedness of values and backward preservation of step *)
(* ============================================================ *)

Lemma value_lc : forall v, value v -> lc_tm_at 0 0 v.
Proof. intros v H; destruct H; assumption. Qed.

Lemma lc_tm_step_back : forall e e', e --> e' -> lc_tm_at 0 0 e' -> lc_tm_at 0 0 e.
Proof.
  intros e e' H. induction H; intros Hlc.
  - constructor; [assumption | apply value_lc; assumption].
  - inversion Hlc. constructor; [eapply IHstep; eassumption | assumption].
  - inversion Hlc. constructor; [apply value_lc; assumption | eapply IHstep; eassumption].
  - constructor; assumption.
  - inversion Hlc. constructor; [eapply IHstep; eassumption | assumption].
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma lc_tm_multi_back : forall e e', e -->* e' -> lc_tm_at 0 0 e' -> lc_tm_at 0 0 e.
Proof.
  intros e e' H. induction H; intros Hlc.
  - assumption.
  - apply lc_tm_step_back with y; auto.
Qed.

(* ============================================================ *)
(* Semantic types and the logical relation                      *)
(* ============================================================ *)

Definition adm (P : pred) : Prop :=
  (forall e, P e -> lc_tm_at 0 0 e) /\
  (forall e, P e -> exists v, e -->* v /\ value v /\ P v) /\
  (forall e e', e -->* e' -> P e' -> P e) /\
  (forall e1 e2, P e1 -> P e2 -> P (tm_choice e1 e2)).

Definition default_semty : semty := (Ty_BVar 0, fun _ => False).

Fixpoint sem (benv : list semty) (aenv : atom -> semty) (T : ty) (e : tm) {struct T} : Prop :=
  lc_tm_at 0 0 e /\
  match T with
  | Ty_BVar i => snd (nth i benv default_semty) e
  | Ty_FVar X => snd (aenv X) e
  | Ty_Arrow T1 T2 =>
      exists v, e -->* v /\
        lc_tm_at 0 0 v /\
        (exists A b, v = tm_abs A b) /\
        (forall a, sem benv aenv T1 a -> sem benv aenv T2 (tm_app v a))
  | Ty_All T1 =>
      exists v, e -->* v /\
        lc_tm_at 0 0 v /\
        (exists b, v = tm_tabs b) /\
        (forall U S, lc_ty_at 0 U -> adm S -> sem ((U,S)::benv) aenv T1 (tm_tapp v U))
  end.

Lemma sem_lc : forall benv aenv T e, sem benv aenv T e -> lc_tm_at 0 0 e.
Proof. intros benv aenv T e H. destruct T; simpl in H; apply (proj1 H). Qed.

Lemma adm_lc_and : forall P, adm P -> adm (fun e => lc_tm_at 0 0 e /\ P e).
Proof.
  intros P [Hlc [Hmay [Hback Hchoice]]]. unfold adm.
  split.
  { intros e [He _]; exact He. }
  split.
  { intros e [He HP]. destruct (Hmay e HP) as [v [Hstep [Hval HPv]]].
    exists v. split; [exact Hstep|]. split; [exact Hval|].
    split; [apply Hlc; exact HPv|exact HPv]. }
  split.
  { intros e e' Hstep [He' HP']. split.
    + apply lc_tm_multi_back with e'; assumption.
    + apply Hback with e'; assumption. }
  { intros e1 e2 [H1 HP1] [H2 HP2]. split; [constructor; assumption|].
    apply Hchoice; assumption. }
Qed.

Lemma multi_trans : forall x y z, x -->* y -> y -->* z -> x -->* z.
Proof.
  intros x y z H. induction H; intros H2.
  - assumption.
  - eapply multi_step; [eassumption|apply IHmulti; assumption].
Qed.

Lemma sem_mk_arrow : forall benv aenv T1 T2 e v,
  e -->* v ->
  lc_tm_at 0 0 v ->
  (exists A b, v = tm_abs A b) ->
  (forall a, sem benv aenv T1 a -> sem benv aenv T2 (tm_app v a)) ->
  sem benv aenv (Ty_Arrow T1 T2) e.
Proof.
  intros. simpl. split; [apply lc_tm_multi_back with v; assumption|].
  exists v. split; [assumption|]. split; [assumption|].
  split; [assumption|assumption].
Qed.

Lemma sem_mk_all : forall benv aenv T1 e v,
  e -->* v ->
  lc_tm_at 0 0 v ->
  (exists b, v = tm_tabs b) ->
  (forall U S, lc_ty_at 0 U -> adm S -> sem ((U,S)::benv) aenv T1 (tm_tapp v U)) ->
  sem benv aenv (Ty_All T1) e.
Proof.
  intros. simpl. split; [apply lc_tm_multi_back with v; assumption|].
  exists v. split; [assumption|]. split; [assumption|].
  split; [assumption|assumption].
Qed.

Lemma adm_sem : forall T benv aenv,
  (forall i, adm (snd (nth i benv default_semty))) ->
  (forall X, adm (snd (aenv X))) ->
  adm (sem benv aenv T).
Proof.
  intros T. induction T as [i|X|T1 IH1 T2 IH2|T1 IH1]; intros benv aenv Hbenv Haenv.
  - simpl. apply adm_lc_and. apply Hbenv.
  - simpl. apply adm_lc_and. apply Haenv.
  - simpl. unfold adm.
    split.
    { intros e [He _]; exact He. }
    split.
    { intros e He. destruct He as [He [v [Hstep [Hlc [Habs Hcl]]]]].
      exists v. split; [exact Hstep|]. split.
      - destruct Habs as [A [b Hb]]. subst v. apply v_abs. exact Hlc.
      - apply sem_mk_arrow with (e := v) (v := v); auto. apply multi_refl. }
    split.
    { intros e e' Hstep He'. destruct He' as [He' [v [Hstep' [Hlc [Habs Hcl]]]]].
      apply sem_mk_arrow with (e := e) (v := v).
      - apply multi_trans with e'; assumption.
      - exact Hlc. - exact Habs. - exact Hcl. }
    { intros e1 e2 He1 He2. destruct He1 as [He1 [v1 [Hstep1 [Hlc1 [Habs1 Hcl1]]]]].
      destruct He2 as [He2 _].
      apply sem_mk_arrow with (e := tm_choice e1 e2) (v := v1).
      - eapply multi_step.
        + apply ST_ChoiceLeft; assumption.
        + exact Hstep1.
      - exact Hlc1. - exact Habs1. - exact Hcl1. }
  - simpl. unfold adm.
    split.
    { intros e [He _]; exact He. }
    split.
    { intros e He. destruct He as [He [v [Hstep [Hlc [Htabs Hcl]]]]].
      exists v. split; [exact Hstep|]. split.
      - destruct Htabs as [b Hb]. subst v. apply v_tabs. exact Hlc.
      - apply sem_mk_all with (e := v) (v := v); auto. apply multi_refl. }
    split.
    { intros e e' Hstep He'. destruct He' as [He' [v [Hstep' [Hlc [Htabs Hcl]]]]].
      apply sem_mk_all with (e := e) (v := v).
      - apply multi_trans with e'; assumption.
      - exact Hlc. - exact Htabs. - exact Hcl. }
    { intros e1 e2 He1 He2. destruct He1 as [He1 [v1 [Hstep1 [Hlc1 [Htabs1 Hcl1]]]]].
      destruct He2 as [He2 _].
      apply sem_mk_all with (e := tm_choice e1 e2) (v := v1).
      - eapply multi_step.
        + apply ST_ChoiceLeft; assumption.
        + exact Hstep1.
      - exact Hlc1. - exact Htabs1. - exact Hcl1. }
Qed.

Lemma sem_back : forall benv aenv T e e',
  (forall i, adm (snd (nth i benv default_semty))) ->
  (forall X, adm (snd (aenv X))) ->
  e -->* e' -> sem benv aenv T e' -> sem benv aenv T e.
Proof.
  intros benv aenv T. induction T as [i|X|T1 IH1 T2 IH2|T1 IH1]; intros e e' Hbenv Haenv Hstep He'.
  - simpl in He' |- *. destruct He' as [He' HP]. split.
    + apply lc_tm_multi_back with e'; assumption.
    + destruct (Hbenv i) as [_ [_ [Hback _]]]. eapply Hback; eassumption.
  - simpl in He' |- *. destruct He' as [He' HP]. split.
    + apply lc_tm_multi_back with e'; assumption.
    + destruct (Haenv X) as [_ [_ [Hback _]]]. eapply Hback; eassumption.
  - simpl in He' |- *. destruct He' as [He' [v [Hstep' [Hlc [Habs Hcl]]]]].
    apply sem_mk_arrow with (e := e) (v := v).
    + apply multi_trans with e'; assumption.
    + exact Hlc. + exact Habs. + exact Hcl.
  - simpl in He' |- *. destruct He' as [He' [v [Hstep' [Hlc [Htabs Hcl]]]]].
    apply sem_mk_all with (e := e) (v := v).
    + apply multi_trans with e'; assumption.
    + exact Hlc. + exact Htabs. + exact Hcl.
Qed.

Lemma sem_may : forall benv aenv T e,
  (forall i, adm (snd (nth i benv default_semty))) ->
  (forall X, adm (snd (aenv X))) ->
  sem benv aenv T e ->
  exists v, e -->* v /\ value v /\ sem benv aenv T v.
Proof.
  intros benv aenv T e Hbenv Haenv He.
  destruct (adm_sem T benv aenv Hbenv Haenv) as [Hlc [Hmay [Hback Hchoice]]].
  apply Hmay. assumption.
Qed.

Lemma sem_choice : forall benv aenv T e1 e2,
  (forall i, adm (snd (nth i benv default_semty))) ->
  (forall X, adm (snd (aenv X))) ->
  sem benv aenv T e1 -> sem benv aenv T e2 -> sem benv aenv T (tm_choice e1 e2).
Proof.
  intros benv aenv T e1 e2 Hbenv Haenv H1 H2.
  destruct (adm_sem T benv aenv Hbenv Haenv) as [Hlc [Hmay [Hback Hchoice]]].
  apply Hchoice; assumption.
Qed.

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  (* Complete the proof of the free theorem. *)
Qed.

End SystemFParametricityNondeterminismHardTask.
