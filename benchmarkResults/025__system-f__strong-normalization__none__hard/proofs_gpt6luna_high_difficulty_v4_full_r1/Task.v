(** System F CBV strong-normalization benchmark, Hard variant.
    Features: none. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Recdef.
Import ListNotations.

Module SystemFNormalizationNoneHardTask.

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

  | tm_tapp : tm -> ty -> tm.

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
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
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
      lc_tm_at K k (tm_tapp t T).

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
      has_type Delta Gamma (tm_tapp t U) (open_ty T U).

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* Construct the logical relation and supporting proofs here. *)

Lemma sn_step : forall t u, strongly_normalizing t -> t --> u ->
  strongly_normalizing u.
Proof. intros t u H; inversion H; eauto. Qed.

Lemma sn_from_steps : forall t,
  (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.
Proof. intros; constructor; assumption. Qed.

Lemma sn_abs : forall T t,
  strongly_normalizing (tm_abs T t).
Proof. intros; constructor; intros u H; inversion H. Qed.

Lemma sn_tabs : forall t,
  strongly_normalizing (tm_tabs t).
Proof. intros; constructor; intros u H; inversion H. Qed.

Lemma multi_refl' : forall t, t -->* t.
Proof. constructor. Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof. intros t u v H; induction H; eauto using multi. Qed.

Lemma lc_step : forall t u, locally_closed_tm t -> t --> u ->
  locally_closed_tm u.
Proof.
  intros t u Hlc Hst.
  assert (Hweaken : forall K k b, lc_tm_at K k b -> lc_tm_at K (S k) b).
  { intros K k b Hb; induction Hb; eauto using lc_tm_at; try lia. }
  assert (Htyweaken : forall K T, lc_ty_at K T -> lc_ty_at (S K) T).
  { intros K T HT; induction HT; eauto using lc_ty_at; try lia. }
  assert (Htmtyweaken : forall K k b,
    lc_tm_at K k b -> lc_tm_at (S K) k b).
  { intros K k b Hb; induction Hb; eauto using lc_tm_at, Htyweaken. }
  assert (Hopen : forall K k b s,
    lc_tm_at K (S k) b -> lc_tm_at K k s ->
    lc_tm_at K k (open_tm_rec k s b)).
  { intros K k b; revert K k.
    induction b; intros K k s Hb Hs; simpl in *.
    - inversion Hb; subst. destruct (Nat.eqb k n) eqn:E.
      + apply Nat.eqb_eq in E; subst; exact Hs.
      + apply lc_tm_bvar. inversion Hb; subst. apply Nat.eqb_neq in E; lia.
    - inversion Hb; constructor.
    - inversion Hb; subst. econstructor; eauto using Hweaken.
    - inversion Hb; subst. econstructor; eauto using Htmtyweaken.
    - inversion Hb; subst. econstructor; eauto using Htmtyweaken.
    - inversion Hb; subst. econstructor; eauto using Htyweaken. }
  assert (Htyopen : forall K U T,
    lc_ty_at (S K) T -> lc_ty_at K U ->
    lc_ty_at K (open_ty_rec K U T)).
  { intros K U T HT; revert K U HT.
    induction T; intros K U HT HU; simpl in *.
    - inversion HT; subst. destruct (Nat.eqb K n) eqn:E.
      + apply Nat.eqb_eq in E; subst; exact HU.
      + apply lc_ty_bvar. apply Nat.eqb_neq in E; lia.
    - inversion HT; constructor.
    - inversion HT; subst. constructor; [eapply IHT1|eapply IHT2]; eauto.
    - inversion HT; subst. constructor. eapply IHT; eauto using Htyweaken. }
  assert (Htytm : forall K k b U,
    lc_tm_at (S K) k b -> lc_ty_at K U ->
    lc_tm_at K k (open_tm_ty_rec K U b)).
  { intros K k b; revert K k.
    induction b; intros K k U Hb HU; simpl in *.
    - inversion Hb; constructor; assumption.
    - inversion Hb; constructor.
    - inversion Hb; subst. econstructor.
      + eapply Htyopen; eauto.
      + eapply IHb; eauto.
    - inversion Hb; subst. econstructor; eauto.
    - inversion Hb; subst. econstructor. eapply IHb; eauto using Htyweaken.
    - inversion Hb; subst. econstructor; eauto using Htyopen. }
  revert Hlc. induction Hst; intros Hlc0.
  - unfold locally_closed_tm in *. inversion Hlc0; subst.
    inversion H; subst.
    unfold locally_closed_tm. eapply Hopen; [exact H8|exact H6].
  - unfold locally_closed_tm in *. inversion Hlc0; subst.
    econstructor; eauto.
  - unfold locally_closed_tm in *. inversion Hlc0; subst.
    econstructor; eauto.
  - unfold locally_closed_tm in *. inversion Hlc0; subst.
    inversion H; subst. unfold locally_closed_tm.
    eapply Htytm; eauto.
  - unfold locally_closed_tm in *. inversion Hlc0; subst.
    econstructor; eauto.
 Qed.

Lemma lc_multi : forall t u, locally_closed_tm t -> t -->* u ->
  locally_closed_tm u.
Proof. intros t u Hlc H; induction H; eauto using lc_step. Qed.

Lemma lc_ty_open_reflect : forall k T X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  intros k T; revert k; induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_ty_bvar. apply Nat.eqb_eq in E; lia.
    + inversion H; subst. apply lc_ty_bvar. apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; subst. constructor; [eapply IHT1|eapply IHT2]; eassumption.
  - inversion H; subst. constructor. eapply IHT. eassumption.
Qed.

Lemma lc_tm_open_reflect : forall K k t x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k; induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_tm_bvar. apply Nat.eqb_eq in E; lia.
    + inversion H; subst. apply lc_tm_bvar. apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; subst. econstructor; eauto.
  - inversion H; subst. econstructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. econstructor. eapply IHt; eauto.
  - inversion H; subst. econstructor; [eapply IHt|]; eauto.
Qed.

Lemma lc_tm_ty_open_reflect : forall K n t X,
  lc_tm_at K n (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) n t.
Proof.
  intros K m t; revert K m; induction t; intros K m X H; simpl in H.
  - inversion H; constructor; assumption.
  - constructor.
  - inversion H; subst. econstructor.
    + eapply lc_ty_open_reflect; eassumption.
    + eapply IHt; eassumption.
  - inversion H; subst. econstructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. econstructor. eapply IHt; eassumption.
  - inversion H; subst. econstructor; [eapply IHt|eapply lc_ty_open_reflect]; eassumption.
Qed.

Lemma in_le_fold_max : forall L x,
  In x L -> x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x Hin; simpl in *; [contradiction|].
  destruct Hin as [->|Hin]; [apply Nat.le_max_l|].
  eapply Nat.le_trans; [eapply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma fresh_notin : forall (L : list atom), exists x, ~ In x L.
Proof.
  intro L. exists (S (fold_right Nat.max 0 L)).
  intro Hin. pose proof (in_le_fold_max L _ Hin). lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf; induction Hwf as
    [Delta X Hin
    |Delta T1 T2 H1 IH1 H2 IH2
    |L Delta T Hbody IHbody].
  - constructor.
  - constructor; assumption.
  - destruct (fresh_notin L) as [X HX].
    specialize (Hbody X HX). pose proof (IHbody X HX) as Hclosed.
    unfold locally_closed_ty in Hclosed.
    apply lc_ty_all. eapply lc_ty_open_reflect. exact Hclosed.
Qed.

Lemma lc_ty_weaken : forall k T, lc_ty_at k T -> lc_ty_at (S k) T.
Proof. intros k T H; induction H; eauto using lc_ty_at; try lia. Qed.

Lemma lc_ty_open : forall k T U,
  lc_ty_at (S k) T -> lc_ty_at k U -> lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k T; revert k; induction T; intros k U HT HU; simpl in *.
  - inversion HT; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact HU.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E; lia.
  - inversion HT; constructor.
  - inversion HT; subst. constructor; [eapply IHT1|eapply IHT2]; eassumption.
  - inversion HT; subst. constructor. eapply IHT; [exact H1|].
    eapply lc_ty_weaken. exact HU.
Qed.

Lemma has_type_regular : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t /\ locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty; induction Hty as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma T1 b T2 Hwf Hbody IHbody
    |Delta Gamma f a T1 T2 Hf IHf Harg IHa
    |L Delta Gamma b T Hbody IHbody
    |Delta Gamma f T U Hf IHf HwfU].
  - split; [exact (lc_tm_fvar 0 0 x)|exact (wf_ty_lc Delta T Hwf)].
  - destruct (fresh_notin L) as [x Hx].
    specialize (Hbody x Hx). specialize (IHbody x Hx) as [Hopen Htype2].
    split.
    + unfold locally_closed_tm. econstructor.
      * exact (wf_ty_lc Delta T1 Hwf).
      * unfold locally_closed_tm in Hopen.
        eapply lc_tm_open_reflect. exact Hopen.
    + unfold locally_closed_ty. constructor.
      * exact (wf_ty_lc Delta T1 Hwf).
      * exact Htype2.
  - destruct IHf as [Hflc Hfty], IHa as [Halc Haty].
    split.
    + unfold locally_closed_tm. econstructor; assumption.
    + inversion Hfty; assumption.
  - destruct (fresh_notin L) as [X HX].
    specialize (Hbody X HX). specialize (IHbody X HX) as [Hopen Htype].
    split.
    + unfold locally_closed_tm. econstructor.
      eapply lc_tm_ty_open_reflect. exact Hopen.
    + unfold locally_closed_ty in Htype.
      apply lc_ty_all. eapply lc_ty_open_reflect. exact Htype.
  - destruct IHf as [Hflc Hforall].
    unfold locally_closed_tm in Hflc. inversion Hforall; subst.
    split.
    + unfold locally_closed_tm. econstructor; [exact Hflc|exact (wf_ty_lc Delta U HwfU)].
    + unfold locally_closed_ty. eapply lc_ty_open; [eassumption|exact (wf_ty_lc Delta U HwfU)].
Qed.

Lemma sn_app_beta : forall f a,
  strongly_normalizing f -> strongly_normalizing a -> locally_closed_tm a ->
  (forall T b f' a',
    f -->* f' -> a -->* a' -> f' = tm_abs T b -> value a' ->
    strongly_normalizing (open_tm b a')) ->
  strongly_normalizing (tm_app f a).
Proof.
  intros f a Hf; revert a.
  induction Hf as [f Hfsteps IHf]; intros a Ha Hla Hbeta.
  induction Ha as [a Hasteps IHa].
  constructor; intros u Hu; inversion Hu; subst.
  - eapply Hbeta; eauto using multi_refl'.
  - eapply IHf; [exact H1|constructor; exact Hasteps|exact Hla|].
    intros T b f' a' Hmf Hma Habs Hval.
    eapply Hbeta; eauto. eapply multi_step; [eassumption|exact Hmf].
  - eapply IHa; [assumption|eapply lc_step; eauto|].
    intros T b f' a' Hmf Hma Habs Hval.
    eapply Hbeta; eauto. eapply multi_step; [eassumption|exact Hma].
Qed.

Lemma sn_tapp_beta : forall f U,
  strongly_normalizing f -> locally_closed_ty U ->
  (forall b f', f -->* f' -> f' = tm_tabs b ->
    strongly_normalizing (open_tm_ty b U)) ->
  strongly_normalizing (tm_tapp f U).
Proof.
  intros f U Hf; induction Hf as [f Hsteps IH]; intros Hlu Hbeta.
  constructor; intros u Hu; inversion Hu; subst.
  - subst. eapply Hbeta; eauto using multi_refl'.
  - eapply IH; eauto.
    intros b f' Hmf Htabs. eapply Hbeta; eauto.
    eapply multi_step; [eassumption|exact Hmf].
Qed.

Definition neutral (t : tm) : Prop :=
  match t with
  | tm_abs _ _ | tm_tabs _ => False
  | _ => True
  end.

Record reducibility_candidate : Type := RC {
  rc_pred : tm -> Prop;
  rc_lc : forall t, rc_pred t -> locally_closed_tm t;
  rc_sn : forall t, rc_pred t -> strongly_normalizing t;
  rc_step : forall t u, rc_pred t -> t --> u -> rc_pred u;
  rc_neutral : forall t, locally_closed_tm t -> neutral t ->
    (forall u, t --> u -> rc_pred u) -> rc_pred t
}.

Definition candidate_env := atom -> reducibility_candidate.

Definition env_set (rho : candidate_env) (X : atom)
    (P : reducibility_candidate) : candidate_env :=
  fun Y => if Nat.eqb X Y then P else rho Y.

Fixpoint ty_size (T : ty) : nat :=
  match T with
  | Ty_BVar _ | Ty_FVar _ => 1
  | Ty_Arrow A B => S (ty_size A + ty_size B)
  | Ty_All A => S (ty_size A)
  end.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => fv_ty A ++ fv_ty B
  | Ty_All A => fv_ty A
  end.

Lemma ty_size_open_var : forall k T X,
  ty_size (open_ty_rec k (Ty_FVar X) T) = ty_size T.
Proof.
  intros k T; revert k; induction T; intros k X; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite IHT1, IHT2; reflexivity.
  - rewrite IHT; reflexivity.
Qed.

Fixpoint red (rho : candidate_env) (bs : list reducibility_candidate)
    (A : ty) (t : tm) {struct A} : Prop :=
  match A with
  | Ty_BVar i =>
      match nth_error bs i with
      | Some P => rc_pred P t
      | None => locally_closed_tm t /\ strongly_normalizing t
      end
  | Ty_FVar X => rc_pred (rho X) t
  | Ty_Arrow A1 B =>
      locally_closed_tm t /\ strongly_normalizing t /\
      (forall s, red rho bs A1 s -> strongly_normalizing (tm_app t s))
  | Ty_All B =>
      locally_closed_tm t /\ strongly_normalizing t /\
      (forall P U, locally_closed_ty U ->
        red rho (P :: bs) B (tm_tapp t U))
  end.

Lemma red_lc : forall rho bs T t, red rho bs T t -> locally_closed_tm t.
Proof.
  intros rho bs T; destruct T; intros t H; cbn [red] in H.
  - destruct (nth_error bs n) as [P|] eqn:E; [eapply rc_lc; eassumption|tauto].
  - eapply rc_lc; exact H.
  - tauto.
  - tauto.
Qed.

Lemma red_sn : forall rho bs T t, red rho bs T t -> strongly_normalizing t.
Proof.
  intros rho bs T; induction T; intros t H; cbn [red] in H.
  - destruct (nth_error bs n) as [P|] eqn:E; [eapply rc_sn; eassumption|tauto].
  - eapply rc_sn; exact H.
  - tauto.
  - tauto.
Qed.

Lemma red_step : forall rho bs T t u,
  red rho bs T t -> t --> u -> red rho bs T u.
Proof.
  intros rho bs T; revert rho bs; induction T; intros rho bs t u Hred Hstep;
    cbn [red] in *.
  - destruct (nth_error bs n) as [P|] eqn:E.
    + eapply rc_step; eauto.
    + destruct Hred as [Hlc Hsn]. split; [eapply lc_step|eapply sn_step]; eauto.
  - eapply rc_step; eauto.
  - destruct Hred as [Hlc [Hsn Happ]]. split.
    + eapply lc_step; eauto.
    + split; [eapply sn_step; eauto|].
      intros s Hs. eapply sn_step; [eapply Happ; eauto|].
      eapply ST_App1; eauto using red_lc.
  - destruct Hred as [Hlc [Hsn Hall]]. split.
    + eapply lc_step; eauto.
    + split; [eapply sn_step; eauto|].
      intros P U HU. eapply IHT; [eapply Hall; eauto|].
      eapply ST_TApp; eauto.
Qed.

Lemma red_multi : forall rho bs T t u,
  red rho bs T t -> t -->* u -> red rho bs T u.
Proof.
  intros rho bs T t u Hred Hm; induction Hm; eauto using red_step.
Qed.

Lemma red_neutral : forall rho bs T t,
  locally_closed_tm t -> neutral t ->
  (forall u, t --> u -> red rho bs T u) -> red rho bs T t.
Proof.
  intros rho bs T; revert rho bs; induction T; intros rho bs t Hlc Hneu Hsteps;
    cbn [red] in *.
  - destruct (nth_error bs n) as [P|] eqn:E.
    + eapply rc_neutral; eauto.
    + split; [exact Hlc|]. constructor. intros u Hstep.
      cbn [red]. apply Hsteps; exact Hstep.
  - eapply rc_neutral; eauto.
  - split; [exact Hlc|]. split.
    + constructor. intros u Hstep.
      destruct (Hsteps u Hstep) as [_ [Hsn _]]. exact Hsn.
    + intros s Hs. eapply sn_app_beta.
      * constructor. intros u Hstep.
        destruct (Hsteps u Hstep) as [_ [Hsn _]]. exact Hsn.
      * eapply red_sn; eauto.
      * eapply red_lc; eauto.
      * intros T0 b f' a' Hmf Hma Habs Hva.
        assert (Hf : red rho bs (Ty_Arrow T1 T2) f').
        { inversion Hmf; subst.
          - simpl in Hneu. contradiction.
          - eapply red_multi; [eapply Hsteps; eassumption|eassumption]. }
        assert (Ha : red rho bs T1 a')
          by (eapply red_multi; [exact Hs|exact Hma]).
        pose proof (red_lc _ _ _ _ Hf) as HfLC.
        destruct Hf as [_ [_ Hcall]].
        apply sn_step with (t:=tm_app f' a'); [eapply Hcall; exact Ha|].
        rewrite Habs. constructor; [rewrite Habs in HfLC; exact HfLC|exact Hva].
  - split; [exact Hlc|]. split.
    + constructor. intros u Hstep.
      destruct (Hsteps u Hstep) as [_ [Hsn _]]. exact Hsn.
    + intros P U HU.
      eapply IHT.
      * unfold locally_closed_tm. constructor; eauto using red_lc.
      * exact I.
      * intros v Hv. inversion Hv; subst; try (simpl in Hneu; contradiction).
        match goal with
        | Hhead : t --> ?t' |- _ =>
            destruct (Hsteps t' Hhead) as [_ [_ Hall]];
            eapply Hall; eassumption
        end.
Qed.

Definition env_equiv_upto (k : nat) (bs1 bs2 : list reducibility_candidate) : Prop :=
  forall i, i < k -> exists P Q,
    nth_error bs1 i = Some P /\ nth_error bs2 i = Some Q /\
    (forall t, rc_pred P t <-> rc_pred Q t).

Lemma env_equiv_cons : forall k P bs1 bs2,
  env_equiv_upto k bs1 bs2 ->
  env_equiv_upto (S k) (P :: bs1) (P :: bs2).
Proof.
  intros k P bs1 bs2 H i Hi. destruct i.
  - exists P, P. simpl. split; [reflexivity|]. split; [reflexivity|].
    intros z; tauto.
  - assert (i < k) by lia. specialize (H i H0).
    destruct H as [P1 [P2 [E1 [E2 Heq]]]].
    exists P1, P2. simpl. split; [exact E1|]. split; [exact E2|exact Heq].
Qed.

Lemma red_env_equiv : forall rho k T t,
  lc_ty_at k T -> forall bs1 bs2,
  env_equiv_upto k bs1 bs2 ->
  (red rho bs1 T t <-> red rho bs2 T t).
Proof.
  intros rho k T; revert rho k; induction T; intros rho k t Hlc bs1 bs2 Heq.
  - cbn [red]. inversion Hlc; subst.
    destruct (Heq n) as [P [Q [E1 [E2 Hpq]]]]; [lia|].
    rewrite E1, E2. exact (Hpq t).
  - cbn [red]. tauto.
  - assert (HlcA : lc_ty_at k T1) by (inversion Hlc; assumption).
    cbn [red]. split.
    + intros [Hclosed [Hsn Happ]]. split; [exact Hclosed|]. split; [exact Hsn|].
      intros s Hs. apply Happ.
      eapply (proj2 (IHT1 rho k s HlcA bs1 bs2 Heq)); exact Hs.
    + intros [Hclosed [Hsn Happ]]. split; [exact Hclosed|]. split; [exact Hsn|].
      intros s Hs. apply Happ.
      eapply (proj1 (IHT1 rho k s HlcA bs1 bs2 Heq)); exact Hs.
  - assert (HlcBody : lc_ty_at (S k) T) by (inversion Hlc; assumption).
    cbn [red]. split.
    + intros [Hclosed [Hsn Hall]]. split; [exact Hclosed|]. split; [exact Hsn|].
      intros P U HU.
      eapply (proj1 (IHT rho (S k) (tm_tapp t U) HlcBody (P :: bs1) (P :: bs2)
        (env_equiv_cons k P bs1 bs2 Heq))). apply Hall; exact HU.
    + intros [Hclosed [Hsn Hall]]. split; [exact Hclosed|]. split; [exact Hsn|].
      intros P U HU.
      eapply (proj2 (IHT rho (S k) (tm_tapp t U) HlcBody (P :: bs1) (P :: bs2)
        (env_equiv_cons k P bs1 bs2 Heq))). apply Hall; exact HU.
 Qed.

Lemma red_free_env_irrel : forall rho X P bs T t,
  ~ In X (fv_ty T) ->
  (red rho bs T t <-> red (env_set rho X P) bs T t).
Proof.
  intros rho X P bs T; revert bs; induction T; intros bs t Hfresh; cbn [red].
  - tauto.
  - unfold env_set. simpl. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. simpl; auto.
    + tauto.
  - assert (H1 : ~ In X (fv_ty T1)) by (intro H; apply Hfresh; apply in_or_app; tauto).
    assert (H2 : ~ In X (fv_ty T2)) by (intro H; apply Hfresh; apply in_or_app; tauto).
    split.
    + intros [Hlc [Hsn Hfun]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros s Hs. apply Hfun. apply (proj2 (IHT1 bs s H1)). exact Hs.
    + intros [Hlc [Hsn Hfun]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros s Hs. apply Hfun. apply (proj1 (IHT1 bs s H1)). exact Hs.
  - assert (Hbody : ~ In X (fv_ty T)) by (intro H; apply Hfresh; exact H).
    split.
    + intros [Hlc [Hsn Hall]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros Q U HU. apply (proj1 (IHT (Q :: bs) (tm_tapp t U) Hbody)).
      apply Hall; exact HU.
    + intros [Hlc [Hsn Hall]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros Q U HU. apply (proj2 (IHT (Q :: bs) (tm_tapp t U) Hbody)).
      apply Hall; exact HU.
Qed.

Fixpoint insert_candidate (k : nat) (P : reducibility_candidate)
    (bs : list reducibility_candidate) : list reducibility_candidate :=
  match k, bs with
  | 0, _ => P :: bs
  | S k', Q :: bs' => Q :: insert_candidate k' P bs'
  | S _, [] => []
  end.

Lemma insert_candidate_cons : forall k P Q bs,
  insert_candidate (S k) P (Q :: bs) = Q :: insert_candidate k P bs.
Proof. reflexivity. Qed.

Lemma env_equiv_upto_zero : forall bs1 bs2, env_equiv_upto 0 bs1 bs2.
Proof. intros bs1 bs2 i Hi; lia. Qed.

Lemma nth_error_insert_lt : forall k n P bs,
  n < k -> nth_error (insert_candidate k P bs) n = nth_error bs n.
Proof.
  induction k; intros n P bs H; [lia|]. destruct bs as [|Q bs].
  - simpl. destruct n; simpl; [reflexivity|].
    destruct k; simpl; destruct n; simpl; auto.
  - destruct n; simpl; [reflexivity|]. apply IHk. lia.
Qed.

Lemma nth_error_insert_eq : forall k P bs,
  k <= length bs ->
  nth_error (insert_candidate k P bs) k = Some P.
Proof.
  induction k; intros P bs H; simpl; [reflexivity|].
  destruct bs as [|Q bs]; simpl in *; [lia|].
  simpl. apply IHk. lia.
Qed.

Lemma red_open_bound : forall rho k bs T U C t,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  k <= length bs ->
  (forall z, red rho bs U z <-> rc_pred C z) ->
  (red rho bs (open_ty_rec k U T) t <->
   red rho (insert_candidate k C bs) T t).
Proof.
  intros rho k bs T; revert rho k bs.
  induction T; intros rho k bs U C t Hlc HU Hlen HC.
  - inversion Hlc as [k' i Hbound| | |]; subst.
    cbn [open_ty_rec red]. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      rewrite nth_error_insert_eq by exact Hlen. simpl. apply HC.
    + apply Nat.eqb_neq in E. rewrite (nth_error_insert_lt k n C bs) by lia.
      tauto.
  - cbn [open_ty_rec red]. tauto.
  - inversion Hlc as [| |? ? ? H1 H2|]; subst.
    cbn [open_ty_rec red]. split.
    + intros [Hcl [Hsn Happ]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros s Hs. apply Happ. apply (proj2 (IHT1 rho k bs U C s H1 HU Hlen HC)). exact Hs.
    + intros [Hcl [Hsn Happ]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros s Hs. apply Happ. apply (proj1 (IHT1 rho k bs U C s H1 HU Hlen HC)). exact Hs.
  - assert (Hbody : lc_ty_at (S (S k)) T) by (inversion Hlc; assumption).
    cbn [open_ty_rec red]. split.
    + intros [Hcl [Hsn Hall]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros P V HV.
      assert (HC' : forall z, red rho (P :: bs) U z <-> rc_pred C z).
      { intro z. transitivity (red rho bs U z).
        - exact (red_env_equiv rho 0 U z HU (P :: bs) bs (env_equiv_upto_zero _ _)).
        - apply HC. }
      change (red rho (P :: insert_candidate k C bs) T (tm_tapp t V)).
      apply (proj1 (IHT rho (S k) (P :: bs) U C (tm_tapp t V) Hbody HU
        ltac:(simpl; lia) HC')).
      apply Hall; exact HV.
    + intros [Hcl [Hsn Hall]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros P V HV.
      assert (HC' : forall z, red rho (P :: bs) U z <-> rc_pred C z).
      { intro z. transitivity (red rho bs U z).
        - exact (red_env_equiv rho 0 U z HU (P :: bs) bs (env_equiv_upto_zero _ _)).
        - apply HC. }
      apply (proj2 (IHT rho (S k) (P :: bs) U C (tm_tapp t V) Hbody HU
        ltac:(simpl; lia) HC')).
      apply Hall; exact HV.
Qed.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => fv_tm b
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs b => fv_tm b
  | tm_tapp b _ => fv_tm b
  end.

Definition tm_env := atom -> tm.

Definition tm_env_set (xi : tm_env) (x : atom) (s : tm) : tm_env :=
  fun y => if Nat.eqb x y then s else xi y.

Fixpoint subst_env (xi : tm_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => xi x
  | tm_abs T b => tm_abs T (subst_env xi b)
  | tm_app t1 t2 => tm_app (subst_env xi t1) (subst_env xi t2)
  | tm_tabs b => tm_tabs (subst_env xi b)
  | tm_tapp b T => tm_tapp (subst_env xi b) T
  end.

Lemma open_tm_rec_lc_at : forall K d k u t,
  d <= k -> lc_tm_at K d t -> open_tm_rec k u t = t.
Proof.
  intros K d k u t Hnk Hlc. revert K d k u Hnk Hlc.
  induction t; intros K d k u Hnk Hlc; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E; [|reflexivity].
    apply Nat.eqb_eq in E. lia.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    eapply (IHt K (S d) (S k) u); [lia|exact H4].
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - inversion Hlc; subst. f_equal. eapply IHt; [exact Hnk|eassumption].
  - inversion Hlc; subst. f_equal. eapply IHt; [exact Hnk|eassumption].
Qed.

Lemma open_tm_rec_lc : forall k u t,
  locally_closed_tm t -> open_tm_rec k u t = t.
Proof.
  intros k u t H. unfold locally_closed_tm in H.
  apply (open_tm_rec_lc_at 0 0 k u t); [lia|exact H].
Qed.

Lemma subst_env_open : forall k t xi x s,
  (forall y, locally_closed_tm (xi y)) -> locally_closed_tm s ->
  ~ In x (fv_tm t) ->
  subst_env (tm_env_set xi x s) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k s (subst_env xi t).
Proof.
  intros k t; revert k; induction t; intros k xi x s Hxi Hs Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl; [unfold tm_env_set; rewrite Nat.eqb_refl|]; reflexivity.
  - simpl in Hfresh. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. simpl; auto.
    + unfold tm_env_set. simpl. rewrite E. symmetry. eapply open_tm_rec_lc; apply Hxi.
  - f_equal. apply IHt; assumption.
  - assert (H1 : ~ In x (fv_tm t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k xi x s Hxi Hs H1).
    rewrite (IHt2 k xi x s Hxi Hs H2). reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
Qed.

Lemma lookup_update_same : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros; simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_update_neq : forall Gamma x y T,
  x <> y -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x y T Hneq. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - reflexivity.
Qed.

Definition term_env_satisfies (rho : candidate_env) (Gamma : context) (xi : tm_env) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> red rho [] T (xi x).

Lemma term_env_satisfies_update : forall rho Gamma xi x T s,
  term_env_satisfies rho Gamma xi ->
  red rho [] T s ->
  ~ In x (map fst Gamma) ->
  term_env_satisfies rho (update Gamma x T) (tm_env_set xi x s).
Proof.
  intros rho Gamma xi x T s Hsat Hs Hfresh y A Hlookup.
  unfold tm_env_set. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; subst. rewrite lookup_update_same in Hlookup.
    inversion Hlookup; subst. exact Hs.
  - apply Nat.eqb_neq in E. apply Hsat.
    rewrite lookup_update_neq in Hlookup; [exact Hlookup|congruence].
Qed.

Inductive etm : Type :=
| e_bvar : nat -> etm
| e_fvar : atom -> etm
| e_abs : etm -> etm
| e_app : etm -> etm -> etm
| e_tabs : etm -> etm
| e_tapp : etm -> etm.

Fixpoint erase (t : tm) : etm :=
  match t with
  | tm_bvar i => e_bvar i
  | tm_fvar x => e_fvar x
  | tm_abs _ b => e_abs (erase b)
  | tm_app t1 t2 => e_app (erase t1) (erase t2)
  | tm_tabs b => e_tabs (erase b)
  | tm_tapp b _ => e_tapp (erase b)
  end.

Fixpoint eopen_rec (k : nat) (u t : etm) : etm :=
  match t with
  | e_bvar i => if Nat.eqb k i then u else e_bvar i
  | e_fvar x => e_fvar x
  | e_abs b => e_abs (eopen_rec (S k) u b)
  | e_app t1 t2 => e_app (eopen_rec k u t1) (eopen_rec k u t2)
  | e_tabs b => e_tabs (eopen_rec k u b)
  | e_tapp b => e_tapp (eopen_rec k u b)
  end.

Definition eopen (t u : etm) := eopen_rec 0 u t.

Inductive elc_at : nat -> etm -> Prop :=
| elc_bvar : forall k i, i < k -> elc_at k (e_bvar i)
| elc_fvar : forall k x, elc_at k (e_fvar x)
| elc_abs : forall k b, elc_at (S k) b -> elc_at k (e_abs b)
| elc_app : forall k a b, elc_at k a -> elc_at k b -> elc_at k (e_app a b)
| elc_tabs : forall k b, elc_at k b -> elc_at k (e_tabs b)
| elc_tapp : forall k b, elc_at k b -> elc_at k (e_tapp b).

Definition eclosed (t : etm) := elc_at 0 t.

Inductive evalue : etm -> Prop :=
| ev_abs : forall b, eclosed (e_abs b) -> evalue (e_abs b)
| ev_tabs : forall b, eclosed (e_tabs b) -> evalue (e_tabs b).

Reserved Notation "a '==>' b" (at level 40).
Inductive estep : etm -> etm -> Prop :=
| ES_AppAbs : forall b v, eclosed (e_abs b) -> evalue v ->
    e_app (e_abs b) v ==> eopen b v
| ES_App1 : forall a a' b, a ==> a' -> eclosed b -> e_app a b ==> e_app a' b
| ES_App2 : forall v b b', evalue v -> b ==> b' -> e_app v b ==> e_app v b'
| ES_TAppTabs : forall b, eclosed (e_tabs b) -> e_tapp (e_tabs b) ==> b
| ES_TApp : forall a a', a ==> a' -> e_tapp a ==> e_tapp a'
where "a '==>' b" := (estep a b).

Inductive emulti : etm -> etm -> Prop :=
| emulti_refl : forall a, emulti a a
| emulti_step : forall a b c, a ==> b -> emulti b c -> emulti a c.

Inductive esn : etm -> Prop :=
| ESN_intro : forall a, (forall b, a ==> b -> esn b) -> esn a.

Lemma esn_step : forall a b, esn a -> a ==> b -> esn b.
Proof. intros a b H; inversion H; eauto. Qed.

Lemma esn_from_steps : forall a, (forall b, a ==> b -> esn b) -> esn a.
Proof. intros; constructor; assumption. Qed.

Lemma emulti_refl' : forall a, emulti a a.
Proof. constructor. Qed.

Lemma emulti_trans : forall a b c, emulti a b -> emulti b c -> emulti a c.
Proof. intros a b c H; induction H; eauto using emulti. Qed.

Lemma eopen_lc_at : forall d k u t,
  d <= k -> elc_at d t -> eopen_rec k u t = t.
Proof.
  intros d k u t Hdk Hlc. revert d k u Hdk Hlc.
  induction t; intros d k u Hdk Hlc; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply (IHt (S d) (S k) u); [lia|eassumption].
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eauto.
  - inversion Hlc; subst. f_equal. eapply IHt; [exact Hdk|eassumption].
  - inversion Hlc; subst. f_equal. eapply IHt; [exact Hdk|eassumption].
Qed.

Lemma eopen_lc : forall k u t, eclosed t -> eopen_rec k u t = t.
Proof.
  intros k u t H; unfold eclosed in H.
  apply (eopen_lc_at 0 k u t); [lia|exact H].
Qed.

Lemma elc_weaken : forall k t, elc_at k t -> elc_at (S k) t.
Proof. intros k t H; induction H; eauto using elc_at; try lia. Qed.

Lemma elc_open : forall k t u,
  elc_at (S k) t -> elc_at k u -> elc_at k (eopen_rec k u t).
Proof.
  intros k t; revert k; induction t; intros k u Ht Hu; simpl in *.
  - inversion Ht; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact Hu.
    + apply elc_bvar. inversion Ht; subst. apply Nat.eqb_neq in E; lia.
  - inversion Ht; constructor.
  - inversion Ht; subst. econstructor. eapply (IHt (S k) u).
    + exact H1.
    + eapply elc_weaken; exact Hu.
  - inversion Ht; subst. econstructor.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
  - inversion Ht; subst. econstructor. eapply IHt; eauto.
  - inversion Ht; subst. econstructor. eapply IHt; eauto.
Qed.

Lemma elc_step : forall a b, eclosed a -> a ==> b -> eclosed b.
Proof.
  intros a b Hlc Hst. unfold eclosed in *. induction Hst.
  - inversion Hlc; subst. inversion H4; subst. eapply elc_open; eassumption.
  - inversion Hlc; subst. econstructor; [eapply IHHst; eassumption|assumption].
  - inversion Hlc; subst. econstructor; [assumption|eapply IHHst; eassumption].
  - inversion Hlc; subst. inversion H2; subst. assumption.
  - inversion Hlc; subst. econstructor. eapply IHHst. eassumption.
Qed.

Lemma elc_multi : forall a b, eclosed a -> emulti a b -> eclosed b.
Proof. intros a b Hlc H; induction H; eauto using elc_step. Qed.

Lemma esn_app_beta : forall f a,
  esn f -> esn a -> eclosed a ->
  (forall b f' a', emulti f f' -> emulti a a' -> f' = e_abs b -> evalue a' ->
    esn (eopen b a')) -> esn (e_app f a).
Proof.
  intros f a Hf; revert a.
  induction Hf as [f Hfsteps IHf]; intros a Ha Hla Hbeta.
  induction Ha as [a Hasteps IHa].
  constructor; intros u Hu; inversion Hu; subst.
  - eapply Hbeta; eauto using emulti_refl'.
  - eapply IHf; [exact H1|constructor; exact Hasteps|exact Hla|].
    intros b f' a2 Hmf Hma Habs Hval. eapply Hbeta; eauto.
    eapply emulti_step; [eassumption|exact Hmf].
  - eapply IHa; [assumption|eapply (elc_step _ _); eauto|].
    intros b f' a2 Hmf Hma Habs Hval. eapply Hbeta; eauto.
    eapply emulti_step; [eassumption|exact Hma].
Qed.

Definition eneutral (t : etm) : Prop :=
  match t with e_abs _ | e_tabs _ => False | _ => True end.

Record ecandidate : Type := EC {
  ec_pred : etm -> Prop;
  ec_lc : forall t, ec_pred t -> eclosed t;
  ec_sn : forall t, ec_pred t -> esn t;
  ec_step : forall t u, ec_pred t -> t ==> u -> ec_pred u;
  ec_neutral : forall t, eclosed t -> eneutral t ->
    (forall u, t ==> u -> ec_pred u) -> ec_pred t
}.

Definition ecandidate_env := atom -> ecandidate.

Definition ecandidate_set (rho : ecandidate_env) (X : atom) (P : ecandidate) : ecandidate_env :=
  fun Y => if Nat.eqb X Y then P else rho Y.

Fixpoint ered (rho : ecandidate_env) (bs : list ecandidate) (A : ty) (t : etm)
    {struct A} : Prop :=
  match A with
  | Ty_BVar i =>
      match nth_error bs i with
      | Some P => ec_pred P t
      | None => eclosed t /\ esn t
      end
  | Ty_FVar X => ec_pred (rho X) t
  | Ty_Arrow A B =>
      eclosed t /\ esn t /\ (forall s, ered rho bs A s -> ered rho bs B (e_app t s))
  | Ty_All B =>
      eclosed t /\ esn t /\ (forall P, ered rho (P :: bs) B (e_tapp t))
  end.

Lemma ered_lc : forall rho bs A t, ered rho bs A t -> eclosed t.
Proof.
  intros rho bs A; destruct A; intros t H; cbn [ered] in H.
  - destruct (nth_error bs n) as [P|]; [eapply ec_lc; eassumption|tauto].
  - eapply ec_lc; exact H.
  - tauto.
  - tauto.
Qed.

Lemma ered_sn : forall rho bs A t, ered rho bs A t -> esn t.
Proof.
  intros rho bs A; induction A; intros t H; cbn [ered] in H.
  - destruct (nth_error bs n) as [P|]; [eapply ec_sn; eassumption|tauto].
  - eapply ec_sn; exact H.
  - tauto.
  - tauto.
Qed.

Lemma ered_step : forall rho bs A t u,
  ered rho bs A t -> t ==> u -> ered rho bs A u.
Proof.
  intros rho bs A; revert rho bs; induction A; intros rho bs t u Hred Hst;
    cbn [ered] in *.
  - destruct (nth_error bs n) as [P|] eqn:E.
    + eapply ec_step; eauto.
    + destruct Hred as [Hlc Hsn]. split; [eapply elc_step|eapply esn_step]; eauto.
  - eapply ec_step; eauto.
  - destruct Hred as [Hlc [Hsn Happ]]. split; [eapply elc_step; eauto|].
    split; [eapply esn_step; eauto|]. intros s Hs.
    eapply IHA2; [apply Happ; exact Hs|].
    eapply ES_App1; eauto using ered_lc.
  - destruct Hred as [Hlc [Hsn Hall]]. split; [eapply elc_step; eauto|].
    split; [eapply esn_step; eauto|]. intros P.
    eapply IHA; [eapply Hall|]; eauto using ES_TApp.
Qed.

Lemma ered_multi : forall rho bs A t u,
  ered rho bs A t -> emulti t u -> ered rho bs A u.
Proof. intros rho bs A t u Hred H; induction H; eauto using ered_step. Qed.

Lemma ered_neutral : forall rho bs A t,
  eclosed t -> eneutral t ->
  (forall u, t ==> u -> ered rho bs A u) -> ered rho bs A t.
Proof.
  intros rho bs A; revert rho bs; induction A; intros rho bs t Hlc Hneu Hsteps;
    cbn [ered] in *.
  - destruct (nth_error bs n) as [P|] eqn:E.
    + eapply ec_neutral; eauto.
    + split; [exact Hlc|]. constructor; intros u Hst.
      cbn [ered]. apply Hsteps; exact Hst.
  - eapply ec_neutral; eauto.
  - split; [exact Hlc|]. split.
    + constructor; intros u Hst. destruct (Hsteps u Hst) as [_ [Hsn _]]. exact Hsn.
    + assert (Happly : forall s, ered rho bs A1 s -> ered rho bs A2 (e_app t s)).
      { intros s Hs. pose proof (ered_sn rho bs A1 s Hs) as HsSN.
        generalize dependent Hs. induction HsSN as [s Hargsteps IHarg]; intros Hs.
        eapply IHA2.
        - unfold eclosed. econstructor; [exact Hlc|eapply ered_lc; exact Hs].
        - exact I.
        - intros v Hv. inversion Hv; subst.
          + simpl in Hneu. contradiction.
          + destruct (Hsteps _ H1) as [_ [_ Hcall]]. eapply Hcall; exact Hs.
          + eapply IHarg; [exact H3|]. eapply ered_step; eauto.
      }
      intros s Hs. apply Happly. exact Hs.
  - split; [exact Hlc|]. split.
    + constructor; intros u Hst. destruct (Hsteps u Hst) as [_ [Hsn _]]. exact Hsn.
    + intros P. eapply IHA.
      * unfold eclosed. constructor; eauto using ered_lc.
      * exact I.
      * intros v Hv. inversion Hv; subst; try (simpl in Hneu; contradiction).
        match goal with
        | Hhead : @estep t ?t' |- _ =>
            destruct (Hsteps t' Hhead) as [_ [_ Hall]]; eapply Hall
        end.
Qed.

Lemma ered_app : forall rho bs A B f s,
  ered rho bs (Ty_Arrow A B) f -> ered rho bs A s ->
  ered rho bs B (e_app f s).
Proof.
  intros rho bs A B f s [Hflc [_ Hcall]] Hs.
  eapply ered_neutral.
  - unfold eclosed. econstructor; [exact Hflc|eapply ered_lc; exact Hs].
  - exact I.
  - intros u Hu. inversion Hu; subst.
    + eapply ered_step; [eapply Hcall; exact Hs|].
      apply ES_AppAbs; assumption.
    + eapply ered_step; [apply Hcall; exact Hs|].
      eapply ES_App1; eauto using ered_lc.
    + eapply Hcall. eapply ered_step; eauto.
Qed.

Definition eenv_equiv_upto (k : nat) (bs1 bs2 : list ecandidate) : Prop :=
  forall i, i < k -> exists P Q,
    nth_error bs1 i = Some P /\ nth_error bs2 i = Some Q /\
    (forall t, ec_pred P t <-> ec_pred Q t).

Lemma eenv_equiv_zero : forall bs1 bs2, eenv_equiv_upto 0 bs1 bs2.
Proof. intros bs1 bs2 i Hi; lia. Qed.

Lemma eenv_equiv_cons : forall k P bs1 bs2,
  eenv_equiv_upto k bs1 bs2 ->
  eenv_equiv_upto (S k) (P :: bs1) (P :: bs2).
Proof.
  intros k P bs1 bs2 H i Hi. destruct i.
  - exists P,P. simpl. split; [reflexivity|]. split; [reflexivity|]. intros t; tauto.
  - assert (i < k) by lia. specialize (H i H0).
    destruct H as [P1 [P2 [E1 [E2 Heq]]]].
    exists P1,P2. simpl. split; [exact E1|]. split; [exact E2|exact Heq].
Qed.

Lemma ered_env_equiv : forall rho k A t,
  lc_ty_at k A -> forall bs1 bs2, eenv_equiv_upto k bs1 bs2 ->
  (ered rho bs1 A t <-> ered rho bs2 A t).
Proof.
  intros rho k A; revert rho k; induction A; intros rho k t Hlc bs1 bs2 Heq.
  - cbn [ered]. inversion Hlc; subst.
    destruct (Heq n) as [P [Q [E1 [E2 Hpq]]]]; [lia|].
    rewrite E1,E2. exact (Hpq t).
  - cbn [ered]. tauto.
  - assert (Hsub : lc_ty_at k A1) by (inversion Hlc; assumption).
    assert (HsubB : lc_ty_at k A2) by (inversion Hlc; assumption).
    cbn [ered]. split.
    + intros [Hcl [Hsn Hfun]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros s Hs.
      pose proof (proj2 (IHA1 rho k s Hsub bs1 bs2 Heq) Hs) as Hs1.
      apply (proj1 (IHA2 rho k (e_app t s) HsubB bs1 bs2 Heq)).
      apply Hfun; exact Hs1.
    + intros [Hcl [Hsn Hfun]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros s Hs.
      pose proof (proj1 (IHA1 rho k s Hsub bs1 bs2 Heq) Hs) as Hs1.
      apply (proj2 (IHA2 rho k (e_app t s) HsubB bs1 bs2 Heq)).
      apply Hfun; exact Hs1.
  - assert (Hbody : lc_ty_at (S k) A) by (inversion Hlc; assumption).
    cbn [ered]. split.
    + intros [Hcl [Hsn Hall]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros P. eapply (proj1 (IHA rho (S k) (e_tapp t) Hbody (P::bs1) (P::bs2)
        (eenv_equiv_cons k P bs1 bs2 Heq))). apply Hall.
    + intros [Hcl [Hsn Hall]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros P. eapply (proj2 (IHA rho (S k) (e_tapp t) Hbody (P::bs1) (P::bs2)
        (eenv_equiv_cons k P bs1 bs2 Heq))). apply Hall.
Qed.

Lemma ered_free_env_irrel : forall rho X P bs A t,
  ~ In X (fv_ty A) ->
  (ered rho bs A t <-> ered (ecandidate_set rho X P) bs A t).
Proof.
  intros rho X P bs A; revert bs; induction A; intros bs t Hfresh; cbn [ered].
  - tauto.
  - unfold ecandidate_set. simpl. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. simpl; auto.
    + tauto.
  - assert (H1 : ~ In X (fv_ty A1)) by (intro H; apply Hfresh; apply in_or_app; tauto).
    assert (H2 : ~ In X (fv_ty A2)) by (intro H; apply Hfresh; apply in_or_app; tauto).
    split.
    + intros [Hcl [Hsn Hfun]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros s Hs. pose proof (proj2 (IHA1 bs s H1) Hs) as Hs0.
      apply (proj1 (IHA2 bs (e_app t s) H2)). apply Hfun; exact Hs0.
    + intros [Hcl [Hsn Hfun]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros s Hs. pose proof (proj1 (IHA1 bs s H1) Hs) as Hs0.
      apply (proj2 (IHA2 bs (e_app t s) H2)). apply Hfun; exact Hs0.
  - assert (Hb : ~ In X (fv_ty A)) by (intro H; apply Hfresh; exact H).
    split.
    + intros [Hcl [Hsn Hall]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros Q. apply (proj1 (IHA (Q::bs) (e_tapp t) Hb)). apply Hall.
    + intros [Hcl [Hsn Hall]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros Q. apply (proj2 (IHA (Q::bs) (e_tapp t) Hb)). apply Hall.
Qed.

Fixpoint einsert (k : nat) (P : ecandidate) (bs : list ecandidate) : list ecandidate :=
  match k,bs with
  | 0,_ => P::bs
  | S k',Q::bs' => Q::einsert k' P bs'
  | S _,[] => []
  end.

Lemma en_error_insert_lt : forall k n P bs,
  n < k -> nth_error (einsert k P bs) n = nth_error bs n.
Proof.
  induction k; intros n P bs H; [lia|]. destruct bs as [|Q bs].
  - simpl. destruct n; simpl; [reflexivity|]. destruct k; simpl; destruct n; simpl; auto.
  - destruct n; simpl; [reflexivity|]. apply IHk. lia.
Qed.

Lemma en_error_insert_eq : forall k P bs,
  k <= length bs -> nth_error (einsert k P bs) k = Some P.
Proof.
  induction k; intros P bs H; simpl; [reflexivity|].
  destruct bs as [|Q bs]; simpl in *; [lia|]. simpl. apply IHk. lia.
Qed.

Lemma ered_open_bound : forall rho k bs A U C t,
  lc_ty_at (S k) A -> locally_closed_ty U -> k <= length bs ->
  (forall z, ered rho bs U z <-> ec_pred C z) ->
  (ered rho bs (open_ty_rec k U A) t <-> ered rho (einsert k C bs) A t).
Proof.
  intros rho k bs A; revert rho k bs; induction A; intros rho k bs U C t Hlc HU Hlen HC.
  - inversion Hlc; subst. cbn [open_ty_rec ered]. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. rewrite en_error_insert_eq by exact Hlen. simpl. apply HC.
    + apply Nat.eqb_neq in E. rewrite (en_error_insert_lt k n C bs) by lia. tauto.
  - cbn [open_ty_rec ered]. tauto.
  - assert (H1 : lc_ty_at (S k) A1) by (inversion Hlc; assumption).
    assert (H2 : lc_ty_at (S k) A2) by (inversion Hlc; assumption).
    cbn [open_ty_rec ered]. split.
    + intros [Hcl [Hsn Hfun]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros s Hs. pose proof (proj2 (IHA1 rho k bs U C s H1 HU Hlen HC) Hs) as Hs0.
      apply (proj1 (IHA2 rho k bs U C (e_app t s) H2 HU Hlen HC)). apply Hfun; exact Hs0.
    + intros [Hcl [Hsn Hfun]]. split; [exact Hcl|]. split; [exact Hsn|].
      intros s Hs. pose proof (proj1 (IHA1 rho k bs U C s H1 HU Hlen HC) Hs) as Hs0.
      apply (proj2 (IHA2 rho k bs U C (e_app t s) H2 HU Hlen HC)). apply Hfun; exact Hs0.
  - assert (Hbody : lc_ty_at (S (S k)) A) by (inversion Hlc; assumption).
    cbn [open_ty_rec ered]. split.
    + intros [Hcl [Hsn Hall]]. split; [exact Hcl|]. split; [exact Hsn|]. intros P.
      assert (HC' : forall z, ered rho (P::bs) U z <-> ec_pred C z).
      { intro z. transitivity (ered rho bs U z).
        - exact (ered_env_equiv rho 0 U z HU (P::bs) bs (eenv_equiv_zero _ _)).
        - apply HC. }
      change (ered rho (P :: einsert k C bs) A (e_tapp t)).
      apply (proj1 (IHA rho (S k) (P::bs) U C (e_tapp t) Hbody HU ltac:(simpl; lia) HC')).
      apply Hall.
    + intros [Hcl [Hsn Hall]]. split; [exact Hcl|]. split; [exact Hsn|]. intros P.
      assert (HC' : forall z, ered rho (P::bs) U z <-> ec_pred C z).
      { intro z. transitivity (ered rho bs U z).
        - exact (ered_env_equiv rho 0 U z HU (P::bs) bs (eenv_equiv_zero _ _)).
        - apply HC. }
      apply (proj2 (IHA rho (S k) (P::bs) U C (e_tapp t) Hbody HU ltac:(simpl; lia) HC')).
      apply Hall.
Qed.

Definition eenv := atom -> etm.

Definition eenv_set (xi : eenv) (x : atom) (s : etm) : eenv :=
  fun y => if Nat.eqb x y then s else xi y.

Fixpoint esubst_env (xi : eenv) (t : etm) : etm :=
  match t with
  | e_bvar i => e_bvar i
  | e_fvar x => xi x
  | e_abs b => e_abs (esubst_env xi b)
  | e_app a b => e_app (esubst_env xi a) (esubst_env xi b)
  | e_tabs b => e_tabs (esubst_env xi b)
  | e_tapp b => e_tapp (esubst_env xi b)
  end.

Lemma esubst_open : forall k t xi x s,
  (forall y, eclosed (xi y)) -> eclosed s -> ~ In x (fv_tm t) ->
  esubst_env (eenv_set xi x s) (eopen_rec k (e_fvar x) (erase t)) =
  eopen_rec k s (esubst_env xi (erase t)).
Proof.
  intros k t; revert k; induction t; intros k xi x s Hxi Hs Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl; [unfold eenv_set; rewrite Nat.eqb_refl|]; reflexivity.
  - simpl in Hfresh. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. simpl; auto.
    + unfold eenv_set. simpl. rewrite E. symmetry. apply eopen_lc. apply Hxi.
  - f_equal. apply IHt; assumption.
  - assert (H1 : ~ In x (fv_tm t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    rewrite (IHt1 k xi x s Hxi Hs H1), (IHt2 k xi x s Hxi Hs H2). reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
Qed.

Lemma erase_open_tm : forall k t u,
  erase (open_tm_rec k u t) = eopen_rec k (erase u) (erase t).
Proof.
  intros k t; revert k; induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - rewrite IHt1, IHt2. reflexivity.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
Qed.

Lemma erase_open_tm_ty_rec : forall k t U,
  erase (open_tm_ty_rec k U t) = erase t.
Proof.
  intros k t; revert k; induction t; intros k U; simpl; try reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
Qed.

Lemma erase_open_tm_ty : forall t U, erase (open_tm_ty t U) = erase t.
Proof. intros; apply erase_open_tm_ty_rec. Qed.

Lemma erase_lc : forall K k t, lc_tm_at K k t -> elc_at k (erase t).
Proof.
  intros K k t H; induction H; simpl; eauto using elc_at.
Qed.

Lemma erase_value : forall v, value v -> evalue (erase v).
Proof.
  intros v H; inversion H; subst.
  - apply ev_abs. exact (erase_lc 0 0 _ H0).
  - apply ev_tabs. exact (erase_lc 0 0 _ H0).
Qed.

Lemma erase_step : forall t u, t --> u -> erase t ==> erase u.
Proof.
  intros t u H; induction H.
  - simpl. unfold open_tm. rewrite erase_open_tm.
    apply ES_AppAbs; [exact (erase_lc 0 0 _ H)|apply erase_value; assumption].
  - simpl. apply ES_App1; [assumption|exact (erase_lc 0 0 _ H0)].
  - simpl. apply ES_App2; [apply erase_value; assumption|assumption].
  - simpl. rewrite erase_open_tm_ty. apply ES_TAppTabs. exact (erase_lc 0 0 _ H).
  - simpl. apply ES_TApp. assumption.
Qed.

Lemma esn_erases_to_sn_gen : forall e, esn e -> forall t, erase t = e -> strongly_normalizing t.
Proof.
  intros e Hsn; induction Hsn as [a Hsteps IH]; intros t Heq.
  constructor. intros u Hstep.
  pose proof (erase_step _ _ Hstep) as Hest. rewrite Heq in Hest.
  eapply IH; [exact Hest|reflexivity].
Qed.

Lemma esn_erases_to_sn : forall t, esn (erase t) -> strongly_normalizing t.
Proof. intros t H; eapply esn_erases_to_sn_gen; eauto. Qed.

Lemma elc_weaken_to : forall i k t, i <= k -> elc_at i t -> elc_at k t.
Proof.
  intros i k t Hle Hlc. induction Hle; auto using elc_weaken.
Qed.

Lemma esubst_lc : forall k t xi,
  elc_at k t -> (forall x, eclosed (xi x)) -> elc_at k (esubst_env xi t).
Proof.
  intros k t xi Hlc; induction Hlc; intros Hxi; simpl.
  - constructor. assumption.
  - eapply (elc_weaken_to 0 k (xi x)); [lia|apply Hxi].
  - constructor. apply IHHlc. exact Hxi.
  - econstructor; [apply IHHlc1|apply IHHlc2]; exact Hxi.
  - constructor. apply IHHlc. exact Hxi.
  - constructor. apply IHHlc. exact Hxi.
Qed.

Lemma esubst_id : forall t, esubst_env (fun x => e_fvar x) t = t.
Proof.
  induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; reflexivity.
Qed.

Definition ered_env_sat (rho : ecandidate_env) (Gamma : context) (xi : eenv) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> ered rho [] T (xi x).

Definition fv_context (Gamma : context) : list atom :=
  concat (map fv_ty (map snd Gamma)).

Lemma lookup_in_map_snd : forall Gamma x T,
  lookup_context x Gamma = Some T -> In T (map snd Gamma).
Proof.
  induction Gamma as [|[y A] Gamma IH]; intros x T H; simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - inversion H; subst. simpl. auto.
  - simpl. right. eapply IH; exact H.
Qed.

Lemma lookup_fv_context : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) -> In X (fv_context Gamma).
Proof.
  intros Gamma x T X Hlook Hfv. unfold fv_context.
  apply in_concat. exists (fv_ty T). split.
  - apply in_map. apply lookup_in_map_snd with (x:=x); exact Hlook.
  - exact Hfv.
Qed.

Lemma ered_env_sat_free_update : forall rho Gamma xi X P,
  ered_env_sat rho Gamma xi -> ~ In X (fv_context Gamma) ->
  ered_env_sat (ecandidate_set rho X P) Gamma xi.
Proof.
  intros rho Gamma xi X P Hsat Hfresh x T Hlook.
  pose proof (Hsat x T Hlook) as Hr.
  assert (Hnot : ~ In X (fv_ty T)).
  { intro Hin. apply Hfresh. eapply lookup_fv_context; eauto. }
  exact (proj1 (ered_free_env_irrel rho X P [] T (xi x) Hnot) Hr).
Qed.

Lemma ered_env_sat_update : forall rho Gamma xi x T s,
  ered_env_sat rho Gamma xi -> ered rho [] T s ->
  ~ In x (map fst Gamma) ->
  ered_env_sat rho (update Gamma x T) (eenv_set xi x s).
Proof.
  intros rho Gamma xi x T s Hsat Hs Hfresh y A Hlook.
  unfold eenv_set. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; subst. rewrite lookup_update_same in Hlook.
    inversion Hlook; subst; exact Hs.
  - apply Nat.eqb_neq in E. apply Hsat.
    rewrite lookup_update_neq in Hlook; [exact Hlook|congruence].
Qed.

Lemma ered_candidate : forall (rho : ecandidate_env) (bs : list ecandidate) (A : ty),
  ecandidate.
Proof.
  intros rho bs A. refine (EC (ered rho bs A) _ _ _ _).
  - intros t H; eapply ered_lc; eauto.
  - intros t H; eapply ered_sn; eauto.
  - intros t u H Hst; eapply ered_step; eauto.
  - intros t Hlc Hneu Hsteps; eapply ered_neutral; eauto.
Defined.

Lemma emulti_abs_eq : forall b t, emulti (e_abs b) t -> t = e_abs b.
Proof.
  intros b t H. remember (e_abs b) as src eqn:E. revert b E.
  induction H; intros b0 E.
  - inversion E; subst. reflexivity.
  - inversion E; subst. inversion H.
Qed.

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall rho xi,
  (forall x, eclosed (xi x)) -> ered_env_sat rho Gamma xi ->
  ered rho [] T (esubst_env xi (erase t)).
Proof.
  intros Delta Gamma t T Hty; induction Hty as
    [Delta Gamma x A Hlook Hwf
    |L Delta Gamma A b B Hwf Hprem IHprem
    |Delta Gamma f a A B Hf IHf Ha IHa
    |L Delta Gamma b T Hprem IHprem
    |Delta Gamma f T U Hf IHf HwfU].
  - intros rho xi Hxi Hsat. unfold ered_env_sat in Hsat.
    specialize (Hsat x A Hlook). exact Hsat.
  - intros rho xi Hxi Hsat.
    destruct (fresh_notin (L ++ fv_tm b ++ map fst Gamma)) as [x Hfresh].
    assert (HxL : ~ In x L) by (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (Hxrest : ~ In x (fv_tm b ++ map fst Gamma))
      by (intro H; apply Hfresh; apply in_or_app; right; exact H).
    assert (Hxb : ~ In x (fv_tm b)) by (intro H; apply Hxrest; apply in_or_app; left; exact H).
    assert (HxG : ~ In x (map fst Gamma)) by (intro H; apply Hxrest; apply in_or_app; right; exact H).
    pose proof (has_type_regular Delta (update Gamma x A) (open_tm b (tm_fvar x)) B
      (Hprem x HxL)) as [Hopenlc _].
    assert (HbLC : elc_at 1 (erase b)).
    { apply erase_lc with (K:=0). apply lc_tm_open_reflect with (x:=x).
      unfold locally_closed_tm in Hopenlc. exact Hopenlc. }
    set (body := esubst_env xi (erase b)).
    assert (HbodyLC : elc_at 1 body) by (unfold body; eapply esubst_lc; eauto).
    assert (Hbeta : forall z, ered rho [] A z -> ered rho [] B (eopen body z)).
    { intros z Hz.
      assert (Hxi' : forall y, eclosed (eenv_set xi x z y)).
      { intro y. unfold eenv_set. destruct (Nat.eqb x y); [exact (ered_lc _ _ _ _ Hz)|apply Hxi]. }
      assert (Hsat' : ered_env_sat rho (update Gamma x A) (eenv_set xi x z)).
      { eapply ered_env_sat_update; eauto. }
      pose proof (IHprem x HxL rho (eenv_set xi x z) Hxi' Hsat') as Htyped.
      unfold open_tm in Htyped. rewrite erase_open_tm in Htyped. cbn [erase] in Htyped.
      unfold body. rewrite (esubst_open 0 b xi x z Hxi (ered_lc _ _ _ _ Hz) Hxb) in Htyped.
      exact Htyped. }
    split.
    + unfold eclosed. constructor. exact HbodyLC.
    + split.
      * constructor. intros u Hu. inversion Hu.
      * intros s Hs. pose proof (ered_sn rho [] A s Hs) as HsSN.
        generalize dependent Hs. induction HsSN as [s Hargsteps IHarg]; intros Hs.
        eapply ered_neutral.
        -- unfold eclosed. econstructor; [unfold body; constructor; exact HbodyLC|eapply ered_lc; exact Hs].
        -- exact I.
        -- intros u Hu. inversion Hu; subst.
           ++ apply Hbeta. exact Hs.
           ++ inversion H1.
           ++ eapply IHarg; [exact H3|eapply ered_step; eauto].
  - intros rho xi Hxi Hsat.
    pose proof (IHf rho xi Hxi Hsat) as Hfr.
    pose proof (IHa rho xi Hxi Hsat) as Har.
    exact (ered_app rho [] A B (esubst_env xi (erase f))
      (esubst_env xi (erase a)) Hfr Har).
  - intros rho xi Hxi Hsat.
    destruct (fresh_notin (L ++ fv_context Gamma ++ fv_ty T)) as [X Hfresh].
    assert (HX_L : ~ In X L) by (intro H; apply Hfresh; apply in_or_app; left; exact H).
    assert (HXrest : ~ In X (fv_context Gamma ++ fv_ty T))
      by (intro H; apply Hfresh; apply in_or_app; right; exact H).
    assert (HXGamma : ~ In X (fv_context Gamma))
      by (intro H; apply HXrest; apply in_or_app; left; exact H).
    assert (HXT : ~ In X (fv_ty T))
      by (intro H; apply HXrest; apply in_or_app; right; exact H).
    pose proof (has_type_regular (X::Delta) Gamma (open_tm_ty b (Ty_FVar X))
      (open_ty T (Ty_FVar X)) (Hprem X HX_L)) as [Hopenlc HtypeLC].
    assert (HbLC : eclosed (erase b)).
    { pose proof (erase_lc 0 0 _ Hopenlc) as Hc.
      rewrite (erase_open_tm_ty b (Ty_FVar X)) in Hc. exact Hc. }
    set (body := esubst_env xi (erase b)).
    assert (HbodyLC : eclosed body) by (unfold body; eapply esubst_lc; eauto).
    split.
    + unfold eclosed in *. constructor. exact HbodyLC.
    + split.
      * constructor. intros u Hu. inversion Hu.
      * intros P.
        set (rho' := ecandidate_set rho X P).
        assert (Hxi' : forall y, eclosed (xi y)) by exact Hxi.
        assert (Hsat' : ered_env_sat rho' Gamma xi).
        { unfold rho'. eapply ered_env_sat_free_update; eauto. }
        pose proof (IHprem X HX_L rho' xi Hxi' Hsat') as Htyped.
        rewrite (erase_open_tm_ty b (Ty_FVar X)) in Htyped.
        unfold locally_closed_ty in HtypeLC.
        assert (HTbody : lc_ty_at 1 T) by (eapply lc_ty_open_reflect; exact HtypeLC).
        assert (HC : forall z, ered rho' [] (Ty_FVar X) z <-> ec_pred P z).
        { intro z. unfold rho', ecandidate_set. simpl. rewrite Nat.eqb_refl. tauto. }
        pose proof (ered_open_bound rho' 0 [] T (Ty_FVar X) P body HTbody
          (lc_ty_fvar 0 X) (le_n 0) HC) as Hopen_sem.
        assert (Hbound : ered rho' [P] T body) by (apply (proj1 Hopen_sem); exact Htyped).
        assert (HbodyOld : ered rho [P] T body).
        { apply (proj2 (ered_free_env_irrel rho X P [P] T body HXT)). exact Hbound. }
        eapply ered_neutral.
        -- unfold eclosed. constructor. constructor. exact HbodyLC.
        -- exact I.
        -- intros u Hu. inversion Hu; subst; try contradiction.
           ++ exact HbodyOld.
           ++ inversion H0.
  - intros rho xi Hxi Hsat.
    pose proof (IHf rho xi Hxi Hsat) as Hfr.
    destruct Hfr as [Hflc [Hfsn Hall]].
    pose proof (has_type_regular Delta Gamma f (Ty_All T) Hf) as [_ HTall].
    unfold locally_closed_ty in HTall. inversion HTall as [| | |k T0 HTbody]; subst.
    set (C := ered_candidate rho [] U).
    assert (HC : forall z, ered rho [] U z <-> ec_pred C z).
    { intro z. reflexivity. }
    pose proof (Hall C) as Hinst.
    pose proof (ered_open_bound rho 0 [] T U C (e_tapp (esubst_env xi (erase f)))
      HTbody (wf_ty_lc Delta U HwfU) (le_n 0) HC) as Hopen_sem.
    apply (proj2 Hopen_sem). exact Hinst.
Qed.

Definition base_ecandidate : ecandidate.
Proof.
  refine (EC (fun t => eclosed t /\ esn t) _ _ _ _).
  - intros t [Hlc _]; exact Hlc.
  - intros t [_ Hsn]; exact Hsn.
  - intros t u [Hlc Hsn] Hst. split; [eapply elc_step|eapply esn_step]; eauto.
  - intros t Hlc Hneu Hsteps. split; [exact Hlc|].
    constructor. intros u Hst. destruct (Hsteps u Hst) as [_ Hsn]. exact Hsn.
Defined.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  set (rho := (fun _ : atom => base_ecandidate)).
  set (xi := (fun x : atom => e_fvar x)).
  assert (Hxi : forall x, eclosed (xi x)).
  { intro x. unfold xi, eclosed. constructor. }
  assert (Hsat : ered_env_sat rho empty xi).
  { intros x A Hlook. discriminate. }
  pose proof (fundamental [] empty t T Hty rho xi Hxi Hsat) as Hred.
  unfold xi in Hred. rewrite esubst_id in Hred.
  apply esn_erases_to_sn. eapply ered_sn. exact Hred.
Qed.

End SystemFNormalizationNoneHardTask.
