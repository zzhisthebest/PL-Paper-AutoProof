(** System F CBV strong-normalization benchmark, Hard variant.
    Features: none. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
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

Definition halts (t : tm) : Prop :=
  exists v, multi t v /\ value v.

Definition reducible (P : tm -> Prop) (t : tm) : Prop :=
  locally_closed_tm t /\
  exists v, multi t v /\ value v /\ P v.

Lemma value_no_step : forall v u, value v -> v --> u -> False.
Proof. intros v u Hv Hs; inversion Hs; subst; inversion Hv. Qed.

Lemma multi_trans : forall a b c, multi a b -> multi b c -> multi a c.
Proof.
  intros a b c Hab Hbc; induction Hab; eauto using multi.
Qed.

Lemma reducible_value : forall P v,
  value v -> locally_closed_tm v -> P v -> reducible P v.
Proof.
  intros P v Hv Hlc HP; split; [assumption|].
  exists v; repeat split; auto using multi_refl.
Qed.

Lemma reducible_elim : forall P t, reducible P t ->
  exists v, multi t v /\ value v /\ P v.
Proof. intros P t [_ H]; exact H. Qed.

Lemma reducible_expand : forall P t u,
  locally_closed_tm t -> t --> u -> reducible P u -> reducible P t.
Proof.
  intros P t u Hlc Hstep [_ [v [Hm [Hv HP]]]].
  split; [exact Hlc|]. exists v; repeat split; auto.
  eapply multi_step; eauto.
Qed.

Lemma reducible_multi_expand : forall P t u,
  locally_closed_tm t -> multi t u -> reducible P u -> reducible P t.
Proof.
  intros P t u Hlc Hm [_ [v [Huv [Hv HP]]]].
  split; [exact Hlc|]. exists v; repeat split; auto.
  eapply multi_trans; eauto.
Qed.

Lemma fresh_list : forall L : list nat, ~ In (S (fold_right Nat.max 0 L)) L.
Proof.
  intros L.
  assert (Hbound : forall a, In a L -> a <= fold_right Nat.max 0 L).
  { induction L as [|b L IH]; intros a Ha; simpl in *; [contradiction|].
    destruct Ha as [<-|Ha]; [lia|]. specialize (IH a Ha); lia. }
  intro H; eapply Hbound in H; lia.
Qed.

Lemma lc_ty_mono : forall k T, lc_ty_at k T ->
  forall j, k <= j -> lc_ty_at j T.
Proof.
  intros k T H; induction H; intros j Hj; constructor; eauto; try lia.
  apply IHlc_ty_at; lia.
Qed.

Lemma lc_tm_mono : forall K k t, lc_tm_at K k t ->
  forall J j, K <= J -> k <= j -> lc_tm_at J j t.
Proof.
  intros K k t H; induction H; intros J j HJ Hj; constructor; eauto; try lia.
  - eapply lc_ty_mono; eauto.
  - apply IHlc_tm_at; lia.
  - apply IHlc_tm_at; lia.
  - eapply lc_ty_mono; eauto.
Qed.

Lemma lc_ty_open_inverse : forall T k U j,
  k <= j -> lc_ty_at j (open_ty_rec k U T) -> lc_ty_at (S j) T.
Proof.
  induction T; intros k U j Hkj Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion Hlc; subst; constructor; lia.
  - constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor.
    apply IHT with (k := S k) (U := U); auto; lia.
Qed.

Lemma lc_tm_open_inverse : forall t k u K j,
  k <= j -> lc_tm_at K j (open_tm_rec k u t) -> lc_tm_at K (S j) t.
Proof.
  induction t; intros k u K j Hkj Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion Hlc; subst; constructor; lia.
  - constructor.
  - inversion Hlc; subst; constructor; auto.
    apply IHt with (k := S k) (u := u); auto; lia.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inverse : forall t k U K j,
  k <= K -> lc_tm_at K j (open_tm_ty_rec k U t) -> lc_tm_at (S K) j t.
Proof.
  induction t; intros k U K j Hk Hlc; simpl in Hlc.
  - inversion Hlc; constructor; auto.
  - constructor.
  - inversion Hlc; subst; constructor.
    + eapply lc_ty_open_inverse; eauto.
    + eapply IHt; eauto.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst; constructor.
    eapply (IHt (S k) U (S K) j); eauto; lia.
  - inversion Hlc; subst; constructor; eauto using lc_ty_open_inverse.
Qed.

Lemma wf_ty_closed : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H as
    [Delta X Hin | Delta T1 T2 HT1 IH1 HT2 IH2 |
     L Delta T Hbody IHbody]; simpl; constructor; auto.
  specialize (IHbody (S (fold_right Nat.max 0 L)) (fresh_list L)).
  eapply lc_ty_open_inverse in IHbody; [exact IHbody|lia].
Qed.

Lemma typing_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H as
    [Delta Gamma x T Hlookup HT |
     L Delta Gamma T1 t2 T2 HT1 Hbody IHbody |
     Delta Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2 |
     L Delta Gamma t T Hbody IHbody |
     Delta Gamma t T U Ht IH HU]; simpl.
  - constructor.
  - constructor; [eapply wf_ty_closed; eauto|].
    specialize (IHbody (S (fold_right Nat.max 0 L)) (fresh_list L)).
    eapply lc_tm_open_inverse in IHbody; [exact IHbody|lia].
  - constructor; auto.
  - constructor.
    specialize (IHbody (S (fold_right Nat.max 0 L)) (fresh_list L)).
    eapply lc_tm_ty_open_inverse in IHbody; [exact IHbody|lia].
  - constructor; auto. eapply wf_ty_closed; eauto.
Qed.

Fixpoint close_ty (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar n => Ty_BVar n
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (close_ty theta A) (close_ty theta B)
  | Ty_All A => Ty_All (close_ty theta A)
  end.

Fixpoint close_tm (theta : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar n => tm_bvar n
  | tm_fvar x => sigma x
  | tm_abs T b => tm_abs (close_ty theta T) (close_tm theta sigma b)
  | tm_app a b => tm_app (close_tm theta sigma a) (close_tm theta sigma b)
  | tm_tabs b => tm_tabs (close_tm theta sigma b)
  | tm_tapp a T => tm_tapp (close_tm theta sigma a) (close_ty theta T)
  end.

Definition set_ty (theta : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else theta Y.
Definition set_tm (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.
Definition set_pred (rho : atom -> tm -> Prop) (X : atom) (P : tm -> Prop)
  : atom -> tm -> Prop := fun Y => if Nat.eqb X Y then P else rho Y.

Fixpoint fresh_ty (X : atom) (T : ty) : Prop :=
  match T with
  | Ty_BVar _ => True
  | Ty_FVar Y => X <> Y
  | Ty_Arrow A B => fresh_ty X A /\ fresh_ty X B
  | Ty_All A => fresh_ty X A
  end.
Fixpoint fresh_tm (x : atom) (t : tm) : Prop :=
  match t with
  | tm_bvar _ => True
  | tm_fvar y => x <> y
  | tm_abs _ b => fresh_tm x b
  | tm_app a b => fresh_tm x a /\ fresh_tm x b
  | tm_tabs b => fresh_tm x b
  | tm_tapp a _ => fresh_tm x a
  end.
Fixpoint fresh_tm_ty (X : atom) (t : tm) : Prop :=
  match t with
  | tm_bvar _ | tm_fvar _ => True
  | tm_abs T b => fresh_ty X T /\ fresh_tm_ty X b
  | tm_app a b => fresh_tm_ty X a /\ fresh_tm_ty X b
  | tm_tabs b => fresh_tm_ty X b
  | tm_tapp a T => fresh_tm_ty X a /\ fresh_ty X T
  end.

Fixpoint free_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => [] | Ty_FVar X => [X]
  | Ty_Arrow A B => free_ty A ++ free_ty B
  | Ty_All A => free_ty A
  end.
Fixpoint free_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => [] | tm_fvar x => [x]
  | tm_abs _ b | tm_tabs b => free_tm b
  | tm_app a b => free_tm a ++ free_tm b
  | tm_tapp a _ => free_tm a
  end.
Fixpoint free_tm_ty (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T b => free_ty T ++ free_tm_ty b
  | tm_app a b => free_tm_ty a ++ free_tm_ty b
  | tm_tabs b => free_tm_ty b
  | tm_tapp a T => free_tm_ty a ++ free_ty T
  end.

Lemma free_ty_fresh : forall X T, ~ In X (free_ty T) -> fresh_ty X T.
Proof.
  intros X T; induction T; simpl; intros H.
  - exact I.
  - intros ->; apply H; auto.
  - split; [apply IHT1|apply IHT2]; intro Hin; apply H; apply in_or_app; auto.
  - apply IHT; assumption.
Qed.
Lemma free_tm_fresh : forall x t, ~ In x (free_tm t) -> fresh_tm x t.
Proof.
  intros x t; induction t; simpl; intros H.
  - exact I.
  - intros ->; apply H; auto.
  - apply IHt; assumption.
  - split; [apply IHt1|apply IHt2]; intro Hin; apply H; apply in_or_app; auto.
  - apply IHt; assumption.
  - apply IHt; assumption.
Qed.
Lemma free_tm_ty_fresh : forall X t, ~ In X (free_tm_ty t) -> fresh_tm_ty X t.
Proof.
  intros X t; induction t; simpl; intros H; auto.
  - split; [apply free_ty_fresh|apply IHt];
      intro Hin; apply H; apply in_or_app; auto.
  - split; [apply IHt1|apply IHt2];
      intro Hin; apply H; apply in_or_app; auto.
  - split; [apply IHt|apply free_ty_fresh];
      intro Hin; apply H; apply in_or_app; auto.
Qed.

Lemma close_ty_lc : forall T K theta,
  lc_ty_at K T -> (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at K (close_ty theta T).
Proof.
  intros T K theta H; induction H; intros Htheta; simpl; try constructor; eauto.
  eapply lc_ty_mono; [apply Htheta|lia].
Qed.
Lemma close_tm_lc : forall t K k theta sigma,
  lc_tm_at K k t -> (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k (close_tm theta sigma t).
Proof.
  intros t K k theta sigma H; induction H; intros Htheta Hsigma; simpl;
    try constructor; eauto using close_ty_lc.
  - eapply lc_tm_mono; [apply Hsigma|lia|lia].
Qed.

Lemma open_tm_closed_at : forall t K j k u,
  lc_tm_at K j t -> j <= k -> open_tm_rec k u t = t.
Proof.
  intros t K j limit u H; revert limit u; induction H;
    intros limit u Hle; simpl; auto.
  - assert (limit <> i) by lia. apply Nat.eqb_neq in H0. now rewrite H0.
  - f_equal; apply IHlc_tm_at; lia.
  - now rewrite IHlc_tm_at1, IHlc_tm_at2 by lia.
  - now rewrite IHlc_tm_at by lia.
  - now rewrite IHlc_tm_at by lia.
Qed.
Lemma open_tm_closed : forall t K k u,
  lc_tm_at K 0 t -> open_tm_rec k u t = t.
Proof. intros; eapply open_tm_closed_at; eauto; lia. Qed.
Lemma open_ty_closed_at : forall T j k U,
  lc_ty_at j T -> j <= k -> open_ty_rec k U T = T.
Proof.
  intros T j limit U H; revert limit U; induction H;
    intros limit U Hle; simpl; auto.
  - assert (limit <> i) by lia. apply Nat.eqb_neq in H0. now rewrite H0.
  - now rewrite IHlc_ty_at1, IHlc_ty_at2 by lia.
  - f_equal; apply IHlc_ty_at; lia.
Qed.
Lemma open_ty_closed : forall T k U,
  locally_closed_ty T -> open_ty_rec k U T = T.
Proof. intros; eapply open_ty_closed_at; eauto; lia. Qed.
Lemma open_tm_ty_closed_at : forall t K j k U,
  lc_tm_at K j t -> K <= k -> open_tm_ty_rec k U t = t.
Proof.
  intros t K j limit U H; revert limit U; induction H;
    intros limit U Hle; simpl; auto.
  - rewrite (open_ty_closed_at _ _ _ _ H Hle), IHlc_tm_at by lia; reflexivity.
  - now rewrite IHlc_tm_at1, IHlc_tm_at2 by lia.
  - f_equal; apply IHlc_tm_at; lia.
  - now rewrite IHlc_tm_at, (open_ty_closed_at _ _ _ _ H0 Hle) by lia.
Qed.
Lemma open_tm_ty_closed : forall t k U,
  locally_closed_tm t -> open_tm_ty_rec k U t = t.
Proof. intros; eapply open_tm_ty_closed_at; eauto; lia. Qed.

Lemma close_open_tm : forall t k x theta sigma v,
  fresh_tm x t -> (forall y, locally_closed_tm (sigma y)) ->
  close_tm theta (set_tm sigma x v) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (close_tm theta sigma t).
Proof.
  induction t; intros k x theta sigma v Hfresh Hsigma; simpl in *; auto.
  - destruct (Nat.eqb k n); simpl; [unfold set_tm; now rewrite Nat.eqb_refl|reflexivity].
  - unfold set_tm. destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; contradiction.
    + symmetry; eapply open_tm_closed; apply Hsigma.
  - f_equal; apply IHt; auto.
  - destruct Hfresh as [Ha Hb]. f_equal; [apply IHt1|apply IHt2]; auto.
  - f_equal; apply IHt; auto.
  - f_equal; apply IHt; auto.
Qed.

Lemma close_open_ty : forall T k X theta U,
  fresh_ty X T -> (forall Y, locally_closed_ty (theta Y)) ->
  close_ty (set_ty theta X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (close_ty theta T).
Proof.
  induction T; intros k X theta U Hfresh Htheta; simpl in *; auto.
  - destruct (Nat.eqb k n); simpl; [unfold set_ty; now rewrite Nat.eqb_refl|reflexivity].
  - unfold set_ty. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; contradiction.
    + symmetry; eapply open_ty_closed; apply Htheta.
  - destruct Hfresh as [Ha Hb]. now rewrite IHT1, IHT2.
  - now rewrite IHT.
Qed.

Lemma close_open_tm_ty : forall t k X theta sigma U,
  fresh_tm_ty X t -> (forall Y, locally_closed_ty (theta Y)) ->
  (forall y, locally_closed_tm (sigma y)) ->
  close_tm (set_ty theta X U) sigma (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (close_tm theta sigma t).
Proof.
  induction t; intros k X theta sigma U Hfresh Htheta Hsigma;
    simpl in *; auto.
  - symmetry; apply open_tm_ty_closed; apply Hsigma.
  - destruct Hfresh as [Ha Hb]. f_equal;
      [apply close_open_ty|apply IHt]; auto.
  - destruct Hfresh as [Ha Hb]. f_equal; [apply IHt1|apply IHt2]; auto.
  - f_equal; apply IHt; auto.
  - destruct Hfresh as [Ha Hb]. f_equal;
      [apply IHt|apply close_open_ty]; auto.
Qed.

Fixpoint val_sem (T : ty) (rho : atom -> tm -> Prop)
  (bound : list (tm -> Prop)) (v : tm) : Prop :=
  match T with
  | Ty_BVar n => nth n bound (fun _ => False) v
  | Ty_FVar X => rho X v
  | Ty_Arrow A B =>
      forall a, reducible (val_sem A rho bound) a ->
        reducible (val_sem B rho bound) (tm_app v a)
  | Ty_All A =>
      forall U P, locally_closed_ty U ->
        reducible (val_sem A rho (P :: bound)) (tm_tapp v U)
  end.

Lemma red_iff : forall P Q t,
  (forall v, P v <-> Q v) -> reducible P t <-> reducible Q t.
Proof.
  intros P Q t Heq; split.
  - intros [Hlc [v [Hm [Hv HP]]]].
    split; [exact Hlc|]. exists v. repeat split; auto.
    apply (proj1 (Heq v)); assumption.
  - intros [Hlc [v [Hm [Hv HP]]]].
    split; [exact Hlc|]. exists v. repeat split; auto.
    apply (proj2 (Heq v)); assumption.
Qed.

Lemma val_sem_agree : forall T k rho bound1 bound2 v,
  lc_ty_at k T ->
  (forall i, i < k -> nth i bound1 (fun _ => False) =
                       nth i bound2 (fun _ => False)) ->
  val_sem T rho bound1 v <-> val_sem T rho bound2 v.
Proof.
  intros T k rho bound1 bound2 v Hlc; revert bound1 bound2 v.
  induction Hlc; intros bound1 bound2 v Hagree; simpl.
  - rewrite Hagree by assumption; reflexivity.
  - reflexivity.
  - split; intros H a Ha.
    + apply (proj1 (red_iff _ _ _ (fun w => IHHlc2 _ _ w Hagree))).
      apply H. apply (proj2 (red_iff _ _ _ (fun w => IHHlc1 _ _ w Hagree)));
        assumption.
    + apply (proj2 (red_iff _ _ _ (fun w => IHHlc2 _ _ w Hagree))).
      apply H. apply (proj1 (red_iff _ _ _ (fun w => IHHlc1 _ _ w Hagree)));
        assumption.
  - assert (Hcons : forall P i, i < S k ->
        nth i (P :: bound1) (fun _ => False) =
        nth i (P :: bound2) (fun _ => False)).
    { intros P [|i] Hi; simpl; auto. apply Hagree; lia. }
    split; intros H U P HU.
    + apply (proj1 (red_iff _ _ _ (fun w => IHHlc _ _ w (Hcons P)))).
      apply H; assumption.
    + apply (proj2 (red_iff _ _ _ (fun w => IHHlc _ _ w (Hcons P)))).
      apply H; assumption.
Qed.

Lemma val_sem_fresh : forall T X rho P bound v,
  fresh_ty X T ->
  val_sem T (set_pred rho X P) bound v <-> val_sem T rho bound v.
Proof.
  induction T; intros X rho P bound v Hfresh; simpl in *.
  - reflexivity.
  - unfold set_pred. destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; contradiction.
    + reflexivity.
  - destruct Hfresh as [Ha Hb].
    assert (HA : forall t, reducible (val_sem T1 (set_pred rho X P) bound) t <->
                reducible (val_sem T1 rho bound) t).
    { intro t; apply red_iff; intros w; apply IHT1; exact Ha. }
    assert (HB : forall t, reducible (val_sem T2 (set_pred rho X P) bound) t <->
                reducible (val_sem T2 rho bound) t).
    { intro t; apply red_iff; intros w; apply IHT2; exact Hb. }
    split; intros H arg Harg.
    + apply (proj1 (HB _)). apply H. apply (proj2 (HA _)); assumption.
    + apply (proj2 (HB _)). apply H. apply (proj1 (HA _)); assumption.
  - assert (HA : forall Q t,
       reducible (val_sem T (set_pred rho X P) (Q :: bound)) t <->
       reducible (val_sem T rho (Q :: bound)) t).
    { intros Q t; apply red_iff; intros w; apply IHT; assumption. }
    split; intros H U Q HU.
    + apply (proj1 (HA Q _)). apply H; assumption.
    + apply (proj2 (HA Q _)). apply H; assumption.
Qed.

Lemma nth_prefix : forall (A : Type) (pre tail1 tail2 : list A) n d,
  n < length pre -> nth n (pre ++ tail1) d = nth n (pre ++ tail2) d.
Proof.
  intros A pre; induction pre as [|a pre IH]; intros tail1 tail2 n d Hn;
    simpl in *; [lia|]. destruct n; auto. apply IH; lia.
Qed.

Lemma val_sem_open : forall T k pre tail U rho v,
  length pre = k -> lc_ty_at (S k) T -> locally_closed_ty U ->
  val_sem (open_ty_rec k U T) rho (pre ++ tail) v <->
  val_sem T rho (pre ++ val_sem U rho [] :: tail) v.
Proof.
  induction T; intros k pre tail U rho v Hlen Hlc HU; simpl in *.
  - inversion Hlc; subst. destruct (Nat.eqb (length pre) n) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      rewrite nth_middle.
      eapply val_sem_agree; [exact HU|]. intros i Hi; lia.
    + apply Nat.eqb_neq in E.
      assert (n < length pre) by lia.
      simpl.
      rewrite (nth_prefix _ pre tail (val_sem U rho [] :: tail) n (fun _ => False) H).
      reflexivity.
  - reflexivity.
  - inversion Hlc; subst.
    assert (HA : forall t,
      reducible (val_sem (open_ty_rec (length pre) U T1) rho (pre ++ tail)) t <->
      reducible (val_sem T1 rho (pre ++ val_sem U rho [] :: tail)) t).
    { intro t; apply red_iff; intros w;
      apply (IHT1 (length pre) pre tail U rho w eq_refl H2 HU). }
    assert (HB : forall t,
      reducible (val_sem (open_ty_rec (length pre) U T2) rho (pre ++ tail)) t <->
      reducible (val_sem T2 rho (pre ++ val_sem U rho [] :: tail)) t).
    { intro t; apply red_iff; intros w;
      apply (IHT2 (length pre) pre tail U rho w eq_refl H3 HU). }
    split; intros H arg Harg.
    + apply (proj1 (HB _)). apply H. apply (proj2 (HA _)); assumption.
    + apply (proj2 (HB _)). apply H. apply (proj1 (HA _)); assumption.
  - inversion Hlc; subst.
    assert (HA : forall P t,
      reducible (val_sem (open_ty_rec (S (length pre)) U T) rho
        (P :: pre ++ tail)) t <->
      reducible (val_sem T rho
        (P :: pre ++ val_sem U rho [] :: tail)) t).
    { intros P t; apply red_iff; intros w.
      apply (IHT (S (length pre)) (P :: pre) tail U rho w eq_refl H1 HU). }
    split; intros H V P HV.
    + apply (proj1 (HA P _)). apply H; assumption.
    + apply (proj2 (HA P _)). apply H; assumption.
Qed.

Lemma multi_app1 : forall t v u,
  multi t v -> locally_closed_tm u ->
  multi (tm_app t u) (tm_app v u).
Proof.
  intros t v u Hm Hu; induction Hm; eauto using multi_refl, multi_step, ST_App1.
Qed.
Lemma multi_app2 : forall v t u,
  value v -> multi t u -> multi (tm_app v t) (tm_app v u).
Proof.
  intros v t u Hv Hm; induction Hm; eauto using multi_refl, multi_step, ST_App2.
Qed.
Lemma multi_tapp : forall t v U,
  multi t v -> locally_closed_ty U ->
  multi (tm_tapp t U) (tm_tapp v U).
Proof.
  intros t v U Hm HU; induction Hm; eauto using multi_refl, multi_step, ST_TApp.
Qed.

Lemma reducible_app : forall A B f arg,
  reducible (fun v => forall a, reducible A a ->
                         reducible B (tm_app v a)) f ->
  reducible A arg -> reducible B (tm_app f arg).
Proof.
  intros A B f arg [Hf [v [Hm [Hv Hfun]]]] Harg.
  eapply reducible_multi_expand.
  - constructor; [exact Hf|exact (proj1 Harg)].
  - apply multi_app1; [exact Hm|exact (proj1 Harg)].
  - apply Hfun; exact Harg.
Qed.
Lemma reducible_tapp : forall T rho U f,
  locally_closed_ty U ->
  reducible (fun v => forall V P, locally_closed_ty V ->
      reducible (val_sem T rho [P]) (tm_tapp v V)) f ->
  forall P, reducible (val_sem T rho [P]) (tm_tapp f U).
Proof.
  intros T rho U f HU [Hf [v [Hm [Hv Hfun]]]] P.
  eapply reducible_multi_expand.
  - constructor; assumption.
  - eapply multi_tapp; eauto.
  - apply (Hfun U P HU).
Qed.

Lemma lc_ty_open_forward : forall T k U,
  lc_ty_at (S k) T -> lc_ty_at k U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; simpl; inversion HT; subst.
  - destruct (Nat.eqb k n) eqn:E; auto.
    apply Nat.eqb_neq in E; constructor; lia.
  - constructor.
  - constructor; [apply IHT1|apply IHT2]; assumption.
  - constructor. apply IHT; [assumption|].
    eapply lc_ty_mono; [exact HU|lia].
Qed.

Lemma typing_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H as
    [Delta Gamma x T Hlookup HT |
     L Delta Gamma T1 t2 T2 HT1 Hbody IHbody |
     Delta Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2 |
     L Delta Gamma t T Hbody IHbody |
     Delta Gamma t T U Ht IH HU].
  - eapply wf_ty_closed; eauto.
  - constructor; [eapply wf_ty_closed; eauto|].
    apply (IHbody (S (fold_right Nat.max 0 L)) (fresh_list L)).
  - inversion IH1; assumption.
  - constructor.
    pose (X := S (fold_right Nat.max 0 L)).
    specialize (IHbody X (fresh_list L)).
    eapply lc_ty_open_inverse in IHbody; [exact IHbody|lia].
  - eapply lc_ty_open_forward; [|eapply wf_ty_closed; eauto].
    inversion IH; assumption.
Qed.

Fixpoint context_ty_vars (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => free_ty T ++ context_ty_vars Gamma'
  end.

Lemma lookup_fresh_ty : forall Gamma x T X,
  ~ In X (context_ty_vars Gamma) ->
  lookup_context x Gamma = Some T -> fresh_ty X T.
Proof.
  induction Gamma as [|[y A] Gamma IH]; intros x T X Hfresh Hlookup;
    simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlookup; subst; apply free_ty_fresh.
    intro Hin; apply Hfresh; apply in_or_app; auto.
  - apply IH with (x := x); auto.
    intro Hin; apply Hfresh; apply in_or_app; auto.
Qed.

Lemma lookup_fresh_key : forall Gamma x,
  ~ In x (map fst Gamma) -> lookup_context x Gamma = None.
Proof.
  induction Gamma as [|[y T] Gamma IH]; intros x Hfresh; simpl in *; auto.
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; auto.
  - apply IH; intro Hin; apply Hfresh; auto.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta rho sigma,
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  (forall x A, lookup_context x Gamma = Some A ->
    reducible (val_sem A rho []) (sigma x)) ->
  reducible (val_sem T rho []) (close_tm theta sigma t).
Proof.
  intros Delta Gamma t T Htyping; induction Htyping as
    [Delta Gamma x T Hlookup HT |
     L Delta Gamma T1 body T2 HT1 Hbody IHbody |
     Delta Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2 |
     L Delta Gamma body T Hbody IHbody |
     Delta Gamma t T U Ht IH HU];
    intros theta rho sigma Htheta Hsigma Henv; simpl.
  - apply Henv; assumption.
  - assert (Habs : locally_closed_tm
        (tm_abs (close_ty theta T1) (close_tm theta sigma body))).
    { change (locally_closed_tm
        (close_tm theta sigma (tm_abs T1 body))).
      apply close_tm_lc; auto.
      eapply typing_closed. eapply T_Abs; eauto. }
    apply reducible_value; [constructor; exact Habs|exact Habs|].
    intros arg Harg.
    destruct Harg as [Harglc [v [Hargmulti [Hv HP]]]].
    assert (Hvlc : locally_closed_tm v).
    { inversion Hv; assumption. }
    assert (Hvr : reducible (val_sem T1 rho []) v).
    { apply reducible_value; assumption. }
    pose (x := S (fold_right Nat.max 0
      (L ++ free_tm body ++ map fst Gamma))).
    assert (HxL : ~ In x L).
    { unfold x; intro Hin; apply (fresh_list
        (L ++ free_tm body ++ map fst Gamma)); apply in_or_app; left; exact Hin. }
    assert (Hxfresh : fresh_tm x body).
    { apply free_tm_fresh; unfold x; intro Hin;
      apply (fresh_list (L ++ free_tm body ++ map fst Gamma));
      apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (HxGamma : ~ In x (map fst Gamma)).
    { unfold x; intro Hin;
      apply (fresh_list (L ++ free_tm body ++ map fst Gamma));
      apply in_or_app; right; apply in_or_app; right; exact Hin. }
    assert (Hsigma' : forall y, locally_closed_tm (set_tm sigma x v y)).
    { intros y; unfold set_tm; destruct (Nat.eqb x y); auto. }
    assert (Henv' : forall y A,
      lookup_context y ((x, T1) :: Gamma) = Some A ->
      reducible (val_sem A rho []) (set_tm sigma x v y)).
    { intros y A Hy. simpl in Hy. unfold set_tm.
      destruct (Nat.eqb y x) eqn:E.
      - apply Nat.eqb_eq in E; subst y.
        inversion Hy; subst A.
        rewrite Nat.eqb_refl. exact Hvr.
      - apply Nat.eqb_neq in E.
        assert (E' : Nat.eqb x y = false) by (apply Nat.eqb_neq; lia).
        rewrite E'. apply Henv.
        exact Hy. }
    pose proof (IHbody x HxL theta rho (set_tm sigma x v)
      Htheta Hsigma' Henv') as Hresult.
    unfold open_tm in Hresult.
    rewrite (close_open_tm body 0 x theta sigma v Hxfresh Hsigma)
      in Hresult.
    eapply reducible_multi_expand.
    + constructor; [exact Habs|exact Harglc].
    + apply multi_app2; [constructor; exact Habs|exact Hargmulti].
    + eapply reducible_expand; [|eapply ST_AppAbs|exact Hresult].
      * constructor; [exact Habs|exact Hvlc].
      * exact Habs.
      * exact Hv.
  - apply reducible_app with (A := val_sem T1 rho []);
      [apply IH1|apply IH2]; assumption.
  - assert (Htabs : locally_closed_tm (tm_tabs (close_tm theta sigma body))).
    { change (locally_closed_tm (close_tm theta sigma (tm_tabs body))).
      apply close_tm_lc; auto.
      eapply typing_closed. eapply T_TAbs; eauto. }
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _
        (T_TAbs L Delta Gamma body T Hbody)) as HH.
      inversion HH; assumption. }
    apply reducible_value; [constructor; exact Htabs|exact Htabs|].
    intros U P HU.
    pose (X := S (fold_right Nat.max 0
      (L ++ free_tm_ty body ++ free_ty T ++ context_ty_vars Gamma))).
    assert (HXL : ~ In X L).
    { unfold X; intro Hin; apply (fresh_list
        (L ++ free_tm_ty body ++ free_ty T ++ context_ty_vars Gamma));
      apply in_or_app; left; exact Hin. }
    assert (HXbody : fresh_tm_ty X body).
    { apply free_tm_ty_fresh; unfold X; intro Hin;
      apply (fresh_list
        (L ++ free_tm_ty body ++ free_ty T ++ context_ty_vars Gamma));
      apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (HXT : fresh_ty X T).
    { apply free_ty_fresh; unfold X; intro Hin;
      apply (fresh_list
        (L ++ free_tm_ty body ++ free_ty T ++ context_ty_vars Gamma));
      apply in_or_app; right; apply in_or_app; right;
      apply in_or_app; left; exact Hin. }
    assert (HXGamma : ~ In X (context_ty_vars Gamma)).
    { unfold X; intro Hin;
      apply (fresh_list
        (L ++ free_tm_ty body ++ free_ty T ++ context_ty_vars Gamma));
      apply in_or_app; right; apply in_or_app; right;
      apply in_or_app; right; exact Hin. }
    assert (Htheta' : forall Y,
      locally_closed_ty (set_ty theta X U Y)).
    { intros Y; unfold set_ty; destruct (Nat.eqb X Y); auto. }
    assert (Henv' : forall y A, lookup_context y Gamma = Some A ->
      reducible (val_sem A (set_pred rho X P) []) (sigma y)).
    { intros y A Hy.
      pose proof (lookup_fresh_ty Gamma y A X HXGamma Hy) as Hfresh.
      apply (proj2 (red_iff
        (val_sem A (set_pred rho X P) []) (val_sem A rho [])
        (sigma y) (fun w => val_sem_fresh A X rho P [] w Hfresh))).
      apply Henv; assumption. }
    pose proof (IHbody X HXL (set_ty theta X U)
      (set_pred rho X P) sigma Htheta' Hsigma Henv') as Hresult.
    unfold open_tm_ty in Hresult.
    rewrite (close_open_tm_ty body 0 X theta sigma U
      HXbody Htheta Hsigma) in Hresult.
    assert (Hsem : forall w,
      val_sem (open_ty T (Ty_FVar X)) (set_pred rho X P) [] w <->
      val_sem T rho [P] w).
    { intro w. unfold open_ty.
      eapply iff_trans.
      - apply (val_sem_open T 0 [] [] (Ty_FVar X)
          (set_pred rho X P) w); [reflexivity|exact HTlc|constructor].
      - simpl. unfold set_pred. rewrite Nat.eqb_refl.
        apply val_sem_fresh; exact HXT. }
    apply (proj1 (red_iff _ _ _ Hsem)) in Hresult.
    eapply reducible_expand; [|eapply ST_TAppTabs|exact Hresult].
    + constructor; [exact Htabs|exact HU].
    + exact Htabs.
    + exact HU.
  - pose proof (wf_ty_closed _ _ HU) as HUlc.
    assert (HUclosed : locally_closed_ty (close_ty theta U)).
    { apply close_ty_lc; assumption. }
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Ht) as HH.
      inversion HH; assumption. }
    pose proof (IH theta rho sigma Htheta Hsigma Henv) as Hpoly.
    pose proof (reducible_tapp T rho (close_ty theta U)
      (close_tm theta sigma t) HUclosed Hpoly
      (val_sem U rho [])) as Hresult.
    apply (proj2 (red_iff _ _ _ (fun w =>
      val_sem_open T 0 [] [] U rho w eq_refl HTlc HUlc))).
    exact Hresult.
Qed.

Lemma step_deterministic : forall t u w,
  t --> u -> t --> w -> u = w.
Proof.
  intros t u w Hstep; revert w.
  induction Hstep; intros w Hother; inversion Hother; subst;
    try reflexivity;
    try solve [exfalso; eapply value_no_step; eauto];
    try solve [f_equal; eauto].
  - inversion H3.
  - exfalso; exact (value_no_step v t2' H0 H5).
  - inversion Hstep.
Qed.

Lemma halts_sn : forall t, halts t -> strongly_normalizing t.
Proof.
  intros t [v [Hm Hv]]. induction Hm.
  - constructor; intros u Hu.
    exfalso; eapply value_no_step; eauto.
  - constructor; intros u Hu.
    assert (u = y) by (eapply step_deterministic; eauto).
    subst; apply IHHm; exact Hv.
Qed.

Lemma close_ty_id : forall T, close_ty Ty_FVar T = T.
Proof. induction T; simpl; f_equal; auto. Qed.
Lemma close_tm_id : forall t, close_tm Ty_FVar tm_fvar t = t.
Proof. induction t; simpl; f_equal; auto using close_ty_id. Qed.


Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Htyping.
  pose proof (fundamental [] empty t T Htyping
    Ty_FVar (fun _ _ => False) tm_fvar) as Hfund.
  assert (Hred : reducible (val_sem T (fun _ _ => False) [])
    (close_tm Ty_FVar tm_fvar t)).
  { apply Hfund.
    - intros; constructor.
    - intros; constructor.
    - intros x A Hlookup; discriminate Hlookup. }
  rewrite close_tm_id in Hred.
  apply halts_sn. destruct Hred as [_ [v [Hm [Hv _]]]].
  exists v; auto.
Qed.

End SystemFNormalizationNoneHardTask.
