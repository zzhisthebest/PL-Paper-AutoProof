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

Fixpoint shape (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs _ t1 => tm_abs (Ty_BVar 0) (shape t1)
  | tm_app t1 t2 => tm_app (shape t1) (shape t2)
  | tm_tabs t1 => tm_tabs (shape t1)
  | tm_tapp t1 _ => tm_tapp (shape t1) (Ty_BVar 0)
  end.

Fixpoint shape_open_rec (k : nat) (u t : tm) : tm :=
  match t with
  | tm_bvar i => if Nat.eqb k i then u else tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs _ t1 => tm_abs (Ty_BVar 0) (shape_open_rec (S k) u t1)
  | tm_app t1 t2 => tm_app (shape_open_rec k u t1) (shape_open_rec k u t2)
  | tm_tabs t1 => tm_tabs (shape_open_rec k u t1)
  | tm_tapp t1 _ => tm_tapp (shape_open_rec k u t1) (Ty_BVar 0)
  end.

Inductive shape_value : tm -> Prop :=
  | shape_v_abs : forall t, shape_value (tm_abs (Ty_BVar 0) t)
  | shape_v_tabs : forall t, shape_value (tm_tabs t).

Reserved Notation "t1 '==>' t2" (at level 40).
Inductive shape_step : tm -> tm -> Prop :=
  | SS_AppAbs : forall t v,
      shape_value v ->
      tm_app (tm_abs (Ty_BVar 0) t) v ==> shape_open_rec 0 v t
  | SS_App1 : forall t1 t1' t2,
      t1 ==> t1' -> tm_app t1 t2 ==> tm_app t1' t2
  | SS_App2 : forall v1 t2 t2',
      shape_value v1 -> t2 ==> t2' -> tm_app v1 t2 ==> tm_app v1 t2'
  | SS_TAppTabs : forall t,
      tm_tapp (tm_tabs t) (Ty_BVar 0) ==> t
  | SS_TApp : forall t t',
      t ==> t' -> tm_tapp t (Ty_BVar 0) ==> tm_tapp t' (Ty_BVar 0)
where "t1 '==>' t2" := (shape_step t1 t2).

Inductive shape_sn : tm -> Prop :=
  | shape_SN_intro : forall t,
      (forall u, t ==> u -> shape_sn u) -> shape_sn t.

Lemma shape_open_shape : forall k u t,
  shape_open_rec k (shape u) (shape t) = shape (open_tm_rec k u t).
Proof.
  intros k u t. revert k u.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH]; intros k u; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - f_equal. apply IH.
  - f_equal; [apply IH1|apply IH2].
  - f_equal. apply IH.
  - f_equal. apply IH.
  all: try (f_equal; auto).
Qed.

Lemma shape_open_ty_rec : forall k T t, shape (open_tm_ty_rec k T t) = shape t.
Proof.
  intros k T t. revert k T.
  induction t as [i|x|A t IH|t1 IH1 t2 IH2|t IH|t IH]; intros k T; simpl; auto.
  - f_equal. apply IH.
  - f_equal; [apply IH1|apply IH2].
  - f_equal. apply IH.
  - f_equal. apply IH.
Qed.

Lemma shape_open_ty : forall t T, shape (open_tm_ty t T) = shape t.
Proof. intros; apply shape_open_ty_rec. Qed.

Lemma value_shape : forall t, value t -> shape_value (shape t).
Proof. intros t H; inversion H; subst; constructor. Qed.

Lemma step_shape : forall t u, t --> u -> shape t ==> shape u.
Proof.
  intros t u H; induction H; subst; unfold open_tm; simpl.
  - rewrite <- shape_open_shape. constructor. apply value_shape; assumption.
  - constructor; assumption.
  - constructor.
    + apply value_shape; assumption.
    + assumption.
  - rewrite shape_open_ty. constructor.
  - constructor; auto.
Qed.

Lemma shape_sn_to_sn : forall t, shape_sn (shape t) -> strongly_normalizing t.
Proof.
  intros t0 H0.
  assert (G : forall s, shape_sn s -> forall q, shape q = s ->
      strongly_normalizing q).
  { intros s H. induction H as [q Hred IHsn]. intros q0 Eq.
    constructor. intros u Hu. pose proof (IHsn (shape u)) as IHu. apply IHu.
    - assert (Es : (shape q0) ==> (shape u)).
      { apply step_shape; assumption. }
      rewrite Eq in Es. exact Es.
    - reflexivity. }
  apply G with (s := shape t0); auto.
Qed.

Inductive shape_lc_at : nat -> tm -> Prop :=
  | slc_bvar : forall k i, i < k -> shape_lc_at k (tm_bvar i)
  | slc_fvar : forall k x, shape_lc_at k (tm_fvar x)
  | slc_abs : forall k t, shape_lc_at (S k) t ->
      shape_lc_at k (tm_abs (Ty_BVar 0) t)
  | slc_app : forall k t1 t2, shape_lc_at k t1 -> shape_lc_at k t2 ->
      shape_lc_at k (tm_app t1 t2)
  | slc_tabs : forall k t, shape_lc_at k t -> shape_lc_at k (tm_tabs t)
  | slc_tapp : forall k t, shape_lc_at k t -> shape_lc_at k (tm_tapp t (Ty_BVar 0)).
Definition semantic_pred := tm -> Prop.
Definition saturated (R : semantic_pred) : Prop :=
  (forall t, R t -> shape_lc_at 0 t /\ shape_sn t /\
    (forall u, t ==> u -> R u)) /\
  (forall t, shape_lc_at 0 t -> (exists u, t ==> u) ->
    (forall u, t ==> u -> R u) -> R t).
Definition tenv := atom -> semantic_pred.
Definition tenv_ok (Delta : ty_context) (rho : tenv) : Prop :=
  forall X, saturated (rho X).
Definition tenv_extend (rho : tenv) (X : atom) (R : semantic_pred) : tenv :=
  fun Y => if Nat.eqb X Y then R else rho Y.

Fixpoint lr (rho : tenv) (bs : list semantic_pred) (T : ty) : semantic_pred :=
  match T with
  | Ty_BVar _ => fun t => shape_lc_at 0 t /\ shape_sn t
  | Ty_FVar X => rho X
  | Ty_Arrow T1 T2 =>
      fun t => shape_lc_at 0 t /\ shape_sn t /\
        forall u, lr rho bs T1 u -> lr rho bs T2 (tm_app t u)
  | Ty_All T1 =>
      fun t => shape_lc_at 0 t /\ shape_sn t /\
        forall U R, locally_closed_ty U -> saturated R ->
          lr rho (R :: bs) T1 (tm_tapp t (Ty_BVar 0))
  end.

Definition bs_ok (bs : list semantic_pred) : Prop := Forall saturated bs.

Lemma shape_lc_weaken : forall j k t, j <= k -> shape_lc_at j t ->
  shape_lc_at k t.
Proof.
  intros j k t Hjk H. revert k Hjk.
  induction H as [j0 i Hi|j0 x|j0 t Ht IH|j0 t1 t2 H1 IH1 H2 IH2|
      j0 t Ht IH|j0 t Ht IH]; intros k' Hjk; simpl.
  - constructor. lia.
  - constructor.
  - constructor. apply IH. lia.
  - constructor; [apply IH1|apply IH2]; assumption.
  - constructor. apply IH. assumption.
  - constructor. apply IH. assumption.
Qed.

Lemma shape_lc_open : forall k u t,
  shape_lc_at (S k) t -> shape_lc_at 0 u ->
  shape_lc_at k (shape_open_rec k u t).
Proof.
  intros k u t. revert k u.
  induction t as [i|x|A t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros k u Ht Hu; inversion Ht; subst; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply shape_lc_weaken with (j := 0); [lia|assumption].
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - constructor. apply IH; assumption.
  - constructor; [apply IH1|apply IH2]; assumption.
  - constructor. apply IH; assumption.
  - constructor. apply IH; assumption.
Qed.

Lemma shape_lc_abs_inv : forall k t,
  shape_lc_at k (tm_abs (Ty_BVar 0) t) -> shape_lc_at (S k) t.
Proof. intros; inversion H; assumption. Qed.

Lemma shape_lc_tabs_inv : forall k t,
  shape_lc_at k (tm_tabs t) -> shape_lc_at k t.
Proof. intros; inversion H; assumption. Qed.

Lemma shape_lc_step : forall t u, shape_lc_at 0 t -> t ==> u -> shape_lc_at 0 u.
Proof.
  intros t u Hlc Hs. revert Hlc.
  induction Hs; intros Hlc; simpl in *.
  - inversion Hlc; subst.
    eapply shape_lc_open; eauto using shape_lc_abs_inv.
  - inversion Hlc; subst. constructor.
    + apply IHHs. assumption.
    + assumption.
  - inversion Hlc; subst. constructor.
    + assumption.
    + apply IHHs. assumption.
  - inversion Hlc; subst. eauto using shape_lc_tabs_inv.
  - inversion Hlc; subst. constructor; eauto.
Qed.

Lemma shape_sn_step : forall t, shape_sn t -> forall u, t ==> u -> shape_sn u.
Proof. intros t H; induction H; intros u Hu; eauto. Qed.

Lemma shape_value_no_step : forall t, shape_value t ->
  forall u, ~ (t ==> u).
Proof. intros t H; inversion H; intros u Hu; inversion Hu. Qed.

Lemma shape_app_cases : forall q v z, tm_app q v ==> z ->
  (exists b, q = tm_abs (Ty_BVar 0) b /\ shape_value v /\
    z = shape_open_rec 0 v b) \/
  (exists q', q ==> q' /\ z = tm_app q' v) \/
  (exists v', shape_value q /\ v ==> v' /\ z = tm_app q v').
Proof.
  intros q v z H; inversion H; subst.
  - left. eauto.
  - right; left. eauto.
  - right; right. eauto.
Qed.

Lemma shape_tapp_cases : forall q z, tm_tapp q (Ty_BVar 0) ==> z ->
  (exists b, q = tm_tabs b /\ z = b) \/
  (exists q', q ==> q' /\ z = tm_tapp q' (Ty_BVar 0)).
Proof.
  intros q z H; inversion H; subst.
  - left. eauto.
  - right. eauto.
Qed.

Lemma lr_app_expand : forall rho bs A B q,
  saturated (lr rho bs A) -> saturated (lr rho bs B) ->
  shape_lc_at 0 q -> (exists q', q ==> q') ->
  (forall q', q ==> q' -> lr rho bs (Ty_Arrow A B) q') ->
  forall v, lr rho bs A v -> lr rho bs B (tm_app q v).
Proof.
  intros rho bs A B q SA SB Hlq Hex Hallq v Hv.
  destruct SA as [SAv SAb]. destruct SB as [SBv SBb].
  pose proof (proj1 (proj2 (SAv _ Hv))) as Hsv.
  revert Hv. induction Hsv as [v Hred IH]. intros Hv.
  apply SBb.
  - constructor; [exact Hlq|exact (proj1 (SAv _ Hv))].
  - destruct Hex as [q' Hq']. exists (tm_app q' v). constructor; assumption.
  - intros z Hz. destruct (shape_app_cases q v z Hz) as [Root|[Left|Right]].
    + destruct Root as [b Hroot]. destruct Hroot as [Hb [Hvv Heq]].
      rewrite Hb in Hex. destruct Hex as [w Hw]. inversion Hw.
    + destruct Left as [q' Hleft]. destruct Hleft as [Hq' Heq]. rewrite Heq.
      pose proof (Hallq _ Hq') as Q. destruct Q as [_ [_ Qapp]].
      exact (Qapp _ Hv).
    + destruct Right as [v' Hright]. destruct Hright as [Hvq [Hv' Heq]].
      rewrite Heq. apply IH.
      * exact Hv'.
      * exact (proj2 (proj2 (SAv _ Hv)) _ Hv').
Qed.

Lemma lr_arrow_sat : forall rho bs T1 T2,
  saturated (lr rho bs T1) -> saturated (lr rho bs T2) ->
  saturated (lr rho bs (Ty_Arrow T1 T2)).
Proof.
  intros rho bs T1 T2 H1 H2. unfold saturated in H1, H2.
  destruct H1 as [Hsat1 Hback1]. destruct H2 as [Hsat2 Hback2].
  unfold saturated. split.
  - intros t Ht. destruct Ht as [Hl [Hsn Hfun]]. split; [exact Hl|]. split; [exact Hsn|].
    intros u Hu. split; [apply shape_lc_step with t; assumption|].
    split; [apply shape_sn_step with t; assumption|].
    intros v Hv. apply (proj2 (proj2 (Hsat2 _ (Hfun v Hv)))).
    constructor; assumption.
  - intros q Hlq Hex Hallq. constructor; [exact Hlq|]. constructor.
    + constructor. intros z Hz. apply (proj1 (proj2 (Hallq z Hz))).
    + intros v Hv. eapply lr_app_expand.
      * unfold saturated. split; [exact Hsat1|exact Hback1].
      * unfold saturated. split; [exact Hsat2|exact Hback2].
      * exact Hlq.
      * exact Hex.
      * exact Hallq.
      * exact Hv.
Qed.
(* old body removed *)
(*
  destruct Ht as [Hl [Hsn Hr]]. split.
  - intros u Hu. split; [exact Hl|]. split; [exact Hsn|].
    intros v Hv. apply (proj1 (proj2 (Hsat2 _ (Hr v Hv)))).
    constructor; assumption.
  - intros q Hlq Hex Hallq. constructor; [exact Hlq|]. constructor.
    + constructor. intros z Hz. apply (proj1 (proj2 (Hallq z Hz))).
    + intros v Hv. apply Hback2.
      * constructor; assumption.
      * destruct Hex as [q' Hq']. exists (tm_app q' v). constructor; assumption.
      * intros z Hz. inversion Hz; subst.
        -- exfalso. eapply (shape_value_no_step q); eauto.
        -- apply (proj2 (proj2 (Hsat2 _ (Hallq _ H0))) v Hv).
        -- apply (proj2 (proj2 (Hsat1 _ Hv0)) _
             (Hr _ (proj1 (proj2 (Hsat1 _ Hv0))))).
  Qed. *)

Lemma lr_all_sat : forall rho bs T,
  (forall R, saturated R -> saturated (lr rho (R :: bs) T)) ->
  saturated (lr rho bs (Ty_All T)).
Proof.
  intros rho bs T HI. unfold saturated in HI.
  unfold saturated. split.
  - intros t Ht. destruct Ht as [Hl [Hsn Hr]]. split; [exact Hl|]. split; [exact Hsn|].
    intros u Hu. split; [apply shape_lc_step with t; assumption|].
    split; [apply shape_sn_step with t; assumption|].
    intros U R HUl HR.
    apply (proj2 (proj2 ((proj1 (HI R HR)) _ (Hr U R HUl HR)))).
    constructor; assumption.
  - intros q Hlq Hex Hallq. constructor; [exact Hlq|]. constructor.
    + constructor. intros z Hz. apply (proj1 (proj2 (Hallq z Hz))).
    + intros U R HUl HR. apply (proj2 (HI R HR)).
      * constructor; assumption.
      * destruct Hex as [q' Hq']. exists (tm_tapp q' (Ty_BVar 0)).
        constructor; assumption.
      * intros z Hz. destruct (shape_tapp_cases q z Hz) as [Root|Inner].
        -- destruct Root as [b Hroot]. destruct Hroot as [Hb Heq].
           rewrite Hb in Hex. destruct Hex as [w Hw]. inversion Hw.
        -- destruct Inner as [q' Hinner]. destruct Hinner as [Hq' Heq].
           rewrite Heq. pose proof (Hallq _ Hq') as Q.
           exact ((proj2 (proj2 Q)) U R HUl HR).
Qed.

Lemma base_sat : saturated (fun t => shape_lc_at 0 t /\ shape_sn t).
Proof.
  unfold saturated. split.
  - intros t [Hl Hsn]. split; [exact Hl|]. split; [exact Hsn|].
    intros u Hu. split; [apply shape_lc_step with t; assumption|].
    apply shape_sn_step with t; assumption.
  - intros q Hlq Hex Hall. split; [exact Hlq|]. constructor.
    intros u Hu. apply (proj2 (Hall u Hu)).
Qed.

Lemma lr_sat_raw : forall Delta rho bs T,
  tenv_ok Delta rho -> bs_ok bs -> saturated (lr rho bs T).
Proof.
  intros Delta rho bs T Hok Hbok. revert bs Hbok.
  induction T; intros bs Hbok.
  - simpl. apply base_sat.
  - simpl. apply Hok.
  - simpl. apply lr_arrow_sat.
    + apply IHT1; assumption.
    + apply IHT2; assumption.
  - simpl. apply lr_all_sat. intros R HR.
    apply IHT. constructor; assumption.
Qed.

Lemma lr_sat : forall Delta rho bs T,
  tenv_ok Delta rho -> bs_ok bs -> wf_ty Delta T -> saturated (lr rho bs T).
Proof. intros Delta rho bs T Hok Hbok Hwf.
  apply (lr_sat_raw Delta rho bs T); assumption.
Qed.

Fixpoint inst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs _ t1 => tm_abs (Ty_BVar 0) (inst sigma t1)
  | tm_app t1 t2 => tm_app (inst sigma t1) (inst sigma t2)
  | tm_tabs t1 => tm_tabs (inst sigma t1)
  | tm_tapp t1 _ => tm_tapp (inst sigma t1) (Ty_BVar 0)
  end.

Lemma shape_inst : forall sigma t, inst sigma (shape t) = inst sigma t.
Proof. intros; induction t; simpl; f_equal; auto. Qed.

Lemma shape_lc_open_no_match : forall k u t,
  shape_lc_at k t -> shape_open_rec k u t = t.
Proof.
  intros k u t. revert k u.
  induction t as [i|x|A t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros k u H; inversion H; subst; simpl.
  - destruct (Nat.eqb k i) eqn:E. apply Nat.eqb_eq in E. subst; lia.
    reflexivity.
  - reflexivity.
  - f_equal. apply IH; assumption.
  - f_equal; [apply IH1; assumption|apply IH2; assumption].
  - f_equal. apply IH; assumption.
  - f_equal. apply IH; assumption.
Qed.

Lemma shape_lc_no_open : forall k u t,
  shape_lc_at 0 t -> shape_open_rec k u t = t.
Proof. intros k u t H. apply shape_lc_open_no_match with (k := k).
  apply shape_lc_weaken with (j := 0); [lia|assumption].
Qed.

Lemma inst_open_rec : forall k sigma x t,
  (forall y, shape_lc_at 0 (sigma y)) ->
  inst sigma (shape_open_rec k (tm_fvar x) t) =
    shape_open_rec k (sigma x) (inst sigma t).
Proof.
  intros k sigma x t Hsig. revert k x.
  induction t as [i|y|A t IH|t1 IH1 t2 IH2|t IH|t IH];
    intros k x; simpl.
  - destruct (Nat.eqb k i) eqn:E; simpl.
    + reflexivity.
    + reflexivity.
  - rewrite (shape_lc_no_open k (sigma x) (sigma y)); [reflexivity|apply Hsig].
  - f_equal. apply IH.
  - f_equal; [apply IH1|apply IH2].
  - f_equal. apply IH.
  - f_equal. apply IH.
Qed.

Lemma inst_open : forall sigma x t,
  (forall y, shape_lc_at 0 (sigma y)) ->
  inst sigma (shape_open_rec 0 (tm_fvar x) t) =
    shape_open_rec 0 (sigma x) (inst sigma t).
Proof. intros; apply inst_open_rec; assumption. Qed.

Fixpoint lc_inst (sigma : atom -> tm) (t : tm) : Prop :=
  shape_lc_at 0 (inst sigma t).

Definition ctx_rel (Gamma : context) (rho : tenv) (sigma : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> lr rho [] T (sigma x).


Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationNoneHardTask.
