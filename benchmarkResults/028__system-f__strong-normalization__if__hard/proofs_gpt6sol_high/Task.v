(** System F CBV strong-normalization benchmark, Hard variant.
    Features: if. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfHardTask.

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

  | Ty_All : ty -> ty
  | Ty_Bool : ty.

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
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.

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

Notation "'Bool'" := Ty_Bool (in custom systemf_ty at level 0) : systemf_scope.
Notation "'true'" := tm_true (in custom systemf_tm at level 0) : systemf_scope.
Notation "'false'" := tm_false (in custom systemf_tm at level 0) : systemf_scope.
Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm, t3 custom systemf_tm at level 200) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_rec k u t1) (open_tm_rec k u t2) (open_tm_rec k u t3)
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2) (open_tm_ty_rec k U t3)
  end.

Definition open_tm_ty (t : tm) (U : ty) : tm :=
  open_tm_ty_rec 0 U t.

Fixpoint ty_subst (X : atom) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then U else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst X U T1) (ty_subst X U T2)
  | Ty_All T1 => Ty_All (ty_subst X U T1)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_ty_subst X U t1) (tm_ty_subst X U t2) (tm_ty_subst X U t3)
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_subst x s t1) (tm_subst x s t2) (tm_subst x s t3)
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
      lc_ty_at k (Ty_All T)
  | lc_ty_bool : forall k, lc_ty_at k Ty_Bool.

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
  | lc_tm_true : forall K k, lc_tm_at K k tm_true
  | lc_tm_false : forall K k, lc_tm_at K k tm_false
  | lc_tm_if : forall K k t1 t2 t3,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 -> lc_tm_at K k (tm_if t1 t2 t3).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_true : value tm_true
  | v_false : value tm_false.

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
  | ST_IfTrue : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_if tm_true t1 t2 --> t1
  | ST_IfFalse : forall t1 t2,
      locally_closed_tm t1 ->
      locally_closed_tm t2 ->
      tm_if tm_false t1 t2 --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      locally_closed_tm t2 ->
      locally_closed_tm t3 ->
      tm_if t1 t2 t3 --> tm_if t1' t2 t3
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
      wf_ty Delta (Ty_All T)
  | WF_Bool : forall Delta, wf_ty Delta Ty_Bool.

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
  | T_True : forall Delta Gamma, has_type Delta Gamma tm_true Ty_Bool
  | T_False : forall Delta Gamma, has_type Delta Gamma tm_false Ty_Bool
  | T_If : forall Delta Gamma t1 t2 t3 T,
      has_type Delta Gamma t1 Ty_Bool ->
      has_type Delta Gamma t2 T -> has_type Delta Gamma t3 T ->
      has_type Delta Gamma (tm_if t1 t2 t3) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* Construct the logical relation and supporting proofs here. *)

Lemma lc_ty_weaken : forall K J T,
  K <= J -> lc_ty_at K T -> lc_ty_at J T.
Proof.
  intros K J T Hle Hlc; revert J Hle.
  induction Hlc; intros J Hle.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHHlc. lia.
  - apply lc_ty_bool.
Qed.

Lemma lc_tm_weaken : forall K k J j t,
  K <= J -> k <= j -> lc_tm_at K k t -> lc_tm_at J j t.
Proof.
  intros K k J j t HK Hk Hlc; revert J j HK Hk.
  induction Hlc; intros J j HK Hk.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_weaken; eauto.
    + apply IHHlc; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHHlc; lia.
  - apply lc_tm_tapp.
    + apply IHHlc; lia.
    + eapply lc_ty_weaken; eauto.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; eauto.
Qed.

Lemma lc_ty_open_rec : forall T K U,
  lc_ty_at (S K) T -> locally_closed_ty U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  induction T; intros K U HT HU; simpl in *; inversion HT; subst;
    try (constructor; eauto; fail).
  destruct (Nat.eqb_spec K n); subst.
  - eapply lc_ty_weaken with (K:=0); [lia | exact HU].
  - constructor; lia.
Qed.

Lemma lc_tm_open_rec : forall t k K u,
  lc_tm_at K (S k) t -> locally_closed_tm u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros k K u Ht Hu; simpl in *; inversion Ht; subst;
    try (constructor; eauto; fail).
  destruct (Nat.eqb_spec k n); subst.
  - eapply lc_tm_weaken with (K:=0) (k:=0); [lia | lia | exact Hu].
  - constructor; lia.
Qed.

Lemma lc_tm_ty_open_rec : forall t K k U,
  lc_tm_at (S K) k t -> locally_closed_ty U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k U Ht HU; simpl in *; inversion Ht; subst;
    try (constructor; eauto using lc_ty_open_rec; fail).
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v Hv; inversion Hv; subst; unfold locally_closed_tm; auto with core. Qed.

Lemma step_lc : forall t u,
  t --> u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u Hstep; induction Hstep; intro Hlc;
    unfold locally_closed_tm in *; inversion Hlc; subst.
  - inversion H; subst. eapply lc_tm_open_rec; eauto using value_lc.
  - apply lc_tm_app; eauto.
  - apply lc_tm_app; eauto.
  - inversion H; subst. eapply lc_tm_ty_open_rec; eauto.
  - apply lc_tm_tapp; eauto.
  - assumption.
  - assumption.
  - apply lc_tm_if; eauto.
Qed.

Lemma sn_step : forall t u,
  strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof. intros t u Hsn Hstep; inversion Hsn; eauto. Qed.

Definition good (R : tm -> Prop) : Prop :=
  (forall t, R t -> locally_closed_tm t /\ strongly_normalizing t) /\
  (forall t u, R t -> t --> u -> R u) /\
  (forall t, locally_closed_tm t -> ~ value t ->
    (forall u, t --> u -> R u) -> R t).

Definition base_candidate (t : tm) : Prop :=
  locally_closed_tm t /\ strongly_normalizing t.

Lemma good_base : good base_candidate.
Proof.
  unfold good, base_candidate; split; [|split].
  - intros t H; exact H.
  - intros t u [Hlc Hsn] Hstep; split;
      eauto using step_lc, sn_step.
  - intros t Hlc _ Hsucc; split; auto.
    constructor. intros u Hu. exact (proj2 (Hsucc u Hu)).
Qed.

Definition sat (P : tm -> Prop) (t : tm) : Prop :=
  locally_closed_tm t /\ strongly_normalizing t /\
  (forall v, t -->* v -> value v -> P v).

Lemma good_sat : forall P, good (sat P).
Proof.
  intro P; unfold good, sat; split; [|split].
  - intros t [Hlc [Hsn _]]; auto.
  - intros t u [Hlc [Hsn HP]] Hstep.
    split; [eauto using step_lc|]. split; [eauto using sn_step|].
    intros v Hmulti Hv. apply HP with (v:=v); auto.
    eapply multi_step; eauto.
  - intros t Hlc Hnv Hsucc.
    split; [assumption|]. split.
    + constructor. intros u Hu. exact (proj1 (proj2 (Hsucc u Hu))).
    + intros v Hmulti Hv. inversion Hmulti; subst.
      * contradiction.
      * destruct (Hsucc y H) as [_ [_ HP]]. eauto.
Qed.

Fixpoint interp (T : ty) (bound : list (tm -> Prop))
    (free : atom -> tm -> Prop) : tm -> Prop :=
  match T with
  | Ty_BVar n => nth n bound base_candidate
  | Ty_FVar X => free X
  | Ty_Arrow A B =>
      sat (fun v => match v with
        | tm_abs _ body => forall a, value a ->
            interp A bound free a -> interp B bound free (open_tm body a)
        | _ => False end)
  | Ty_All B =>
      sat (fun v => match v with
        | tm_tabs body => forall U C, locally_closed_ty U -> good C ->
            interp B (C :: bound) free (open_tm_ty body U)
        | _ => False end)
  | Ty_Bool => sat (fun v => v = tm_true \/ v = tm_false)
  end.

Lemma nth_good : forall bound n,
  Forall good bound -> good (nth n bound base_candidate).
Proof.
  induction bound as [|C bound IH]; intros [|n] Hb; simpl; auto using good_base.
  - inversion Hb; subst; assumption.
  - inversion Hb; subst; apply IH; assumption.
Qed.

Lemma interp_good : forall T bound free,
  Forall good bound -> (forall X, good (free X)) ->
  good (interp T bound free).
Proof.
  induction T; intros bound free Hb Hf; simpl; eauto using good_sat.
  - apply nth_good; assumption.
Qed.

Lemma app_compat : forall A B f a,
  good A -> good B ->
  sat (fun v => match v with
    | tm_abs _ body => forall u, value u -> A u -> B (open_tm body u)
    | _ => False end) f ->
  A a -> B (tm_app f a).
Proof.
  intros A B f a HA HB Hf Ha.
  pose proof (proj1 (good_sat _) f Hf) as [Hlf Hsf].
  revert a Ha.
  induction Hsf as [f Hsf IHf]; intros a Ha.
  pose proof (proj1 HA a Ha) as [Hla Hsa].
  induction Hsa as [a Hsa IHa].
  apply (proj2 (proj2 HB));
    [unfold locally_closed_tm in *; apply lc_tm_app; assumption|intro Hv; inversion Hv|].
  intros u Hstep. inversion Hstep; subst.
  - destruct Hf as [_ [_ Hval]].
    apply (Hval (tm_abs T t)); auto using multi_refl, v_abs.
  - apply IHf; auto.
    apply (proj1 (proj2 (good_sat _))) with (t:=f); assumption.
    eauto using step_lc.
  - apply IHa; auto.
    apply (proj1 (proj2 HA)) with (t:=a); assumption.
    eauto using step_lc.
Qed.

Lemma tapp_compat : forall R f U,
  good R -> locally_closed_ty U ->
  sat (fun v => match v with
    | tm_tabs body => R (open_tm_ty body U)
    | _ => False end) f ->
  R (tm_tapp f U).
Proof.
  intros R f U HR HU Hf.
  pose proof (proj1 (good_sat _) f Hf) as [Hlf Hsf].
  induction Hsf as [f Hsf IHf].
  apply (proj2 (proj2 HR));
    [unfold locally_closed_tm in *; apply lc_tm_tapp; assumption|intro Hv; inversion Hv|].
  intros u Hstep. inversion Hstep; subst.
  - destruct Hf as [_ [_ Hval]].
    apply (Hval (tm_tabs t)); auto using multi_refl, v_tabs.
  - apply IHf.
    + assumption.
    + apply (proj1 (proj2 (good_sat _))) with (t:=f); assumption.
    + eauto using step_lc.
Qed.

Lemma if_compat : forall R g t e,
  good R -> sat (fun v => v = tm_true \/ v = tm_false) g ->
  R t -> R e -> R (tm_if g t e).
Proof.
  intros R g t e HR Hg Ht He.
  pose proof (proj1 (good_sat _) g Hg) as [Hlg Hsg].
  induction Hsg as [g Hsg IHg].
  pose proof (proj1 HR t Ht) as [Hlt _].
  pose proof (proj1 HR e He) as [Hle _].
  apply (proj2 (proj2 HR));
    [unfold locally_closed_tm in *; apply lc_tm_if; assumption|intro Hv; inversion Hv|].
  intros u Hstep. inversion Hstep; subst; auto.
  - apply IHg.
    + assumption.
    + apply (proj1 (proj2 (good_sat _))) with (t:=g); assumption.
    + eauto using step_lc.
Qed.

Lemma lc_ty_open_inv_rec : forall T K X,
  lc_ty_at K (open_ty_rec K (Ty_FVar X) T) -> lc_ty_at (S K) T.
Proof.
  induction T; intros K X H; simpl in H.
  - destruct (Nat.eqb_spec K n); subst; [apply lc_ty_bvar; lia|].
    inversion H; subst; apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - inversion H; subst; apply lc_ty_arrow; eauto.
  - inversion H; subst; apply lc_ty_all; eauto.
  - apply lc_ty_bool.
Qed.

Lemma lc_tm_open_inv_rec : forall t k K x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros k K x H; simpl in H.
  - destruct (Nat.eqb_spec k n); subst; [apply lc_tm_bvar; lia|].
    inversion H; subst; apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - inversion H; subst; apply lc_tm_abs; eauto.
  - inversion H; subst; apply lc_tm_app; eauto.
  - inversion H; subst; apply lc_tm_tabs; eauto.
  - inversion H; subst; apply lc_tm_tapp; eauto.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - inversion H; subst; apply lc_tm_if; eauto.
Qed.

Lemma lc_tm_ty_open_inv_rec : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H.
  - inversion H; subst; apply lc_tm_bvar; assumption.
  - apply lc_tm_fvar.
  - inversion H; subst; apply lc_tm_abs; eauto using lc_ty_open_inv_rec.
  - inversion H; subst; apply lc_tm_app; eauto.
  - inversion H; subst; apply lc_tm_tabs; eauto.
  - inversion H; subst; apply lc_tm_tapp; eauto using lc_ty_open_inv_rec.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - inversion H; subst; apply lc_tm_if; eauto.
Qed.

Fixpoint atom_max (L : list atom) : nat :=
  match L with [] => 0 | x :: L' => Nat.max x (atom_max L') end.

Lemma atom_max_spec : forall L x, In x L -> x <= atom_max L.
Proof.
  induction L as [|y L IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [<-|H]; [lia|]. apply IH in H; lia.
Qed.

Lemma fresh_atom : forall (L : list atom), exists x, ~ In x L.
Proof.
  intro L; exists (S (atom_max L)); intro H.
  apply atom_max_spec in H; lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf; induction Hwf as
    [Delta X Hin | Delta A B HA IHA HB IHB |
     L Delta T Hbody IH | Delta].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - destruct (fresh_atom L) as [X HX].
    apply lc_ty_all. eapply lc_ty_open_inv_rec with (X:=X).
    apply IH; assumption.
  - apply lc_ty_bool.
Qed.

Lemma typing_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty; induction Hty as
    [Delta Gamma x T Hlook Hwf |
     L Delta Gamma A body B HA Hbody IH |
     Delta Gamma f a A B Hf IHf Ha IHa |
     L Delta Gamma body B Hbody IH |
     Delta Gamma f B U Hf IHf HU |
     Delta Gamma | Delta Gamma |
     Delta Gamma g t e T Hg IHg Ht IHt He IHe].
  - apply lc_tm_fvar.
  - destruct (fresh_atom L) as [x Hx].
    apply lc_tm_abs; [apply wf_ty_lc with (Delta:=Delta); assumption|].
    eapply lc_tm_open_inv_rec with (x:=x). apply IH; assumption.
  - apply lc_tm_app; assumption.
  - destruct (fresh_atom L) as [X HX].
    apply lc_tm_tabs. eapply lc_tm_ty_open_inv_rec with (X:=X).
    apply IH; assumption.
  - apply lc_tm_tapp; [assumption|].
    apply wf_ty_lc with (Delta:=Delta); assumption.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; assumption.
Qed.

Lemma typing_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty; induction Hty as
    [Delta Gamma x T Hlook Hwf |
     L Delta Gamma A body B HA Hbody IH |
     Delta Gamma f a A B Hf IHf Ha IHa |
     L Delta Gamma body B Hbody IH |
     Delta Gamma f B U Hf IHf HU |
     Delta Gamma | Delta Gamma |
     Delta Gamma g t e T Hg IHg Ht IHt He IHe].
  - eapply wf_ty_lc; eauto.
  - apply lc_ty_arrow; [eapply wf_ty_lc; eauto|].
    destruct (fresh_atom L) as [x Hx]; exact (IH x Hx).
  - inversion IHf; subst; assumption.
  - destruct (fresh_atom L) as [X HX].
    apply lc_ty_all. eapply lc_ty_open_inv_rec with (X:=X).
    apply IH; assumption.
  - inversion IHf; subst. eapply lc_ty_open_rec; eauto using wf_ty_lc.
  - apply lc_ty_bool.
  - apply lc_ty_bool.
  - exact IHt.
Qed.

Fixpoint map_ty (sigma : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sigma X
  | Ty_Arrow A B => Ty_Arrow (map_ty sigma A) (map_ty sigma B)
  | Ty_All B => Ty_All (map_ty sigma B)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint map_tm_ty (sigma : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T body => tm_abs (map_ty sigma T) (map_tm_ty sigma body)
  | tm_app f a => tm_app (map_tm_ty sigma f) (map_tm_ty sigma a)
  | tm_tabs body => tm_tabs (map_tm_ty sigma body)
  | tm_tapp f T => tm_tapp (map_tm_ty sigma f) (map_ty sigma T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if g t e => tm_if (map_tm_ty sigma g) (map_tm_ty sigma t) (map_tm_ty sigma e)
  end.

Fixpoint map_tm (theta : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => theta x
  | tm_abs T body => tm_abs T (map_tm theta body)
  | tm_app f a => tm_app (map_tm theta f) (map_tm theta a)
  | tm_tabs body => tm_tabs (map_tm theta body)
  | tm_tapp f T => tm_tapp (map_tm theta f) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if g t e => tm_if (map_tm theta g) (map_tm theta t) (map_tm theta e)
  end.

Definition realize (sigma : atom -> ty) (theta : atom -> tm) (t : tm) : tm :=
  map_tm theta (map_tm_ty sigma t).

Lemma map_ty_lc : forall sigma T K,
  (forall X, locally_closed_ty (sigma X)) ->
  lc_ty_at K T -> lc_ty_at K (map_ty sigma T).
Proof.
  intros sigma T K Hsigma HT; induction HT; simpl;
    eauto using lc_ty_at, lc_ty_weaken.
  eapply lc_ty_weaken with (K:=0); [lia|apply Hsigma].
Qed.

Lemma map_tm_ty_lc : forall sigma t K k,
  (forall X, locally_closed_ty (sigma X)) ->
  lc_tm_at K k t -> lc_tm_at K k (map_tm_ty sigma t).
Proof.
  intros sigma t K k Hsigma Ht; induction Ht; simpl;
    eauto using lc_tm_at, map_ty_lc.
Qed.

Lemma map_tm_lc : forall theta t K k,
  (forall x, locally_closed_tm (theta x)) ->
  lc_tm_at K k t -> lc_tm_at K k (map_tm theta t).
Proof.
  intros theta t K k Htheta Ht; induction Ht; simpl;
    eauto using lc_tm_at.
  eapply lc_tm_weaken with (K:=0) (k:=0); [lia|lia|apply Htheta].
Qed.

Lemma open_ty_rec_lc_id : forall T K U,
  lc_ty_at K T -> open_ty_rec K U T = T.
Proof.
  induction T; intros K U Hlc; simpl; inversion Hlc; subst; auto.
  - destruct (Nat.eqb_spec K n); [lia|reflexivity].
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma open_tm_rec_lc_id : forall t K k u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  induction t; intros K k u Hlc; simpl; inversion Hlc; subst; auto.
  - destruct (Nat.eqb_spec k n); [lia|reflexivity].
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma open_tm_ty_rec_lc_id : forall t K k U,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  induction t; intros K k U Hlc; simpl; inversion Hlc; subst; auto.
  - f_equal; eauto using open_ty_rec_lc_id.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto. apply open_ty_rec_lc_id; assumption.
  - f_equal; eauto.
Qed.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => [] | tm_fvar x => [x]
  | tm_abs _ body | tm_tabs body => fv_tm body
  | tm_app f a => fv_tm f ++ fv_tm a
  | tm_tapp f _ => fv_tm f
  | tm_true | tm_false => []
  | tm_if g t e => fv_tm g ++ fv_tm t ++ fv_tm e
  end.

Fixpoint ftv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => [] | Ty_FVar X => [X]
  | Ty_Arrow A B => ftv_ty A ++ ftv_ty B
  | Ty_All B => ftv_ty B
  | Ty_Bool => []
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false => []
  | tm_abs T body => ftv_ty T ++ ftv_tm body
  | tm_app f a => ftv_tm f ++ ftv_tm a
  | tm_tabs body => ftv_tm body
  | tm_tapp f T => ftv_tm f ++ ftv_ty T
  | tm_if g t e => ftv_tm g ++ ftv_tm t ++ ftv_tm e
  end.

Definition put_ty (sigma : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else sigma Y.

Definition put_tm (theta : atom -> tm) (x : atom) (a : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then a else theta y.

Definition put_rel (free : atom -> tm -> Prop) (X : atom)
    (C : tm -> Prop) : atom -> tm -> Prop :=
  fun Y => if Nat.eqb X Y then C else free Y.

Lemma fv_tm_map_tm_ty : forall sigma t,
  fv_tm (map_tm_ty sigma t) = fv_tm t.
Proof. induction t; simpl; congruence. Qed.

Lemma map_tm_ty_open_tm_rec : forall sigma t k x,
  map_tm_ty sigma (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (tm_fvar x) (map_tm_ty sigma t).
Proof.
  intros sigma t; induction t; intros k x; simpl; try (f_equal; eauto; fail).
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma map_tm_open_tm_rec : forall theta x a t k,
  (forall y, locally_closed_tm (theta y)) ->
  locally_closed_tm a -> ~ In x (fv_tm t) ->
  map_tm (put_tm theta x a) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k a (map_tm theta t).
Proof.
  intros theta x a t; induction t; intros k Htheta Ha Hfresh; simpl in *.
  - destruct (Nat.eqb_spec k n); subst; simpl.
    + unfold put_tm. rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - assert (Hneq : x <> a0) by (intro E; subst; apply Hfresh; auto).
    unfold put_tm. apply Nat.eqb_neq in Hneq. rewrite Hneq.
    symmetry. eapply open_tm_rec_lc_id with (K:=0).
    eapply lc_tm_weaken with (K:=0) (k:=0); [lia|lia|apply Htheta].
  - f_equal. apply IHt; auto.
  - f_equal; [apply IHt1|apply IHt2]; auto;
      intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1; auto. intro H; apply Hfresh.
      apply in_or_app; left; assumption.
    + apply IHt2; auto. intro H; apply Hfresh.
      apply in_or_app; right. apply in_or_app; left; assumption.
    + apply IHt3; auto. intro H; apply Hfresh.
      apply in_or_app; right. apply in_or_app; right; assumption.
Qed.

Lemma map_ty_open_rec : forall sigma X U T K,
  (forall Y, locally_closed_ty (sigma Y)) ->
  ~ In X (ftv_ty T) ->
  map_ty (put_ty sigma X U) (open_ty_rec K (Ty_FVar X) T) =
  open_ty_rec K U (map_ty sigma T).
Proof.
  intros sigma X U T; induction T; intros K Hsigma Hfresh; simpl in *.
  - destruct (Nat.eqb_spec K n); subst; simpl.
    + unfold put_ty. rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - assert (Hneq : X <> a) by (intro E; subst; apply Hfresh; auto).
    unfold put_ty. apply Nat.eqb_neq in Hneq. rewrite Hneq.
    symmetry. eapply open_ty_rec_lc_id with (K:=K).
    eapply lc_ty_weaken with (K:=0); [lia|apply Hsigma].
  - f_equal; [apply IHT1|apply IHT2]; auto;
      intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal. apply IHT; auto.
  - reflexivity.
Qed.

Lemma map_tm_ty_open_rec : forall sigma X U t K,
  (forall Y, locally_closed_ty (sigma Y)) ->
  ~ In X (ftv_tm t) ->
  map_tm_ty (put_ty sigma X U) (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K U (map_tm_ty sigma t).
Proof.
  intros sigma X U t; induction t; intros K Hsigma Hfresh; simpl in *;
    try reflexivity.
  - f_equal.
    + apply map_ty_open_rec; auto. intro H; apply Hfresh; apply in_or_app; auto.
    + apply IHt; auto. intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal; [apply IHt1|apply IHt2]; auto;
      intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal. apply IHt; auto.
  - f_equal.
    + apply IHt; auto. intro H; apply Hfresh; apply in_or_app; auto.
    + apply map_ty_open_rec; auto. intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal.
    + apply IHt1; auto. intro H; apply Hfresh.
      apply in_or_app; left; assumption.
    + apply IHt2; auto. intro H; apply Hfresh.
      apply in_or_app; right. apply in_or_app; left; assumption.
    + apply IHt3; auto. intro H; apply Hfresh.
      apply in_or_app; right. apply in_or_app; right; assumption.
Qed.

Lemma map_tm_open_tm_ty_rec : forall theta t K U,
  (forall x, locally_closed_tm (theta x)) ->
  map_tm theta (open_tm_ty_rec K U t) =
  open_tm_ty_rec K U (map_tm theta t).
Proof.
  intros theta t; induction t; intros K U Htheta; simpl; try reflexivity.
  - symmetry. eapply open_tm_ty_rec_lc_id with (k:=0).
    eapply lc_tm_weaken with (K:=0) (k:=0); [lia|lia|apply Htheta].
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma sat_equiv : forall P Q,
  (forall v, value v -> (P v <-> Q v)) ->
  forall t, sat P t <-> sat Q t.
Proof.
  intros P Q Heq t; unfold sat; split.
  - intros [Hlc [Hsn Hval]]. split; [assumption|].
    split; [assumption|]. intros v Hmulti Hv.
    apply (proj1 (Heq v Hv)); eauto.
  - intros [Hlc [Hsn Hval]]. split; [assumption|].
    split; [assumption|]. intros v Hmulti Hv.
    apply (proj2 (Heq v Hv)); eauto.
Qed.

Definition same_bound (K : nat) (rho rho' : list (tm -> Prop)) : Prop :=
  forall i, i < K -> forall t,
    (nth i rho base_candidate t <-> nth i rho' base_candidate t).

Lemma same_bound_cons : forall K C rho rho',
  same_bound K rho rho' -> same_bound (S K) (C::rho) (C::rho').
Proof.
  unfold same_bound; intros K C rho rho' H i Hi t.
  destruct i; simpl; [tauto|]. apply H; lia.
Qed.

Lemma interp_bound_ext : forall T K rho rho' free t,
  lc_ty_at K T -> same_bound K rho rho' ->
  (interp T rho free t <-> interp T rho' free t).
Proof.
  induction T; intros K rho rho' free t Hlc Hsame; simpl in *.
  - inversion Hlc; subst. apply Hsame; assumption.
  - tauto.
  - inversion Hlc; subst.
    assert (Hdom : forall z, interp T1 rho free z <-> interp T1 rho' free z).
    { intro z; eapply IHT1; eauto. }
    assert (Hcod : forall z, interp T2 rho free z <-> interp T2 rho' free z).
    { intro z; eapply IHT2; eauto. }
    apply sat_equiv. intros v Hv.
    destruct v; simpl; try tauto. split; intros H a Ha HR.
    + apply (proj1 (Hcod _)).
      apply H; auto. apply (proj2 (Hdom _)); auto.
    + apply (proj2 (Hcod _)).
      apply H; auto. apply (proj1 (Hdom _)); auto.
  - inversion Hlc; subst. apply sat_equiv. intros v Hv.
    destruct v; simpl; try tauto. split; intros H U C HU HC.
    + apply (proj1 (IHT (S K) (C::rho) (C::rho') free _ H1
        (same_bound_cons K C rho rho' Hsame))). apply H; auto.
    + apply (proj2 (IHT (S K) (C::rho) (C::rho') free _ H1
        (same_bound_cons K C rho rho' Hsame))). apply H; auto.
  - apply sat_equiv; intros; tauto.
Qed.

Lemma interp_free_ext : forall T rho free free' t,
  (forall X, In X (ftv_ty T) -> forall u,
    free X u <-> free' X u) ->
  (interp T rho free t <-> interp T rho free' t).
Proof.
  induction T; intros rho free free' t Hsame; simpl in *.
  - tauto.
  - apply Hsame; auto.
  - apply sat_equiv. intros v Hv.
    destruct v; simpl; try tauto. split; intros H a Ha HR.
    + apply (proj1 (IHT2 rho free free' _ (fun X HX u => Hsame X (in_or_app _ _ _ (or_intror HX)) u))).
      apply H; auto.
      apply (proj2 (IHT1 rho free free' _ (fun X HX u => Hsame X (in_or_app _ _ _ (or_introl HX)) u))); auto.
    + apply (proj2 (IHT2 rho free free' _ (fun X HX u => Hsame X (in_or_app _ _ _ (or_intror HX)) u))).
      apply H; auto.
      apply (proj1 (IHT1 rho free free' _ (fun X HX u => Hsame X (in_or_app _ _ _ (or_introl HX)) u))); auto.
  - apply sat_equiv. intros v Hv.
    destruct v; simpl; try tauto. split; intros H U C HU HC.
    + apply (proj1 (IHT (C::rho) free free' _ Hsame)); apply H; auto.
    + apply (proj2 (IHT (C::rho) free free' _ Hsame)); apply H; auto.
  - apply sat_equiv; intros; tauto.
Qed.

Fixpoint insert_candidate (K : nat) (C : tm -> Prop)
    (rho : list (tm -> Prop)) : list (tm -> Prop) :=
  match K with
  | 0 => C :: rho
  | S K' => match rho with
      | [] => base_candidate :: insert_candidate K' C []
      | D :: rho' => D :: insert_candidate K' C rho'
      end
  end.

Lemma nth_insert_lt : forall K C rho i,
  i < K -> nth i (insert_candidate K C rho) base_candidate =
           nth i rho base_candidate.
Proof.
  induction K; intros C rho i Hi; [lia|].
  destruct rho as [|D rho]; destruct i; simpl; auto.
  - rewrite IHK by lia. destruct i; reflexivity.
  - apply IHK; lia.
Qed.

Lemma nth_insert_eq : forall K C rho,
  nth K (insert_candidate K C rho) base_candidate = C.
Proof.
  induction K; intros C rho; simpl; auto.
  destruct rho; simpl; apply IHK.
Qed.

Lemma interp_open_rec : forall T K U rho free t,
  lc_ty_at (S K) T -> locally_closed_ty U ->
  (interp (open_ty_rec K U T) rho free t <->
   interp T (insert_candidate K (interp U [] free) rho) free t).
Proof.
  induction T; intros K U rho free t Hlc HU; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb_spec K n); subst.
    + rewrite nth_insert_eq.
      apply interp_bound_ext with (K:=0); auto.
      unfold same_bound; intros; lia.
    + assert (n < K) by lia.
      rewrite nth_insert_lt by assumption. tauto.
  - tauto.
  - inversion Hlc; subst.
    assert (Hdom : forall z,
      interp (open_ty_rec K U T1) rho free z <->
      interp T1 (insert_candidate K (interp U [] free) rho) free z).
    { intro z; apply IHT1; auto. }
    assert (Hcod : forall z,
      interp (open_ty_rec K U T2) rho free z <->
      interp T2 (insert_candidate K (interp U [] free) rho) free z).
    { intro z; apply IHT2; auto. }
    apply sat_equiv. intros v Hv. destruct v; simpl; try tauto.
    split; intros H a Ha HR.
    + apply (proj1 (Hcod _)). apply H; auto.
      apply (proj2 (Hdom _)); auto.
    + apply (proj2 (Hcod _)). apply H; auto.
      apply (proj1 (Hdom _)); auto.
  - inversion Hlc; subst. apply sat_equiv. intros v Hv.
    destruct v; simpl; try tauto. split; intros H V C HV HC.
    + apply (proj1 (IHT (S K) U (C::rho) free _ H1 HU)).
      apply H; auto.
    + apply (proj2 (IHT (S K) U (C::rho) free _ H1 HU)).
      apply H; auto.
  - apply sat_equiv; intros; tauto.
Qed.

Lemma interp_open : forall T U free t,
  lc_ty_at 1 T -> locally_closed_ty U ->
  (interp (open_ty T U) [] free t <->
   interp T [interp U [] free] free t).
Proof. intros; apply interp_open_rec; auto. Qed.

Lemma interp_fvar_open : forall T X C free t,
  lc_ty_at 1 T -> ~ In X (ftv_ty T) ->
  (interp (open_ty T (Ty_FVar X)) [] (put_rel free X C) t <->
   interp T [C] free t).
Proof.
  intros T X C free t Hlc Hfresh.
  pose proof (interp_open T (Ty_FVar X) (put_rel free X C) t
    Hlc (lc_ty_fvar 0 X)) as Hopen.
  simpl in Hopen. unfold put_rel in Hopen. rewrite Nat.eqb_refl in Hopen.
  eapply iff_trans; [exact Hopen|].
  apply interp_free_ext.
  intros Y HY u. unfold put_rel.
  assert (X <> Y) by (intro E; subst; contradiction).
  apply Nat.eqb_neq in H. rewrite H. tauto.
Qed.

Lemma value_no_step : forall v u, value v -> ~ (v --> u).
Proof.
  intros v u Hv Hstep; inversion Hv; subst; inversion Hstep.
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv; constructor. intros u Hu.
  exfalso; eapply value_no_step; eauto.
Qed.

Lemma multi_value_eq : forall v u,
  value v -> v -->* u -> u = v.
Proof.
  intros v u Hv Hmulti; inversion Hmulti; subst; auto.
  exfalso; eapply value_no_step; eauto.
Qed.

Lemma sat_value : forall P v,
  value v -> P v -> sat P v.
Proof.
  intros P v Hv HP; unfold sat; split; [eauto using value_lc|].
  split; [eauto using value_sn|].
  intros u Hmulti Hu. rewrite (multi_value_eq v u Hv Hmulti); assumption.
Qed.

Lemma sat_map : forall P Q t,
  (forall v, value v -> P v -> Q v) ->
  sat P t -> sat Q t.
Proof.
  intros P Q t Hmap [Hlc [Hsn Hval]].
  unfold sat; split; [assumption|]. split; [assumption|].
  intros v Hmulti Hv; apply Hmap; auto.
Qed.

Fixpoint ftv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => ftv_ty T ++ ftv_context Gamma'
  end.

Lemma lookup_ftv_context : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (ftv_ty T) ->
  In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y A] Gamma IH]; intros x T X Hlook Hin;
    simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst. apply in_or_app; left; assumption.
  - apply in_or_app; right. eapply IH; eauto.
Qed.

Lemma realize_lc : forall sigma theta t,
  (forall X, locally_closed_ty (sigma X)) ->
  (forall x, locally_closed_tm (theta x)) ->
  locally_closed_tm t ->
  locally_closed_tm (realize sigma theta t).
Proof.
  intros sigma theta t Hsigma Htheta Hlc.
  unfold realize. apply map_tm_lc; auto.
  apply map_tm_ty_lc; auto.
Qed.

Lemma realize_id : forall t,
  realize (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  intro t; unfold realize.
  assert (forall T, map_ty (fun X => Ty_FVar X) T = T) as Hty.
  { induction T; simpl; congruence. }
  assert (forall u, map_tm_ty (fun X => Ty_FVar X) u = u) as Htmty.
  { induction u; simpl; try rewrite Hty; congruence. }
  assert (forall u, map_tm (fun x => tm_fvar x) u = u) as Htm.
  { induction u; simpl; congruence. }
  rewrite Htmty. apply Htm.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall sigma free theta,
    (forall X, locally_closed_ty (sigma X)) ->
    (forall X, good (free X)) ->
    (forall x, locally_closed_tm (theta x)) ->
    (forall x A, lookup_context x Gamma = Some A ->
      interp A [] free (theta x)) ->
    interp T [] free (realize sigma theta t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [Delta Gamma x T Hlook Hwf |
     L Delta Gamma A body B HA Hbody IH |
     Delta Gamma f a A B Hf IHf Ha IHa |
     L Delta Gamma body B Hbody IH |
     Delta Gamma f B U Hf IHf HU |
     Delta Gamma | Delta Gamma |
     Delta Gamma g t e T Hg IHg Ht IHt He IHe];
    intros sigma free theta Hsigma Hfree Htheta Hgamma.
  - unfold realize; simpl. apply Hgamma; assumption.
  - destruct (fresh_atom (L ++ fv_tm body)) as [x Hfresh].
    assert (Hx : ~ In x L).
    { intro H; apply Hfresh; apply in_or_app; left; assumption. }
    assert (Hfx : ~ In x (fv_tm body)).
    { intro H; apply Hfresh; apply in_or_app; right; assumption. }
    change (sat (fun v => match v with
      | tm_abs _ b => forall u, value u -> interp A [] free u ->
          interp B [] free (open_tm b u)
      | _ => False end) (realize sigma theta (tm_abs A body))).
    apply sat_value.
    + unfold realize; simpl. apply v_abs.
      change (locally_closed_tm (realize sigma theta (tm_abs A body))).
      apply realize_lc; auto. unfold locally_closed_tm.
      apply lc_tm_abs; [eapply wf_ty_lc; eauto|].
      eapply lc_tm_open_inv_rec with (x:=x).
      eapply typing_lc. apply Hbody; assumption.
    + unfold realize; simpl. intros u Hu Hru.
      assert (Htheta' : forall y, locally_closed_tm (put_tm theta x u y)).
      { intro y; unfold put_tm; destruct (Nat.eqb x y); auto.
        apply (proj1 (proj1 (interp_good A [] free (Forall_nil _) Hfree) u Hru)). }
      assert (Hgamma' : forall y D,
        lookup_context y ((x,A)::Gamma) = Some D ->
        interp D [] free (put_tm theta x u y)).
      { intros y D Hlook'; simpl in Hlook'.
        unfold put_tm. destruct (Nat.eqb x y) eqn:E.
        - apply Nat.eqb_eq in E; subst.
          rewrite Nat.eqb_refl in Hlook'. inversion Hlook'; subst; assumption.
        - rewrite Nat.eqb_sym in Hlook'. rewrite E in Hlook'.
          apply Hgamma; assumption. }
      specialize (IH x Hx sigma free (put_tm theta x u)
        Hsigma Hfree Htheta' Hgamma').
      unfold realize in IH at 1.
      unfold open_tm in IH |- *.
      rewrite map_tm_ty_open_tm_rec in IH.
      assert (Hlu : locally_closed_tm u).
      { exact (proj1 ((proj1 (interp_good A [] free
          (Forall_nil _) Hfree)) u Hru)). }
      assert (Hfresh' : ~ In x (fv_tm (map_tm_ty sigma body))).
      { rewrite fv_tm_map_tm_ty; assumption. }
      rewrite (map_tm_open_tm_rec theta x u (map_tm_ty sigma body) 0
        Htheta Hlu Hfresh') in IH.
      exact IH.
  - change (interp B [] free (tm_app (realize sigma theta f)
      (realize sigma theta a))).
    apply app_compat with (A:=interp A [] free).
    + apply interp_good; auto.
    + apply interp_good; auto.
    + apply IHf; assumption.
    + apply IHa; assumption.
  - destruct (fresh_atom
      (L ++ ftv_tm body ++ ftv_ty B ++ ftv_context Gamma))
      as [X Hfresh].
    assert (HX : ~ In X L).
    { intro H; apply Hfresh. apply in_or_app; left; assumption. }
    assert (Hft : ~ In X (ftv_tm body)).
    { intro H; apply Hfresh. apply in_or_app; right.
      apply in_or_app; left; assumption. }
    assert (HfB : ~ In X (ftv_ty B)).
    { intro H; apply Hfresh. apply in_or_app; right.
      apply in_or_app; right. apply in_or_app; left; assumption. }
    assert (HfG : ~ In X (ftv_context Gamma)).
    { intro H; apply Hfresh. apply in_or_app; right.
      apply in_or_app; right. apply in_or_app; right; assumption. }
    assert (HlcB : lc_ty_at 1 B).
    { eapply lc_ty_open_inv_rec with (X:=X).
      eapply typing_type_lc. apply Hbody; assumption. }
    change (sat (fun v => match v with
      | tm_tabs b => forall V C, locally_closed_ty V -> good C ->
          interp B [C] free (open_tm_ty b V)
      | _ => False end) (realize sigma theta (tm_tabs body))).
    apply sat_value.
    + unfold realize; simpl. apply v_tabs.
      change (locally_closed_tm (realize sigma theta (tm_tabs body))).
      apply realize_lc; auto. unfold locally_closed_tm.
      apply lc_tm_tabs. eapply lc_tm_ty_open_inv_rec with (X:=X).
      eapply typing_lc. apply Hbody; assumption.
    + unfold realize; simpl. intros V C HV HC.
      assert (Hsigma' : forall Y, locally_closed_ty (put_ty sigma X V Y)).
      { intro Y; unfold put_ty; destruct (Nat.eqb X Y); auto. }
      assert (Hfree' : forall Y, good (put_rel free X C Y)).
      { intro Y; unfold put_rel; destruct (Nat.eqb X Y); auto. }
      assert (Hgamma' : forall y D,
        lookup_context y Gamma = Some D ->
        interp D [] (put_rel free X C) (theta y)).
      { intros y D Hlook'.
        assert (Heq : interp D [] free (theta y) <->
          interp D [] (put_rel free X C) (theta y)).
        { apply interp_free_ext. intros Y HY z. unfold put_rel.
          assert (Hneq : X <> Y).
          { intro E; subst. apply HfG.
            eapply lookup_ftv_context; eauto. }
          apply Nat.eqb_neq in Hneq. rewrite Hneq. tauto. }
        apply (proj1 Heq). apply Hgamma; assumption. }
      specialize (IH X HX (put_ty sigma X V) (put_rel free X C)
        theta Hsigma' Hfree' Htheta Hgamma').
      apply (proj1 (interp_fvar_open B X C free _ HlcB HfB)) in IH.
      unfold realize in IH at 1.
      unfold open_tm_ty in IH |- *.
      rewrite map_tm_ty_open_rec in IH; auto.
      rewrite map_tm_open_tm_ty_rec in IH; auto.
  - change (interp (open_ty B U) [] free
      (tm_tapp (realize sigma theta f) (map_ty sigma U))).
    apply tapp_compat.
    + apply interp_good; auto.
    + apply map_ty_lc; auto. eapply wf_ty_lc; eauto.
    + eapply sat_map with (P:=fun v => match v with
        | tm_tabs b => forall V C, locally_closed_ty V -> good C ->
            interp B [C] free (open_tm_ty b V)
        | _ => False end).
      * intros v Hv HP. destruct v; simpl in *;
          try (inversion Hv); try contradiction.
        assert (HlcB : lc_ty_at 1 B).
        { pose proof (typing_type_lc _ _ _ _ Hf) as Htype.
          inversion Htype; subst; assumption. }
        pose proof (interp_open B U free
          (open_tm_ty v (map_ty sigma U)) HlcB
          (wf_ty_lc Delta U HU)) as Heq.
        apply (proj2 Heq).
        apply HP with (V:=map_ty sigma U) (C:=interp U [] free).
        -- apply map_ty_lc; auto. eapply wf_ty_lc; eauto.
        -- apply interp_good; auto.
      * apply IHf; auto.
  - change (sat (fun v => v = tm_true \/ v = tm_false) tm_true).
    apply sat_value; auto using v_true.
  - change (sat (fun v => v = tm_true \/ v = tm_false) tm_false).
    apply sat_value; auto using v_false.
  - change (interp T [] free (tm_if (realize sigma theta g)
      (realize sigma theta t) (realize sigma theta e))).
    apply if_compat.
    + apply interp_good; auto.
    + exact (IHg sigma free theta Hsigma Hfree Htheta Hgamma).
    + exact (IHt sigma free theta Hsigma Hfree Htheta Hgamma).
    + exact (IHe sigma free theta Hsigma Hfree Htheta Hgamma).
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  pose (free := fun _ : atom => base_candidate).
  assert (Hfree : forall X, good (free X)).
  { intro X; apply good_base. }
  pose proof (fundamental [] empty t T Hty
    (fun X => Ty_FVar X) free (fun x => tm_fvar x)
    (fun X => lc_ty_fvar 0 X) Hfree
    (fun x => lc_tm_fvar 0 0 x)) as Hred.
  assert (Hempty : forall x A, lookup_context x empty = Some A ->
    interp A [] free (tm_fvar x)).
  { intros x A H; discriminate. }
  specialize (Hred Hempty).
  rewrite realize_id in Hred.
  exact (proj2 ((proj1 (interp_good T [] free
    (Forall_nil _) Hfree)) t Hred)).
Qed.

End SystemFNormalizationIfHardTask.
