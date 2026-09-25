(** System F CBV strong-normalization benchmark, Medium variant.
    Features: if. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfMediumTask.

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

Definition type_substitution := atom -> ty.

Definition term_substitution := atom -> tm.

Fixpoint instantiate_ty (theta : type_substitution) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (instantiate_ty theta T1) (instantiate_ty theta T2)
  | Ty_All T1 => Ty_All (instantiate_ty theta T1)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint instantiate
    (theta : type_substitution) (gamma : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs T t1 => tm_abs (instantiate_ty theta T) (instantiate theta gamma t1)
  | tm_app t1 t2 => tm_app (instantiate theta gamma t1) (instantiate theta gamma t2)
  | tm_tabs t1 => tm_tabs (instantiate theta gamma t1)
  | tm_tapp t1 T => tm_tapp (instantiate theta gamma t1) (instantiate_ty theta T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (instantiate theta gamma t1) (instantiate theta gamma t2) (instantiate theta gamma t3)
  end.

Definition type_substitution_closed (theta : type_substitution) : Prop :=
  forall X : atom, locally_closed_ty (theta X).

Definition term_substitution_closed (gamma : term_substitution) : Prop :=
  forall x : atom, locally_closed_tm (gamma x).

Definition relation := tm -> Prop.
Record value_candidate := {
  candidate_relation : relation;
  candidate_values : forall v, candidate_relation v -> value v
}.
Definition relation_env := atom -> option value_candidate.
Definition relation_update (rho : relation_env) (X : atom) (a : value_candidate) :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

Definition expression_lifting (R : relation) (t : tm) : Prop :=
  locally_closed_tm t /\ strongly_normalizing t /\
  forall v, t -->* v -> value v -> R v.

Fixpoint value_relation (eta : list value_candidate) (rho : relation_env)
    (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error eta i with Some a => a.(candidate_relation) v | None => False end
  | Ty_FVar X =>
      match rho X with Some a => a.(candidate_relation) v | None => False end
  | Ty_Arrow T1 T2 =>
      value v /\ exists U body, v = tm_abs U body /\
      forall arg, value_relation eta rho T1 arg ->
        expression_lifting (value_relation eta rho T2) (open_tm body arg)
  | Ty_All T =>
      value v /\ exists body, v = tm_tabs body /\
      forall (U : ty) (a : value_candidate), locally_closed_ty U ->
        expression_lifting (value_relation (a :: eta) rho T) (open_tm_ty body U)
  | Ty_Bool => value v /\ (v = tm_true \/ v = tm_false)
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

Lemma lc_ty_weaken : forall K J T,
  K <= J -> lc_ty_at K T -> lc_ty_at J T.
Proof.
  intros K J T Hle Hlc. revert J Hle.
  induction Hlc; intros J Hle.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHHlc. lia.
  - apply lc_ty_bool.
Qed.

Lemma lc_tm_weaken : forall K k J j t,
  K <= J -> k <= j -> lc_tm_at K k t -> lc_tm_at J j t.
Proof.
  intros K k J j t HK Hk Hlc. revert J j HK Hk.
  induction Hlc; intros J j HK Hk.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; eauto using lc_ty_weaken. apply IHHlc; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs. apply IHHlc; lia.
  - apply lc_tm_tapp; eauto using lc_ty_weaken.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; eauto.
Qed.

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; subst; auto; unfold locally_closed_tm; constructor. Qed.

Lemma value_no_step : forall v u, value v -> ~ v --> u.
Proof. intros v u Hv Hs; inversion Hv; subst; inversion Hs. Qed.

Lemma step_deterministic : forall t u v, t --> u -> t --> v -> u = v.
Proof.
  intros t u v H. revert v.
  induction H; intros w Hw; inversion Hw; subst; try reflexivity;
    try solve [match goal with
      | Hv : value ?v, Hs : step ?v ?u |- _ =>
          exfalso; exact (value_no_step v u Hv Hs)
      end];
    try solve [exfalso; eapply value_no_step; [econstructor; eauto|eauto]];
    try solve [f_equal; eauto].
Qed.

Lemma sn_step_back : forall t u,
  t --> u -> strongly_normalizing u -> strongly_normalizing t.
Proof.
  intros t u Hstep Hsn. constructor. intros v Hv.
  rewrite <- (step_deterministic _ _ _ Hstep Hv). exact Hsn.
Qed.

Lemma multi_step_forward : forall t u v,
  t --> u -> t -->* v -> u -->* v \/ t = v.
Proof.
  intros t u v Hstep Hmulti. inversion Hmulti; subst; auto.
  left. assert (u = y) by (eapply step_deterministic; eauto).
  subst; assumption.
Qed.

Lemma expression_step_back : forall R t u,
  locally_closed_tm t -> t --> u -> expression_lifting R u ->
  expression_lifting R t.
Proof.
  intros R t u Hlc Hstep [HlcU [Hsn HR]].
  split; [exact Hlc|]. split.
  - eapply sn_step_back; eauto.
  - intros v Hmulti Hv. destruct (multi_step_forward _ _ _ Hstep Hmulti)
      as [Htail|Heq].
    + eapply HR; eauto.
    + subst. exfalso. eapply value_no_step; eauto.
Qed.

Lemma expression_value : forall R v,
  expression_lifting R v -> value v -> R v.
Proof.
  intros R v [_ [_ HR]] Hv. eapply HR; eauto using multi_refl.
Qed.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => [] | tm_fvar x => [x]
  | tm_abs _ t => fv_tm t
  | tm_app t u => fv_tm t ++ fv_tm u
  | tm_tabs t => fv_tm t
  | tm_tapp t _ => fv_tm t
  | tm_true | tm_false => []
  | tm_if t u v => fv_tm t ++ fv_tm u ++ fv_tm v
  end.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => [] | Ty_FVar X => [X]
  | Ty_Arrow T U => fv_ty T ++ fv_ty U
  | Ty_All T => fv_ty T
  | Ty_Bool => []
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t => fv_ty T ++ ftv_tm t
  | tm_app t u => ftv_tm t ++ ftv_tm u
  | tm_tabs t => ftv_tm t
  | tm_tapp t T => ftv_tm t ++ fv_ty T
  | tm_true | tm_false => []
  | tm_if t u v => ftv_tm t ++ ftv_tm u ++ ftv_tm v
  end.

Lemma lc_tm_open_inverse : forall K k t x,
  ~ In x (fv_tm t) ->
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t. revert K k.
  induction t; intros K k x Hfresh Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar. lia.
    + inversion Hlc; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs; auto.
    apply IHt with (x:=x); auto.
  - inversion Hlc; subst. apply lc_tm_app.
    + apply IHt1 with (x:=x); auto. intro H; apply Hfresh; apply in_or_app; auto.
    + apply IHt2 with (x:=x); auto. intro H; apply Hfresh; apply in_or_app; auto.
  - inversion Hlc; subst. apply lc_tm_tabs.
    apply IHt with (x:=x); auto.
  - inversion Hlc; subst. apply lc_tm_tapp; auto.
    apply IHt with (x:=x); auto.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - inversion Hlc; subst. apply lc_tm_if.
    + apply IHt1 with (x:=x); auto.
      intro H; apply Hfresh; apply in_or_app; left; exact H.
    + apply IHt2 with (x:=x); auto.
      intro H; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact H.
    + apply IHt3 with (x:=x); auto.
      intro H; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact H.
Qed.

Lemma lc_ty_open_inverse : forall K T X,
  ~ In X (fv_ty T) ->
  lc_ty_at K (open_ty_rec K (Ty_FVar X) T) ->
  lc_ty_at (S K) T.
Proof.
  intros K T. revert K.
  induction T; intros K X Hfresh Hlc; simpl in *.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + inversion Hlc; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion Hlc; subst. apply lc_ty_arrow.
    + apply IHT1 with (X:=X); auto.
      intro H; apply Hfresh; apply in_or_app; auto.
    + apply IHT2 with (X:=X); auto.
      intro H; apply Hfresh; apply in_or_app; auto.
  - inversion Hlc; subst. apply lc_ty_all.
    apply IHT with (X:=X); auto.
  - apply lc_ty_bool.
Qed.

Lemma lc_tm_ty_open_inverse : forall K k t X,
  ~ In X (ftv_tm t) ->
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  intros K k t. revert K k.
  induction t; intros K k X Hfresh Hlc; simpl in *.
  - inversion Hlc; subst. apply lc_tm_bvar; auto.
  - apply lc_tm_fvar.
  - inversion Hlc; subst. apply lc_tm_abs.
    + apply lc_ty_open_inverse with (X:=X); auto.
      intro H; apply Hfresh; apply in_or_app; auto.
    + apply IHt with (X:=X); auto.
      intro H; apply Hfresh; apply in_or_app; auto.
  - inversion Hlc; subst. apply lc_tm_app.
    + apply IHt1 with (X:=X); auto.
      intro H; apply Hfresh; apply in_or_app; auto.
    + apply IHt2 with (X:=X); auto.
      intro H; apply Hfresh; apply in_or_app; auto.
  - inversion Hlc; subst. apply lc_tm_tabs.
    apply IHt with (X:=X); auto.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + apply IHt with (X:=X); auto.
      intro H; apply Hfresh; apply in_or_app; auto.
    + apply lc_ty_open_inverse with (X:=X); auto.
      intro H; apply Hfresh; apply in_or_app; auto.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - inversion Hlc; subst. apply lc_tm_if.
    + apply IHt1 with (X:=X); auto.
      intro H; apply Hfresh; apply in_or_app; left; exact H.
    + apply IHt2 with (X:=X); auto.
      intro H; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact H.
    + apply IHt3 with (X:=X); auto.
      intro H; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact H.
Qed.

Definition fresh (xs : list atom) : atom := S (fold_right Nat.max 0 xs).

Lemma in_fold_max : forall xs x,
  In x xs -> x <= fold_right Nat.max 0 xs.
Proof.
  induction xs as [|y xs IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [H|H]; subst; [lia|].
    specialize (IH _ H). lia.
Qed.

Lemma fresh_not_in : forall xs, ~ In (fresh xs) xs.
Proof.
  intros xs H. unfold fresh in H.
  apply in_fold_max in H. lia.
Qed.

Lemma wf_ty_regular : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf. induction Hwf.
  - constructor.
  - constructor; auto.
  - set (X := fresh (L ++ fv_ty T)).
    assert (HX : ~ In X (L ++ fv_ty T)) by (apply fresh_not_in).
    apply lc_ty_all. apply lc_ty_open_inverse with (X:=X).
    + intro Hin. apply HX. apply in_or_app. right; exact Hin.
    + apply H0. intro Hin. apply HX. apply in_or_app. left; exact Hin.
  - constructor.
Qed.

Lemma typing_regular : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - constructor.
  - unfold locally_closed_tm. apply lc_tm_abs.
    + apply wf_ty_regular in H. exact H.
    + set (x := fresh (L ++ fv_tm t2)).
      assert (Hx : ~ In x (L ++ fv_tm t2)) by apply fresh_not_in.
      apply lc_tm_open_inverse with (x:=x).
      * intro Hin. apply Hx. apply in_or_app. right; exact Hin.
      * apply H1. intro Hin. apply Hx. apply in_or_app. left; exact Hin.
  - constructor; auto.
  - unfold locally_closed_tm. apply lc_tm_tabs.
    set (X := fresh (L ++ ftv_tm t)).
    assert (HX : ~ In X (L ++ ftv_tm t)) by apply fresh_not_in.
    apply lc_tm_ty_open_inverse with (X:=X).
    + intro Hin. apply HX. apply in_or_app. right; exact Hin.
    + apply H0. intro Hin. apply HX. apply in_or_app. left; exact Hin.
  - apply lc_tm_tapp; [exact IHHty|].
    apply wf_ty_regular in H. exact H.
  - constructor.
  - constructor.
  - constructor; auto.
Qed.

Definition theta_update (theta : type_substitution) (X : atom) (U : ty) :=
  fun Y => if Nat.eqb X Y then U else theta Y.
Definition gamma_update (gamma : term_substitution) (x : atom) (v : tm) :=
  fun y => if Nat.eqb x y then v else gamma y.

Lemma open_ty_above : forall T K k U,
  lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  induction T; intros K k U Hlc Hle; simpl; inversion Hlc; subst; try reflexivity.
  - assert (k <> n) by lia. apply Nat.eqb_neq in H. rewrite H. reflexivity.
  - f_equal; eauto.
  - f_equal. apply IHT with (K:=S K); auto; lia.
Qed.

Lemma open_ty_closed : forall T k U,
  locally_closed_ty T -> open_ty_rec k U T = T.
Proof. intros; eapply open_ty_above; eauto; lia. Qed.

Lemma open_tm_above : forall t K k j u,
  lc_tm_at K k t -> k <= j -> open_tm_rec j u t = t.
Proof.
  induction t; intros K k j u Hlc Hle; simpl; inversion Hlc; subst; try reflexivity.
  - assert (j <> n) by lia. apply Nat.eqb_neq in H. rewrite H. reflexivity.
  - f_equal. apply IHt with (K:=K) (k:=S k); auto; lia.
  - f_equal; eauto.
  - f_equal. apply IHt with (K:=S K) (k:=k); auto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma open_tm_closed : forall t k u,
  locally_closed_tm t -> open_tm_rec k u t = t.
Proof. intros; eapply open_tm_above; eauto; lia. Qed.

Lemma open_tm_ty_above : forall t K k j U,
  lc_tm_at K k t -> K <= j -> open_tm_ty_rec j U t = t.
Proof.
  induction t; intros K k j U Hlc Hle; simpl; inversion Hlc; subst; try reflexivity.
  - f_equal.
    + eapply open_ty_above; eauto.
    + apply IHt with (K:=K) (k:=S k); auto.
  - f_equal; eauto.
  - f_equal. apply IHt with (K:=S K) (k:=k); auto; lia.
  - f_equal; eauto using open_ty_above.
  - f_equal; eauto.
Qed.

Lemma open_tm_ty_closed : forall t k U,
  locally_closed_tm t -> open_tm_ty_rec k U t = t.
Proof. intros; eapply open_tm_ty_above; eauto; lia. Qed.

Lemma instantiate_open_tm : forall t k x theta gamma v,
  ~ In x (fv_tm t) ->
  term_substitution_closed gamma ->
  instantiate theta (gamma_update gamma x v)
    (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (instantiate theta gamma t).
Proof.
  induction t; intros k x theta gamma v Hfresh Hgamma; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n); simpl; auto.
    unfold gamma_update. rewrite Nat.eqb_refl. reflexivity.
  - unfold gamma_update. assert (x <> a) by (intro H; subst; apply Hfresh; auto).
    apply Nat.eqb_neq in H. rewrite H.
    symmetry. apply open_tm_closed. apply Hgamma.
  - f_equal. apply IHt; auto.
  - f_equal; [apply IHt1|apply IHt2];
      [intro H; apply Hfresh; apply in_or_app; auto|exact Hgamma|
       intro H; apply Hfresh; apply in_or_app; auto|exact Hgamma].
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
  - f_equal.
    + apply IHt1; [|exact Hgamma].
      intro H; apply Hfresh; apply in_or_app; left; exact H.
    + apply IHt2; [|exact Hgamma].
      intro H; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact H.
    + apply IHt3; [|exact Hgamma].
      intro H; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact H.
Qed.

Lemma instantiate_ty_open : forall T k X theta U,
  ~ In X (fv_ty T) ->
  type_substitution_closed theta ->
  instantiate_ty (theta_update theta X U)
    (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (instantiate_ty theta T).
Proof.
  induction T; intros k X theta U Hfresh Htheta; simpl in *; try reflexivity.
  - destruct (Nat.eqb k n); simpl; auto.
    unfold theta_update. rewrite Nat.eqb_refl. reflexivity.
  - unfold theta_update. assert (X <> a) by (intro H; subst; apply Hfresh; auto).
    apply Nat.eqb_neq in H. rewrite H.
    symmetry. apply open_ty_closed. apply Htheta.
  - f_equal; [apply IHT1|apply IHT2];
      [intro H; apply Hfresh; apply in_or_app; auto|exact Htheta|
       intro H; apply Hfresh; apply in_or_app; auto|exact Htheta].
  - f_equal. apply IHT; auto.
Qed.

Lemma instantiate_open_tm_ty : forall t k X theta gamma U,
  ~ In X (ftv_tm t) ->
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  instantiate (theta_update theta X U) gamma
    (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  induction t; intros k X theta gamma U Hfresh Htheta Hgamma; simpl in *; try reflexivity.
  - symmetry. apply open_tm_ty_closed. apply Hgamma.
  - f_equal.
    + apply instantiate_ty_open; [|exact Htheta].
      intro H; apply Hfresh; apply in_or_app; auto.
    + apply IHt; [|exact Htheta|exact Hgamma].
      intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal; [apply IHt1|apply IHt2];
      [intro H; apply Hfresh; apply in_or_app; auto|exact Htheta|exact Hgamma|
       intro H; apply Hfresh; apply in_or_app; auto|exact Htheta|exact Hgamma].
  - f_equal. apply IHt; auto.
  - f_equal.
    + apply IHt; [|exact Htheta|exact Hgamma].
      intro H; apply Hfresh; apply in_or_app; auto.
    + apply instantiate_ty_open; [|exact Htheta].
      intro H; apply Hfresh; apply in_or_app; auto.
  - f_equal.
    + apply IHt1; [|exact Htheta|exact Hgamma].
      intro H; apply Hfresh; apply in_or_app; left; exact H.
    + apply IHt2; [|exact Htheta|exact Hgamma].
      intro H; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact H.
    + apply IHt3; [|exact Htheta|exact Hgamma].
      intro H; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact H.
Qed.

Lemma expression_lifting_ext : forall R S t,
  (forall v, R v <-> S v) ->
  expression_lifting R t <-> expression_lifting S t.
Proof.
  intros R S t H. unfold expression_lifting. firstorder.
Qed.

Lemma value_relation_value : forall eta rho T v,
  value_relation eta rho T v -> value v.
Proof.
  intros eta rho T. induction T; intros v H; simpl in H.
  - destruct (nth_error eta n) as [a|]; [eapply candidate_values; eauto|contradiction].
  - destruct (rho a) as [b|]; [eapply candidate_values; eauto|contradiction].
  - exact (proj1 H).
  - exact (proj1 H).
  - exact (proj1 H).
Qed.

Definition type_candidate (rho : relation_env) (U : ty) : value_candidate :=
  {| candidate_relation := value_relation [] rho U;
     candidate_values := value_relation_value [] rho U |}.

Lemma nth_error_app_left : forall (A : Type) (xs ys : list A) i,
  i < length xs -> nth_error (xs ++ ys) i = nth_error xs i.
Proof.
  intros A xs. induction xs as [|x xs IH]; intros ys i H; simpl in *; [lia|].
  destruct i; simpl; auto. apply IH. lia.
Qed.

Lemma value_relation_eta_extension : forall T n eta extra rho v,
  lc_ty_at n T -> length eta = n ->
  value_relation (eta ++ extra) rho T v <-> value_relation eta rho T v.
Proof.
  induction T; intros n0 eta extra rho v Hlc Hlen; simpl in *;
    inversion Hlc; subst; try tauto.
  - rewrite nth_error_app_left by lia. tauto.
  - assert (HD : forall w, value_relation (eta ++ extra) rho T1 w <->
        value_relation eta rho T1 w) by
        (intro w; eapply IHT1; eauto).
    assert (HC : forall w, value_relation (eta ++ extra) rho T2 w <->
        value_relation eta rho T2 w) by
        (intro w; eapply IHT2; eauto).
    split.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg. apply (proj1 (expression_lifting_ext _ _ _ HC)).
      apply Hbody. apply (proj2 (HD arg)); exact Harg.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg. apply (proj2 (expression_lifting_ext _ _ _ HC)).
      apply Hbody. apply (proj1 (HD arg)); exact Harg.
  - assert (HC : forall a w,
        value_relation (a :: eta ++ extra) rho T w <->
        value_relation (a :: eta) rho T w).
    { intros a w. change (value_relation ((a :: eta) ++ extra) rho T w <->
        value_relation (a :: eta) rho T w).
      eapply IHT; eauto. }
    split.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U a HU. apply (proj1 (expression_lifting_ext _ _ _ (HC a))).
      apply Hbody; exact HU.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U a HU. apply (proj2 (expression_lifting_ext _ _ _ (HC a))).
      apply Hbody; exact HU.
Qed.

Lemma nth_error_app_last : forall (A : Type) (xs : list A) a,
  nth_error (xs ++ [a]) (length xs) = Some a.
Proof.
  intros A xs. induction xs as [|x xs IH]; intros a; simpl; auto.
Qed.

Lemma value_relation_open : forall T k eta rho rho' Q a v,
  length eta = k -> lc_ty_at (S k) T ->
  (forall Y, In Y (fv_ty T) -> rho' Y = rho Y) ->
  (forall xi w, value_relation xi rho' Q w <-> candidate_relation a w) ->
  value_relation eta rho' (open_ty_rec k Q T) v <->
  value_relation (eta ++ [a]) rho T v.
Proof.
  induction T; intros k eta rho rho' Q c v Hlen Hlc Henv HQ;
    simpl in *; inversion Hlc; subst; try tauto.
  - destruct (Nat.eqb (length eta) n) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      rewrite nth_error_app_last. apply HQ.
    + apply Nat.eqb_neq in E. assert (n < length eta) by lia.
      rewrite nth_error_app_left by lia. tauto.
  - rewrite Henv by (simpl; auto). tauto.
  - assert (HD : forall w,
        value_relation eta rho' (open_ty_rec (length eta) Q T1) w <->
        value_relation (eta ++ [c]) rho T1 w).
    { intro w. eapply IHT1; eauto.
      intros Y HY. apply Henv. apply in_or_app; auto. }
    assert (HC : forall w,
        value_relation eta rho' (open_ty_rec (length eta) Q T2) w <->
        value_relation (eta ++ [c]) rho T2 w).
    { intro w. eapply IHT2; eauto.
      intros Y HY. apply Henv. apply in_or_app; auto. }
    split.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg. apply (proj1 (expression_lifting_ext _ _ _ HC)).
      apply Hbody. apply (proj2 (HD arg)); exact Harg.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg. apply (proj2 (expression_lifting_ext _ _ _ HC)).
      apply Hbody. apply (proj1 (HD arg)); exact Harg.
  - assert (HC : forall b w,
        value_relation (b :: eta) rho' (open_ty_rec (S (length eta)) Q T) w <->
        value_relation (b :: eta ++ [c]) rho T w).
    { intros b w. change (value_relation ((b :: eta) ++ [c]) rho T w)
        with (value_relation (b :: eta ++ [c]) rho T w).
      apply (IHT (S (length eta)) (b :: eta) rho rho' Q c w);
        auto; simpl; lia. }
    split.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U b HU. apply (proj1 (expression_lifting_ext _ _ _ (HC b))).
      apply Hbody; exact HU.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U b HU. apply (proj2 (expression_lifting_ext _ _ _ (HC b))).
      apply Hbody; exact HU.
Qed.

Lemma value_relation_open_var : forall T rho X a v,
  lc_ty_at 1 T -> ~ In X (fv_ty T) ->
  value_relation [] (relation_update rho X a)
    (open_ty T (Ty_FVar X)) v <->
  value_relation [a] rho T v.
Proof.
  intros T rho X a v Hlc Hfresh.
  eapply (value_relation_open T 0 [] rho (relation_update rho X a)
    (Ty_FVar X) a v); simpl; auto.
  - intros Y HY. unfold relation_update.
    assert (X <> Y) by (intro Heq; subst; contradiction).
    apply Nat.eqb_neq in H. rewrite H. reflexivity.
  - intros xi w. simpl. unfold relation_update.
    rewrite Nat.eqb_refl. tauto.
Qed.

Lemma value_relation_open_type : forall T rho U v,
  lc_ty_at 1 T -> locally_closed_ty U ->
  value_relation [] rho (open_ty T U) v <->
  value_relation [type_candidate rho U] rho T v.
Proof.
  intros T rho U v Hlc HU.
  eapply (value_relation_open T 0 [] rho rho U (type_candidate rho U) v);
    simpl; auto.
  intros xi w. simpl.
  exact (value_relation_eta_extension U 0 [] xi rho w HU eq_refl).
Qed.

Lemma instantiate_ty_lc : forall theta K T,
  type_substitution_closed theta -> lc_ty_at K T ->
  lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta K T Htheta Hlc. induction Hlc; simpl; try constructor; auto.
  - eapply lc_ty_weaken with (K:=0); [lia|apply Htheta].
Qed.

Lemma instantiate_lc : forall theta gamma K k t,
  type_substitution_closed theta -> term_substitution_closed gamma ->
  lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Htheta Hgamma Hlc.
  induction Hlc; simpl; try constructor; eauto using instantiate_ty_lc.
  - eapply lc_tm_weaken with (K:=0) (k:=0); [lia|lia|apply Hgamma].
Qed.

Lemma theta_update_closed : forall theta X U,
  type_substitution_closed theta -> locally_closed_ty U ->
  type_substitution_closed (theta_update theta X U).
Proof.
  intros theta X U Htheta HU Y. unfold theta_update.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma gamma_update_closed : forall gamma x v,
  term_substitution_closed gamma -> locally_closed_tm v ->
  term_substitution_closed (gamma_update gamma x v).
Proof.
  intros gamma x v Hgamma Hv y. unfold gamma_update.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma open_ty_lc : forall T K U,
  lc_ty_at (S K) T -> lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  induction T; intros K U Hlc HU; simpl; inversion Hlc; subst;
    try constructor; eauto.
  - destruct (Nat.eqb K n) eqn:E.
    + exact HU.
    + apply Nat.eqb_neq in E. apply lc_ty_bvar. lia.
  - apply IHT.
    + assumption.
    + eapply lc_ty_weaken with (K:=K); eauto; lia.
Qed.

Lemma typing_result_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T Hty. induction Hty.
  - eapply wf_ty_regular; eauto.
  - apply lc_ty_arrow.
    + eapply wf_ty_regular; eauto.
    + set (x := fresh L). assert (Hx : ~ In x L) by apply fresh_not_in.
      exact (H1 x Hx).
  - inversion IHHty1; subst; assumption.
  - apply lc_ty_all.
    set (X := fresh (L ++ fv_ty T)).
    assert (HX : ~ In X (L ++ fv_ty T)) by apply fresh_not_in.
    apply lc_ty_open_inverse with (X:=X).
    + intro Hin. apply HX. apply in_or_app; right; exact Hin.
    + apply H0. intro Hin. apply HX. apply in_or_app; left; exact Hin.
  - inversion IHHty; subst.
    eapply open_ty_lc; [exact H2|eapply wf_ty_regular; exact H].
  - constructor.
  - constructor.
  - exact IHHty2.
Qed.

Definition evaluation_lifting (R : relation) (t : tm) : Prop :=
  strongly_normalizing t /\
  forall v, t -->* v -> value v -> R v.

Lemma expression_evaluation : forall R t,
  expression_lifting R t -> evaluation_lifting R t.
Proof. intros R t [_ H]; exact H. Qed.

Lemma evaluation_value : forall R v,
  evaluation_lifting R v -> value v -> R v.
Proof.
  intros R v [_ H] Hv. apply (H v); auto using multi_refl.
Qed.

Lemma evaluation_intro : forall R t,
  ~ value t ->
  (forall u, t --> u -> evaluation_lifting R u) ->
  evaluation_lifting R t.
Proof.
  intros R t Hnv Hred. split.
  - constructor. intros u Hu. apply (Hred u Hu).
  - intros v Hmulti Hv. inversion Hmulti; subst.
    + contradiction.
    + destruct (Hred y H) as [_ HR]. apply (HR v); auto.
Qed.

Lemma evaluation_app : forall eta rho T1 T2 f a,
  evaluation_lifting (value_relation eta rho (Ty_Arrow T1 T2)) f ->
  evaluation_lifting (value_relation eta rho T1) a ->
  evaluation_lifting (value_relation eta rho T2) (tm_app f a).
Proof.
  intros eta rho T1 T2 f a [Hsnf Hvalf] Ha.
  revert a Ha Hvalf.
  induction Hsnf as [f Hredf IHf]; intros a [Hsna Hvala] Hvalf.
  revert Hvala Hvalf.
  induction Hsna as [a Hreda IHa]; intros Hvala Hvalf.
  apply evaluation_intro.
  - intro Hv. inversion Hv.
  - intros u Hu. inversion Hu; subst.
    + assert (Hf : value_relation eta rho (Ty_Arrow T1 T2)
          (tm_abs T t)) by
          (apply (Hvalf (tm_abs T t)); auto using multi_refl).
      destruct Hf as [_ [U [body [Heq Hbody]]]].
      inversion Heq; subst.
      assert (Harg : value_relation eta rho T1 a) by
          (apply (Hvala a); auto using multi_refl).
      apply expression_evaluation. apply Hbody. exact Harg.
    + apply (IHf t1').
      * assumption.
      * split; [constructor; exact Hreda|exact Hvala].
      * intros v Hmulti Hv. apply (Hvalf v); auto.
        eapply multi_step; eauto.
    + apply IHa.
      * assumption.
      * intros v Hmulti Hv. apply (Hvala v); auto.
        eapply multi_step; eauto.
      * exact Hvalf.
Qed.

Lemma evaluation_tapp : forall rho T Usem Uterm f,
  lc_ty_at 1 T -> locally_closed_ty Usem -> locally_closed_ty Uterm ->
  evaluation_lifting (value_relation [] rho (Ty_All T)) f ->
  evaluation_lifting (value_relation [] rho (open_ty T Usem))
    (tm_tapp f Uterm).
Proof.
  intros rho T Usem Uterm f HT HUse HUt [Hsn Hval]. revert Hval.
  induction Hsn as [f Hred IH]; intros Hval.
  apply evaluation_intro.
  - intro Hv. inversion Hv.
  - intros u Hu. inversion Hu; subst.
    + assert (Hf : value_relation [] rho (Ty_All T) (tm_tabs t)) by
        (apply (Hval (tm_tabs t)); auto using multi_refl).
      destruct Hf as [_ [body [Heq Hbody]]]. inversion Heq; subst.
      specialize (Hbody Uterm (type_candidate rho Usem) HUt).
      apply expression_evaluation.
      apply (proj2 (expression_lifting_ext _ _ _
        (fun v => value_relation_open_type T rho Usem v HT HUse))).
      exact Hbody.
    + apply IH; [assumption|].
      intros v Hmulti Hv. apply (Hval v); auto.
      eapply multi_step; eauto.
Qed.

Lemma evaluation_if : forall rho R c t e,
  evaluation_lifting (value_relation [] rho Ty_Bool) c ->
  evaluation_lifting R t -> evaluation_lifting R e ->
  evaluation_lifting R (tm_if c t e).
Proof.
  intros rho R c t e [Hsn Hval] Ht He. revert Hval.
  induction Hsn as [c Hred IH]; intros Hval.
  apply evaluation_intro.
  - intro Hv. inversion Hv.
  - intros u Hu. inversion Hu; subst.
    + exact Ht.
    + exact He.
    + apply IH; [assumption|].
      intros v Hmulti Hv. apply (Hval v); auto.
      eapply multi_step; eauto.
Qed.

Fixpoint ftv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => fv_ty T ++ ftv_context Gamma'
  end.

Lemma lookup_context_ftv : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) ->
  In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlook Hin;
    simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst. apply in_or_app; auto.
  - apply in_or_app; right. eapply IH; eauto.
Qed.

Lemma value_relation_rho_ext : forall T eta rho sigma v,
  (forall X, In X (fv_ty T) -> rho X = sigma X) ->
  value_relation eta rho T v <-> value_relation eta sigma T v.
Proof.
  induction T; intros eta rho sigma v Henv; simpl in *; try tauto.
  - rewrite Henv by (simpl; auto). tauto.
  - assert (HD : forall w, value_relation eta rho T1 w <->
        value_relation eta sigma T1 w).
    { intro w. apply IHT1. intros X HX. apply Henv. apply in_or_app; auto. }
    assert (HC : forall w, value_relation eta rho T2 w <->
        value_relation eta sigma T2 w).
    { intro w. apply IHT2. intros X HX. apply Henv. apply in_or_app; auto. }
    split.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg. apply (proj1 (expression_lifting_ext _ _ _ HC)).
      apply Hbody. apply (proj2 (HD arg)); exact Harg.
    + intros [Hv [U [body [Heq Hbody]]]].
      split; [exact Hv|]. exists U, body. split; [exact Heq|].
      intros arg Harg. apply (proj2 (expression_lifting_ext _ _ _ HC)).
      apply Hbody. apply (proj1 (HD arg)); exact Harg.
  - assert (HC : forall a w, value_relation (a :: eta) rho T w <->
        value_relation (a :: eta) sigma T w).
    { intros a w. apply IHT. exact Henv. }
    split.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U a HU. apply (proj1 (expression_lifting_ext _ _ _ (HC a))).
      apply Hbody; exact HU.
    + intros [Hv [body [Heq Hbody]]].
      split; [exact Hv|]. exists body. split; [exact Heq|].
      intros U a HU. apply (proj2 (expression_lifting_ext _ _ _ (HC a))).
      apply Hbody; exact HU.
Qed.

Lemma expression_from_value : forall eta rho T v,
  value_relation eta rho T v ->
  expression_relation eta rho T v.
Proof.
  intros eta rho T v HR. unfold expression_relation, expression_lifting.
  pose proof (value_relation_value eta rho T v HR) as Hv.
  split; [apply value_closed; exact Hv|].
  split.
  - constructor. intros u Hu. exfalso. eapply value_no_step; eauto.
  - intros w Hmulti Hw. inversion Hmulti; subst; auto.
    exfalso. exact (value_no_step v y Hv H).
Qed.

Lemma instantiate_typing_closed : forall Delta Gamma t T theta gamma,
  has_type Delta Gamma t T ->
  type_substitution_closed theta -> term_substitution_closed gamma ->
  locally_closed_tm (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T theta gamma Hty Htheta Hgamma.
  eapply instantiate_lc; eauto.
  exact (typing_regular _ _ _ _ Hty).
Qed.

Lemma related_gamma_update : forall rho Gamma gamma x T v,
  related_substitution rho Gamma gamma ->
  value_relation [] rho T v ->
  related_substitution rho ((x, T) :: Gamma) (gamma_update gamma x v).
Proof.
  intros rho Gamma gamma x T v Hrel Hv y U Hlook.
  simpl in Hlook. unfold gamma_update.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst.
    rewrite Nat.eqb_refl. inversion Hlook; subst. exact Hv.
  - assert (Nat.eqb x y = false) as E' by
        (apply Nat.eqb_neq; apply Nat.eqb_neq in E; lia).
    rewrite E'. apply Hrel. exact Hlook.
Qed.

Lemma related_rho_update : forall rho Gamma gamma X a,
  ~ In X (ftv_context Gamma) ->
  related_substitution rho Gamma gamma ->
  related_substitution (relation_update rho X a) Gamma gamma.
Proof.
  intros rho Gamma gamma X a Hfresh Hrel x T Hlook.
  assert (Henv : forall Y, In Y (fv_ty T) ->
    rho Y = relation_update rho X a Y).
  { intros Y HY. unfold relation_update.
    assert (X <> Y) by
      (intro Heq; subst; apply Hfresh; eapply lookup_context_ftv; eauto).
    apply Nat.eqb_neq in H. rewrite H. reflexivity. }
  apply (proj1 (value_relation_rho_ext T [] rho
    (relation_update rho X a) (gamma x) Henv)).
  apply Hrel. exact Hlook.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta rho gamma,
  type_substitution_closed theta ->
  term_substitution_closed gamma ->
  related_substitution rho Gamma gamma ->
  expression_relation [] rho T (instantiate theta gamma t).
Proof.
  intros Delta Gamma t T Hty.
  pose proof (typing_regular _ _ _ _ Hty) as Hregular.
  pose proof (typing_result_lc _ _ _ _ Hty) as Htype.
  induction Hty; intros theta rho gamma Htheta Hgamma Hrelated; simpl in *.
  - apply expression_from_value. apply Hrelated; exact H.
  - apply expression_from_value. simpl. split.
    + apply v_abs.
      change (locally_closed_tm (instantiate theta gamma (tm_abs T1 t2))).
      eapply instantiate_lc; eauto.
    + exists (instantiate_ty theta T1), (instantiate theta gamma t2).
      split; [reflexivity|]. intros arg Harg.
      set (x := fresh (L ++ fv_tm t2)).
      assert (Hx : ~ In x (L ++ fv_tm t2)) by apply fresh_not_in.
      assert (HxL : ~ In x L).
      { intro Hin. apply Hx. apply in_or_app; left; exact Hin. }
      assert (Hxt : ~ In x (fv_tm t2)).
      { intro Hin. apply Hx. apply in_or_app; right; exact Hin. }
      pose proof (H0 x HxL) as Htyped.
      pose proof (H1 x HxL
        (typing_regular _ _ _ _ Htyped)
        (typing_result_lc _ _ _ _ Htyped)
        theta rho (gamma_update gamma x arg)
        Htheta
        (gamma_update_closed gamma x arg Hgamma
          (value_closed _ (value_relation_value _ _ _ _ Harg)))
        (related_gamma_update rho Gamma gamma x T1 arg Hrelated Harg))
        as Hbody.
      unfold open_tm in Hbody.
      rewrite instantiate_open_tm in Hbody; auto.
  - unfold expression_relation. split.
    + change (locally_closed_tm (instantiate theta gamma (tm_app t1 t2))).
      eapply instantiate_lc; eauto.
    + eapply evaluation_app.
      * apply expression_evaluation. eapply IHHty1; eauto using typing_regular, typing_result_lc.
      * apply expression_evaluation. eapply IHHty2; eauto using typing_regular, typing_result_lc.
  - apply expression_from_value. simpl. split.
    + apply v_tabs.
      change (locally_closed_tm (instantiate theta gamma (tm_tabs t))).
      eapply instantiate_lc; eauto.
    + exists (instantiate theta gamma t). split; [reflexivity|].
      intros U a HU.
      set (X := fresh (L ++ ftv_tm t ++ fv_ty T ++ ftv_context Gamma)).
      assert (HX : ~ In X (L ++ ftv_tm t ++ fv_ty T ++ ftv_context Gamma))
        by apply fresh_not_in.
      assert (HXL : ~ In X L).
      { intro Hin. apply HX. apply in_or_app; left; exact Hin. }
      assert (HXt : ~ In X (ftv_tm t)).
      { intro Hin. apply HX. apply in_or_app; right.
        apply in_or_app; left; exact Hin. }
      assert (HXT : ~ In X (fv_ty T)).
      { intro Hin. apply HX. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; left; exact Hin. }
      assert (HXG : ~ In X (ftv_context Gamma)).
      { intro Hin. apply HX. apply in_or_app; right.
        apply in_or_app; right. apply in_or_app; right; exact Hin. }
      pose proof (H X HXL) as Htyped.
      pose proof (H0 X HXL
        (typing_regular _ _ _ _ Htyped)
        (typing_result_lc _ _ _ _ Htyped)
        (theta_update theta X U) (relation_update rho X a) gamma
        (theta_update_closed theta X U Htheta HU)
        Hgamma (related_rho_update rho Gamma gamma X a HXG Hrelated))
        as Hbody.
      unfold open_tm_ty in Hbody.
      rewrite instantiate_open_tm_ty in Hbody; auto.
      assert (HT : lc_ty_at 1 T) by (inversion Htype; subst; assumption).
      apply (proj1 (expression_lifting_ext _ _ _
        (fun v => value_relation_open_var T rho X a v HT HXT))) in Hbody.
      exact Hbody.
  - unfold expression_relation. split.
    + change (locally_closed_tm (instantiate theta gamma (tm_tapp t U))).
      eapply instantiate_lc; eauto.
    + eapply evaluation_tapp.
      * pose proof (typing_result_lc _ _ _ _ Hty) as HfT.
        inversion HfT; subst; assumption.
      * apply wf_ty_regular in H. exact H.
      * eapply instantiate_ty_lc; [exact Htheta|].
        apply wf_ty_regular in H. exact H.
      * apply expression_evaluation.
        eapply IHHty; eauto using typing_regular, typing_result_lc.
  - apply expression_from_value. simpl. split; [constructor|auto].
  - apply expression_from_value. simpl. split; [constructor|auto].
  - unfold expression_relation. split.
    + change (locally_closed_tm (instantiate theta gamma (tm_if t1 t2 t3))).
      eapply instantiate_lc; eauto.
    + eapply evaluation_if.
      * apply expression_evaluation. eapply IHHty1; eauto using typing_regular, typing_result_lc.
      * apply expression_evaluation. eapply IHHty2; eauto using typing_regular, typing_result_lc.
      * apply expression_evaluation. eapply IHHty3; eauto using typing_regular, typing_result_lc.
Qed.

Lemma instantiate_ty_identity : forall T,
  instantiate_ty Ty_FVar T = T.
Proof. induction T; simpl; f_equal; auto. Qed.

Lemma instantiate_identity : forall t,
  instantiate Ty_FVar tm_fvar t = t.
Proof.
  induction t; simpl; f_equal; auto using instantiate_ty_identity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof (fundamental [] empty t T Hty Ty_FVar
    (fun _ => None) tm_fvar) as Hfund.
  assert (Htheta : type_substitution_closed Ty_FVar).
  { intros X. constructor. }
  assert (Hgamma : term_substitution_closed tm_fvar).
  { intros x. constructor. }
  assert (Hrel : related_substitution (fun _ => None) empty tm_fvar).
  { intros x U Hlook. discriminate. }
  specialize (Hfund Htheta Hgamma Hrel).
  rewrite instantiate_identity in Hfund.
  exact (proj1 (proj2 Hfund)).
Qed.

End SystemFNormalizationIfMediumTask.
