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

(* ================================================================ *)
(* Auxiliary definitions and syntactic lemmas                       *)
(* ================================================================ *)

Definition fresh (l : list atom) : atom := S (fold_right Nat.max 0 l).

Lemma fold_max_upper : forall l x, In x l -> x <= fold_right Nat.max 0 l.
Proof.
  induction l as [| a l IH]; simpl; intros x Hx.
  - contradiction.
  - destruct Hx as [-> | Hx].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (fold_right Nat.max 0 l).
      * apply IH; exact Hx.
      * apply Nat.le_max_r.
Qed.

Lemma fresh_not_in : forall l, ~ In (fresh l) l.
Proof.
  intros l H. unfold fresh in H.
  pose proof (fold_max_upper l (S (fold_right Nat.max 0 l)) H). lia.
Qed.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T1 => fv_ty T1
  end.

(* Free *term variables* of a term (atoms in tm_fvar positions). *)
Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => fv_tm b
  | tm_app a b => fv_tm a ++ fv_tm b
  | tm_tabs b => fv_tm b
  | tm_tapp b _ => fv_tm b
  | tm_choice a b => fv_tm a ++ fv_tm b
  end.

(* Free *type variable* atoms of a term. *)
Fixpoint fv_tm_ty (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T b => fv_ty T ++ fv_tm_ty b
  | tm_app a b => fv_tm_ty a ++ fv_tm_ty b
  | tm_tabs b => fv_tm_ty b
  | tm_tapp b T => fv_tm_ty b ++ fv_ty T
  | tm_choice a b => fv_tm_ty a ++ fv_tm_ty b
  end.

Fixpoint fv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => fv_ty T ++ fv_context Gamma'
  end.

Fixpoint ty_subst_env (sigma : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sigma X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst_env sigma T1) (ty_subst_env sigma T2)
  | Ty_All T1 => Ty_All (ty_subst_env sigma T1)
  end.

Fixpoint tm_ty_subst_env (sigma : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (ty_subst_env sigma T) (tm_ty_subst_env sigma b)
  | tm_app a b => tm_app (tm_ty_subst_env sigma a) (tm_ty_subst_env sigma b)
  | tm_tabs b => tm_tabs (tm_ty_subst_env sigma b)
  | tm_tapp b T => tm_tapp (tm_ty_subst_env sigma b) (ty_subst_env sigma T)
  | tm_choice a b => tm_choice (tm_ty_subst_env sigma a) (tm_ty_subst_env sigma b)
  end.

Fixpoint tm_subst_env (gamma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs T b => tm_abs T (tm_subst_env gamma b)
  | tm_app a b => tm_app (tm_subst_env gamma a) (tm_subst_env gamma b)
  | tm_tabs b => tm_tabs (tm_subst_env gamma b)
  | tm_tapp b T => tm_tapp (tm_subst_env gamma b) T
  | tm_choice a b => tm_choice (tm_subst_env gamma a) (tm_subst_env gamma b)
  end.

Definition apply_env (sigma : atom -> ty) (gamma : atom -> tm) (t : tm) : tm :=
  tm_subst_env gamma (tm_ty_subst_env sigma t).

(* ---------------- Definitional equalities ---------------- *)

Lemma ty_subst_env_id : forall T,
  ty_subst_env (fun X => Ty_FVar X) T = T.
Proof.
  induction T; simpl; congruence.
Qed.

Lemma tm_ty_subst_env_id : forall t,
  tm_ty_subst_env (fun X => Ty_FVar X) t = t.
Proof.
  induction t; simpl; try rewrite ty_subst_env_id; congruence.
Qed.

Lemma tm_subst_env_id : forall t,
  tm_subst_env (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; congruence.
Qed.

Lemma apply_env_id : forall t,
  apply_env (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  intros. unfold apply_env. rewrite tm_ty_subst_env_id. apply tm_subst_env_id.
Qed.

(* ---------------- Free variables ---------------- *)

Lemma fv_tm_tm_ty_subst_env : forall sigma t,
  fv_tm (tm_ty_subst_env sigma t) = fv_tm t.
Proof.
  intros sigma t. induction t; simpl; try reflexivity; congruence.
Qed.

Lemma ty_subst_env_agree_fv : forall sigma1 sigma2 T,
  (forall X, In X (fv_ty T) -> sigma1 X = sigma2 X) ->
  ty_subst_env sigma1 T = ty_subst_env sigma2 T.
Proof.
  intros sigma1 sigma2 T. induction T; simpl; intros Hagree.
  - reflexivity.
  - apply Hagree. simpl. auto.
  - f_equal.
    + apply IHT1. intros X HX. apply Hagree. simpl. apply in_or_app. left. exact HX.
    + apply IHT2. intros X HX. apply Hagree. simpl. apply in_or_app. right. exact HX.
  - f_equal. apply IHT. intros X HX. apply Hagree. simpl. exact HX.
Qed.

Lemma tm_ty_subst_env_agree : forall sigma1 sigma2 t,
  (forall X, In X (fv_tm_ty t) -> sigma1 X = sigma2 X) ->
  tm_ty_subst_env sigma1 t = tm_ty_subst_env sigma2 t.
Proof.
  intros sigma1 sigma2 t. induction t; simpl; intros Hagree.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply ty_subst_env_agree_fv. intros X HX. apply Hagree. simpl. apply in_or_app. left. exact HX.
    + apply IHt. intros X HX. apply Hagree. simpl. apply in_or_app. right. exact HX.
  - f_equal; [apply IHt1 | apply IHt2]; intros X HX; apply Hagree; simpl; apply in_or_app;
      [left | right]; exact HX.
  - f_equal. apply IHt. intros X HX. apply Hagree. simpl. exact HX.
  - f_equal.
    + apply IHt. intros X HX. apply Hagree. simpl. apply in_or_app. left. exact HX.
    + apply ty_subst_env_agree_fv. intros X HX. apply Hagree. simpl. apply in_or_app. right. exact HX.
  - f_equal; [apply IHt1 | apply IHt2]; intros X HX; apply Hagree; simpl; apply in_or_app;
      [left | right]; exact HX.
Qed.

Lemma tm_subst_env_agree : forall gamma1 gamma2 t,
  (forall x, In x (fv_tm t) -> gamma1 x = gamma2 x) ->
  tm_subst_env gamma1 t = tm_subst_env gamma2 t.
Proof.
  intros gamma1 gamma2 t. induction t; simpl; intros Hagree.
  - reflexivity.
  - apply Hagree. simpl. auto.
  - f_equal. apply IHt. intros x Hx. apply Hagree. simpl. exact Hx.
  - f_equal; [apply IHt1 | apply IHt2]; intros x Hx; apply Hagree; simpl; apply in_or_app;
      [left | right]; exact Hx.
  - f_equal. apply IHt. intros x Hx. apply Hagree. simpl. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply Hagree. simpl. exact Hx.
  - f_equal; [apply IHt1 | apply IHt2]; intros x Hx; apply Hagree; simpl; apply in_or_app;
      [left | right]; exact Hx.
Qed.

(* (Substitution/opening commutation lemmas are placed after the
   local-closure opening lemmas they depend on.) *)

(* ================================================================ *)
(* Well-formedness / local closure lemmas                            *)
(* ================================================================ *)

Lemma lc_ty_mono : forall T k k',
  lc_ty_at k T -> k <= k' -> lc_ty_at k' T.
Proof.
  induction T; intros k k' H Hle; inversion H; subst.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - apply lc_ty_all. eapply IHT. eassumption. lia.
Qed.

Lemma lc_tm_mono : forall t K k K' k',
  lc_tm_at K k t -> K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  induction t; intros K k K' k' H HK Hk; inversion H; subst.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_mono; eauto.
    + eapply IHt; eauto; lia.
  - apply lc_tm_app; [eapply IHt1; eauto; lia | eapply IHt2; eauto; lia].
  - apply lc_tm_tabs. eapply IHt; eauto; lia.
  - apply lc_tm_tapp.
    + eapply IHt; eauto; lia.
    + eapply lc_ty_mono; eauto.
  - apply lc_tm_choice; [eapply IHt1; eauto; lia | eapply IHt2; eauto; lia].
Qed.

(* ---------- Opening inverse lemmas ---------- *)

Lemma lc_ty_open_elim : forall T k U K,
  lc_ty_at K (open_ty_rec k U T) -> k <= K -> lc_ty_at (S K) T.
Proof.
  induction T; intros k U K H HkK; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_ty_bvar. lia.
    + inversion H; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion H; subst. apply lc_ty_arrow.
    + eapply IHT1; eassumption.
    + eapply IHT2; eassumption.
  - inversion H; subst. apply lc_ty_all.
    eapply IHT. eassumption. lia.
Qed.

Lemma lc_ty_open_intro : forall T K U,
  lc_ty_at (S K) T -> lc_ty_at K U -> lc_ty_at K (open_ty_rec K U T).
Proof.
  induction T; intros K U H HU; simpl.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact HU.
    + apply lc_ty_bvar. inversion H; subst.
      destruct (Nat.lt_ge_cases n K) as [Hlt | Hge]; [exact Hlt |].
      exfalso.
      assert (Hle : n <= K) by (apply Nat.lt_succ_r; assumption).
      apply Nat.eqb_neq in E.
      assert (Heq : n = K) by (apply Nat.le_antisymm; assumption).
      apply E. symmetry. exact Heq.
  - apply lc_ty_fvar.
  - inversion H; subst. apply lc_ty_arrow.
    + eapply IHT1; eassumption.
    + eapply IHT2; eassumption.
  - inversion H; subst. apply lc_ty_all.
    eapply IHT. eassumption.
    eapply lc_ty_mono; eauto.
Qed.

Lemma lc_tm_open_tm_elim : forall t K k u,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_tm_bvar. lia.
    + inversion H; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + eassumption.
    + eapply IHt. eassumption.
  - inversion H; subst. apply lc_tm_app;
      [eapply IHt1; eassumption | eapply IHt2; eassumption].
  - inversion H; subst. apply lc_tm_tabs. eapply IHt. eassumption.
  - inversion H; subst. apply lc_tm_tapp;
      [eapply IHt; eassumption | eassumption].
  - inversion H; subst. apply lc_tm_choice;
      [eapply IHt1; eassumption | eapply IHt2; eassumption].
Qed.

Lemma lc_tm_open_tm_intro : forall t K k u,
  lc_tm_at K (S k) t -> lc_tm_at K k u -> lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros K k u H Hu; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. exact Hu.
    + apply lc_tm_bvar. inversion H; subst.
      destruct (Nat.lt_ge_cases n k) as [Hlt | Hge]; [exact Hlt |].
      exfalso.
      assert (Hle : n <= k) by (apply Nat.lt_succ_r; assumption).
      apply Nat.eqb_neq in E.
      assert (Heq : n = k) by (apply Nat.le_antisymm; assumption).
      apply E. symmetry. exact Heq.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + eassumption.
    + eapply IHt. eassumption.
      eapply lc_tm_mono; [exact Hu | lia | lia].
  - inversion H; subst. apply lc_tm_app; eauto.
  - inversion H; subst. apply lc_tm_tabs. eapply IHt. eassumption.
    eapply lc_tm_mono; [exact Hu | lia | lia].
  - inversion H; subst. apply lc_tm_tapp; eauto.
  - inversion H; subst. apply lc_tm_choice; eauto.
Qed.

Lemma lc_tm_open_ty_elim : forall t j K k X,
  j <= K -> lc_tm_at K k (open_tm_ty_rec j (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros j K k X HjK H; simpl in H.
  - inversion H; subst. apply lc_tm_bvar. assumption.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + eapply lc_ty_open_elim; eassumption.
    + eapply IHt; [exact HjK | eassumption].
  - inversion H; subst. apply lc_tm_app; eauto.
  - inversion H; subst. apply lc_tm_tabs.
    eapply IHt with (j := S j) (X := X). lia. eassumption.
  - inversion H; subst. apply lc_tm_tapp.
    + eapply IHt; [exact HjK | eassumption].
    + eapply lc_ty_open_elim; eassumption.
  - inversion H; subst. apply lc_tm_choice; eauto.
Qed.

Lemma lc_tm_open_ty_intro : forall t K k U,
  lc_tm_at (S K) k t -> lc_ty_at K U -> lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k U H HU; simpl.
  - apply lc_tm_bvar. inversion H; subst. assumption.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + eapply lc_ty_open_intro; eassumption.
    + eapply IHt. eassumption. assumption.
  - inversion H; subst. apply lc_tm_app; eauto.
  - inversion H; subst. apply lc_tm_tabs. eapply IHt. eassumption.
    eapply lc_ty_mono; eauto.
  - inversion H; subst. apply lc_tm_tapp.
    + eapply IHt; eassumption.
    + eapply lc_ty_open_intro; eassumption.
  - inversion H; subst. apply lc_tm_choice; eauto.
Qed.

(* Locally closed objects are unaffected by opening. *)

Lemma open_ty_rec_id_lc : forall T K,
  lc_ty_at K T -> forall j U, K <= j -> open_ty_rec j U T = T.
Proof.
  induction T; intros K H j U HKj; simpl.
  - inversion H; subst. destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - inversion H; subst. f_equal.
    + apply (IHT1 K); [eassumption | exact HKj].
    + apply (IHT2 K); [eassumption | exact HKj].
  - inversion H; subst. f_equal.
    apply (IHT (S K)); [eassumption | lia].
Qed.

Lemma open_tm_rec_id_lc : forall t K k,
  lc_tm_at K k t -> forall j u, k <= j -> open_tm_rec j u t = t.
Proof.
  induction t; intros K k H j u Hkj; simpl.
  - inversion H; subst. destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - inversion H; subst. f_equal.
    apply (IHt K (S k)); [eassumption | lia].
  - inversion H; subst. f_equal.
    + apply (IHt1 K k); [eassumption | exact Hkj].
    + apply (IHt2 K k); [eassumption | exact Hkj].
  - inversion H; subst. f_equal.
    apply (IHt (S K) k); [eassumption | exact Hkj].
  - inversion H; subst. f_equal.
    apply (IHt K k); [eassumption | exact Hkj].
  - inversion H; subst. f_equal.
    + apply (IHt1 K k); [eassumption | exact Hkj].
    + apply (IHt2 K k); [eassumption | exact Hkj].
Qed.

Lemma open_tm_ty_rec_id_lc : forall t K k,
  lc_tm_at K k t -> forall j U, K <= j -> open_tm_ty_rec j U t = t.
Proof.
  induction t; intros K k H j U HKj; simpl.
  - reflexivity.
  - reflexivity.
  - inversion H; subst. f_equal.
    + eapply open_ty_rec_id_lc; [eassumption | exact HKj].
    + apply (IHt K (S k)); [eassumption | exact HKj].
  - inversion H; subst. f_equal.
    + apply (IHt1 K k); [eassumption | exact HKj].
    + apply (IHt2 K k); [eassumption | exact HKj].
  - inversion H; subst. f_equal.
    apply (IHt (S K) k); [eassumption | lia].
  - inversion H; subst. f_equal.
    + apply (IHt K k); [eassumption | exact HKj].
    + eapply open_ty_rec_id_lc; [eassumption | exact HKj].
  - inversion H; subst. f_equal.
    + apply (IHt1 K k); [eassumption | exact HKj].
    + apply (IHt2 K k); [eassumption | exact HKj].
Qed.

(* Term substitution commutes with term opening, for locally closed substitutions. *)
Lemma tm_subst_env_open_tm_rec_lc : forall gamma,
  (forall x, locally_closed_tm (gamma x)) ->
  forall k u t,
    tm_subst_env gamma (open_tm_rec k u t) =
    open_tm_rec k (tm_subst_env gamma u) (tm_subst_env gamma t).
Proof.
  intros gamma Hlc k u t. revert k u.
  induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. eapply (open_tm_rec_id_lc _ 0 0); [apply Hlc | lia].
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
Qed.

(* ---------------- Substitution commutes with opening ---------------- *)

Lemma ty_subst_env_open_ty_rec : forall sigma,
  (forall X, locally_closed_ty (sigma X)) ->
  forall k U T,
    ty_subst_env sigma (open_ty_rec k U T) =
    open_ty_rec k (ty_subst_env sigma U) (ty_subst_env sigma T).
Proof.
  intros sigma Hsig k U T. revert k U. induction T; intros k U; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. eapply (open_ty_rec_id_lc _ 0); [apply Hsig | lia].
  - f_equal; [apply IHT1 | apply IHT2].
  - f_equal. apply IHT.
Qed.

Lemma tm_ty_subst_env_open_tm_rec : forall sigma k u t,
  tm_ty_subst_env sigma (open_tm_rec k u t) =
  open_tm_rec k (tm_ty_subst_env sigma u) (tm_ty_subst_env sigma t).
Proof.
  intros sigma k u t. revert k u. induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
Qed.

Lemma tm_ty_subst_env_open_tm_ty_rec : forall sigma,
  (forall X, locally_closed_ty (sigma X)) ->
  forall k U t,
    tm_ty_subst_env sigma (open_tm_ty_rec k U t) =
    open_tm_ty_rec k (ty_subst_env sigma U) (tm_ty_subst_env sigma t).
Proof.
  intros sigma Hsig k U t. revert k U. induction t; intros k U; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply ty_subst_env_open_ty_rec; assumption.
    + apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal. apply IHt.
  - f_equal.
    + apply IHt.
    + apply ty_subst_env_open_ty_rec; assumption.
  - f_equal; [apply IHt1 | apply IHt2].
Qed.

Lemma tm_subst_env_open_tm_ty_rec : forall gamma,
  (forall x, locally_closed_tm (gamma x)) ->
  forall k U t,
    tm_subst_env gamma (open_tm_ty_rec k U t) =
    open_tm_ty_rec k U (tm_subst_env gamma t).
Proof.
  intros gamma Hlc k U t. revert k U. induction t; intros k U; simpl.
  - reflexivity.
  - symmetry. eapply (open_tm_ty_rec_id_lc _ 0 0); [apply Hlc | lia].
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
Qed.

Lemma apply_env_open_tm_fvar :
  forall sigma gamma x t,
    (forall y, locally_closed_tm (gamma y)) ->
    apply_env sigma gamma (open_tm t (tm_fvar x)) =
    open_tm (apply_env sigma gamma t) (gamma x).
Proof.
  intros sigma gamma x t Hlc. unfold apply_env, open_tm.
  rewrite tm_ty_subst_env_open_tm_rec. simpl.
  rewrite tm_subst_env_open_tm_rec_lc; [reflexivity | exact Hlc].
Qed.

Lemma apply_env_open_tm_ty :
  forall sigma gamma X U b,
    (forall Y, locally_closed_ty (sigma Y)) ->
    (forall y, locally_closed_tm (gamma y)) ->
    locally_closed_ty U ->
    ~ In X (fv_tm_ty b) ->
    apply_env (fun Y => if Nat.eqb Y X then U else sigma Y) gamma
      (open_tm_ty b (Ty_FVar X)) =
    open_tm_ty (apply_env sigma gamma b) U.
Proof.
  intros sigma gamma X U b Hsig Hlc HU Hfresh.
  assert (Hsig' : forall Y, locally_closed_ty
    ((fun Y => if Nat.eqb Y X then U else sigma Y) Y)).
  { intro Y. destruct (Nat.eqb Y X) eqn:E.
    - apply Nat.eqb_eq in E. subst Y. exact HU.
    - apply Hsig. }
  unfold apply_env, open_tm_ty.
  rewrite (tm_ty_subst_env_open_tm_ty_rec
             (fun Y => if Nat.eqb Y X then U else sigma Y) Hsig').
  rewrite (tm_subst_env_open_tm_ty_rec gamma Hlc).
  assert (Hsubst : tm_ty_subst_env (fun Y => if Nat.eqb Y X then U else sigma Y) b
                 = tm_ty_subst_env sigma b).
  { apply tm_ty_subst_env_agree. intros Y HY.
    destruct (Nat.eqb Y X) eqn:E.
    - apply Nat.eqb_eq in E. subst Y. exfalso. apply Hfresh. exact HY.
    - reflexivity. }
  rewrite Hsubst.
  simpl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(* ================================================================ *)
(* Local closure of well-typed terms and of substituted terms        *)
(* ================================================================ *)

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H as
    [ Delta X Hin
    | Delta T1 T2 H1 H2 IH1 IH2
    | L Delta T Hbody IHbody ].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    pose proof (IHbody (fresh L) (fresh_not_in L)) as Hc.
    eapply lc_ty_open_elim; [eassumption | lia].
Qed.

Lemma ty_subst_env_lc : forall sigma T,
  (forall X, lc_ty_at 0 (sigma X)) ->
  forall K, lc_ty_at K T -> lc_ty_at K (ty_subst_env sigma T).
Proof.
  intros sigma T Hsig K H. induction H.
  - apply lc_ty_bvar. assumption.
  - simpl. eapply lc_ty_mono; [apply Hsig | lia].
  - simpl. apply lc_ty_arrow; assumption.
  - simpl. apply lc_ty_all. apply IHlc_ty_at.
Qed.

Lemma tm_ty_subst_env_lc : forall sigma t,
  (forall X, lc_ty_at 0 (sigma X)) ->
  forall K k, lc_tm_at K k t -> lc_tm_at K k (tm_ty_subst_env sigma t).
Proof.
  intros sigma t Hsig K k H. induction H.
  - simpl. apply lc_tm_bvar. assumption.
  - simpl. apply lc_tm_fvar.
  - simpl. apply lc_tm_abs.
    + eapply ty_subst_env_lc; eassumption.
    + assumption.
  - simpl. apply lc_tm_app; assumption.
  - simpl. apply lc_tm_tabs. assumption.
  - simpl. apply lc_tm_tapp.
    + assumption.
    + eapply ty_subst_env_lc; eassumption.
  - simpl. apply lc_tm_choice; assumption.
Qed.

Lemma tm_subst_env_lc : forall gamma t,
  (forall x, lc_tm_at 0 0 (gamma x)) ->
  forall K k, lc_tm_at K k t -> lc_tm_at K k (tm_subst_env gamma t).
Proof.
  intros gamma t Hgam K k H. induction H.
  - simpl. apply lc_tm_bvar. assumption.
  - simpl. eapply lc_tm_mono; [apply Hgam | lia | lia].
  - simpl. apply lc_tm_abs; assumption.
  - simpl. apply lc_tm_app; assumption.
  - simpl. apply lc_tm_tabs; assumption.
  - simpl. apply lc_tm_tapp; assumption.
  - simpl. apply lc_tm_choice; assumption.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at 0 0 t /\ lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H. induction H as
    [ Delta Gamma x T Hlookup Hwf
    | L Delta Gamma T1 t2 T2 HwfT1 Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U Ht IH HwfU
    | Delta Gamma t1 t2 T Ht1 IH1 Ht2 IH2 ].
  - split.
    + apply lc_tm_fvar.
    + eapply wf_ty_lc; eassumption.
  - split.
    + apply lc_tm_abs.
      * eapply wf_ty_lc; eassumption.
      * pose proof (IHbody (fresh L) (fresh_not_in L)) as [Ht _].
        simpl in Ht. eapply lc_tm_open_tm_elim. eassumption.
    + apply lc_ty_arrow.
      * eapply wf_ty_lc; eassumption.
      * pose proof (IHbody (fresh L) (fresh_not_in L)) as [_ Hty]. assumption.
  - destruct IH1 as [Hlc1 Hty1]. destruct IH2 as [Hlc2 _].
    split.
    + apply lc_tm_app; assumption.
    + inversion Hty1; subst. assumption.
  - split.
    + apply lc_tm_tabs.
      pose proof (IHbody (fresh L) (fresh_not_in L)) as [Ht _].
      simpl in Ht.
      eapply (lc_tm_open_ty_elim t 0 0 0 (fresh L)); [lia | eassumption].
    + apply lc_ty_all.
      pose proof (IHbody (fresh L) (fresh_not_in L)) as [_ Hty].
      simpl in Hty. eapply lc_ty_open_elim; [eassumption | lia].
  - destruct IH as [Hlct Hty].
    split.
    + apply lc_tm_tapp.
      * assumption.
      * eapply wf_ty_lc; eassumption.
    + unfold open_ty.
      eapply lc_ty_open_intro.
      * inversion Hty; subst. assumption.
      * eapply wf_ty_lc; eassumption.
  - split.
    + apply lc_tm_choice; [apply (proj1 IH1) | apply (proj1 IH2)].
    + apply (proj2 IH1).
Qed.

(* ================================================================ *)
(* Semantic logical relation                                         *)
(* ================================================================ *)

Definition PRel := tm -> Prop.

Definition lookup_rel (benv : list PRel) (i : nat) : PRel :=
  match nth_error benv i with
  | Some P => P
  | None => fun _ => False
  end.

Fixpoint VR (T : ty) (benv : list PRel) (rho : atom -> PRel) (v : tm) : Prop :=
  match T with
  | Ty_BVar i => lookup_rel benv i v
  | Ty_FVar X => rho X v
  | Ty_Arrow T1 T2 =>
      forall w, value w -> VR T1 benv rho w ->
        locally_closed_tm (tm_app v w) /\
        (exists v', tm_app v w -->* v' /\ value v' /\ VR T2 benv rho v')
  | Ty_All T1 =>
      forall U P, locally_closed_ty U ->
        locally_closed_tm (tm_tapp v U) /\
        (exists v', tm_tapp v U -->* v' /\ value v' /\ VR T1 (P :: benv) rho v')
  end.

Definition TR (T : ty) (benv : list PRel) (rho : atom -> PRel) (t : tm) : Prop :=
  locally_closed_tm t /\ exists v, t -->* v /\ value v /\ VR T benv rho v.

(* ---------------- Multi-step lemmas ---------------- *)

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H1 H2. revert c H2.
  induction H1 as [x | x y z Hxy Hyz IH]; intros c H2.
  - exact H2.
  - eapply multi_step; [exact Hxy | apply IH; exact H2].
Qed.

Lemma multi_app_l : forall t1 t1' t2,
  t1 -->* t1' -> locally_closed_tm t2 -> tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 H. induction H as [x | x y z Hxy Hyz IH]; intros Hlc.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App1; [exact Hxy | exact Hlc].
    + apply IH; exact Hlc.
Qed.

Lemma multi_app_r : forall v t2 t2',
  value v -> t2 -->* t2' -> tm_app v t2 -->* tm_app v t2'.
Proof.
  intros v t2 t2' Hv H. induction H as [x | x y z Hxy Hyz IH].
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_App2; [exact Hv | exact Hxy].
    + exact IH.
Qed.

Lemma multi_tapp : forall t t' U,
  t -->* t' -> locally_closed_ty U -> tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H. induction H as [x | x y z Hxy Hyz IH]; intros Hlc.
  - apply multi_refl.
  - eapply multi_step.
    + apply ST_TApp; [exact Hxy | exact Hlc].
    + apply IH; exact Hlc.
Qed.

(* ---------------- Basic properties of TR ---------------- *)

Lemma TR_congr : forall T1 T2 benv1 benv2 rho1 rho2 t,
  (forall v, VR T1 benv1 rho1 v <-> VR T2 benv2 rho2 v) ->
  (TR T1 benv1 rho1 t <-> TR T2 benv2 rho2 t).
Proof.
  intros T1 T2 benv1 benv2 rho1 rho2 t H. unfold TR. split.
  - intros [Hlc [v [Hs [Hval Hvr]]]]. split; [exact Hlc |].
    exists v. split; [exact Hs | split; [exact Hval |]].
    apply H. exact Hvr.
  - intros [Hlc [v [Hs [Hval Hvr]]]]. split; [exact Hlc |].
    exists v. split; [exact Hs | split; [exact Hval |]].
    apply H. exact Hvr.
Qed.

Lemma TR_value : forall T benv rho t,
  value t -> VR T benv rho t -> TR T benv rho t.
Proof.
  intros T benv rho t Hv Hvr. split.
  - destruct Hv; assumption.
  - exists t. split; [apply multi_refl | split; assumption].
Qed.

Lemma TR_multi : forall T benv rho t u,
  locally_closed_tm t -> t -->* u -> TR T benv rho u -> TR T benv rho t.
Proof.
  intros T benv rho t u Hlc Hstep [Hlcu [v [Huv [Hval Hvr]]]].
  split; [exact Hlc |].
  exists v. split.
  - eapply multi_trans; eassumption.
  - split; assumption.
Qed.

(* ---------------- lookup_rel over lists ---------------- *)

Lemma lookup_rel_cons0 : forall b P v,
  lookup_rel (P :: b) 0 v <-> P v.
Proof. intros. simpl. reflexivity. Qed.

Lemma lookup_rel_consS : forall b P i v,
  lookup_rel (P :: b) (S i) v <-> lookup_rel b i v.
Proof. intros. simpl. reflexivity. Qed.

Lemma lookup_rel_app_single_lt : forall l P i v,
  i < length l -> (lookup_rel l i v <-> lookup_rel (l ++ [P]) i v).
Proof.
  intro l. induction l as [| a l IH]; intros P i v Hi; simpl in *.
  - lia.
  - destruct i as [| i].
    + simpl. reflexivity.
    + simpl. apply IH. lia.
Qed.

Lemma lookup_rel_app_single_eq : forall l P v,
  P v <-> lookup_rel (l ++ [P]) (length l) v.
Proof.
  intro l. induction l as [| a l IH]; intros P v; simpl.
  - reflexivity.
  - apply IH.
Qed.

(* ---------------- Environment agreement ---------------- *)

Definition benv_agree (k : nat) (b1 b2 : list PRel) : Prop :=
  forall i, i < k -> forall v, lookup_rel b1 i v <-> lookup_rel b2 i v.

Definition benv_pequiv (b1 b2 : list PRel) : Prop :=
  forall i v, lookup_rel b1 i v <-> lookup_rel b2 i v.

Lemma benv_agree_cons : forall k b1 b2 P,
  benv_agree k b1 b2 -> benv_agree (S k) (P :: b1) (P :: b2).
Proof.
  intros k b1 b2 P H i Hi v. destruct i as [| i].
  - simpl. reflexivity.
  - simpl. apply H. lia.
Qed.

Lemma benv_agree_sym : forall k b1 b2,
  benv_agree k b1 b2 -> benv_agree k b2 b1.
Proof.
  intros k b1 b2 H i Hi v. symmetry. apply H; assumption.
Qed.

Lemma benv_pequiv_cons : forall b1 b2 P,
  benv_pequiv b1 b2 -> benv_pequiv (P :: b1) (P :: b2).
Proof.
  intros b1 b2 P H i v. destruct i as [| i].
  - simpl. reflexivity.
  - simpl. apply H.
Qed.

Lemma benv_pequiv_app_single : forall l P1 P2,
  (forall v, P1 v <-> P2 v) -> benv_pequiv (l ++ [P1]) (l ++ [P2]).
Proof.
  intro l. induction l as [| a l IH]; intros P1 P2 HP i v; simpl.
  - destruct i as [| i]; simpl.
    + apply HP.
    + reflexivity.
  - destruct i as [| i]; simpl.
    + reflexivity.
    + apply IH. exact HP.
Qed.

Lemma VR_benv_agree : forall k T, lc_ty_at k T ->
  forall benv1 benv2 rho v,
    benv_agree k benv1 benv2 ->
    (VR T benv1 rho v <-> VR T benv2 rho v).
Proof.
  intros k T Hlc. induction Hlc as
    [ k i Hi | k X | k T1 T2 H1 IH1 H2 IH2 | k T1 H1 IH1 ];
    intros benv1 benv2 rho v Hag.
  - simpl. apply Hag. exact Hi.
  - simpl. reflexivity.
  - simpl. split; intros H w Hw Harg.
    + apply (proj1 (TR_congr T2 T2 benv1 benv2 rho rho (tm_app v w)
                   (fun v' => IH2 benv1 benv2 rho v' Hag))).
      apply H with (w := w).
      * exact Hw.
      * apply (proj2 (IH1 benv1 benv2 rho w Hag)). exact Harg.
    + apply (proj2 (TR_congr T2 T2 benv1 benv2 rho rho (tm_app v w)
                   (fun v' => IH2 benv1 benv2 rho v' Hag))).
      apply H with (w := w).
      * exact Hw.
      * apply (proj1 (IH1 benv1 benv2 rho w Hag)). exact Harg.
  - simpl. split; intros H U P HlcU.
    + apply (proj1 (TR_congr T1 T1 (P :: benv1) (P :: benv2) rho rho
                   (tm_tapp v U)
                   (fun v' => IH1 (P :: benv1) (P :: benv2) rho v'
                                 (benv_agree_cons k benv1 benv2 P Hag)))).
      apply H; exact HlcU.
    + apply (proj2 (TR_congr T1 T1 (P :: benv1) (P :: benv2) rho rho
                   (tm_tapp v U)
                   (fun v' => IH1 (P :: benv1) (P :: benv2) rho v'
                                 (benv_agree_cons k benv1 benv2 P Hag)))).
      apply H; exact HlcU.
Qed.

Lemma VR_benv_pequiv : forall T benv1 benv2 rho v,
  benv_pequiv benv1 benv2 -> (VR T benv1 rho v <-> VR T benv2 rho v).
Proof.
  induction T as [ n | X | T1 IH1 T2 IH2 | T1 IH1 ];
    intros benv1 benv2 rho v Hpe.
  - simpl. apply Hpe.
  - simpl. reflexivity.
  - simpl. split; intros H w Hw Harg.
    + apply (proj1 (TR_congr T2 T2 benv1 benv2 rho rho (tm_app v w)
                   (fun v' => IH2 benv1 benv2 rho v' Hpe))).
      apply H with (w := w).
      * exact Hw.
      * apply (proj2 (IH1 benv1 benv2 rho w Hpe)). exact Harg.
    + apply (proj2 (TR_congr T2 T2 benv1 benv2 rho rho (tm_app v w)
                   (fun v' => IH2 benv1 benv2 rho v' Hpe))).
      apply H with (w := w).
      * exact Hw.
      * apply (proj1 (IH1 benv1 benv2 rho w Hpe)). exact Harg.
  - simpl. split; intros H U P HlcU.
    + apply (proj1 (TR_congr T1 T1 (P :: benv1) (P :: benv2) rho rho
                   (tm_tapp v U)
                   (fun v' => IH1 (P :: benv1) (P :: benv2) rho v'
                                  (benv_pequiv_cons benv1 benv2 P Hpe)))).
      apply H; exact HlcU.
    + apply (proj2 (TR_congr T1 T1 (P :: benv1) (P :: benv2) rho rho
                   (tm_tapp v U)
                   (fun v' => IH1 (P :: benv1) (P :: benv2) rho v'
                                  (benv_pequiv_cons benv1 benv2 P Hpe)))).
      apply H; exact HlcU.
Qed.

Lemma VR_rho_agree : forall T benv rho1 rho2,
  (forall X, In X (fv_ty T) -> forall v, rho1 X v <-> rho2 X v) ->
  forall v, VR T benv rho1 v <-> VR T benv rho2 v.
Proof.
  induction T as [ n | X | T1 IH1 T2 IH2 | T1 IH1 ];
    intros benv rho1 rho2 Hagree v; simpl.
  - reflexivity.
  - apply Hagree. simpl. auto.
  - simpl in Hagree.
    split; intros H w Hw Harg.
    + apply (proj1 (TR_congr T2 T2 benv benv rho1 rho2 (tm_app v w)
                   (fun v' => IH2 benv rho1 rho2
                     (fun X HX => Hagree X (in_or_app _ _ _ (or_intror HX))) v'))).
      apply H with (w := w).
      * exact Hw.
      * apply (proj2 (IH1 benv rho1 rho2
                     (fun X HX => Hagree X (in_or_app _ _ _ (or_introl HX))) w)). exact Harg.
    + apply (proj2 (TR_congr T2 T2 benv benv rho1 rho2 (tm_app v w)
                   (fun v' => IH2 benv rho1 rho2
                     (fun X HX => Hagree X (in_or_app _ _ _ (or_intror HX))) v'))).
      apply H with (w := w).
      * exact Hw.
      * apply (proj1 (IH1 benv rho1 rho2
                     (fun X HX => Hagree X (in_or_app _ _ _ (or_introl HX))) w)). exact Harg.
  - simpl in Hagree.
    split; intros H U P HlcU.
    + apply (proj1 (TR_congr T1 T1 (P :: benv) (P :: benv) rho1 rho2
                   (tm_tapp v U) (fun v' => IH1 (P :: benv) rho1 rho2 Hagree v'))).
      apply H; exact HlcU.
    + apply (proj2 (TR_congr T1 T1 (P :: benv) (P :: benv) rho1 rho2
                   (tm_tapp v U) (fun v' => IH1 (P :: benv) rho1 rho2 Hagree v'))).
      apply H; exact HlcU.
Qed.


(* ---------------- Opening of a type by a locally closed type ---------- *)

Lemma VR_open_ty_rec_subst : forall T j benv rho U,
  length benv = j ->
  locally_closed_ty U ->
  lc_ty_at (S j) T ->
  forall v,
    VR (open_ty_rec j U T) benv rho v <->
    VR T (benv ++ [VR U benv rho]) rho v.
Proof.
  induction T as [ n | X | T1 IH1 T2 IH2 | T1 IH1 ];
    intros j benv rho U Hlen HU Hlc v.
  - (* Ty_BVar *)
    simpl.
    assert (HnSj : n < S j) by (inversion Hlc; assumption).
    destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      rewrite <- Hlen. apply lookup_rel_app_single_eq.
    + apply Nat.eqb_neq in E.
      assert (Hn : n < j).
      { destruct (Nat.lt_ge_cases n j) as [Hlt | Hge]; [exact Hlt |].
        exfalso.
        assert (Hle : n <= j) by (apply Nat.lt_succ_r; assumption).
        assert (Heq : n = j) by (apply Nat.le_antisymm; assumption).
        apply E. symmetry. exact Heq. }
      rewrite <- Hlen in Hn.
      apply lookup_rel_app_single_lt. exact Hn.
  - (* Ty_FVar *)
    simpl. reflexivity.
  - (* Ty_Arrow *)
    simpl. inversion Hlc; subst.
    split; intros H w Hw Harg.
    + change (TR T2 (benv ++ [VR U benv rho]) rho (tm_app v w)).
      apply (proj1 (TR_congr (open_ty_rec (length benv) U T2) T2 benv
                    (benv ++ [VR U benv rho]) rho rho (tm_app v w)
                    (fun v' => IH2 (length benv) benv rho U eq_refl HU H3 v'))).
      apply H with (w := w).
      * exact Hw.
      * apply (proj2 (IH1 (length benv) benv rho U eq_refl HU H2 w)). exact Harg.
    + change (TR (open_ty_rec (length benv) U T2) benv rho (tm_app v w)).
      apply (proj2 (TR_congr (open_ty_rec (length benv) U T2) T2 benv
                    (benv ++ [VR U benv rho]) rho rho (tm_app v w)
                    (fun v' => IH2 (length benv) benv rho U eq_refl HU H3 v'))).
      apply H with (w := w).
      * exact Hw.
      * apply (proj1 (IH1 (length benv) benv rho U eq_refl HU H2 w)). exact Harg.
  - (* Ty_All *)
    simpl. inversion Hlc; subst.
    assert (Hpt : forall P v',
      VR (open_ty_rec (S (length benv)) U T1) (P :: benv) rho v' <->
      VR T1 (P :: (benv ++ [VR U benv rho])) rho v').
    { intros P v'. eapply iff_trans.
      - apply (IH1 (S (length benv)) (P :: benv) rho U eq_refl HU H1 v').
      - apply (VR_benv_pequiv T1 ((P :: benv) ++ [VR U (P :: benv) rho])
                (P :: (benv ++ [VR U benv rho])) rho v').
        change (benv_pequiv ((P :: benv) ++ [VR U (P :: benv) rho])
                            ((P :: benv) ++ [VR U benv rho])).
        eapply benv_pequiv_app_single.
        intro w. apply (VR_benv_agree 0 U HU (P :: benv) benv rho w).
        intros i Hi. lia. }
    split; intros H U2 P HlcU2.
    + change (TR T1 (P :: (benv ++ [VR U benv rho])) rho (tm_tapp v U2)).
      apply (proj1 (TR_congr (open_ty_rec (S (length benv)) U T1) T1 (P :: benv)
                    (P :: (benv ++ [VR U benv rho])) rho rho (tm_tapp v U2)
                    (fun v' => Hpt P v'))).
      apply H; exact HlcU2.
    + change (TR (open_ty_rec (S (length benv)) U T1) (P :: benv) rho (tm_tapp v U2)).
      apply (proj2 (TR_congr (open_ty_rec (S (length benv)) U T1) T1 (P :: benv)
                    (P :: (benv ++ [VR U benv rho])) rho rho (tm_tapp v U2)
                    (fun v' => Hpt P v'))).
      apply H; exact HlcU2.
Qed.


(* ---------------- Context environment interpretation ---------------- *)

Definition env_rel (Gamma : context) (rho : atom -> PRel) (gamma : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value (gamma x) /\ VR T [] rho (gamma x).

Lemma fv_context_lookup : forall Gamma x T,
  lookup_context x Gamma = Some T ->
  forall Y, In Y (fv_ty T) -> In Y (fv_context Gamma).
Proof.
  induction Gamma as [| [y T0] Gamma IH]; intros x T H Y HY; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + injection H as <-. apply in_or_app. left. exact HY.
    + apply in_or_app. right. eapply IH; eassumption.
Qed.

Lemma eqb_refl_true : forall x : atom, (x =? x) = true.
Proof. intro x. apply Nat.eqb_eq. reflexivity. Qed.

Lemma lookup_context_update_same : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof.
  intros. unfold update, lookup_context.
  destruct (Nat.eqb x x) eqn:E; [reflexivity |].
  apply Nat.eqb_neq in E. exfalso. apply (E eq_refl).
Qed.

Lemma lookup_context_update_other : forall Gamma x y T,
  y <> x -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x y T Hne. unfold update, lookup_context.
  destruct (Nat.eqb y x) eqn:E; [| reflexivity].
  apply Nat.eqb_eq in E. subst y. exfalso. apply Hne. reflexivity.
Qed.

(* ---------------- Fundamental theorem ---------------- *)

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall sigma rho gamma,
    (forall X, locally_closed_ty (sigma X)) ->
    (forall x, locally_closed_tm (gamma x)) ->
    env_rel Gamma rho gamma ->
    TR T [] rho (apply_env sigma gamma t).
Proof.
  intros Delta Gamma t T H.
  induction H as
    [ Delta Gamma x T Hlookup Hwf
    | L Delta Gamma T1 t2 T2 HwfT1 Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U Ht IH HwfU
    | Delta Gamma t1 t2 T Ht1 IH1 Ht2 IH2 ];
    intros sigma rho gamma Hsig Hgam Henv.
  - (* T_Var *)
    simpl. split.
    + apply Hgam.
    + destruct (Henv x T Hlookup) as [Hval Hvr].
      exists (gamma x). split; [apply multi_refl | split; assumption].
  - (* T_Abs *)
    simpl.
    change (TR (Ty_Arrow T1 T2) [] rho
              (tm_abs (ty_subst_env sigma T1) (apply_env sigma gamma t2))).
    set (x := fresh (L ++ fv_tm t2)).
    assert (HxL : ~ In x L).
    { subst x. intro Hin. apply (fresh_not_in (L ++ fv_tm t2)).
      apply in_or_app. left. exact Hin. }
    assert (HxFV : ~ In x (fv_tm t2)).
    { subst x. intro Hin. apply (fresh_not_in (L ++ fv_tm t2)).
      apply in_or_app. right. exact Hin. }
    assert (Hbodyx := Hbody x HxL).
    assert (Hlc_abs : locally_closed_tm
              (tm_abs (ty_subst_env sigma T1) (apply_env sigma gamma t2))).
    { apply lc_tm_abs.
      - eapply ty_subst_env_lc; [exact Hsig | eapply wf_ty_lc; eassumption].
      - pose proof (has_type_lc Delta (update Gamma x T1)
                      (open_tm t2 (tm_fvar x)) T2 Hbodyx) as [Hlcbody _].
        simpl in Hlcbody.
        pose proof (lc_tm_open_tm_elim t2 0 0 (tm_fvar x) Hlcbody) as Hlc_t2.
        pose proof (tm_ty_subst_env_lc sigma t2 Hsig 0 1 Hlc_t2) as Hlc_t2s.
        eapply tm_subst_env_lc; [exact Hgam | exact Hlc_t2s]. }
    split; [exact Hlc_abs |].
    exists (tm_abs (ty_subst_env sigma T1) (apply_env sigma gamma t2)).
    split; [apply multi_refl | split].
    + apply v_abs. exact Hlc_abs.
    + intros w Hw Harg.
    change (TR T2 [] rho
              (tm_app (tm_abs (ty_subst_env sigma T1) (apply_env sigma gamma t2)) w)).
    pose (gamma' := fun y => if Nat.eqb y x then w else gamma y).
    assert (Hgam' : forall y, locally_closed_tm (gamma' y)).
    { intro y. unfold gamma'. destruct (Nat.eqb y x) eqn:E.
      - destruct Hw; assumption.
      - apply Hgam. }
    assert (Henv' : env_rel (update Gamma x T1) rho gamma').
    { intros y T' Hlook.
      destruct (Nat.eq_dec y x) as [Heq | Hne].
      - subst y. rewrite lookup_context_update_same in Hlook.
        injection Hlook as <-.
        assert (Hgx : gamma' x = w).
        { unfold gamma'. destruct (Nat.eqb x x) eqn:E; [reflexivity |].
          apply Nat.eqb_neq in E. exfalso. apply (E eq_refl). }
        rewrite Hgx. split; [exact Hw | exact Harg].
      - rewrite (lookup_context_update_other Gamma x y T1 Hne) in Hlook.
        destruct (Henv y T' Hlook) as [Hval Hvr].
        assert (Hgy : gamma' y = gamma y).
        { unfold gamma'. destruct (Nat.eqb y x) eqn:E; [| reflexivity].
          apply Nat.eqb_eq in E. exfalso. apply Hne. exact E. }
        rewrite Hgy. split; assumption. }
    assert (Htr := IHbody x HxL sigma rho gamma' Hsig Hgam' Henv').
    assert (Happ : apply_env sigma gamma' t2 = apply_env sigma gamma t2).
    { unfold apply_env. apply tm_subst_env_agree. intros y Hy.
      rewrite fv_tm_tm_ty_subst_env in Hy.
      unfold gamma'. destruct (Nat.eqb y x) eqn:E.
      - apply Nat.eqb_eq in E. subst y. exfalso. apply HxFV. exact Hy.
      - reflexivity. }
    assert (Hgx : gamma' x = w).
    { unfold gamma'. destruct (Nat.eqb x x) eqn:E; [reflexivity |].
      apply Nat.eqb_neq in E. exfalso. apply (E eq_refl). }
    rewrite (apply_env_open_tm_fvar sigma gamma' x t2 Hgam') in Htr.
    rewrite Hgx in Htr.
    rewrite Happ in Htr.
    assert (Hstep : tm_app (tm_abs (ty_subst_env sigma T1)
                             (apply_env sigma gamma t2)) w -->
                    open_tm (apply_env sigma gamma t2) w).
    { apply ST_AppAbs; [exact Hlc_abs | exact Hw]. }
    assert (Hlc_app : locally_closed_tm
              (tm_app (tm_abs (ty_subst_env sigma T1)
                        (apply_env sigma gamma t2)) w)).
    { apply lc_tm_app; [exact Hlc_abs | destruct Hw; assumption]. }
    eapply TR_multi.
    * exact Hlc_app.
    * apply multi_step with (y := open_tm (apply_env sigma gamma t2) w).
      -- exact Hstep.
      -- apply multi_refl.
    * exact Htr.
  - (* T_App *)
    simpl.
    change (TR T2 [] rho
              (tm_app (apply_env sigma gamma t1) (apply_env sigma gamma t2))).
    pose proof (IH1 sigma rho gamma Hsig Hgam Henv) as Htr1.
    pose proof (IH2 sigma rho gamma Hsig Hgam Henv) as Htr2.
    destruct Htr1 as [Hlc1 [v1 [Hs1 [Hval1 Hvr1]]]].
    destruct Htr2 as [Hlc2 [v2 [Hs2 [Hval2 Hvr2]]]].
    assert (Hlc_app : locally_closed_tm
              (tm_app (apply_env sigma gamma t1) (apply_env sigma gamma t2))).
    { apply lc_tm_app; assumption. }
    assert (Hpath : tm_app (apply_env sigma gamma t1) (apply_env sigma gamma t2)
                    -->* tm_app v1 v2).
    { eapply multi_trans.
      - apply multi_app_l; [exact Hs1 | exact Hlc2].
      - apply multi_app_r; [exact Hval1 | exact Hs2]. }
    assert (Htr12 : TR T2 [] rho (tm_app v1 v2)).
    { apply Hvr1 with (w := v2); [exact Hval2 | exact Hvr2]. }
    eapply TR_multi.
    + exact Hlc_app.
    + exact Hpath.
    + exact Htr12.
  - (* T_TAbs *)
    simpl.
    change (TR (Ty_All T) [] rho (tm_tabs (apply_env sigma gamma t))).
    set (X := fresh (L ++ fv_ty T ++ fv_tm_ty t ++ fv_context Gamma)).
    assert (HXall : ~ In X (L ++ fv_ty T ++ fv_tm_ty t ++ fv_context Gamma)).
    { subst X. apply fresh_not_in. }
    assert (HXL : ~ In X L).
    { intro Hin. apply HXall. repeat rewrite in_app_iff. tauto. }
    assert (HXT : ~ In X (fv_ty T)).
    { intro Hin. apply HXall. repeat rewrite in_app_iff. tauto. }
    assert (HXt : ~ In X (fv_tm_ty t)).
    { intro Hin. apply HXall. repeat rewrite in_app_iff. tauto. }
    assert (HXG : ~ In X (fv_context Gamma)).
    { intro Hin. apply HXall. repeat rewrite in_app_iff. tauto. }
    assert (HbodyX := Hbody X HXL).
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (has_type_lc (X :: Delta) Gamma
                    (open_tm_ty t (Ty_FVar X)) (open_ty T (Ty_FVar X))
                    HbodyX) as [_ Hty].
      simpl in Hty. eapply lc_ty_open_elim; [eassumption | lia]. }
    assert (Hlc_body : lc_tm_at 1 0 (apply_env sigma gamma t)).
    { pose proof (has_type_lc (X :: Delta) Gamma
                    (open_tm_ty t (Ty_FVar X)) (open_ty T (Ty_FVar X))
                    HbodyX) as [Hlcbody _].
      simpl in Hlcbody.
      pose proof (lc_tm_open_ty_elim t 0 0 0 X ltac:(lia) Hlcbody) as Hlc_t.
      pose proof (tm_ty_subst_env_lc sigma t Hsig 1 0 Hlc_t) as Hlc_ts.
      eapply tm_subst_env_lc; [exact Hgam | exact Hlc_ts]. }
    assert (Hlc_tabs : locally_closed_tm (tm_tabs (apply_env sigma gamma t)))
      by (apply lc_tm_tabs; exact Hlc_body).
    split; [exact Hlc_tabs |].
    exists (tm_tabs (apply_env sigma gamma t)).
    split; [apply multi_refl | split].
    + apply v_tabs. exact Hlc_tabs.
    + intros U0 P HlcU0.
    change (TR T (P :: []) rho (tm_tapp (tm_tabs (apply_env sigma gamma t)) U0)).
    pose (sigma' := fun Y => if Nat.eqb Y X then U0 else sigma Y).
    pose (rho' := fun Y => if Nat.eqb Y X then P else rho Y).
    assert (Hsig' : forall Y, locally_closed_ty (sigma' Y)).
    { intro Y. unfold sigma'. destruct (Nat.eqb Y X) eqn:E.
      - exact HlcU0.
      - apply Hsig. }
    assert (Henv' : env_rel Gamma rho' gamma).
    { intros y T' Hlook. destruct (Henv y T' Hlook) as [Hval Hvr].
      split; [exact Hval |].
      assert (Hagree : forall Y, In Y (fv_ty T') -> forall v0,
                 rho' Y v0 <-> rho Y v0).
      { intros Y HY v0. unfold rho'. destruct (Nat.eqb Y X) eqn:E.
        + apply Nat.eqb_eq in E. subst Y. exfalso. apply HXG.
          eapply fv_context_lookup; eassumption.
        + reflexivity. }
      apply (proj2 (VR_rho_agree T' [] rho' rho Hagree (gamma y))).
      exact Hvr. }
    assert (Htr := IHbody X HXL sigma' rho' gamma Hsig' Hgam Henv').
    assert (Hrho'X : rho' X = P).
    { unfold rho'. destruct (Nat.eqb X X) eqn:E; [reflexivity |].
      apply Nat.eqb_neq in E. exfalso. apply (E eq_refl). }
    assert (Hterm : apply_env sigma' gamma (open_tm_ty t (Ty_FVar X)) =
                    open_tm_ty (apply_env sigma gamma t) U0).
    { unfold sigma'. apply apply_env_open_tm_ty; assumption. }
    destruct Htr as [Hlc_H [v_H [Hs_H [Hval_H Hvr_H]]]].
    rewrite Hterm in Hlc_H.
    rewrite Hterm in Hs_H.
    assert (Hpt : forall v',
      VR (open_ty T (Ty_FVar X)) [] rho' v' <-> VR T (P :: []) rho v').
    { intro v'.
      assert (Hstep1 : VR (open_ty T (Ty_FVar X)) [] rho' v' <-> VR T [P] rho' v').
      { rewrite <- Hrho'X.
        apply (VR_open_ty_rec_subst T 0 [] rho' (Ty_FVar X)
                 eq_refl (lc_ty_fvar 0 X) HlcT v'). }
      assert (Hagree : forall Y, In Y (fv_ty T) -> forall v0,
                 rho' Y v0 <-> rho Y v0).
      { intros Y HY v0. unfold rho'. destruct (Nat.eqb Y X) eqn:E.
        - apply Nat.eqb_eq in E. subst Y. exfalso. apply HXT. exact HY.
        - reflexivity. }
      assert (Hstep2 : VR T [P] rho' v' <-> VR T [P] rho v').
      { apply (VR_rho_agree T [P] rho' rho Hagree). }
      exact (iff_trans Hstep1 Hstep2). }
    assert (HvrT : VR T (P :: []) rho v_H).
    { apply (proj1 (Hpt v_H)). exact Hvr_H. }
    assert (HtrT : TR T (P :: []) rho (open_tm_ty (apply_env sigma gamma t) U0)).
    { split; [exact Hlc_H |].
      exists v_H. split; [exact Hs_H | split; [exact Hval_H | exact HvrT]]. }
    assert (Hstep : tm_tapp (tm_tabs (apply_env sigma gamma t)) U0 -->
                    open_tm_ty (apply_env sigma gamma t) U0).
    { apply ST_TAppTabs; [exact Hlc_tabs | exact HlcU0]. }
    assert (Hlc_tapp : locally_closed_tm
              (tm_tapp (tm_tabs (apply_env sigma gamma t)) U0)).
    { apply lc_tm_tapp; [exact Hlc_tabs | exact HlcU0]. }
    eapply TR_multi.
    * exact Hlc_tapp.
    * apply multi_step with (y := open_tm_ty (apply_env sigma gamma t) U0).
      -- exact Hstep.
      -- apply multi_refl.
    * exact HtrT.
  - (* T_TApp *)
    simpl.
    change (TR (open_ty T U) [] rho
              (tm_tapp (apply_env sigma gamma t) (ty_subst_env sigma U))).
    assert (Htr := IH sigma rho gamma Hsig Hgam Henv).
    destruct Htr as [Hlc_t [v [Hs [Hval Hvr]]]].
    assert (HlcU : locally_closed_ty (ty_subst_env sigma U)).
    { eapply ty_subst_env_lc; [exact Hsig | eapply wf_ty_lc; eassumption]. }
    assert (HlcUo : locally_closed_ty U) by (eapply wf_ty_lc; eassumption).
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (has_type_lc Delta Gamma t (Ty_All T) Ht) as [_ Hty].
      inversion Hty; subst. assumption. }
    assert (HtrT : TR T [VR U [] rho] rho
                     (tm_tapp v (ty_subst_env sigma U))).
    { apply Hvr. exact HlcU. }
    assert (Hpt : forall v',
      VR (open_ty T U) [] rho v' <-> VR T [VR U [] rho] rho v').
    { intro v'. apply (VR_open_ty_rec_subst T 0 [] rho U).
      - reflexivity.
      - exact HlcUo.
      - simpl. exact HlcT. }
    assert (HtrOpen : TR (open_ty T U) [] rho
                        (tm_tapp v (ty_subst_env sigma U))).
    { apply (proj2 (TR_congr (open_ty T U) T [] [VR U [] rho] rho rho
                    (tm_tapp v (ty_subst_env sigma U))
                    (fun v' => Hpt v'))).
      exact HtrT. }
    assert (Hlc_goal : locally_closed_tm
              (tm_tapp (apply_env sigma gamma t) (ty_subst_env sigma U))).
    { apply lc_tm_tapp; [exact Hlc_t | exact HlcU]. }
    eapply TR_multi.
    + exact Hlc_goal.
    + apply multi_tapp; [exact Hs | exact HlcU].
    + exact HtrOpen.
  - (* T_Choice *)
    simpl.
    change (TR T [] rho
              (tm_choice (apply_env sigma gamma t1) (apply_env sigma gamma t2))).
    assert (Htr1 := IH1 sigma rho gamma Hsig Hgam Henv).
    assert (Htr2 := IH2 sigma rho gamma Hsig Hgam Henv).
    assert (Hlc1 : locally_closed_tm (apply_env sigma gamma t1))
      by exact (proj1 Htr1).
    assert (Hlc2 : locally_closed_tm (apply_env sigma gamma t2))
      by exact (proj1 Htr2).
    assert (Hlc_ch : locally_closed_tm
              (tm_choice (apply_env sigma gamma t1) (apply_env sigma gamma t2))).
    { apply lc_tm_choice; assumption. }
    eapply TR_multi.
    + exact Hlc_ch.
    + apply multi_step with (y := apply_env sigma gamma t1).
      * apply ST_ChoiceLeft; assumption.
      * apply multi_refl.
    + exact Htr1.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H. destruct H; assumption. Qed.

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t Ht U v HwfU Hval Hvty.
  pose (sigma := fun X : atom => Ty_FVar X).
  pose (gamma := fun x : atom => tm_fvar x).
  pose (rho := fun (_ : atom) (w : tm) => True).
  assert (Hsig : forall X, locally_closed_ty (sigma X)).
  { intro X. unfold sigma. apply lc_ty_fvar. }
  assert (Hgam : forall x, locally_closed_tm (gamma x)).
  { intro x. unfold gamma. apply lc_tm_fvar. }
  assert (Henv : env_rel empty rho gamma).
  { intros x T' Hlook. simpl in Hlook. discriminate Hlook. }
  pose proof (fundamental [] empty t
                (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))
                Ht sigma rho gamma Hsig Hgam Henv) as Htr.
  unfold sigma, gamma in Htr.
  rewrite apply_env_id in Htr.
  destruct Htr as [Hlc_t [vt [Hstep_t [Hvalt HvrAll]]]].
  assert (HlcU : locally_closed_ty U) by (eapply wf_ty_lc; exact HwfU).
  pose proof (HvrAll U (fun w => w = v) HlcU) as HTR2raw.
  destruct HTR2raw as [Hlc2 [w [Hstep2 [Hval2 HvrArrow]]]].
  pose proof (HvrArrow v Hval
                (ltac:(simpl; reflexivity) :
                   VR (Ty_BVar 0) [(fun w : tm => w = v)] rho v))
    as HTR3raw.
  destruct HTR3raw as [Hlc3 [w' [Hstep3 [Hval3 Hvr3]]]].
  unfold lookup_rel in Hvr3. simpl in Hvr3. subst w'.
  assert (HstepA : tm_tapp t U -->* tm_tapp vt U).
  { apply multi_tapp; [exact Hstep_t | exact HlcU]. }
  assert (HstepB : tm_tapp t U -->* w).
  { eapply multi_trans; [exact HstepA | exact Hstep2]. }
  assert (HstepC : tm_app (tm_tapp t U) v -->* tm_app w v).
  { apply multi_app_l; [exact HstepB | apply value_lc; exact Hval]. }
  eapply multi_trans.
  - exact HstepC.
  - exact Hstep3.
Qed.

End SystemFParametricityNondeterminismHardTask.
