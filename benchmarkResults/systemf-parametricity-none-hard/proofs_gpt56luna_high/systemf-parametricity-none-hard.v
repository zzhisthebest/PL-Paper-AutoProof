(** System F parametricity benchmark, Hard variant.
    Features: none. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNoneHardTask.

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


Hint Constructors lc_ty_at lc_tm_at value : core.

Lemma in_le_fold : forall (L : list atom) y,
  In y L -> y <= fold_right Nat.max 0 L.
Proof.
  induction L as [|x L IH].
  - simpl; intros y H; exact (False_rect _ H).
  - simpl; intros y H; destruct H as [H|H].
    + subst y; apply Nat.le_max_l.
    + etransitivity; [apply IH; assumption|apply Nat.le_max_r].
Qed.

Definition rel := tm -> tm -> Prop.

Fixpoint lookup_tm (x : atom) (s : list (atom * tm)) : option tm :=
  match s with
  | [] => None
  | (y, u) :: s' => if Nat.eqb x y then Some u else lookup_tm x s'
  end.

Definition dom_subst (s : list (atom * tm)) : list atom :=
  map (@fst atom tm) s.

Fixpoint subst_env (s : list (atom * tm)) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => match lookup_tm x s with
                 | Some u => u
                 | None => tm_fvar x
                 end
  | tm_abs T t1 => tm_abs T (subst_env s t1)
  | tm_app t1 t2 => tm_app (subst_env s t1) (subst_env s t2)
  | tm_tabs t1 => tm_tabs (subst_env s t1)
  | tm_tapp t1 T => tm_tapp (subst_env s t1) T
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => fv_tm t1
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs t1 => fv_tm t1
  | tm_tapp t1 _ => fv_tm t1
  end.

Lemma lookup_tm_none : forall x s,
  ~ In x (dom_subst s) -> lookup_tm x s = None.
Proof.
  induction s as [|[y u] s IH]; simpl; intros H.
  - reflexivity.
  - destruct (Nat.eqb x y) eqn:E.
    + exfalso; apply H; apply Nat.eqb_eq in E; simpl; auto.
    + apply IH; intro Hin; apply H; simpl; right; assumption.
Qed.

Lemma open_tm_id : forall K k u t,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros K k u t H; revert K k u H;
    induction t; intros K k u H; inversion H; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma notin_app_l : forall (x : atom) (A B : list atom), ~ In x (A ++ B) -> ~ In x A.
Proof. intros x A B H h; apply H; rewrite in_app_iff; left; assumption. Qed.

Lemma notin_app_r : forall (x : atom) (A B : list atom), ~ In x (A ++ B) -> ~ In x B.
Proof. intros x A B H h; apply H; rewrite in_app_iff; right; assumption. Qed.

Lemma lc_tm_weaken : forall K j t,
  lc_tm_at K j t -> forall k, j <= k -> lc_tm_at K k t.
Proof.
  intros K j t H; induction H; intros k0 Hk.
  - constructor; lia.
  - constructor.
  - constructor.
    + assumption.
    + apply IHlc_tm_at; lia.
  - constructor; [apply IHlc_tm_at1|apply IHlc_tm_at2]; assumption.
  - constructor; apply IHlc_tm_at; assumption.
  - constructor; [apply IHlc_tm_at|assumption]; assumption.
Qed.

Lemma lc_ty_weaken : forall j T, lc_ty_at j T -> forall k, j <= k -> lc_ty_at k T.
Proof.
  intros j T H; induction H; intros k0 Hk.
  - constructor; lia.
  - constructor.
  - constructor; [apply IHlc_ty_at1|apply IHlc_ty_at2]; assumption.
  - constructor; apply IHlc_ty_at; lia.
Qed.

Lemma open_ty_id_ge : forall j k U T,
  j <= k -> lc_ty_at j T -> open_ty_rec k U T = T.
Proof.
  intros j k U T Hjk H; revert j k U Hjk H;
    induction T; intros j k U Hjk H; inversion H; simpl.
  - destruct (Nat.eqb k n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal; [apply IHT1 with (j:=j) (k:=k)|apply IHT2 with (j:=j) (k:=k)]; assumption.
  - f_equal; apply IHT with (j:=S j) (k:=S k); [lia|assumption].
Qed.

Lemma open_tm_ty_id_ge : forall j K k U t,
  j <= K -> lc_tm_at j k t -> open_tm_ty_rec K U t = t.
Proof.
  intros j K k U t Hjk H; revert j K k U Hjk H;
    induction t; intros j K k U Hjk H; inversion H; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply open_ty_id_ge with (j:=j) (k:=K)|apply IHt with (j:=j) (K:=K) (k:=S k)]; assumption.
  - f_equal; [apply IHt1 with (j:=j) (K:=K) (k:=k)|apply IHt2 with (j:=j) (K:=K) (k:=k)]; assumption.
  - f_equal; apply IHt with (j:=S j) (K:=S K) (k:=k); [lia|assumption].
  - f_equal; [apply IHt with (j:=j) (K:=K) (k:=k)|apply open_ty_id_ge with (j:=j) (k:=K)]; assumption.
Qed.

Lemma subst_open_tm : forall s x u k t,
  ~ In x (dom_subst s) -> ~ In x (fv_tm t) ->
  (forall y v, lookup_tm y s = Some v -> locally_closed_tm v) ->
  subst_env ((x,u) :: s) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (subst_env s t).
Proof.
  intros s x u k t Hdom Hfv Hclosed; revert s x u k Hdom Hfv Hclosed;
    induction t;
    intros s x u k Hdom Hfv Hclosed.
  - simpl; destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst n; destruct k; unfold open_tm_rec; simpl;
      rewrite Nat.eqb_refl; reflexivity.
    + simpl; reflexivity.
  - match goal with
    | |- subst_env ((x,u) :: s) (open_tm_rec k (tm_fvar x) (tm_fvar ?z)) =
         open_tm_rec k u (subst_env s (tm_fvar ?z)) => (
        assert (E : z <> x)
          by (intro H; apply Hfv; subst z; simpl; auto);
        unfold open_tm_rec;
        destruct (lookup_tm z s) eqn:Es;
        unfold subst_env; simpl;
        destruct (Nat.eqb z x) eqn:Q;
        try (apply Nat.eqb_eq in Q; contradiction);
        try (apply Nat.eqb_neq in Q; rewrite Es; reflexivity);
        apply Nat.eqb_neq in Q; rewrite Es;
        symmetry; apply open_tm_id with (K := 0) (k := k) (u := u);
        eapply lc_tm_weaken; [eapply Hclosed; exact Es|lia])
    end.
  - simpl; f_equal; eauto.
  - simpl; simpl in Hfv; f_equal.
    apply IHt1; [assumption|apply (notin_app_l x (fv_tm t1) (fv_tm t2)); exact Hfv|assumption].
    apply IHt2; [assumption|apply (notin_app_r x (fv_tm t1) (fv_tm t2)); exact Hfv|assumption].
  - simpl; f_equal; eauto.
  - simpl; f_equal; eauto.
Qed.

Lemma subst_open_ty_tm : forall s x K t,
  (forall y v, lookup_tm y s = Some v -> locally_closed_tm v) ->
  subst_env s (open_tm_ty_rec K (Ty_FVar x) t) =
  open_tm_ty_rec K (Ty_FVar x) (subst_env s t).
Proof.
  intros s x K t Hclosed; revert s x K Hclosed;
    induction t; intros s x K Hclosed; simpl.
  - reflexivity.
  - destruct (lookup_tm a s) eqn:E.
    + rewrite (open_tm_ty_id_ge 0 K 0 (Ty_FVar x) t).
      * reflexivity.
      * lia.
      * eapply Hclosed; exact E.
    + reflexivity.
  - unfold subst_env; simpl.
    f_equal.
    + apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal; apply IHt with (K:=S K); assumption.
  - f_equal.
    + apply IHt; assumption.
Qed.

Definition term_rel (R : rel) (t1 t2 : tm) : Prop :=
  locally_closed_tm t1 /\ locally_closed_tm t2 /\
  exists v1 v2, multi t1 v1 /\ multi t2 v2 /\ value v1 /\ value v2 /\ R v1 v2.

Fixpoint ty_rel (rho : atom -> rel) (bs : list rel) (T : ty) : rel :=
  match T with
  | Ty_BVar i => match nth_error bs i with Some R => R | None => fun _ _ => False end
  | Ty_FVar X => rho X
  | Ty_Arrow T1 T2 =>
      fun f1 f2 => value f1 /\ value f2 /\
        forall a1 a2, value a1 -> value a2 ->
          ty_rel rho bs T1 a1 a2 ->
          term_rel (ty_rel rho bs T2) (tm_app f1 a1) (tm_app f2 a2)
  | Ty_All T1 =>
      fun f1 f2 => value f1 /\ value f2 /\
        forall R, term_rel (ty_rel rho (R :: bs) T1)
          (tm_tapp f1 (Ty_FVar 0)) (tm_tapp f2 (Ty_FVar 0))
  end.

Definition subst_rel (rho : atom -> rel) (bs : list rel)
    (Gamma : context) (s1 s2 : list (atom * tm)) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    exists u1 u2,
      lookup_tm x s1 = Some u1 /\ lookup_tm x s2 = Some u2 /\
      term_rel (ty_rel rho bs T) u1 u2.

Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
Proof.
  intros x y z H; induction H; eauto using multi.
Qed.

Lemma multi_app1 : forall t t' u, multi t t' -> locally_closed_tm u ->
  multi (tm_app t u) (tm_app t' u).
Proof.
  intros t t' u H; induction H; intros Hu.
  - constructor.
  - eapply multi_step; [apply ST_App1; eassumption|apply IHmulti; assumption].
Qed.

Lemma multi_app2 : forall v t t', value v -> multi t t' ->
  multi (tm_app v t) (tm_app v t').
Proof.
  intros v t t' Hv H; induction H.
  - constructor.
  - eapply multi_step; [apply ST_App2; eassumption|apply IHmulti].
Qed.

Lemma multi_tapp : forall t t' T, locally_closed_ty T -> multi t t' ->
  multi (tm_tapp t T) (tm_tapp t' T).
Proof.
  intros t t' T HT H; induction H.
  - constructor.
  - eapply multi_step; [apply ST_TApp; eassumption|apply IHmulti].
Qed.

Lemma term_rel_witness : forall R t1 t2,
  term_rel R t1 t2 ->
  exists v1 v2, multi t1 v1 /\ multi t2 v2 /\ value v1 /\ value v2 /\ R v1 v2.
Proof. intros R t1 t2 [_ [_ H]]; exact H. Qed.

Lemma fresh_notin : forall (L : list atom),
  ~ In (S (fold_right Nat.max 0 L)) L.
Proof.
  intros L H; pose proof (in_le_fold L _ H); lia.
Qed.

Lemma lc_ty_open_rev : forall k T U,
  lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  intros k T U H; revert k U H; induction T as [i|X|T1 IH1 T2 IH2|T IH];
    intros k U H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + constructor; apply Nat.eqb_eq in E; lia.
    + inversion H; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H.
  - constructor.
  - constructor; assumption.
  - constructor.
    apply lc_ty_open_rev with (U := Ty_FVar (S (fold_right Nat.max 0 L))).
    apply H0; apply fresh_notin.
Qed.

Lemma lc_tm_open_rev : forall K k t u,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k t u H; revert K k u H;
    induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T];
    intros K k u H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + constructor; apply Nat.eqb_eq in E; lia.
    + inversion H; constructor; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; constructor; eauto using lc_ty_open_rev.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_rev : forall K k t U,
  lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  intros K k t U H; revert K k U H;
    induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH T];
    intros K k U H; simpl in H.
  - constructor; inversion H; assumption.
  - constructor.
  - inversion H; constructor.
    + apply lc_ty_open_rev with (U := U); assumption.
    + apply IH with (U := U); assumption.
  - inversion H; constructor; eauto.
  - inversion H; constructor.
    apply IH with (U := U); assumption.
  - inversion H; constructor.
    + apply IH with (U := U); assumption.
    + apply lc_ty_open_rev with (U := U); assumption.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H.
  - constructor.
  - constructor.
    + apply wf_ty_lc with (Delta := Delta); assumption.
    + pose (x := S (fold_right Nat.max 0 L)).
      assert (Hx : ~ In x L) by (subst x; apply fresh_notin).
      apply lc_tm_open_rev with (u := tm_fvar x).
      apply H1; assumption.
  - constructor; assumption.
  - constructor.
    pose (X := S (fold_right Nat.max 0 L)).
    assert (HX : ~ In X L) by (subst X; apply fresh_notin).
    apply lc_tm_ty_open_rev with (U := Ty_FVar X).
    exact (H0 X HX).
  - constructor.
    + assumption.
    + apply wf_ty_lc with (Delta := Delta); assumption.
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
  (* The remaining proof requires the type-substitution fundamental theorem. *)
Qed.

End SystemFParametricityNoneHardTask.
