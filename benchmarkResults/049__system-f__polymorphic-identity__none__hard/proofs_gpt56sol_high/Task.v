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

(** The logical relation below is deliberately phrased on computations, rather
    than only on normal forms.  [sem_value] is its value part; [sem_expr] is
    the usual biorthogonal (may-convergence) lifting. *)

Definition ty_substitution := atom -> ty.
Definition tm_substitution := atom -> tm.
Definition relation := tm -> tm -> Prop.

Definition update_fun {A : Type} (f : atom -> A) (x : atom) (a : A) : atom -> A :=
  fun y => if Nat.eqb x y then a else f y.

Fixpoint subst_ty_many (s : ty_substitution) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => s X
  | Ty_Arrow T1 T2 => Ty_Arrow (subst_ty_many s T1) (subst_ty_many s T2)
  | Ty_All T1 => Ty_All (subst_ty_many s T1)
  end.

Fixpoint subst_tm_types_many (s : ty_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (subst_ty_many s T) (subst_tm_types_many s t1)
  | tm_app t1 t2 => tm_app (subst_tm_types_many s t1) (subst_tm_types_many s t2)
  | tm_tabs t1 => tm_tabs (subst_tm_types_many s t1)
  | tm_tapp t1 T => tm_tapp (subst_tm_types_many s t1) (subst_ty_many s T)
  end.

Fixpoint subst_tm_many (g : tm_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => g x
  | tm_abs T t1 => tm_abs T (subst_tm_many g t1)
  | tm_app t1 t2 => tm_app (subst_tm_many g t1) (subst_tm_many g t2)
  | tm_tabs t1 => tm_tabs (subst_tm_many g t1)
  | tm_tapp t1 T => tm_tapp (subst_tm_many g t1) T
  end.

Definition close_tm (s : ty_substitution) (g : tm_substitution) (t : tm) : tm :=
  subst_tm_many g (subst_tm_types_many s t).

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T1 => fv_ty T1
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

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T t1 => fv_ty T ++ ftv_tm t1
  | tm_app t1 t2 => ftv_tm t1 ++ ftv_tm t2
  | tm_tabs t1 => ftv_tm t1
  | tm_tapp t1 T => ftv_tm t1 ++ fv_ty T
  end.

Fixpoint atoms_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x,T) :: G => x :: fv_ty T ++ atoms_context G
  end.

Fixpoint sum_atoms (L : list atom) : nat :=
  match L with [] => 0 | x :: L' => x + sum_atoms L' end.

Lemma in_sum_atoms : forall x L, In x L -> x <= sum_atoms L.
Proof.
  intros x L; induction L as [|a L IH]; simpl; intros H.
  - contradiction.
  - destruct H as [H|H].
    + subst; lia.
    + specialize (IH H); lia.
 Qed.

Lemma fresh_atom : forall (L : list atom), exists x, ~ In x L.
Proof. intro L. exists (S (sum_atoms L)). intro H.
  pose proof (in_sum_atoms _ _ H). lia.
Qed.

Definition false_relation : relation := fun _ _ => False.

Fixpoint nth_relation (n : nat) (rs : list relation) : relation :=
  match n, rs with
  | 0, R :: _ => R
  | S n', _ :: rs' => nth_relation n' rs'
  | _, _ => false_relation
  end.

Fixpoint sem_value (beta : list relation) (rho : atom -> relation)
    (T : ty) (a b : tm) : Prop :=
  value a /\ value b /\
  match T with
  | Ty_BVar i => nth_relation i beta a b
  | Ty_FVar X => rho X a b
  | Ty_Arrow T1 T2 =>
      forall a' b', sem_value beta rho T1 a' b' ->
        exists c d, tm_app a a' -->* c /\ tm_app b b' -->* d /\
                    sem_value beta rho T2 c d
  | Ty_All T1 =>
      forall U1 U2 (R : relation),
        locally_closed_ty U1 -> locally_closed_ty U2 ->
        exists c d, tm_tapp a U1 -->* c /\ tm_tapp b U2 -->* d /\
          sem_value (R :: beta) rho T1 c d
  end.

Definition sem_expr (beta : list relation) (rho : atom -> relation)
    (T : ty) (a b : tm) : Prop :=
  exists c d, a -->* c /\ b -->* d /\ sem_value beta rho T c d.

Definition ty_env_ok (Delta : ty_context) (s : ty_substitution) : Prop :=
  forall X, In X Delta -> wf_ty [] (s X).

Definition tm_env_ok (rho : atom -> relation) (Gamma : context)
    (g1 g2 : tm_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    sem_value [] rho T (g1 x) (g2 x).

Lemma update_fun_eq : forall A (f : atom -> A) x a,
  update_fun f x a x = a.
Proof. intros; unfold update_fun; now rewrite Nat.eqb_refl. Qed.

Lemma update_fun_neq : forall A (f : atom -> A) x y a,
  x <> y -> update_fun f x a y = f y.
Proof. intros; unfold update_fun; apply Nat.eqb_neq in H; now rewrite H. Qed.

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H; induction H; intro Hbc; eauto using multi.
Qed.

Lemma multi_app1 : forall a b u, a -->* b -> locally_closed_tm u ->
  tm_app a u -->* tm_app b u.
Proof. intros a b u H; induction H; intros; eauto using multi, step. Qed.

Lemma multi_app2 : forall v a b, value v -> a -->* b ->
  tm_app v a -->* tm_app v b.
Proof. intros v a b Hv H; induction H; eauto using multi, step. Qed.

Lemma multi_tapp : forall a b U, a -->* b -> locally_closed_ty U ->
  tm_tapp a U -->* tm_tapp b U.
Proof. intros a b U H; induction H; intros; eauto using multi, step. Qed.

Lemma lc_ty_open_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X Hlc; simpl in Hlc.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion Hlc; subst. constructor. apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion Hlc; subst. apply lc_ty_arrow; [eapply IHT1|eapply IHT2]; eassumption.
  - inversion Hlc; subst. apply lc_ty_all. eapply IHT. eassumption.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H.
  - constructor.
  - constructor; assumption.
  - destruct (fresh_atom L) as [X HX]. specialize (H0 X HX).
    unfold locally_closed_ty in *. constructor. now apply lc_ty_open_inv in H0.
Qed.

Lemma lc_ty_weaken : forall k T, lc_ty_at k T -> forall j, k <= j -> lc_ty_at j T.
Proof.
  intros k T H; induction H; intros j Hj.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. match goal with IH : forall j, _ |- _ => apply IH; lia end.
Qed.

Lemma subst_ty_many_lc : forall k T s,
  lc_ty_at k T -> (forall X, locally_closed_ty (s X)) ->
  lc_ty_at k (subst_ty_many s T).
Proof.
  intros k T s H; induction H; simpl; intros Hs; eauto.
  apply lc_ty_weaken with (k := 0); [apply Hs|lia].
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption. Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H; induction H as
    [K k i Hi | K k x | K k T t HT Ht IHt |
     K k t1 t2 H1 IH1 H2 IH2 | K k t Ht IHt |
     K k t T Ht IHt HT]; intros K' k' HK Hk.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_weaken; eauto.
    + eapply IHt; lia.
  - apply lc_tm_app; [eapply IH1|eapply IH2]; eauto.
  - apply lc_tm_tabs. eapply IHt; lia.
  - apply lc_tm_tapp.
    + eapply IHt; eauto.
    + eapply lc_ty_weaken; eauto.
Qed.

Lemma subst_tm_types_many_lc : forall K k t s,
  lc_tm_at K k t -> (forall X, locally_closed_ty (s X)) ->
  lc_tm_at K k (subst_tm_types_many s t).
Proof.
  intros K k t s H; induction H; simpl; intros Hs; eauto using subst_ty_many_lc.
Qed.

Lemma subst_tm_many_lc : forall K k t g,
  lc_tm_at K k t -> (forall x, locally_closed_tm (g x)) ->
  lc_tm_at K k (subst_tm_many g t).
Proof.
  intros K k t g H; induction H; simpl; intros Hg; eauto.
  - eapply lc_tm_weaken; [apply Hg|lia|lia].
Qed.

Lemma close_tm_lc : forall t s g,
  locally_closed_tm t ->
  (forall X, locally_closed_ty (s X)) ->
  (forall x, locally_closed_tm (g x)) ->
  locally_closed_tm (close_tm s g t).
Proof.
  unfold close_tm, locally_closed_tm; intros.
  apply subst_tm_many_lc; [apply subst_tm_types_many_lc|]; assumption.
Qed.

Lemma open_ty_rec_lc : forall K U, lc_ty_at K U ->
  forall k V, K <= k -> open_ty_rec k V U = U.
Proof.
  intros K U H; induction H as
    [K i Hi | K X | K T1 T2 H1 IH1 H2 IH2 | K T H IH];
    intros k V Hle; simpl.
  - destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - now rewrite IH1, IH2.
  - now rewrite IH by lia.
Qed.

Lemma open_ty_rec_closed : forall U, locally_closed_ty U ->
  forall k V, open_ty_rec k V U = U.
Proof.
  intros U H k V. eapply open_ty_rec_lc; [apply H|lia].
Qed.

Lemma subst_ty_many_open_rec : forall T s k U,
  (forall X, locally_closed_ty (s X)) ->
  subst_ty_many s (open_ty_rec k U T) =
  open_ty_rec k (subst_ty_many s U) (subst_ty_many s T).
Proof. induction T; intros s k U Hs; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply open_ty_rec_closed. apply Hs.
  - now rewrite IHT1, IHT2.
  - now rewrite IHT.
Qed.

Lemma subst_tm_types_open_tm : forall t s k u,
  subst_tm_types_many s (open_tm_rec k u t) =
  open_tm_rec k (subst_tm_types_many s u) (subst_tm_types_many s t).
Proof. induction t; intros; simpl; try now rewrite ?IHt, ?IHt1, ?IHt2.
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma subst_tm_types_open_ty_rec : forall t s k U,
  (forall X, locally_closed_ty (s X)) ->
  subst_tm_types_many s (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (subst_ty_many s U) (subst_tm_types_many s t).
Proof.
  induction t; intros s k U Hs; simpl; try now rewrite ?IHt, ?IHt1, ?IHt2,
    ?subst_ty_many_open_rec by assumption.
Qed.

Lemma open_tm_rec_lc : forall K q t, lc_tm_at K q t ->
  forall k u, q <= k -> open_tm_rec k u t = t.
Proof.
  intros K q t H; induction H as
    [K q i Hi | K q x | K q T t HT Ht IH |
     K q t1 t2 H1 IH1 H2 IH2 | K q t Ht IH |
     K q t T Ht IH HT]; intros k u Hle; simpl.
  - destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - now rewrite IH by lia.
  - now rewrite IH1, IH2.
  - now rewrite IH.
  - now rewrite IH.
Qed.

Lemma open_tm_rec_closed : forall t, locally_closed_tm t ->
  forall k u, open_tm_rec k u t = t.
Proof. intros; eapply open_tm_rec_lc; [apply H|lia]. Qed.

Lemma open_tm_ty_rec_lc : forall K q t, lc_tm_at K q t ->
  forall k U, K <= k -> open_tm_ty_rec k U t = t.
Proof.
  intros K q t H; induction H as
    [K q i Hi | K q x | K q T t HT Ht IH |
     K q t1 t2 H1 IH1 H2 IH2 | K q t Ht IH |
     K q t T Ht IH HT]; intros k U Hle; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (open_ty_rec_lc _ _ HT k U Hle), IH by assumption; reflexivity.
  - now rewrite IH1, IH2.
  - now rewrite IH by lia.
  - rewrite IH by assumption. rewrite (open_ty_rec_lc _ _ HT k U Hle). reflexivity.
Qed.

Lemma open_tm_ty_rec_closed : forall t, locally_closed_tm t ->
  forall k U, open_tm_ty_rec k U t = t.
Proof. intros; eapply open_tm_ty_rec_lc; [apply H|lia]. Qed.

Lemma subst_tm_many_open_rec : forall t g k u,
  (forall x, locally_closed_tm (g x)) ->
  subst_tm_many g (open_tm_rec k u t) =
  open_tm_rec k (subst_tm_many g u) (subst_tm_many g t).
Proof. induction t; intros g k u Hg; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry; apply open_tm_rec_closed; apply Hg.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt.
  - now rewrite IHt.
Qed.

Lemma subst_tm_many_open_ty_rec : forall t g k U,
  (forall x, locally_closed_tm (g x)) ->
  subst_tm_many g (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (subst_tm_many g t).
Proof. induction t; intros g k U Hg; simpl.
  - reflexivity.
  - symmetry; apply open_tm_ty_rec_closed; apply Hg.
  - now rewrite IHt.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt.
  - now rewrite IHt.
Qed.

Lemma lc_tm_open_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. apply lc_tm_bvar; lia.
    + inversion H; subst. apply lc_tm_bvar. apply Nat.eqb_neq in E; lia.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs; [assumption|]. eapply IHt; eassumption.
  - inversion H; subst. apply lc_tm_app; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. apply lc_tm_tabs. eapply IHt; eassumption.
  - inversion H; subst. apply lc_tm_tapp; [eapply IHt|]; eassumption.
Qed.

Lemma lc_tm_ty_open_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H.
  - inversion H; subst. apply lc_tm_bvar; assumption.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + eapply lc_ty_open_inv; eassumption.
    + eapply IHt; eassumption.
  - inversion H; subst. apply lc_tm_app; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion H; subst. apply lc_tm_tabs. eapply IHt; eassumption.
  - inversion H; subst. apply lc_tm_tapp.
    + eapply IHt; eassumption.
    + eapply lc_ty_open_inv; eassumption.
Qed.

Lemma typing_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply wf_ty_lc in H. exact H.
    + destruct (fresh_atom L) as [x Hx]. specialize (H1 x Hx).
      unfold locally_closed_tm in H1. eapply lc_tm_open_inv; eassumption.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs. destruct (fresh_atom L) as [X HX].
    specialize (H0 X HX). unfold locally_closed_tm in H0.
    eapply lc_tm_ty_open_inv; eassumption.
  - apply lc_tm_tapp; [assumption|]. apply wf_ty_lc in H0. exact H0.
Qed.

Definition closed_ty_subst (s : ty_substitution) : Prop :=
  forall X, locally_closed_ty (s X).

Definition value_tm_subst (g : tm_substitution) : Prop :=
  forall x, locally_closed_tm (g x).

Lemma closed_ty_subst_lc : forall s, closed_ty_subst s ->
  forall X, locally_closed_ty (s X).
Proof. intros s H X. apply H. Qed.

Lemma value_tm_subst_lc : forall g, value_tm_subst g ->
  forall x, locally_closed_tm (g x).
Proof. intros g H x. apply H. Qed.

Lemma subst_ty_many_update_irrelevant : forall T s X U,
  ~ In X (fv_ty T) ->
  subst_ty_many (update_fun s X U) T = subst_ty_many s T.
Proof.
  induction T; intros s X U Hfresh; simpl in *.
  - reflexivity.
  - rewrite update_fun_neq; [reflexivity|]. intro E; subst; apply Hfresh; auto.
  - rewrite IHT1, IHT2; [reflexivity| |]; intro Hin; apply Hfresh;
      apply in_or_app; auto.
  - rewrite IHT; auto.
Qed.

Lemma subst_tm_types_update_irrelevant : forall t s X U,
  ~ In X (ftv_tm t) ->
  subst_tm_types_many (update_fun s X U) t = subst_tm_types_many s t.
Proof.
  induction t; intros s X U Hfresh; simpl in *; try reflexivity.
  - rewrite subst_ty_many_update_irrelevant, IHt; [reflexivity| |];
      intro Hin; apply Hfresh; apply in_or_app; auto.
  - rewrite IHt1, IHt2; [reflexivity| |]; intro Hin; apply Hfresh;
      apply in_or_app; auto.
  - rewrite IHt; auto.
  - rewrite IHt, subst_ty_many_update_irrelevant; [reflexivity| |];
      intro Hin; apply Hfresh; apply in_or_app; auto.
Qed.

Lemma subst_tm_many_update_irrelevant : forall t g x u,
  ~ In x (fv_tm t) ->
  subst_tm_many (update_fun g x u) t = subst_tm_many g t.
Proof.
  induction t; intros g x u Hfresh; simpl in *; try reflexivity.
  - rewrite update_fun_neq; [reflexivity|]. intro E; subst; apply Hfresh; auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; [reflexivity| |]; intro Hin; apply Hfresh;
      apply in_or_app; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
Qed.

Lemma fv_tm_types_many : forall t s, fv_tm (subst_tm_types_many s t) = fv_tm t.
Proof. induction t; intros; simpl; try now rewrite ?IHt, ?IHt1, ?IHt2. Qed.

Lemma close_open_tm : forall t s g x u,
  closed_ty_subst s -> value_tm_subst g -> locally_closed_tm u ->
  ~ In x (fv_tm t) ->
  close_tm s (update_fun g x u) (open_tm t (tm_fvar x)) =
  open_tm (close_tm s g t) u.
Proof.
  intros t s g x u Hs Hg Hu Hfresh.
  unfold close_tm, open_tm.
  rewrite subst_tm_types_open_tm.
  rewrite subst_tm_many_open_rec.
  - simpl.
    rewrite subst_tm_many_update_irrelevant.
    + replace (update_fun g x u x) with u by (symmetry; apply update_fun_eq).
      reflexivity.
    + now rewrite fv_tm_types_many.
  - intro y. unfold update_fun. destruct (Nat.eqb x y); auto using value_lc.
Qed.

Lemma close_open_ty : forall t s g X U,
  closed_ty_subst s -> value_tm_subst g -> locally_closed_ty U ->
  ~ In X (ftv_tm t) ->
  close_tm (update_fun s X U) g (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (close_tm s g t) U.
Proof.
  intros t s g X U Hs Hg HU Hfresh.
  unfold close_tm, open_tm_ty.
  rewrite subst_tm_types_open_ty_rec.
  2:{ intro Y. unfold update_fun. destruct (Nat.eqb X Y).
      - exact HU.
      - apply closed_ty_subst_lc; assumption. }
  rewrite subst_tm_types_update_irrelevant by assumption.
  rewrite subst_tm_many_open_ty_rec.
  - replace (subst_ty_many (update_fun s X U) (Ty_FVar X)) with U.
    + reflexivity.
    + simpl. symmetry. apply update_fun_eq.
  - apply value_tm_subst_lc; assumption.
Qed.

Lemma closed_ty_subst_update : forall s X U,
  closed_ty_subst s -> locally_closed_ty U ->
  closed_ty_subst (update_fun s X U).
Proof. intros s X U Hs HU Y; unfold update_fun; destruct (Nat.eqb X Y); auto. Qed.

Lemma value_tm_subst_update : forall g x u,
  value_tm_subst g -> value u -> value_tm_subst (update_fun g x u).
Proof. intros g x u Hg Hu y; unfold update_fun; destruct (Nat.eqb x y);
  auto using value_lc. Qed.

Lemma sem_value_update_irrelevant : forall T beta rho X R a b,
  ~ In X (fv_ty T) ->
  (sem_value beta (update_fun rho X R) T a b <->
   sem_value beta rho T a b).
Proof.
  induction T as [n|Y|T1 IHT1 T2 IHT2|T IHT];
    intros beta rho X R a b Hfresh; simpl in *.
  - tauto.
  - rewrite update_fun_neq; [tauto|]. intro E; subst; apply Hfresh; auto.
  - assert (Hf1 : ~ In X (fv_ty T1)) by
        (intro H; apply Hfresh; apply in_or_app; auto).
    assert (Hf2 : ~ In X (fv_ty T2)) by
        (intro H; apply Hfresh; apply in_or_app; auto).
    split; intros [Ha [Hb Hmap]]; repeat split; try assumption.
    + intros a' b' Hab.
      apply (IHT1 beta rho X R a' b' Hf1) in Hab.
      specialize (Hmap a' b' Hab).
      destruct Hmap as [c [d [Hc [Hd Hcd]]]].
      exists c, d; repeat split; try assumption.
      apply (IHT2 beta rho X R c d Hf2); assumption.
    + intros a' b' Hab.
      apply (IHT1 beta rho X R a' b' Hf1) in Hab.
      specialize (Hmap a' b' Hab).
      destruct Hmap as [c [d [Hc [Hd Hcd]]]].
      exists c, d; repeat split; try assumption.
      apply (IHT2 beta rho X R c d Hf2); assumption.
  - split; intros [Ha [Hb Hall]]; repeat split; try assumption;
      intros U1 U2 R0 HU1 HU2;
      specialize (Hall U1 U2 R0 HU1 HU2);
      destruct Hall as [c [d [Hc [Hd Hcd]]]];
      exists c, d; repeat split; try assumption.
    + apply (IHT (R0 :: beta) rho X R c d Hfresh); assumption.
    + apply (IHT (R0 :: beta) rho X R c d Hfresh) in Hcd; assumption.
Qed.

Fixpoint insert_relation (k : nat) (R : relation) (beta : list relation) :
    list relation :=
  match k, beta with
  | 0, _ => R :: beta
  | S k', B :: beta' => B :: insert_relation k' R beta'
  | S k', [] => false_relation :: insert_relation k' R []
  end.

Lemma nth_relation_insert : forall k beta R i,
  i <= k -> k <= length beta ->
  nth_relation i (insert_relation k R beta) =
  if Nat.eqb k i then R else nth_relation i beta.
Proof.
  induction k as [|k IH]; intros beta R i Hik Hlen.
  - assert (i = 0) by lia; subst; reflexivity.
  - destruct beta as [|B beta]; simpl in Hlen; [lia|].
    destruct i as [|i]; simpl.
    + reflexivity.
    + apply IH; lia.
Qed.

Lemma sem_value_open : forall T k beta rho X R a b,
  k <= length beta -> lc_ty_at (S k) T -> ~ In X (fv_ty T) ->
  (sem_value beta (update_fun rho X R)
       (open_ty_rec k (Ty_FVar X) T) a b <->
   sem_value (insert_relation k R beta) rho T a b).
Proof.
  induction T as [n|Y|T1 IHT1 T2 IHT2|T IHT];
    intros k beta rho X R a b Hlen Hlc Hfresh; simpl in *.
  - inversion Hlc; subst. rewrite nth_relation_insert by lia.
    destruct (Nat.eqb k n) eqn:E; simpl.
    + rewrite update_fun_eq. tauto.
    + tauto.
  - rewrite update_fun_neq; [tauto|]. intro E; subst; apply Hfresh; auto.
  - assert (Hf1 : ~ In X (fv_ty T1)) by
        (intro H; apply Hfresh; apply in_or_app; auto).
    assert (Hf2 : ~ In X (fv_ty T2)) by
        (intro H; apply Hfresh; apply in_or_app; auto).
    split; intros [Ha [Hb Hmap]]; repeat split; try assumption.
    + intros a' b' Hab.
      inversion Hlc; subst.
      apply (proj2 (IHT1 k beta rho X R a' b' Hlen H2 Hf1)) in Hab.
      specialize (Hmap a' b' Hab).
      destruct Hmap as [c [d [Hc [Hd Hcd]]]]. exists c, d.
      repeat split; try assumption.
      apply (proj1 (IHT2 k beta rho X R c d Hlen H3 Hf2)); assumption.
    + intros a' b' Hab.
      inversion Hlc; subst.
      apply (proj1 (IHT1 k beta rho X R a' b' Hlen H2 Hf1)) in Hab.
      specialize (Hmap a' b' Hab).
      destruct Hmap as [c [d [Hc [Hd Hcd]]]]. exists c, d.
      repeat split; try assumption.
      apply (proj2 (IHT2 k beta rho X R c d Hlen H3 Hf2)); assumption.
  - split; intros [Ha [Hb Hall]]; repeat split; try assumption;
      intros U1 U2 R0 HU1 HU2;
      specialize (Hall U1 U2 R0 HU1 HU2);
      destruct Hall as [c [d [Hc [Hd Hcd]]]]; exists c, d;
      repeat split; try assumption.
    + change (sem_value (R0 :: insert_relation k R beta) rho T c d).
      inversion Hlc; subst.
      apply (proj1 (IHT (S k) (R0 :: beta) rho X R c d
        ltac:(simpl; lia) H1 Hfresh)); assumption.
    + change (sem_value (R0 :: insert_relation k R beta) rho T c d) in Hcd.
      inversion Hlc; subst.
      apply (proj2 (IHT (S k) (R0 :: beta) rho X R c d
        ltac:(simpl; lia) H1 Hfresh)); assumption.
Qed.

Lemma sem_value_open0 : forall T rho X R a b,
  lc_ty_at 1 T -> ~ In X (fv_ty T) ->
  sem_value [] (update_fun rho X R) (open_ty T (Ty_FVar X)) a b ->
  sem_value [R] rho T a b.
Proof.
  intros. apply (sem_value_open T 0 [] rho X R a b); simpl; auto.
Qed.

Definition beta_agree (k : nat) (b1 b2 : list relation) : Prop :=
  forall i, i < k -> nth_relation i b1 = nth_relation i b2.

Lemma sem_value_beta_ext : forall T k b1 b2 rho a b,
  lc_ty_at k T -> beta_agree k b1 b2 ->
  (sem_value b1 rho T a b <-> sem_value b2 rho T a b).
Proof.
  induction T as [n|X|T1 IH1 T2 IH2|T IH];
    intros k b1 b2 rho a b Hlc Hag; simpl in *.
  - inversion Hlc; subst. rewrite (Hag n H1). tauto.
  - tauto.
  - inversion Hlc; subst. split; intros [Ha [Hb Hmap]]; repeat split; try assumption.
    + intros a' b' Hab. apply (proj2 (IH1 k b1 b2 rho a' b' H2 Hag)) in Hab.
      specialize (Hmap a' b' Hab). destruct Hmap as [c [d [Hc [Hd Hcd]]]].
      exists c, d; repeat split; try assumption.
      apply (proj1 (IH2 k b1 b2 rho c d H3 Hag)); assumption.
    + intros a' b' Hab. apply (proj1 (IH1 k b1 b2 rho a' b' H2 Hag)) in Hab.
      specialize (Hmap a' b' Hab). destruct Hmap as [c [d [Hc [Hd Hcd]]]].
      exists c, d; repeat split; try assumption.
      apply (proj2 (IH2 k b1 b2 rho c d H3 Hag)); assumption.
  - inversion Hlc; subst. split; intros [Ha [Hb Hall]]; repeat split; try assumption;
      intros U1 U2 R HU1 HU2; specialize (Hall U1 U2 R HU1 HU2);
      destruct Hall as [c [d [Hc [Hd Hcd]]]]; exists c, d;
      repeat split; try assumption.
    + apply (proj1 (IH (S k) (R :: b1) (R :: b2) rho c d H1
        ltac:(intros i Hi; destruct i; simpl; [reflexivity|apply Hag; lia]))).
      assumption.
    + apply (proj2 (IH (S k) (R :: b1) (R :: b2) rho c d H1
        ltac:(intros i Hi; destruct i; simpl; [reflexivity|apply Hag; lia]))).
      assumption.
Qed.

Lemma sem_value_beta_closed : forall U b1 b2 rho a b,
  locally_closed_ty U ->
  (sem_value b1 rho U a b <-> sem_value b2 rho U a b).
Proof.
  intros. eapply sem_value_beta_ext; [exact H|].
  intros i Hi; lia.
Qed.

Lemma sem_value_open_closed : forall T k beta rho U Q a b,
  k <= length beta -> lc_ty_at (S k) T -> locally_closed_ty U ->
  (forall x y, Q x y <-> sem_value beta rho U x y) ->
  (sem_value (insert_relation k Q beta) rho T a b <->
   sem_value beta rho (open_ty_rec k U T) a b).
Proof.
  induction T as [n|X|T1 IH1 T2 IH2|T IH];
    intros k beta rho U Q a b Hlen Hlc HU HQ; simpl in *.
  - inversion Hlc; subst. rewrite nth_relation_insert by lia.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. split.
      * intros [_ [_ Hq]]. apply (proj1 (HQ a b)); exact Hq.
      * intro Hsem. assert (HV : value a /\ value b).
        { destruct U; simpl in Hsem; tauto. }
        destruct HV as [Ha Hb].
        repeat split; try assumption. apply (proj2 (HQ a b)); exact Hsem.
    + change (value a /\ value b /\ nth_relation n beta a b <->
              value a /\ value b /\ nth_relation n beta a b). tauto.
  - tauto.
  - inversion Hlc; subst. split; intros [Ha [Hb Hmap]]; repeat split; try assumption.
    + intros a' b' Hab.
      apply (proj2 (IH1 k beta rho U Q a' b' Hlen H2 HU HQ)) in Hab.
      specialize (Hmap a' b' Hab). destruct Hmap as [c [d [Hc [Hd Hcd]]]].
      exists c, d; repeat split; try assumption.
      apply (proj1 (IH2 k beta rho U Q c d Hlen H3 HU HQ)); assumption.
    + intros a' b' Hab.
      apply (proj1 (IH1 k beta rho U Q a' b' Hlen H2 HU HQ)) in Hab.
      specialize (Hmap a' b' Hab). destruct Hmap as [c [d [Hc [Hd Hcd]]]].
      exists c, d; repeat split; try assumption.
      apply (proj2 (IH2 k beta rho U Q c d Hlen H3 HU HQ)); assumption.
  - inversion Hlc; subst. split; intros [Ha [Hb Hall]]; repeat split; try assumption;
      intros U1 U2 R HU1 HU2; specialize (Hall U1 U2 R HU1 HU2);
      destruct Hall as [c [d [Hc [Hd Hcd]]]]; exists c, d;
      repeat split; try assumption.
    + change (sem_value (R :: beta) rho (open_ty_rec (S k) U T) c d).
      assert (HQ' : forall x y, Q x y <-> sem_value (R :: beta) rho U x y).
      { intros x y. rewrite HQ. apply sem_value_beta_closed; assumption. }
      apply (proj1 (IH (S k) (R :: beta) rho U Q c d
        ltac:(simpl; lia) H1 HU HQ')). exact Hcd.
    + change (sem_value (R :: insert_relation k Q beta) rho T c d).
      assert (HQ' : forall x y, Q x y <-> sem_value (R :: beta) rho U x y).
      { intros x y. rewrite HQ. apply sem_value_beta_closed; assumption. }
      apply (proj2 (IH (S k) (R :: beta) rho U Q c d
        ltac:(simpl; lia) H1 HU HQ')). exact Hcd.
Qed.

Lemma sem_value_open_closed0 : forall T rho U a b,
  lc_ty_at 1 T -> locally_closed_ty U ->
  sem_value [fun x y => sem_value [] rho U x y] rho T a b ->
  sem_value [] rho (open_ty T U) a b.
Proof.
  intros. apply (proj1 (sem_value_open_closed T 0 [] rho U
    (fun x y => sem_value [] rho U x y) a b
    ltac:(simpl; lia) H H0 ltac:(tauto))). exact H1.
Qed.

Lemma lc_ty_open_rec : forall T k U,
  lc_ty_at (S k) T -> lc_ty_at k U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; simpl; inversion HT; subst.
  - destruct (Nat.eqb k n) eqn:E.
    + exact HU.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; [eapply IHT1|eapply IHT2]; eassumption.
  - apply lc_ty_all. eapply IHT; [eassumption|].
    eapply lc_ty_weaken; [exact HU|lia].
Qed.

Lemma typing_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H.
  - apply wf_ty_lc in H0; exact H0.
  - apply lc_ty_arrow.
    + apply wf_ty_lc in H; exact H.
    + destruct (fresh_atom L) as [x Hx]. apply (H1 x Hx).
  - inversion IHhas_type1; assumption.
  - apply lc_ty_all. destruct (fresh_atom L) as [X HX].
    specialize (H0 X HX). unfold locally_closed_ty in H0.
    eapply lc_ty_open_inv; eassumption.
  - unfold locally_closed_ty in *. inversion IHhas_type; subst.
    eapply lc_ty_open_rec; [eassumption|]. apply wf_ty_lc in H0; exact H0.
Qed.

Lemma lookup_context_atoms : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (fv_ty T) ->
  In X (atoms_context Gamma).
Proof.
  induction Gamma as [|[y A] Gamma IH]; intros x T X Hlook Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlook; subst. right. apply in_or_app; auto.
    + right. apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma tm_env_ok_update : forall rho Gamma g1 g2 x T a b,
  tm_env_ok rho Gamma g1 g2 -> sem_value [] rho T a b ->
  tm_env_ok rho (update Gamma x T) (update_fun g1 x a) (update_fun g2 x b).
Proof.
  intros rho Gamma g1 g2 x T a b Henv Hab y A Hlook.
  simpl in Hlook. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E; subst. inversion Hlook; subst.
    replace (update_fun g1 x a x) with a by (symmetry; apply update_fun_eq).
    replace (update_fun g2 x b x) with b by (symmetry; apply update_fun_eq).
    assumption.
  - apply Nat.eqb_neq in E.
    rewrite update_fun_neq by congruence. rewrite update_fun_neq by congruence.
    eapply Henv; eassumption.
Qed.

Lemma tm_env_ok_rho_update : forall rho Gamma g1 g2 X R,
  tm_env_ok rho Gamma g1 g2 -> ~ In X (atoms_context Gamma) ->
  tm_env_ok (update_fun rho X R) Gamma g1 g2.
Proof.
  intros rho Gamma g1 g2 X R Henv Hfresh x T Hlook.
  assert (HF : ~ In X (fv_ty T)).
  { intro Hin. apply Hfresh. eapply lookup_context_atoms; eauto. }
  apply (proj2 (sem_value_update_irrelevant T [] rho X R (g1 x) (g2 x) HF)).
  eapply Henv; eauto.
Qed.

Lemma sem_expr_value : forall beta rho T a b,
  sem_value beta rho T a b -> sem_expr beta rho T a b.
Proof. intros; exists a, b; repeat split; try assumption; apply multi_refl. Qed.

Lemma sem_value_values : forall beta rho T a b,
  sem_value beta rho T a b -> value a /\ value b.
Proof. destruct T; simpl; intros; tauto. Qed.

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho s1 s2 g1 g2,
    closed_ty_subst s1 -> closed_ty_subst s2 ->
    value_tm_subst g1 -> value_tm_subst g2 ->
    tm_env_ok rho Gamma g1 g2 ->
    sem_expr [] rho T (close_tm s1 g1 t) (close_tm s2 g2 t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [Delta Gamma x T Hlook Hwf |
     L Delta Gamma T1 t2 T2 HT1 Hbody IHbody |
     Delta Gamma t1 t2 T1 T2 Ht1 IH1 Ht2 IH2 |
     L Delta Gamma t T Hbody IHbody |
     Delta Gamma t T U Ht IHt HU];
    intros rho s1 s2 g1 g2 Hs1 Hs2 Hg1 Hg2 Henv.
  - apply sem_expr_value. simpl. eapply Henv; eassumption.
  - destruct (fresh_atom (L ++ fv_tm t2)) as [x Hfresh].
    assert (HxL : ~ In x L).
    { intro Hin; apply Hfresh; apply in_or_app; auto. }
    assert (HxT : ~ In x (fv_tm t2)).
    { intro Hin; apply Hfresh; apply in_or_app; auto. }
    assert (Horig : locally_closed_tm (tm_abs T1 t2)).
    { eapply typing_lc. eapply T_Abs with (L := L); eauto. }
    assert (Hcl1 : locally_closed_tm (close_tm s1 g1 (tm_abs T1 t2))).
    { eapply close_tm_lc; eauto using closed_ty_subst_lc, value_tm_subst_lc. }
    assert (Hcl2 : locally_closed_tm (close_tm s2 g2 (tm_abs T1 t2))).
    { eapply close_tm_lc; eauto using closed_ty_subst_lc, value_tm_subst_lc. }
    apply sem_expr_value. simpl.
    repeat split.
    + apply v_abs. exact Hcl1.
    + apply v_abs. exact Hcl2.
    + intros a b Hab.
      pose proof (sem_value_values _ _ _ _ _ Hab) as [Hva Hvb].
      specialize (IHbody x HxL rho s1 s2
        (update_fun g1 x a) (update_fun g2 x b) Hs1 Hs2).
      assert (Hg1' : value_tm_subst (update_fun g1 x a))
        by (apply value_tm_subst_update; assumption).
      assert (Hg2' : value_tm_subst (update_fun g2 x b))
        by (apply value_tm_subst_update; assumption).
      specialize (IHbody Hg1' Hg2' (tm_env_ok_update _ _ _ _ _ _ _ _ Henv
        Hab)).
      destruct IHbody as [c [d [Hc [Hd Hcd]]]]. exists c, d.
      repeat split; try assumption.
      * eapply multi_step.
        -- apply ST_AppAbs; [exact Hcl1|exact Hva].
        -- change (open_tm (close_tm s1 g1 t2) a -->* c).
           rewrite <- (close_open_tm t2 s1 g1 x a Hs1 Hg1
             (value_lc _ Hva) HxT). exact Hc.
      * eapply multi_step.
        -- apply ST_AppAbs; [exact Hcl2|exact Hvb].
        -- change (open_tm (close_tm s2 g2 t2) b -->* d).
           rewrite <- (close_open_tm t2 s2 g2 x b Hs2 Hg2
             (value_lc _ Hvb) HxT). exact Hd.
  - destruct (IH1 rho s1 s2 g1 g2 Hs1 Hs2 Hg1 Hg2 Henv)
      as [f1 [f2 [Hf1 [Hf2 Hfun]]]].
    destruct (IH2 rho s1 s2 g1 g2 Hs1 Hs2 Hg1 Hg2 Henv)
      as [a [b [Ha [Hb Hab]]]].
    destruct Hfun as [Vf1 [Vf2 Hmap]].
    specialize (Hmap a b Hab). destruct Hmap as [c [d [Hc [Hd Hcd]]]].
    exists c, d; repeat split; try assumption.
    + eapply multi_trans.
      * apply multi_app1; [exact Hf1|].
        eapply close_tm_lc; eauto using typing_lc, closed_ty_subst_lc,
          value_tm_subst_lc.
      * eapply multi_trans.
        -- apply multi_app2; [exact Vf1|exact Ha].
        -- exact Hc.
    + eapply multi_trans.
      * apply multi_app1; [exact Hf2|].
        eapply close_tm_lc; eauto using typing_lc, closed_ty_subst_lc,
          value_tm_subst_lc.
      * eapply multi_trans.
        -- apply multi_app2; [exact Vf2|exact Hb].
        -- exact Hd.
  - destruct (fresh_atom
        (L ++ ftv_tm t ++ fv_ty T ++ atoms_context Gamma)) as [X Hfresh].
    assert (HXL : ~ In X L).
    { intro Hin; apply Hfresh. apply in_or_app; auto. }
    assert (HXt : ~ In X (ftv_tm t)).
    { intro Hin; apply Hfresh. apply in_or_app; right.
      apply in_or_app; auto. }
    assert (HXT : ~ In X (fv_ty T)).
    { intro Hin; apply Hfresh. apply in_or_app; right.
      apply in_or_app; right. apply in_or_app; auto. }
    assert (HXG : ~ In X (atoms_context Gamma)).
    { intro Hin; apply Hfresh. apply in_or_app; right.
      apply in_or_app; right. apply in_or_app; auto. }
    assert (Horig : locally_closed_tm (tm_tabs t)).
    { eapply typing_lc. eapply T_TAbs with (L := L); eauto. }
    assert (Hcl1 : locally_closed_tm (close_tm s1 g1 (tm_tabs t))).
    { eapply close_tm_lc; eauto using closed_ty_subst_lc, value_tm_subst_lc. }
    assert (Hcl2 : locally_closed_tm (close_tm s2 g2 (tm_tabs t))).
    { eapply close_tm_lc; eauto using closed_ty_subst_lc, value_tm_subst_lc. }
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _
        (T_TAbs L Delta Gamma t T Hbody)) as HH. inversion HH; assumption. }
    apply sem_expr_value. simpl. repeat split.
    + apply v_tabs. exact Hcl1.
    + apply v_tabs. exact Hcl2.
    + intros U1 U2 R HU1 HU2.
      specialize (IHbody X HXL (update_fun rho X R)
        (update_fun s1 X U1) (update_fun s2 X U2) g1 g2).
      assert (Hs1' : closed_ty_subst (update_fun s1 X U1)).
      { apply closed_ty_subst_update; assumption. }
      assert (Hs2' : closed_ty_subst (update_fun s2 X U2)).
      { apply closed_ty_subst_update; assumption. }
      specialize (IHbody Hs1' Hs2' Hg1 Hg2
        (tm_env_ok_rho_update _ _ _ _ _ _ Henv HXG)).
      destruct IHbody as [c [d [Hc [Hd Hcd]]]]. exists c, d.
      repeat split.
      * eapply multi_step.
        -- apply ST_TAppTabs; [exact Hcl1|exact HU1].
        -- change (open_tm_ty (close_tm s1 g1 t) U1 -->* c).
           rewrite <- (close_open_ty t s1 g1 X U1 Hs1 Hg1 HU1 HXt).
           exact Hc.
      * eapply multi_step.
        -- apply ST_TAppTabs; [exact Hcl2|exact HU2].
        -- change (open_tm_ty (close_tm s2 g2 t) U2 -->* d).
           rewrite <- (close_open_ty t s2 g2 X U2 Hs2 Hg2 HU2 HXt).
           exact Hd.
      * eapply sem_value_open0; eauto.
  - destruct (IHt rho s1 s2 g1 g2 Hs1 Hs2 Hg1 Hg2 Henv)
      as [f1 [f2 [Hf1 [Hf2 Hfun]]]].
    destruct Hfun as [Vf1 [Vf2 Hall]].
    assert (HU1lc : locally_closed_ty (subst_ty_many s1 U)).
    { apply subst_ty_many_lc.
      - apply wf_ty_lc in HU; exact HU.
      - apply closed_ty_subst_lc; assumption. }
    assert (HU2lc : locally_closed_ty (subst_ty_many s2 U)).
    { apply subst_ty_many_lc.
      - apply wf_ty_lc in HU; exact HU.
      - apply closed_ty_subst_lc; assumption. }
    specialize (Hall (subst_ty_many s1 U) (subst_ty_many s2 U)
      (fun x y => sem_value [] rho U x y) HU1lc HU2lc).
    destruct Hall as [c [d [Hc [Hd Hcd]]]]. exists c, d.
    repeat split; try assumption.
    + eapply multi_trans.
      * apply multi_tapp; [exact Hf1|exact HU1lc].
      * exact Hc.
    + eapply multi_trans.
      * apply multi_tapp; [exact Hf2|exact HU2lc].
      * exact Hd.
    + eapply sem_value_open_closed0; [| |exact Hcd].
      * pose proof (typing_type_lc _ _ _ _ Ht) as HAll.
        inversion HAll; assumption.
      * apply wf_ty_lc in HU; exact HU.
Qed.

Definition identity_ty_subst : ty_substitution := fun X => Ty_FVar X.
Definition identity_tm_subst : tm_substitution := fun x => tm_fvar x.

Lemma subst_ty_many_identity : forall T,
  subst_ty_many identity_ty_subst T = T.
Proof.
  induction T; simpl.
  - reflexivity.
  - unfold identity_ty_subst; reflexivity.
  - now rewrite IHT1, IHT2.
  - now rewrite IHT.
Qed.

Lemma subst_tm_types_many_identity : forall t,
  subst_tm_types_many identity_ty_subst t = t.
Proof.
  induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2,
    ?subst_ty_many_identity; reflexivity.
Qed.

Lemma subst_tm_many_identity : forall t,
  subst_tm_many identity_tm_subst t = t.
Proof.
  induction t; simpl; try now rewrite ?IHt, ?IHt1, ?IHt2.
Qed.

Lemma close_tm_identity : forall t,
  close_tm identity_ty_subst identity_tm_subst t = t.
Proof.
  intro t. unfold close_tm. rewrite subst_tm_types_many_identity.
  apply subst_tm_many_identity.
Qed.

Lemma identity_ty_subst_closed : closed_ty_subst identity_ty_subst.
Proof. intro X. unfold identity_ty_subst, locally_closed_ty. constructor. Qed.

Lemma identity_tm_subst_lc : value_tm_subst identity_tm_subst.
Proof. intro x. unfold identity_tm_subst, locally_closed_tm. constructor. Qed.

Lemma empty_tm_env_ok : forall rho g1 g2, tm_env_ok rho empty g1 g2.
Proof. unfold tm_env_ok, empty; intros; discriminate. Qed.

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t Ht U v HU Hv Htv.
  pose (R := fun a b : tm => a = v /\ b = v).
  pose (rho := fun _ : atom => R).
  pose proof (fundamental _ _ _ _ Ht rho
    identity_ty_subst identity_ty_subst
    identity_tm_subst identity_tm_subst
    identity_ty_subst_closed identity_ty_subst_closed
    identity_tm_subst_lc identity_tm_subst_lc
    (empty_tm_env_ok rho _ _)) as Hfund.
  repeat rewrite close_tm_identity in Hfund.
  destruct Hfund as [f1 [f2 [Ht1 [Ht2 HAll]]]].
  simpl in HAll. destruct HAll as [Vf1 [Vf2 Hall]].
  assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; exact HU).
  specialize (Hall U U R HUlc HUlc).
  destruct Hall as [p1 [p2 [Hp1 [Hp2 Harr]]]].
  simpl in Harr. destruct Harr as [Vp1 [Vp2 Hmap]].
  assert (Hvv : sem_value [R] rho (Ty_BVar 0) v v).
  { simpl. repeat split; auto. }
  specialize (Hmap v v Hvv).
  destruct Hmap as [c [d [Hc [Hd Hcd]]]].
  simpl in Hcd. destruct Hcd as [_ [_ [Hcv Hdv]]]. subst c d.
  eapply multi_trans.
  - apply multi_app1.
    + eapply multi_trans.
      * apply multi_tapp; [exact Ht1|exact HUlc].
      * exact Hp1.
    + apply value_lc; exact Hv.
  - exact Hc.
Qed.

End SystemFParametricityNoneHardTask.
