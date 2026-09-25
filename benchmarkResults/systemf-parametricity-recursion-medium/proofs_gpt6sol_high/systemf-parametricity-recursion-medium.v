(** System F parametricity benchmark, Medium variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityRecursionMediumTask.

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
  | Ty_Nat : ty.

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
  | tm_zero : tm
  | tm_succ : tm -> tm
  | tm_natrec : tm -> tm -> tm -> tm.

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

Notation "'Nat'" := Ty_Nat (in custom systemf_ty at level 0) : systemf_scope.
Notation "'zero'" := tm_zero (in custom systemf_tm at level 0) : systemf_scope.
Notation "'succ' t" := (tm_succ t) (in custom systemf_tm at level 9, t custom systemf_tm at level 0) : systemf_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom systemf_tm at level 9, n custom systemf_tm at level 0, b custom systemf_tm at level 0, s custom systemf_tm at level 0) : systemf_scope.

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  | Ty_Nat => Ty_Nat
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_tm_rec k u t1)
  | tm_natrec n b f => tm_natrec (open_tm_rec k u n) (open_tm_rec k u b) (open_tm_rec k u f)
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_tm_ty_rec k U t1)
  | tm_natrec n b f => tm_natrec (open_tm_ty_rec k U n) (open_tm_ty_rec k U b) (open_tm_ty_rec k U f)
  end.

Definition open_tm_ty (t : tm) (U : ty) : tm :=
  open_tm_ty_rec 0 U t.

Fixpoint ty_subst (X : atom) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar Y => if Nat.eqb X Y then U else Ty_FVar Y
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst X U T1) (ty_subst X U T2)
  | Ty_All T1 => Ty_All (ty_subst X U T1)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint tm_ty_subst (X : atom) (U : ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst X U T) (tm_ty_subst X U t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst X U t1) (tm_ty_subst X U t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst X U t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst X U t1) (ty_subst X U T)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_ty_subst X U t1)
  | tm_natrec n b f => tm_natrec (tm_ty_subst X U n) (tm_ty_subst X U b) (tm_ty_subst X U f)
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_subst x s t1)
  | tm_natrec n b f => tm_natrec (tm_subst x s n) (tm_subst x s b) (tm_subst x s f)
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
  | lc_ty_nat : forall k, lc_ty_at k Ty_Nat.

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
  | lc_tm_zero : forall K k, lc_tm_at K k tm_zero
  | lc_tm_succ : forall K k t, lc_tm_at K k t -> lc_tm_at K k (tm_succ t)
  | lc_tm_rec : forall K k n b s,
      lc_tm_at K k n -> lc_tm_at K k b -> lc_tm_at K k s -> lc_tm_at K k (tm_natrec n b s).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive numeric_value : tm -> Prop :=
  | nv_zero : numeric_value tm_zero
  | nv_succ : forall (n : tm), numeric_value n -> numeric_value (tm_succ n).

Fixpoint numeral (n : nat) : tm :=
  match n with O => tm_zero | S m => tm_succ (numeral m) end.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_nat : forall n, numeric_value n -> value n.

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
  | ST_Succ : forall t t',
      t --> t' -> tm_succ t --> tm_succ t'
  | ST_RecArg : forall n n' b s,

      n --> n' -> locally_closed_tm b -> locally_closed_tm s ->
      tm_natrec n b s --> tm_natrec n' b s
  | ST_RecBase : forall n b b' s,

      numeric_value n -> b --> b' -> locally_closed_tm s ->
      tm_natrec n b s --> tm_natrec n b' s
  | ST_RecStep : forall n b s s',

      numeric_value n -> value b -> s --> s' ->
      tm_natrec n b s --> tm_natrec n b s'
  | ST_RecZero : forall b s,

      value b -> value s -> tm_natrec tm_zero b s --> b
  | ST_RecSucc : forall n b s,

      numeric_value n -> value b -> value s ->
      tm_natrec (tm_succ n) b s -->
        tm_app (tm_app s n) (tm_natrec n b s)
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
  | WF_Nat : forall Delta, wf_ty Delta Ty_Nat.

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
  | T_Zero : forall Delta Gamma, has_type Delta Gamma tm_zero Ty_Nat
  | T_Succ : forall Delta Gamma n,
      has_type Delta Gamma n Ty_Nat -> has_type Delta Gamma (tm_succ n) Ty_Nat
  | T_Rec : forall Delta Gamma n b s T,
      has_type Delta Gamma n Ty_Nat -> has_type Delta Gamma b T ->
      has_type Delta Gamma s (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ->
      has_type Delta Gamma (tm_natrec n b s) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).


Hint Constructors lc_ty_at lc_tm_at value : core.

Inductive evaluates : tm -> tm -> Prop :=
  | EvalValue : forall v, value v -> evaluates v v
  | EvalApp : forall f arg U body v result,
      evaluates f (tm_abs U body) -> evaluates arg v ->
      evaluates (open_tm body v) result -> evaluates (tm_app f arg) result
  | EvalTApp : forall f U body result,
      evaluates f (tm_tabs body) -> locally_closed_ty U ->
      evaluates (open_tm_ty body U) result -> evaluates (tm_tapp f U) result
  | EvalSucc : forall t n,
      evaluates t n -> numeric_value n -> evaluates (tm_succ t) (tm_succ n)
  | EvalRecZero : forall n b s vb vs,
      evaluates n tm_zero -> evaluates b vb -> evaluates s vs ->
      evaluates (tm_natrec n b s) vb
  | EvalRecSucc : forall n b s k vb vs result,
      evaluates n (tm_succ k) -> numeric_value k ->
      evaluates b vb -> evaluates s vs ->
      evaluates (tm_app (tm_app vs k) (tm_natrec k vb vs)) result ->
      evaluates (tm_natrec n b s) result.

Definition binary_relation := tm -> tm -> Prop.

Record binary_candidate := {
  candidate_relation : binary_relation;
  candidate_values : forall v1 v2, candidate_relation v1 v2 -> value v1 /\ value v2
}.

Definition binary_env := atom -> option binary_candidate.
Definition relation_update (rho : binary_env) (X : atom) (a : binary_candidate) :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

Definition results_match (R : binary_relation) (t1 t2 : tm) : Prop :=
  exists v1 v2,
    evaluates t1 v1 /\ evaluates t2 v2 /\ R v1 v2.

Definition expression_lifting (R : binary_relation) (t1 t2 : tm) : Prop :=
  locally_closed_tm t1 /\ locally_closed_tm t2 /\ results_match R t1 t2.

Fixpoint value_relation (eta : list binary_candidate) (rho : binary_env)
    (T : ty) (v1 v2 : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error eta i with Some a => a.(candidate_relation) v1 v2 | None => False end
  | Ty_FVar X =>
      match rho X with Some a => a.(candidate_relation) v1 v2 | None => False end
  | Ty_Arrow T1 T2 =>
      value v1 /\ value v2 /\
      exists U1 body1 U2 body2,
        v1 = tm_abs U1 body1 /\ v2 = tm_abs U2 body2 /\
        forall arg1 arg2, value_relation eta rho T1 arg1 arg2 ->
          expression_lifting (value_relation eta rho T2)
            (open_tm body1 arg1) (open_tm body2 arg2)
  | Ty_All T =>
      value v1 /\ value v2 /\
      exists body1 body2,
        v1 = tm_tabs body1 /\ v2 = tm_tabs body2 /\
        forall (U1 U2 : ty) (a : binary_candidate),
          locally_closed_ty U1 -> locally_closed_ty U2 ->
          expression_lifting (value_relation (a :: eta) rho T)
            (open_tm_ty body1 U1) (open_tm_ty body2 U2)
  | Ty_Nat => v1 = v2 /\ numeric_value v1
  end.

Definition expression_relation eta rho T t1 t2 :=
  expression_lifting (value_relation eta rho T) t1 t2.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H; unfold locally_closed_tm in *; eauto with core.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst; eauto using numeric_value_lc.
Qed.

Lemma value_relation_values : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  intros eta rho T; induction T; simpl; intros v1 v2 H.
  - destruct (nth_error eta n) as [a|] eqn:E; [exact (candidate_values a _ _ H)|contradiction].
  - destruct (rho a) as [c|] eqn:E; [exact (candidate_values c _ _ H)|contradiction].
  - tauto.
  - tauto.
  - destruct H as [-> H]; split; constructor; exact H.
Qed.

Lemma multi_trans : forall x y z, x -->* y -> y -->* z -> x -->* z.
Proof.
  intros x y z H; induction H; intros H2; eauto using multi.
Qed.

Lemma multi_app1 : forall t t' u,
  t -->* t' -> locally_closed_tm u -> tm_app t u -->* tm_app t' u.
Proof.
  intros t t' u H; induction H; intros Hu; eauto using multi, step.
Qed.

Lemma multi_app2 : forall v t t',
  value v -> t -->* t' -> tm_app v t -->* tm_app v t'.
Proof.
  intros v t t' Hv H; induction H; eauto using multi, step.
Qed.

Lemma multi_tapp : forall t t' U,
  t -->* t' -> locally_closed_ty U -> tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H; induction H; intros HU; eauto using multi, step.
Qed.

Lemma multi_succ : forall t t', t -->* t' -> tm_succ t -->* tm_succ t'.
Proof.
  intros t t' H; induction H; eauto using multi, step.
Qed.

Lemma multi_rec_arg : forall n n' b s,
  n -->* n' -> locally_closed_tm b -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n' b s.
Proof.
  intros n n' b s H; induction H; intros Hb Hs; eauto using multi, step.
Qed.

Lemma multi_rec_base : forall n b b' s,
  numeric_value n -> b -->* b' -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n b' s.
Proof.
  intros n b b' s Hn H; induction H; intros Hs; eauto using multi, step.
Qed.

Lemma multi_rec_step : forall n b s s',
  numeric_value n -> value b -> s -->* s' ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof.
  intros n b s s' Hn Hb H; induction H; eauto using multi, step.
Qed.

Definition fresh (L : list atom) : atom := S (fold_right Nat.max 0 L).

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  intros L.
  assert (forall x, In x L -> x <= fold_right Nat.max 0 L) as Hbound.
  { induction L as [|a L IH]; simpl; intros x Hx.
    - contradiction.
    - destruct Hx as [->|Hx]; [apply Nat.le_max_l|].
      eapply Nat.le_trans; [apply IH; exact Hx|apply Nat.le_max_r]. }
  unfold fresh. intro H. specialize (Hbound _ H). lia.
Qed.

Lemma lc_ty_open_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; simpl; intros k X H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eauto.
  - constructor.
Qed.

Lemma lc_tm_open_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t; simpl; intros K k x H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; simpl; intros K k X H.
  - inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst. constructor; eauto using lc_ty_open_inv.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto using lc_ty_open_inv.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H; unfold locally_closed_ty in *; eauto with core.
  - constructor. eapply lc_ty_open_inv with (X := fresh L).
    apply H0, fresh_not_in.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H; unfold locally_closed_tm in *.
  - constructor.
  - apply lc_tm_abs; [eapply wf_ty_lc; eassumption|].
    eapply lc_tm_open_inv with (x := fresh L). apply H1, fresh_not_in.
  - constructor; assumption.
  - apply lc_tm_tabs. eapply lc_tm_ty_open_inv with (X := fresh L).
    apply H0, fresh_not_in.
  - constructor; [assumption|eapply wf_ty_lc; eassumption].
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma lc_ty_mono : forall K T, lc_ty_at K T ->
  forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H; induction H; intros K' HK; eauto with core.
  - constructor; lia.
  - constructor. apply IHlc_ty_at. lia.
Qed.

Lemma lc_tm_mono : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H; induction H; intros K' k' HK Hk; eauto with core.
  - constructor; lia.
  - constructor.
    + eapply lc_ty_mono; eauto.
    + apply IHlc_tm_at; lia.
  - constructor. apply IHlc_tm_at; lia.
  - constructor.
    + apply IHlc_tm_at; lia.
    + eapply lc_ty_mono; eauto.
Qed.

Lemma lc_tm_open : forall t K k u,
  lc_tm_at K (S k) t -> locally_closed_tm u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros K k u H Hu; inversion H; subst; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + eapply lc_tm_mono; eauto; lia.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma lc_ty_open : forall T K U,
  lc_ty_at (S K) T -> locally_closed_ty U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  induction T; intros K U H HU; inversion H; subst; simpl.
  - destruct (Nat.eqb K n) eqn:E.
    + eapply lc_ty_mono; eauto; lia.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
  - constructor.
Qed.

Lemma lc_tm_ty_open : forall t K k U,
  lc_tm_at (S K) k t -> locally_closed_ty U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k U H HU; inversion H; subst; simpl;
    eauto with core.
  - constructor; eauto using lc_ty_open.
  - constructor; eauto using lc_ty_open.
Qed.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof.
  intros t v H; induction H; eauto using value, numeric_value.
Qed.

Lemma evaluates_multi : forall t v,
  evaluates t v -> locally_closed_tm t -> t -->* v.
Proof.
  intros t v H; induction H; intros Hlc.
  - constructor.
  - inversion Hlc; subst.
    assert (Hf : f -->* tm_abs U body) by (apply IHevaluates1; assumption).
    assert (Ha : arg -->* v) by (apply IHevaluates2; assumption).
    assert (Hv : value v) by (eapply evaluates_value; eassumption).
    assert (Habs : locally_closed_tm (tm_abs U body))
      by (apply value_lc; eapply evaluates_value; eassumption).
    eapply multi_trans.
    + apply multi_app1; eauto.
    + eapply multi_trans.
      * apply multi_app2; eauto using value.
      * eapply multi_step.
        { apply ST_AppAbs; eauto. }
        apply IHevaluates3. inversion Habs; subst.
        eapply lc_tm_open; eauto using value_lc.
  - inversion Hlc; subst.
    assert (Hf : f -->* tm_tabs body) by (apply IHevaluates1; assumption).
    assert (Htabs : locally_closed_tm (tm_tabs body))
      by (apply value_lc; eapply evaluates_value; eassumption).
    eapply multi_trans.
    + apply multi_tapp; eauto.
    + eapply multi_step.
      * apply ST_TAppTabs; assumption.
      * apply IHevaluates2. inversion Htabs; subst.
        eapply lc_tm_ty_open; eauto.
  - inversion Hlc; subst. apply multi_succ. apply IHevaluates; assumption.
  - inversion Hlc; subst.
    assert (Hn : n -->* tm_zero) by (apply IHevaluates1; assumption).
    assert (Hb : b -->* vb) by (apply IHevaluates2; assumption).
    assert (Hs : s -->* vs) by (apply IHevaluates3; assumption).
    assert (Hvb : value vb) by (eapply evaluates_value; eassumption).
    assert (Hvs : value vs) by (eapply evaluates_value; eassumption).
    eapply multi_trans; [apply multi_rec_arg; eauto|].
    eapply multi_trans; [apply multi_rec_base; eauto using numeric_value|].
    eapply multi_trans; [apply multi_rec_step; eauto using numeric_value|].
    eapply multi_step; [apply ST_RecZero; assumption|constructor].
  - inversion Hlc; subst.
    assert (Hn : n -->* tm_succ k) by (apply IHevaluates1; assumption).
    assert (Hb : b -->* vb) by (apply IHevaluates2; assumption).
    assert (Hs : s -->* vs) by (apply IHevaluates3; assumption).
    assert (Hvb : value vb) by (eapply evaluates_value; eassumption).
    assert (Hvs : value vs) by (eapply evaluates_value; eassumption).
    eapply multi_trans; [apply multi_rec_arg; eauto|].
    eapply multi_trans; [apply multi_rec_base; eauto using numeric_value|].
    eapply multi_trans; [apply multi_rec_step; eauto using numeric_value|].
    eapply multi_step; [apply ST_RecSucc; assumption|].
    apply IHevaluates4.
    apply lc_tm_app.
    + apply lc_tm_app.
      * apply value_lc; exact Hvs.
      * apply numeric_value_lc; exact H0.
    + apply lc_tm_rec.
      * apply numeric_value_lc; exact H0.
      * apply value_lc; exact Hvb.
      * apply value_lc; exact Hvs.
Qed.

Lemma related_values_as_expression : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 -> expression_relation eta rho T v1 v2.
Proof.
  intros eta rho T v1 v2 H.
  pose proof (value_relation_values _ _ _ _ _ H) as [Hv1 Hv2].
  unfold expression_relation, expression_lifting, results_match.
  repeat split; eauto using value_lc, evaluates.
  exists v1, v2. repeat split; eauto using evaluates.
Qed.

Lemma expression_app : forall eta rho A B f1 f2 a1 a2,
  expression_relation eta rho (Ty_Arrow A B) f1 f2 ->
  expression_relation eta rho A a1 a2 ->
  expression_relation eta rho B (tm_app f1 a1) (tm_app f2 a2).
Proof.
  intros eta rho A B f1 f2 a1 a2 Hf Ha.
  destruct Hf as [Hlf1 [Hlf2 [vf1 [vf2 [Hef1 [Hef2 Hrf]]]]]].
  destruct Ha as [Hla1 [Hla2 [va1 [va2 [Hea1 [Hea2 Hra]]]]]].
  simpl in Hrf.
  destruct Hrf as [_ [_ [U1 [body1 [U2 [body2 [E1 [E2 Hbody]]]]]]]].
  subst vf1 vf2.
  specialize (Hbody va1 va2 Hra).
  destruct Hbody as [_ [_ [w1 [w2 [Hew1 [Hew2 Hr]]]]]].
  unfold expression_relation, expression_lifting, results_match.
  split; [apply lc_tm_app; assumption|].
  split; [apply lc_tm_app; assumption|].
  exists w1, w2. repeat split; eauto using evaluates.
Qed.

Lemma expression_tapp : forall eta rho T f1 f2 U1 U2 a,
  expression_relation eta rho (Ty_All T) f1 f2 ->
  locally_closed_ty U1 -> locally_closed_ty U2 ->
  expression_relation (a :: eta) rho T (tm_tapp f1 U1) (tm_tapp f2 U2).
Proof.
  intros eta rho T f1 f2 U1 U2 a Hf HU1 HU2.
  destruct Hf as [Hlf1 [Hlf2 [vf1 [vf2 [Hef1 [Hef2 Hrf]]]]]].
  simpl in Hrf.
  destruct Hrf as [_ [_ [body1 [body2 [E1 [E2 Hbody]]]]]].
  subst vf1 vf2.
  specialize (Hbody U1 U2 a HU1 HU2).
  destruct Hbody as [_ [_ [w1 [w2 [Hew1 [Hew2 Hr]]]]]].
  unfold expression_relation, expression_lifting, results_match.
  split; [apply lc_tm_tapp; assumption|].
  split; [apply lc_tm_tapp; assumption|].
  exists w1, w2. repeat split; eauto using evaluates.
Qed.

Lemma expression_succ : forall eta rho n1 n2,
  expression_relation eta rho Ty_Nat n1 n2 ->
  expression_relation eta rho Ty_Nat (tm_succ n1) (tm_succ n2).
Proof.
  intros eta rho n1 n2 H.
  destruct H as [Hl1 [Hl2 [v1 [v2 [He1 [He2 [E Hn]]]]]]]. subst v2.
  unfold expression_relation, expression_lifting, results_match.
  split; [apply lc_tm_succ; assumption|].
  split; [apply lc_tm_succ; assumption|].
  exists (tm_succ v1), (tm_succ v1). repeat split;
    eauto using evaluates, numeric_value.
Qed.

Lemma related_rec_values : forall eta rho T n b1 b2 s1 s2,
  numeric_value n -> value_relation eta rho T b1 b2 ->
  value_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 s2 ->
  expression_relation eta rho T
    (tm_natrec n b1 s1) (tm_natrec n b2 s2).
Proof.
  intros eta rho T n b1 b2 s1 s2 Hn.
  induction Hn; intros Hb Hs.
  - pose proof (value_relation_values _ _ _ _ _ Hb) as [Hvb1 Hvb2].
    pose proof (value_relation_values _ _ _ _ _ Hs) as [Hvs1 Hvs2].
    unfold expression_relation, expression_lifting, results_match.
    split; [apply lc_tm_rec; [constructor|apply value_lc; exact Hvb1|apply value_lc; exact Hvs1]|].
    split; [apply lc_tm_rec; [constructor|apply value_lc; exact Hvb2|apply value_lc; exact Hvs2]|].
    exists b1, b2. repeat split; try assumption.
    + eapply EvalRecZero.
      * apply EvalValue. apply v_nat. constructor.
      * apply EvalValue. exact Hvb1.
      * apply EvalValue. exact Hvs1.
    + eapply EvalRecZero.
      * apply EvalValue. apply v_nat. constructor.
      * apply EvalValue. exact Hvb2.
      * apply EvalValue. exact Hvs2.
  - pose proof (value_relation_values _ _ _ _ _ Hb) as [Hvb1 Hvb2].
    pose proof (value_relation_values _ _ _ _ _ Hs) as [Hvs1 Hvs2].
    pose proof (related_values_as_expression _ _ _ _ _ Hs) as Hse.
    assert (Hne : expression_relation eta rho Ty_Nat n n).
    { apply related_values_as_expression. simpl. auto. }
    pose proof (expression_app _ _ _ _ _ _ _ _ Hse Hne) as Hstep.
    pose proof (IHHn Hb Hs) as Hrec.
    pose proof (expression_app _ _ _ _ _ _ _ _ Hstep Hrec) as Hresult.
    destruct Hresult as [_ [_ [w1 [w2 [Hew1 [Hew2 Hr]]]]]].
    unfold expression_relation, expression_lifting, results_match.
    split; [apply lc_tm_rec; [apply numeric_value_lc; constructor; exact Hn|apply value_lc; exact Hvb1|apply value_lc; exact Hvs1]|].
    split; [apply lc_tm_rec; [apply numeric_value_lc; constructor; exact Hn|apply value_lc; exact Hvb2|apply value_lc; exact Hvs2]|].
    exists w1, w2. repeat split; try assumption.
    + apply EvalRecSucc with (k := n) (vb := b1) (vs := s1);
        eauto using EvalValue, numeric_value.
    + apply EvalRecSucc with (k := n) (vb := b2) (vs := s2);
        eauto using EvalValue, numeric_value.
Qed.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => fv_ty A ++ fv_ty B
  | Ty_All A => fv_ty A
  | Ty_Nat => []
  end.

Lemma expression_lifting_ext : forall R S t1 t2,
  (forall v1 v2, R v1 v2 <-> S v1 v2) ->
  expression_lifting R t1 t2 <-> expression_lifting S t1 t2.
Proof.
  intros R S t1 t2 Hext; unfold expression_lifting, results_match.
  split; intros [Hl1 [Hl2 [v1 [v2 [He1 [He2 Hr]]]]]];
    repeat split; try assumption; exists v1, v2; repeat split; eauto;
    apply Hext; assumption.
Qed.

Lemma value_relation_open_fvar : forall T p s rho X cand v1 v2,
  lc_ty_at (S (length p)) T -> ~ In X (fv_ty T) ->
  value_relation (p ++ cand :: s) rho T v1 v2 <->
  value_relation (p ++ s) (relation_update rho X cand)
    (open_ty_rec (length p) (Ty_FVar X) T) v1 v2.
Proof.
  induction T as [n|Y|T1 IHT1 T2 IHT2|T IHT|];
    intros p s rho X cand v1 v2 Hlc Hfresh;
    simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eq_dec n (length p)) as [->|Hneq].
    + rewrite Nat.eqb_refl. unfold relation_update.
      rewrite nth_error_app2 by lia. simpl.
      rewrite Nat.sub_diag. rewrite Nat.eqb_refl. simpl. tauto.
    + assert (n < length p) by lia.
      assert (length p =? n = false) as E by (apply Nat.eqb_neq; lia).
      rewrite E. simpl.
      rewrite nth_error_app1 by lia.
      rewrite nth_error_app1 by lia. tauto.
  - assert (Y <> X) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold relation_update. apply Nat.eqb_neq in H.
    rewrite Nat.eqb_sym, H. tauto.
  - inversion Hlc; subst.
    assert (Hlc1 : lc_ty_at (S (length p)) T1) by (inversion Hlc; assumption).
    assert (Hlc2 : lc_ty_at (S (length p)) T2) by (inversion Hlc; assumption).
    assert (Hfa : ~ In X (fv_ty T1)).
    { intro H; apply Hfresh. apply in_or_app. left; exact H. }
    assert (Hfb : ~ In X (fv_ty T2)).
    { intro H; apply Hfresh. apply in_or_app. right; exact H. }
    simpl.
    split; intros [Hv1 [Hv2 [U1 [b1 [U2 [b2 [E1 [E2 Hbody]]]]]]]].
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, b1, U2, b2.
      split; [exact E1|]. split; [exact E2|].
      intros z1 z2 Harg.
      apply (proj1 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHT2 p s rho X cand r1 r2 Hlc2 Hfb))).
      apply Hbody. apply (proj2 (IHT1 p s rho X cand z1 z2 Hlc1 Hfa)).
      exact Harg.
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, b1, U2, b2.
      split; [exact E1|]. split; [exact E2|].
      intros z1 z2 Harg.
      apply (proj2 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHT2 p s rho X cand r1 r2 Hlc2 Hfb))).
      apply Hbody. apply (proj1 (IHT1 p s rho X cand z1 z2 Hlc1 Hfa)).
      exact Harg.
  - inversion Hlc; subst.
    simpl.
    assert (Hinner : lc_ty_at (S (S (length p))) T)
      by (inversion Hlc; assumption).
    split; intros [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hbody]]]]]].
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 c HU1 HU2.
      apply (proj1 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHT (c :: p) s rho X cand r1 r2 Hinner Hfresh))).
      apply Hbody; assumption.
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 c HU1 HU2.
      apply (proj2 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHT (c :: p) s rho X cand r1 r2 Hinner Hfresh))).
      apply Hbody; assumption.
  - tauto.
Qed.

Lemma value_relation_tail_irrel : forall T p s1 s2 rho v1 v2,
  lc_ty_at (length p) T ->
  value_relation (p ++ s1) rho T v1 v2 <->
  value_relation (p ++ s2) rho T v1 v2.
Proof.
  induction T as [n|Y|A IHA B IHB|A IHA|];
    intros p s1 s2 rho v1 v2 Hlc; simpl in *.
  - inversion Hlc; subst.
    rewrite !nth_error_app1 by lia. tauto.
  - tauto.
  - inversion Hlc; subst.
    assert (Ha : lc_ty_at (length p) A) by (inversion Hlc; assumption).
    assert (Hb : lc_ty_at (length p) B) by (inversion Hlc; assumption).
    split; intros [Hv1 [Hv2 [U1 [b1 [U2 [b2 [E1 [E2 Hbody]]]]]]]].
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, b1, U2, b2. split; [exact E1|]. split; [exact E2|].
      intros z1 z2 Hz.
      apply (proj1 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHB p s1 s2 rho r1 r2 Hb))).
      apply Hbody. apply (proj2 (IHA p s1 s2 rho z1 z2 Ha)). exact Hz.
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, b1, U2, b2. split; [exact E1|]. split; [exact E2|].
      intros z1 z2 Hz.
      apply (proj2 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHB p s1 s2 rho r1 r2 Hb))).
      apply Hbody. apply (proj1 (IHA p s1 s2 rho z1 z2 Ha)). exact Hz.
  - inversion Hlc; subst.
    assert (Ha : lc_ty_at (S (length p)) A) by (inversion Hlc; assumption).
    split; intros [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hbody]]]]]].
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 c HU1 HU2.
      apply (proj1 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHA (c :: p) s1 s2 rho r1 r2 Ha))).
      apply Hbody; assumption.
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 c HU1 HU2.
      apply (proj2 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHA (c :: p) s1 s2 rho r1 r2 Ha))).
      apply Hbody; assumption.
  - tauto.
Qed.

Definition type_candidate (rho : binary_env) (U : ty) : binary_candidate :=
  {| candidate_relation := value_relation [] rho U;
     candidate_values := value_relation_values [] rho U |}.

Lemma value_relation_open_ty : forall T p s rho U v1 v2,
  lc_ty_at (S (length p)) T -> lc_ty_at 0 U ->
  value_relation (p ++ type_candidate rho U :: s) rho T v1 v2 <->
  value_relation (p ++ s) rho (open_ty_rec (length p) U T) v1 v2.
Proof.
  induction T as [n|Y|A IHA B IHB|A IHA|];
    intros p s rho U v1 v2 Hlc HU; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eq_dec n (length p)) as [->|Hneq].
    + rewrite Nat.eqb_refl.
      rewrite nth_error_app2 by lia.
      rewrite Nat.sub_diag. simpl.
      apply (value_relation_tail_irrel U [] [] (p ++ s) rho v1 v2 HU).
    + assert (n < length p) by lia.
      assert (length p =? n = false) as E by (apply Nat.eqb_neq; lia).
      rewrite E. simpl.
      rewrite nth_error_app1 by lia.
      rewrite nth_error_app1 by lia. tauto.
  - tauto.
  - inversion Hlc; subst.
    assert (Ha : lc_ty_at (S (length p)) A) by (inversion Hlc; assumption).
    assert (Hb : lc_ty_at (S (length p)) B) by (inversion Hlc; assumption).
    split; intros [Hv1 [Hv2 [V1 [b1 [V2 [b2 [E1 [E2 Hbody]]]]]]]].
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists V1, b1, V2, b2. split; [exact E1|]. split; [exact E2|].
      intros z1 z2 Hz.
      apply (proj1 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHB p s rho U r1 r2 Hb HU))).
      apply Hbody. apply (proj2 (IHA p s rho U z1 z2 Ha HU)). exact Hz.
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists V1, b1, V2, b2. split; [exact E1|]. split; [exact E2|].
      intros z1 z2 Hz.
      apply (proj2 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHB p s rho U r1 r2 Hb HU))).
      apply Hbody. apply (proj1 (IHA p s rho U z1 z2 Ha HU)). exact Hz.
  - inversion Hlc; subst.
    assert (Ha : lc_ty_at (S (S (length p))) A)
      by (inversion Hlc; assumption).
    split; intros [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hbody]]]]]].
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros V1 V2 c HV1 HV2.
      apply (proj1 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHA (c :: p) s rho U r1 r2 Ha HU))).
      apply Hbody; assumption.
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros V1 V2 c HV1 HV2.
      apply (proj2 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHA (c :: p) s rho U r1 r2 Ha HU))).
      apply Hbody; assumption.
  - tauto.
Qed.

Lemma has_type_result_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H; unfold locally_closed_ty in *.
  - eapply wf_ty_lc; eassumption.
  - constructor; [eapply wf_ty_lc; eassumption|].
    exact (H1 (fresh L) (fresh_not_in L)).
  - inversion IHhas_type1; assumption.
  - constructor. eapply lc_ty_open_inv with (X := fresh L).
    exact (H0 (fresh L) (fresh_not_in L)).
  - inversion IHhas_type; subst.
    eapply lc_ty_open; eauto using wf_ty_lc.
  - constructor.
  - constructor.
  - exact IHhas_type2.
Qed.

Fixpoint sem_ty (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (sem_ty theta A) (sem_ty theta B)
  | Ty_All A => Ty_All (sem_ty theta A)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint sem_tm (theta : atom -> ty) (gamma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs T b => tm_abs (sem_ty theta T) (sem_tm theta gamma b)
  | tm_app f a => tm_app (sem_tm theta gamma f) (sem_tm theta gamma a)
  | tm_tabs b => tm_tabs (sem_tm theta gamma b)
  | tm_tapp f T => tm_tapp (sem_tm theta gamma f) (sem_ty theta T)
  | tm_zero => tm_zero
  | tm_succ n => tm_succ (sem_tm theta gamma n)
  | tm_natrec n b s =>
      tm_natrec (sem_tm theta gamma n) (sem_tm theta gamma b) (sem_tm theta gamma s)
  end.

Definition ty_env_update (theta : atom -> ty) X U :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition tm_env_update (gamma : atom -> tm) x v :=
  fun y => if Nat.eqb x y then v else gamma y.

Lemma sem_ty_lc : forall T K theta,
  lc_ty_at K T -> (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at K (sem_ty theta T).
Proof.
  intros T K theta H; induction H; intros Htheta; simpl; eauto with core.
  - eapply lc_ty_mono; [apply Htheta|lia].
Qed.

Lemma sem_tm_lc : forall t K k theta gamma,
  lc_tm_at K k t ->
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (gamma x)) ->
  lc_tm_at K k (sem_tm theta gamma t).
Proof.
  intros t K k theta gamma H; induction H; intros Htheta Hgamma;
    simpl; eauto with core.
  - eapply lc_tm_mono; [apply Hgamma|lia|lia].
  - constructor; eauto using sem_ty_lc.
  - constructor; eauto using sem_ty_lc.
Qed.

Lemma open_ty_closed_id : forall T K,
  lc_ty_at K T -> forall q U, K <= q -> open_ty_rec q U T = T.
Proof.
  intros T K H; induction H; intros q U Hk; simpl; f_equal; eauto; try lia.
  - assert (q =? i = false) as E by (apply Nat.eqb_neq; lia).
    rewrite E. reflexivity.
  - apply IHlc_ty_at. lia.
Qed.

Lemma open_tm_closed_id : forall t K j,
  lc_tm_at K j t -> forall q u, j <= q -> open_tm_rec q u t = t.
Proof.
  intros t K j H; induction H; intros q u Hk; simpl; f_equal; eauto; try lia.
  - assert (q =? i = false) as E by (apply Nat.eqb_neq; lia).
    rewrite E. reflexivity.
  - apply IHlc_tm_at. lia.
Qed.

Lemma open_tm_ty_closed_id : forall t K j,
  lc_tm_at K j t -> forall q U, K <= q -> open_tm_ty_rec q U t = t.
Proof.
  intros t K j H; induction H; intros q U Hk; simpl; f_equal; eauto; try lia.
  - eapply open_ty_closed_id; eassumption.
  - apply IHlc_tm_at. lia.
  - eapply open_ty_closed_id; eassumption.
Qed.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => fv_tm b
  | tm_app f a => fv_tm f ++ fv_tm a
  | tm_tabs b => fv_tm b
  | tm_tapp f _ => fv_tm f
  | tm_zero => []
  | tm_succ n => fv_tm n
  | tm_natrec n b s => fv_tm n ++ fv_tm b ++ fv_tm s
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_zero => []
  | tm_abs T b => fv_ty T ++ ftv_tm b
  | tm_app f a => ftv_tm f ++ ftv_tm a
  | tm_tabs b => ftv_tm b
  | tm_tapp f T => ftv_tm f ++ fv_ty T
  | tm_succ n => ftv_tm n
  | tm_natrec n b s => ftv_tm n ++ ftv_tm b ++ ftv_tm s
  end.

Lemma sem_ty_open : forall T theta X U q,
  ~ In X (fv_ty T) ->
  (forall Y, locally_closed_ty (theta Y)) -> locally_closed_ty U ->
  sem_ty (ty_env_update theta X U)
    (open_ty_rec q (Ty_FVar X) T) =
  open_ty_rec q U (sem_ty theta T).
Proof.
  induction T as [i|Y|A IHA B IHB|A IHA|];
    intros theta X U q Hfresh Htheta HU; simpl in *.
  - destruct (Nat.eqb q i); simpl; [unfold ty_env_update; rewrite Nat.eqb_refl|]; reflexivity.
  - assert (X <> Y) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold ty_env_update. apply Nat.eqb_neq in H.
    rewrite H. symmetry.
    apply (open_ty_closed_id (theta Y) 0 (Htheta Y) q U). lia.
  - assert (Ha : ~ In X (fv_ty A)).
    { intro H; apply Hfresh. apply in_or_app. left; exact H. }
    assert (Hb : ~ In X (fv_ty B)).
    { intro H; apply Hfresh. apply in_or_app. right; exact H. }
    f_equal; eauto.
  - f_equal. apply IHA; assumption.
  - reflexivity.
Qed.

Lemma sem_tm_open : forall t theta gamma x v q,
  ~ In x (fv_tm t) ->
  (forall y, locally_closed_tm (gamma y)) -> locally_closed_tm v ->
  sem_tm theta (tm_env_update gamma x v)
    (open_tm_rec q (tm_fvar x) t) =
  open_tm_rec q v (sem_tm theta gamma t).
Proof.
  induction t; intros theta gamma x v q Hfresh Hgamma Hv;
    simpl in *.
  - destruct (Nat.eqb q n) eqn:E; simpl.
    + unfold tm_env_update. rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (x <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold tm_env_update. apply Nat.eqb_neq in H.
    rewrite H. symmetry.
    apply (open_tm_closed_id (gamma a) 0 0
      (Hgamma a) q v). lia.
  - f_equal. apply IHt; assumption.
  - assert (Hf : ~ In x (fv_tm t1)).
    { intro H; apply Hfresh. apply in_or_app. left; exact H. }
    assert (Ha : ~ In x (fv_tm t2)).
    { intro H; apply Hfresh. apply in_or_app. right; exact H. }
    f_equal; eauto.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - assert (Hn : ~ In x (fv_tm t1)).
    { intro H; apply Hfresh. apply in_or_app. left; exact H. }
    assert (Hb : ~ In x (fv_tm t2)).
    { intro H; apply Hfresh. apply in_or_app. right. apply in_or_app. left; exact H. }
    assert (Hs : ~ In x (fv_tm t3)).
    { intro H; apply Hfresh. apply in_or_app. right. apply in_or_app. right; exact H. }
    f_equal; eauto.
Qed.

Lemma sem_tm_ty_open : forall t theta gamma X U q,
  ~ In X (ftv_tm t) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  (forall y, locally_closed_tm (gamma y)) -> locally_closed_ty U ->
  sem_tm (ty_env_update theta X U) gamma
    (open_tm_ty_rec q (Ty_FVar X) t) =
  open_tm_ty_rec q U (sem_tm theta gamma t).
Proof.
  induction t; intros theta gamma X U q Hfresh Htheta Hgamma HU;
    simpl in *.
  - reflexivity.
  - symmetry.
    apply (open_tm_ty_closed_id (gamma a) 0 0
      (Hgamma a) q U). lia.
  - assert (Ht : ~ In X (fv_ty t)).
    { intro H; apply Hfresh. apply in_or_app. left; exact H. }
    assert (Hb : ~ In X (ftv_tm t0)).
    { intro H; apply Hfresh. apply in_or_app. right; exact H. }
    f_equal; [apply sem_ty_open; assumption|apply IHt; assumption].
  - assert (Hf : ~ In X (ftv_tm t1)).
    { intro H; apply Hfresh. apply in_or_app. left; exact H. }
    assert (Ha : ~ In X (ftv_tm t2)).
    { intro H; apply Hfresh. apply in_or_app. right; exact H. }
    f_equal; eauto.
  - f_equal. apply IHt; assumption.
  - assert (Hf : ~ In X (ftv_tm t)).
    { intro H; apply Hfresh. apply in_or_app. left; exact H. }
    assert (Ht : ~ In X (fv_ty t0)).
    { intro H; apply Hfresh. apply in_or_app. right; exact H. }
    f_equal; [apply IHt; assumption|apply sem_ty_open; assumption].
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - assert (Hn : ~ In X (ftv_tm t1)).
    { intro H; apply Hfresh. apply in_or_app. left; exact H. }
    assert (Hb : ~ In X (ftv_tm t2)).
    { intro H; apply Hfresh. apply in_or_app. right. apply in_or_app. left; exact H. }
    assert (Hs : ~ In X (ftv_tm t3)).
    { intro H; apply Hfresh. apply in_or_app. right. apply in_or_app. right; exact H. }
    f_equal; eauto.
Qed.

Lemma numeric_evaluates_self : forall n,
  numeric_value n -> forall w, evaluates n w -> w = n.
Proof.
  intros n Hn; induction Hn; intros w He.
  - inversion He; subst; reflexivity.
  - inversion He; subst; try reflexivity.
    f_equal. apply IHHn; assumption.
Qed.

Lemma value_evaluates_self : forall v w,
  value v -> evaluates v w -> w = v.
Proof.
  intros v w Hv He; inversion Hv; subst.
  - inversion He; subst; reflexivity.
  - inversion He; subst; reflexivity.
  - eapply numeric_evaluates_self; eassumption.
Qed.

Lemma evaluates_rec_lift : forall nv n b s vb vs r,
  numeric_value nv -> value vb -> value vs ->
  evaluates n nv -> evaluates b vb -> evaluates s vs ->
  evaluates (tm_natrec nv vb vs) r ->
  evaluates (tm_natrec n b s) r.
Proof.
  intros nv n b s vb vs r Hnv Hvb Hvs Hn Hb Hs Hr.
  destruct Hnv.
  - inversion Hr; subst.
    + inversion H; subst; inversion H0.
    + pose proof (value_evaluates_self _ _ Hvb H4); subst.
      eapply EvalRecZero; eassumption.
    + pose proof (numeric_evaluates_self _ nv_zero _ H2) as E.
      discriminate E.
  - inversion Hr; subst.
    + inversion H; subst; inversion H0.
    + pose proof (numeric_evaluates_self _ (nv_succ _ Hnv) _ H2) as E.
      discriminate E.
    + pose proof (value_evaluates_self _ _ Hvb H4); subst.
      pose proof (value_evaluates_self _ _ Hvs H6); subst.
      pose proof (numeric_evaluates_self _ (nv_succ _ Hnv) _ H2) as E.
      inversion E; subst.
      eapply EvalRecSucc; eassumption.
Qed.

Lemma expression_rec : forall eta rho T n1 n2 b1 b2 s1 s2,
  expression_relation eta rho Ty_Nat n1 n2 ->
  expression_relation eta rho T b1 b2 ->
  expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 s2 ->
  expression_relation eta rho T
    (tm_natrec n1 b1 s1) (tm_natrec n2 b2 s2).
Proof.
  intros eta rho T n1 n2 b1 b2 s1 s2 Hn Hb Hs.
  destruct Hn as [Hln1 [Hln2 [vn1 [vn2 [Hen1 [Hen2 [En Hnv]]]]]]].
  subst vn2.
  destruct Hb as [Hlb1 [Hlb2 [vb1 [vb2 [Heb1 [Heb2 Hrb]]]]]].
  destruct Hs as [Hls1 [Hls2 [vs1 [vs2 [Hes1 [Hes2 Hrs]]]]]].
  pose proof (value_relation_values _ _ _ _ _ Hrb) as [Hvb1 Hvb2].
  pose proof (value_relation_values _ _ _ _ _ Hrs) as [Hvs1 Hvs2].
  pose proof (related_rec_values _ _ _ _ _ _ _ _ Hnv Hrb Hrs) as Hrec.
  destruct Hrec as [_ [_ [r1 [r2 [Her1 [Her2 Hr]]]]]].
  unfold expression_relation, expression_lifting, results_match.
  split; [apply lc_tm_rec; assumption|].
  split; [apply lc_tm_rec; assumption|].
  exists r1, r2. repeat split; try assumption.
  - eapply (evaluates_rec_lift vn1 n1 b1 s1 vb1 vs1 r1); eassumption.
  - eapply (evaluates_rec_lift vn1 n2 b2 s2 vb2 vs2 r2); eassumption.
Qed.

Fixpoint fv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => fv_ty T ++ fv_context Gamma'
  end.

Lemma lookup_fv_context : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  ~ In X (fv_context Gamma) -> ~ In X (fv_ty T).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlook Hfresh;
    simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst. intro H.
    apply Hfresh. apply in_or_app. left; exact H.
  - apply (IH x T X Hlook). intro H.
    apply Hfresh. apply in_or_app. right; exact H.
Qed.

Lemma value_relation_rho_update : forall T eta rho X cand v1 v2,
  ~ In X (fv_ty T) ->
  value_relation eta rho T v1 v2 <->
  value_relation eta (relation_update rho X cand) T v1 v2.
Proof.
  induction T as [i|Y|A IHA B IHB|A IHA|];
    intros eta rho X cand v1 v2 Hfresh; simpl in *.
  - tauto.
  - assert (X <> Y) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold relation_update. apply Nat.eqb_neq in H.
    rewrite H. tauto.
  - assert (Ha : ~ In X (fv_ty A)).
    { intro H; apply Hfresh. apply in_or_app. left; exact H. }
    assert (Hb : ~ In X (fv_ty B)).
    { intro H; apply Hfresh. apply in_or_app. right; exact H. }
    split; intros [Hv1 [Hv2 [U1 [b1 [U2 [b2 [E1 [E2 Hbody]]]]]]]].
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, b1, U2, b2. split; [exact E1|]. split; [exact E2|].
      intros z1 z2 Hz.
      apply (proj1 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHB eta rho X cand r1 r2 Hb))).
      apply Hbody. apply (proj2 (IHA eta rho X cand z1 z2 Ha)). exact Hz.
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, b1, U2, b2. split; [exact E1|]. split; [exact E2|].
      intros z1 z2 Hz.
      apply (proj2 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHB eta rho X cand r1 r2 Hb))).
      apply Hbody. apply (proj1 (IHA eta rho X cand z1 z2 Ha)). exact Hz.
  - split; intros [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hbody]]]]]].
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 c HU1 HU2.
      apply (proj1 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHA (c :: eta) rho X cand r1 r2 Hfresh))).
      apply Hbody; assumption.
    + split; [exact Hv1|]. split; [exact Hv2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 c HU1 HU2.
      apply (proj2 (expression_lifting_ext _ _ _ _
        (fun r1 r2 => IHA (c :: eta) rho X cand r1 r2 Hfresh))).
      apply Hbody; assumption.
  - tauto.
Qed.

Theorem fundamental_relation : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta1 theta2 gamma1 gamma2 rho,
    (forall X, locally_closed_ty (theta1 X) /\ locally_closed_ty (theta2 X)) ->
    (forall x, locally_closed_tm (gamma1 x) /\ locally_closed_tm (gamma2 x)) ->
    (forall x U, lookup_context x Gamma = Some U ->
      value_relation [] rho U (gamma1 x) (gamma2 x)) ->
    expression_relation [] rho T
      (sem_tm theta1 gamma1 t) (sem_tm theta2 gamma2 t).
Proof.
  intros Delta Gamma t T Htyping; induction Htyping;
    intros theta1 theta2 gamma1 gamma2 rho Htheta Hgamma Henv;
    simpl.
  - apply related_values_as_expression. apply Henv. assumption.
  - set (x := fresh (L ++ fv_tm t2)).
    assert (HxL : ~ In x L).
    { unfold x. intro Hin; apply (fresh_not_in (L ++ fv_tm t2)).
      apply in_or_app. left; exact Hin. }
    assert (HxF : ~ In x (fv_tm t2)).
    { unfold x. intro Hin; apply (fresh_not_in (L ++ fv_tm t2)).
      apply in_or_app. right; exact Hin. }
    assert (Hcl1 : locally_closed_tm (sem_tm theta1 gamma1 (tm_abs T1 t2))).
    { eapply sem_tm_lc; [eapply has_type_lc; eapply T_Abs; eauto|..
      ]; [intros X; apply Htheta|intros y; apply Hgamma]. }
    assert (Hcl2 : locally_closed_tm (sem_tm theta2 gamma2 (tm_abs T1 t2))).
    { eapply sem_tm_lc; [eapply has_type_lc; eapply T_Abs; eauto|..
      ]; [intros X; apply Htheta|intros y; apply Hgamma]. }
    apply related_values_as_expression.
    simpl. split; [apply v_abs; exact Hcl1|].
    split; [apply v_abs; exact Hcl2|].
    exists (sem_ty theta1 T1), (sem_tm theta1 gamma1 t2),
      (sem_ty theta2 T1), (sem_tm theta2 gamma2 t2).
    split; [reflexivity|]. split; [reflexivity|].
    intros a1 a2 Ha.
    pose proof (value_relation_values _ _ _ _ _ Ha) as [Hva1 Hva2].
    pose proof (H1 x HxL theta1 theta2
      (tm_env_update gamma1 x a1) (tm_env_update gamma2 x a2)
      rho Htheta) as Hbody.
    assert (Hg' : forall y,
      locally_closed_tm (tm_env_update gamma1 x a1 y) /\
      locally_closed_tm (tm_env_update gamma2 x a2 y)).
    { intro y. unfold tm_env_update.
      destruct (Nat.eqb x y);
        [split; apply value_lc; assumption|apply Hgamma]. }
    specialize (Hbody Hg').
    assert (He' : forall y U,
      lookup_context y (update Gamma x T1) = Some U ->
      value_relation [] rho U
        (tm_env_update gamma1 x a1 y)
        (tm_env_update gamma2 x a2 y)).
    { intros y U Hy. unfold update in Hy. simpl in Hy.
      destruct (Nat.eqb y x) eqn:E.
      - apply Nat.eqb_eq in E; subst. inversion Hy; subst.
        unfold tm_env_update. rewrite Nat.eqb_refl. exact Ha.
      - assert (Nat.eqb x y = false) as E' by
          (rewrite Nat.eqb_sym; exact E).
        unfold tm_env_update. rewrite E'. apply Henv; exact Hy. }
    specialize (Hbody He').
    unfold open_tm in Hbody.
    rewrite (sem_tm_open t2 theta1 gamma1 x a1 0 HxF
      (fun y => proj1 (Hgamma y)) (value_lc _ Hva1)) in Hbody.
    rewrite (sem_tm_open t2 theta2 gamma2 x a2 0 HxF
      (fun y => proj2 (Hgamma y)) (value_lc _ Hva2)) in Hbody.
    exact Hbody.
  - eapply expression_app; eauto.
  - set (X := fresh (L ++ ftv_tm t ++ fv_ty T ++ fv_context Gamma)).
    assert (HXL : ~ In X L).
    { unfold X. intro Hin. apply (fresh_not_in (L ++ ftv_tm t ++ fv_ty T ++ fv_context Gamma)).
      apply in_or_app. left; exact Hin. }
    assert (HXF : ~ In X (ftv_tm t)).
    { unfold X. intro Hin. apply (fresh_not_in (L ++ ftv_tm t ++ fv_ty T ++ fv_context Gamma)).
      apply in_or_app. right. apply in_or_app. left; exact Hin. }
    assert (HXT : ~ In X (fv_ty T)).
    { unfold X. intro Hin. apply (fresh_not_in (L ++ ftv_tm t ++ fv_ty T ++ fv_context Gamma)).
      apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left; exact Hin. }
    assert (HXC : ~ In X (fv_context Gamma)).
    { unfold X. intro Hin. apply (fresh_not_in (L ++ ftv_tm t ++ fv_ty T ++ fv_context Gamma)).
      apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right; exact Hin. }
    assert (HlcT : lc_ty_at 1 T).
    { eapply lc_ty_open_inv with (X := X).
      eapply has_type_result_lc. apply H; exact HXL. }
    assert (Hcl1 : locally_closed_tm (sem_tm theta1 gamma1 (tm_tabs t))).
    { eapply sem_tm_lc; [eapply has_type_lc; eapply T_TAbs; eauto|..
      ]; [intros Y; apply Htheta|intros y; apply Hgamma]. }
    assert (Hcl2 : locally_closed_tm (sem_tm theta2 gamma2 (tm_tabs t))).
    { eapply sem_tm_lc; [eapply has_type_lc; eapply T_TAbs; eauto|..
      ]; [intros Y; apply Htheta|intros y; apply Hgamma]. }
    apply related_values_as_expression.
    simpl. split; [apply v_tabs; exact Hcl1|].
    split; [apply v_tabs; exact Hcl2|].
    exists (sem_tm theta1 gamma1 t), (sem_tm theta2 gamma2 t).
    split; [reflexivity|]. split; [reflexivity|].
    intros U1 U2 cand HU1 HU2.
    assert (Hth' : forall Y,
      locally_closed_ty (ty_env_update theta1 X U1 Y) /\
      locally_closed_ty (ty_env_update theta2 X U2 Y)).
    { intro Y. unfold ty_env_update.
      destruct (Nat.eqb X Y); [exact (conj HU1 HU2)|apply Htheta]. }
    assert (He' : forall y A, lookup_context y Gamma = Some A ->
      value_relation [] (relation_update rho X cand) A (gamma1 y) (gamma2 y)).
    { intros y A Hy. apply (proj1 (value_relation_rho_update A [] rho X cand _ _
        (lookup_fv_context Gamma y A X Hy HXC))).
      apply Henv; exact Hy. }
    pose proof (H0 X HXL
      (ty_env_update theta1 X U1) (ty_env_update theta2 X U2)
      gamma1 gamma2 (relation_update rho X cand)
      Hth' Hgamma He') as Hbody.
    unfold open_tm_ty in Hbody.
    rewrite (sem_tm_ty_open t theta1 gamma1 X U1 0 HXF
      (fun Y => proj1 (Htheta Y)) (fun y => proj1 (Hgamma y)) HU1)
      in Hbody.
    rewrite (sem_tm_ty_open t theta2 gamma2 X U2 0 HXF
      (fun Y => proj2 (Htheta Y)) (fun y => proj2 (Hgamma y)) HU2)
      in Hbody.
    apply (proj2 (expression_lifting_ext _ _ _ _
      (fun r1 r2 => value_relation_open_fvar T [] [] rho X cand
        r1 r2 HlcT HXT))).
    exact Hbody.
  - pose proof (IHHtyping theta1 theta2 gamma1 gamma2 rho
      Htheta Hgamma Henv) as Hf.
    assert (HUlc : lc_ty_at 0 U) by (eapply wf_ty_lc; eassumption).
    assert (Hcl1 : locally_closed_ty (sem_ty theta1 U)).
    { eapply sem_ty_lc; [exact HUlc|intros Y; apply Htheta]. }
    assert (Hcl2 : locally_closed_ty (sem_ty theta2 U)).
    { eapply sem_ty_lc; [exact HUlc|intros Y; apply Htheta]. }
    pose proof (expression_tapp [] rho T _ _
      (sem_ty theta1 U) (sem_ty theta2 U)
      (type_candidate rho U) Hf Hcl1 Hcl2) as Hresult.
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (has_type_result_lc _ _ _ _ Htyping) as Hlc.
      inversion Hlc; assumption. }
    apply (proj1 (expression_lifting_ext _ _ _ _
      (fun r1 r2 => value_relation_open_ty T [] [] rho U
        r1 r2 HlcT HUlc))). exact Hresult.
  - apply related_values_as_expression. simpl. split; [reflexivity|constructor].
  - apply expression_succ. apply IHHtyping; assumption.
  - eapply expression_rec; eauto.
Qed.

Lemma sem_ty_id : forall T, sem_ty Ty_FVar T = T.
Proof.
  induction T; simpl; f_equal; auto.
Qed.

Lemma sem_tm_id : forall t, sem_tm Ty_FVar tm_fvar t = t.
Proof.
  induction t; simpl; f_equal; eauto using sem_ty_id.
Qed.

Definition singleton_candidate (v : tm) (Hv : value v) : binary_candidate.
Proof.
  refine {| candidate_relation := fun x y => x = v /\ y = v |}.
  intros x y [-> ->]. split; assumption.
Defined.

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t Ht U v HU Hv Hvt.
  pose (rho := fun _ : atom => @None binary_candidate).
  assert (Hfund : expression_relation [] rho
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) t t).
  { pose proof (fundamental_relation _ _ _ _ Ht
      Ty_FVar Ty_FVar tm_fvar tm_fvar rho) as H.
    assert (Htheta : forall X,
      locally_closed_ty (Ty_FVar X) /\ locally_closed_ty (Ty_FVar X)).
    { intro X. split; constructor. }
    assert (Hgamma : forall x,
      locally_closed_tm (tm_fvar x) /\ locally_closed_tm (tm_fvar x)).
    { intro x. split; constructor. }
    specialize (H Htheta Hgamma).
    assert (Henv : forall x A,
      lookup_context x empty = Some A ->
      value_relation [] rho A (tm_fvar x) (tm_fvar x)).
    { intros x A Hlook. discriminate Hlook. }
    specialize (H Henv).
    rewrite !sem_tm_id in H. exact H. }
  pose (a := singleton_candidate v Hv).
  assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eassumption).
  pose proof (expression_tapp [] rho
    (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))
    t t U U a Hfund HUlc HUlc) as Htapp.
  assert (Harg : expression_relation [a] rho (Ty_BVar 0) v v).
  { apply related_values_as_expression. simpl.
    unfold a, singleton_candidate. simpl. auto. }
  pose proof (expression_app [a] rho (Ty_BVar 0) (Ty_BVar 0)
    (tm_tapp t U) (tm_tapp t U) v v Htapp Harg) as Happ.
  destruct Happ as [Hlc [_ [w1 [w2 [He1 [_ Hr]]]]]].
  simpl in Hr. unfold a, singleton_candidate in Hr. simpl in Hr.
  destruct Hr as [-> _].
  eapply evaluates_multi; eassumption.
Qed.

End SystemFParametricityRecursionMediumTask.
