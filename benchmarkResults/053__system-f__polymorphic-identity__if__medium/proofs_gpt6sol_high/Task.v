(** System F parametricity benchmark, Medium variant.
    Features: if. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfMediumTask.

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


Hint Constructors lc_ty_at lc_tm_at value : core.

Inductive evaluates : tm -> tm -> Prop :=
  | EvalValue : forall v, value v -> evaluates v v
  | EvalApp : forall f arg U body v result,
      evaluates f (tm_abs U body) -> evaluates arg v ->
      evaluates (open_tm body v) result -> evaluates (tm_app f arg) result
  | EvalTApp : forall f U body result,
      evaluates f (tm_tabs body) -> locally_closed_ty U ->
      evaluates (open_tm_ty body U) result -> evaluates (tm_tapp f U) result
  | EvalIfTrue : forall c t u v,
      evaluates c tm_true -> evaluates t v -> locally_closed_tm u ->
      evaluates (tm_if c t u) v
  | EvalIfFalse : forall c t u v,
      evaluates c tm_false -> locally_closed_tm t -> evaluates u v ->
      evaluates (tm_if c t u) v.

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
  | Ty_Bool => (v1 = tm_true /\ v2 = tm_true) \/ (v1 = tm_false /\ v2 = tm_false)
  end.

Definition expression_relation eta rho T t1 t2 :=
  expression_lifting (value_relation eta rho T) t1 t2.

Lemma lc_ty_open_inverse : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in H;
    try solve [constructor; inversion H; subst; eauto].
  destruct (Nat.eqb k n) eqn:E.
  - apply Nat.eqb_eq in E; subst; constructor; lia.
  - inversion H; subst; constructor; lia.
Qed.

Lemma lc_tm_open_inverse : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H;
    try solve [constructor; inversion H; subst; eauto].
  destruct (Nat.eqb k n) eqn:E.
  - apply Nat.eqb_eq in E; subst; constructor; lia.
  - inversion H; subst; constructor; lia.
Qed.

Lemma lc_tm_ty_open_inverse : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H;
    try solve [constructor; inversion H; subst; eauto using lc_ty_open_inverse].
Qed.

Definition fresh_atom (L : list atom) := S (fold_right Nat.max 0 L).

Lemma fresh_atom_not_in : forall L, ~ In (fresh_atom L) L.
Proof.
  assert (Hbound : forall L x, In x L -> x <= fold_right Nat.max 0 L).
  { induction L as [|a L IH]; simpl; intros x H; [contradiction|].
    destruct H as [<-|H]; [lia| specialize (IH x H); lia]. }
  intros L H; unfold fresh_atom in H.
  specialize (Hbound L (S (fold_right Nat.max 0 L)) H); lia.
Qed.

Lemma wf_ty_closed : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H;
    try solve [constructor; eauto].
  constructor. eapply lc_ty_open_inverse.
  apply H0, fresh_atom_not_in.
Qed.

Fixpoint close_ty (sigma : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sigma X
  | Ty_Arrow A B => Ty_Arrow (close_ty sigma A) (close_ty sigma B)
  | Ty_All A => Ty_All (close_ty sigma A)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint close_tm (theta : atom -> tm) (sigma : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => theta x
  | tm_abs A body => tm_abs (close_ty sigma A) (close_tm theta sigma body)
  | tm_app f arg => tm_app (close_tm theta sigma f) (close_tm theta sigma arg)
  | tm_tabs body => tm_tabs (close_tm theta sigma body)
  | tm_tapp f A => tm_tapp (close_tm theta sigma f) (close_ty sigma A)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if c a b => tm_if (close_tm theta sigma c)
                                (close_tm theta sigma a) (close_tm theta sigma b)
  end.

Definition change {A} (env : atom -> A) (x : atom) (a : A) : atom -> A :=
  fun y => if Nat.eqb x y then a else env y.

Fixpoint free_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => [] | Ty_FVar X => [X]
  | Ty_Arrow A B => free_ty A ++ free_ty B
  | Ty_All A => free_ty A | Ty_Bool => []
  end.

Fixpoint free_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => [] | tm_fvar x => [x]
  | tm_abs _ b | tm_tabs b => free_tm b
  | tm_app a b => free_tm a ++ free_tm b
  | tm_tapp a _ => free_tm a
  | tm_true | tm_false => []
  | tm_if a b c => free_tm a ++ free_tm b ++ free_tm c
  end.

Fixpoint free_tm_ty (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs A b => free_ty A ++ free_tm_ty b
  | tm_app a b => free_tm_ty a ++ free_tm_ty b
  | tm_tabs b => free_tm_ty b
  | tm_tapp a A => free_tm_ty a ++ free_ty A
  | tm_true | tm_false => []
  | tm_if a b c => free_tm_ty a ++ free_tm_ty b ++ free_tm_ty c
  end.

Lemma lc_ty_mono : forall T K K', K <= K' ->
  lc_ty_at K T -> lc_ty_at K' T.
Proof.
  induction T; intros K K' Hle H; inversion H; subst.
  - constructor; lia.
  - constructor.
  - constructor; eauto.
  - constructor. apply (IHT (S K) (S K')); [lia|assumption].
  - constructor.
Qed.

Lemma closed_ty_at : forall T K, locally_closed_ty T -> lc_ty_at K T.
Proof.
  intros T K H; apply (lc_ty_mono T 0 K); [lia|exact H].
Qed.

Lemma lc_tm_mono : forall t K k K' k', K <= K' -> k <= k' ->
  lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  induction t; intros K k K' k' HK Hk H; inversion H; subst;
    try solve [constructor; eauto using lc_ty_mono; lia].
  - constructor.
    + apply (lc_ty_mono t K K'); assumption.
    + apply (IHt K (S k) K' (S k')); [assumption|lia|assumption].
  - constructor. apply (IHt (S K) k (S K') k'); [lia|assumption|assumption].
Qed.

Lemma closed_tm_at : forall t K k, locally_closed_tm t -> lc_tm_at K k t.
Proof.
  intros t K k H; apply (lc_tm_mono t 0 0 K k); [lia|lia|exact H].
Qed.

Lemma close_ty_lc : forall T K sigma,
  lc_ty_at K T -> (forall X, locally_closed_ty (sigma X)) ->
  lc_ty_at K (close_ty sigma T).
Proof.
  induction T; intros K sigma H Hsigma; inversion H; subst; simpl;
    try solve [constructor; eauto using closed_ty_at].
  apply closed_ty_at, Hsigma.
Qed.

Lemma close_tm_lc : forall t K k theta sigma,
  lc_tm_at K k t ->
  (forall x, locally_closed_tm (theta x)) ->
  (forall X, locally_closed_ty (sigma X)) ->
  lc_tm_at K k (close_tm theta sigma t).
Proof.
  induction t; intros K k theta sigma H Htheta Hsigma;
    inversion H; subst; simpl;
    try solve [constructor; eauto using closed_tm_at, close_ty_lc].
  apply closed_tm_at, Htheta.
Qed.

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; subst; eauto; constructor. Qed.

Lemma typed_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H;
    try solve [constructor; eauto using wf_ty_closed].
  - apply lc_tm_abs.
    + apply (wf_ty_closed Delta T1); assumption.
    + apply (lc_tm_open_inverse t2 0 0 (fresh_atom L)).
      apply H1, fresh_atom_not_in.
  - apply lc_tm_tabs. apply (lc_tm_ty_open_inverse t 0 0 (fresh_atom L)).
    apply H0, fresh_atom_not_in.
  - apply lc_tm_tapp; [assumption|apply (wf_ty_closed Delta U); assumption].
Qed.

Lemma open_ty_inert : forall T k U,
  lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  induction T; intros k U H; inversion H; subst; simpl;
    try solve [f_equal; eauto].
  assert (k <> n) by lia. apply Nat.eqb_neq in H0. now rewrite H0.
Qed.

Lemma open_tm_inert : forall t K k u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  induction t; intros K k u H; inversion H; subst; simpl;
    try solve [f_equal; eauto].
  assert (k <> n) by lia. apply Nat.eqb_neq in H0. now rewrite H0.
Qed.

Lemma open_tm_ty_inert : forall t K k U,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  induction t; intros K k U H; inversion H; subst; simpl;
    try solve [f_equal; eauto using open_ty_inert].
Qed.

Lemma close_ty_update : forall T sigma X U,
  ~ In X (free_ty T) ->
  close_ty (change sigma X U) T = close_ty sigma T.
Proof.
  induction T; intros sigma X U H; simpl in *; try reflexivity.
  - unfold change; destruct (Nat.eqb X a) eqn:E; [apply Nat.eqb_eq in E; subst; tauto|reflexivity].
  - rewrite in_app_iff in H. assert (H1 : ~ In X (free_ty T1)) by tauto.
    assert (H2 : ~ In X (free_ty T2)) by tauto.
    now rewrite (IHT1 _ _ _ H1), (IHT2 _ _ _ H2).
  - now rewrite (IHT _ _ _ H).
Qed.

Lemma close_tm_update : forall t theta sigma x v,
  ~ In x (free_tm t) ->
  close_tm (change theta x v) sigma t = close_tm theta sigma t.
Proof.
  induction t; intros theta sigma x v H; simpl in *; try reflexivity.
  - unfold change; destruct (Nat.eqb x a) eqn:E; [apply Nat.eqb_eq in E; subst; tauto|reflexivity].
  - now rewrite (IHt _ _ _ _ H).
  - rewrite in_app_iff in H.
    assert (H1 : ~ In x (free_tm t1)) by tauto.
    assert (H2 : ~ In x (free_tm t2)) by tauto.
    now rewrite (IHt1 _ _ _ _ H1), (IHt2 _ _ _ _ H2).
  - now rewrite (IHt _ _ _ _ H).
  - now rewrite (IHt _ _ _ _ H).
  - repeat rewrite in_app_iff in H.
    assert (H1 : ~ In x (free_tm t1)) by tauto.
    assert (H2 : ~ In x (free_tm t2)) by tauto.
    assert (H3 : ~ In x (free_tm t3)) by tauto.
    now rewrite (IHt1 _ _ _ _ H1), (IHt2 _ _ _ _ H2), (IHt3 _ _ _ _ H3).
Qed.

Lemma close_tm_type_update : forall t theta sigma X U,
  ~ In X (free_tm_ty t) ->
  close_tm theta (change sigma X U) t = close_tm theta sigma t.
Proof.
  induction t; intros theta sigma X U H; simpl in *; try reflexivity.
  - rewrite in_app_iff in H.
    assert (H1 : ~ In X (free_ty t)) by tauto.
    assert (H2 : ~ In X (free_tm_ty t0)) by tauto.
    now rewrite (close_ty_update _ _ _ _ H1), (IHt _ _ _ _ H2).
  - rewrite in_app_iff in H.
    assert (H1 : ~ In X (free_tm_ty t1)) by tauto.
    assert (H2 : ~ In X (free_tm_ty t2)) by tauto.
    now rewrite (IHt1 _ _ _ _ H1), (IHt2 _ _ _ _ H2).
  - now rewrite (IHt _ _ _ _ H).
  - rewrite in_app_iff in H.
    assert (H1 : ~ In X (free_tm_ty t)) by tauto.
    assert (H2 : ~ In X (free_ty t0)) by tauto.
    now rewrite (IHt _ _ _ _ H1), (close_ty_update _ _ _ _ H2).
  - repeat rewrite in_app_iff in H.
    assert (H1 : ~ In X (free_tm_ty t1)) by tauto.
    assert (H2 : ~ In X (free_tm_ty t2)) by tauto.
    assert (H3 : ~ In X (free_tm_ty t3)) by tauto.
    now rewrite (IHt1 _ _ _ _ H1), (IHt2 _ _ _ _ H2), (IHt3 _ _ _ _ H3).
Qed.

Lemma close_ty_open : forall T k sigma X,
  (forall Y, locally_closed_ty (sigma Y)) ->
  close_ty sigma (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k (sigma X) (close_ty sigma T).
Proof.
  induction T; intros k sigma X Hsigma; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry; apply open_ty_inert, closed_ty_at, Hsigma.
  - now rewrite (IHT1 _ _ _ Hsigma), (IHT2 _ _ _ Hsigma).
  - now rewrite (IHT _ _ _ Hsigma).
Qed.

Lemma close_tm_open : forall t k theta sigma x,
  (forall y, locally_closed_tm (theta y)) ->
  close_tm theta sigma (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (theta x) (close_tm theta sigma t).
Proof.
  induction t; intros k theta sigma x Htheta; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry; apply open_tm_inert with (K := 0).
    apply closed_tm_at, Htheta.
  - now rewrite (IHt _ _ _ _ Htheta).
  - now rewrite (IHt1 _ _ _ _ Htheta), (IHt2 _ _ _ _ Htheta).
  - now rewrite (IHt _ _ _ _ Htheta).
  - now rewrite (IHt _ _ _ _ Htheta).
  - now rewrite (IHt1 _ _ _ _ Htheta), (IHt2 _ _ _ _ Htheta), (IHt3 _ _ _ _ Htheta).
Qed.

Lemma close_tm_ty_open : forall t K theta sigma X,
  (forall y, locally_closed_tm (theta y)) ->
  (forall Y, locally_closed_ty (sigma Y)) ->
  close_tm theta sigma (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K (sigma X) (close_tm theta sigma t).
Proof.
  induction t; intros K theta sigma X Htheta Hsigma; simpl; try reflexivity.
  - symmetry; apply open_tm_ty_inert with (k := 0).
    apply closed_tm_at, Htheta.
  - now rewrite (close_ty_open _ _ _ _ Hsigma), (IHt _ _ _ _ Htheta Hsigma).
  - now rewrite (IHt1 _ _ _ _ Htheta Hsigma), (IHt2 _ _ _ _ Htheta Hsigma).
  - now rewrite (IHt _ _ _ _ Htheta Hsigma).
  - now rewrite (IHt _ _ _ _ Htheta Hsigma), (close_ty_open _ _ _ _ Hsigma).
  - now rewrite (IHt1 _ _ _ _ Htheta Hsigma),
      (IHt2 _ _ _ _ Htheta Hsigma), (IHt3 _ _ _ _ Htheta Hsigma).
Qed.

Lemma lifting_ext : forall R S t1 t2,
  (forall v1 v2, R v1 v2 <-> S v1 v2) ->
  expression_lifting R t1 t2 <-> expression_lifting S t1 t2.
Proof.
  intros R S t1 t2 Heq; unfold expression_lifting, results_match.
  split; intros [H1 [H2 [v1 [v2 [E1 [E2 H]]]]]];
    repeat split; eauto; exists v1, v2; repeat split; eauto;
    apply Heq; assumption.
Qed.

Lemma value_relation_open : forall T k prefix eta rho X a v1 v2,
  length prefix = k ->
  lc_ty_at (S k) T ->
  ~ In X (free_ty T) ->
  (value_relation (prefix ++ a :: eta) rho T v1 v2 <->
   value_relation (prefix ++ eta) (relation_update rho X a)
     (open_ty_rec k (Ty_FVar X) T) v1 v2).
Proof.
  induction T; intros k prefix eta rho X candidate v1 v2 Hlength Hlc Hfresh;
    simpl in *.
  - revert Hlength; inversion Hlc; subst; intros Hlength.
    destruct (Nat.eq_dec n k) as [->|Hneq].
    + rewrite Nat.eqb_refl.
      rewrite nth_error_app2 by lia.
      replace (k - length prefix) with 0 by lia.
      unfold relation_update; simpl; now rewrite Nat.eqb_refl.
    + assert (n < k) by lia.
      assert (E : (k =? n) = false) by (apply Nat.eqb_neq; lia).
      rewrite E.
      rewrite (nth_error_app1 prefix (candidate :: eta)) by lia.
      simpl. now rewrite (nth_error_app1 prefix eta) by lia.
  - unfold relation_update.
    destruct (Nat.eqb X a) eqn:E; [apply Nat.eqb_eq in E; subst; simpl in Hfresh; tauto|reflexivity].
  - revert Hlength; inversion Hlc; subst; intros Hlength.
    assert (Hleft : ~ In X (free_ty T1)) by (rewrite in_app_iff in Hfresh; tauto).
    assert (Hright : ~ In X (free_ty T2)) by (rewrite in_app_iff in Hfresh; tauto).
    specialize (IHT1 k prefix eta rho X candidate) as IHleft.
    specialize (IHT2 k prefix eta rho X candidate) as IHright.
    assert (HL : forall x y,
      value_relation (prefix ++ candidate :: eta) rho T1 x y <->
      value_relation (prefix ++ eta) (relation_update rho X candidate)
        (open_ty_rec k (Ty_FVar X) T1) x y).
    { intros; apply IHleft; assumption. }
    assert (HR : forall x y,
      value_relation (prefix ++ candidate :: eta) rho T2 x y <->
      value_relation (prefix ++ eta) (relation_update rho X candidate)
        (open_ty_rec k (Ty_FVar X) T2) x y).
    { intros; apply IHright; assumption. }
    split; intros [V1 [V2 [A [b1 [B [b2 [E1 [E2 H]]]]]]]].
    + split; [exact V1|]. split; [exact V2|].
      exists A, b1, B, b2. split; [exact E1|]. split; [exact E2|].
      intros left right Harg.
      apply (proj1 (lifting_ext _ _ _ _ HR)).
      apply H, (proj2 (HL _ _)), Harg.
    + split; [exact V1|]. split; [exact V2|].
      exists A, b1, B, b2. split; [exact E1|]. split; [exact E2|].
      intros left right Harg.
      apply (proj2 (lifting_ext _ _ _ _ HR)).
      apply H, (proj1 (HL _ _)), Harg.
  - revert Hlength; inversion Hlc; subst; intros Hlength.
    assert (IH : forall b s r,
      value_relation (b :: prefix ++ candidate :: eta) rho T s r <->
      value_relation (b :: prefix ++ eta) (relation_update rho X candidate)
        (open_ty_rec (S k) (Ty_FVar X) T) s r).
    { intros; change (b :: prefix ++ candidate :: eta)
        with ((b :: prefix) ++ candidate :: eta).
      change (b :: prefix ++ eta) with ((b :: prefix) ++ eta).
      apply IHT; simpl; auto. }
    split; intros [V1 [V2 [b1 [b2 [E1 [E2 H]]]]]].
    + split; [exact V1|]. split; [exact V2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 b HC1 HC2.
      apply (proj1 (lifting_ext _ _ _ _ (IH b))). apply H; assumption.
    + split; [exact V1|]. split; [exact V2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 b HC1 HC2.
      apply (proj2 (lifting_ext _ _ _ _ (IH b))). apply H; assumption.
  - reflexivity.
Qed.

Lemma related_values : forall T eta rho v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  induction T; intros eta rho v1 v2 H; simpl in H.
  - destruct (nth_error eta n) as [a|]; [apply (candidate_values a); exact H|contradiction].
  - destruct (rho a) as [b|]; [apply (candidate_values b); exact H|contradiction].
  - tauto.
  - tauto.
  - destruct H as [[-> ->]|[-> ->]]; auto with core.
Qed.

Lemma relation_fresh : forall T eta rho X a v1 v2,
  ~ In X (free_ty T) ->
  (value_relation eta (relation_update rho X a) T v1 v2 <->
   value_relation eta rho T v1 v2).
Proof.
  induction T; intros eta rho X candidate v1 v2 Hfresh; simpl in *.
  - reflexivity.
  - unfold relation_update.
    destruct (Nat.eqb X a) eqn:E; [apply Nat.eqb_eq in E; subst; tauto|reflexivity].
  - assert (HL : forall x y, value_relation eta (relation_update rho X candidate) T1 x y <->
        value_relation eta rho T1 x y).
    { intros; apply IHT1; rewrite in_app_iff in Hfresh; tauto. }
    assert (HR : forall x y, value_relation eta (relation_update rho X candidate) T2 x y <->
        value_relation eta rho T2 x y).
    { intros; apply IHT2; rewrite in_app_iff in Hfresh; tauto. }
    split; intros [V1 [V2 [A [b1 [B [b2 [E1 [E2 H]]]]]]]].
    + split; [exact V1|]. split; [exact V2|].
      exists A, b1, B, b2. split; [exact E1|]. split; [exact E2|].
      intros left right Harg.
      apply (proj1 (lifting_ext _ _ _ _ HR)).
      apply H, (proj2 (HL _ _)), Harg.
    + split; [exact V1|]. split; [exact V2|].
      exists A, b1, B, b2. split; [exact E1|]. split; [exact E2|].
      intros left right Harg.
      apply (proj2 (lifting_ext _ _ _ _ HR)).
      apply H, (proj1 (HL _ _)), Harg.
  - split; intros [V1 [V2 [b1 [b2 [E1 [E2 H]]]]]].
    + split; [exact V1|]. split; [exact V2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 b HC1 HC2.
      apply (proj1 (lifting_ext _ _ _ _ (fun s r => IHT (b :: eta) rho X candidate s r Hfresh))).
      apply H; assumption.
    + split; [exact V1|]. split; [exact V2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 b HC1 HC2.
      apply (proj2 (lifting_ext _ _ _ _ (fun s r => IHT (b :: eta) rho X candidate s r Hfresh))).
      apply H; assumption.
  - reflexivity.
Qed.

Lemma relation_stack_agree : forall T k eta1 eta2 rho v1 v2,
  lc_ty_at k T ->
  (forall i, i < k -> nth_error eta1 i = nth_error eta2 i) ->
  (value_relation eta1 rho T v1 v2 <-> value_relation eta2 rho T v1 v2).
Proof.
  induction T; intros k eta1 eta2 rho v1 v2 Hlc Hagree; simpl in *.
  - inversion Hlc; subst. now rewrite Hagree by assumption.
  - reflexivity.
  - inversion Hlc; subst.
    assert (HL : forall s r, value_relation eta1 rho T1 s r <-> value_relation eta2 rho T1 s r).
    { intros; apply IHT1 with k; assumption. }
    assert (HR : forall s r, value_relation eta1 rho T2 s r <-> value_relation eta2 rho T2 s r).
    { intros; apply IHT2 with k; assumption. }
    split; intros [V1 [V2 [A [b1 [B [b2 [E1 [E2 H]]]]]]]].
    + split; [exact V1|]. split; [exact V2|].
      exists A, b1, B, b2. split; [exact E1|]. split; [exact E2|].
      intros left right Harg.
      apply (proj1 (lifting_ext _ _ _ _ HR)). apply H, (proj2 (HL _ _)), Harg.
    + split; [exact V1|]. split; [exact V2|].
      exists A, b1, B, b2. split; [exact E1|]. split; [exact E2|].
      intros left right Harg.
      apply (proj2 (lifting_ext _ _ _ _ HR)). apply H, (proj1 (HL _ _)), Harg.
  - inversion Hlc; subst.
    assert (Hbody : forall a s r,
      value_relation (a :: eta1) rho T s r <->
      value_relation (a :: eta2) rho T s r).
    { intros. apply IHT with (k := S k); [assumption|].
      intros [|i] Hi; simpl; [reflexivity|apply Hagree; lia]. }
    split; intros [V1 [V2 [b1 [b2 [E1 [E2 H]]]]]].
    + split; [exact V1|]. split; [exact V2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 a HC1 HC2.
      apply (proj1 (lifting_ext _ _ _ _ (Hbody a))). apply H; assumption.
    + split; [exact V1|]. split; [exact V2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 a HC1 HC2.
      apply (proj2 (lifting_ext _ _ _ _ (Hbody a))). apply H; assumption.
  - reflexivity.
Qed.

Lemma relation_closed_stack : forall U eta1 eta2 rho v1 v2,
  locally_closed_ty U ->
  (value_relation eta1 rho U v1 v2 <-> value_relation eta2 rho U v1 v2).
Proof.
  intros U eta1 eta2 rho v1 v2 H.
  apply (relation_stack_agree U 0 eta1 eta2); [exact H|intros; lia].
Qed.

Definition type_candidate (rho : binary_env) (U : ty) : binary_candidate :=
  {| candidate_relation := value_relation [] rho U;
     candidate_values := related_values U [] rho |}.

Lemma value_relation_subst : forall T k prefix eta rho U v1 v2,
  length prefix = k -> lc_ty_at (S k) T -> locally_closed_ty U ->
  (value_relation (prefix ++ type_candidate rho U :: eta) rho T v1 v2 <->
   value_relation (prefix ++ eta) rho (open_ty_rec k U T) v1 v2).
Proof.
  induction T; intros k prefix eta rho U v1 v2 Hlength Hlc HU; simpl in *.
  - revert Hlength; inversion Hlc; subst; intros Hlength.
    destruct (Nat.eq_dec n k) as [->|Hneq].
    + rewrite Nat.eqb_refl.
      rewrite nth_error_app2 by lia.
      replace (k - length prefix) with 0 by lia.
      simpl. apply relation_closed_stack; assumption.
    + assert (n < k) by lia.
      assert (E : (k =? n) = false) by (apply Nat.eqb_neq; lia).
      rewrite E. rewrite (nth_error_app1 prefix (type_candidate rho U :: eta)) by lia.
      simpl. now rewrite (nth_error_app1 prefix eta) by lia.
  - reflexivity.
  - revert Hlength; inversion Hlc; subst; intros Hlength.
    assert (HL : forall s r,
      value_relation (prefix ++ type_candidate rho U :: eta) rho T1 s r <->
      value_relation (prefix ++ eta) rho (open_ty_rec k U T1) s r).
    { intros; apply IHT1; assumption. }
    assert (HR : forall s r,
      value_relation (prefix ++ type_candidate rho U :: eta) rho T2 s r <->
      value_relation (prefix ++ eta) rho (open_ty_rec k U T2) s r).
    { intros; apply IHT2; assumption. }
    split; intros [V1 [V2 [A [b1 [B [b2 [E1 [E2 H]]]]]]]].
    + split; [exact V1|]. split; [exact V2|].
      exists A, b1, B, b2. split; [exact E1|]. split; [exact E2|].
      intros left right Harg.
      apply (proj1 (lifting_ext _ _ _ _ HR)). apply H, (proj2 (HL _ _)), Harg.
    + split; [exact V1|]. split; [exact V2|].
      exists A, b1, B, b2. split; [exact E1|]. split; [exact E2|].
      intros left right Harg.
      apply (proj2 (lifting_ext _ _ _ _ HR)). apply H, (proj1 (HL _ _)), Harg.
  - revert Hlength; inversion Hlc; subst; intros Hlength.
    assert (Hbody : forall a s r,
      value_relation (a :: prefix ++ type_candidate rho U :: eta) rho T s r <->
      value_relation (a :: prefix ++ eta) rho (open_ty_rec (S k) U T) s r).
    { intros. change (a :: prefix ++ type_candidate rho U :: eta)
        with ((a :: prefix) ++ type_candidate rho U :: eta).
      change (a :: prefix ++ eta) with ((a :: prefix) ++ eta).
      apply IHT; simpl; auto. }
    split; intros [V1 [V2 [b1 [b2 [E1 [E2 H]]]]]].
    + split; [exact V1|]. split; [exact V2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 a HC1 HC2.
      apply (proj1 (lifting_ext _ _ _ _ (Hbody a))). apply H; assumption.
    + split; [exact V1|]. split; [exact V2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros U1 U2 a HC1 HC2.
      apply (proj2 (lifting_ext _ _ _ _ (Hbody a))). apply H; assumption.
  - reflexivity.
Qed.

Lemma open_ty_lc : forall T k U,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; inversion HT; subst; simpl;
    try solve [constructor; eauto].
  destruct (Nat.eqb k n) eqn:E.
  - apply closed_ty_at, HU.
  - constructor; apply Nat.eqb_neq in E; lia.
Qed.

Lemma typed_type_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H.
  - apply (wf_ty_closed Delta T); assumption.
  - apply lc_ty_arrow; [apply (wf_ty_closed Delta T1); assumption|].
    exact (H1 (fresh_atom L) (fresh_atom_not_in L)).
  - inversion IHhas_type1; assumption.
  - apply lc_ty_all. apply (lc_ty_open_inverse T 0 (fresh_atom L)).
    exact (H0 (fresh_atom L) (fresh_atom_not_in L)).
  - apply open_ty_lc; [inversion IHhas_type; assumption|apply (wf_ty_closed Delta U); assumption].
  - constructor.
  - constructor.
  - exact IHhas_type2.
Qed.

Lemma close_ty_open_any : forall T k sigma U,
  (forall X, locally_closed_ty (sigma X)) ->
  close_ty sigma (open_ty_rec k U T) =
  open_ty_rec k (close_ty sigma U) (close_ty sigma T).
Proof.
  induction T; intros k sigma U Hsigma; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry; apply open_ty_inert, closed_ty_at, Hsigma.
  - now rewrite (IHT1 _ _ _ Hsigma), (IHT2 _ _ _ Hsigma).
  - now rewrite (IHT _ _ _ Hsigma).
Qed.

Lemma close_tm_ty_open_any : forall t K theta sigma U,
  (forall y, locally_closed_tm (theta y)) ->
  (forall X, locally_closed_ty (sigma X)) ->
  close_tm theta sigma (open_tm_ty_rec K U t) =
  open_tm_ty_rec K (close_ty sigma U) (close_tm theta sigma t).
Proof.
  induction t; intros K theta sigma U Htheta Hsigma; simpl; try reflexivity.
  - symmetry; apply open_tm_ty_inert with (k := 0).
    apply closed_tm_at, Htheta.
  - now rewrite (close_ty_open_any _ _ _ _ Hsigma), (IHt _ _ _ _ Htheta Hsigma).
  - now rewrite (IHt1 _ _ _ _ Htheta Hsigma), (IHt2 _ _ _ _ Htheta Hsigma).
  - now rewrite (IHt _ _ _ _ Htheta Hsigma).
  - now rewrite (IHt _ _ _ _ Htheta Hsigma), (close_ty_open_any _ _ _ _ Hsigma).
  - now rewrite (IHt1 _ _ _ _ Htheta Hsigma),
      (IHt2 _ _ _ _ Htheta Hsigma), (IHt3 _ _ _ _ Htheta Hsigma).
Qed.

Fixpoint free_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: rest => free_ty T ++ free_context rest
  end.

Lemma lookup_free_context : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  In X (free_ty T) -> In X (free_context Gamma).
Proof.
  induction Gamma as [|[y A] rest IH]; intros x T X Hlookup Hin;
    simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E; [inversion Hlookup; subst; apply in_or_app; auto|].
  apply in_or_app; right; apply (IH x T X); assumption.
Qed.

Definition related_context Gamma theta1 theta2 rho :=
  forall x T, lookup_context x Gamma = Some T ->
    value_relation [] rho T (theta1 x) (theta2 x).

Lemma related_context_update : forall Gamma theta1 theta2 rho x T v1 v2,
  related_context Gamma theta1 theta2 rho ->
  value_relation [] rho T v1 v2 ->
  related_context (update Gamma x T) (change theta1 x v1) (change theta2 x v2) rho.
Proof.
  intros Gamma theta1 theta2 rho x T v1 v2 Henv Harg y A Hlookup.
  simpl in Hlookup; unfold change.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E; subst.
    inversion Hlookup; subst.
    now rewrite Nat.eqb_refl.
  - rewrite Nat.eqb_sym in E. now rewrite E; apply Henv.
Qed.

Lemma related_context_type_update : forall Gamma theta1 theta2 rho X a,
  ~ In X (free_context Gamma) ->
  related_context Gamma theta1 theta2 rho ->
  related_context Gamma theta1 theta2 (relation_update rho X a).
Proof.
  intros Gamma theta1 theta2 rho X a Hfresh Henv x T Hlookup.
  assert (Hno : ~ In X (free_ty T)).
  { intro Hin; apply Hfresh, (lookup_free_context Gamma x T X Hlookup), Hin. }
  apply (proj2 (relation_fresh T [] rho X a _ _ Hno)).
  apply Henv, Hlookup.
Qed.

Lemma closed_instantiation : forall Delta Gamma t T theta sigma,
  has_type Delta Gamma t T ->
  (forall x, locally_closed_tm (theta x)) ->
  (forall X, locally_closed_ty (sigma X)) ->
  locally_closed_tm (close_tm theta sigma t).
Proof.
  intros Delta Gamma t T theta sigma H Htheta Hsigma.
  apply close_tm_lc; auto. apply (typed_closed Delta Gamma t T), H.
Qed.

Theorem fundamental_relation : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta1 theta2 sigma1 sigma2 rho,
    (forall x, locally_closed_tm (theta1 x)) ->
    (forall x, locally_closed_tm (theta2 x)) ->
    (forall X, locally_closed_ty (sigma1 X)) ->
    (forall X, locally_closed_ty (sigma2 X)) ->
    related_context Gamma theta1 theta2 rho ->
    expression_relation [] rho T
      (close_tm theta1 sigma1 t) (close_tm theta2 sigma2 t).
Proof.
  intros Delta Gamma t T Htyping; induction Htyping;
    intros theta1 theta2 sigma1 sigma2 rho Htheta1 Htheta2 Hsigma1 Hsigma2 Henv;
    unfold expression_relation, expression_lifting, results_match.
  - split; [apply Htheta1|]. split; [apply Htheta2|].
    exists (theta1 x), (theta2 x).
    pose proof (Henv x T H) as Hrelated.
    destruct (related_values T [] rho _ _ Hrelated) as [HV1 HV2].
    repeat split; try constructor; assumption.
  - assert (Habs : locally_closed_tm (tm_abs T1 t2)).
    { eapply typed_closed. eapply T_Abs with (L := L); eauto. }
    assert (HV1 : value (tm_abs (close_ty sigma1 T1) (close_tm theta1 sigma1 t2))).
    { constructor. change (locally_closed_tm (close_tm theta1 sigma1 (tm_abs T1 t2))).
      apply close_tm_lc; assumption. }
    assert (HV2 : value (tm_abs (close_ty sigma2 T1) (close_tm theta2 sigma2 t2))).
    { constructor. change (locally_closed_tm (close_tm theta2 sigma2 (tm_abs T1 t2))).
      apply close_tm_lc; assumption. }
    split; [apply value_closed, HV1|].
    split; [apply value_closed, HV2|].
    exists (tm_abs (close_ty sigma1 T1) (close_tm theta1 sigma1 t2)),
      (tm_abs (close_ty sigma2 T1) (close_tm theta2 sigma2 t2)).
    split; [apply EvalValue, HV1|]. split; [apply EvalValue, HV2|].
    simpl. split; [exact HV1|]. split; [exact HV2|].
    exists (close_ty sigma1 T1), (close_tm theta1 sigma1 t2),
      (close_ty sigma2 T1), (close_tm theta2 sigma2 t2).
    split; [reflexivity|]. split; [reflexivity|].
    intros arg1 arg2 Harg.
    set (x := fresh_atom (L ++ free_tm t2)).
    assert (HxL : ~ In x L).
    { intro Hin; apply (fresh_atom_not_in (L ++ free_tm t2)).
      apply in_or_app; left; exact Hin. }
    assert (Hxt : ~ In x (free_tm t2)).
    { intro Hin; apply (fresh_atom_not_in (L ++ free_tm t2)).
      apply in_or_app; right; exact Hin. }
    destruct (related_values T1 [] rho _ _ Harg) as [Harg1 Harg2].
    assert (Hchange1 : forall y, locally_closed_tm (change theta1 x arg1 y)).
    { intros y; unfold change; destruct (Nat.eqb x y); eauto using value_closed. }
    assert (Hchange2 : forall y, locally_closed_tm (change theta2 x arg2 y)).
    { intros y; unfold change; destruct (Nat.eqb x y); eauto using value_closed. }
    specialize (H1 x HxL (change theta1 x arg1) (change theta2 x arg2)
      sigma1 sigma2 rho Hchange1 Hchange2 Hsigma1 Hsigma2
      (related_context_update Gamma theta1 theta2 rho x T1 arg1 arg2 Henv Harg)).
    unfold expression_relation, open_tm in H1.
    rewrite (close_tm_open t2 0 (change theta1 x arg1) sigma1 x Hchange1) in H1.
    rewrite (close_tm_open t2 0 (change theta2 x arg2) sigma2 x Hchange2) in H1.
    rewrite (close_tm_update t2 theta1 sigma1 x arg1 Hxt) in H1.
    rewrite (close_tm_update t2 theta2 sigma2 x arg2 Hxt) in H1.
    unfold change in H1. rewrite Nat.eqb_refl in H1. exact H1.
  - pose proof (IHHtyping1 theta1 theta2 sigma1 sigma2 rho
      Htheta1 Htheta2 Hsigma1 Hsigma2 Henv) as HF.
    pose proof (IHHtyping2 theta1 theta2 sigma1 sigma2 rho
      Htheta1 Htheta2 Hsigma1 Hsigma2 Henv) as HA.
    unfold expression_relation, expression_lifting, results_match in HF, HA.
    destruct HF as [LCf1 [LCf2 [f1 [f2 [Ef1 [Ef2 HF]]]]]].
    destruct HA as [LCa1 [LCa2 [a1 [a2 [Ea1 [Ea2 HA]]]]]].
    destruct HF as [Vf1 [Vf2 [A [b1 [B [b2 [Eq1 [Eq2 Hfun]]]]]]]].
    subst f1 f2.
    destruct (Hfun a1 a2 HA) as [LCb1 [LCb2 [r1 [r2 [Er1 [Er2 HR]]]]]].
    split; [constructor; assumption|]. split; [constructor; assumption|].
    exists r1, r2; split.
    + eapply EvalApp with (U := A) (body := b1) (v := a1); eauto.
    + split; [eapply EvalApp with (U := B) (body := b2) (v := a2); eauto|exact HR].
  - assert (Htabs : locally_closed_tm (tm_tabs t)).
    { eapply typed_closed. eapply T_TAbs with (L := L); eauto. }
    assert (Htype : lc_ty_at 1 T).
    { pose proof (typed_type_closed _ _ _ _ (T_TAbs L Delta Gamma t T H)) as HC.
      inversion HC; assumption. }
    assert (HV1 : value (tm_tabs (close_tm theta1 sigma1 t))).
    { constructor. change (locally_closed_tm (close_tm theta1 sigma1 (tm_tabs t))).
      apply close_tm_lc; assumption. }
    assert (HV2 : value (tm_tabs (close_tm theta2 sigma2 t))).
    { constructor. change (locally_closed_tm (close_tm theta2 sigma2 (tm_tabs t))).
      apply close_tm_lc; assumption. }
    split; [apply value_closed, HV1|]. split; [apply value_closed, HV2|].
    exists (tm_tabs (close_tm theta1 sigma1 t)),
      (tm_tabs (close_tm theta2 sigma2 t)).
    split; [apply EvalValue, HV1|]. split; [apply EvalValue, HV2|].
    simpl. split; [exact HV1|]. split; [exact HV2|].
    exists (close_tm theta1 sigma1 t), (close_tm theta2 sigma2 t).
    split; [reflexivity|]. split; [reflexivity|].
    intros U1 U2 candidate HU1 HU2.
    set (X := fresh_atom (L ++ free_tm_ty t ++ free_ty T ++ free_context Gamma)).
    assert (Hfresh : ~ In X (L ++ free_tm_ty t ++ free_ty T ++ free_context Gamma))
      by apply fresh_atom_not_in.
    assert (HL : ~ In X L) by (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    assert (Ht : ~ In X (free_tm_ty t))
      by (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    assert (HT : ~ In X (free_ty T))
      by (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    assert (HG : ~ In X (free_context Gamma))
      by (intro Hin; apply Hfresh; repeat rewrite in_app_iff; tauto).
    assert (HS1 : forall Y, locally_closed_ty (change sigma1 X U1 Y)).
    { intros Y; unfold change; destruct (Nat.eqb X Y); auto. }
    assert (HS2 : forall Y, locally_closed_ty (change sigma2 X U2 Y)).
    { intros Y; unfold change; destruct (Nat.eqb X Y); auto. }
    pose proof (H0 X HL theta1 theta2 (change sigma1 X U1)
      (change sigma2 X U2) (relation_update rho X candidate)
      Htheta1 Htheta2 HS1 HS2
      (related_context_type_update Gamma theta1 theta2 rho X candidate HG Henv)) as HB.
    unfold expression_relation, open_tm_ty in HB.
    rewrite (close_tm_ty_open t 0 theta1 (change sigma1 X U1) X Htheta1 HS1) in HB.
    rewrite (close_tm_ty_open t 0 theta2 (change sigma2 X U2) X Htheta2 HS2) in HB.
    rewrite (close_tm_type_update t theta1 sigma1 X U1 Ht) in HB.
    rewrite (close_tm_type_update t theta2 sigma2 X U2 Ht) in HB.
    unfold change in HB; rewrite Nat.eqb_refl in HB.
    apply (proj2 (lifting_ext _ _ _ _
      (fun s r => value_relation_open T 0 [] [] rho X candidate s r eq_refl Htype HT))).
    exact HB.
  - pose proof (IHHtyping theta1 theta2 sigma1 sigma2 rho
      Htheta1 Htheta2 Hsigma1 Hsigma2 Henv) as HF.
    unfold expression_relation, expression_lifting, results_match in HF.
    destruct HF as [LCf1 [LCf2 [f1 [f2 [Ef1 [Ef2 HF]]]]]].
    destruct HF as [Vf1 [Vf2 [b1 [b2 [Eq1 [Eq2 Hfun]]]]]].
    subst f1 f2.
    assert (HU : locally_closed_ty U) by (apply (wf_ty_closed Delta U); assumption).
    assert (HU1 : locally_closed_ty (close_ty sigma1 U)).
    { apply close_ty_lc; assumption. }
    assert (HU2 : locally_closed_ty (close_ty sigma2 U)).
    { apply close_ty_lc; assumption. }
    assert (HT : lc_ty_at 1 T).
    { pose proof (typed_type_closed _ _ _ _ Htyping) as HC.
      inversion HC; assumption. }
    specialize (Hfun (close_ty sigma1 U) (close_ty sigma2 U)
      (type_candidate rho U) HU1 HU2).
    apply (proj1 (lifting_ext _ _ _ _
      (fun s r => value_relation_subst T 0 [] [] rho U s r eq_refl HT HU))) in Hfun.
    destruct Hfun as [LCb1 [LCb2 [r1 [r2 [Er1 [Er2 HR]]]]]].
    split; [constructor; assumption|]. split; [constructor; assumption|].
    exists r1, r2; split.
    + eapply EvalTApp with (body := b1); eauto.
    + split; [eapply EvalTApp with (body := b2); eauto|exact HR].
  - split; [constructor|]. split; [constructor|].
    exists tm_true, tm_true. split; [apply EvalValue; constructor|].
    split; [apply EvalValue; constructor|]. simpl; left; auto.
  - split; [constructor|]. split; [constructor|].
    exists tm_false, tm_false. split; [apply EvalValue; constructor|].
    split; [apply EvalValue; constructor|]. simpl; right; auto.
  - pose proof (IHHtyping1 theta1 theta2 sigma1 sigma2 rho
      Htheta1 Htheta2 Hsigma1 Hsigma2 Henv) as HC.
    pose proof (IHHtyping2 theta1 theta2 sigma1 sigma2 rho
      Htheta1 Htheta2 Hsigma1 Hsigma2 Henv) as HA.
    pose proof (IHHtyping3 theta1 theta2 sigma1 sigma2 rho
      Htheta1 Htheta2 Hsigma1 Hsigma2 Henv) as HB.
    unfold expression_relation, expression_lifting, results_match in HC, HA, HB.
    destruct HC as [LCc1 [LCc2 [c1 [c2 [Ec1 [Ec2 HC]]]]]].
    destruct HA as [LCa1 [LCa2 [a1 [a2 [Ea1 [Ea2 HA]]]]]].
    destruct HB as [LCb1 [LCb2 [b1 [b2 [Eb1 [Eb2 HB]]]]]].
    split; [constructor; assumption|]. split; [constructor; assumption|].
    destruct HC as [[-> ->]|[-> ->]].
    + exists a1, a2. split.
      * eapply EvalIfTrue; eauto.
      * split; [eapply EvalIfTrue; eauto|exact HA].
    + exists b1, b2. split.
      * eapply EvalIfFalse; eauto.
      * split; [eapply EvalIfFalse; eauto|exact HB].
Qed.

Lemma open_tm_lc : forall t K k u,
  lc_tm_at K (S k) t -> locally_closed_tm u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  induction t; intros K k u H HU; inversion H; subst; simpl;
    try solve [constructor; eauto].
  destruct (Nat.eqb k n) eqn:E.
  - apply closed_tm_at, HU.
  - constructor; apply Nat.eqb_neq in E; lia.
Qed.

Lemma open_tm_ty_lc : forall t K k U,
  lc_tm_at (S K) k t -> locally_closed_ty U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  induction t; intros K k U H HU; inversion H; subst; simpl;
    try solve [constructor; eauto using open_ty_lc].
Qed.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof.
  intros t v H; induction H; assumption.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; induction H; intros Huv; [exact Huv|].
  eapply multi_step; eauto.
Qed.

Lemma multi_app_left : forall t u arg,
  t -->* u -> locally_closed_tm arg -> tm_app t arg -->* tm_app u arg.
Proof.
  intros t u arg H; induction H; intros Harg; [constructor|].
  eapply multi_step; [apply ST_App1; eassumption|apply IHmulti; assumption].
Qed.

Lemma multi_app_right : forall f t u,
  value f -> t -->* u -> tm_app f t -->* tm_app f u.
Proof.
  intros f t u Hf H; induction H; [constructor|].
  eapply multi_step; [apply ST_App2; eassumption|exact IHmulti].
Qed.

Lemma multi_tapp_context : forall t u U,
  t -->* u -> locally_closed_ty U -> tm_tapp t U -->* tm_tapp u U.
Proof.
  intros t u U H; induction H; intros HU; [constructor|].
  eapply multi_step; [apply ST_TApp; eassumption|apply IHmulti; assumption].
Qed.

Lemma multi_if_context : forall c d a b,
  c -->* d -> locally_closed_tm a -> locally_closed_tm b ->
  tm_if c a b -->* tm_if d a b.
Proof.
  intros c d a b H; induction H; intros Ha Hb; [constructor|].
  eapply multi_step; [apply ST_If; eassumption|apply IHmulti; assumption].
Qed.

Lemma evaluates_multi : forall t v,
  evaluates t v -> locally_closed_tm t -> t -->* v.
Proof.
  intros t v H; induction H; intros Hlc.
  - constructor.
  - inversion Hlc; subst.
    pose proof (evaluates_value _ _ H) as Hf.
    pose proof (evaluates_value _ _ H0) as Harg.
    inversion Hf; subst.
    assert (Hbody : locally_closed_tm (open_tm body v)).
    { apply open_tm_lc; [pose proof (value_closed _ Hf) as Habs; inversion Habs; assumption
      |apply value_closed, Harg]. }
    eapply multi_trans.
    + apply multi_app_left; [apply IHevaluates1; assumption|assumption].
    + eapply multi_trans.
      * apply multi_app_right; [exact Hf|apply IHevaluates2; assumption].
      * eapply multi_step.
        -- apply ST_AppAbs; assumption.
        -- apply IHevaluates3, Hbody.
  - inversion Hlc; subst.
    pose proof (evaluates_value _ _ H) as Hf.
    inversion Hf; subst.
    assert (Hbody : locally_closed_tm (open_tm_ty body U)).
    { apply open_tm_ty_lc; [pose proof (value_closed _ Hf) as Htabs; inversion Htabs; assumption
      |assumption]. }
    eapply multi_trans.
    + apply multi_tapp_context; [apply IHevaluates1; assumption|assumption].
    + eapply multi_step.
      * apply ST_TAppTabs; [apply value_closed, Hf|assumption].
      * apply IHevaluates2, Hbody.
  - inversion Hlc; subst.
    eapply multi_trans.
    + apply multi_if_context; [apply IHevaluates1; assumption|assumption|assumption].
    + eapply multi_step.
      * apply ST_IfTrue; assumption.
      * apply IHevaluates2; assumption.
  - inversion Hlc; subst.
    eapply multi_trans.
    + apply multi_if_context; [apply IHevaluates1; assumption|assumption|assumption].
    + eapply multi_step.
      * apply ST_IfFalse; assumption.
      * apply IHevaluates2; assumption.
Qed.

Lemma close_ty_identity : forall T, close_ty Ty_FVar T = T.
Proof.
  induction T; simpl; congruence.
Qed.

Lemma close_tm_identity : forall t, close_tm tm_fvar Ty_FVar t = t.
Proof.
  induction t; simpl; try rewrite close_ty_identity;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3;
    reflexivity.
Qed.

Definition singleton_candidate (v : tm) (Hv : value v) : binary_candidate.
Proof.
  refine {| candidate_relation := fun a b => a = v /\ b = v |}.
  intros a b [-> ->]; split; assumption.
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
  intros t Htyping U v HU Hv Htypedv.
  assert (HUclosed : locally_closed_ty U) by (apply (wf_ty_closed [] U); assumption).
  pose proof (fundamental_relation [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Htyping
    tm_fvar tm_fvar Ty_FVar Ty_FVar (fun _ => None)
    (fun x => lc_tm_fvar 0 0 x) (fun x => lc_tm_fvar 0 0 x)
    (fun X => lc_ty_fvar 0 X) (fun X => lc_ty_fvar 0 X)) as Hfund.
  assert (Henv : related_context empty tm_fvar tm_fvar (fun _ => None)).
  { intros x T Hlookup; discriminate. }
  specialize (Hfund Henv).
  unfold expression_relation, expression_lifting, results_match in Hfund.
  repeat rewrite close_tm_identity in Hfund.
  destruct Hfund as [Ht1 [Ht2 [w1 [w2 [Et1 [Et2 HAll]]]]]].
  simpl in HAll.
  destruct HAll as [_ [_ [body1 [body2 [E1 [E2 Hforall]]]]]].
  subst w1 w2.
  pose proof (Hforall U U (singleton_candidate v Hv) HUclosed HUclosed) as Hbody.
  destruct Hbody as [Hb1 [Hb2 [f1 [f2 [Ef1 [Ef2 HArrow]]]]]].
  simpl in HArrow.
  destruct HArrow as [_ [_ [A [abody [B [bbody [F1 [F2 Hfun]]]]]]]].
  subst f1 f2.
  specialize (Hfun v v (conj eq_refl eq_refl)).
  destruct Hfun as [Ha1 [Ha2 [r1 [r2 [Er1 [Er2 Hr]]]]]].
  simpl in Hr. destruct Hr as [-> ->].
  apply evaluates_multi.
  - eapply EvalApp with (U := A) (body := abody) (v := v).
    + eapply EvalTApp with (body := body1); eauto.
    + apply EvalValue, Hv.
    + exact Er1.
  - apply lc_tm_app.
    + apply lc_tm_tapp;
        [apply (typed_closed [] empty t (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))), Htyping
        |exact HUclosed].
    + apply value_closed, Hv.
Qed.

End SystemFParametricityIfMediumTask.
