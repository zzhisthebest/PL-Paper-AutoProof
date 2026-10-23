(** System F parametricity benchmark, Hard variant.
    Features: if-nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfNondeterminismHardTask.

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
  | tm_if : tm -> tm -> tm -> tm
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

Notation "'Bool'" := Ty_Bool (in custom systemf_ty at level 0) : systemf_scope.
Notation "'true'" := tm_true (in custom systemf_tm at level 0) : systemf_scope.
Notation "'false'" := tm_false (in custom systemf_tm at level 0) : systemf_scope.
Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm, t3 custom systemf_tm at level 200) : systemf_scope.
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm at level 200) : systemf_scope.

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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2) (open_tm_ty_rec k U t3)
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_subst x s t1) (tm_subst x s t2) (tm_subst x s t3)
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
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 -> lc_tm_at K k (tm_if t1 t2 t3)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

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
      has_type Delta Gamma (tm_if t1 t2 t3) T
  | T_Choice : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma (tm_choice t1 t2) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).


Hint Constructors lc_ty_at lc_tm_at value : core.

(* The relation below is a may-convergence relation.  The two components of
   a related pair are allowed to make different choices, but have to finish
   in related values.  This is the useful direction of the relation for the
   (angelic) choice semantics used here. *)
Definition trel := tm -> tm -> Prop.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => fv_tm t1
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs t1 => fv_tm t1
  | tm_tapp t1 _ => fv_tm t1
  | tm_true => []
  | tm_false => []
  | tm_if t1 t2 t3 => fv_tm t1 ++ fv_tm t2 ++ fv_tm t3
  | tm_choice t1 t2 => fv_tm t1 ++ fv_tm t2
  end.

Definition lc_rel (R : trel) : Prop :=
  forall x y, R x y -> locally_closed_tm x /\ locally_closed_tm y /\
    fv_tm x = [] /\ fv_tm y = [] /\ value x /\ value y.

Fixpoint rel_at (X : atom) (Delta : ty_context) (rho : list trel) : trel :=
  match Delta, rho with
  | [], _ => fun _ _ => False
  | Y :: Delta', R :: rho' =>
      if Nat.eqb X Y then R else rel_at X Delta' rho'
  | _ :: Delta', [] => rel_at X Delta' []
  end.

Fixpoint sem (Delta : ty_context) (rho : list trel) (T : ty) : trel :=
  match T with
  | Ty_BVar n => fun x y =>
      locally_closed_tm x /\ locally_closed_tm y /\
      fv_tm x = [] /\ fv_tm y = [] /\
      exists vx vy, (match nth_error rho n with
        | Some R => R vx vy
        | None => False
        end) /\ value vx /\ value vy /\ fv_tm vx = [] /\ fv_tm vy = [] /\
        multi x vx /\ multi y vy
  | Ty_FVar X => fun x y =>
      locally_closed_tm x /\ locally_closed_tm y /\
      fv_tm x = [] /\ fv_tm y = [] /\
      exists vx vy, rel_at X Delta rho vx vy /\ value vx /\ value vy /\
        fv_tm vx = [] /\ fv_tm vy = [] /\ multi x vx /\ multi y vy
  | Ty_Bool => fun x y =>
      locally_closed_tm x /\ locally_closed_tm y /\
      fv_tm x = [] /\ fv_tm y = [] /\
      ((multi x tm_true /\ multi y tm_true) \/
       (multi x tm_false /\ multi y tm_false))
  | Ty_Arrow A B => fun x y =>
      locally_closed_tm x /\ locally_closed_tm y /\
      fv_tm x = [] /\ fv_tm y = [] /\
      exists vx vy, value vx /\ value vy /\ fv_tm vx = [] /\ fv_tm vy = [] /\
        multi x vx /\ multi y vy /\
        (forall ax ay, sem Delta rho A ax ay ->
          sem Delta rho B (tm_app vx ax) (tm_app vy ay))
  | Ty_All T1 => fun x y =>
      locally_closed_tm x /\ locally_closed_tm y /\
      fv_tm x = [] /\ fv_tm y = [] /\
      exists bx b2, value (tm_tabs bx) /\ value (tm_tabs b2) /\
        fv_tm (tm_tabs bx) = [] /\ fv_tm (tm_tabs b2) = [] /\
        multi x (tm_tabs bx) /\ multi y (tm_tabs b2) /\
        (forall X, ~ In X Delta -> forall R, lc_rel R ->
          sem (X :: Delta) (R :: rho) T1
            (open_tm_ty bx (Ty_FVar X))
            (open_tm_ty b2 (Ty_FVar X)))
  end.

Fixpoint subst_sem (s : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => s x
  | tm_abs T t1 => tm_abs T (subst_sem s t1)
  | tm_app t1 t2 => tm_app (subst_sem s t1) (subst_sem s t2)
  | tm_tabs t1 => tm_tabs (subst_sem s t1)
  | tm_tapp t1 T => tm_tapp (subst_sem s t1) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (subst_sem s t1) (subst_sem s t2) (subst_sem s t3)
  | tm_choice t1 t2 => tm_choice (subst_sem s t1) (subst_sem s t2)
  end.

Definition env_ok (Delta : ty_context) (rho : list trel)
    (Gamma : context) (s1 s2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    sem Delta rho T (s1 x) (s2 x).

Definition extend_subst (s : atom -> tm) (x : atom) (a : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then a else s y.

Definition subst_ok (s : atom -> tm) : Prop :=
  forall x, locally_closed_tm (s x) /\ fv_tm (s x) = [].

Lemma subst_ok_extend : forall s x a,
  subst_ok s -> locally_closed_tm a -> fv_tm a = [] ->
  subst_ok (extend_subst s x a).
Proof.
  intros s x a Hs Hla Hfa y; unfold extend_subst.
  destruct (Nat.eqb x y) eqn:E.
  - split; assumption.
  - apply Hs.
Qed.

Lemma env_ok_update : forall Delta rho Gamma s1 s2 x T a1 a2,
  env_ok Delta rho Gamma s1 s2 -> sem Delta rho T a1 a2 ->
  env_ok Delta rho (update Gamma x T)
    (extend_subst s1 x a1) (extend_subst s2 x a2).
Proof.
  intros Delta rho Gamma s1 s2 x T a1 a2 Henv Ha y Ty Hlook.
  simpl in Hlook; destruct (Nat.eqb y x) eqn:E.
  - inversion Hlook; subst Ty; unfold extend_subst; rewrite Nat.eqb_sym, E; exact Ha.
  - unfold extend_subst; rewrite Nat.eqb_sym, E; apply Henv; exact Hlook.
Qed.

Lemma lc_ty_open_rec_rev : forall k U T,
  lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  intros k U T; revert k U; induction T; intros k U H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_ty_bvar; apply Nat.eqb_eq in E; lia.
    + inversion H; apply lc_ty_bvar; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - constructor.
Qed.

Lemma lc_tm_open_rec_rev : forall K k u t,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k u t; revert K k u; induction t; intros K k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply lc_tm_bvar; apply Nat.eqb_eq in E; lia.
    + inversion H; apply lc_tm_bvar; apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion H; constructor; eauto using lc_ty_at.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto using lc_ty_at.
  - constructor.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_rec_rev : forall K j U t,
  lc_tm_at K j (open_tm_ty_rec K U t) -> lc_tm_at (S K) j t.
Proof.
  intros K j U t; revert K j U; induction t; intros K j U H; simpl in H.
  - constructor; inversion H; eauto.
  - constructor.
  - inversion H; constructor.
    + eapply lc_ty_open_rec_rev; eauto.
    + eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor.
    + eauto.
    + eapply lc_ty_open_rec_rev; eauto.
  - constructor.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
Qed.

Lemma in_le_max : forall L x, In x L ->
  x <= fold_right Nat.max 0 L.
Proof.
  induction L as [|a L IH]; intros x H.
  - inversion H.
  - simpl in H; destruct H as [<- | H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eassumption | apply Nat.le_max_r].
Qed.

Lemma exists_not_in : forall L : list atom, exists x, ~ In x L.
Proof.
  intro L; exists (S (fold_right Nat.max 0 L)); intro H.
  pose proof (in_le_max L (S (fold_right Nat.max 0 L)) H).
  lia.
Qed.

Scheme wf_ty_ind_full := Induction for wf_ty Sort Prop.
Scheme has_type_ind_full := Induction for has_type Sort Prop.

Lemma wf_lc_ty : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H using wf_ty_ind_full.
  - constructor.
  - constructor; assumption.
  - destruct (exists_not_in L) as [X HX].
    specialize (H X HX).
    apply lc_ty_all.
    eapply lc_ty_open_rec_rev; eauto.
  - constructor.
Qed.

Lemma typing_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H.
  - constructor.
  - constructor.
    + eapply wf_lc_ty; eauto.
    + destruct (exists_not_in L) as [x Hx].
      specialize (H0 x Hx).
      eapply lc_tm_open_rec_rev.
      exact (H1 x Hx).
  - constructor; assumption.
  - constructor.
    destruct (exists_not_in L) as [X HX].
    specialize (H X HX).
    eapply (lc_tm_ty_open_rec_rev 0 0 (Ty_FVar X) t).
    exact (H0 X HX).
  - constructor.
    + assumption.
    + eapply wf_lc_ty; eauto.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T ->
  forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H; induction H; intros K' Hle.
  - constructor; lia.
  - constructor.
  - constructor; eauto; lia.
  - apply lc_ty_all.
    apply IHlc_ty_at; lia.
  - constructor.
Qed.

Lemma lc_tm_weaken_type : forall K k t, lc_tm_at K k t ->
  forall K', K <= K' -> lc_tm_at K' k t.
Proof.
  intros K k t H; induction H; intros K' Hle.
  - constructor; assumption.
  - constructor.
  - constructor; eauto using lc_ty_weaken; lia.
  - constructor; eauto; lia.
  - apply lc_tm_tabs; eapply IHlc_tm_at; lia.
  - constructor.
    + eauto.
    + eauto using lc_ty_weaken.
  - constructor.
  - constructor.
  - constructor; eauto; lia.
  - constructor; eauto; lia.
Qed.

Lemma lc_tm_weaken_term : forall K k t, lc_tm_at K k t ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t H; induction H; eauto using lc_tm_at, lc_ty_at.
Qed.

Lemma lc_tm_weaken_term_n : forall K k t, lc_tm_at K k t ->
  forall k', k <= k' -> lc_tm_at K k' t.
Proof.
  intros K k t H k' Hle; induction Hle.
  - exact H.
  - apply lc_tm_weaken_term; assumption.
Qed.

Lemma lc_tm_subst : forall K k t s,
  lc_tm_at K k t ->
  (forall x, lc_tm_at K k (s x)) ->
  lc_tm_at K k (subst_sem s t).
Proof.
  intros K k t s H; induction H; intros Hs; simpl.
  - constructor; assumption.
  - apply Hs.
  - constructor.
    + eauto using lc_ty_at.
    + apply IHlc_tm_at; intro x; apply lc_tm_weaken_term; apply Hs.
  - constructor; eauto.
  - apply lc_tm_tabs.
    apply IHlc_tm_at.
    intro x; eapply lc_tm_weaken_type; [apply Hs | lia].
  - constructor.
    + eapply IHlc_tm_at; eauto.
    + assumption.
  - constructor.
  - constructor.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma fv_subst_nil : forall t s, (forall x, fv_tm (s x) = []) ->
  fv_tm (subst_sem s t) = [].
Proof.
  induction t; intros s Hs; simpl.
  - reflexivity.
  - apply Hs.
  - rewrite (IHt s Hs); reflexivity.
  - rewrite (IHt1 s Hs), (IHt2 s Hs); reflexivity.
  - rewrite (IHt s Hs); reflexivity.
  - rewrite (IHt s Hs); reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IHt1 s Hs), (IHt2 s Hs), (IHt3 s Hs); reflexivity.
  - rewrite (IHt1 s Hs), (IHt2 s Hs); reflexivity.
Qed.

Lemma subst_lc_typing : forall Delta Gamma t T s,
  has_type Delta Gamma t T -> subst_ok s ->
  locally_closed_tm (subst_sem s t).
Proof.
  intros Delta Gamma t T s H Hs.
  eapply lc_tm_subst.
  - apply typing_lc with (Delta := Delta) (Gamma := Gamma) (t := t) (T := T); exact H.
  - intro x; apply (Hs x).
Qed.

Lemma subst_fv_ok : forall s t, subst_ok s -> fv_tm (subst_sem s t) = [].
Proof.
  intros s t H; apply fv_subst_nil; intro x; apply (H x).
Qed.

Lemma multi_trans : forall x y z, multi x y -> multi y z -> multi x z.
Proof.
  intros x y z Hxy Hyz; induction Hxy; eauto using multi.
Qed.

Lemma sem_expand : forall Delta rho T a1 a2 b1 b2,
  sem Delta rho T b1 b2 ->
  locally_closed_tm a1 -> locally_closed_tm a2 ->
  fv_tm a1 = [] -> fv_tm a2 = [] ->
  multi a1 b1 -> multi a2 b2 ->
  sem Delta rho T a1 a2.
Proof.
  intros Delta rho T; induction T; intros a1 a2 b1 b2 H;
    simpl in H |- *.
  - destruct H as [L1 [L2 [F1 [F2 [v1 [v2 [HR [V1 [V2 [M1 M2]]]]]]]]]].
    repeat split; try assumption; exists v1, v2; repeat split; try assumption;
      eapply multi_trans; eassumption.
  - destruct H as [L1 [L2 [F1 [F2 [v1 [v2 [HR [V1 [V2 [M1 M2]]]]]]]]]].
    repeat split; try assumption; exists v1, v2; repeat split; try assumption;
      eapply multi_trans; eassumption.
  - destruct H as [L1 [L2 [F1 [F2 [v1 [v2 [V1 [V2 [M1 [M2 Hp]]]]]]]]]].
    repeat split; try assumption; exists v1, v2; repeat split; try assumption;
      eapply multi_trans; eassumption.
  - destruct H as [L1 [L2 [F1 [F2 [b1' [b2' [V1 [V2 [M1 [M2 Hp]]]]]]]]]].
    repeat split; try assumption; exists b1', b2'; repeat split; try assumption;
      eapply multi_trans; eassumption.
  - destruct H as [L1 [L2 [F1 [F2 H]]]].
    repeat split; try assumption.
    destruct H as [Htrue | Hfalse].
    + destruct Htrue as [M1 M2].
      left; split; [eapply multi_trans; eassumption | eapply multi_trans; eassumption].
    + destruct Hfalse as [M1 M2].
      right; split; [eapply multi_trans; eassumption | eapply multi_trans; eassumption].
Qed.

Lemma sem_lc : forall Delta rho T x y,
  sem Delta rho T x y -> locally_closed_tm x /\ locally_closed_tm y.
Proof.
  intros Delta rho T x y H; destruct T; simpl in H.
  - destruct (nth_error rho n); tauto.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
Qed.

Lemma sem_fv : forall Delta rho T x y,
  sem Delta rho T x y -> fv_tm x = [] /\ fv_tm y = [].
Proof.
  intros Delta rho T x y H; destruct T; simpl in H.
  - destruct (nth_error rho n); tauto.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
Qed.

Lemma sem_values : forall Delta rho T x y,
  sem Delta rho T x y ->
  exists vx vy, value vx /\ value vy /\ multi x vx /\ multi y vy.
Proof.
  intros Delta rho T x y H; destruct T; simpl in H.
  - destruct H as [_ [_ [_ [_ [vx [vy [_ [V1 [V2 [M1 M2]]]]]]]]]].
    exists vx, vy; repeat split; assumption.
  - destruct H as [_ [_ [_ [_ [vx [vy [_ [V1 [V2 [M1 M2]]]]]]]]]].
    exists vx, vy; repeat split; assumption.
  - destruct H as [_ [_ [_ [_ [vx [vy [V1 [V2 [M1 [M2 _]]]]]]]]]].
    exists vx, vy; repeat split; assumption.
  - destruct H as [_ [_ [_ [_ [bx [b2 [V1 [V2 [M1 [M2 _]]]]]]]]]].
    exists (tm_tabs bx), (tm_tabs b2); repeat split; assumption.
  - destruct H as [_ [_ [_ [_ H]]]].
    destruct H as [[M1 M2] | [M1 M2]].
    + exists tm_true, tm_true; repeat split; try constructor; assumption.
    + exists tm_false, tm_false; repeat split; try constructor; assumption.
Qed.

Lemma multi_app_l : forall x y z, multi x y -> locally_closed_tm z ->
  multi (tm_app x z) (tm_app y z).
Proof.
  intros x y z Hxy Hz; revert Hz; induction Hxy as [q | a b c Hab IH].
  - intro Hz; apply multi_refl.
  - intro Hz; eapply multi_step.
    + eapply ST_App1; eauto.
    + pose proof (IHIH Hz) as Q.
      exact Q.
Qed.

Lemma multi_app_r : forall v x y, value v -> multi x y ->
  multi (tm_app v x) (tm_app v y).
Proof.
  intros v x y Hv Hxy; induction Hxy as [q | a b c Hab IH].
  - apply multi_refl.
  - eapply multi_step.
    + eapply ST_App2; eauto.
    + apply IHIH.
Qed.

Lemma multi_tapp : forall x y T, multi x y -> locally_closed_ty T ->
  multi (tm_tapp x T) (tm_tapp y T).
Proof.
  intros x y T Hxy HT; revert HT; induction Hxy as [q | a b c Hab IH].
  - intro HT; apply multi_refl.
  - intro HT; eapply multi_step.
    + eapply ST_TApp; eauto.
    + apply IHIH; exact HT.
Qed.

Lemma multi_if_guard : forall x y a b, multi x y ->
  locally_closed_tm a -> locally_closed_tm b ->
  multi (tm_if x a b) (tm_if y a b).
Proof.
  intros x y a b Hxy Ha Hb; revert Ha Hb;
    induction Hxy as [q | c d e Hcd IH].
  - intros Ha Hb; apply multi_refl.
  - intros Ha Hb; eapply multi_step.
    + eapply ST_If; eauto.
    + eapply IHIH; eauto.
Qed.

Lemma subst_closed : forall s t, fv_tm t = [] -> subst_sem s t = t.
Proof.
  intros s t; induction t; simpl; intro H.
  - reflexivity.
  - exfalso; discriminate H.
  - f_equal; eauto.
  - apply app_eq_nil in H; destruct H; f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - reflexivity.
  - reflexivity.
  - apply app_eq_nil in H; destruct H as [H1 H23].
    apply app_eq_nil in H23; destruct H23; f_equal; eauto.
  - apply app_eq_nil in H; destruct H; f_equal; eauto.
Qed.

Lemma subst_open_rec : forall s x a k t, ~ In x (fv_tm t) -> fv_tm a = [] ->
  subst_sem (extend_subst s x a) (open_tm_rec k (tm_fvar x) t) =
  subst_sem s (open_tm_rec k a t).
Proof.
  intros s x a k t Hf Ha; revert k Hf Ha;
    induction t; intros k Hf Ha; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold extend_subst; rewrite Nat.eqb_refl; symmetry; apply subst_closed; exact Ha.
    + unfold extend_subst; simpl; reflexivity.
  - destruct (Nat.eqb x a0) eqn:E.
    + exfalso; apply Hf; simpl; left; apply Nat.eqb_eq in E; symmetry; exact E.
    + unfold extend_subst; rewrite E; reflexivity.
  - f_equal; eauto.
  - assert (Hf1 : ~ In x (fv_tm t1)).
    { intro H; apply Hf; apply in_or_app; left; exact H. }
    assert (Hf2 : ~ In x (fv_tm t2)).
    { intro H; apply Hf; apply in_or_app; right; exact H. }
    f_equal.
    + eauto.
    + eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - reflexivity.
  - reflexivity.
  - assert (Hf1 : ~ In x (fv_tm t1)).
    { intro H; apply Hf; apply in_or_app; left; exact H. }
    assert (Hf23 : ~ In x (fv_tm t2 ++ fv_tm t3)).
    { intro H; apply Hf; apply in_or_app; right; exact H. }
    assert (Hf2 : ~ In x (fv_tm t2)).
    { intro H; apply Hf23; apply in_or_app; left; exact H. }
    assert (Hf3 : ~ In x (fv_tm t3)).
    { intro H; apply Hf23; apply in_or_app; right; exact H. }
    f_equal.
    + eauto.
    + eauto.
    + eauto.
  - assert (Hf1 : ~ In x (fv_tm t1)).
    { intro H; apply Hf; apply in_or_app; left; exact H. }
    assert (Hf2 : ~ In x (fv_tm t2)).
    { intro H; apply Hf; apply in_or_app; right; exact H. }
    f_equal.
    + eauto.
    + eauto.
Qed.

Lemma subst_open : forall s x a t, ~ In x (fv_tm t) -> fv_tm a = [] ->
  subst_sem (extend_subst s x a) (open_tm t (tm_fvar x)) =
  subst_sem s (open_tm t a).
Proof. intros; eapply subst_open_rec; eassumption. Qed.

Lemma open_lc_rec : forall K k u t,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  intros K k u t H; induction H; simpl.
  - destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma open_lc : forall t u, locally_closed_tm t -> open_tm t u = t.
Proof. intros; apply open_lc_rec with (K:=0) (k:=0); exact H. Qed.

Lemma open_subst_rec : forall s t a k, (forall x, locally_closed_tm (s x)) ->
  fv_tm a = [] ->
  open_tm_rec k a (subst_sem s t) = subst_sem s (open_tm_rec k a t).
Proof.
  intros s t a k Hs Ha; revert k; induction t; intros k; simpl.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + symmetry; apply subst_closed; exact Ha.
    + reflexivity.
  - rewrite (open_lc_rec 0 k a (s a0)
               (lc_tm_weaken_term_n 0 0 (s a0) (Hs a0) k (le_0_n k)));
      reflexivity.
  - f_equal; eapply IHt; eauto.
  - f_equal.
    + eapply IHt1; eauto.
    + eapply IHt2; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma open_subst : forall s t a, (forall x, locally_closed_tm (s x)) ->
  fv_tm a = [] ->
  open_tm (subst_sem s t) a = subst_sem s (open_tm t a).
Proof. intros; apply open_subst_rec; assumption. Qed.

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho s1 s2, subst_ok s1 -> subst_ok s2 ->
    env_ok Delta rho Gamma s1 s2 ->
    sem Delta rho T (subst_sem s1 t) (subst_sem s2 t).
Proof.
  intros Delta Gamma t T H; induction H using has_type_ind_full;
    intros rho s1 s2 Hs1 Hs2 Henv.
  - apply Henv; assumption.
  - simpl.
    split.
    + change (locally_closed_tm (subst_sem s1 (tm_abs T1 t2))).
      eapply subst_lc_typing; [econstructor; eauto | exact Hs1].
    + split.
      * change (locally_closed_tm (subst_sem s2 (tm_abs T1 t2))).
        eapply subst_lc_typing; [econstructor; eauto | exact Hs2].
      * split.
        -- apply subst_fv_ok; exact Hs1.
        -- split.
          ++ apply subst_fv_ok; exact Hs2.
          ++ exists (tm_abs T1 (subst_sem s1 t2)),
          (tm_abs T1 (subst_sem s2 t2)); repeat split.
          *** apply v_abs.
           change (locally_closed_tm (subst_sem s1 (tm_abs T1 t2))).
           eapply subst_lc_typing; [econstructor; eauto | exact Hs1].
          *** apply v_abs.
           change (locally_closed_tm (subst_sem s2 (tm_abs T1 t2))).
           eapply subst_lc_typing; [econstructor; eauto | exact Hs2].
          *** apply multi_refl.
          *** apply multi_refl.
          *** intros ax ay Haxay.
           destruct (exists_not_in (L ++ fv_tm t2)) as [x Hx].
           assert (HxL : ~ In x L) by
             (intro Q; apply Hx; apply in_or_app; left; exact Q).
           assert (HxT : ~ In x (fv_tm t2)) by
             (intro Q; apply Hx; apply in_or_app; right; exact Q).
           assert (Ha1 : locally_closed_tm ax) by
             (apply (proj1 (sem_lc Delta rho T1 ax ay Haxay))).
           assert (Ha2 : locally_closed_tm ay) by
             (apply (proj2 (sem_lc Delta rho T1 ax ay Haxay))).
           assert (Fxa : fv_tm ax = []) by
             (apply (proj1 (sem_fv Delta rho T1 ax ay Haxay))).
           assert (Fya : fv_tm ay = []) by
             (apply (proj2 (sem_fv Delta rho T1 ax ay Haxay))).
           assert (Va1 : value ax) by
             (destruct (sem_values Delta rho T1 ax ay Haxay) as [q1 [q2 [Vq1 [Vq2 [Mq1 Mq2]]]]];
              exact Vq1).
           assert (Va2 : value ay) by
             (destruct (sem_values Delta rho T1 ax ay Haxay) as [q1 [q2 [Vq1 [Vq2 [Mq1 Mq2]]]]];
              exact Vq2).
           pose proof (H x HxL rho
             (extend_subst s1 x ax) (extend_subst s2 x ay)
             (subst_ok_extend s1 x ax Hs1 Ha1 Fxa)
             (subst_ok_extend s2 x ay Hs2 Ha2 Fya)
             (env_ok_update Delta rho Gamma s1 s2 x T1 ax ay Henv Haxay)) as Q.
           rewrite (subst_open s1 x ax t2 HxT Fxa) in Q.
           rewrite (subst_open s2 x ay t2 HxT Fya) in Q.
           rewrite <- (open_subst s1 t2 ax (fun y =>
             proj1 (Hs1 y)) Fxa) in Q.
           rewrite <- (open_subst s2 t2 ay (fun y =>
             proj1 (Hs2 y)) Fya) in Q.
           assert (LCApp1 : locally_closed_tm
             (tm_app (tm_abs T1 (subst_sem s1 t2)) ax)) by
             (constructor; [
                eapply subst_lc_typing with (t := tm_abs T1 t2);
                [exact (T_Abs L Delta Gamma T1 t2 T2 w h) | exact Hs1]
                | exact Ha1]).
           assert (LCApp2 : locally_closed_tm
             (tm_app (tm_abs T1 (subst_sem s2 t2)) ay)) by
             (constructor; [
                eapply subst_lc_typing with (t := tm_abs T1 t2);
                [exact (T_Abs L Delta Gamma T1 t2 T2 w h) | exact Hs2]
                | exact Ha2]).
           assert (FVApp1 : fv_tm
             (tm_app (tm_abs T1 (subst_sem s1 t2)) ax) = []) by
             (simpl; rewrite (subst_fv_ok s1 t2 Hs1), Fxa; reflexivity).
           assert (FVApp2 : fv_tm
             (tm_app (tm_abs T1 (subst_sem s2 t2)) ay) = []) by
             (simpl; rewrite (subst_fv_ok s2 t2 Hs2), Fya; reflexivity).
           eapply sem_expand; [exact Q | exact LCApp1 | exact LCApp2 |
             exact FVApp1 | exact FVApp2 | |].
           **** eapply multi_step.
              ***** eapply ST_AppAbs.
                ****** eapply subst_lc_typing with (t := tm_abs T1 t2);
                  [exact (T_Abs L Delta Gamma T1 t2 T2 w h) | exact Hs1].
                ****** exact Va1.
              ***** apply multi_refl.
           **** eapply multi_step.
              ***** eapply ST_AppAbs.
                ****** eapply subst_lc_typing with (t := tm_abs T1 t2);
                  [exact (T_Abs L Delta Gamma T1 t2 T2 w h) | exact Hs2].
                ****** exact Va2.
              ***** apply multi_refl.
  - simpl.
    destruct H as [F1 [F2 [v1 [v2 [V1 [V2 [M1 [M2 Hp]]]]]]]].
    destruct H0 as [F3 [F4 [a1 [a2 [A1 [A2 [N1 [N2 Hpa]]]]]]]].
    pose proof (Hpa Haxay) as HB.
    assert (Lc2_1 : locally_closed_tm (subst_sem s1 t2)) by
      (eapply subst_lc_typing; [eassumption | exact Hs1]).
    assert (Lc2_2 : locally_closed_tm (subst_sem s2 t2)) by
      (eapply subst_lc_typing; [eassumption | exact Hs2]).
    assert (Mapp1 : multi (tm_app (subst_sem s1 t1) (subst_sem s1 t2))
        (tm_app v1 a1)).
    { eapply multi_trans.
      - apply multi_app_l; [exact M1 | exact Lc2_1].
      - apply multi_app_r; [exact V1 | exact N1]. }
    assert (Mapp2 : multi (tm_app (subst_sem s2 t1) (subst_sem s2 t2))
        (tm_app v2 a2)).
    { eapply multi_trans.
      - apply multi_app_l; [exact M2 | exact Lc2_2].
      - apply multi_app_r; [exact V2 | exact N2]. }
    eapply sem_expand; [exact HB | | | | | exact Mapp1 | exact Mapp2].
    + eapply subst_lc_typing; [eassumption | exact Hs1].
    + eapply subst_lc_typing; [eassumption | exact Hs2].
    + apply subst_fv_ok; exact Hs1.
    + apply subst_fv_ok; exact Hs2.
  - admit.
  - admit.
  - simpl; repeat split; try constructor.
  - simpl; repeat split; try constructor.
  - admit.
  - admit.
Admitted.

Theorem polymorphic_identity_theorem_for_free : forall t,
  has_type [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) ->
  forall U v,
    wf_ty [] U ->
    value v ->
    has_type [] empty v U ->
    tm_app (tm_tapp t U) v -->* v.
Proof.
  (* Complete the proof of the free theorem. *)
Admitted.

End SystemFParametricityIfNondeterminismHardTask.
