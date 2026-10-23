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

(** A value relation is indexed by the interpretations of the bound and
    free type variables.  The expression lifting uses may convergence: a
    choice may take any branch that witnesses the relation. *)
Definition rel := tm -> tm -> Prop.
Definition rel_env := atom -> rel.
Definition bound_rel_env := list rel.

Definition expr_rel (R : rel) (t1 t2 : tm) : Prop :=
  exists v1 v2, t1 -->* v1 /\ t2 -->* v2 /\ R v1 v2.

Fixpoint value_rel (B : bound_rel_env) (F : rel_env)
    (T : ty) (v1 v2 : tm) : Prop :=
  value v1 /\ value v2 /\
  match T with
  | Ty_BVar i =>
      match nth_error B i with Some R => R v1 v2 | None => False end
  | Ty_FVar X => F X v1 v2
  | Ty_Arrow A C =>
      forall a1 a2, value_rel B F A a1 a2 ->
        expr_rel (value_rel B F C) (tm_app v1 a1) (tm_app v2 a2)
  | Ty_All C =>
      forall U1 U2 (R : rel),
        locally_closed_ty U1 -> locally_closed_ty U2 ->
        expr_rel (value_rel (R :: B) F C)
          (tm_tapp v1 U1) (tm_tapp v2 U2)
  | Ty_Bool =>
      (v1 = tm_true /\ v2 = tm_true) \/
      (v1 = tm_false /\ v2 = tm_false)
  end.

Definition fresh (L : list atom) : atom :=
  S (fold_right Nat.max 0 L).

Lemma fresh_not_in : forall L, ~ In (fresh L) L.
Proof.
  assert (Hbound : forall L a, In a L -> a <= fold_right Nat.max 0 L).
  { induction L as [|b L IH]; intros a H; simpl in *.
    - contradiction.
    - destruct H as [H | H].
      + subst; lia.
      + specialize (IH a H); lia. }
  intros L H. unfold fresh in H.
  pose proof (Hbound L (S (fold_right Nat.max 0 L)) H). lia.
Qed.

Lemma lc_ty_open_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) ->
  lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eauto.
  - constructor.
Qed.

Lemma lc_tm_open_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion H; subst. constructor; lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H.
  - inversion H; subst. constructor; assumption.
  - constructor.
  - inversion H; subst. constructor.
    + eapply lc_ty_open_inv; eassumption.
    + eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto using lc_ty_open_inv.
  - constructor.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor; eauto.
Qed.

Lemma wf_ty_lc : forall D T, wf_ty D T -> locally_closed_ty T.
Proof.
  intros D T H; induction H; unfold locally_closed_ty in *.
  - constructor.
  - constructor; assumption.
  - constructor. specialize (H (fresh L) (fresh_not_in L)).
    eapply lc_ty_open_inv; exact (H0 (fresh L) (fresh_not_in L)).
  - constructor.
Qed.

Lemma has_type_lc : forall D G t T,
  has_type D G t T -> locally_closed_tm t.
Proof.
  intros D G t T H; induction H; unfold locally_closed_tm in *.
  - constructor.
  - constructor.
    + apply wf_ty_lc in H; exact H.
    + eapply lc_tm_open_inv.
      exact (H1 (fresh L) (fresh_not_in L)).
  - constructor; assumption.
  - constructor. eapply lc_tm_ty_open_inv.
    exact (H0 (fresh L) (fresh_not_in L)).
  - apply lc_tm_tapp; [assumption | eapply wf_ty_lc; eassumption].
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Fixpoint inst_ty (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A C => Ty_Arrow (inst_ty theta A) (inst_ty theta C)
  | Ty_All C => Ty_All (inst_ty theta C)
  | Ty_Bool => Ty_Bool
  end.

Fixpoint inst_tm (theta : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs A b => tm_abs (inst_ty theta A) (inst_tm theta sigma b)
  | tm_app a b => tm_app (inst_tm theta sigma a) (inst_tm theta sigma b)
  | tm_tabs b => tm_tabs (inst_tm theta sigma b)
  | tm_tapp b A => tm_tapp (inst_tm theta sigma b) (inst_ty theta A)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if a b c => tm_if (inst_tm theta sigma a)
                              (inst_tm theta sigma b)
                              (inst_tm theta sigma c)
  | tm_choice a b => tm_choice (inst_tm theta sigma a)
                                (inst_tm theta sigma b)
  end.

Definition set_ty (theta : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else theta Y.
Definition set_tm (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.
Definition set_rel (F : rel_env) (X : atom) (R : rel) : rel_env :=
  fun Y => if Nat.eqb X Y then R else F Y.

Fixpoint ty_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A C => ty_atoms A ++ ty_atoms C
  | Ty_All C => ty_atoms C
  | Ty_Bool => []
  end.

Fixpoint tm_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b => tm_atoms b
  | tm_app a b => tm_atoms a ++ tm_atoms b
  | tm_tabs b => tm_atoms b
  | tm_tapp b _ => tm_atoms b
  | tm_true | tm_false => []
  | tm_if a b c => tm_atoms a ++ tm_atoms b ++ tm_atoms c
  | tm_choice a b => tm_atoms a ++ tm_atoms b
  end.

Fixpoint tm_type_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false => []
  | tm_abs A b => ty_atoms A ++ tm_type_atoms b
  | tm_app a b => tm_type_atoms a ++ tm_type_atoms b
  | tm_tabs b => tm_type_atoms b
  | tm_tapp b A => tm_type_atoms b ++ ty_atoms A
  | tm_if a b c => tm_type_atoms a ++ tm_type_atoms b ++ tm_type_atoms c
  | tm_choice a b => tm_type_atoms a ++ tm_type_atoms b
  end.

Fixpoint context_type_atoms (G : context) : list atom :=
  match G with
  | [] => []
  | (_, A) :: G' => ty_atoms A ++ context_type_atoms G'
  end.

Lemma lc_ty_weaken : forall k T, lc_ty_at k T ->
  forall k', k <= k' -> lc_ty_at k' T.
Proof.
  intros k T H; induction H; intros k' Hle.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all. apply IHlc_ty_at; lia.
  - apply lc_ty_bool.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H; induction H; intros K' k' HK Hk;
    try solve [constructor; eauto using lc_ty_weaken; lia].
  - constructor; [eapply lc_ty_weaken; eauto | eapply IHlc_tm_at; lia].
  - constructor. eapply IHlc_tm_at; lia.
Qed.

Lemma inst_ty_lc : forall k T theta,
  lc_ty_at k T ->
  (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at k (inst_ty theta T).
Proof.
  intros k T theta H; induction H; intros Htheta; simpl; eauto.
  - eapply lc_ty_weaken; [apply Htheta | lia].
Qed.

Lemma inst_tm_lc : forall K k t theta sigma,
  lc_tm_at K k t ->
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k (inst_tm theta sigma t).
Proof.
  intros K k t theta sigma H; induction H; intros Htheta Hsigma; simpl;
    try solve [constructor; eauto using inst_ty_lc].
  - eapply lc_tm_weaken; [apply Hsigma | lia | lia].
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst; unfold locally_closed_tm in *; eauto.
Qed.

Lemma value_rel_lc : forall B F T v1 v2,
  value_rel B F T v1 v2 ->
  locally_closed_tm v1 /\ locally_closed_tm v2.
Proof.
  intros B F T v1 v2 H. destruct T; simpl in H;
    destruct H as [H1 [H2 _]].
  all: split; eapply value_lc; eassumption.
Qed.

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H; induction H; intros Hbc; eauto using multi.
Qed.

Lemma multi_app1 : forall a a' b,
  a -->* a' -> locally_closed_tm b ->
  tm_app a b -->* tm_app a' b.
Proof.
  intros a a' b H; induction H; intros Hb.
  - constructor.
  - eapply multi_step; [apply ST_App1; eassumption | eauto].
Qed.

Lemma multi_app2 : forall v b b',
  value v -> b -->* b' -> tm_app v b -->* tm_app v b'.
Proof.
  intros v b b' Hv H; induction H.
  - constructor.
  - eapply multi_step; [apply ST_App2; eassumption | eauto].
Qed.

Lemma multi_tapp : forall a a' U,
  a -->* a' -> locally_closed_ty U ->
  tm_tapp a U -->* tm_tapp a' U.
Proof.
  intros a a' U H; induction H; intros HU.
  - constructor.
  - eapply multi_step; [apply ST_TApp; eassumption | eauto].
Qed.

Lemma multi_if : forall a a' b c,
  a -->* a' -> locally_closed_tm b -> locally_closed_tm c ->
  tm_if a b c -->* tm_if a' b c.
Proof.
  intros a a' b c H; induction H; intros Hb Hc.
  - constructor.
  - eapply multi_step; [apply ST_If; eassumption | eauto].
Qed.

Lemma expr_rel_step_back : forall R a1 a2 b1 b2,
  a1 -->* b1 -> a2 -->* b2 -> expr_rel R b1 b2 ->
  expr_rel R a1 a2.
Proof.
  intros R a1 a2 b1 b2 H1 H2 [v1 [v2 [H3 [H4 HR]]]].
  exists v1, v2; repeat split; eauto using multi_trans.
Qed.

Lemma expr_rel_choice : forall R a1 a2 b1 b2,
  locally_closed_tm a1 -> locally_closed_tm a2 ->
  locally_closed_tm b1 -> locally_closed_tm b2 ->
  expr_rel R a1 a2 ->
  expr_rel R (tm_choice a1 b1) (tm_choice a2 b2).
Proof.
  intros R a1 a2 b1 b2 Ha1 Ha2 Hb1 Hb2 HR.
  eapply expr_rel_step_back; [| | exact HR].
  - eapply multi_step; [apply ST_ChoiceLeft; eassumption | constructor].
  - eapply multi_step; [apply ST_ChoiceLeft; eassumption | constructor].
Qed.

Lemma open_ty_lc_id : forall k T U,
  lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  intros k T U H; induction H; simpl; f_equal; eauto.
  destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
Qed.

Lemma open_tm_lc_id : forall K k t v,
  lc_tm_at K k t -> open_tm_rec k v t = t.
Proof.
  intros K k t v H; induction H; simpl; f_equal; eauto.
  destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
Qed.

Lemma open_tm_ty_lc_id : forall K k t U,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  intros K k t U H; induction H; simpl; f_equal; eauto using open_ty_lc_id.
Qed.

Lemma inst_ty_set_fresh : forall T theta X U,
  ~ In X (ty_atoms T) ->
  inst_ty (set_ty theta X U) T = inst_ty theta T.
Proof.
  induction T; intros theta X U H; simpl in *; f_equal; eauto.
  - unfold set_ty. destruct (Nat.eqb X a) eqn:E; auto.
    apply Nat.eqb_eq in E; subst. exfalso; apply H; auto.
  - apply IHT1. intro C; apply H; apply in_or_app; left; exact C.
  - apply IHT2. intro C; apply H; apply in_or_app; right; exact C.
Qed.

Lemma inst_tm_set_tm_fresh : forall t theta sigma x v,
  ~ In x (tm_atoms t) ->
  inst_tm theta (set_tm sigma x v) t = inst_tm theta sigma t.
Proof.
  induction t; intros theta sigma x v H; simpl in *; f_equal; eauto.
  - unfold set_tm. destruct (Nat.eqb x a) eqn:E; auto.
    apply Nat.eqb_eq in E; subst. exfalso; apply H; auto.
  - apply IHt1. intro C; apply H; apply in_or_app; left; exact C.
  - apply IHt2. intro C; apply H; apply in_or_app; right; exact C.
  - apply IHt1. intro C; apply H; apply in_or_app; left; exact C.
  - apply IHt2. intro C; apply H; apply in_or_app; right; apply in_or_app; left; exact C.
  - apply IHt3. intro C; apply H; apply in_or_app; right; apply in_or_app; right; exact C.
  - apply IHt1. intro C; apply H; apply in_or_app; left; exact C.
  - apply IHt2. intro C; apply H; apply in_or_app; right; exact C.
Qed.

Lemma inst_ty_open_fvar : forall T k theta X U,
  ~ In X (ty_atoms T) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  inst_ty (set_ty theta X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (inst_ty theta T).
Proof.
  induction T; intros k theta X U Hfresh Htheta; simpl in *.
  - destruct (Nat.eqb k n); simpl; [unfold set_ty; rewrite Nat.eqb_refl | ]; reflexivity.
  - assert (a <> X) by (intro E; subst; apply Hfresh; auto).
    unfold set_ty. assert (E : (X =? a) = false) by (apply Nat.eqb_neq; lia).
    rewrite E.
    symmetry. eapply open_ty_lc_id. eapply lc_ty_weaken; [apply Htheta | lia].
  - f_equal.
    + apply IHT1; auto. intro C; apply Hfresh; apply in_or_app; left; exact C.
    + apply IHT2; auto. intro C; apply Hfresh; apply in_or_app; right; exact C.
  - f_equal. apply IHT; auto.
  - reflexivity.
Qed.

Lemma inst_tm_open_fvar : forall t k theta sigma x v,
  ~ In x (tm_atoms t) ->
  (forall y, locally_closed_tm (sigma y)) ->
  inst_tm theta (set_tm sigma x v) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (inst_tm theta sigma t).
Proof.
  induction t; intros k theta sigma x v Hfresh Hsigma; simpl in *;
    try reflexivity.
  - destruct (Nat.eqb k n); simpl; [unfold set_tm; rewrite Nat.eqb_refl | ]; reflexivity.
  - assert (a <> x) by (intro E; subst; apply Hfresh; auto).
    unfold set_tm. assert (E : (x =? a) = false) by (apply Nat.eqb_neq; lia).
    rewrite E.
    symmetry. eapply (open_tm_lc_id 0 k).
    eapply lc_tm_weaken; [apply Hsigma | lia | lia].
  - f_equal. apply IHt; auto.
  - f_equal.
    + apply IHt1; auto. intro C; apply Hfresh; apply in_or_app; left; exact C.
    + apply IHt2; auto. intro C; apply Hfresh; apply in_or_app; right; exact C.
  - f_equal. apply IHt; auto.
  - f_equal. apply IHt; auto.
  - f_equal.
    + apply IHt1; auto. intro C; apply Hfresh; apply in_or_app; left; exact C.
    + apply IHt2; auto. intro C; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact C.
    + apply IHt3; auto. intro C; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact C.
  - f_equal.
    + apply IHt1; auto. intro C; apply Hfresh; apply in_or_app; left; exact C.
    + apply IHt2; auto. intro C; apply Hfresh; apply in_or_app; right; exact C.
Qed.

Lemma inst_tm_open_ty_fvar : forall t K theta sigma X U,
  ~ In X (tm_type_atoms t) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  (forall y, locally_closed_tm (sigma y)) ->
  inst_tm (set_ty theta X U) sigma
    (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K U (inst_tm theta sigma t).
Proof.
  induction t; intros K theta sigma X U Hfresh Htheta Hsigma; simpl in *;
    try reflexivity.
  - symmetry. eapply (open_tm_ty_lc_id K 0).
    eapply lc_tm_weaken; [apply Hsigma | lia | lia].
  - f_equal.
    + eapply inst_ty_open_fvar; eauto.
      intro C; apply Hfresh; apply in_or_app; left; exact C.
    + apply IHt; auto. intro C; apply Hfresh; apply in_or_app; right; exact C.
  - f_equal.
    + apply IHt1; auto. intro C; apply Hfresh; apply in_or_app; left; exact C.
    + apply IHt2; auto. intro C; apply Hfresh; apply in_or_app; right; exact C.
  - f_equal. apply IHt; auto.
  - f_equal.
    + apply IHt; auto. intro C; apply Hfresh; apply in_or_app; left; exact C.
    + eapply inst_ty_open_fvar; eauto.
      intro C; apply Hfresh; apply in_or_app; right; exact C.
  - f_equal.
    + apply IHt1; auto. intro C; apply Hfresh; apply in_or_app; left; exact C.
    + apply IHt2; auto. intro C; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact C.
    + apply IHt3; auto. intro C; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact C.
  - f_equal.
    + apply IHt1; auto. intro C; apply Hfresh; apply in_or_app; left; exact C.
    + apply IHt2; auto. intro C; apply Hfresh; apply in_or_app; right; exact C.
Qed.

Lemma expr_rel_ext : forall R S,
  (forall a b, R a b <-> S a b) ->
  forall t1 t2, expr_rel R t1 t2 <-> expr_rel S t1 t2.
Proof.
  intros R S H t1 t2; unfold expr_rel.
  split; intros [a [b [H1 [H2 H3]]]]; exists a, b;
    repeat split; auto; apply H; assumption.
Qed.

Lemma value_rel_fresh : forall T B F X R v1 v2,
  ~ In X (ty_atoms T) ->
  value_rel B (set_rel F X R) T v1 v2 <->
  value_rel B F T v1 v2.
Proof.
  induction T; intros B F X R v1 v2 Hfresh; simpl in *.
  - reflexivity.
  - assert (X <> a) by (intro E; subst; apply Hfresh; auto).
    unfold set_rel. assert (E : (X =? a) = false) by (apply Nat.eqb_neq; lia).
    rewrite E; reflexivity.
  - assert (HA : ~ In X (ty_atoms T1)).
    { intro C; apply Hfresh; apply in_or_app; left; exact C. }
    assert (HC : ~ In X (ty_atoms T2)).
    { intro C; apply Hfresh; apply in_or_app; right; exact C. }
    split; intros [Hv1 [Hv2 Hfun]]; repeat split; auto.
    + intros a1 a2 Ha. apply (proj1 (expr_rel_ext _ _ (fun w1 w2 => IHT2 B F X R w1 w2 HC) _ _)).
      apply Hfun. apply (proj2 (IHT1 B F X R a1 a2 HA)); exact Ha.
    + intros a1 a2 Ha. apply (proj2 (expr_rel_ext _ _ (fun w1 w2 => IHT2 B F X R w1 w2 HC) _ _)).
      apply Hfun. apply (proj1 (IHT1 B F X R a1 a2 HA)); exact Ha.
  - split; intros [Hv1 [Hv2 Hfun]]; repeat split; auto;
      intros U1 U2 Q HU1 HU2.
    + apply (proj1 (expr_rel_ext _ _
        (fun w1 w2 => IHT (Q :: B) F X R w1 w2 Hfresh) _ _)).
      apply Hfun; assumption.
    + apply (proj2 (expr_rel_ext _ _
        (fun w1 w2 => IHT (Q :: B) F X R w1 w2 Hfresh) _ _)).
      apply Hfun; assumption.
  - reflexivity.
Qed.

Lemma value_rel_prefix_irrel : forall T k,
  lc_ty_at k T ->
  forall P B C F v1 v2,
    length P = k ->
    value_rel (P ++ B) F T v1 v2 <->
    value_rel (P ++ C) F T v1 v2.
Proof.
  intros T k Hlc; induction Hlc; intros P B C F v1 v2 Hlen; simpl.
  - rewrite nth_error_app1 by lia.
    rewrite nth_error_app1 by lia. reflexivity.
  - reflexivity.
  - split; intros [Hv1 [Hv2 Hfun]]; repeat split; auto.
    + intros a1 a2 Ha.
      apply (proj1 (expr_rel_ext _ _
        (fun w1 w2 => IHHlc2 P B C F w1 w2 Hlen) _ _)).
      apply Hfun. apply (proj2 (IHHlc1 P B C F a1 a2 Hlen)); exact Ha.
    + intros a1 a2 Ha.
      apply (proj2 (expr_rel_ext _ _
        (fun w1 w2 => IHHlc2 P B C F w1 w2 Hlen) _ _)).
      apply Hfun. apply (proj1 (IHHlc1 P B C F a1 a2 Hlen)); exact Ha.
  - split; intros [Hv1 [Hv2 Hfun]]; repeat split; auto;
      intros U1 U2 R HU1 HU2.
    + apply (proj1 (expr_rel_ext _ _
        (fun w1 w2 => IHHlc (R :: P) B C F w1 w2 (f_equal S Hlen)) _ _)).
      apply Hfun; assumption.
    + apply (proj2 (expr_rel_ext _ _
        (fun w1 w2 => IHHlc (R :: P) B C F w1 w2 (f_equal S Hlen)) _ _)).
      apply Hfun; assumption.
  - reflexivity.
Qed.

Lemma nth_error_snoc : forall (A : Type) (P : list A) (r : A),
  nth_error (P ++ [r]) (length P) = Some r.
Proof.
  intros A P; induction P as [|a P IH]; intros r; simpl; auto.
Qed.

Lemma value_rel_open_same : forall T k P F U R v1 v2,
  lc_ty_at (S k) T -> length P = k ->
  (forall B a b,
    value_rel B F U a b <-> value a /\ value b /\ R a b) ->
  value_rel P F (open_ty_rec k U T) v1 v2 <->
  value_rel (P ++ [R]) F T v1 v2.
Proof.
  induction T; intros k P F U R v1 v2 Hlc Hlen HU; simpl.
  - assert (Hbound : n < S k) by (inversion Hlc; lia).
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      rewrite nth_error_snoc. apply HU.
    + apply Nat.eqb_neq in E.
      assert (n < k) by lia.
      rewrite nth_error_app1 by lia. reflexivity.
  - reflexivity.
  - assert (HAlc : lc_ty_at (S k) T1) by (inversion Hlc; assumption).
    assert (HClc : lc_ty_at (S k) T2) by (inversion Hlc; assumption).
    assert (HA : forall a b,
      value_rel P F (open_ty_rec k U T1) a b <->
      value_rel (P ++ [R]) F T1 a b).
    { intros a b; eapply IHT1; eauto. }
    assert (HC : forall a b,
      value_rel P F (open_ty_rec k U T2) a b <->
      value_rel (P ++ [R]) F T2 a b).
    { intros a b; eapply IHT2; eauto. }
    split; intros [Hv1 [Hv2 Hfun]]; repeat split; auto.
    + intros a1 a2 Ha.
      apply (proj1 (expr_rel_ext _ _ HC _ _)).
      apply Hfun. apply (proj2 (HA a1 a2)); exact Ha.
    + intros a1 a2 Ha.
      apply (proj2 (expr_rel_ext _ _ HC _ _)).
      apply Hfun. apply (proj1 (HA a1 a2)); exact Ha.
  - assert (HTlc : lc_ty_at (S (S k)) T) by (inversion Hlc; assumption).
    split; intros [Hv1 [Hv2 Hfun]]; repeat split; auto;
      intros U1 U2 Q HU1 HU2.
    + apply (proj1 (expr_rel_ext _ _
        (fun a b => IHT (S k) (Q :: P) F U R a b HTlc (f_equal S Hlen) HU) _ _)).
      apply Hfun; assumption.
    + apply (proj2 (expr_rel_ext _ _
        (fun a b => IHT (S k) (Q :: P) F U R a b HTlc (f_equal S Hlen) HU) _ _)).
      apply Hfun; assumption.
  - reflexivity.
Qed.

Lemma value_rel_open_closed : forall T U F v1 v2,
  lc_ty_at 1 T -> locally_closed_ty U ->
  value_rel [] F (open_ty T U) v1 v2 <->
  value_rel [value_rel [] F U] F T v1 v2.
Proof.
  intros T U F v1 v2 HT HU.
  unfold open_ty.
  eapply value_rel_open_same with (k := 0) (P := [])
    (R := value_rel [] F U); eauto.
  intros B a b.
    pose proof (value_rel_prefix_irrel U 0 HU [] B [] F a b eq_refl) as H.
    simpl in H. split; intro HR.
  - apply H in HR. destruct U; simpl in HR;
      destruct HR as [Ha [Hb HR]]; repeat split; assumption.
  - destruct HR as [_ [_ HR]]. apply H; exact HR.
Qed.

Lemma value_rel_open_fvar : forall T F X R v1 v2,
  lc_ty_at 1 T -> ~ In X (ty_atoms T) ->
  value_rel [] (set_rel F X R) (open_ty T (Ty_FVar X)) v1 v2 <->
  value_rel [R] F T v1 v2.
Proof.
  intros T F X R v1 v2 Hlc Hfresh.
  unfold open_ty.
  transitivity (value_rel [R] (set_rel F X R) T v1 v2).
  - eapply value_rel_open_same with (k := 0) (P := []); eauto.
    intros B a b; simpl. unfold set_rel. rewrite Nat.eqb_refl.
    reflexivity.
  - apply value_rel_fresh; exact Hfresh.
Qed.

Lemma expr_rel_app : forall B F A C f1 f2 a1 a2,
  locally_closed_tm a1 -> locally_closed_tm a2 ->
  expr_rel (value_rel B F (Ty_Arrow A C)) f1 f2 ->
  expr_rel (value_rel B F A) a1 a2 ->
  expr_rel (value_rel B F C) (tm_app f1 a1) (tm_app f2 a2).
Proof.
  intros B F A C f1 f2 a1 a2 Hlc1 Hlc2
    [g1 [g2 [Hg1 [Hg2 Hfun]]]]
    [w1 [w2 [Hw1 [Hw2 Harg]]]].
  simpl in Hfun. destruct Hfun as [Hvg1 [Hvg2 Hfun]].
  specialize (Hfun w1 w2 Harg).
  eapply expr_rel_step_back; [| | exact Hfun].
  - eapply multi_trans; [apply multi_app1; eassumption |].
    apply multi_app2; assumption.
  - eapply multi_trans; [apply multi_app1; eassumption |].
    apply multi_app2; assumption.
Qed.

Lemma expr_rel_tapp : forall F T U f1 f2 U1 U2,
  lc_ty_at 1 T -> locally_closed_ty U ->
  locally_closed_ty U1 -> locally_closed_ty U2 ->
  expr_rel (value_rel [] F (Ty_All T)) f1 f2 ->
  expr_rel (value_rel [] F (open_ty T U))
    (tm_tapp f1 U1) (tm_tapp f2 U2).
Proof.
  intros F T U f1 f2 U1 U2 HT HU HU1 HU2
    [g1 [g2 [Hg1 [Hg2 Hforall]]]].
  simpl in Hforall. destruct Hforall as [_ [_ Hforall]].
  specialize (Hforall U1 U2 (value_rel [] F U) HU1 HU2).
  eapply expr_rel_step_back; [| |].
  - eapply multi_tapp; eassumption.
  - eapply multi_tapp; eassumption.
  - apply (proj2 (expr_rel_ext _ _
      (fun a b => value_rel_open_closed T U F a b HT HU) _ _)).
    exact Hforall.
Qed.

Lemma expr_rel_if : forall B F T c1 c2 a1 a2 b1 b2,
  locally_closed_tm a1 -> locally_closed_tm a2 ->
  locally_closed_tm b1 -> locally_closed_tm b2 ->
  expr_rel (value_rel B F Ty_Bool) c1 c2 ->
  expr_rel (value_rel B F T) a1 a2 ->
  expr_rel (value_rel B F T) b1 b2 ->
  expr_rel (value_rel B F T)
    (tm_if c1 a1 b1) (tm_if c2 a2 b2).
Proof.
  intros B F T c1 c2 a1 a2 b1 b2 Ha1 Ha2 Hb1 Hb2
    [w1 [w2 [Hc1 [Hc2 Hbool]]]] Hthen Helse.
  simpl in Hbool. destruct Hbool as [_ [_ [[E1 E2] | [E1 E2]]]]; subst.
  - eapply expr_rel_step_back; [| | exact Hthen].
    + eapply multi_trans; [apply multi_if; eassumption |].
      eapply multi_step; [apply ST_IfTrue; eassumption | constructor].
    + eapply multi_trans; [apply multi_if; eassumption |].
      eapply multi_step; [apply ST_IfTrue; eassumption | constructor].
  - eapply expr_rel_step_back; [| | exact Helse].
    + eapply multi_trans; [apply multi_if; eassumption |].
      eapply multi_step; [apply ST_IfFalse; eassumption | constructor].
    + eapply multi_trans; [apply multi_if; eassumption |].
      eapply multi_step; [apply ST_IfFalse; eassumption | constructor].
Qed.

Lemma lc_ty_open : forall T k U,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; simpl.
  - assert (n < S k) by (inversion HT; lia).
    destruct (Nat.eqb k n) eqn:E.
    + eapply lc_ty_weaken; [exact HU | lia].
    + apply Nat.eqb_neq in E. constructor; lia.
  - constructor.
  - assert (H1 : lc_ty_at (S k) T1) by (inversion HT; assumption).
    assert (H2 : lc_ty_at (S k) T2) by (inversion HT; assumption).
    constructor; eauto.
  - assert (H1 : lc_ty_at (S (S k)) T) by (inversion HT; assumption).
    constructor. eauto.
  - constructor.
Qed.

Lemma has_type_type_lc : forall D G t T,
  has_type D G t T -> locally_closed_ty T.
Proof.
  intros D G t T H; induction H; unfold locally_closed_ty in *.
  - eapply wf_ty_lc; eassumption.
  - constructor; [eapply wf_ty_lc; eassumption |].
    exact (H1 (fresh L) (fresh_not_in L)).
  - inversion IHhas_type1; assumption.
  - constructor. eapply lc_ty_open_inv.
    exact (H0 (fresh L) (fresh_not_in L)).
  - inversion IHhas_type; subst.
    eapply lc_ty_open; eauto using wf_ty_lc.
  - constructor.
  - constructor.
  - assumption.
  - assumption.
Qed.

Lemma value_rel_values : forall B F T v1 v2,
  value_rel B F T v1 v2 -> value v1 /\ value v2.
Proof.
  intros B F T v1 v2 H; destruct T; simpl in H;
    destruct H as [H1 [H2 _]].
  all: split; assumption.
Qed.

Definition term_context_rel (G : context) (F : rel_env)
    (sigma1 sigma2 : atom -> tm) : Prop :=
  forall x T, lookup_context x G = Some T ->
    value_rel [] F T (sigma1 x) (sigma2 x).

Lemma term_context_rel_update : forall G F sigma1 sigma2 x T v1 v2,
  term_context_rel G F sigma1 sigma2 ->
  value_rel [] F T v1 v2 ->
  term_context_rel (update G x T) F
    (set_tm sigma1 x v1) (set_tm sigma2 x v2).
Proof.
  intros G F sigma1 sigma2 x T v1 v2 Henv HR y A Hlookup.
  unfold update in Hlookup; simpl in Hlookup.
  rewrite Nat.eqb_sym in Hlookup.
  unfold set_tm. destruct (Nat.eqb x y) eqn:E.
  - inversion Hlookup; subst; exact HR.
  - apply Henv; exact Hlookup.
Qed.

Lemma lookup_context_type_atoms : forall G x T X,
  lookup_context x G = Some T ->
  In X (ty_atoms T) -> In X (context_type_atoms G).
Proof.
  induction G as [|[y A] G IH]; intros x T X Hlookup HX; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. apply in_or_app; left; exact HX.
    + apply in_or_app; right; eauto.
Qed.

Lemma term_context_rel_type_fresh : forall G F sigma1 sigma2 X R,
  ~ In X (context_type_atoms G) ->
  term_context_rel G F sigma1 sigma2 ->
  term_context_rel G (set_rel F X R) sigma1 sigma2.
Proof.
  intros G F sigma1 sigma2 X R Hfresh Henv x T Hlookup.
  assert (Hnot : ~ In X (ty_atoms T)).
  { intro HX; apply Hfresh; eapply lookup_context_type_atoms; eauto. }
  apply (proj2 (value_rel_fresh T [] F X R _ _ Hnot)).
  apply Henv; assumption.
Qed.

Definition type_context_rel (D : ty_context)
    (theta1 theta2 : atom -> ty) (F : rel_env) : Prop :=
  forall X, In X D ->
    locally_closed_ty (theta1 X) /\ locally_closed_ty (theta2 X).

Lemma inst_tm_typed_lc : forall D G t T theta sigma,
  has_type D G t T ->
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  locally_closed_tm (inst_tm theta sigma t).
Proof.
  intros D G t T theta sigma H Htheta Hsigma.
  exact (inst_tm_lc 0 0 t theta sigma
    (has_type_lc D G t T H) Htheta Hsigma).
Qed.

Lemma set_ty_closed : forall theta X U,
  (forall Y, locally_closed_ty (theta Y)) ->
  locally_closed_ty U ->
  forall Y, locally_closed_ty (set_ty theta X U Y).
Proof.
  intros theta X U Htheta HU Y; unfold set_ty.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma set_tm_closed : forall sigma x v,
  (forall y, locally_closed_tm (sigma y)) ->
  locally_closed_tm v ->
  forall y, locally_closed_tm (set_tm sigma x v y).
Proof.
  intros sigma x v Hsigma Hv y; unfold set_tm.
  destruct (Nat.eqb x y); auto.
Qed.

Theorem fundamental : forall D G t T,
  has_type D G t T ->
  forall theta1 theta2 sigma1 sigma2 F,
    (forall X, locally_closed_ty (theta1 X)) ->
    (forall X, locally_closed_ty (theta2 X)) ->
    (forall x, locally_closed_tm (sigma1 x)) ->
    (forall x, locally_closed_tm (sigma2 x)) ->
    term_context_rel G F sigma1 sigma2 ->
    expr_rel (value_rel [] F T)
      (inst_tm theta1 sigma1 t) (inst_tm theta2 sigma2 t).
Proof.
  intros D G t T Htyping; induction Htyping;
    intros theta1 theta2 sigma1 sigma2 F Htheta1 Htheta2 Hsigma1 Hsigma2 Henv;
    simpl.
  - apply expr_rel_step_back with (b1 := sigma1 x) (b2 := sigma2 x);
      try constructor.
    exists (sigma1 x), (sigma2 x); repeat split; try constructor.
    apply Henv; assumption.
  - assert (Htyped : has_type Delta Gamma (tm_abs T1 t2)
        (Ty_Arrow T1 T2)) by (eapply T_Abs; eauto).
    assert (Hlc1 : locally_closed_tm (inst_tm theta1 sigma1 (tm_abs T1 t2))).
    { eapply inst_tm_typed_lc; eauto. }
    assert (Hlc2 : locally_closed_tm (inst_tm theta2 sigma2 (tm_abs T1 t2))).
    { eapply inst_tm_typed_lc; eauto. }
    exists (tm_abs (inst_ty theta1 T1) (inst_tm theta1 sigma1 t2)),
           (tm_abs (inst_ty theta2 T1) (inst_tm theta2 sigma2 t2)).
    repeat split; try constructor.
    all: try exact Hlc1; try exact Hlc2.
    intros a1 a2 Harg.
    destruct (value_rel_values [] F T1 a1 a2 Harg) as [Hva1 Hva2].
    pose (x := fresh (L ++ tm_atoms t2)).
    assert (HxL : ~ In x L).
    { unfold x; intro C; apply fresh_not_in with (L := L ++ tm_atoms t2).
      apply in_or_app; left; exact C. }
    assert (Hxt : ~ In x (tm_atoms t2)).
    { unfold x; intro C; apply fresh_not_in with (L := L ++ tm_atoms t2).
      apply in_or_app; right; exact C. }
    pose proof (H1 x HxL theta1 theta2
      (set_tm sigma1 x a1) (set_tm sigma2 x a2) F
      Htheta1 Htheta2
      (set_tm_closed sigma1 x a1 Hsigma1 (value_lc a1 Hva1))
      (set_tm_closed sigma2 x a2 Hsigma2 (value_lc a2 Hva2))
      (term_context_rel_update Gamma F sigma1 sigma2 x T1 a1 a2 Henv Harg))
      as Hbody.
    unfold open_tm in Hbody.
    rewrite (inst_tm_open_fvar t2 0 theta1 sigma1 x a1 Hxt Hsigma1) in Hbody.
    rewrite (inst_tm_open_fvar t2 0 theta2 sigma2 x a2 Hxt Hsigma2) in Hbody.
    eapply expr_rel_step_back; [| | exact Hbody].
    + eapply multi_step; [apply ST_AppAbs; assumption | constructor].
    + eapply multi_step; [apply ST_AppAbs; assumption | constructor].
  - eapply expr_rel_app; eauto using inst_tm_typed_lc.
  - assert (Htyped : has_type Delta Gamma (tm_tabs t) (Ty_All T))
      by (eapply T_TAbs; eauto).
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (has_type_type_lc _ _ _ _ Htyped) as Hlc.
      inversion Hlc; assumption. }
    assert (Hlc1 : locally_closed_tm (inst_tm theta1 sigma1 (tm_tabs t))).
    { eapply inst_tm_typed_lc; eauto. }
    assert (Hlc2 : locally_closed_tm (inst_tm theta2 sigma2 (tm_tabs t))).
    { eapply inst_tm_typed_lc; eauto. }
    exists (tm_tabs (inst_tm theta1 sigma1 t)),
           (tm_tabs (inst_tm theta2 sigma2 t)).
    repeat split; try constructor.
    all: try exact Hlc1; try exact Hlc2.
    intros U1 U2 R HU1 HU2.
    pose (X := fresh (L ++ tm_type_atoms t ++ ty_atoms T ++ context_type_atoms Gamma)).
    assert (HXL : ~ In X L).
    { unfold X; intro C; apply fresh_not_in with
        (L := L ++ tm_type_atoms t ++ ty_atoms T ++ context_type_atoms Gamma).
      apply in_or_app; left; exact C. }
    assert (HXt : ~ In X (tm_type_atoms t)).
    { unfold X; intro C; apply fresh_not_in with
        (L := L ++ tm_type_atoms t ++ ty_atoms T ++ context_type_atoms Gamma).
      apply in_or_app; right; apply in_or_app; left; exact C. }
    assert (HXT : ~ In X (ty_atoms T)).
    { unfold X; intro C; apply fresh_not_in with
        (L := L ++ tm_type_atoms t ++ ty_atoms T ++ context_type_atoms Gamma).
      apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; left; exact C. }
    assert (HXG : ~ In X (context_type_atoms Gamma)).
    { unfold X; intro C; apply fresh_not_in with
        (L := L ++ tm_type_atoms t ++ ty_atoms T ++ context_type_atoms Gamma).
      apply in_or_app; right; apply in_or_app; right;
        apply in_or_app; right; exact C. }
    pose proof (H0 X HXL
      (set_ty theta1 X U1) (set_ty theta2 X U2)
      sigma1 sigma2 (set_rel F X R)
      (set_ty_closed theta1 X U1 Htheta1 HU1)
      (set_ty_closed theta2 X U2 Htheta2 HU2)
      Hsigma1 Hsigma2
      (term_context_rel_type_fresh Gamma F sigma1 sigma2 X R HXG Henv))
      as Hbody.
    unfold open_tm_ty in Hbody.
    rewrite (inst_tm_open_ty_fvar t 0 theta1 sigma1 X U1 HXt Htheta1 Hsigma1)
      in Hbody.
    rewrite (inst_tm_open_ty_fvar t 0 theta2 sigma2 X U2 HXt Htheta2 Hsigma2)
      in Hbody.
    eapply expr_rel_step_back; [| |].
    + eapply multi_step; [apply ST_TAppTabs; assumption | constructor].
    + eapply multi_step; [apply ST_TAppTabs; assumption | constructor].
    + apply (proj1 (expr_rel_ext _ _
        (fun a b => value_rel_open_fvar T F X R a b HTlc HXT) _ _)).
      exact Hbody.
  - assert (HTlc : lc_ty_at 1 T).
    { pose proof (has_type_type_lc _ _ _ _ Htyping) as Hlc.
      inversion Hlc; assumption. }
    eapply expr_rel_tapp; eauto using wf_ty_lc.
    + eapply inst_ty_lc; [eapply wf_ty_lc; eassumption | exact Htheta1].
    + eapply inst_ty_lc; [eapply wf_ty_lc; eassumption | exact Htheta2].
  - exists tm_true, tm_true; repeat split; try constructor.
    simpl; repeat split; auto using value.
  - exists tm_false, tm_false.
    split; [constructor |]. split; [constructor |].
    simpl. repeat split; auto using value.
  - eapply expr_rel_if; eauto using inst_tm_typed_lc.
  - eapply expr_rel_choice; eauto using inst_tm_typed_lc.
Qed.

Lemma ty_atoms_open_superset : forall T k U X,
  In X (ty_atoms T) ->
  In X (ty_atoms (open_ty_rec k U T)).
Proof.
  induction T; intros k U X H; simpl in *;
    repeat rewrite in_app_iff in *; eauto; try tauto.
  destruct H; [left; eapply IHT1 | right; eapply IHT2]; eassumption.
Qed.

Lemma tm_atoms_open_superset : forall t k x y,
  In y (tm_atoms t) ->
  In y (tm_atoms (open_tm_rec k (tm_fvar x) t)).
Proof.
  induction t; intros k x y H; simpl in *;
    repeat rewrite in_app_iff in *; eauto; try tauto.
  all: repeat match goal with H : _ \/ _ |- _ => destruct H end;
    solve [left; eauto | right; left; eauto | right; right; eauto | right; eauto].
Qed.

Lemma tm_type_atoms_open_tm : forall t k x,
  tm_type_atoms (open_tm_rec k (tm_fvar x) t) = tm_type_atoms t.
Proof.
  induction t; intros k x; simpl; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite (IHt (S k) x); reflexivity.
  - rewrite (IHt1 k x), (IHt2 k x); reflexivity.
  - rewrite (IHt k x); reflexivity.
  - rewrite (IHt k x); reflexivity.
  - rewrite (IHt1 k x), (IHt2 k x), (IHt3 k x); reflexivity.
  - rewrite (IHt1 k x), (IHt2 k x); reflexivity.
Qed.

Lemma tm_atoms_open_ty : forall t K U,
  tm_atoms (open_tm_ty_rec K U t) = tm_atoms t.
Proof.
  induction t; intros K U; simpl; try reflexivity.
  - rewrite (IHt K U); reflexivity.
  - rewrite (IHt1 K U), (IHt2 K U); reflexivity.
  - rewrite (IHt (S K) U); reflexivity.
  - rewrite (IHt K U); reflexivity.
  - rewrite (IHt1 K U), (IHt2 K U), (IHt3 K U); reflexivity.
  - rewrite (IHt1 K U), (IHt2 K U); reflexivity.
Qed.

Lemma tm_type_atoms_open_ty_superset : forall t K U X,
  In X (tm_type_atoms t) ->
  In X (tm_type_atoms (open_tm_ty_rec K U t)).
Proof.
  induction t; intros K U X H; simpl in *;
    repeat rewrite in_app_iff in *; eauto using ty_atoms_open_superset;
    try tauto.
  all: repeat match goal with H : _ \/ _ |- _ => destruct H end;
    solve [left; eauto using ty_atoms_open_superset |
           right; left; eauto using ty_atoms_open_superset |
           right; right; eauto using ty_atoms_open_superset |
           right; eauto using ty_atoms_open_superset].
Qed.

Lemma wf_ty_atoms : forall D T,
  wf_ty D T -> forall X, In X (ty_atoms T) -> In X D.
Proof.
  intros D T Hwf; induction Hwf; intros Y HY; simpl in *.
  - destruct HY as [E | []]; subst; assumption.
  - apply in_app_iff in HY; destruct HY;
      [apply IHHwf1 | apply IHHwf2]; assumption.
  - pose (X := fresh (L ++ ty_atoms T)).
    assert (HXL : ~ In X L).
    { unfold X; intro C; apply fresh_not_in with (L := L ++ ty_atoms T).
      apply in_or_app; left; exact C. }
    assert (HXT : ~ In X (ty_atoms T)).
    { unfold X; intro C; apply fresh_not_in with (L := L ++ ty_atoms T).
      apply in_or_app; right; exact C. }
    specialize (H0 X HXL Y).
    assert (HY' : In Y (ty_atoms (open_ty T (Ty_FVar X)))).
    { unfold open_ty; eapply ty_atoms_open_superset; exact HY. }
    specialize (H0 HY'). simpl in H0. destruct H0 as [E | HD].
    + subst; contradiction.
    + exact HD.
  - contradiction.
Qed.

Lemma has_type_term_atoms : forall D G t T,
  has_type D G t T ->
  forall y, In y (tm_atoms t) ->
    exists A, lookup_context y G = Some A.
Proof.
  intros D G t T Htyping; induction Htyping; intros y Hy; simpl in Hy.
  - destruct Hy as [E | []]; subst. eauto.
  - pose (x := fresh (L ++ tm_atoms t2)).
    assert (HxL : ~ In x L).
    { unfold x; intro C; apply fresh_not_in with (L := L ++ tm_atoms t2).
      apply in_or_app; left; exact C. }
    assert (Hxt : ~ In x (tm_atoms t2)).
    { unfold x; intro C; apply fresh_not_in with (L := L ++ tm_atoms t2).
      apply in_or_app; right; exact C. }
    assert (Hyopen : In y (tm_atoms (open_tm t2 (tm_fvar x)))).
    { unfold open_tm. eapply tm_atoms_open_superset; exact Hy. }
    destruct (H1 x HxL y Hyopen) as [A HA].
    simpl in HA.
    assert (y <> x) by (intro E; subst; contradiction).
    destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E; contradiction.
    + exists A; exact HA.
  - apply in_app_iff in Hy; destruct Hy;
      [apply IHHtyping1 | apply IHHtyping2]; assumption.
  - pose (X := fresh L).
    assert (HXL : ~ In X L) by (unfold X; apply fresh_not_in).
    apply (H0 X HXL y).
    unfold open_tm_ty. rewrite tm_atoms_open_ty. exact Hy.
  - apply IHHtyping; exact Hy.
  - contradiction.
  - contradiction.
  - repeat rewrite in_app_iff in Hy.
    destruct Hy as [Hy | [Hy | Hy]].
    + apply IHHtyping1; exact Hy.
    + apply IHHtyping2; exact Hy.
    + apply IHHtyping3; exact Hy.
  - apply in_app_iff in Hy; destruct Hy;
      [apply IHHtyping1 | apply IHHtyping2]; assumption.
Qed.

Lemma has_type_type_atoms : forall D G t T,
  has_type D G t T ->
  forall X, In X (tm_type_atoms t) -> In X D.
Proof.
  intros D G t T Htyping; induction Htyping; intros Y HY; simpl in HY.
  - contradiction.
  - apply in_app_iff in HY; destruct HY as [HY | HY].
    + eapply wf_ty_atoms; eauto.
    + pose (x := fresh L).
      assert (HxL : ~ In x L) by (unfold x; apply fresh_not_in).
      apply (H1 x HxL Y).
      unfold open_tm. rewrite tm_type_atoms_open_tm. exact HY.
  - apply in_app_iff in HY; destruct HY;
      [apply IHHtyping1 | apply IHHtyping2]; assumption.
  - pose (X := fresh (L ++ tm_type_atoms t)).
    assert (HXL : ~ In X L).
    { unfold X; intro C; apply fresh_not_in with (L := L ++ tm_type_atoms t).
      apply in_or_app; left; exact C. }
    assert (HXT : ~ In X (tm_type_atoms t)).
    { unfold X; intro C; apply fresh_not_in with (L := L ++ tm_type_atoms t).
      apply in_or_app; right; exact C. }
    assert (HYopen : In Y (tm_type_atoms (open_tm_ty t (Ty_FVar X)))).
    { unfold open_tm_ty. eapply tm_type_atoms_open_ty_superset; exact HY. }
    specialize (H0 X HXL Y HYopen). simpl in H0.
    destruct H0 as [E | HD].
    + subst; contradiction.
    + exact HD.
  - apply in_app_iff in HY; destruct HY as [HY | HY].
    + apply IHHtyping; exact HY.
    + eapply wf_ty_atoms; eauto.
  - contradiction.
  - contradiction.
  - repeat rewrite in_app_iff in HY.
    destruct HY as [HY | [HY | HY]].
    + apply IHHtyping1; exact HY.
    + apply IHHtyping2; exact HY.
    + apply IHHtyping3; exact HY.
  - apply in_app_iff in HY; destruct HY;
      [apply IHHtyping1 | apply IHHtyping2]; assumption.
Qed.

Lemma inst_ty_no_atoms : forall T theta,
  (forall X, ~ In X (ty_atoms T)) ->
  inst_ty theta T = T.
Proof.
  induction T; intros theta Hnone; simpl; try reflexivity.
  - exfalso; apply (Hnone a); simpl; auto.
  - f_equal.
    + apply IHT1. intros X HX; apply (Hnone X); simpl;
        apply in_or_app; left; exact HX.
    + apply IHT2. intros X HX; apply (Hnone X); simpl;
        apply in_or_app; right; exact HX.
  - f_equal. apply IHT; exact Hnone.
Qed.

Lemma inst_tm_no_atoms : forall t theta sigma,
  (forall x, ~ In x (tm_atoms t)) ->
  (forall X, ~ In X (tm_type_atoms t)) ->
  inst_tm theta sigma t = t.
Proof.
  induction t; intros theta sigma Hterm Htype; simpl; try reflexivity.
  - exfalso; apply (Hterm a); simpl; auto.
  - f_equal.
    + apply inst_ty_no_atoms. intros X HX; apply (Htype X).
      simpl; apply in_or_app; left; exact HX.
    + apply IHt; auto. intros X HX; apply (Htype X).
      simpl; apply in_or_app; right; exact HX.
  - f_equal.
    + apply IHt1; intros X HX; [apply (Hterm X) | apply (Htype X)];
        simpl; apply in_or_app; left; exact HX.
    + apply IHt2; intros X HX; [apply (Hterm X) | apply (Htype X)];
        simpl; apply in_or_app; right; exact HX.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; auto. intros X HX; apply (Htype X).
      simpl; apply in_or_app; left; exact HX.
    + apply inst_ty_no_atoms. intros X HX; apply (Htype X).
      simpl; apply in_or_app; right; exact HX.
  - f_equal.
    + apply IHt1; intros X HX; [apply (Hterm X) | apply (Htype X)];
        simpl; apply in_or_app; left; exact HX.
    + apply IHt2; intros X HX; [apply (Hterm X) | apply (Htype X)];
        simpl; apply in_or_app; right; apply in_or_app; left; exact HX.
    + apply IHt3; intros X HX; [apply (Hterm X) | apply (Htype X)];
        simpl; apply in_or_app; right; apply in_or_app; right; exact HX.
  - f_equal.
    + apply IHt1; intros X HX; [apply (Hterm X) | apply (Htype X)];
        simpl; apply in_or_app; left; exact HX.
    + apply IHt2; intros X HX; [apply (Hterm X) | apply (Htype X)];
        simpl; apply in_or_app; right; exact HX.
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
  intros t Htyping U v HU Hv _.
  set (theta := fun _ : atom => Ty_Bool).
  set (sigma := fun _ : atom => tm_true).
  set (F := fun (_ : atom) (_ _ : tm) => False).
  assert (Htheta : forall X, locally_closed_ty (theta X)).
  { intros X; unfold theta, locally_closed_ty; constructor. }
  assert (Hsigma : forall x, locally_closed_tm (sigma x)).
  { intros x; unfold sigma, locally_closed_tm; constructor. }
  assert (Henv : term_context_rel empty F sigma sigma).
  { intros x T Hlookup; discriminate. }
  assert (Hterm : forall x, ~ In x (tm_atoms t)).
  { intros x HX.
    destruct (has_type_term_atoms [] empty t
      (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))
      Htyping x HX) as [A HA].
    discriminate. }
  assert (Htype : forall X, ~ In X (tm_type_atoms t)).
  { intros X HX.
    pose proof (has_type_type_atoms [] empty t
      (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))
      Htyping X HX) as HC.
    contradiction. }
  pose proof (fundamental [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))
    Htyping theta theta sigma sigma F
    Htheta Htheta Hsigma Hsigma Henv) as Hfund.
  rewrite (inst_tm_no_atoms t theta sigma Hterm Htype) in Hfund.
  destruct Hfund as [f1 [f2 [Hf1 [Hf2 Hpoly]]]].
  simpl in Hpoly. destruct Hpoly as [_ [_ Hpoly]].
  set (R := fun (a b : tm) => a = v /\ b = v).
  assert (HUlc : locally_closed_ty U) by (eapply wf_ty_lc; eassumption).
  specialize (Hpoly U U R HUlc HUlc).
  assert (Htapp : expr_rel
    (value_rel [R] F (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))
    (tm_tapp t U) (tm_tapp t U)).
  { eapply expr_rel_step_back; [| | exact Hpoly];
      eapply multi_tapp; eassumption. }
  assert (Harg : expr_rel (value_rel [R] F (Ty_BVar 0)) v v).
  { exists v, v. repeat split; try constructor.
    simpl. repeat split; auto. unfold R; auto. }
  pose proof (expr_rel_app [R] F (Ty_BVar 0) (Ty_BVar 0)
    (tm_tapp t U) (tm_tapp t U) v v
    (value_lc v Hv) (value_lc v Hv) Htapp Harg) as Happ.
  destruct Happ as [w1 [w2 [Hstep1 [_ Hresult]]]].
  simpl in Hresult. destruct Hresult as [_ [_ [E _]]].
  subst w1. exact Hstep1.
Qed.

End SystemFParametricityIfNondeterminismHardTask.
