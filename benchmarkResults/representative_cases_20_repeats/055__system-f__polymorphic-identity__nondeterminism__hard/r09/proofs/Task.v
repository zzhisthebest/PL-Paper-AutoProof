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

(* ============================================================ *)
(* Auxiliary infrastructure for the logical relation.           *)
(* ============================================================ *)

Definition Rel := tm -> tm -> Prop.

Definition bot_rel : Rel := fun _ _ => False.

Fixpoint max_atom_list (l : list atom) : atom :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (max_atom_list l')
  end.

Definition fresh_atom (l : list atom) : atom := S (max_atom_list l).

Lemma max_atom_list_ge : forall l x, In x l -> x <= max_atom_list l.
Proof.
  intros l x H. induction l as [| a l' IH]; simpl in *.
  - inversion H.
  - destruct H as [-> | H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; assumption | apply Nat.le_max_r].
Qed.

Lemma fresh_atom_notin : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l H. unfold fresh_atom in H.
  pose proof (max_atom_list_ge l _ H). lia.
Qed.

Fixpoint insert_at (k : nat) (r : Rel) (env : list Rel) : list Rel :=
  match env with
  | [] => [r]
  | e :: env' =>
      match k with
      | 0 => r :: e :: env'
      | S k' => e :: insert_at k' r env'
      end
  end.

Lemma insert_at_zero : forall (r : Rel) env, insert_at 0 r env = r :: env.
Proof. intros r env. destruct env; simpl; reflexivity. Qed.

Lemma nth_insert_at_lt : forall env k r i,
  k <= length env -> i < k ->
  nth i (insert_at k r env) bot_rel = nth i env bot_rel.
Proof.
  induction env as [| e env' IH]; intros k r i Hk Hi.
  - simpl in Hk. assert (k = 0) by lia. lia.
  - destruct k as [| k'].
    + lia.
    + simpl. destruct i as [| i'].
      * reflexivity.
      * apply IH; simpl in Hk; lia.
Qed.

Lemma nth_insert_at_eq : forall env k r,
  k <= length env -> nth k (insert_at k r env) bot_rel = r.
Proof.
  induction env as [| e env' IH]; intros k r Hk.
  - simpl in Hk. assert (k = 0) by lia. subst. reflexivity.
  - destruct k as [| k']; simpl.
    + reflexivity.
    + apply IH. simpl in Hk. lia.
Qed.

Lemma nth_insert_at_eq_app : forall env k (r : Rel) a b,
  k <= length env ->
  (nth k (insert_at k r env) bot_rel a b <-> r a b).
Proof.
  intros env k r a b Hk. rewrite (nth_insert_at_eq env k r Hk). tauto.
Qed.

Lemma nth_insert_at_lt_app : forall env k (r : Rel) i a b,
  k <= length env -> i < k ->
  (nth i (insert_at k r env) bot_rel a b <-> nth i env bot_rel a b).
Proof.
  intros env k r i a b Hk Hi. rewrite (nth_insert_at_lt env k r i Hk Hi). tauto.
Qed.

(* Free type variables of a type *)
Fixpoint ty_fv (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_fv T1 ++ ty_fv T2
  | Ty_All T1 => ty_fv T1
  end.

(* Free term variables of a term *)
Fixpoint tm_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => tm_fv t1
  | tm_app t1 t2 => tm_fv t1 ++ tm_fv t2
  | tm_tabs t1 => tm_fv t1
  | tm_tapp t1 _ => tm_fv t1
  | tm_choice t1 t2 => tm_fv t1 ++ tm_fv t2
  end.

(* Free type variables occurring in a term's annotations *)
Fixpoint tm_ty_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T t1 => ty_fv T ++ tm_ty_fv t1
  | tm_app t1 t2 => tm_ty_fv t1 ++ tm_ty_fv t2
  | tm_tabs t1 => tm_ty_fv t1
  | tm_tapp t1 T => tm_ty_fv t1 ++ ty_fv T
  | tm_choice t1 t2 => tm_ty_fv t1 ++ tm_ty_fv t2
  end.

(* Free type variables occurring in a term context *)
Fixpoint ctx_fv (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x, T) :: Gamma' => ty_fv T ++ ctx_fv Gamma'
  end.

Lemma ctx_fv_lookup : forall Gamma y T,
  lookup_context y Gamma = Some T ->
  forall X, In X (ty_fv T) -> In X (ctx_fv Gamma).
Proof.
  intros Gamma. induction Gamma as [| [z S] Gamma' IH]; intros y T Hlook X HX.
  - simpl in Hlook. discriminate.
  - simpl in Hlook. simpl. destruct (Nat.eqb y z) eqn:E.
    + apply Nat.eqb_eq in E. subst y. injection Hlook as Heq. subst S.
      apply in_or_app. auto.
    + apply in_or_app. right. apply (IH y T Hlook X HX).
Qed.

(* Simultaneous type-variable substitution on types *)
Fixpoint ty_subst_env (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst_env theta T1) (ty_subst_env theta T2)
  | Ty_All T1 => Ty_All (ty_subst_env theta T1)
  end.

(* Simultaneous type-variable substitution on terms *)
Fixpoint tm_ty_subst_env (theta : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst_env theta T) (tm_ty_subst_env theta t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst_env theta t1) (tm_ty_subst_env theta t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst_env theta t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst_env theta t1) (ty_subst_env theta T)
  | tm_choice t1 t2 => tm_choice (tm_ty_subst_env theta t1) (tm_ty_subst_env theta t2)
  end.

(* Simultaneous term-variable substitution *)
Fixpoint tm_subst_env (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs T (tm_subst_env sigma t1)
  | tm_app t1 t2 => tm_app (tm_subst_env sigma t1) (tm_subst_env sigma t2)
  | tm_tabs t1 => tm_tabs (tm_subst_env sigma t1)
  | tm_tapp t1 T => tm_tapp (tm_subst_env sigma t1) T
  | tm_choice t1 t2 => tm_choice (tm_subst_env sigma t1) (tm_subst_env sigma t2)
  end.

Definition update_sigma (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then u else sigma y.

Definition update_xi (xi : atom -> Rel) (X : atom) (r : Rel) : atom -> Rel :=
  fun Y => if Nat.eqb Y X then r else xi Y.

Lemma update_xi_neq : forall xi X rho Y, Y <> X -> update_xi xi X rho Y = xi Y.
Proof.
  intros. unfold update_xi. destruct (Nat.eqb Y X) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.


Lemma ty_subst_env_ext : forall theta1 theta2 T,
  (forall X, In X (ty_fv T) -> theta1 X = theta2 X) ->
  ty_subst_env theta1 T = ty_subst_env theta2 T.
Proof.
  intros theta1 theta2 T. induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1];
    intros Hagree; simpl.
  - reflexivity.
  - apply Hagree. simpl. left. reflexivity.
  - rewrite IH1.
    + rewrite IH2.
      * reflexivity.
      * intros Y HY. apply Hagree. apply in_or_app. auto.
    + intros Y HY. apply Hagree. apply in_or_app. auto.
  - rewrite IH1.
    + reflexivity.
    + intros Y HY. apply Hagree. assumption.
Qed.

Lemma tm_ty_subst_env_ext : forall theta1 theta2 t,
  (forall X, In X (tm_ty_fv t) -> theta1 X = theta2 X) ->
  tm_ty_subst_env theta1 t = tm_ty_subst_env theta2 t.
Proof.
  intros theta1 theta2 t.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
    intros Hagree; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (ty_subst_env_ext theta1 theta2 T).
    + rewrite IH1.
      * reflexivity.
      * intros Y HY. apply Hagree. apply in_or_app. auto.
    + intros Y HY. apply Hagree. apply in_or_app. auto.
  - rewrite IH1.
    + rewrite IH2.
      * reflexivity.
      * intros Y HY. apply Hagree. apply in_or_app. auto.
    + intros Y HY. apply Hagree. apply in_or_app. auto.
  - rewrite IH1.
    + reflexivity.
    + intros Y HY. apply Hagree. assumption.
  - rewrite IH1.
    + rewrite (ty_subst_env_ext theta1 theta2 T).
      * reflexivity.
      * intros Y HY. apply Hagree. apply in_or_app. auto.
    + intros Y HY. apply Hagree. apply in_or_app. auto.
  - rewrite IH1.
    + rewrite IH2.
      * reflexivity.
      * intros Y HY. apply Hagree. apply in_or_app. auto.
    + intros Y HY. apply Hagree. apply in_or_app. auto.
Qed.

Lemma tm_subst_env_ext : forall sigma1 sigma2 t,
  (forall x, In x (tm_fv t) -> sigma1 x = sigma2 x) ->
  tm_subst_env sigma1 t = tm_subst_env sigma2 t.
Proof.
  intros sigma1 sigma2 t.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
    intros Hagree; simpl.
  - reflexivity.
  - apply Hagree. simpl. left. reflexivity.
  - rewrite IH1.
    + reflexivity.
    + intros y Hy. apply Hagree. assumption.
  - rewrite IH1.
    + rewrite IH2.
      * reflexivity.
      * intros y Hy. apply Hagree. apply in_or_app. auto.
    + intros y Hy. apply Hagree. apply in_or_app. auto.
  - rewrite IH1.
    + reflexivity.
    + intros y Hy. apply Hagree. assumption.
  - rewrite IH1.
    + reflexivity.
    + intros y Hy. apply Hagree. assumption.
  - rewrite IH1.
    + rewrite IH2.
      * reflexivity.
      * intros y Hy. apply Hagree. apply in_or_app. auto.
    + intros y Hy. apply Hagree. apply in_or_app. auto.
Qed.

Lemma tm_fv_tm_ty_subst_env : forall theta t,
  tm_fv (tm_ty_subst_env theta t) = tm_fv t.
Proof.
  intros theta t.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
    simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma tm_subst_env_id : forall t,
  tm_subst_env (fun x => tm_fvar x) t = t.
Proof.
  intros t.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
    simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma ty_subst_env_id : forall T,
  ty_subst_env (fun X => Ty_FVar X) T = T.
Proof.
  intros T. induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
Qed.

Lemma tm_ty_subst_env_id : forall t,
  tm_ty_subst_env (fun X => Ty_FVar X) t = t.
Proof.
  intros t.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
    simpl.
  - reflexivity.
  - reflexivity.
  - rewrite ty_subst_env_id. rewrite IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, ty_subst_env_id. reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

(* Commutation of opening operations with substitutions *)

Lemma tm_ty_subst_env_open_tm : forall theta d v t,
  tm_ty_subst_env theta (open_tm_rec d v t) =
  open_tm_rec d (tm_ty_subst_env theta v) (tm_ty_subst_env theta t).
Proof.
  intros theta d v t. revert d.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
    intros d; simpl.
  - destruct (Nat.eqb d n); reflexivity.
  - reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1. reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma lc_ty_open_ty_rec_id : forall K T, lc_ty_at K T ->
  forall d U, K <= d -> open_ty_rec d U T = T.
Proof.
  intros K T H.
  induction H as [k i Hi | k X | k T1 T2 H1 IH1 H2 IH2 | k T1 H1 IH1];
    intros d U Hd; simpl.
  - destruct (Nat.eqb d i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - rewrite IH1; auto. rewrite IH2; auto.
  - rewrite IH1. reflexivity. lia.
Qed.

Lemma lc_tm_open_ty_rec_id : forall K k t, lc_tm_at K k t ->
  forall d U, K <= d -> open_tm_ty_rec d U t = t.
Proof.
  intros K k t H.
  induction H as [K k i Hi | K k x | K k T t1 Hty Hr0 IH1
                 | K k t1 t2 Hr1 IH1 Hr2 IH2
                 | K k t1 Hr IH1 | K k t1 T Hr IH1 Hty
                 | K k t1 t2 Hr1 IH1 Hr2 IH2];
    intros d U Hd; simpl.
  - reflexivity.
  - reflexivity.
  - assert (Hann : open_ty_rec d U T = T) by (apply (lc_ty_open_ty_rec_id K T Hty d U Hd)).
    rewrite Hann. rewrite (IH1 d U Hd). reflexivity.
  - rewrite (IH1 d U Hd). rewrite (IH2 d U Hd). reflexivity.
  - rewrite (IH1 (S d) U ltac:(lia)). reflexivity.
  - rewrite (IH1 d U Hd).
    assert (Hann : open_ty_rec d U T = T) by (apply (lc_ty_open_ty_rec_id K T Hty d U Hd)).
    rewrite Hann. reflexivity.
  - rewrite (IH1 d U Hd). rewrite (IH2 d U Hd). reflexivity.
Qed.

Lemma lc_tm_open_tm_rec_id : forall K k t, lc_tm_at K k t ->
  forall d v, k <= d -> open_tm_rec d v t = t.
Proof.
  intros K k t H.
  induction H as [K k i Hi | K k x | K k T t1 Hty Hr0 IH1
                 | K k t1 t2 Hr1 IH1 Hr2 IH2
                 | K k t1 Hr IH1 | K k t1 T Hr IH1 Hty
                 | K k t1 t2 Hr1 IH1 Hr2 IH2];
    intros d v Hd; simpl.
  - destruct (Nat.eqb d i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - rewrite (IH1 (S d) v ltac:(lia)). reflexivity.
  - rewrite (IH1 d v Hd). rewrite (IH2 d v Hd). reflexivity.
  - rewrite (IH1 d v Hd). reflexivity.
  - rewrite (IH1 d v Hd). reflexivity.
  - rewrite (IH1 d v Hd). rewrite (IH2 d v Hd). reflexivity.
Qed.

Lemma tm_subst_env_open_tm : forall sigma d v t,
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  tm_subst_env sigma (open_tm_rec d v t) =
  open_tm_rec d (tm_subst_env sigma v) (tm_subst_env sigma t).
Proof.
  intros sigma d v t Hlc. revert d.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
    intros d; simpl.
  - destruct (Nat.eqb d n); reflexivity.
  - rewrite (lc_tm_open_tm_rec_id 0 0 (sigma x) (Hlc x) d (tm_subst_env sigma v)).
    + reflexivity.
    + lia.
  - rewrite (IH1 (S d)). reflexivity.
  - rewrite (IH1 d). rewrite (IH2 d). reflexivity.
  - rewrite (IH1 d). reflexivity.
  - rewrite (IH1 d). reflexivity.
  - rewrite (IH1 d). rewrite (IH2 d). reflexivity.
Qed.

Lemma tm_subst_env_open_tm_ty : forall sigma d U t,
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  tm_subst_env sigma (open_tm_ty_rec d U t) =
  open_tm_ty_rec d U (tm_subst_env sigma t).
Proof.
  intros sigma d U t Hlc. revert d.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
    intros d; simpl.
  - reflexivity.
  - rewrite (lc_tm_open_ty_rec_id 0 0 (sigma x) (Hlc x) d U). reflexivity. lia.
  - rewrite (IH1 d). reflexivity.
  - rewrite (IH1 d). rewrite (IH2 d). reflexivity.
  - rewrite (IH1 (S d)). reflexivity.
  - rewrite (IH1 d). reflexivity.
  - rewrite (IH1 d). rewrite (IH2 d). reflexivity.
Qed.

Lemma ty_subst_env_open_ty : forall theta,
  (forall X, lc_ty_at 0 (theta X)) ->
  forall d U T,
  ty_subst_env theta (open_ty_rec d U T) =
  open_ty_rec d (ty_subst_env theta U) (ty_subst_env theta T).
Proof.
  intros theta Hlc d U T. revert d.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1]; intros d; simpl.
  - destruct (Nat.eqb d n); reflexivity.
  - rewrite (lc_ty_open_ty_rec_id 0 (theta X) (Hlc X) d (ty_subst_env theta U)).
    + reflexivity.
    + lia.
  - rewrite (IH1 d), (IH2 d). reflexivity.
  - rewrite (IH1 (S d)). reflexivity.
Qed.

Lemma tm_ty_subst_env_open_tm_ty : forall theta,
  (forall X, lc_ty_at 0 (theta X)) ->
  forall d U t,
  tm_ty_subst_env theta (open_tm_ty_rec d U t) =
  open_tm_ty_rec d (ty_subst_env theta U) (tm_ty_subst_env theta t).
Proof.
  intros theta Hlc d U t. revert d.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
    intros d; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (ty_subst_env_open_ty theta Hlc d U T). rewrite (IH1 d). reflexivity.
  - rewrite (IH1 d), (IH2 d). reflexivity.
  - rewrite (IH1 (S d)). reflexivity.
  - rewrite (IH1 d). rewrite (ty_subst_env_open_ty theta Hlc d U T). reflexivity.
  - rewrite (IH1 d), (IH2 d). reflexivity.
Qed.

(* ---------- Monotonicity of locally-closedness ---------- *)

Lemma lc_ty_at_mono : forall k k' T, k <= k' -> lc_ty_at k T -> lc_ty_at k' T.
Proof.
  intros k k' T Hle H. revert k' Hle.
  induction H as [k i Hi | k X | k T1 T2 H1 IH1 H2 IH2 | k T1 H1 IH1];
    intros k' Hle; simpl.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; [apply IH1 | apply IH2]; lia.
  - apply lc_ty_all. apply IH1. lia.
Qed.

Lemma lc_tm_at_mono : forall K K' k k' t,
  K <= K' -> k <= k' -> lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  intros K K' k k' t HK Hk H. revert K' k' HK Hk.
  induction H as [K k i Hi | K k x | K k T t1 Hty Hr IH1
                 | K k t1 t2 Hr1 IH1 Hr2 IH2 | K k t1 Hr IH1
                 | K k t1 T Hr IH1 Hty | K k t1 t2 Hr1 IH1 Hr2 IH2];
    intros K' k' HK Hk; simpl.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply (lc_ty_at_mono K K' T); assumption.
    + apply IH1; lia.
  - apply lc_tm_app; [apply IH1; lia | apply IH2; lia].
  - apply lc_tm_tabs. apply IH1; lia.
  - apply lc_tm_tapp.
    + apply IH1; lia.
    + apply (lc_ty_at_mono K K' T); assumption.
  - apply lc_tm_choice; [apply IH1; lia | apply IH2; lia].
Qed.

(* ---------- Closing: from an opened locally closed object to the body ---------- *)

Lemma lc_ty_open_ty_rec_close : forall k d X T,
  lc_ty_at k (open_ty_rec d (Ty_FVar X) T) -> lc_ty_at (max k (S d)) T.
Proof.
  intros k d X T. revert k d.
  induction T as [n | Y | T1 IH1 T2 IH2 | T1 IH1]; intros k d H; simpl in H.
  - destruct (Nat.eqb d n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      apply lc_ty_bvar. lia.
    + inversion H. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion H as [k0 A B H1 H2 | | |]; subst.
    apply lc_ty_arrow.
    + apply IH1 with (d := d). assumption.
    + apply IH2 with (d := d). assumption.
  - inversion H as [k0 T0 H1 | | |]; subst.
    apply lc_ty_all.
    assert (Heq : S (max k (S d)) = max (S k) (S (S d))) by apply Nat.succ_max_distr.
    rewrite Heq. apply IH1 with (d := S d). assumption.
Qed.

Lemma lc_tm_open_ty_rec_close : forall K k d X t,
  lc_tm_at K k (open_tm_ty_rec d (Ty_FVar X) t) -> lc_tm_at (max K (S d)) k t.
Proof.
  intros K k d X t. revert K k d.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
    intros K k d H; simpl in H.
  - inversion H as [K0 k0 i Hi | | | | | |]; subst. apply lc_tm_bvar. assumption.
  - inversion H as [K0 k0 x0 | | | | | |]; subst. apply lc_tm_fvar.
  - inversion H as [K0 k0 T0 t0 Hty Hbody | | | | | |]; subst.
    apply lc_tm_abs.
    + apply (lc_ty_open_ty_rec_close K d X T). assumption.
    + apply (IH1 K (S k) d). assumption.
  - inversion H as [K0 k0 s1 s2 H1 H2 | | | | | |]; subst.
    apply lc_tm_app.
    + apply (IH1 K k d). assumption.
    + apply (IH2 K k d). assumption.
  - inversion H as [K0 k0 t0 H1 | | | | | |]; subst.
    apply lc_tm_tabs.
    assert (Heq : S (max K (S d)) = max (S K) (S (S d))) by apply Nat.succ_max_distr.
    rewrite Heq. apply (IH1 (S K) k (S d)). assumption.
  - inversion H as [K0 k0 t0 T0 H1 Hty | | | | | |]; subst.
    apply lc_tm_tapp.
    + apply (IH1 K k d). assumption.
    + apply (lc_ty_open_ty_rec_close K d X T). assumption.
  - inversion H as [K0 k0 s1 s2 H1 H2 | | | | | |]; subst.
    apply lc_tm_choice.
    + apply (IH1 K k d). assumption.
    + apply (IH2 K k d). assumption.
Qed.

Lemma lc_tm_open_tm_rec_close : forall K k d x t,
  lc_tm_at K k (open_tm_rec d (tm_fvar x) t) -> lc_tm_at K (max k (S d)) t.
Proof.
  intros K k d x t. revert K k d.
  induction t as [n | y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
    intros K k d H; simpl in H.
  - destruct (Nat.eqb d n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_tm_bvar. lia.
    + inversion H as [K0 k0 i Hi | | | | | |]; subst. apply lc_tm_bvar. lia.
  - inversion H as [K0 k0 x0 | | | | | |]; subst. apply lc_tm_fvar.
  - inversion H as [K0 k0 T0 t0 Hty Hbody | | | | | |]; subst.
    apply lc_tm_abs.
    + assumption.
    + assert (Heq : S (max k (S d)) = max (S k) (S (S d))) by apply Nat.succ_max_distr.
      rewrite Heq. apply (IH1 K (S k) (S d)). assumption.
  - inversion H as [K0 k0 s1 s2 H1 H2 | | | | | |]; subst.
    apply lc_tm_app.
    + apply (IH1 K k d). assumption.
    + apply (IH2 K k d). assumption.
  - inversion H as [K0 k0 t0 H1 | | | | | |]; subst.
    apply lc_tm_tabs.
    apply (IH1 (S K) k d). assumption.
  - inversion H as [K0 k0 t0 T0 H1 Hty | | | | | |]; subst.
    apply lc_tm_tapp.
    + apply (IH1 K k d). assumption.
    + assumption.
  - inversion H as [K0 k0 s1 s2 H1 H2 | | | | | |]; subst.
    apply lc_tm_choice.
    + apply (IH1 K k d). assumption.
    + apply (IH2 K k d). assumption.
Qed.

(* ---------- Well-formedness facts ---------- *)

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H.
  induction H as [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T0 Hbody IHbody].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    pose (X := fresh_atom (L ++ ty_fv T0)).
    assert (HXL : ~ In X L).
    { intro Hc. apply (fresh_atom_notin (L ++ ty_fv T0)). apply in_or_app. left. assumption. }
    assert (HXT : ~ In X (ty_fv T0)).
    { intro Hc. apply (fresh_atom_notin (L ++ ty_fv T0)). apply in_or_app. right. assumption. }
    exact (lc_ty_open_ty_rec_close 0 0 X T0 (IHbody X HXL)).
Qed.

Lemma wf_ty_weaken : forall Delta Delta' T,
  (forall X, In X Delta -> In X Delta') -> wf_ty Delta T -> wf_ty Delta' T.
Proof.
  intros Delta Delta' T Hincl H. revert Delta' Hincl.
  induction H as [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T0 Hbody IHbody];
    intros Delta' Hincl.
  - apply WF_Var. auto.
  - apply WF_Arrow; auto.
  - apply WF_All with (L := L). intros X HX.
    apply (IHbody X HX).
    intros Y [-> | HY].
    + left. reflexivity.
    + right. apply Hincl. assumption.
Qed.

Lemma wf_ty_subst_env : forall Delta' Delta theta T,
  wf_ty Delta' T ->
  (forall X, lc_ty_at 0 (theta X)) ->
  (forall X, In X Delta' -> wf_ty Delta (theta X)) ->
  wf_ty Delta (ty_subst_env theta T).
Proof.
  intros Delta' Delta theta T H. revert Delta theta.
  induction H as [Delta' X Hin | Delta' T1 T2 H1 IH1 H2 IH2 | L Delta' T0 Hbody IHbody];
    intros Delta theta Hlc Htheta.
  - apply Htheta. assumption.
  - apply WF_Arrow; [apply IH1 | apply IH2]; assumption.
  - apply WF_All with (L := L ++ Delta ++ ty_fv T0).
    intros Y HY.
    assert (HYL : ~ In Y L).
    { intro Hc. apply HY. repeat rewrite in_app_iff. auto. }
    assert (HYT : ~ In Y (ty_fv T0)).
    { intro Hc. apply HY. repeat rewrite in_app_iff. auto. }
    set (theta' := fun Z => if Nat.eqb Z Y then Ty_FVar Y else theta Z).
    assert (Hlc' : forall Z, lc_ty_at 0 (theta' Z)).
    { intro Z. unfold theta'. destruct (Nat.eqb Z Y) eqn:E.
      - apply lc_ty_fvar.
      - apply Hlc. }
    assert (Himg : forall Z, In Z (Y :: Delta') -> wf_ty (Y :: Delta) (theta' Z)).
    { intros Z [-> | HZ].
      - unfold theta'. rewrite Nat.eqb_refl. apply WF_Var. left. reflexivity.
      - unfold theta'. destruct (Nat.eqb Z Y) eqn:E.
        + apply Nat.eqb_eq in E. subst Z. apply WF_Var. left. reflexivity.
        + apply wf_ty_weaken with (Delta := Delta). intros W HW. right. assumption.
          apply Htheta. assumption. }
    pose proof (IHbody Y HYL (Y :: Delta) theta' Hlc' Himg) as Hres.
    assert (Heq : ty_subst_env theta' (open_ty T0 (Ty_FVar Y)) =
                  open_ty (ty_subst_env theta T0) (Ty_FVar Y)).
    { unfold open_ty. rewrite (ty_subst_env_open_ty theta' Hlc' 0 (Ty_FVar Y) T0).
      cbn [ty_subst_env]. unfold theta'. rewrite Nat.eqb_refl. simpl.
      assert (HTeq : ty_subst_env theta' T0 = ty_subst_env theta T0).
      { apply (ty_subst_env_ext theta' theta T0). intros Z HZ.
        unfold theta'. destruct (Nat.eqb Z Y) eqn:E.
        - apply Nat.eqb_eq in E. subst Z. contradiction.
        - reflexivity. }
      fold theta'. rewrite HTeq. reflexivity. }
    rewrite Heq in Hres. exact Hres.
Qed.

Lemma wf_open_ty : forall Delta T U,
  wf_ty Delta (Ty_All T) -> wf_ty Delta U -> wf_ty Delta (open_ty T U).
Proof.
  intros Delta T U HAll HU.
  inversion HAll as [| | L Delta' T0 Hbody]; subst.
  pose (X := fresh_atom (L ++ Delta ++ ty_fv T)).
  assert (HXL : ~ In X L).
  { intro Hc. apply (fresh_atom_notin (L ++ Delta ++ ty_fv T)).
    repeat rewrite in_app_iff. auto. }
  assert (HXD : ~ In X Delta).
  { intro Hc. apply (fresh_atom_notin (L ++ Delta ++ ty_fv T)).
    repeat rewrite in_app_iff. auto. }
  assert (HXT : ~ In X (ty_fv T)).
  { intro Hc. apply (fresh_atom_notin (L ++ Delta ++ ty_fv T)).
    repeat rewrite in_app_iff. auto. }
  set (theta := fun Z => if Nat.eqb Z X then U else Ty_FVar Z).
  assert (Hlc : forall Z, lc_ty_at 0 (theta Z)).
  { intro Z. unfold theta. destruct (Nat.eqb Z X).
    - apply (wf_ty_lc Delta U). assumption.
    - apply lc_ty_fvar. }
  assert (Himg : forall Z, In Z (X :: Delta) -> wf_ty Delta (theta Z)).
  { intros Z [-> | HZ].
    - unfold theta. rewrite Nat.eqb_refl. assumption.
    - unfold theta. destruct (Nat.eqb Z X) eqn:E.
      + apply Nat.eqb_eq in E. subst Z. contradiction.
      + apply WF_Var. assumption. }
  pose proof (wf_ty_subst_env (X :: Delta) Delta theta (open_ty T (Ty_FVar X))
              (Hbody X HXL) Hlc Himg) as Hres.
  assert (Heq : ty_subst_env theta (open_ty T (Ty_FVar X)) = open_ty T U).
  { unfold open_ty. rewrite (ty_subst_env_open_ty theta Hlc 0 (Ty_FVar X) T).
    cbn [ty_subst_env]. unfold theta. rewrite Nat.eqb_refl. simpl.
    assert (HTeq : ty_subst_env theta T = T).
    { transitivity (ty_subst_env (fun Z => Ty_FVar Z) T).
      - apply (ty_subst_env_ext theta (fun Z => Ty_FVar Z) T). intros Z HZ.
        unfold theta. destruct (Nat.eqb Z X) eqn:E.
        + apply Nat.eqb_eq in E. subst Z. contradiction.
        + reflexivity.
      - apply ty_subst_env_id. }
    fold theta. rewrite HTeq. reflexivity. }
  rewrite Heq in Hres. exact Hres.
Qed.

Lemma wf_ty_arrow_inv : forall Delta T1 T2,
  wf_ty Delta (Ty_Arrow T1 T2) -> wf_ty Delta T1 /\ wf_ty Delta T2.
Proof.
  intros Delta T1 T2 H. inversion H; subst. split; assumption.
Qed.

(* ---------- Typing implies well-formed type and locally closed term ---------- *)

Lemma has_type_wf_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> wf_ty Delta T /\ lc_tm_at 0 0 t.
Proof.
  intros Delta Gamma t T H.
  induction H as
    [Delta Gamma x T0 Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf1 Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t0 T0 Hbody IHbody
    | Delta Gamma t0 T0 U H1 IH1 HwfU
    | Delta Gamma t1 t2 T0 H1 IH1 H2 IH2].
  - split. apply Hwf. apply lc_tm_fvar.
  - split.
    + apply WF_Arrow.
      * apply Hwf1.
      * exact (proj1 (IHbody (fresh_atom L) (fresh_atom_notin L))).
    + apply lc_tm_abs.
      * apply (wf_ty_lc Delta T1). apply Hwf1.
      * exact (lc_tm_open_tm_rec_close 0 0 0 (fresh_atom L) t2
                 (proj2 (IHbody (fresh_atom L) (fresh_atom_notin L)))).
  - split.
    + exact (proj2 (wf_ty_arrow_inv Delta T1 T2 (proj1 IH1))).
    + apply lc_tm_app; [exact (proj2 IH1) | exact (proj2 IH2)].
  - split.
    + apply WF_All with (L := L). intros X HX. exact (proj1 (IHbody X HX)).
    + apply lc_tm_tabs.
      exact (lc_tm_open_ty_rec_close 0 0 0 (fresh_atom L) t0
               (proj2 (IHbody (fresh_atom L) (fresh_atom_notin L)))).
  - split.
    + apply wf_open_ty; [exact (proj1 IH1) | exact HwfU].
    + apply lc_tm_tapp.
      * exact (proj2 IH1).
      * apply (wf_ty_lc Delta U). exact HwfU.
  - split.
    + exact (proj1 IH1).
    + apply lc_tm_choice; [exact (proj2 IH1) | exact (proj2 IH2)].
Qed.

(* ---------- Multi-step reasoning ---------- *)

Lemma multi_trans : forall t1 t2 t3, t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 H12. revert t3.
  induction H12 as [x | x y z Hxy Hyz IH]; intros t3 H23.
  - assumption.
  - apply multi_step with (y := y); [assumption | apply IH; assumption].
Qed.

Lemma multi_app_l : forall t1 t2 t1',
  t1 -->* t1' -> lc_tm_at 0 0 t2 -> tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t2 t1' H.
  induction H as [x | x y z Hxy Hyz IH].
  - intros Hlc. apply multi_refl.
  - intros Hlc. apply multi_step with (y := tm_app y t2).
    + apply ST_App1; assumption.
    + apply IH. assumption.
Qed.

Lemma multi_app_r : forall v1 t2 t2',
  value v1 -> t2 -->* t2' -> tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros v1 t2 t2' Hv H.
  induction H as [x | x y z Hxy Hyz IH].
  - apply multi_refl.
  - apply multi_step with (y := tm_app v1 y).
    + apply ST_App2; assumption.
    + apply IH.
Qed.

Lemma multi_tapp : forall t t' U,
  t -->* t' -> lc_ty_at 0 U -> tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H.
  induction H as [x | x y z Hxy Hyz IH].
  - intros Hlc. apply multi_refl.
  - intros Hlc. apply multi_step with (y := tm_tapp y U).
    + apply ST_TApp; assumption.
    + apply IH. assumption.
Qed.

Lemma value_lc : forall v, value v -> lc_tm_at 0 0 v.
Proof. intros v H. inversion H; assumption. Qed.

Lemma multi_beta : forall T body v,
  lc_tm_at 0 0 (tm_abs T body) -> value v ->
  tm_app (tm_abs T body) v -->* open_tm body v.
Proof.
  intros. apply multi_step with (y := open_tm body v).
  - apply ST_AppAbs; assumption.
  - apply multi_refl.
Qed.

Lemma multi_tbeta : forall body U,
  lc_tm_at 0 0 (tm_tabs body) -> lc_ty_at 0 U ->
  tm_tapp (tm_tabs body) U -->* open_tm_ty body U.
Proof.
  intros. apply multi_step with (y := open_tm_ty body U).
  - apply ST_TAppTabs; assumption.
  - apply multi_refl.
Qed.

Lemma multi_choice_l : forall t1 t2,
  lc_tm_at 0 0 t1 -> lc_tm_at 0 0 t2 -> tm_choice t1 t2 -->* t1.
Proof.
  intros. apply multi_step with (y := t1).
  - apply ST_ChoiceLeft; assumption.
  - apply multi_refl.
Qed.

Lemma multi_choice_r : forall t1 t2,
  lc_tm_at 0 0 t1 -> lc_tm_at 0 0 t2 -> tm_choice t1 t2 -->* t2.
Proof.
  intros. apply multi_step with (y := t2).
  - apply ST_ChoiceRight; assumption.
  - apply multi_refl.
Qed.

(* ---------- Locally-closedness is preserved by substitutions ---------- *)

Lemma lc_ty_subst_env : forall k theta T,
  lc_ty_at k T -> (forall X, lc_ty_at 0 (theta X)) ->
  lc_ty_at k (ty_subst_env theta T).
Proof.
  intros k theta T H. revert k theta H.
  induction T as [n | X | A IHA B IHB | T1 IH1]; intros k theta Hlc Htheta; simpl.
  - assumption.
  - apply lc_ty_at_mono with (k := 0).
    + lia.
    + apply Htheta.
  - inversion Hlc as [k0 i Hi | k0 X0 | k0 A0 B0 HA HB | k0 T0 H0]; subst.
    apply lc_ty_arrow.
    + apply (IHA k theta HA Htheta).
    + apply (IHB k theta HB Htheta).
  - inversion Hlc as [k0 i Hi | k0 X0 | k0 A0 B0 HA HB | k0 T0 H0]; subst.
    apply lc_ty_all. apply (IH1 (S k) theta H0 Htheta).
Qed.

Lemma lc_tm_ty_subst_env : forall K k theta t,
  lc_tm_at K k t -> (forall X, lc_ty_at 0 (theta X)) ->
  lc_tm_at K k (tm_ty_subst_env theta t).
Proof.
  intros K k theta t H. revert K k theta H.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
    intros K k theta Hlc Htheta; simpl.
  - assumption.
  - assumption.
  - inversion Hlc as [K0 k0 i Hi | K0 k0 x0 | K0 k0 T0 t0 Hty Hbody
                    | K0 k0 s1 s2 H1 H2 | K0 k0 s0 H1 | K0 k0 s0 T0 H1 Hty
                    | K0 k0 s1 s2 H1 H2]; subst.
    apply lc_tm_abs.
    + apply (lc_ty_subst_env K theta T Hty Htheta).
    + apply (IH1 K (S k) theta Hbody Htheta).
  - inversion Hlc as [K0 k0 i Hi | K0 k0 x0 | K0 k0 T0 t0 Hty Hbody
                    | K0 k0 s1 s2 H1 H2 | K0 k0 s0 H1 | K0 k0 s0 T0 H1 Hty
                    | K0 k0 s1 s2 H1 H2]; subst.
    apply lc_tm_app.
    + apply (IH1 K k theta H1 Htheta).
    + apply (IH2 K k theta H2 Htheta).
  - inversion Hlc as [K0 k0 i Hi | K0 k0 x0 | K0 k0 T0 t0 Hty Hbody
                    | K0 k0 s1 s2 H1 H2 | K0 k0 s0 H1 | K0 k0 s0 T0 H1 Hty
                    | K0 k0 s1 s2 H1 H2]; subst.
    apply lc_tm_tabs. apply (IH1 (S K) k theta H1 Htheta).
  - inversion Hlc as [K0 k0 i Hi | K0 k0 x0 | K0 k0 T0 t0 Hty Hbody
                    | K0 k0 s1 s2 H1 H2 | K0 k0 s0 H1 | K0 k0 s0 T0 H1 Hty
                    | K0 k0 s1 s2 H1 H2]; subst.
    apply lc_tm_tapp.
    + apply (IH1 K k theta H1 Htheta).
    + apply (lc_ty_subst_env K theta T Hty Htheta).
  - inversion Hlc as [K0 k0 i Hi | K0 k0 x0 | K0 k0 T0 t0 Hty Hbody
                    | K0 k0 s1 s2 H1 H2 | K0 k0 s0 H1 | K0 k0 s0 T0 H1 Hty
                    | K0 k0 s1 s2 H1 H2]; subst.
    apply lc_tm_choice.
    + apply (IH1 K k theta H1 Htheta).
    + apply (IH2 K k theta H2 Htheta).
Qed.

Lemma lc_tm_subst_env : forall K k sigma t,
  lc_tm_at K k t -> (forall x, lc_tm_at 0 0 (sigma x)) ->
  lc_tm_at K k (tm_subst_env sigma t).
Proof.
  intros K k sigma t H. revert K k sigma H.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
    intros K k sigma Hlc Hsigma; simpl.
  - assumption.
  - apply lc_tm_at_mono with (K := 0) (k := 0).
    + lia.
    + lia.
    + apply Hsigma.
  - inversion Hlc as [K0 k0 i Hi | K0 k0 x0 | K0 k0 T0 t0 Hty Hbody
                    | K0 k0 s1 s2 H1 H2 | K0 k0 s0 H1 | K0 k0 s0 T0 H1 Hty
                    | K0 k0 s1 s2 H1 H2]; subst.
    apply lc_tm_abs.
    + assumption.
    + apply (IH1 K (S k) sigma Hbody Hsigma).
  - inversion Hlc as [K0 k0 i Hi | K0 k0 x0 | K0 k0 T0 t0 Hty Hbody
                    | K0 k0 s1 s2 H1 H2 | K0 k0 s0 H1 | K0 k0 s0 T0 H1 Hty
                    | K0 k0 s1 s2 H1 H2]; subst.
    apply lc_tm_app.
    + apply (IH1 K k sigma H1 Hsigma).
    + apply (IH2 K k sigma H2 Hsigma).
  - inversion Hlc as [K0 k0 i Hi | K0 k0 x0 | K0 k0 T0 t0 Hty Hbody
                    | K0 k0 s1 s2 H1 H2 | K0 k0 s0 H1 | K0 k0 s0 T0 H1 Hty
                    | K0 k0 s1 s2 H1 H2]; subst.
    apply lc_tm_tabs. apply (IH1 (S K) k sigma H1 Hsigma).
  - inversion Hlc as [K0 k0 i Hi | K0 k0 x0 | K0 k0 T0 t0 Hty Hbody
                    | K0 k0 s1 s2 H1 H2 | K0 k0 s0 H1 | K0 k0 s0 T0 H1 Hty
                    | K0 k0 s1 s2 H1 H2]; subst.
    apply lc_tm_tapp.
    + apply (IH1 K k sigma H1 Hsigma).
    + assumption.
  - inversion Hlc as [K0 k0 i Hi | K0 k0 x0 | K0 k0 T0 t0 Hty Hbody
                    | K0 k0 s1 s2 H1 H2 | K0 k0 s0 H1 | K0 k0 s0 T0 H1 Hty
                    | K0 k0 s1 s2 H1 H2]; subst.
    apply lc_tm_choice.
    + apply (IH1 K k sigma H1 Hsigma).
    + apply (IH2 K k sigma H2 Hsigma).
Qed.

Lemma lc_ty_all_inv : forall k T, lc_ty_at k (Ty_All T) -> lc_ty_at (S k) T.
Proof. intros k T H. inversion H; assumption. Qed.

(* ============================================================ *)
(* The logical relation.                                        *)
(* ============================================================ *)

Fixpoint Vty (env : list Rel) (xi : atom -> Rel) (T : ty) : Rel :=
  match T with
  | Ty_BVar i => fun v1 v2 => value v1 /\ value v2 /\ nth i env bot_rel v1 v2
  | Ty_FVar X => fun v1 v2 => value v1 /\ value v2 /\ xi X v1 v2
  | Ty_Arrow A B => fun v1 v2 =>
      value v1 /\ value v2 /\
      (forall w1 w2, Vty env xi A w1 w2 ->
         exists u1 u2, tm_app v1 w1 -->* u1 /\ tm_app v2 w2 -->* u2 /\
                       Vty env xi B u1 u2)
  | Ty_All T1 => fun v1 v2 =>
      value v1 /\ value v2 /\
      (forall (rho : Rel) (U1 U2 : ty),
         lc_ty_at 0 U1 -> lc_ty_at 0 U2 ->
         exists u1 u2, tm_tapp v1 U1 -->* u1 /\ tm_tapp v2 U2 -->* u2 /\
                       Vty (rho :: env) xi T1 u1 u2)
  end.

Definition Rty (env : list Rel) (xi : atom -> Rel) (T : ty) : Rel :=
  fun t1 t2 =>
    lc_tm_at 0 0 t1 /\ lc_tm_at 0 0 t2 /\
    exists v1 v2, t1 -->* v1 /\ t2 -->* v2 /\ Vty env xi T v1 v2.

Lemma Vty_value : forall env xi T v1 v2,
  Vty env xi T v1 v2 -> value v1 /\ value v2.
Proof.
  intros env xi T. induction T as [n | X | A IHA B IHB | T1 IH1];
    intros v1 v2 H; simpl in H.
  - destruct H as [H1 [H2 H3]]. auto.
  - destruct H as [H1 [H2 H3]]. auto.
  - destruct H as [H1 [H2 H3]]. auto.
  - destruct H as [H1 [H2 H3]]. auto.
Qed.

Lemma Vty_lc : forall env xi T v1 v2,
  Vty env xi T v1 v2 -> lc_tm_at 0 0 v1 /\ lc_tm_at 0 0 v2.
Proof.
  intros env xi T v1 v2 H.
  apply Vty_value in H. destruct H as [H1 H2]. split; apply value_lc; assumption.
Qed.

Lemma Vty_env_agree : forall d T env1 env2 xi,
  lc_ty_at d T ->
  (forall i, i < d -> nth i env1 bot_rel = nth i env2 bot_rel) ->
  forall v1 v2, Vty env1 xi T v1 v2 <-> Vty env2 xi T v1 v2.
Proof.
  intros d T. revert d.
  induction T as [n | X | A IHA B IHB | T1 IH1];
    intros d env1 env2 xi Hlc Hagree v1 v2; simpl.
  - inversion Hlc as [d0 i Hi | d0 X0 | d0 A0 B0 HA HB | d0 T0 H0]; subst.
    split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
    + rewrite <- (Hagree n Hi). assumption.
    + rewrite (Hagree n Hi). assumption.
  - split; intros H; exact H.
  - inversion Hlc as [d0 i Hi | d0 X0 | d0 A0 B0 HA HB | d0 T0 H0]; subst.
    split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
    + intros w1 w2 Hw.
      apply (proj2 (IHA d env1 env2 xi HA Hagree w1 w2)) in Hw.
      destruct (H3 w1 w2 Hw) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      exact (proj1 (IHB d env1 env2 xi HB Hagree u1 u2) HV).
    + intros w1 w2 Hw.
      apply (proj1 (IHA d env1 env2 xi HA Hagree w1 w2)) in Hw.
      destruct (H3 w1 w2 Hw) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      exact (proj2 (IHB d env1 env2 xi HB Hagree u1 u2) HV).
  - inversion Hlc as [d0 i Hi | d0 X0 | d0 A0 B0 HA HB | d0 T0 H0]; subst.
    split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
    + intros rho U1 U2 HU1 HU2.
      destruct (H3 rho U1 U2 HU1 HU2) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      assert (Hag' : forall i, i < S d ->
        nth i (rho :: env1) bot_rel = nth i (rho :: env2) bot_rel).
      { intros i Hi. destruct i as [| i'].
        - reflexivity.
        - simpl. apply Hagree. lia. }
      exact (proj1 (IH1 (S d) (rho :: env1) (rho :: env2) xi H0 Hag' u1 u2) HV).
    + intros rho U1 U2 HU1 HU2.
      destruct (H3 rho U1 U2 HU1 HU2) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      assert (Hag' : forall i, i < S d ->
        nth i (rho :: env2) bot_rel = nth i (rho :: env1) bot_rel).
      { intros i Hi. destruct i as [| i'].
        - reflexivity.
        - simpl. symmetry. apply Hagree. lia. }
      exact (proj1 (IH1 (S d) (rho :: env2) (rho :: env1) xi H0 Hag' u1 u2) HV).
Qed.

Lemma Vty_xi_agree : forall T env xi1 xi2,
  (forall X, In X (ty_fv T) -> xi1 X = xi2 X) ->
  forall v1 v2, Vty env xi1 T v1 v2 <-> Vty env xi2 T v1 v2.
Proof.
  intros T. induction T as [n | X | A IHA B IHB | T1 IH1];
    intros env xi1 xi2 Hagree v1 v2; simpl.
  - split; intros H; exact H.
  - split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
    + rewrite <- (Hagree X). assumption. simpl. auto.
    + rewrite (Hagree X). assumption. simpl. auto.
  - split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
    + intros w1 w2 Hw.
      assert (HagA : forall Y, In Y (ty_fv A) -> xi1 Y = xi2 Y).
      { intros Y HY. apply Hagree. simpl. apply in_or_app. auto. }
      assert (HagB : forall Y, In Y (ty_fv B) -> xi1 Y = xi2 Y).
      { intros Y HY. apply Hagree. simpl. apply in_or_app. auto. }
      apply (proj2 (IHA env xi1 xi2 HagA w1 w2)) in Hw.
      destruct (H3 w1 w2 Hw) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      exact (proj1 (IHB env xi1 xi2 HagB u1 u2) HV).
    + intros w1 w2 Hw.
      assert (HagA : forall Y, In Y (ty_fv A) -> xi1 Y = xi2 Y).
      { intros Y HY. apply Hagree. simpl. apply in_or_app. auto. }
      assert (HagB : forall Y, In Y (ty_fv B) -> xi1 Y = xi2 Y).
      { intros Y HY. apply Hagree. simpl. apply in_or_app. auto. }
      apply (proj1 (IHA env xi1 xi2 HagA w1 w2)) in Hw.
      destruct (H3 w1 w2 Hw) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      exact (proj2 (IHB env xi1 xi2 HagB u1 u2) HV).
  - split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
    + intros rho U1 U2 HU1 HU2.
      destruct (H3 rho U1 U2 HU1 HU2) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      exact (proj1 (IH1 (rho :: env) xi1 xi2 Hagree u1 u2) HV).
    + intros rho U1 U2 HU1 HU2.
      destruct (H3 rho U1 U2 HU1 HU2) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      exact (proj2 (IH1 (rho :: env) xi1 xi2 Hagree u1 u2) HV).
Qed.

Lemma Rty_xi_agree : forall T env xi1 xi2,
  (forall X, In X (ty_fv T) -> xi1 X = xi2 X) ->
  forall t1 t2, Rty env xi1 T t1 t2 <-> Rty env xi2 T t1 t2.
Proof.
  intros T env xi1 xi2 Hagree t1 t2. unfold Rty.
  split; intros [H1 [H2 Hex]]; (split; [assumption | split; [assumption |]]).
  - destruct Hex as [v1 [v2 [R1 [R2 HV]]]]. exists v1, v2.
    split; [assumption | split; [assumption |]].
    exact (proj1 (Vty_xi_agree T env xi1 xi2 Hagree v1 v2) HV).
  - destruct Hex as [v1 [v2 [R1 [R2 HV]]]]. exists v1, v2.
    split; [assumption | split; [assumption |]].
    exact (proj2 (Vty_xi_agree T env xi1 xi2 Hagree v1 v2) HV).
Qed.

(* ---------- Opening lemmas for the relation ---------- *)

Lemma Vty_open_ty : forall env xi k T U R,
  k <= length env ->
  lc_ty_at 0 U ->
  lc_ty_at (S k) T ->
  (forall a b, R a b <-> Vty env xi U a b) ->
  forall v1 v2,
    Vty env xi (open_ty_rec k U T) v1 v2 <->
    Vty (insert_at k R env) xi T v1 v2.
Proof.
  intros env xi k T U R. revert env xi k R.
  induction T as [n | X | A IHA B IHB | T1 IH1];
    intros env xi k R Hlen HU Hlc Hreq v1 v2; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      split; intro H.
      * destruct (Vty_value env xi U v1 v2 H) as [Hv1 Hv2].
        split; [assumption | split; [assumption |]].
        exact (proj2 (nth_insert_at_eq_app env k R v1 v2 Hlen) (proj2 (Hreq v1 v2) H)).
      * destruct H as [Hv1 [Hv2 H3]].
        exact (proj1 (Hreq v1 v2) (proj1 (nth_insert_at_eq_app env k R v1 v2 Hlen) H3)).
    + apply Nat.eqb_neq in E.
      inversion Hlc as [d0 i Hi | d0 X0 | d0 A0 B0 HA HB | d0 T0 H0]; subst.
      assert (Hnk : n < k) by lia.
      split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
      * exact (proj2 (nth_insert_at_lt_app env k R n v1 v2 Hlen Hnk) H3).
      * exact (proj1 (nth_insert_at_lt_app env k R n v1 v2 Hlen Hnk) H3).
  - split; intros H; exact H.
  - inversion Hlc as [d0 i Hi | d0 X0 | d0 A0 B0 HA HB | d0 T0 H0]; subst.
    split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
    + intros w1 w2 Hw.
      apply (proj2 (IHA env xi k R Hlen HU HA Hreq w1 w2)) in Hw.
      destruct (H3 w1 w2 Hw) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      exact (proj1 (IHB env xi k R Hlen HU HB Hreq u1 u2) HV).
    + intros w1 w2 Hw.
      apply (proj1 (IHA env xi k R Hlen HU HA Hreq w1 w2)) in Hw.
      destruct (H3 w1 w2 Hw) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      exact (proj2 (IHB env xi k R Hlen HU HB Hreq u1 u2) HV).
  - inversion Hlc as [d0 i Hi | d0 X0 | d0 A0 B0 HA HB | d0 T0 H0]; subst.
    split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
    + intros rho U1 U2 HU1 HU2.
      destruct (H3 rho U1 U2 HU1 HU2) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      assert (Hreq' : forall a b, R a b <-> Vty (rho :: env) xi U a b).
      { intros a b. split; intro Hx.
        - apply (proj1 (Vty_env_agree 0 U env (rho :: env) xi HU
                        ltac:(intros i Hi0; lia) a b)).
          apply (proj1 (Hreq a b) Hx).
        - apply (proj2 (Hreq a b)).
          apply (proj2 (Vty_env_agree 0 U env (rho :: env) xi HU
                         ltac:(intros i Hi0; lia) a b)).
          assumption. }
      exact (proj1 (IH1 (rho :: env) xi (S k) R ltac:(simpl; lia) HU H0 Hreq' u1 u2) HV).
    + intros rho U1 U2 HU1 HU2.
      destruct (H3 rho U1 U2 HU1 HU2) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      assert (Hreq' : forall a b, R a b <-> Vty (rho :: env) xi U a b).
      { intros a b. split; intro Hx.
        - apply (proj1 (Vty_env_agree 0 U env (rho :: env) xi HU
                        ltac:(intros i Hi0; lia) a b)).
          apply (proj1 (Hreq a b) Hx).
        - apply (proj2 (Hreq a b)).
          apply (proj2 (Vty_env_agree 0 U env (rho :: env) xi HU
                         ltac:(intros i Hi0; lia) a b)).
          assumption. }
      exact (proj2 (IH1 (rho :: env) xi (S k) R ltac:(simpl; lia) HU H0 Hreq' u1 u2) HV).
Qed.

Lemma Vty_open_fvar : forall env xi k T X rho,
  k <= length env ->
  ~ In X (ty_fv T) ->
  lc_ty_at (S k) T ->
  forall v1 v2,
    Vty env (update_xi xi X rho) (open_ty_rec k (Ty_FVar X) T) v1 v2 <->
    Vty (insert_at k rho env) xi T v1 v2.
Proof.
  intros env xi k T. revert env xi k.
  induction T as [n | Y | A IHA B IHB | T1 IH1];
    intros env xi k X rho Hlen Hfresh Hlc v1 v2; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n.
      assert (Hupd : update_xi xi X rho X = rho).
      { unfold update_xi. rewrite Nat.eqb_refl. reflexivity. }
      split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
      * rewrite Hupd in H3.
        exact (proj2 (nth_insert_at_eq_app env k rho v1 v2 Hlen) H3).
      * rewrite Hupd.
        exact (proj1 (nth_insert_at_eq_app env k rho v1 v2 Hlen) H3).
    + apply Nat.eqb_neq in E.
      inversion Hlc as [d0 i Hi | d0 X0 | d0 A0 B0 HA HB | d0 T0 H0]; subst.
      assert (Hnk : n < k) by lia.
      split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
      * exact (proj2 (nth_insert_at_lt_app env k rho n v1 v2 Hlen Hnk) H3).
      * exact (proj1 (nth_insert_at_lt_app env k rho n v1 v2 Hlen Hnk) H3).
  - assert (HYX : Y <> X).
    { intro Hc. apply Hfresh. simpl. subst. auto. }
    assert (Hupd : update_xi xi X rho Y = xi Y).
    { unfold update_xi. destruct (Nat.eqb Y X) eqn:E.
      - apply Nat.eqb_eq in E. subst Y. contradiction.
      - reflexivity. }
    split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
    + rewrite Hupd in H3. assumption.
    + rewrite Hupd. assumption.
  - inversion Hlc as [d0 i Hi | d0 X0 | d0 A0 B0 HA HB | d0 T0 H0]; subst.
    assert (HfreshA : ~ In X (ty_fv A)).
    { intro Hc. apply Hfresh. simpl. apply in_or_app. auto. }
    assert (HfreshB : ~ In X (ty_fv B)).
    { intro Hc. apply Hfresh. simpl. apply in_or_app. auto. }
    split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
    + intros w1 w2 Hw.
      apply (proj2 (IHA env xi k X rho Hlen HfreshA HA w1 w2)) in Hw.
      destruct (H3 w1 w2 Hw) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      exact (proj1 (IHB env xi k X rho Hlen HfreshB HB u1 u2) HV).
    + intros w1 w2 Hw.
      apply (proj1 (IHA env xi k X rho Hlen HfreshA HA w1 w2)) in Hw.
      destruct (H3 w1 w2 Hw) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      exact (proj2 (IHB env xi k X rho Hlen HfreshB HB u1 u2) HV).
  - inversion Hlc as [d0 i Hi | d0 X0 | d0 A0 B0 HA HB | d0 T0 H0]; subst.
    split; intros [H1 [H2 H3]]; (split; [assumption | split; [assumption |]]).
    + intros rho' U1 U2 HU1 HU2.
      destruct (H3 rho' U1 U2 HU1 HU2) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      exact (proj1 (IH1 (rho' :: env) xi (S k) X rho ltac:(simpl; lia) Hfresh H0 u1 u2) HV).
    + intros rho' U1 U2 HU1 HU2.
      destruct (H3 rho' U1 U2 HU1 HU2) as [u1 [u2 [R1 [R2 HV]]]].
      exists u1, u2. split; [assumption | split; [assumption |]].
      exact (proj2 (IH1 (rho' :: env) xi (S k) X rho ltac:(simpl; lia) Hfresh H0 u1 u2) HV).
Qed.

Lemma Rty_open_ty : forall env xi k T U R,
  k <= length env ->
  lc_ty_at 0 U ->
  lc_ty_at (S k) T ->
  (forall a b, R a b <-> Vty env xi U a b) ->
  forall t1 t2,
    Rty env xi (open_ty_rec k U T) t1 t2 <->
    Rty (insert_at k R env) xi T t1 t2.
Proof.
  intros env xi k T U R Hlen HU Hlc Hreq t1 t2. unfold Rty.
  split; intros [H1 [H2 Hex]]; (split; [assumption | split; [assumption |]]).
  - destruct Hex as [v1 [v2 [R1 [R2 HV]]]]. exists v1, v2.
    split; [assumption | split; [assumption |]].
    exact (proj1 (Vty_open_ty env xi k T U R Hlen HU Hlc Hreq v1 v2) HV).
  - destruct Hex as [v1 [v2 [R1 [R2 HV]]]]. exists v1, v2.
    split; [assumption | split; [assumption |]].
    exact (proj2 (Vty_open_ty env xi k T U R Hlen HU Hlc Hreq v1 v2) HV).
Qed.

Lemma Rty_open_fvar : forall env xi k T X rho,
  k <= length env ->
  ~ In X (ty_fv T) ->
  lc_ty_at (S k) T ->
  forall t1 t2,
    Rty env (update_xi xi X rho) (open_ty_rec k (Ty_FVar X) T) t1 t2 <->
    Rty (insert_at k rho env) xi T t1 t2.
Proof.
  intros env xi k T X rho Hlen Hfresh Hlc t1 t2. unfold Rty.
  split; intros [H1 [H2 Hex]]; (split; [assumption | split; [assumption |]]).
  - destruct Hex as [v1 [v2 [R1 [R2 HV]]]]. exists v1, v2.
    split; [assumption | split; [assumption |]].
    exact (proj1 (Vty_open_fvar env xi k T X rho Hlen Hfresh Hlc v1 v2) HV).
  - destruct Hex as [v1 [v2 [R1 [R2 HV]]]]. exists v1, v2.
    split; [assumption | split; [assumption |]].
    exact (proj2 (Vty_open_fvar env xi k T X rho Hlen Hfresh Hlc v1 v2) HV).
Qed.


(* ---------- Elimination/introduction helpers for the relations ---------- *)

Definition update_theta (theta : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb Y X then U else theta Y.

Lemma lookup_update_eq : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof.
  intros. unfold update. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_update_neq : forall Gamma x y T, x <> y ->
  lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros. unfold update. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. contradiction.
  - reflexivity.
Qed.

Lemma update_sigma_eq : forall sigma x u,
  update_sigma sigma x u x = u.
Proof. intros. unfold update_sigma. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_sigma_neq : forall sigma x y u, y <> x ->
  update_sigma sigma x u y = sigma y.
Proof.
  intros. unfold update_sigma. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. contradiction.
  - reflexivity.
Qed.

Lemma update_theta_eq : forall theta X U,
  update_theta theta X U X = U.
Proof. intros. unfold update_theta. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_theta_neq : forall theta X Y U, Y <> X ->
  update_theta theta X U Y = theta Y.
Proof.
  intros. unfold update_theta. destruct (Nat.eqb Y X) eqn:E.
  - apply Nat.eqb_eq in E. subst Y. contradiction.
  - reflexivity.
Qed.

Lemma Vty_bvar_elim : forall env xi i v1 v2,
  Vty env xi (Ty_BVar i) v1 v2 ->
  value v1 /\ value v2 /\ nth i env bot_rel v1 v2.
Proof. intros env xi i v1 v2 H. simpl in H. exact H. Qed.

Lemma Vty_fvar_elim : forall env xi X v1 v2,
  Vty env xi (Ty_FVar X) v1 v2 ->
  value v1 /\ value v2 /\ xi X v1 v2.
Proof. intros env xi X v1 v2 H. simpl in H. exact H. Qed.

Lemma Vty_arrow_elim : forall env xi A B v1 v2,
  Vty env xi (Ty_Arrow A B) v1 v2 ->
  value v1 /\ value v2 /\
  (forall w1 w2, Vty env xi A w1 w2 ->
     exists u1 u2, tm_app v1 w1 -->* u1 /\ tm_app v2 w2 -->* u2 /\
                   Vty env xi B u1 u2).
Proof. intros env xi A B v1 v2 H. simpl in H. exact H. Qed.

Lemma Vty_all_elim : forall env xi T1 v1 v2,
  Vty env xi (Ty_All T1) v1 v2 ->
  value v1 /\ value v2 /\
  (forall (rho : Rel) (U1 U2 : ty), lc_ty_at 0 U1 -> lc_ty_at 0 U2 ->
     exists u1 u2, tm_tapp v1 U1 -->* u1 /\ tm_tapp v2 U2 -->* u2 /\
                   Vty (rho :: env) xi T1 u1 u2).
Proof. intros env xi T1 v1 v2 H. simpl in H. exact H. Qed.

Lemma Rty_intro : forall env xi T t1 t2 v1 v2,
  lc_tm_at 0 0 t1 -> lc_tm_at 0 0 t2 ->
  t1 -->* v1 -> t2 -->* v2 -> Vty env xi T v1 v2 ->
  Rty env xi T t1 t2.
Proof.
  intros. unfold Rty. repeat split; auto. exists v1, v2. auto.
Qed.

Lemma Rty_elim : forall env xi T t1 t2,
  Rty env xi T t1 t2 ->
  lc_tm_at 0 0 t1 /\ lc_tm_at 0 0 t2 /\
  exists v1 v2, t1 -->* v1 /\ t2 -->* v2 /\ Vty env xi T v1 v2.
Proof. intros. unfold Rty in H. exact H. Qed.

Lemma Rty_of_Vty : forall env xi T v1 v2,
  Vty env xi T v1 v2 -> Rty env xi T v1 v2.
Proof.
  intros env xi T v1 v2 H.
  pose proof (Vty_value env xi T v1 v2 H) as HV. destruct HV as [Hv1 Hv2].
  apply Rty_intro with (v1 := v1) (v2 := v2).
  - apply value_lc; assumption.
  - apply value_lc; assumption.
  - apply multi_refl.
  - apply multi_refl.
  - assumption.
Qed.

Lemma Rty_multi_l : forall env xi T t1 t1' t2,
  t1 -->* t1' -> Rty env xi T t1' t2 -> lc_tm_at 0 0 t1 -> Rty env xi T t1 t2.
Proof.
  intros env xi T t1 t1' t2 Hstep HR Hlc.
  destruct (Rty_elim env xi T t1' t2 HR) as [Hlc1 [Hlc2 Hex]].
  destruct Hex as [v1 [v2 [R1 [R2 HV]]]].
  apply Rty_intro with (v1 := v1) (v2 := v2).
  - assumption.
  - assumption.
  - apply multi_trans with (t2 := t1'); assumption.
  - assumption.
  - assumption.
Qed.

Lemma Rty_multi_r : forall env xi T t1 t2 t2',
  t2 -->* t2' -> Rty env xi T t1 t2' -> lc_tm_at 0 0 t2 -> Rty env xi T t1 t2.
Proof.
  intros env xi T t1 t2 t2' Hstep HR Hlc.
  destruct (Rty_elim env xi T t1 t2' HR) as [Hlc1 [Hlc2 Hex]].
  destruct Hex as [v1 [v2 [R1 [R2 HV]]]].
  apply Rty_intro with (v1 := v1) (v2 := v2).
  - assumption.
  - assumption.
  - assumption.
  - apply multi_trans with (t2 := t2'); assumption.
  - assumption.
Qed.

(* ---------- The fundamental theorem ---------- *)

Definition FundStmt (Delta : ty_context) (Gamma : context) (t : tm) (T : ty) : Prop :=
  forall env xi theta1 theta2 sigma1 sigma2,
    (forall X, lc_ty_at 0 (theta1 X)) ->
    (forall X, lc_ty_at 0 (theta2 X)) ->
    (forall x, lc_tm_at 0 0 (sigma1 x)) ->
    (forall x, lc_tm_at 0 0 (sigma2 x)) ->
    (forall x Ti, lookup_context x Gamma = Some Ti ->
       Rty env xi Ti (sigma1 x) (sigma2 x)) ->
    Rty env xi T (tm_subst_env sigma1 (tm_ty_subst_env theta1 t))
                 (tm_subst_env sigma2 (tm_ty_subst_env theta2 t)).

Lemma lc_subst_both : forall theta sigma t,
  (forall X, lc_ty_at 0 (theta X)) ->
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  lc_tm_at 0 0 t ->
  lc_tm_at 0 0 (tm_subst_env sigma (tm_ty_subst_env theta t)).
Proof.
  intros theta sigma t Hl Hs Hlc.
  apply lc_tm_subst_env with (K := 0) (k := 0); [|assumption].
  apply lc_tm_ty_subst_env with (K := 0) (k := 0); assumption.
Qed.

Lemma update_sigma_lc : forall sigma x w,
  (forall y, lc_tm_at 0 0 (sigma y)) -> lc_tm_at 0 0 w ->
  forall y, lc_tm_at 0 0 (update_sigma sigma x w y).
Proof.
  intros sigma x w Hs Hw y. unfold update_sigma.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst y. assumption.
  - apply Hs.
Qed.

Lemma update_theta_lc : forall theta X U,
  (forall Y, lc_ty_at 0 (theta Y)) -> lc_ty_at 0 U ->
  forall Y, lc_ty_at 0 (update_theta theta X U Y).
Proof.
  intros theta X U Hl HU Y. unfold update_theta.
  destruct (Nat.eqb Y X) eqn:E.
  - apply Nat.eqb_eq in E. subst Y. assumption.
  - apply Hl.
Qed.

Lemma subst_open_fvar_update : forall theta sigma x t w,
  (forall X, lc_ty_at 0 (theta X)) ->
  (forall y, lc_tm_at 0 0 (sigma y)) ->
  lc_tm_at 0 0 w ->
  ~ In x (tm_fv t) ->
  tm_subst_env (update_sigma sigma x w) (tm_ty_subst_env theta (open_tm t (tm_fvar x)))
  = open_tm (tm_subst_env sigma (tm_ty_subst_env theta t)) w.
Proof.
  intros theta sigma x t w Hl Hs Hw Hfresh.
  unfold open_tm.
  rewrite (tm_ty_subst_env_open_tm theta 0 (tm_fvar x) t).
  simpl.
  rewrite (tm_subst_env_open_tm (update_sigma sigma x w) 0 (tm_fvar x)
             (tm_ty_subst_env theta t)
             (update_sigma_lc sigma x w Hs Hw)).
  simpl.
  rewrite update_sigma_eq.
  assert (Heq : tm_subst_env (update_sigma sigma x w) (tm_ty_subst_env theta t)
              = tm_subst_env sigma (tm_ty_subst_env theta t)).
  { apply tm_subst_env_ext. intros y Hy.
    rewrite tm_fv_tm_ty_subst_env in Hy.
    apply update_sigma_neq. intro Hc. apply Hfresh. subst y. assumption. }
  rewrite Heq. reflexivity.
Qed.

Lemma subst_open_ty_fvar_update : forall theta sigma X U t,
  (forall Y, lc_ty_at 0 (theta Y)) ->
  lc_ty_at 0 U ->
  (forall y, lc_tm_at 0 0 (sigma y)) ->
  ~ In X (tm_ty_fv t) ->
  tm_subst_env sigma (tm_ty_subst_env (update_theta theta X U) (open_tm_ty t (Ty_FVar X)))
  = open_tm_ty (tm_subst_env sigma (tm_ty_subst_env theta t)) U.
Proof.
  intros theta sigma X U t Hl HU Hs Hfresh.
  unfold open_tm_ty.
  rewrite (tm_ty_subst_env_open_tm_ty (update_theta theta X U)
             (update_theta_lc theta X U Hl HU) 0 (Ty_FVar X) t).
  cbn [ty_subst_env].
  rewrite update_theta_eq.
  rewrite (tm_subst_env_open_tm_ty sigma 0 U
             (tm_ty_subst_env (update_theta theta X U) t) Hs).
  assert (Heq : tm_ty_subst_env (update_theta theta X U) t = tm_ty_subst_env theta t).
  { apply tm_ty_subst_env_ext. intros Y HY.
    apply update_theta_neq. intro Hc. apply Hfresh. subst Y. assumption. }
  rewrite Heq. reflexivity.
Qed.

Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T -> FundStmt Delta Gamma t T.
Proof.
  intros Delta Gamma t T H.
  induction H as
    [Delta Gamma x T0 Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf1 Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t0 T0 Hbody IHbody
    | Delta Gamma t0 T0 U H1 IH1 HwfU
    | Delta Gamma t1 t2 T0 H1 IH1 H2 IH2];
    intros env xi th1 th2 s1 s2 Hl1 Hl2 Hs1 Hs2 Henv.
  - (* T_Var *)
    simpl. apply (Henv x T0 Hlook).
  - (* T_Abs *)
    pose proof (has_type_wf_lc Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)
                  (T_Abs L Delta Gamma T1 t2 T2 Hwf1 Hbody)) as Hwl.
    destruct Hwl as [HwfArrow HlcAbs].
    change (Rty env xi (Ty_Arrow T1 T2)
              (tm_abs (ty_subst_env th1 T1) (tm_subst_env s1 (tm_ty_subst_env th1 t2)))
              (tm_abs (ty_subst_env th2 T1) (tm_subst_env s2 (tm_ty_subst_env th2 t2)))).
    apply Rty_intro with
      (v1 := tm_abs (ty_subst_env th1 T1) (tm_subst_env s1 (tm_ty_subst_env th1 t2)))
      (v2 := tm_abs (ty_subst_env th2 T1) (tm_subst_env s2 (tm_ty_subst_env th2 t2))).
    + change (lc_tm_at 0 0 (tm_subst_env s1 (tm_ty_subst_env th1 (tm_abs T1 t2)))).
      apply lc_subst_both; assumption.
    + change (lc_tm_at 0 0 (tm_subst_env s2 (tm_ty_subst_env th2 (tm_abs T1 t2)))).
      apply lc_subst_both; assumption.
    + apply multi_refl.
    + apply multi_refl.
    + unfold Vty. split.
      * apply v_abs.
        change (lc_tm_at 0 0 (tm_subst_env s1 (tm_ty_subst_env th1 (tm_abs T1 t2)))).
        apply lc_subst_both; assumption.
      * split.
        -- apply v_abs.
           change (lc_tm_at 0 0 (tm_subst_env s2 (tm_ty_subst_env th2 (tm_abs T1 t2)))).
           apply lc_subst_both; assumption.
        -- intros w1 w2 Hw.
           pose proof (Vty_value env xi T1 w1 w2 Hw) as HVw. destruct HVw as [Hvw1 Hvw2].
           assert (Hlcw1 : lc_tm_at 0 0 w1) by (apply value_lc; assumption).
           assert (Hlcw2 : lc_tm_at 0 0 w2) by (apply value_lc; assumption).
           set (x := fresh_atom (L ++ tm_fv t2)).
           assert (HxL : ~ In x L).
           { intro Hc. apply (fresh_atom_notin (L ++ tm_fv t2)). apply in_or_app. left. assumption. }
           assert (Hxfv : ~ In x (tm_fv t2)).
           { intro Hc. apply (fresh_atom_notin (L ++ tm_fv t2)). apply in_or_app. right. assumption. }
           assert (Hls1' : forall y, lc_tm_at 0 0 (update_sigma s1 x w1 y)).
           { apply update_sigma_lc; assumption. }
           assert (Hls2' : forall y, lc_tm_at 0 0 (update_sigma s2 x w2 y)).
           { apply update_sigma_lc; assumption. }
           assert (Henv' : forall y Ti, lookup_context y (update Gamma x T1) = Some Ti ->
                     Rty env xi Ti (update_sigma s1 x w1 y) (update_sigma s2 x w2 y)).
           { intros y Ti Hy. destruct (Nat.eqb y x) eqn:E.
             - apply Nat.eqb_eq in E. subst y.
               rewrite lookup_update_eq in Hy. injection Hy as Heq. subst Ti.
               rewrite update_sigma_eq. rewrite update_sigma_eq.
               apply Rty_of_Vty. assumption.
             - apply Nat.eqb_neq in E.
               assert (Hxy : x <> y) by (intro Hc; apply E; symmetry; assumption).
               rewrite lookup_update_neq in Hy; [| assumption].
               rewrite update_sigma_neq; [| assumption].
               rewrite update_sigma_neq; [| assumption].
               apply Henv. assumption. }
           pose proof (IHbody x HxL env xi th1 th2 (update_sigma s1 x w1) (update_sigma s2 x w2)
                         Hl1 Hl2 Hls1' Hls2' Henv') as HIH.
           assert (Heq1 : tm_subst_env (update_sigma s1 x w1)
                            (tm_ty_subst_env th1 (open_tm t2 (tm_fvar x)))
                          = open_tm (tm_subst_env s1 (tm_ty_subst_env th1 t2)) w1).
           { apply subst_open_fvar_update; assumption. }
           assert (Heq2 : tm_subst_env (update_sigma s2 x w2)
                            (tm_ty_subst_env th2 (open_tm t2 (tm_fvar x)))
                          = open_tm (tm_subst_env s2 (tm_ty_subst_env th2 t2)) w2).
           { apply subst_open_fvar_update; assumption. }
           rewrite Heq1 in HIH. rewrite Heq2 in HIH.
           destruct (Rty_elim env xi T2
                       (open_tm (tm_subst_env s1 (tm_ty_subst_env th1 t2)) w1)
                       (open_tm (tm_subst_env s2 (tm_ty_subst_env th2 t2)) w2) HIH)
             as [HlcR1 [HlcR2 HexR]].
           destruct HexR as [u1 [u2 [Ru1 [Ru2 HVu]]]].
           exists u1, u2. split.
           ++ apply multi_trans with (t2 := open_tm (tm_subst_env s1 (tm_ty_subst_env th1 t2)) w1).
              ** apply multi_beta.
                 --- change (lc_tm_at 0 0 (tm_subst_env s1 (tm_ty_subst_env th1 (tm_abs T1 t2)))).
                     apply lc_subst_both; assumption.
                 --- assumption.
              ** assumption.
           ++ split.
              ** apply multi_trans with (t2 := open_tm (tm_subst_env s2 (tm_ty_subst_env th2 t2)) w2).
                 --- apply multi_beta.
                     +++ change (lc_tm_at 0 0 (tm_subst_env s2 (tm_ty_subst_env th2 (tm_abs T1 t2)))).
                         apply lc_subst_both; assumption.
                     +++ assumption.
                 --- assumption.
              ** assumption.
  - (* T_App *)
    pose proof (IH1 env xi th1 th2 s1 s2 Hl1 Hl2 Hs1 Hs2 Henv) as HR1.
    pose proof (IH2 env xi th1 th2 s1 s2 Hl1 Hl2 Hs1 Hs2 Henv) as HR2.
    change (Rty env xi T2
              (tm_app (tm_subst_env s1 (tm_ty_subst_env th1 t1))
                      (tm_subst_env s1 (tm_ty_subst_env th1 t2)))
              (tm_app (tm_subst_env s2 (tm_ty_subst_env th2 t1))
                      (tm_subst_env s2 (tm_ty_subst_env th2 t2)))).
    destruct (Rty_elim env xi (Ty_Arrow T1 T2)
                (tm_subst_env s1 (tm_ty_subst_env th1 t1))
                (tm_subst_env s2 (tm_ty_subst_env th2 t1)) HR1)
      as [Hlc1a [Hlc1b Hex1]].
    destruct Hex1 as [v1 [v2 [Rv1 [Rv2 HV1]]]].
    destruct (Rty_elim env xi T1
                (tm_subst_env s1 (tm_ty_subst_env th1 t2))
                (tm_subst_env s2 (tm_ty_subst_env th2 t2)) HR2)
      as [Hlc2a [Hlc2b Hex2]].
    destruct Hex2 as [u1 [u2 [Ru1 [Ru2 HV2]]]].
    destruct (Vty_arrow_elim env xi T1 T2 v1 v2 HV1) as [Hvv1 [Hvv2 Hf]].
    destruct (Hf u1 u2 HV2) as [w1 [w2 [Rw1 [Rw2 HVw]]]].
    apply Rty_intro with (v1 := w1) (v2 := w2).
    + apply lc_tm_app; assumption.
    + apply lc_tm_app; assumption.
    + apply multi_trans with (t2 := tm_app v1 u1).
      * apply multi_trans with (t2 := tm_app v1 (tm_subst_env s1 (tm_ty_subst_env th1 t2))).
        -- apply multi_app_l; assumption.
        -- apply multi_app_r; assumption.
      * assumption.
    + apply multi_trans with (t2 := tm_app v2 u2).
      * apply multi_trans with (t2 := tm_app v2 (tm_subst_env s2 (tm_ty_subst_env th2 t2))).
        -- apply multi_app_l; assumption.
        -- apply multi_app_r; assumption.
      * assumption.
    + assumption.
  - (* T_TAbs *)
    pose proof (has_type_wf_lc Delta Gamma (tm_tabs t0) (Ty_All T0)
                  (T_TAbs L Delta Gamma t0 T0 Hbody)) as Hwl.
    destruct Hwl as [HwfAll HlcTabs].
    assert (HlcT1 : lc_ty_at 1 T0).
    { apply lc_ty_all_inv with (k := 0). apply (wf_ty_lc Delta (Ty_All T0)). assumption. }
    change (Rty env xi (Ty_All T0)
              (tm_tabs (tm_subst_env s1 (tm_ty_subst_env th1 t0)))
              (tm_tabs (tm_subst_env s2 (tm_ty_subst_env th2 t0)))).
    apply Rty_intro with
      (v1 := tm_tabs (tm_subst_env s1 (tm_ty_subst_env th1 t0)))
      (v2 := tm_tabs (tm_subst_env s2 (tm_ty_subst_env th2 t0))).
    + change (lc_tm_at 0 0 (tm_subst_env s1 (tm_ty_subst_env th1 (tm_tabs t0)))).
      apply lc_subst_both; assumption.
    + change (lc_tm_at 0 0 (tm_subst_env s2 (tm_ty_subst_env th2 (tm_tabs t0)))).
      apply lc_subst_both; assumption.
    + apply multi_refl.
    + apply multi_refl.
    + unfold Vty. split.
      * apply v_tabs.
        change (lc_tm_at 0 0 (tm_subst_env s1 (tm_ty_subst_env th1 (tm_tabs t0)))).
        apply lc_subst_both; assumption.
      * split.
        -- apply v_tabs.
           change (lc_tm_at 0 0 (tm_subst_env s2 (tm_ty_subst_env th2 (tm_tabs t0)))).
           apply lc_subst_both; assumption.
        -- intros rho U1 U2 HU1 HU2.
           set (X := fresh_atom (L ++ ty_fv T0 ++ tm_ty_fv t0 ++ ctx_fv Gamma)).
           assert (HXL : ~ In X L).
           { intro Hc. apply (fresh_atom_notin (L ++ ty_fv T0 ++ tm_ty_fv t0 ++ ctx_fv Gamma)).
             repeat rewrite in_app_iff. auto. }
           assert (HXfvT : ~ In X (ty_fv T0)).
           { intro Hc. apply (fresh_atom_notin (L ++ ty_fv T0 ++ tm_ty_fv t0 ++ ctx_fv Gamma)).
             repeat rewrite in_app_iff. auto. }
           assert (HXfvt : ~ In X (tm_ty_fv t0)).
           { intro Hc. apply (fresh_atom_notin (L ++ ty_fv T0 ++ tm_ty_fv t0 ++ ctx_fv Gamma)).
             repeat rewrite in_app_iff. auto. }
           assert (HXctx : ~ In X (ctx_fv Gamma)).
           { intro Hc. apply (fresh_atom_notin (L ++ ty_fv T0 ++ tm_ty_fv t0 ++ ctx_fv Gamma)).
             repeat rewrite in_app_iff. auto. }
           assert (Henv' : forall y Ti, lookup_context y Gamma = Some Ti ->
                     Rty env (update_xi xi X rho) Ti (s1 y) (s2 y)).
           { intros y Ti Hy.
             apply (proj1 (Rty_xi_agree Ti env xi (update_xi xi X rho)
                            ltac:(intros Y HY; symmetry; apply update_xi_neq;
                                  intro Hc; apply HXctx; rewrite <- Hc;
                                  apply (ctx_fv_lookup Gamma y Ti Hy Y HY))
                            (s1 y) (s2 y))).
             apply Henv. assumption. }
           assert (Hl1' : forall Y, lc_ty_at 0 (update_theta th1 X U1 Y)).
           { apply update_theta_lc; assumption. }
           assert (Hl2' : forall Y, lc_ty_at 0 (update_theta th2 X U2 Y)).
           { apply update_theta_lc; assumption. }
           pose proof (IHbody X HXL env (update_xi xi X rho)
                         (update_theta th1 X U1) (update_theta th2 X U2)
                         s1 s2 Hl1' Hl2' Hs1 Hs2 Henv') as HIH.
           assert (Heq1 : tm_subst_env s1
                            (tm_ty_subst_env (update_theta th1 X U1) (open_tm_ty t0 (Ty_FVar X)))
                          = open_tm_ty (tm_subst_env s1 (tm_ty_subst_env th1 t0)) U1).
           { apply subst_open_ty_fvar_update; assumption. }
           assert (Heq2 : tm_subst_env s2
                            (tm_ty_subst_env (update_theta th2 X U2) (open_tm_ty t0 (Ty_FVar X)))
                          = open_tm_ty (tm_subst_env s2 (tm_ty_subst_env th2 t0)) U2).
           { apply subst_open_ty_fvar_update; assumption. }
           rewrite Heq1 in HIH. rewrite Heq2 in HIH.
           pose proof (proj1 (Rty_open_fvar env xi 0 T0 X rho ltac:(lia) HXfvT HlcT1
                                (open_tm_ty (tm_subst_env s1 (tm_ty_subst_env th1 t0)) U1)
                                (open_tm_ty (tm_subst_env s2 (tm_ty_subst_env th2 t0)) U2))
                         HIH) as HRrho.
           rewrite insert_at_zero in HRrho.
           destruct (Rty_elim (rho :: env) xi T0
                       (open_tm_ty (tm_subst_env s1 (tm_ty_subst_env th1 t0)) U1)
                       (open_tm_ty (tm_subst_env s2 (tm_ty_subst_env th2 t0)) U2) HRrho)
             as [HlcR1 [HlcR2 HexR]].
           destruct HexR as [u1 [u2 [Ru1 [Ru2 HVu]]]].
           exists u1, u2. split.
           ++ apply multi_trans with
                (t2 := open_tm_ty (tm_subst_env s1 (tm_ty_subst_env th1 t0)) U1).
              ** apply multi_tbeta.
                 --- change (lc_tm_at 0 0 (tm_subst_env s1 (tm_ty_subst_env th1 (tm_tabs t0)))).
                     apply lc_subst_both; assumption.
                 --- assumption.
              ** assumption.
           ++ split.
              ** apply multi_trans with
                   (t2 := open_tm_ty (tm_subst_env s2 (tm_ty_subst_env th2 t0)) U2).
                 --- apply multi_tbeta.
                     +++ change (lc_tm_at 0 0 (tm_subst_env s2 (tm_ty_subst_env th2 (tm_tabs t0)))).
                         apply lc_subst_both; assumption.
                     +++ assumption.
                 --- assumption.
              ** assumption.
  - (* T_TApp *)
    pose proof (IH1 env xi th1 th2 s1 s2 Hl1 Hl2 Hs1 Hs2 Henv) as HR1.
    pose proof (has_type_wf_lc Delta Gamma t0 (Ty_All T0) H1) as Hwl.
    destruct Hwl as [HwfAll _].
    assert (HlcT1 : lc_ty_at 1 T0).
    { apply lc_ty_all_inv with (k := 0). apply (wf_ty_lc Delta (Ty_All T0)). assumption. }
    assert (HlcU : lc_ty_at 0 U) by (apply (wf_ty_lc Delta U); assumption).
    assert (HlcU1 : lc_ty_at 0 (ty_subst_env th1 U)).
    { apply (lc_ty_subst_env 0 th1 U); assumption. }
    assert (HlcU2 : lc_ty_at 0 (ty_subst_env th2 U)).
    { apply (lc_ty_subst_env 0 th2 U); assumption. }
    change (Rty env xi (open_ty T0 U)
              (tm_tapp (tm_subst_env s1 (tm_ty_subst_env th1 t0)) (ty_subst_env th1 U))
              (tm_tapp (tm_subst_env s2 (tm_ty_subst_env th2 t0)) (ty_subst_env th2 U))).
    destruct (Rty_elim env xi (Ty_All T0)
                (tm_subst_env s1 (tm_ty_subst_env th1 t0))
                (tm_subst_env s2 (tm_ty_subst_env th2 t0)) HR1)
      as [Hlc0a [Hlc0b Hex0]].
    destruct Hex0 as [v1 [v2 [Rv1 [Rv2 HV0]]]].
    destruct (Vty_all_elim env xi T0 v1 v2 HV0) as [Hvv1 [Hvv2 Hfall]].
    destruct (Hfall (Vty env xi U) (ty_subst_env th1 U) (ty_subst_env th2 U) HlcU1 HlcU2)
      as [a1 [a2 [Ra1 [Ra2 HVa]]]].
    assert (HVa' : Vty env xi (open_ty T0 U) a1 a2).
    { apply (proj2 (Vty_open_ty env xi 0 T0 U (Vty env xi U) ltac:(lia) HlcU HlcT1
                     ltac:(intros p q; split; intro Hx; exact Hx) a1 a2)).
      rewrite insert_at_zero. exact HVa. }
    apply Rty_intro with (v1 := a1) (v2 := a2).
    + apply lc_tm_tapp; assumption.
    + apply lc_tm_tapp; assumption.
    + apply multi_trans with (t2 := tm_tapp v1 (ty_subst_env th1 U)).
      * apply multi_tapp; assumption.
      * assumption.
    + apply multi_trans with (t2 := tm_tapp v2 (ty_subst_env th2 U)).
      * apply multi_tapp; assumption.
      * assumption.
    + assumption.
  - (* T_Choice *)
    pose proof (IH1 env xi th1 th2 s1 s2 Hl1 Hl2 Hs1 Hs2 Henv) as HR1.
    pose proof (IH2 env xi th1 th2 s1 s2 Hl1 Hl2 Hs1 Hs2 Henv) as HR2.
    change (Rty env xi T0
              (tm_choice (tm_subst_env s1 (tm_ty_subst_env th1 t1))
                         (tm_subst_env s1 (tm_ty_subst_env th1 t2)))
              (tm_choice (tm_subst_env s2 (tm_ty_subst_env th2 t1))
                         (tm_subst_env s2 (tm_ty_subst_env th2 t2)))).
    destruct (Rty_elim env xi T0
                (tm_subst_env s1 (tm_ty_subst_env th1 t1))
                (tm_subst_env s2 (tm_ty_subst_env th2 t1)) HR1)
      as [Hlc1a [Hlc1b Hex1]].
    destruct Hex1 as [v1 [v2 [Rv1 [Rv2 HV1]]]].
    destruct (Rty_elim env xi T0
                (tm_subst_env s1 (tm_ty_subst_env th1 t2))
                (tm_subst_env s2 (tm_ty_subst_env th2 t2)) HR2)
      as [Hlc2a [Hlc2b Hex2]].
    apply Rty_intro with (v1 := v1) (v2 := v2).
    + apply lc_tm_choice; assumption.
    + apply lc_tm_choice; assumption.
    + apply multi_trans with (t2 := tm_subst_env s1 (tm_ty_subst_env th1 t1)).
      * apply multi_choice_l; assumption.
      * assumption.
    + apply multi_trans with (t2 := tm_subst_env s2 (tm_ty_subst_env th2 t1)).
      * apply multi_choice_l; assumption.
      * assumption.
    + assumption.
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
  intros t Ht U v HwfU Hv HvU.
  set (rho := fun a b => a -->* v /\ b -->* v).
  pose proof (fundamental [] empty t (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
              [] (fun _ => rho) (fun X => Ty_FVar X) (fun X => Ty_FVar X)
              (fun x => tm_fvar x) (fun x => tm_fvar x)) as Hf.
  assert (HlcTheta : forall X, lc_ty_at 0 ((fun X => Ty_FVar X) X))
    by (intro; apply lc_ty_fvar).
  assert (HlcSigma : forall x, lc_tm_at 0 0 ((fun x => tm_fvar x) x))
    by (intro; apply lc_tm_fvar).
  assert (Henv : forall x Ti, lookup_context x empty = Some Ti ->
                 Rty [] (fun _ => rho) Ti ((fun x => tm_fvar x) x) ((fun x => tm_fvar x) x)).
  { intros x Ti Hlk. simpl in Hlk. discriminate. }
  specialize (Hf HlcTheta HlcTheta HlcSigma HlcSigma Henv).
  rewrite tm_ty_subst_env_id in Hf.
  rewrite tm_subst_env_id in Hf.
  destruct (Rty_elim [] (fun _ => rho) (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) t t Hf)
    as [HlcT1 [HlcT2 Hex]].
  destruct Hex as [w1 [w2 [Rw1 [Rw2 HV]]]].
  destruct (Vty_all_elim [] (fun _ => rho) (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)) w1 w2 HV)
    as [Hvw1 [Hvw2 Hfall]].
  assert (HlcU : lc_ty_at 0 U) by (apply (wf_ty_lc [] U); assumption).
  destruct (Hfall rho U U HlcU HlcU) as [u1 [u2 [Ru1 [Ru2 HVu]]]].
  destruct (Vty_arrow_elim [rho] (fun _ => rho) (Ty_BVar 0) (Ty_BVar 0) u1 u2 HVu)
    as [Hvu1 [Hvu2 Hfar]].
  assert (Hvv : Vty [rho] (fun _ => rho) (Ty_BVar 0) v v).
  { simpl. split; [assumption | split; [assumption |]].
    unfold rho. split; apply multi_refl. }
  destruct (Hfar v v Hvv) as [s1 [s2 [Rs1 [Rs2 HVs]]]].
  destruct (Vty_bvar_elim [rho] (fun _ => rho) 0 s1 s2 HVs) as [Hvs1 [Hvs2 Hrho]].
  unfold rho in Hrho. destruct Hrho as [Hs1 _].
  apply multi_trans with (t2 := tm_app (tm_tapp w1 U) v).
  - apply multi_app_l.
    + apply multi_tapp; assumption.
    + apply value_lc; assumption.
  - apply multi_trans with (t2 := tm_app u1 v).
    + apply multi_app_l.
      * assumption.
      * apply value_lc; assumption.
    + apply multi_trans with (t2 := s1).
      * assumption.
      * assumption.
Qed.

End SystemFParametricityNondeterminismHardTask.
